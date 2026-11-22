module

public import OnlineColouring.AppBDOneLevel
public import OnlineColouring.Transfer

/-!
# Corollary B.2 (a cheaper top)

Corollary B.2 (`cor:cheap-top`, Appendix B): *Let `K ≥ 3` and `j ≥ 1` with
`2K - 2 ≤ |P_j(k)|`.  Running the flow adversary of Theorem D.2 on `K_{2K-2}` and then `j - 1`
reservation blow-ups below it gives an adversary that forces `K` colours on `k`-colourable graphs
with at most `2^j K^{(j^2+j+2)/2}` vertices.*

This file proves the statement in per-algorithm form (as `Forcing.lean` does for Theorem 6.4),
through the predicate `ForcesWith` of `Transfer.lean`.

* `flow_forcesWith`: the play of the flow adversary against a proper algorithm is an input with
  `∑ b_t` vertices that is a blow-up of `K_m`, hence maps to `Tmpl(P)` if `m ≤ |J*(P)|`
  (Lemma 5.1 (i) and Lemma 5.2), has post-degree at most `max_{t ≥ 2} b_t`, and
  receives `⌊m/2⌋ + 1` colours.
* `cheaper_top_forcesWith`: with `m = 2K - 2` and minimal blocks `max(1, m - t)`: `binom(m,2) + 1`
  vertices, post-degree at most `2K - 4`, `K` colours.
* `cheapTopSize K j`: the exact number of vertices after `j - 1` reservation blow-ups
  (`ForcesWith.iterate`), and `cheapTopSize_le : cheapTopSize K j ≤ 2^j K^{(j^2+j+2)/2}` for
  `K ≥ 3` and `j ≥ 1`.
* `cheaper_top`: **Corollary B.2**, per-algorithm form: every proper algorithm uses `K` colours on
  some `k`-colourable input with `cheapTopSize K j` vertices, obtained from its play against the
  flow adversary by `j - 1` reservation blow-ups.

The corollary for the adversary that the paper names, the flow adversary with `j - 1` blow-ups
`Blow.B` below it (`cheapAdv`, `cheaper_top_composed`), is in `AppBDCheapTopAdv.lean`, with the
bound `N_k(K) ≤ 2^j K^{(j^2+j+2)/2}`.  The numbers quoted after the corollary (7 176, 20 944,
3 685, about `2.7 · 10^9`) are `Cert.cheapTop_values` (`CertNumbers.lean`).
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-! ### A one-level sequence is a blow-up of `K_m` -/

theorem if_pos_trunc {N : ℕ → Finset ℕ} {n i : ℕ} (hi : i < n) : truncSeq N n i = N i := by
  simp [truncSeq, hi]

section OneLevel

variable {m : ℕ} {b : ℕ → ℕ} {N : ℕ → Finset ℕ} {srv : ℕ → ℕ → ℕ}

/-- The data of `IsOneLevelSeq`, with the server map named. -/
structure OneLevelData (m : ℕ) (b : ℕ → ℕ) (N : ℕ → Finset ℕ) (srv : ℕ → ℕ → ℕ) : Prop where
  mem : ∀ t < m, ∀ s < t, srv t s ∈ blk b s
  inj : ∀ t < m, ∀ t' < m, ∀ s, s < t → s < t' → srv t s = srv t' s → t = t'
  nbr : ∀ t < m, ∀ x ∈ blk b t, N x = (range t).image (srv t)

theorem OneLevelData.mem_iff (h : OneLevelData m b N srv) {x u : ℕ} (hx : x < start b m)
    (hu : u < start b m) :
    x ∈ N u ↔ blockOf b m x < blockOf b m u ∧ srv (blockOf b m u) (blockOf b m x) = x := by
  obtain ⟨hub, hum⟩ := mem_blk_blockOf hu
  rw [h.nbr _ hum u hub, mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_range] at hs
    have e := blockOf_of_mem (hs.trans hum) (h.mem _ hum s hs)
    rw [e]
    exact ⟨hs, rfl⟩
  · rintro ⟨hlt, e⟩
    exact ⟨_, mem_range.2 hlt, e⟩

theorem OneLevelData.lt_of_mem (h : OneLevelData m b N srv) {x u : ℕ} (hu : u < start b m)
    (hx : x ∈ N u) : x < u := by
  obtain ⟨hub, hum⟩ := mem_blk_blockOf hu
  rw [h.nbr _ hum u hub, mem_image] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [mem_range] at hs
  exact (lt_of_mem_blk (h.mem _ hum s hs) hs).trans_le (mem_blk.1 hub).1

theorem OneLevelData.valid (h : OneLevelData m b N srv) :
    ValidSeq (truncSeq N (start b m)) := by
  intro i x hx
  unfold truncSeq at hx
  split_ifs at hx with hi
  · exact mem_range.2 (h.lt_of_mem hi hx)
  · simp at hx

open scoped Classical in
/-- The serve map of a one-level sequence: `x` serves the block `t` with `srv t (block of x) = x`,
if there is one. -/
noncomputable def serveOf (m : ℕ) (b : ℕ → ℕ) (srv : ℕ → ℕ → ℕ) (x : Fin (start b m)) :
    Option (Fin m) :=
  if h : ∃ t : Fin m, blockOf b m x < t ∧ srv t (blockOf b m x) = x then some h.choose else none

theorem OneLevelData.serveOf_eq_some (h : OneLevelData m b N srv) {x : Fin (start b m)}
    {v : Fin m} :
    serveOf m b srv x = some v ↔ blockOf b m x < v ∧ srv v (blockOf b m x) = x := by
  unfold serveOf
  split_ifs with hex
  · have hs := hex.choose_spec
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact hs
    · rintro ⟨hlt, e⟩
      exact Fin.ext (h.inj _ hex.choose.2 _ v.2 _ hs.1 hlt (hs.2.trans e.symm))
  · constructor
    · intro hn
      simp at hn
    · exact fun hv => absurd ⟨v, hv⟩ hex

/-- A one-level sequence with nonempty blocks is a blow-up of the clique `K_m`. -/
noncomputable def OneLevelData.blowUp (h : OneLevelData m b N srv) (hb1 : ∀ t < m, 1 ≤ b t) :
    BlowUp (⊤ : SimpleGraph (Fin m))
      (OnlineInput.ofSeq (truncSeq N (start b m)) h.valid (start b m)).graph where
  π x := ⟨blockOf b m x, (mem_blk_blockOf x.2).2⟩
  serve := serveOf m b srv
  π_surjective v := by
    have hmem : start b v ∈ blk b v := by
      refine mem_blk.2 ⟨le_rfl, ?_⟩
      rw [start_succ]
      have := hb1 v v.2
      omega
    exact ⟨⟨start b v, lt_of_mem_blk hmem v.2⟩, Fin.ext (blockOf_of_mem v.2 hmem)⟩
  lt_of_π_lt x y hxy := by
    have hlt : blockOf b m x < blockOf b m y := hxy
    exact Fin.lt_def.2 ((lt_of_mem_blk (mem_blk_blockOf x.2).1 hlt).trans_le
      (mem_blk.1 (mem_blk_blockOf y.2).1).1)
  serve_spec x v hs := by
    have := (h.serveOf_eq_some.1 hs).1
    exact ⟨Fin.lt_def.2 this, by
      rw [SimpleGraph.top_adj]
      exact fun e => absurd (congrArg Fin.val e) this.ne⟩
  adj_iff x u := by
    have key : ∀ x u : Fin (start b m), (x : ℕ) ∈ truncSeq N (start b m) u ↔
        serveOf m b srv x = some ⟨blockOf b m u, (mem_blk_blockOf u.2).2⟩ := by
      intro x u
      rw [h.serveOf_eq_some, if_pos_trunc u.2]
      exact h.mem_iff x.2 u.2
    have hlt : ∀ x u : Fin (start b m), (x : ℕ) ∈ truncSeq N (start b m) u → x < u := by
      intro x u hx
      rw [if_pos_trunc u.2] at hx
      exact Fin.lt_def.2 (h.lt_of_mem u.2 hx)
    rw [OnlineInput.ofSeq_adj]
    constructor
    · rintro (hx | hx)
      · exact Or.inl ⟨hlt x u hx, (key x u).1 hx⟩
      · exact Or.inr ⟨hlt u x hx, (key u x).1 hx⟩
    · rintro (⟨-, hx⟩ | ⟨-, hx⟩)
      · exact Or.inl ((key x u).2 hx)
      · exact Or.inr ((key u x).2 hx)

/-- A vertex of a one-level sequence serves at most one block, so its post-degree is at most the
size of a block other than the first. -/
theorem OneLevelData.postDeg_le (h : OneLevelData m b N srv) {D : ℕ}
    (hD : ∀ t, 1 ≤ t → t < m → b t ≤ D) (w : ℕ) (hw : w < start b m) :
    postDeg (truncSeq N (start b m)) (start b m) w ≤ D := by
  unfold postDeg rank
  rcases ((range (start b m)).filter fun v => w ∈ truncSeq N (start b m) v).eq_empty_or_nonempty
    with he | ⟨v₀, hv₀⟩
  · rw [he]
    simp
  rw [mem_filter, mem_range] at hv₀
  have hmem : ∀ v, v < start b m → w ∈ truncSeq N (start b m) v →
      blockOf b m w < blockOf b m v ∧ srv (blockOf b m v) (blockOf b m w) = w := by
    intro v hv hwv
    rw [if_pos_trunc hv] at hwv
    exact (h.mem_iff hw hv).1 hwv
  obtain ⟨h0lt, h0e⟩ := hmem v₀ hv₀.1 hv₀.2
  obtain ⟨-, h0m⟩ := mem_blk_blockOf hv₀.1
  refine (card_le_card (t := blk b (blockOf b m v₀)) fun v hv => ?_).trans ?_
  · rw [mem_filter, mem_range] at hv
    obtain ⟨hlt, he⟩ := hmem v hv.1 hv.2
    obtain ⟨hvb, hvm⟩ := mem_blk_blockOf hv.1
    rw [h.inj _ h0m _ hvm _ h0lt hlt (h0e.trans he.symm)]
    exact hvb
  · rw [card_blk]
    exact hD _ (by omega) h0m

end OneLevel

/-! ### The flow adversary as the top of a tower -/

/-- The play of the flow adversary on `K_m` (`m ≥ 1`, block sizes `b t ≥ minBlock m t`) against a
proper algorithm: an input with `∑ b_t` vertices that maps to `Tmpl(P)` (if `m ≤ |J*(P)|`), has
post-degree at most `D` (if the blocks other than the first have at most `D` vertices), and
receives `⌊m/2⌋ + 1` colours. -/
theorem flow_forcesWith {P : Type*} [PartialOrder P] [Fintype (Jst P)] {m D : ℕ} {b : ℕ → ℕ}
    (hm : 1 ≤ m) (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) (hD : ∀ t, 1 ≤ t → t < m → b t ≤ D)
    (hP : m ≤ Fintype.card (Jst P)) : ForcesWith P (m / 2 + 1) (start b m) D := by
  intro A hA
  have hb' : ∀ t < m, m - t - 1 ≤ b t := fun t ht => (le_max_right _ _).trans (hb t ht)
  have hb1 : ∀ t < m, 1 ≤ b t := fun t ht => (le_max_left _ _).trans (hb t ht)
  obtain ⟨srv, h1, h2, h3⟩ := flowSeq_isOneLevelSeq A hb'
  have hdata : OneLevelData m b (playSeq (flowRule m b) A) srv := ⟨h1, h2, h3⟩
  refine ⟨truncSeq (playSeq (flowRule m b) A) (start b m), hdata.valid,
    fun w hw => hdata.postDeg_le hD w hw,
    (hdata.blowUp hb1).hasLabelling_of_jst (hasLabelling_clique_iff.2 hP), ?_⟩
  have e : (range (start b m)).image (runCol A (truncSeq (playSeq (flowRule m b) A) (start b m)))
      = (range (start b m)).image (flowCol m b A) :=
    image_congr fun i hi => runCol_congr fun j hj =>
      if_pos_trunc (lt_of_le_of_lt hj (mem_range.1 hi))
  rw [e]
  exact colours_ge hm hb' hb1 fun t ht => flowCol_properAt A hA hb' ht

/-- The minimal block sizes `max(1, m - t)` of Theorem D.2 (block `t` here is the paper's
`v_{t+1}`). -/
def minBlock (m t : ℕ) : ℕ := max 1 (m - t - 1)

theorem sum_max_one (m : ℕ) : ∑ t ∈ range (m + 1), max 1 t = (m + 1).choose 2 + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (m + 1 + 1).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
      Nat.choose_succ_succ' (m + 1) 1
    rw [sum_range_succ, ih, e, Nat.choose_one_right, max_eq_right (by omega : 1 ≤ m + 1)]
    omega

/-- With minimal blocks the flow adversary presents `binom(m, 2) + 1` vertices. -/
theorem start_minBlock {m : ℕ} (hm : 1 ≤ m) : start (minBlock m) m = m.choose 2 + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [← sum_max_one, start, ← sum_range_reflect]
  exact sum_congr rfl fun t ht => by
    rw [mem_range] at ht
    simp only [minBlock]
    congr 1
    omega

/-- The top of Corollary B.2: for `K ≥ 3`, the flow adversary on `K_{2K-2}` with minimal blocks
forces `K` colours with `binom(2K-2, 2) + 1` vertices and post-degree at most `2K - 4`, on graphs
that map to `Tmpl(P_j(k))` if `2K - 2 ≤ |P_{j+1}(k)|` (here `j + 1` is the `j` of the
corollary). -/
theorem cheaper_top_forcesWith {k K j : ℕ} (hK : 3 ≤ K)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k (j + 1))) :
    ForcesWith (LabelPoset k j) K ((2 * K - 2).choose 2 + 1) (2 * K - 4) := by
  have h := flow_forcesWith (P := LabelPoset k j) (m := 2 * K - 2) (D := 2 * K - 4)
    (b := minBlock (2 * K - 2)) (by omega) (fun t _ => le_rfl)
    (fun t ht _ => by
      simp only [minBlock]
      omega) hP
  have e : (2 * K - 2) / 2 + 1 = K := by omega
  rw [start_minBlock (by omega), e] at h
  exact h

/-! ### The size after `j - 1` reservation blow-ups -/

/-- The number of vertices of Corollary B.2: the flow play on `K_{2K-2}` with
`binom(2K-2, 2) + 1` vertices and post-degree `D = 2K - 4`, followed by `j - 1` reservation
blow-ups with block sizes `(K-1)^{i+1} (D - 1) + 1`, `i < j - 1`. -/
def cheapTopSize (K j : ℕ) : ℕ :=
  ((2 * K - 2).choose 2 + 1) * ∏ i ∈ range (j - 1), ((K - 1) ^ (i + 1) * (2 * K - 4 - 1) + 1)

theorem cheapTop_base_le {K : ℕ} (hK : 3 ≤ K) : (2 * K - 2).choose 2 + 1 ≤ 2 * K ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, K = a + 3 := ⟨K - 3, by omega⟩
  have e1 : 2 * (a + 3) - 2 = 2 * a + 4 := by omega
  have e2 : (2 * a + 4) * (2 * a + 4 - 1) = 2 * ((a + 2) * (2 * a + 3)) := by
    rw [show 2 * a + 4 - 1 = 2 * a + 3 by omega]
    ring
  rw [e1, Nat.choose_two_right, e2, Nat.mul_div_cancel_left _ two_pos]
  nlinarith

theorem cheapTop_factor_le {K : ℕ} (hK : 3 ≤ K) (i : ℕ) :
    (K - 1) ^ (i + 1) * (2 * K - 4 - 1) + 1 ≤ 2 * K ^ (i + 2) := by
  have hp : 1 ≤ K ^ (i + 1) := Nat.one_le_pow _ _ (by omega)
  have hq : (K - 1) ^ (i + 1) ≤ K ^ (i + 1) := Nat.pow_le_pow_left (by omega) _
  have h1 : (K - 1) ^ (i + 1) * (2 * K - 4 - 1) ≤ K ^ (i + 1) * (2 * K - 1) :=
    Nat.mul_le_mul hq (by omega)
  have h2 : K ^ (i + 1) * (2 * K - 1) + K ^ (i + 1) = 2 * K ^ (i + 2) := by
    obtain ⟨a, rfl⟩ : ∃ a, K = a + 1 := ⟨K - 1, by omega⟩
    rw [show 2 * (a + 1) - 1 = 2 * a + 1 by omega]
    ring
  omega

theorem cheapTop_prod_le {K : ℕ} (hK : 3 ≤ K) (n : ℕ) :
    ∏ i ∈ range n, ((K - 1) ^ (i + 1) * (2 * K - 4 - 1) + 1) ≤ 2 ^ n * K ^ (n * (n + 3) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (n + 1) * (n + 1 + 3) / 2 = n * (n + 3) / 2 + (n + 2) := by
      rw [show (n + 1) * (n + 1 + 3) = n * (n + 3) + 2 * (n + 2) by ring,
        Nat.add_mul_div_left _ _ two_pos]
    rw [prod_range_succ, e]
    calc _ ≤ 2 ^ n * K ^ (n * (n + 3) / 2) * (2 * K ^ (n + 2)) :=
          Nat.mul_le_mul ih (cheapTop_factor_le hK n)
      _ = 2 ^ (n + 1) * K ^ (n * (n + 3) / 2 + (n + 2)) := by ring

/-- For `K ≥ 3` and `j ≥ 1`, `cheapTopSize K j ≤ 2^j K^{(j^2+j+2)/2}`. -/
theorem cheapTopSize_le {K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j) :
    cheapTopSize K j ≤ 2 ^ j * K ^ ((j ^ 2 + j + 2) / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have e : ((n + 1) ^ 2 + (n + 1) + 2) / 2 = n * (n + 3) / 2 + 2 := by
    rw [show (n + 1) ^ 2 + (n + 1) + 2 = n * (n + 3) + 2 * 2 by ring,
      Nat.add_mul_div_left _ _ two_pos]
  rw [cheapTopSize, Nat.add_sub_cancel, e]
  calc _ ≤ 2 * K ^ 2 * (2 ^ n * K ^ (n * (n + 3) / 2)) :=
        Nat.mul_le_mul (cheapTop_base_le hK) (cheapTop_prod_le hK n)
    _ = 2 ^ (n + 1) * K ^ (n * (n + 3) / 2 + 2) := by ring

/-- **Corollary B.2 (a cheaper top)**, per-algorithm form.  Let `K ≥ 3` and `j ≥ 1` with
`2K - 2 ≤ |P_j(k)|`.  Every proper deterministic algorithm uses at least `K` colours on some
`k`-colourable input with `cheapTopSize K j ≤ 2^j K^{(j^2+j+2)/2}` vertices: its play against
the flow adversary of Theorem D.2 on `K_{2K-2}`, blown up `j - 1` times by the reservation
adversary of Lemma 6.2. -/
theorem cheaper_top {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    ChiDetAtLeast k (cheapTopSize K j) K ∧
      cheapTopSize K j ≤ 2 ^ j * K ^ ((j ^ 2 + j + 2) / 2) := by
  refine ⟨?_, cheapTopSize_le hK hj⟩
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have h := ForcesWith.iterate (k := k) (by omega : 2 ≤ K) n _ _ (by omega : 1 ≤ 2 * K - 4)
    (cheaper_top_forcesWith hK hP)
  exact h.chiDetAtLeast

end OnlineColouring.AppBD
