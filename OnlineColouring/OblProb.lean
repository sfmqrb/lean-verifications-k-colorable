module

public import OnlineColouring.Oblivious
public import OnlineColouring.OblCount

/-!
# The oblivious blow-up `OB_R(ℋ)` (Construction C.1) and Lemma C.2

Construction C.1 (`con:OB`) and Lemma C.2 (`lem:O`, forcing survives an oblivious blow-up) of
Appendix C, with both conclusions.  The part of the proof in which the hidden indices are fixed
(the presented sequence `obSeq`, the simulated algorithm of Step 2 and the comparison of Step 3)
is in `Oblivious.lean`; this file adds the distribution, Step 1 and the assembly.

## Construction C.1

* `ℋ : PMF (OnlineInput N)` is an arbitrary distribution over ordered graphs on exactly `N`
  vertices `v_0, …, v_{N-1}`, and `δ : ℕ → ℕ` (used at the positions `m < N`) is the position-only
  bound: `∀ I ∈ ℋ.support, ∀ m < N, postDeg I.seq N m ≤ δ m` (`postDeg I.seq N m` is the number of
  later neighbours of `v_m`, `postDeg_seq_eq`).
* `Idx N R δ` is the sample space of the hidden indices: one value in `Fin (δ m - 1 + 1)` for each
  position `m < N` and each of the `R` vertices of the block `σ(v_m)`.  For `δ m ≥ 1` this is
  `Fin (δ m)`, the paper's `[δ(m)]` counted from `0`; for `δ m = 0` it is a one-point type and the
  value is not used.  The indices are drawn from the uniform distribution `unifPMF (Idx N R δ)` on
  this product, that is, they are independent and each is uniform on its factor
  (`unifPMF_idx_apply`, `card_idx`).
* `idx δ ω w t` is the index of the `t`-th vertex of the block of `v_w`, as a natural number; a
  vertex of a block with `δ w = 0` has *no index*: it gets the value `N`, which is the rank of no
  later neighbour (`rank_seq_lt`), so it belongs to no index class that is ever joined.
* `obInput R δ I ω` is the outcome: the ordered graph on exactly `N * R` vertices in which the
  block of `v_m` is `m*R, …, m*R+R-1` and every vertex of the block of `v_m` is joined to the whole
  index class `I(w, a)` for every earlier neighbour `w` of `v_m`, where `v_m` is the `a`-th later
  neighbour of `w` (`a = rank I.seq w m`, counted from `0`).  `mem_obInput_nbr` states this rule
  directly: `x` is an earlier neighbour of `y` iff the block of `x` is an earlier neighbour of the
  block of `y` in `I`, the block of `x` has indices (`δ ≠ 0`), and the index of `x` is the rank of
  the block of `y` among the later neighbours of the block of `x`.
* `OB R δ ℋ : PMF (OnlineInput (N * R))` is the distribution of the outcome when `I ∼ ℋ` and
  `ω` uniform are independent: `ℋ.bind fun I => (unifPMF (Idx N R δ)).map (obInput R δ I)`.
* The paragraph after the construction: `obInput_blowUp` (for `R ≥ 1`, every outcome is a blow-up
  of `I`), `postDeg_obInput_le` (post-degree at most `R`) and `postDeg_obInput_eq_zero`
  (post-degree `0` for blocks with `δ m = 0`).

## Lemma C.2

`oblivious_blowup` is the lemma as stated: for `K ≥ 2`, `ρ` and `ε` real, a partial order `P`,
(a) every `I` in the support of `ℋ` has a `J*(P)`-labelling, (b) every proper deterministic online
algorithm uses at least `K` colours on `I ∼ ℋ` with probability at least `ρ`, and
(c) `∑_{m<N} δ(m) (1 - 1/δ(m))^⌈R/(K-1)⌉ ≤ ε` (in `ℝ`, where a term with `δ(m) = 0` is
`0 * … = 0`, the paper's convention), every graph in the support of `OB R δ ℋ` has a
`P`-labelling, and every proper deterministic online algorithm uses at least `K` colours on
`OB R δ ℋ` with probability at least `ρ - ε`.  The two conclusions are also available separately
(`oblivious_blowup_labelling`, `oblivious_blowup_forcing`).  The hypothesis `ε ≥ 0` of the paper
follows from (c) and is not assumed.  `R = 0` is allowed (then the hypotheses give `ρ ≤ ε`).

`cond_c_of_weak` is the remark after the lemma: (c) follows from `N D exp(-R/((K-1)D)) ≤ ε` if
`δ(m) ≤ D` for all `m`.

## Differences from the paper's proof

* The popular colour `π(v_m)` is `popCol` of `Oblivious.lean`: the first colour of the block that
  occurs at least `c = ⌈R/(K-1)⌉` times, not the most frequent one.  The proof only uses that
  `π(v_m)` occurs at least `c` times when `T_m` fails; `π` does not occur in the statement.
* Step 1 conditions on *all* blocks other than `σ(v_m)` (`card_filter_mul_le`), not only on the
  earlier ones; the colouring of `σ(v_m)` depends on the earlier ones only (`obCol_congr`).
* Probabilities of the uniform indices are counted (`card_evE_le`), and the independence of `I`
  and `ω` is Fubini for the product distribution (`mix_bound`).
* "Deterministic online algorithm" means a proper one (`OnlineAlg.IsProper`), in hypothesis (b)
  and in the conclusion, as everywhere in the library.
-/

@[expose] public section

namespace OnlineColouring

namespace Obl

open Finset
open scoped ENNReal

/-! ### Facts about input sequences -/

theorem mem_seq {N : ℕ} {I : OnlineInput N} {x v : ℕ} :
    x ∈ I.seq v ↔ ∃ (hv : v < N) (hx : x < N), (⟨x, hx⟩ : Fin N) ∈ I.nbr ⟨v, hv⟩ := by
  unfold OnlineInput.seq
  constructor
  · intro h
    split_ifs at h with hv
    · simp only [mem_map, Fin.valEmbedding_apply] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨hv, u.2, hu⟩
    · simp at h
  · rintro ⟨hv, hx, h⟩
    simp only [hv, ↓reduceDIte]
    exact mem_map.2 ⟨⟨x, hx⟩, h, rfl⟩

theorem lt_of_mem_seq {N : ℕ} {I : OnlineInput N} {x v : ℕ} (h : x ∈ I.seq v) : v < N :=
  (mem_seq.1 h).1

theorem rank_le (H : ℕ → Finset ℕ) (w v : ℕ) : rank H w v ≤ v :=
  (card_filter_le _ _).trans (card_range v).le

/-- The rank of a later neighbour is less than `N`. -/
theorem rank_seq_lt {N : ℕ} {I : OnlineInput N} {w v : ℕ} (h : w ∈ I.seq v) :
    rank I.seq w v < N :=
  lt_of_le_of_lt (rank_le _ _ _) (lt_of_mem_seq h)

/-- `postDeg I.seq N m` is the post-degree `d⁺_I(v_m)`: the number of vertices that have `v_m` as
an earlier neighbour. -/
theorem postDeg_seq_eq {N : ℕ} (I : OnlineInput N) (m : Fin N) :
    postDeg I.seq N m = (univ.filter fun v : Fin N => m ∈ I.nbr v).card := by
  unfold postDeg rank
  symm
  refine card_bij (fun v _ => (v : ℕ)) (fun v hv => ?_) (fun _ _ _ _ h => Fin.ext h)
    fun i hi => ?_
  · refine mem_filter.2 ⟨mem_range.2 v.2, mem_seq.2 ⟨v.2, m.2, (mem_filter.1 hv).2⟩⟩
  · obtain ⟨hv, _, h⟩ := mem_seq.1 (mem_filter.1 hi).2
    exact ⟨⟨i, hv⟩, mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩

theorem cost_eq_colsOn {N : ℕ} (I : OnlineInput N) (A : OnlineAlg) :
    I.cost A = colsOn A I.seq N := by
  have h := OnlineInput.cost_ofSeq (N := I.seq) (hN := I.seq_valid) (n := N) A
  rwa [OnlineInput.ofSeq_seq] at h

/-! ### Construction C.1: the hidden indices -/

/-- The sample space of the hidden indices: for every position `m < N` and each of the `R`
vertices of the block `σ(v_m)`, a value in `Fin (δ m - 1 + 1)` (which is `Fin (δ m)` if
`δ m ≥ 1`, and a one-point type, "no index", if `δ m = 0`). -/
abbrev Idx (N R : ℕ) (δ : ℕ → ℕ) : Type := (m : Fin N) → Fin R → Fin (δ m - 1 + 1)

/-- The number of index families: `∏_{m<N} max(δ m, 1)^R`. -/
theorem card_idx (N R : ℕ) (δ : ℕ → ℕ) :
    Fintype.card (Idx N R δ) = ∏ m : Fin N, (δ m - 1 + 1) ^ R := by
  simp [Idx]

/-- Under the uniform distribution on `Idx N R δ`, every index family has probability
`∏_{m<N} (1/max(δ m, 1))^R`: the indices are independent and uniform. -/
theorem unifPMF_idx_apply (N R : ℕ) (δ : ℕ → ℕ) (ω : Idx N R δ) :
    unifPMF (Idx N R δ) ω = ((∏ m : Fin N, (δ m - 1 + 1) ^ R : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [unifPMF_apply, card_idx]

/-- The hidden index of the `t`-th vertex of the block of `v_w`, as a natural number.  A vertex of
a block with `δ w = 0` has no index: it gets the value `N`, which is the rank of no later
neighbour. -/
def idx {N R : ℕ} (δ : ℕ → ℕ) (ω : Idx N R δ) (w t : ℕ) : ℕ :=
  if h : w < N ∧ t < R then (if δ w = 0 then N else (ω ⟨w, h.1⟩ ⟨t, h.2⟩ : ℕ)) else N

section Idx

variable {N R : ℕ} {δ : ℕ → ℕ}

theorem idx_of_lt (ω : Idx N R δ) {w t : ℕ} (hw : w < N) (ht : t < R) (hδ : δ w ≠ 0) :
    idx δ ω w t = (ω ⟨w, hw⟩ ⟨t, ht⟩ : ℕ) := by
  unfold idx
  simp only [hw, ht, and_self, ↓reduceDIte, hδ, ↓reduceIte]

theorem idx_of_zero (ω : Idx N R δ) {w : ℕ} (t : ℕ) (hδ : δ w = 0) : idx δ ω w t = N := by
  unfold idx
  split_ifs <;> rfl

/-- An index is less than `δ`, when there is one. -/
theorem idx_lt (ω : Idx N R δ) {w t : ℕ} (hw : w < N) (ht : t < R) (hδ : δ w ≠ 0) :
    idx δ ω w t < δ w := by
  rw [idx_of_lt ω hw ht hδ]
  have h : (ω ⟨w, hw⟩ ⟨t, ht⟩ : ℕ) < δ w - 1 + 1 := (ω ⟨w, hw⟩ ⟨t, ht⟩).2
  omega

theorem idx_update_of_ne (ω : Idx N R δ) (m : Fin N) (g : Fin R → Fin (δ m - 1 + 1)) {w : ℕ}
    (hw : w ≠ m) : idx δ (Function.update ω m g) w = idx δ ω w := by
  funext t
  unfold idx
  split_ifs with h h0
  · rfl
  · have hne : (⟨w, h.1⟩ : Fin N) ≠ m := fun e => hw (congrArg Fin.val e)
    rw [Function.update_of_ne hne]
  · rfl

theorem idx_update_self (ω : Idx N R δ) (m : Fin N) (g : Fin R → Fin (δ m - 1 + 1)) (t : Fin R)
    (hδ : δ m ≠ 0) : idx δ (Function.update ω m g) m t = (g t : ℕ) := by
  rw [idx_of_lt _ m.2 t.2 hδ]
  simp

end Idx

/-! ### Construction C.1: the outcome and the distribution -/

/-- The outcome of the oblivious blow-up of the ordered graph `I` with blocks of size `R` and
hidden indices `ω`: an ordered graph on exactly `N * R` vertices. -/
def obInput {N : ℕ} (R : ℕ) (δ : ℕ → ℕ) (I : OnlineInput N) (ω : Idx N R δ) :
    OnlineInput (N * R) :=
  OnlineInput.ofSeq (obSeq R I.seq (idx δ ω)) (obSeq_valid I.seq_valid) (N * R)

/-- **Construction C.1: the oblivious blow-up `OB_R(ℋ)`.** Sample `I ∼ ℋ` and, independently, the
hidden indices uniformly, and present `obInput R δ I ω`. -/
noncomputable def OB {N : ℕ} (R : ℕ) (δ : ℕ → ℕ) (𝓗 : PMF (OnlineInput N)) :
    PMF (OnlineInput (N * R)) :=
  𝓗.bind fun I => (unifPMF (Idx N R δ)).map (obInput R δ I)

section Outcome

variable {N R : ℕ} {δ : ℕ → ℕ}

theorem pos_of_fin_mul (x : Fin (N * R)) : 0 < R := by
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h
    exact absurd x.2 (by simp)
  · exact h

/-- The position of a presented vertex inside its block. -/
def posMap (R N : ℕ) (x : Fin (N * R)) : Fin R := ⟨x % R, Nat.mod_lt _ (pos_of_fin_mul x)⟩

/-- **The joining rule of Construction C.1.** In the outcome, `x` is an earlier neighbour of `y`
if and only if the block `w` of `x` is an earlier neighbour of the block `v` of `y` in `I`, the
block of `x` carries indices (`δ w ≠ 0`), and the index of `x` is `a`, where `v` is the `a`-th
later neighbour of `w` (`a = rank I.seq w v`, counted from `0`). -/
theorem mem_obInput_nbr (I : OnlineInput N) (ω : Idx N R δ) (x y : Fin (N * R)) :
    x ∈ (obInput R δ I ω).nbr y ↔
      blockMap R N x ∈ I.nbr (blockMap R N y) ∧ δ (blockMap R N x) ≠ 0 ∧
        (ω (blockMap R N x) (posMap R N x) : ℕ) =
          rank I.seq (blockMap R N x) (blockMap R N y) := by
  have hR := pos_of_fin_mul x
  have hxN : (x : ℕ) / R < N := (blockMap R N x).2
  have hxR : (x : ℕ) % R < R := Nat.mod_lt _ hR
  rw [obInput, OnlineInput.mem_ofSeq_nbr, mem_obSeq hR]
  constructor
  · rintro ⟨hmem, hidx⟩
    obtain ⟨hv, hw, hnbr⟩ := mem_seq.1 hmem
    have hδ : δ ((x : ℕ) / R) ≠ 0 := by
      intro h0
      rw [idx_of_zero ω _ h0] at hidx
      exact absurd (rank_seq_lt hmem) (by omega)
    rw [idx_of_lt ω hxN hxR hδ] at hidx
    exact ⟨hnbr, hδ, hidx⟩
  · rintro ⟨hnbr, hδ, hidx⟩
    refine ⟨mem_seq.2 ⟨(blockMap R N y).2, hxN, hnbr⟩, ?_⟩
    rw [idx_of_lt ω hxN hxR hδ]
    exact hidx

/-- **Every outcome is a blow-up of `I`** (Definition 4.6), for `R ≥ 1`: a vertex serves the arc
to the later neighbour of its block's vertex whose rank is its index, if there is one. -/
theorem obInput_blowUp (hR : 0 < R) (I : OnlineInput N) (ω : Idx N R δ) :
    Nonempty (BlowUp I.graph (obInput R δ I ω).graph) := by
  have h := obBlowUpOf (m := N) (ι := idx δ ω) I.seq_valid hR
  rw [OnlineInput.ofSeq_seq] at h
  exact ⟨h⟩

/-- A presented vertex has post-degree at most `R`. -/
theorem postDeg_obInput_le (I : OnlineInput N) (ω : Idx N R δ) (x : ℕ) :
    postDeg (obInput R δ I ω).seq (N * R) x ≤ R := by
  rcases Nat.eq_zero_or_pos R with h | hR
  · subst h
    simp [postDeg, rank]
  · have e : postDeg (obInput R δ I ω).seq (N * R) x =
        postDeg (obSeq R I.seq (idx δ ω)) (N * R) x :=
      rank_congr fun i hi => OnlineInput.seq_ofSeq hi
    rw [e]
    exact postDeg_obSeq_le hR _ _

/-- A vertex of a block `σ(v_m)` with `δ(m) = 0` has post-degree `0`. -/
theorem postDeg_obInput_eq_zero (I : OnlineInput N) (ω : Idx N R δ) {x : ℕ}
    (hδ : δ (x / R) = 0) : postDeg (obInput R δ I ω).seq (N * R) x = 0 := by
  unfold postDeg rank
  rw [card_eq_zero, filter_eq_empty_iff]
  intro u hu hx
  rw [obInput, OnlineInput.seq_ofSeq (mem_range.1 hu)] at hx
  have hR : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · subst h
      simp at hu
    · exact h
  obtain ⟨hmem, hidx⟩ := (mem_obSeq hR).1 hx
  rw [idx_of_zero ω _ hδ] at hidx
  exact absurd (rank_seq_lt hmem) (by omega)

theorem cost_obInput (I : OnlineInput N) (ω : Idx N R δ) (A : OnlineAlg) :
    (obInput R δ I ω).cost A = colsOn A (obSeq R I.seq (idx δ ω)) (N * R) :=
  OnlineInput.cost_ofSeq A

theorem mem_support_OB {𝓗 : PMF (OnlineInput N)} {J : OnlineInput (N * R)}
    (hJ : J ∈ (OB R δ 𝓗).support) : ∃ I ∈ 𝓗.support, ∃ ω : Idx N R δ, obInput R δ I ω = J := by
  obtain ⟨I, hI, hJ'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hJ
  obtain ⟨ω, -, hω⟩ := (PMF.mem_support_map_iff _ _ _).1 hJ'
  exact ⟨I, hI, ω, hω⟩

end Outcome

/-! ### Lemma C.2, first conclusion: labels -/

/-- **Lemma C.2, first conclusion.** If every graph in the support of `ℋ` maps to `T(J*(P))`,
then every graph in the support of `OB_R(ℋ)` maps to `T(P)`. -/
theorem oblivious_blowup_labelling {N R : ℕ} {δ : ℕ → ℕ} (𝓗 : PMF (OnlineInput N))
    {P : Type*} [PartialOrder P] (ha : ∀ I ∈ 𝓗.support, HasLabelling I.graph (Jst P)) :
    ∀ J ∈ (OB R δ 𝓗).support, HasLabelling J.graph P := by
  intro J hJ
  obtain ⟨I, hI, ω, rfl⟩ := mem_support_OB hJ
  rcases Nat.eq_zero_or_pos R with h | hR
  · subst h
    exact ⟨fun x => absurd x.2 (by simp), fun x => absurd x.2 (by simp)⟩
  · obtain ⟨B⟩ := obInput_blowUp hR I ω
    exact B.hasLabelling_of_jst (ha I hI)

/-! ### Step 1: an index class misses the popular colour with small probability -/

/-- The block-size condition of the pigeonhole step, for `c = ⌈R/(K-1)⌉`. -/
theorem ceil_spec {R K : ℕ} (hK : 2 ≤ K) (hR : 1 ≤ R) :
    1 ≤ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ ∧ (K - 1) * (⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ - 1) + 1 ≤ R := by
  have hK' : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hpos : 0 < (R : ℝ) / ((K : ℝ) - 1) := div_pos hR' hK'
  set c := ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ with hc
  have hc1 : 1 ≤ c := Nat.ceil_pos.2 hpos
  refine ⟨hc1, ?_⟩
  have hlt : (c : ℝ) < (R : ℝ) / ((K : ℝ) - 1) + 1 := Nat.ceil_lt_add_one hpos.le
  have h₁ : ((c : ℝ) - 1) * ((K : ℝ) - 1) < R := by
    rw [← lt_div_iff₀ hK']
    linarith
  have h₂ : (((K - 1) * (c - 1) : ℕ) : ℝ) < (R : ℕ) := by
    push_cast [Nat.cast_sub hc1, Nat.cast_sub (by omega : 1 ≤ K)]
    linarith
  have h₃ : (K - 1) * (c - 1) < R := by exact_mod_cast h₂
  omega

theorem card_filter_fin (R : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (univ.filter fun t : Fin R => p t).card = ((range R).filter p).card := by
  refine card_bij (fun t _ => (t : ℕ)) (fun t ht => ?_) (fun _ _ _ _ h => Fin.ext h)
    fun i hi => ?_
  · exact mem_filter.2 ⟨mem_range.2 t.2, (mem_filter.1 ht).2⟩
  · exact ⟨⟨i, mem_range.1 (mem_filter.1 hi).1⟩, mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2⟩,
      rfl⟩

section Step1

variable {N R K c : ℕ} {δ : ℕ → ℕ}

open Classical in
/-- **Step 1, conditioned on the other blocks.** Fix the indices `ω` of all blocks other than
`σ(v_m)`.  At most `d (d-1)^c d^(R-c)` choices `g` of the indices of `σ(v_m)` (`d = δ(m) ≥ 1`)
make `E_m` occur, if `c ≥ 1` and `(K-1)(c-1)+1 ≤ R`. -/
theorem card_fiber_evE_le (A : OnlineAlg) (I : OnlineInput N) (hc : 1 ≤ c)
    (hRc : (K - 1) * (c - 1) + 1 ≤ R) (m : Fin N) (hδ : δ m ≠ 0) (ω : Idx N R δ) :
    (univ.filter fun g : Fin R → Fin (δ m - 1 + 1) =>
      EvE K R c δ (idx δ (Function.update ω m g))
        (obCol A R I.seq (idx δ (Function.update ω m g))) m).card ≤
      (δ m - 1 + 1) * ((δ m - 1 + 1 - 1) ^ c * (δ m - 1 + 1) ^ (R - c)) := by
  set col₀ := obCol A R I.seq (idx δ ω) with hcol₀
  have hcol : ∀ g : Fin R → Fin (δ m - 1 + 1), ∀ i < ((m : ℕ) + 1) * R,
      obCol A R I.seq (idx δ (Function.update ω m g)) i = col₀ i := fun g =>
    obCol_congr I.seq_valid (fun _ _ => rfl)
      (fun w hw => idx_update_of_ne ω m g (Nat.ne_of_lt hw))
  by_cases hT : EvT K R col₀ m
  · have hempty : (univ.filter fun g : Fin R → Fin (δ m - 1 + 1) =>
        EvE K R c δ (idx δ (Function.update ω m g))
          (obCol A R I.seq (idx δ (Function.update ω m g))) m) = ∅ := by
      rw [filter_eq_empty_iff]
      intro g _ hE
      exact hE.1 ((evT_congr (hcol g)).2 hT)
    rw [hempty, card_empty]
    exact Nat.zero_le _
  · set S : Finset (Fin R) :=
      univ.filter fun t : Fin R => col₀ (m * R + t) = popCol R c col₀ m with hS
    have hSc : c ≤ S.card := by
      have h := popCol_spec (m := m) hc hRc hT
      rw [length_clsList] at h
      rw [hS, card_filter_fin R fun t => col₀ (m * R + t) = popCol R c col₀ m]
      exact h
    refine le_trans (card_le_card ?_) (card_miss_le S hSc)
    intro g hg
    have hE := (mem_filter.1 hg).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have hC := hE.2
    unfold EvC at hC
    push Not at hC
    obtain ⟨a, ha, hmiss⟩ := hC
    refine ⟨⟨a, by omega⟩, fun t ht hgt => ?_⟩
    have ht' : col₀ (m * R + t) = popCol R c col₀ m := (mem_filter.1 ht).2
    refine hmiss t t.2 ?_ ?_
    · rw [idx_update_self ω m g t hδ, hgt]
    · rw [hcol g _ (block_lt le_rfl t.2), popCol_congr (hcol g) le_rfl]
      exact ht'

open Classical in
/-- **Step 1.** `Pr(E_m) ≤ δ(m) (1 - 1/δ(m))^c`, as a count over the index families (for `K ≥ 2`,
`c ≥ 1` and `(K-1)(c-1)+1 ≤ R`). -/
theorem card_evE_le (A : OnlineAlg) (I : OnlineInput N) (hK : 2 ≤ K) (hc : 1 ≤ c)
    (hRc : (K - 1) * (c - 1) + 1 ≤ R) (m : Fin N) :
    ((univ.filter fun ω : Idx N R δ =>
      EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m).card : ℝ) ≤
      Fintype.card (Idx N R δ) * ((δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c) := by
  by_cases hδ : δ m = 0
  · have hempty : (univ.filter fun ω : Idx N R δ =>
        EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m) = ∅ := by
      rw [filter_eq_empty_iff]
      intro ω _ hE
      refine hE.2 fun a ha => ?_
      omega
    rw [hempty, card_empty, hδ]
    simp
  · have hcR : c ≤ R := by
      have : c - 1 ≤ (K - 1) * (c - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hd : δ m - 1 + 1 = δ m := by omega
    have key := card_filter_mul_le (β := fun m : Fin N => Fin R → Fin (δ m - 1 + 1)) m
      (fun ω : Idx N R δ => EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m) _
      (card_fiber_evE_le A I hc hRc m hδ)
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at key
    have key' := (Nat.cast_le (α := ℝ)).2 key
    rw [Nat.cast_mul, Nat.cast_mul, miss_fraction (by omega) hcR, Nat.cast_pow, hd] at key'
    have hpos : (0 : ℝ) < (δ m : ℝ) ^ R := by
      have : (0 : ℝ) < δ m := by exact_mod_cast Nat.pos_of_ne_zero hδ
      positivity
    refine le_of_mul_le_mul_right ?_ hpos
    calc _ ≤ _ := key'
      _ = _ := by ring

open Classical in
/-- **Step 1 and the union bound.** Under (c) with the exponent `c`, `Pr(⋃_m E_m) ≤ ε`, as a count
(same conditions on `K`, `c` and `R`). -/
theorem card_exists_evE_le (A : OnlineAlg) (I : OnlineInput N) (hK : 2 ≤ K) (hc : 1 ≤ c)
    (hRc : (K - 1) * (c - 1) + 1 ≤ R) {ε : ℝ}
    (hsum : ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c ≤ ε) :
    ((univ.filter fun ω : Idx N R δ =>
      ∃ m < N, EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m).card : ℝ) ≤
      Fintype.card (Idx N R δ) * ε := by
  have hsub : (univ.filter fun ω : Idx N R δ =>
      ∃ m < N, EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m) ⊆
      (univ : Finset (Fin N)).biUnion fun m => univ.filter fun ω : Idx N R δ =>
        EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m := by
    intro ω hω
    obtain ⟨m, hm, hE⟩ := (mem_filter.1 hω).2
    exact mem_biUnion.2 ⟨⟨m, hm⟩, mem_univ _, mem_filter.2 ⟨mem_univ _, hE⟩⟩
  have h₁ := (card_le_card hsub).trans card_biUnion_le
  have h₂ := (Nat.cast_le (α := ℝ)).2 h₁
  rw [Nat.cast_sum] at h₂
  have hcard : (0 : ℝ) ≤ Fintype.card (Idx N R δ) := Nat.cast_nonneg _
  calc _ ≤ _ := h₂
    _ ≤ ∑ m : Fin N, (Fintype.card (Idx N R δ) : ℝ) *
          ((δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c) :=
        sum_le_sum fun m _ => card_evE_le A I hK hc hRc m
    _ = Fintype.card (Idx N R δ) * ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c := by
        rw [← mul_sum, Fin.sum_univ_eq_sum_range fun m => (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hcard

open Classical in
/-- **Steps 1–3 for one inner graph.** Let `A` be proper, `K ≥ 2`, `c ≥ 1`, `(K-1)(c-1)+1 ≤ R` and
`∑_{m<N} δ(m) (1 - 1/δ(m))^c ≤ ε`.  If the post-degrees of `I` are at most `δ`, the number of
index families for which the simulated algorithm uses at least `K` colours on `I` is at most the
number of those for which `A` uses at least `K` colours on the outcome, plus `ε |Idx|`. -/
theorem card_sim_le {A : OnlineAlg} (hA : A.IsProper) (I : OnlineInput N) (hK : 2 ≤ K)
    (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R)
    (hdeg : ∀ w < N, postDeg I.seq N w ≤ δ w) {ε : ℝ}
    (hsum : ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ c ≤ ε) :
    ((univ.filter fun ω : Idx N R δ => K ≤ I.cost (simAlgP A K R c δ (idx δ ω))).card : ℝ) ≤
      (univ.filter fun ω : Idx N R δ => K ≤ (obInput R δ I ω).cost A).card +
        Fintype.card (Idx N R δ) * ε := by
  have hsub : (univ.filter fun ω : Idx N R δ => K ≤ I.cost (simAlgP A K R c δ (idx δ ω))) ⊆
      (univ.filter fun ω : Idx N R δ => K ≤ (obInput R δ I ω).cost A) ∪
        univ.filter fun ω : Idx N R δ =>
          ∃ m < N, EvE K R c δ (idx δ ω) (obCol A R I.seq (idx δ ω)) m := by
    intro ω hω
    have h := (mem_filter.1 hω).2
    rw [cost_eq_colsOn] at h
    have e : colsOn (simAlgP A K R c δ (idx δ ω)) I.seq N =
        colsOn (simAlg A K R c δ (idx δ ω)) I.seq N := by
      unfold colsOn
      rw [image_congr fun i _ => runCol_simAlgP hA hc hRc I.seq_valid i]
    rw [e] at h
    rcases comparison' hc hRc I.seq_valid hdeg h with h' | h'
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, by rwa [cost_obInput]⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h'⟩)
  have h₁ := (card_le_card hsub).trans (card_union_le _ _)
  have h₂ := (Nat.cast_le (α := ℝ)).2 h₁
  rw [Nat.cast_add] at h₂
  have h₃ := card_exists_evE_le A I hK hc hRc hsum
  linarith

end Step1

/-! ### Lemma C.2, second conclusion: forcing -/

theorem probAtLeast_le_one {N : ℕ} (D : PMF (OnlineInput N)) (A : OnlineAlg) (K : ℕ) :
    probAtLeast D A K ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (toOuterMeasure_le_one D {I | K ≤ I.cost A})
  simpa [probAtLeast] using h

/-- The algorithm that always answers `0`, patched to be proper. -/
def zeroAlg : OnlineAlg := (⟨fun _ _ => 0⟩ : OnlineAlg).patch

/-- On an input without edges, `zeroAlg` uses at most one colour. -/
theorem cost_zeroAlg_le {N : ℕ} (I : OnlineInput N) (hI : ∀ i, I.seq i = ∅) :
    I.cost zeroAlg ≤ 1 := by
  have hrun : ∀ i, runCol zeroAlg I.seq i = 0 := fun i =>
    runCol_patch_of_proper (A := ⟨fun _ _ => 0⟩) I.seq_valid
      (fun i l hl => by rw [hI i] at hl; simp at hl) i
  rw [cost_eq_colsOn]
  unfold colsOn
  calc ((range N).image (runCol zeroAlg I.seq)).card ≤ ({0} : Finset ℕ).card := by
        apply card_le_card
        intro x hx
        obtain ⟨i, -, rfl⟩ := mem_image.1 hx
        rw [hrun i]
        exact mem_singleton_self 0
    _ = 1 := card_singleton 0

/-- If all post-degree bounds are `0`, no algorithm-independent forcing is possible: `ρ ≤ 0`. -/
theorem rho_nonpos_of_delta_zero {N K : ℕ} {δ : ℕ → ℕ} (𝓗 : PMF (OnlineInput N)) (hK : 2 ≤ K)
    {ρ : ℝ} (hδ : ∀ I ∈ 𝓗.support, ∀ m < N, postDeg I.seq N m ≤ δ m)
    (hb : ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K) (h0 : ∀ m < N, δ m = 0) :
    ρ ≤ 0 := by
  have h := hb zeroAlg (OnlineAlg.patch_isProper _)
  have hz : 𝓗.toOuterMeasure {I | K ≤ I.cost zeroAlg} = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro I hI hcost
    have hseq : ∀ i, I.seq i = ∅ := by
      intro i
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      have hi : i < N := lt_of_mem_seq hw
      have hwi : w < i := mem_range.1 (I.seq_valid i hw)
      have h₁ : rank I.seq w i < rank I.seq w N := rank_lt_rank hi hw
      have h₂ := hδ I hI w (by omega)
      rw [h0 w (by omega)] at h₂
      change rank I.seq w N ≤ 0 at h₂
      omega
    have := cost_zeroAlg_le I hseq
    have hcost' : K ≤ I.cost zeroAlg := hcost
    omega
  unfold probAtLeast at h
  rw [hz] at h
  simpa using h

/-- **Lemma C.2, second conclusion.** Let `K ≥ 2`.  Suppose that `δ` bounds the post-degrees on
the support of `ℋ`, that (b) every proper deterministic online algorithm uses at least `K` colours
on `I ∼ ℋ` with probability at least `ρ`, and that
(c) `∑_{m<N} δ(m) (1 - 1/δ(m))^⌈R/(K-1)⌉ ≤ ε`.  Then every proper deterministic online algorithm
uses at least `K` colours on `OB_R(ℋ)` with probability at least `ρ - ε`. -/
theorem oblivious_blowup_forcing {N R K : ℕ} {δ : ℕ → ℕ} (𝓗 : PMF (OnlineInput N))
    (hK : 2 ≤ K) {ρ ε : ℝ}
    (hδ : ∀ I ∈ 𝓗.support, ∀ m < N, postDeg I.seq N m ≤ δ m)
    (hb : ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K)
    (hc : ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ ≤ ε) :
    ∀ A : OnlineAlg, A.IsProper → ρ - ε ≤ probAtLeast (OB R δ 𝓗) A K := by
  intro A hA
  have hterm : ∀ m, 0 ≤ (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ := by
    intro m
    rcases Nat.eq_zero_or_pos (δ m) with h | h
    · rw [h]; simp
    · have h1 : (1 : ℝ) ≤ δ m := by exact_mod_cast h
      have : 0 ≤ 1 - 1 / (δ m : ℝ) := by
        rw [sub_nonneg, div_le_one (by linarith)]
        exact h1
      positivity
  have hε : 0 ≤ ε := (sum_nonneg fun m _ => hterm m).trans hc
  rcases Nat.eq_zero_or_pos R with hR | hR
  · -- blocks of size `0`: the hypotheses give `ρ ≤ ε`
    have hρε : ρ ≤ ε := by
      by_cases h0 : ∀ m < N, δ m = 0
      · exact (rho_nonpos_of_delta_zero 𝓗 hK hδ hb h0).trans hε
      · push Not at h0
        obtain ⟨m, hm, hm0⟩ := h0
        have h1 : (1 : ℝ) ≤ δ m := by exact_mod_cast Nat.pos_of_ne_zero hm0
        have h2 := single_le_sum (fun m _ => hterm m) (mem_range.2 hm)
        rw [hR] at h2 hc
        simp only [Nat.cast_zero, zero_div, Nat.ceil_zero, pow_zero, mul_one] at h2 hc
        have h3 := (hb _ OnlineAlg.firstFit_isProper).trans (probAtLeast_le_one 𝓗 _ K)
        linarith
    have := probAtLeast_nonneg (OB R δ 𝓗) A K
    linarith
  · obtain ⟨hc1, hRc⟩ := ceil_spec hK hR
    exact mix_bound 𝓗 (obInput R δ) (fun J => K ≤ J.cost A)
      (fun ω I => K ≤ I.cost (simAlgP A K R ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ δ (idx δ ω))) hε
      (fun ω => hb _ (simAlgP_isProper _ _ _ _ _ _))
      (fun I hI => by convert card_sim_le hA I hK hc1 hRc (hδ I hI) hc)

/-- **Lemma C.2 (forcing survives an oblivious blow-up).** Let `K ≥ 2`, let `ℋ` be a distribution
over ordered graphs on exactly `N` vertices whose post-degrees are bounded by the position-only
function `δ`, and suppose that
(a) every `I` in the support of `ℋ` maps to `T(J*(P))`;
(b) every proper deterministic online algorithm uses at least `K` colours on `I ∼ ℋ` with
probability at least `ρ`;
(c) `∑_{m<N} δ(m) (1 - 1/δ(m))^⌈R/(K-1)⌉ ≤ ε` (terms with `δ(m) = 0` are `0`).
Then every graph in the support of `OB_R(ℋ)` maps to `T(P)`, and every proper deterministic online
algorithm uses at least `K` colours on `OB_R(ℋ)` with probability at least `ρ - ε`. -/
theorem oblivious_blowup {N R K : ℕ} {δ : ℕ → ℕ} (𝓗 : PMF (OnlineInput N))
    {P : Type*} [PartialOrder P] (hK : 2 ≤ K) {ρ ε : ℝ}
    (hδ : ∀ I ∈ 𝓗.support, ∀ m < N, postDeg I.seq N m ≤ δ m)
    (ha : ∀ I ∈ 𝓗.support, HasLabelling I.graph (Jst P))
    (hb : ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K)
    (hc : ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ ≤ ε) :
    (∀ J ∈ (OB R δ 𝓗).support, HasLabelling J.graph P) ∧
      ∀ A : OnlineAlg, A.IsProper → ρ - ε ≤ probAtLeast (OB R δ 𝓗) A K :=
  ⟨oblivious_blowup_labelling 𝓗 ha, oblivious_blowup_forcing 𝓗 hK hδ hb hc⟩

/-! ### The sufficient condition for (c) -/

/-- **The remark after Lemma C.2.** Condition (c) holds if `N D exp(-R/((K-1)D)) ≤ ε` and
`δ(m) ≤ D` for all `m < N`.  `D = 0` is allowed; it is the case of the remark in which every `δ(m)`
is `0`. -/
theorem cond_c_of_weak {N R K D : ℕ} {δ : ℕ → ℕ} (hK : 2 ≤ K) (hD : ∀ m < N, δ m ≤ D) {ε : ℝ}
    (h : (N : ℝ) * D * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D)) ≤ ε) :
    ∑ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ ≤ ε := by
  have hK' : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hr0 : (0 : ℝ) ≤ (R : ℝ) / ((K : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hK'.le
  have hterm : ∀ m ∈ range N, (δ m : ℝ) * (1 - 1 / (δ m : ℝ)) ^ ⌈(R : ℝ) / ((K : ℝ) - 1)⌉₊ ≤
      D * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D)) := by
    intro m hm
    have hmD : (δ m : ℝ) ≤ D := by exact_mod_cast hD m (mem_range.1 hm)
    have e : -(R : ℝ) / (((K : ℝ) - 1) * D) = -((R : ℝ) / ((K : ℝ) - 1) / D) := by
      rw [div_div, neg_div]
    rw [e]
    rcases Nat.eq_zero_or_pos (δ m) with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, zero_mul]
      positivity
    · exact weak_term_le (by exact_mod_cast h0) hmD hr0 (Nat.le_ceil _)
  calc _ ≤ ∑ _m ∈ range N, (D : ℝ) * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D)) :=
        sum_le_sum hterm
    _ = (N : ℝ) * D * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D)) := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]
    _ ≤ ε := h

end Obl

end OnlineColouring
