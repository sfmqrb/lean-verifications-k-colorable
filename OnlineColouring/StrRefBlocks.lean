module

public import OnlineColouring.Structure

/-!
# Blow-ups with blocks of variable size, as input sequences

The adversary `𝒜'` of Proposition B.1 (Appendix B) uses reservation blow-ups in which the size of
a block depends on the node ("every block of a node of level `ℓ` below `v_t` has `b_ℓ(t)`
nodes").  This file is the static part: `SeqBlowUp.lean` for blocks of variable size.

Let `bs : ℕ → ℕ` give the block sizes (`bs v > 0` is the size of the block of the inner vertex
`v`).  The blocks are laid out one after the other: the block of `v` consists of the positions
`off bs v, …, off bs v + bs v - 1`, where `off bs v = ∑_{u < v} bs u`, and `blk bs p` is the inner
vertex whose block contains the position `p`.  For blocks of constant size `R` these are `v * R`
and `p / R` (`off_const`, `blk_const`).

* `gBlowSeq bs H σ`: the blow-up of the input sequence `H`; the arc `w → v` (`w ∈ H v`) is served
  by the vertex in position `σ w (rank H w v)` of the block of `w`, and every vertex of the block of
  `v` has exactly the servers of the arcs into `v` as earlier neighbours.  For constant `bs` it is
  `blowSeq` (`gBlowSeq_const`).
* `gBlowSeq_valid`, `gblock_eq_of_mem` (a vertex serves at most one block), `gBlowUpOf` (the first
  `off bs m` vertices form a `BlowUp` of the first `m` vertices of `H`, provided the inner vertex
  `w` has post-degree at most `bs w`), `postDeg_gBlowSeq_le` (the post-degree of a vertex is at
  most the size of the one block it serves).
-/

@[expose] public section

namespace OnlineColouring.Str

open Finset

/-! ### Offsets and blocks -/

/-- `off bs v`: the number of vertices in the blocks of the inner vertices `0, …, v-1`.  The block
of `v` consists of the positions `off bs v, …, off bs v + bs v - 1`. -/
def off (bs : ℕ → ℕ) (v : ℕ) : ℕ := ∑ u ∈ range v, bs u

/-- `blk bs p`: the inner vertex whose block contains the position `p`. -/
def blk (bs : ℕ → ℕ) (p : ℕ) : ℕ := Nat.findGreatest (fun v => off bs v ≤ p) p

@[simp] theorem off_zero (bs : ℕ → ℕ) : off bs 0 = 0 := by simp [off]

theorem off_succ (bs : ℕ → ℕ) (v : ℕ) : off bs (v + 1) = off bs v + bs v :=
  sum_range_succ _ _

theorem off_mono (bs : ℕ → ℕ) {v v' : ℕ} (h : v ≤ v') : off bs v ≤ off bs v' := by
  induction v', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    rw [off_succ]
    omega

theorem off_add (bs : ℕ → ℕ) (a n : ℕ) :
    off bs (a + n) = off bs a + ∑ r ∈ range n, bs (a + r) :=
  sum_range_add _ _ _

theorem off_blk_le (bs : ℕ → ℕ) (p : ℕ) : off bs (blk bs p) ≤ p :=
  Nat.findGreatest_spec (P := fun v => off bs v ≤ p) (Nat.zero_le p) (by simp)

section Blocks

variable {bs : ℕ → ℕ}

theorem le_off (hbs : ∀ v, 0 < bs v) (v : ℕ) : v ≤ off bs v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [off_succ]
    have := hbs v
    omega

theorem lt_off_blk_succ (hbs : ∀ v, 0 < bs v) (p : ℕ) : p < off bs (blk bs p + 1) := by
  by_contra h
  rw [not_lt] at h
  have h1 : blk bs p + 1 ≤ p := (le_off hbs _).trans h
  have h2 : blk bs p + 1 ≤ blk bs p :=
    Nat.le_findGreatest (P := fun v => off bs v ≤ p) h1 h
  omega

theorem blk_lt_iff (hbs : ∀ v, 0 < bs v) {p v : ℕ} : blk bs p < v ↔ p < off bs v := by
  constructor
  · intro h
    exact (lt_off_blk_succ hbs p).trans_le (off_mono bs h)
  · intro h
    by_contra hle
    rw [not_lt] at hle
    exact absurd ((off_mono bs hle).trans (off_blk_le bs p)) (not_le.2 h)

theorem le_blk_iff (hbs : ∀ v, 0 < bs v) {p v : ℕ} : v ≤ blk bs p ↔ off bs v ≤ p := by
  rw [← not_lt, blk_lt_iff hbs, not_lt]

theorem blk_eq (hbs : ∀ v, 0 < bs v) {p v : ℕ} (h1 : off bs v ≤ p) (h2 : p < off bs (v + 1)) :
    blk bs p = v :=
  le_antisymm (Nat.lt_succ_iff.1 ((blk_lt_iff hbs).2 h2)) ((le_blk_iff hbs).2 h1)

theorem blk_off_add (hbs : ∀ v, 0 < bs v) {v r : ℕ} (hr : r < bs v) :
    blk bs (off bs v + r) = v :=
  blk_eq hbs (Nat.le_add_right _ _) (by rw [off_succ]; omega)

theorem blk_off (hbs : ∀ v, 0 < bs v) (v : ℕ) : blk bs (off bs v) = v :=
  blk_off_add hbs (hbs v)

/-- The position of `p` inside its block. -/
theorem sub_off_blk_lt (hbs : ∀ v, 0 < bs v) (p : ℕ) : p - off bs (blk bs p) < bs (blk bs p) := by
  have h1 := lt_off_blk_succ hbs p
  rw [off_succ] at h1
  have h2 := off_blk_le bs p
  omega

theorem off_lt_off (hbs : ∀ v, 0 < bs v) {v v' : ℕ} (h : v < v') : off bs v < off bs v' := by
  have h1 := off_mono bs (Nat.succ_le_of_lt h)
  rw [off_succ] at h1
  have := hbs v
  omega

end Blocks

theorem off_const (R v : ℕ) : off (fun _ => R) v = v * R := by
  simp [off]

theorem blk_const {R : ℕ} (hR : 0 < R) (p : ℕ) : blk (fun _ => R) p = p / R := by
  apply blk_eq (fun _ => hR)
  · rw [off_const]
    exact Nat.div_mul_le_self p R
  · rw [off_const, Nat.succ_mul]
    exact Nat.lt_div_mul_add hR

/-! ### The blow-up sequence -/

/-- `σ` gives, for every block, distinct positions inside the block. -/
structure GPerm (bs : ℕ → ℕ) (σ : ℕ → ℕ → ℕ) : Prop where
  lt : ∀ w t, σ w t < bs w
  inj : ∀ w t t', t < bs w → t' < bs w → σ w t = σ w t' → t = t'

/-- The blow-up of `H` with blocks of sizes `bs`: the vertex `p` lies in the block of `blk bs p`,
and its earlier neighbours are the servers `off bs w + σ w (rank H w (blk bs p))` of the arcs
`w → blk bs p`. -/
def gBlowSeq (bs : ℕ → ℕ) (H : ℕ → Finset ℕ) (σ : ℕ → ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (H (blk bs p)).image fun w => off bs w + σ w (rank H w (blk bs p))

/-- For blocks of constant size this is `blowSeq`. -/
theorem gBlowSeq_const {R : ℕ} (hR : 0 < R) (H : ℕ → Finset ℕ) (σ : ℕ → ℕ → ℕ) :
    gBlowSeq (fun _ => R) H σ = blowSeq R H σ := by
  funext p
  unfold gBlowSeq blowSeq
  rw [blk_const hR]
  simp only [off_const]

section Seq

variable {bs : ℕ → ℕ} {H : ℕ → Finset ℕ} {σ : ℕ → ℕ → ℕ}

theorem mem_gBlowSeq (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ) {x p : ℕ} :
    x ∈ gBlowSeq bs H σ p ↔ blk bs x ∈ H (blk bs p) ∧
      x = off bs (blk bs x) + σ (blk bs x) (rank H (blk bs x) (blk bs p)) := by
  unfold gBlowSeq
  simp only [mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [blk_off_add hbs (hσ.lt _ _)]
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, hx⟩
    exact ⟨blk bs x, hw, hx.symm⟩

/-- The earlier neighbours of a vertex depend only on its block. -/
theorem gBlowSeq_off_blk (hbs : ∀ v, 0 < bs v) (p : ℕ) :
    gBlowSeq bs H σ (off bs (blk bs p)) = gBlowSeq bs H σ p := by
  unfold gBlowSeq
  rw [blk_off hbs]

theorem gBlowSeq_congr_σ {σ' : ℕ → ℕ → ℕ} {p : ℕ} (h : ∀ w ∈ H (blk bs p), σ w = σ' w) :
    gBlowSeq bs H σ p = gBlowSeq bs H σ' p := by
  unfold gBlowSeq
  apply Finset.image_congr
  intro w hw
  simp only [h w (Finset.mem_coe.1 hw)]

theorem lt_of_mem_gBlowSeq (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ) {x p : ℕ}
    (hx : x ∈ gBlowSeq bs H σ p) : x < p := by
  obtain ⟨hw, -⟩ := (mem_gBlowSeq hbs hσ).1 hx
  have h₁ : blk bs x < blk bs p := mem_range.1 (hH _ hw)
  exact ((blk_lt_iff hbs).1 h₁).trans_le (off_blk_le bs p)

theorem gBlowSeq_valid (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ) :
    ValidSeq (gBlowSeq bs H σ) :=
  fun _ _ hx => mem_range.2 (lt_of_mem_gBlowSeq hH hbs hσ hx)

/-- A vertex serves at most one block among the first `m`. -/
theorem gblock_eq_of_mem (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ) {m : ℕ}
    (hdeg : ∀ w < m, postDeg H m w ≤ bs w) {x p₁ p₂ : ℕ}
    (hx₁ : x ∈ gBlowSeq bs H σ p₁) (hx₂ : x ∈ gBlowSeq bs H σ p₂) (h₁ : blk bs p₁ < m)
    (h₂ : blk bs p₂ < m) : blk bs p₁ = blk bs p₂ := by
  obtain ⟨hw₁, hx₁⟩ := (mem_gBlowSeq hbs hσ).1 hx₁
  obtain ⟨hw₂, hx₂⟩ := (mem_gBlowSeq hbs hσ).1 hx₂
  set w := blk bs x
  have hwm : w < m := (mem_range.1 (hH _ hw₁)).trans h₁
  have hr₁ : rank H w (blk bs p₁) < bs w := (rank_lt_rank h₁ hw₁).trans_le (hdeg w hwm)
  have hr₂ : rank H w (blk bs p₂) < bs w := (rank_lt_rank h₂ hw₂).trans_le (hdeg w hwm)
  have hσeq : σ w (rank H w (blk bs p₁)) = σ w (rank H w (blk bs p₂)) := by omega
  exact rank_inj hw₁ hw₂ (hσ.inj w _ _ hr₁ hr₂ hσeq)

/-- **Post-degrees in the blow-up.**  A vertex `x` has later neighbours in at most one block, so
its post-degree is at most `dd` if every block served from the block of `x` has at most `dd`
vertices. -/
theorem postDeg_gBlowSeq_le (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ) {m : ℕ}
    (hdeg : ∀ w < m, postDeg H m w ≤ bs w) {x dd : ℕ}
    (hdd : ∀ v < m, blk bs x ∈ H v → bs v ≤ dd) :
    postDeg (gBlowSeq bs H σ) (off bs m) x ≤ dd := by
  unfold postDeg rank
  set S := (range (off bs m)).filter fun u => x ∈ gBlowSeq bs H σ u
  rcases S.eq_empty_or_nonempty with hS | ⟨u₀, hu₀⟩
  · rw [hS, card_empty]
    exact Nat.zero_le _
  · have hu₀' := mem_filter.1 hu₀
    have hv₀ : blk bs u₀ < m := (blk_lt_iff hbs).2 (mem_range.1 hu₀'.1)
    have hsub : S ⊆ Ico (off bs (blk bs u₀)) (off bs (blk bs u₀ + 1)) := by
      intro u hu
      have hu' := mem_filter.1 hu
      have e := gblock_eq_of_mem hH hbs hσ hdeg hu'.2 hu₀'.2
        ((blk_lt_iff hbs).2 (mem_range.1 hu'.1)) hv₀
      rw [mem_Ico, ← e]
      exact ⟨off_blk_le bs u, lt_off_blk_succ hbs u⟩
    calc S.card ≤ (Ico (off bs (blk bs u₀)) (off bs (blk bs u₀ + 1))).card := card_le_card hsub
      _ = bs (blk bs u₀) := by simp [off_succ]
      _ ≤ dd := hdd _ hv₀ ((mem_gBlowSeq hbs hσ).1 hu₀'.2).1

end Seq

/-! ### The blow-up structure -/

section BlowUpOf

variable {bs : ℕ → ℕ} {H : ℕ → Finset ℕ} {σ : ℕ → ℕ → ℕ} {m : ℕ}

/-- The block map of the blow-up. -/
def gBlockMap (hbs : ∀ v, 0 < bs v) (m : ℕ) (x : Fin (off bs m)) : Fin m :=
  ⟨blk bs x, (blk_lt_iff hbs).2 x.2⟩

open Classical in
/-- The serve map of the blow-up: `x` serves the arc into `v` iff `x` is an earlier neighbour of
the first vertex `off bs v` of the block of `v`. -/
noncomputable def gServeMap (bs : ℕ → ℕ) (H : ℕ → Finset ℕ) (σ : ℕ → ℕ → ℕ) (m : ℕ)
    (x : Fin (off bs m)) : Option (Fin m) :=
  if h : ∃ v : Fin m, (x : ℕ) ∈ gBlowSeq bs H σ (off bs v) then some h.choose else none

theorem gServeMap_eq_some (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ bs w) {x : Fin (off bs m)} {v : Fin m} :
    gServeMap bs H σ m x = some v ↔ (x : ℕ) ∈ gBlowSeq bs H σ (off bs v) := by
  classical
  unfold gServeMap
  constructor
  · intro hs
    split_ifs at hs with h
    · cases hs
      exact h.choose_spec
  · intro hx
    have h : ∃ v : Fin m, (x : ℕ) ∈ gBlowSeq bs H σ (off bs v) := ⟨v, hx⟩
    rw [dite_eq_left_of_eq_true (eq_true h)]
    congr 1
    apply Fin.ext
    have e := gblock_eq_of_mem hH hbs hσ hdeg h.choose_spec hx
      (by rw [blk_off hbs]; exact h.choose.2) (by rw [blk_off hbs]; exact v.2)
    rwa [blk_off hbs, blk_off hbs] at e

theorem mem_gBlowSeq_iff_gServeMap (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ bs w) (x u : Fin (off bs m)) :
    (x : ℕ) ∈ gBlowSeq bs H σ u ↔ gServeMap bs H σ m x = some (gBlockMap hbs m u) := by
  rw [gServeMap_eq_some hH hbs hσ hdeg]
  change _ ↔ (x : ℕ) ∈ gBlowSeq bs H σ (off bs (blk bs u))
  rw [gBlowSeq_off_blk hbs]

/-- The first `off bs m` vertices of `gBlowSeq bs H σ` form a blow-up of the first `m` vertices of
`H` (Definition 4.6), for all positive block sizes `bs` and all `σ` with `GPerm bs σ`, provided
every inner vertex `w < m` has post-degree at most `bs w`. -/
noncomputable def gBlowUpOf (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) (hσ : GPerm bs σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ bs w) :
    BlowUp (OnlineInput.ofSeq H hH m).graph
      (OnlineInput.ofSeq (gBlowSeq bs H σ) (gBlowSeq_valid hH hbs hσ) (off bs m)).graph where
  π := gBlockMap hbs m
  serve := gServeMap bs H σ m
  π_surjective v := ⟨⟨off bs v, off_lt_off hbs v.2⟩, Fin.ext (blk_off hbs v)⟩
  lt_of_π_lt x y h := by
    have h' : blk bs x < blk bs y := Fin.lt_def.1 h
    exact Fin.lt_def.2 (((blk_lt_iff hbs).1 h').trans_le (off_blk_le bs y))
  serve_spec x v h := by
    have hx := (gServeMap_eq_some hH hbs hσ hdeg).1 h
    obtain ⟨hw, -⟩ := (mem_gBlowSeq hbs hσ).1 hx
    rw [blk_off hbs] at hw
    exact ⟨Fin.lt_def.2 (mem_range.1 (hH _ hw)), OnlineInput.ofSeq_adj.2 (Or.inl hw)⟩
  adj_iff x u := by
    rw [OnlineInput.ofSeq_adj, mem_gBlowSeq_iff_gServeMap hH hbs hσ hdeg,
      mem_gBlowSeq_iff_gServeMap hH hbs hσ hdeg]
    constructor
    · rintro (h | h)
      · refine Or.inl ⟨?_, h⟩
        have := (mem_gBlowSeq_iff_gServeMap hH hbs hσ hdeg x u).2 h
        exact Fin.lt_def.2 (lt_of_mem_gBlowSeq hH hbs hσ this)
      · refine Or.inr ⟨?_, h⟩
        have := (mem_gBlowSeq_iff_gServeMap hH hbs hσ hdeg u x).2 h
        exact Fin.lt_def.2 (lt_of_mem_gBlowSeq hH hbs hσ this)
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h

end BlowUpOf

end OnlineColouring.Str
