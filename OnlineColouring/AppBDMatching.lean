module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A matching that covers all tight rows and columns (Kőnig's edge-colouring theorem, as used in
# Theorem D.2)

Appendix D.2, step (a) of the flow adversary of Theorem D.2: *It views `Y_t`
as a bipartite multigraph of maximum degree at most `W_t`, which by Kőnig's edge-colouring theorem
splits into `W_t` matchings, each covering every tight row and column.  It plays a matching `M_t`
of at most average size, `|M_t| ≤ |Y_t| / W_t`.*

Only the consequence is needed: a matching in the support of `Y` that covers every tight row and
every tight column and has at most `|Y| / W` edges.  We derive it from the Birkhoff–von Neumann
theorem of Mathlib instead of Kőnig's theorem: the matrix `[[D_r, Y], [Yᵀ, D_c]] / W`, where `D_r`
and `D_c` are the diagonal matrices of the row and column deficits, is doubly stochastic, hence a
convex combination of permutation matrices; every permutation of positive weight gives a matching
of the required kind, and their average size is `|Y| / W`.

* `exists_matching_matrix`: the statement for a matrix `Y : β → γ → ℕ`.
* `exists_matching`: the statement for a finite multiset of edges, given as a finite set `R` with
  two maps `f` (row) and `g` (column).
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

section MatrixForm

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

/-- The square matrix `[[D_r, Y], [Yᵀ, D_c]]` with all row and column sums equal to `W`. -/
def auxMatrix (Y : β → γ → ℕ) (W : ℕ) : Matrix (β ⊕ γ) (β ⊕ γ) ℝ := fun i j =>
  match i, j with
  | .inl b, .inr c => Y b c
  | .inl b, .inl b' => if b = b' then (W : ℝ) - ∑ c, (Y b c : ℝ) else 0
  | .inr c, .inr c' => if c = c' then (W : ℝ) - ∑ b, (Y b c : ℝ) else 0
  | .inr c, .inl b => Y b c

end MatrixForm

/-- The matrix form: a nonnegative integer matrix with row and column sums at most `W`, `W ≥ 1`,
has a matching in its support that covers every tight row and column and has at most `|Y| / W`
entries. -/
theorem exists_matching_matrix {β γ : Type*} [Fintype β] [Fintype γ]
    (Y : β → γ → ℕ) {W : ℕ} (hW : 0 < W)
    (hr : ∀ b, ∑ c, Y b c ≤ W) (hc : ∀ c, ∑ b, Y b c ≤ W) :
    ∃ M : Finset (β × γ), (∀ p ∈ M, 0 < Y p.1 p.2) ∧
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q) ∧
      (∀ b, ∑ c, Y b c = W → ∃ p ∈ M, p.1 = b) ∧ (∀ c, ∑ b, Y b c = W → ∃ p ∈ M, p.2 = c) ∧
      W * M.card ≤ ∑ b, ∑ c, Y b c := by
  classical
  set A := auxMatrix Y W with hA
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hrR : ∀ b, ∑ c, (Y b c : ℝ) ≤ W := fun b => by exact_mod_cast hr b
  have hcR : ∀ c, ∑ b, (Y b c : ℝ) ≤ W := fun c => by exact_mod_cast hc c
  have hA0 : ∀ i j, 0 ≤ A i j := by
    rintro (b | c) (b' | c') <;> simp only [hA, auxMatrix]
    · split_ifs
      · linarith [hrR b]
      · exact le_rfl
    · positivity
    · positivity
    · split_ifs
      · linarith [hcR c]
      · exact le_rfl
  have hrow : ∀ i, ∑ j, A i j = W := by
    rintro (b | c) <;> simp [hA, auxMatrix, Fintype.sum_sum_type]
  have hcol : ∀ j, ∑ i, A i j = W := by
    rintro (b | c) <;> simp [hA, auxMatrix, Fintype.sum_sum_type]
  have hDS : (W : ℝ)⁻¹ • A ∈ doublyStochastic ℝ (β ⊕ γ) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hWr.le) (hA0 i j)
    · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow]
      exact inv_mul_cancel₀ hWr.ne'
    · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hcol]
      exact inv_mul_cancel₀ hWr.ne'
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hDS
  have hentry : ∀ i j, ∑ σ : Equiv.Perm (β ⊕ γ), w σ * (if σ i = j then 1 else 0)
      = (W : ℝ)⁻¹ * A i j := by
    intro i j
    have := congrFun (congrFun hw i) j
    simpa [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, eq_comm] using this
  let Mσ : Equiv.Perm (β ⊕ γ) → Finset (β × γ) := fun σ =>
    univ.filter fun p => σ (.inl p.1) = .inr p.2
  have hcard : ∀ σ, ((Mσ σ).card : ℝ)
      = ∑ b, ∑ c, (if σ (.inl b) = .inr c then (1 : ℝ) else 0) := by
    intro σ
    simp only [Mσ, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Fintype.sum_prod_type]
  set S : ℝ := ∑ b, ∑ c, (Y b c : ℝ) with hS
  have h1 : ∑ σ, w σ * ((Mσ σ).card : ℝ) = (W : ℝ)⁻¹ * S := by
    simp only [hcard, Finset.mul_sum, hS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hentry (.inl b) (.inr c)]
    rfl
  have havg : ∑ σ, ((W : ℝ) * (w σ * (Mσ σ).card) - w σ * S) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1, hw1]
    field_simp
    ring
  obtain ⟨σ, hσ, hσS⟩ : ∃ σ, 0 < w σ ∧ (W : ℝ) * (Mσ σ).card ≤ S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, 0 < w σ₀ := by
      by_contra h0
      push Not at h0
      have : ∑ σ, w σ = 0 :=
        Finset.sum_eq_zero fun σ _ => le_antisymm (h0 σ) (hw0 σ)
      rw [hw1] at this
      exact one_ne_zero this
    have hpos : 0 < ∑ σ, ((W : ℝ) * (w σ * (Mσ σ).card) - w σ * S) := by
      refine Finset.sum_pos' (fun σ _ => ?_) ⟨σ₀, mem_univ _, ?_⟩
      · rcases (hw0 σ).eq_or_lt with h | h
        · simp [← h]
        · nlinarith [hcon σ h]
      · nlinarith [hcon σ₀ hσ₀]
    linarith
  have hpos : ∀ i, 0 < A i (σ i) := by
    intro i
    have h := hentry i (σ i)
    have h2 : w σ * (if σ i = σ i then (1 : ℝ) else 0)
        ≤ ∑ τ : Equiv.Perm (β ⊕ γ), w τ * (if τ i = σ i then 1 else 0) :=
      Finset.single_le_sum (f := fun τ : Equiv.Perm (β ⊕ γ) => w τ * (if τ i = σ i then 1 else 0))
        (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (mem_univ σ)
    rw [h] at h2
    simp only [↓reduceIte, mul_one] at h2
    by_contra hneg
    have : A i (σ i) ≤ 0 := not_lt.1 hneg
    have : (W : ℝ)⁻¹ * A i (σ i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hWr.le) this
    linarith
  refine ⟨Mσ σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : σ (.inl p.1) = .inr p.2 := (mem_filter.1 hp).2
    have := hpos (.inl p.1)
    rw [hp'] at this
    have h : (0 : ℝ) < (Y p.1 p.2 : ℝ) := this
    exact_mod_cast h
  · intro p hp q hq hpq
    have hp' : σ (.inl p.1) = .inr p.2 := (mem_filter.1 hp).2
    have hq' : σ (.inl q.1) = .inr q.2 := (mem_filter.1 hq).2
    rw [hpq, hq'] at hp'
    exact Prod.ext hpq (Sum.inr_injective hp').symm
  · intro p hp q hq hpq
    have hp' : σ (.inl p.1) = .inr p.2 := (mem_filter.1 hp).2
    have hq' : σ (.inl q.1) = .inr q.2 := (mem_filter.1 hq).2
    rw [hpq, ← hq'] at hp'
    exact Prod.ext (Sum.inl_injective (σ.injective hp')) hpq
  · intro b hb
    have h := hpos (.inl b)
    rcases hσb : σ (.inl b) with b' | c
    · rw [hσb] at h
      have hb' : ∑ c, (Y b c : ℝ) = W := by exact_mod_cast hb
      simp [hA, auxMatrix, hb'] at h
    · exact ⟨(b, c), mem_filter.2 ⟨mem_univ _, hσb⟩, rfl⟩
  · intro c hc'
    have h := hpos (σ.symm (.inr c))
    rw [Equiv.apply_symm_apply] at h
    rcases hσc : σ.symm (.inr c) with b | c'
    · refine ⟨(b, c), mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
      rw [← hσc, Equiv.apply_symm_apply]
    · rw [hσc] at h
      have hc'' : ∑ b, (Y b c : ℝ) = W := by exact_mod_cast hc'
      have hcc : c' = c ∨ c' ≠ c := eq_or_ne _ _
      rcases hcc with rfl | hne
      · simp [hA, auxMatrix, hc''] at h
      · simp [hA, auxMatrix, hne] at h
  · have : ((W * (Mσ σ).card : ℕ) : ℝ) ≤ ((∑ b, ∑ c, Y b c : ℕ) : ℝ) := by
      push_cast
      exact hσS
    exact_mod_cast this


/-- **A matching covering all tight rows and columns, of at most average size.**  `R` is a finite
set of edges of a bipartite multigraph; the edge `x` joins the row `f x` to the column `g x`.  If
`W ≥ 1` and every row and every column contains at most `W` edges, there is a matching `M ⊆ R`
(no two edges of `M` share a row or a column) that meets every row and every column with exactly
`W` edges and has `W |M| ≤ |R|`. -/
theorem exists_matching {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (R : Finset α) (f : α → β) (g : α → γ) {W : ℕ} (hW : 0 < W)
    (hf : ∀ b, (R.filter fun x => f x = b).card ≤ W)
    (hg : ∀ c, (R.filter fun x => g x = c).card ≤ W) :
    ∃ M ⊆ R, Set.InjOn f M ∧ Set.InjOn g M ∧
      (∀ b, (R.filter fun x => f x = b).card = W → ∃ x ∈ M, f x = b) ∧
      (∀ c, (R.filter fun x => g x = c).card = W → ∃ x ∈ M, g x = c) ∧
      W * M.card ≤ R.card := by
  classical
  let Y : ↥(R.image f) → ↥(R.image g) → ℕ := fun b c =>
    (R.filter fun x => f x = b ∧ g x = c).card
  have hrow : ∀ b : ↥(R.image f), ∑ c, Y b c = (R.filter fun x => f x = (b : β)).card := by
    intro b
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := R.image g)
      (fun x hx => mem_image_of_mem g (mem_filter.1 hx).1),
      ← Finset.sum_coe_sort (R.image g)]
    exact Finset.sum_congr rfl fun c _ => by simp only [Y, filter_filter]
  have hcol : ∀ c : ↥(R.image g), ∑ b, Y b c = (R.filter fun x => g x = (c : γ)).card := by
    intro c
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := R.image f)
      (fun x hx => mem_image_of_mem f (mem_filter.1 hx).1),
      ← Finset.sum_coe_sort (R.image f)]
    exact Finset.sum_congr rfl fun b _ => by simp only [Y, filter_filter, and_comm]
  have htot : ∑ b, ∑ c, Y b c = R.card := by
    simp only [hrow]
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := R.image f)
      (fun x hx => mem_image_of_mem f hx), ← Finset.sum_coe_sort (R.image f)]
  obtain ⟨Mp, hMpos, hM1, hM2, hMr, hMc, hMcard⟩ := exists_matching_matrix Y hW
    (fun b => (hrow b).trans_le (hf b)) (fun c => (hcol c).trans_le (hg c))
  have hex : ∀ p ∈ Mp, ∃ x ∈ R, f x = (p.1 : β) ∧ g x = (p.2 : γ) := by
    intro p hp
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (hMpos p hp)
    exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  let e : {p // p ∈ Mp} → α := fun p => (hex p.1 p.2).choose
  have he : ∀ p : {p // p ∈ Mp}, e p ∈ R ∧ f (e p) = (p.1.1 : β) ∧ g (e p) = (p.1.2 : γ) :=
    fun p => (hex p.1 p.2).choose_spec
  refine ⟨Mp.attach.image e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, -, rfl⟩ := mem_image.1 hx
    exact (he p).1
  · intro x hx y hy hxy
    obtain ⟨p, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    obtain ⟨q, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
    rw [(he p).2.1, (he q).2.1] at hxy
    rw [Subtype.ext (hM1 p.1 p.2 q.1 q.2 (Subtype.ext hxy))]
  · intro x hx y hy hxy
    obtain ⟨p, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    obtain ⟨q, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
    rw [(he p).2.2, (he q).2.2] at hxy
    rw [Subtype.ext (hM2 p.1 p.2 q.1 q.2 (Subtype.ext hxy))]
  · intro b hb
    have hbm : b ∈ R.image f := by
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (hb ▸ hW)
      exact mem_image.2 ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
    obtain ⟨p, hp, hpb⟩ := hMr ⟨b, hbm⟩ ((hrow _).trans hb)
    exact ⟨e ⟨p, hp⟩, mem_image_of_mem e (mem_attach _ _), by rw [(he ⟨p, hp⟩).2.1, hpb]⟩
  · intro c hc
    have hcm : c ∈ R.image g := by
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (hc ▸ hW)
      exact mem_image.2 ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
    obtain ⟨p, hp, hpc⟩ := hMc ⟨c, hcm⟩ ((hcol _).trans hc)
    exact ⟨e ⟨p, hp⟩, mem_image_of_mem e (mem_attach _ _), by rw [(he ⟨p, hp⟩).2.2, hpc]⟩
  · calc W * (Mp.attach.image e).card ≤ W * Mp.card :=
        Nat.mul_le_mul_left _ (card_image_le.trans (card_attach).le)
      _ ≤ R.card := htot ▸ hMcard

end OnlineColouring.AppBD
