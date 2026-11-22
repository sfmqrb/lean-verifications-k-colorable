module

public import OnlineColouring.UExact

/-!
# Lemmas 8.3 and 8.4 for the random wiring `R_j(m)`, in the form stated in the paper

The quantities of the analysis are those of `UExact.lean`: for an algorithm `alg` and a wiring
`ω : EΩ m j A`, `uME alg ω c t` is the unused mass `u_c` at the start of phase `t`, `fME alg ω c t`
is `a_t(c)` and `qME alg ω c t` is `q_t(c)`.  Phases are numbered `0, …, m - 1` here (the paper
numbers them `1, …, m`), so the paper's `u_c(m + 1)` is `uME alg ω c m`.

* `mass` (Lemma 8.3, bookkeeping): `u_c(t+1) ≤ u_c(t) + a_t(c)`, `a_t(c) ≤ min(1, q_t(c))` and
  `∑_c u_c(m+1) = (3m+1)/4`, in every play.  The sum over all colours is a `finsum` (only the
  colours used have mass); `sum_uME_end` is the same with a finite sum over the colours used.
* `NoNbrOfColour alg ω c y`: the presented vertex `y` has no earlier neighbour of colour `c`.
* `SameHistory ω ω₀ t`: the wirings `ω` and `ω₀` present the same graph before phase `t` (the
  same earlier neighbours for every vertex of the phases `< t`); the colours given before phase
  `t` are then the same too (`SameHistory.uColE_eq`), because the algorithm is deterministic.
* `card_noNbr_update_le` (Lemma 8.4, conditioned on the random choices of the earlier phases) and
  `miss` (**Lemma 8.4 as stated**: conditioned on the history before phase `t`): among the
  wirings with a given history before phase `t`, the fraction of those in which a fixed vertex
  `y` of phase `t` has no earlier neighbour of colour `c` is at most `exp(-u_c(t))`.  All wirings
  are equally likely under `R_j(m)`, so this is the conditional probability.  `u_c(t)` is
  determined by the history (`SameHistory.uME_eq`).
-/

@[expose] public section

namespace OnlineColouring

namespace Rjm

open Finset

variable {m j A : ℕ}

/-! ### Lemma 8.3 -/

theorem uME_nonneg (alg : OnlineAlg) (ω : EΩ m j A) (c t : ℕ) : 0 ≤ uME alg ω c t :=
  sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Only the colours used on the presented graph have mass. -/
theorem support_uME_subset (alg : OnlineAlg) (ω : EΩ m j A) :
    (Function.support fun c => uME alg ω c m) ⊆
      ((range (m * A ^ j)).image (uColE alg ω) : Finset ℕ) := by
  intro c hc
  exact mem_colsBeforeE_of_pos (lt_of_le_of_ne (uME_nonneg alg ω c m) (Ne.symm hc))

/-- The total unused mass at the end, summed over the colours used: `(3m+1)/4`. -/
theorem sum_uME_end (hm : 1 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg) (ω : EΩ m j (2 * m)) :
    ∑ c ∈ (range (m * (2 * m) ^ j)).image (uColE alg ω), uME alg ω c m = (3 * m + 1) / 4 := by
  rw [sum_uME_final (by omega) hj]
  have h := final_mass hm
  push_cast at h ⊢
  exact h

/-- **Lemma 8.3 (bookkeeping).** In every play (every wiring `ω` of `R_j(m)`, `A = 2m`, and every
proper algorithm) and for every colour `c` and phase `t`:
`u_c(t+1) ≤ u_c(t) + a_t(c)`, `a_t(c) ≤ min(1, q_t(c))`, and `∑_c u_c(m+1) = (3m+1)/4`. -/
theorem mass (hm : 1 ≤ m) (hj : 1 ≤ j) {alg : OnlineAlg} (halg : alg.IsProper)
    (ω : EΩ m j (2 * m)) :
    (∀ c t, uME alg ω c (t + 1) ≤ uME alg ω c t + fME alg ω c t) ∧
      (∀ c t, fME alg ω c t ≤ min 1 (qME alg ω c t)) ∧
      ∑ᶠ c, uME alg ω c m = (3 * m + 1) / 4 := by
  have hA : 0 < 2 * m := by omega
  refine ⟨fun c t => uME_succ_le c t,
    fun c t => le_min (fME_le_one hA c t) (fME_le_qME hA halg c t), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (support_uME_subset alg ω)]
  exact sum_uME_end hm hj alg ω

/-! ### The top server is visible in the presented graph -/

section Top

variable {τ : ℕ → ℕ → ℕ} {φ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}

/-- The ancestor at depth `1` of the neighbour below `s` of a node with root `t` is the top server
`τ s t`. -/
theorem ueNb_div_pow_pred (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A) (k s y : ℕ) :
    ueNb A τ φ (k + 1) s y / A ^ k = s * A + τ s (y / A ^ (k + 1)) := by
  induction k generalizing y with
  | zero => simp [ueNb, ueDig]
  | succ k ih =>
    rw [div_pow_succ, ueNb_succ_div hA hτ hφ, ih, div_pow_succ y (k + 1)]

theorem ueNb_top (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (k s y : ℕ) : (ueNb A τ φ (k + 1) s y / A ^ k) % A = τ s (y / A ^ (k + 1)) := by
  rw [ueNb_div_pow_pred hA hτ hφ, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (hτ _ _)]

end Top

/-! ### Histories -/

/-- The presented vertex `y` has no earlier neighbour of colour `c`. -/
def NoNbrOfColour (alg : OnlineAlg) (ω : EΩ m j A) (c y : ℕ) : Prop :=
  ∀ x ∈ uSeqE ω y, uColE alg ω x ≠ c

/-- The wirings `ω` and `ω₀` present the same graph before phase `t`: every vertex of the phases
`< t` has the same earlier neighbours. -/
def SameHistory (ω ω₀ : EΩ m j A) (t : ℕ) : Prop :=
  ∀ i < t * A ^ j, uSeqE ω i = uSeqE ω₀ i

theorem SameHistory.refl (ω : EΩ m j A) (t : ℕ) : SameHistory ω ω t := fun _ _ => rfl

theorem AgreeBelowE.sameHistory {ω ω' : EΩ m j A} {t : ℕ} (h : AgreeBelowE ω ω' t) :
    SameHistory ω ω' t :=
  fun _ hi => uSeqE_congr h (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi))

/-- The history before phase `t` does not depend on the random choices of phase `t`. -/
theorem sameHistory_update_iff (ω ω₀ : EΩ m j A) (t : Fin m) (X : (s : Fin m) → EZ A j t s) :
    SameHistory (Function.update ω t X) ω₀ t ↔ SameHistory ω ω₀ t := by
  have h := AgreeBelowE.sameHistory (agreeBelowE_update ω t X)
  constructor
  · intro h' i hi
    rw [h i hi, h' i hi]
  · intro h' i hi
    rw [← h i hi, h' i hi]

/-- With the same history, the algorithm has given the same colours before phase `t`. -/
theorem SameHistory.uColE_eq {ω ω₀ : EΩ m j A} {t : ℕ} (h : SameHistory ω ω₀ t)
    (alg : OnlineAlg) {x : ℕ} (hx : x < t * A ^ j) : uColE alg ω x = uColE alg ω₀ x := by
  unfold uColE
  exact runCol_congr fun i hi => h i (lt_of_le_of_lt hi hx)

/-- With the same history, the same top servers have been used before phase `t`. -/
theorem SameHistory.tauE_eq {ω ω₀ : EΩ m j A} {t : ℕ} (h : SameHistory ω ω₀ t) (hA : 0 < A)
    (hj : 1 ≤ j) {s t' : ℕ} (hst : s < t') (ht : t' < t) : tauE ω s t' = tauE ω₀ s t' := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hy : t' * A ^ (k + 1) < t * A ^ (k + 1) := Nat.mul_lt_mul_of_pos_right ht (pow_pos hA _)
  have hyt : t' * A ^ (k + 1) / A ^ (k + 1) = t' := Nat.mul_div_cancel _ (pow_pos hA _)
  have hmem : ueNb A (tauE ω) (phiE ω) (k + 1) s (t' * A ^ (k + 1)) ∈
      uSeqE ω (t' * A ^ (k + 1)) := mem_ueSeq.2 ⟨s, by rw [hyt]; exact hst, rfl⟩
  rw [h _ hy] at hmem
  obtain ⟨s', -, hs'⟩ := mem_ueSeq.1 hmem
  have hss : s' = s := by
    have h₁ := ueNb_div_pow hA (tauE_lt ω₀ hA) (phiE_lt ω₀ hA) (k + 1) s' (t' * A ^ (k + 1))
    have h₂ := ueNb_div_pow hA (tauE_lt ω hA) (phiE_lt ω hA) (k + 1) s (t' * A ^ (k + 1))
    rw [hs'] at h₁
    exact h₁.symm.trans h₂
  rw [hss] at hs'
  have e₁ := ueNb_top hA (tauE_lt ω hA) (phiE_lt ω hA) k s (t' * A ^ (k + 1))
  have e₂ := ueNb_top hA (tauE_lt ω₀ hA) (phiE_lt ω₀ hA) k s (t' * A ^ (k + 1))
  rw [hyt] at e₁ e₂
  rw [← e₁, ← e₂, hs']

theorem SameHistory.usedTopE_eq {ω ω₀ : EΩ m j A} {t : ℕ} (h : SameHistory ω ω₀ t) (hA : 0 < A)
    (hj : 1 ≤ j) (htm : t ≤ m) (s : ℕ) :
    ∀ i, s + i < t → usedTopE ω s i = usedTopE ω₀ s i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [usedTopE_succ, usedTopE_succ, ih (by omega),
      ← OnlineColouring.tauE_eq ω (by omega : s < s + 1 + i) (by omega),
      ← OnlineColouring.tauE_eq ω₀ (by omega : s < s + 1 + i) (by omega),
      h.tauE_eq hA hj (by omega) (by omega)]

/-- With the same history, the same vertices are eligible at the start of phase `t`. -/
theorem SameHistory.eligE_eq {ω ω₀ : EΩ m j A} {t : ℕ} (h : SameHistory ω ω₀ t) (hA : 0 < A)
    (hj : 1 ≤ j) (htm : t ≤ m) (s : ℕ) : eligE ω s t = eligE ω₀ s t := by
  unfold eligE
  by_cases hst : s < t
  · rw [h.usedTopE_eq hA hj htm s _ (by omega)]
  · rw [show t - s - 1 = 0 by omega]; rfl

/-- **The unused mass `u_c(t)` is determined by the history before phase `t`.** -/
theorem SameHistory.uME_eq {ω ω₀ : EΩ m j A} {t : ℕ} (h : SameHistory ω ω₀ t) (hA : 0 < A)
    (hj : 1 ≤ j) (htm : t ≤ m) (alg : OnlineAlg) (c : ℕ) :
    uME alg ω c t = uME alg ω₀ c t := by
  unfold uME
  apply sum_congr rfl
  intro s hs
  rw [h.eligE_eq hA hj htm s]
  congr 3
  apply filter_congr
  intro y hy
  rw [h.uColE_eq alg (lt_of_div_lt hA (by
    rw [(mem_phase hA).1 (eligE_subset (ω := ω₀) s t hy)]; exact mem_range.1 hs))]

/-! ### Lemma 8.4 -/

/-- In the wiring `update ω t X`, a vertex `y` of phase `t` has no earlier neighbour of colour `c`
iff none of the servers `nbOfE ω s t y (X s)`, `s < t`, has colour `c` (colours as in `ω`: they
are given before phase `t`). -/
theorem noNbrOfColour_update_iff (hA : 0 < A) (alg : OnlineAlg) (ω : EΩ m j A) (t : Fin m)
    (X : (s : Fin m) → EZ A j t s) (c : ℕ) {y : ℕ} (hyt : y / A ^ j = t) :
    NoNbrOfColour alg (Function.update ω t X) c y ↔
      ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c := by
  unfold NoNbrOfColour uSeqE
  constructor
  · intro h s hs
    have := h _ (mem_ueSeq.2 ⟨s, by rw [hyt]; exact hs, rfl⟩)
    rwa [ueNb_updateE (ω := ω) t X s hyt, uColE_update alg ω t X (lt_of_div_lt hA (by
      rw [nbOfE_div hA]; exact hs))] at this
  · intro h x hx
    obtain ⟨s, hs, rfl⟩ := mem_ueSeq.1 hx
    rw [hyt] at hs
    have hsm : s < m := lt_trans hs t.2
    have := h ⟨s, hsm⟩ hs
    rwa [← ueNb_updateE (ω := ω) t X ⟨s, hsm⟩ hyt, ← uColE_update alg ω t X (lt_of_div_lt hA (by
      rw [ueNb_updateE (ω := ω) t X ⟨s, hsm⟩ hyt, nbOfE_div hA]; exact hs))] at this

open Classical in
/-- **Lemma 8.4, conditioned on the random choices of the earlier phases.** Fix the coordinates
of `ω` outside phase `t`.  For every vertex `y` of phase `t` and every colour `c`, at most a
fraction `exp(-u_c(t))` of the wirings `X` of phase `t` leave `y` without an earlier neighbour of
colour `c`. -/
theorem card_noNbr_update_le (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (ω : EΩ m j A)
    (t : Fin m) (c : ℕ) {y : ℕ} (hyt : y / A ^ j = t) :
    ((univ.filter fun X : (s : Fin m) → EZ A j t s =>
        NoNbrOfColour alg (Function.update ω t X) c y).card : ℝ) ≤
      (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω c t) := by
  have h := card_bad_leE hA hj alg ω t.2 c y
  have e : (univ.filter fun X : (s : Fin m) → EZ A j t s =>
      NoNbrOfColour alg (Function.update ω t X) c y) =
      univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c := by
    apply filter_congr
    intro X _
    exact noNbrOfColour_update_iff hA alg ω t X c hyt
  rw [e]
  exact h

open Classical in
/-- **Lemma 8.4 (colours with large mass are seen).** Fix a deterministic algorithm `alg` and play
it against `R_j(m)`.  Condition on the history before phase `t`, that of the wiring `ω₀`.  Then
for every presented vertex `y` of phase `t` and every colour `c`,
`Pr[y has no earlier neighbour of colour c | history] ≤ exp(-u_c(t))`: among the wirings with the
history of `ω₀` (all equally likely), at most a fraction `exp(-u_c(t))` leave `y` without an
earlier neighbour of colour `c`. -/
theorem miss (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (ω₀ : EΩ m j A) (t : Fin m) (c : ℕ)
    {y : ℕ} (hyt : y / A ^ j = t) :
    ((univ.filter fun ω : EΩ m j A =>
        SameHistory ω ω₀ t ∧ NoNbrOfColour alg ω c y).card : ℝ) ≤
      ((univ.filter fun ω : EΩ m j A => SameHistory ω ω₀ t).card : ℝ) *
        Real.exp (-uME alg ω₀ c t) := by
  have hne : Nonempty ((s : Fin m) → EZ A j t s) := ⟨ω₀ t⟩
  have hpos : (0 : ℝ) < (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) :=
    Nat.cast_pos.2 Fintype.card_pos
  set f : EΩ m j A → ℝ := fun ω =>
    if SameHistory ω ω₀ t ∧ NoNbrOfColour alg ω c y then 1 else 0 with hf
  have hsum := sum_mul_card_eq_sum_update_dep (X := fun t : Fin m => (s : Fin m) → EZ A j t s) t f
  have hL : ((univ.filter fun ω : EΩ m j A =>
      SameHistory ω ω₀ t ∧ NoNbrOfColour alg ω c y).card : ℝ) = ∑ ω, f ω := by
    rw [hf, sum_boole]
  have hinner : ∀ ω : EΩ m j A, ∑ X : (s : Fin m) → EZ A j t s, f (Function.update ω t X) ≤
      if SameHistory ω ω₀ t then
        (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω₀ c t) else 0 := by
    intro ω
    by_cases hω : SameHistory ω ω₀ t
    · rw [ite_eq_left hω, ← hω.uME_eq hA hj t.2.le alg c]
      refine le_trans (le_of_eq ?_) (card_noNbr_update_le hA hj alg ω t c hyt)
      rw [← sum_boole]
      apply sum_congr rfl
      intro X _
      simp only [hf, sameHistory_update_iff, hω, true_and]
    · rw [ite_eq_right hω]
      apply le_of_eq
      apply sum_eq_zero
      intro X _
      simp only [hf, sameHistory_update_iff, hω, false_and, ite_false]
  have hR : ∑ ω : EΩ m j A, (if SameHistory ω ω₀ t then
      (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω₀ c t) else 0) =
      ((univ.filter fun ω : EΩ m j A => SameHistory ω ω₀ t).card : ℝ) *
        ((Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω₀ c t)) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hmain : (∑ ω, f ω) * (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) ≤
      ((univ.filter fun ω : EΩ m j A => SameHistory ω ω₀ t).card : ℝ) *
        Real.exp (-uME alg ω₀ c t) * (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) := by
    rw [hsum]
    refine (sum_le_sum fun ω _ => hinner ω).trans (le_of_eq ?_)
    rw [hR]
    ring
  rw [hL]
  exact le_of_mul_le_mul_right hmain hpos

end Rjm

end OnlineColouring
