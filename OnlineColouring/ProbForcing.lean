module

public import OnlineColouring.RandModel

/-!
# Forcing with a given probability: the predicate `ProbForcing`

The statements of the form "there is a distribution over `k`-colourable ordered graphs on `n`
vertices on which every deterministic online algorithm uses at least `x` colours with probability
at least `p`" in Corollary 8.6, Theorem C.3, Corollary C.4 and Appendix D.5 are stated with one
predicate.

* `ProbForcing k n x p`: there is a probability distribution `D` (a Mathlib `PMF`) over online
  inputs on exactly `n` vertices, supported on `k`-colourable graphs, such that every proper
  deterministic online algorithm `A` satisfies `Pr_{I ∼ D}[cost_A(I) ≥ x] ≥ p`.  Here
  `D.toOuterMeasure S` is `∑_{I ∈ S} D(I)`, the probability of the event `S`.  The distribution
  is fixed before the algorithm (`∃ D, ∀ A`), as in the paper.
* `ProbForcing.of_le` (a smaller bound), `ProbForcing.pad` (appending isolated vertices, for
  `k ≥ 1`), `probForcing_one` (every algorithm uses at least one colour on `n ≥ 1` vertices) and
  `not_probForcing_succ` (the predicate is not vacuous: nothing forces `n + 1` colours on `n`
  vertices with positive probability).
* Under the uniform distribution on a finite set, "probability at least `p`" is a counting
  statement: `ofReal_le_unifPMF`, `ofReal_le_unifPMF_pred`, and `ofReal_le_unifInput` for the
  image of a uniform distribution under a map to online inputs.

`ExplProper.lean` shows that properness of the algorithm on the inputs in the support of `D` is
enough (`Expl.probForcing_iff_properOn`).
-/

@[expose] public section

namespace OnlineColouring

open Finset
open scoped ENNReal

/-! ### The predicate and its closure properties -/

/-- `ProbForcing k n x p`: some distribution over `k`-colourable online inputs on exactly `n`
vertices makes every proper deterministic online algorithm use at least `x` colours with
probability at least `p`. -/
def ProbForcing (k n : ℕ) (x p : ℝ) : Prop :=
  ∃ D : PMF (OnlineInput n), (∀ I ∈ D.support, I.graph.Colorable k) ∧
    ∀ A : OnlineAlg, A.IsProper → ENNReal.ofReal p ≤ D.toOuterMeasure {I | x ≤ (I.cost A : ℝ)}

/-- Monotonicity in the bound. -/
theorem ProbForcing.of_le {k n : ℕ} {x x' p : ℝ} (h : ProbForcing k n x p) (hx : x' ≤ x) :
    ProbForcing k n x' p := by
  obtain ⟨D, hcol, hD⟩ := h
  refine ⟨D, hcol, fun A hA => (hD A hA).trans ?_⟩
  apply PMF.toOuterMeasure_mono
  rintro I ⟨hI, -⟩
  exact hx.trans hI

/-- **Padding**: appending isolated vertices keeps the inputs `k`-colourable (for `k ≥ 1`) and
decreases no cost. -/
theorem ProbForcing.pad {k N n : ℕ} {x p : ℝ} (h : ProbForcing k N x p) (hNn : N ≤ n)
    (hk : 1 ≤ k) : ProbForcing k n x p := by
  obtain ⟨D, hcol, hD⟩ := h
  refine ⟨D.map fun I => padInput I n, fun I' hI' => ?_, fun A hA => (hD A hA).trans ?_⟩
  · obtain ⟨I, hI, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hI'
    exact colorable_padInput hk (hcol I hI) n
  · rw [PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_mono
    rintro I ⟨hI, -⟩
    change x ≤ ((padInput I n).cost A : ℝ)
    exact hI.trans (by exact_mod_cast cost_le_padInput hNn I A)

/-- The trivial bound: every algorithm uses at least one colour on `n ≥ 1` vertices, with
probability `1` (the point mass on the edgeless input). -/
theorem probForcing_one {k n : ℕ} {p : ℝ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hp : p ≤ 1) :
    ProbForcing k n 1 p := by
  refine ⟨PMF.pure (emptyInput n), fun I hI => ?_, fun A _ => ?_⟩
  · rw [PMF.mem_support_pure_iff] at hI
    exact hI ▸ emptyInput_colorable hk
  · have hmem : emptyInput n ∈ {I : OnlineInput n | (1 : ℝ) ≤ (I.cost A : ℝ)} := by
      change (1 : ℝ) ≤ ((emptyInput n).cost A : ℝ)
      exact_mod_cast one_le_cost hn A
    rw [PMF.toOuterMeasure_pure_apply, ite_eq_left hmem]
    exact ENNReal.ofReal_le_one.2 hp

/-- Sanity check (the predicate is not vacuous): no distribution forces `n + 1` colours on `n`
vertices with a positive probability, since First-Fit uses at most `n`. -/
theorem not_probForcing_succ (k n : ℕ) {p : ℝ} (hp : 0 < p) : ¬ ProbForcing k n (n + 1) p := by
  rintro ⟨D, -, hD⟩
  have h := hD _ OnlineAlg.firstFit_isProper
  have hempty : {I : OnlineInput n | ((n : ℝ) + 1) ≤ (I.cost OnlineAlg.firstFit : ℝ)} = ∅ := by
    ext I
    have h1 : (I.cost OnlineAlg.firstFit : ℝ) ≤ n := by exact_mod_cast I.cost_le OnlineAlg.firstFit
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    linarith
  rw [hempty, PMF.toOuterMeasure_apply] at h
  simp only [Set.indicator_empty, tsum_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
  linarith

/-! ### Uniform distributions: probability `≥ p` is a counting statement -/

/-- Under the uniform distribution on a nonempty finite type, an event containing at least a
fraction `p` of the points has probability at least `p`. -/
theorem ofReal_le_unifPMF {Ω : Type*} [Fintype Ω] [Nonempty Ω] (s : Set Ω)
    [DecidablePred (· ∈ s)] {p : ℝ} (h : p * Fintype.card Ω ≤ (univ.filter (· ∈ s)).card) :
    ENNReal.ofReal p ≤ (unifPMF Ω).toOuterMeasure s := by
  have hcpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hval : (unifPMF Ω).toOuterMeasure s =
      ((univ.filter (· ∈ s)).card : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
    rw [PMF.toOuterMeasure_apply_fintype]
    simp only [Set.indicator_apply, unifPMF_apply]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hp : p ≤ ((univ.filter (· ∈ s)).card : ℝ) / Fintype.card Ω := by
    rw [le_div_iff₀ hcpos]
    exact h
  rw [hval]
  calc ENNReal.ofReal p ≤ ENNReal.ofReal (((univ.filter (· ∈ s)).card : ℝ) / Fintype.card Ω) :=
        ENNReal.ofReal_le_ofReal hp
    _ = ((univ.filter (· ∈ s)).card : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hcpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          div_eq_mul_inv]

/-- The same, for an event given by a predicate `P` (stated with the filter `univ.filter P`, so
that it applies without unfolding `P`). -/
theorem ofReal_le_unifPMF_pred {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop)
    [DecidablePred P] {p : ℝ} (h : p * Fintype.card Ω ≤ (univ.filter P).card) :
    ENNReal.ofReal p ≤ (unifPMF Ω).toOuterMeasure {ω | P ω} := by
  apply ofReal_le_unifPMF
  have e : (univ.filter (· ∈ {ω | P ω}) : Finset Ω) = univ.filter P := by
    ext ω
    simp
  rw [e]
  exact h

/-- The same for the image of the uniform distribution under `inp`. -/
theorem ofReal_le_unifInput {Ω : Type*} [Fintype Ω] [Nonempty Ω] {N : ℕ}
    (inp : Ω → OnlineInput N) (S : Set (OnlineInput N)) [DecidablePred (· ∈ S)] {p : ℝ}
    (h : p * Fintype.card Ω ≤ (univ.filter fun ω => inp ω ∈ S).card) :
    ENNReal.ofReal p ≤ (unifInput inp).toOuterMeasure S := by
  rw [unifInput, PMF.toOuterMeasure_map_apply]
  exact @ofReal_le_unifPMF _ _ _ (inp ⁻¹' S)
    (fun ω => inferInstanceAs (Decidable (inp ω ∈ S))) p h

end OnlineColouring
