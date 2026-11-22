module

public import OnlineColouring.PaperRand
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Definition 4.1: arbitrary probability measures over deterministic algorithms

Definition 4.1 calls randomized online algorithms "probability distributions over deterministic
ones".  `RandModel.lean` uses discrete distributions (`PMF OnlineAlg`).  This file shows that
nothing is lost for general probability measures: for *every* σ-algebra on the set of
deterministic online algorithms for which the cost functions `A ↦ cost(A, I)` are measurable, and
*every* probability measure `P` that is concentrated on proper algorithms, there is a finitely
supported proper randomized algorithm with the same expected cost on every `k`-colourable input
on `n` vertices (`exists_finite_support_of_measure`).  Hence the maximum expected cost of `P` is
at least `chiRand k n` (`chiRand_le_of_measure`), and `χ^rand_k(n)` is the minimum over
probability measures in this general sense as well.
-/

@[expose] public section

namespace OnlineColouring

namespace Paper

open MeasureTheory

/-- **Every probability measure over deterministic online algorithms is equivalent to a finitely
supported one**, on the `k`-colourable inputs on `n` vertices. -/
theorem exists_finite_support_of_measure (k n : ℕ) {m : MeasurableSpace OnlineAlg}
    (P : Measure OnlineAlg) [IsProbabilityMeasure P]
    (hmeas : ∀ I : ColInput k n, Measurable fun A : OnlineAlg => I.1.cost A)
    (hproper : ∀ᵐ A ∂P, A.IsProper) :
    ∃ ν : PMF OnlineAlg, IsProperRand ν ∧ ν.support.Finite ∧
      ∀ I : ColInput k n, expCost ν I.1 = ∫ A, (I.1.cost A : ℝ) ∂P := by
  have := Fintype.ofFinite (costVecs k n)
  let S : costVecs k n → Set OnlineAlg := fun v => {A | costVec k n A = v.1}
  have hS : ∀ v, MeasurableSet (S v) := by
    intro v
    have : S v = ⋂ I : ColInput k n, (fun A : OnlineAlg => I.1.cost A) ⁻¹' {v.1 I} := by
      ext A
      simp only [S, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h I => congrFun h I, fun h => funext h⟩
    rw [this]
    exact MeasurableSet.iInter fun I => hmeas I (measurableSet_singleton _)
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro v v' hne
    rw [Function.onFun, Set.disjoint_left]
    intro A hA hA'
    exact hne (Subtype.ext (hA.symm.trans hA'))
  have hcover : ∀ A : OnlineAlg, A.IsProper → A ∈ S (cv k n A) := by
    intro A hA
    change costVec k n A = (cv k n A).1
    funext I
    exact (cv_apply hA I).symm
  have hunion : P.real (⋃ v, S v) = 1 := by
    have h1 : P.real (⋃ v, S v) = P.real Set.univ := by
      refine measureReal_congr ?_
      filter_upwards [hproper] with A hA
      exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_iUnion.2 ⟨_, hcover A hA⟩⟩
    rw [h1]
    simp
  set w : costVecs k n → ℝ := fun v => P.real (S v) with hwdef
  have hw : IsWeight w :=
    ⟨fun v => measureReal_nonneg, by rw [← measureReal_iUnion_fintype hdisj hS]; exact hunion⟩
  obtain ⟨ν, hν, hfin, hνw⟩ := exists_pmf_of_weights hw
  refine ⟨ν, hν, hfin, fun I => ?_⟩
  rw [hνw I]
  have hae : (fun A : OnlineAlg => (I.1.cost A : ℝ)) =ᵐ[P]
      fun A => ∑ v, (S v).indicator (fun _ => (v.1 I : ℝ)) A := by
    filter_upwards [hproper] with A hA
    rw [Finset.sum_eq_single (cv k n A)]
    · rw [Set.indicator_of_mem (hcover A hA), cv_apply hA]
    · intro v _ hv
      refine Set.indicator_of_notMem (fun hA' => hv ?_) _
      exact Subtype.ext ((show costVec k n A = v.1 from hA').symm.trans (hcover A hA))
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [integral_congr_ae hae, integral_finsetSum _ fun v _ => (integrable_const _).indicator (hS v)]
  unfold mix
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hS v), smul_eq_mul]

/-- **`χ^rand_k(n)` bounds the maximum expected cost of every probability measure over
deterministic online algorithms**, not only of the discrete ones. -/
theorem chiRand_le_of_measure (k n : ℕ) {m : MeasurableSpace OnlineAlg}
    (P : Measure OnlineAlg) [IsProbabilityMeasure P]
    (hmeas : ∀ I : ColInput k n, Measurable fun A : OnlineAlg => I.1.cost A)
    (hproper : ∀ᵐ A ∂P, A.IsProper) :
    chiRand k n ≤ ⨆ I : ColInput k n, ∫ A, (I.1.cost A : ℝ) ∂P := by
  obtain ⟨ν, hν, -, hνP⟩ := exists_finite_support_of_measure k n P hmeas hproper
  rw [← iSup_congr hνP]
  exact (chiRand_isLeast k n).2 ⟨ν, hν, rfl⟩

end Paper

end OnlineColouring
