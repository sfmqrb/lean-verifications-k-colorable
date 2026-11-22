module

public import OnlineColouring.RandModel
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Definition 4.1: the minimum in `χ^rand_k(n)` is attained

Definition 4.1: *`χ^rand_k(n)` is the minimum, over randomized online algorithms (probability
distributions over deterministic ones), of the maximum expected cost over all ordered
`k`-colourable graphs on `n` vertices.*

`RandModel.lean` defines `chiRand k n` as an **infimum** over `PMF OnlineAlg` (discrete
distributions, countable support).  This file proves that the infimum is a minimum, and that it is
attained by a finitely supported distribution, so the word "minimum" of the definition is exact
for each of the readings "finitely supported", "discrete", and anything in between:

* `exists_finite_support_minimizer`: some proper randomized algorithm with *finite* support has
  maximum expected cost exactly `chiRand k n`;
* `chiRand_isLeast`: `chiRand k n` is the least element of the set of the maximum expected costs
  of the proper randomized algorithms (`PMF OnlineAlg`);
* `chiRand_isLeast_finite`: the same for the finitely supported ones;
* `exists_finite_support_expCost_eq`: every proper randomized algorithm has the same expected
  cost on every `k`-colourable input on `n` vertices as a finitely supported one.

Proof, following the remark after Definition 4.1: for fixed `n` the cost vectors
`(cost of A on I)_{I}` of the proper deterministic algorithms form a finite set `costVecs k n`
(every cost lies in `{0, …, n}` and there are finitely many inputs).  The expected-cost vector of
a randomized algorithm is a convex combination of these vectors (`exists_weights`), every convex
combination is the expected-cost vector of a finitely supported randomized algorithm
(`exists_pmf_of_weights`), and the maximum coordinate is a continuous function on the compact
simplex of weights, so it has a minimum (`exists_min_weights`).
-/

@[expose] public section

namespace OnlineColouring

namespace Paper

open scoped ENNReal

/-- The `k`-colourable online inputs on `n` vertices. -/
abbrev ColInput (k n : ℕ) : Type := {I : OnlineInput n // I.graph.Colorable k}

/-- The maximum expected cost of the randomized algorithm `μ` over the `k`-colourable inputs on
`n` vertices (the inner maximum of Definition 4.1). -/
noncomputable def maxExpCost (k n : ℕ) (μ : PMF OnlineAlg) : ℝ :=
  ⨆ I : ColInput k n, expCost μ I.1

theorem chiRand_eq_iInf (k n : ℕ) :
    chiRand k n = ⨅ μ : {μ : PMF OnlineAlg // IsProperRand μ}, maxExpCost k n μ.1 := rfl

/-! ### Cost vectors -/

/-- The cost vector of the deterministic algorithm `A`. -/
def costVec (k n : ℕ) (A : OnlineAlg) : ColInput k n → ℕ := fun I => I.1.cost A

/-- The cost vectors of the proper deterministic algorithms. -/
def costVecs (k n : ℕ) : Set (ColInput k n → ℕ) :=
  Set.range fun A : {A : OnlineAlg // A.IsProper} => costVec k n A.1

/-- For fixed `n` there are finitely many cost vectors. -/
theorem costVecs_finite (k n : ℕ) : (costVecs k n).Finite := by
  have hfin : {f : ColInput k n → ℕ | ∀ I, f I ∈ Set.Iic n}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Iic n
  refine hfin.subset ?_
  rintro _ ⟨A, rfl⟩ I
  exact I.1.cost_le A.1

instance (k n : ℕ) : Finite (costVecs k n) := (costVecs_finite k n).to_subtype

instance (k n : ℕ) : Nonempty (costVecs k n) :=
  ⟨⟨_, ⟨OnlineAlg.firstFit, OnlineAlg.firstFit_isProper⟩, rfl⟩⟩

/-- A proper deterministic algorithm with the cost vector `v`. -/
noncomputable def rep {k n : ℕ} (v : costVecs k n) : OnlineAlg := (Classical.choose v.2).1

theorem rep_isProper {k n : ℕ} (v : costVecs k n) : (rep v).IsProper := (Classical.choose v.2).2

theorem costVec_rep {k n : ℕ} (v : costVecs k n) : costVec k n (rep v) = v.1 :=
  Classical.choose_spec v.2

open Classical in
/-- The cost vector of `A` as an element of `costVecs k n` (a default value if `A` is not
proper). -/
noncomputable def cv (k n : ℕ) (A : OnlineAlg) : costVecs k n :=
  if h : A.IsProper then ⟨costVec k n A, ⟨A, h⟩, rfl⟩
  else ⟨_, ⟨OnlineAlg.firstFit, OnlineAlg.firstFit_isProper⟩, rfl⟩

theorem cv_apply {k n : ℕ} {A : OnlineAlg} (h : A.IsProper) (I : ColInput k n) :
    (cv k n A).1 I = I.1.cost A := by
  simp [cv, h, costVec]

/-! ### Mixtures -/

/-- Change of variables for the push-forward of a discrete distribution. -/
theorem tsum_map_mul {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' b, (p.map f) b * g b = ∑' a, p a * g (f a) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  congr 1
  funext a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp [hb]

/-- The weights: nonnegative with sum `1`. -/
def IsWeight {ι : Type*} [Fintype ι] (w : ι → ℝ) : Prop := (∀ v, 0 ≤ w v) ∧ ∑ v, w v = 1

section

variable {k n : ℕ}

/-- The coordinate `I` of the convex combination of the cost vectors with weights `w`. -/
noncomputable def mix [Fintype (costVecs k n)] (w : costVecs k n → ℝ) (I : ColInput k n) : ℝ :=
  ∑ v, w v * (v.1 I : ℝ)

/-- **Every expected-cost vector is a convex combination of cost vectors.** -/
theorem exists_weights [Fintype (costVecs k n)] (μ : PMF OnlineAlg) (hμ : IsProperRand μ) :
    ∃ w : costVecs k n → ℝ, IsWeight w ∧ ∀ I : ColInput k n, expCost μ I.1 = mix w I := by
  set q : PMF (costVecs k n) := μ.map (cv k n) with hq
  refine ⟨fun v => (q v).toReal, ⟨fun v => ENNReal.toReal_nonneg, ?_⟩, fun I => ?_⟩
  · have hs : ∑ v, q v = 1 := by
      have := q.tsum_coe
      rwa [tsum_fintype] at this
    rw [← ENNReal.toReal_sum fun v _ => q.apply_ne_top v, hs]
    rfl
  · have h1 : expCostE μ I.1 = ∑ v, q v * ((v.1 I : ℕ) : ℝ≥0∞) := by
      have h2 := tsum_map_mul μ (cv k n) fun v => ((v.1 I : ℕ) : ℝ≥0∞)
      rw [tsum_fintype] at h2
      rw [hq, h2]
      unfold expCostE
      refine tsum_congr fun A => ?_
      by_cases hA : A ∈ μ.support
      · rw [cv_apply (hμ A hA)]
      · rw [(PMF.apply_eq_zero_iff μ A).2 hA, zero_mul, zero_mul]
    unfold expCost mix
    rw [h1, ENNReal.toReal_sum fun v _ =>
      ENNReal.mul_ne_top (q.apply_ne_top v) (ENNReal.natCast_ne_top _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- **Every convex combination of cost vectors is the expected-cost vector of a finitely
supported proper randomized algorithm.** -/
theorem exists_pmf_of_weights [Fintype (costVecs k n)] {w : costVecs k n → ℝ}
    (hw : IsWeight w) :
    ∃ μ : PMF OnlineAlg, IsProperRand μ ∧ μ.support.Finite ∧
      ∀ I : ColInput k n, expCost μ I.1 = mix w I := by
  have hsum : ∑ v, ENNReal.ofReal (w v) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => hw.1 v, hw.2, ENNReal.ofReal_one]
  set q : PMF (costVecs k n) := PMF.ofFintype (fun v => ENNReal.ofReal (w v)) hsum with hq
  refine ⟨q.map rep, ?_, ?_, fun I => ?_⟩
  · intro A hA
    obtain ⟨v, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hA
    exact rep_isProper v
  · refine (Set.finite_range (rep (k := k) (n := n))).subset ?_
    intro A hA
    obtain ⟨v, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hA
    exact ⟨v, rfl⟩
  · have h1 : expCostE (q.map rep) I.1 = ∑ v, ENNReal.ofReal (w v) * ((v.1 I : ℕ) : ℝ≥0∞) := by
      unfold expCostE
      rw [tsum_map_mul q rep fun A => ((I.1.cost A : ℕ) : ℝ≥0∞), tsum_fintype]
      refine Finset.sum_congr rfl fun v _ => ?_
      have : I.1.cost (rep v) = v.1 I := congrFun (costVec_rep v) I
      rw [this]
      rfl
    unfold expCost mix
    rw [h1, ENNReal.toReal_sum fun v _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (hw.1 v)]

/-- The weights form a compact set. -/
theorem isCompact_isWeight {ι : Type*} [Fintype ι] : IsCompact {w : ι → ℝ | IsWeight w} := by
  have hclosed : IsClosed {w : ι → ℝ | IsWeight w} := by
    have : {w : ι → ℝ | IsWeight w} = (⋂ v, {w : ι → ℝ | 0 ≤ w v}) ∩ {w | ∑ v, w v = 1} := by
      ext w
      simp [IsWeight]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun v => ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply v)
    · exact isClosed_eq (by fun_prop) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)) hclosed ?_
  rintro w ⟨h0, h1⟩
  refine ⟨fun v => h0 v, fun v => ?_⟩
  have := Finset.single_le_sum (f := w) (fun i _ => h0 i) (Finset.mem_univ v)
  rw [h1] at this
  exact this

/-- **The maximum coordinate has a minimum over the simplex of weights.** -/
theorem exists_min_weights [Fintype (costVecs k n)] [Nonempty (ColInput k n)] :
    ∃ w : costVecs k n → ℝ, IsWeight w ∧
      ∀ w' : costVecs k n → ℝ, IsWeight w' → (⨆ I, mix w I) ≤ ⨆ I, mix w' I := by
  have := Fintype.ofFinite (ColInput k n)
  have hcont : Continuous fun w : costVecs k n → ℝ => ⨆ I : ColInput k n, mix w I := by
    have h : (fun w : costVecs k n → ℝ => ⨆ I : ColInput k n, mix w I) =
        fun w => Finset.univ.sup' Finset.univ_nonempty fun I : ColInput k n => mix w I := by
      funext w
      exact (Finset.sup'_univ_eq_ciSup _).symm
    rw [h]
    refine Continuous.finset_sup'_apply _ fun I _ => ?_
    unfold mix
    fun_prop
  have hne : {w : costVecs k n → ℝ | IsWeight w}.Nonempty := by
    classical
    obtain ⟨v₀⟩ := (inferInstance : Nonempty (costVecs k n))
    refine ⟨Pi.single v₀ 1, fun v => ?_, ?_⟩
    · by_cases h : v = v₀
      · subst h; simp
      · simp [h]
    · simp [Pi.single_apply]
  obtain ⟨w, hw, hmin⟩ := isCompact_isWeight.exists_isMinOn hne hcont.continuousOn
  exact ⟨w, hw, fun w' hw' => hmin hw'⟩

end

/-! ### The minimum -/

theorem maxExpCost_eq_of_forall {k n : ℕ} {μ ν : PMF OnlineAlg}
    (h : ∀ I : ColInput k n, expCost μ I.1 = expCost ν I.1) :
    maxExpCost k n μ = maxExpCost k n ν := by
  unfold maxExpCost
  exact iSup_congr h

/-- **Every proper randomized algorithm is equivalent, on the `k`-colourable inputs on `n`
vertices, to a finitely supported one.** -/
theorem exists_finite_support_expCost_eq (k n : ℕ) (μ : PMF OnlineAlg) (hμ : IsProperRand μ) :
    ∃ ν : PMF OnlineAlg, IsProperRand ν ∧ ν.support.Finite ∧
      ∀ I : ColInput k n, expCost ν I.1 = expCost μ I.1 := by
  have := Fintype.ofFinite (costVecs k n)
  obtain ⟨w, hw, hwμ⟩ := exists_weights (k := k) (n := n) μ hμ
  obtain ⟨ν, hν, hfin, hνw⟩ := exists_pmf_of_weights hw
  exact ⟨ν, hν, hfin, fun I => (hνw I).trans (hwμ I).symm⟩

/-- A finitely supported proper randomized algorithm whose maximum expected cost is at most that
of every proper randomized algorithm. -/
theorem exists_finite_support_le (k n : ℕ) :
    ∃ μ : PMF OnlineAlg, IsProperRand μ ∧ μ.support.Finite ∧
      ∀ ν : PMF OnlineAlg, IsProperRand ν → maxExpCost k n μ ≤ maxExpCost k n ν := by
  have := Fintype.ofFinite (costVecs k n)
  rcases isEmpty_or_nonempty (ColInput k n) with hE | hN
  · -- no `k`-colourable input at all: every maximum is `0`
    refine ⟨PMF.pure OnlineAlg.firstFit, isProperRand_pure OnlineAlg.firstFit_isProper, ?_,
      fun ν _ => ?_⟩
    · rw [PMF.support_pure]
      exact Set.finite_singleton _
    · unfold maxExpCost
      rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
  · obtain ⟨w, hw, hmin⟩ := exists_min_weights (k := k) (n := n)
    obtain ⟨μ, hμ, hfin, hμw⟩ := exists_pmf_of_weights hw
    refine ⟨μ, hμ, hfin, fun ν hν => ?_⟩
    obtain ⟨w', hw', hνw⟩ := exists_weights (k := k) (n := n) ν hν
    unfold maxExpCost
    rw [iSup_congr hμw, iSup_congr hνw]
    exact hmin w' hw'

/-- **Definition 4.1, "minimum".** The infimum defining `χ^rand_k(n)` is attained, and by a
randomized algorithm with finite support: some finitely supported probability distribution over
proper deterministic online algorithms has maximum expected cost exactly `χ^rand_k(n)`. -/
theorem exists_finite_support_minimizer (k n : ℕ) :
    ∃ μ : PMF OnlineAlg, IsProperRand μ ∧ μ.support.Finite ∧ maxExpCost k n μ = chiRand k n := by
  obtain ⟨μ, hμ, hfin, hmin⟩ := exists_finite_support_le k n
  refine ⟨μ, hμ, hfin, le_antisymm ?_ ?_⟩
  · rw [chiRand_eq_iInf]
    have := nonempty_properRand
    exact le_ciInf fun ν => hmin ν.1 ν.2
  · rw [chiRand_eq_iInf]
    refine ciInf_le ⟨maxExpCost k n μ, ?_⟩ (⟨μ, hμ⟩ : {μ : PMF OnlineAlg // IsProperRand μ})
    rintro _ ⟨ν, rfl⟩
    exact hmin ν.1 ν.2

/-- **`χ^rand_k(n)` is a minimum over the randomized algorithms** (`PMF OnlineAlg`): it is the
least of their maximum expected costs. -/
theorem chiRand_isLeast (k n : ℕ) :
    IsLeast {c : ℝ | ∃ μ : PMF OnlineAlg, IsProperRand μ ∧ maxExpCost k n μ = c}
      (chiRand k n) := by
  obtain ⟨μ, hμ, -, hmin⟩ := exists_finite_support_le k n
  obtain ⟨μ', hμ', -, heq⟩ := exists_finite_support_minimizer k n
  refine ⟨⟨μ', hμ', heq⟩, ?_⟩
  rintro c ⟨ν, hν, rfl⟩
  rw [chiRand_eq_iInf]
  exact ciInf_le ⟨maxExpCost k n μ, by rintro _ ⟨ρ, rfl⟩; exact hmin ρ.1 ρ.2⟩
    (⟨ν, hν⟩ : {μ : PMF OnlineAlg // IsProperRand μ})

/-- **`χ^rand_k(n)` is the minimum over the finitely supported randomized algorithms**: the value
does not depend on whether "probability distribution" means finitely supported or discrete. -/
theorem chiRand_isLeast_finite (k n : ℕ) :
    IsLeast {c : ℝ | ∃ μ : PMF OnlineAlg, IsProperRand μ ∧ μ.support.Finite ∧
      maxExpCost k n μ = c} (chiRand k n) := by
  obtain ⟨μ, hμ, hfin, heq⟩ := exists_finite_support_minimizer k n
  refine ⟨⟨μ, hμ, hfin, heq⟩, ?_⟩
  rintro c ⟨ν, hν, -, rfl⟩
  exact (chiRand_isLeast k n).2 ⟨ν, hν, rfl⟩

/-- The inner maximum of Definition 4.1 is attained (for `k ≥ 1`): `maxExpCost` is the expected
cost on some `k`-colourable input. -/
theorem exists_expCost_eq_maxExpCost {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (μ : PMF OnlineAlg) :
    ∃ I : OnlineInput n, I.graph.Colorable k ∧ expCost μ I = maxExpCost k n μ := by
  have := nonempty_colorableInput (n := n) hk
  obtain ⟨I, hI⟩ := exists_eq_ciSup_of_finite (f := fun I : ColInput k n => expCost μ I.1)
  exact ⟨I.1, I.2, hI⟩

end Paper

end OnlineColouring
