module

public import OnlineColouring.Online
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Randomized online algorithms and Yao's principle

Definition 4.1 (the randomized half) and Lemma 4.4 (Yao's principle).

* A *randomized online algorithm* is a probability distribution over deterministic online
  algorithms, `μ : PMF OnlineAlg`; it is *proper* (`IsProperRand μ`) if every deterministic
  algorithm in its support is proper.  This is the paper's definition ("probability distributions
  over deterministic ones") for an oblivious adversary: the input is fixed first, and the
  algorithm then draws its deterministic strategy independently of the input.  `PMF` is Mathlib's
  type of probability mass functions, that is, of discrete distributions with any countable
  support.  This choice changes nothing: on the `k`-colourable inputs on `n` vertices, every
  proper randomized algorithm has the same expected costs as one with finite support
  (`Paper.exists_finite_support_expCost_eq`, `PaperRand.lean`), and the same holds for arbitrary
  probability measures over deterministic algorithms (`Paper.exists_finite_support_of_measure`,
  `PaperMeasure.lean`).
* `expCost μ I` is the expected number of colours of `μ` on the input `I` (a real number;
  `expCostE` is the same in `ℝ≥0∞`).
* `ChiRandAtLeast k n x` ("`χ^rand_k(n) ≥ x`"): every proper randomized algorithm has a
  `k`-colourable input on exactly `n` vertices with expected cost at least `x`.
* `chiRand k n` is `χ^rand_k(n)` of Definition 4.1, written as the infimum over proper randomized
  algorithms of the maximum expected cost over `k`-colourable inputs on `n` vertices;
  `le_chiRand_iff : x ≤ chiRand k n ↔ ChiRandAtLeast k n x` (for `k ≥ 1`).  The infimum is
  attained, so it is the minimum of the definition (`Paper.chiRand_isLeast`, `PaperRand.lean`).
* `chiRand_le_chiDet`: `χ^rand_k(n) ≤ χ^det_k(n)`, because a deterministic algorithm is a point
  mass.
* Padding (`padInput`, `ChiRandAtLeast.mono`): appending isolated vertices decreases no cost.
* Lemma 4.4, first sentence (`exists_support_le_expCost`, `yao_expectation`): if every proper
  deterministic algorithm has expected cost at least `x` on a distribution `D` over
  `k`-colourable inputs on exactly `N` vertices, then every proper randomized algorithm has
  expected cost at least `x` on some input in the support of `D`, so `χ^rand_k(n) ≥ x` for every
  `n ≥ N`.  `unifPMF`, `unifInput` and `yao_uniform` are the case of a uniformly random member of
  a finite family of inputs.
* Lemma 4.4, second sentence (`yao`): if `D` makes every proper deterministic algorithm use at
  least `K` colours with probability at least `1 - ε` (`probAtLeast D A K ≥ 1 - ε`), then
  `χ^rand_k(n) ≥ (1 - ε) K` for every `n ≥ N`.
* `ChiRandAtLeast.le_of_le` (smaller bounds) and `ChiRandAtLeast.pad` / `pad_of_pos` (padding,
  for `k ≥ 1` or `x > 0`; `not_chiRandAtLeast_zero_one_zero` shows that a hypothesis is needed).

The statements of Lemma 4.4 for the number `chiRand k n` are `Det.yao_expectation_chiRand` and
`Det.yao_chiRand` (`DetYao.lean`).  The predicate forms of Lemma 4.4 need `k ≥ 1`, which the paper
has throughout.
-/

@[expose] public section

namespace OnlineColouring

open scoped ENNReal

/-! ### Online inputs form a finite type -/

instance (n : ℕ) : Finite (OnlineInput n) :=
  Finite.of_injective (fun I : OnlineInput n => I.nbr) fun _ _ h => OnlineInput.ext h

/-! ### Randomized algorithms and expected costs -/

/-- A randomized online algorithm `μ` (a probability distribution over deterministic online
algorithms) is proper if every deterministic algorithm in its support is proper. -/
def IsProperRand (μ : PMF OnlineAlg) : Prop := ∀ A ∈ μ.support, A.IsProper

/-- The expected cost of the randomized algorithm `μ` on the input `I`, in `ℝ≥0∞`. -/
noncomputable def expCostE (μ : PMF OnlineAlg) {n : ℕ} (I : OnlineInput n) : ℝ≥0∞ :=
  ∑' A, μ A * (I.cost A : ℝ≥0∞)

/-- The expected cost of the randomized algorithm `μ` on the input `I`: the expected number of
distinct colours. -/
noncomputable def expCost (μ : PMF OnlineAlg) {n : ℕ} (I : OnlineInput n) : ℝ :=
  (expCostE μ I).toReal

variable {n : ℕ}

theorem expCostE_le (μ : PMF OnlineAlg) (I : OnlineInput n) : expCostE μ I ≤ n := by
  calc ∑' A, μ A * (I.cost A : ℝ≥0∞) ≤ ∑' A, μ A * (n : ℝ≥0∞) :=
        tsum_le_tsum fun A => mul_le_mul_right (by exact_mod_cast I.cost_le A) _
    _ = n := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

theorem expCostE_ne_top (μ : PMF OnlineAlg) (I : OnlineInput n) : expCostE μ I ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (expCostE_le μ I)

theorem expCost_nonneg (μ : PMF OnlineAlg) (I : OnlineInput n) : 0 ≤ expCost μ I :=
  ENNReal.toReal_nonneg

theorem expCost_le (μ : PMF OnlineAlg) (I : OnlineInput n) : expCost μ I ≤ n := by
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (expCostE_le μ I)
  simpa [expCost] using this

/-- The expected cost of a deterministic algorithm (a point mass) is its cost. -/
theorem expCostE_pure (A : OnlineAlg) (I : OnlineInput n) :
    expCostE (PMF.pure A) I = I.cost A := by
  unfold expCostE
  rw [tsum_eq_single A]
  · simp
  · intro B hB
    simp [PMF.pure_apply, hB]

theorem isProperRand_pure {A : OnlineAlg} (hA : A.IsProper) : IsProperRand (PMF.pure A) := by
  intro B hB
  rw [PMF.mem_support_pure_iff] at hB
  exact hB ▸ hA

/-- Monotonicity of the expected cost in the costs. -/
theorem expCost_mono (μ : PMF OnlineAlg) {m : ℕ} {I : OnlineInput m} {J : OnlineInput n}
    (h : ∀ A, I.cost A ≤ J.cost A) : expCost μ I ≤ expCost μ J := by
  apply ENNReal.toReal_mono (expCostE_ne_top μ J)
  exact tsum_le_tsum fun A => mul_le_mul_right (by exact_mod_cast h A) _

/-! ### `χ^rand` -/

/-- `ChiRandAtLeast k n x` is the statement `χ^rand_k(n) ≥ x`: for every proper randomized online
algorithm there is an online input on exactly `n` vertices whose graph is `k`-colourable and on
which the expected number of colours is at least `x`. -/
def ChiRandAtLeast (k n : ℕ) (x : ℝ) : Prop :=
  ∀ μ : PMF OnlineAlg, IsProperRand μ →
    ∃ I : OnlineInput n, I.graph.Colorable k ∧ x ≤ expCost μ I

/-- Definition 4.1: `χ^rand_k(n)` is the infimum, over proper randomized online algorithms, of
the maximum expected cost over all `k`-colourable online inputs on `n` vertices.  The infimum is
attained (`Paper.chiRand_isLeast`), so it is the minimum of the definition. -/
noncomputable def chiRand (k n : ℕ) : ℝ :=
  ⨅ μ : {μ : PMF OnlineAlg // IsProperRand μ},
    ⨆ I : {I : OnlineInput n // I.graph.Colorable k}, expCost μ.1 I.1

theorem nonempty_properRand : Nonempty {μ : PMF OnlineAlg // IsProperRand μ} :=
  ⟨⟨PMF.pure OnlineAlg.firstFit, isProperRand_pure OnlineAlg.firstFit_isProper⟩⟩

theorem nonempty_colorableInput {k : ℕ} (hk : 1 ≤ k) :
    Nonempty {I : OnlineInput n // I.graph.Colorable k} :=
  ⟨⟨emptyInput n, emptyInput_colorable hk⟩⟩

theorem bddAbove_expCost (k : ℕ) (μ : PMF OnlineAlg) :
    BddAbove (Set.range fun I : {I : OnlineInput n // I.graph.Colorable k} => expCost μ I.1) :=
  ⟨n, by rintro _ ⟨I, rfl⟩; exact expCost_le μ I.1⟩

/-- `chiRand` is an infimum of maxima, so `χ^rand_k(n) ≥ x` holds exactly when every proper
randomized algorithm has a `k`-colourable input with expected cost at least `x`. -/
theorem le_chiRand_iff {k : ℕ} (hk : 1 ≤ k) {x : ℝ} : x ≤ chiRand k n ↔ ChiRandAtLeast k n x := by
  have := nonempty_colorableInput (n := n) hk
  have := nonempty_properRand
  have hbddBelow : BddBelow (Set.range fun μ : {μ : PMF OnlineAlg // IsProperRand μ} =>
      ⨆ I : {I : OnlineInput n // I.graph.Colorable k}, expCost μ.1 I.1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨μ, rfl⟩
    obtain ⟨I⟩ := nonempty_colorableInput (n := n) hk
    exact (expCost_nonneg μ.1 I.1).trans (le_ciSup (bddAbove_expCost k μ.1) I)
  constructor
  · intro hx μ hμ
    have h₁ := hx.trans (ciInf_le hbddBelow ⟨μ, hμ⟩)
    obtain ⟨I, hI⟩ := exists_eq_ciSup_of_finite
      (f := fun I : {I : OnlineInput n // I.graph.Colorable k} => expCost μ I.1)
    exact ⟨I.1, I.2, h₁.trans_eq hI.symm⟩
  · intro h
    apply le_ciInf
    rintro ⟨μ, hμ⟩
    obtain ⟨I, hIc, hI⟩ := h μ hμ
    exact hI.trans (le_ciSup (bddAbove_expCost k μ) ⟨I, hIc⟩)

/-- Sanity check (the definition is not vacuous): no randomized algorithm is forced to use more
than `n` colours on `n` vertices in expectation. -/
theorem not_chiRandAtLeast_succ (k n : ℕ) : ¬ ChiRandAtLeast k n (n + 1) := by
  intro h
  obtain ⟨I, -, hI⟩ := h _ (isProperRand_pure OnlineAlg.firstFit_isProper)
  have := expCost_le (PMF.pure OnlineAlg.firstFit) I
  linarith

/-- A randomized lower bound is at most the deterministic one: `χ^rand_k(n) ≥ K` implies
`χ^det_k(n) ≥ K` (apply it to point masses). -/
theorem ChiRandAtLeast.chiDetAtLeast {k K : ℕ} (h : ChiRandAtLeast k n K) :
    ChiDetAtLeast k n K := by
  intro A hA
  obtain ⟨I, hc, hI⟩ := h _ (isProperRand_pure hA)
  refine ⟨I, hc, ?_⟩
  have : expCost (PMF.pure A) I = I.cost A := by simp [expCost, expCostE_pure]
  exact_mod_cast hI.trans_eq this

/-- **`χ^det_k(n) ≥ χ^rand_k(n)`**: a proper deterministic algorithm is the point mass on it. -/
theorem chiRand_le_chiDet {k n : ℕ} (hk : 1 ≤ k) : chiRand k n ≤ chiDet k n := by
  obtain ⟨A, hA, hmax⟩ := exists_maxCost_eq_chiDet k n
  obtain ⟨I, hI, hle⟩ := (le_chiRand_iff (n := n) hk).1 le_rfl (PMF.pure A) (isProperRand_pure hA)
  have hcost : expCost (PMF.pure A) I = I.cost A := by simp [expCost, expCostE_pure]
  have hc : I.cost A ≤ maxCost A k n := (le_maxCost_iff hk).2 ⟨I, hI, le_rfl⟩
  calc chiRand k n ≤ expCost (PMF.pure A) I := hle
    _ = I.cost A := hcost
    _ ≤ chiDet k n := by rw [← hmax]; exact_mod_cast hc

theorem ChiRandAtLeast.of_le {k : ℕ} {x y : ℝ} (hxy : y ≤ x) (h : ChiRandAtLeast k n x) :
    ChiRandAtLeast k n y := by
  intro μ hμ
  obtain ⟨I, hc, hI⟩ := h μ hμ
  exact ⟨I, hc, hxy.trans hI⟩

/-- Every algorithm uses at least one colour on a nonempty input. -/
theorem one_le_cost {I : OnlineInput n} (hn : 1 ≤ n) (A : OnlineAlg) : 1 ≤ I.cost A := by
  unfold OnlineInput.cost
  exact Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn⟩)⟩

theorem one_le_expCost {I : OnlineInput n} (hn : 1 ≤ n) (μ : PMF OnlineAlg) :
    1 ≤ expCost μ I := by
  have h : (1 : ℝ≥0∞) ≤ expCostE μ I := by
    calc (1 : ℝ≥0∞) = ∑' A, μ A * 1 := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
      _ ≤ _ := tsum_le_tsum fun A =>
          mul_le_mul_right (by exact_mod_cast one_le_cost hn A) _
  simpa [expCost] using ENNReal.toReal_mono (expCostE_ne_top μ I) h

theorem chiRandAtLeast_one {k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : ChiRandAtLeast k n 1 := by
  intro μ _
  exact ⟨emptyInput n, emptyInput_colorable hk, one_le_expCost hn μ⟩

theorem chiRandAtLeast_zero {k : ℕ} (hk : 1 ≤ k) : ChiRandAtLeast k n 0 := by
  intro μ _
  exact ⟨emptyInput n, emptyInput_colorable hk, expCost_nonneg μ _⟩

/-! ### Padding -/

/-- The input `I` on `m` vertices followed by isolated vertices, up to `n` vertices. -/
def padInput {m : ℕ} (I : OnlineInput m) (n : ℕ) : OnlineInput n :=
  OnlineInput.ofSeq (truncSeq I.seq m) (truncSeq_valid I.seq_valid m) n

theorem colorable_padInput {m k : ℕ} (hk : 1 ≤ k) {I : OnlineInput m} (hI : I.graph.Colorable k)
    (n : ℕ) : (padInput I n).graph.Colorable k := by
  apply colorable_truncSeq I.seq_valid hk
  rwa [OnlineInput.ofSeq_seq]

theorem cost_le_padInput {m : ℕ} (hmn : m ≤ n) (I : OnlineInput m) (A : OnlineAlg) :
    I.cost A ≤ (padInput I n).cost A := by
  apply le_cost_truncSeq I.seq_valid hmn
  rw [← OnlineInput.cost_ofSeq (hN := I.seq_valid), OnlineInput.ofSeq_seq]

/-- `χ^rand_k(n)` is non-decreasing in `n`: appending isolated vertices decreases no cost. -/
theorem ChiRandAtLeast.mono {k m : ℕ} {x : ℝ} (hk : 1 ≤ k) (hmn : m ≤ n)
    (h : ChiRandAtLeast k m x) : ChiRandAtLeast k n x := by
  intro μ hμ
  obtain ⟨I, hc, hI⟩ := h μ hμ
  exact ⟨padInput I n, colorable_padInput hk hc n,
    hI.trans (expCost_mono μ (cost_le_padInput hmn I))⟩

/-- **Monotonicity in the bound.** `χ^rand_k(n) ≥ x` and `x' ≤ x` give `χ^rand_k(n) ≥ x'`. -/
theorem ChiRandAtLeast.le_of_le {k : ℕ} {x x' : ℝ} (h : ChiRandAtLeast k n x) (hx : x' ≤ x) :
    ChiRandAtLeast k n x' :=
  h.of_le hx

/-- **Padding.** `χ^rand_k(n) ≥ x` and `n ≤ n'` give `χ^rand_k(n') ≥ x`, if `k ≥ 1`. -/
theorem ChiRandAtLeast.pad {k n' : ℕ} {x : ℝ} (h : ChiRandAtLeast k n x) (hn : n ≤ n')
    (hk : 1 ≤ k) : ChiRandAtLeast k n' x :=
  h.mono hk hn

/-- **Padding**, when `x > 0`: then `k ≥ 1` is automatic. -/
theorem ChiRandAtLeast.pad_of_pos {k n' : ℕ} {x : ℝ} (h : ChiRandAtLeast k n x) (hn : n ≤ n')
    (hx : 0 < x) : ChiRandAtLeast k n' x := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- on `0` vertices every expected cost is `0`, so the hypothesis is contradictory
    subst h0
    obtain ⟨I, -, hI⟩ := h _ (isProperRand_pure OnlineAlg.firstFit_isProper)
    have := expCost_le (PMF.pure OnlineAlg.firstFit) I
    push_cast at this
    linarith
  · obtain ⟨I, hc, -⟩ := h _ (isProperRand_pure OnlineAlg.firstFit_isProper)
    obtain ⟨col⟩ := hc
    have hk : 1 ≤ k := by
      have := (col ⟨0, hpos⟩).2
      omega
    exact h.mono hk hn

/-- The hypothesis `k ≥ 1` (or `x > 0`) of padding cannot be dropped: the empty graph on `0`
vertices is `0`-colourable, but no graph on `1` vertex is. -/
theorem chiRandAtLeast_zero_zero_zero : ChiRandAtLeast 0 0 0 := by
  intro μ _
  refine ⟨emptyInput 0, ⟨SimpleGraph.Coloring.mk (fun v => v.elim0) fun {v} => v.elim0⟩,
    expCost_nonneg μ _⟩

theorem not_chiRandAtLeast_zero_one_zero : ¬ ChiRandAtLeast 0 1 0 := by
  intro h
  obtain ⟨I, ⟨col⟩, -⟩ := h _ (isProperRand_pure OnlineAlg.firstFit_isProper)
  exact (col ⟨0, Nat.one_pos⟩).elim0

/-! ### Yao's principle -/

/-- The probability that the deterministic algorithm `A` uses at least `K` colours on an input
drawn from the distribution `D`. -/
noncomputable def probAtLeast {N : ℕ} (D : PMF (OnlineInput N)) (A : OnlineAlg) (K : ℕ) : ℝ :=
  (D.toOuterMeasure {I | K ≤ I.cost A}).toReal

theorem probAtLeast_nonneg {N : ℕ} (D : PMF (OnlineInput N)) (A : OnlineAlg) (K : ℕ) :
    0 ≤ probAtLeast D A K := ENNReal.toReal_nonneg

theorem toOuterMeasure_le_one {α : Type*} (D : PMF α) (s : Set α) : D.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← D.tsum_coe]
  exact tsum_le_tsum fun x => Set.indicator_apply_le fun _ => le_rfl

theorem toOuterMeasure_ne_top {α : Type*} (D : PMF α) (s : Set α) : D.toOuterMeasure s ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_le_one D s)

theorem ofReal_le_toOuterMeasure {α : Type*} {D : PMF α} {s : Set α} {x : ℝ}
    (h : x ≤ (D.toOuterMeasure s).toReal) : ENNReal.ofReal x ≤ D.toOuterMeasure s :=
  (ENNReal.ofReal_le_iff_le_toReal (toOuterMeasure_ne_top D s)).2 h

/-- First moment: if `A` uses `K` colours with probability at least `1 - ε`, its expected cost is
at least `(1 - ε) K`. -/
theorem ofReal_le_tsum_cost {N K : ℕ} {ε : ℝ} (D : PMF (OnlineInput N)) (A : OnlineAlg)
    (h : 1 - ε ≤ probAtLeast D A K) :
    ENNReal.ofReal ((1 - ε) * K) ≤ ∑' I, D I * (I.cost A : ℝ≥0∞) := by
  rw [ENNReal.ofReal_mul' (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
  calc ENNReal.ofReal (1 - ε) * K ≤ D.toOuterMeasure {I | K ≤ I.cost A} * K :=
        mul_le_mul_left (ofReal_le_toOuterMeasure h) _
    _ = ∑' I, {I | K ≤ I.cost A}.indicator D I * K := by
        rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]
    _ ≤ ∑' I, D I * (I.cost A : ℝ≥0∞) := by
        refine tsum_le_tsum fun I => ?_
        by_cases hI : K ≤ I.cost A
        · rw [Set.indicator_of_mem (by exact hI)]
          exact mul_le_mul_right (by exact_mod_cast hI) _
        · rw [Set.indicator_of_notMem (by exact hI), zero_mul]
          exact zero_le

/-- The expected cost of the deterministic algorithm `A` on an input drawn from `D`. -/
noncomputable def detExpCost {N : ℕ} (D : PMF (OnlineInput N)) (A : OnlineAlg) : ℝ :=
  (∑' I, D I * (I.cost A : ℝ≥0∞)).toReal

theorem tsum_cost_le {N : ℕ} (D : PMF (OnlineInput N)) (A : OnlineAlg) :
    ∑' I, D I * (I.cost A : ℝ≥0∞) ≤ N := by
  calc ∑' I, D I * (I.cost A : ℝ≥0∞) ≤ ∑' I, D I * (N : ℝ≥0∞) :=
        tsum_le_tsum fun I => mul_le_mul_right (by exact_mod_cast I.cost_le A) _
    _ = N := by rw [ENNReal.tsum_mul_right, D.tsum_coe, one_mul]

theorem ofReal_le_tsum_of_le_detExpCost {N : ℕ} {D : PMF (OnlineInput N)} {A : OnlineAlg} {x : ℝ}
    (h : x ≤ detExpCost D A) : ENNReal.ofReal x ≤ ∑' I, D I * (I.cost A : ℝ≥0∞) :=
  (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (tsum_cost_le D A))).2 h

/-- **Lemma 4.4 (Yao's principle), expectation form, before padding.** If every proper deterministic
algorithm has expected cost at least `x` on `I ∼ D`, then every proper randomized algorithm has
expected cost at least `x` on some input in the support of `D`. -/
theorem exists_support_le_expCost {N : ℕ} {x : ℝ} (D : PMF (OnlineInput N))
    (hforce : ∀ A : OnlineAlg, A.IsProper → x ≤ detExpCost D A)
    (μ : PMF OnlineAlg) (hμ : IsProperRand μ) :
    ∃ I ∈ D.support, x ≤ expCost μ I := by
  set y := ENNReal.ofReal x
  -- Fubini: the expected cost of `μ` on `I ∼ D` is at least `y`
  have hfub : y ≤ ∑' I, D I * expCostE μ I := by
    calc y = ∑' A, μ A * y := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
      _ ≤ ∑' A, μ A * ∑' I, D I * (I.cost A : ℝ≥0∞) := by
          refine tsum_le_tsum fun A => ?_
          by_cases hA : A ∈ μ.support
          · exact mul_le_mul_right (ofReal_le_tsum_of_le_detExpCost (hforce A (hμ A hA))) _
          · rw [(PMF.apply_eq_zero_iff μ A).2 hA, zero_mul, zero_mul]
      _ = ∑' I, D I * expCostE μ I := by
          simp only [expCostE, ← ENNReal.tsum_mul_left]
          rw [tsum_comm]
          congr 1; funext I; congr 1; funext A
          ring
  -- so some input in the support of `D` has expected cost at least `y`
  have hex : ∃ I ∈ D.support, y ≤ expCostE μ I := by
    by_contra hcon
    push Not at hcon
    obtain ⟨I₀, hI₀⟩ := D.support_nonempty
    have hlt : ∑' I, D I * expCostE μ I < ∑' I, D I * y := by
      refine ENNReal.tsum_lt_tsum (i := I₀) ?_ (fun I => ?_) ?_
      · refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) ?_
        calc ∑' I, D I * expCostE μ I ≤ ∑' I, D I * (N : ℝ≥0∞) :=
              tsum_le_tsum fun I => mul_le_mul_right (expCostE_le μ I) _
          _ = N := by rw [ENNReal.tsum_mul_right, D.tsum_coe, one_mul]
      · by_cases hI : I ∈ D.support
        · exact mul_le_mul_right (hcon I hI).le _
        · rw [(PMF.apply_eq_zero_iff D I).2 hI, zero_mul, zero_mul]
      · exact ENNReal.mul_lt_mul_right ((PMF.mem_support_iff D I₀).1 hI₀) (D.apply_ne_top I₀)
          (hcon I₀ hI₀)
    rw [ENNReal.tsum_mul_right, D.tsum_coe, one_mul] at hlt
    exact absurd hfub (not_le.2 hlt)
  obtain ⟨I, hID, hI⟩ := hex
  refine ⟨I, hID, ?_⟩
  calc x ≤ y.toReal := by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    _ ≤ expCost μ I := ENNReal.toReal_mono (expCostE_ne_top μ I) hI

/-- **Lemma 4.4 (Yao's principle), expectation form.** Let `D` be a distribution over `k`-colourable
online inputs on exactly `N` vertices such that every proper deterministic online algorithm has
expected cost at least `x` on `I ∼ D`.  Then `χ^rand_k(n) ≥ x` for every `n ≥ N`. -/
theorem yao_expectation {k N : ℕ} {x : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n) (D : PMF (OnlineInput N))
    (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → x ≤ detExpCost D A) :
    ChiRandAtLeast k n x := by
  intro μ hμ
  obtain ⟨I, hID, hI⟩ := exists_support_le_expCost D hforce μ hμ
  exact ⟨padInput I n, colorable_padInput hk (hcol I hID) n,
    hI.trans (expCost_mono μ (cost_le_padInput hNn I))⟩

/-- **Lemma 4.4 (Yao's principle), second sentence.** Let `D` be a distribution over `k`-colourable
online inputs on exactly `N` vertices such that every proper deterministic online algorithm uses
at least `K` colours with probability at least `1 - ε` on `I ∼ D`.  Then
`χ^rand_k(n) ≥ (1 - ε) K` for every `n ≥ N`. -/
theorem yao {k N K : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n) (D : PMF (OnlineInput N))
    (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → 1 - ε ≤ probAtLeast D A K) :
    ChiRandAtLeast k n ((1 - ε) * K) := by
  refine yao_expectation hk hNn D hcol fun A hA => ?_
  have h := ofReal_le_tsum_cost D A (hforce A hA)
  have hne := ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (tsum_cost_le D A)
  calc (1 - ε) * K ≤ (ENNReal.ofReal ((1 - ε) * K)).toReal := by
        rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    _ ≤ detExpCost D A := ENNReal.toReal_mono hne h

/-! ### Uniform distributions over finitely many inputs -/

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def unifPMF (Ω : Type*) [Fintype Ω] [Nonempty Ω] : PMF Ω :=
  PMF.ofFintype (fun _ : Ω => ((Fintype.card Ω : ℝ≥0∞))⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _))

theorem unifPMF_apply {Ω : Type*} [Fintype Ω] [Nonempty Ω] (ω : Ω) :
    unifPMF Ω ω = ((Fintype.card Ω : ℝ≥0∞))⁻¹ := rfl

/-- The image of the uniform distribution on a nonempty finite type `Ω` under `inp`. -/
noncomputable def unifInput {Ω : Type*} [Fintype Ω] [Nonempty Ω] {N : ℕ}
    (inp : Ω → OnlineInput N) : PMF (OnlineInput N) :=
  (unifPMF Ω).map inp

theorem mem_support_unifInput {Ω : Type*} [Fintype Ω] [Nonempty Ω] {N : ℕ}
    {inp : Ω → OnlineInput N} {I : OnlineInput N} (h : I ∈ (unifInput inp).support) :
    ∃ ω, inp ω = I := by
  obtain ⟨ω, -, hω⟩ := (PMF.mem_support_map_iff _ _ _).1 h
  exact ⟨ω, hω⟩

/-- The expected cost on the image of a uniform distribution is the average cost. -/
theorem detExpCost_unifInput {Ω : Type*} [Fintype Ω] [Nonempty Ω] {N : ℕ}
    (inp : Ω → OnlineInput N) (A : OnlineAlg) :
    detExpCost (unifInput inp) A = (∑ ω, ((inp ω).cost A : ℝ)) / Fintype.card Ω := by
  classical
  unfold detExpCost unifInput
  have h : ∑' I, (PMF.map inp (unifPMF Ω)) I *
      ((I.cost A : ℕ) : ℝ≥0∞) = ∑ ω : Ω, ((Fintype.card Ω : ℝ≥0∞))⁻¹ * ((inp ω).cost A : ℝ≥0∞) := by
    simp only [PMF.map_apply, unifPMF_apply, ← ENNReal.tsum_mul_right]
    rw [tsum_comm, tsum_fintype]
    congr 1
    funext ω
    rw [tsum_eq_single (inp ω)]
    · simp
    · intro I hI
      simp [hI]
  rw [h, ← Finset.mul_sum, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => ENNReal.natCast_ne_top _)]
  simp only [ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]

/-- **Yao's principle for a uniform family of inputs.** If `inp : Ω → OnlineInput N` (`Ω` a
nonempty finite type) takes only `k`-colourable values and every proper deterministic algorithm
has average cost at least `x` over `ω ∈ Ω`, then `χ^rand_k(n) ≥ x` for every `n ≥ N`. -/
theorem yao_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] {k N : ℕ} {x : ℝ} (hk : 1 ≤ k)
    (hNn : N ≤ n) (inp : Ω → OnlineInput N) (hcol : ∀ ω, (inp ω).graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper →
      x ≤ (∑ ω, ((inp ω).cost A : ℝ)) / Fintype.card Ω) :
    ChiRandAtLeast k n x := by
  refine yao_expectation hk hNn (unifInput inp) (fun I hI => ?_) fun A hA => ?_
  · obtain ⟨ω, rfl⟩ := mem_support_unifInput hI
    exact hcol ω
  · rw [detExpCost_unifInput]
    exact hforce A hA

end OnlineColouring
