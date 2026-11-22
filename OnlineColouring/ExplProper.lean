module

public import OnlineColouring.ProbForcing
public import OnlineColouring.KnownGame
public import OnlineColouring.Det
public import OnlineColouring.PaperStatements

/-!
# Properness bridges: only the histories that occur matter

The paper (Section 4, first paragraph) requires of an online algorithm that the colour of a new
vertex differs from the colours of its earlier neighbours.  The library states this as
`OnlineAlg.IsProper`, which constrains the algorithm on *every* history, including histories that
cannot occur.  All lower bounds quantify over proper algorithms, so one may ask whether they also
hold for algorithms that colour properly only where it matters.  They do: an algorithm `A` can be
patched (`OnlineAlg.patch`: answer a fresh colour wherever the answer of `A` would clash) into an
algorithm that is proper on every history and behaves exactly like `A` on every input, or in
every play, that `A` colours properly.  `ChiDetAtLeast.of_isProperOn` (`Online.lean`) is this
statement for `χ^det`.  This file proves it for the other notions, each time as an equivalence
with the weakest sensible properness hypothesis.

* `ProperOn A I`: `A` colours the input `I` properly.  `run_patch_of_properOn`,
  `cost_patch_of_properOn`: then `A.patch` and `A` agree on `I`.
* `χ^det` (`chiDetAtLeast_iff_properOn`, `chiDet_eq_sInf_properOn`): it is enough that the
  algorithm colours the `k`-colourable inputs on `n` vertices properly.
* `χ^rand` (`chiRandAtLeast_iff_properOn`, `chiRand_eq_iInf_properOn`): it is enough that every
  deterministic algorithm in the support does (`IsProperRandOn`).  Patching a randomized
  algorithm is `PMF.map OnlineAlg.patch` (`expCost_map_patch`, `isProperRand_map_patch`).
* Known graphs (`onlineChromaticAtLeast_iff_properOn`, `chiOl_eq_sInf_properOn`,
  `randKnownAtLeast_iff_properOn`): it is enough that the algorithm colours every presentation of
  `G` properly (`ProperOnPres`).
* `ProbForcing` (`probForcing_iff_properOn`): the same distribution works against every algorithm
  that colours the inputs in its support properly; `probAtLeast_patch` is the corresponding fact
  for `probAtLeast` (the form used in Appendix C).
* `chiRandAtLeast_of_isProperOn`, `onlineChromaticAtLeast_of_isProperOn`,
  `randKnownAtLeast_of_isProperOn`, `probForcing_of_isProperOn`: the literal analogues of
  `ChiDetAtLeast.of_isProperOn`, with `OnlineAlg.IsProperOn n` as the hypothesis.
* Adversaries: `ProperAgainst adv A` says that `A` answers properly in its play against `adv`,
  equivalently (`properAgainst_iff_properHist`) that every history of that play is properly
  coloured.  Then the plays against `A` and `A.patch` coincide (`hist_patch`), so every notion
  of the form "for every proper algorithm, the play satisfies …" is unchanged
  (`forall_isProper_iff_properAgainst`): `forces_iff_properAgainst`,
  `commitsTo_iff_properAgainst`, `sizeLE_iff_properAgainst`, `postDegLE_iff_properAgainst`,
  `landsIn_iff_properAgainst`, `nkLE_iff_properAgainst`, and Proposition 9.4 in this form
  (`le_card_jst_of_properAgainst`).
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset
open scoped ENNReal

/-! ### Algorithms that colour one input properly -/

/-- `A` colours the online input `I` properly. -/
def ProperOn (A : OnlineAlg) {n : ℕ} (I : OnlineInput n) : Prop :=
  ∀ u v : Fin n, I.graph.Adj u v → I.run A u ≠ I.run A v

theorem isProperOn_iff (A : OnlineAlg) (n : ℕ) :
    A.IsProperOn n ↔ ∀ I : OnlineInput n, ProperOn A I := Iff.rfl

theorem properOn_of_isProper {A : OnlineAlg} (hA : A.IsProper) {n : ℕ} (I : OnlineInput n) :
    ProperOn A I := fun _ _ h => I.run_ne_of_adj hA h

/-- On an input that `A` colours properly, the patched algorithm behaves exactly like `A`. -/
theorem run_patch_of_properOn {A : OnlineAlg} {n : ℕ} {I : OnlineInput n} (hA : ProperOn A I) :
    I.run A.patch = I.run A := by
  have key : ∀ i < n, runCol A.patch I.seq i = runCol A I.seq i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi
    have hhist : runHist A.patch I.seq i = runHist A I.seq i := by
      rw [runHist_eq_map, runHist_eq_map]
      exact List.map_congr_left fun j hj => by
        rw [ih j (List.mem_range.1 hj) ((List.mem_range.1 hj).trans hi)]
    change (if A.step _ _ ∈ nbrColours _ _ then _ else _) = _
    rw [hhist, nbrColours_runHist (I.seq_valid i), ite_eq_right]
    · rfl
    intro hmem
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hmem
    simp only [OnlineInput.seq, hi, ↓reduceDIte, Finset.mem_map, Fin.valEmbedding_apply] at hj
    obtain ⟨u, hu, rfl⟩ := hj
    exact hA u ⟨i, hi⟩ (Or.inl hu) hji
  funext v
  exact key v v.2

theorem cost_patch_of_properOn {A : OnlineAlg} {n : ℕ} {I : OnlineInput n} (hA : ProperOn A I) :
    I.cost A.patch = I.cost A := by
  unfold OnlineInput.cost
  rw [run_patch_of_properOn hA]

/-! ### `χ^det` -/

/-- **`χ^det`: properness is needed only on the `k`-colourable inputs on `n` vertices.**
`χ^det_k(n) ≥ K` iff every algorithm that colours the `k`-colourable inputs on `n` vertices
properly uses at least `K` colours on one of them. -/
theorem chiDetAtLeast_iff_properOn {k n K : ℕ} :
    ChiDetAtLeast k n K ↔ ∀ A : OnlineAlg,
      (∀ I : OnlineInput n, I.graph.Colorable k → ProperOn A I) →
      ∃ I : OnlineInput n, I.graph.Colorable k ∧ K ≤ I.cost A := by
  constructor
  · intro h A hA
    obtain ⟨I, hc, hK⟩ := h A.patch A.patch_isProper
    exact ⟨I, hc, by rwa [cost_patch_of_properOn (hA I hc)] at hK⟩
  · intro h A hA
    exact h A fun I _ => properOn_of_isProper hA I

theorem maxCost_patch {A : OnlineAlg} {k n : ℕ}
    (hA : ∀ I : OnlineInput n, I.graph.Colorable k → ProperOn A I) :
    maxCost A.patch k n = maxCost A k n := by
  unfold maxCost
  congr 1
  ext c
  constructor
  · rintro ⟨I, hc, rfl⟩
    exact ⟨I, hc, (cost_patch_of_properOn (hA I hc)).symm⟩
  · rintro ⟨I, hc, rfl⟩
    exact ⟨I, hc, cost_patch_of_properOn (hA I hc)⟩

/-- `χ^det_k(n)` is also the minimum, over the algorithms that colour the `k`-colourable inputs
on `n` vertices properly, of the maximum cost. -/
theorem chiDet_eq_sInf_properOn (k n : ℕ) :
    chiDet k n = sInf {c | ∃ A : OnlineAlg,
      (∀ I : OnlineInput n, I.graph.Colorable k → ProperOn A I) ∧ maxCost A k n = c} := by
  unfold chiDet
  congr 1
  ext c
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, fun I _ => properOn_of_isProper hA I, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A.patch, A.patch_isProper, maxCost_patch hA⟩

/-! ### `χ^rand` -/

/-- The expected cost of the image of a randomized algorithm under a map of deterministic
algorithms. -/
theorem expCostE_map (μ : PMF OnlineAlg) (f : OnlineAlg → OnlineAlg) {n : ℕ}
    (I : OnlineInput n) :
    expCostE (μ.map f) I = ∑' A, μ A * (I.cost (f A) : ℝ≥0∞) := by
  classical
  unfold expCostE
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  congr 1
  funext A
  rw [tsum_eq_single (f A)]
  · simp
  · intro B hB
    simp [hB]

/-- Patching every deterministic algorithm in the support does not change the expected cost on an
input that all of them colour properly. -/
theorem expCost_map_patch {μ : PMF OnlineAlg} {n : ℕ} {I : OnlineInput n}
    (h : ∀ A ∈ μ.support, ProperOn A I) : expCost (μ.map OnlineAlg.patch) I = expCost μ I := by
  have e : expCostE (μ.map OnlineAlg.patch) I = expCostE μ I := by
    rw [expCostE_map]
    unfold expCostE
    apply tsum_congr
    intro A
    by_cases hA : A ∈ μ.support
    · rw [cost_patch_of_properOn (h A hA)]
    · rw [(PMF.apply_eq_zero_iff μ A).2 hA, zero_mul, zero_mul]
  unfold expCost
  rw [e]

theorem isProperRand_map_patch (μ : PMF OnlineAlg) : IsProperRand (μ.map OnlineAlg.patch) := by
  intro B hB
  obtain ⟨A, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hB
  exact A.patch_isProper

/-- The randomized algorithm `μ` colours the `k`-colourable inputs on `n` vertices properly: every
deterministic algorithm in its support does. -/
def IsProperRandOn (μ : PMF OnlineAlg) (k n : ℕ) : Prop :=
  ∀ A ∈ μ.support, ∀ I : OnlineInput n, I.graph.Colorable k → ProperOn A I

theorem isProperRandOn_of_isProperRand {μ : PMF OnlineAlg} (hμ : IsProperRand μ) (k n : ℕ) :
    IsProperRandOn μ k n := fun A hA I _ => properOn_of_isProper (hμ A hA) I

/-- **`χ^rand`: properness is needed only on the `k`-colourable inputs on `n` vertices.** -/
theorem chiRandAtLeast_iff_properOn {k n : ℕ} {x : ℝ} :
    ChiRandAtLeast k n x ↔ ∀ μ : PMF OnlineAlg, IsProperRandOn μ k n →
      ∃ I : OnlineInput n, I.graph.Colorable k ∧ x ≤ expCost μ I := by
  constructor
  · intro h μ hμ
    obtain ⟨I, hc, hx⟩ := h _ (isProperRand_map_patch μ)
    exact ⟨I, hc, by rwa [expCost_map_patch fun A hA => hμ A hA I hc] at hx⟩
  · intro h μ hμ
    exact h μ (isProperRandOn_of_isProperRand hμ k n)

/-- `χ^rand_k(n)` is also the infimum, over the randomized algorithms that colour the
`k`-colourable inputs on `n` vertices properly, of the maximum expected cost. -/
theorem chiRand_eq_iInf_properOn (k n : ℕ) :
    chiRand k n = ⨅ μ : {μ : PMF OnlineAlg // IsProperRandOn μ k n},
      ⨆ I : {I : OnlineInput n // I.graph.Colorable k}, expCost μ.1 I.1 := by
  have hrange : (Set.range fun μ : {μ : PMF OnlineAlg // IsProperRand μ} =>
      ⨆ I : {I : OnlineInput n // I.graph.Colorable k}, expCost μ.1 I.1) =
      Set.range fun μ : {μ : PMF OnlineAlg // IsProperRandOn μ k n} =>
        ⨆ I : {I : OnlineInput n // I.graph.Colorable k}, expCost μ.1 I.1 := by
    ext c
    constructor
    · rintro ⟨⟨μ, hμ⟩, rfl⟩
      exact ⟨⟨μ, isProperRandOn_of_isProperRand hμ k n⟩, rfl⟩
    · rintro ⟨⟨μ, hμ⟩, rfl⟩
      refine ⟨⟨μ.map OnlineAlg.patch, isProperRand_map_patch μ⟩, ?_⟩
      exact iSup_congr fun I => expCost_map_patch fun A hA => hμ A hA I.1 I.2
  unfold chiRand iInf
  rw [hrange]

/-- A randomized algorithm that colours the `k`-colourable inputs on `n` vertices properly has
maximum expected cost at least `χ^rand_k(n)`. -/
theorem chiRand_le_of_properOn {k n : ℕ} (hk : 1 ≤ k) {μ : PMF OnlineAlg}
    (hμ : IsProperRandOn μ k n) :
    ∃ I : OnlineInput n, I.graph.Colorable k ∧ chiRand k n ≤ expCost μ I :=
  chiRandAtLeast_iff_properOn.1 ((le_chiRand_iff hk).1 le_rfl) μ hμ

/-! ### Known graphs -/

/-- `A` colours every presentation of `G` properly: this is all that can be asked of an algorithm
that knows `G`. -/
def ProperOnPres (A : OnlineAlg) {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ I : OnlineInput N, Nonempty (I.graph ≃g G) → ProperOn A I

/-- **`χ_ol(G) ≥ K`: properness is needed only on the presentations of `G`.** -/
theorem onlineChromaticAtLeast_iff_properOn {N : ℕ} {G : SimpleGraph (Fin N)} {K : ℕ} :
    OnlineChromaticAtLeast G K ↔ ∀ A : OnlineAlg, ProperOnPres A G →
      ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ K ≤ I.cost A := by
  constructor
  · intro h A hA
    obtain ⟨I, hI, hK⟩ := h A.patch A.patch_isProper
    exact ⟨I, hI, by rwa [cost_patch_of_properOn (hA I hI)] at hK⟩
  · intro h A hA
    exact h A fun I _ => properOn_of_isProper hA I

/-- `χ_ol(G)` is also the least `c` such that some algorithm that colours every presentation of
`G` properly uses at most `c` colours on every presentation of `G`. -/
theorem chiOl_eq_sInf_properOn {N : ℕ} (G : SimpleGraph (Fin N)) :
    Paper.chiOl G = sInf {c | ∃ A : OnlineAlg, ProperOnPres A G ∧
      ∀ I : OnlineInput N, Nonempty (I.graph ≃g G) → I.cost A ≤ c} := by
  unfold Paper.chiOl
  congr 1
  ext c
  constructor
  · rintro ⟨A, hA, hc⟩
    exact ⟨A, fun I _ => properOn_of_isProper hA I, hc⟩
  · rintro ⟨A, hA, hc⟩
    refine ⟨A.patch, A.patch_isProper, fun I hI => ?_⟩
    rw [cost_patch_of_properOn (hA I hI)]
    exact hc I hI

/-- **The randomized known-graph bound: properness is needed only on the presentations of
`G`.** -/
theorem randKnownAtLeast_iff_properOn {N : ℕ} {G : SimpleGraph (Fin N)} {x : ℝ} :
    RandKnownAtLeast G x ↔ ∀ μ : PMF OnlineAlg, (∀ A ∈ μ.support, ProperOnPres A G) →
      ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ x ≤ expCost μ I := by
  constructor
  · intro h μ hμ
    obtain ⟨I, hI, hx⟩ := h _ (isProperRand_map_patch μ)
    exact ⟨I, hI, by rwa [expCost_map_patch fun A hA => hμ A hA I hI] at hx⟩
  · intro h μ hμ
    exact h μ fun A hA I _ => properOn_of_isProper (hμ A hA) I

/-! ### Forcing with a given probability -/

/-- The events "`A.patch` uses at least `x` colours" and "`A` uses at least `x` colours" have the
same probability under a distribution on whose support `A` colours properly. -/
theorem toOuterMeasure_cost_patch {n : ℕ} (D : PMF (OnlineInput n)) {A : OnlineAlg}
    (hA : ∀ I ∈ D.support, ProperOn A I) (x : ℝ) :
    D.toOuterMeasure {I | x ≤ (I.cost A.patch : ℝ)} =
      D.toOuterMeasure {I | x ≤ (I.cost A : ℝ)} := by
  rw [← PMF.toOuterMeasure_apply_inter_support D {I | x ≤ (I.cost A.patch : ℝ)},
    ← PMF.toOuterMeasure_apply_inter_support D {I | x ≤ (I.cost A : ℝ)}]
  congr 1
  ext I
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    change x ≤ (I.cost A.patch : ℝ) at h1
    change x ≤ (I.cost A : ℝ)
    rwa [cost_patch_of_properOn (hA I h2)] at h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    change x ≤ (I.cost A : ℝ) at h1
    change x ≤ (I.cost A.patch : ℝ)
    rwa [cost_patch_of_properOn (hA I h2)]

/-- **`ProbForcing`: properness is needed only on the support of the distribution.**  The
distribution that witnesses `ProbForcing k n x p` makes every algorithm that colours the inputs in
its support properly use at least `x` colours with probability at least `p`. -/
theorem probForcing_iff_properOn {k n : ℕ} {x p : ℝ} :
    ProbForcing k n x p ↔ ∃ D : PMF (OnlineInput n), (∀ I ∈ D.support, I.graph.Colorable k) ∧
      ∀ A : OnlineAlg, (∀ I ∈ D.support, ProperOn A I) →
        ENNReal.ofReal p ≤ D.toOuterMeasure {I | x ≤ (I.cost A : ℝ)} := by
  constructor
  · rintro ⟨D, hcol, hD⟩
    refine ⟨D, hcol, fun A hA => ?_⟩
    rw [← toOuterMeasure_cost_patch D hA]
    exact hD A.patch A.patch_isProper
  · rintro ⟨D, hcol, hD⟩
    exact ⟨D, hcol, fun A hA => hD A fun I _ => properOn_of_isProper hA I⟩

/-- The same for `probAtLeast` (the probability that `A` uses at least `K` colours). -/
theorem probAtLeast_patch {n : ℕ} (D : PMF (OnlineInput n)) {A : OnlineAlg}
    (hA : ∀ I ∈ D.support, ProperOn A I) (K : ℕ) :
    probAtLeast D A.patch K = probAtLeast D A K := by
  unfold probAtLeast
  rw [← PMF.toOuterMeasure_apply_inter_support D {I | K ≤ I.cost A.patch},
    ← PMF.toOuterMeasure_apply_inter_support D {I | K ≤ I.cost A}]
  congr 2
  ext I
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    change K ≤ I.cost A.patch at h1
    change K ≤ I.cost A
    rwa [cost_patch_of_properOn (hA I h2)] at h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    change K ≤ I.cost A at h1
    change K ≤ I.cost A.patch
    rwa [cost_patch_of_properOn (hA I h2)]

/-- A bound `ρ ≤ Pr[A uses at least K colours]` for all proper algorithms holds for all
algorithms that colour the inputs in the support properly. -/
theorem forall_probAtLeast_iff_properOn {n : ℕ} (D : PMF (OnlineInput n)) (K : ℕ) (ρ : ℝ) :
    (∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast D A K) ↔
      ∀ A : OnlineAlg, (∀ I ∈ D.support, ProperOn A I) → ρ ≤ probAtLeast D A K := by
  constructor
  · intro h A hA
    rw [← probAtLeast_patch D hA]
    exact h A.patch A.patch_isProper
  · intro h A hA
    exact h A fun I _ => properOn_of_isProper hA I

/-! ### The literal analogues of `ChiDetAtLeast.of_isProperOn` -/

/-- A lower bound `χ^rand_k(n) ≥ x` also holds against randomized algorithms whose deterministic
algorithms are only proper on the inputs on `n` vertices. -/
theorem chiRandAtLeast_of_isProperOn {k n : ℕ} {x : ℝ} (h : ChiRandAtLeast k n x)
    {μ : PMF OnlineAlg} (hμ : ∀ A ∈ μ.support, A.IsProperOn n) :
    ∃ I : OnlineInput n, I.graph.Colorable k ∧ x ≤ expCost μ I :=
  chiRandAtLeast_iff_properOn.1 h μ fun A hA I _ => hμ A hA I

/-- `χ_ol(G) ≥ K` also holds against algorithms that are only proper on the inputs on `N`
vertices. -/
theorem onlineChromaticAtLeast_of_isProperOn {N : ℕ} {G : SimpleGraph (Fin N)} {K : ℕ}
    (h : OnlineChromaticAtLeast G K) {A : OnlineAlg} (hA : A.IsProperOn N) :
    ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ K ≤ I.cost A :=
  onlineChromaticAtLeast_iff_properOn.1 h A fun I _ => hA I

/-- The randomized known-graph bound also holds against randomized algorithms whose deterministic
algorithms are only proper on the inputs on `N` vertices. -/
theorem randKnownAtLeast_of_isProperOn {N : ℕ} {G : SimpleGraph (Fin N)} {x : ℝ}
    (h : RandKnownAtLeast G x) {μ : PMF OnlineAlg} (hμ : ∀ A ∈ μ.support, A.IsProperOn N) :
    ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ x ≤ expCost μ I :=
  randKnownAtLeast_iff_properOn.1 h μ fun A hA I _ => hμ A hA I

/-- `ProbForcing k n x p` gives a distribution that works against every algorithm that is only
proper on the inputs on `n` vertices. -/
theorem probForcing_of_isProperOn {k n : ℕ} {x p : ℝ} (h : ProbForcing k n x p) :
    ∃ D : PMF (OnlineInput n), (∀ I ∈ D.support, I.graph.Colorable k) ∧
      ∀ A : OnlineAlg, A.IsProperOn n →
        ENNReal.ofReal p ≤ D.toOuterMeasure {I | x ≤ (I.cost A : ℝ)} := by
  obtain ⟨D, hcol, hD⟩ := probForcing_iff_properOn.1 h
  exact ⟨D, hcol, fun A hA => hD A fun I _ => hA I⟩

/-! ### Adversaries -/

/-- `A` answers properly in its play against `adv`: whenever `adv` presents a vertex, the colour
that `A` gives it differs from the colours of its earlier neighbours. -/
def ProperAgainst (adv : Adversary) (A : OnlineAlg) : Prop :=
  ∀ p s, adv.move (adv.hist A p) = some s →
    A.step (adv.hist A p) s ∉ nbrColours (adv.hist A p) s

theorem properAgainst_of_isProper {A : OnlineAlg} (hA : A.IsProper) (adv : Adversary) :
    ProperAgainst adv A := fun _ _ _ => (OnlineAlg.isProper_iff A).1 hA _ _

/-- **The plays against `A` and against `A.patch` coincide** if `A` answers properly in its play
against `adv`. -/
theorem hist_patch {adv : Adversary} {A : OnlineAlg} (h : ProperAgainst adv A) :
    ∀ p, adv.hist A.patch p = adv.hist A p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    cases hm : adv.move (adv.hist A p) with
    | none =>
      rw [Det.hist_succ_of_none hm, Det.hist_succ_of_none (by rw [ih]; exact hm), ih]
    | some s =>
      rw [Det.hist_succ_of_some hm, Det.hist_succ_of_some (by rw [ih]; exact hm), ih]
      have hs := h p s hm
      change _ ++ [(s, if A.step (adv.hist A p) s ∈ nbrColours (adv.hist A p) s then _ else _)]
        = _
      rw [ite_eq_right hs]

/-- **The general bridge for adversaries.** A property of the play of `adv` (the sequence of its
histories) holds against every proper algorithm iff it holds against every algorithm that answers
properly in its play against `adv`. -/
theorem forall_isProper_iff_properAgainst (adv : Adversary) (Q : (ℕ → History) → Prop) :
    (∀ A : OnlineAlg, A.IsProper → Q (adv.hist A)) ↔
      ∀ A : OnlineAlg, ProperAgainst adv A → Q (adv.hist A) := by
  constructor
  · intro h A hA
    have e : adv.hist A.patch = adv.hist A := funext (hist_patch hA)
    rw [← e]
    exact h A.patch A.patch_isProper
  · intro h A hA
    exact h A (properAgainst_of_isProper hA adv)

/-- **`Adversary.Forces`: properness is needed only in the play.** -/
theorem forces_iff_properAgainst {adv : Adversary} {K : ℕ} :
    adv.Forces K ↔ ∀ A : OnlineAlg, ProperAgainst adv A →
      ∃ p, adv.move (adv.hist A p) = none ∧ K ≤ (usedColours (adv.hist A p)).card :=
  forall_isProper_iff_properAgainst adv
    fun f => ∃ p, adv.move (f p) = none ∧ K ≤ (usedColours (f p)).card

/-- **`Adversary.CommitsTo`: properness is needed only in the play.** -/
theorem commitsTo_iff_properAgainst {P : Type*} [PartialOrder P] {adv : Adversary}
    {ψ : History → P} :
    adv.CommitsTo ψ ↔ ∀ A : OnlineAlg, ProperAgainst adv A → ∀ p, LabelsHist ψ (adv.hist A p) :=
  forall_isProper_iff_properAgainst adv fun f => ∀ p, LabelsHist ψ (f p)

theorem sizeLE_iff_properAgainst {adv : Adversary} {N : ℕ} :
    adv.SizeLE N ↔ ∀ A : OnlineAlg, ProperAgainst adv A → ∀ p, (adv.hist A p).length ≤ N :=
  forall_isProper_iff_properAgainst adv fun f => ∀ p, (f p).length ≤ N

theorem postDegLE_iff_properAgainst {adv : Adversary} {D : ℕ} :
    adv.PostDegLE D ↔
      ∀ A : OnlineAlg, ProperAgainst adv A → ∀ p i, (adv.hist A p).postDeg i ≤ D :=
  forall_isProper_iff_properAgainst adv fun f => ∀ p i, (f p).postDeg i ≤ D

theorem landsIn_iff_properAgainst {adv : Adversary}
    {C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop} :
    adv.LandsIn C ↔ ∀ A : OnlineAlg, ProperAgainst adv A →
      ∀ p, adv.StopsAt A p → C _ (adv.hist A p).graph :=
  forall_isProper_iff_properAgainst adv fun f => ∀ p, adv.move (f p) = none → C _ (f p).graph

/-- **`N_k(K) ≤ n`: properness is needed only in the plays.** -/
theorem nkLE_iff_properAgainst {k K n : ℕ} :
    NkLE k K n ↔ ∃ adv : Adversary,
      (∀ A : OnlineAlg, ProperAgainst adv A →
        ∃ p, adv.move (adv.hist A p) = none ∧ K ≤ (usedColours (adv.hist A p)).card) ∧
      (∀ A : OnlineAlg, ProperAgainst adv A → ∀ p, (adv.hist A p).length ≤ n) ∧
      ∀ A : OnlineAlg, ProperAgainst adv A →
        ∀ p, adv.StopsAt A p → (adv.hist A p).graph.Colorable k := by
  constructor
  · rintro ⟨adv, h1, h2, h3⟩
    exact ⟨adv, forces_iff_properAgainst.1 h1, sizeLE_iff_properAgainst.1 h2,
      landsIn_iff_properAgainst.1 h3⟩
  · rintro ⟨adv, h1, h2, h3⟩
    exact ⟨adv, forces_iff_properAgainst.2 h1, sizeLE_iff_properAgainst.2 h2,
      landsIn_iff_properAgainst.2 h3⟩

/-- **Proposition 9.4 with properness only in the play.** If every algorithm that answers properly
in its play against `adv` is forced to use `K` colours, and the labels given by `ψ` form a
`P`-labelling in every such play, then `K ≤ |J*(P)|`. -/
theorem le_card_jst_of_properAgainst {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]
    [DecidableLE P] {adv : Adversary} {K : ℕ} {ψ : History → P}
    (hK : ∀ A : OnlineAlg, ProperAgainst adv A →
      ∃ p, adv.move (adv.hist A p) = none ∧ K ≤ (usedColours (adv.hist A p)).card)
    (hψ : ∀ A : OnlineAlg, ProperAgainst adv A → ∀ p, LabelsHist ψ (adv.hist A p)) :
    K ≤ Fintype.card (Jst P) :=
  Adversary.le_card_jst (forces_iff_properAgainst.2 hK) (commitsTo_iff_properAgainst.2 hψ)

/-! ### Properly coloured histories -/

/-- The history `h` is properly coloured: the colour of every vertex differs from the colours of
its earlier neighbours. -/
def ProperHist (h : History) : Prop :=
  ∀ i j (hj : j < h.length), i < j → i ∈ h[j].1 → colourAt h i ≠ h[j].2

theorem properHist_nil : ProperHist [] := fun _ _ hj => absurd hj (by simp)

theorem properHist_append_iff {h : History} {s : Finset ℕ} {c : ℕ} :
    ProperHist (h ++ [(s, c)]) ↔ ProperHist h ∧ c ∉ nbrColours h s := by
  constructor
  · intro hp
    constructor
    · intro i j hj hij hmem
      have hj' : j < (h ++ [(s, c)]).length := by
        rw [List.length_append]
        exact Nat.lt_add_right _ hj
      have h1 := hp i j hj' hij (by rwa [List.getElem_append_left hj])
      rwa [Det.colourAt_append_left (hij.trans hj), List.getElem_append_left hj] at h1
    · intro hmem
      simp only [nbrColours, mem_image, mem_filter] at hmem
      obtain ⟨i, ⟨his, hil⟩, hic⟩ := hmem
      have hlen : h.length < (h ++ [(s, c)]).length := by simp
      have h1 := hp i h.length hlen hil (by simpa using his)
      rw [Det.colourAt_append_left hil] at h1
      exact h1 (by simpa using hic)
  · rintro ⟨hp, hc⟩ i j hj hij hmem
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem_append_left hj'] at hmem ⊢
      rw [Det.colourAt_append_left (hij.trans hj')]
      exact hp i j hj' hij hmem
    · rw [Det.colourAt_append_left hij]
      have hmem' : i ∈ s := by simpa using hmem
      intro heq
      apply hc
      simp only [nbrColours, mem_image, mem_filter]
      exact ⟨i, ⟨hmem', hij⟩, by simpa using heq⟩

/-- **`A` answers properly in its play against `adv` iff every history of the play is properly
coloured.** -/
theorem properAgainst_iff_properHist {adv : Adversary} {A : OnlineAlg} :
    ProperAgainst adv A ↔ ∀ p, ProperHist (adv.hist A p) := by
  constructor
  · intro h p
    induction p with
    | zero => exact properHist_nil
    | succ p ih =>
      cases hm : adv.move (adv.hist A p) with
      | none =>
        rw [Det.hist_succ_of_none hm]
        exact ih
      | some s =>
        rw [Det.hist_succ_of_some hm]
        exact properHist_append_iff.2 ⟨ih, h p s hm⟩
  · intro h p s hm
    have h1 := h (p + 1)
    rw [Det.hist_succ_of_some hm] at h1
    exact (properHist_append_iff.1 h1).2

end Expl

end OnlineColouring
