module

public import OnlineColouring.RandModel

/-!
# Lemma 4.4 (Yao's principle) for the number `χ^rand_k(n)`

Lemma 4.4: *Let `D` be a distribution over ordered `k`-colourable graphs on exactly `N` vertices
such that every deterministic online algorithm uses at least `x` colours in expectation on
`G ∼ D`. Then `χ^rand_k(n) ≥ x` for every `n ≥ N`. In particular, if every deterministic online
algorithm uses at least `K` colours with probability at least `1 - ε`, then
`χ^rand_k(n) ≥ (1 - ε) K`.*

`RandModel.lean` proves both sentences for the predicate `ChiRandAtLeast` (`yao_expectation` and
`yao`).  This file restates them for the number `chiRand k n` of Definition 4.1 (through
`le_chiRand_iff`): `Det.yao_expectation_chiRand` (first sentence) and `Det.yao_chiRand` (second
sentence).  The hypothesis `k ≥ 1` comes from the predicate forms, which need it (for `k = 0` the
number `chiRand 0 n` is `0`); the paper has `k ≥ 1` throughout.
-/

@[expose] public section

namespace OnlineColouring

namespace Det

/-- **Lemma 4.4 (Yao's principle), first sentence.** -/
theorem yao_expectation_chiRand {k N n : ℕ} {x : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n)
    (D : PMF (OnlineInput N)) (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → x ≤ detExpCost D A) : x ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (yao_expectation hk hNn D hcol hforce)

/-- **Lemma 4.4 (Yao's principle), "In particular".**  If every proper deterministic online
algorithm uses at least `K` colours with probability at least `1 - ε` on `I ∼ D`, then
`χ^rand_k(n) ≥ (1 - ε) K` for every `n ≥ N`. -/
theorem yao_chiRand {k N n K : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n) (D : PMF (OnlineInput N))
    (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → 1 - ε ≤ probAtLeast D A K) :
    (1 - ε) * K ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (yao hk hNn D hcol hforce)

end Det

end OnlineColouring
