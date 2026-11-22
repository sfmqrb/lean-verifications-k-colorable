module

public import OnlineColouring.KnownGraphs
public import OnlineColouring.PadGraph

/-!
# The known-graph game: closure properties, and its randomized form

Section 7 and Theorem 1.3.  `OnlineChromaticAtLeast G K` (`KnownGraphs.lean`) says that every
proper deterministic online algorithm, which may depend on `G`, uses at least `K` colours on some
presentation of `G`.  This file adds the randomized form and closure properties of both notions;
the proof of Theorem 1.3 for `G′` uses monotonicity and padding.

* `RandKnownAtLeast G x`: every proper randomized online algorithm (a `PMF OnlineAlg`, which may
  depend on `G`) has a presentation of `G`, that is, an online input whose graph is isomorphic to
  `G`, on which its expected number of colours is at least `x`.  For `G = G′` and
  `x = N^{1/(L+2)}/(8(1+ln 4N))` this is the sentence "Every randomized online algorithm that
  knows `G′` in advance has a presentation order of `G′` on which it uses at least
  `N^{1/(L+2)}/(8(1+ln 4N))` colours in expectation" of Theorem 1.3.
* Both notions are monotone in the bound (`.mono`), invariant under isomorphism (`.of_iso`) and
  closed under padding with isolated vertices (`.pad`, with `padGraph`);
  `RandKnownAtLeast.onlineChromaticAtLeast`: a randomized bound gives the deterministic one.
* `KnownQ k N x`: some triangle-free `k`-colourable graph `G` on `N` vertices has
  `χ_ol(G) ≥ ⌈x⌉` and `RandKnownAtLeast G x`.  It is monotone in `x` (`knownQ_hmono`), closed
  under padding (`knownQ_hpad`, `k ≥ 1`) and holds for `x = 1` (`knownQ_hbase`, `k ≥ 1` and
  `N ≥ 1`): three of the four hypotheses of the generic argument of `LogStarGeneric.lean`.  The
  fourth, the uniform tower, is `Rjm.knownQ_hcore` (`MainLogStar.lean`).
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### The randomized known-graph game -/

/-- `RandKnownAtLeast G x`: every proper randomized online algorithm (which may depend on `G`)
has a presentation of `G` on which its expected number of colours is at least `x`. -/
def RandKnownAtLeast {N : ℕ} (G : SimpleGraph (Fin N)) (x : ℝ) : Prop :=
  ∀ μ : PMF OnlineAlg, IsProperRand μ →
    ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ x ≤ expCost μ I

/-! ### Monotonicity, padding and isomorphism invariance -/

variable {N N' : ℕ}

theorem OnlineChromaticAtLeast.mono {G : SimpleGraph (Fin N)} {K K' : ℕ}
    (h : OnlineChromaticAtLeast G K) (hK : K' ≤ K) : OnlineChromaticAtLeast G K' := by
  intro A hA
  obtain ⟨I, hI, hc⟩ := h A hA
  exact ⟨I, hI, hK.trans hc⟩

/-- Padding with isolated vertices keeps the deterministic bound. -/
theorem OnlineChromaticAtLeast.pad {G : SimpleGraph (Fin N)} {K : ℕ}
    (h : OnlineChromaticAtLeast G K) (hN : N ≤ N') : OnlineChromaticAtLeast (padGraph G N') K := by
  intro A hA
  obtain ⟨I, ⟨e⟩, hK⟩ := h A hA
  obtain ⟨e'⟩ := padGraph_iso hN e
  refine ⟨padInput I N', ⟨?_⟩, hK.trans (cost_le_padInput hN I A)⟩
  rw [padInput_graph]
  exact e'

theorem OnlineChromaticAtLeast.of_iso {G G' : SimpleGraph (Fin N)} {K : ℕ}
    (h : OnlineChromaticAtLeast G K) (e : G ≃g G') : OnlineChromaticAtLeast G' K := by
  intro A hA
  obtain ⟨I, ⟨e'⟩, hK⟩ := h A hA
  exact ⟨I, ⟨e'.trans e⟩, hK⟩

theorem RandKnownAtLeast.mono {G : SimpleGraph (Fin N)} {x x' : ℝ} (h : RandKnownAtLeast G x)
    (hx : x' ≤ x) : RandKnownAtLeast G x' := by
  intro μ hμ
  obtain ⟨I, hI, hc⟩ := h μ hμ
  exact ⟨I, hI, hx.trans hc⟩

/-- Padding with isolated vertices keeps the randomized bound. -/
theorem RandKnownAtLeast.pad {G : SimpleGraph (Fin N)} {x : ℝ} (h : RandKnownAtLeast G x)
    (hN : N ≤ N') : RandKnownAtLeast (padGraph G N') x := by
  intro μ hμ
  obtain ⟨I, ⟨e⟩, hx⟩ := h μ hμ
  obtain ⟨e'⟩ := padGraph_iso hN e
  refine ⟨padInput I N', ⟨?_⟩, hx.trans (expCost_mono μ (cost_le_padInput hN I))⟩
  rw [padInput_graph]
  exact e'

theorem RandKnownAtLeast.of_iso {G G' : SimpleGraph (Fin N)} {x : ℝ}
    (h : RandKnownAtLeast G x) (e : G ≃g G') : RandKnownAtLeast G' x := by
  intro μ hμ
  obtain ⟨I, ⟨e'⟩, hx⟩ := h μ hμ
  exact ⟨I, ⟨e'.trans e⟩, hx⟩

/-- A randomized known-graph bound gives the deterministic one (point masses). -/
theorem RandKnownAtLeast.onlineChromaticAtLeast {G : SimpleGraph (Fin N)} {K : ℕ}
    (h : RandKnownAtLeast G K) : OnlineChromaticAtLeast G K := by
  intro A hA
  obtain ⟨I, hI, hc⟩ := h _ (isProperRand_pure hA)
  refine ⟨I, hI, ?_⟩
  have : expCost (PMF.pure A) I = I.cost A := by simp [expCost, expCostE_pure]
  exact_mod_cast hc.trans_eq this

/-! ### Packaging for the generic argument of Theorem 1.1 -/

/-- `KnownQ k N x`: some triangle-free `k`-colourable graph `G` on `N` vertices has
`χ_ol(G) ≥ ⌈x⌉`, and every randomized algorithm that knows `G` has expected cost at least `x` on
some presentation of `G`. -/
def KnownQ (k N : ℕ) (x : ℝ) : Prop :=
  ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧
    OnlineChromaticAtLeast G ⌈x⌉₊ ∧ RandKnownAtLeast G x

theorem KnownQ.mono {k : ℕ} {x x' : ℝ} (h : KnownQ k N x) (hx : x' ≤ x) : KnownQ k N x' := by
  obtain ⟨G, hc, hf, hd, hr⟩ := h
  exact ⟨G, hc, hf, hd.mono (Nat.ceil_mono hx), hr.mono hx⟩

theorem KnownQ.pad {k : ℕ} {x : ℝ} (hk : 1 ≤ k) (h : KnownQ k N x) (hN : N ≤ N') :
    KnownQ k N' x := by
  obtain ⟨G, hc, hf, hd, hr⟩ := h
  exact ⟨padGraph G N', padGraph_colorable hk hc, padGraph_cliqueFree hf, hd.pad hN, hr.pad hN⟩

/-- The edgeless graph: every algorithm uses at least one colour on `N ≥ 1` vertices. -/
theorem knownQ_one {k : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) : KnownQ k N 1 := by
  refine ⟨(emptyInput N).graph, emptyInput_colorable hk, emptyInput_cliqueFree N, ?_, ?_⟩
  · rw [Nat.ceil_one]
    exact emptyInput_onlineChromaticAtLeast_one hN
  · intro μ _
    exact ⟨emptyInput N, ⟨RelIso.refl _⟩, one_le_expCost hN μ⟩

/-! Three of the four hypotheses of the generic argument of `LogStarGeneric.lean`. -/

theorem knownQ_hmono : ∀ (k n : ℕ) (x x' : ℝ), 1 ≤ k → KnownQ k n x → x' ≤ x → KnownQ k n x' :=
  fun _ _ _ _ _ h hx => h.mono hx

theorem knownQ_hpad : ∀ (k n n' : ℕ) (x : ℝ), 1 ≤ k → KnownQ k n x → n ≤ n' → KnownQ k n' x :=
  fun _ _ _ _ hk h hn => h.pad hk hn

theorem knownQ_hbase : ∀ k n, 1 ≤ k → 1 ≤ n → KnownQ k n 1 :=
  fun _ _ hk hn => knownQ_one hk hn

end OnlineColouring
