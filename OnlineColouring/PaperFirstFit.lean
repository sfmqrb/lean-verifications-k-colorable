module

public import OnlineColouring.CeilingPadded
public import OnlineColouring.TwoPerColour

/-!
# First-Fit as an online algorithm (Theorem 1.5), and Lemma 5.3 with its labelling

* `run_firstFit_eq`, `cost_firstFit_eq`: the online algorithm `OnlineAlg.firstFit` (`Online.lean`)
  colours every online input exactly as the First-Fit colouring `firstFit` of its ordered graph
  (`FirstFit.lean`), for which Lemma 9.5 and Theorem 1.5 are proved.  So these results are
  statements about the cost of the online algorithm First-Fit.
* `ceiling_online`, `exists_threshold_online`: **Theorem 1.5**, both sentences, for online inputs
  and the cost of the online algorithm First-Fit.
* `exists_isLabelling_down`: **Lemma 5.3** with the labelling named in the paper,
  `ψ(v) = ↓ f(σ(v))` (`BlowUp.hasLabelling_jst_of_full` states that `H` has some
  `J*(P)`-labelling).
-/

@[expose] public section

namespace OnlineColouring

namespace Paper

/-- **The online First-Fit algorithm is the static First-Fit colouring**: on every online input
`I`, `OnlineAlg.firstFit` gives the vertex `v` the colour `firstFit I.graph v`. -/
theorem run_firstFit_eq {n : ℕ} (I : OnlineInput n) (v : Fin n) :
    I.run OnlineAlg.firstFit v = firstFit I.graph v := by
  induction v using WellFoundedLT.induction with
  | ind v ih =>
  rw [OnlineColouring.firstFit_eq]
  set S := {c | ∀ u, u < v → I.graph.Adj u v → firstFit I.graph u ≠ c} with hS
  have hmem : I.run OnlineAlg.firstFit v ∈ S := by
    intro u hu hadj
    rw [← ih u hu]
    exact I.run_ne_of_adj OnlineAlg.firstFit_isProper hadj
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, hrun⟩ := I.exists_nbr_of_lt_run_firstFit v hlt
    have huv : u < v := I.nbr_lt v u hu
    have hS' : sInf S ∈ S := Nat.sInf_mem ⟨_, hmem⟩
    exact hS' u huv (OnlineInput.graph_adj.2 (Or.inl hu)) ((ih u huv).symm.trans hrun)
  · exact Nat.sInf_le hmem

/-- The cost of the online algorithm First-Fit is the number of colours of the static First-Fit
colouring. -/
theorem cost_firstFit_eq {n : ℕ} (I : OnlineInput n) :
    I.cost OnlineAlg.firstFit = (Set.range (firstFit I.graph)).ncard := by
  have h : Set.range (firstFit I.graph) =
      ((Finset.univ.image (I.run OnlineAlg.firstFit) : Finset ℕ) : Set ℕ) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    congr 1
    funext v
    exact (run_firstFit_eq I v).symm
  rw [h, Set.ncard_coe_finset]
  rfl

/-- **Theorem 1.5 (a ceiling for towers), first sentence, for the online algorithm First-Fit.**
If First-Fit uses `c ≥ 2` colours on an online input that is a `k`-colourable `j`-level tower
(an initial segment of a full tower presented subtree by subtree, possibly followed by isolated
vertices) with `n` vertices, then `c ≤ |P_j(k)|` and `n ≥ choose(c-1, i+1)` for every `i ≤ j`. -/
theorem ceiling_online {n m j k : ℕ} (I : OnlineInput n) (hT : IsPaddedTower m j I.graph)
    (hc : I.graph.Colorable k) (_h2 : 2 ≤ I.cost OnlineAlg.firstFit) :
    I.cost OnlineAlg.firstFit ≤ Fintype.card (LabelPoset k j) ∧
      ∀ i ≤ j, (I.cost OnlineAlg.firstFit - 1).choose (i + 1) ≤ n := by
  have h := hT.ceiling hc
  rw [← cost_firstFit_eq, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- **Theorem 1.5, second sentence, for the online algorithm First-Fit.** There is `n_k` such
that for every `n ≥ n_k`, First-Fit uses at most `n^{1/(lg* n - lg* k - 3)}` colours on every
online input that is a `k`-colourable tower with at most `n` vertices. -/
theorem exists_threshold_online (k : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ (m j n' : ℕ) (I : OnlineInput n'), n' ≤ n →
      IsPaddedTower m j I.graph → I.graph.Colorable k →
        (I.cost OnlineAlg.firstFit : ℝ) ≤ (n : ℝ) ^ (1 / ((logStar n : ℝ) - logStar k - 3)) := by
  obtain ⟨n₀, h⟩ := exists_threshold_le_rpow.{0} k
  refine ⟨n₀, fun n hn m j n' I hn' hT hc => ?_⟩
  have := h n hn m j (Fin n') I.graph hT hc
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn')
  rwa [← cost_firstFit_eq] at this

section Ascend

variable {V W : Type*} [LinearOrder V] [LinearOrder W] {H : SimpleGraph V} {G : SimpleGraph W}
  {P : Type*} [PartialOrder P]

/-- **Lemma 5.3 (labels ascend through full blow-ups), with its labelling.** If a full blow-up
`G` of `H` maps to `Tmpl(P)` via `f`, then `H` maps to `Tmpl(J*(P))` via `ψ(v) = ↓ f(σ(v))`: the
labelling `ψ` satisfies `p ∈ ψ(v) ↔ p ≤ f(x)` for some `x` in the block of `v`. -/
theorem exists_isLabelling_down [Finite P] (B : BlowUp H G) (hB : B.IsFull) {f : W → P}
    (hf : IsLabelling G f) :
    ∃ ψ : V → Jst P, (∀ v p, p ∈ ψ v ↔ ∃ x, B.π x = v ∧ p ≤ f x) ∧ IsLabelling H ψ := by
  classical
  have := Fintype.ofFinite P
  let ψ : V → Jst P := fun v =>
    Jst.mk (Finset.univ.filter fun p => ∃ x, B.π x = v ∧ p ≤ f x)
      (by
        intro a ha b hba
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        obtain ⟨x, hx, hax⟩ := ha
        exact ⟨x, hx, hba.trans hax⟩)
      (by
        obtain ⟨x, hx⟩ := B.π_surjective v
        refine ⟨f x, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, hx, le_rfl⟩)
  have hmem : ∀ v p, p ∈ ψ v ↔ ∃ x, B.π x = v ∧ p ≤ f x := by
    intro v p
    change p ∈ Finset.univ.filter _ ↔ _
    simp
  refine ⟨ψ, hmem, fun w v hwv hadj hle => ?_⟩
  obtain ⟨x, hxw, hxs⟩ := hB hwv hadj
  have hx : f x ∈ ψ v := (Jst.le_iff_forall.1 hle) _ ((hmem w _).2 ⟨x, hxw, le_rfl⟩)
  obtain ⟨u, hu, hxu⟩ := (hmem v _).1 hx
  have hs : B.serve x = some (B.π u) := by rw [hu]; exact hxs
  have hadj' : G.Adj x u := B.adj_of_serve hs
  have hlt : x < u := B.lt_of_π_lt (by rw [hxw, hu]; exact hwv)
  exact hf hlt hadj' hxu

end Ascend

end Paper

end OnlineColouring
