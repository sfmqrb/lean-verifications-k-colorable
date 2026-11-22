module

public import OnlineColouring.Labels

/-!
# Blow-ups, and the two halves of the calculus of labels

Definition 4.6 (blow-up) of the paper, and

* Lemma 5.2 (labels descend through blow-ups): `BlowUp.hasLabelling_of_jst`,
* Lemma 5.3 (labels ascend through full blow-ups): `BlowUp.hasLabelling_jst_of_full`.

A blow-up of the ordered graph `H` (on the linear order `V`) is an ordered graph `G` (on the
linear order `W`) together with

* a surjective *block map* `π : W → V`; the block of `v` is `σ(v) = π⁻¹(v)`, and the blocks arrive
  one after the other in the order of `H` (`π x < π y → x < y`; condition (i) of the definition);
* a partial *serve map* `serve : W → Option V`; if `serve x = some v` then `x` serves the arc
  `π x → v`, which must be an arc of `H` (`π x < v` and `π x ~ v`; condition (ii));
* the edges of `G` are exactly the pairs `x < u` with `serve x = some (π u)` (condition (iii)).

The blow-up is full if every arc of `H` is served by at least one vertex (`BlowUp.IsFull`), and a
reservation blow-up if every arc is served by exactly one vertex (`BlowUp.IsReservation`).
Independence of the blocks is a consequence (`BlowUp.not_adj_of_π_eq`), so it is not a field of
the structure.  The sentence after the definition, that every vertex is joined to at most one
later block, completely, is `BlowUp.serve_eq_of_adj` together with `BlowUp.adj_of_serve`.
-/

@[expose] public section

namespace OnlineColouring

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Definition 4.6: a blow-up structure exhibiting `G` (on `W`) as a blow-up of `H` (on `V`). -/
structure BlowUp (H : SimpleGraph V) (G : SimpleGraph W) where
  /-- The block map: `x` lies in the block `σ(π x)`. -/
  π : W → V
  /-- The partial serve map: `serve x = some v` means that `x` serves the arc `π x → v`. -/
  serve : W → Option V
  /-- Every block is nonempty. -/
  π_surjective : Function.Surjective π
  /-- Condition (i): the blocks arrive one after the other, in the order of `H`. -/
  lt_of_π_lt : ∀ ⦃x y : W⦄, π x < π y → x < y
  /-- Condition (ii): a vertex only serves arcs `π x → v` of `H` with `π x` earlier than `v`. -/
  serve_spec : ∀ ⦃x : W⦄ ⦃v : V⦄, serve x = some v → π x < v ∧ H.Adj (π x) v
  /-- Condition (iii): the edges of `G` are the pairs `x < u` with `x` serving the arc into the
  block of `u`. -/
  adj_iff : ∀ x u : W, G.Adj x u ↔ (x < u ∧ serve x = some (π u)) ∨ (u < x ∧ serve u = some (π x))

namespace BlowUp

variable {H : SimpleGraph V} {G : SimpleGraph W}

/-- A blow-up is *full* if every arc `w → v` of `H` (with `w < v`) is served by some vertex of
the block of `w`. -/
def IsFull (B : BlowUp H G) : Prop :=
  ∀ ⦃w v : V⦄, w < v → H.Adj w v → ∃ x, B.π x = w ∧ B.serve x = some v

/-- A blow-up is a *reservation* blow-up if every arc is served by exactly one vertex. -/
def IsReservation (B : BlowUp H G) : Prop :=
  ∀ ⦃w v : V⦄, w < v → H.Adj w v → ∃! x, B.π x = w ∧ B.serve x = some v

theorem IsReservation.isFull {B : BlowUp H G} (h : B.IsReservation) : B.IsFull :=
  fun _ _ hwv hadj => (h hwv hadj).exists

/-- If `x u` is an edge of a blow-up with `x` earlier than `u`, then `x` serves the arc into the
block of `u`. -/
theorem serve_eq_of_adj (B : BlowUp H G) {x u : W} (hxu : x < u) (hadj : G.Adj x u) :
    B.serve x = some (B.π u) := by
  rcases (B.adj_iff x u).1 hadj with ⟨_, h⟩ | ⟨hux, _⟩
  · exact h
  · exact absurd hxu (lt_asymm hux)

/-- Blocks are independent sets. -/
theorem not_adj_of_π_eq (B : BlowUp H G) {x u : W} (h : B.π x = B.π u) : ¬ G.Adj x u := by
  intro hadj
  rcases (B.adj_iff x u).1 hadj with ⟨_, hs⟩ | ⟨_, hs⟩
  · exact lt_irrefl _ (h ▸ (B.serve_spec hs).1)
  · exact lt_irrefl _ (h ▸ (B.serve_spec hs).1)

/-- Every edge of a blow-up projects to an edge of `H`. -/
theorem adj_π_of_adj (B : BlowUp H G) {x u : W} (hadj : G.Adj x u) : H.Adj (B.π x) (B.π u) := by
  rcases (B.adj_iff x u).1 hadj with ⟨_, hs⟩ | ⟨_, hs⟩
  · exact (B.serve_spec hs).2
  · exact (B.serve_spec hs).2.symm

/-- A vertex that serves the arc into the block of `u` is adjacent to `u`.  With
`serve_eq_of_adj`: each vertex has later neighbours in at most one block, and is joined to all of
it. -/
theorem adj_of_serve (B : BlowUp H G) {x u : W} (hs : B.serve x = some (B.π u)) : G.Adj x u :=
  (B.adj_iff x u).2 (Or.inl ⟨B.lt_of_π_lt (B.serve_spec hs).1, hs⟩)

variable {P : Type*} [PartialOrder P]

/-- **Lemma 5.2 (labels descend through blow-ups).** If `H` has a `J*(P)`-labelling, then every
blow-up of `H` has a `P`-labelling. -/
theorem hasLabelling_of_jst (B : BlowUp H G) (hH : HasLabelling H (Jst P)) :
    HasLabelling G P := by
  obtain ⟨ψ, hψ⟩ := hH
  -- For each `x` choose `f x ∈ ψ (π x)`, avoiding `ψ v` if `x` serves the arc `π x → v`.
  have key : ∀ x : W, ∃ p : P, p ∈ ψ (B.π x) ∧ ∀ v, B.serve x = some v → p ∉ ψ v := by
    intro x
    cases hx : B.serve x with
    | none =>
      obtain ⟨p, hp⟩ := (ψ (B.π x)).nonempty
      exact ⟨p, hp, fun v hv => by cases hv⟩
    | some v =>
      obtain ⟨hlt, hadj⟩ := B.serve_spec hx
      have hnle : ¬ ψ (B.π x) ≤ ψ v := hψ hlt hadj
      rw [Jst.le_iff_forall] at hnle
      push Not at hnle
      obtain ⟨p, hp, hpv⟩ := hnle
      refine ⟨p, hp, fun v' hv' => ?_⟩
      cases hv'
      exact hpv
  choose f hf₁ hf₂ using key
  refine ⟨f, fun x u hxu hadj hle => ?_⟩
  have hs := B.serve_eq_of_adj hxu hadj
  exact hf₂ x (B.π u) hs (Jst.mem_of_le hle (hf₁ u))

/-- **Lemma 5.3 (labels ascend through full blow-ups).** If a full blow-up `G` of `H` has a
`P`-labelling `f`, then `H` has a `J*(P)`-labelling.  The proof takes `ψ v = ↓ f(σ(v))`, and
`Paper.exists_isLabelling_down` (`PaperFirstFit.lean`) states the lemma with this `ψ`. -/
theorem hasLabelling_jst_of_full [Finite P] (B : BlowUp H G) (hB : B.IsFull)
    (hG : HasLabelling G P) : HasLabelling H (Jst P) := by
  classical
  have := Fintype.ofFinite P
  obtain ⟨f, hf⟩ := hG
  -- `ψ v` is the down-closure of the labels of the block of `v`.
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
  refine ⟨ψ, fun w v hwv hadj hle => ?_⟩
  obtain ⟨x, hxw, hxs⟩ := hB hwv hadj
  -- `f x ∈ ψ w ⊆ ψ v`, so `f x ≤ f u` for some `u` in the block of `v`, which `x` serves.
  have hx : f x ∈ ψ v := (Jst.le_iff_forall.1 hle) _ ((hmem w _).2 ⟨x, hxw, le_rfl⟩)
  obtain ⟨u, hu, hxu⟩ := (hmem v _).1 hx
  have hs : B.serve x = some (B.π u) := by rw [hu]; exact hxs
  have hadj' : G.Adj x u := B.adj_of_serve hs
  have hlt : x < u := B.lt_of_π_lt (by rw [hxw, hu]; exact hwv)
  exact hf hlt hadj' hxu

end BlowUp

end OnlineColouring
