module

public import OnlineColouring.Towers
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Remark 6.5: blow-ups are triangle-free; odd girth at least `2j + 3` for `j`-fold blow-ups of `K_K`

* `BlowUp.exists_closed_walk`: a closed walk of positive length `L` in a blow-up `G` of `H` gives
  a closed walk of length `L - 2` in `H`.  Map the walk to `H` by the block map; the earliest
  vertex `x` of the walk has both of its walk neighbours later, so both lie in the block that `x`
  serves, and deleting this backtrack leaves a closed walk two shorter.  In particular an odd
  closed walk of length `L` gives an odd closed walk of length `L - 2`
  (`BlowUp.exists_odd_closed_walk`).
* `BlowUp.cliqueFree_three`: blow-ups are triangle-free; `IsTower.cliqueFree_three`.
* `IsTower.le_length_of_odd`: in a `j`-fold blow-up of `K_K` (any blow-ups, not necessarily full)
  every odd closed walk has length at least `2j + 3`;
  `IsTower.isBipartite_or_oddGirth`: such a graph is bipartite or has odd girth at least
  `2j + 3`; `IsTower.le_length_of_isCycle`: every odd cycle has length at least `2j + 3`.

The sentence of Remark 6.5 about First-Fit, for the graphs presented by the adversary of
Theorem 6.4, is in `BlowTower.lean` (`Blow.tower_firstFit_le`, `Blow.tower_firstFit_eq`).
-/

@[expose] public section

namespace OnlineColouring

open SimpleGraph

/-- In a simple graph no closed walk has length `1`. -/
theorem walk_length_ne_one {V : Type*} {G : SimpleGraph V} {v : V}
    (q : G.Walk v v) : q.length ≠ 1 := by
  cases q with
  | nil => simp
  | cons h q' =>
    cases q' with
    | nil => exact absurd h (G.loopless.irrefl _)
    | cons _ _ => simp

/-- An odd closed walk has length at least `3`. -/
theorem walk_three_le_length_of_odd {V : Type*} {G : SimpleGraph V} {v : V}
    (q : G.Walk v v) (hq : Odd q.length) : 3 ≤ q.length := by
  have h1 := walk_length_ne_one q
  rw [Nat.odd_iff] at hq
  omega

namespace BlowUp

variable {V W : Type*} [LinearOrder V] [LinearOrder W] {H : SimpleGraph V} {G : SimpleGraph W}

/-- The block map is a graph homomorphism `G →g H`. -/
def hom (B : BlowUp H G) : G →g H := ⟨B.π, fun h => B.adj_π_of_adj h⟩

/-- **Remark (the hard instances), one step.** A closed walk of positive length `L` in a blow-up
`G` of `H` yields a closed walk of length `L - 2` in `H`. -/
theorem exists_closed_walk (B : BlowUp H G) {u : W} (p : G.Walk u u) (hp : 0 < p.length) :
    ∃ (v : V) (q : H.Walk v v), q.length + 2 = p.length := by
  classical
  -- the earliest vertex `x` of the walk
  obtain ⟨x, hxmem, hxmin⟩ : ∃ x ∈ p.support, ∀ y ∈ p.support, x ≤ y := by
    have hne : p.support.toFinset.Nonempty := ⟨u, List.mem_toFinset.2 p.start_mem_support⟩
    exact ⟨_, List.mem_toFinset.1 (Finset.min'_mem _ hne),
      fun y hy => Finset.min'_le _ _ (List.mem_toFinset.2 hy)⟩
  -- rotate the walk to start at `x`
  obtain ⟨c, hc_len, hc_min⟩ :
      ∃ c : G.Walk x x, c.length = p.length ∧ ∀ y ∈ c.support, x ≤ y :=
    ⟨p.rotate x hxmem, Walk.length_rotate _ _ _,
      fun y hy => hxmin y ((Walk.mem_support_rotate_iff _ _ _).1 hy)⟩
  cases c with
  | nil => simp at hc_len; omega
  | @cons _ y _ hxy c₁ =>
    -- `c = x → y ⋯ z → x`; reverse the tail to expose `z`
    obtain ⟨c₂, hc₂⟩ : ∃ c₂ : G.Walk x y, c₂ = c₁.reverse := ⟨_, rfl⟩
    cases c₂ with
    | nil => exact absurd hxy (G.loopless.irrefl _)
    | @cons _ z _ hxz c₃ =>
      have hy : y ∈ (Walk.cons hxy c₁).support := by simp
      have hz : z ∈ (Walk.cons hxy c₁).support := by
        have : z ∈ c₁.reverse.support := by rw [← hc₂]; simp
        rw [Walk.support_reverse, List.mem_reverse] at this
        simp [this]
      have hxy' : x < y := lt_of_le_of_ne (hc_min y hy) hxy.ne
      have hxz' : x < z := lt_of_le_of_ne (hc_min z hz) hxz.ne
      -- both `y` and `z` are later neighbours of `x`, so they lie in the block `x` serves
      have hyz : B.π z = B.π y := by
        have h1 := B.serve_eq_of_adj hxy' hxy
        have h2 := B.serve_eq_of_adj hxz' hxz
        rw [h1] at h2
        exact (Option.some.inj h2).symm
      refine ⟨B.hom y, (c₃.map B.hom).copy (show B.hom z = B.hom y from hyz) rfl, ?_⟩
      have hlen : c₁.reverse.length = c₃.length + 1 := by rw [← hc₂]; simp
      rw [Walk.length_reverse] at hlen
      simp only [Walk.length_copy, Walk.length_map]
      simp only [Walk.length_cons] at hc_len
      omega

/-- **Remark (the hard instances).** An odd closed walk of length `L` in a blow-up of `H` yields
an odd closed walk of length `L - 2` in `H`. -/
theorem exists_odd_closed_walk (B : BlowUp H G) {u : W} (p : G.Walk u u)
    (hp : Odd p.length) : ∃ (v : V) (q : H.Walk v v), Odd q.length ∧ q.length + 2 = p.length := by
  obtain ⟨v, q, hq⟩ := B.exists_closed_walk p (Odd.pos hp)
  refine ⟨v, q, ?_, hq⟩
  rw [Nat.odd_iff] at hp ⊢
  omega

/-- **Remark (the hard instances).** Blow-ups are triangle-free. -/
theorem cliqueFree_three (B : BlowUp H G) : G.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hac.symm .nil))
  obtain ⟨v, q, hq⟩ := B.exists_closed_walk p (by simp [p])
  have h1 : q.length = 1 := by simp [p] at hq; omega
  exact walk_length_ne_one q h1

end BlowUp

/-- **Remark (the hard instances).** In a `j`-fold blow-up of `K_K` (the blow-ups need not be
full), every odd closed walk has length at least `2j + 3`. -/
theorem IsTower.le_length_of_odd {K j : ℕ} {G : OrdGraph} (hT : IsTower K j G) :
    ∀ {u : G.V} (p : G.G.Walk u u), Odd p.length → 2 * j + 3 ≤ p.length := by
  induction hT with
  | clique =>
    intro u p hp
    simpa using walk_three_le_length_of_odd p hp
  | @blowUp j H G _ hB ih =>
    intro u p hp
    obtain ⟨B⟩ := hB
    obtain ⟨v, q, hq, hlen⟩ := B.exists_odd_closed_walk p hp
    have := ih q hq
    omega

/-- **Remark (the hard instances).** A `j`-fold blow-up of `K_K` is bipartite or has odd girth at
least `2j + 3`: if it is not bipartite, it has an odd closed walk, and all of them have length at
least `2j + 3`. -/
theorem IsTower.isBipartite_or_oddGirth {K j : ℕ} {G : OrdGraph} (hT : IsTower K j G) :
    G.G.IsBipartite ∨
      ((∃ (u : G.V) (p : G.G.Walk u u), Odd p.length) ∧
        ∀ (u : G.V) (p : G.G.Walk u u), Odd p.length → 2 * j + 3 ≤ p.length) := by
  by_cases h : G.G.IsBipartite
  · exact Or.inl h
  · refine Or.inr ⟨?_, fun u p hp => hT.le_length_of_odd p hp⟩
    rw [SimpleGraph.isBipartite_iff_forall_walk_even_length] at h
    push Not at h
    obtain ⟨u, p, hp⟩ := h
    exact ⟨u, p, hp⟩

/-- **Remark (the hard instances).** Every odd cycle of a `j`-fold blow-up of `K_K` has length at
least `2j + 3`. -/
theorem IsTower.le_length_of_isCycle {K j : ℕ} {G : OrdGraph} (hT : IsTower K j G) {u : G.V}
    (p : G.G.Walk u u) (_ : p.IsCycle) (hp : Odd p.length) : 2 * j + 3 ≤ p.length :=
  hT.le_length_of_odd p hp

/-- A `j`-fold blow-up of `K_K` with `j ≥ 1` is triangle-free. -/
theorem IsTower.cliqueFree_three {K j : ℕ} {G : OrdGraph} (hT : IsTower K (j + 1) G) :
    G.G.CliqueFree 3 := by
  cases hT with
  | blowUp _ hB =>
    obtain ⟨B⟩ := hB
    exact B.cliqueFree_three

end OnlineColouring
