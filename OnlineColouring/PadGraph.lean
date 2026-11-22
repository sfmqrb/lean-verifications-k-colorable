module

public import OnlineColouring.Iso
public import OnlineColouring.RandModel

/-!
# Padding a graph with isolated vertices

The graph `G′` of Theorem 1.3, the towers of Definition 4.7 and the adversaries of Corollary 9.6
are completed to a given number of vertices by appending isolated vertices.  For online inputs
this is `padInput` (`RandModel.lean`); this file is the corresponding operation on graphs.

* `padGraph G N'`: the graph `G` on `Fin N` followed by isolated vertices, `N'` vertices in all
  (`padGraph_adj`; `padGraph_self` for `N' = N`).
* Padding preserves `k`-colourability for `k ≥ 1` (`padGraph_colorable`), triangle-freeness
  (`padGraph_cliqueFree`) and isomorphisms (`padGraph_iso`).
* `padInput_graph`: the padded online input `padInput I N'` presents `padGraph I.graph N'`
  (`mem_truncSeq_seq` describes its neighbour sets).
* `ofSeq_graph_iso_of_eq`, `OnlineInput.exists_cast`: an input on `n` vertices is an input on
  `n'` vertices when `n = n'`, with an isomorphic graph and the same costs.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Isomorphisms of inputs -/

/-- Changing the number of vertices by an equality gives an isomorphic graph. -/
theorem ofSeq_graph_iso_of_eq {H : ℕ → Finset ℕ} {hH : ValidSeq H} {n n' : ℕ} (h : n = n') :
    Nonempty ((OnlineInput.ofSeq H hH n).graph ≃g (OnlineInput.ofSeq H hH n').graph) := by
  subst h
  exact ⟨RelIso.refl _⟩

/-- An input on `n = n'` vertices is also an input on `n'` vertices, with an isomorphic graph
and the same costs. -/
theorem OnlineInput.exists_cast {n n' : ℕ} (h : n = n') (I : OnlineInput n) :
    ∃ I' : OnlineInput n', Nonempty (I'.graph ≃g I.graph) ∧ ∀ A, I'.cost A = I.cost A := by
  subst h
  exact ⟨I, ⟨RelIso.refl _⟩, fun _ => rfl⟩

/-! ### Padding a graph with isolated vertices -/

/-- The graph `G` on `Fin N` followed by isolated vertices, `N'` vertices in all (if `N ≤ N'`). -/
def padGraph {N : ℕ} (G : SimpleGraph (Fin N)) (N' : ℕ) : SimpleGraph (Fin N') where
  Adj u v := ∃ (hu : (u : ℕ) < N) (hv : (v : ℕ) < N), G.Adj ⟨u, hu⟩ ⟨v, hv⟩
  symm := ⟨fun _ _ ⟨hu, hv, h⟩ => ⟨hv, hu, h.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, h⟩ => G.loopless.irrefl _ h⟩

variable {N N' : ℕ}

theorem padGraph_adj {G : SimpleGraph (Fin N)} {u v : Fin N'} :
    (padGraph G N').Adj u v ↔ ∃ (hu : (u : ℕ) < N) (hv : (v : ℕ) < N), G.Adj ⟨u, hu⟩ ⟨v, hv⟩ :=
  Iff.rfl

/-- Padding to the same size changes nothing. -/
theorem padGraph_self (G : SimpleGraph (Fin N)) : padGraph G N = G := by
  ext u v
  rw [padGraph_adj]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩

/-- Padding keeps `k`-colourability (`k ≥ 1`). -/
theorem padGraph_colorable {G : SimpleGraph (Fin N)} {k : ℕ} (hk : 1 ≤ k) (h : G.Colorable k) :
    (padGraph G N').Colorable k := by
  obtain ⟨c⟩ := h
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if hv : (v : ℕ) < N then c ⟨v, hv⟩ else ⟨0, hk⟩) ?_⟩
  rintro u v ⟨hu, hv, hadj⟩
  simp only [hu, hv, ↓reduceDIte]
  exact c.valid hadj

/-- Padding keeps triangle-freeness. -/
theorem padGraph_cliqueFree {G : SimpleGraph (Fin N)} (h : G.CliqueFree 3) :
    (padGraph G N').CliqueFree 3 := by
  apply cliqueFree_three_of
  rintro x y z _ _ ⟨hx, hy, hxy⟩ ⟨hx', hz, hxz⟩ ⟨hy', hz', hyz⟩
  exact h _ (SimpleGraph.is3Clique_triple_iff.2 ⟨hxy, hxz, hyz⟩)

/-- Padding keeps isomorphisms. -/
theorem padGraph_iso {G₁ G₂ : SimpleGraph (Fin N)} (hN : N ≤ N') (e : G₁ ≃g G₂) :
    Nonempty (padGraph G₁ N' ≃g padGraph G₂ N') := by
  classical
  let f : Fin N ≃ {x : Fin N' // (x : ℕ) < N} :=
    { toFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hN⟩, i.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ψ : Equiv.Perm (Fin N') := Equiv.Perm.extendDomain (e.toEquiv : Equiv.Perm (Fin N)) f
  have hψ₁ : ∀ x : Fin N', ∀ hx : (x : ℕ) < N, ψ x = ⟨e ⟨x, hx⟩, lt_of_lt_of_le (e _).2 hN⟩ := by
    intro x hx
    apply Fin.ext
    change ((Equiv.Perm.extendDomain (e.toEquiv : Equiv.Perm (Fin N)) f x : Fin N') : ℕ) = _
    rw [Equiv.Perm.extendDomain_apply_subtype _ f hx]
    rfl
  have hψ₂ : ∀ x : Fin N', ¬ (x : ℕ) < N → ψ x = x :=
    fun x hx => Equiv.Perm.extendDomain_apply_not_subtype _ f hx
  refine ⟨⟨ψ, fun {u v} => ?_⟩⟩
  change (padGraph G₂ N').Adj (ψ u) (ψ v) ↔ (padGraph G₁ N').Adj u v
  rw [padGraph_adj, padGraph_adj]
  by_cases hu : (u : ℕ) < N
  · by_cases hv : (v : ℕ) < N
    · rw [hψ₁ u hu, hψ₁ v hv]
      constructor
      · rintro ⟨h₁, h₂, h⟩
        exact ⟨hu, hv, e.map_adj_iff.1 h⟩
      · rintro ⟨h₁, h₂, h⟩
        exact ⟨(e _).2, (e _).2, e.map_adj_iff.2 h⟩
    · rw [hψ₂ v hv]
      constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact absurd h₂ hv
  · rw [hψ₂ u hu]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact absurd h₁ hu

theorem mem_truncSeq_seq {n : ℕ} {I : OnlineInput n} {a b : ℕ} :
    a ∈ truncSeq I.seq n b ↔ ∃ (ha : a < n) (hb : b < n), (⟨a, ha⟩ : Fin n) ∈ I.nbr ⟨b, hb⟩ := by
  unfold truncSeq OnlineInput.seq
  by_cases hb : b < n
  · rw [ite_eq_left hb, dite_eq_left hb, Finset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hb, hx⟩
    · rintro ⟨ha, hb', h⟩
      exact ⟨_, h, rfl⟩
  · rw [ite_eq_right hb]
    constructor
    · intro h
      simp at h
    · rintro ⟨ha, hb', h⟩
      exact absurd hb' hb

/-- The padded input `padInput I N'` presents the padded graph `padGraph I.graph N'`. -/
theorem padInput_graph {n : ℕ} (I : OnlineInput n) (N' : ℕ) :
    (padInput I N').graph = padGraph I.graph N' := by
  ext u v
  change (OnlineInput.ofSeq (truncSeq I.seq n) _ N').graph.Adj u v ↔ _
  rw [OnlineInput.ofSeq_adj, padGraph_adj, mem_truncSeq_seq, mem_truncSeq_seq]
  constructor
  · rintro (⟨hu, hv, h⟩ | ⟨hv, hu, h⟩)
    · exact ⟨hu, hv, Or.inl h⟩
    · exact ⟨hu, hv, Or.inr h⟩
  · rintro ⟨hu, hv, h | h⟩
    · exact Or.inl ⟨hu, hv, h⟩
    · exact Or.inr ⟨hv, hu, h⟩

end OnlineColouring
