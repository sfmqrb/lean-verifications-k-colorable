module

public import OnlineColouring.Towers
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Proposition D.1: reservation-free levels

Appendix D.1 ("Reservations are necessary"), Proposition D.1 (`prop:S`).

A *reservation-free level* over an ordered graph `H` replaces every vertex `v` of `H` by a gadget
`Γ(v)` that contains an edge; every vertex of `Γ(v)` is joined to all of a fixed *selected* set
`X(w) ⊆ Γ(w)` for every earlier neighbour `w` of `v`, and `X(w)` is nonempty whenever `w` has a
later neighbour.  In `ResFreeLevel H G` the gadgets are the fibres of `π : W → V`, and
`X : V → Set W` is the selection; since `X` depends on `w` only, `X(w)` is the same for all later
neighbours of `w`.  The graph `G` may have further edges, inside gadgets and between them; the
proposition does not need to exclude them.  The order of the produced graph `G` plays no role, so
`W` is an arbitrary type.

* `ResFreeLevel.exists_isNClique`: a clique on `s + 1` vertices one level up gives a clique on
  `s + 2` vertices.
* `IsResFreeChain H d G`: `G` arises from `H` by `d` reservation-free levels.
  `IsResFreeChain.exists_isNClique` (`d` levels over a nonempty graph contain `K_{d+1}`),
  `IsResFreeChain.exists_isNClique_of_adj` (over a graph with an edge, `K_{d+2}`),
  `IsResFreeChain.not_colorable` (a chain of `k` levels over a nonempty graph is never
  `k`-colourable) and `IsResFreeChain.not_adj_of_colorable` (a chain of `k-1` levels is
  `k`-colourable only if the graph at the top has no edge).
* `resFreeLevel`, `exists_isResFreeChain`: every ordered graph has a reservation-free level over
  it (gadgets `K_2`), and chains of every length exist, so the hypotheses can be met.
-/

@[expose] public section

namespace OnlineColouring

variable {V W : Type*} [LinearOrder V]

/-- A reservation-free level `G` (on `W`) over the ordered graph `H` (on `V`). -/
structure ResFreeLevel (H : SimpleGraph V) (G : SimpleGraph W) where
  /-- `π x = v` means that `x` belongs to the gadget `Γ(v)`. -/
  π : W → V
  /-- The selected set `X(w) ⊆ Γ(w)`. -/
  X : V → Set W
  /-- `X(w)` lies in the gadget `Γ(w)`. -/
  X_subset : ∀ ⦃w : V⦄ ⦃x : W⦄, x ∈ X w → π x = w
  /-- `X(w)` is nonempty when `w` has a later neighbour. -/
  X_nonempty : ∀ ⦃w v : V⦄, w < v → H.Adj w v → (X w).Nonempty
  /-- Every gadget contains an edge. -/
  gadget_edge : ∀ v : V, ∃ u u' : W, π u = v ∧ π u' = v ∧ G.Adj u u'
  /-- Every vertex of `Γ(v)` is joined to all of `X(w)` for every earlier neighbour `w` of `v`. -/
  adj_of_mem : ∀ ⦃x y : W⦄, π y < π x → H.Adj (π y) (π x) → y ∈ X (π y) → G.Adj x y

namespace ResFreeLevel

variable {H : SimpleGraph V} {G : SimpleGraph W}

/-- **Proposition (reservation-free levels), one level.** If the graph one level up contains a
clique on `s + 1` vertices, then the graph produced by a reservation-free level contains a clique
on `s + 2` vertices. -/
theorem exists_isNClique (L : ResFreeLevel H G) {s : ℕ} {t : Finset V}
    (ht : H.IsNClique (s + 1) t) : ∃ t' : Finset W, G.IsNClique (s + 2) t' := by
  classical
  have hne : t.Nonempty := by
    rw [← Finset.card_pos, ht.card_eq]
    exact Nat.succ_pos s
  -- `q` is the last vertex of the clique, `t₀` the others
  set q := t.max' hne with hq
  have hqt : q ∈ t := Finset.max'_mem _ _
  set t₀ := t.erase q with ht₀
  have hlt : ∀ r ∈ t₀, r < q ∧ H.Adj r q := by
    intro r hr
    obtain ⟨hrq, hrt⟩ := Finset.mem_erase.1 hr
    exact ⟨lt_of_le_of_ne (Finset.le_max' _ _ hrt) hrq, ht.isClique hrt hqt hrq⟩
  -- an edge `u u'` inside `Γ(q)`
  obtain ⟨u, u', hu, hu', huu'⟩ := L.gadget_edge q
  -- `y r ∈ X(r)` for every `r ∈ t₀`
  have hy : ∀ r : V, ∃ y : W, r ∈ t₀ → y ∈ L.X r := by
    intro r
    by_cases hr : r ∈ t₀
    · obtain ⟨y, hy⟩ := L.X_nonempty (hlt r hr).1 (hlt r hr).2
      exact ⟨y, fun _ => hy⟩
    · exact ⟨u, fun h => absurd h hr⟩
  choose y hyX using hy
  have hπy : ∀ r ∈ t₀, L.π (y r) = r := fun r hr => L.X_subset (hyX r hr)
  -- the vertices `y r` form a clique on `s` vertices
  have hY : G.IsNClique s (t₀.image y) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hb
      have hrr' : r ≠ r' := fun h => hab (by rw [h])
      have hcl : H.Adj r r' := ht.isClique (Finset.mem_of_mem_erase hr)
        (Finset.mem_of_mem_erase hr') hrr'
      rcases lt_or_gt_of_ne hrr' with h | h
      · refine (L.adj_of_mem ?_ ?_ ?_).symm
        · rw [hπy r hr, hπy r' hr']; exact h
        · rw [hπy r hr, hπy r' hr']; exact hcl
        · rw [hπy r hr]; exact hyX r hr
      · refine L.adj_of_mem ?_ ?_ ?_
        · rw [hπy r hr, hπy r' hr']; exact h
        · rw [hπy r hr, hπy r' hr']; exact hcl.symm
        · rw [hπy r' hr']; exact hyX r' hr'
    · rw [Finset.card_image_of_injOn, ht₀, Finset.card_erase_of_mem hqt, ht.card_eq]
      · rfl
      · intro r hr r' hr' h
        rw [← hπy r hr, ← hπy r' hr']
        exact congrArg L.π h
  -- a vertex of `Γ(q)` is joined to every `y r`
  have hadj : ∀ z, L.π z = q → ∀ b ∈ t₀.image y, G.Adj z b := by
    intro z hz b hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hb
    refine L.adj_of_mem ?_ ?_ ?_
    · rw [hπy r hr, hz]; exact (hlt r hr).1
    · rw [hπy r hr, hz]; exact (hlt r hr).2
    · rw [hπy r hr]; exact hyX r hr
  have hY' : G.IsNClique (s + 1) (insert u' (t₀.image y)) := hY.insert (hadj u' hu')
  refine ⟨insert u (insert u' (t₀.image y)), hY'.insert ?_⟩
  intro b hb
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact huu'
  · exact hadj u hu b hb

end ResFreeLevel

/-- `IsResFreeChain H d G`: the ordered graph `G` arises from `H` by `d` successive
reservation-free levels. -/
inductive IsResFreeChain (H : OrdGraph) : ℕ → OrdGraph → Prop
  | refl : IsResFreeChain H 0 H
  | step {d : ℕ} {G G' : OrdGraph} :
      IsResFreeChain H d G → Nonempty (ResFreeLevel G.G G'.G) → IsResFreeChain H (d + 1) G'

namespace IsResFreeChain

variable {H G : OrdGraph} {d : ℕ}

/-- `d` reservation-free levels turn a clique on `s + 1` vertices into one on `s + 1 + d`
vertices. -/
theorem exists_isNClique_add (hC : IsResFreeChain H d G) {s : ℕ}
    (ht : ∃ t : Finset H.V, H.G.IsNClique (s + 1) t) :
    ∃ t : Finset G.V, G.G.IsNClique (s + 1 + d) t := by
  induction hC with
  | refl => exact ht
  | @step d G G' _ hL ih =>
    obtain ⟨L⟩ := hL
    obtain ⟨t, ht'⟩ := ih
    rw [show s + 1 + d = (s + d) + 1 by omega] at ht'
    obtain ⟨t', ht''⟩ := L.exists_isNClique ht'
    exact ⟨t', by rwa [show s + 1 + (d + 1) = s + d + 2 by omega]⟩

/-- **Proposition (reservation-free levels).** `d` reservation-free levels over a nonempty graph
produce a clique on `d + 1` vertices. -/
theorem exists_isNClique (hC : IsResFreeChain H d G) [Nonempty H.V] :
    ∃ t : Finset G.V, G.G.IsNClique (d + 1) t := by
  classical
  obtain ⟨v⟩ := ‹Nonempty H.V›
  have := hC.exists_isNClique_add (s := 0) ⟨{v}, SimpleGraph.isNClique_one.2 ⟨v, rfl⟩⟩
  rwa [show 0 + 1 + d = d + 1 by omega] at this

/-- Starting from an edge, `d` reservation-free levels produce a clique on `d + 2` vertices. -/
theorem exists_isNClique_of_adj (hC : IsResFreeChain H d G) {u v : H.V} (huv : H.G.Adj u v) :
    ∃ t : Finset G.V, G.G.IsNClique (d + 2) t := by
  classical
  have h2 : H.G.IsNClique 2 {u, v} := by
    rw [SimpleGraph.isNClique_iff, Finset.card_pair huv.ne]
    refine ⟨?_, rfl⟩
    rw [Finset.coe_pair]
    exact SimpleGraph.isClique_pair.2 fun _ => huv
  have := hC.exists_isNClique_add (s := 1) ⟨_, h2⟩
  rwa [show 1 + 1 + d = d + 2 by omega] at this

/-- **Proposition (reservation-free levels), colourability.** A chain of `k` reservation-free
levels over a nonempty graph is never `k`-colourable. -/
theorem not_colorable {k : ℕ} (hC : IsResFreeChain H k G) [Nonempty H.V] :
    ¬ G.G.Colorable k := by
  intro hc
  obtain ⟨t, ht⟩ := hC.exists_isNClique
  have := ht.isClique.card_le_of_colorable hc
  rw [ht.card_eq] at this
  omega

/-- **Proposition (reservation-free levels), colourability.** A chain of `k - 1` reservation-free
levels (here `d` levels and `k = d + 1`) is `k`-colourable only if the graph at the top has no
edge. -/
theorem not_adj_of_colorable (hC : IsResFreeChain H d G) (hc : G.G.Colorable (d + 1))
    (u v : H.V) : ¬ H.G.Adj u v := by
  intro huv
  obtain ⟨t, ht⟩ := hC.exists_isNClique_of_adj huv
  have := ht.isClique.card_le_of_colorable hc
  rw [ht.card_eq] at this
  omega

end IsResFreeChain

/-! ### Non-vacuity -/

/-- The edge relation of the canonical reservation-free level over `H`: the gadget of `v` is the
edge `(v,0)(v,1)`, the selected set of `w` is `{(w,0)}`, and `(v,i)` is joined to `(w,0)` for
every earlier neighbour `w` of `v`. -/
def resFreeAdj (H : SimpleGraph V) (x y : V × Fin 2) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (y.1 < x.1 ∧ H.Adj y.1 x.1 ∧ y.2 = 0) ∨
    (x.1 < y.1 ∧ H.Adj x.1 y.1 ∧ x.2 = 0)

/-- The canonical reservation-free level graph on `V × Fin 2`. -/
def resFreeGraph (H : SimpleGraph V) : SimpleGraph (V × Fin 2) where
  Adj := resFreeAdj H
  symm := ⟨fun x y h => by
    rcases h with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact h rfl
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h⟩

/-- Every ordered graph has a reservation-free level over it, so the hypotheses of the
proposition can be met. -/
def resFreeLevel (H : SimpleGraph V) : ResFreeLevel H (resFreeGraph H) where
  π x := x.1
  X w := {x | x.1 = w ∧ x.2 = 0}
  X_subset _ _ h := h.1
  X_nonempty w _ _ _ := ⟨(w, 0), rfl, rfl⟩
  gadget_edge v := ⟨(v, 0), (v, 1), rfl, rfl, Or.inl ⟨rfl, Fin.zero_ne_one⟩⟩
  adj_of_mem _ _ hlt hadj hy := Or.inr (Or.inl ⟨hlt, hadj, hy.2⟩)

/-- Chains of reservation-free levels of every length exist over every ordered graph. -/
theorem exists_isResFreeChain (H : OrdGraph) (d : ℕ) : ∃ G : OrdGraph, IsResFreeChain H d G := by
  induction d with
  | zero => exact ⟨H, .refl⟩
  | succ d ih =>
    obtain ⟨G, hG⟩ := ih
    exact ⟨⟨G.V ×ₗ Fin 2, resFreeGraph G.G⟩, .step hG ⟨resFreeLevel G.G⟩⟩

end OnlineColouring
