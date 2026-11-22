module

public import OnlineColouring.Towers
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Non-vacuity: every ordered graph has a reservation blow-up

To make sure that the hypotheses of the converse half of Corollary 5.4 (colourability of iterated
blow-ups) can be met, we construct for every ordered graph `H` on `V` a reservation blow-up, in
the sense of Definition 4.6, on `V ×ₗ V` (lexicographic order):

* the block of `w` is `{(w, v) | v ∈ V}`, so blocks are nonempty and contiguous;
* `(w, v)` serves the arc `w → v` if `w < v` and `w ~ v` in `H`, and serves nothing otherwise
  (in particular `(w, w)` is a private sink of the block).

Consequently full towers of every height exist over every clique (`exists_isFullTower`), and
the colourability threshold is attained: some full `j`-fold blow-up of `K_m` is `k`-colourable
iff `m ≤ |P_j(k)|` (`exists_fullTower_colorable_iff`).
-/

@[expose] public section

namespace OnlineColouring

open scoped Classical in
/-- The serve map of the canonical blow-up. -/
noncomputable def canonServe {V : Type*} [LinearOrder V] (H : SimpleGraph V) (x : V ×ₗ V) :
    Option V :=
  if (ofLex x).1 < (ofLex x).2 ∧ H.Adj (ofLex x).1 (ofLex x).2 then some (ofLex x).2 else none

theorem canonServe_eq_some {V : Type*} [LinearOrder V] {H : SimpleGraph V} {x : V ×ₗ V}
    {v : V} : canonServe H x = some v ↔
      ((ofLex x).1 < (ofLex x).2 ∧ H.Adj (ofLex x).1 (ofLex x).2) ∧ (ofLex x).2 = v := by
  unfold canonServe
  split_ifs with h <;> simp [h]

/-- The canonical blow-up graph on `V ×ₗ V`. -/
noncomputable def canonGraph {V : Type*} [LinearOrder V] (H : SimpleGraph V) :
    SimpleGraph (V ×ₗ V) where
  Adj x u := (x < u ∧ canonServe H x = some (ofLex u).1) ∨
    (u < x ∧ canonServe H u = some (ofLex x).1)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩

/-- The canonical blow-up structure. -/
noncomputable def canonBlowUp {V : Type*} [LinearOrder V] (H : SimpleGraph V) :
    BlowUp H (canonGraph H) where
  π x := (ofLex x).1
  serve := canonServe H
  π_surjective w := ⟨toLex (w, w), rfl⟩
  lt_of_π_lt x y h := Prod.Lex.lt_iff.2 (Or.inl h)
  serve_spec x v h := by
    obtain ⟨h₁, rfl⟩ := canonServe_eq_some.1 h
    exact h₁
  adj_iff _ _ := Iff.rfl

/-- The canonical blow-up is a reservation blow-up: the arc `w → v` is served by `(w, v)` only. -/
theorem canonBlowUp_isReservation {V : Type*} [LinearOrder V] (H : SimpleGraph V) :
    (canonBlowUp H).IsReservation := by
  intro w v hwv hadj
  refine ⟨toLex (w, v), ⟨rfl, canonServe_eq_some.2 ⟨⟨hwv, hadj⟩, rfl⟩⟩, ?_⟩
  rintro x ⟨hxw, hxv⟩
  obtain ⟨-, hx2⟩ := canonServe_eq_some.1 hxv
  change (ofLex x).1 = w at hxw
  apply ofLex.injective
  simp only [ofLex_toLex]
  exact Prod.ext hxw hx2

theorem canonBlowUp_isFull {V : Type*} [LinearOrder V] (H : SimpleGraph V) :
    (canonBlowUp H).IsFull :=
  (canonBlowUp_isReservation H).isFull

/-- Every ordered graph has a full blow-up (indeed a reservation blow-up). -/
theorem exists_full_blowUp (H : OrdGraph) :
    ∃ G : OrdGraph, ∃ B : BlowUp H.G G.G, B.IsFull :=
  ⟨⟨H.V ×ₗ H.V, canonGraph H.G⟩, canonBlowUp H.G, canonBlowUp_isFull H.G⟩

/-- Full towers of every height exist over every clique. -/
theorem exists_isFullTower (m j : ℕ) : ∃ G : OrdGraph, IsFullTower m j G := by
  induction j with
  | zero => exact ⟨_, .clique⟩
  | succ j ih =>
    obtain ⟨H, hH⟩ := ih
    obtain ⟨G, hG⟩ := exists_full_blowUp H
    exact ⟨G, .blowUp hH hG⟩

/-- **Corollary 5.4 (colourability of iterated blow-ups), as an equivalence.** Some (equivalently,
every) full `j`-fold blow-up of `K_m` is `k`-colourable iff `m ≤ |P_j(k)|`. -/
theorem exists_fullTower_colorable_iff (m j k : ℕ) :
    (∃ G : OrdGraph, IsFullTower m j G ∧ G.G.Colorable k) ↔
      m ≤ Fintype.card (LabelPoset k j) := by
  constructor
  · rintro ⟨G, hT, hc⟩
    exact hT.le_card hc
  · intro hm
    obtain ⟨G, hT⟩ := exists_isFullTower m j
    exact ⟨G, hT, hT.isTower.colorable hm⟩

end OnlineColouring
