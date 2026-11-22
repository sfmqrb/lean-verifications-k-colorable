module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Multiset.MapFold

/-!
# The abstract one-level game

Paper: Appendix D.3 ("One level, exactly") and Question 10.3.  The values `V(m)`
of the minimal one-level game are certified by strategies for an *abstract* game, in which a
position is a list of multisets of colours: one row for each earlier block, containing the colours
of its vertices that have not served yet.  This file defines that game and proves its symmetries;
nothing here is computed, and nothing refers to graphs.  The link to adversaries and algorithms is
`NumOneLevel.lean` (upper bounds) and `NumOneLevelAdv.lean` (lower bounds).

* `Picked rows rows' F`: the adversary picks one server in each earlier block: `rows'` arises from
  `rows` by removing one element from each row, and `F` is the set of the removed colours (the
  colours forbidden for the next block).
* `Surv C bs rows` ("the algorithm survives with the palette `{0, …, C - 1}`"; `bs` lists the
  sizes of the remaining blocks): whatever the adversary picks, the algorithm can colour the next
  block with a multiset `M` of `bs.head` colours of the palette outside `F` and survive from the
  position `M :: rows'`.
* `Win C bs rows` ("the adversary beats the palette"): some choice of servers is such that every
  multiset `M` of allowed colours of the palette leads to a winning position; with no block left
  the adversary has lost.  `win_iff_not_surv`: the game is determined.
* Symmetries: `Surv.perm` (the order of the rows does not matter) and `Surv.of_map` (the names of
  the colours of the palette do not matter); `Win.perm`, `Win.of_map`.
* `Win.cons_row`: an extra row with enough elements does not hurt the adversary.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-- `rows'` arises from `rows` by removing one element from each row, and `F` is the set of the
removed elements. -/
def Picked : List (Multiset ℕ) → List (Multiset ℕ) → Finset ℕ → Prop
  | [], rows', F => rows' = [] ∧ F = ∅
  | r :: rows, rows', F =>
    ∃ c ∈ r, ∃ rs' F', Picked rows rs' F' ∧ rows' = r.erase c :: rs' ∧ F = insert c F'

/-- Picking commutes with reordering the rows. -/
theorem Picked.perm {rows rows₂ : List (Multiset ℕ)} (h : rows.Perm rows₂) :
    ∀ {rows' : List (Multiset ℕ)} {F : Finset ℕ}, Picked rows rows' F →
      ∃ rows₂', Picked rows₂ rows₂' F ∧ rows'.Perm rows₂' := by
  induction h with
  | nil => exact fun {rows' F} hP => ⟨rows', hP, List.Perm.refl _⟩
  | cons x _ ih =>
    intro rows' F hP
    obtain ⟨c, hc, rs', F', hP', rfl, rfl⟩ := hP
    obtain ⟨rs₂', hP₂, hperm⟩ := ih hP'
    exact ⟨x.erase c :: rs₂', ⟨c, hc, rs₂', F', hP₂, rfl, rfl⟩, hperm.cons _⟩
  | swap x y l =>
    intro rows' F hP
    obtain ⟨c, hc, rs', F', hP', rfl, rfl⟩ := hP
    obtain ⟨d, hd, rs'', F'', hP'', rfl, rfl⟩ := hP'
    exact ⟨x.erase d :: y.erase c :: rs'',
      ⟨d, hd, _, _, ⟨c, hc, rs'', F'', hP'', rfl, rfl⟩, rfl, Finset.insert_comm c d F''⟩,
      List.Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    intro rows' F hP
    obtain ⟨r₂, hP₂, hp₂⟩ := ih₁ hP
    obtain ⟨r₃, hP₃, hp₃⟩ := ih₂ hP₂
    exact ⟨r₃, hP₃, hp₂.trans hp₃⟩

/-- Picking commutes with renaming the colours. -/
theorem Picked.map (σ : ℕ → ℕ) : ∀ {rows rows' : List (Multiset ℕ)} {F : Finset ℕ},
    Picked rows rows' F →
      Picked (rows.map (Multiset.map σ)) (rows'.map (Multiset.map σ)) (F.image σ)
  | [], _, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Finset.image_empty σ⟩
  | r :: rows, _, _, h => by
    obtain ⟨c, hc, rs', F', hP, rfl, rfl⟩ := h
    refine ⟨σ c, Multiset.mem_map_of_mem σ hc, rs'.map (Multiset.map σ), F'.image σ,
      hP.map σ, ?_, ?_⟩
    · rw [List.map_cons, Multiset.map_erase_of_mem _ _ hc]
    · rw [Finset.image_insert]

/-- **The algorithm survives** the remaining blocks, of sizes `bs`, with the palette
`{0, …, C - 1}`: whatever one element the adversary removes from each row (the servers of the
next block; `F` is the set of their colours), the algorithm can colour the next block with a
multiset `M` of colours of the palette outside `F` and survive the rest. -/
def Surv (C : ℕ) : List ℕ → List (Multiset ℕ) → Prop
  | [], _ => True
  | bt :: bs, rows => ∀ rows' F, Picked rows rows' F →
      ∃ M : Multiset ℕ, M.card = bt ∧ (∀ c ∈ M, c < C ∧ c ∉ F) ∧ Surv C bs (M :: rows')

/-- **The adversary beats the palette** `{0, …, C - 1}`: it can choose the servers of the next
block so that every colouring of that block within the palette leads to a position from which it
beats the palette.  When no block is left it has lost. -/
def Win (C : ℕ) : List ℕ → List (Multiset ℕ) → Prop
  | [], _ => False
  | bt :: bs, rows => ∃ rows' F, Picked rows rows' F ∧
      ∀ M : Multiset ℕ, M.card = bt → (∀ c ∈ M, c < C ∧ c ∉ F) → Win C bs (M :: rows')

/-- The abstract game is determined. -/
theorem win_iff_not_surv (C : ℕ) :
    ∀ (bs : List ℕ) (rows : List (Multiset ℕ)), Win C bs rows ↔ ¬ Surv C bs rows
  | [], _ => by simp [Win, Surv]
  | bt :: bs, rows => by
    simp only [Win, Surv, win_iff_not_surv C bs]
    push Not
    rfl

/-- The order of the rows does not matter. -/
theorem Surv.perm {C : ℕ} : ∀ {bs : List ℕ} {rows rows₂ : List (Multiset ℕ)},
    rows.Perm rows₂ → Surv C bs rows → Surv C bs rows₂
  | [], _, _, _, _ => trivial
  | bt :: bs, rows, rows₂, hp, hS => by
    intro rows₂' F hP
    obtain ⟨rows', hP', hp'⟩ := Picked.perm hp.symm hP
    obtain ⟨M, hM, hMF, hS'⟩ := hS rows' F hP'
    exact ⟨M, hM, hMF, Surv.perm (hp'.symm.cons M) hS'⟩

/-- The names of the colours do not matter: if `σ` maps the palette onto itself (`τ` is a right
inverse on the palette) and the algorithm survives from the renamed position, then it survives
from the position. -/
theorem Surv.of_map {C : ℕ} {σ τ : ℕ → ℕ} (hτ : ∀ c < C, τ c < C ∧ σ (τ c) = c) :
    ∀ {bs : List ℕ} {rows : List (Multiset ℕ)},
      Surv C bs (rows.map (Multiset.map σ)) → Surv C bs rows
  | [], _, _ => trivial
  | bt :: bs, rows, hS => by
    intro rows' F hP
    obtain ⟨M', hM', hMF', hS'⟩ := hS _ _ (hP.map σ)
    have hστ : (M'.map τ).map σ = M' := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id M']
      exact Multiset.map_congr rfl fun c hc => (hτ c (hMF' c hc).1).2
    refine ⟨M'.map τ, by rw [Multiset.card_map, hM'], ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.1 hc
      refine ⟨(hτ c' (hMF' c' hc').1).1, fun hF => (hMF' c' hc').2 ?_⟩
      rw [Finset.mem_image]
      exact ⟨τ c', hF, (hτ c' (hMF' c' hc').1).2⟩
    · apply Surv.of_map hτ (bs := bs)
      rw [List.map_cons, hστ]
      exact hS'

/-- The order of the rows does not matter for the adversary either. -/
theorem Win.perm {C : ℕ} {bs : List ℕ} {rows rows₂ : List (Multiset ℕ)} (hp : rows.Perm rows₂)
    (hW : Win C bs rows) : Win C bs rows₂ := by
  rw [win_iff_not_surv] at hW ⊢
  exact fun hS => hW (hS.perm hp.symm)

/-- The names of the colours do not matter for the adversary: if `σ` and `τ` are mutually inverse
on the palette, all colours of the position lie in the palette, and the adversary wins from the
renamed position, then it wins from the position. -/
theorem Win.of_map {C : ℕ} {σ τ : ℕ → ℕ} (hσ : ∀ c < C, σ c < C ∧ τ (σ c) = c)
    {bs : List ℕ} {rows : List (Multiset ℕ)} (hrows : ∀ r ∈ rows, ∀ c ∈ r, c < C)
    (hW : Win C bs (rows.map (Multiset.map σ))) : Win C bs rows := by
  rw [win_iff_not_surv] at hW ⊢
  intro hS
  apply hW
  apply Surv.of_map (σ := τ) (τ := σ) hσ
  have h : (rows.map (Multiset.map σ)).map (Multiset.map τ) = rows := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rows]
    refine List.map_congr_left fun r hr => ?_
    change (r.map σ).map τ = r
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id r]
    exact Multiset.map_congr rfl fun c hc => (hσ c (hrows r hr c hc)).2
  rw [h]
  exact hS

/-- An extra row with at least as many elements as there are blocks left does not hurt the
adversary: it picks any element of that row in addition.  (This is the "null move": if the
adversary wins without the next block, it wins whatever the algorithm does with it.) -/
theorem Win.cons_row {C : ℕ} : ∀ {bs : List ℕ} {rows : List (Multiset ℕ)} {X : Multiset ℕ},
    bs.length ≤ X.card → Win C bs rows → Win C bs (X :: rows)
  | [], _, _, _, h => by simp [Win] at h
  | bt :: bs, rows, X, hX, h => by
    rw [List.length_cons] at hX
    obtain ⟨rows', F, hP, hall⟩ := h
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < X.card by omega)
    refine ⟨X.erase x :: rows', insert x F, ⟨x, hx, rows', F, hP, rfl, rfl⟩, fun M hM hMF => ?_⟩
    have h1 := hall M hM fun c hc =>
      ⟨(hMF c hc).1, fun hF => (hMF c hc).2 (Finset.mem_insert_of_mem hF)⟩
    have h2 := Win.cons_row (X := X.erase x)
      (by rw [Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one]; omega) h1
    exact h2.perm (List.Perm.swap _ _ _)

end Num

end OnlineColouring
