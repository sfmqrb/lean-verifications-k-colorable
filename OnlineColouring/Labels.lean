module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Antichain
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Posets, nonempty down-sets and labellings

This file sets up the static vocabulary of the paper: the paragraph "Posets and labels" of
Section 4 and Definition 4.5 (templates and labellings).

* `Anti α` is the type `α` with the discrete order (`a ≤ b ↔ a = b`); `Anti (Fin k)` is the
  antichain `P_0(k)`, with the colours `0, …, k-1`.
* `IsLowerFinset s` says that the finset `s` is a down-set.
* `Jst P` is `J*(P)`, the poset of nonempty down-sets of `P`, ordered by inclusion.  We use a
  subtype of `Finset P` (rather than Mathlib's `LowerSet`, which is `Set`-based) so that all the
  instances are computable and small cases can be checked with `decide`;
  `Jst.lowerSetEmbedding` and `Jst.exists_lowerSet_eq` identify it, for finite `P`, with the
  nonempty lower sets of Mathlib.
* `IsLabelling G f` says that `f : V → P` is a `P`-labelling of the ordered graph `(V, <, G)`:
  `f u ≰ f v` whenever `u < v` and `uv` is an edge (Definition 4.5).
* `HasLabelling G P` says that `G` has a `P`-labelling, which the paper calls "`G` maps to
  `Tmpl(P)`"; the template digraph `Tmpl(P)` is not defined as an object.  The two remarks after
  Definition 4.5 are `HasLabelling.induce` (a labelling restricts to every induced ordered
  subgraph) and `hasLabelling_anti_fin_iff_colorable` (a `P_0(k)`-labelling is a proper
  `k`-colouring).
-/

@[expose] public section

namespace OnlineColouring

/-! ### The antichain -/

/-- `Anti α` is a copy of `α` carrying the discrete partial order `a ≤ b ↔ a = b`. -/
def Anti (α : Type*) : Type _ := α

namespace Anti

variable {α : Type*}

/-- The identity map `α → Anti α`. -/
def mk (a : α) : Anti α := a

/-- The identity map `Anti α → α`. -/
def val (a : Anti α) : α := a

instance [DecidableEq α] : DecidableEq (Anti α) := inferInstanceAs (DecidableEq α)
instance [Fintype α] : Fintype (Anti α) := inferInstanceAs (Fintype α)

instance : PartialOrder (Anti α) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

instance [DecidableEq α] : DecidableLE (Anti α) := fun a b => (inferInstance : Decidable (a = b))

@[simp] theorem le_iff {a b : Anti α} : a ≤ b ↔ a = b := Iff.rfl

@[simp] theorem card [Fintype α] : Fintype.card (Anti α) = Fintype.card α := rfl

/-- In `Anti α` every set is an antichain. -/
theorem isAntichain (s : Set (Anti α)) : IsAntichain (· ≤ ·) s := fun _ _ _ _ hne h => hne h

end Anti

/-! ### Down-sets and `J*(P)` -/

variable {P : Type*} [PartialOrder P]

/-- A finset `s` is a down-set if `b ≤ a ∈ s` implies `b ∈ s`. -/
def IsLowerFinset (s : Finset P) : Prop := ∀ a ∈ s, ∀ b, b ≤ a → b ∈ s

theorem isLowerFinset_iff_isLowerSet (s : Finset P) : IsLowerFinset s ↔ IsLowerSet (s : Set P) :=
  ⟨fun h _ _ hba ha => h _ ha _ hba, fun h _ ha _ hba => h hba ha⟩

instance [Fintype P] [DecidableEq P] [DecidableLE P] (s : Finset P) :
    Decidable (IsLowerFinset s) :=
  inferInstanceAs (Decidable (∀ a ∈ s, ∀ b, b ≤ a → b ∈ s))

/-- `J*(P)`: the nonempty down-sets of `P`, ordered by inclusion. -/
def Jst (P : Type*) [PartialOrder P] : Type _ := {s : Finset P // IsLowerFinset s ∧ s.Nonempty}

namespace Jst

instance : PartialOrder (Jst P) :=
  inferInstanceAs (PartialOrder {s : Finset P // IsLowerFinset s ∧ s.Nonempty})

/-- The underlying finset of a nonempty down-set. -/
def val (s : Jst P) : Finset P := Subtype.val s

instance : Membership P (Jst P) := ⟨fun s p => p ∈ s.val⟩

/-- Build an element of `J*(P)` from a nonempty lower finset. -/
def mk (s : Finset P) (h₁ : IsLowerFinset s) (h₂ : s.Nonempty) : Jst P := ⟨s, h₁, h₂⟩

@[simp] theorem val_mk (s : Finset P) (h₁ h₂) : (mk s h₁ h₂).val = s := rfl

@[simp] theorem mem_val {s : Jst P} {p : P} : p ∈ s.val ↔ p ∈ s := Iff.rfl

@[simp] theorem mem_mk {s : Finset P} {h₁ h₂} {p : P} : p ∈ mk s h₁ h₂ ↔ p ∈ s := Iff.rfl

theorem isLower (s : Jst P) : IsLowerFinset s.val := s.2.1

theorem nonempty (s : Jst P) : ∃ p, p ∈ s := s.2.2

theorem mem_of_le {s : Jst P} {a b : P} (hb : b ≤ a) (ha : a ∈ s) : b ∈ s := s.2.1 a ha b hb

theorem le_iff {s t : Jst P} : s ≤ t ↔ s.val ⊆ t.val := Iff.rfl

theorem le_iff_forall {s t : Jst P} : s ≤ t ↔ ∀ p, p ∈ s → p ∈ t := Iff.rfl

theorem val_injective : Function.Injective (val : Jst P → Finset P) := Subtype.val_injective

@[ext] theorem ext {s t : Jst P} (h : ∀ p, p ∈ s ↔ p ∈ t) : s = t :=
  val_injective (Finset.ext h)

instance [DecidableEq P] : DecidableEq (Jst P) :=
  inferInstanceAs (DecidableEq {s : Finset P // IsLowerFinset s ∧ s.Nonempty})

instance [DecidableEq P] : DecidableLE (Jst P) := fun s t =>
  decidable_of_iff (s.val ⊆ t.val) Iff.rfl

instance [Fintype P] [DecidableEq P] [DecidableLE P] : Fintype (Jst P) :=
  inferInstanceAs (Fintype {s : Finset P // IsLowerFinset s ∧ s.Nonempty})

/-- The underlying set of an element of `J*(P)` is a down-set in Mathlib's sense. -/
theorem isLowerSet (s : Jst P) : IsLowerSet (s.val : Set P) :=
  (isLowerFinset_iff_isLowerSet _).1 s.isLower

/-- The corresponding element of Mathlib's `LowerSet P`. -/
def lowerSet (s : Jst P) : LowerSet P := ⟨s.val, s.isLowerSet⟩

/-- `Jst.lowerSet` is an order embedding of `J*(P)` into Mathlib's lattice of down-sets, whose
image consists of the nonempty down-sets (when `P` is finite, every down-set is finite). -/
def lowerSetEmbedding : Jst P ↪o LowerSet P :=
  OrderEmbedding.ofMapLEIff lowerSet fun s t => by
    change ((s.val : Set P) ⊆ t.val) ↔ s.val ⊆ t.val
    exact Finset.coe_subset

theorem lowerSet_nonempty (s : Jst P) : (s.lowerSet : Set P).Nonempty := by
  obtain ⟨p, hp⟩ := s.nonempty
  exact ⟨p, hp⟩

theorem exists_lowerSet_eq [Finite P] (L : LowerSet P) (hL : (L : Set P).Nonempty) :
    ∃ s : Jst P, s.lowerSet = L := by
  classical
  have hfin : (L : Set P).Finite := Set.toFinite _
  refine ⟨⟨hfin.toFinset, ?_, ?_⟩, ?_⟩
  · intro a ha b hba
    simp only [Set.Finite.mem_toFinset] at ha ⊢
    exact L.lower hba ha
  · simpa using hL
  · ext p
    simp [lowerSet, val]

end Jst

/-! ### Ordered graphs and labellings -/

section Labelling

variable {V : Type*} [LinearOrder V]

/-- Definition 4.5: `f : V → P` is a `P`-labelling of the ordered graph `G` (the vertex order of
`V` is the arrival order) if `f u ≰ f v` for every edge `uv` with `u` earlier than `v`. -/
def IsLabelling (G : SimpleGraph V) (f : V → P) : Prop :=
  ∀ ⦃u v : V⦄, u < v → G.Adj u v → ¬ f u ≤ f v

/-- `G` maps to the template `Tmpl(P)` (Definition 4.5), i.e. it has a `P`-labelling. -/
def HasLabelling (G : SimpleGraph V) (P : Type*) [PartialOrder P] : Prop :=
  ∃ f : V → P, IsLabelling G f

/-- A labelling of `G` is a labelling of every subgraph of `G` on the same ordered vertex set. -/
theorem IsLabelling.mono {G G' : SimpleGraph V} (h : G' ≤ G) {f : V → P}
    (hf : IsLabelling G f) : IsLabelling G' f :=
  fun _ _ huv hadj => hf huv (h hadj)

/-- Labellings pull back along order embeddings that map edges to edges. -/
theorem IsLabelling.comap {W : Type*} [LinearOrder W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (e : W ↪o V) (he : ∀ ⦃x y⦄, G'.Adj x y → G.Adj (e x) (e y)) {f : V → P}
    (hf : IsLabelling G f) : IsLabelling G' (f ∘ e) :=
  fun _ _ hxy hadj => hf (e.strictMono hxy) (he hadj)

/-- A `P`-labelling restricts to every induced ordered subgraph. -/
theorem HasLabelling.induce {G : SimpleGraph V} (h : HasLabelling G P) (s : Set V) :
    HasLabelling (G.induce s) P := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun x => f x, fun _ _ hxy hadj => hf hxy hadj⟩

/-- **Labellings by the antichain are proper colourings.**  Since `a ≤ b ↔ a = b` in `Anti α`,
an `Anti α`-labelling of `G` is exactly a proper colouring of `G` with colours in `α`. -/
theorem isLabelling_anti_iff {α : Type*} {G : SimpleGraph V} {f : V → Anti α} :
    IsLabelling G f ↔ ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v := by
  constructor
  · intro hf u v hadj
    rcases lt_trichotomy u v with huv | huv | huv
    · exact hf huv hadj
    · exact absurd huv (G.ne_of_adj hadj)
    · exact fun h => hf huv hadj.symm h.symm
  · intro hf u v _ hadj
    exact hf hadj

/-- `G` has an `Anti α`-labelling iff it has a proper colouring with colours in `α`. -/
theorem hasLabelling_anti_iff_nonempty_coloring {α : Type*} {G : SimpleGraph V} :
    HasLabelling G (Anti α) ↔ Nonempty (G.Coloring α) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨SimpleGraph.Coloring.mk (fun v => Anti.val (f v))
      fun hadj => isLabelling_anti_iff.1 hf hadj⟩
  · rintro ⟨c⟩
    exact ⟨fun v => Anti.mk (c v), isLabelling_anti_iff.2 fun _ _ hadj => c.valid hadj⟩

/-- **A `P_0(k)`-labelling is a proper `k`-colouring** (remark after Definition 4.5). -/
theorem hasLabelling_anti_fin_iff_colorable {k : ℕ} {G : SimpleGraph V} :
    HasLabelling G (Anti (Fin k)) ↔ G.Colorable k :=
  hasLabelling_anti_iff_nonempty_coloring

end Labelling

end OnlineColouring
