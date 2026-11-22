module

public import OnlineColouring.NumPoset

/-!
# The label posets `P_j(2)`: `|P_j(2)| = j + 2` and `width(P_j(2)) = 2`

Paper: Section 5, after Corollary 5.7: "The first values are
`|P_j(2)| = j + 2` … For `k = 2` the width stays `2`"; Section 9, after the proof of Theorem 1.4:
"`width(P_j(2)) = 2` for all `j`".

`P_j(2)` consists of two incomparable minimal elements and a chain of `j` elements above both.
`IsVee a b` expresses this shape: `a` and `b` are incomparable, and every other element lies above
both and is comparable with every element.  For such a poset the nonempty down-sets are the
principal ones and `{a, b}` (`IsVee.eq_pair_or_principal`), so `|J*(P)| = |P| + 1`
(`IsVee.card_jst`), `J*(P)` has the same shape with `↓a`, `↓b` (`IsVee.jst`), and the width is
`2` (`IsVee.width_eq`).

* `card_labelPoset_two : |P_j(2)| = j + 2` for all `j`.
* `width_labelPoset_two : width(P_j(2)) = 2` for all `j`.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

open Finset

variable {P : Type*} [PartialOrder P]

/-- `a` and `b` are incomparable, and every other element of `P` lies above both and is
comparable with every element: `P` is the two-element antichain `{a, b}` with a chain on top. -/
def IsVee (a b : P) : Prop :=
  ¬ a ≤ b ∧ ¬ b ≤ a ∧ ∀ x, x = a ∨ x = b ∨ (a ≤ x ∧ b ≤ x ∧ ∀ y, y ≤ x ∨ x ≤ y)

theorem IsVee.symm {a b : P} (h : IsVee a b) : IsVee b a :=
  ⟨h.2.1, h.1, fun x => by
    rcases h.2.2 x with hx | hx | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)⟩

theorem IsVee.eq_of_le_left {a b : P} (h : IsVee a b) {y : P} (hy : y ≤ a) : y = a := by
  rcases h.2.2 y with rfl | rfl | ⟨h1, -, -⟩
  · rfl
  · exact absurd hy h.2.1
  · exact le_antisymm hy h1

/-- A down-set in which `a` is a maximal element is `{a, b}` or `↓a`. -/
theorem IsVee.mem_iff_of_maximal {a b : P} (h : IsVee a b) (D : Jst P) (haD : a ∈ D)
    (hmax : ∀ y, y ∈ D → a ≤ y → y ≤ a) :
    (∀ p, p ∈ D ↔ p = a ∨ p = b) ∨ (∀ p, p ∈ D ↔ p ≤ a) := by
  by_cases hb : b ∈ D
  · left
    intro p
    constructor
    · intro hp
      rcases h.2.2 p with rfl | rfl | ⟨h1, -, -⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl (le_antisymm (hmax p hp h1) h1)
    · rintro (rfl | rfl)
      · exact haD
      · exact hb
  · right
    intro p
    constructor
    · intro hp
      rcases h.2.2 p with rfl | rfl | ⟨h1, -, -⟩
      · exact le_rfl
      · exact absurd hp hb
      · exact hmax p hp h1
    · intro hp
      exact Jst.mem_of_le hp haD

section Fin

variable [Fintype P] [DecidableLE P]

theorem mem_principal {x p : P} : p ∈ principalEmbedding x ↔ p ≤ x := by
  change p ∈ Jst.down {x} (Finset.singleton_nonempty x) ↔ _
  rw [Jst.mem_down]
  simp

omit [Fintype P] [DecidableLE P] in
theorem IsVee.isLowerFinset_pair [DecidableEq P] {a b : P} (h : IsVee a b) :
    IsLowerFinset ({a, b} : Finset P) := by
  intro x hx y hyx
  rcases mem_insert.1 hx with rfl | hx
  · rw [h.eq_of_le_left hyx]
    exact mem_insert_self _ _
  · rw [mem_singleton] at hx
    subst hx
    rw [h.symm.eq_of_le_left hyx]
    exact mem_insert_of_mem (mem_singleton_self _)

/-- The down-set `{a, b}`. -/
def IsVee.pair [DecidableEq P] {a b : P} (h : IsVee a b) : Jst P :=
  Jst.mk {a, b} h.isLowerFinset_pair (insert_nonempty _ _)

omit [Fintype P] [DecidableLE P] in
theorem IsVee.mem_pair [DecidableEq P] {a b : P} (h : IsVee a b) {p : P} :
    p ∈ h.pair ↔ p = a ∨ p = b := by
  change p ∈ ({a, b} : Finset P) ↔ _
  simp

/-- **The down-sets of a vee.**  Every nonempty down-set is `{a, b}` or principal. -/
theorem IsVee.eq_pair_or_principal [DecidableEq P] {a b : P} (h : IsVee a b) (D : Jst P) :
    D = h.pair ∨ ∃ x, D = principalEmbedding x := by
  obtain ⟨g, hg⟩ := Finset.exists_maximal (s := D.val) D.2.2
  have hgD : g ∈ D := hg.1
  have hmax : ∀ y, y ∈ D → g ≤ y → y ≤ g := fun y hy hgy => hg.2 hy hgy
  rcases h.2.2 g with rfl | rfl | ⟨-, -, hcomp⟩
  · rcases h.mem_iff_of_maximal D hgD hmax with h1 | h1
    · left
      ext p
      rw [h1, h.mem_pair]
    · right
      exact ⟨_, by ext p; rw [h1, mem_principal]⟩
  · rcases h.symm.mem_iff_of_maximal D hgD hmax with h1 | h1
    · left
      ext p
      rw [h1, h.mem_pair, or_comm]
    · right
      exact ⟨_, by ext p; rw [h1, mem_principal]⟩
  · right
    refine ⟨g, ?_⟩
    ext p
    rw [mem_principal]
    constructor
    · intro hp
      rcases hcomp p with h1 | h1
      · exact h1
      · exact hmax p hp h1
    · intro hp
      exact Jst.mem_of_le hp hgD

theorem IsVee.pair_ne_principal [DecidableEq P] {a b : P} (h : IsVee a b) (x : P) :
    h.pair ≠ principalEmbedding x := by
  intro hx
  have ha : a ≤ x := mem_principal.1 (hx ▸ h.mem_pair.2 (Or.inl rfl))
  have hb : b ≤ x := mem_principal.1 (hx ▸ h.mem_pair.2 (Or.inr rfl))
  have hxm : x ∈ h.pair := hx ▸ mem_principal.2 le_rfl
  rcases h.mem_pair.1 hxm with rfl | rfl
  · exact h.2.1 hb
  · exact h.1 ha

/-- **Size.**  A vee has one more nonempty down-set than elements. -/
theorem IsVee.card_jst [DecidableEq P] {a b : P} (h : IsVee a b) :
    Fintype.card (Jst P) = Fintype.card P + 1 := by
  have hnot : h.pair ∉ (univ : Finset P).image principalEmbedding := by
    intro hm
    obtain ⟨x, -, hx⟩ := mem_image.1 hm
    exact h.pair_ne_principal x hx.symm
  have huniv : (univ : Finset (Jst P)) =
      insert h.pair ((univ : Finset P).image principalEmbedding) := by
    ext D
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases h.eq_pair_or_principal D with h1 | ⟨x, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x, h1.symm⟩
  rw [← card_univ, huniv, card_insert_of_notMem hnot,
    card_image_of_injective _ principalEmbedding.injective, card_univ]

/-- **Shape.**  The nonempty down-sets of a vee form a vee, with `↓a` and `↓b` at the bottom. -/
theorem IsVee.jst {a b : P} (h : IsVee a b) :
    IsVee (principalEmbedding a) (principalEmbedding b) := by
  classical
  have hpa : principalEmbedding a ≤ h.pair := fun p hp =>
    h.mem_pair.2 (Or.inl (h.eq_of_le_left (mem_principal.1 hp)))
  have hpb : principalEmbedding b ≤ h.pair := fun p hp =>
    h.mem_pair.2 (Or.inr (h.symm.eq_of_le_left (mem_principal.1 hp)))
  have hpx : ∀ x, a ≤ x → b ≤ x → h.pair ≤ principalEmbedding x := by
    intro x hax hbx p hp
    rcases h.mem_pair.1 hp with rfl | rfl
    · exact mem_principal.2 hax
    · exact mem_principal.2 hbx
  refine ⟨fun hle => h.1 (principalEmbedding.le_iff_le.1 hle),
    fun hle => h.2.1 (principalEmbedding.le_iff_le.1 hle), fun D => ?_⟩
  rcases h.eq_pair_or_principal D with rfl | ⟨x, rfl⟩
  · refine Or.inr (Or.inr ⟨hpa, hpb, fun D' => ?_⟩)
    rcases h.eq_pair_or_principal D' with rfl | ⟨y, rfl⟩
    · exact Or.inl le_rfl
    · rcases h.2.2 y with rfl | rfl | ⟨hay, hby, -⟩
      · exact Or.inl hpa
      · exact Or.inl hpb
      · exact Or.inr (hpx y hay hby)
  · rcases h.2.2 x with rfl | rfl | ⟨hax, hbx, hcomp⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨principalEmbedding.le_iff_le.2 hax,
        principalEmbedding.le_iff_le.2 hbx, fun D' => ?_⟩)
      rcases h.eq_pair_or_principal D' with rfl | ⟨y, rfl⟩
      · exact Or.inl (hpx x hax hbx)
      · rcases hcomp y with hyx | hxy
        · exact Or.inl (principalEmbedding.le_iff_le.2 hyx)
        · exact Or.inr (principalEmbedding.le_iff_le.2 hxy)

omit [DecidableLE P] in
/-- **Width.**  A vee has width `2`. -/
theorem IsVee.width_eq {a b : P} (h : IsVee a b) : width P = 2 := by
  classical
  have hab : a ≠ b := fun e => h.1 (e ▸ le_rfl)
  refine le_antisymm (width_le_of_forall fun A hA => ?_) (le_width_iff.2 ⟨{a, b}, ?_, ?_⟩)
  · by_cases hx : ∃ x ∈ A, x ≠ a ∧ x ≠ b
    · obtain ⟨x, hxA, hxa, hxb⟩ := hx
      rcases h.2.2 x with h1 | h1 | ⟨-, -, hcomp⟩
      · exact absurd h1 hxa
      · exact absurd h1 hxb
      · have hsub : A ⊆ {x} := by
          intro y hy
          rw [mem_singleton]
          by_contra hne
          rcases hcomp y with h2 | h2
          · exact hA hy hxA hne h2
          · exact hA hxA hy (Ne.symm hne) h2
        exact (card_le_card hsub).trans (by simp)
    · have hsub : A ⊆ {a, b} := by
        intro y hy
        by_contra hne
        rw [mem_insert, mem_singleton, not_or] at hne
        exact hx ⟨y, hy, hne.1, hne.2⟩
      exact (card_le_card hsub).trans card_le_two
  · intro x hx y hy hne hle
    have hx' : x = a ∨ x = b := by simpa using hx
    have hy' : y = a ∨ y = b := by simpa using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact hne rfl
    · exact h.1 hle
    · exact h.2.1 hle
    · exact hne rfl
  · exact card_pair hab

end Fin

/-! ### The label posets `P_j(2)` -/

/-- `P_j(2)` is a vee, for every `j`. -/
theorem exists_isVee_labelPoset_two : ∀ j : ℕ, ∃ a b : LabelPoset 2 j, IsVee a b
  | 0 => by
    have key : ∀ x : Anti (Fin 2), x = Anti.mk 0 ∨ x = Anti.mk 1 := by decide
    have h01 : (Anti.mk 0 : Anti (Fin 2)) ≠ Anti.mk 1 := by decide
    refine ⟨Anti.mk (0 : Fin 2), Anti.mk (1 : Fin 2), fun h => h01 (Anti.le_iff.1 h),
      fun h => h01 (Anti.le_iff.1 h).symm, fun x => ?_⟩
    rcases key x with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
  | j + 1 => by
    obtain ⟨a, b, h⟩ := exists_isVee_labelPoset_two j
    exact ⟨principalEmbedding a, principalEmbedding b, h.jst⟩

/-- **`|P_j(2)| = j + 2` for all `j`.** -/
theorem card_labelPoset_two : ∀ j : ℕ, Fintype.card (LabelPoset 2 j) = j + 2
  | 0 => card_labelPoset_zero 2
  | j + 1 => by
    obtain ⟨a, b, h⟩ := exists_isVee_labelPoset_two j
    have h1 : Fintype.card (LabelPoset 2 (j + 1)) = Fintype.card (LabelPoset 2 j) + 1 :=
      h.card_jst
    rw [h1, card_labelPoset_two j]

/-- **`width(P_j(2)) = 2` for all `j`.** -/
theorem width_labelPoset_two (j : ℕ) : width (LabelPoset 2 j) = 2 := by
  obtain ⟨a, b, h⟩ := exists_isVee_labelPoset_two j
  exact h.width_eq

end Num

end OnlineColouring
