module

public import OnlineColouring.Growth

/-!
# Base facts about `P_1(3)` and `P_2(3)`

Lemma 5.5 (iii) of the paper and two of the first values that are listed after Corollary 5.7:

* `|P_1(3)| = 7` (`card_labelPoset_three_one`, from the general `|P_1(k)| = 2^k - 1`);
* `|P_2(3)| = 18` (`card_labelPoset_three_two`, by `decide +kernel`);
* the four nonempty down-sets `↓{{1,2}}`, `↓{{1,3}}`, `↓{{2,3}}` and `M = {{1},{2},{3}}` of
  `P_1(3)` are pairwise incomparable, so `width(P_2(3)) ≥ 4`
  (`hasAntichain_labelPoset_three_two`, by `decide +kernel` on an explicit antichain).

All `decide` calls are checked by the kernel (`decide +kernel`); no `native_decide` is used.
The colours are `0, 1, 2 : Fin 3`, where the paper writes `1, 2, 3`.  Of the other values of the
list after Corollary 5.7, `|P_j(2)| = j + 2` for all `j`, `|P_3(3)| = 81`, `|P_4(3)| = 8569` and
`|P_2(4)| = 166` are proved in `NumTwo.lean`, `NumP3.lean` and `NumP4.lean`; the whole list is
`Num.first_values` (`NumValues.lean`).
-/

@[expose] public section

namespace OnlineColouring

/-- In the antichain every finset is a down-set. -/
theorem isLowerFinset_anti {α : Type*} (s : Finset (Anti α)) : IsLowerFinset s := by
  intro a ha b hba
  rw [Anti.le_iff] at hba
  exact hba ▸ ha

namespace BaseFacts

/-- `P_1(3)`, unbundled. -/
abbrev Q1 : Type := Jst (Anti (Fin 3))

/-- `P_2(3)`, unbundled. -/
abbrev Q2 : Type := Jst Q1

/-- The element `{a, b}` of `P_1(3)`. -/
def pair (a b : Fin 3) : Q1 :=
  Jst.mk {Anti.mk a, Anti.mk b} (isLowerFinset_anti _) (Finset.insert_nonempty _ _)

/-- The element `{a}` of `P_1(3)`. -/
def single (a : Fin 3) : Q1 :=
  Jst.mk {Anti.mk a} (isLowerFinset_anti _) (Finset.singleton_nonempty _)

/-- The element `M = {{0}, {1}, {2}}` of `P_2(3)`. -/
def M : Q2 :=
  Jst.mk {single 0, single 1, single 2} (by decide +kernel) (Finset.insert_nonempty _ _)

/-- The element `↓{{a, b}}` of `P_2(3)`. -/
def downPair (a b : Fin 3) : Q2 := Jst.down {pair a b} (Finset.singleton_nonempty _)

/-- The four pairwise incomparable elements of `P_2(3)`. -/
def A : Finset Q2 := {downPair 0 1, downPair 0 2, downPair 1 2, M}

theorem card_A : A.card = 4 := by decide +kernel

theorem A_pairwise : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ≤ b := by decide +kernel

theorem isAntichain_A : IsAntichain (· ≤ ·) (A : Set Q2) :=
  fun a ha b hb hab => A_pairwise a ha b hb hab

theorem card_Q2 : Fintype.card Q2 = 18 := by decide +kernel

end BaseFacts

/-- `|P_1(3)| = 7`. -/
theorem card_labelPoset_three_one : Fintype.card (LabelPoset 3 1) = 7 := by
  rw [card_labelPoset_one]; rfl

/-- `|P_2(3)| = 18`. -/
theorem card_labelPoset_three_two : Fintype.card (LabelPoset 3 2) = 18 :=
  BaseFacts.card_Q2

/-- **Lemma 5.5 (iii).** `P_2(3)` has an antichain of size `4`, so `width(P_2(3)) ≥ 4`. -/
theorem hasAntichain_labelPoset_three_two : HasAntichain (LabelPoset 3 2) 4 :=
  ⟨BaseFacts.A, BaseFacts.isAntichain_A, BaseFacts.card_A⟩

/-! ### Some first values (after Corollary 5.7: `|P_j(2)| = j + 2`, `|P_1(4)| = 15`) -/

example : Fintype.card (LabelPoset 2 1) = 3 := by decide +kernel
example : Fintype.card (LabelPoset 2 2) = 4 := by decide +kernel
example : Fintype.card (LabelPoset 2 3) = 5 := by decide +kernel
example : Fintype.card (LabelPoset 2 4) = 6 := by decide +kernel
example : Fintype.card (LabelPoset 4 1) = 15 := by decide +kernel

end OnlineColouring
