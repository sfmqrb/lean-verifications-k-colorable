module

public import OnlineColouring.NumTwo
public import OnlineColouring.NumP3
public import OnlineColouring.NumP4

/-!
# The first values of `|P_j(k)|` and the widths of `P_j(3)`

Paper, Section 5, after Corollary 5.7 (number of levels): *"The first
values are `|P_j(2)| = j + 2`, `|P_j(3)| = 3, 7, 18, 81, 8569` and `|P_j(4)| = 4, 15, 166` for
`j = 0, 1, 2, …`.  For `k = 2` the width stays `2` …"*  This file collects the sizes in one
statement (`first_values`) and the widths `3, 3, 4, 7` of `P_j(3)` for `j = 0, …, 3`
(`widths_three`; the paper says, before Lemma 5.5, "For `k = 3` the width is `3` after one level
and `4` after two", and the script `check_posets.py` of the supplementary material computes all
four).  The widths `width(P_j(2)) = 2` for all `j` and `width(P_1(4)) = 6`, which the paper
quotes in Section 9 after the proof of Theorem 1.4, are `width_labelPoset_two` (`NumTwo.lean`)
and `width_labelPoset_four_one` (`NumP4.lean`).

The proofs are in `NumTwo.lean` (`k = 2`, all `j`), `NumP3.lean`, `NumP4.lean` (kernel
computations with the verified down-set counter of `NumPoset.lean`), and `Towers.lean`,
`BaseFacts.lean` (the values `3, 7, 18` and `4`).
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-- **Section 5, the first values (after Corollary 5.7).**  `|P_j(2)| = j + 2` for all `j`;
`|P_j(3)| = 3, 7, 18, 81, 8569` for `j = 0, …, 4`; `|P_j(4)| = 4, 15, 166` for `j = 0, 1, 2`. -/
theorem first_values :
    (∀ j, Fintype.card (LabelPoset 2 j) = j + 2) ∧
    (Fintype.card (LabelPoset 3 0) = 3 ∧ Fintype.card (LabelPoset 3 1) = 7 ∧
      Fintype.card (LabelPoset 3 2) = 18 ∧ Fintype.card (LabelPoset 3 3) = 81 ∧
      Fintype.card (LabelPoset 3 4) = 8569) ∧
    (Fintype.card (LabelPoset 4 0) = 4 ∧ Fintype.card (LabelPoset 4 1) = 15 ∧
      Fintype.card (LabelPoset 4 2) = 166) :=
  ⟨card_labelPoset_two,
    ⟨card_labelPoset_zero 3, card_labelPoset_three_one, card_labelPoset_three_two,
      card_labelPoset_three_three, card_labelPoset_three_four⟩,
    ⟨card_labelPoset_zero 4, coding41.card_eq, card_labelPoset_four_two⟩⟩

/-- **The widths of `P_j(3)`, `j = 0, …, 3`, are `3, 3, 4, 7`.** -/
theorem widths_three :
    width (LabelPoset 3 0) = 3 ∧ width (LabelPoset 3 1) = 3 ∧ width (LabelPoset 3 2) = 4 ∧
      width (LabelPoset 3 3) = 7 :=
  ⟨width_labelPoset_three_zero, width_labelPoset_three_one, width_labelPoset_three_two,
    width_labelPoset_three_three⟩

/-- `width(P_0(k)) = k`. -/
theorem width_labelPoset_zero (k : ℕ) : width (LabelPoset k 0) = k :=
  le_antisymm (width_le_card.trans_eq (card_labelPoset_zero k))
    (le_width_iff.2 (hasAntichain_labelPoset_zero k))

end Num

end OnlineColouring
