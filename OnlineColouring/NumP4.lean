module

public import OnlineColouring.NumPoset
public import OnlineColouring.BaseFacts

/-!
# The label posets `P_j(4)`: `|P_2(4)| = 166` and `width(P_1(4)) = 6`

Paper: Section 5: "The first values are … `|P_j(4)| = 4, 15, 166`";
Section 9: "`width(P_1(4)) = binom(4, 2) = 6`".

* `card_labelPoset_four_two : |P_2(4)| = 166` (`P_1(4)` has 167 down-sets: kernel evaluation of
  `cntL`, the list form of the verified count `cnt` of `NumPoset.lean`).
* `width_labelPoset_four_one : width(P_1(4)) = 6`.

The lists are generated data, checked by the kernel with the Bool checks of `NumPoset.lean`.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-! ### Data (generated) -/

/-- The elements of `P_1(4)`: the bit masks of the nonempty subsets of `{0, 1, 2, 3}`. -/
def L41 : List ℕ := [
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The order of `P_1(4)`: bit `i` of row `j` says whether element `i` lies below
element `j`. -/
def R41 : List ℕ := [
  1, 2, 7, 8, 25, 42, 127, 128, 385, 642, 1927, 2184, 6553, 10922, 32767]

/-- A cover of `P_1(4)` by 6 chains: the chain of each element. -/
def C41 : List ℕ := [
  0, 1, 0, 2, 2, 1, 0, 3, 3, 4, 3, 5, 2, 1, 0]

/-- An antichain of `P_1(4)` with 6 elements (the 2-element subsets). -/
def A41 : List ℕ := [
  2, 4, 5, 8, 9, 11]

/-- The numbering of `P_1(4)`. -/
def idx41 : LabelPoset 4 1 → ℕ := jstIdx (idxAnti 4) 4 L41

theorem coding41 : IsCoding (LabelPoset 4 1) 15 (fun j => R41.getD j 0) idx41 :=
  (isCoding_labelPoset_zero 4).jst (L := L41) (rows := R41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `|P_2(4)| = 166`. -/
theorem card_labelPoset_four_two : Fintype.card (LabelPoset 4 2) = 166 :=
  coding41.card_jst (cnt_eq_of_cntL rfl (by decide +kernel))

/-- `width(P_1(4)) = 6`. -/
theorem width_labelPoset_four_one : width (LabelPoset 4 1) = 6 :=
  le_antisymm (coding41.width_le (ch := C41) rfl (by decide +kernel))
    (le_width_iff.2 (coding41.hasAntichain (a := A41) (by decide +kernel)))

end Num

end OnlineColouring
