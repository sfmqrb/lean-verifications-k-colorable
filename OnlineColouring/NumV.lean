module

public import OnlineColouring.NumVDef
public import OnlineColouring.NumAlgSmall
public import OnlineColouring.NumAlg11
public import OnlineColouring.NumAdvSmall
public import OnlineColouring.NumAdv8
public import OnlineColouring.NumAdv9

/-!
# The one-level values `V(m)`, `m = 4, …, 11` (Appendix D.3, Question 10.3)

Paper, Appendix D.3: *Exhaustive game search gives the following values.*
The table that follows has `V(m) = 3, 4, 4, 5, 6, 6, 7, 7` for `m = 4, …, 11`, and the text
continues: *The upper bounds are certified for every `m` … The lower bounds are certified in the
same way for `m ≤ 9`; for `m = 10` the lower bound was obtained by two independent exhaustive
searches, and `m = 11` follows by monotonicity; the whole table is also verified in Lean.  The
values rule out the natural guess `V(m) = ⌊(2m+2)/3⌋` at `m = 11`.*  Question 10.3
quotes the same values.

The definitions (`minBlock`, `Forceable`, `V`) and the general facts are in `NumVDef.lean`;
"`V(m) = v`" is `IsGreatest (Forceable m) v`.

## What is proved

* **Upper bounds for all `m = 4, …, 11`** (`forceable_le_4`, …, `forceable_le_11`): no adversary
  of the minimal one-level game forces more than `3, 4, 4, 5, 6, 6, 7, 7` colours.  From the
  algorithm certificates (`NumAlgSmall.lean`, `NumAlg11.lean`) and `not_forces_of_surv`.
* **Lower bounds for `m = 4, …, 9`** (`mem_forceable_4`, …, `mem_forceable_9`), from adversary
  certificates and `exists_adv_of_win`: for `m ≤ 7` the certificates of the supplementary material
  (`NumAdvSmall.lean`), for `m = 8, 9` certificates with null moves (`NumAdv8.lean`,
  `NumAdv9.lean`, checker `NumGameSkip.lean`).
* **The exact values `V(4), …, V(9) = 3, 4, 4, 5, 6, 6`** (`isGreatest_4`, …, `isGreatest_9`,
  `V_table`).
* For `m = 10, 11`: `6 ≤ V(m) ≤ 7` (`V_bounds_ten_eleven`), and the two values follow from the
  single statement `7 ∈ Forceable 10`, i.e. `V(10) ≥ 7` (`isGreatest_ten_eleven_of`).  By
  `succ_mem_forceable_iff` that statement is equivalent to
  `Win 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] []` in the abstract game (`V_ten_eleven_of_win`).  That
  statement is proved in `NumV10.lean`, which completes the table; it is a separate module because
  its certificate is large (107 285 positions, about 16 MB of data and 50 minutes of kernel
  time).
* The guess `⌊(2m+2)/3⌋` is ruled out at `m = 11` (`V_eleven_ne_guess`; this needs only the upper
  bound) and agrees with the table for `m = 4, …, 9` (`V_table_guess`).
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-! ### The block sizes -/

theorem sizes_4 : sizesFrom 4 (minBlock 4) 0 = [3, 2, 1, 1] := by decide
theorem sizes_5 : sizesFrom 5 (minBlock 5) 0 = [4, 3, 2, 1, 1] := by decide
theorem sizes_6 : sizesFrom 6 (minBlock 6) 0 = [5, 4, 3, 2, 1, 1] := by decide
theorem sizes_7 : sizesFrom 7 (minBlock 7) 0 = [6, 5, 4, 3, 2, 1, 1] := by decide
theorem sizes_8 : sizesFrom 8 (minBlock 8) 0 = [7, 6, 5, 4, 3, 2, 1, 1] := by decide
theorem sizes_9 : sizesFrom 9 (minBlock 9) 0 = [8, 7, 6, 5, 4, 3, 2, 1, 1] := by decide
theorem sizes_10 : sizesFrom 10 (minBlock 10) 0 = [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] := by decide
theorem sizes_11 : sizesFrom 11 (minBlock 11) 0 = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 1] := by
  decide

/-! ### Upper bounds, `m = 4, …, 11` -/

/-- `V(4) ≤ 3`. -/
theorem forceable_le_4 {c : ℕ} (hc : c ∈ Forceable 4) : c ≤ 3 :=
  forceable_le_of_surv (by rw [sizes_4]; exact surv_4) hc

/-- `V(5) ≤ 4`. -/
theorem forceable_le_5 {c : ℕ} (hc : c ∈ Forceable 5) : c ≤ 4 :=
  forceable_le_of_surv (by rw [sizes_5]; exact surv_5) hc

/-- `V(6) ≤ 4`. -/
theorem forceable_le_6 {c : ℕ} (hc : c ∈ Forceable 6) : c ≤ 4 :=
  forceable_le_of_surv (by rw [sizes_6]; exact surv_6) hc

/-- `V(7) ≤ 5`. -/
theorem forceable_le_7 {c : ℕ} (hc : c ∈ Forceable 7) : c ≤ 5 :=
  forceable_le_of_surv (by rw [sizes_7]; exact surv_7) hc

/-- `V(8) ≤ 6`. -/
theorem forceable_le_8 {c : ℕ} (hc : c ∈ Forceable 8) : c ≤ 6 :=
  forceable_le_of_surv (by rw [sizes_8]; exact surv_8) hc

/-- `V(9) ≤ 6`. -/
theorem forceable_le_9 {c : ℕ} (hc : c ∈ Forceable 9) : c ≤ 6 :=
  forceable_le_of_surv (by rw [sizes_9]; exact surv_9) hc

/-- `V(10) ≤ 7`. -/
theorem forceable_le_10 {c : ℕ} (hc : c ∈ Forceable 10) : c ≤ 7 :=
  forceable_le_of_surv (by rw [sizes_10]; exact surv_10) hc

/-- `V(11) ≤ 7`. -/
theorem forceable_le_11 {c : ℕ} (hc : c ∈ Forceable 11) : c ≤ 7 :=
  forceable_le_of_surv (by rw [sizes_11]; exact surv_11) hc

/-! ### Lower bounds, `m = 4, …, 9` -/

/-- `V(4) ≥ 3`. -/
theorem mem_forceable_4 : 3 ∈ Forceable 4 :=
  mem_forceable_of_win (C := 2) (by rw [sizes_4]; exact win_4)

/-- `V(5) ≥ 4`. -/
theorem mem_forceable_5 : 4 ∈ Forceable 5 :=
  mem_forceable_of_win (C := 3) (by rw [sizes_5]; exact win_5)

/-- `V(6) ≥ 4`. -/
theorem mem_forceable_6 : 4 ∈ Forceable 6 :=
  mem_forceable_of_win (C := 3) (by rw [sizes_6]; exact win_6)

/-- `V(7) ≥ 5`. -/
theorem mem_forceable_7 : 5 ∈ Forceable 7 :=
  mem_forceable_of_win (C := 4) (by rw [sizes_7]; exact win_7)

/-- `V(8) ≥ 6`. -/
theorem mem_forceable_8 : 6 ∈ Forceable 8 :=
  mem_forceable_of_win (C := 5) (by rw [sizes_8]; exact win_8)

/-- `V(9) ≥ 6`. -/
theorem mem_forceable_9 : 6 ∈ Forceable 9 :=
  mem_forceable_of_win (C := 5) (by rw [sizes_9]; exact win_9)

/-! ### Exact values, `m = 4, …, 9` -/

/-- **`V(4) = 3`.** -/
theorem isGreatest_4 : IsGreatest (Forceable 4) 3 := ⟨mem_forceable_4, fun _ => forceable_le_4⟩

/-- **`V(5) = 4`.** -/
theorem isGreatest_5 : IsGreatest (Forceable 5) 4 := ⟨mem_forceable_5, fun _ => forceable_le_5⟩

/-- **`V(6) = 4`.** -/
theorem isGreatest_6 : IsGreatest (Forceable 6) 4 := ⟨mem_forceable_6, fun _ => forceable_le_6⟩

/-- **`V(7) = 5`.** -/
theorem isGreatest_7 : IsGreatest (Forceable 7) 5 := ⟨mem_forceable_7, fun _ => forceable_le_7⟩

/-- **`V(8) = 6`.** -/
theorem isGreatest_8 : IsGreatest (Forceable 8) 6 := ⟨mem_forceable_8, fun _ => forceable_le_8⟩

/-- **`V(9) = 6`.** -/
theorem isGreatest_9 : IsGreatest (Forceable 9) 6 := ⟨mem_forceable_9, fun _ => forceable_le_9⟩

/-- **Appendix D.3, the table of `V(m)`, `m = 4, …, 9`:** `3, 4, 4, 5, 6, 6`. -/
theorem V_table : V 4 = 3 ∧ V 5 = 4 ∧ V 6 = 4 ∧ V 7 = 5 ∧ V 8 = 6 ∧ V 9 = 6 :=
  ⟨V_eq isGreatest_4, V_eq isGreatest_5, V_eq isGreatest_6, V_eq isGreatest_7, V_eq isGreatest_8,
    V_eq isGreatest_9⟩

/-! ### `m = 10` and `m = 11` -/

/-- For `m = 10, 11`: the upper bound `7` of the table, and the lower bound `6` (from Theorem D.2,
or from `V(9) = 6` and monotonicity). -/
theorem V_bounds_ten_eleven : (6 ≤ V 10 ∧ V 10 ≤ 7) ∧ (6 ≤ V 11 ∧ V 11 ≤ 7) :=
  ⟨⟨half_le_V (m := 10) (by decide), V_le fun _ => forceable_le_10⟩,
    ⟨half_le_V (m := 11) (by decide), V_le fun _ => forceable_le_11⟩⟩

/-- The values `V(10) = 7` and `V(11) = 7` of the table follow from the single statement
`V(10) ≥ 7`, by the upper bounds and monotonicity. -/
theorem isGreatest_ten_eleven_of (h : 7 ∈ Forceable 10) :
    IsGreatest (Forceable 10) 7 ∧ IsGreatest (Forceable 11) 7 :=
  ⟨⟨h, fun _ => forceable_le_10⟩, ⟨forceable_subset_succ 10 h, fun _ => forceable_le_11⟩⟩

/-- The same in terms of the abstract game: a winning strategy of the adversary against six
colours for `m = 10` gives the last two columns of the table. -/
theorem V_ten_eleven_of_win (h : Win 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] []) :
    V 10 = 7 ∧ V 11 = 7 := by
  have h7 : 7 ∈ Forceable 10 := mem_forceable_of_win (C := 6) (by rw [sizes_10]; exact h)
  exact ⟨V_eq (isGreatest_ten_eleven_of h7).1, V_eq (isGreatest_ten_eleven_of h7).2⟩

/-- **"The values rule out the natural guess `V(m) = ⌊(2m+2)/3⌋` at `m = 11`."**  (Only the upper
bound `V(11) ≤ 7` is needed: the guess would be `8`.) -/
theorem V_eleven_ne_guess : V 11 ≠ (2 * 11 + 2) / 3 := by
  have := V_bounds_ten_eleven.2.2
  omega

/-- For `m = 4, …, 9` the guess `⌊(2m+2)/3⌋` agrees with `V(m)`. -/
theorem V_table_guess :
    V 4 = (2 * 4 + 2) / 3 ∧ V 5 = (2 * 5 + 2) / 3 ∧ V 6 = (2 * 6 + 2) / 3 ∧
      V 7 = (2 * 7 + 2) / 3 ∧ V 8 = (2 * 8 + 2) / 3 ∧ V 9 = (2 * 9 + 2) / 3 := by
  obtain ⟨h4, h5, h6, h7, h8, h9⟩ := V_table
  rw [h4, h5, h6, h7, h8, h9]
  decide

end Num

end OnlineColouring
