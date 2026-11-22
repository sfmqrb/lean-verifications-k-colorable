module

public import OnlineColouring.NumV
public import OnlineColouring.NumAdv10

/-!
# The one-level values `V(10) = 7` and `V(11) = 7`: the table of Appendix D.3, complete

Paper, Appendix D.3: the table has `V(m) = 3, 4, 4, 5, 6, 6, 7, 7` for
`m = 4, …, 11`, and the text says: *for `m = 10` the lower bound was obtained by two independent
exhaustive searches, and `m = 11` follows by monotonicity; the whole table is also verified in
Lean.*

`NumV.lean` proves the table for `m ≤ 9`, the upper bounds for `m = 10, 11`, and reduces the last
two columns to `V(10) ≥ 7`.  This file proves `V(10) ≥ 7` (`mem_forceable_10`) from the adversary
certificate with null moves of `NumAdv10.lean` (107 285 positions, kernel-checked with the verified
checker of `NumGameSkip.lean`) and concludes

* `isGreatest_10 : IsGreatest (Forceable 10) 7` and `isGreatest_11 : IsGreatest (Forceable 11) 7`
  (the latter by monotonicity, `forceable_subset_succ`);
* `V_table_full`: **`V(4), …, V(11) = 3, 4, 4, 5, 6, 6, 7, 7`**, the whole table.

The supplementary material has no certificate for `V(10) ≥ 7`; the certificate used here was
written by a variant of its solver (see `docs/num_generators.md`).
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-- `V(10) ≥ 7`. -/
theorem mem_forceable_10 : 7 ∈ Forceable 10 :=
  mem_forceable_of_win (C := 6) (by rw [sizes_10]; exact win_10)

/-- **`V(10) = 7`.** -/
theorem isGreatest_10 : IsGreatest (Forceable 10) 7 :=
  ⟨mem_forceable_10, fun _ => forceable_le_10⟩

/-- `V(11) ≥ 7`, by monotonicity. -/
theorem mem_forceable_11 : 7 ∈ Forceable 11 := forceable_subset_succ 10 mem_forceable_10

/-- **`V(11) = 7`.** -/
theorem isGreatest_11 : IsGreatest (Forceable 11) 7 :=
  ⟨mem_forceable_11, fun _ => forceable_le_11⟩

/-- **Appendix D.3, the table of `V(m)`:** `V(m) = 3, 4, 4, 5, 6, 6, 7, 7` for
`m = 4, …, 11`. -/
theorem V_table_full :
    V 4 = 3 ∧ V 5 = 4 ∧ V 6 = 4 ∧ V 7 = 5 ∧ V 8 = 6 ∧ V 9 = 6 ∧ V 10 = 7 ∧ V 11 = 7 :=
  ⟨V_table.1, V_table.2.1, V_table.2.2.1, V_table.2.2.2.1, V_table.2.2.2.2.1, V_table.2.2.2.2.2,
    V_eq isGreatest_10, V_eq isGreatest_11⟩

end Num

end OnlineColouring
