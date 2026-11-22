module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Theorem D.5 (partial joins): the summation

End of the proof of Theorem D.5 (Appendix D.4): *Summing
`|B_i| ≥ (m-i)((m-i)/(2 log₂ N + 1) - 1) + 1` over `i` gives the bound.*

`pj_arith`: let `m ≥ 1` and `N ≥ 1`.  If the block sizes `b i` (`i < m`, blocks numbered from `0`)
sum to at most `N`, and for every block `i` other than the last there is a reserve size `r` with
`(m-1-i)(r-1)+1 ≤ b i` (round robin) and `m-1-i ≤ r (2 ⌊log₂ N⌋ + 1)` (the hub strategy), then
`N ≥ m³ / (3 (2 log₂ N + 1)) - m²`.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

theorem sum_succ_sq_real (n : ℕ) :
    ∑ d ∈ range n, ((d : ℝ) + 1) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem sum_id_real (n : ℕ) : ∑ d ∈ range n, (d : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The summation at the end of the proof of Theorem D.5. -/
theorem pj_arith {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (b : ℕ → ℕ)
    (hsum : ∑ i ∈ range m, b i ≤ N)
    (h : ∀ i, i + 1 < m → ∃ r : ℕ, (m - 1 - i) * (r - 1) + 1 ≤ b i ∧
      m - 1 - i ≤ r * (2 * Nat.log 2 N + 1)) :
    (m : ℝ) ^ 3 / (3 * (2 * Real.logb 2 N + 1)) - (m : ℝ) ^ 2 ≤ N := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlog : (0 : ℝ) ≤ Real.logb 2 N :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hN)
  set Lr : ℝ := 2 * Real.logb 2 N + 1 with hLr
  have hLr1 : 1 ≤ Lr := by linarith
  have hLint : ((2 * Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Lr := by
    have h0 : (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := by
      have := Real.natLog_le_logb N 2
      simpa using this
    push_cast
    linarith
  set x : ℝ := 1 / Lr with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by linarith)]
    exact hLr1
  have key : ∀ i ∈ range n,
      (((n - 1 - i : ℕ) : ℝ) + 1) ^ 2 * x - ((n - 1 - i : ℕ) : ℝ) ≤ b i := by
    intro i hi
    rw [mem_range] at hi
    obtain ⟨r, hr1, hr2⟩ := h i (by omega)
    have hd : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
    rw [hd] at hr1 hr2
    set d : ℕ := n - 1 - i with hdd
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · simp at hr2
      · exact hpos
    have h1 : (((d + 1) * (r - 1) + 1 : ℕ) : ℝ) ≤ b i := by exact_mod_cast hr1
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr] at h1
    push_cast at h1
    have h2 : ((d + 1 : ℕ) : ℝ) ≤ (r : ℝ) * ((2 * Nat.log 2 N + 1 : ℕ) : ℝ) := by
      exact_mod_cast hr2
    have h3 : ((d : ℝ) + 1) ≤ r * Lr := by
      push_cast at h2
      have : (r : ℝ) * (2 * (Nat.log 2 N : ℝ) + 1) ≤ r * Lr :=
        mul_le_mul_of_nonneg_left (by push_cast at hLint; linarith) (by positivity)
      linarith
    have h4 : ((d : ℝ) + 1) * x ≤ r := by
      rw [hx, mul_one_div, div_le_iff₀ (by linarith)]
      exact h3
    have hd0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 hd0]
  have hsum1 := sum_le_sum key
  have hsum2 : ∑ i ∈ range n, (b i : ℝ) ≤ N := by
    have : ∑ i ∈ range n, b i ≤ ∑ i ∈ range (n + 1), b i :=
      sum_le_sum_of_subset (range_mono (Nat.le_succ n))
    exact_mod_cast this.trans hsum
  have hrefl : ∑ i ∈ range n, ((((n - 1 - i : ℕ) : ℝ) + 1) ^ 2 * x - ((n - 1 - i : ℕ) : ℝ))
      = ∑ j ∈ range n, (((j : ℝ) + 1) ^ 2 * x - (j : ℝ)) :=
    sum_range_reflect (fun j => ((j : ℝ) + 1) ^ 2 * x - (j : ℝ)) n
  rw [hrefl, sum_sub_distrib, ← sum_mul, sum_succ_sq_real, sum_id_real] at hsum1
  have e : ((n + 1 : ℕ) : ℝ) ^ 3 / (3 * Lr) = ((n : ℝ) + 1) ^ 3 * x / 3 := by
    rw [hx]
    push_cast
    field_simp
  rw [e]
  push_cast
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hx1 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * (3 * n + 2)),
    hsum1, hsum2]

end OnlineColouring.AppBD
