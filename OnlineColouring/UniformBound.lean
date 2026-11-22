module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The bound `X_m` of Theorem 8.5 and the bound of Corollary 8.6

* `uniformBound m = (2m+1) / (4 (1 + ln 4m))` is `X_m` of Theorem 8.5.  The threshold for heavy
  colours in its proof is `b = ln 4m`: `one_le_log_four_mul` (`b ≥ 1` for `m ≥ 2`) and
  `mul_exp_neg_log` (`m e^{-b} = 1/4`).
* `epsBound m ε = (2m+1) / (4 (1 + ln(4m/ε)))` is the bound of Corollary 8.6, whose proof uses
  the threshold `b = ln(4m/ε)`: `one_le_log_four_mul_div` (`b ≥ 1` for `m ≥ 2`, `0 < ε < 1`) and
  `mul_exp_neg_log_div` (`m e^{-b} = ε/4`).
-/

@[expose] public section

namespace OnlineColouring

/-- The bound of Theorem 8.5: `(2m+1) / (4 (1 + ln(4m)))`. -/
noncomputable def uniformBound (m : ℕ) : ℝ := (2 * m + 1) / (4 * (1 + Real.log (4 * m)))

theorem one_le_log_four_mul {m : ℕ} (hm : 2 ≤ m) : 1 ≤ Real.log (4 * m) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_three
  have h2 : (8 : ℝ) ≤ 4 * m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  linarith

theorem mul_exp_neg_log {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) * Real.exp (-Real.log (4 * m)) = 1 / 4 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- The bound of the corollary: `(2m+1)/(4(1+ln(4m/ε)))`. -/
noncomputable def epsBound (m : ℕ) (ε : ℝ) : ℝ := (2 * m + 1) / (4 * (1 + Real.log (4 * m / ε)))

/-- The threshold `ln(4m/ε)` is at least `1`. -/
theorem one_le_log_four_mul_div {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 ≤ Real.log (4 * m / ε) := by
  have h4m : (8 : ℝ) ≤ 4 * m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hge : (4 * m : ℝ) ≤ 4 * m / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith
  exact (one_le_log_four_mul hm).trans (Real.log_le_log (by linarith) hge)

/-- `m e^{-ln(4m/ε)} = ε/4`. -/
theorem mul_exp_neg_log_div {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε0 : 0 < ε) :
    (m : ℝ) * Real.exp (-Real.log (4 * m / ε)) = ε / 4 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  field_simp

end OnlineColouring
