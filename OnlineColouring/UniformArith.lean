module

public import OnlineColouring.UniformBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arithmetic of the proof of Theorem 1.1

The real-number part of the proof of Theorem 1.1 (Section 8.4, "Putting things together").
For `n ≥ 1` and `j` we put `M = (n / 2^j)^{1/(j+1)}` (`levelM n j`) and `m = ⌊M⌋`.

* `two_pow_mul_levelM_pow`: `2^j M^{j+1} = n`; `levelM_le`: `M ≤ n`;
  `rpow_le_two_mul_levelM`: `n^{1/(j+1)} ≤ 2M` (the paper's `2^{j/(j+1)} ≤ 2`).
* `xLower_le_uniformBound`: if `M ≥ 2`, then `X_m ≥ (2M-1)/(4(1+ln 4M))`, the first step of
  (8.2) (`xLower M` is that expression; `X_m = uniformBound m` is defined in
  `UniformBound.lean`).
* `rpow_div_le_xLower`: the rest of (8.2), `(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+1)}/(8(1+ln 4n))`.
* `rpow_div_le_epsBound`: the chain (8.2) for Corollary 8.6, with `ln(4m/ε) ≤ ln(4n/ε)` in place
  of `ln 4m ≤ ln 4n`: `(2m+1)/(4(1+ln(4m/ε))) ≥ n^{1/(j+1)}/(8(1+ln(4n/ε)))`.
* `rpow_le_xLower_of_log`: a sufficient condition, in logarithms, for
  `(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+2)}` (inequality (A.1) of Lemma A.1).
-/

@[expose] public section

namespace OnlineColouring

open Real

/-- `M = (n / 2^j)^{1/(j+1)}`, as in the proof of Theorem 1.1. -/
noncomputable def levelM (n j : ℕ) : ℝ := ((n : ℝ) / 2 ^ j) ^ ((1 : ℝ) / ((j : ℝ) + 1))

/-- The second expression of (8.2) (the first lower bound for `X_m`):
`(2M - 1) / (4 (1 + ln 4M))`. -/
noncomputable def xLower (M : ℝ) : ℝ := (2 * M - 1) / (4 * (1 + Real.log (4 * M)))

/-- `x ≤ y^d` implies `x^{1/d} ≤ y`. -/
theorem rpow_one_div_le_of_le_pow {x y : ℝ} {d : ℕ} (hd : d ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ y ^ d) : x ^ ((1 : ℝ) / d) ≤ y := by
  calc x ^ ((1 : ℝ) / d) ≤ (y ^ d) ^ ((1 : ℝ) / d) := Real.rpow_le_rpow hx h (by positivity)
    _ = y := by rw [one_div]; exact Real.pow_rpow_inv_natCast hy hd

theorem levelM_pos {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : 0 < levelM n j := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_pos_of_pos (by positivity) _

theorem levelM_pow (n j : ℕ) : levelM n j ^ (j + 1) = (n : ℝ) / 2 ^ j := by
  have e : (1 : ℝ) / ((j : ℝ) + 1) = (((j + 1 : ℕ) : ℝ))⁻¹ := by push_cast; rw [one_div]
  rw [levelM, e]
  exact Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero j)

/-- `2^j M^{j+1} = n`. -/
theorem two_pow_mul_levelM_pow (n j : ℕ) : 2 ^ j * levelM n j ^ (j + 1) = n := by
  rw [levelM_pow]
  field_simp

/-- `M ≤ n`. -/
theorem levelM_le {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : levelM n j ≤ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply le_of_pow_le_pow_left₀ (Nat.succ_ne_zero j) (by linarith)
  rw [levelM_pow]
  calc (n : ℝ) / 2 ^ j ≤ n := div_le_self (by linarith) (one_le_pow₀ (by norm_num))
    _ = (n : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (n : ℝ) ^ (j + 1) := pow_le_pow_right₀ hn' (by omega)

/-- `n^{1/(j+1)} ≤ 2M`, since `(2M)^{j+1} = 2n`. -/
theorem rpow_le_two_mul_levelM {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) ≤ 2 * levelM n j := by
  have hM := levelM_pos hn j
  have e : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  apply rpow_one_div_le_of_le_pow (Nat.succ_ne_zero j) (Nat.cast_nonneg _) (by positivity)
  have h := two_pow_mul_levelM_pow n j
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) ≤ 2 * n := by linarith
    _ = (2 * levelM n j) ^ (j + 1) := by rw [← h, mul_pow, pow_succ]; ring

/-- The first step of (8.2): for `M ≥ 2` and `m = ⌊M⌋`, `X_m ≥ (2M-1)/(4(1+ln 4M))`. -/
theorem xLower_le_uniformBound {M : ℝ} (hM : 2 ≤ M) : xLower M ≤ uniformBound ⌊M⌋₊ := by
  have hm1 : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hm2 : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  have hm0 : (2 : ℝ) ≤ (⌊M⌋₊ : ℝ) := by
    have : 2 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast hM)
    exact_mod_cast this
  have hlog1 : Real.log (4 * (⌊M⌋₊ : ℝ)) ≤ Real.log (4 * M) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogpos : 0 < Real.log (4 * (⌊M⌋₊ : ℝ)) := Real.log_pos (by linarith)
  unfold xLower uniformBound
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The rest of (8.2): `(2M-1)/(4(1+ln 4M)) ≥ M/(4(1+ln 4n)) ≥ n^{1/(j+1)}/(8(1+ln 4n))`. -/
theorem rpow_div_le_xLower {n j : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ levelM n j) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ≤
      xLower (levelM n j) := by
  have h1 := rpow_le_two_mul_levelM hn j
  have h2 := levelM_le hn j
  set M := levelM n j
  have hlog : Real.log (4 * M) ≤ Real.log (4 * n) := Real.log_le_log (by positivity) (by linarith)
  have hlogM : 0 < Real.log (4 * M) := Real.log_pos (by linarith)
  unfold xLower
  calc (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n)))
      ≤ (2 * M) / (8 * (1 + Real.log (4 * n))) :=
        div_le_div_of_nonneg_right h1 (by linarith)
    _ = M / (4 * (1 + Real.log (4 * n))) := by
        have : 0 < 1 + Real.log (4 * (n : ℝ)) := by linarith
        field_simp
        ring
    _ ≤ (2 * M - 1) / (4 * (1 + Real.log (4 * M))) :=
        div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- The arithmetic: if `M = (n/2^j)^{1/(j+1)} ≥ 2` and `m = ⌊M⌋`, then
`(2m+1)/(4(1+ln(4m/ε))) ≥ M/(4(1+ln(4n/ε))) ≥ n^{1/(j+1)}/(8(1+ln(4n/ε)))`. -/
theorem rpow_div_le_epsBound {n j : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ levelM n j) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n / ε))) ≤
      epsBound ⌊levelM n j⌋₊ ε := by
  have h1 := rpow_le_two_mul_levelM hn j
  have h2 := levelM_le hn j
  set M := levelM n j
  have hm1 : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hm2 : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  have hm2' : 2 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast hM)
  have hm0 : (2 : ℝ) ≤ (⌊M⌋₊ : ℝ) := by exact_mod_cast hm2'
  have hlog : Real.log (4 * (⌊M⌋₊ : ℝ) / ε) ≤ Real.log (4 * n / ε) :=
    Real.log_le_log (div_pos (by linarith) hε0)
      (div_le_div_of_nonneg_right (by linarith) hε0.le)
  have hlogm : 1 ≤ Real.log (4 * (⌊M⌋₊ : ℝ) / ε) := one_le_log_four_mul_div hm2' hε0 hε1
  unfold epsBound
  calc (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n / ε)))
      ≤ (2 * M) / (8 * (1 + Real.log (4 * n / ε))) :=
        div_le_div_of_nonneg_right h1 (by linarith)
    _ = M / (4 * (1 + Real.log (4 * n / ε))) := by
        have : 0 < 1 + Real.log (4 * (n : ℝ) / ε) := by linarith
        field_simp
        ring
    _ ≤ (2 * (⌊M⌋₊ : ℝ) + 1) / (4 * (1 + Real.log (4 * (⌊M⌋₊ : ℝ) / ε))) :=
        div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- **The condition behind Lemma A.1, in logarithms.** With `u = ln M`, if
`(2j+2) ln 2 + (j+2) ln(1 + 2 ln 2 + u) + (j+2)/(2M-1) ≤ u`, then
`(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+2)}`.  (Raise both sides to the power `j+2`, use
`n = 2^j M^{j+1}` and `ln(2M-1) ≥ ln 2M - 1/(2M-1)`.) -/
theorem rpow_le_xLower_of_log {n j : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ levelM n j)
    (h : (2 * j + 2) * Real.log 2 +
        (j + 2) * Real.log (1 + 2 * Real.log 2 + Real.log (levelM n j)) +
        (j + 2) / (2 * levelM n j - 1) ≤ Real.log (levelM n j)) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ xLower (levelM n j) := by
  have hnM := two_pow_mul_levelM_pow n j
  set M := levelM n j
  set u := Real.log M with hu
  have hM0 : 0 < M := by linarith
  have hu0 : 0 ≤ u := Real.log_nonneg hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw : 0 < 1 + 2 * Real.log 2 + u := by linarith
  have hlog4M : Real.log (4 * M) = 2 * Real.log 2 + u := by
    rw [Real.log_mul (by norm_num) hM0.ne', log_four]
  have h2M : 0 < 2 * M - 1 := by linarith
  have hY : 0 < xLower M := by
    unfold xLower
    rw [hlog4M]
    apply div_pos h2M
    linarith
  have e : ((j : ℝ) + 2) = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  apply rpow_one_div_le_of_le_pow (by omega) (Nat.cast_nonneg _) hY.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_le_log_iff hn0 (pow_pos hY _), Real.log_pow]
  have hlogn : Real.log n = j * Real.log 2 + (j + 1) * u := by
    rw [← hnM, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogY : Real.log (xLower M) =
      Real.log (2 * M - 1) - 2 * Real.log 2 - Real.log (1 + 2 * Real.log 2 + u) := by
    unfold xLower
    rw [hlog4M, Real.log_div h2M.ne' (by positivity), Real.log_mul (by norm_num) (by linarith),
      log_four]
    ring_nf
  -- `ln(2M-1) ≥ ln 2 + ln M - 1/(2M-1)`
  have hlog2M : Real.log 2 + u - 1 / (2 * M - 1) ≤ Real.log (2 * M - 1) := by
    have hx : 0 < (2 * M - 1) / (2 * M) := by positivity
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div h2M.ne' (by positivity), Real.log_mul (by norm_num) hM0.ne', inv_div] at h1
    have h3 : 1 - 2 * M / (2 * M - 1) = -(1 / (2 * M - 1)) := by
      field_simp
      ring
    rw [h3] at h1
    linarith
  rw [hlogn, hlogY]
  push_cast
  have hj2 : (0 : ℝ) ≤ j + 2 := by positivity
  have key := mul_le_mul_of_nonneg_left hlog2M hj2
  have e2 : ((j : ℝ) + 2) * (1 / (2 * M - 1)) = (j + 2) / (2 * M - 1) := by ring
  nlinarith [key, h, e2]

end OnlineColouring
