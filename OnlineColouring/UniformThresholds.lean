module

public import OnlineColouring.UniformArith
public import OnlineColouring.MainTheorem
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma A.1 (thresholds), in Appendix A (Thresholds for Theorem 1.1)

With `L = lg* n`, `1 ≤ j ≤ j₀(n)` (`j₀ = L + 1` for `k = 3`, `j₀ = max(1, L - 1)` for `k ≥ 4`) and
`M = (n/2^j)^{1/(j+1)}`:

  `(2M - 1) / (4 (1 + ln 4M)) ≥ n^{1/(j+2)}`

for `n ≥ 2^406` (`k = 3`, `threshold_three`) and for `n ≥ 2^201` (`k ≥ 4`, `threshold_four`).
Both also give `M ≥ 2`, which the proof of Theorem 1.1 needs.

The proof follows the appendix, with the monotonicity argument made algebraic.
By `rpow_le_xLower_of_log` it suffices that, with `u = ln M`,

  `(2j+2) ln 2 + (j+2) ln(1 + 2 ln 2 + u) + (j+2)/(2M-1) ≤ u`.        (★)

* `lf_of_base` (monotonicity): if (★) holds at `u = a` with slack `ε ≥ (j+2)/(2M-1)` and
  `j + 2 ≤ 1 + 2 ln 2 + a` (the paper's condition `1 + ln 4M ≥ j + 2`), then it holds for every
  `u ≥ a`, since `ln` is concave (`ln x ≤ x - 1`).
* `L = 5` (`n ≤ 2^65536`, so `j ≤ 6` resp. `j ≤ 4`): `a = c ln 2` with `c (j+1) ≤ log₂ n - j`.
  For `j < j₀` the crude bound `ln(1 + (2+c) ln 2) ≤ p ln 2` with an integer `p` suffices
  (`base_of_pow`). The two tight cases are `j = 6`, `n ≥ 2^406` (`base_six`, margin about
  `0.00072` in `log₂` units) and `j = 4`, `n ≥ 2^201` (`base_four`, margin about `0.00779`); they
  use `ln 2 < 0.6931471808` and the exact rational inequalities `(8399/200)^56 · 101/100 ≤ 2^302`
  and `(297/10)^30 · 11/10 ≤ 2^147`, checked by `norm_num`.
* `L ≥ 6` (`threshold_big`): `n > tow(L-1)` gives `ln M ≥ (5j+11)^2`, and then (★) follows from
  `ln x ≤ 2√x` (`lf_big`). The paper splits this into `L = 6` (numerically) and `L ≥ 7`
  (analytically); one analytic argument covers both here.
-/

@[expose] public section

namespace OnlineColouring

open Real

/-! ### The inequality (★) -/

/-- **Monotonicity of (★) in `u = ln M`.** -/
theorem lf_of_base {j : ℕ} {M a ε : ℝ} (ha : a ≤ Real.log M)
    (hw : (j : ℝ) + 2 ≤ 1 + 2 * Real.log 2 + a)
    (hbase : (2 * j + 2) * Real.log 2 + (j + 2) * Real.log (1 + 2 * Real.log 2 + a) + ε ≤ a)
    (hε : (j + 2) / (2 * M - 1) ≤ ε) :
    (2 * j + 2) * Real.log 2 + (j + 2) * Real.log (1 + 2 * Real.log 2 + Real.log M) +
      (j + 2) / (2 * M - 1) ≤ Real.log M := by
  set u := Real.log M
  set w0 := 1 + 2 * Real.log 2 + a with hw0def
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hw0 : 0 < w0 := by linarith
  have hwu : 0 < 1 + 2 * Real.log 2 + u := by linarith
  have hlog : Real.log (1 + 2 * Real.log 2 + u) ≤ Real.log w0 + (u - a) / w0 := by
    have hpos : 0 < (1 + 2 * Real.log 2 + u) / w0 := div_pos hwu hw0
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div hwu.ne' hw0.ne'] at h1
    have h2 : (1 + 2 * Real.log 2 + u) / w0 - 1 = (u - a) / w0 := by
      field_simp
      ring
    linarith
  have hfrac : (j + 2) * ((u - a) / w0) ≤ u - a := by
    rw [mul_div_assoc', div_le_iff₀ hw0]
    have : 0 ≤ u - a := by linarith
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ j + 2)
  rw [mul_add] at h3
  linarith

/-- **(★) for large `M`**: it holds as soon as `ln M ≥ (5j+11)^2`. -/
theorem lf_big {j : ℕ} {M : ℝ} (hM : 1 ≤ M) (hu : ((5 * j + 11 : ℕ) : ℝ) ^ 2 ≤ Real.log M) :
    (2 * j + 2) * Real.log 2 + (j + 2) * Real.log (1 + 2 * Real.log 2 + Real.log M) +
      (j + 2) / (2 * M - 1) ≤ Real.log M := by
  set u := Real.log M
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hu
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  set v := Real.sqrt (u + 3) with hvdef
  have hv : v ^ 2 = u + 3 := Real.sq_sqrt (by linarith)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : (5 * j + 11 : ℝ) ≤ v := by
    have e : (5 * j + 11 : ℝ) = Real.sqrt ((5 * j + 11 : ℝ) ^ 2) :=
      (Real.sqrt_sq (by positivity)).symm
    rw [e]
    exact Real.sqrt_le_sqrt (by linarith)
  have hl2 := Real.log_two_lt_d9
  norm_num at hl2
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvpos : 0 < v := by linarith
  have hlogw : Real.log (1 + 2 * Real.log 2 + u) ≤ 2 * v := by
    calc Real.log (1 + 2 * Real.log 2 + u) ≤ Real.log (v ^ 2) :=
          Real.log_le_log (by linarith) (by rw [hv]; linarith)
      _ = 2 * Real.log v := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (v - 1) := by linarith [Real.log_le_sub_one_of_pos hvpos]
      _ ≤ 2 * v := by linarith
  have hfrac : (j + 2 : ℝ) / (2 * M - 1) ≤ j + 2 := div_le_self (by positivity) (by linarith)
  have h1 : (2 * j + 2 : ℝ) * Real.log 2 ≤ 2 * j + 2 := by nlinarith
  have h2 : (j + 2 : ℝ) * Real.log (1 + 2 * Real.log 2 + u) ≤ (j + 2) * (2 * v) :=
    mul_le_mul_of_nonneg_left hlogw (by positivity)
  have h3 : (5 * j + 11 : ℝ) * v ≤ v * v := mul_le_mul_of_nonneg_right hv1 hv0
  have h4 : 0 ≤ (3 * j + 7 : ℝ) * (v - 1) := mul_nonneg (by positivity) (by linarith)
  nlinarith

/-! ### Numerical bases (the left ends of the range `L = 5`) -/

/-- A crude base case: `ln(1 + (2+c) ln 2) ≤ p ln 2` for an integer `p`. -/
theorem base_of_pow {j p : ℕ} {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hp : 1 + (2 + c) * 0.6931471808 ≤ (2 : ℝ) ^ p)
    (h : 2 * j + 2 + (j + 2) * p + 2 * ε ≤ c) :
    (2 * j + 2) * Real.log 2 + (j + 2) * Real.log (1 + 2 * Real.log 2 + c * Real.log 2) + ε ≤
      c * Real.log 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  norm_num at hl2 hl2' hp
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hw : 0 < 1 + 2 * Real.log 2 + c * Real.log 2 := by positivity
  have hle : 1 + 2 * Real.log 2 + c * Real.log 2 ≤ (2 : ℝ) ^ p := by
    have := mul_le_mul_of_nonneg_left hl2.le (by linarith : (0 : ℝ) ≤ 2 + c)
    nlinarith
  have hlog : Real.log (1 + 2 * Real.log 2 + c * Real.log 2) ≤ p * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log hw hle
  have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ j + 2)
  have h2 := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ Real.log 2)
  have h3 : 0 ≤ ε * (2 * Real.log 2 - 1) := mul_nonneg hε (by linarith)
  nlinarith

/-- The tight case `k = 3`, `L = 5`, `j = 6`, `n ≥ 2^406` (so `ln M ≥ (400/7) ln 2`). -/
theorem base_six :
    14 * Real.log 2 + 8 * Real.log (1 + 2 * Real.log 2 + 400 / 7 * Real.log 2) + 1 / 707 ≤
      400 / 7 * Real.log 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  norm_num at hl2 hl2'
  have hpos : 0 < 1 + 2 * Real.log 2 + 400 / 7 * Real.log 2 := by linarith
  have h1 : Real.log (1 + 2 * Real.log 2 + 400 / 7 * Real.log 2) ≤ Real.log (8399 / 200) :=
    Real.log_le_log hpos (by linarith)
  have h2 : Real.log ((8399 / 200 : ℝ) ^ 56 * (101 / 100)) ≤ Real.log ((2 : ℝ) ^ 302) := by
    refine Real.log_le_log (by positivity) ?_
    rw [show (302 : ℕ) = 151 + 151 by norm_num, pow_add]
    norm_num
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow] at h2
  have h3 : (1 : ℝ) / 101 ≤ Real.log (101 / 100) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 101 / 100)
    norm_num at this ⊢
    linarith
  push_cast at h2
  linarith

/-- The tight case `k ≥ 4`, `L = 5`, `j = 4`, `n ≥ 2^201` (so `ln M ≥ (197/5) ln 2`). -/
theorem base_four :
    10 * Real.log 2 + 6 * Real.log (1 + 2 * Real.log 2 + 197 / 5 * Real.log 2) + 1 / 55 ≤
      197 / 5 * Real.log 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  norm_num at hl2 hl2'
  have hpos : 0 < 1 + 2 * Real.log 2 + 197 / 5 * Real.log 2 := by linarith
  have h1 : Real.log (1 + 2 * Real.log 2 + 197 / 5 * Real.log 2) ≤ Real.log (297 / 10) :=
    Real.log_le_log hpos (by linarith)
  have h2 : Real.log ((297 / 10 : ℝ) ^ 30 * (11 / 10)) ≤ Real.log ((2 : ℝ) ^ 147) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow] at h2
  have h3 : (1 : ℝ) / 11 ≤ Real.log (11 / 10) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    norm_num at this ⊢
    linarith
  push_cast at h2
  linarith

/-! ### The range `L = 5` -/

/-- Lemma A.1 for one fixed `j ≤ X₀`, from a base case at `n = 2^{X₀}`: if `c (j+1) ≤ X₀ - j` (so
that `ln M ≥ c ln 2`), `c ≥ 20`, `j + 2 ≤ c/2` and (★) holds at `u = c ln 2` with slack
`ε ≥ (j+2)/(2^21 - 1)`, then `M ≥ 2` and the inequality holds for all `n ≥ 2^{X₀}`. -/
theorem threshold_of_base {n j X0 : ℕ} {c ε : ℝ} (hn : 2 ^ X0 ≤ n) (hjX : j ≤ X0)
    (hc : c * (j + 1) ≤ (X0 : ℝ) - j) (hc20 : 20 ≤ c) (hcj : (j : ℝ) + 2 ≤ c / 2)
    (hε : (j + 2 : ℝ) / (2 * 2 ^ 20 - 1) ≤ ε)
    (hbase : (2 * j + 2) * Real.log 2 + (j + 2) * Real.log (1 + 2 * Real.log 2 + c * Real.log 2)
      + ε ≤ c * Real.log 2) :
    2 ≤ levelM n j ∧ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ xLower (levelM n j) := by
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hM0 := levelM_pos hn1 j
  have hpow := levelM_pow n j
  set M := levelM n j
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := Real.log_two_gt_d9
  norm_num at hl2'
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlogM : ((X0 : ℝ) - j) * Real.log 2 ≤ (j + 1) * Real.log M := by
    have h1 : (2 : ℝ) ^ (X0 - j) ≤ M ^ (j + 1) := by
      rw [hpow, le_div_iff₀ (by positivity), ← pow_add, Nat.sub_add_cancel hjX]
      exact_mod_cast hn
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_pow, Nat.cast_sub hjX] at h2
    push_cast at h2
    linarith
  have ha : c * Real.log 2 ≤ Real.log M := by
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have : c * Real.log 2 * (j + 1) ≤ Real.log M * (j + 1) := by nlinarith
    exact le_of_mul_le_mul_right this hj1
  have hM20 : (2 : ℝ) ^ 20 ≤ M := by
    rw [← Real.log_le_log_iff (by positivity) hM0, Real.log_pow]
    push_cast
    nlinarith
  have hM2 : 2 ≤ M := le_trans (by norm_num) hM20
  refine ⟨hM2, rpow_le_xLower_of_log hn1 (by linarith) ?_⟩
  apply lf_of_base (a := c * Real.log 2) (ε := ε) ha _ hbase
  · calc (j + 2 : ℝ) / (2 * M - 1) ≤ (j + 2) / (2 * 2 ^ 20 - 1) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ ε := hε
  · nlinarith

/-! ### The range `L ≥ 6` -/

theorem poly_le_tow {i : ℕ} (hi : 4 ≤ i) :
    2 * (i + 4) * (5 * i + 26) ^ 2 + 2 * i + 6 ≤ tow i := by
  induction i, hi using Nat.le_induction with
  | base => rw [tow_four]; norm_num
  | succ i hi ih =>
    rw [tow_succ]
    have h3 : 2 * (i + 1 + 4) * (5 * (i + 1) + 26) ^ 2 + 2 * (i + 1) + 6 ≤
        2 * (2 * (i + 4) * (5 * i + 26) ^ 2 + 2 * i + 6) := by
      ring_nf
      nlinarith [Nat.zero_le (i ^ 3), Nat.zero_le (i ^ 2)]
    exact h3.trans ((Nat.mul_le_mul_left 2 ih).trans (Nat.mul_le_pow (by decide) _))

/-- For `L ≥ 6` and `j ≤ L + 1`: `2 (j+1) (5j+11)^2 + 2j ≤ tow(L-2)`. -/
theorem poly_j_le_tow {L j : ℕ} (hL : 6 ≤ L) (hj : j ≤ L + 1) :
    2 * (j + 1) * (5 * j + 11) ^ 2 + 2 * j ≤ tow (L - 2) := by
  refine le_trans ?_ (poly_le_tow (i := L - 2) (by omega))
  have h1 : j + 1 ≤ L - 2 + 4 := by omega
  have h2 : 5 * j + 11 ≤ 5 * (L - 2) + 26 := by omega
  have h3 : 2 * (j + 1) * (5 * j + 11) ^ 2 ≤ 2 * (L - 2 + 4) * (5 * (L - 2) + 26) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) (Nat.pow_le_pow_left h2 2)
  omega

/-- **Lemma A.1 for `L ≥ 6`.** If `n > tow(L-1)`, `L ≥ 6` and `j ≤ L + 1`, then `M ≥ 2` and
`(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+2)}`. -/
theorem threshold_big {n j L : ℕ} (hL : 6 ≤ L) (hn : tow (L - 1) < n) (hj : j ≤ L + 1) :
    2 ≤ levelM n j ∧ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ xLower (levelM n j) := by
  have hn1 : 1 ≤ n := by omega
  have hM0 := levelM_pos hn1 j
  have hpow := levelM_pow n j
  set M := levelM n j
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := Real.log_two_gt_d9
  have hl2'' := Real.log_two_lt_d9
  norm_num at hl2' hl2''
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set T := tow (L - 2) with hTdef
  have hT : tow (L - 1) = 2 ^ T := by
    have e : L - 1 = (L - 2) + 1 := by omega
    rw [e, tow_succ]
  have hpoly := poly_j_le_tow hL hj
  have hlogn : (T : ℝ) * Real.log 2 ≤ Real.log n := by
    have h1 : (2 : ℝ) ^ T ≤ n := by exact_mod_cast (hT ▸ hn.le)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hlogM : (j + 1) * Real.log M = Real.log n - j * Real.log 2 := by
    have h1 : Real.log (M ^ (j + 1)) = Real.log ((n : ℝ) / 2 ^ j) := by rw [hpow]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [Real.log_pow, Real.log_div hn0.ne' (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hpolyR : 2 * ((j : ℝ) + 1) * (5 * j + 11) ^ 2 + 2 * j ≤ T := by exact_mod_cast hpoly
  have hu : ((5 * j + 11 : ℕ) : ℝ) ^ 2 ≤ Real.log M := by
    push_cast
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have hP : (0 : ℝ) ≤ (j + 1) * (5 * j + 11) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hpolyR hl2.le
    have h2 : 0 ≤ (2 * ((j : ℝ) + 1) * (5 * j + 11) ^ 2 + 2 * j) * (Real.log 2 - 1 / 2) :=
      mul_nonneg (by positivity) (by linarith)
    have h3 : (j : ℝ) * Real.log 2 ≤ j := by nlinarith
    have : ((j : ℝ) + 1) * (5 * j + 11) ^ 2 ≤ (j + 1) * Real.log M := by
      rw [hlogM]
      nlinarith
    exact le_of_mul_le_mul_left this hj1
  have hu1 : 1 ≤ Real.log M := le_trans (by push_cast; nlinarith) hu
  have hM2 : 2 ≤ M := by
    rw [← Real.log_le_log_iff (by norm_num) hM0]
    linarith
  exact ⟨hM2, rpow_le_xLower_of_log hn1 (by linarith) (lf_big (by linarith) hu)⟩

/-! ### Lemma A.1 -/

theorem five_le_logStar {n : ℕ} (hn : 2 ^ 201 ≤ n) : 5 ≤ logStar n := by
  by_contra h
  have h1 : n ≤ tow 4 := logStar_le_iff.1 (by omega)
  rw [tow_four] at h1
  have h2 : (65536 : ℕ) < 2 ^ 201 := by norm_num
  omega

/-- **Lemma A.1, `k = 3`.** For `n ≥ 2^406`, `L = lg* n` and `1 ≤ j ≤ L + 1`, with
`M = (n/2^j)^{1/(j+1)}`: `M ≥ 2` and `(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+2)}`. -/
theorem threshold_three {n j : ℕ} (hn : 2 ^ 406 ≤ n) (hj : 1 ≤ j) (hjL : j ≤ logStar n + 1) :
    2 ≤ levelM n j ∧ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ xLower (levelM n j) := by
  rcases le_or_gt (logStar n) 5 with hL | hL
  · have hj6 : j ≤ 6 := by omega
    interval_cases j
    · exact threshold_of_base (X0 := 406) (c := 202) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 406) (c := 134) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 406) (c := 100) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 406) (c := 80) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 406) (c := 66) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 406) (c := 400 / 7) (ε := 1 / 707) hn (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by have := base_six; push_cast; linarith)
  · exact threshold_big (L := logStar n) (by omega) (lt_tow_of_lt_logStar (by omega)) hjL

/-- **Lemma A.1, `k ≥ 4`.** For `n ≥ 2^201`, `L = lg* n` and `1 ≤ j ≤ max(1, L - 1)`, with
`M = (n/2^j)^{1/(j+1)}`: `M ≥ 2` and `(2M-1)/(4(1+ln 4M)) ≥ n^{1/(j+2)}`. -/
theorem threshold_four {n j : ℕ} (hn : 2 ^ 201 ≤ n) (hj : 1 ≤ j)
    (hjL : j ≤ max 1 (logStar n - 1)) :
    2 ≤ levelM n j ∧ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ xLower (levelM n j) := by
  have hL5 := five_le_logStar hn
  rcases le_or_gt (logStar n) 5 with hL | hL
  · have hj4 : j ≤ 4 := by omega
    interval_cases j
    · exact threshold_of_base (X0 := 201) (c := 100) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 201) (c := 66) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 201) (c := 49) (ε := 1) hn (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
        (base_of_pow (p := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact threshold_of_base (X0 := 201) (c := 197 / 5) (ε := 1 / 55) hn (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by have := base_four; push_cast; linarith)
  · exact threshold_big (L := logStar n) (by omega) (lt_tow_of_lt_logStar (by omega)) (by omega)

end OnlineColouring
