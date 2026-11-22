module

public import OnlineColouring.CertNumbers
public import OnlineColouring.UniformBound

/-!
# Section 8.4: where the uniform towers overtake the explicit construction

Section 8.4, after the proof of Theorem 1.1: *At small sizes the explicit adversary of
Theorem 6.4 is better; for `3`-colourable graphs the bound of Theorem 8.5 overtakes it at `j = 4`
with `m` of about `600`, that is, for `n` of about `2^50` (about `2^54` against the smaller
instances of Appendix B).*

The sentence is approximate.  The exact facts behind it, as computed by
`repro/check_sizes.py`, are formalized here for the towers with `j = 4` levels
(`uniformBound m = (2m+1)/(4(1 + ln 4m))` is `X_m` of Theorem 8.5, `UniformBound.lean`; a uniform
tower with parameters `m`, `j` has `m (2m)^j` vertices):

* `overtake_two_pow_50`: with `n = 2^50` vertices the adversary of Theorem 6.4 (three levels)
  forces `33` colours and not `34` (`playSize 33 3 ≤ 2^50 < playSize 34 3`), while `m = 588`,
  `j = 4` fits into `2^50` vertices and `X_588 > 33`, so Theorem 8.5 (ii) forces `34` colours.
* `not_yet_two_pow_49`: with `n = 2^49` the adversary of Theorem 6.4 forces `31` colours,
  while the largest `m` with `m (2m)^4 ≤ 2^49` is `512` and `X_512 ≤ 30`.
* `overtake_two_pow_54`, `not_yet_two_pow_53`: the same against the instances of
  Proposition B.1 (`54` against `55` colours at `2^54`; `51` against `49` at `2^53`).

Not formalized: that no other number of levels `j ≠ 4` (and no smaller `m`) does better for the
uniform towers at `2^49` and `2^53`, and that the least `j` with `|P_j(3)| ≥ K` equals `3` for
`19 ≤ K ≤ 81` (it follows from the values `|P_j(3)| = 3, 7, 18, 81` for `j ≤ 3`,
`Num.first_values`).  The script tries the levels `j = 1, …, 4`, with the values `|P_j(3)|`
written into it.  For `j ≥ 5` the uniform towers do worse: `m (2m)^j ≤ 2^53` forces `m ≤ 256`,
and `X_256 < 17`.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

theorem log_2352_lt : Real.log 2352 < 7.77 := by
  have h : (2352 : ℝ) ^ 5 < 2 ^ 56 := by norm_num
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  have := Real.log_two_lt_d9
  norm_num at h'
  linarith

theorem log_3564_gt : 8.1 < Real.log 3564 := by
  have h : (2 : ℝ) ^ 117 < 3564 ^ 10 := by norm_num
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  have := Real.log_two_gt_d9
  norm_num at h'
  linarith

theorem log_two_pow (a : ℕ) : Real.log ((2 : ℝ) ^ a) = a * Real.log 2 := Real.log_pow _ _

/-- At `n = 2^50` the uniform tower with `j = 4` and `m = 588` forces `34` colours, one more
than the adversary of Theorem 6.4. -/
theorem overtake_two_pow_50 :
    playSize 33 3 ≤ 2 ^ 50 ∧ 2 ^ 50 < playSize 34 3 ∧ 588 * (2 * 588) ^ 4 ≤ 2 ^ 50 ∧
      33 < uniformBound 588 := by
  refine ⟨by decide +kernel, by decide +kernel, by norm_num, ?_⟩
  have h := log_2352_lt
  rw [uniformBound, lt_div_iff₀ (by norm_num; linarith [Real.log_nonneg (by norm_num :
    (1 : ℝ) ≤ 2352)])]
  norm_num
  linarith

/-- At `n = 2^49` the adversary of Theorem 6.4 forces `31` colours; the largest uniform tower
with `j = 4` has `m = 512`, and `X_512 ≤ 30`. -/
theorem not_yet_two_pow_49 :
    playSize 31 3 ≤ 2 ^ 49 ∧ 512 * (2 * 512) ^ 4 ≤ 2 ^ 49 ∧ 2 ^ 49 < 513 * (2 * 513) ^ 4 ∧
      uniformBound 512 ≤ 30 := by
  refine ⟨by decide +kernel, by norm_num, by norm_num, ?_⟩
  have h2 := Real.log_two_gt_d9
  have h : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, log_two_pow]
    norm_num
  rw [uniformBound, div_le_iff₀ (by norm_num; linarith)]
  norm_num
  linarith

/-- At `n = 2^54` the uniform tower with `j = 4` and `m = 1024` forces `55` colours, one more
than the instances of Proposition B.1. -/
theorem overtake_two_pow_54 :
    refinedSize 54 3 ≤ 2 ^ 54 ∧ 2 ^ 54 < refinedSize 55 3 ∧ 1024 * (2 * 1024) ^ 4 ≤ 2 ^ 54 ∧
      54 < uniformBound 1024 := by
  refine ⟨by decide +kernel, by decide +kernel, by norm_num, ?_⟩
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have h : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_two_pow]
    norm_num
  rw [uniformBound, lt_div_iff₀ (by norm_num; linarith)]
  norm_num
  linarith

/-- At `n = 2^53` the instances of Proposition B.1 force `51` colours; the largest
uniform tower with `j = 4` has `m = 891`, and `X_891 ≤ 49`. -/
theorem not_yet_two_pow_53 :
    refinedSize 51 3 ≤ 2 ^ 53 ∧ 891 * (2 * 891) ^ 4 ≤ 2 ^ 53 ∧ 2 ^ 53 < 892 * (2 * 892) ^ 4 ∧
      uniformBound 891 ≤ 49 := by
  refine ⟨by decide +kernel, by norm_num, by norm_num, ?_⟩
  have h := log_3564_gt
  rw [uniformBound, div_le_iff₀ (by norm_num; linarith)]
  norm_num
  linarith

end Cert

end OnlineColouring
