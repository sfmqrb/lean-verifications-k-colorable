module

public import OnlineColouring.UniformThresholds

/-!
# The choice of parameters in the proof of Theorem 1.1, for an abstract forcing predicate

Section 8.4 ("Putting things together").  The proofs of Theorem 1.1, of Theorem 1.3 for `G′`, of
the second statement of Corollary 8.6 and of the lower bound of Corollary 9.6 choose the number
of levels `j` and the size `m` of the top clique in the same way and then run the same chain of
inequalities.  This file does it once, for an abstract predicate `Q k n x` ("`x` colours can be
forced on `k`-colourable graphs with `n` vertices"), which is assumed to be

* monotone in `x` (`hmono`) and closed under padding in `n` (`hpad`), both for `k ≥ 1`;
* true for the uniform tower (`hcore`): `Q k (m (2m)^j) X_m` whenever `j ≥ 1`, `m ≥ 2` and
  `m ≤ |P_j(k)|`, where `X_m = uniformBound m` (Theorem 8.5);
* true for `x = 1` when `k ≥ 1` and `n ≥ 1` (`hbase`, needed for the first bound only).

The instances are `ChiRandAtLeast` and `KnownQ` (`MainLogStar.lean`), `Det.TowerInputs`
(`DetValue.lean`) and `Expl.UniformParams` (`ExplCor.lean`).

* `uniform_step`: if `j ≥ 1`, `|P_j(k)| ≥ n` and `M = (n/2^j)^{1/(j+1)} ≥ 2`, then
  `Q k n ((2M-1)/(4(1+ln 4M)))`: the tower with `m = ⌊M⌋` has at most `n` vertices.
* `uniform_rpow_div`: the chain (8.2): if `j ≥ 1` and `|P_j(k)| ≥ n ≥ 1`, then
  `Q k n (n^{1/(j+1)} / (8 (1 + ln 4n)))`.
* `Rjm.jMin k n`: the number of levels chosen in the paper, the least `j ≥ 1` with
  `|P_j(k)| ≥ n` (`jMin_spec`, `jMin_le`).  By Corollary 5.7 with `K = n`,
  `jMin 3 n ≤ lg* n + 1` and `jMin k n ≤ max(1, lg* n - 1)` for `k ≥ 4` (`jMin_three_le`,
  `jMin_le_of_four_le`).
* `Rjm.logStar_three`, `Rjm.logStar_of_four_le`: the first bounds of Theorem 1.1 for `Q`, with
  `j = jMin k n` and the exponent `1/(j+1)` weakened to `1/(lg* n + 2)`, respectively `1/lg* n`.
* `Rjm.logStar_three_large`, `Rjm.logStar_of_four_le_large`: the second bounds, `n^{1/(lg* n+3)}`
  for `n ≥ 2^406` and `n^{1/(lg* n+1)}` for `k ≥ 4`, `n ≥ 2^201`, by Lemma A.1
  (`threshold_three`, `threshold_four`) at `j = jMin k n`.
-/

@[expose] public section

namespace OnlineColouring

open Real

/-! ### The generic step and the chain (8.2) -/

section Generic

variable (Q : ℕ → ℕ → ℝ → Prop)

/-- **The generic step of the proof of Theorem 1.1.** Let `Q k n x` be monotone in `x`, closed
under padding, and satisfy Theorem 8.5 (all for `k ≥ 1`). If `|P_j(k)| ≥ n`, `j ≥ 1` and
`M = (n/2^j)^{1/(j+1)} ≥ 2`, then `Q k n ((2M-1)/(4(1+ln 4M)))`: with `m = ⌊M⌋`, the uniform
tower on `m (2m)^j ≤ n` vertices, padded to `n` vertices, forces `X_m ≥ (2M-1)/(4(1+ln 4M))`. -/
theorem uniform_step
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hnP : n ≤ Fintype.card (LabelPoset k j)) (hM : 2 ≤ levelM n j) :
    Q k n (xLower (levelM n j)) := by
  have hnM := two_pow_mul_levelM_pow n j
  have hMn := levelM_le hn j
  set M := levelM n j
  have hm2 : 2 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast hM)
  have hmM : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hmn : ⌊M⌋₊ ≤ n := by exact_mod_cast hmM.trans hMn
  have hsize : ⌊M⌋₊ * (2 * ⌊M⌋₊) ^ j ≤ n := by
    have h : ((⌊M⌋₊ * (2 * ⌊M⌋₊) ^ j : ℕ) : ℝ) ≤ n := by
      push_cast
      rw [← hnM]
      calc ((⌊M⌋₊ : ℕ) : ℝ) * (2 * (⌊M⌋₊ : ℝ)) ^ j = 2 ^ j * (⌊M⌋₊ : ℝ) ^ (j + 1) := by ring
        _ ≤ 2 ^ j * M ^ (j + 1) := by gcongr
    exact_mod_cast h
  have h := hcore k j ⌊M⌋₊ hk hj hm2 (hmn.trans hnP)
  exact hmono k n _ _ hk (hpad k _ n _ hk h hsize) (xLower_le_uniformBound hM)

/-- (8.2) for an abstract `Q`: if `|P_j(k)| ≥ n ≥ 1` and `j ≥ 1`, then
`Q k n (n^{1/(j+1)} / (8 (1 + ln 4n)))`. When `M < 2` the bound is below `1` and `Q k n 1` is
used. -/
theorem uniform_rpow_div
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    (hbase : ∀ k n, 1 ≤ k → 1 ≤ n → Q k n 1)
    {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hnP : n ≤ Fintype.card (LabelPoset k j)) :
    Q k n ((n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n)))) := by
  rcases lt_or_ge (levelM n j) 2 with hM | hM
  · refine hmono k n _ _ hk (hbase k n hk hn) ?_
    have h1 := rpow_le_two_mul_levelM hn j
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
    rw [div_le_one (by positivity)]
    linarith
  · exact hmono k n _ _ hk (uniform_step Q hmono hpad hcore hk hn hj hnP hM)
      (rpow_div_le_xLower hn hM)

end Generic

namespace Rjm

open Finset Real

/-! ### The number of levels chosen in the proof of Theorem 1.1 -/

/-- The least `j ≥ 1` with `|P_j(k)| ≥ n` (and `0` if there is none). -/
noncomputable def jMin (k n : ℕ) : ℕ :=
  sInf {j | 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset k j)}

theorem jMin_spec {k n J : ℕ} (hJ : 1 ≤ J) (hnP : n ≤ Fintype.card (LabelPoset k J)) :
    1 ≤ jMin k n ∧ n ≤ Fintype.card (LabelPoset k (jMin k n)) :=
  Nat.sInf_mem (s := {j | 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset k j)}) ⟨J, hJ, hnP⟩

/-- `jMin k n` is the least such `j`. -/
theorem jMin_le {k n J : ℕ} (hJ : 1 ≤ J) (hnP : n ≤ Fintype.card (LabelPoset k J)) :
    jMin k n ≤ J :=
  Nat.sInf_le (s := {j | 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset k j)}) ⟨hJ, hnP⟩

/-- Corollary 5.7 with `K = n`, `k = 3`: `j ≤ L + 1`. -/
theorem jMin_three_le {n : ℕ} (hn : 2 ≤ n) : jMin 3 n ≤ logStar n + 1 :=
  jMin_le (by omega) (le_card_labelPoset_three hn)

/-- Corollary 5.7 with `K = n`, `k ≥ 4`: `j ≤ max(1, L - 1)`. -/
theorem jMin_le_of_four_le {k : ℕ} (hk : 4 ≤ k) (n : ℕ) : jMin k n ≤ max 1 (logStar n - 1) :=
  jMin_le (le_max_left _ _) (le_card_labelPoset_of_four_le hk n)

/-! ### The generic argument, with the paper's choice of `j` -/

section Generic

variable (Q : ℕ → ℕ → ℝ → Prop)

theorem rpow_inv_anti {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (n : ℝ) ^ (1 / b) ≤ (n : ℝ) ^ (1 / a) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (one_div_le_one_div_of_le ha hab)

/-- **Theorem 1.1, first bound, `k = 3`, for an abstract `Q`**, with `j = jMin 3 n`. -/
theorem logStar_three
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    (hbase : ∀ k n, 1 ≤ k → 1 ≤ n → Q k n 1)
    {n : ℕ} (hn : 3 ≤ n) :
    Q 3 n ((n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n)))) := by
  obtain ⟨hj, hnP⟩ := jMin_spec (k := 3) (n := n) (J := logStar n + 1) (by omega)
    (le_card_labelPoset_three (by omega))
  have hjL := jMin_three_le (n := n) (by omega)
  have h := uniform_rpow_div Q hmono hpad hcore hbase (k := 3) (j := jMin 3 n)
    (by norm_num) (by omega) hj hnP
  refine hmono 3 n _ _ (by norm_num) h ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply rpow_inv_anti (by omega) (by positivity)
  have : ((jMin 3 n : ℕ) : ℝ) ≤ (logStar n : ℝ) + 1 := by exact_mod_cast hjL
  linarith

/-- **Theorem 1.1, first bound, `k ≥ 4`, for an abstract `Q`**, with `j = jMin k n`. -/
theorem logStar_of_four_le
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    (hbase : ∀ k n, 1 ≤ k → 1 ≤ n → Q k n 1)
    {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) :
    Q k n ((n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n)))) := by
  have hL := two_le_logStar hn
  obtain ⟨hj, hnP⟩ := jMin_spec (k := k) (n := n) (J := max 1 (logStar n - 1))
    (le_max_left _ _) (le_card_labelPoset_of_four_le hk n)
  have hjL := jMin_le_of_four_le hk n
  have h := uniform_rpow_div Q hmono hpad hcore hbase (k := k) (j := jMin k n)
    (by omega) (by omega) hj hnP
  refine hmono k n _ _ (by omega) h ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply rpow_inv_anti (by omega) (by positivity)
  have : jMin k n + 1 ≤ logStar n := by omega
  exact_mod_cast this

/-- **Theorem 1.1, second bound, `k = 3`, for an abstract `Q`** (`n ≥ 2^406`), with
`j = jMin 3 n` and Lemma A.1. -/
theorem logStar_three_large
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    {n : ℕ} (hn : 2 ^ 406 ≤ n) :
    Q 3 n ((n : ℝ) ^ (1 / (logStar n + 3 : ℝ))) := by
  have hn2 : 2 ≤ n := le_trans (Nat.le_self_pow (by norm_num) 2) hn
  obtain ⟨hj, hnP⟩ := jMin_spec (k := 3) (n := n) (J := logStar n + 1) (by omega)
    (le_card_labelPoset_three hn2)
  have hjL := jMin_three_le hn2
  obtain ⟨hM, hle⟩ := threshold_three hn hj hjL
  refine hmono 3 n _ _ (by norm_num)
    (uniform_step Q hmono hpad hcore (by norm_num) (by omega) hj hnP hM) (le_trans ?_ hle)
  rw [show ((1 : ℝ) / ((jMin 3 n : ℝ) + 2)) = 1 / ((jMin 3 n : ℝ) + 2) from rfl]
  apply rpow_inv_anti (by omega) (by positivity)
  have : ((jMin 3 n : ℕ) : ℝ) ≤ (logStar n : ℝ) + 1 := by exact_mod_cast hjL
  linarith

/-- **Theorem 1.1, second bound, `k ≥ 4`, for an abstract `Q`** (`n ≥ 2^201`), with
`j = jMin k n` and Lemma A.1. -/
theorem logStar_of_four_le_large
    (hmono : ∀ k n x x', 1 ≤ k → Q k n x → x' ≤ x → Q k n x')
    (hpad : ∀ k n n' x, 1 ≤ k → Q k n x → n ≤ n' → Q k n' x)
    (hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
      Q k (m * (2 * m) ^ j) (uniformBound m))
    {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    Q k n ((n : ℝ) ^ (1 / (logStar n + 1 : ℝ))) := by
  have hn3 : 3 ≤ n := le_trans (by norm_num) hn
  have hL := five_le_logStar hn
  obtain ⟨hj, hnP⟩ := jMin_spec (k := k) (n := n) (J := max 1 (logStar n - 1))
    (le_max_left _ _) (le_card_labelPoset_of_four_le hk n)
  have hjL := jMin_le_of_four_le hk n
  obtain ⟨hM, hle⟩ := threshold_four hn hj hjL
  refine hmono k n _ _ (by omega)
    (uniform_step Q hmono hpad hcore (by omega) (by omega) hj hnP hM) (le_trans ?_ hle)
  apply rpow_inv_anti (by omega) (by positivity)
  have : jMin k n + 2 ≤ logStar n + 1 := by omega
  exact_mod_cast this

end Generic

end Rjm

end OnlineColouring
