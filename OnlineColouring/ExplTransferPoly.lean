module

public import OnlineColouring.ExplTransferSize
public import OnlineColouring.Asymptotic

/-!
# Lower bounds with constant probability transfer between values of `k`

Appendix D.5, paragraph "Transfer for randomized algorithms": *Lower bounds `n^c` or
`2^{(log n)^c}` that hold with constant probability against every deterministic algorithm also
transfer from any `k' ≥ 3` to `k = 3`, with a smaller `c`.*

This file proves both forms.  `ProbForcing k n x p` (`ProbForcing.lean`) says that some
distribution over `k`-colourable ordered graphs on `n` vertices makes every (proper) deterministic
online algorithm use at least `x` colours with probability at least `p`.

* **`probForcing_pow`** (the analogue of the first sentence of Theorem 1.4): for `k ≥ 1`, `j ≥ 1`
  with `width(P_j(k)) ≥ k'` and `0 < ε < 1` there is `N₁` (the witness of the proof depends only
  on `j` and `ε`) such that for every `N ≥ N₁`, every `x > 1` and every `ρ`:
  `ProbForcing k' N x ρ → ProbForcing k (N^{(j+1)(j+2)}) x (ρ - ε)`.
* **`transfer_rand_poly`**: let `k ≥ 3`, `c > 0`, `0 < ε < 1`.  If `ProbForcing k' N (N^c) ρ` for
  all large `N`, then `ProbForcing k n (n^{c'}) (ρ - ε)` for all large `n`, with
  `c' = c / (2 (lg* k' + 2)(lg* k' + 3))`.  The paper's case is `k = 3`.
* **`transfer_rand_quasipoly`**: let `k ≥ 3`, `0 < c' < c`, `0 < ε < 1`.  If
  `ProbForcing k' N (2^{(log₂ N)^c}) ρ` for all large `N`, then
  `ProbForcing k n (2^{(log₂ n)^{c'}}) (ρ - ε)` for all large `n`.
* `transfer_rand_poly_of_antichain`, `transfer_rand_quasipoly_of_antichain`: the same for every
  `j ≥ 1` with `width(P_j(k)) ≥ k'` (exponent `c / (2 (j+1)(j+2))` in the first form).

The proof uses the transfer of `ExplTransfer.lean` (`probForcing_transfer`, with the paper's block
sizes) and its size `n ≤ N^{j+1} (K Λ)^{j(j+1)/2}`, `Λ = max(1, ln(j n²/ε))`
(`trN_le_pow_succ`).  Since `K ≤ N` and `Λ^{j(j+1)} ≤ n` for large `n`
(`exists_log_pow_le`), this gives `n ≤ N^{(j+1)(j+2)}` for large `N` (`trN_le_pow_two`).  The
size `N^{(j+1)(j+2)}` is the square of the size `N^{(j+1)(j+2)/2}` of Theorem 1.4: the
logarithmic factors `Λ` are absorbed by doubling the exponent of `N`, which is crude (the true
loss is `n^{o(1)}`) but gives statements without `o(1)`.  The exponent `c'` of the first form is
a quarter of the exponent `2c/((lg* k'+2)(lg* k'+3))` of Theorem 1.4: one factor `2` is this
doubling, the other comes from the bound `⌊n^{1/(2a)}⌋ ≥ n^{1/(4a)}`, `a = (j+1)(j+2)/2`, for the
number `N` of vertices before the transfer (`exists_root_floor`).

The paragraph ends: *This does not cover `χ^rand_{k'}`: an expected cost of `x` gives `x/2`
colours with probability at least `x/(2N)`, but in general not with constant probability.*
`prob_half_of_detExpCost` is this guarantee.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset
open scoped ENNReal

/-! ### Two facts about `ProbForcing` -/

/-- The number of colours is an integer: forcing `x` colours is forcing `⌈x⌉` colours. -/
theorem probForcing_ceil {k n : ℕ} {x p : ℝ} (h : ProbForcing k n x p) :
    ProbForcing k n (⌈x⌉₊ : ℕ) p := by
  obtain ⟨D, hcol, hD⟩ := h
  refine ⟨D, hcol, fun A hA => ?_⟩
  have hset : {I : OnlineInput n | ((⌈x⌉₊ : ℕ) : ℝ) ≤ (I.cost A : ℝ)} =
      {I | x ≤ (I.cost A : ℝ)} := by
    ext I
    change ((⌈x⌉₊ : ℕ) : ℝ) ≤ (I.cost A : ℝ) ↔ x ≤ (I.cost A : ℝ)
    rw [Nat.cast_le, Nat.ceil_le]
  rw [hset]
  exact hD A hA

/-- With positive probability one cannot force more than `n` colours on `n` vertices. -/
theorem le_of_probForcing {k n : ℕ} {x p : ℝ} (h : ProbForcing k n x p) (hp : 0 < p) :
    x ≤ n := by
  obtain ⟨D, -, hD⟩ := h
  by_contra hx
  push Not at hx
  have h1 := hD _ OnlineAlg.firstFit_isProper
  have hempty : {I : OnlineInput n | x ≤ (I.cost OnlineAlg.firstFit : ℝ)} = ∅ := by
    ext I
    have h2 : (I.cost OnlineAlg.firstFit : ℝ) ≤ n := by
      exact_mod_cast I.cost_le OnlineAlg.firstFit
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    linarith
  rw [hempty, PMF.toOuterMeasure_apply] at h1
  simp only [Set.indicator_empty, tsum_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  linarith

/-- For a probability `p ≤ 0` the predicate holds trivially (for `k ≥ 1`). -/
theorem probForcing_of_nonpos {k n : ℕ} (hk : 1 ≤ k) (x : ℝ) {p : ℝ} (hp : p ≤ 0) :
    ProbForcing k n x p := by
  refine ⟨PMF.pure (emptyInput n), fun I hI => ?_, fun A _ => ?_⟩
  · rw [PMF.mem_support_pure_iff] at hI
    exact hI ▸ emptyInput_colorable hk
  · rw [ENNReal.ofReal_of_nonpos hp]
    exact bot_le

/-! ### The size is polynomial -/

/-- A power of the logarithm is eventually below the square: there is `T ≥ 1` such that
`max(1, ln(j t²/ε))^{4e} ≤ t²` for all `t ≥ T`. -/
theorem exists_log_pow_le {j : ℕ} (hj : 1 ≤ j) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (e : ℕ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      (max 1 (Real.log (j * t ^ 2 / ε))) ^ (4 * e) ≤ t ^ 2 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hc : (0 : ℝ) < ε / j := by positivity
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    ((Real.isLittleO_pow_log_id_atTop (n := 4 * e)).def hc)
  refine ⟨max 1 X, le_max_left _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htX : X ≤ t := (le_max_right _ _).trans ht
  have hpos : (0 : ℝ) ≤ j * t ^ 2 / ε := by positivity
  have hXt : X ≤ j * t ^ 2 / ε := by
    have h1 : t ≤ t ^ 2 := by nlinarith
    have h2 : t ^ 2 ≤ j * t ^ 2 / ε := by
      rw [le_div_iff₀ hε0]
      have h3 : ε * t ^ 2 ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right hε1.le (sq_nonneg t)
      have h4 : 1 * t ^ 2 ≤ j * t ^ 2 := mul_le_mul_of_nonneg_right hj' (sq_nonneg t)
      linarith
    linarith
  have hb := hX _ hXt
  simp only [id, Real.norm_eq_abs] at hb
  rw [abs_of_nonneg hpos] at hb
  have hb' : |Real.log (j * t ^ 2 / ε) ^ (4 * e)| ≤ t ^ 2 := by
    calc |Real.log (j * t ^ 2 / ε) ^ (4 * e)| ≤ ε / j * (j * t ^ 2 / ε) := hb
      _ = t ^ 2 := by field_simp
  rcases le_total (Real.log (j * t ^ 2 / ε)) 1 with hl | hl
  · rw [max_eq_left hl, one_pow]
    nlinarith
  · rw [max_eq_right hl]
    exact (le_abs_self _).trans hb'

/-- **Polynomial size.** With `2 ≤ K ≤ N`, a post-degree bound `1 ≤ D ≤ N`, and `N` beyond the
threshold `T` of `exists_log_pow_le`, the transferred distribution has at most `N^{(j+1)(j+2)}`
vertices. -/
theorem trN_le_pow_two {K j N D : ℕ} {ε : ℝ} (hK : 2 ≤ K) (hKN : K ≤ N) (hj : 1 ≤ j)
    (hD : 1 ≤ D) (hDN : D ≤ N) (hε0 : 0 < ε) (hε1 : ε < 1) {T : ℝ}
    (hT : ∀ t : ℝ, T ≤ t →
      (max 1 (Real.log (j * t ^ 2 / ε))) ^ (4 * (j * (j + 1) / 2)) ≤ t ^ 2)
    (hNT : T ≤ N) : trN K j ε N D j ≤ N ^ (2 * ((j + 1) * (j + 2) / 2)) := by
  have hN : 1 ≤ N := by omega
  have hae : (j + 1) * (j + 2) / 2 = j * (j + 1) / 2 + (j + 1) := succ_mul_succ_succ_div_two j
  have hn1 : (1 : ℝ) ≤ (trN K j ε N D j : ℝ) := by
    exact_mod_cast (trState_pos hK hj hN hD hε0 hε1 j).1
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hsz : (trN K j ε N D j : ℝ) ≤ (N : ℝ) ^ ((j + 1) * (j + 2) / 2) *
      (max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) := by
    calc (trN K j ε N D j : ℝ)
        ≤ (N : ℝ) ^ (j + 1) * ((K : ℝ) *
            max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) :=
          trN_le_pow_succ hK hj hN hD hε0 hε1 hDN
      _ ≤ (N : ℝ) ^ (j + 1) * ((N : ℝ) *
            max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) := by
          gcongr
      _ = _ := by
          rw [hae, mul_pow, pow_add]
          ring
  have hmain : (trN K j ε N D j : ℝ) ≤ (N : ℝ) ^ (2 * ((j + 1) * (j + 2) / 2)) := by
    rcases le_or_gt T (trN K j ε N D j : ℝ) with hTn | hTn
    · have h4 := hT _ hTn
      have h2e : (max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
          (2 * (j * (j + 1) / 2)) ≤ (trN K j ε N D j : ℝ) := by
        have h5 : ((max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
            (2 * (j * (j + 1) / 2))) ^ 2 ≤ (trN K j ε N D j : ℝ) ^ 2 := by
          rw [← pow_mul]
          convert h4 using 2
          ring
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h5
      have hsq : (trN K j ε N D j : ℝ) * (trN K j ε N D j : ℝ) ≤
          (N : ℝ) ^ (2 * ((j + 1) * (j + 2) / 2)) * (trN K j ε N D j : ℝ) := by
        calc (trN K j ε N D j : ℝ) * (trN K j ε N D j : ℝ)
            ≤ ((N : ℝ) ^ ((j + 1) * (j + 2) / 2) *
                (max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
                  (j * (j + 1) / 2)) *
              ((N : ℝ) ^ ((j + 1) * (j + 2) / 2) *
                (max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
                  (j * (j + 1) / 2)) := mul_le_mul hsz hsz (by positivity) (by positivity)
          _ = (N : ℝ) ^ (2 * ((j + 1) * (j + 2) / 2)) *
                (max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
                  (2 * (j * (j + 1) / 2)) := by ring
          _ ≤ (N : ℝ) ^ (2 * ((j + 1) * (j + 2) / 2)) * (trN K j ε N D j : ℝ) :=
              mul_le_mul_of_nonneg_left h2e (by positivity)
      exact le_of_mul_le_mul_right hsq (by linarith)
    · calc (trN K j ε N D j : ℝ) ≤ T := hTn.le
        _ ≤ N := hNT
        _ ≤ (N : ℝ) ^ (2 * ((j + 1) * (j + 2) / 2)) := le_self_pow₀ hN' (by omega)
  exact_mod_cast hmain

/-! ### The transfer with polynomial size -/

/-- **The randomized transfer with polynomial size** (the analogue of the first sentence of
Theorem 1.4 for oblivious adversaries).  Let `k ≥ 1`, `j ≥ 1` with `width(P_j(k)) ≥ k'`, and
`0 < ε < 1`.  There is `N₁` (the witness of the proof depends only on `j` and `ε`) such that for
all `N ≥ N₁`: if some distribution over `k'`-colourable ordered graphs on `N` vertices forces
`x > 1` colours with probability `ρ`, then some distribution over `k`-colourable ordered graphs on
`N^{(j+1)(j+2)}` vertices forces `x` colours with probability `ρ - ε`. -/
theorem probForcing_pow {k k' j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hanti : HasAntichain (LabelPoset k j) k') {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ x ρ : ℝ, 1 < x → ProbForcing k' N x ρ →
      ProbForcing k (N ^ (2 * ((j + 1) * (j + 2) / 2))) x (ρ - ε) := by
  obtain ⟨T, -, hT⟩ := exists_log_pow_le hj hε0 hε1 (j * (j + 1) / 2)
  refine ⟨⌈T⌉₊, fun N hN x ρ hx h0 => ?_⟩
  rcases le_or_gt ρ ε with hρ | hρ
  · exact probForcing_of_nonpos hk _ (by linarith)
  have hNT : T ≤ N := (Nat.le_ceil T).trans (by exact_mod_cast hN)
  have hxN : x ≤ N := le_of_probForcing h0 (hε0.trans hρ)
  have h1 := probForcing_ceil h0
  have hKN : ⌈x⌉₊ ≤ N := Nat.ceil_le.2 hxN
  have hK2 : 2 ≤ ⌈x⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hx)
  have h2 := probForcing_transfer hK2 hanti hε0 h1
  have hsize := trN_le_pow_two (D := N - 1) hK2 hKN hj (by omega) (Nat.sub_le _ _) hε0 hε1 hT hNT
  exact (h2.pad hsize hk).of_le (Nat.le_ceil _)

/-- For `n ≥ max(2, N₁)^{4a}` there is `N ≥ max(2, N₁)` with `n^{1/(4a)} ≤ N` and
`N^{2a} ≤ n`, namely `N = ⌊n^{1/(2a)}⌋`. -/
theorem exists_root_floor {a N₁ n : ℕ} (ha : 1 ≤ a) (hn : (max 2 N₁) ^ (4 * a) ≤ n) :
    ∃ N : ℕ, N₁ ≤ N ∧ 2 ≤ N ∧ (n : ℝ) ^ (((4 * a : ℕ) : ℝ)⁻¹) ≤ N ∧ N ^ (2 * a) ≤ n := by
  have h4a : 4 * a ≠ 0 := by omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (n : ℝ) ^ (((4 * a : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hz4 : z ^ (4 * a) = n := by
    rw [hz]
    exact Real.rpow_inv_natCast_pow hn0 h4a
  have hMz : ((max 2 N₁ : ℕ) : ℝ) ≤ z := by
    have h1 : (((max 2 N₁ : ℕ) : ℝ) ^ (4 * a)) ^ (((4 * a : ℕ) : ℝ)⁻¹) = ((max 2 N₁ : ℕ) : ℝ) :=
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) h4a
    rw [← h1, hz]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by positivity)
  have hz2 : (2 : ℝ) ≤ z := le_trans (by exact_mod_cast le_max_left 2 N₁) hMz
  have hNle : ((⌊z ^ 2⌋₊ : ℕ) : ℝ) ≤ z ^ 2 := Nat.floor_le (by positivity)
  have hzN : z ≤ (⌊z ^ 2⌋₊ : ℕ) := by
    have h1 := Nat.lt_floor_add_one (z ^ 2)
    nlinarith
  refine ⟨⌊z ^ 2⌋₊, ?_, ?_, ?_, ?_⟩
  · have h1 : (N₁ : ℝ) ≤ (⌊z ^ 2⌋₊ : ℕ) :=
      le_trans (le_trans (by exact_mod_cast le_max_right 2 N₁) hMz) hzN
    exact_mod_cast h1
  · have h1 : ((2 : ℕ) : ℝ) ≤ (⌊z ^ 2⌋₊ : ℕ) := by
      push_cast
      exact hz2.trans hzN
    exact_mod_cast h1
  · rw [← hz]
    exact hzN
  · have h1 : ((⌊z ^ 2⌋₊ : ℕ) : ℝ) ^ (2 * a) ≤ n := by
      calc ((⌊z ^ 2⌋₊ : ℕ) : ℝ) ^ (2 * a) ≤ (z ^ 2) ^ (2 * a) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hNle _
        _ = z ^ (4 * a) := by
            rw [← pow_mul]
            congr 1
            ring
        _ = n := hz4
    exact_mod_cast h1

theorem one_le_succ_mul_succ_div_two (j : ℕ) : 1 ≤ (j + 1) * (j + 2) / 2 := by
  have := succ_mul_succ_succ_div_two j
  omega

/-! ### Bounds of the form `n^c` -/

/-- **Polynomial bounds with constant probability transfer**, for every `j ≥ 1` with
`width(P_j(k)) ≥ k'`: from `N^c` colours with probability `ρ` on `k'`-colourable graphs to
`n^{c/(2(j+1)(j+2))}` colours with probability `ρ - ε` on `k`-colourable graphs. -/
theorem transfer_rand_poly_of_antichain {k k' j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hanti : HasAntichain (LabelPoset k j) k') {c ρ ε : ℝ} (hc : 0 < c) (hε0 : 0 < ε)
    (hε1 : ε < 1) (N₀ : ℕ) (h : ∀ N ≥ N₀, ProbForcing k' N ((N : ℝ) ^ c) ρ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ProbForcing k n
      ((n : ℝ) ^ (c / ((4 * ((j + 1) * (j + 2) / 2) : ℕ) : ℝ))) (ρ - ε) := by
  obtain ⟨N₁, hN₁⟩ := probForcing_pow (k' := k') hk hj hanti hε0 hε1
  refine ⟨(max 2 (max N₀ N₁)) ^ (4 * ((j + 1) * (j + 2) / 2)), fun n hn => ?_⟩
  obtain ⟨N, hN1, hN2, hzN, hNn⟩ := exists_root_floor (one_le_succ_mul_succ_div_two j) hn
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN1
  have hx : (1 : ℝ) < (N : ℝ) ^ c := Real.one_lt_rpow (by exact_mod_cast hN2) hc
  have h1 := hN₁ N ((le_max_right _ _).trans hN1) _ ρ hx (h N hN0)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : (n : ℝ) ^ (c / ((4 * ((j + 1) * (j + 2) / 2) : ℕ) : ℝ)) ≤ (N : ℝ) ^ c := by
    have e1 : (n : ℝ) ^ (c / ((4 * ((j + 1) * (j + 2) / 2) : ℕ) : ℝ)) =
        ((n : ℝ) ^ (((4 * ((j + 1) * (j + 2) / 2) : ℕ) : ℝ)⁻¹)) ^ c := by
      rw [← Real.rpow_mul hn0, div_eq_inv_mul]
    rw [e1]
    exact Real.rpow_le_rpow (by positivity) hzN hc.le
  exact (h1.pad hNn hk).of_le hpow

/-- **Polynomial lower bounds that hold with constant probability transfer between values of
`k`** (Appendix D.5, first form).  Let `k ≥ 3`, `c > 0` and `0 < ε < 1`.  If for all large `N`
some distribution over `k'`-colourable ordered graphs on `N` vertices makes every deterministic
online algorithm use at least `N^c` colours with probability at least `ρ`, then for all large `n`
some distribution over `k`-colourable ordered graphs on `n` vertices makes every deterministic
online algorithm use at least `n^{c'}` colours with probability at least `ρ - ε`, where
`c' = c / (2 (lg* k' + 2)(lg* k' + 3))`. -/
theorem transfer_rand_poly {k k' : ℕ} (hk : 3 ≤ k) {c ρ ε : ℝ} (hc : 0 < c) (hε0 : 0 < ε)
    (hε1 : ε < 1) (N₀ : ℕ) (h : ∀ N ≥ N₀, ProbForcing k' N ((N : ℝ) ^ c) ρ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ProbForcing k n
      ((n : ℝ) ^ (c / (2 * ((logStar k' + 2) * (logStar k' + 3))))) (ρ - ε) := by
  obtain ⟨n₀, hn₀⟩ := transfer_rand_poly_of_antichain (j := logStar k' + 1) (by omega)
    (Nat.le_add_left _ _) (hasAntichain_labelPoset_logStar hk k') hc hε0 hε1 N₀ h
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 := hn₀ n hn
  have e : (((4 * ((logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2) : ℕ)) : ℝ) =
      2 * (((logStar k' : ℝ) + 2) * ((logStar k' : ℝ) + 3)) := by
    have h2 := two_mul_succ_succ_div_two (logStar k')
    have h3 : 4 * ((logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2) =
        2 * ((logStar k' + 2) * (logStar k' + 3)) := by
      have h4 : (logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2 =
          (logStar k' + 2) * (logStar k' + 3) / 2 := rfl
      rw [h4]
      omega
    rw [h3]
    push_cast
    ring
  rwa [e] at h1

/-! ### Bounds of the form `2^{(log n)^c}` -/

/-- **Bounds of the form `2^{(log n)^c}` with constant probability transfer**, for every `j ≥ 1`
with `width(P_j(k)) ≥ k'`: from `2^{(log₂ N)^c}` colours with probability `ρ` to
`2^{(log₂ n)^{c'}}` colours with probability `ρ - ε`, for every `0 < c' < c`. -/
theorem transfer_rand_quasipoly_of_antichain {k k' j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hanti : HasAntichain (LabelPoset k j) k') {c c' ρ ε : ℝ} (hc' : 0 < c') (hcc' : c' < c)
    (hε0 : 0 < ε) (hε1 : ε < 1) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ProbForcing k' N ((2 : ℝ) ^ (Real.logb 2 N ^ c)) ρ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ProbForcing k n ((2 : ℝ) ^ (Real.logb 2 n ^ c')) (ρ - ε) := by
  obtain ⟨N₁, hN₁⟩ := probForcing_pow (k' := k') hk hj hanti hε0 hε1
  have hc : 0 < c := hc'.trans hcc'
  have ha1 := one_le_succ_mul_succ_div_two j
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((4 * ((j + 1) * (j + 2) / 2) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hq]
    exact_mod_cast (by omega : 0 < 4 * ((j + 1) * (j + 2) / 2))
  have hqc : 0 < q ^ c := Real.rpow_pos_of_pos hq0 c
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = (q ^ c) ^ (c - c')⁻¹ := ⟨_, rfl⟩
  have hL₀pos : 0 < L₀ := by
    rw [hL₀]
    exact Real.rpow_pos_of_pos hqc _
  refine ⟨max ((max 2 (max N₀ N₁)) ^ (4 * ((j + 1) * (j + 2) / 2))) ⌈(2 : ℝ) ^ L₀⌉₊,
    fun n hn => ?_⟩
  obtain ⟨N, hN1, hN2, hzN, hNn⟩ := exists_root_floor ha1 ((le_max_left _ _).trans hn)
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN1
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) (by linarith)
  have hx : (1 : ℝ) < (2 : ℝ) ^ (Real.logb 2 N ^ c) :=
    Real.one_lt_rpow (by norm_num) (Real.rpow_pos_of_pos hlogN c)
  have h1 := hN₁ N ((le_max_right _ _).trans hN1) _ ρ hx (h N hN0)
  have hnL : (2 : ℝ) ^ L₀ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hnL
  have hℓ : L₀ ≤ Real.logb 2 n := (Real.le_logb_iff_rpow_le (by norm_num) hn0).2 hnL
  have hℓpos : 0 < Real.logb 2 n := hL₀pos.trans_le hℓ
  have hz : q⁻¹ * Real.logb 2 n ≤ Real.logb 2 N := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn0, hq]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos hn0 _) hzN
  have hexp : Real.logb 2 n ^ c' ≤ Real.logb 2 N ^ c := by
    have h2 : (q⁻¹ * Real.logb 2 n) ^ c ≤ Real.logb 2 N ^ c :=
      Real.rpow_le_rpow (by positivity) hz hc.le
    have h3 : (q⁻¹ * Real.logb 2 n) ^ c =
        (q ^ c)⁻¹ * (Real.logb 2 n ^ c' * Real.logb 2 n ^ (c - c')) := by
      rw [Real.mul_rpow (by positivity) hℓpos.le, Real.inv_rpow hq0.le,
        ← Real.rpow_add hℓpos]
      congr 2
      ring
    have h4 : q ^ c ≤ Real.logb 2 n ^ (c - c') := by
      have h5 : L₀ ^ (c - c') = q ^ c := by
        rw [hL₀]
        exact Real.rpow_inv_rpow hqc.le (sub_pos.2 hcc').ne'
      rw [← h5]
      exact Real.rpow_le_rpow hL₀pos.le hℓ (sub_pos.2 hcc').le
    have h6 : (0 : ℝ) ≤ Real.logb 2 n ^ c' := Real.rpow_nonneg hℓpos.le _
    calc Real.logb 2 n ^ c' = (q ^ c)⁻¹ * (Real.logb 2 n ^ c' * q ^ c) := by field_simp
      _ ≤ (q ^ c)⁻¹ * (Real.logb 2 n ^ c' * Real.logb 2 n ^ (c - c')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 h6) (inv_pos.2 hqc).le
      _ = (q⁻¹ * Real.logb 2 n) ^ c := h3.symm
      _ ≤ Real.logb 2 N ^ c := h2
  exact (h1.pad hNn hk).of_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

/-- **Lower bounds of the form `2^{(log n)^c}` that hold with constant probability transfer
between values of `k`** (Appendix D.5, second form).  Let `k ≥ 3`, `0 < c' < c` and
`0 < ε < 1`.  If for all large `N` some distribution over `k'`-colourable ordered graphs on `N`
vertices makes every deterministic online algorithm use at least `2^{(log₂ N)^c}` colours with
probability at least `ρ`, then for all large `n` some distribution over `k`-colourable ordered
graphs on `n` vertices makes every deterministic online algorithm use at least
`2^{(log₂ n)^{c'}}` colours with probability at least `ρ - ε`. -/
theorem transfer_rand_quasipoly {k k' : ℕ} (hk : 3 ≤ k) {c c' ρ ε : ℝ} (hc' : 0 < c')
    (hcc' : c' < c) (hε0 : 0 < ε) (hε1 : ε < 1) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ProbForcing k' N ((2 : ℝ) ^ (Real.logb 2 N ^ c)) ρ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ProbForcing k n ((2 : ℝ) ^ (Real.logb 2 n ^ c')) (ρ - ε) :=
  transfer_rand_quasipoly_of_antichain (j := logStar k' + 1) (by omega) (Nat.le_add_left _ _)
    (hasAntichain_labelPoset_logStar hk k') hc' hcc' hε0 hε1 N₀ h

/-! ### Why expected-cost bounds are not transferred -/

/-- **Expected cost `x` guarantees `x/2` colours with probability `x/(2N)`** (the last sentence
of the paragraph: the reason why the transfer is not claimed for bounds on `χ^rand_{k'}`).  If a
deterministic algorithm has expected cost at least `x` on a distribution over inputs with `N ≥ 1`
vertices, then it uses at least `x/2` colours with probability at least `x/(2N)` (the bound
`cost ≤ N` even gives `x/(2N - x)`). -/
theorem prob_half_of_detExpCost {N : ℕ} (hN : 1 ≤ N) (D : PMF (OnlineInput N)) (A : OnlineAlg)
    {x : ℝ} (hx : x ≤ detExpCost D A) :
    ENNReal.ofReal (x / (2 * N)) ≤ D.toOuterMeasure {I | x / 2 ≤ (I.cost A : ℝ)} := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx0 (by positivity))]
    exact bot_le
  have hP := toOuterMeasure_ne_top D {I | x / 2 ≤ (I.cost A : ℝ)}
  have hterm : ∀ I : OnlineInput N, D I * (I.cost A : ℝ≥0∞) ≤
      {I | x / 2 ≤ (I.cost A : ℝ)}.indicator D I * N + D I * ENNReal.ofReal (x / 2) := by
    intro I
    by_cases hI : x / 2 ≤ (I.cost A : ℝ)
    · rw [Set.indicator_of_mem (by exact hI)]
      exact le_add_right (mul_le_mul_right (by exact_mod_cast I.cost_le A) _)
    · rw [Set.indicator_of_notMem (by exact hI), zero_mul, zero_add]
      refine mul_le_mul_right ?_ _
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (not_le.1 hI).le
  have hsum : ∑' I, D I * (I.cost A : ℝ≥0∞) ≤
      D.toOuterMeasure {I | x / 2 ≤ (I.cost A : ℝ)} * N + ENNReal.ofReal (x / 2) := by
    calc ∑' I, D I * (I.cost A : ℝ≥0∞)
        ≤ ∑' I, ({I | x / 2 ≤ (I.cost A : ℝ)}.indicator D I * N +
            D I * ENNReal.ofReal (x / 2)) := tsum_le_tsum hterm
      _ = D.toOuterMeasure {I | x / 2 ≤ (I.cost A : ℝ)} * N + ENNReal.ofReal (x / 2) := by
          rw [tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, D.tsum_coe,
            one_mul, PMF.toOuterMeasure_apply]
  have h1 := (ofReal_le_tsum_of_le_detExpCost hx).trans hsum
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hP (ENNReal.natCast_ne_top N),
      ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hP (ENNReal.natCast_ne_top N)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hx0.le,
    ENNReal.toReal_ofReal (by positivity)] at h2
  apply (ENNReal.ofReal_le_iff_le_toReal hP).2
  rw [div_le_iff₀ (by positivity)]
  linarith

end Expl

end OnlineColouring
