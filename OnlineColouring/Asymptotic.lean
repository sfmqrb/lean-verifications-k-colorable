module

public import OnlineColouring.MainTheorem
public import OnlineColouring.Transfer
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Asymptotic forms of Theorems 1.2 and 1.4

* Theorem 1.2, the sentence "In particular `χ^det_k(n) ≥ n^{(2-o(1))/(lg* n)^2}` for every
  fixed `k ≥ 3`": `chiDet_ge_asymptotic`.  The `o(1)` is spelled out: for every `ε > 0` there
  is `N` with `n^{(2-ε)/(lg* n)^2} ≤ χ^det_k(n)` for all `n ≥ N`.  The literal form, with a
  function `g(n) → 0` in place of `o(1)`, is `exists_chiDet_ge_rpow_two_sub`.
* Theorem 1.4, second statement: if `χ^det_{k'}(n) = Ω(n^ε)` for a fixed `k' ≥ 3`, then
  `χ^det_3(n) = Ω(n^{ε'})` with `ε' = 2ε/((lg* k'+2)(lg* k'+3))`: `transfer_poly_real` (the `Ω`
  is spelled out with a constant `c > 0` and a threshold).  The same holds for every target
  `k ≥ 3` (`transfer_poly_real_of_three_le`), and the `Asymptotics.IsBigO` form is
  `transfer_isBigO`.
* Monotonicity of `χ^det`: `chiDet_mono_right` (in `n`, the sentence after Definition 4.1) and
  `chiDet_mono_left` (in `k`).

Proof of the first statement: `k = 3` suffices, because a `3`-colourable graph is
`k`-colourable (`chiDet_mono_left`), and so does `ε ≤ 1`.  For `L = lg* n` large, the floor
bound `⌊n^a⌋ ≤ χ^det_3(n)` with `a = 2/((L+2)(L+3))` (`floor_rpow_le_chiDet_three`) and
`⌊y⌋ > y - 1` reduce it to `n^b + 1 ≤ n^a` with `b = (2-ε)/L^2`.  This follows from
`a - b ≥ 1/L^3` (once `εL ≥ 34`, `exponent_gap`) and `n > tow(L-1) ≥ 2^{L^3}` (`cube_le_tow`),
which give `n^{a-b} ≥ 2`.

Proof of the second statement: with `e = (lg* k'+2)(lg* k'+3)/2` and `M = ⌊n^{1/e}⌋`,
Theorem 1.4 (`chiDet_transfer`, `j = lg* k' + 1`) and padding give
`χ^det_{k'}(M) ≤ χ^det_k(n)` because `M^e ≤ n`; and `M ≥ n^{1/e}/2`, so
`c M^ε ≥ (c/2^ε) n^{ε/e}`.  The paper argues through `N_{k'}(K) = O(K^{1/ε})` and
Observation 4.3 instead.
-/

@[expose] public section

namespace OnlineColouring

/-! ### Monotonicity of `χ^det` -/

/-- A `k`-colourable graph is `k'`-colourable for `k ≤ k'`, so lower bounds for `k` hold
for `k'`. -/
theorem ChiDetAtLeast.mono_left {k k' n K : ℕ} (hkk' : k ≤ k') (h : ChiDetAtLeast k n K) :
    ChiDetAtLeast k' n K := fun A hA => by
  obtain ⟨I, hc, hK⟩ := h A hA
  exact ⟨I, hc.mono hkk', hK⟩

/-- `χ^det_k(n) ≤ χ^det_{k'}(n)` for `1 ≤ k ≤ k'`. -/
theorem chiDet_mono_left {k k' n : ℕ} (hk : 1 ≤ k) (hkk' : k ≤ k') : chiDet k n ≤ chiDet k' n :=
  (le_chiDet_iff (hk.trans hkk')).2 (((le_chiDet_iff hk).1 le_rfl).mono_left hkk')

/-- `χ^det_k(m) ≤ χ^det_k(n)` for `k ≥ 1` and `m ≤ n` (padding with isolated vertices). -/
theorem chiDet_mono_right {k m n : ℕ} (hk : 1 ≤ k) (hmn : m ≤ n) : chiDet k m ≤ chiDet k n :=
  (le_chiDet_iff hk).2 (((le_chiDet_iff hk).1 le_rfl).mono hk hmn)

theorem one_le_chiDet {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : 1 ≤ chiDet k n :=
  (le_chiDet_iff hk).2 (chiDetAtLeast_one hk hn)

/-! ### Theorem 1.2, asymptotic form -/

theorem cube_le_two_pow {x : ℕ} (hx : 10 ≤ x) : x ^ 3 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ 2 x]
    have h₁ : 10 * (x * x) ≤ x * (x * x) := Nat.mul_le_mul_right _ hx
    have h₂ : 10 * x ≤ x * x := Nat.mul_le_mul_right _ hx
    have h : (x + 1) ^ 3 ≤ 2 * x ^ 3 := by
      have e₁ : (x + 1) ^ 3 = x * (x * x) + 3 * (x * x) + 3 * x + 1 := by ring
      have e₂ : x ^ 3 = x * (x * x) := by ring
      rw [e₁, e₂]
      omega
    omega

theorem add_three_le_tow {m : ℕ} (hm : 3 ≤ m) : m + 3 ≤ tow m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [tow]
  | succ m hm ih =>
    have := tow_lt_tow_succ m
    omega

/-- `(i+2)^3 ≤ tow i` for `i ≥ 4`. -/
theorem cube_le_tow {i : ℕ} (hi : 4 ≤ i) : (i + 2) ^ 3 ≤ tow i := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have h16 : 16 ≤ tow m := by
    have := tow_mono (show 3 ≤ m by omega)
    norm_num [tow] at this
    exact this
  calc (m + 1 + 2) ^ 3 = (m + 3) ^ 3 := rfl
    _ ≤ tow m ^ 3 := Nat.pow_le_pow_left (add_three_le_tow (by omega)) 3
    _ ≤ 2 ^ tow m := cube_le_two_pow (by omega)
    _ = tow (m + 1) := rfl

/-- `2^{L^3} ≤ n` for `L = lg* n ≥ 6`, since `n > tow(L-1) = 2^{tow(L-2)}`. -/
theorem two_pow_cube_logStar_le {n : ℕ} (hL : 6 ≤ logStar n) : 2 ^ (logStar n ^ 3) ≤ n := by
  set L := logStar n
  have h₁ : tow (L - 1) < n := lt_tow_of_lt_logStar (by omega)
  have h₂ : L ^ 3 ≤ tow (L - 2) := by
    have := cube_le_tow (i := L - 2) (by omega)
    rwa [show L - 2 + 2 = L by omega] at this
  have h₃ : tow (L - 1) = 2 ^ tow (L - 2) := by
    rw [show L - 1 = L - 2 + 1 by omega, tow_succ]
  have h₄ : 2 ^ (L ^ 3) ≤ 2 ^ tow (L - 2) := Nat.pow_le_pow_right (by norm_num) h₂
  omega

/-- The gap between the exponents: if `ε > 0`, `L ≥ 1` and `εL ≥ 34`, then
`(2-ε)/L^2 + 1/L^3 ≤ 2/((L+2)(L+3))`. -/
theorem exponent_gap {ε L : ℝ} (hε : 0 < ε) (hL : 1 ≤ L) (hεL : 34 ≤ ε * L) :
    (2 - ε) / L ^ 2 + (L ^ 3)⁻¹ ≤ 2 / ((L + 2) * (L + 3)) := by
  have hL0 : 0 < L := by linarith
  have key : ((2 - ε) * L + 1) * ((L + 2) * (L + 3)) ≤ 2 * L ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hεL (sq_nonneg L), mul_nonneg hε.le (sq_nonneg L),
      mul_nonneg hε.le hL0.le, mul_nonneg (sub_nonneg.2 hL) (by linarith : (0 : ℝ) ≤ 23 * L + 6)]
  have e : (2 - ε) / L ^ 2 + (L ^ 3)⁻¹ = ((2 - ε) * L + 1) / L ^ 3 := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- If `x ≥ 1`, `b ≥ 0` and `x^{a-b} ≥ 2`, then `x^b + 1 ≤ x^a`. -/
theorem rpow_add_one_le_rpow {x a b : ℝ} (hx : 1 ≤ x) (hb : 0 ≤ b) (hab : 2 ≤ x ^ (a - b)) :
    x ^ b + 1 ≤ x ^ a := by
  have h1 : 1 ≤ x ^ b := Real.one_le_rpow hx hb
  have h2 : x ^ a = x ^ (a - b) * x ^ b := by
    rw [← Real.rpow_add (by linarith), sub_add_cancel]
  rw [h2]
  nlinarith

/-- **Theorem 1.2, asymptotic form, `k = 3`:** for every `ε > 0`,
`n^{(2-ε)/(lg* n)^2} ≤ χ^det_3(n)` for all large `n`. -/
theorem chiDet_three_ge_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ ((2 - ε) / ((logStar n : ℝ) ^ 2)) ≤ chiDet 3 n := by
  -- it suffices to treat `δ = min ε 1`
  set δ := min ε 1 with hδ
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set L0 : ℕ := max 6 ⌈34 / δ⌉₊ with hL0def
  refine ⟨tow L0 + 1, fun n hn => ?_⟩
  set L := logStar n with hLdef
  have hL0 : L0 < L := by
    by_contra h
    have := logStar_le_iff.1 (not_lt.1 h)
    omega
  have hL6 : 6 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hδL : 34 ≤ δ * L := by
    have h₁ : 34 / δ ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 6 _).trans hL0.le)
    rw [div_le_iff₀ hδ0] at h₁
    linarith
  have hn3 : 3 ≤ n := by
    have : tow 2 ≤ tow L0 := tow_mono (by omega)
    norm_num [tow] at this
    omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set a : ℝ := 2 / ((L + 2) * (L + 3)) with ha
  set b : ℝ := (2 - δ) / (L : ℝ) ^ 2 with hb
  -- `a - b ≥ 1/L^3` and `n ≥ 2^{L^3}` give `n^{a-b} ≥ 2`
  have hab : (((L ^ 3 : ℕ) : ℝ))⁻¹ ≤ a - b := by
    have := exponent_gap hδ0 hLr hδL
    push_cast
    linarith
  have h2 : (2 : ℝ) ≤ (n : ℝ) ^ (a - b) := by
    have hp : ((2 : ℝ) ^ (L ^ 3)) ≤ n := by exact_mod_cast two_pow_cube_logStar_le hL6
    have hL3 : L ^ 3 ≠ 0 := by positivity
    calc (2 : ℝ) = ((2 : ℝ) ^ (L ^ 3)) ^ (((L ^ 3 : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hL3).symm
      _ ≤ (n : ℝ) ^ (((L ^ 3 : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow (by positivity) hp (by positivity)
      _ ≤ (n : ℝ) ^ (a - b) := Real.rpow_le_rpow_of_exponent_le hn1 hab
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (by positivity)
  have hkey : (n : ℝ) ^ b + 1 ≤ (n : ℝ) ^ a := rpow_add_one_le_rpow hn1 hb0 h2
  have hfloor : (n : ℝ) ^ a < ⌊(n : ℝ) ^ a⌋₊ + 1 := Nat.lt_floor_add_one _
  have hchi₀ : ⌊(n : ℝ) ^ a⌋₊ ≤ chiDet 3 n := floor_rpow_le_chiDet_three hn3
  have hchi : ((⌊(n : ℝ) ^ a⌋₊ : ℕ) : ℝ) ≤ (chiDet 3 n : ℝ) := Nat.cast_le.2 hchi₀
  have hεb : (n : ℝ) ^ ((2 - ε) / (L : ℝ) ^ 2) ≤ (n : ℝ) ^ b := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    rw [hb]
    gcongr
  linarith

/-- **Theorem 1.2, asymptotic form** ("`χ^det_k(n) ≥ n^{(2-o(1))/(lg* n)^2}` for every fixed
`k ≥ 3`"): for every `k ≥ 3` and `ε > 0`, `n^{(2-ε)/(lg* n)^2} ≤ χ^det_k(n)` for all large `n`. -/
theorem chiDet_ge_asymptotic {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ ((2 - ε) / ((logStar n : ℝ) ^ 2)) ≤ chiDet k n := by
  obtain ⟨N, hN⟩ := chiDet_three_ge_asymptotic hε
  exact ⟨N, fun n hn => (hN n hn).trans (by exact_mod_cast chiDet_mono_left (by norm_num) hk)⟩

theorem one_le_logStar {n : ℕ} (hn : 2 ≤ n) : 1 ≤ logStar n := by
  by_contra h
  have := logStar_le_iff.1 (show logStar n ≤ 0 by omega)
  rw [tow_zero] at this
  omega

open Filter Topology in
/-- **Theorem 1.2, asymptotic form, literal `o(1)` version:** for every `k ≥ 3` there is
`g : ℕ → ℝ` with `g(n) → 0` and `n^{(2-g(n))/(lg* n)^2} ≤ χ^det_k(n)` for every `n ≥ 1`. -/
theorem exists_chiDet_ge_rpow_two_sub {k : ℕ} (hk : 3 ≤ k) :
    ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ ((2 - g n) / ((logStar n : ℝ) ^ 2)) ≤ chiDet k n := by
  set g : ℕ → ℝ := fun n => max 0 (2 - (logStar n : ℝ) ^ 2 * Real.logb n (chiDet k n)) with hg
  have hχ : ∀ n ≥ 1, (1 : ℝ) ≤ chiDet k n := fun n hn => by
    exact_mod_cast one_le_chiDet (by omega) hn
  have hL : ∀ n ≥ 2, (0 : ℝ) < (logStar n : ℝ) ^ 2 := fun n hn => by
    have : (1 : ℝ) ≤ logStar n := by exact_mod_cast one_le_logStar hn
    positivity
  refine ⟨g, ?_, fun n hn => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := chiDet_ge_asymptotic hk (half_pos hε)
    refine ⟨max N 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := le_of_max_le_right hn
    have hb : (1 : ℝ) < n := by exact_mod_cast hn2
    have h₁ := hN n (le_of_max_le_left hn)
    rw [← Real.le_logb_iff_rpow_le hb (by linarith [hχ n (by omega)]),
      div_le_iff₀ (hL n hn2)] at h₁
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
    refine max_lt hε ?_
    linarith
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [Nat.cast_one, Real.one_rpow]
      exact hχ 1 le_rfl
    · have hb : (1 : ℝ) < n := by exact_mod_cast hn2
      have h₁ : (2 - g n) / (logStar n : ℝ) ^ 2 ≤ Real.logb n (chiDet k n) := by
        rw [div_le_iff₀ (hL n hn2)]
        have : 2 - (logStar n : ℝ) ^ 2 * Real.logb n (chiDet k n) ≤ g n := le_max_right _ _
        linarith
      calc (n : ℝ) ^ ((2 - g n) / (logStar n : ℝ) ^ 2)
          ≤ (n : ℝ) ^ Real.logb n (chiDet k n) := Real.rpow_le_rpow_of_exponent_le hb.le h₁
        _ = chiDet k n := Real.rpow_logb (by linarith) hb.ne' (by linarith [hχ n hn])

/-! ### Theorem 1.4, second statement -/

/-- `(L+2)(L+3)` is even. -/
theorem two_mul_succ_succ_div_two (L : ℕ) : (L + 2) * (L + 3) = 2 * ((L + 2) * (L + 3) / 2) :=
  (Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (L + 2))).symm

/-- Theorem 1.4 in terms of `χ^det`, with padding: if `k ≥ 3`, `k' ≥ 1`, `n ≥ 1` and `M^e ≤ n`
with `e = (lg* k'+2)(lg* k'+3)/2`, then `χ^det_{k'}(M) ≤ χ^det_k(n)`. -/
theorem chiDet_le_chiDet_of_pow_le {k k' M n : ℕ} (hk : 3 ≤ k) (hk' : 1 ≤ k') (hn : 1 ≤ n)
    (hM : M ^ ((logStar k' + 2) * (logStar k' + 3) / 2) ≤ n) : chiDet k' M ≤ chiDet k n := by
  rcases Nat.lt_or_ge (chiDet k' M) 2 with h | h
  · have := one_le_chiDet (by omega : 1 ≤ k) hn
    omega
  · have h₁ := chiDet_transfer hk hk' h le_rfl
    have e : (logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2 =
        (logStar k' + 2) * (logStar k' + 3) / 2 := rfl
    rw [e] at h₁
    exact h₁.trans (chiDet_mono_right (by omega) hM)

/-- **Theorem 1.4, second statement, any target `k ≥ 3`:** let `k' ≥ 1`, `ε > 0` and `c > 0`.  If
`c n^ε ≤ χ^det_{k'}(n)` for all `n ≥ N₀` (i.e. `χ^det_{k'}(n) = Ω(n^ε)`), then there are `c' > 0`
and `N₁` with `c' n^{ε'} ≤ χ^det_k(n)` for all `n ≥ N₁`, where `ε' = 2ε/((lg* k'+2)(lg* k'+3))`. -/
theorem transfer_poly_real_of_three_le {k k' : ℕ} (hk : 3 ≤ k) (hk' : 1 ≤ k') {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (N0 : ℕ) (h : ∀ n ≥ N0, c * (n : ℝ) ^ ε ≤ chiDet k' n) :
    ∃ c' > 0, ∃ N1 : ℕ, ∀ n ≥ N1,
      c' * (n : ℝ) ^ (2 * ε / ((logStar k' + 2) * (logStar k' + 3))) ≤ chiDet k n := by
  set e : ℕ := (logStar k' + 2) * (logStar k' + 3) / 2 with he_def
  have he_nat : (logStar k' + 2) * (logStar k' + 3) = 2 * e := two_mul_succ_succ_div_two _
  have he2 : ((logStar k' : ℝ) + 2) * ((logStar k' : ℝ) + 3) = 2 * (e : ℝ) := by
    exact_mod_cast he_nat
  have he0 : e ≠ 0 := by
    have : 6 ≤ (logStar k' + 2) * (logStar k' + 3) := by nlinarith
    omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
  refine ⟨c / 2 ^ ε, div_pos hc (Real.rpow_pos_of_pos two_pos _), N0 ^ e + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set x : ℝ := (n : ℝ) ^ ((e : ℝ)⁻¹) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1r (by positivity)
  set M := ⌊x⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hx1)
  have hxM : x / 2 ≤ M := by
    have h₁ := Nat.lt_floor_add_one x
    have h₂ : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hMn : M ^ e ≤ n := by
    have h₁ : (M : ℝ) ^ e ≤ x ^ e :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) e
    have h₂ : x ^ e = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) he0
    exact_mod_cast h₁.trans_eq h₂
  have hN0M : N0 ≤ M := by
    apply Nat.le_floor
    have h₁ : ((N0 : ℝ) ^ e) ^ ((e : ℝ)⁻¹) = N0 := Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) he0
    rw [← h₁]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact_mod_cast (by omega : N0 ^ e ≤ n)
  have hchi : chiDet k' M ≤ chiDet k n := chiDet_le_chiDet_of_pow_le hk hk' hn1 hMn
  have hcM := h M hN0M
  have hexp : 2 * ε / (((logStar k' : ℝ) + 2) * ((logStar k' : ℝ) + 3)) = (e : ℝ)⁻¹ * ε := by
    rw [he2]
    field_simp
  have hxε : (n : ℝ) ^ ((e : ℝ)⁻¹ * ε) = x ^ ε := Real.rpow_mul (Nat.cast_nonneg n) _ _
  rw [hexp, hxε]
  calc c / 2 ^ ε * x ^ ε = c * (x / 2) ^ ε := by
        rw [Real.div_rpow (by positivity) (by norm_num)]
        ring
    _ ≤ c * (M : ℝ) ^ ε := by gcongr
    _ ≤ chiDet k' M := hcM
    _ ≤ chiDet k n := by exact_mod_cast hchi

/-- **Theorem 1.4, second statement** (the paper's statement, target `k = 3`): if
`χ^det_{k'}(n) = Ω(n^ε)` for a fixed `k' ≥ 3`, then `χ^det_3(n) = Ω(n^{ε'})` with
`ε' = 2ε/((lg* k'+2)(lg* k'+3))`. -/
theorem transfer_poly_real {k' : ℕ} (hk' : 3 ≤ k') {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (N0 : ℕ)
    (h : ∀ n ≥ N0, c * (n : ℝ) ^ ε ≤ chiDet k' n) :
    ∃ c' > 0, ∃ N1 : ℕ, ∀ n ≥ N1,
      c' * (n : ℝ) ^ (2 * ε / ((logStar k' + 2) * (logStar k' + 3))) ≤ chiDet 3 n :=
  transfer_poly_real_of_three_le le_rfl (by omega) hε hc N0 h

open Asymptotics Filter in
/-- **Theorem 1.4, second statement, with `Ω` as `Asymptotics.IsBigO`:** for `k' ≥ 1` and `ε > 0`,
if `n^ε = O(χ^det_{k'}(n))`, then `n^{ε'} = O(χ^det_k(n))` for every `k ≥ 3`, where
`ε' = 2ε/((lg* k'+2)(lg* k'+3))`. -/
theorem transfer_isBigO {k k' : ℕ} (hk : 3 ≤ k) (hk' : 1 ≤ k') {ε : ℝ} (hε : 0 < ε)
    (h : (fun n : ℕ => (n : ℝ) ^ ε) =O[atTop] (fun n : ℕ => (chiDet k' n : ℝ))) :
    (fun n : ℕ => (n : ℝ) ^ (2 * ε / ((logStar k' + 2) * (logStar k' + 3)))) =O[atTop]
      (fun n : ℕ => (chiDet k n : ℝ)) := by
  obtain ⟨C, hC, hCw⟩ := h.exists_pos
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hCw.bound
  have h' : ∀ n ≥ N0, C⁻¹ * (n : ℝ) ^ ε ≤ chiDet k' n := by
    intro n hn
    have := hN0 n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at this
    rw [inv_mul_le_iff₀ hC]
    exact this
  obtain ⟨c', hc', N1, hN1⟩ := transfer_poly_real_of_three_le hk hk' hε (inv_pos.2 hC) N0 h'
  refine IsBigO.of_bound c'⁻¹ (eventually_atTop.2 ⟨N1, fun n hn => ?_⟩)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul,
    le_div_iff₀ hc', mul_comm]
  exact hN1 n hn

end OnlineColouring
