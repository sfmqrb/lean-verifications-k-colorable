module

public import OnlineColouring.AppBDPJ
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theorem D.5 (partial joins): the asymptotic statements

Theorem D.5: *… then `N ≥ m³ / (3 (2 log₂ N + 1)) - m²`, so `N ≥ m^{3 - o(1)}`.  In particular, a
lower bound `χ^det_3(n) ≥ n^c` obtained from one partial-join level over `K_m` for arbitrarily
large `m` has `c ≤ 1/3`.*

* `partial_joins_rpow`: for every `ε > 0` there is `m₀` such that every `3`-colourable
  partial-join level over `K_m`, `m ≥ m₀`, that forces `m` colours and has at most `N` vertices
  has `N ≥ m^{3-ε}`.
* `partial_joins_exponent`: if for arbitrarily large `m` some `3`-colourable partial-join level
  over `K_m` that forces `m` colours and has at most `N` vertices has `N^c ≤ m`, then `c ≤ 1/3`.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Filter

theorem eventually_log_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 6 * (6 * Real.logb 2 m + 1) ≤ (m : ℝ) ^ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 := (isLittleO_log_rpow_atTop hδ).def (by positivity : 0 < Real.log 2 / 72)
  have h2 := (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (12 : ℝ))
  obtain ⟨a, ha⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨max 1 ⌈a⌉₊, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hma : a ≤ m := (Nat.le_ceil a).trans (by exact_mod_cast (le_max_right _ _).trans hm)
  obtain ⟨h3, h4⟩ := ha m hma
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hpow : 0 ≤ (m : ℝ) ^ δ := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at h3
  have h5 : Real.logb 2 m ≤ (m : ℝ) ^ δ / 72 := by
    rw [Real.logb, div_le_iff₀ hl2]
    linarith
  linarith

/-- The inequality of Theorem D.5 gives `N ≥ m^{3 - o(1)}`. -/
theorem pj_rpow {ε : ℝ} (hε : 0 < ε) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m →
    (m : ℝ) ^ 3 / (3 * (2 * Real.logb 2 N + 1)) - (m : ℝ) ^ 2 ≤ N → (m : ℝ) ^ (3 - ε) ≤ N := by
  set δ := min ε 1 with hδ
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨m₁, hm₁⟩ := eventually_log_le hδ0
  refine ⟨max 4 m₁, fun m N hm hN => ?_⟩
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hstar := hm₁ m ((le_max_right _ _).trans hm)
  have hmono : (m : ℝ) ^ (3 - ε) ≤ (m : ℝ) ^ (3 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith [min_le_left ε 1])
  refine hmono.trans ?_
  have h3 : (m : ℝ) ^ (3 : ℝ) = (m : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast]
    norm_num
  by_cases hbig : (m : ℝ) ^ 3 ≤ N
  · refine le_trans ?_ hbig
    rw [← h3]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hbig' : (N : ℝ) < (m : ℝ) ^ 3 := not_le.1 hbig
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, Real.logb_zero, mul_zero, zero_add, mul_one] at hN
    have : (m : ℝ) ^ 3 / 3 ≤ (m : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by norm_num)] at this
    nlinarith [sq_nonneg (m : ℝ)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hlogN0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg one_lt_two hN1
  have hlogN : Real.logb 2 N ≤ 3 * Real.logb 2 m := by
    have := Real.logb_le_logb_of_le one_lt_two hNpos hbig'.le
    rwa [Real.logb_pow] at this
  set Lm : ℝ := 6 * Real.logb 2 m + 1 with hLm
  have hLm1 : 1 ≤ Lm := by
    have : 0 ≤ Real.logb 2 m := Real.logb_nonneg one_lt_two hm1
    linarith
  set t : ℝ := (m : ℝ) ^ δ with ht
  have ht6 : 6 * Lm ≤ t := hstar
  have htpos : 0 < t := by linarith
  have htm : t ≤ m := by
    have := Real.rpow_le_rpow_of_exponent_le hm1 hδ1
    rwa [Real.rpow_one] at this
  have hrpow : (m : ℝ) ^ (3 - δ) = (m : ℝ) ^ 3 / t := by
    rw [Real.rpow_sub hmpos, h3]
  rw [hrpow]
  have hcube : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
  -- `m³ / (3 (2 log₂ N + 1)) ≥ m³ / (3 Lm) ≥ 2 m³ / t` and `m² ≤ m³ / t`
  have hA : 2 * ((m : ℝ) ^ 3 / t) ≤ (m : ℝ) ^ 3 / (3 * (2 * Real.logb 2 N + 1)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ htpos (by linarith)]
    have h6 : 2 * (3 * (2 * Real.logb 2 N + 1)) ≤ t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h6 hcube]
  have hB : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 / t := by
    rw [le_div_iff₀ htpos]
    nlinarith [mul_le_mul_of_nonneg_left htm (sq_nonneg (m : ℝ))]
  linarith

/-- If levels with `N ≥ m³ / (3 (2 log₂ N + 1)) - m²` force `m ≥ N^c` colours for arbitrarily
large `m`, then `c ≤ 1/3`. -/
theorem pj_exponent {c : ℝ} (h : ∀ m₀ : ℕ, ∃ m N : ℕ, m₀ ≤ m ∧
    (m : ℝ) ^ 3 / (3 * (2 * Real.logb 2 N + 1)) - (m : ℝ) ^ 2 ≤ N ∧ (N : ℝ) ^ c ≤ m) :
    c ≤ 1 / 3 := by
  by_contra hc
  have hc3 : 1 / 3 < c := not_le.1 hc
  have hc0 : 0 < c := by linarith
  set ε : ℝ := (3 - 1 / c) / 2 with hε
  have hinv : 1 / c < 3 := by
    rw [div_lt_iff₀ hc0]
    linarith
  have hε0 : 0 < ε := by
    rw [hε]
    linarith
  have hexp : 1 < (3 - ε) * c := by
    have e : (3 - ε) * c = (3 * c + 1) / 2 := by
      rw [hε]
      field_simp
      ring
    rw [e]
    linarith
  obtain ⟨m₀, hm₀⟩ := pj_rpow hε0
  obtain ⟨m, N, hm, hN, hNc⟩ := h (max 2 m₀)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have h1 := hm₀ m N ((le_max_right _ _).trans hm) hN
  have h2 : ((m : ℝ) ^ (3 - ε)) ^ c ≤ (N : ℝ) ^ c :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 hc0.le
  rw [← Real.rpow_mul (by linarith)] at h2
  have h3 : (m : ℝ) < (m : ℝ) ^ ((3 - ε) * c) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < m) hexp
    rwa [Real.rpow_one] at this
  linarith

variable {β : History → ℕ} {ρ : History → Finset ℕ}

/-- **Theorem D.5, "so `N ≥ m^{3-o(1)}`".**  For every `ε > 0` there is `m₀` such that every
partial-join level over `K_m` with `m ≥ m₀` that forces `m` colours, is `3`-colourable in every
play and has at most `N` vertices has `N ≥ m^{3-ε}`. -/
theorem partial_joins_rpow {ε : ℝ} (hε : 0 < ε) : ∃ m₀ : ℕ, ∀ (m N : ℕ) (adv : Adversary)
    (β : History → ℕ) (ρ : History → Finset ℕ), m₀ ≤ m → IsPJAdv β ρ m adv → adv.Forces m →
    (adv.LandsIn fun _ G => G.Colorable 3) → adv.SizeLE N → (m : ℝ) ^ (3 - ε) ≤ N := by
  obtain ⟨m₀, hm₀⟩ := pj_rpow hε
  exact ⟨m₀, fun m N adv β ρ hm hadv hF h3 hN => hm₀ m N hm (partial_joins hadv hF h3 hN)⟩

/-- **Theorem D.5, "in particular".**  If for arbitrarily large `m` there is a partial-join level
over `K_m`, `3`-colourable in every play and with at most `N` vertices, that gives the bound
`m ≥ N^c` (it forces `m` colours with `N` vertices), then `c ≤ 1/3`. -/
theorem partial_joins_exponent {c : ℝ}
    (h : ∀ m₀ : ℕ, ∃ (m N : ℕ) (adv : Adversary) (β : History → ℕ) (ρ : History → Finset ℕ),
      m₀ ≤ m ∧ IsPJAdv β ρ m adv ∧ adv.Forces m ∧
      (adv.LandsIn fun _ G => G.Colorable 3) ∧ adv.SizeLE N ∧ (N : ℝ) ^ c ≤ m) :
    c ≤ 1 / 3 := by
  refine pj_exponent fun m₀ => ?_
  obtain ⟨m, N, adv, β, ρ, hm, hadv, hF, h3, hN, hc⟩ := h m₀
  exact ⟨m, N, hm, partial_joins hadv hF h3 hN, hc⟩

end OnlineColouring.AppBD
