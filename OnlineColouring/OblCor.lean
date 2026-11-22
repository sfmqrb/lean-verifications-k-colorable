module

public import OnlineColouring.OblTower
public import OnlineColouring.MainTheorem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corollary C.4 (high probability)

Corollary C.4 (`thm:main-rand`) of Appendix C, as stated.  Let `n ≥ 3`,
`ε ∈ (0,1)`, `L = lg* n` and `Λ_n = ⌈ln((L+1) n²/ε)⌉` (`Lam n ε`).

* `oblivious_high_prob_three` (`k = 3`): with `K = ⌊n^{2/((L+2)(L+3))}/Λ_n⌋`, there is a
  distribution over `3`-colourable online inputs on exactly `n` vertices on which every proper
  deterministic online algorithm uses at least `K` colours with probability at least `1 - ε`
  (`ProbForcing 3 n K (1 - ε)`), and `χ^rand_3(n) ≥ (1 - ε) K`.
* `oblivious_high_prob_of_four_le` (`k ≥ 4`): the same with `K = ⌊n^{2/(L(L+1))}/Λ_n⌋`.

The proof is the paper's (`probForcing_floor`): `j = L + 1` for `k = 3` and `j = L - 1` for
`k ≥ 4`, `e = (j+1)(j+2)/2`, `M = K Λ`, the block sizes `b_ℓ = (K-1) D_ℓ Λ`, that is
`b_ℓ = (K-1) ((K-1)Λ)^{j+1-ℓ}` and `D_ℓ = (K-1) ((K-1)Λ)^{j-ℓ}` (`corB`, `towD_corB`,
`corB_eq`), the bound `N_0 ≤ M^e ≤ n` (`towN_le_pow`), each loss at most
`n² e^{-Λ} ≤ ε/(L+1)`, Theorem C.3, padding, and Yao's principle
(`chiRandAtLeast_of_probForcing`).  If `K ≤ 1` the statement is trivial (`probForcing_one`).
-/

@[expose] public section

namespace OnlineColouring

namespace Obl

open Finset
open scoped ENNReal

/-- `Λ_n = ⌈ln((L+1) n²/ε)⌉` with `L = lg* n`. -/
noncomputable def Lam (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.log (((logStar n : ℝ) + 1) * (n : ℝ) ^ 2 / ε)⌉₊

/-! ### Yao's principle for `ProbForcing` -/

/-- Yao's principle (Lemma 4.4), the "In particular" sentence, for the predicate `ProbForcing`. -/
theorem chiRandAtLeast_of_probForcing {k n K : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (h : ProbForcing k n (K : ℝ) (1 - ε)) : ChiRandAtLeast k n ((1 - ε) * K) := by
  obtain ⟨D, hcol, hD⟩ := h
  refine yao hk le_rfl D hcol fun A hA => ?_
  have hset : {I : OnlineInput n | (K : ℝ) ≤ (I.cost A : ℝ)} = {I | K ≤ I.cost A} := by
    ext I
    simp
  have h₁ := hD A hA
  rw [hset] at h₁
  have h₂ := ENNReal.toReal_mono (toOuterMeasure_ne_top D _) h₁
  rw [ENNReal.toReal_ofReal'] at h₂
  exact (le_max_left _ _).trans h₂

/-! ### Triangular exponents -/

theorem tri_succ (d : ℕ) : (d + 1 + 1) * (d + 1 + 2) / 2 = (d + 1) * (d + 2) / 2 + (d + 2) := by
  have h : (d + 1 + 1) * (d + 1 + 2) = (d + 1) * (d + 2) + 2 * (d + 2) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num)]

theorem tri_mono {a b : ℕ} (h : a ≤ b) : (a + 1) * (a + 2) / 2 ≤ (b + 1) * (b + 2) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

theorem two_mul_tri (j : ℕ) : 2 * ((j + 1) * (j + 2) / 2) = (j + 1) * (j + 2) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self (j + 1)).two_dvd

/-- `N_{j-d} ≤ M^{(d+1)(d+2)/2}` if `K ≤ M` and `b_{j-d} ≤ M^{d+2}`. -/
theorem towN_le_pow {K j M : ℕ} {b : ℕ → ℕ} (hKM : K ≤ M)
    (hb : ∀ d < j, b (j - d) ≤ M ^ (d + 2)) :
    ∀ d ≤ j, towN K j b (j - d) ≤ M ^ ((d + 1) * (d + 2) / 2) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, towN_self]
    simpa using hKM
  | succ d ih =>
    intro hd
    have hlt : j - (d + 1) < j := by omega
    have e : j - (d + 1) + 1 = j - d := by omega
    rw [towN_pred K b hlt, e, tri_succ, pow_add]
    exact Nat.mul_le_mul (ih (by omega)) (hb d (by omega))

/-! ### The block sizes of the corollary -/

/-- The block sizes `b_ℓ = (K-1) ((K-1)Λ)^{j+1-ℓ}` (which equal `(K-1) D_ℓ Λ`). -/
def corB (K Λ j : ℕ) (ℓ : ℕ) : ℕ := (K - 1) * ((K - 1) * Λ) ^ (j + 1 - ℓ)

theorem towD_corB (K Λ : ℕ) {j ℓ : ℕ} (h : ℓ ≤ j) :
    towD K j (corB K Λ j) ℓ = (K - 1) * ((K - 1) * Λ) ^ (j - ℓ) := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · rw [towD_self, Nat.sub_self, pow_zero, mul_one]
  · rw [towD_pred K _ hlt]
    unfold corB
    congr 2
    omega

/-- `b_ℓ = (K-1) D_ℓ Λ`, the paper's choice. -/
theorem corB_eq (K Λ : ℕ) {j ℓ : ℕ} (h : ℓ ≤ j) :
    corB K Λ j ℓ = (K - 1) * towD K j (corB K Λ j) ℓ * Λ := by
  rw [towD_corB K Λ h]
  unfold corB
  have e : j + 1 - ℓ = (j - ℓ) + 1 := by omega
  rw [e, pow_succ]
  ring

/-! ### The core of Corollary C.4 -/

/-- **Corollary C.4 for a general number `j` of levels.** Let `k ≥ 2`, `n ≥ 3`,
`1 ≤ j ≤ lg* n + 1`, `n ≤ |P_j(k)|` and `ε ∈ (0,1)`.  Then some distribution over `k`-colourable
online inputs on `n` vertices forces `⌊n^{2/((j+1)(j+2))}/Λ_n⌋` colours with probability at least
`1 - ε`. -/
theorem probForcing_floor {k n j : ℕ} (hk : 2 ≤ k) (hn : 3 ≤ n) (hj : 1 ≤ j)
    (hjL : j ≤ logStar n + 1) (hnP : n ≤ Fintype.card (LabelPoset k j)) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ProbForcing k n
      (⌊(n : ℝ) ^ ((2 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) / (Lam n ε : ℝ)⌋₊ : ℝ)
      (1 - ε) := by
  set Λ := Lam n ε with hΛdef
  set x : ℝ := (n : ℝ) ^ ((2 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) with hx
  set K := ⌊x / (Λ : ℝ)⌋₊ with hKdef
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ (logStar n : ℝ) := Nat.cast_nonneg _
  -- `Λ ≥ ln y` and `Λ ≥ 1`, where `y = (L+1) n² / ε`
  set y : ℝ := ((logStar n : ℝ) + 1) * (n : ℝ) ^ 2 / ε with hy
  have hy1 : 1 < y := by
    rw [hy, lt_div_iff₀ hε0]
    nlinarith
  have hΛlog : Real.log y ≤ Λ := Nat.le_ceil _
  have hΛ1 : 1 ≤ Λ := Nat.ceil_pos.2 (Real.log_pos hy1)
  have hΛpos : (0 : ℝ) < Λ := by exact_mod_cast hΛ1
  rcases lt_or_ge K 2 with hK | hK
  · -- `K ≤ 1`: trivial
    refine (probForcing_one (by omega) (by omega) (by linarith)).of_le ?_
    have : K ≤ 1 := by omega
    exact_mod_cast this
  -- the main case `K ≥ 2`
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKx : (K : ℝ) ≤ x / Λ := Nat.floor_le (div_nonneg hx0 hΛpos.le)
  have hMx : (K : ℝ) * Λ ≤ x := (le_div_iff₀ hΛpos).1 hKx
  set e := (j + 1) * (j + 2) / 2 with he
  have he2 : 2 * e = (j + 1) * (j + 2) := two_mul_tri j
  have he2' : (2 : ℝ) * e = ((j : ℝ) + 1) * ((j : ℝ) + 2) := by exact_mod_cast he2
  have hje : j + 1 ≤ e := by nlinarith
  set M := K * Λ with hM
  have hM1 : 1 ≤ M := Nat.mul_pos (by omega) hΛ1
  have hKM : K ≤ M := Nat.le_mul_of_pos_right K hΛ1
  -- `M^e ≤ n`
  have hMe : M ^ e ≤ n := by
    have h : ((M ^ e : ℕ) : ℝ) ≤ n := by
      rw [hM]
      push_cast
      calc ((K : ℝ) * Λ) ^ e ≤ x ^ e := pow_le_pow_left₀ (by positivity) hMx e
        _ = n := by
            rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
            have hone : (2 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * (e : ℝ) = 1 := by
              rw [← he2']
              have : (e : ℝ) ≠ 0 := by
                have : (1 : ℝ) ≤ e := by exact_mod_cast (by omega : 1 ≤ e)
                positivity
              field_simp
            rw [hone, Real.rpow_one]
    exact_mod_cast h
  have hKn : K ≤ n := hKM.trans ((Nat.le_self_pow (by omega) M).trans hMe)
  -- the block sizes
  set q := (K - 1) * Λ with hq
  have hq1 : 1 ≤ q := Nat.mul_pos (by omega) hΛ1
  have hqM : q ≤ M := Nat.mul_le_mul_right Λ (Nat.sub_le K 1)
  have hK1M : K - 1 ≤ M := (Nat.sub_le K 1).trans hKM
  set b := corB K Λ j with hbdef
  have hbpos : ∀ ℓ ∈ Icc 1 j, 0 < b ℓ := fun ℓ _ =>
    Nat.mul_pos (by omega) (Nat.pow_pos hq1)
  have hbM : ∀ d < j, b (j - d) ≤ M ^ (d + 2) := by
    intro d hd
    have e₁ : j + 1 - (j - d) = d + 1 := by omega
    change (K - 1) * ((K - 1) * Λ) ^ (j + 1 - (j - d)) ≤ M ^ (d + 2)
    rw [e₁, pow_succ' M (d + 1)]
    exact Nat.mul_le_mul hK1M (Nat.pow_le_pow_left hqM _)
  have hN := towN_le_pow hKM hbM
  -- `N_ℓ ≤ n` and `D_ℓ ≤ n`
  have hNn : ∀ ℓ ≤ j, towN K j b ℓ ≤ n := by
    intro ℓ hℓ
    have h := hN (j - ℓ) (Nat.sub_le j ℓ)
    rw [Nat.sub_sub_self hℓ] at h
    exact h.trans ((Nat.pow_le_pow_right hM1 (tri_mono (Nat.sub_le j ℓ))).trans hMe)
  have hDn : ∀ ℓ ≤ j, towD K j b ℓ ≤ n := by
    intro ℓ hℓ
    rw [hbdef, towD_corB K Λ hℓ]
    calc (K - 1) * ((K - 1) * Λ) ^ (j - ℓ) ≤ M * M ^ (j - ℓ) :=
          Nat.mul_le_mul hK1M (Nat.pow_le_pow_left hqM _)
      _ = M ^ (j - ℓ + 1) := (pow_succ' M (j - ℓ)).symm
      _ ≤ M ^ e := Nat.pow_le_pow_right hM1 (by omega)
      _ ≤ n := hMe
  have hDpos : ∀ ℓ ≤ j, 0 < towD K j b ℓ := by
    intro ℓ hℓ
    rw [hbdef, towD_corB K Λ hℓ]
    exact Nat.mul_pos (by omega) (Nat.pow_pos hq1)
  -- `n² e^{-Λ} ≤ ε / (L+1)`
  have hexp : (n : ℝ) * n * Real.exp (-(Λ : ℝ)) ≤ ε / ((logStar n : ℝ) + 1) := by
    have hy0 : 0 < y := by linarith
    have h₁ : Real.exp (-(Λ : ℝ)) ≤ y⁻¹ := by
      rw [← Real.exp_log hy0, ← Real.exp_neg]
      exact Real.exp_le_exp.2 (by linarith)
    have hn0 : (0 : ℝ) < (n : ℝ) * n := by nlinarith
    calc (n : ℝ) * n * Real.exp (-(Λ : ℝ)) ≤ (n : ℝ) * n * y⁻¹ :=
          mul_le_mul_of_nonneg_left h₁ hn0.le
      _ = ε / ((logStar n : ℝ) + 1) := by
          rw [hy]
          field_simp
  -- condition (C.1)
  have hstar : ∑ ℓ ∈ Icc 1 j, (towN K j b ℓ : ℝ) * towD K j b ℓ *
      Real.exp (-(b ℓ : ℝ) / (((K : ℝ) - 1) * towD K j b ℓ)) ≤ ε := by
    have hterm : ∀ ℓ ∈ Icc 1 j, (towN K j b ℓ : ℝ) * towD K j b ℓ *
        Real.exp (-(b ℓ : ℝ) / (((K : ℝ) - 1) * towD K j b ℓ)) ≤
          ε / ((logStar n : ℝ) + 1) := by
      intro ℓ hℓ
      have hℓj : ℓ ≤ j := (mem_Icc.1 hℓ).2
      have hD0 : (0 : ℝ) < towD K j b ℓ := by exact_mod_cast hDpos ℓ hℓj
      have hK0 : (0 : ℝ) < (K : ℝ) - 1 := by
        have : (2 : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      have hbℓ : (b ℓ : ℝ) = ((K : ℝ) - 1) * towD K j b ℓ * Λ := by
        have h := corB_eq K Λ hℓj
        rw [← hbdef] at h
        rw [h]
        push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
        ring
      have hexpo : -(b ℓ : ℝ) / (((K : ℝ) - 1) * towD K j b ℓ) = -(Λ : ℝ) := by
        rw [hbℓ]
        field_simp
      rw [hexpo]
      have h₁ : (towN K j b ℓ : ℝ) ≤ n := by exact_mod_cast hNn ℓ hℓj
      have h₂ : (towD K j b ℓ : ℝ) ≤ n := by exact_mod_cast hDn ℓ hℓj
      have h₃ : (towN K j b ℓ : ℝ) * towD K j b ℓ ≤ (n : ℝ) * n :=
        mul_le_mul h₁ h₂ hD0.le (Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_right h₃ (Real.exp_pos _).le).trans hexp
    calc _ ≤ ∑ _ℓ ∈ Icc 1 j, ε / ((logStar n : ℝ) + 1) := sum_le_sum hterm
      _ = (j : ℝ) * (ε / ((logStar n : ℝ) + 1)) := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ ((logStar n : ℝ) + 1) * (ε / ((logStar n : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hjL
      _ = ε := by field_simp
  have hmain := oblivious_towers hk hK hj (hKn.trans hnP) hε0 hε1 b hbpos hstar
  have hN0 : towN K j b 0 ≤ n := hNn 0 (Nat.zero_le j)
  exact hmain.pad hN0 (by omega)

/-! ### Corollary C.4 -/

/-- **Corollary C.4 (high probability), `k = 3`.** Let `n ≥ 3`, `ε ∈ (0,1)`, `L = lg* n`,
`Λ_n = ⌈ln((L+1) n²/ε)⌉` and `K = ⌊n^{2/((L+2)(L+3))}/Λ_n⌋`.  There is a distribution over
`3`-colourable ordered graphs on `n` vertices on which every proper deterministic online
algorithm uses at least `K` colours with probability at least `1 - ε`.  In particular
`χ^rand_3(n) ≥ (1 - ε) K`. -/
theorem oblivious_high_prob_three {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing 3 n
      (⌊(n : ℝ) ^ ((2 : ℝ) / (((logStar n : ℝ) + 2) * ((logStar n : ℝ) + 3))) /
        (Lam n ε : ℝ)⌋₊ : ℝ) (1 - ε) ∧
    (1 - ε) * (⌊(n : ℝ) ^ ((2 : ℝ) / (((logStar n : ℝ) + 2) * ((logStar n : ℝ) + 3))) /
        (Lam n ε : ℝ)⌋₊ : ℝ) ≤ chiRand 3 n := by
  have h := probForcing_floor (k := 3) (j := logStar n + 1) (by norm_num) hn (by omega) le_rfl
    (le_card_labelPoset_three (by omega)) hε0 hε1
  have e₁ : (((logStar n + 1 : ℕ) : ℝ) + 1) = (logStar n : ℝ) + 2 := by push_cast; ring
  have e₂ : (((logStar n + 1 : ℕ) : ℝ) + 2) = (logStar n : ℝ) + 3 := by push_cast; ring
  rw [e₁, e₂] at h
  exact ⟨h, (le_chiRand_iff (by norm_num)).2 (chiRandAtLeast_of_probForcing (by norm_num) h)⟩

/-- **Corollary C.4 (high probability), `k ≥ 4`.** Let `n ≥ 3`, `ε ∈ (0,1)`, `L = lg* n`,
`Λ_n = ⌈ln((L+1) n²/ε)⌉` and `K = ⌊n^{2/(L(L+1))}/Λ_n⌋`.  There is a distribution over
`k`-colourable ordered graphs on `n` vertices on which every proper deterministic online
algorithm uses at least `K` colours with probability at least `1 - ε`.  In particular
`χ^rand_k(n) ≥ (1 - ε) K`. -/
theorem oblivious_high_prob_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing k n
      (⌊(n : ℝ) ^ ((2 : ℝ) / ((logStar n : ℝ) * ((logStar n : ℝ) + 1))) /
        (Lam n ε : ℝ)⌋₊ : ℝ) (1 - ε) ∧
    (1 - ε) * (⌊(n : ℝ) ^ ((2 : ℝ) / ((logStar n : ℝ) * ((logStar n : ℝ) + 1))) /
        (Lam n ε : ℝ)⌋₊ : ℝ) ≤ chiRand k n := by
  have hL := two_le_logStar hn
  have hmax : max 1 (logStar n - 1) = logStar n - 1 := by omega
  have hP := le_card_labelPoset_of_four_le hk n
  rw [hmax] at hP
  have h := probForcing_floor (k := k) (j := logStar n - 1) (by omega) hn (by omega) (by omega)
    hP hε0 hε1
  have e₁ : (((logStar n - 1 : ℕ) : ℝ) + 1) = (logStar n : ℝ) := by
    have : logStar n - 1 + 1 = logStar n := by omega
    exact_mod_cast this
  have e₂ : (((logStar n - 1 : ℕ) : ℝ) + 2) = (logStar n : ℝ) + 1 := by
    have : logStar n - 1 + 2 = logStar n + 1 := by omega
    exact_mod_cast this
  rw [e₁, e₂] at h
  exact ⟨h, (le_chiRand_iff (by omega)).2 (chiRandAtLeast_of_probForcing (by omega) h)⟩

end Obl

end OnlineColouring
