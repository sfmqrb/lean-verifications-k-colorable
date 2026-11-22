module

public import OnlineColouring.ExplTransfer

/-!
# The size of the randomized transfer (Appendix D.5)

The paragraph "Transfer for randomized algorithms" of Appendix D.5 continues: *Lower bounds
`n^c` or `2^{(log n)^c}` that hold with constant probability against every deterministic algorithm
also transfer from any `k' ≥ 3` to `k = 3`, with a smaller `c`.*  This rests on the size of the
transferred distribution, which the paper does not state.  This file bounds it, in analogy with
the count `N^{j+1} K^{j(j+1)/2}` in the proof of Theorem 1.4 (`transferSize_le_mul`).

With `N_i = trN … i` and `R_i = trR … i` (`R_0 = D`) as in `ExplTransfer.lean`:

* `trR_succ_le`: `R_{i+1} ≤ K L R_i` whenever `K ≥ 1` and `L ≥ 1` bounds the logarithm
  `ln(j N_i R_i/ε)` of step `i`.
* `trR_le_pow`, `trN_le_pow`: if `K ≥ 1` and `L ≥ 1` bounds the logarithms of the steps `< i₀`,
  then `R_i ≤ D (K L)^i` and `N_i ≤ N D^i (K L)^{i(i+1)/2}` for all `i ≤ i₀`.
* `trState_pos`: for `K ≥ 2`, `j, N, D ≥ 1` and `0 < ε < 1` all `N_i` and `R_i` are positive
  (the non-degenerate case: no block is empty).
* **`trN_le`**: in the non-degenerate case with `D ≤ N`, the final number of vertices `n = N_j`
  satisfies `n ≤ N D^j (K Λ)^{j(j+1)/2}` with `Λ = max(1, ln(j n²/ε))`; in particular
  `n ≤ N^{j+1} (K Λ)^{j(j+1)/2}` (`trN_le_pow_succ`; `trN_le_size` includes `j = 0`).  Compared
  with the deterministic transfer, the factor `K` between consecutive block sizes becomes `K Λ`,
  with `Λ = O(log(n/ε))`.

The asymptotic sentence quoted above is proved in `ExplTransferPoly.lean` from this bound.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset

variable {K j N D : ℕ} {ε : ℝ}

/-- One step: `R_{i+1} ≤ K L R_i` if `K ≥ 1` and `L ≥ 1` bounds the logarithm of the step. -/
theorem trR_succ_le (hK : 1 ≤ K) {L : ℝ} (hL : 1 ≤ L) (i : ℕ)
    (hlog : Real.log (j * trN K j ε N D i * trR K j ε N D i / ε) ≤ L) :
    (trR K j ε N D (i + 1) : ℝ) ≤ K * L * trR K j ε N D i := by
  rw [trR_succ]
  have hK' : (0 : ℝ) ≤ (K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hR0 : (0 : ℝ) ≤ trR K j ε N D i := Nat.cast_nonneg _
  rcases le_or_gt (((K : ℝ) - 1) * trR K j ε N D i *
      Real.log (j * trN K j ε N D i * trR K j ε N D i / ε)) 0 with hx0 | hx0
  · rw [Nat.ceil_eq_zero.2 hx0, Nat.cast_zero]
    positivity
  · have hceil := Nat.ceil_lt_add_one hx0.le
    have hxle : ((K : ℝ) - 1) * trR K j ε N D i *
        Real.log (j * trN K j ε N D i * trR K j ε N D i / ε) ≤
        ((K : ℝ) - 1) * trR K j ε N D i * L :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hK' hR0)
    have hRpos : 0 < trR K j ε N D i := by
      rcases Nat.eq_zero_or_pos (trR K j ε N D i) with h0 | h0
      · rw [h0] at hx0
        simp at hx0
      · exact h0
    have hR1 : (1 : ℝ) ≤ trR K j ε N D i := by exact_mod_cast hRpos
    have hRL : (1 : ℝ) ≤ trR K j ε N D i * L := one_le_mul_of_one_le_of_one_le hR1 hL
    have e : ((K : ℝ) - 1) * trR K j ε N D i * L + trR K j ε N D i * L =
        K * L * trR K j ε N D i := by ring
    linarith

/-- `R_i ≤ D (K L)^i`, if `K ≥ 1` and `L ≥ 1` bounds the logarithms of the steps `< i₀`. -/
theorem trR_le_pow (hK : 1 ≤ K) {L : ℝ} (hL : 1 ≤ L) {i₀ : ℕ}
    (hlog : ∀ i < i₀, Real.log (j * trN K j ε N D i * trR K j ε N D i / ε) ≤ L) :
    ∀ i ≤ i₀, (trR K j ε N D i : ℝ) ≤ D * (K * L) ^ i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [trR_zero, pow_zero, mul_one]
  | succ i ih =>
    intro hi
    have hKL : (0 : ℝ) ≤ K * L := by positivity
    calc (trR K j ε N D (i + 1) : ℝ) ≤ K * L * trR K j ε N D i :=
          trR_succ_le hK hL i (hlog i hi)
      _ ≤ K * L * (D * (K * L) ^ i) := mul_le_mul_of_nonneg_left (ih (by omega)) hKL
      _ = D * (K * L) ^ (i + 1) := by ring

/-- `N_i ≤ N D^i (K L)^{i(i+1)/2}`, if `K ≥ 1` and `L ≥ 1` bounds the logarithms of the steps
`< i₀`. -/
theorem trN_le_pow (hK : 1 ≤ K) {L : ℝ} (hL : 1 ≤ L) {i₀ : ℕ}
    (hlog : ∀ i < i₀, Real.log (j * trN K j ε N D i * trR K j ε N D i / ε) ≤ L) :
    ∀ i ≤ i₀, (trN K j ε N D i : ℝ) ≤ N * (D : ℝ) ^ i * (K * L) ^ (i * (i + 1) / 2) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [trN_zero]
  | succ i ih =>
    intro hi
    have hKL : (0 : ℝ) ≤ K * L := by positivity
    have hR := trR_le_pow hK hL hlog (i + 1) hi
    have hN := ih (by omega)
    have e : (i + 1) * (i + 1 + 1) / 2 = i * (i + 1) / 2 + (i + 1) :=
      succ_mul_succ_succ_div_two i
    rw [trN_succ, Nat.cast_mul]
    calc (trN K j ε N D i : ℝ) * trR K j ε N D (i + 1)
        ≤ (N * (D : ℝ) ^ i * (K * L) ^ (i * (i + 1) / 2)) * (D * (K * L) ^ (i + 1)) :=
          mul_le_mul hN hR (Nat.cast_nonneg _) (by positivity)
      _ = N * (D : ℝ) ^ (i + 1) * (K * L) ^ ((i + 1) * (i + 1 + 1) / 2) := by
          rw [e]
          ring

/-- **The non-degenerate case.** For `K ≥ 2`, `j, N, D ≥ 1` and `0 < ε < 1`, all sizes `N_i` and
all block sizes `R_i` are positive. -/
theorem trState_pos (hK : 2 ≤ K) (hj : 1 ≤ j) (hN : 1 ≤ N) (hD : 1 ≤ D) (hε0 : 0 < ε)
    (hε1 : ε < 1) : ∀ i, 1 ≤ trN K j ε N D i ∧ 1 ≤ trR K j ε N D i := by
  intro i
  induction i with
  | zero => exact ⟨hN, hD⟩
  | succ i ih =>
    obtain ⟨hNi, hRi⟩ := ih
    have hR : 1 ≤ trR K j ε N D (i + 1) := by
      rw [trR_succ]
      apply Nat.ceil_pos.2
      have hK' : (0 : ℝ) < (K : ℝ) - 1 := by
        have : (2 : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      have hRi' : (1 : ℝ) ≤ trR K j ε N D i := by exact_mod_cast hRi
      have hNi' : (1 : ℝ) ≤ trN K j ε N D i := by exact_mod_cast hNi
      have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have h1 : (1 : ℝ) ≤ j * trN K j ε N D i * trR K j ε N D i :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hj' hNi') hRi'
      have hlog : 0 < Real.log (j * trN K j ε N D i * trR K j ε N D i / ε) := by
        apply Real.log_pos
        rw [lt_div_iff₀ hε0, one_mul]
        linarith
      have hRpos : (0 : ℝ) < trR K j ε N D i := by linarith
      positivity
    exact ⟨by rw [trN_succ]; exact Nat.mul_pos hNi hR, hR⟩

section NonDegenerate

variable (hK : 2 ≤ K) (hj : 1 ≤ j) (hN : 1 ≤ N) (hD : 1 ≤ D) (hε0 : 0 < ε) (hε1 : ε < 1)

include hK hj hN hD hε0 hε1

theorem trN_mono {i i' : ℕ} (h : i ≤ i') : trN K j ε N D i ≤ trN K j ε N D i' := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ i' _ ih =>
    rw [trN_succ]
    exact ih.trans (Nat.le_mul_of_pos_right _ (trState_pos hK hj hN hD hε0 hε1 (i' + 1)).2)

theorem trR_le_trN (hDN : D ≤ N) (i : ℕ) : trR K j ε N D i ≤ trN K j ε N D i := by
  cases i with
  | zero => exact hDN
  | succ i =>
    rw [trN_succ]
    exact Nat.le_mul_of_pos_left _ (trState_pos hK hj hN hD hε0 hε1 i).1

/-- **The size of the randomized transfer.** In the non-degenerate case with `D ≤ N`, the final
number of vertices `n = N_j = N R_1 ⋯ R_j` satisfies
`n ≤ N D^j (K Λ)^{j(j+1)/2}` with `Λ = max(1, ln(j n²/ε))`. -/
theorem trN_le (hDN : D ≤ N) :
    (trN K j ε N D j : ℝ) ≤ N * (D : ℝ) ^ j *
      (K * max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) := by
  refine trN_le_pow (by omega) (le_max_left _ _) (fun i hi => ?_) j le_rfl
  refine le_trans ?_ (le_max_right _ _)
  obtain ⟨hNi, hRi⟩ := trState_pos hK hj hN hD hε0 hε1 i
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hNi' : (0 : ℝ) < trN K j ε N D i := by exact_mod_cast hNi
  have hRi' : (0 : ℝ) < trR K j ε N D i := by exact_mod_cast hRi
  have h1 : (trN K j ε N D i : ℝ) ≤ trN K j ε N D j := by
    exact_mod_cast trN_mono hK hj hN hD hε0 hε1 hi.le
  have h2 : (trR K j ε N D i : ℝ) ≤ trN K j ε N D j := by
    exact_mod_cast (trR_le_trN hK hj hN hD hε0 hε1 hDN i).trans
      (trN_mono hK hj hN hD hε0 hε1 hi.le)
  apply Real.log_le_log (by positivity)
  apply div_le_div_of_nonneg_right _ hε0.le
  rw [pow_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hRi'.le (hNi'.le.trans h1)) hj'.le

/-- In particular `n ≤ N^{j+1} (K Λ)^{j(j+1)/2}` with `Λ = max(1, ln(j n²/ε))`, the count
`N^{j+1} K^{j(j+1)/2}` of the proof of Theorem 1.4 with `K Λ` in place of `K`. -/
theorem trN_le_pow_succ (hDN : D ≤ N) :
    (trN K j ε N D j : ℝ) ≤ (N : ℝ) ^ (j + 1) *
      (K * max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) := by
  refine (trN_le hK hj hN hD hε0 hε1 hDN).trans ?_
  have hDN' : (D : ℝ) ≤ N := by exact_mod_cast hDN
  have hpow : (D : ℝ) ^ j ≤ (N : ℝ) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hDN' j
  have hKL : (0 : ℝ) ≤ (K * max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^
      (j * (j + 1) / 2) := by positivity
  rw [pow_succ' (N : ℝ) j]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hKL

end NonDegenerate

/-- The size bound for every `j ≥ 0` (for `j = 0` nothing is blown up and `n = N`):
`n ≤ N^{j+1} (K Λ)^{j(j+1)/2}` with `Λ = max(1, ln(j n²/ε))`, for `K ≥ 2`, `1 ≤ D ≤ N` and
`0 < ε < 1`. -/
theorem trN_le_size (hK : 2 ≤ K) (hD : 1 ≤ D) (hDN : D ≤ N) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (trN K j ε N D j : ℝ) ≤ (N : ℝ) ^ (j + 1) *
      (K * max 1 (Real.log (j * (trN K j ε N D j : ℝ) ^ 2 / ε))) ^ (j * (j + 1) / 2) := by
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    simp [trN_zero]
  · exact trN_le_pow_succ hK h0 (hD.trans hDN) hD hε0 hε1 hDN

end Expl

end OnlineColouring
