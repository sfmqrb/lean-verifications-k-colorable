module

public import OnlineColouring.BlowTower
public import OnlineColouring.Det
public import OnlineColouring.TowerGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 1.2 (explicit deterministic bound)

For every `n ≥ 3` and `L = lg* n`:

* `chiDet_three_ge`: every `K ≥ 2` with `K^((L+2)(L+3)/2) ≤ n` satisfies `χ^det_3(n) ≥ K` (here
  `n ≥ 3` is not needed);
* `chiDet_ge_of_four_le`: for `k ≥ 4`, every `K ≥ 2` with `K^(L(L+1)/2) ≤ n` satisfies
  `χ^det_k(n) ≥ K`.

Since `⌊n^{1/e}⌋` is the largest `K` with `K^e ≤ n`, these are the floor bounds of the theorem;
the displayed forms are `floor_rpow_le_chiDet_three` and `floor_rpow_le_chiDet_of_four_le`:
`⌊n^{2/((L+2)(L+3))}⌋ ≤ χ^det_3(n)` and `⌊n^{2/(L(L+1))}⌋ ≤ χ^det_k(n)`.  For `3 ≤ n ≤ 2^65536`
the exponents `1/28` and `1/15` of the last sentence of the theorem are
`chiDetAtLeast_three_of_le_tow_five` and `chiDetAtLeast_of_four_le_of_le_tow_five` (in the form
`K ≥ 2`, `K^28 ≤ n → χ^det_3(n) ≥ K`; the floor forms are `Paper.floor_rpow_28_le_chiDet_three`
and `Paper.floor_rpow_15_le_chiDet_of_four_le` in `PaperStatements.lean`).  The sentence
`χ^det_k(n) ≥ n^{(2-o(1))/(lg* n)^2}` is in `Asymptotic.lean`.

The proof follows the paper: `K ≤ n` gives `lg* K ≤ L`, Corollary 5.7 gives `|P_j(k)| ≥ K` for
`j = lg* K + 1 ≤ L + 1` (`k = 3`) or `j = max(1, lg* K - 1) ≤ L - 1` (`k ≥ 4`)
(`exists_levels_three`, `exists_levels_of_four_le`), the adversary of Theorem 6.4
(`Blow.theorem_6_4`, in the form `Blow.NkLE_playSize`) uses at most `K^((j+1)(j+2)/2) ≤ n`
vertices, and Observation 4.3 (`Det.chiDetAtLeast_of_NkLE`: an adversary of size at most `n` gives
`χ^det_k(n) ≥ K`) concludes (`chiDetAtLeast_of_adversary`).
-/

@[expose] public section

namespace OnlineColouring

theorem two_le_logStar {n : ℕ} (hn : 3 ≤ n) : 2 ≤ logStar n := by
  by_contra h
  have h₁ : n ≤ tow 1 := logStar_le_iff.1 (by omega)
  simp [tow] at h₁
  omega

theorem logStar_mono {a b : ℕ} (h : a ≤ b) : logStar a ≤ logStar b :=
  logStar_le_iff.2 (h.trans (le_tow_logStar b))

/-- The choice of the number of levels for `k = 3` (proof of Theorem 1.2): if `K ≥ 2` and
`K^((L+2)(L+3)/2) ≤ n` with `L = lg* n`, then some `j ≥ 1` (in the proof, `j = lg* K + 1`)
satisfies `|P_j(3)| ≥ K` and `K^((j+1)(j+2)/2) ≤ n`. -/
theorem exists_levels_three {n K : ℕ} (hK : 2 ≤ K)
    (hKn : K ^ ((logStar n + 2) * (logStar n + 3) / 2) ≤ n) :
    ∃ j, 1 ≤ j ∧ K ≤ Fintype.card (LabelPoset 3 j) ∧ K ^ ((j + 1) * (j + 2) / 2) ≤ n := by
  set L := logStar n
  have he : (L + 2) * (L + 3) / 2 ≠ 0 := by
    have : 6 ≤ (L + 2) * (L + 3) := by nlinarith
    omega
  have hKle : K ≤ n := (Nat.le_self_pow he K).trans hKn
  have hLK : logStar K ≤ L := logStar_mono hKle
  refine ⟨logStar K + 1, by omega, le_card_labelPoset_three hK, ?_⟩
  refine le_trans (Nat.pow_le_pow_right (by omega) ?_) hKn
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul <;> omega

/-- The choice of the number of levels for `k ≥ 4` (proof of Theorem 1.2): if `n ≥ 3`, `K ≥ 2`
and `K^(L(L+1)/2) ≤ n` with `L = lg* n`, then some `j ≥ 1` (in the proof,
`j = max(1, lg* K - 1)`) satisfies `|P_j(k)| ≥ K` and `K^((j+1)(j+2)/2) ≤ n`. -/
theorem exists_levels_of_four_le {n k K : ℕ} (hn : 3 ≤ n) (hk : 4 ≤ k) (hK : 2 ≤ K)
    (hKn : K ^ (logStar n * (logStar n + 1) / 2) ≤ n) :
    ∃ j, 1 ≤ j ∧ K ≤ Fintype.card (LabelPoset k j) ∧ K ^ ((j + 1) * (j + 2) / 2) ≤ n := by
  have hL : 2 ≤ logStar n := two_le_logStar hn
  set L := logStar n
  have he : L * (L + 1) / 2 ≠ 0 := by
    have : 6 ≤ L * (L + 1) := by nlinarith
    omega
  have hKle : K ≤ n := (Nat.le_self_pow he K).trans hKn
  have hLK : logStar K ≤ L := logStar_mono hKle
  refine ⟨max 1 (logStar K - 1), le_max_left _ _, le_card_labelPoset_of_four_le hk K, ?_⟩
  refine le_trans (Nat.pow_le_pow_right (by omega) ?_) hKn
  have hj : max 1 (logStar K - 1) ≤ L - 1 := max_le (by omega) (by omega)
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul <;> omega

/-- **Theorem 6.4 with Observation 4.3.** If `k ≥ 1`, `K ≥ 2`, `|P_j(k)| ≥ K` and
`K^((j+1)(j+2)/2) ≤ n`, then `χ^det_k(n) ≥ K`: the adversary `Blow.tower K j` of Theorem 6.4 forces
`K` colours on `k`-colourable graphs with at most `(K-1) b_j ⋯ b_1 + 1 ≤ K^((j+1)(j+2)/2) ≤ n`
vertices, and Observation 4.3 turns an adversary of size at most `n` into a lower bound for
`χ^det_k(n)`. -/
theorem chiDetAtLeast_of_adversary {k K j n : ℕ} (hk : 1 ≤ k) (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) (hn : K ^ ((j + 1) * (j + 2) / 2) ≤ n) :
    ChiDetAtLeast k n K :=
  Det.chiDetAtLeast_of_NkLE hk ((Blow.NkLE_playSize hK hKj).mono ((playSize_le hK j).trans hn))

/-- **Theorem 1.2, `k = 3`.** For `L = lg* n`, every `K ≥ 2` with `K^((L+2)(L+3)/2) ≤ n`
satisfies `χ^det_3(n) ≥ K`.  (The paper's hypothesis `n ≥ 3` is not needed here: for `n ≤ 2` no
`K ≥ 2` qualifies.) -/
theorem chiDetAtLeast_three {n : ℕ} {K : ℕ} (hK : 2 ≤ K)
    (hKn : K ^ ((logStar n + 2) * (logStar n + 3) / 2) ≤ n) : ChiDetAtLeast 3 n K := by
  obtain ⟨j, -, hKj, hjn⟩ := exists_levels_three hK hKn
  exact chiDetAtLeast_of_adversary (by norm_num) hK hKj hjn

/-- **Theorem 1.2, `k ≥ 4`.** For `n ≥ 3` and `L = lg* n`, every `K ≥ 2` with `K^(L(L+1)/2) ≤ n`
satisfies `χ^det_k(n) ≥ K`. -/
theorem chiDetAtLeast_of_four_le {n k : ℕ} (hn : 3 ≤ n) (hk : 4 ≤ k) {K : ℕ} (hK : 2 ≤ K)
    (hKn : K ^ (logStar n * (logStar n + 1) / 2) ≤ n) : ChiDetAtLeast k n K := by
  obtain ⟨j, -, hKj, hjn⟩ := exists_levels_of_four_le hn hk hK hKn
  exact chiDetAtLeast_of_adversary (by omega) hK hKj hjn

/-- **Theorem 1.2, `k = 3`, with `χ^det` as a min–max.** -/
theorem chiDet_three_ge {n : ℕ} {K : ℕ} (hK : 2 ≤ K)
    (hKn : K ^ ((logStar n + 2) * (logStar n + 3) / 2) ≤ n) : K ≤ chiDet 3 n :=
  (le_chiDet_iff (by norm_num)).2 (chiDetAtLeast_three hK hKn)

/-- **Theorem 1.2, `k ≥ 4`, with `χ^det` as a min–max.** -/
theorem chiDet_ge_of_four_le {n k : ℕ} (hn : 3 ≤ n) (hk : 4 ≤ k) {K : ℕ} (hK : 2 ≤ K)
    (hKn : K ^ (logStar n * (logStar n + 1) / 2) ≤ n) : K ≤ chiDet k n :=
  (le_chiDet_iff (by omega)).2 (chiDetAtLeast_of_four_le hn hk hK hKn)

/-! ### The floor form -/

/-- If `e = c/2` with `c > 0` even and `K = ⌊n^{2/c}⌋`, then `K^e ≤ n`. -/
theorem floor_rpow_pow_le {n c : ℕ} (hc : 0 < c) (heven : Even c) :
    ⌊(n : ℝ) ^ ((2 : ℝ) / c)⌋₊ ^ (c / 2) ≤ n := by
  set e := c / 2
  have hce : c = 2 * e := (Nat.two_mul_div_two_of_even heven).symm
  have he : e ≠ 0 := by omega
  have hx : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / c) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp : (2 : ℝ) / c = ((e : ℕ) : ℝ)⁻¹ := by
    rw [hce]
    push_cast
    field_simp
  have h₁ : ((⌊(n : ℝ) ^ ((2 : ℝ) / c)⌋₊ : ℕ) : ℝ) ^ e ≤ ((n : ℝ) ^ ((2 : ℝ) / c)) ^ e :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hx) e
  have h₂ : ((n : ℝ) ^ ((2 : ℝ) / c)) ^ e = n := by
    rw [hexp, Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) he]
  exact_mod_cast h₁.trans_eq h₂

/-- **Theorem 1.2, `k = 3`, floor form:** `χ^det_3(n) ≥ ⌊n^{2/((L+2)(L+3))}⌋` for `n ≥ 3`. -/
theorem floor_rpow_le_chiDet_three {n : ℕ} (hn : 3 ≤ n) :
    ⌊(n : ℝ) ^ ((2 : ℝ) / ((logStar n + 2) * (logStar n + 3)))⌋₊ ≤ chiDet 3 n := by
  set L := logStar n
  set K := ⌊(n : ℝ) ^ ((2 : ℝ) / ((L + 2) * (L + 3)))⌋₊
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have h1 : 1 ≤ chiDet 3 n := (le_chiDet_iff (by norm_num)).2 (chiDetAtLeast_one (by norm_num)
      (by omega))
    omega
  · apply chiDet_three_ge hK
    have heven : Even ((L + 2) * (L + 3)) := Nat.even_mul_succ_self (L + 2)
    have := floor_rpow_pow_le (n := n) (c := (L + 2) * (L + 3)) (by positivity) heven
    push_cast at this
    exact this

/-- **Theorem 1.2, `k ≥ 4`, floor form:** `χ^det_k(n) ≥ ⌊n^{2/(L(L+1))}⌋` for `n ≥ 3`. -/
theorem floor_rpow_le_chiDet_of_four_le {n k : ℕ} (hn : 3 ≤ n) (hk : 4 ≤ k) :
    ⌊(n : ℝ) ^ ((2 : ℝ) / (logStar n * (logStar n + 1)))⌋₊ ≤ chiDet k n := by
  have hL : 2 ≤ logStar n := two_le_logStar hn
  set L := logStar n
  set K := ⌊(n : ℝ) ^ ((2 : ℝ) / (L * (L + 1)))⌋₊
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have h1 : 1 ≤ chiDet k n := (le_chiDet_iff (by omega)).2 (chiDetAtLeast_one (by omega)
      (by omega))
    omega
  · apply chiDet_ge_of_four_le hn hk hK
    have heven : Even (L * (L + 1)) := Nat.even_mul_succ_self L
    have := floor_rpow_pow_le (n := n) (c := L * (L + 1)) (by positivity) heven
    push_cast at this
    exact this

/-! ### Explicit exponents for `n ≤ 2^65536` -/

theorem tow_five : tow 5 = 2 ^ 65536 := by rw [tow_succ, tow_four]

/-- For `n ≤ 2^65536` and `K ≥ 2`: `K^28 ≤ n` implies `χ^det_3(n) ≥ K`. -/
theorem chiDetAtLeast_three_of_le_tow_five {n K : ℕ} (hn' : n ≤ 2 ^ 65536)
    (hK : 2 ≤ K) (hKn : K ^ 28 ≤ n) : ChiDetAtLeast 3 n K := by
  have hL : logStar n ≤ 5 := logStar_le_iff.2 (tow_five ▸ hn')
  apply chiDetAtLeast_three hK
  refine le_trans (Nat.pow_le_pow_right (by omega) ?_) hKn
  have : (logStar n + 2) * (logStar n + 3) ≤ 7 * 8 := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- For `3 ≤ n ≤ 2^65536`, `k ≥ 4` and `K ≥ 2`: `K^15 ≤ n` implies `χ^det_k(n) ≥ K`. -/
theorem chiDetAtLeast_of_four_le_of_le_tow_five {n k K : ℕ} (hn : 3 ≤ n) (hn' : n ≤ 2 ^ 65536)
    (hk : 4 ≤ k) (hK : 2 ≤ K) (hKn : K ^ 15 ≤ n) : ChiDetAtLeast k n K := by
  have hL : logStar n ≤ 5 := logStar_le_iff.2 (tow_five ▸ hn')
  apply chiDetAtLeast_of_four_le hn hk hK
  refine le_trans (Nat.pow_le_pow_right (by omega) ?_) hKn
  have : logStar n * (logStar n + 1) ≤ 5 * 6 := Nat.mul_le_mul (by omega) (by omega)
  omega

end OnlineColouring
