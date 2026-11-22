module

public import OnlineColouring.Counting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The closed-form numbers of the paper

Every number below is the value of a formula that is written in the paper; the formula is
defined here as in the paper and evaluated by `decide +kernel`, `decide` or `norm_num`.
No `native_decide`.  Computed values that are not closed formulas are in other modules: the exact
values `N_k(c)` of Proposition B.4 in `CertNk.lean` (`Cert.prop_small`), the sizes of the label
posets in `NumValues.lean` (`Num.first_values`), and the one-level values `V(m)` of Appendix D.3
in `NumV10.lean` (`Num.V_table_full`).  The numbers of Section 8.4 are in `CertOvertake.lean`.

* **Table 2 (Section 6).**  The block sizes and the size bounds `(K-1) ∏ b_ℓ + 1` are
  `blockSize_table` and `playSize_table` in `Counting.lean`.  Here: the rounded values
  `1.03 · 10^19` and `1.99 · 10^13` (`playSize_81_3_approx`, `playSize_166_2_approx`), the
  last column `log(bound)/log K = 2.7, 5.5, 5.8, 10.0, 2.9, 6.0` to the stated precision
  (`logRatio_table`), and the two further bounds quoted in the text (Figure 1) and in Table 3,
  `22` and `426 394` (`playSize_more`).  That the `j` of each row is the least number of levels
  with `|P_j(k)| ≥ K` follows from the poset sizes of `Num.first_values`.
* **Table 3 (Appendix B).**  `refinedSize K j` is `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` with
  `D_j(t) = K - t`, `b_ℓ(t) = (K-t)(D_ℓ(t)-1)+1` if `D_ℓ(t) ≥ 1` and `1` otherwise (in the
  paper's formula `D_ℓ(t) = 0` occurs only for `t = K`, where the formula gives `1`), and
  `D_{ℓ-1}(t) = max_{t<t'≤K} b_ℓ(t')`; `refinedSize_table`: `12, 77, 14 484, 70 558, 3 591 642`.
  The adversary of Proposition B.1 and the same numbers for its sizes are in `StrRefTower.lean`
  (`Str.proposition_B_1`, `Str.refSize_table`).
* **After Corollary B.2 (Appendix B).**  `cheapTop K j`: the flow adversary on
  `K_{2K-2}` (`C(2K-2, 2) + 1` vertices, post-degree `2K - 4`) followed by `j - 1` reservation
  blow-ups with block sizes `b'_1 = (K-1)(D-1)+1`, `b'_{i+1} = (K-1)(b'_i - 1)+1`;
  `cheapTop_values`: `92 · 78 = 7 176`, `20 944`, `3 685`, and `2.66 · 10^9` ("about
  `2.7 · 10^9`") for `K = 18`, `j = 3`; `cheapTop_le`: these are at most `2^j K^{(j²+j+2)/2}`.
* **Theorem 1.2, last sentence.**  `(L+2)(L+3)/2 = 28` and `L(L+1)/2 = 15` for `L = 5`
  (`exponents_L5`).
* **Appendix D.3, table of `V(m)`.**  The rows `⌊m/2⌋ + 1` and the guess `⌊(2m+2)/3⌋`, which
  agrees with the table for `4 ≤ m ≤ 10` and is `8 ≠ 7` at `m = 11` (`oneLevel_rows`).  The row
  `V(m)` itself, `3, 4, 4, 5, 6, 6, 7, 7` for `m = 4, …, 11`, is proved in `NumV10.lean`
  (`Num.V_table_full`), and `V(11) ≠ ⌊(2 · 11 + 2)/3⌋` in `NumV.lean` (`Num.V_eleven_ne_guess`).
* **Appendix D.5, First-Fit row.**  `ffEscape K R = 1 - ∏_{d=1}^{K-1} surj(R, d)` with
  `surj(R, d) = ∑_{i=0}^{d} (-1)^i C(d,i) (1 - i/d)^R`; `ffEscape_four`:
  `1, 1, 5/6, 11/18, 91/216, 61/216, 485/2592, 2881/23328` for `K = 4`, `R = 1, …, 8`.  That
  this closed form is the probability that First-Fit uses at most `K - 1` colours is not
  formalized.
* **Appendix D.5, explicit instances.**  `condC K R δ` is the left side of condition (c) of
  Lemma C.2, `∑_m δ(m) (1 - 1/δ(m))^{⌈R/(K-1)⌉}`.  `instance_one`: `7 · 150 = 1050` and
  `1 - condC ≥ 0.915` for the post-degrees `6, 5, …, 0` of `K_7`; `instance_two`:
  `8 · 245 · 27 293 = 53 494 280`, the two failure terms add up to at most `0.094`, and
  `8 - 7 · 0.094 > 7.25`.
* **Appendix D.6, Figure 4.**  `liSize K β h` is the result of the recursion of the
  paper for Li's construction, where `β = ⌈log₂ K⌉` and `h` is least with `β^h ≥ K` (these two
  conditions are `IsLiParams`); `liSize_log2`: `⌊log₂ N⌋` for the values of `K` plotted in the
  figure.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

open Finset

/-! ### Table 2 -/

/-- The entry `1.03 · 10^19` of Table 2 (`K = 81`, `j = 3`). -/
theorem playSize_81_3_approx :
    1025 * 10 ^ 16 ≤ playSize 81 3 ∧ playSize 81 3 < 1035 * 10 ^ 16 := by decide +kernel

/-- The entry `1.99 · 10^13` of Table 2 (`K = 166`, `j = 2`). -/
theorem playSize_166_2_approx :
    1985 * 10 ^ 10 ≤ playSize 166 2 ∧ playSize 166 2 < 1995 * 10 ^ 10 := by decide +kernel

/-- The play with `22` vertices of Figure 1 (also an entry of Table 3) and the entry `426 394` of
Table 3. -/
theorem playSize_more : playSize 4 1 = 22 ∧ playSize 10 2 = 426394 := by decide +kernel

theorem log_ratio_bounds {K P a b : ℕ} (hK : 1 < K) (hP : 0 < P) (h1 : K ^ a ≤ P ^ 100)
    (h2 : P ^ 100 ≤ K ^ b) :
    (a : ℝ) / 100 ≤ Real.log P / Real.log K ∧ Real.log P / Real.log K ≤ (b : ℝ) / 100 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast hK)
  have e1 : (a : ℝ) * Real.log K ≤ 100 * Real.log P := by
    have h : (K : ℝ) ^ a ≤ (P : ℝ) ^ 100 := by exact_mod_cast h1
    have := Real.log_le_log (pow_pos hK0 a) h
    simpa [Real.log_pow] using this
  have e2 : 100 * Real.log P ≤ (b : ℝ) * Real.log K := by
    have h : (P : ℝ) ^ 100 ≤ (K : ℝ) ^ b := by exact_mod_cast h2
    have := Real.log_le_log (pow_pos hP0 100) h
    simpa [Real.log_pow] using this
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hlogK]
    linarith
  · rw [div_le_div_iff₀ hlogK (by norm_num)]
    linarith

/-- The last column of Table 2: `log(bound)/log K` is `2.7, 5.5, 5.8, 10.0, 2.9, 6.0`, each up to
`0.05`. -/
theorem logRatio_table :
    (2.65 ≤ Real.log (playSize 7 1) / Real.log 7 ∧
      Real.log (playSize 7 1) / Real.log 7 ≤ 2.75) ∧
    (5.45 ≤ Real.log (playSize 8 2) / Real.log 8 ∧
      Real.log (playSize 8 2) / Real.log 8 ≤ 5.55) ∧
    (5.75 ≤ Real.log (playSize 18 2) / Real.log 18 ∧
      Real.log (playSize 18 2) / Real.log 18 ≤ 5.85) ∧
    (9.95 ≤ Real.log (playSize 81 3) / Real.log 81 ∧
      Real.log (playSize 81 3) / Real.log 81 ≤ 10.05) ∧
    (2.85 ≤ Real.log (playSize 15 1) / Real.log 15 ∧
      Real.log (playSize 15 1) / Real.log 15 ≤ 2.95) ∧
    (5.95 ≤ Real.log (playSize 166 2) / Real.log 166 ∧
      Real.log (playSize 166 2) / Real.log 166 ≤ 6.05) := by
  have h1 := log_ratio_bounds (K := 7) (P := playSize 7 1) (a := 265) (b := 275)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h2 := log_ratio_bounds (K := 8) (P := playSize 8 2) (a := 545) (b := 555)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h3 := log_ratio_bounds (K := 18) (P := playSize 18 2) (a := 575) (b := 585)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h4 := log_ratio_bounds (K := 81) (P := playSize 81 3) (a := 995) (b := 1005)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h5 := log_ratio_bounds (K := 15) (P := playSize 15 1) (a := 285) (b := 295)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h6 := log_ratio_bounds (K := 166) (P := playSize 166 2) (a := 595) (b := 605)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num at h1 h2 h3 h4 h5 h6 ⊢
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ### Table 3 (Appendix B) -/

/-- `D_{j-d}(t)` for the refined adversary: `D_j(t) = K - t` and
`D_{ℓ-1}(t) = max_{t < t' ≤ K} b_ℓ(t')` (the maximum of the empty set is `0`), where
`b_ℓ(t) = (K - t)(D_ℓ(t) - 1) + 1` if `D_ℓ(t) ≥ 1` and `b_ℓ(t) = 1` otherwise. -/
def refD (K : ℕ) : ℕ → ℕ → ℕ
  | 0, t => K - t
  | d + 1, t => (Ioc t K).sup fun t' =>
      if 1 ≤ refD K d t' then (K - t') * (refD K d t' - 1) + 1 else 1

/-- `b_{j-d}(t)` for the refined adversary. -/
def refB (K d t : ℕ) : ℕ := if 1 ≤ refD K d t then (K - t) * (refD K d t - 1) + 1 else 1

/-- The bound `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` of Proposition B.1 (smaller blocks). -/
def refinedSize (K j : ℕ) : ℕ := ∑ t ∈ Icc 1 K, ∏ d ∈ range j, refB K d t

/-- The last column of Table 3. -/
theorem refinedSize_table :
    refinedSize 4 1 = 12 ∧ refinedSize 7 1 = 77 ∧ refinedSize 8 2 = 14484 ∧
      refinedSize 10 2 = 70558 ∧ refinedSize 18 2 = 3591642 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### The cheaper top (the numbers after Corollary B.2) -/

/-- The block sizes below the flow adversary: `b'_1 = (K-1)(D-1)+1` with `D = 2K - 4`, and
`b'_{i+1} = (K-1)(b'_i - 1) + 1`. -/
def cheapBlock (K : ℕ) : ℕ → ℕ
  | 0 => (K - 1) * (2 * K - 4 - 1) + 1
  | i + 1 => (K - 1) * (cheapBlock K i - 1) + 1

/-- The size of the adversary of Corollary B.2 (a cheaper top): `C(2K-2, 2) + 1` vertices of the
flow adversary, times the block sizes of `j - 1` reservation blow-ups. -/
def cheapTop (K j : ℕ) : ℕ := ((2 * K - 2).choose 2 + 1) * ∏ i ∈ range (j - 1), cheapBlock K i

/-- `8` colours with `92 · 78 = 7 176` vertices, `10` colours with `20 944`, `7` colours with
`3 685`, and `18` colours with about `2.7 · 10^9` vertices (`j = 3`). -/
theorem cheapTop_values :
    cheapTop 8 2 = 92 * 78 ∧ cheapTop 8 2 = 7176 ∧ cheapTop 10 2 = 20944 ∧ cheapTop 7 2 = 3685 ∧
      cheapTop 18 3 = 2658754560 ∧ 265 * 10 ^ 7 ≤ cheapTop 18 3 ∧
      cheapTop 18 3 < 275 * 10 ^ 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The instances obey the bound `2^j K^{(j²+j+2)/2}` of Corollary B.2. -/
theorem cheapTop_le :
    cheapTop 8 2 ≤ 2 ^ 2 * 8 ^ ((2 ^ 2 + 2 + 2) / 2) ∧
      cheapTop 10 2 ≤ 2 ^ 2 * 10 ^ ((2 ^ 2 + 2 + 2) / 2) ∧
      cheapTop 7 2 ≤ 2 ^ 2 * 7 ^ ((2 ^ 2 + 2 + 2) / 2) ∧
      cheapTop 18 3 ≤ 2 ^ 3 * 18 ^ ((3 ^ 2 + 3 + 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Theorem 1.2 -/

/-- For `L = 5` (the largest value of `lg* n` for `n ≤ 2^65536`) the exponents of Theorem 1.2 are
`28` and `15`. -/
theorem exponents_L5 : (5 + 2) * (5 + 3) / 2 = 28 ∧ 5 * (5 + 1) / 2 = 15 := by decide

/-! ### Appendix D.3: the rows of the table of `V(m)` that are formulas -/

/-- The row `⌊m/2⌋ + 1` of the table for `m = 4, …, 11`; and `⌊(2m+2)/3⌋` equals the row `V(m)`
of the table (`3, 4, 4, 5, 6, 6, 7`) for `m = 4, …, 10` but is `8`, not `7`, at `m = 11`.  The
row `V(m)` itself is `Num.V_table_full` (`NumV10.lean`). -/
theorem oneLevel_rows :
    ((List.range' 4 8).map fun m => m / 2 + 1) = [3, 3, 4, 4, 5, 5, 6, 6] ∧
      ((List.range' 4 7).map fun m => (2 * m + 2) / 3) = [3, 4, 4, 5, 6, 6, 7] ∧
      (2 * 11 + 2) / 3 = 8 := by decide

/-! ### Appendix D.5: First-Fit on one oblivious blow-up -/

/-- `surj(R, d) = ∑_{i=0}^{d} (-1)^i C(d, i) (1 - i/d)^R`, the probability that `R` uniform balls
hit all `d` bins. -/
def surj (R d : ℕ) : ℚ := ∑ i ∈ range (d + 1), (-1) ^ i * (d.choose i : ℚ) * (1 - (i : ℚ) / d) ^ R

/-- `1 - ∏_{d=1}^{K-1} surj(R, d)`, the paper's closed form for the probability that First-Fit
uses at most `K - 1` colours on one oblivious blow-up of `K_K` with blocks of `R` vertices. -/
def ffEscape (K R : ℕ) : ℚ := 1 - ∏ d ∈ Icc 1 (K - 1), surj R d

/-- The First-Fit row of the table of Appendix D.5 (`K = 4`, `R = 1, …, 8`). -/
theorem ffEscape_four :
    ffEscape 4 1 = 1 ∧ ffEscape 4 2 = 1 ∧ ffEscape 4 3 = 5 / 6 ∧ ffEscape 4 4 = 11 / 18 ∧
      ffEscape 4 5 = 91 / 216 ∧ ffEscape 4 6 = 61 / 216 ∧ ffEscape 4 7 = 485 / 2592 ∧
      ffEscape 4 8 = 2881 / 23328 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Appendix D.5: the explicit oblivious instances -/

/-- The left side of condition (c) of Lemma C.2 for a list `δ` of post-degrees:
`∑_m δ(m) (1 - 1/δ(m))^{⌈R/(K-1)⌉}` (a term with `δ(m) = 0` is `0`). -/
def condC (K R : ℕ) (δ : List ℕ) : ℚ :=
  (δ.map fun d : ℕ => (d : ℚ) * (1 - 1 / (d : ℚ)) ^ ⌈(R : ℚ) / ((K : ℚ) - 1)⌉₊).sum

/-- One oblivious blow-up of `K_7` with blocks of `150` vertices: `1 050` vertices, and
condition (c) holds with `ε = 0.085`, so every deterministic algorithm uses `7` colours with
probability at least `0.915`. -/
theorem instance_one :
    7 * 150 = 1050 ∧ condC 7 150 [6, 5, 4, 3, 2, 1, 0] ≤ 85 / 1000 ∧
      (915 : ℚ) / 1000 ≤ 1 - 85 / 1000 := by
  have hc : ⌈((150 : ℕ) : ℚ) / (((7 : ℕ) : ℚ) - 1)⌉₊ = 25 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  refine ⟨by norm_num, ?_, by norm_num⟩
  norm_num [condC, hc]

theorem condC_append (K R : ℕ) (δ δ' : List ℕ) :
    condC K R (δ ++ δ') = condC K R δ + condC K R δ' := by simp [condC]

theorem condC_replicate (K R n d : ℕ) : condC K R (List.replicate n d) =
    n * ((d : ℚ) * (1 - 1 / (d : ℚ)) ^ ⌈(R : ℚ) / ((K : ℚ) - 1)⌉₊) := by
  rw [condC, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- Two oblivious blow-ups of `K_8` with blocks of `245` and `27 293` vertices:
`53 494 280` vertices; condition (c) holds at the top level (post-degrees `7, …, 0`, blocks of
`245`) and at the lower level (`8 · 245` nodes, of which `7 · 245` have post-degree `245`, blocks
of `27 293`) with failure probabilities that add up to at most `0.094`, so every deterministic
algorithm uses `8` colours with probability at least `0.906`, and `8 - 7 · 0.094 > 7.25`. -/
theorem instance_two :
    8 * 245 * 27293 = 53494280 ∧
      condC 8 245 [7, 6, 5, 4, 3, 2, 1, 0] +
        condC 8 27293 (List.replicate (7 * 245) 245 ++ List.replicate 245 0) ≤ 94 / 1000 ∧
      (906 : ℚ) / 1000 ≤ 1 - 94 / 1000 ∧ (7.25 : ℚ) < 8 - 7 * (94 / 1000) := by
  have hc1 : ⌈((245 : ℕ) : ℚ) / (((8 : ℕ) : ℚ) - 1)⌉₊ = 35 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hc2 : ⌈((27293 : ℕ) : ℚ) / (((8 : ℕ) : ℚ) - 1)⌉₊ = 3899 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  have hx : ((244 : ℚ) / 245) ^ 3899 ≤ 11869 / 10 ^ 11 := by
    have hn : 244 ^ 3899 * 10 ^ 11 ≤ 11869 * 245 ^ 3899 := by decide +kernel
    have hq : (244 : ℚ) ^ 3899 * 10 ^ 11 ≤ 11869 * 245 ^ 3899 := by exact_mod_cast hn
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    exact hq
  rw [condC_append, condC_replicate, condC_replicate, hc2]
  norm_num [condC, hc1]
  generalize ((244 : ℚ) / 245) ^ 3899 = X at hx ⊢
  linarith

/-! ### Appendix D.6: the recursion for Li's construction -/

/-- The parameters of the recursion: `β = ⌈log₂ K⌉` and `h` is the least integer with
`β^h ≥ K`. -/
def IsLiParams (K β h : ℕ) : Prop :=
  2 ^ (β - 1) < K ∧ K ≤ 2 ^ β ∧ β ^ (h - 1) < K ∧ K ≤ β ^ h

instance (K β h : ℕ) : Decidable (IsLiParams K β h) := by
  unfold IsLiParams
  infer_instance

/-- The thresholds `t_i = β^i` for `i < h` and `t_h = K`. -/
def liT (K β h i : ℕ) : ℕ := if i < h then β ^ i else K

/-- One step of the recursion, with `t = t_i` and `q = t_{i+1}`:
`j = ⌈(2q - t)/⌈t/2⌉⌉`, `B = K(2^{j+1} - 1)`, `R = K q D`, `N ← N R B`, `D ← R B + B - 1`.
The state is the pair `(N, D)`; `⌈a/b⌉` is written `(a + (b - 1)) / b` and `⌈t/2⌉` is
`(t + 1) / 2`. -/
def liStep (K t q : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  let j := (2 * q - t + ((t + 1) / 2 - 1)) / ((t + 1) / 2)
  let B := K * (2 ^ (j + 1) - 1)
  let R := K * q * s.2
  (s.1 * R * B, R * B + B - 1)

/-- The state after the steps `i = h - 1, …, h - r`, starting from `(N, D) = (1, 1)`. -/
def liState (K β h : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | r + 1 => liStep K (liT K β h (h - 1 - r)) (liT K β h (h - r)) (liState K β h r)

/-- The final `N` of the recursion (the number plotted in Figure 4). -/
def liSize (K β h : ℕ) : ℕ := (liState K β h h).1

/-- `2^a ≤ N < 2^{a+1}`, that is, `⌊log₂ N⌋ = a`. -/
def LiLog (K β h a : ℕ) : Prop :=
  IsLiParams K β h ∧ 2 ^ a ≤ liSize K β h ∧ liSize K β h < 2 ^ (a + 1)

instance (K β h a : ℕ) : Decidable (LiLog K β h a) := by
  unfold LiLog
  infer_instance

/-- The values of `⌊log₂ N⌋` for the values of `K` plotted in Figure 4.  The figure plots
`log₂ N = 27.6, 35.0, 36.1, 47.6, 72.0, 199.7, 381.1, 1039.0, 1719.8, 5180.0, 26053.0, 84798.6`
(for `K = 2^64` the value is just below `26053`). -/
theorem liSize_log2 :
    LiLog 3 2 2 27 ∧ LiLog 4 2 2 34 ∧ LiLog 5 3 2 36 ∧ LiLog 8 3 2 47 ∧ LiLog 16 4 2 71 ∧
      LiLog 100 7 3 199 ∧ LiLog 1000 10 3 381 ∧ LiLog 65536 16 4 1039 ∧
      LiLog 1048583 21 5 1719 ∧ LiLog (2 ^ 32) 32 7 5179 ∧ LiLog (2 ^ 64) 64 11 26052 ∧
      LiLog (2 ^ 100) 100 16 84798 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Cert

end OnlineColouring
