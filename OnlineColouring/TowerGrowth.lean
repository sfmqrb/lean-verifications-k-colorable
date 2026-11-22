module

public import OnlineColouring.BaseFacts
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# Tower growth of the label posets

Lemma 5.6 (tower growth) and Corollary 5.7 (number of levels) of the paper.

* `tow 0 = 1`, `tow (i+1) = 2 ^ tow i`; `logStar x = min {i | tow i ≥ x}` (the paper's `lg* x`;
  paragraph "Iterated logarithms" of Section 4, with its examples `lg* 2 = 1`, `lg* 16 = 3`,
  `lg* 65536 = 4` in `logStar_examples`).
* The recursion stated after Lemma 5.5: `T 0 = 4`, `T (i+1) = choose (T i) ⌊T i / 2⌋`
  (`T_values`), and `tow (i+1) ≤ T i` (`tow_succ_le_T`), which is the inequality of the proof of
  Lemma 5.6.
* Lemma 5.6: `width(P_j(k)) ≥ tow(j+1)` for `k ≥ 4` (`hasAntichain_labelPoset_of_four_le`),
  `width(P_j(3)) ≥ tow(j-1)` for `j ≥ 2` (`hasAntichain_labelPoset_three`), and
  `|P_j(k)| ≤ tow(j + lg* k)` (`card_labelPoset_le_tow`).  The first two are stated with
  `HasAntichain`; with `width` they are `Paper.tow_le_width_labelPoset_of_four_le` and
  `Paper.tow_le_width_labelPoset_three` (`PaperStatements.lean`).
* Corollary 5.7: `le_card_labelPoset_of_four_le`, `le_card_labelPoset_three`,
  `logStar_sub_logStar_le`.
-/

@[expose] public section

namespace OnlineColouring

/-! ### The tower function and `lg*` -/

/-- The tower function: `tow 0 = 1`, `tow (i + 1) = 2 ^ tow i`. -/
def tow : ℕ → ℕ
  | 0 => 1
  | i + 1 => 2 ^ tow i

@[simp] theorem tow_zero : tow 0 = 1 := rfl

theorem tow_succ (i : ℕ) : tow (i + 1) = 2 ^ tow i := rfl

theorem tow_lt_tow_succ (i : ℕ) : tow i < tow (i + 1) := Nat.lt_two_pow_self

theorem tow_strictMono : StrictMono tow := strictMono_nat_of_lt_succ tow_lt_tow_succ

theorem tow_mono : Monotone tow := tow_strictMono.monotone

theorem lt_tow (i : ℕ) : i < tow i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := tow_lt_tow_succ i
    omega

theorem exists_le_tow (x : ℕ) : ∃ i, x ≤ tow i := ⟨x, (lt_tow x).le⟩

/-- `lg* x = min {i ≥ 0 | tow i ≥ x}`. -/
def logStar (x : ℕ) : ℕ := Nat.find (exists_le_tow x)

theorem le_tow_logStar (x : ℕ) : x ≤ tow (logStar x) := Nat.find_spec (exists_le_tow x)

theorem logStar_le_iff {x i : ℕ} : logStar x ≤ i ↔ x ≤ tow i :=
  ⟨fun h => (le_tow_logStar x).trans (tow_mono h), fun h => Nat.find_min' _ h⟩

theorem lt_tow_of_lt_logStar {x i : ℕ} (h : i < logStar x) : tow i < x := by
  by_contra h'
  exact absurd (logStar_le_iff.2 (not_lt.1 h')) (not_le.2 h)

theorem tow_four : tow 4 = 65536 := by norm_num [tow]

/-- The values quoted in Section 4: `lg* 2 = 1`, `lg* 16 = 3`, `lg* 65536 = 4`. -/
theorem logStar_examples : logStar 2 = 1 ∧ logStar 16 = 3 ∧ logStar 65536 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold logStar <;> rw [Nat.find_eq_iff] <;>
    refine ⟨by norm_num [tow], fun n hn => ?_⟩ <;> interval_cases n <;> norm_num [tow]

/-! ### The recursion `T` -/

/-- `T 0 = 4`, `T (i + 1) = choose (T i) ⌊T i / 2⌋`; the values are `4, 6, 20, 184756, …`. -/
def T : ℕ → ℕ
  | 0 => 4
  | i + 1 => (T i).choose (T i / 2)

theorem T_succ (i : ℕ) : T (i + 1) = (T i).choose (T i / 2) := rfl

theorem T_values : T 0 = 4 ∧ T 1 = 6 ∧ T 2 = 20 ∧ T 3 = 184756 := by
  have h1 : T 1 = 6 := by rfl
  have h2 : T 2 = 20 := by rw [T_succ, h1]; rfl
  have h3 : T 3 = 184756 := by
    rw [T_succ, h2]
    norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  exact ⟨rfl, h1, h2, h3⟩

/-- `w ↦ choose w ⌊w/2⌋` is monotone. -/
theorem choose_half_mono : Monotone fun w : ℕ => w.choose (w / 2) := by
  refine monotone_nat_of_le_succ fun w => ?_
  calc w.choose (w / 2) ≤ (w + 1).choose (w / 2) := Nat.choose_le_choose _ (Nat.le_succ w)
    _ ≤ (w + 1).choose ((w + 1) / 2) := Nat.choose_le_middle _ _

/-- `2^w ≤ (w + 1) · choose w ⌊w/2⌋`, i.e. `choose w ⌊w/2⌋ ≥ 2^w/(w+1)`. -/
theorem two_pow_le_succ_mul_choose_half (w : ℕ) : 2 ^ w ≤ (w + 1) * w.choose (w / 2) := by
  rw [← Nat.sum_range_choose]
  calc ∑ m ∈ Finset.range (w + 1), w.choose m
      ≤ (Finset.range (w + 1)).card • w.choose (w / 2) :=
        Finset.sum_le_card_nsmul _ _ _ fun m _ => Nat.choose_le_middle m w
    _ = (w + 1) * w.choose (w / 2) := by rw [Finset.card_range, smul_eq_mul]

theorem four_mul_add_two_le_two_pow {x : ℕ} (hx : 5 ≤ x) : 4 * x + 2 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ]
    omega

/-- For `i ≥ 3`, `T i ≥ 2 tow(i+1)`. -/
theorem two_mul_tow_le_T {i : ℕ} (hi : 3 ≤ i) : 2 * tow (i + 1) ≤ T i := by
  induction i, hi using Nat.le_induction with
  | base => rw [T_values.2.2.2, tow_four]; norm_num
  | succ i hi ih =>
    set x := tow (i + 1) with hx
    set y := tow (i + 1 + 1) with hy
    have hxy : y = 2 ^ x := rfl
    have hx5 : 5 ≤ x := by
      have : tow 4 ≤ tow (i + 1) := tow_mono (by omega)
      rw [tow_four] at this
      omega
    -- `T (i+1) = c(T i) ≥ c(2x)` and `(2x+1) c(2x) ≥ 2^{2x} = y²`.
    have h₁ : (2 * x).choose (2 * x / 2) ≤ T (i + 1) := by
      rw [T_succ]
      exact choose_half_mono ih
    have h₂ : y * y ≤ (2 * x + 1) * (2 * x).choose (2 * x / 2) := by
      have := two_pow_le_succ_mul_choose_half (2 * x)
      rw [hxy, ← pow_add, ← two_mul]
      exact this
    have h₃ : 4 * x + 2 ≤ y := hxy ▸ four_mul_add_two_le_two_pow hx5
    have h₄ : (2 * x + 1) * (2 * y) ≤ (2 * x + 1) * (2 * x).choose (2 * x / 2) := by
      calc (2 * x + 1) * (2 * y) = (4 * x + 2) * y := by ring
        _ ≤ y * y := Nat.mul_le_mul_right _ h₃
        _ ≤ _ := h₂
    exact (Nat.le_of_mul_le_mul_left h₄ (by omega)).trans h₁

/-- `T i ≥ tow (i + 1)` for all `i`. -/
theorem tow_succ_le_T (i : ℕ) : tow (i + 1) ≤ T i := by
  rcases lt_or_ge i 3 with hi | hi
  · obtain ⟨h0, h1, h2, -⟩ := T_values
    interval_cases i
    · rw [h0]; norm_num [tow]
    · rw [h1]; norm_num [tow]
    · rw [h2]; norm_num [tow]
  · exact le_trans (by omega) (two_mul_tow_le_T hi)

theorem one_le_T (i : ℕ) : 1 ≤ T i := by
  have := lt_tow (i + 1)
  have := tow_succ_le_T i
  omega

/-! ### Tower growth -/

/-- Iterating Lemma 5.5 (i): if `P_{j₀}(k)` has an antichain of size `4`, then
`P_{j₀+i}(k)` has an antichain of size `T i`. -/
theorem hasAntichain_labelPoset_T {k j₀ : ℕ} (h : HasAntichain (LabelPoset k j₀) 4) (i : ℕ) :
    HasAntichain (LabelPoset k (j₀ + i)) (T i) := by
  induction i with
  | zero => exact h
  | succ i ih => exact ih.labelPoset_succ (one_le_T i)

/-- **Lemma 5.6 (tower growth), `k ≥ 4`.** `width(P_j(k)) ≥ tow(j+1)`. -/
theorem hasAntichain_labelPoset_of_four_le {k : ℕ} (hk : 4 ≤ k) (j : ℕ) :
    HasAntichain (LabelPoset k j) (tow (j + 1)) := by
  have h4 : HasAntichain (LabelPoset k 0) 4 := (hasAntichain_labelPoset_zero k).mono hk
  have := hasAntichain_labelPoset_T h4 j
  rw [Nat.zero_add] at this
  exact this.mono (tow_succ_le_T j)

/-- **Lemma 5.6 (tower growth), `k = 3`.** `width(P_j(3)) ≥ tow(j-1)` for `j ≥ 2`. -/
theorem hasAntichain_labelPoset_three {j : ℕ} (hj : 2 ≤ j) :
    HasAntichain (LabelPoset 3 j) (tow (j - 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = 2 + i := ⟨j - 2, by omega⟩
  have := hasAntichain_labelPoset_T hasAntichain_labelPoset_three_two i
  refine this.mono ?_
  have e : 2 + i - 1 = i + 1 := by omega
  rw [e]
  exact tow_succ_le_T i

/-- **Lemma 5.6 (tower growth), upper bound.** `|P_j(k)| ≤ tow(j + lg* k)`. -/
theorem card_labelPoset_le_tow (k j : ℕ) :
    Fintype.card (LabelPoset k j) ≤ tow (j + logStar k) := by
  induction j with
  | zero =>
    rw [card_labelPoset_zero, Nat.zero_add]
    exact le_tow_logStar k
  | succ j ih =>
    have e : j + 1 + logStar k = (j + logStar k) + 1 := by omega
    rw [e, tow_succ]
    calc Fintype.card (LabelPoset k (j + 1)) ≤ 2 ^ Fintype.card (LabelPoset k j) - 1 :=
          card_labelPoset_succ_le k j
      _ ≤ 2 ^ Fintype.card (LabelPoset k j) := Nat.sub_le _ _
      _ ≤ 2 ^ tow (j + logStar k) := Nat.pow_le_pow_right (by norm_num) ih

/-! ### Number of levels -/

/-- **Corollary 5.7 (number of levels), `k ≥ 4`.** `|P_j(k)| ≥ K` for `j = max(1, lg* K - 1)`. -/
theorem le_card_labelPoset_of_four_le {k : ℕ} (hk : 4 ≤ k) (K : ℕ) :
    K ≤ Fintype.card (LabelPoset k (max 1 (logStar K - 1))) := by
  set j := max 1 (logStar K - 1)
  calc K ≤ tow (logStar K) := le_tow_logStar K
    _ ≤ tow (j + 1) := tow_mono (by omega)
    _ ≤ Fintype.card (LabelPoset k j) := (hasAntichain_labelPoset_of_four_le hk j).le_card

/-- **Corollary 5.7 (number of levels), `k = 3`.** `|P_j(3)| ≥ K` for `j = lg* K + 1`, `K ≥ 2`. -/
theorem le_card_labelPoset_three {K : ℕ} (hK : 2 ≤ K) :
    K ≤ Fintype.card (LabelPoset 3 (logStar K + 1)) := by
  have hpos : 1 ≤ logStar K := by
    by_contra h
    have h0 : logStar K = 0 := by omega
    have := le_tow_logStar K
    rw [h0, tow_zero] at this
    omega
  have hj : 2 ≤ logStar K + 1 := by omega
  calc K ≤ tow (logStar K) := le_tow_logStar K
    _ = tow (logStar K + 1 - 1) := by rw [Nat.add_sub_cancel]
    _ ≤ Fintype.card (LabelPoset 3 (logStar K + 1)) :=
        (hasAntichain_labelPoset_three hj).le_card

/-- **Corollary 5.7 (number of levels), converse.** `|P_j(k)| ≥ K` implies `j ≥ lg* K - lg* k`. -/
theorem logStar_sub_logStar_le {k j K : ℕ} (h : K ≤ Fintype.card (LabelPoset k j)) :
    logStar K - logStar k ≤ j := by
  have : logStar K ≤ j + logStar k := logStar_le_iff.2 (h.trans (card_labelPoset_le_tow k j))
  omega

end OnlineColouring
