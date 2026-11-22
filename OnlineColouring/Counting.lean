module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The vertex count of the iterated reservation adversary

Theorem 6.4 (the iterated reservation adversary), the inequality of the statement and the
paragraph "Counting" of the proof: with block sizes `b_ℓ = (K-1)^{j-ℓ+1} (K-2) + 1` for
`1 ≤ ℓ ≤ j`,

  `(K - 1) * ∏_{ℓ=1}^{j} b_ℓ + 1 ≤ K ^ ((j + 1) (j + 2) / 2)`   (`playSize_le`).

We also check the recursion `b_j = (K-1)(K-2)+1`, `b_{ℓ-1} = (K-1)(b_ℓ - 1) + 1`
(`blockSize_top`, `blockSize_pred`) and the block sizes and the size bounds `(K-1) ∏ b_ℓ + 1` of
Table 2 (`blockSize_table`, `playSize_table`).  The two entries of Table 2 that the paper prints in
rounded form and its last column are in `CertNumbers.lean`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-- The size `b_ℓ = (K-1)^{j-ℓ+1} (K-2) + 1` of the blocks of the nodes of level `ℓ` when `j`
blow-ups are stacked under `K_K`. -/
def blockSize (K j ℓ : ℕ) : ℕ := (K - 1) ^ (j - ℓ + 1) * (K - 2) + 1

/-- The size bound of the adversary of Theorem 6.4: every play has at most
`(K-1) ∏_{ℓ=1}^{j} b_ℓ + 1` vertices. -/
def playSize (K j : ℕ) : ℕ := (K - 1) * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ + 1

/-- The blocks of the top vertices: `b_j = (K-1)(K-2)+1`. -/
theorem blockSize_top (K j : ℕ) : blockSize K j j = (K - 1) * (K - 2) + 1 := by
  simp [blockSize]

/-- The recursion `b_{ℓ-1} = (K-1)(b_ℓ - 1) + 1` (each blow-up uses `D = ` the previous block
size, so `R = (K-1)(D-1)+1`). -/
theorem blockSize_pred (K j ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓj : ℓ ≤ j) :
    blockSize K j (ℓ - 1) = (K - 1) * (blockSize K j ℓ - 1) + 1 := by
  have e : j - (ℓ - 1) + 1 = (j - ℓ + 1) + 1 := by omega
  simp only [blockSize, e, Nat.add_sub_cancel, pow_succ]
  ring

/-- `b_ℓ ≤ K^{j-ℓ+2}`, written for `c_k = (K-1)^{k+1}(K-2)+1 ≤ K^{k+2}`. -/
theorem block_le_pow {K : ℕ} (hK : 2 ≤ K) (k : ℕ) :
    (K - 1) ^ (k + 1) * (K - 2) + 1 ≤ K ^ (k + 2) := by
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 2 := ⟨K - 2, by omega⟩
  have h₁ : (L + 2 - 1) ^ (k + 1) ≤ (L + 2) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
  have h₂ : 1 ≤ (L + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have e : L + 2 - 2 = L := by omega
  rw [e, pow_succ (L + 2) (k + 1)]
  nlinarith [Nat.mul_le_mul_right L h₁]

/-- Reindexing: `∏_{ℓ=1}^{j} b_ℓ = ∏_{k<j} ((K-1)^{k+1}(K-2)+1)`. -/
theorem prod_blockSize_eq (K j : ℕ) :
    ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ = ∏ k ∈ range j, ((K - 1) ^ (k + 1) * (K - 2) + 1) := by
  symm
  refine Finset.prod_nbij' (fun k => j - k) (fun ℓ => j - ℓ) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range, mem_Icc] at hk ⊢
    omega
  · intro ℓ hℓ
    simp only [mem_range, mem_Icc] at hℓ ⊢
    omega
  · intro k hk
    simp only [mem_range] at hk
    omega
  · intro ℓ hℓ
    simp only [mem_Icc] at hℓ
    omega
  · intro k hk
    simp only [mem_range] at hk
    have e : j - (j - k) = k := by omega
    simp only [blockSize, e]

theorem prod_block_le {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∏ k ∈ range j, ((K - 1) ^ (k + 1) * (K - 2) + 1) ≤ K ^ (j * (j + 3) / 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ]
    have e : (j + 1) * (j + 1 + 3) / 2 = j * (j + 3) / 2 + (j + 2) := by
      have : (j + 1) * (j + 1 + 3) = j * (j + 3) + 2 * (j + 2) := by ring
      rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
    calc (∏ k ∈ range j, ((K - 1) ^ (k + 1) * (K - 2) + 1)) * ((K - 1) ^ (j + 1) * (K - 2) + 1)
        ≤ K ^ (j * (j + 3) / 2) * K ^ (j + 2) := Nat.mul_le_mul ih (block_le_pow hK j)
      _ = K ^ ((j + 1) * (j + 1 + 3) / 2) := by rw [← pow_add, e]

/-- **Theorem 6.4 (the iterated reservation adversary), counting.** For `K ≥ 2` and every `j`,
`(K-1) ∏_{ℓ=1}^{j} b_ℓ + 1 ≤ K^{(j+1)(j+2)/2}`. -/
theorem playSize_le {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : playSize K j ≤ K ^ ((j + 1) * (j + 2) / 2) := by
  unfold playSize
  rw [prod_blockSize_eq]
  set X := ∏ k ∈ range j, ((K - 1) ^ (k + 1) * (K - 2) + 1)
  have hX1 : 1 ≤ X := by
    apply Nat.one_le_iff_ne_zero.2
    rw [Finset.prod_ne_zero_iff]
    intro k _
    omega
  have hX : X ≤ K ^ (j * (j + 3) / 2) := prod_block_le hK j
  have e : (j + 1) * (j + 2) / 2 = j * (j + 3) / 2 + 1 := by
    have : (j + 1) * (j + 2) = j * (j + 3) + 2 * 1 := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
  -- `(K-1) X + 1 ≤ K X ≤ K · K^{j(j+3)/2}`
  have h₁ : (K - 1) * X + 1 ≤ K * X := by
    have hK' : K = (K - 1) + 1 := by omega
    calc (K - 1) * X + 1 ≤ (K - 1) * X + X := Nat.add_le_add_left hX1 _
      _ = ((K - 1) + 1) * X := by ring
      _ = K * X := by rw [← hK']
  calc (K - 1) * X + 1 ≤ K * X := h₁
    _ ≤ K * K ^ (j * (j + 3) / 2) := Nat.mul_le_mul_left _ hX
    _ = K ^ ((j + 1) * (j + 2) / 2) := by rw [e, pow_succ, Nat.mul_comm]

/-- The size bounds of Table 2 (`k = 3`: `K = 7, 8, 18, 81`; `k = 4`: `K = 15, 166`), exactly.
The paper prints those for `K = 81` and `K = 166` as `1.03 · 10^19` and `1.99 · 10^13`. -/
theorem playSize_table :
    playSize 7 1 = 187 ∧ playSize 8 2 = 88796 ∧ playSize 18 2 = 21464626 ∧
    playSize 15 1 = 2563 ∧ playSize 81 3 = 10341433999400953681 ∧
    playSize 166 2 = 19936073183566 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The block sizes `b_j, …, b_1` of Table 2. -/
theorem blockSize_table :
    (blockSize 7 1 1 = 31) ∧ (blockSize 8 2 2 = 43 ∧ blockSize 8 2 1 = 295) ∧
    (blockSize 18 2 2 = 273 ∧ blockSize 18 2 1 = 4625) ∧
    (blockSize 81 3 3 = 6321 ∧ blockSize 81 3 2 = 505601 ∧ blockSize 81 3 1 = 40448001) ∧
    (blockSize 15 1 1 = 183) ∧ (blockSize 166 2 2 = 27061 ∧ blockSize 166 2 1 = 4464901) := by
  decide +kernel

end OnlineColouring
