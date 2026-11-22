module

public import OnlineColouring.TowerIndex

/-!
# The phases of a uniform tower

In the uniform tower of Section 8.1 (`m` top vertices, every node of positive level with `A`
children, `j` levels) the presented vertices are numbered `0, …, m A^j - 1` in arrival order, and
*phase* `t` consists of the presented vertices below the top vertex `v_t`.  (Phases and top
vertices are numbered from `0` here and from `1` in the paper.)

* `phase A j t`: the vertices of phase `t`, the interval `[t A^j, (t+1) A^j)`.
* `mem_phase`: `y` lies in phase `t` iff its root `y / A^j` is `t`; `card_phase`: a phase has
  `A^j` vertices; `phase_subset_range`: an earlier phase lies before the start of a later one.
* `card_phase_filter`: the vertices of phase `s` below the children of `v_s` outside a set
  `S ⊆ [A]` are `(A - |S|) A^(j-1)` in number.  With `S` the set of children that have served,
  this counts the eligible vertices of Section 8.2.
-/

@[expose] public section

namespace OnlineColouring

open Finset

variable {j A : ℕ}

/-- The leaves of the root (phase) `t`. -/
def phase (A j t : ℕ) : Finset ℕ := Ico (t * A ^ j) ((t + 1) * A ^ j)

theorem mem_phase (hA : 0 < A) {t y : ℕ} : y ∈ phase A j t ↔ y / A ^ j = t := by
  have hL : 0 < A ^ j := pow_pos hA j
  rw [phase, mem_Ico]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Nat.div_eq_of_lt_le h₁ h₂
  · rintro rfl
    refine ⟨Nat.div_mul_le_self y _, ?_⟩
    have := Nat.lt_div_mul_add (a := y) hL
    rw [Nat.add_mul, Nat.one_mul]
    exact this

theorem card_phase (A j t : ℕ) : (phase A j t).card = A ^ j := by
  rw [phase, Nat.card_Ico, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

theorem phase_subset_range {s t : ℕ} (hst : s < t) : phase A j s ⊆ range (t * A ^ j) := by
  intro y hy
  rw [phase, mem_Ico] at hy
  rw [mem_range]
  exact lt_of_lt_of_le hy.2 (Nat.mul_le_mul_right _ hst)

/-- The leaves of the root `s` below children outside `S ⊆ [A]`: `(A - |S|) A^(j-1)` of them. -/
theorem card_phase_filter (hA : 0 < A) (hj : 1 ≤ j) (s : ℕ) {S : Finset ℕ} (hS : S ⊆ range A) :
    ((phase A j s).filter fun y => (y / A ^ (j - 1)) % A ∉ S).card =
      (A - S.card) * A ^ (j - 1) := by
  set P := A ^ (j - 1)
  have hP : 0 < P := pow_pos hA _
  have hL : A ^ j = P * A := by
    rw [← pow_succ]; congr 1; omega
  have hcard : ((range A \ S) ×ˢ range P).card = (A - S.card) * P := by
    rw [card_product, card_sdiff_of_subset hS, card_range, card_range]
  rw [← hcard]
  apply card_nbij' (fun y => ((y / P) % A, y % P)) (fun p => (s * A + p.1) * P + p.2)
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    simp only [coe_product, coe_sdiff, coe_range, Set.mem_prod, Set.mem_sdiff, Set.mem_Iio]
    exact ⟨⟨Nat.mod_lt _ hA, hy.2⟩, Nat.mod_lt _ hP⟩
  · intro p hp
    simp only [coe_product, coe_sdiff, coe_range, Set.mem_prod, Set.mem_sdiff, Set.mem_Iio] at hp
    simp only [coe_filter, Set.mem_ofPred_eq]
    have h1 : ((s * A + p.1) * P + p.2) / P = s * A + p.1 := by
      rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hp.2, Nat.add_zero]
    refine ⟨(mem_phase hA).2 ?_, ?_⟩
    · rw [hL, ← Nat.div_div_eq_div_mul, h1, Nat.mul_comm, Nat.mul_add_div hA,
        Nat.div_eq_of_lt hp.1.1, Nat.add_zero]
    · rw [h1, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.1.1]
      exact hp.1.2
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    have hys : y / A ^ j = s := (mem_phase hA).1 hy.1
    have h2 : y / P / A = s := by rw [Nat.div_div_eq_div_mul, ← hL, hys]
    simp only
    conv_rhs => rw [← Nat.div_add_mod y P, ← Nat.div_add_mod (y / P) A, h2]
    ring
  · intro p hp
    simp only [coe_product, coe_sdiff, coe_range, Set.mem_prod, Set.mem_sdiff, Set.mem_Iio] at hp
    have h1 : ((s * A + p.1) * P + p.2) / P = s * A + p.1 := by
      rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hp.2, Nat.add_zero]
    simp only [h1]
    rw [Nat.mul_comm s A, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.1.1,
      Nat.mul_comm (A * s + p.1) P, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2]

end OnlineColouring
