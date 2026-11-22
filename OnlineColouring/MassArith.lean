module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators

/-!
# The arithmetic of unused mass (Sections 8.2 and 8.3)

Real-number lemmas behind Lemma 8.3, Lemma 8.4 and inequality (8.1).  Nothing here mentions
graphs; the quantities `u_c(t)`, `a_t(c)`, `q_t(c)` of the paper are arbitrary real sequences `u`,
`f`, `q` indexed by colours `c` and phases `t = 0, …, M` (the paper numbers the phases from `1`).

* `mass_le_one_colour`, `mass_le_of_steps` (the light/heavy argument behind (8.1)): if
  `u_c(0) = 0`, `u_c(t+1) ≤ u_c(t) + f_t(c)`, `f_t(c) ≤ min(q_t(c), 1)` and `q_t(c) ≥ 0`, then
  for every threshold `b ≥ 0` and every finite set `C` of colours
  `∑_{c ∈ C} u_c(M) ≤ |C| (b + 1) + ∑_{t < M} ∑_{c ∈ C, u_c(t) ≥ b} q_t(c)`.
* `final_mass`: `∑_{s < m} (2m - (m - s - 1)) / (2m) = (3m + 1) / 4`, the total unused mass at the
  end of the play for blocks of size `A = 2m` (Lemma 8.3).
* `prod_one_sub_le_exp`: `∏ (1 - w_i) ≤ exp(-∑ w_i)` for `w_i ≤ 1` (the last step of the proof of
  Lemma 8.4), and `prod_fin_ite`, a product over `Fin m` restricted to the indices below `t`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### The light/heavy argument -/

theorem mass_le_one_colour {M : ℕ} (u f q : ℕ → ℝ) {b : ℝ} (hu0 : u 0 = 0)
    (hstep : ∀ t < M, u (t + 1) ≤ u t + f t) (hfq : ∀ t < M, f t ≤ q t)
    (hf1 : ∀ t < M, f t ≤ 1) (hq0 : ∀ t < M, 0 ≤ q t) (hb : 0 ≤ b) :
    ∀ T ≤ M, u T ≤ (b + 1) + ∑ t ∈ range T, if b ≤ u t then q t else 0 := by
  have hnn : ∀ T ≤ M, 0 ≤ ∑ t ∈ range T, if b ≤ u t then q t else 0 := by
    intro T hT
    apply sum_nonneg
    intro t ht
    split_ifs
    · exact hq0 t (by have := mem_range.1 ht; omega)
    · exact le_rfl
  intro T
  induction T with
  | zero => intro _; simp [hu0]; linarith
  | succ T ih =>
    intro hT
    have hTM : T < M := by omega
    rw [sum_range_succ]
    by_cases hheavy : b ≤ u T
    · rw [ite_eq_left hheavy]
      have := hstep T hTM
      have := hfq T hTM
      have := ih (by omega)
      linarith
    · rw [ite_eq_right hheavy, add_zero]
      have h1 := hstep T hTM
      have h2 := hf1 T hTM
      have h3 := hnn T (by omega)
      push Not at hheavy
      linarith

/-- **The light/heavy argument.** -/
theorem mass_le_of_steps {C : Finset ℕ} {M : ℕ} (u f q : ℕ → ℕ → ℝ) {b : ℝ}
    (hu0 : ∀ c ∈ C, u c 0 = 0) (hstep : ∀ c ∈ C, ∀ t < M, u c (t + 1) ≤ u c t + f c t)
    (hfq : ∀ c ∈ C, ∀ t < M, f c t ≤ q c t) (hf1 : ∀ c ∈ C, ∀ t < M, f c t ≤ 1)
    (hq0 : ∀ c ∈ C, ∀ t < M, 0 ≤ q c t) (hb : 0 ≤ b) :
    ∑ c ∈ C, u c M ≤ C.card * (b + 1) + ∑ t ∈ range M, ∑ c ∈ C with b ≤ u c t, q c t := by
  calc ∑ c ∈ C, u c M
      ≤ ∑ c ∈ C, ((b + 1) + ∑ t ∈ range M, if b ≤ u c t then q c t else 0) :=
        sum_le_sum fun c hc => mass_le_one_colour (u c) (f c) (q c) (hu0 c hc) (hstep c hc)
          (hfq c hc) (hf1 c hc) (hq0 c hc) hb M le_rfl
    _ = C.card * (b + 1) + ∑ t ∈ range M, ∑ c ∈ C with b ≤ u c t, q c t := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_comm]
        congr 1
        apply sum_congr rfl
        intro t _
        rw [sum_filter]

/-! ### The final mass -/

/-- For `A = 2m`, the final mass is `(3m+1)/4`. -/
theorem final_mass {m : ℕ} (hm : 1 ≤ m) :
    ∑ s ∈ range m, ((2 * m - (m - s - 1) : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) = (3 * m + 1) / 4 := by
  have hsum : ∑ s ∈ range m, (2 * m - (m - s - 1) : ℕ) = m * (m + 1) + ∑ s ∈ range m, s := by
    rw [show m * (m + 1) = ∑ _s ∈ range m, (m + 1) by rw [sum_const, card_range, smul_eq_mul],
      ← sum_add_distrib]
    apply sum_congr rfl
    intro s hs
    have := mem_range.1 hs
    omega
  have hid := sum_range_id_mul_two m
  have hnat : 4 * ∑ s ∈ range m, (2 * m - (m - s - 1) : ℕ) = 2 * m * (3 * m + 1) := by
    rw [hsum, Nat.mul_add]
    have : 4 * ∑ s ∈ range m, s = 2 * (m * (m - 1)) := by rw [← hid]; ring
    rw [this]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [← sum_div, ← Nat.cast_sum]
  have hm' : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  rw [div_eq_div_iff hm'.ne' (by norm_num)]
  have := congrArg (fun x : ℕ => (x : ℝ)) hnat
  push_cast at this ⊢
  linarith

/-! ### Products -/

theorem prod_one_sub_le_exp {ι : Type*} (S : Finset ι) (w : ι → ℝ) (h1 : ∀ i ∈ S, w i ≤ 1) :
    ∏ i ∈ S, (1 - w i) ≤ Real.exp (-∑ i ∈ S, w i) := by
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod₀
  · intro i hi; linarith [h1 i hi]
  · intro i _; have := Real.add_one_le_exp (-w i); linarith

theorem prod_fin_ite {m t : ℕ} (ht : t ≤ m) (g : ℕ → ℝ) :
    ∏ s : Fin m, (if (s : ℕ) < t then g s else 1) = ∏ s ∈ range t, g s := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < t then g i else 1), ← prod_filter]
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  omega

end OnlineColouring
