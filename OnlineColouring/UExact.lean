module

public import OnlineColouring.UWiringE
public import OnlineColouring.MassArith
public import OnlineColouring.UniformBound
public import OnlineColouring.ProbForcing

/-!
# Theorem 8.5 (i) and the first statement of Corollary 8.6, for the random wiring `R_j(m)`

`UWiringE.lean` defines the random wiring `R_j(m)` of Construction 8.1: the uniform distribution
on `EΩ m j A` (for every pair `s < t`, a uniform unused child of `v_s` and an independent uniform
bijection for every node of level `≥ 2` below `v_t`, including `v_t`).  This file carries out the
analysis of Sections 8.2 and 8.3 for it.

* The quantities of the analysis: `uME alg ω c t` is the unused mass `u_c(t)`, `fME` is
  `a_t(c)`, `qME` is `q_t(c)`, `HME b alg ω t` is `H_t` for the threshold `b`, and `numColsE` is
  the number `C` of colours used.  Phases are numbered from `0`.
* The per-play inequality (8.1) (`perPlay_boundE`), from the light/heavy argument
  `mass_le_of_steps` and the final mass `final_mass` of `MassArith.lean`.
* The counting core of Lemma 8.4 (`card_bad_leE`; the lemma as stated is `Rjm.miss` in
  `RjmMass.lean`): for a leaf `y` of phase `t` and a colour `c`, at most a fraction
  `exp(-u_c(t))` of the values of the phase-`t` coordinate leave `y` without an earlier neighbour of
  colour `c`.  It rests on the counting lemma `card_mul_card_colour_le` of `UWiringE.lean` (each
  eligible leaf is the neighbour for at least a fraction `A^{-j}` of the values of the coordinate)
  and on independence across the earlier roots (`card_filter_pi_dep`).
* `sum_HME_le`: `E[H_t] ≤ m e^{-b}` for `b ≥ 1`, by averaging over the phase-`t` coordinate
  (`sum_mul_card_eq_sum_update_dep`).
* **Theorem 8.5 (i) for `R_j(m)`**: `avg_numCols_geE` (every proper deterministic algorithm uses
  at least `(2m+1)/(4(1+ln 4m))` colours in expectation) and `uniform_tower_randE`.
* **Corollary 8.6, first statement, for `R_j(m)`**: `uniform_tower_eps_probE` and
  `uniform_tower_eps_inputE` (at least `(2m+1)/(4(1+ln(4m/ε)))` colours with probability at least
  `1 - ε`), packaged as `uniform_tower_epsE`.
-/

@[expose] public section

namespace OnlineColouring

open Finset
open scoped ENNReal

/-! ### Generic facts for dependent products -/

/-- Averaging over one coordinate of a dependent product. -/
theorem sum_mul_card_eq_sum_update_dep {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (i : ι) (f : ((i : ι) → X i) → ℝ) :
    (∑ ω, f ω) * Fintype.card (X i) = ∑ ω, ∑ x : X i, f (Function.update ω i x) := by
  let e : ((i : ι) → X i) × X i ≃ ((i : ι) → X i) × X i :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp [Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by simp [Function.update_idem, Function.update_eq_self] }
  calc (∑ ω, f ω) * Fintype.card (X i) = ∑ p : ((i : ι) → X i) × X i, f p.1 := by
        rw [Fintype.sum_prod_type, sum_mul]
        simp [sum_const, card_univ, nsmul_eq_mul, mul_comm]
    _ = ∑ p : ((i : ι) → X i) × X i, f (e p).1 := (Equiv.sum_comp e (fun p => f p.1)).symm
    _ = ∑ ω, ∑ x, f (Function.update ω i x) := Fintype.sum_prod_type _

/-- Counting in a dependent product: the coordinates `s < t` are constrained independently. -/
theorem card_filter_pi_dep {m : ℕ} {Z : Fin m → Type*} [∀ s, Fintype (Z s)] (t : ℕ)
    (P : (s : Fin m) → Z s → Prop) [∀ s, DecidablePred (P s)] :
    (univ.filter fun X : (s : Fin m) → Z s => ∀ s : Fin m, (s : ℕ) < t → P s (X s)).card =
      ∏ s : Fin m, if (s : ℕ) < t then (univ.filter (P s)).card else Fintype.card (Z s) := by
  classical
  have : (univ.filter fun X : (s : Fin m) → Z s => ∀ s : Fin m, (s : ℕ) < t → P s (X s)) =
      Fintype.piFinset fun s : Fin m => if (s : ℕ) < t then univ.filter (P s) else univ := by
    ext X
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    apply forall_congr'
    intro s
    split_ifs with h <;> simp [h]
  rw [this, Fintype.card_piFinset]
  apply prod_congr rfl
  intro s _
  split_ifs <;> simp

/-! ### The quantities of the analysis -/

variable {m j A : ℕ}

/-- `u_c(t)`: the weight of the eligible leaves of colour `c` at the start of phase `t`. -/
noncomputable def uME (alg : OnlineAlg) (ω : EΩ m j A) (c t : ℕ) : ℝ :=
  ∑ s ∈ range t, (((eligE ω s t).filter fun y => uColE alg ω y = c).card : ℝ) / (A ^ j : ℕ)

/-- `a_t(c)`: the fraction of the leaves of phase `t` with colour `c`. -/
noncomputable def fME (alg : OnlineAlg) (ω : EΩ m j A) (c t : ℕ) : ℝ :=
  (((phase A j t).filter fun y => uColE alg ω y = c).card : ℝ) / (A ^ j : ℕ)

/-- `q_t(c)`: the fraction of the leaves of phase `t` without an earlier neighbour of colour
`c`. -/
noncomputable def qME (alg : OnlineAlg) (ω : EΩ m j A) (c t : ℕ) : ℝ :=
  (((phase A j t).filter fun y =>
    ∀ s < t, uColE alg ω (ueNb A (tauE ω) (phiE ω) j s y) ≠ c).card : ℝ) / (A ^ j : ℕ)

/-- The colours used before phase `t`. -/
noncomputable def colsBeforeE (alg : OnlineAlg) (ω : EΩ m j A) (t : ℕ) : Finset ℕ :=
  (range (t * A ^ j)).image (uColE alg ω)

/-- `H_t`: the sum of `q_t(c)` over the heavy colours (`u_c(t) ≥ b`) used before phase `t`. -/
noncomputable def HME (b : ℝ) (alg : OnlineAlg) (ω : EΩ m j A) (t : ℕ) : ℝ :=
  ∑ c ∈ (colsBeforeE alg ω t).filter (fun c => b ≤ uME alg ω c t), qME alg ω c t

/-- The number of colours used on the whole presented graph. -/
noncomputable def numColsE (alg : OnlineAlg) (ω : EΩ m j A) : ℕ :=
  ((range (m * A ^ j)).image (uColE alg ω)).card

variable {alg : OnlineAlg} {ω : EΩ m j A}

theorem eligE_mono {s t : ℕ} (hst : s < t) : eligE ω s (t + 1) ⊆ eligE ω s t := by
  intro y hy
  rw [eligE, mem_filter] at hy ⊢
  exact ⟨hy.1, fun h => hy.2 (usedTopE_mono ω s (by omega) h)⟩

theorem uME_succ_le (c t : ℕ) : uME alg ω c (t + 1) ≤ uME alg ω c t + fME alg ω c t := by
  unfold uME fME
  rw [sum_range_succ]
  apply add_le_add
  · apply sum_le_sum
    intro s hs
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast card_le_card (filter_subset_filter _ (eligE_mono (mem_range.1 hs)))
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast card_le_card (filter_subset_filter _ (eligE_subset (ω := ω) t (t + 1)))

/-- Properness: a leaf of colour `c` has no earlier neighbour of colour `c`. -/
theorem fME_le_qME (hA : 0 < A) (halg : alg.IsProper) (c t : ℕ) :
    fME alg ω c t ≤ qME alg ω c t := by
  unfold fME qME
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.2
  apply card_le_card
  intro y hy
  rw [mem_filter] at hy ⊢
  refine ⟨hy.1, fun s hs hcol => ?_⟩
  have hyt : y / A ^ j = t := (mem_phase hA).1 hy.1
  have hmem : ueNb A (tauE ω) (phiE ω) j s y ∈ uSeqE ω y := mem_ueSeq.2 ⟨s, by omega, rfl⟩
  have hlt := mem_range.1 (ueSeq_valid hA (tauE_lt ω hA) (phiE_lt ω hA) j y hmem)
  exact runCol_ne halg hmem hlt (hy.2.trans hcol.symm)

theorem fME_le_one (hA : 0 < A) (c t : ℕ) : fME alg ω c t ≤ 1 := by
  unfold fME
  have hL : (0 : ℝ) < (A ^ j : ℕ) := by exact_mod_cast pow_pos hA j
  rw [div_le_one hL]
  have := card_le_card (filter_subset (fun y => uColE alg ω y = c) (phase A j t))
  rw [card_phase] at this
  exact_mod_cast this

theorem qME_nonneg (c t : ℕ) : 0 ≤ qME alg ω c t :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem HME_nonneg (b : ℝ) (t : ℕ) : 0 ≤ HME b alg ω t :=
  sum_nonneg fun c _ => qME_nonneg c t

/-- A colour with positive unused mass at the start of phase `t` has been used before phase
`t`. -/
theorem mem_colsBeforeE_of_pos {c t : ℕ} (h : 0 < uME alg ω c t) : c ∈ colsBeforeE alg ω t := by
  unfold uME at h
  obtain ⟨s, hs, hcard⟩ : ∃ s ∈ range t,
      0 < ((eligE ω s t).filter fun y => uColE alg ω y = c).card := by
    by_contra h0
    push Not at h0
    have : ∑ s ∈ range t, (((eligE ω s t).filter fun y => uColE alg ω y = c).card : ℝ) /
        (A ^ j : ℕ) = 0 := by
      apply sum_eq_zero
      intro s hs
      rw [Nat.le_zero.1 (h0 s hs)]
      simp
    rw [this] at h
    exact lt_irrefl _ h
  obtain ⟨y, hy⟩ := card_pos.1 hcard
  rw [mem_filter] at hy
  exact mem_image.2 ⟨y, phase_subset_range (mem_range.1 hs) (eligE_subset (ω := ω) s t hy.1),
    hy.2⟩

theorem colsBeforeE_subset {t : ℕ} (ht : t ≤ m) :
    colsBeforeE alg ω t ⊆ (range (m * A ^ j)).image (uColE alg ω) :=
  image_subset_image (range_subset_range.2 (Nat.mul_le_mul_right _ ht))

/-- **The per-play inequality** (before computing the final mass). -/
theorem perPlayE (hA : 0 < A) (halg : alg.IsProper) {b : ℝ} (hb : 0 < b) :
    ∑ c ∈ (range (m * A ^ j)).image (uColE alg ω), uME alg ω c m ≤
      numColsE alg ω * (b + 1) + ∑ t ∈ range m, HME b alg ω t := by
  refine (mass_le_of_steps (uME alg ω) (fME alg ω) (qME alg ω) (fun c _ => by simp [uME])
    (fun c _ t _ => uME_succ_le c t) (fun c _ t _ => fME_le_qME hA halg c t)
    (fun c _ t _ => fME_le_one hA c t) (fun c _ t _ => qME_nonneg c t) hb.le).trans_eq ?_
  unfold numColsE HME
  congr 1
  apply sum_congr rfl
  intro t ht
  apply sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter]
  constructor
  · rintro ⟨-, hc⟩
    exact ⟨mem_colsBeforeE_of_pos (lt_of_lt_of_le hb hc), hc⟩
  · rintro ⟨hc, hb'⟩
    exact ⟨colsBeforeE_subset (mem_range.1 ht).le hc, hb'⟩

theorem card_eligE_final (hA : 0 < A) (hj : 1 ≤ j) {s : ℕ} (hs : s < m) :
    (eligE ω s m).card = (A - (m - s - 1)) * A ^ (j - 1) := by
  unfold eligE
  rw [card_phase_filter hA hj s (usedTopE_subset ω hs (by omega)), card_usedTopE]

/-- The total eligible mass at the end: `∑_c u_c(m) = ∑_{s<m} (A - (m-1-s)) / A`. -/
theorem sum_uME_final (hA : 0 < A) (hj : 1 ≤ j) :
    ∑ c ∈ (range (m * A ^ j)).image (uColE alg ω), uME alg ω c m =
      ∑ s ∈ range m, ((A - (m - s - 1) : ℕ) : ℝ) / A := by
  unfold uME
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  have hs' := mem_range.1 hs
  rw [← sum_div]
  have hfib := card_eq_sum_card_fiberwise (f := uColE alg ω) (s := eligE ω s m)
    (t := (range (m * A ^ j)).image (uColE alg ω))
    (fun y hy => mem_image_of_mem _ (phase_subset_range hs' (eligE_subset (ω := ω) s m hy)))
  rw [← Nat.cast_sum, ← hfib, card_eligE_final hA hj hs']
  have hL : ((A ^ j : ℕ) : ℝ) = ((A ^ (j - 1) : ℕ) : ℝ) * A := by
    have : A ^ j = A ^ (j - 1) * A := by rw [← pow_succ]; congr 1; omega
    rw [this]; push_cast; ring
  have hP : (0 : ℝ) < ((A ^ (j - 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hA _
  rw [hL, Nat.cast_mul]
  field_simp

/-- **The per-play inequality (8.1)** for `R_j(m)`. For `A = 2m`, every threshold `b > 0`, every
proper algorithm and every realization: `(3m+1)/4 ≤ C (b + 1) + ∑_{t<m} H_t`, where `C` is the
number of colours used. -/
theorem perPlay_boundE (hm : 1 ≤ m) (hj : 1 ≤ j) (halg : alg.IsProper) {b : ℝ} (hb : 0 < b)
    (ω : EΩ m j (2 * m)) :
    ((3 * m + 1) / 4 : ℝ) ≤ numColsE alg ω * (b + 1) + ∑ t ∈ range m, HME b alg ω t := by
  have hA : 0 < 2 * m := by omega
  have h := perPlayE (ω := ω) hA halg hb
  rw [sum_uME_final hA hj] at h
  have hfm := final_mass hm
  push_cast at hfm h ⊢
  linarith

/-! ### Lemma 8.4 and conditioning on the earlier phases -/

/-- **Lemma 8.4 for `R_j(m)`, counting form.** For a leaf `y` of phase `t < m` and a colour `c`, at
most a fraction `exp(-u_c(t))` of the values `X` of the phase-`t` coordinate leave `y` without an
earlier neighbour of colour `c`. -/
theorem card_bad_leE (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (ω : EΩ m j A) {t : ℕ}
    (htm : t < m) (c y : ℕ) :
    ((univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c).card : ℝ) ≤
      (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω c t) := by
  classical
  have hL : (0 : ℝ) < ((A ^ j : ℕ) : ℝ) := Nat.cast_pos.2 (pow_pos hA j)
  set w : ℕ → ℝ := fun s =>
    (((eligE ω s t).filter fun x => uColE alg ω x = c).card : ℝ) / ((A ^ j : ℕ) : ℝ) with hw
  have hw1 : ∀ s, w s ≤ 1 := by
    intro s
    rw [hw, div_le_one hL]
    have h1 := card_le_card (filter_subset (fun x => uColE alg ω x = c) (eligE ω s t))
    have h2 := card_le_card (eligE_subset (ω := ω) s t)
    rw [card_phase] at h2
    exact_mod_cast h1.trans h2
  have hone : ∀ s : Fin m, (s : ℕ) < t →
      ((univ.filter fun z : EZ A j t s => uColE alg ω (nbOfE ω s t y z) ≠ c).card : ℝ) ≤
        (Fintype.card (EZ A j t s) : ℝ) * (1 - w s) := by
    intro s hs
    have hsplit := card_filter_add_card_filter_not
      (s := (univ : Finset (EZ A j t s))) (fun z => uColE alg ω (nbOfE ω s t y z) = c)
    rw [card_univ] at hsplit
    have hcol := card_mul_card_colour_le ω hA hj (uColE alg ω) (y := y) hs htm c
    have hcol' : (Fintype.card (EZ A j t s) : ℝ) * w s ≤
        ((univ.filter fun z : EZ A j t s => uColE alg ω (nbOfE ω s t y z) = c).card : ℝ) := by
      rw [hw, mul_div_assoc', div_le_iff₀ hL]
      exact_mod_cast hcol
    have hsplit' :
        ((univ.filter fun z : EZ A j t s => uColE alg ω (nbOfE ω s t y z) = c).card : ℝ) +
        ((univ.filter fun z : EZ A j t s => ¬ (uColE alg ω (nbOfE ω s t y z) = c)).card : ℝ) =
        (Fintype.card (EZ A j t s) : ℝ) := by
      exact_mod_cast hsplit
    have hne : ((univ.filter fun z : EZ A j t s => uColE alg ω (nbOfE ω s t y z) ≠ c).card : ℝ) =
        ((univ.filter fun z : EZ A j t s => ¬ (uColE alg ω (nbOfE ω s t y z) = c)).card : ℝ) := rfl
    rw [hne]
    nlinarith
  have hcount := card_filter_pi_dep (Z := fun s : Fin m => EZ A j t s) t
    (fun (s : Fin m) z => uColE alg ω (nbOfE ω s t y z) ≠ c)
  rw [hcount]
  push_cast
  calc ∏ s : Fin m, (if (s : ℕ) < t then
          ((univ.filter fun z : EZ A j t s => uColE alg ω (nbOfE ω s t y z) ≠ c).card : ℝ)
        else (Fintype.card (EZ A j t s) : ℝ))
      ≤ ∏ s : Fin m, ((Fintype.card (EZ A j t s) : ℝ) * if (s : ℕ) < t then 1 - w s else 1) := by
        apply prod_le_prod₀
        · intro s _
          split_ifs <;> positivity
        · intro s _
          split_ifs with hs
          · exact hone s hs
          · rw [mul_one]
    _ = (∏ s : Fin m, (Fintype.card (EZ A j t s) : ℝ)) *
          ∏ s : Fin m, (if (s : ℕ) < t then 1 - w s else 1) := prod_mul_distrib
    _ = (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * ∏ s ∈ range t, (1 - w s) := by
        rw [Fintype.card_pi, Nat.cast_prod, prod_fin_ite htm.le (fun s => 1 - w s)]
    _ ≤ (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-∑ s ∈ range t, w s) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact prod_one_sub_le_exp _ _ (fun s _ => hw1 s)
    _ = (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω c t) := rfl

theorem uColE_update (alg : OnlineAlg) (ω : EΩ m j A) (t : Fin m) (X : (s : Fin m) → EZ A j t s)
    {x : ℕ} (hx : x < t * A ^ j) : uColE alg (Function.update ω t X) x = uColE alg ω x :=
  (uColE_congr alg (agreeBelowE_update ω t X) hx).symm

theorem uME_update (hA : 0 < A) (alg : OnlineAlg) (ω : EΩ m j A) (t : Fin m)
    (X : (s : Fin m) → EZ A j t s) (c : ℕ) :
    uME alg (Function.update ω t X) c t = uME alg ω c t := by
  unfold uME
  apply sum_congr rfl
  intro s hs
  rw [← eligE_congr (agreeBelowE_update ω t X) s]
  congr 3
  apply filter_congr
  intro y hy
  rw [uColE_update alg ω t X (lt_of_div_lt hA (by
    rw [(mem_phase hA).1 (eligE_subset (ω := ω) s t hy)]; exact mem_range.1 hs))]

theorem colsBeforeE_update (alg : OnlineAlg) (ω : EΩ m j A) (t : Fin m)
    (X : (s : Fin m) → EZ A j t s) :
    colsBeforeE alg (Function.update ω t X) t = colsBeforeE alg ω t := by
  unfold colsBeforeE
  apply image_congr
  intro x hx
  exact uColE_update alg ω t X (mem_range.1 hx)

theorem qME_update (hA : 0 < A) (alg : OnlineAlg) (ω : EΩ m j A) (t : Fin m)
    (X : (s : Fin m) → EZ A j t s) (c : ℕ) :
    qME alg (Function.update ω t X) c t =
      (((phase A j t).filter fun y =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c).card : ℝ) /
        (A ^ j : ℕ) := by
  unfold qME
  congr 3
  apply filter_congr
  intro y hy
  have hyt : y / A ^ j = t := (mem_phase hA).1 hy
  constructor
  · intro h s hs
    have := h s hs
    rwa [ueNb_updateE (ω := ω) t X s hyt, uColE_update alg ω t X (lt_of_div_lt hA (by
      rw [nbOfE_div hA]; exact hs))] at this
  · intro h s hs
    have hsm : s < m := lt_trans hs t.2
    have := h ⟨s, hsm⟩ hs
    rwa [← ueNb_updateE (ω := ω) t X ⟨s, hsm⟩ hyt, ← uColE_update alg ω t X (lt_of_div_lt hA (by
      rw [ueNb_updateE (ω := ω) t X ⟨s, hsm⟩ hyt, nbOfE_div hA]; exact hs))] at this

theorem sum_qME_update_le (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (ω : EΩ m j A)
    (t : Fin m) (c : ℕ) :
    ∑ X : (s : Fin m) → EZ A j t s, qME alg (Function.update ω t X) c t ≤
      (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω c t) := by
  classical
  have hL : (0 : ℝ) < ((A ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hA j
  simp only [qME_update hA alg ω t, ← sum_div]
  rw [div_le_iff₀ hL]
  have hswap : ∑ X : (s : Fin m) → EZ A j t s,
      (((phase A j t).filter fun y =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c).card : ℝ) =
      ∑ y ∈ phase A j t, ((univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c).card : ℝ) := by
    simp only [card_filter, Nat.cast_sum]
    rw [sum_comm]
  rw [hswap]
  calc ∑ y ∈ phase A j t, ((univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c).card : ℝ)
      ≤ ∑ _y ∈ phase A j t,
          (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-uME alg ω c t) :=
        sum_le_sum fun y _ => card_bad_leE hA hj alg ω t.2 c y
    _ = _ := by rw [sum_const, card_phase, nsmul_eq_mul]; ring

/-- At most `t` (hence at most `m`) colours are heavy, when `b ≥ 1`. -/
theorem card_heavy_leE (hA : 0 < A) (alg : OnlineAlg) (ω : EΩ m j A) {t : ℕ} {b : ℝ}
    (hb : 1 ≤ b) : (((colsBeforeE alg ω t).filter fun c => b ≤ uME alg ω c t).card : ℝ) ≤ t := by
  classical
  have hL : (0 : ℝ) < ((A ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hA j
  have huM0 : ∀ c, 0 ≤ uME alg ω c t := fun c =>
    sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htotal : ∑ c ∈ colsBeforeE alg ω t, uME alg ω c t ≤ t := by
    unfold uME
    rw [sum_comm]
    calc ∑ s ∈ range t, ∑ c ∈ colsBeforeE alg ω t,
          (((eligE ω s t).filter fun y => uColE alg ω y = c).card : ℝ) / (A ^ j : ℕ)
        = ∑ s ∈ range t, ((eligE ω s t).card : ℝ) / (A ^ j : ℕ) := by
          apply sum_congr rfl
          intro s hs
          rw [← sum_div, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise]
          intro y hy
          exact mem_image.2 ⟨y, phase_subset_range (mem_range.1 hs)
            (eligE_subset (ω := ω) s t hy), rfl⟩
      _ ≤ ∑ _s ∈ range t, (1 : ℝ) := by
          apply sum_le_sum
          intro s _
          rw [div_le_one hL]
          have := card_le_card (eligE_subset (ω := ω) s t)
          rw [card_phase] at this
          exact_mod_cast this
      _ = t := by simp
  calc (((colsBeforeE alg ω t).filter fun c => b ≤ uME alg ω c t).card : ℝ)
      ≤ ∑ c ∈ (colsBeforeE alg ω t).filter (fun c => b ≤ uME alg ω c t), uME alg ω c t := by
        rw [← nsmul_one, ← sum_const]
        apply sum_le_sum
        intro c hc
        exact hb.trans (mem_filter.1 hc).2
    _ ≤ ∑ c ∈ colsBeforeE alg ω t, uME alg ω c t :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun c _ _ => huM0 c
    _ ≤ t := htotal

/-- **`E[H_t | earlier phases] ≤ m e^{-b}`** for `b ≥ 1`, for `R_j(m)`. -/
theorem sum_HME_update_le (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (ω : EΩ m j A)
    (t : Fin m) {b : ℝ} (hb : 1 ≤ b) :
    ∑ X : (s : Fin m) → EZ A j t s, HME b alg (Function.update ω t X) t ≤
      (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * (m * Real.exp (-b)) := by
  classical
  set Hv := (colsBeforeE alg ω t).filter fun c => b ≤ uME alg ω c t
  have hHM : ∀ X, HME b alg (Function.update ω t X) t =
      ∑ c ∈ Hv, qME alg (Function.update ω t X) c t := by
    intro X
    unfold HME
    rw [colsBeforeE_update]
    simp only [uME_update hA alg ω t X]
    rfl
  simp only [hHM]
  rw [sum_comm]
  have hC : (0 : ℝ) ≤ (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) := Nat.cast_nonneg _
  calc ∑ c ∈ Hv, ∑ X : (s : Fin m) → EZ A j t s, qME alg (Function.update ω t X) c t
      ≤ ∑ c ∈ Hv, (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-b) := by
        apply sum_le_sum
        intro c hc
        refine (sum_qME_update_le hA hj alg ω t c).trans ?_
        apply mul_le_mul_of_nonneg_left _ hC
        exact Real.exp_le_exp.2 (neg_le_neg (mem_filter.1 hc).2)
    _ = (Hv.card : ℝ) * ((Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-b)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * ((Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * Real.exp (-b)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (card_heavy_leE hA alg ω hb).trans (by exact_mod_cast t.2.le)
    _ = _ := by ring

/-- **`E[H_t] ≤ m e^{-b}`** for `b ≥ 1`, for `R_j(m)`, in sum form. -/
theorem sum_HME_le (hmA : m ≤ A) (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (t : Fin m)
    {b : ℝ} (hb : 1 ≤ b) :
    ∑ ω : EΩ m j A, HME b alg ω t ≤ Fintype.card (EΩ m j A) * (m * Real.exp (-b)) := by
  classical
  have hne : Nonempty ((s : Fin m) → EZ A j t s) :=
    ⟨fun s => (⟨0, by have := t.2; omega⟩, fun _ _ => 1)⟩
  have hpos : (0 : ℝ) < (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) :=
    Nat.cast_pos.2 Fintype.card_pos
  have h := sum_mul_card_eq_sum_update_dep (X := fun t : Fin m => (s : Fin m) → EZ A j t s) t
    (fun ω : EΩ m j A => HME b alg ω t)
  have h2 : ∑ ω : EΩ m j A, ∑ X : (s : Fin m) → EZ A j t s, HME b alg (Function.update ω t X) t ≤
      ∑ _ω : EΩ m j A, (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * (m * Real.exp (-b)) :=
    sum_le_sum fun ω _ => sum_HME_update_le hA hj alg ω t hb
  rw [sum_const, card_univ, nsmul_eq_mul, ← h] at h2
  rw [show (Fintype.card (EΩ m j A) : ℝ) *
      ((Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) * (m * Real.exp (-b))) =
      (Fintype.card (EΩ m j A) : ℝ) * (m * Real.exp (-b)) *
        (Fintype.card ((s : Fin m) → EZ A j t s) : ℝ) by ring] at h2
  exact le_of_mul_le_mul_right h2 hpos

/-! ### Theorem 8.5 (i) for `R_j(m)` -/

/-- **Theorem 8.5 (i) for the random wiring `R_j(m)`.** On the uniform tower with `A = 2m`, every
proper deterministic algorithm uses on average at least `(2m+1)/(4(1+ln 4m))` colours. -/
theorem avg_numCols_geE (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg) (halg : alg.IsProper) :
    uniformBound m ≤
      (∑ ω : EΩ m j (2 * m), (numColsE alg ω : ℝ)) / Fintype.card (EΩ m j (2 * m)) := by
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  have hb : 1 ≤ Real.log (4 * m) := one_le_log_four_mul hm
  have hA : 0 < 2 * m := by omega
  have hQ : (0 : ℝ) < (Fintype.card (EΩ m j (2 * m)) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ _ω : EΩ m j (2 * m), ((3 * m + 1) / 4 : ℝ) ≤
      ∑ ω : EΩ m j (2 * m), ((numColsE alg ω : ℝ) * (Real.log (4 * m) + 1) +
        ∑ t ∈ range m, HME (Real.log (4 * m)) alg ω t) :=
    sum_le_sum fun ω _ => perPlay_boundE (m := m) (j := j) (by omega) hj halg (by linarith) ω
  rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, ← sum_mul, sum_comm] at hsum
  have hH : ∑ t ∈ range m, ∑ ω : EΩ m j (2 * m), HME (Real.log (4 * m)) alg ω t ≤
      m * ((Fintype.card (EΩ m j (2 * m)) : ℝ) / 4) := by
    calc _ ≤ ∑ _t ∈ range m, (Fintype.card (EΩ m j (2 * m)) : ℝ) / 4 := by
          apply sum_le_sum
          intro t ht
          have h := sum_HME_le (by omega) hA hj alg ⟨t, mem_range.1 ht⟩ hb
          rw [mul_exp_neg_log (by omega)] at h
          calc _ ≤ _ := h
            _ = _ := by ring
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  unfold uniformBound
  rw [div_le_div_iff₀ (by positivity) hQ]
  nlinarith

theorem numColsE_eq_cost (hA : 0 < A) (alg : OnlineAlg) (ω : EΩ m j A) :
    (uInputE hA ω).cost alg = numColsE alg ω := by
  unfold uInputE ueInput numColsE
  rw [OnlineInput.cost_ofSeq, utSize_eq]
  rfl

/-- **Theorem 8.5 (i) for `R_j(m)`, with Yao's principle.** For `j ≥ 1`, `m ≥ 2` and
`m ≤ |P_j(k)|`, every proper randomized algorithm has expected cost at least
`(2m+1)/(4(1+ln 4m))` on some `k`-colourable input on `m (2m)^j` vertices (`ChiRandAtLeast`); the
proof takes it in the support of `R_j(m)`. -/
theorem uniform_tower_randE {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) :
    ChiRandAtLeast k (m * (2 * m) ^ j) (uniformBound m) := by
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  have hA : 0 < 2 * m := by omega
  have hcol : ∀ ω : EΩ m j (2 * m), (uInputE hA ω).graph.Colorable k :=
    fun ω => uInputE_colorable ω hA hP
  have hk : 1 ≤ k := by
    obtain ⟨ω⟩ := (inferInstance : Nonempty (EΩ m j (2 * m)))
    exact one_le_of_colorable (by rw [utSize_eq]; exact Nat.mul_pos (by omega) (pow_pos hA j))
      (hcol ω)
  refine yao_uniform hk (utSize_eq (2 * m) m j).le (uInputE hA) hcol fun alg halg => ?_
  simp only [numColsE_eq_cost hA]
  exact avg_numCols_geE hm hj alg halg

/-! ### Corollary 8.6, first statement, for `R_j(m)` -/

/-- `H = ∑_{t<m} H_t` for the heavy-colour threshold `b`. -/
noncomputable def sumHMbE (b : ℝ) (alg : OnlineAlg) (ω : EΩ m j (2 * m)) : ℝ :=
  ∑ t ∈ range m, HME b alg ω t

theorem sumHMbE_nonneg (b : ℝ) (alg : OnlineAlg) (ω : EΩ m j (2 * m)) : 0 ≤ sumHMbE b alg ω :=
  sum_nonneg fun t _ => HME_nonneg b t

/-- **`E[H] ≤ εm/4`** for the threshold `ln(4m/ε)`, in sum form. -/
theorem sum_sumHMbE_le (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∑ ω : EΩ m j (2 * m), sumHMbE (Real.log (4 * m / ε)) alg ω ≤
      Fintype.card (EΩ m j (2 * m)) * (ε * m / 4) := by
  have hb : 1 ≤ Real.log (4 * m / ε) := one_le_log_four_mul_div hm hε0 hε1
  have hA : 0 < 2 * m := by omega
  unfold sumHMbE
  rw [sum_comm]
  calc ∑ t ∈ range m, ∑ ω : EΩ m j (2 * m), HME (Real.log (4 * m / ε)) alg ω t
      ≤ ∑ _t ∈ range m, (Fintype.card (EΩ m j (2 * m)) : ℝ) * (ε / 4) := by
        apply sum_le_sum
        intro t ht
        have h := sum_HME_le (by omega) hA hj alg ⟨t, mem_range.1 ht⟩ hb
        rw [mul_exp_neg_log_div (by omega) hε0] at h
        exact h
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Markov's inequality, counting form.** At most a fraction `ε` of the realizations have
`H ≥ m/4`. -/
theorem card_heavyPlays_le_epsE (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((univ.filter fun ω : EΩ m j (2 * m) =>
        (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω).card : ℝ) ≤
      ε * Fintype.card (EΩ m j (2 * m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hB : ((univ.filter fun ω : EΩ m j (2 * m) =>
        (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω).card : ℝ) * ((m : ℝ) / 4) ≤
      Fintype.card (EΩ m j (2 * m)) * (ε * m / 4) :=
    calc ((univ.filter fun ω : EΩ m j (2 * m) =>
            (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω).card : ℝ) * ((m : ℝ) / 4)
          = ∑ _ω ∈ univ.filter (fun ω : EΩ m j (2 * m) =>
              (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω), (m : ℝ) / 4 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ univ.filter (fun ω : EΩ m j (2 * m) =>
              (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω),
            sumHMbE (Real.log (4 * m / ε)) alg ω :=
          sum_le_sum fun ω hω => (mem_filter.1 hω).2
      _ ≤ ∑ ω : EΩ m j (2 * m), sumHMbE (Real.log (4 * m / ε)) alg ω :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ω _ _ => sumHMbE_nonneg _ alg ω
      _ ≤ _ := sum_sumHMbE_le hm hj alg hε0 hε1
  have h4 : ((univ.filter fun ω : EΩ m j (2 * m) =>
        (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω).card : ℝ) * m ≤
      ε * Fintype.card (EΩ m j (2 * m)) * m := by
    linarith
  exact le_of_mul_le_mul_right h4 hm0

/-- **On a realization with `H < m/4`**, the per-play inequality gives
`C > (2m+1)/(4(1+ln(4m/ε)))`. -/
theorem epsBound_lt_numColsE (hm : 2 ≤ m) (hj : 1 ≤ j) {alg : OnlineAlg} (halg : alg.IsProper)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (ω : EΩ m j (2 * m))
    (hH : sumHMbE (Real.log (4 * m / ε)) alg ω < (m : ℝ) / 4) :
    epsBound m ε < numColsE alg ω := by
  have hb : 1 ≤ Real.log (4 * m / ε) := one_le_log_four_mul_div hm hε0 hε1
  have h := perPlay_boundE (m := m) (j := j) (b := Real.log (4 * m / ε)) (by omega) hj halg
    (by linarith) ω
  change ((3 * m + 1) / 4 : ℝ) ≤ numColsE alg ω * (Real.log (4 * m / ε) + 1) +
    sumHMbE (Real.log (4 * m / ε)) alg ω at h
  have hpos : (0 : ℝ) < 4 * (1 + Real.log (4 * m / ε)) := by linarith
  unfold epsBound
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- **Corollary 8.6, first statement, for `R_j(m)`, counting form.** For `j ≥ 1`, `m ≥ 2` and
`0 < ε < 1`, every proper deterministic algorithm uses at least `(2m+1)/(4(1+ln(4m/ε)))` colours
on at least a fraction `1 - ε` of the realizations of `R_j(m)` (`A = 2m`). -/
theorem uniform_tower_eps_countE (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg)
    (halg : alg.IsProper) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * Fintype.card (EΩ m j (2 * m)) ≤
      ((univ.filter fun ω : EΩ m j (2 * m) => epsBound m ε ≤ numColsE alg ω).card : ℝ) := by
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset (EΩ m j (2 * m))))
    (fun ω => (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω)
  have hsub : (univ.filter fun ω : EΩ m j (2 * m) =>
      ¬ ((m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω)) ⊆
      univ.filter fun ω : EΩ m j (2 * m) => epsBound m ε ≤ numColsE alg ω := by
    intro ω hω
    rw [mem_filter] at hω ⊢
    exact ⟨mem_univ _, (epsBound_lt_numColsE hm hj halg hε0 hε1 ω (not_le.1 hω.2)).le⟩
  have h1 : ((univ.filter fun ω : EΩ m j (2 * m) =>
      ¬ ((m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω)).card : ℝ) ≤
      ((univ.filter fun ω : EΩ m j (2 * m) => epsBound m ε ≤ numColsE alg ω).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have h2 := card_heavyPlays_le_epsE hm hj alg hε0 hε1
  rw [card_univ] at hsplit
  have hsplit' : ((univ.filter fun ω : EΩ m j (2 * m) =>
        (m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω).card : ℝ) +
      ((univ.filter fun ω : EΩ m j (2 * m) =>
        ¬ ((m : ℝ) / 4 ≤ sumHMbE (Real.log (4 * m / ε)) alg ω)).card : ℝ) =
      Fintype.card (EΩ m j (2 * m)) := by
    exact_mod_cast hsplit
  linarith

/-- **Corollary 8.6, first statement, for the random wiring `R_j(m)`.** Under the uniform
distribution on the realizations of `R_j(m)`, every proper deterministic algorithm uses at least
`(2m+1)/(4(1+ln(4m/ε)))` colours with probability at least `1 - ε`. -/
theorem uniform_tower_eps_probE (hm : 2 ≤ m) (hj : 1 ≤ j) [Nonempty (EΩ m j (2 * m))]
    (alg : OnlineAlg) (halg : alg.IsProper) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (1 - ε) ≤ (unifPMF (EΩ m j (2 * m))).toOuterMeasure
      {ω | epsBound m ε ≤ numColsE alg ω} :=
  ofReal_le_unifPMF_pred (fun ω => epsBound m ε ≤ (numColsE alg ω : ℝ))
    (uniform_tower_eps_countE hm hj alg halg hε0 hε1)

/-- **Corollary 8.6, first statement, on online inputs.** On the distribution of the presented
input under `R_j(m)` (`unifInput (uInputE hA)`, inputs on `m (2m)^j` vertices), every proper
deterministic algorithm uses at least `(2m+1)/(4(1+ln(4m/ε)))` colours with probability at least
`1 - ε`. -/
theorem uniform_tower_eps_inputE (hm : 2 ≤ m) (hj : 1 ≤ j) [Nonempty (EΩ m j (2 * m))]
    (hA : 0 < 2 * m) (alg : OnlineAlg) (halg : alg.IsProper) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ENNReal.ofReal (1 - ε) ≤ (unifInput (uInputE (m := m) (j := j) hA)).toOuterMeasure
      {I | epsBound m ε ≤ (I.cost alg : ℝ)} := by
  refine @ofReal_le_unifInput _ _ _ _ (uInputE hA)
    {I : OnlineInput (utSize (2 * m) m j) | epsBound m ε ≤ (I.cost alg : ℝ)}
    (fun I => inferInstanceAs (Decidable (epsBound m ε ≤ (I.cost alg : ℝ)))) (1 - ε) ?_
  have hset : (univ.filter fun ω : EΩ m j (2 * m) =>
      uInputE hA ω ∈ {I : OnlineInput (utSize (2 * m) m j) | epsBound m ε ≤ (I.cost alg : ℝ)}) =
      univ.filter fun ω : EΩ m j (2 * m) => epsBound m ε ≤ (numColsE alg ω : ℝ) := by
    apply filter_congr
    intro ω _
    rw [Set.mem_ofPred_eq, numColsE_eq_cost hA]
  rw [hset]
  exact uniform_tower_eps_countE hm hj alg halg hε0 hε1

/-- **Corollary 8.6, first statement, packaged.** For `j ≥ 1`, `m ≥ 2`, `m ≤ |P_j(k)|` and
`0 < ε < 1`, the random wiring `R_j(m)` is a distribution over `k`-colourable online inputs on
`m (2m)^j` vertices that makes every proper deterministic algorithm use at least
`(2m+1)/(4(1+ln(4m/ε)))` colours with probability at least `1 - ε`; the statement is
`ProbForcing k (m (2m)^j) (epsBound m ε) (1 - ε)`. -/
theorem uniform_tower_epsE {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing k (m * (2 * m) ^ j) (epsBound m ε) (1 - ε) := by
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  have hA : 0 < 2 * m := by omega
  have hcol : ∀ ω : EΩ m j (2 * m), (uInputE hA ω).graph.Colorable k :=
    fun ω => uInputE_colorable ω hA hP
  have hk : 1 ≤ k := by
    obtain ⟨ω⟩ := (inferInstance : Nonempty (EΩ m j (2 * m)))
    exact one_le_of_colorable (by rw [utSize_eq]; exact Nat.mul_pos (by omega) (pow_pos hA j))
      (hcol ω)
  have hcore : ProbForcing k (utSize (2 * m) m j) (epsBound m ε) (1 - ε) := by
    refine ⟨unifInput (uInputE hA), fun I hI => ?_, fun alg halg =>
      uniform_tower_eps_inputE hm hj hA alg halg hε0 hε1⟩
    obtain ⟨ω, rfl⟩ := mem_support_unifInput hI
    exact hcol ω
  exact hcore.pad (utSize_eq (2 * m) m j).le hk

end OnlineColouring
