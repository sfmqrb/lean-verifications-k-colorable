module

public import OnlineColouring.RjmMass
public import OnlineColouring.OblCount

/-!
# The random wiring `R_j(m)`: the earlier neighbours of a vertex are exactly uniform

Proof of Lemma 8.4 (Section 8.2): *given the history, the wiring of phase `t` is
drawn as in Construction 8.1 … so `x_s(z_1)` is uniform over the eligible vertices below `v_s`,
and these choices are independent for different `s`.*

`UWiringE.lean` proves the inequality that Lemma 8.4 needs (`card_le_card_fiber_mul`: every
eligible leaf is the neighbour for at least a fraction `A^{-j}` of the values of the coordinate of
`(t, s)`).  This file proves the exact statements quoted above, uniformity and independence, and
the product formula for the probability.  Fix the coordinates of the other phases (`ω`),
`s < t < m` and a vertex `y`.

* `nbOfE_mem_eligE`: for every value `z` of the coordinate of `(t, s)`, the neighbour
  `nbOfE ω s t y z` of `y` below `v_s` is an eligible leaf of `v_s`.
* `card_eligE`: there are exactly `(A - (t - s - 1)) A^(j-1)` eligible leaves below `v_s` at the
  start of phase `t`.
* **`card_fiber_mul_card_eligE`** (exact uniformity): every eligible leaf `x` is the neighbour for
  exactly a fraction `1 / |eligible|` of the values `z`:
  `#{z | nbOfE ω s t y z = x} * |eligE ω s t| = |EZ A j t s|`.
  `card_fiber_eq_zero`: a leaf that is not eligible is never the neighbour.
* `map_nbOfE_apply`: the same as a statement about distributions: the image of the uniform
  distribution on the coordinate under `z ↦ nbOfE ω s t y z` gives every eligible leaf the
  probability `1 / |eligible|` and every other number the probability `0`; that is, it is the
  uniform distribution on the eligible leaves.
* **`card_nbrs_mul_prod`** (uniformity and independence across `s`): for every choice of eligible
  leaves `x s` below `v_s`, `s < t`, exactly a fraction `1 / ∏_{s<t} |eligE ω s t|` of the
  wirings `X` of phase `t` give the vertex `y` of phase `t` the earlier neighbours `x s`, `s < t`,
  in the realization `update ω t X`.
* `card_pred_mul_card_eligE`, `card_forall_pred_mul_prod`: the same for events: the probability
  that the neighbour below `v_s` has a property is the fraction of the eligible leaves with that
  property, independently for different `s`.
* **`card_noNbr_mul_prod`**: the probability that `y` has no earlier neighbour of colour `c` is
  exactly `∏_{s<t} (1 - p_s)`, as the proof of Lemma 8.4 says, where `p_s` is the fraction of
  the eligible vertices below `v_s` that have colour `c`.

The proof combines the injection behind `card_le_card_fiber_mul`, with its exact count
`(A - (t - s - 1)) A^(j-1)` (`card_le_card_fiber_mul_exact`), with the facts that the fibres
partition the values of the coordinate and that there are exactly that many eligible leaves: a
sum of `|eligible|` numbers, each at least the mean, that equals `|eligible|` times the mean has
all terms equal to the mean.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset
open scoped ENNReal

variable {m j A : ℕ} (ω : EΩ m j A)

/-- The number of eligible leaves below `v_s` at the start of phase `t`. -/
theorem card_eligE (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t) (htm : t < m) :
    (eligE ω s t).card = (A - (t - s - 1)) * A ^ (j - 1) := by
  unfold eligE
  rw [card_phase_filter hA hj s (usedTopE_subset ω (by omega) (by omega)), card_usedTopE]

/-- **The neighbour is an eligible leaf**, for every value of the coordinate. -/
theorem nbOfE_mem_eligE (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t) (htm : t < m) (y : ℕ)
    (z : EZ A j t s) : nbOfE ω s t y z ∈ eligE ω s t := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hU := usedTopE_subset ω (by omega : s < m) (by omega : s + (t - s - 1) < m)
  have hrank : (z.1 : ℕ) < A - (usedTopE ω s (t - s - 1)).card := by
    rw [card_usedTopE]
    exact z.1.2
  have hpick : pickR (usedTopE ω s (t - s - 1)) z.1 < A := pickR_lt hU hrank
  have htop : (nbOfE ω s t y z / A ^ (k + 1 - 1)) % A = pickR (usedTopE ω s (t - s - 1)) z.1 := by
    change (nbOfE ω s t y z / A ^ k) % A = _
    unfold nbOfE
    rw [Rjm.ueNb_top hA (fun _ _ => Nat.mod_lt _ hA) (fun _ _ => phiOf_lt hA _)]
    exact Nat.mod_eq_of_lt hpick
  unfold eligE
  rw [mem_filter, mem_phase hA, htop]
  exact ⟨nbOfE_div hA ω s t y z, pickR_notMem _ _⟩

/-- The injection behind `card_le_card_fiber_mul`, with its exact count: for every eligible leaf
`x`, `|EZ A j t s| ≤ #{z | nbOfE ω s t y z = x} * ((A - (t - s - 1)) A^(j-1))`. -/
theorem card_le_card_fiber_mul_exact (hA : 0 < A) (hj : 1 ≤ j) {s t y x : ℕ}
    (hst : s < t) (htm : t < m) (hx : x ∈ eligE ω s t) :
    Fintype.card (EZ A j t s) ≤
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card *
        ((A - (t - s - 1)) * A ^ (j - 1)) := by
  classical
  have hxs : x / A ^ j = s := (mem_phase hA).1 (mem_filter.1 hx).1
  have hc₀U : (x / A ^ (j - 1)) % A ∉ usedTopE ω s (t - s - 1) := (mem_filter.1 hx).2
  have hU := usedTopE_subset ω (by omega : s < m) (by omega : s + (t - s - 1) < m)
  obtain ⟨r₀, hr₀, hpick⟩ := exists_pickR_eq hU hc₀U (Nat.mod_lt _ hA)
  rw [card_usedTopE] at hr₀
  -- the ancestors of `y` (local indices), their positions, and the digits of `x`
  let a : (k : Fin (j - 1)) → Fin (A ^ (k : ℕ)) :=
    fun k => ⟨(y / A ^ (j - k)) % A ^ (k : ℕ), Nat.mod_lt _ (pow_pos hA _)⟩
  let d : Fin (j - 1) → Fin A := fun k => ⟨(y / A ^ (j - k - 1)) % A, Nat.mod_lt _ hA⟩
  let e : Fin (j - 1) → Fin A := fun k => ⟨(x / A ^ (j - k - 2)) % A, Nat.mod_lt _ hA⟩
  -- the correction of a coordinate
  let N : EZ A j t s → EZ A j t s := fun z =>
    (⟨r₀, hr₀⟩, fun k g => if g = a k then Equiv.swap (z.2 k (a k) (d k)) (e k) * z.2 k (a k)
      else z.2 k g)
  have hN : ∀ z, nbOfE ω s t y (N z) = x := by
    intro z
    apply nbOfE_eq_of_digits ω hj (N z) hxs
    · change pickR (usedTopE ω s (t - s - 1)) r₀ % A = (x / A ^ (j - 1)) % A
      rw [hpick, Nat.mod_mod]
    · intro k hk
      have hk' : k < j - 1 := by omega
      have hdA : (y / A ^ (j - k - 1)) % A < A := Nat.mod_lt _ hA
      have hp : permOf (N z) k (y / A ^ (j - k)) =
          Equiv.swap (z.2 ⟨k, hk'⟩ (a ⟨k, hk'⟩) (d ⟨k, hk'⟩)) (e ⟨k, hk'⟩) *
            z.2 ⟨k, hk'⟩ (a ⟨k, hk'⟩) := by
        unfold permOf
        rw [dite_eq_left ⟨hk', hA⟩]
        change (if (⟨(y / A ^ (j - k)) % A ^ k, _⟩ : Fin (A ^ k)) = a ⟨k, hk'⟩ then _ else _) = _
        rw [ite_eq_left rfl]
      unfold phiOf
      rw [dite_eq_left hdA, hp, Equiv.Perm.mul_apply]
      have hdd : (⟨(y / A ^ (j - k - 1)) % A, hdA⟩ : Fin A) = d ⟨k, hk'⟩ := rfl
      rw [hdd, Equiv.swap_apply_left]
  -- the injection
  let F : EZ A j t s → {z : EZ A j t s // nbOfE ω s t y z = x} ×
      (Fin (A - (t - s - 1)) × (Fin (j - 1) → Fin A)) :=
    fun z => (⟨N z, hN z⟩, (z.1, fun k => z.2 k (a k) (d k)))
  have hFinj : Function.Injective F := by
    intro z w hzw
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hzw
    obtain ⟨hNzw, h1, h2⟩ := hzw
    refine Prod.ext h1 ?_
    funext k g
    have hk := congrFun h2 k
    have hg := congrFun (congrFun (congrArg Prod.snd hNzw) k) g
    simp only [N] at hg
    by_cases hga : g = a k
    · rw [hga] at hg ⊢
      rw [ite_eq_left rfl, ite_eq_left rfl, hk] at hg
      exact mul_left_cancel hg
    · rw [ite_eq_right hga, ite_eq_right hga] at hg
      exact hg
  have hcard := Fintype.card_le_of_injective F hFinj
  have hR : Fintype.card ({z : EZ A j t s // nbOfE ω s t y z = x} ×
      (Fin (A - (t - s - 1)) × (Fin (j - 1) → Fin A))) =
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card *
        ((A - (t - s - 1)) * A ^ (j - 1)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_subtype, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact hcard.trans_eq hR

/-- **Exact uniformity of the neighbour.** Fix the coordinates of the other phases, `s < t < m`
and a vertex `y`.  Every eligible leaf `x` of `v_s` is the neighbour of `y` below `v_s` for
exactly a fraction `1 / |eligE ω s t|` of the values `z` of the coordinate of `(t, s)`. -/
theorem card_fiber_mul_card_eligE (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t)
    (htm : t < m) (y : ℕ) {x : ℕ} (hx : x ∈ eligE ω s t) :
    (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card * (eligE ω s t).card =
      Fintype.card (EZ A j t s) := by
  classical
  have hcardE := card_eligE ω hA hj hst htm (j := j)
  have hfib : Fintype.card (EZ A j t s) = ∑ x' ∈ eligE ω s t,
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x').card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise fun z _ => nbOfE_mem_eligE ω hA hj hst htm y z
  have hsum : ∑ _x' ∈ eligE ω s t, Fintype.card (EZ A j t s) = ∑ x' ∈ eligE ω s t,
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x').card *
        ((A - (t - s - 1)) * A ^ (j - 1)) := by
    rw [sum_const, smul_eq_mul, hcardE, ← sum_mul, ← hfib, Nat.mul_comm]
  have hall := (sum_eq_sum_iff_of_le fun x' hx' =>
    card_le_card_fiber_mul_exact ω hA hj (y := y) hst htm hx').1 hsum
  rw [hcardE]
  exact (hall x hx).symm

/-- A leaf that is not eligible is never the neighbour. -/
theorem card_fiber_eq_zero (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t) (htm : t < m)
    (y : ℕ) {x : ℕ} (hx : x ∉ eligE ω s t) :
    (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro z _ hz
  exact hx (hz ▸ nbOfE_mem_eligE ω hA hj hst htm y z)

/-- The eligible leaves are not all used up: there is one, for `s < t < m ≤ A`. -/
theorem card_eligE_pos (hmA : m ≤ A) (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t)
    (htm : t < m) : 0 < (eligE ω s t).card := by
  rw [card_eligE ω hA hj hst htm]
  exact Nat.mul_pos (by omega) (pow_pos hA _)

/-- **The neighbour is uniformly distributed over the eligible leaves.** Under the uniform
distribution on the coordinate of `(t, s)`, the neighbour of `y` below `v_s` equals a given
eligible leaf with probability `1 / |eligE ω s t|`, and it is never another number. -/
theorem map_nbOfE_apply (hmA : m ≤ A) (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t)
    (htm : t < m) (y x : ℕ) [Nonempty (EZ A j t s)] :
    ((unifPMF (EZ A j t s)).map (nbOfE ω s t y)) x =
      if x ∈ eligE ω s t then ((eligE ω s t).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have hval : ((unifPMF (EZ A j t s)).map (nbOfE ω s t y)) x =
      ((univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card : ℝ≥0∞) *
        (Fintype.card (EZ A j t s) : ℝ≥0∞)⁻¹ := by
    have e : (univ.filter (· ∈ nbOfE ω s t y ⁻¹' {x}) : Finset (EZ A j t s)) =
        univ.filter fun z => nbOfE ω s t y z = x := by
      apply filter_congr
      intro z _
      simp
    rw [← PMF.toOuterMeasure_apply_singleton (PMF.map (nbOfE ω s t y) (unifPMF (EZ A j t s))) x,
      PMF.toOuterMeasure_map_apply, Obl.toOuterMeasure_unifPMF, e]
  rw [hval]
  split_ifs with hx
  · have h := card_fiber_mul_card_eligE ω hA hj hst htm y hx
    have hpos := card_eligE_pos ω hmA hA hj hst htm (j := j)
    have hfpos : 0 < (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card := by
      rcases Nat.eq_zero_or_pos
        (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card with h0 | h0
      · rw [h0, Nat.zero_mul] at h
        exact absurd h.symm (Nat.ne_of_gt Fintype.card_pos)
      · exact h0
    rw [← h, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast hfpos.ne') (ENNReal.natCast_ne_top _), one_mul]
  · rw [card_fiber_eq_zero ω hA hj hst htm y hx, Nat.cast_zero, zero_mul]

/-! ### All earlier neighbours of a vertex: uniform and independent -/

theorem prod_fin_ite_nat {t : ℕ} (ht : t ≤ m) (g : ℕ → ℕ) :
    ∏ s : Fin m, (if (s : ℕ) < t then g s else 1) = ∏ s ∈ range t, g s := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < t then g i else 1), ← prod_filter]
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  omega

/-- **Uniformity and independence, counting form.** Fix the coordinates of the other phases and
a vertex `y`.  For every family of eligible leaves `x s` below `v_s`, `s < t`, exactly a fraction
`1 / ∏_{s<t} |eligE ω s t|` of the wirings `X` of phase `t` satisfy `nbOfE ω s t y (X s) = x s`
for all `s < t`. -/
theorem card_nbOfE_mul_prod (hA : 0 < A) (hj : 1 ≤ j) (t : Fin m) (y : ℕ) (x : ℕ → ℕ)
    (hx : ∀ s < (t : ℕ), x s ∈ eligE ω s t) :
    (univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → nbOfE ω s t y (X s) = x s).card *
      ∏ s ∈ range t, (eligE ω s t).card = Fintype.card ((s : Fin m) → EZ A j t s) := by
  classical
  rw [card_filter_pi_dep (Z := fun s : Fin m => EZ A j t s) t
    (fun (s : Fin m) z => nbOfE ω s t y z = x s),
    ← prod_fin_ite_nat t.2.le (fun s => (eligE ω s t).card), ← prod_mul_distrib, Fintype.card_pi]
  apply prod_congr rfl
  intro s _
  split_ifs with hs
  · exact card_fiber_mul_card_eligE ω hA hj hs t.2 y (hx s hs)
  · rw [Nat.mul_one]

/-- **Uniformity and independence of the earlier neighbours** (the claim in the proof of
Lemma 8.4).  Fix the coordinates of the other phases and a vertex `y` of phase `t`.  For every
family of eligible leaves `x s` below `v_s`, `s < t`, exactly a fraction
`1 / ∏_{s<t} |eligE ω s t|` of the wirings `X` of phase `t` give `y`, in the realization
`update ω t X`, the earlier neighbour `x s` below `v_s` for all `s < t`. -/
theorem card_nbrs_mul_prod (hA : 0 < A) (hj : 1 ≤ j) (t : Fin m) {y : ℕ} (hy : y / A ^ j = t)
    (x : ℕ → ℕ) (hx : ∀ s < (t : ℕ), x s ∈ eligE ω s t) :
    (univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t →
          ueNb A (tauE (Function.update ω t X)) (phiE (Function.update ω t X)) j s y = x s).card *
      ∏ s ∈ range t, (eligE ω s t).card = Fintype.card ((s : Fin m) → EZ A j t s) := by
  classical
  have e : (univ.filter fun X : (s : Fin m) → EZ A j t s =>
      ∀ s : Fin m, (s : ℕ) < t →
        ueNb A (tauE (Function.update ω t X)) (phiE (Function.update ω t X)) j s y = x s) =
      univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → nbOfE ω s t y (X s) = x s := by
    apply filter_congr
    intro X _
    apply forall₂_congr
    intro s _
    rw [ueNb_updateE (ω := ω) t X s hy]
  rw [e]
  exact card_nbOfE_mul_prod ω hA hj t y x hx

/-! ### Events: the probability is the fraction of the eligible leaves -/

/-- **Uniformity, for events.** For every property `P` of vertices, the fraction of the values `z`
of the coordinate of `(t, s)` for which the neighbour of `y` below `v_s` has `P` equals the
fraction of the eligible leaves of `v_s` that have `P`:
`#{z | P (nbOfE ω s t y z)} * |eligE ω s t| = |EZ A j t s| * #{x ∈ eligE ω s t | P x}`. -/
theorem card_pred_mul_card_eligE (hA : 0 < A) (hj : 1 ≤ j) {s t : ℕ} (hst : s < t)
    (htm : t < m) (y : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun z : EZ A j t s => P (nbOfE ω s t y z)).card * (eligE ω s t).card =
      Fintype.card (EZ A j t s) * ((eligE ω s t).filter P).card := by
  classical
  have hfib : (univ.filter fun z : EZ A j t s => P (nbOfE ω s t y z)).card =
      ∑ x ∈ (eligE ω s t).filter P,
        (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card := by
    rw [card_eq_sum_card_fiberwise (f := nbOfE ω s t y)
      (s := univ.filter fun z : EZ A j t s => P (nbOfE ω s t y z)) (t := (eligE ω s t).filter P)
      (fun z hz => mem_filter.2 ⟨nbOfE_mem_eligE ω hA hj hst htm y z, (mem_filter.1 hz).2⟩)]
    apply sum_congr rfl
    intro x hx
    congr 1
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ (mem_filter.1 hx).2, h⟩
  rw [hfib, sum_mul,
    sum_congr rfl fun x hx => card_fiber_mul_card_eligE ω hA hj hst htm y (mem_filter.1 hx).1,
    sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Uniformity and independence, for events.** For properties `P s` of vertices, the fraction
of the wirings `X` of phase `t` for which the neighbour of `y` below `v_s` has `P s` for all
`s < t` is the product over `s < t` of the fractions of the eligible leaves of `v_s` with
`P s`. -/
theorem card_forall_pred_mul_prod (hA : 0 < A) (hj : 1 ≤ j) (t : Fin m) (y : ℕ)
    (P : ℕ → ℕ → Prop) [∀ s, DecidablePred (P s)] :
    (univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → P s (nbOfE ω s t y (X s))).card *
      ∏ s ∈ range t, (eligE ω s t).card =
    Fintype.card ((s : Fin m) → EZ A j t s) * ∏ s ∈ range t, ((eligE ω s t).filter (P s)).card := by
  classical
  rw [card_filter_pi_dep (Z := fun s : Fin m => EZ A j t s) t
    (fun (s : Fin m) z => P s (nbOfE ω s t y z)),
    ← prod_fin_ite_nat t.2.le (fun s => (eligE ω s t).card),
    ← prod_fin_ite_nat t.2.le (fun s => ((eligE ω s t).filter (P s)).card), ← prod_mul_distrib,
    Fintype.card_pi, ← prod_mul_distrib]
  apply prod_congr rfl
  intro s _
  split_ifs with hs
  · exact card_pred_mul_card_eligE ω hA hj hs t.2 y (P s)
  · rw [Nat.mul_one]

open Classical in
/-- **The probability of the event of Lemma 8.4, exactly** (the paper: *hence the probability is
`∏_{s<t} (1 - p_s)`*, where `p_s` is the fraction of the eligible vertices below `v_s` that have
colour `c`).  Fix the coordinates of the other phases and a vertex `y` of phase `t`.  The fraction
of the wirings `X` of phase `t` for which `y` has no earlier neighbour of colour `c` in the
realization `update ω t X` is `∏_{s<t} #{x ∈ eligE ω s t | colour x ≠ c} / |eligE ω s t|`. -/
theorem card_noNbr_mul_prod (hA : 0 < A) (hj : 1 ≤ j) (alg : OnlineAlg) (t : Fin m) (c : ℕ)
    {y : ℕ} (hy : y / A ^ j = t) :
    (univ.filter fun X : (s : Fin m) → EZ A j t s =>
        Rjm.NoNbrOfColour alg (Function.update ω t X) c y).card *
      ∏ s ∈ range t, (eligE ω s t).card =
    Fintype.card ((s : Fin m) → EZ A j t s) *
      ∏ s ∈ range t, ((eligE ω s t).filter fun x => uColE alg ω x ≠ c).card := by
  have e : (univ.filter fun X : (s : Fin m) → EZ A j t s =>
      Rjm.NoNbrOfColour alg (Function.update ω t X) c y) =
      univ.filter fun X : (s : Fin m) → EZ A j t s =>
        ∀ s : Fin m, (s : ℕ) < t → uColE alg ω (nbOfE ω s t y (X s)) ≠ c := by
    apply filter_congr
    intro X _
    exact Rjm.noNbrOfColour_update_iff hA alg ω t X c hy
  rw [e]
  exact card_forall_pred_mul_prod ω hA hj t y (fun _ x => uColE alg ω x ≠ c)

/-- The earlier neighbours of a vertex of phase `t` are always eligible leaves. -/
theorem ueNb_update_mem_eligE (hA : 0 < A) (hj : 1 ≤ j) (t : Fin m) {y : ℕ}
    (hy : y / A ^ j = t) (X : (s : Fin m) → EZ A j t s) (s : Fin m) (hs : (s : ℕ) < t) :
    ueNb A (tauE (Function.update ω t X)) (phiE (Function.update ω t X)) j s y ∈
      eligE ω s t := by
  rw [ueNb_updateE (ω := ω) t X s hy]
  exact nbOfE_mem_eligE ω hA hj hs t.2 y (X s)

end Expl

end OnlineColouring
