module

public import OnlineColouring.RandModel
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Counting and mixing lemmas for uniform distributions (used in Appendix C and Lemma 8.4)

Generic tools for the proof of Lemma C.2 (`OblProb.lean`); `ExplUniform.lean` uses
`toOuterMeasure_unifPMF` for the uniformity statement in the proof of Lemma 8.4
(`Expl.map_nbOfE_apply`).  Nothing here mentions graphs.

* `card_filter_mul_le` (conditioning on all coordinates but one): in a finite product
  `∀ j, β j`, if for every point `ω` at most `B` values `g` of the coordinate `i` make
  `P (update ω i g)` true, then `P` holds on at most a fraction `B / |β i|` of the product.
* `card_miss_le` (Step 1 of the proof, for one block): among the index vectors `g : Fin R → Fin d`,
  at most `d (d-1)^c d^(R-c)` have a value `a` that `g` misses on a fixed set of at least `c`
  positions.
* `toOuterMeasure_unifPMF`: under the uniform distribution an event has probability
  `|event| / |Ω|`.
* `mix_bound`: the assembly of Step 3.  Let `ε ≥ 0`, and let `a ∼ 𝓗` and `ω` uniform on `Ω` be
  independent.  If for every `ω` the event `T ω` has `𝓗`-probability at least `ρ`, and for every
  `a` in the support the number of `ω` with `a ∈ T ω` is at most the number of `ω` with
  `f a ω ∈ S` plus `ε |Ω|`, then `f a ω ∈ S` with probability at least `ρ - ε`.
* `weak_term_le`: `x (1 - 1/x)^c ≤ D e^{-r/D}` for `1 ≤ x ≤ D` and `0 ≤ r ≤ c` (the remark after
  the lemma: `(1-1/x)^c ≤ e^{-c/x}` and `x e^{-c/x}` is increasing in `x`).
-/

@[expose] public section

namespace OnlineColouring

namespace Obl

open Finset
open scoped ENNReal

/-! ### Conditioning on all coordinates but one -/

/-- If, for every `ω`, at most `B` values `g` of coordinate `i` satisfy `P (update ω i g)`, then
`|{ω | P ω}| · |β i| ≤ B · |∀ j, β j|`. -/
theorem card_filter_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ j, Fintype (β j)] (i : ι) (P : (∀ j, β j) → Prop)
    [DecidablePred P] (B : ℕ)
    (h : ∀ ω : ∀ j, β j, (univ.filter fun g : β i => P (Function.update ω i g)).card ≤ B) :
    (univ.filter P).card * Fintype.card (β i) ≤ B * Fintype.card (∀ j, β j) := by
  classical
  set T : Finset ((∀ j, β j) × β i) :=
    (univ ×ˢ univ).filter fun p => P (Function.update p.1 i p.2) with hT
  have h₁ : (univ.filter P).card * Fintype.card (β i) ≤ T.card := by
    rw [← card_univ (α := β i), ← card_product]
    refine card_le_card_of_injOn (fun p => (Function.update p.1 i p.2, p.1 i)) ?_ ?_
    · rintro ⟨ω, g⟩ hp
      have hP : P ω := (mem_filter.1 (mem_product.1 (mem_coe.1 hp)).1).2
      simp only [hT, coe_filter, mem_product, mem_univ, and_self, true_and, Set.mem_ofPred_eq]
      simpa using hP
    · rintro ⟨ω, g⟩ - ⟨ω', g'⟩ - heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h₁, h₂⟩ := heq
      have hg : g = g' := by
        have := congrFun h₁ i
        simpa using this
      have hω : ω = ω' := by
        funext j
        by_cases hj : j = i
        · subst hj; exact h₂
        · have := congrFun h₁ j
          simpa [Function.update_of_ne hj] using this
      rw [hg, hω]
  have h₂ : T.card ≤ B * Fintype.card (∀ j, β j) := by
    rw [hT, card_filter, sum_product]
    calc ∑ ω : ∀ j, β j, ∑ g : β i, (if P (Function.update ω i g) then 1 else 0)
        = ∑ ω : ∀ j, β j, (univ.filter fun g : β i => P (Function.update ω i g)).card := by
          refine sum_congr rfl fun ω _ => ?_
          rw [card_filter]
      _ ≤ ∑ _ω : ∀ j, β j, B := sum_le_sum fun ω _ => h ω
      _ = B * Fintype.card (∀ j, β j) := by
          rw [sum_const, card_univ, smul_eq_mul, Nat.mul_comm]
  exact h₁.trans h₂

/-! ### Index vectors that miss a value on a large set -/

/-- The number of `g : Fin R → Fin d` that avoid the value `a` on the set `S`. -/
theorem card_avoid {R d : ℕ} (S : Finset (Fin R)) (a : Fin d) :
    (univ.filter fun g : Fin R → Fin d => ∀ t ∈ S, g t ≠ a).card =
      (d - 1) ^ S.card * d ^ (R - S.card) := by
  classical
  have e : (univ.filter fun g : Fin R → Fin d => ∀ t ∈ S, g t ≠ a) =
      Fintype.piFinset fun t : Fin R => if t ∈ S then univ.erase a else univ := by
    ext g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hg t
      by_cases ht : t ∈ S
      · simp [ht, hg t ht]
      · simp [ht]
    · intro hg t ht
      have := hg t
      simpa [ht] using this
  rw [e, Fintype.card_piFinset]
  have hterm : ∀ t : Fin R, (if t ∈ S then univ.erase a else (univ : Finset (Fin d))).card =
      if t ∈ S then d - 1 else d := by
    intro t
    split_ifs
    · rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]
    · rw [card_univ, Fintype.card_fin]
  simp only [hterm]
  rw [prod_ite, prod_const, prod_const]
  have h₁ : (univ.filter fun t : Fin R => t ∈ S) = S := by
    ext t; simp
  have h₂ : (univ.filter fun t : Fin R => t ∉ S).card = R - S.card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin R))) (fun t => t ∈ S)
    rw [h₁, card_univ, Fintype.card_fin] at this
    omega
  rw [h₁, h₂]

/-- **Step 1 for one block, as a count.** Let `S` be a set of at least `c` positions of a block of
size `R`.  At most `d (d-1)^c d^(R-c)` index vectors `g : Fin R → Fin d` have an index class
`{t : g t = a}` that misses `S`. -/
theorem card_miss_le {R d c : ℕ} (S : Finset (Fin R)) (hS : c ≤ S.card) :
    (univ.filter fun g : Fin R → Fin d => ∃ a : Fin d, ∀ t ∈ S, g t ≠ a).card ≤
      d * ((d - 1) ^ c * d ^ (R - c)) := by
  classical
  have hSR : S.card ≤ R := by
    have := card_le_univ S
    rwa [Fintype.card_fin] at this
  have hsub : (univ.filter fun g : Fin R → Fin d => ∃ a : Fin d, ∀ t ∈ S, g t ≠ a) ⊆
      (univ : Finset (Fin d)).biUnion fun a =>
        univ.filter fun g : Fin R → Fin d => ∀ t ∈ S, g t ≠ a := by
    intro g hg
    obtain ⟨a, ha⟩ := (mem_filter.1 hg).2
    exact mem_biUnion.2 ⟨a, mem_univ a, mem_filter.2 ⟨mem_univ g, ha⟩⟩
  have hmono : (d - 1) ^ S.card * d ^ (R - S.card) ≤ (d - 1) ^ c * d ^ (R - c) := by
    have e₁ : S.card = c + (S.card - c) := by omega
    have e₂ : R - c = (S.card - c) + (R - S.card) := by omega
    calc (d - 1) ^ S.card * d ^ (R - S.card)
        = (d - 1) ^ c * ((d - 1) ^ (S.card - c) * d ^ (R - S.card)) := by
          rw [← Nat.mul_assoc, ← pow_add, ← e₁]
      _ ≤ (d - 1) ^ c * (d ^ (S.card - c) * d ^ (R - S.card)) := by
          gcongr
          omega
      _ = (d - 1) ^ c * d ^ (R - c) := by rw [e₂, pow_add]
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a : Fin d, (univ.filter fun g : Fin R → Fin d => ∀ t ∈ S, g t ≠ a).card :=
        card_biUnion_le
    _ ≤ ∑ _a : Fin d, (d - 1) ^ c * d ^ (R - c) :=
        sum_le_sum fun a _ => by rw [card_avoid]; exact hmono
    _ = d * ((d - 1) ^ c * d ^ (R - c)) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- The count of `card_miss_le` as a fraction: `d (d-1)^c d^(R-c) = d^R · d (1 - 1/d)^c` for
`c ≤ R` and `d ≥ 1`. -/
theorem miss_fraction {R d c : ℕ} (hd : 1 ≤ d) (hc : c ≤ R) :
    ((d * ((d - 1) ^ c * d ^ (R - c)) : ℕ) : ℝ) =
      (d : ℝ) ^ R * ((d : ℝ) * (1 - 1 / (d : ℝ)) ^ c) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have e : (d : ℝ) ^ R = (d : ℝ) ^ c * (d : ℝ) ^ (R - c) := by
    rw [← pow_add]; congr 1; omega
  have e' : ((d : ℝ) - 1) = d * (1 - 1 / (d : ℝ)) := by field_simp
  push_cast [Nat.cast_sub hd]
  rw [e, e', mul_pow]
  ring

/-! ### Uniform distributions and mixtures -/

/-- Under the uniform distribution, an event has probability `|event| / |Ω|`. -/
theorem toOuterMeasure_unifPMF {Ω : Type*} [Fintype Ω] [Nonempty Ω] (s : Set Ω)
    [DecidablePred (· ∈ s)] :
    (unifPMF Ω).toOuterMeasure s =
      ((univ.filter (· ∈ s)).card : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator_apply, unifPMF_apply]
  rw [← sum_filter, sum_const, nsmul_eq_mul]

theorem card_mul_inv_card (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    (Fintype.card Ω : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- Fubini for a distribution `𝓗` and an independent uniform `ω`. -/
theorem tsum_mul_unif_eq {α Ω : Type*} [Fintype Ω] [Nonempty Ω] (𝓗 : PMF α)
    (Q : α → Ω → Prop) :
    ∑' a, 𝓗 a * (unifPMF Ω).toOuterMeasure {ω | Q a ω} =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * 𝓗.toOuterMeasure {a | Q a ω} := by
  classical
  simp only [PMF.toOuterMeasure_apply, ← tsum_fintype (L := .unconditional _),
    ← ENNReal.tsum_mul_left]
  rw [tsum_comm]
  refine tsum_congr fun ω => tsum_congr fun a => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, unifPMF_apply]
  split_ifs
  · rw [mul_comm]
  · simp

open Classical in
/-- **The assembly of Step 3.** Let `ε ≥ 0`, let `a ∼ 𝓗` and let `ω` be uniform on `Ω` and
independent of `a`.  Suppose that for every fixed `ω` the event `T ω` has `𝓗`-probability at
least `ρ`, and that for every `a` in the support of `𝓗` the number of `ω` with `T ω a` is at most
the number of `ω` with `S (f a ω)` plus `ε |Ω|`.  Then `S (f a ω)` with probability at least
`ρ - ε`. -/
theorem mix_bound {α β Ω : Type*} [Fintype Ω] [Nonempty Ω] (𝓗 : PMF α) (f : α → Ω → β)
    (S : β → Prop) (T : Ω → α → Prop) {ρ ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ ω, ρ ≤ (𝓗.toOuterMeasure {a | T ω a}).toReal)
    (hcount : ∀ a ∈ 𝓗.support,
      ((univ.filter fun ω => T ω a).card : ℝ) ≤
        (univ.filter fun ω => S (f a ω)).card + Fintype.card Ω * ε) :
    ρ - ε ≤ ((𝓗.bind fun a => (unifPMF Ω).map (f a)).toOuterMeasure {b | S b}).toReal := by
  classical
  set c : ℝ≥0∞ := (Fintype.card Ω : ℝ≥0∞)⁻¹ with hc
  have hcc := card_mul_inv_card Ω
  -- per `a` in the support
  have hper : ∀ a ∈ 𝓗.support, (unifPMF Ω).toOuterMeasure {ω | T ω a} ≤
      (unifPMF Ω).toOuterMeasure {ω | S (f a ω)} + ENNReal.ofReal ε := by
    intro a ha
    have h := hcount a ha
    rw [toOuterMeasure_unifPMF, toOuterMeasure_unifPMF]
    have h' : ((univ.filter fun ω => ω ∈ {ω | T ω a}).card : ℝ≥0∞) ≤
        ((univ.filter fun ω => ω ∈ {ω | S (f a ω)}).card : ℝ≥0∞) +
          (Fintype.card Ω : ℝ≥0∞) * ENNReal.ofReal ε := by
      have := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hε),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast] at this
      simpa using this
    calc _ ≤ (((univ.filter fun ω => ω ∈ {ω | S (f a ω)}).card : ℝ≥0∞) +
          (Fintype.card Ω : ℝ≥0∞) * ENNReal.ofReal ε) * c := by gcongr
      _ = _ := by
          rw [add_mul, mul_right_comm, hcc, one_mul]
  -- the mixture
  have hmix : ENNReal.ofReal ρ ≤
      (𝓗.bind fun a => (unifPMF Ω).map (f a)).toOuterMeasure {b | S b} + ENNReal.ofReal ε := by
    calc ENNReal.ofReal ρ = ∑ _ω : Ω, c * ENNReal.ofReal ρ := by
          rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc, hcc, one_mul]
      _ ≤ ∑ ω : Ω, c * 𝓗.toOuterMeasure {a | T ω a} := by
          refine sum_le_sum fun ω _ => ?_
          gcongr
          exact ofReal_le_toOuterMeasure (hT ω)
      _ = ∑' a, 𝓗 a * (unifPMF Ω).toOuterMeasure {ω | T ω a} :=
          (tsum_mul_unif_eq 𝓗 fun a ω => T ω a).symm
      _ ≤ ∑' a, 𝓗 a * ((unifPMF Ω).toOuterMeasure {ω | S (f a ω)} + ENNReal.ofReal ε) := by
          refine tsum_le_tsum fun a => ?_
          by_cases ha : a ∈ 𝓗.support
          · gcongr
            exact hper a ha
          · rw [(PMF.apply_eq_zero_iff 𝓗 a).2 ha, zero_mul, zero_mul]
      _ = _ := by
          simp only [mul_add]
          rw [tsum_add, ENNReal.tsum_mul_right, 𝓗.tsum_coe, one_mul,
            PMF.toOuterMeasure_bind_apply]
          congr 2
          funext a
          rw [PMF.toOuterMeasure_map_apply]
          rfl
  have hne := toOuterMeasure_ne_top (𝓗.bind fun a => (unifPMF Ω).map (f a)) {b | S b}
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne, ENNReal.ofReal_ne_top⟩) hmix
  rw [ENNReal.toReal_add hne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε,
    ENNReal.toReal_ofReal'] at h
  have := le_max_left ρ 0
  linarith

/-! ### The sufficient condition for (c) -/

/-- `x (1 - 1/x)^c ≤ D e^{-r/D}` for reals `1 ≤ x ≤ D` and `0 ≤ r ≤ c`: `(1-1/x)^c ≤ e^{-c/x}`,
and `x e^{-c/x}` is increasing in `x`. -/
theorem weak_term_le {x D r : ℝ} {c : ℕ} (hx : 1 ≤ x) (hxD : x ≤ D) (hr0 : 0 ≤ r)
    (hrc : r ≤ c) : x * (1 - 1 / x) ^ c ≤ D * Real.exp (-(r / D)) := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have h₁ : (1 - 1 / x) ^ c ≤ Real.exp (-(c / x)) := by
    have hb : 1 - 1 / x ≤ Real.exp (-(1 / x)) := by
      have := Real.add_one_le_exp (-(1 / x))
      linarith
    have hnn : 0 ≤ 1 - 1 / x := by
      rw [sub_nonneg, div_le_one hx0]
      exact hx
    calc (1 - 1 / x) ^ c ≤ Real.exp (-(1 / x)) ^ c := pow_le_pow_left₀ hnn hb c
      _ = Real.exp (-(c / x)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have h₂ : Real.exp (-(c / x)) ≤ Real.exp (-(r / D)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    calc r / D ≤ r / x := div_le_div_of_nonneg_left hr0 hx0 hxD
      _ ≤ c / x := div_le_div_of_nonneg_right hrc hx0.le
  calc x * (1 - 1 / x) ^ c ≤ x * Real.exp (-(r / D)) :=
        mul_le_mul_of_nonneg_left (h₁.trans h₂) hx0.le
    _ ≤ D * Real.exp (-(r / D)) := mul_le_mul_of_nonneg_right hxD (Real.exp_pos _).le

end Obl

end OnlineColouring
