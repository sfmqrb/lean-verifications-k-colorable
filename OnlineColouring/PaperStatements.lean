module

public import OnlineColouring.PaperRand
public import OnlineColouring.MainLogStar
public import OnlineColouring.MainTheorem
public import OnlineColouring.StrKnown
public import OnlineColouring.Transfer
public import OnlineColouring.CeilingPadded
public import OnlineColouring.BaseFacts

/-!
# Statements in the paper's literal form

Several results are stated elsewhere in the library in a form that is convenient for proofs:
with the predicates `ChiRandAtLeast` and `OnlineChromaticAtLeast` in place of the numbers
`χ^rand` and `χ_ol`, with `HasAntichain` in place of `width`, and with one theorem for each of the
two graphs of Theorem 1.3.  This file derives the statements as they are written in the paper.

* **Definition 4.1 / Lemma 4.4.** `chiRand_mono` (`χ^rand` is non-decreasing in `n`; for `χ^det`
  this is `chiDet_mono_right`), `yao_chiRand` and `yao_prob_chiRand` (Lemma 4.4, both sentences,
  for the number `chiRand k n`), `yao_known` (the remark after Lemma 4.4: if all graphs in the
  support are presentations of one graph `G`, then every randomized algorithm that knows `G` has
  a presentation of `G` with expected cost at least `x`).
* **`χ_ol`.** `chiOl G` is the online chromatic number of `G` as defined in the introduction (the
  least `c` such that some deterministic online algorithm uses at most `c` colours on every
  presentation order of `G`), and `le_chiOl_iff : K ≤ chiOl G ↔ OnlineChromaticAtLeast G K`.
* **Definition 4.7.** `ordConnected_fiber`, `ordConnected_block`, `ordConnected_subtree`,
  `lt_of_comp_lt`: by condition (i) of Definition 4.6, every full tower is presented subtree by
  subtree (the descendants of a node form an interval of the arrival order, and the intervals come
  in the order of the nodes), as the paper remarks after Definition 4.7.
* **Lemmas 5.5 and 5.6 in terms of `width`** (they are stated with `HasAntichain` in
  `Growth.lean`, `BaseFacts.lean` and `TowerGrowth.lean`): `le_width_jst`,
  `four_le_width_labelPoset_three_two`, `tow_le_width_labelPoset_of_four_le`,
  `tow_le_width_labelPoset_three`.
* **Theorem 1.1 for every admissible number of levels.** `chiRand_ge_of_level`:
  `χ^rand_k(n) ≥ n^{1/(j+1)}/(8(1+ln 4n))` for every `j ≥ 1` with `|P_j(k)| ≥ n` (the chain (8.2));
  `chiRand_ge_of_level_large_three`, `chiRand_ge_of_level_large_of_four_le`:
  `χ^rand_k(n) ≥ n^{1/(j+2)}` for `n ≥ 2^406` (`k ≥ 4`: `n ≥ 2^201`) and every such `j ≤ j₀(n)`
  (Lemma A.1).  The theorem itself, where `j` is the least such number, is `main_logStar_three`,
  `main_logStar_of_four_le` (`MainLogStar.lean`).  `main_logStar_three_least` and
  `main_logStar_of_four_le_least` state it with that `j` and with the two intermediate bounds of
  its proof (`exists_least_level_three`, `exists_least_level_of_four_le`: the least `j` exists
  and is at most `j₀(n)`).
* **Theorem 1.2, last sentence**, in floor form: `floor_rpow_28_le_chiDet_three`,
  `floor_rpow_15_le_chiDet_of_four_le`.
* **Theorem 1.3** with `chiOl`, with `G` and `G′` in one statement, and with *the same* graph `G′`
  for the bound `N^{1/(L+3)}` (`N ≥ 2^406`; `k ≥ 4`: `N^{1/(L+1)}`, `N ≥ 2^201`):
  `known_graphs_three`, `known_graphs_of_four_le`.
* **Theorem 1.4, first sentence**, as written (`∃ j ≤ lg* k' + 1, ∀ N K, …` with `chiDet`):
  `transfer_chiDet`; the sentence after the theorem, `N_k(K) ≤ N_{k'}(K)^{(j+1)(j+2)/2}`:
  `transfer_Nk`.
* **Lemma 7.1** with "by an isomorphism that maps blocks to blocks" in its conclusion:
  `blowSeq_iso_blocks` (`SeqIso.blowSeq` of `Iso.lean` states the isomorphism only).
-/

@[expose] public section

namespace OnlineColouring

namespace Paper

open Finset

/-! ### Definition 4.1 and Lemma 4.4 -/

/-- **"Both quantities are non-decreasing in `n`"**, for `χ^rand` (for `χ^det`:
`chiDet_mono_right`). -/
theorem chiRand_mono {k m n : ℕ} (hk : 1 ≤ k) (hmn : m ≤ n) : chiRand k m ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (((le_chiRand_iff hk).1 le_rfl).mono hk hmn)

/-- **Lemma 4.4 (Yao's principle), first sentence**, with the number `χ^rand_k(n)`. -/
theorem yao_chiRand {k N n : ℕ} {x : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n) (D : PMF (OnlineInput N))
    (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → x ≤ detExpCost D A) : x ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (yao_expectation hk hNn D hcol hforce)

/-- **Lemma 4.4 (Yao's principle), second sentence**, with the number `χ^rand_k(n)`. -/
theorem yao_prob_chiRand {k N n K : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hNn : N ≤ n)
    (D : PMF (OnlineInput N)) (hcol : ∀ I ∈ D.support, I.graph.Colorable k)
    (hforce : ∀ A : OnlineAlg, A.IsProper → 1 - ε ≤ probAtLeast D A K) :
    (1 - ε) * K ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (yao hk hNn D hcol hforce)

/-- **The remark after Lemma 4.4.** If all graphs in the support of `D` are presentations of one
graph `G`, then every randomized algorithm that knows `G` in advance has a presentation order of
`G` on which it uses at least `x` colours in expectation. -/
theorem yao_known {N : ℕ} {x : ℝ} (G : SimpleGraph (Fin N)) (D : PMF (OnlineInput N))
    (hiso : ∀ I ∈ D.support, Nonempty (I.graph ≃g G))
    (hforce : ∀ A : OnlineAlg, A.IsProper → x ≤ detExpCost D A) : RandKnownAtLeast G x := by
  intro μ hμ
  obtain ⟨I, hI, hx⟩ := exists_support_le_expCost D hforce μ hμ
  exact ⟨I, hiso I hI, hx⟩

/-! ### The online chromatic number of a graph -/

/-- **`χ_ol(G)`** (paragraph "Known graphs" of the introduction): the least `c` such that some
(proper) deterministic online algorithm uses at most `c` colours on every presentation order of
`G`, i.e. on every online input whose graph is isomorphic to `G`. -/
noncomputable def chiOl {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ :=
  sInf {c | ∃ A : OnlineAlg, A.IsProper ∧
    ∀ I : OnlineInput N, Nonempty (I.graph ≃g G) → I.cost A ≤ c}

/-- `χ_ol(G) ≥ K` holds exactly when every proper deterministic online algorithm uses at least
`K` colours on some presentation of `G`. -/
theorem le_chiOl_iff {N : ℕ} {G : SimpleGraph (Fin N)} {K : ℕ} :
    K ≤ chiOl G ↔ OnlineChromaticAtLeast G K := by
  have hne : {c | ∃ A : OnlineAlg, A.IsProper ∧
      ∀ I : OnlineInput N, Nonempty (I.graph ≃g G) → I.cost A ≤ c}.Nonempty :=
    ⟨N, OnlineAlg.firstFit, OnlineAlg.firstFit_isProper, fun I _ => I.cost_le _⟩
  constructor
  · intro hK A hA
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos K with rfl | hpos
    · exact absurd (hcon (OnlineInput.ofGraph G)
        ⟨by rw [OnlineInput.graph_ofGraph]⟩) (Nat.not_lt_zero _)
    · have hmem : K - 1 ∈ {c | ∃ A : OnlineAlg, A.IsProper ∧
          ∀ I : OnlineInput N, Nonempty (I.graph ≃g G) → I.cost A ≤ c} :=
        ⟨A, hA, fun I hI => by have := hcon I hI; omega⟩
      have := hK.trans (Nat.sInf_le hmem)
      omega
  · intro h
    apply le_csInf hne
    rintro c ⟨A, hA, hc⟩
    obtain ⟨I, hI, hK⟩ := h A hA
    exact hK.trans (hc I hI)

/-- `χ_ol(G) ≥ x` for a real `x`, from `χ_ol(G) ≥ ⌈x⌉`. -/
theorem le_chiOl_of_ceil {N : ℕ} {G : SimpleGraph (Fin N)} {x : ℝ}
    (h : OnlineChromaticAtLeast G ⌈x⌉₊) : x ≤ (chiOl G : ℝ) :=
  (Nat.le_ceil x).trans (by exact_mod_cast le_chiOl_iff.2 h)

/-! ### Definition 4.7: "presented subtree by subtree" is automatic -/

/-- If `p x < p y → x < y` (condition (i) of Definition 4.6 for a block map, and for every
composite of block maps), then every fibre of `p` is an interval of the arrival order. -/
theorem ordConnected_fiber {V W : Type*} [LinearOrder V] [LinearOrder W] {p : W → V}
    (hp : ∀ ⦃x y : W⦄, p x < p y → x < y) (v : V) : (p ⁻¹' {v}).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hx' : p x = v := hx
  have hy' : p y = v := hy
  change p z = v
  rcases lt_trichotomy (p z) v with h | h | h
  · exact absurd (hp (hx' ▸ h)) (not_lt.2 hz.1)
  · exact h
  · exact absurd (hp (hy' ▸ h)) (not_lt.2 hz.2)

/-- Condition (i) is closed under composition of block maps. -/
theorem lt_of_comp_lt {U V W : Type*} [LinearOrder U] [LinearOrder V] [LinearOrder W]
    {p : W → V} {q : V → U} (hp : ∀ ⦃x y : W⦄, p x < p y → x < y)
    (hq : ∀ ⦃x y : V⦄, q x < q y → x < y) ⦃x y : W⦄ (h : q (p x) < q (p y)) : x < y :=
  hp (hq h)

/-- The blocks of a blow-up are intervals of the arrival order (and they come in the order of
`H`, by `BlowUp.lt_of_π_lt`). -/
theorem ordConnected_block {V W : Type*} [LinearOrder V] [LinearOrder W] {H : SimpleGraph V}
    {G : SimpleGraph W} (B : BlowUp H G) (v : V) : (B.π ⁻¹' {v}).OrdConnected :=
  ordConnected_fiber B.lt_of_π_lt v

/-- **Every full tower is presented subtree by subtree**: the descendants of a top vertex form an
interval of the arrival order (and these intervals come in the order of the top vertices, by
`IsFullTowerAnc.lt_of_lt`).  The same holds for the nodes of every level, by
`ordConnected_block` and `lt_of_comp_lt`. -/
theorem ordConnected_subtree {m j : ℕ} {G : OrdGraph} {τ : G.V → Fin m}
    (hT : IsFullTowerAnc m j G τ) (t : Fin m) : (τ ⁻¹' {t}).OrdConnected :=
  ordConnected_fiber (fun _ _ h => hT.lt_of_lt h) t

/-! ### Lemmas 5.5 and 5.6 in terms of `width` -/

/-- **Lemma 5.5 (i), width.** If `P` has an antichain of size `w ≥ 1`, then
`width(J*(P)) ≥ choose w ⌊w/2⌋`. -/
theorem le_width_jst {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    {A : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P)) (hw : 1 ≤ A.card) :
    A.card.choose (A.card / 2) ≤ width (Jst P) :=
  le_width_iff.2 (HasAntichain.jst ⟨A, hA, rfl⟩ hw)

/-- **Lemma 5.5 (iii).** `width(P_2(3)) ≥ 4`. -/
theorem four_le_width_labelPoset_three_two : 4 ≤ width (LabelPoset 3 2) :=
  le_width_iff.2 hasAntichain_labelPoset_three_two

/-- **Lemma 5.6, `k ≥ 4`.** `width(P_j(k)) ≥ tow(j+1)`. -/
theorem tow_le_width_labelPoset_of_four_le {k : ℕ} (hk : 4 ≤ k) (j : ℕ) :
    tow (j + 1) ≤ width (LabelPoset k j) :=
  le_width_iff.2 (hasAntichain_labelPoset_of_four_le hk j)

/-- **Lemma 5.6, `k = 3`.** `width(P_j(3)) ≥ tow(j-1)` for `j ≥ 2`. -/
theorem tow_le_width_labelPoset_three {j : ℕ} (hj : 2 ≤ j) :
    tow (j - 1) ≤ width (LabelPoset 3 j) :=
  le_width_iff.2 (hasAntichain_labelPoset_three hj)

/-! ### Theorem 1.1 for every admissible number of levels -/

/-- (8.2) for `χ^rand`, for every level count: if `j ≥ 1` and `|P_j(k)| ≥ n ≥ 1`, then
`χ^rand_k(n) ≥ n^{1/(j+1)} / (8 (1 + ln 4n))`. -/
theorem chiRand_ge_of_level {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hP : n ≤ Fintype.card (LabelPoset k j)) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand k n :=
  (le_chiRand_iff hk).2 (uniform_rpow_div ChiRandAtLeast chiRand_hmono chiRand_hpad
    Rjm.chiRand_hcore chiRand_hbase hk hn hj hP)

/-- The second sentence of Theorem 1.1 for every admissible level count, `k = 3`: if
`n ≥ 2^406`, `1 ≤ j ≤ lg* n + 1` and `|P_j(3)| ≥ n`, then `χ^rand_3(n) ≥ n^{1/(j+2)}`
(Theorem 8.5 with Lemma A.1). -/
theorem chiRand_ge_of_level_large_three {n j : ℕ} (hn : 2 ^ 406 ≤ n) (hj : 1 ≤ j)
    (hjL : j ≤ logStar n + 1) (hP : n ≤ Fintype.card (LabelPoset 3 j)) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ chiRand 3 n := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  obtain ⟨hM, hle⟩ := threshold_three hn hj hjL
  exact (le_chiRand_iff (by norm_num)).2 (chiRand_hmono 3 n _ _ (by norm_num)
    (uniform_step ChiRandAtLeast chiRand_hmono chiRand_hpad Rjm.chiRand_hcore (by norm_num) hn1 hj
      hP hM) hle)

/-- The second sentence of Theorem 1.1 for every admissible level count, `k ≥ 4`: if
`n ≥ 2^201`, `1 ≤ j ≤ max(1, lg* n - 1)` and `|P_j(k)| ≥ n`, then `χ^rand_k(n) ≥ n^{1/(j+2)}`. -/
theorem chiRand_ge_of_level_large_of_four_le {k n j : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n)
    (hj : 1 ≤ j) (hjL : j ≤ max 1 (logStar n - 1)) (hP : n ≤ Fintype.card (LabelPoset k j)) :
    (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ chiRand k n := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  obtain ⟨hM, hle⟩ := threshold_four hn hj hjL
  exact (le_chiRand_iff (by omega)).2 (chiRand_hmono k n _ _ (by omega)
    (uniform_step ChiRandAtLeast chiRand_hmono chiRand_hpad Rjm.chiRand_hcore (by omega) hn1 hj
      hP hM) hle)

/-! ### Theorem 1.1 with the least number of levels in the statement -/

/-- **The choice of `j` in the proof of Theorem 1.1, `k = 3`:** the least `j ≥ 1` with
`|P_j(3)| ≥ n` exists and is at most `lg* n + 1` (Corollary 5.7 with `K = n`).  It is
`Rjm.jMin 3 n`. -/
theorem exists_least_level_three {n : ℕ} (hn : 2 ≤ n) :
    ∃ j, 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset 3 j) ∧
      (∀ i, 1 ≤ i → i < j → ¬ n ≤ Fintype.card (LabelPoset 3 i)) ∧ j ≤ logStar n + 1 := by
  obtain ⟨hj, hP⟩ := Rjm.jMin_spec (k := 3) (n := n) (J := logStar n + 1) (by omega)
    (le_card_labelPoset_three hn)
  exact ⟨Rjm.jMin 3 n, hj, hP, fun i hi hlt hni => absurd (Rjm.jMin_le hi hni) (by omega),
    Rjm.jMin_three_le hn⟩

/-- **The choice of `j` in the proof of Theorem 1.1, `k ≥ 4`:** the least `j ≥ 1` with
`|P_j(k)| ≥ n` exists and is at most `max(1, lg* n - 1)`, which is `lg* n - 1` for `n ≥ 3`.  It is
`Rjm.jMin k n`. -/
theorem exists_least_level_of_four_le {k : ℕ} (hk : 4 ≤ k) (n : ℕ) :
    ∃ j, 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset k j) ∧
      (∀ i, 1 ≤ i → i < j → ¬ n ≤ Fintype.card (LabelPoset k i)) ∧
      j ≤ max 1 (logStar n - 1) := by
  obtain ⟨hj, hP⟩ := Rjm.jMin_spec (k := k) (n := n) (J := max 1 (logStar n - 1))
    (le_max_left _ _) (le_card_labelPoset_of_four_le hk n)
  exact ⟨Rjm.jMin k n, hj, hP, fun i hi hlt hni => absurd (Rjm.jMin_le hi hni) (by omega),
    Rjm.jMin_le_of_four_le hk n⟩

/-- **Theorem 1.1, `k = 3`, with the number of levels of its proof.** For `n ≥ 3`, `L = lg* n` and
the least `j ≥ 1` with `|P_j(3)| ≥ n`: `j ≤ L + 1`,
`χ^rand_3(n) ≥ n^{1/(j+1)}/(8(1+ln 4n)) ≥ n^{1/(L+2)}/(8(1+ln 4n))`, `χ^det_3(n) ≥ χ^rand_3(n)`,
and for `n ≥ 2^406`, `χ^rand_3(n) ≥ n^{1/(j+2)} ≥ n^{1/(L+3)}`. -/
theorem main_logStar_three_least {n : ℕ} (hn : 3 ≤ n) :
    ∃ j, 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset 3 j) ∧
      (∀ i, 1 ≤ i → i < j → ¬ n ≤ Fintype.card (LabelPoset 3 i)) ∧ j ≤ logStar n + 1 ∧
      (n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤
        (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ∧
      (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand 3 n ∧
      chiRand 3 n ≤ chiDet 3 n ∧
      (2 ^ 406 ≤ n → (n : ℝ) ^ (1 / (logStar n + 3 : ℝ)) ≤ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ∧
        (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ chiRand 3 n) := by
  obtain ⟨j, hj, hP, hmin, hjL⟩ := exists_least_level_three (n := n) (by omega)
  have hn1 : 1 ≤ n := by omega
  have hjR : (j : ℝ) ≤ (logStar n : ℝ) + 1 := by exact_mod_cast hjL
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hden : (0 : ℝ) ≤ 8 * (1 + Real.log (4 * n)) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * n by linarith)
    positivity
  refine ⟨j, hj, hP, hmin, hjL, ?_, chiRand_ge_of_level (by norm_num) hn1 hj hP,
    chiRand_le_chiDet (by norm_num), fun h406 => ⟨?_, chiRand_ge_of_level_large_three h406 hj hjL
      hP⟩⟩
  · exact div_le_div_of_nonneg_right (Rjm.rpow_inv_anti hn1 (by linarith) (by linarith)) hden
  · exact Rjm.rpow_inv_anti hn1 (by linarith) (by linarith)

/-- **Theorem 1.1, `k ≥ 4`, with the number of levels of its proof.** For `n ≥ 3`, `L = lg* n` and
the least `j ≥ 1` with `|P_j(k)| ≥ n`: `j ≤ L - 1`,
`χ^rand_k(n) ≥ n^{1/(j+1)}/(8(1+ln 4n)) ≥ n^{1/L}/(8(1+ln 4n))`, `χ^det_k(n) ≥ χ^rand_k(n)`, and
for `n ≥ 2^201`, `χ^rand_k(n) ≥ n^{1/(j+2)} ≥ n^{1/(L+1)}`. -/
theorem main_logStar_of_four_le_least {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) :
    ∃ j, 1 ≤ j ∧ n ≤ Fintype.card (LabelPoset k j) ∧
      (∀ i, 1 ≤ i → i < j → ¬ n ≤ Fintype.card (LabelPoset k i)) ∧ j ≤ logStar n - 1 ∧
      (n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤
        (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ∧
      (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand k n ∧
      chiRand k n ≤ chiDet k n ∧
      (2 ^ 201 ≤ n → (n : ℝ) ^ (1 / (logStar n + 1 : ℝ)) ≤ (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ∧
        (n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 2)) ≤ chiRand k n) := by
  obtain ⟨j, hj, hP, hmin, hjL⟩ := exists_least_level_of_four_le hk n
  have hL := two_le_logStar hn
  have hjL' : j ≤ logStar n - 1 := by omega
  have hn1 : 1 ≤ n := by omega
  have hjR : (j : ℝ) + 1 ≤ (logStar n : ℝ) := by
    have : j + 1 ≤ logStar n := by omega
    exact_mod_cast this
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hden : (0 : ℝ) ≤ 8 * (1 + Real.log (4 * n)) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * n by linarith)
    positivity
  refine ⟨j, hj, hP, hmin, hjL', ?_, chiRand_ge_of_level (by omega) hn1 hj hP,
    chiRand_le_chiDet (by omega), fun h201 => ⟨?_, chiRand_ge_of_level_large_of_four_le hk h201
      hj hjL hP⟩⟩
  · exact div_le_div_of_nonneg_right (Rjm.rpow_inv_anti hn1 (by linarith) (by linarith)) hden
  · exact Rjm.rpow_inv_anti hn1 (by linarith) (by linarith)

/-! ### Theorem 1.2, last sentence, floor form -/

/-- **Theorem 1.2, last sentence, `k = 3`:** `χ^det_3(n) ≥ ⌊n^{1/28}⌋` for `3 ≤ n ≤ 2^65536`. -/
theorem floor_rpow_28_le_chiDet_three {n : ℕ} (hn : 3 ≤ n) (hn' : n ≤ 2 ^ 65536) :
    ⌊(n : ℝ) ^ ((1 : ℝ) / 28)⌋₊ ≤ chiDet 3 n := by
  set K := ⌊(n : ℝ) ^ ((1 : ℝ) / 28)⌋₊ with hKdef
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have h1 : 1 ≤ chiDet 3 n := (le_chiDet_iff (by norm_num)).2 (chiDetAtLeast_one (by norm_num)
      (by omega))
    omega
  · refine (le_chiDet_iff (by norm_num)).2 (chiDetAtLeast_three_of_le_tow_five hn' hK ?_)
    have h := floor_rpow_pow_le (n := n) (c := 56) (by norm_num) (by decide)
    have e : (2 : ℝ) / ((56 : ℕ) : ℝ) = (1 : ℝ) / 28 := by norm_num
    rw [e] at h
    exact h

/-- **Theorem 1.2, last sentence, `k ≥ 4`:** `χ^det_k(n) ≥ ⌊n^{1/15}⌋` for `3 ≤ n ≤ 2^65536`. -/
theorem floor_rpow_15_le_chiDet_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n)
    (hn' : n ≤ 2 ^ 65536) : ⌊(n : ℝ) ^ ((1 : ℝ) / 15)⌋₊ ≤ chiDet k n := by
  set K := ⌊(n : ℝ) ^ ((1 : ℝ) / 15)⌋₊ with hKdef
  rcases Nat.lt_or_ge K 2 with hK | hK
  · have h1 : 1 ≤ chiDet k n := (le_chiDet_iff (by omega)).2 (chiDetAtLeast_one (by omega)
      (by omega))
    omega
  · refine (le_chiDet_iff (by omega)).2
      (chiDetAtLeast_of_four_le_of_le_tow_five hn hn' hk hK ?_)
    have h := floor_rpow_pow_le (n := n) (c := 30) (by norm_num) (by decide)
    have e : (2 : ℝ) / ((30 : ℕ) : ℝ) = (1 : ℝ) / 15 := by norm_num
    rw [e] at h
    exact h

/-! ### Theorem 1.3 with `χ_ol`, and with one graph `G′` for both bounds -/

/-- The uniform tower with `j` levels, padded to `N` vertices, as a known graph: one graph `G′`
carries every bound up to `(2M-1)/(4(1+ln 4M))`, `M = (N/2^j)^{1/(j+1)}`. -/
theorem exists_known_graph_of_level {k N j : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) (hj : 1 ≤ j)
    (hP : N ≤ Fintype.card (LabelPoset k j)) (hM : 2 ≤ levelM N j) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧
      ∀ x : ℝ, x ≤ xLower (levelM N j) → OnlineChromaticAtLeast G ⌈x⌉₊ ∧ RandKnownAtLeast G x := by
  obtain ⟨G, hc, hf, hdet, hrand⟩ :=
    uniform_step KnownQ knownQ_hmono knownQ_hpad Rjm.knownQ_hcore hk hN hj hP hM
  exact ⟨G, hc, hf, fun x hx => ⟨hdet.mono (Nat.ceil_mono hx), hrand.mono hx⟩⟩

/-- **Theorem 1.3 (known graphs), `k = 3`, as stated.** For every `N ≥ 3` and `L = lg* N` there
are triangle-free `3`-colourable graphs `G` and `G′` on `N` vertices with
`χ_ol(G) ≥ ⌊N^{2/((L+2)(L+3))}⌋` and `χ_ol(G′) ≥ N^{1/(L+2)}/(8(1+ln 4N))`; every randomized
online algorithm that knows `G′` has a presentation order of `G′` with expected cost at least
`N^{1/(L+2)}/(8(1+ln 4N))`; and for `N ≥ 2^406` both bounds hold for the same `G′` with
`N^{1/(L+3)}`. -/
theorem known_graphs_three {N : ℕ} (hN : 3 ≤ N) :
    ∃ G G' : SimpleGraph (Fin N),
      G.Colorable 3 ∧ G.CliqueFree 3 ∧ G'.Colorable 3 ∧ G'.CliqueFree 3 ∧
      ⌊(N : ℝ) ^ ((2 : ℝ) / ((logStar N + 2) * (logStar N + 3)))⌋₊ ≤ chiOl G ∧
      (N : ℝ) ^ (1 / (logStar N + 2 : ℝ)) / (8 * (1 + Real.log (4 * N))) ≤ (chiOl G' : ℝ) ∧
      RandKnownAtLeast G' ((N : ℝ) ^ (1 / (logStar N + 2 : ℝ)) / (8 * (1 + Real.log (4 * N)))) ∧
      (2 ^ 406 ≤ N → (N : ℝ) ^ (1 / (logStar N + 3 : ℝ)) ≤ (chiOl G' : ℝ) ∧
        RandKnownAtLeast G' ((N : ℝ) ^ (1 / (logStar N + 3 : ℝ)))) := by
  obtain ⟨G, hGc, hGf, hG⟩ := known_graph_three_floor hN
  by_cases h406 : 2 ^ 406 ≤ N
  · -- `G′` is the uniform tower with the least number of levels, as in the paper
    obtain ⟨hj, hnP⟩ := Rjm.jMin_spec (k := 3) (n := N) (J := logStar N + 1) (by omega)
      (le_card_labelPoset_three (by omega))
    have hjL := Rjm.jMin_three_le (n := N) (by omega)
    obtain ⟨hM, hle⟩ := threshold_three h406 hj hjL
    obtain ⟨G', hc, hf, hall⟩ := exists_known_graph_of_level (k := 3) (N := N)
      (j := Rjm.jMin 3 N) (by norm_num) (by omega) hj hnP hM
    have hN1 : 1 ≤ N := by omega
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hjR : ((Rjm.jMin 3 N : ℕ) : ℝ) ≤ (logStar N : ℝ) + 1 := by exact_mod_cast hjL
    have hlog : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    have ha : (N : ℝ) ^ (1 / (logStar N + 2 : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / ((Rjm.jMin 3 N : ℝ) + 1)) :=
      Rjm.rpow_inv_anti hN1 (by positivity) (by linarith)
    have hb : (N : ℝ) ^ (1 / (logStar N + 3 : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / ((Rjm.jMin 3 N : ℝ) + 2)) :=
      Rjm.rpow_inv_anti hN1 (by positivity) (by linarith)
    have h1 := (div_le_div_of_nonneg_right ha
      (by linarith : (0 : ℝ) ≤ 8 * (1 + Real.log (4 * N)))).trans (rpow_div_le_xLower hN1 hM)
    have h2 := hb.trans hle
    exact ⟨G, G', hGc, hGf, hc, hf, le_chiOl_iff.2 hG, le_chiOl_of_ceil (hall _ h1).1,
      (hall _ h1).2, fun _ => ⟨le_chiOl_of_ceil (hall _ h2).1, (hall _ h2).2⟩⟩
  · obtain ⟨G', hc, hf, hdet, hrand⟩ := known_graph_uniform_three hN
    exact ⟨G, G', hGc, hGf, hc, hf, le_chiOl_iff.2 hG, le_chiOl_of_ceil hdet, hrand,
      fun h => absurd h h406⟩

/-- **Theorem 1.3 (known graphs), `k ≥ 4`, as stated**: the same for `k`-colourable graphs, with
exponents `2/(L(L+1))` and `1/L`, and with `N^{1/(L+1)}` for `N ≥ 2^201`. -/
theorem known_graphs_of_four_le {k N : ℕ} (hk : 4 ≤ k) (hN : 3 ≤ N) :
    ∃ G G' : SimpleGraph (Fin N),
      G.Colorable k ∧ G.CliqueFree 3 ∧ G'.Colorable k ∧ G'.CliqueFree 3 ∧
      ⌊(N : ℝ) ^ ((2 : ℝ) / (logStar N * (logStar N + 1)))⌋₊ ≤ chiOl G ∧
      (N : ℝ) ^ (1 / (logStar N : ℝ)) / (8 * (1 + Real.log (4 * N))) ≤ (chiOl G' : ℝ) ∧
      RandKnownAtLeast G' ((N : ℝ) ^ (1 / (logStar N : ℝ)) / (8 * (1 + Real.log (4 * N)))) ∧
      (2 ^ 201 ≤ N → (N : ℝ) ^ (1 / (logStar N + 1 : ℝ)) ≤ (chiOl G' : ℝ) ∧
        RandKnownAtLeast G' ((N : ℝ) ^ (1 / (logStar N + 1 : ℝ)))) := by
  obtain ⟨G, hGc, hGf, hG⟩ := known_graph_of_four_le_floor hN hk
  have hL := two_le_logStar hN
  by_cases h201 : 2 ^ 201 ≤ N
  · obtain ⟨hj, hnP⟩ := Rjm.jMin_spec (k := k) (n := N) (J := max 1 (logStar N - 1))
      (le_max_left _ _) (le_card_labelPoset_of_four_le hk N)
    have hjL := Rjm.jMin_le_of_four_le hk N
    obtain ⟨hM, hle⟩ := threshold_four h201 hj hjL
    obtain ⟨G', hc, hf, hall⟩ := exists_known_graph_of_level (k := k) (N := N)
      (j := Rjm.jMin k N) (by omega) (by omega) hj hnP hM
    have hN1 : 1 ≤ N := by omega
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hjR : ((Rjm.jMin k N : ℕ) : ℝ) + 1 ≤ (logStar N : ℝ) := by
      have : Rjm.jMin k N + 1 ≤ logStar N := by omega
      exact_mod_cast this
    have hlog : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    have ha : (N : ℝ) ^ (1 / (logStar N : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / ((Rjm.jMin k N : ℝ) + 1)) :=
      Rjm.rpow_inv_anti hN1 (by positivity) hjR
    have hb : (N : ℝ) ^ (1 / (logStar N + 1 : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / ((Rjm.jMin k N : ℝ) + 2)) :=
      Rjm.rpow_inv_anti hN1 (by positivity) (by linarith)
    have h1 := (div_le_div_of_nonneg_right ha
      (by linarith : (0 : ℝ) ≤ 8 * (1 + Real.log (4 * N)))).trans (rpow_div_le_xLower hN1 hM)
    have h2 := hb.trans hle
    exact ⟨G, G', hGc, hGf, hc, hf, le_chiOl_iff.2 hG, le_chiOl_of_ceil (hall _ h1).1,
      (hall _ h1).2, fun _ => ⟨le_chiOl_of_ceil (hall _ h2).1, (hall _ h2).2⟩⟩
  · obtain ⟨G', hc, hf, hdet, hrand⟩ := known_graph_uniform_of_four_le hk hN
    exact ⟨G, G', hGc, hGf, hc, hf, le_chiOl_iff.2 hG, le_chiOl_of_ceil hdet, hrand,
      fun h => absurd h h201⟩

/-! ### Theorem 1.4, first sentence -/

/-- **Theorem 1.4 (transfer between values of `k`), first sentence, as stated.** Let
`k, k' ≥ 3`.  There is `j ≤ lg* k' + 1` such that for all `N` and all `K ≥ 2`, if
`χ^det_{k'}(N) ≥ K` then `χ^det_k(N^{(j+1)(j+2)/2}) ≥ K`. -/
theorem transfer_chiDet {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k') :
    ∃ j ≤ logStar k' + 1, ∀ N K : ℕ, 2 ≤ K → K ≤ chiDet k' N →
      K ≤ chiDet k (N ^ ((j + 1) * (j + 2) / 2)) := by
  obtain ⟨j, hj, -, h⟩ := transfer (k' := k') hk
  exact ⟨j, hj, fun N K hK hle => (le_chiDet_iff (by omega)).2
    (h K N hK ((le_chiDet_iff (by omega)).1 hle))⟩

/-- **The sentence after Theorem 1.4.** Let `k, k' ≥ 3`.  There is `j ≤ lg* k' + 1` such that
`N_k(K) ≤ N_{k'}(K)^{(j+1)(j+2)/2}` for every `K ≥ 2`, where `N_k(K)` is the least number of
vertices with which an adversary can force `K` colours on `k`-colourable graphs (`⊤` if there is
no such adversary; the inequality is one of extended natural numbers).  This is Theorem 1.4 read
through Observation 4.3 (`Det.le_chiDet_iff_Nk_le`), with the same `j`. -/
theorem transfer_Nk {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k') :
    ∃ j ≤ logStar k' + 1, ∀ K : ℕ, 2 ≤ K → Nk k K ≤ Nk k' K ^ ((j + 1) * (j + 2) / 2) := by
  obtain ⟨j, hj, h⟩ := transfer_chiDet hk hk'
  refine ⟨j, hj, fun K hK => ?_⟩
  have he : (j + 1) * (j + 2) / 2 ≠ 0 := by
    have : 2 ≤ (j + 1) * (j + 2) := by nlinarith
    omega
  rcases eq_or_ne (Nk k' K) ⊤ with htop | hne
  · rw [htop, ENat.top_pow he]
    exact le_top
  · obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
    have h1 : K ≤ chiDet k' N := (Det.le_chiDet_iff_Nk_le (by omega)).2 hN.ge
    have h2 := (Det.le_chiDet_iff_Nk_le (by omega)).1 (h N K hK h1)
    rw [← hN]
    exact_mod_cast h2

/-! ### Lemma 7.1 with "maps blocks to blocks" -/

/-- **Lemma 7.1 (the server assignment does not matter), as stated.** If `φ` is an isomorphism
between the digraphs on the first `m` vertices of `H` and `H'`, all out-degrees are at most `R`,
and `σ`, `σ'` are server assignments, then the two blow-ups with blocks of size `R` are isomorphic
by an isomorphism `Ψ` that maps blocks to blocks: the block of `w` goes to the block of `φ w`
(`x / R` is the index of the block of the vertex `x`). -/
theorem blowSeq_iso_blocks {R : ℕ} {H H' : ℕ → Finset ℕ} {σ σ' : ℕ → ℕ → ℕ} {m : ℕ}
    (hR : 0 < R) (hσ : BlockPerm R σ) (hσ' : BlockPerm R σ')
    (hdeg : ∀ w < m, postDeg H m w ≤ R) (hdeg' : ∀ w < m, postDeg H' m w ≤ R)
    (φ : Fin m ≃ Fin m) (hφ : ∀ u v : Fin m, (u : ℕ) ∈ H v ↔ (φ u : ℕ) ∈ H' (φ v)) :
    ∃ Ψ : Fin (m * R) ≃ Fin (m * R),
      (∀ x u : Fin (m * R), (x : ℕ) ∈ blowSeq R H σ u ↔ (Ψ x : ℕ) ∈ blowSeq R H' σ' (Ψ u)) ∧
      ∀ x : Fin (m * R), (Ψ x : ℕ) / R = (φ x.divNat : ℕ) := by
  let f : Fin m → Fin m → Fin R := fun w v => ⟨σ w (rank H w v), hσ.lt _ _⟩
  let g : Fin m → Fin m → Fin R := fun w v => ⟨σ' (φ w) (rank H' (φ w) (φ v)), hσ'.lt _ _⟩
  let s : Fin m → Set (Fin m) := fun w => {v | (w : ℕ) ∈ H v}
  have hf : ∀ w, Set.InjOn (f w) (s w) := by
    intro w v₁ hv₁ v₂ hv₂ he
    have he' : σ w (rank H w v₁) = σ w (rank H w v₂) := congrArg Fin.val he
    have hr := hσ.inj w _ _ (rank_lt_of_postDeg (hdeg w w.2) v₁.2 hv₁)
      (rank_lt_of_postDeg (hdeg w w.2) v₂.2 hv₂) he'
    exact Fin.ext (rank_inj hv₁ hv₂ hr)
  have hg : ∀ w, Set.InjOn (g w) (s w) := by
    intro w v₁ hv₁ v₂ hv₂ he
    have hv₁' : (φ w : ℕ) ∈ H' (φ v₁) := (hφ w v₁).1 hv₁
    have hv₂' : (φ w : ℕ) ∈ H' (φ v₂) := (hφ w v₂).1 hv₂
    have he' : σ' (φ w) (rank H' (φ w) (φ v₁)) = σ' (φ w) (rank H' (φ w) (φ v₂)) :=
      congrArg Fin.val he
    have hr := hσ'.inj (φ w) _ _ (rank_lt_of_postDeg (hdeg' _ (φ w).2) (φ v₁).2 hv₁')
      (rank_lt_of_postDeg (hdeg' _ (φ w).2) (φ v₂).2 hv₂') he'
    exact φ.injective (Fin.ext (rank_inj hv₁' hv₂' hr))
  choose π hπ using fun w => exists_perm_extend (hf w) (hg w)
  let Ψ : Fin (m * R) ≃ Fin (m * R) :=
    (finProdFinEquiv.symm.trans (Equiv.prodShear φ π)).trans finProdFinEquiv
  have hΨ : ∀ x : Fin (m * R),
      (Ψ x : ℕ) = (π x.divNat x.modNat : ℕ) + R * (φ x.divNat : ℕ) := fun x => rfl
  have hΨdiv : ∀ x : Fin (m * R), (Ψ x : ℕ) / R = φ x.divNat := by
    intro x
    rw [hΨ, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (π _ _).2, Nat.zero_add]
  have hΨmod : ∀ x : Fin (m * R), (Ψ x : ℕ) % R = π x.divNat x.modNat := by
    intro x
    rw [hΨ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (π _ _).2]
  refine ⟨Ψ, fun x u => ?_, hΨdiv⟩
  rw [mem_blowSeq_iff_mod hR hσ, mem_blowSeq_iff_mod hR hσ', hΨdiv, hΨdiv, hΨmod]
  change (x.divNat : ℕ) ∈ H u.divNat ∧ (x.modNat : ℕ) = σ x.divNat (rank H x.divNat u.divNat) ↔
    (φ x.divNat : ℕ) ∈ H' (φ u.divNat) ∧
      (π x.divNat x.modNat : ℕ) = σ' (φ x.divNat) (rank H' (φ x.divNat) (φ u.divNat))
  rw [← hφ]
  constructor
  · rintro ⟨hw, ht⟩
    refine ⟨hw, ?_⟩
    have : x.modNat = f x.divNat u.divNat := Fin.ext ht
    rw [this, hπ _ _ hw]
  · rintro ⟨hw, ht⟩
    refine ⟨hw, ?_⟩
    have h₁ : π x.divNat x.modNat = g x.divNat u.divNat := Fin.ext ht
    rw [← hπ _ _ hw] at h₁
    exact congrArg Fin.val ((π x.divNat).injective h₁)

end Paper

end OnlineColouring
