module

public import OnlineColouring.Forcing
public import OnlineColouring.TowerGrowth

/-!
# Theorem 1.4 (transfer between values of `k`), first sentence

Theorem 1.4: *let `k, k' ≥ 3`.  There is `j ≤ lg* k' + 1` such that for all `N` and all `K ≥ 2`,
if `χ^det_{k'}(N) ≥ K` then `χ^det_k(N^{(j+1)(j+2)/2}) ≥ K`.*

The proof replaces the clique at the top of the iterated reservation adversary by an arbitrary
top that forces `K` colours on `k'`-colourable graphs with `N` vertices.  Its graphs map to
`Tmpl(P_j(k))` when `width(P_j(k)) ≥ k'` (Lemma 5.1 (ii)), so after `j` reservation blow-ups
they map to `Tmpl(P_0(k))`, i.e. they are `k`-colourable (Lemma 5.2).  The first block size is
`(K-1)(N-2)+1` and each later one is `(K-1)(b-1)+1` for the previous `b`.

## Formalization

`χ^det_{k'}(N) ≥ K` is `ChiDetAtLeast k' N K`: every proper algorithm uses `K` colours on some
`k'`-colourable input on `N` vertices.  The proof works with these inputs directly, so it does
not pass through adversaries and Observation 4.3, as the paper's does.

* `ForcesWith P K m D`: for every proper algorithm there is an input sequence whose first `m`
  vertices have post-degree at most `D`, have a `P`-labelling, and receive at least `K` colours.
  This generalizes the invariant of `forcing_structure` (`Forcing.lean`): there the first `m`
  vertices form a full tower over `K_K`, here they map to `Tmpl(P)`.
* `ForcesWith.blowUp` (one level: Lemma 6.2 with Lemma 5.2):
  `ForcesWith (J*(P)) K m D → ForcesWith P K (m R) R` with `R = (K-1)(D-1)+1`.  The proof reuses
  `inducedAlg`, `blowUpOf`, `postDeg_blowSeq_le` and `forcing_step`.
* `ForcesWith.iterate` (Lemma 6.3): `j` levels, from `P_j(k)` down to `P_0(k)`.
* `chiDetAtLeast_of_labelled_top` ("other adversaries at the top", Section 9.1): if every
  proper algorithm can be forced to `K` colours on some input with `N` vertices that maps to
  `Tmpl(P_j(k))`, then `ChiDetAtLeast k (transferSize K N j) K`, where
  `transferSize K N j = N ∏_{i<j} ((K-1)^{i+1}(N-2)+1)` is the exact size
  (`N · b_j ⋯ b_1` with `b_j = (K-1)(N-2)+1`).
* `chiDetAtLeast_transfer`: the same with "maps to `Tmpl(P_j(k))`" replaced by "`k'`-colourable"
  and `width(P_j(k)) ≥ k'` (`HasAntichain (LabelPoset k j) k'`).
* Bounds: `transferSize_le_mul` (the paper's `N^{j+1} K^{j(j+1)/2}`) and `transferSize_le_pow`
  (`N^{(j+1)(j+2)/2}`, using `K ≤ N`).
* **Theorem 1.4, first sentence**: `transfer` (some `j ≤ lg* k' + 1` with `width(P_j(k)) ≥ k'`;
  the proof takes `j = lg* k' + 1`) and `transfer_least` (with the least `j` such that
  `width(P_j(k)) ≥ k'`, as in the paper's proof; it satisfies `j ≤ lg* k' + 1`).  They need only
  `k ≥ 3`; `k'` is arbitrary.  `chiDet_transfer` is the statement for the number `chiDet` with
  `j = lg* k' + 1`; it has the additional hypothesis `k' ≥ 1`.  `Paper.transfer_chiDet`
  (`PaperStatements.lean`) is the sentence as it is written in the paper.
* The examples after the proof: `transfer_three_four` (`j = 2` for `k = 3`, `k' = 4`, exponent
  `6`) and `transfer_four_of_le_six` (`j = 1` for `k = 4`, `k' ≤ 6`, exponent `3`).
* `transfer_poly`: a polynomial consequence in discrete form: if `C K^a` vertices suffice to
  force `K` colours on `k'`-colourable inputs for all `K ≥ 2`, then `C^e K^{ae}` vertices suffice
  for `k`-colourable ones, with `e = (j+1)(j+2)/2` and `j = lg* k' + 1`.  The second sentence of
  the theorem, with `Ω(n^ε)`, is in `Asymptotic.lean`.
* `chiDetAtLeast_of_card_labelPoset'`: a consistency check, the lower bound of Theorem 6.4 for
  the full tower (`ChiDetAtLeast k (towerSize K j) K`) re-derived from
  `chiDetAtLeast_of_labelled_top` with the clique `K_K` at the top (`transferSize K K j` is
  `towerSize K j`).

The sentence after the theorem, `N_k(K) ≤ N_{k'}(K)^{(j+1)(j+2)/2}`, is the same statement read
through Observation 4.3 (`Det.le_chiDet_iff_Nk_le`).
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### The invariant and one level -/

/-- `ForcesWith P K m D`: for every proper algorithm there is a valid input sequence whose first
`m` vertices have post-degree at most `D`, map to `Tmpl(P)` (have a `P`-labelling), and receive at
least `K` colours. -/
def ForcesWith (P : Type*) [PartialOrder P] (K m D : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H),
    (∀ w < m, postDeg H m w ≤ D) ∧ HasLabelling (OnlineInput.ofSeq H hH m).graph P ∧
      K ≤ ((range m).image (runCol A H)).card

theorem ForcesWith.congr {P : Type*} [PartialOrder P] {K m m' D D' : ℕ}
    (h : ForcesWith P K m D) (hm : m = m') (hD : D = D') : ForcesWith P K m' D' := by
  subst hm hD
  exact h

/-- **One level** (Lemma 6.2 together with Lemma 5.2).  If the inner game forces `K` colours on
inputs that map to `Tmpl(J*(P))`, then one reservation blow-up with blocks of size
`R = (K-1)(D-1)+1` forces `K` colours on inputs that map to `Tmpl(P)`. -/
theorem ForcesWith.blowUp {P : Type*} [PartialOrder P] {K m D : ℕ} (hK : 2 ≤ K) (hD : 1 ≤ D)
    (h : ForcesWith (Jst P) K m D) :
    ForcesWith P K (m * ((K - 1) * (D - 1) + 1)) ((K - 1) * (D - 1) + 1) := by
  intro A hA
  set R := (K - 1) * (D - 1) + 1 with hRdef
  -- the inner input, for the induced algorithm
  obtain ⟨H, hH, hdeg, hlab, hforce⟩ := h (inducedAlg A R D) (inducedAlg_isProper A R D)
  have hR : 0 < R := by omega
  have hDR : D ≤ R := by
    have : D - 1 ≤ (K - 1) * (D - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hσ := resPos_blockPerm (D := D) hR (outCol R D H A)
  have hdeg' : ∀ w < m, postDeg H m w ≤ R := fun w hw => (hdeg w hw).trans hDR
  -- the outer input: the reservation blow-up played against `A`
  refine ⟨blowSeq R H (resPos R D (outCol R D H A)), blowSeq_valid hH hR hσ, ?_, ?_, ?_⟩
  · exact fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w
  · exact (blowUpOf hH hR hσ hdeg').hasLabelling_of_jst hlab
  · rw [← outSeq_eq hH]
    exact forcing_step hRdef hD hA hH hdeg hforce

/-- **Stacking** (Lemma 6.3): `t` reservation blow-ups take inputs that map to
`Tmpl(P_t(k))` to inputs that map to `Tmpl(P_0(k))`.  The block sizes are
`(K-1)^{i+1}(D-1)+1`, `i < t`. -/
theorem ForcesWith.iterate {k K : ℕ} (hK : 2 ≤ K) : ∀ (t m D : ℕ), 1 ≤ D →
    ForcesWith (LabelPoset k t) K m D →
    ForcesWith (LabelPoset k 0) K (m * ∏ i ∈ range t, ((K - 1) ^ (i + 1) * (D - 1) + 1))
      ((K - 1) ^ t * (D - 1) + 1)
  | 0, m, D, hD, h => h.congr (by simp) (by simp; omega)
  | t + 1, m, D, hD, h => by
    have h₁ := ForcesWith.blowUp (P := LabelPoset k t) hK hD h
    have h₂ := ForcesWith.iterate hK t _ _ (Nat.le_add_left _ _) h₁
    rw [Nat.add_sub_cancel] at h₂
    refine h₂.congr ?_ (by ring)
    rw [prod_range_succ', Nat.mul_comm _ ((K - 1) ^ (0 + 1) * (D - 1) + 1), ← Nat.mul_assoc]
    congr 1
    · ring
    · exact prod_congr rfl fun i _ => by ring

/-! ### The top: inputs with `N` vertices -/

/-- In an input on `m` vertices every vertex has post-degree at most `m - 1`. -/
theorem postDeg_le_pred {H : ℕ → Finset ℕ} (hH : ValidSeq H) {m w : ℕ} (hw : w < m) :
    postDeg H m w ≤ m - 1 := by
  unfold postDeg rank
  have hsub : (range m).filter (fun v => w ∈ H v) ⊆ (range m).erase w := by
    intro v hv
    simp only [mem_filter, mem_range] at hv
    refine mem_erase.2 ⟨?_, mem_range.2 hv.1⟩
    rintro rfl
    exact lt_irrefl _ (mem_range.1 (hH v hv.2))
  calc _ ≤ ((range m).erase w).card := card_le_card hsub
    _ = m - 1 := by rw [card_erase_of_mem (mem_range.2 hw), card_range]

/-- The top of the construction: if every proper algorithm can be forced to `K` colours on some
input with `N` vertices that maps to `Tmpl(P)`, then `ForcesWith P K N (N - 1)`. -/
theorem forcesWith_of_top {P : Type*} [PartialOrder P] {K N : ℕ}
    (h : ∀ A : OnlineAlg, A.IsProper →
      ∃ I : OnlineInput N, HasLabelling I.graph P ∧ K ≤ I.cost A) :
    ForcesWith P K N (N - 1) := by
  intro A hA
  obtain ⟨I, hlab, hK⟩ := h A hA
  refine ⟨I.seq, I.seq_valid, fun w hw => postDeg_le_pred I.seq_valid hw, ?_, ?_⟩
  · rw [OnlineInput.ofSeq_seq]
    exact hlab
  · have e := OnlineInput.cost_ofSeq (N := I.seq) (hN := I.seq_valid) (n := N) A
    rw [OnlineInput.ofSeq_seq] at e
    rwa [← e]

/-- At the bottom, a `P_0(k)`-labelling is a `k`-colouring. -/
theorem ForcesWith.chiDetAtLeast {k K M D : ℕ} (h : ForcesWith (LabelPoset k 0) K M D) :
    ChiDetAtLeast k M K := by
  intro A hA
  obtain ⟨H, hH, -, hlab, hK⟩ := h A hA
  refine ⟨OnlineInput.ofSeq H hH M, hasLabelling_labelPoset_zero_iff.1 hlab, ?_⟩
  rw [OnlineInput.cost_ofSeq]
  exact hK

/-! ### Sizes -/

/-- The number of vertices after `j` reservation blow-ups of a top with `N` vertices (post-degree
at most `N - 1`): `N b_j ⋯ b_1` with `b_j = (K-1)(N-2)+1` and `b_{ℓ-1} = (K-1)(b_ℓ-1)+1`. -/
def transferSize (K N j : ℕ) : ℕ := N * ∏ i ∈ range j, ((K - 1) ^ (i + 1) * (N - 2) + 1)

/-- With the clique `K_K` at the top, the size is `K b_j ⋯ b_1`, with the block sizes `b_ℓ` of
Theorem 6.4. -/
theorem transferSize_self (K j : ℕ) : transferSize K K j = towerSize K j := by
  rw [towerSize_eq_prod, transferSize]

/-- Each block size is at most `K^{i+1} N`. -/
theorem transfer_block_le {K N : ℕ} (hK : 1 ≤ K) (hN : 2 ≤ N) (i : ℕ) :
    (K - 1) ^ (i + 1) * (N - 2) + 1 ≤ K ^ (i + 1) * N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have h₁ : (K - 1) ^ (i + 1) ≤ K ^ (i + 1) := Nat.pow_le_pow_left (by omega) _
  have h₂ : 1 ≤ K ^ (i + 1) := Nat.one_le_pow _ _ hK
  rw [Nat.add_sub_cancel]
  nlinarith [Nat.mul_le_mul_right M h₁]

theorem succ_mul_succ_succ_div_two (j : ℕ) :
    (j + 1) * (j + 2) / 2 = j * (j + 1) / 2 + (j + 1) := by
  have : (j + 1) * (j + 2) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

/-- The paper's count: the size is at most `N^{j+1} K^{j(j+1)/2}`. -/
theorem transferSize_le_mul {K N : ℕ} (hK : 1 ≤ K) (hN : 2 ≤ N) (j : ℕ) :
    transferSize K N j ≤ N ^ (j + 1) * K ^ (j * (j + 1) / 2) := by
  induction j with
  | zero => simp [transferSize]
  | succ j ih =>
    unfold transferSize at ih ⊢
    rw [prod_range_succ, ← Nat.mul_assoc]
    have e : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + (j + 1) :=
      succ_mul_succ_succ_div_two j
    calc N * (∏ i ∈ range j, ((K - 1) ^ (i + 1) * (N - 2) + 1)) *
          ((K - 1) ^ (j + 1) * (N - 2) + 1)
        ≤ N ^ (j + 1) * K ^ (j * (j + 1) / 2) * (K ^ (j + 1) * N) :=
          Nat.mul_le_mul ih (transfer_block_le hK hN j)
      _ = N ^ (j + 1 + 1) * K ^ ((j + 1) * (j + 1 + 1) / 2) := by
          rw [e, pow_succ, pow_add]; ring

/-- Using `K ≤ N`: the size is at most `N^{(j+1)(j+2)/2}`. -/
theorem transferSize_le_pow {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hN : 2 ≤ N) (j : ℕ) :
    transferSize K N j ≤ N ^ ((j + 1) * (j + 2) / 2) := by
  calc transferSize K N j ≤ N ^ (j + 1) * K ^ (j * (j + 1) / 2) := transferSize_le_mul hK hN j
    _ ≤ N ^ (j + 1) * N ^ (j * (j + 1) / 2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hKN _)
    _ = N ^ ((j + 1) * (j + 2) / 2) := by
        rw [← pow_add, succ_mul_succ_succ_div_two, Nat.add_comm]

/-! ### Other adversaries at the top -/

/-- If every proper algorithm can be forced to `K` colours on an input with `N` vertices, then
`K ≤ N`. -/
theorem le_of_forall_exists_cost {K N : ℕ} {Q : OnlineInput N → Prop}
    (h : ∀ A : OnlineAlg, A.IsProper → ∃ I : OnlineInput N, Q I ∧ K ≤ I.cost A) : K ≤ N := by
  obtain ⟨I, -, hK⟩ := h OnlineAlg.firstFit OnlineAlg.firstFit_isProper
  exact hK.trans (I.cost_le _)

/-- **Other adversaries at the top.**  If every proper algorithm can be forced to use `K ≥ 2`
colours on some input with `N` vertices that maps to `Tmpl(P_j(k))`, then every proper algorithm can
be forced to use `K` colours on some `k`-colourable input with `transferSize K N j` vertices. -/
theorem chiDetAtLeast_of_labelled_top {k j K N : ℕ} (hK : 2 ≤ K)
    (h : ∀ A : OnlineAlg, A.IsProper →
      ∃ I : OnlineInput N, HasLabelling I.graph (LabelPoset k j) ∧ K ≤ I.cost A) :
    ChiDetAtLeast k (transferSize K N j) K := by
  have hKN := le_of_forall_exists_cost h
  have h₁ := ForcesWith.iterate hK j N (N - 1) (by omega) (forcesWith_of_top h)
  have e : N - 1 - 1 = N - 2 := by omega
  rw [e] at h₁
  exact h₁.chiDetAtLeast

/-- **Transfer, exact size.**  If `width(P_j(k)) ≥ k'`, `K ≥ 2` and `N_{k'}(K) ≤ N`, then
`N_k(K) ≤ N b_j ⋯ b_1 = transferSize K N j`. -/
theorem chiDetAtLeast_transfer {k k' j K N : ℕ} (hK : 2 ≤ K)
    (hj : HasAntichain (LabelPoset k j) k') (h : ChiDetAtLeast k' N K) :
    ChiDetAtLeast k (transferSize K N j) K := by
  obtain ⟨Ach, hAch, hcard⟩ := hj
  apply chiDetAtLeast_of_labelled_top hK
  intro A hA
  obtain ⟨I, hc, hI⟩ := h A hA
  exact ⟨I, hasLabelling_of_colorable hAch hcard.ge hc, hI⟩

/-- **Transfer, power form.**  If `k ≥ 1`, `width(P_j(k)) ≥ k'`, `K ≥ 2` and `N_{k'}(K) ≤ N`, then
`N_k(K) ≤ N^{(j+1)(j+2)/2}`. -/
theorem chiDetAtLeast_transfer_pow {k k' j K N : ℕ} (hk : 1 ≤ k) (hK : 2 ≤ K)
    (hj : HasAntichain (LabelPoset k j) k') (h : ChiDetAtLeast k' N K) :
    ChiDetAtLeast k (N ^ ((j + 1) * (j + 2) / 2)) K := by
  have hKN : K ≤ N := le_of_forall_exists_cost h
  exact (chiDetAtLeast_transfer hK hj h).mono hk (transferSize_le_pow (by omega) hKN (by omega) j)

/-! ### Theorem 1.4 -/

/-- For `k ≥ 3`, `width(P_j(k)) ≥ k'` with `j = lg* k' + 1` (Lemma 5.6). -/
theorem hasAntichain_labelPoset_logStar {k : ℕ} (hk : 3 ≤ k) (k' : ℕ) :
    HasAntichain (LabelPoset k (logStar k' + 1)) k' := by
  rcases Nat.lt_or_ge 3 k with hk4 | hk3
  · refine (hasAntichain_labelPoset_of_four_le hk4 _).mono ?_
    exact (le_tow_logStar k').trans (tow_mono (by omega))
  · obtain rfl : k = 3 := by omega
    rcases Nat.lt_or_ge k' 2 with hk' | hk'
    · -- `lg* k' = 0`, and `P_1(3)` has an antichain of size `3`
      have h0 : logStar k' = 0 := Nat.le_zero.1 (logStar_le_iff.2 (by rw [tow_zero]; omega))
      rw [h0]
      have h3 := (hasAntichain_labelPoset_zero 3).labelPoset_succ (by norm_num)
      exact h3.mono (by norm_num; omega)
    · have hpos : 1 ≤ logStar k' := by
        by_contra hz
        have := le_tow_logStar k'
        rw [show logStar k' = 0 by omega, tow_zero] at this
        omega
      refine (hasAntichain_labelPoset_three (by omega)).mono ?_
      rw [Nat.add_sub_cancel]
      exact le_tow_logStar k'

/-- **Theorem 1.4 (transfer between values of `k`).**  Let `k ≥ 3`.  There is `j ≤ lg* k' + 1`
such that `N_k(K) ≤ N_{k'}(K)^{(j+1)(j+2)/2}` for every `K ≥ 2`: every `N` with
`N_{k'}(K) ≤ N` satisfies `N_k(K) ≤ N^{(j+1)(j+2)/2}`. -/
theorem transfer {k k' : ℕ} (hk : 3 ≤ k) :
    ∃ j ≤ logStar k' + 1, HasAntichain (LabelPoset k j) k' ∧
      ∀ K N, 2 ≤ K → ChiDetAtLeast k' N K → ChiDetAtLeast k (N ^ ((j + 1) * (j + 2) / 2)) K :=
  ⟨logStar k' + 1, le_rfl, hasAntichain_labelPoset_logStar hk k',
    fun _ _ hK h => chiDetAtLeast_transfer_pow (by omega) hK
      (hasAntichain_labelPoset_logStar hk k') h⟩

/-- **Theorem 1.4, with the paper's choice of `j`**: the least `j` with `width(P_j(k)) ≥ k'`. -/
theorem transfer_least {k k' : ℕ} (hk : 3 ≤ k) :
    ∃ j ≤ logStar k' + 1, HasAntichain (LabelPoset k j) k' ∧
      (∀ i < j, ¬ HasAntichain (LabelPoset k i) k') ∧
      ∀ K N, 2 ≤ K → ChiDetAtLeast k' N K → ChiDetAtLeast k (N ^ ((j + 1) * (j + 2) / 2)) K := by
  classical
  have hex : ∃ j, HasAntichain (LabelPoset k j) k' := ⟨_, hasAntichain_labelPoset_logStar hk k'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (hasAntichain_labelPoset_logStar hk k'),
    Nat.find_spec hex, fun i hi => Nat.find_min hex hi, fun _ _ hK h => ?_⟩
  exact chiDetAtLeast_transfer_pow (by omega) hK (Nat.find_spec hex) h

/-- Theorem 1.4 in terms of `χ^det`: for `k ≥ 3`, `k' ≥ 1` and `K ≥ 2`, `χ^det_{k'}(N) ≥ K`
implies `χ^det_k(N^{(j+1)(j+2)/2}) ≥ K`, with `j = lg* k' + 1`. -/
theorem chiDet_transfer {k k' K N : ℕ} (hk : 3 ≤ k) (hk' : 1 ≤ k') (hK : 2 ≤ K)
    (h : K ≤ chiDet k' N) :
    K ≤ chiDet k (N ^ ((logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2)) :=
  (le_chiDet_iff (by omega)).2 (chiDetAtLeast_transfer_pow (by omega) hK
    (hasAntichain_labelPoset_logStar hk k') ((le_chiDet_iff hk').1 h))

/-- The paper's example `j = 2` for `k = 3`, `k' = 4`: `N_3(K) ≤ N_4(K)^6`. -/
theorem transfer_three_four {K N : ℕ} (hK : 2 ≤ K) (h : ChiDetAtLeast 4 N K) :
    ChiDetAtLeast 3 (N ^ 6) K :=
  chiDetAtLeast_transfer_pow (j := 2) (by norm_num) hK hasAntichain_labelPoset_three_two h

/-- The paper's example `j = 1` for `k = 4`, `k' ≤ 6` (`width(P_1(4)) = 6`):
`N_4(K) ≤ N_{k'}(K)^3`. -/
theorem transfer_four_of_le_six {k' K N : ℕ} (hk' : k' ≤ 6) (hK : 2 ≤ K)
    (h : ChiDetAtLeast k' N K) : ChiDetAtLeast 4 (N ^ 3) K := by
  have h6 : HasAntichain (LabelPoset 4 1) 6 :=
    (hasAntichain_labelPoset_zero 4).labelPoset_succ (by norm_num)
  exact chiDetAtLeast_transfer_pow (j := 1) (by norm_num) hK (h6.mono hk') h

/-- **Theorem 1.4, polynomial consequence** (discrete form): let `k ≥ 3`; if `N_{k'}(K) ≤ C K^a`
for every `K ≥ 2`, then `N_k(K) ≤ C^e K^{ae}` for every `K ≥ 2`, with `e = (j+1)(j+2)/2` and
`j = lg* k' + 1`. -/
theorem transfer_poly {k k' C a : ℕ} (hk : 3 ≤ k)
    (h : ∀ K, 2 ≤ K → ChiDetAtLeast k' (C * K ^ a) K) (K : ℕ) (hK : 2 ≤ K) :
    ChiDetAtLeast k (C ^ ((logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2) *
      K ^ (a * ((logStar k' + 1 + 1) * (logStar k' + 1 + 2) / 2))) K := by
  have := chiDetAtLeast_transfer_pow (by omega) hK (hasAntichain_labelPoset_logStar hk k') (h K hK)
  rwa [mul_pow, ← pow_mul] at this

/-! ### Consistency check: Theorem 6.4 from the general statement -/

/-- The lower bound of Theorem 6.4 (`chiDetAtLeast_of_card_labelPoset`), with the size
`towerSize K j` of the full tower, re-derived from `chiDetAtLeast_of_labelled_top` with the clique
`K_K` at the top, which maps to `Tmpl(P_j(k))` iff `K ≤ |P_j(k)|` (Lemma 5.1 (i)). -/
theorem chiDetAtLeast_of_card_labelPoset' {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) : ChiDetAtLeast k (towerSize K j) K := by
  rw [← transferSize_self]
  apply chiDetAtLeast_of_labelled_top hK
  intro A hA
  refine ⟨OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K, ?_, ?_⟩
  · rw [ofSeq_cliqueSeq_graph]
    exact hasLabelling_clique_iff.2 hKj
  · rw [OnlineInput.cost_ofSeq, card_image_runCol_cliqueSeq hA]

end OnlineColouring
