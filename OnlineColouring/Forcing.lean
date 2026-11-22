module

public import OnlineColouring.Structure
public import OnlineColouring.Counting

/-!
# The iterated reservation adversary (Theorem 6.4), against a fixed algorithm

Theorem 6.4 (the iterated reservation adversary), proved in the form of the second sentence of
Observation 4.3 (for every proper deterministic algorithm, an input on which it uses `K`
colours), without the stop rule and with every block completed, as in Section 7 (the structure
mode of `Structure.lean`).  The adversary of the paper, with its stop rule, is `Blow.tower`
(`BlowTower.lean`), and Theorem 6.4 for it is `Blow.theorem_6_4`; the adversary `𝒜^str` of
Section 7 is `Str.strTower` (`StrTower.lean`).  `KnownGraphs.lean` shows that the inputs of this
construction are isomorphic, oriented by arrival, to the one graph `H_j(K)`
(`forcing_structure_iso`, the counterpart of Lemma 7.2 for these inputs).

* `levelDeg K j = (K-1)^j (K-2) + 1` is the post-degree bound after `j` blow-ups of `K_K`; it is
  also the block size of the `j`-th blow-up, so that with `j` blow-ups every block of a node of
  level `ℓ` has size `levelDeg K (j-ℓ+1) = blockSize K j ℓ = b_ℓ`.
* `towerSize K j = K · b_j ⋯ b_1` is the number of presented vertices
  (`towerSize_eq : towerSize K j = K * ∏_{ℓ=1}^{j} blockSize K j ℓ`), and
  `towerSize_le : towerSize K j ≤ K^((j+1)(j+2)/2)`.
* `forcing_structure` (the induction on the number of levels: Lemma 6.2 (forcing survives a
  blow-up) once per level, as in Lemma 6.3 (stacking)): for every proper algorithm `A` there is an
  input sequence `H` whose first `towerSize K j` vertices form a `j`-fold full blow-up of `K_K`
  (each blow-up of the proof is a reservation blow-up), with post-degrees at most `levelDeg K j`,
  on which `A` uses at least `K` colours.  The induction step applies the induction hypothesis to
  the induced algorithm `inducedAlg A R D` and blows up the inner input it returns
  (`forcing_step`).
* `iterated_reservation_adversary` (Theorem 6.4 in this form) and
  `chiDetAtLeast_of_card_labelPoset` (the resulting lower bound on `χ^det`).  The bound
  `(K-1) b_j ⋯ b_1 + 1` of the theorem on the number of vertices is proved in `PlayBound.lean`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Block sizes -/

/-- `levelDeg K j = (K-1)^j (K-2) + 1`. -/
def levelDeg (K j : ℕ) : ℕ := (K - 1) ^ j * (K - 2) + 1

/-- The number of vertices `K b_j ⋯ b_1` of the full `j`-level tower over `K_K` with the block
sizes of Theorem 6.4. -/
def towerSize (K : ℕ) : ℕ → ℕ
  | 0 => K
  | j + 1 => towerSize K j * levelDeg K (j + 1)

theorem one_le_levelDeg (K j : ℕ) : 1 ≤ levelDeg K j := Nat.le_add_left _ _

theorem levelDeg_zero {K : ℕ} (hK : 2 ≤ K) : levelDeg K 0 = K - 1 := by
  simp only [levelDeg, pow_zero, Nat.one_mul]
  omega

/-- `b_{ℓ-1} = (K-1)(b_ℓ - 1) + 1`: each blow-up uses `R = (K-1)(D-1)+1` with `D` the previous
post-degree bound. -/
theorem levelDeg_succ (K j : ℕ) : levelDeg K (j + 1) = (K - 1) * (levelDeg K j - 1) + 1 := by
  simp only [levelDeg, Nat.add_sub_cancel, pow_succ]
  ring

theorem levelDeg_le_succ {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : levelDeg K j ≤ levelDeg K (j + 1) := by
  rw [levelDeg_succ]
  have h₁ := one_le_levelDeg K j
  have h₂ : levelDeg K j - 1 ≤ (K - 1) * (levelDeg K j - 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The block sizes of the paper: `b_ℓ = levelDeg K (j - ℓ + 1)`. -/
theorem blockSize_eq_levelDeg (K j ℓ : ℕ) : blockSize K j ℓ = levelDeg K (j - ℓ + 1) := rfl

theorem towerSize_eq_prod (K j : ℕ) :
    towerSize K j = K * ∏ i ∈ range j, ((K - 1) ^ (i + 1) * (K - 2) + 1) := by
  induction j with
  | zero => simp [towerSize]
  | succ j ih => rw [towerSize, ih, prod_range_succ, Nat.mul_assoc]; rfl

/-- `towerSize K j = K b_j ⋯ b_1`. -/
theorem towerSize_eq (K j : ℕ) : towerSize K j = K * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ := by
  rw [towerSize_eq_prod, prod_blockSize_eq]

/-- `K b_j ⋯ b_1 ≤ K^((j+1)(j+2)/2)`. -/
theorem towerSize_le {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    towerSize K j ≤ K ^ ((j + 1) * (j + 2) / 2) := by
  rw [towerSize_eq_prod]
  have e : (j + 1) * (j + 2) / 2 = j * (j + 3) / 2 + 1 := by
    have : (j + 1) * (j + 2) = j * (j + 3) + 2 * 1 := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
  calc K * ∏ i ∈ range j, ((K - 1) ^ (i + 1) * (K - 2) + 1) ≤ K * K ^ (j * (j + 3) / 2) :=
        Nat.mul_le_mul_left _ (prod_block_le hK j)
    _ = K ^ ((j + 1) * (j + 2) / 2) := by rw [e, pow_succ, Nat.mul_comm]

/-- The paper's play bound `(K-1) b_j ⋯ b_1 + 1` is at most the size of the full tower. -/
theorem playSize_le_towerSize {K : ℕ} (hK : 1 ≤ K) (j : ℕ) : playSize K j ≤ towerSize K j := by
  rw [towerSize_eq, playSize]
  have : 1 ≤ ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ :=
    Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun ℓ _ => by simp [blockSize])
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.succ_mul]
  omega

theorem two_le_towerSize {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : 2 ≤ towerSize K j := by
  induction j with
  | zero => exact hK
  | succ j ih =>
    have := one_le_levelDeg K (j + 1)
    calc 2 ≤ towerSize K j := ih
      _ ≤ towerSize K j * levelDeg K (j + 1) := Nat.le_mul_of_pos_right _ this

/-! ### The clique -/

/-- The arrival-ordered clique: vertex `i` is adjacent to all earlier vertices. -/
def cliqueSeq (i : ℕ) : Finset ℕ := range i

theorem cliqueSeq_valid : ValidSeq cliqueSeq := fun _ => subset_refl _

theorem ofSeq_cliqueSeq_graph (K : ℕ) :
    (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).graph = ⊤ := by
  ext u v
  rw [OnlineInput.ofSeq_adj, SimpleGraph.top_adj]
  simp only [cliqueSeq, mem_range, ne_eq, Fin.ext_iff]
  constructor <;> intro h <;> omega

theorem ofSeq_cliqueSeq (K : ℕ) :
    (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph = OrdGraph.clique K := by
  unfold OnlineInput.toOrdGraph OrdGraph.clique
  rw [ofSeq_cliqueSeq_graph]

theorem postDeg_cliqueSeq_le (K w : ℕ) : postDeg cliqueSeq K w ≤ K - 1 := by
  unfold postDeg rank
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hsub : (range K).filter (fun v => w ∈ cliqueSeq v) ⊆ (range K).erase 0 := by
    intro v hv
    simp only [cliqueSeq, mem_filter, mem_range] at hv
    exact mem_erase.2 ⟨by omega, mem_range.2 hv.1⟩
  calc _ ≤ ((range K).erase 0).card := card_le_card hsub
    _ = K - 1 := by rw [card_erase_of_mem (mem_range.2 hK), card_range]

/-- Every proper algorithm uses `K` colours on the clique `K_K`. -/
theorem card_image_runCol_cliqueSeq {A : OnlineAlg} (hA : A.IsProper) (K : ℕ) :
    ((range K).image (runCol A cliqueSeq)).card = K := by
  rw [card_image_of_injOn, card_range]
  intro u _ v _ huv
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact runCol_ne hA (mem_range.2 h) h huv.symm
  · exact runCol_ne hA (mem_range.2 h) h huv

/-! ### Stacking the blow-ups -/

/-- **Forcing against a fixed algorithm** (Lemma 6.2 (forcing survives a blow-up), applied once
per level as in Lemma 6.3 (stacking)). For every proper algorithm `A` there is an input whose
first `towerSize K j = K b_j ⋯ b_1` vertices form a `j`-fold full blow-up of `K_K`, with all
post-degrees at most `levelDeg K j`, on which `A` uses at least `K` colours. -/
theorem forcing_structure {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ A : OnlineAlg, A.IsProper →
      ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H),
        IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
        (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
        K ≤ ((range (towerSize K j)).image (runCol A H)).card := by
  induction j with
  | zero =>
    intro A hA
    refine ⟨cliqueSeq, cliqueSeq_valid, ?_, ?_, ?_⟩
    · change IsFullTower K 0 (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph
      rw [ofSeq_cliqueSeq]
      exact .clique
    · intro w _
      rw [levelDeg_zero hK]
      exact postDeg_cliqueSeq_le K w
    · exact (card_image_runCol_cliqueSeq hA K).ge
  | succ j ih =>
    intro A hA
    obtain ⟨R, hRdef⟩ : ∃ R, R = (K - 1) * (levelDeg K j - 1) + 1 := ⟨_, rfl⟩
    have hRj : levelDeg K (j + 1) = R := by rw [hRdef, levelDeg_succ]
    -- the inner input, for the induced algorithm
    obtain ⟨H, hH, htower, hdeg, hforce⟩ :=
      ih (inducedAlg A R (levelDeg K j)) (inducedAlg_isProper A R (levelDeg K j))
    have hR : 0 < R := by omega
    have hD : 1 ≤ levelDeg K j := one_le_levelDeg K j
    have hDR : levelDeg K j ≤ R := hRj ▸ levelDeg_le_succ hK j
    have hσ := resPos_blockPerm (D := levelDeg K j) hR (outCol R (levelDeg K j) H A)
    have hdeg' : ∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ R :=
      fun w hw => (hdeg w hw).trans hDR
    have hsize : towerSize K (j + 1) = towerSize K j * R := by rw [← hRj]; rfl
    -- the outer input: the reservation blow-up played against `A`
    refine ⟨blowSeq R H (resPos R (levelDeg K j) (outCol R (levelDeg K j) H A)),
      blowSeq_valid hH hR hσ, ?_, ?_, ?_⟩
    · rw [hsize]
      exact .blowUp htower ⟨blowUpOf hH hR hσ hdeg', (blowUpOf_isReservation hH hR hσ hdeg').isFull⟩
    · rw [hsize, hRj]
      exact fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w
    · rw [hsize, ← outSeq_eq hH]
      exact forcing_step hRdef hD hA hH hdeg hforce

/-- A `k`-colourable graph on a nonempty vertex set needs `k ≥ 1`. -/
theorem one_le_of_colorable {n k : ℕ} {G : SimpleGraph (Fin n)} (hn : 1 ≤ n)
    (hG : G.Colorable k) : 1 ≤ k := by
  obtain ⟨c⟩ := hG
  have := (c ⟨0, hn⟩).2
  omega

/-- **Theorem 6.4 (the iterated reservation adversary), against a fixed algorithm.** Let `K ≥ 2`
and `|P_j(k)| ≥ K`.  For every proper deterministic online algorithm `A` there is an online input
on `K b_j ⋯ b_1` vertices (`b_ℓ = (K-1)^{j-ℓ+1}(K-2)+1`; at most `K^((j+1)(j+2)/2)` vertices by
`towerSize_le` and `towerSize_eq`) which is a `j`-fold full blow-up of `K_K`, hence
`k`-colourable, and on which `A` uses at least `K` colours. -/
theorem iterated_reservation_adversary {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) (A : OnlineAlg) (hA : A.IsProper) :
    ∃ I : OnlineInput (K * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ),
      IsFullTower K j I.toOrdGraph ∧ I.graph.Colorable k ∧ K ≤ I.cost A := by
  obtain ⟨H, hH, htower, -, hforce⟩ := forcing_structure hK j A hA
  rw [← towerSize_eq]
  refine ⟨OnlineInput.ofSeq H hH (towerSize K j), htower, htower.isTower.colorable hKj, ?_⟩
  rw [OnlineInput.cost_ofSeq]
  exact hforce

/-- **Theorem 6.4, as a lower bound.** If `K ≥ 2`, `|P_j(k)| ≥ K` and `K^((j+1)(j+2)/2) ≤ n`, then
`χ^det_k(n) ≥ K`. -/
theorem chiDetAtLeast_of_card_labelPoset {k K j n : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) (hn : K ^ ((j + 1) * (j + 2) / 2) ≤ n) :
    ChiDetAtLeast k n K := by
  intro A hA
  obtain ⟨H, hH, htower, -, hforce⟩ := forcing_structure hK j A hA
  have hc := htower.isTower.colorable hKj
  have hk : 1 ≤ k := one_le_of_colorable (by have := two_le_towerSize hK j; omega) hc
  exact exists_input_of_seq hH hk ((towerSize_le hK j).trans hn) hc hforce

end OnlineColouring
