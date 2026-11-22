module

public import OnlineColouring.Forcing

/-!
# Theorem 6.4 with the bound `(K-1) b_j ⋯ b_1 + 1`, against a fixed algorithm

Theorem 6.4 bounds every play of the iterated reservation adversary by
`(K-1) ∏ b_ℓ + 1 = playSize K j` vertices, because the play ends at the latest at the first vertex
`y` below the last top vertex `v_K` (paragraph "The play ends no later than the first vertex below
`v_K`" of its proof).  This file proves the bound in the per-algorithm form of `Forcing.lean`,
where no stop rule is applied and every block is completed: every proper algorithm has used `K`
colours on the first `playSize K j` vertices of an input built as in `forcing_structure`.  The
adversary of the paper, with its stop rule, is `Blow.tower` (`BlowTower.lean`), and Theorem 6.4 for
it is `Blow.theorem_6_4`.

`firstLast K j = (K-1) b_j ⋯ b_1` is the index of `y`.  The induction (`forcing_play`) carries:
either `A` uses `K` colours before `y`, or the earlier neighbours of `y` carry at least `K - 1`
colours (and then `y` gets a `K`-th one).  For `K_K` the earlier neighbours of `v_K` carry `K - 1`
colours.  In the induction step, if some block before the block of `y` has no colour with `D`
vertices, it carries `K` colours; otherwise the induced colours of the inner vertices before `y`
are colours of `A`, and the server below each earlier inner neighbour `w` of the inner `y` has the
induced colour of `w`.

* `iterated_reservation_adversary_play`: if `K ≥ 2` and `|P_j(k)| ≥ K`, then for every proper
  algorithm there is a `k`-colourable input on `playSize K j ≤ K^((j+1)(j+2)/2)` vertices on which
  it uses `K` colours.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-- The index `(K-1) b_j ⋯ b_1` of the first presented vertex below the last top vertex `v_K`. -/
def firstLast (K : ℕ) : ℕ → ℕ
  | 0 => K - 1
  | j + 1 => firstLast K j * levelDeg K (j + 1)

theorem firstLast_eq_prod (K j : ℕ) :
    firstLast K j = (K - 1) * ∏ i ∈ range j, ((K - 1) ^ (i + 1) * (K - 2) + 1) := by
  induction j with
  | zero => simp [firstLast]
  | succ j ih => rw [firstLast, ih, prod_range_succ, Nat.mul_assoc]; rfl

theorem firstLast_add_one (K j : ℕ) : firstLast K j + 1 = playSize K j := by
  rw [firstLast_eq_prod, playSize, prod_blockSize_eq]

theorem firstLast_lt_towerSize {K : ℕ} (hK : 1 ≤ K) (j : ℕ) : firstLast K j < towerSize K j := by
  induction j with
  | zero => simp only [firstLast, towerSize]; omega
  | succ j ih =>
    have h := one_le_levelDeg K (j + 1)
    exact Nat.mul_lt_mul_of_pos_right ih h

/-- **Forcing within the play bound.** For every proper algorithm `A` there is an input whose
first `towerSize K j` vertices form a `j`-fold full blow-up of `K_K`, with post-degrees at most
`levelDeg K j`, such that either `A` uses `K` colours on the vertices before `y = firstLast K j`,
or the earlier neighbours of `y` carry at least `K - 1` colours. -/
theorem forcing_play {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ A : OnlineAlg, A.IsProper →
      ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H),
        IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
        (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
        (K ≤ ((range (firstLast K j)).image (runCol A H)).card ∨
          K - 1 ≤ ((H (firstLast K j)).image (runCol A H)).card) := by
  induction j with
  | zero =>
    intro A hA
    refine ⟨cliqueSeq, cliqueSeq_valid, ?_, ?_, Or.inr ?_⟩
    · change IsFullTower K 0 (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph
      rw [ofSeq_cliqueSeq]
      exact .clique
    · intro w _
      rw [levelDeg_zero hK]
      exact postDeg_cliqueSeq_le K w
    · exact (card_image_runCol_cliqueSeq hA (K - 1)).ge
  | succ j ih =>
    intro A hA
    obtain ⟨R, hRdef⟩ : ∃ R, R = (K - 1) * (levelDeg K j - 1) + 1 := ⟨_, rfl⟩
    have hRj : levelDeg K (j + 1) = R := by rw [hRdef, levelDeg_succ]
    set D := levelDeg K j with hDdef
    obtain ⟨H, hH, htower, hdeg, hplay⟩ :=
      ih (inducedAlg A R D) (inducedAlg_isProper A R D)
    set m := towerSize K j with hmdef
    set f := firstLast K j with hfdef
    have hfm : f < m := firstLast_lt_towerSize (by omega) j
    have hR : 0 < R := by omega
    have hD : 1 ≤ D := one_le_levelDeg K j
    have hDR : D ≤ R := hRj ▸ levelDeg_le_succ hK j
    have hσ := resPos_blockPerm (D := D) hR (outCol R D H A)
    have hdeg' : ∀ w < m, postDeg H m w ≤ R := fun w hw => (hdeg w hw).trans hDR
    have hsize : towerSize K (j + 1) = m * R := by rw [← hRj]; rfl
    have hfsize : firstLast K (j + 1) = f * R := by rw [← hRj]; rfl
    have hG := outSeq_eq (D := D) (A := A) hH (R := R)
    have hblock : ∀ v < f, ∀ t < R, v * R + t < f * R := by
      intro v hv t ht
      have := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hv)
      rw [Nat.succ_mul] at this
      omega
    refine ⟨blowSeq R H (resPos R D (outCol R D H A)), blowSeq_valid hH hR hσ, ?_, ?_, ?_⟩
    · rw [hsize]
      exact .blowUp htower ⟨blowUpOf hH hR hσ hdeg', (blowUpOf_isReservation hH hR hσ hdeg').isFull⟩
    · rw [hsize, hRj]
      exact fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w
    rw [hfsize, ← hG]
    change K ≤ ((range (f * R)).image (outCol R D H A)).card ∨
      K - 1 ≤ ((outSeq R D H A (f * R)).image (outCol R D H A)).card
    by_cases hfaith : ∀ v < f, ∃ c, D ≤ (clsList R (blockCol (outCol R D H A) R v) c).length
    · -- the blocks before the block of `y` are faithful
      have heq := runCol_inducedAlg_eq hA hH hR hD hdeg hfm.le hfaith
      rcases hplay with hi | hii
      · left
        refine hi.trans (card_le_card ?_)
        intro c hc
        obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
        rw [mem_range] at hv
        rw [heq v hv]
        obtain ⟨t, ht, htc⟩ := popular_mem hD (popular_spec hD (hfaith v hv))
        exact mem_image.2 ⟨v * R + t, mem_range.2 (hblock v hv t ht), htc⟩
      · right
        refine hii.trans (card_le_card ?_)
        intro c hc
        obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
        have hwf : w < f := mem_range.1 (hH f hw)
        rw [heq w hwf]
        have hmem := server_mem_outSeq (D := D) (A := A) hH hR hw hR
        rw [Nat.add_zero] at hmem
        exact mem_image.2 ⟨_, hmem, outCol_server hD hdeg hH hfm hw (hfaith w hwf)⟩
    · -- some block before the block of `y` carries `K` colours
      left
      push Not at hfaith
      obtain ⟨v, hv, hsmall⟩ := hfaith
      have hK' : K ≤ ((range R).image (blockCol (outCol R D H A) R v)).card := by
        by_contra hlt
        push Not at hlt
        obtain ⟨b, -, hb⟩ := exists_large_colour_class (range R) (blockCol (outCol R D H A) R v)
          (by rw [card_range, hRdef]) hlt
        rw [← length_clsList] at hb
        exact absurd hb (not_le.2 (hsmall b))
      refine hK'.trans (card_le_card ?_)
      intro c hc
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hc
      exact mem_image.2 ⟨v * R + t, mem_range.2 (hblock v hv t (mem_range.1 ht)), rfl⟩

/-- Restricting to an initial segment keeps `k`-colourability. -/
theorem colorable_ofSeq_of_le {N : ℕ → Finset ℕ} (hN : ValidSeq N) {m n k : ℕ} (hmn : m ≤ n)
    (hc : (OnlineInput.ofSeq N hN n).graph.Colorable k) :
    (OnlineInput.ofSeq N hN m).graph.Colorable k := by
  obtain ⟨c⟩ := hc
  refine ⟨SimpleGraph.Coloring.mk (fun v => c (Fin.castLE hmn v)) fun {u v} huv => c.valid ?_⟩
  rw [OnlineInput.ofSeq_adj] at huv ⊢
  exact huv

/-- **Theorem 6.4 (the iterated reservation adversary), with the paper's bound.** Let `K ≥ 2` and
`|P_j(k)| ≥ K`.  For every proper deterministic online algorithm `A` there is a `k`-colourable
online input on `(K-1) b_j ⋯ b_1 + 1 = playSize K j` vertices (`≤ K^((j+1)(j+2)/2)` by
`playSize_le`) on which `A` uses at least `K` colours.  The input of the proof is an initial
segment of a `j`-fold reservation blow-up of `K_K`; the statement keeps only that it is
`k`-colourable. -/
theorem iterated_reservation_adversary_play {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) (A : OnlineAlg) (hA : A.IsProper) :
    ∃ I : OnlineInput (playSize K j), I.graph.Colorable k ∧ K ≤ I.cost A := by
  obtain ⟨H, hH, htower, -, hplay⟩ := forcing_play hK j A hA
  have hle : playSize K j ≤ towerSize K j := by
    rw [← firstLast_add_one]; exact firstLast_lt_towerSize (by omega) j
  refine ⟨OnlineInput.ofSeq H hH (playSize K j),
    colorable_ofSeq_of_le hH hle (htower.isTower.colorable hKj), ?_⟩
  rw [OnlineInput.cost_ofSeq, ← firstLast_add_one]
  set f := firstLast K j
  rcases hplay with hi | hii
  · refine hi.trans (card_le_card (image_subset_image ?_))
    exact range_subset_range.2 (Nat.le_succ f)
  · -- `y = f` gets a colour different from the `K - 1` colours of its earlier neighbours
    have hnot : runCol A H f ∉ (H f).image (runCol A H) := by
      intro hmem
      obtain ⟨w, hw, hwc⟩ := mem_image.1 hmem
      exact runCol_ne hA hw (mem_range.1 (hH f hw)) hwc.symm
    have hsub : insert (runCol A H f) ((H f).image (runCol A H)) ⊆
        (range (f + 1)).image (runCol A H) := by
      intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · exact mem_image.2 ⟨f, mem_range.2 (Nat.lt_succ_self f), rfl⟩
      · obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
        exact mem_image.2 ⟨w, mem_range.2 ((mem_range.1 (hH f hw)).trans (Nat.lt_succ_self f)),
          rfl⟩
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    omega

end OnlineColouring
