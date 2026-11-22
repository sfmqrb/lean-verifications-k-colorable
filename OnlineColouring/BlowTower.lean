module

public import OnlineColouring.BlowStack
public import OnlineColouring.OddGirth

/-!
# Theorem 6.4 and Remark 6.5: the iterated reservation adversary as an adversary object

Theorem 6.4 (`thm:L`) and Remark 6.5 (`rem:instances`) of Section 6.

`Blow.tower K j` is the adversary of the paper's proof: `𝒜_j` presents the arrival-ordered clique
`K_K` (`Adversary.clique K`), and `𝒜_i = B(𝒜_{i+1})` with `D` equal to the post-degree bound of
`𝒜_{i+1}` (`K - 1` for the clique, then the previous block size); `tower K j = 𝒜_0`.  In the
indexing of `Blow.stack`, `tower K j = stack K (K-1) (clique K) j`, and the `i`-th blow-up below
the clique has `D = levelDeg K (i-1)` and block size `levelDeg K i = (K-1)^i (K-2) + 1 = b_{j-i+1}`
(`tower_succ`).

The proof of Theorem 6.4 follows the paper for forcing and for the number of vertices; the
colourability of the graphs presented is proved by a different argument.

* Forcing: "By Lemma 6.3, each `𝒜_i` forces `K` colours" is `tower_stackOK`, which is
  `Blow.lemma_6_3` for the clique (`Adversary.clique_forces`, `clique_sizeLE`,
  `clique_postDegLE`).
* The graphs.  The paper's argument: at every level the graph presented is a reservation blow-up
  of the inner graph restricted to the blocks that have started (the remark after Lemma 6.2), so
  every graph presented by `𝒜_0` is a `j`-fold blow-up of an initial segment `K_m` of `K_K`, and
  Corollary 5.4 applies.  The formal argument (`tower_play`): against every proper algorithm
  `Alg`, the play of `tower K j` follows an input sequence `H` whose first `K b_j ⋯ b_1` vertices
  form a `j`-fold full blow-up of `K_K` (`IsFullTower`; each of its blow-ups is a reservation
  blow-up, `blowUpOf_isReservation`), and it stops at the first moment `T ≤ K b_j ⋯ b_1` at which
  `Alg` has used `K` colours.  Every graph presented is therefore an initial segment of this
  blow-up, and the `k`-colouring that Corollary 5.4 gives for the whole blow-up
  (`IsTower.colorable`) restricts to it (`hasLabelling_runHist`).
* "The play ends no later than the first vertex below `v_K`": `tower_first_last` and
  `tower_sizeLE`.  Let `y` be the vertex with index `(K-1) b_j ⋯ b_1`.  If fewer than `K` colours
  are in use when `y` is about to arrive, the invariant of Lemma 6.3 holds, and by its last part
  the earlier neighbours of `y` are, at every level, servers with the induced colours of the nodes
  they belong to; at the top these are the `K - 1` distinct colours of `v_1, …, v_{K-1}`.  So `y`
  receives a `K`-th colour, the adversary stops, and every play has at most
  `(K-1) b_j ⋯ b_1 + 1` vertices.
* `theorem_6_4`: `tower K j` forces `K` colours, every play has at most
  `(K-1) ∏ b_ℓ + 1 = playSize K j ≤ K^((j+1)(j+2)/2)` vertices, and all final graphs are
  `k`-colourable when `|P_j(k)| ≥ K` (Corollary 5.4 via `IsTower.colorable`, i.e. Lemmas 5.1(i) and
  5.2).  Under the same hypothesis, `tower_colorable`: indeed every graph presented is
  `k`-colourable; `NkLE_playSize`: `N_k(K) ≤ (K-1) ∏ b_ℓ + 1`.  The paper assumes `k ≥ 2` and
  `j ≥ 1`; neither is needed.  `tower_spec` collects what is known about a play.
* `tower_presents`: every graph presented is an initial segment of a `j`-fold full blow-up of
  `K_K` (`IsFullTower`).
* Remark 6.5 for the graphs presented by `tower K j`: `tower_cliqueFree_three` (triangle-free for
  `j ≥ 1`), `tower_odd_walk` and `tower_isBipartite_or_oddGirth` (bipartite or odd girth at least
  `2j + 3`), `tower_firstFit_le` (First-Fit uses at most `K` colours on them),
  `tower_card_usedColours_eq` (every proper algorithm, in particular First-Fit
  (`tower_firstFit_eq`), ends with exactly `K` colours against the adversary).
-/

@[expose] public section

namespace OnlineColouring.Blow

open Finset

/-- **The adversary of Theorem 6.4**: the clique `K_K` with `j` reservation blow-ups below it. -/
def tower (K j : ℕ) : Adversary := stack K (K - 1) (Adversary.clique K) j

theorem deg_eq_levelDeg {K : ℕ} (hK : 2 ≤ K) : ∀ i, deg K (K - 1) i = levelDeg K i
  | 0 => (levelDeg_zero hK).symm
  | i + 1 => by rw [deg, deg_eq_levelDeg hK i, levelDeg_succ]; rfl

theorem tower_succ {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    tower K (j + 1) = B K (levelDeg K j) (tower K j) := by
  rw [← deg_eq_levelDeg hK j]
  rfl

/-! ### The graphs presented -/

/-- **The graphs presented by the adversary of Theorem 6.4.**  Against every proper algorithm
`Alg`, the play of `tower K j` follows an input sequence `H` whose first `K b_j ⋯ b_1` vertices
form a `j`-fold full blow-up of `K_K` (in the proof, each blow-up is a reservation blow-up) with
at most `K - 1` earlier neighbours per vertex, and it stops at the first moment
`T ≤ K b_j ⋯ b_1` at which `Alg` has used `K` colours.  So every graph presented is an initial
segment of such a blow-up. -/
theorem tower_play {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ Alg : OnlineAlg, Alg.IsProper →
      ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H) (T : ℕ),
        IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
        (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
        (∀ v < towerSize K j, (H v).card ≤ K - 1) ∧
        T ≤ towerSize K j ∧
        Follows (tower K j) Alg H T ∧
        K ≤ ((range T).image (runCol Alg H)).card ∧
        ∀ t < T, ((range t).image (runCol Alg H)).card < K := by
  induction j with
  | zero =>
    intro Alg hAlg
    refine ⟨cliqueSeq, cliqueSeq_valid, K, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
    · change IsFullTower K 0 (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph
      rw [ofSeq_cliqueSeq]
      exact .clique
    · intro w _
      rw [levelDeg_zero hK]
      exact postDeg_cliqueSeq_le K w
    · intro v hv
      change v < K at hv
      rw [cliqueSeq, card_range]
      omega
    · exact Adversary.clique_hist K Alg
    · exact (card_image_runCol_cliqueSeq hAlg K).ge
    · intro t ht
      rw [card_image_runCol_cliqueSeq hAlg t]
      exact ht
  | succ j ih =>
    intro Alg hAlg
    have hRj : levelDeg K (j + 1) = R K (levelDeg K j) := levelDeg_succ K j
    obtain ⟨H, hH, T', htower, hdeg, hcard, hT'm, hfol', hTK', hlt'⟩ :=
      ih (induced Alg K (levelDeg K j)) (induced_isProper _ _ _)
    have hrc : runCol (induced Alg K (levelDeg K j)) H =
        runCol (inducedAlg Alg (R K (levelDeg K j)) (levelDeg K j)) H :=
      funext (runCol_induced hH K _)
    rw [hrc] at hTK'
    have hT := hfol'.tracks hH
    rw [tower_succ hK j]
    set D := levelDeg K j with hDdef
    set m := towerSize K j with hmdef
    have hR : 0 < R K D := R_pos K D
    have hD : 1 ≤ D := one_le_levelDeg K j
    have hDR : D ≤ R K D := le_R hK
    have hσ := resPos_blockPerm (D := D) hR (outCol (R K D) D H Alg)
    have hdeg' : ∀ w < m, postDeg H m w ≤ R K D := fun w hw => (hdeg w hw).trans hDR
    have hsize : towerSize K (j + 1) = m * R K D := by rw [← hRj]; rfl
    have hG := outSeq_eq (D := D) (A := Alg) hH (R := R K D)
    obtain ⟨T, hTle, hfol, hTK, hlt, -⟩ := sim hD hAlg hH hT
      (fun w hw => (rank_mono H w hT'm).trans (hdeg w (lt_of_lt_of_le hw hT'm))) hTK'
    refine ⟨blowSeq (R K D) H (resPos (R K D) D (outCol (R K D) D H Alg)),
      blowSeq_valid hH hR hσ, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsize]
      exact .blowUp htower ⟨blowUpOf hH hR hσ hdeg', (blowUpOf_isReservation hH hR hσ hdeg').isFull⟩
    · rw [hsize, hRj]
      exact fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w
    · intro v hv
      rw [hsize] at hv
      refine card_image_le.trans (hcard _ ?_)
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hv)
    · rw [hsize]
      exact hTle.trans (Nat.mul_le_mul_right _ hT'm)
    · rw [← hG]
      exact hfol
    · rw [← hG]
      exact hTK
    · rw [← hG]
      exact hlt

/-! ### Forcing, and the end of the play, from Lemma 6.3 -/

theorem clique_sizeLE (K : ℕ) : (Adversary.clique K).SizeLE K := by
  intro A _ p
  rw [Adversary.clique_hist, length_runHist]
  exact min_le_right _ _

theorem clique_postDegLE (K : ℕ) : (Adversary.clique K).PostDegLE (K - 1) := by
  intro A _ p i
  rw [Adversary.clique_hist]
  exact (postDeg_runHist_le _ _ _ _).trans
    ((rank_mono _ _ (min_le_right p K)).trans (postDeg_cliqueSeq_le K i))

/-- **Lemma 6.3 for the adversary of Theorem 6.4**: `tower K j` forces `K` colours, and while the
algorithm has used at most `K - 1` colours the invariant `StackOK` holds at every level. -/
theorem tower_stackOK {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    (tower K j).Forces K ∧
      ∀ Alg : OnlineAlg, Alg.IsProper → ∀ p,
        (usedColours ((tower K j).hist Alg p)).card ≤ K - 1 →
        StackOK K (K - 1) (Adversary.clique K) (usedColours ((tower K j).hist Alg p)) j Alg
          ((tower K j).hist Alg p) :=
  lemma_6_3 hK (by omega) (Adversary.clique_forces K) (clique_sizeLE K) (clique_postDegLE K) j

theorem usedColours_snoc (h : History) (s : Finset ℕ) (c : ℕ) :
    usedColours (h ++ [(s, c)]) = insert c (usedColours h) := by
  ext x
  simp [usedColours]

theorem nbrColours_subset_usedColours (h : History) (s : Finset ℕ) :
    nbrColours h s ⊆ usedColours h := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
  exact colourAt_mem_usedColours (mem_filter.1 hi).2

/-- **"The play ends no later than the first vertex below `v_K`", the colours seen by `y`.**
Let `y` be the first presented vertex below `v_K`, the vertex with index `(K-1) b_j ⋯ b_1`.  If the
invariant of Lemma 6.3 holds when `y` is about to be presented, then `tower K j` presents `y`, and
the earlier neighbours of `y` carry at least `K - 1` colours: at every level they are servers, one
below each `v_s` with `s < K`, and by Lemma 6.3 the server below `v_s` has the induced colour
`col(v_s)`; at the top these are the `K - 1` distinct colours of `v_1, …, v_{K-1}`. -/
theorem tower_first_last {K : ℕ} (hK : 2 ≤ K) (C : Finset ℕ) :
    ∀ (j : ℕ) (Alg : OnlineAlg), Alg.IsProper → ∀ p,
      StackOK K (K - 1) (Adversary.clique K) C j Alg ((tower K j).hist Alg p) →
      ((tower K j).hist Alg p).length = firstLast K j →
      ∃ s, (tower K j).move ((tower K j).hist Alg p) = some s ∧
        K - 1 ≤ (nbrColours ((tower K j).hist Alg p) s).card := by
  intro j
  induction j with
  | zero =>
    intro Alg hAlg p _ hlen
    have e : tower K 0 = Adversary.clique K := rfl
    rw [e, Adversary.clique_hist] at hlen ⊢
    rw [length_runHist] at hlen
    have hlen' : min p K = K - 1 := hlen
    rw [hlen']
    refine ⟨cliqueSeq (K - 1), ?_, ?_⟩
    · change (if (runHist Alg cliqueSeq (K - 1)).length < K then
        some (range (runHist Alg cliqueSeq (K - 1)).length) else none) = _
      rw [length_runHist]
      exact ite_eq_left_of_eq_true _ _ (eq_true (by omega))
    · rw [nbrColours_runHist (cliqueSeq_valid _)]
      exact (card_image_runCol_cliqueSeq hAlg (K - 1)).ge
  | succ j ih =>
    intro Alg hAlg p hok hlen
    obtain ⟨-, hglen, hcol, hsrv, -, hok'⟩ := hok
    have hR : firstLast K (j + 1) = firstLast K j * R K (deg K (K - 1) j) := by
      rw [deg_eq_levelDeg hK j]
      change firstLast K j * levelDeg K (j + 1) = _
      rw [levelDeg_succ]
      rfl
    have hm : ((tower K (j + 1)).hist Alg p).length / R K (deg K (K - 1) j) = firstLast K j := by
      rw [hlen, hR, Nat.mul_div_cancel _ (R_pos _ _)]
    obtain ⟨s', hs', hK'⟩ := ih (induced Alg K (deg K (K - 1) j)) (induced_isProper _ _ _)
      (((tower K (j + 1)).hist Alg p).length / R K (deg K (K - 1) j)) hok'
      (hglen.trans hm)
    obtain ⟨srv, hmove, hsrv'⟩ := hsrv s' hs'
    refine ⟨_, hmove, hK'.trans (card_le_card ?_)⟩
    intro c hc
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
    obtain ⟨hws, hwlt⟩ := mem_filter.1 hw
    have hwm : w < ((tower K (j + 1)).hist Alg p).length / R K (deg K (K - 1) j) :=
      lt_of_lt_of_eq hwlt hglen
    obtain ⟨hdiv, hcw⟩ := hsrv' w hws hwm
    refine mem_image.2 ⟨srv w, mem_filter.2 ⟨mem_image.2 ⟨w, mem_inter.2 ⟨hws, mem_range.2 hwm⟩,
      rfl⟩, ?_⟩, ?_⟩
    · by_contra hcon
      have := Nat.div_le_div_right (c := R K (deg K (K - 1) j)) (not_lt.1 hcon)
      omega
    · rw [hcw, (hcol w hwm).1]
      rfl

/-- **"The play ends no later than the first vertex below `v_K`."**  Every play of `tower K j`
has at most `(K-1) b_j ⋯ b_1 + 1` vertices: by `tower_first_last`, the vertex `y` with index
`(K-1) b_j ⋯ b_1` receives a `K`-th colour if fewer than `K` colours are in use when it arrives,
and the adversary stops as soon as `K` colours are in use. -/
theorem tower_sizeLE {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : (tower K j).SizeLE (playSize K j) := by
  cases j with
  | zero =>
    refine (clique_sizeLE K).mono ?_
    rw [← firstLast_add_one]
    change K ≤ K - 1 + 1
    omega
  | succ j =>
    intro Alg hAlg p
    rw [← firstLast_add_one]
    have hst : tower K (j + 1) = B K (deg K (K - 1) j) (tower K j) := rfl
    have key : ((tower K (j + 1)).hist Alg p).length ≤ firstLast K (j + 1) + 1 ∧
        (((tower K (j + 1)).hist Alg p).length = firstLast K (j + 1) + 1 →
          K ≤ (usedColours ((tower K (j + 1)).hist Alg p)).card) := by
      induction p with
      | zero => exact ⟨Nat.zero_le _, fun h => absurd h (Nat.succ_ne_zero _).symm⟩
      | succ p ih =>
        cases hmv : (tower K (j + 1)).move ((tower K (j + 1)).hist Alg p) with
        | none =>
          rw [hist_succ_none hmv]
          exact ih
        | some s =>
          rw [hist_succ_some hmv]
          have hlt : (usedColours ((tower K (j + 1)).hist Alg p)).card < K := by
            by_contra hcon
            have hnone : (B K (deg K (K - 1) j) (tower K j)).move
                ((tower K (j + 1)).hist Alg p) = none :=
              ite_eq_left_of_eq_true _ _ (eq_true (not_lt.1 hcon))
            rw [← hst, hmv] at hnone
            exact Option.some_ne_none _ hnone
          have hne : ((tower K (j + 1)).hist Alg p).length ≠ firstLast K (j + 1) + 1 :=
            fun h => absurd (ih.2 h) (not_le.2 hlt)
          have hle := ih.1
          rw [List.length_append, List.length_singleton]
          refine ⟨by omega, fun hlen => ?_⟩
          obtain ⟨s₀, hs₀, hK'⟩ := tower_first_last hK _ (j + 1) Alg hAlg p
            ((tower_stackOK hK (j + 1)).2 Alg hAlg p (by omega)) (by omega)
          obtain rfl : s₀ = s := Option.some.inj (hs₀.symm.trans hmv)
          have hnot := (OnlineAlg.isProper_iff Alg).1 hAlg ((tower K (j + 1)).hist Alg p) s₀
          rw [usedColours_snoc]
          have := card_le_card (insert_subset_insert
            (Alg.step ((tower K (j + 1)).hist Alg p) s₀)
            (nbrColours_subset_usedColours ((tower K (j + 1)).hist Alg p) s₀))
          rw [card_insert_of_notMem hnot] at this
          omega
    exact key.1

/-- **The play of the iterated reservation adversary.**  Against a proper algorithm `Alg`, the
play of `tower K j` follows an input sequence `H` whose first `K b_j ⋯ b_1` vertices form a
`j`-fold full blow-up of `K_K` in which every vertex has at most `K - 1` earlier neighbours, and it
stops after `T ≤ (K-1) b_j ⋯ b_1 + 1` vertices, with exactly `K` colours in use. -/
theorem tower_spec {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper) :
    ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H) (T : ℕ),
      IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
      (∀ v < towerSize K j, (H v).card ≤ K - 1) ∧
      T ≤ playSize K j ∧ playSize K j ≤ towerSize K j ∧
      Follows (tower K j) Alg H T ∧ ((range T).image (runCol Alg H)).card = K := by
  obtain ⟨H, hH, T, htower, -, hcard, -, hfol, hTK, hlt⟩ := tower_play hK j Alg hAlg
  have hT : T ≤ playSize K j := by
    have := tower_sizeLE hK j Alg hAlg T
    rwa [hfol T, min_self, length_runHist] at this
  refine ⟨H, hH, T, htower, hcard, hT, playSize_le_towerSize (by omega) j, hfol,
    le_antisymm ?_ hTK⟩
  cases T with
  | zero => simp
  | succ T =>
    have := hlt T (Nat.lt_succ_self T)
    rw [range_add_one, image_insert]
    exact (card_insert_le _ _).trans (by omega)

/-- **Theorem 6.4 (the iterated reservation adversary).**  Let `K ≥ 2` and `|P_j(k)| ≥ K`, and
put `b_ℓ = (K-1)^{j-ℓ+1}(K-2)+1`.  The adversary `tower K j` forces every deterministic online
algorithm to use `K` colours, every play has at most
`(K-1) ∏_{ℓ=1}^{j} b_ℓ + 1 ≤ K^((j+1)(j+2)/2)` vertices, and all its final graphs are
`k`-colourable. -/
theorem theorem_6_4 {k K j : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    (tower K j).Forces K ∧
    (tower K j).SizeLE ((K - 1) * ∏ ℓ ∈ Icc 1 j, ((K - 1) ^ (j - ℓ + 1) * (K - 2) + 1) + 1) ∧
    (K - 1) * ∏ ℓ ∈ Icc 1 j, ((K - 1) ^ (j - ℓ + 1) * (K - 2) + 1) + 1 ≤
      K ^ ((j + 1) * (j + 2) / 2) ∧
    (tower K j).LandsIn fun _ G => G.Colorable k := by
  refine ⟨(tower_stackOK hK j).1, tower_sizeLE hK j, playSize_le hK j, ?_⟩
  · intro Alg hAlg p _
    obtain ⟨H, hH, T, htower, -, hT, hle, hfol, -⟩ := tower_spec hK j hAlg
    rw [hfol p]
    exact hasLabelling_labelPoset_zero_iff.1 (hasLabelling_runHist hH
      ((min_le_right _ _).trans (hT.trans hle))
      (hasLabelling_labelPoset_zero_iff.2 (htower.isTower.colorable hKj)))

/-- Every graph presented by the adversary of Theorem 6.4 is `k`-colourable (not only the final
ones). -/
theorem tower_colorable {k K j : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j))
    {Alg : OnlineAlg} (hAlg : Alg.IsProper) (p : ℕ) :
    ((tower K j).hist Alg p).graph.Colorable k := by
  obtain ⟨H, hH, T, htower, -, hT, hle, hfol, -⟩ := tower_spec hK j hAlg
  rw [hfol p]
  exact hasLabelling_labelPoset_zero_iff.1 (hasLabelling_runHist hH
    ((min_le_right _ _).trans (hT.trans hle))
    (hasLabelling_labelPoset_zero_iff.2 (htower.isTower.colorable hKj)))

/-- Theorem 6.4 in terms of `N_k(K)`: `N_k(K) ≤ (K-1) b_j ⋯ b_1 + 1`. -/
theorem NkLE_playSize {k K j : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    NkLE k K (playSize K j) :=
  ⟨tower K j, (theorem_6_4 hK hKj).1, (theorem_6_4 hK hKj).2.1, (theorem_6_4 hK hKj).2.2.2⟩

/-! ### Remark 6.5: the hard instances -/

/-- Every graph presented by `tower K j` is an initial segment of a `j`-fold full blow-up of
`K_K`: the history is the run on the first `t` vertices of an input sequence whose first
`K b_j ⋯ b_1` vertices form such a blow-up. -/
theorem tower_presents {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper)
    (p : ℕ) :
    ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H) (t : ℕ), t ≤ towerSize K j ∧
      IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
      (∀ v < towerSize K j, (H v).card ≤ K - 1) ∧
      (tower K j).hist Alg p = runHist Alg H t := by
  obtain ⟨H, hH, T, htower, hcard, hT, hle, hfol, -⟩ := tower_spec hK j hAlg
  exact ⟨H, hH, min p T, (min_le_right _ _).trans (hT.trans hle), htower, hcard, hfol p⟩

/-- The graph of a run on a valid sequence maps homomorphically to every longer initial segment
of the sequence. -/
def runHom {N : ℕ → Finset ℕ} (hN : ValidSeq N) (X : OnlineAlg) {t n : ℕ} (htn : t ≤ n) :
    (runHist X N t).graph →g (OnlineInput.ofSeq N hN n).graph where
  toFun v := Fin.castLE (by rw [length_runHist]; exact htn) v
  map_rel' := by
    intro u v hadj
    rw [graph_runHist_adj] at hadj
    rw [OnlineInput.ofSeq_adj]
    rcases hadj with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- **Remark 6.5.**  In every graph presented by `tower K j`, every odd closed walk has length at
least `2j + 3`. -/
theorem tower_odd_walk {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper)
    (p : ℕ) (u : Fin ((tower K j).hist Alg p).length)
    (w : ((tower K j).hist Alg p).graph.Walk u u) (hw : Odd w.length) : 2 * j + 3 ≤ w.length := by
  obtain ⟨H, hH, t, ht, htower, -, hfol⟩ := tower_presents hK j hAlg p
  revert u
  rw [hfol]
  intro u w hw
  have hlen : (w.map (runHom hH Alg ht)).length = w.length := SimpleGraph.Walk.length_map _ _
  have hodd : Odd (w.map (runHom hH Alg ht)).length := hlen.symm ▸ hw
  have h1 : 2 * j + 3 ≤ (w.map (runHom hH Alg ht)).length :=
    htower.isTower.le_length_of_odd (G := (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph)
      (w.map (runHom hH Alg ht)) hodd
  exact h1.trans_eq hlen

/-- **Remark 6.5.**  Every graph presented by `tower K j` is bipartite or has odd girth at least
`2j + 3`. -/
theorem tower_isBipartite_or_oddGirth {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg}
    (hAlg : Alg.IsProper) (p : ℕ) :
    ((tower K j).hist Alg p).graph.IsBipartite ∨
      ((∃ (u : Fin ((tower K j).hist Alg p).length)
          (w : ((tower K j).hist Alg p).graph.Walk u u), Odd w.length) ∧
        ∀ (u : Fin ((tower K j).hist Alg p).length)
          (w : ((tower K j).hist Alg p).graph.Walk u u), Odd w.length → 2 * j + 3 ≤ w.length) := by
  by_cases h : ((tower K j).hist Alg p).graph.IsBipartite
  · exact Or.inl h
  · refine Or.inr ⟨?_, fun u w hw => tower_odd_walk hK j hAlg p u w hw⟩
    rw [SimpleGraph.isBipartite_iff_forall_walk_even_length] at h
    push Not at h
    obtain ⟨u, w, hw⟩ := h
    exact ⟨u, w, hw⟩

/-- **Remark 6.5.**  For `j ≥ 1`, every graph presented by `tower K j` is triangle-free. -/
theorem tower_cliqueFree_three {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg}
    (hAlg : Alg.IsProper) (p : ℕ) :
    ((tower K (j + 1)).hist Alg p).graph.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  have := tower_odd_walk hK (j + 1) hAlg p a (.cons hab (.cons hbc (.cons hac.symm .nil)))
    (by simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]; decide)
  simp at this

/-- First-Fit gives a vertex with `d` earlier neighbours a colour among the first `d + 1`
colours `0, …, d`. -/
theorem firstFit_step_le (h : History) (s : Finset ℕ) :
    OnlineAlg.firstFit.step h s ≤ s.card := by
  have hc : (nbrColours h s).card ≤ s.card :=
    card_image_le.trans (card_le_card (filter_subset _ _))
  have hex : ∃ c ∈ range ((nbrColours h s).card + 1), c ∉ nbrColours h s := by
    by_contra hcon
    push Not at hcon
    have := card_le_card (show range ((nbrColours h s).card + 1) ⊆ nbrColours h s from hcon)
    simp at this
  obtain ⟨c, hc1, hc2⟩ := hex
  have hff : OnlineAlg.firstFit.step h s ≤ c := Nat.find_min' _ hc2
  rw [mem_range] at hc1
  omega

/-- **Remark 6.5.**  First-Fit uses at most `K` colours on every graph presented by `tower K j`
(against any proper algorithm): every vertex has at most `K - 1` earlier neighbours.  The graph
of a history `h` is given to First-Fit as the input sequence `i ↦ N⁻(i)`. -/
theorem tower_firstFit_le {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper)
    (p : ℕ) :
    ((range ((tower K j).hist Alg p).length).image
      (runCol OnlineAlg.firstFit fun i => (((tower K j).hist Alg p).getD i (∅, 0)).1)).card ≤
      K := by
  obtain ⟨H, hH, t, ht, -, hcard, hfol⟩ := tower_presents hK j hAlg p
  rw [hfol, length_runHist]
  refine (card_le_card ?_).trans (card_range K).le
  intro c hc
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
  rw [mem_range] at hi ⊢
  have hseq : ∀ i' ≤ i, (fun i => ((runHist Alg H t).getD i (∅, 0)).1) i' = H i' := by
    intro i' hi'
    change ((runHist Alg H t).getD i' (∅, 0)).1 = H i'
    rw [List.getD_of_lt _ (by rw [length_runHist]; omega), getElem_runHist]
  rw [runCol_congr hseq]
  have h1 := firstFit_step_le (runHist OnlineAlg.firstFit H i) (H i)
  have h2 := hcard i (by omega)
  change OnlineAlg.firstFit.step (runHist OnlineAlg.firstFit H i) (H i) < K
  omega

/-- **Remark 6.5.**  Against the adversary `tower K j`, every proper algorithm ends with exactly
`K` colours in use. -/
theorem tower_card_usedColours_eq {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg}
    (hAlg : Alg.IsProper) {p : ℕ} (hp : (tower K j).StopsAt Alg p) :
    (usedColours ((tower K j).hist Alg p)).card = K := by
  obtain ⟨H, hH, T, -, -, -, -, hfol, hTK⟩ := tower_spec hK j hAlg
  have hpT : T ≤ p := by
    by_contra hcon
    have h1 := hfol (p + 1)
    rw [hist_succ_none hp, hfol p] at h1
    have := congrArg List.length h1
    rw [length_runHist, length_runHist] at this
    omega
  rw [hfol p, min_eq_right hpT, usedColours_runHist, hTK]

/-- **Remark 6.5.**  First-Fit uses exactly `K` colours against the adversary `tower K j`. -/
theorem tower_firstFit_eq {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {p : ℕ}
    (hp : (tower K j).StopsAt OnlineAlg.firstFit p) :
    (usedColours ((tower K j).hist OnlineAlg.firstFit p)).card = K :=
  tower_card_usedColours_eq hK j OnlineAlg.firstFit_isProper hp

end OnlineColouring.Blow
