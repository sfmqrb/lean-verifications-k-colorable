module

public import OnlineColouring.MainTheorem
public import OnlineColouring.Iso

/-!
# Known graphs: `χ_ol`, the digraph `H_j(K)` and the graph `G` of Theorem 1.3

Section 7.  The input that `forcing_structure` (`Forcing.lean`) builds against a proper algorithm
chooses its servers by colour, so different algorithms see different inputs, but by Lemma 7.1
(`SeqIso.blowSeq`) all of them are isomorphic, as digraphs oriented by arrival, to one fixed
graph `H_j(K)`.

* `canonSeq K j`: an input sequence whose first `K b_j ⋯ b_1` vertices form the canonical full
  tower `H_j(K)`, built from `K_K` by `j` blow-ups with blocks of size `b_j, …, b_1` in which the
  `r`-th later neighbour of a node is served by the `r`-th vertex of its block.
* `forcing_structure_iso` (the counterpart of Lemma 7.2 for these inputs): for every proper
  algorithm there is an input on which it uses `K` colours and which is isomorphic, oriented by
  arrival, to `H_j(K)`.  The adversary `𝒜^str` of the paper and Lemma 7.2 for it are
  `Str.strTower` and `Str.lemma_7_2` (`StrTower.lean`).
* `OnlineChromaticAtLeast G K` ("`χ_ol(G) ≥ K`"): every proper deterministic online algorithm uses
  at least `K` colours on some presentation of `G`, i.e. on some online input whose graph is
  isomorphic to `G`.  The algorithm is quantified after `G`, so it may depend on `G`; the bound
  therefore also holds in Halldórsson's known-graph game, in which Bob is shown `G` in advance
  (every prefix of a presentation of `G` is isomorphic to an induced subgraph of `G`, so
  presenting `G` is legal).  The number `χ_ol(G)` itself is `Paper.chiOl`
  (`PaperStatements.lean`), with `Paper.le_chiOl_iff`.
* `knownGraph K j N`: `H_j(K)` followed by isolated vertices, `N` vertices in all.  For `K ≥ 2`:
  `knownGraph_colorable`: it is `k`-colourable when `|P_j(k)| ≥ K`; `knownGraph_cliqueFree`: it is
  triangle-free for `j ≥ 1`; `known_graph_of_inputs`: it has `χ_ol ≥ K` when `N ≥ K b_j ⋯ b_1`,
  from the inputs of `forcing_structure_iso`.
* The statements of Theorem 1.3 about `G` (`known_graph`, `known_graph_three_floor`,
  `known_graph_of_four_le_floor`) are in `StrKnown.lean`; they are proved as in the paper, from
  the adversary `𝒜^str` and Lemma 7.2 (`Str.known_graph_adversary`).  The statements about `G′`
  are in `MainLogStar.lean`, and both graphs appear together in `Paper.known_graphs_three`,
  `Paper.known_graphs_of_four_le`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-- Server positions `t mod R`, used by `canonSeq`. -/
theorem modPerm {R : ℕ} (hR : 0 < R) : BlockPerm R (fun _ t => t % R) where
  lt _ t := Nat.mod_lt t hR
  inj _ t t' ht ht' h := by rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h

/-- An input sequence whose first `K b_j ⋯ b_1` vertices form the canonical full `j`-level tower
`H_j(K)` over `K_K`. -/
def canonSeq (K : ℕ) : ℕ → ℕ → Finset ℕ
  | 0 => cliqueSeq
  | j + 1 => blowSeq (levelDeg K (j + 1)) (canonSeq K j) (fun _ t => t % levelDeg K (j + 1))

theorem canonSeq_valid (K j : ℕ) : ValidSeq (canonSeq K j) := by
  induction j with
  | zero => exact cliqueSeq_valid
  | succ j ih =>
    exact blowSeq_valid ih (one_le_levelDeg K (j + 1)) (modPerm (one_le_levelDeg K (j + 1)))

theorem canonSeq_spec {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    IsFullTower K j
        (OnlineInput.ofSeq (canonSeq K j) (canonSeq_valid K j) (towerSize K j)).toOrdGraph ∧
      ∀ w < towerSize K j, postDeg (canonSeq K j) (towerSize K j) w ≤ levelDeg K j := by
  induction j with
  | zero =>
    refine ⟨?_, fun w _ => by rw [levelDeg_zero hK]; exact postDeg_cliqueSeq_le K w⟩
    change IsFullTower K 0 (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph
    rw [ofSeq_cliqueSeq]
    exact .clique
  | succ j ih =>
    obtain ⟨htower, hdeg⟩ := ih
    have hR : 0 < levelDeg K (j + 1) := one_le_levelDeg K (j + 1)
    have hσ := modPerm hR
    have hdeg' : ∀ w < towerSize K j,
        postDeg (canonSeq K j) (towerSize K j) w ≤ levelDeg K (j + 1) :=
      fun w hw => (hdeg w hw).trans (levelDeg_le_succ hK j)
    have hH := canonSeq_valid K j
    exact ⟨.blowUp htower ⟨blowUpOf hH hR hσ hdeg', (blowUpOf_isReservation hH hR hσ hdeg').isFull⟩,
      fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w⟩

/-- **The counterpart of Lemma 7.2 (one final graph) for the inputs of `forcing_structure`.** For
every proper algorithm `A` there is an input sequence, built as in `forcing_structure`, whose
first `K b_j ⋯ b_1` vertices have post-degree at most `levelDeg K j` and form a digraph (oriented
by arrival) isomorphic to `H_j(K)`, and on which `A` uses at least `K` colours. -/
theorem forcing_structure_iso {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ A : OnlineAlg, A.IsProper →
      ∃ H : ℕ → Finset ℕ, ValidSeq H ∧
        (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
        SeqIso H (canonSeq K j) (towerSize K j) ∧
        K ≤ ((range (towerSize K j)).image (runCol A H)).card := by
  induction j with
  | zero =>
    intro A hA
    exact ⟨cliqueSeq, cliqueSeq_valid,
      fun w _ => by rw [levelDeg_zero hK]; exact postDeg_cliqueSeq_le K w, SeqIso.refl _ _,
      (card_image_runCol_cliqueSeq hA K).ge⟩
  | succ j ih =>
    intro A hA
    obtain ⟨R, hRdef⟩ : ∃ R, R = (K - 1) * (levelDeg K j - 1) + 1 := ⟨_, rfl⟩
    have hRj : levelDeg K (j + 1) = R := by rw [hRdef, levelDeg_succ]
    obtain ⟨H, hH, hdeg, hiso, hforce⟩ :=
      ih (inducedAlg A R (levelDeg K j)) (inducedAlg_isProper A R (levelDeg K j))
    have hdegc := (canonSeq_spec hK j).2
    have hR : 0 < R := by omega
    have hD : 1 ≤ levelDeg K j := one_le_levelDeg K j
    have hDR : levelDeg K j ≤ R := hRj ▸ levelDeg_le_succ hK j
    have hσ := resPos_blockPerm (D := levelDeg K j) hR (outCol R (levelDeg K j) H A)
    have hdeg' : ∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ R :=
      fun w hw => (hdeg w hw).trans hDR
    have hdegc' : ∀ w < towerSize K j, postDeg (canonSeq K j) (towerSize K j) w ≤ R :=
      fun w hw => (hdegc w hw).trans hDR
    have hsize : towerSize K (j + 1) = towerSize K j * R := by rw [← hRj]; rfl
    have hcanon : canonSeq K (j + 1) = blowSeq R (canonSeq K j) (fun _ t => t % R) := by
      rw [← hRj]; rfl
    refine ⟨blowSeq R H (resPos R (levelDeg K j) (outCol R (levelDeg K j) H A)),
      blowSeq_valid hH hR hσ, ?_, ?_, ?_⟩
    · rw [hsize, hRj]
      exact fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w
    · rw [hsize, hcanon]
      exact hiso.blowSeq hR hσ (modPerm hR) hdeg' hdegc'
    · rw [hsize, ← outSeq_eq hH]
      exact forcing_step hRdef hD hA hH hdeg hforce

/-- `χ_ol(G) ≥ K`: every proper deterministic online algorithm (which may depend on `G`) uses at
least `K` colours on some presentation of `G`. -/
def OnlineChromaticAtLeast {N : ℕ} (G : SimpleGraph (Fin N)) (K : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ I : OnlineInput N, Nonempty (I.graph ≃g G) ∧ K ≤ I.cost A

/-- `H_j(K)` followed by isolated vertices, `N` vertices in all (if `N ≥ K b_j ⋯ b_1`). -/
def knownGraph (K j N : ℕ) : SimpleGraph (Fin N) :=
  (OnlineInput.ofSeq (truncSeq (canonSeq K j) (towerSize K j))
    (truncSeq_valid (canonSeq_valid K j) _) N).graph

/-- `H_j(K)` padded to `N` vertices is `k`-colourable if `K ≥ 2` and `|P_j(k)| ≥ K`
(Corollary 5.4). -/
theorem knownGraph_colorable {k K j N : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) : (knownGraph K j N).Colorable k := by
  have hc := (canonSeq_spec hK j).1.isTower.colorable hKj
  have hk : 1 ≤ k := one_le_of_colorable (by have := two_le_towerSize hK j; omega) hc
  exact colorable_truncSeq (canonSeq_valid K j) hk hc

/-- **`χ_ol(G) ≥ K`, from inputs against a fixed algorithm.** If `K ≥ 2` and
`N ≥ K b_j ⋯ b_1`, then `H_j(K)` padded to `N` vertices has online chromatic number at least `K`:
for every proper algorithm, the input of `forcing_structure_iso` followed by isolated vertices is
a presentation of it.  The paper's proof, with the adversary `𝒜^str` and Lemma 7.2, is
`Str.known_graph_adversary` (`StrTower.lean`), and that is the proof behind `known_graph`
(`StrKnown.lean`). -/
theorem known_graph_of_inputs {K j N : ℕ} (hK : 2 ≤ K) (hN : towerSize K j ≤ N) :
    OnlineChromaticAtLeast (knownGraph K j N) K := by
  intro A hA
  obtain ⟨H, hH, -, hiso, hforce⟩ := forcing_structure_iso hK j A hA
  exact ⟨_, (hiso.truncSeq hH (canonSeq_valid K j) hN).graphIso _ _,
    le_cost_truncSeq hH hN hforce⟩

/-- For `K ≥ 2` and `j ≥ 1`, `H_j(K)` is triangle-free (Remark 6.5), also after padding. -/
theorem knownGraph_cliqueFree {K j N : ℕ} (hK : 2 ≤ K) (hj : 1 ≤ j) :
    (knownGraph K j N).CliqueFree 3 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hR : 0 < levelDeg K (j + 1) := one_le_levelDeg K (j + 1)
  have hdeg' : ∀ w < towerSize K j,
      postDeg (canonSeq K j) (towerSize K j) w ≤ levelDeg K (j + 1) :=
    fun w hw => ((canonSeq_spec hK j).2 w hw).trans (levelDeg_le_succ hK j)
  apply cliqueFree_three_ofSeq
  intro x u u' _ _
  apply truncSeq_notMem
  intro x u u' hu hu' hx hx'
  exact notMem_of_mem_blowSeq (canonSeq_valid K j) hR (modPerm hR) hdeg' hu hu' hx hx'

/-! ### Small cases -/

/-- The graph with no edges on `N ≥ 1` vertices has `χ_ol ≥ 1`. -/
theorem emptyInput_onlineChromaticAtLeast_one {N : ℕ} (hN : 1 ≤ N) :
    OnlineChromaticAtLeast (emptyInput N).graph 1 := by
  intro A _
  refine ⟨emptyInput N, ⟨RelIso.refl _⟩, ?_⟩
  unfold OnlineInput.cost
  exact Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hN⟩)⟩

theorem emptyInput_cliqueFree (N : ℕ) : (emptyInput N).graph.CliqueFree 3 := by
  apply cliqueFree_three_of
  intro x y _ _ _ hxy
  rcases hxy with h | h <;> exact absurd h (Finset.notMem_empty _)

/-- A small `K` is witnessed by the empty graph. -/
theorem exists_known_graph_of_le_one {N k K : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hK : K ≤ 1) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧ OnlineChromaticAtLeast G K := by
  refine ⟨(emptyInput N).graph, emptyInput_colorable hk, emptyInput_cliqueFree N, ?_⟩
  intro A hA
  obtain ⟨I, hI, hc⟩ := emptyInput_onlineChromaticAtLeast_one hN A hA
  exact ⟨I, hI, hK.trans hc⟩

end OnlineColouring
