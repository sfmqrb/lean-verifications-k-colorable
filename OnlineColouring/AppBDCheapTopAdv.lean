module

public import OnlineColouring.AppBDCheapTop
public import OnlineColouring.BlowStack

/-!
# Corollary B.2 (a cheaper top) as a statement about one adversary

Corollary B.2 (`cor:cheap-top`, Appendix B): *Let `K ≥ 3` and `j ≥ 1` with
`2K - 2 ≤ |P_j(k)|`.  Running the flow adversary of Theorem D.2 on `K_{2K-2}` and then `j - 1`
reservation blow-ups below it gives an adversary that forces `K` colours on `k`-colourable graphs
with at most `2^j K^{(j^2+j+2)/2}` vertices.*

* `cheapAdv K j` is the adversary that the corollary names: the flow adversary
  `flowAdv (2K-2) (minBlock (2K-2))` of Theorem D.2 on `K_{2K-2}` with the minimal blocks
  `max(1, m - t)`, with `j - 1` reservation blow-ups `Blow.B` of Construction 6.1 below it
  (`Blow.stack`).  The first blow-up has `D = 2K - 4`, the post-degree bound of the flow adversary,
  and each later one has `D` equal to the block size of the previous one, as in the paper's proof.
* `cheaper_top_composed`: **Corollary B.2** for this adversary.  It forces `K` colours, all its
  final graphs are `k`-colourable, and every play has at most `2^j K^{(j^2+j+2)/2}` vertices.
  `cheapAdv_sizeLE` is the exact bound `cheapTopSize K j` on the size, and `cheapAdv_colorable`
  says that every graph presented is `k`-colourable.
* The proof is the paper's (`cheapAdv_good`).  The flow adversary forces `⌊m/2⌋ + 1 = K` colours
  with `binom(m, 2) + 1` vertices and post-degree at most `2K - 4`, and its graphs are blow-ups of
  `K_m`, which map to `Tmpl(P_{j-1}(k))` by Lemma 5.1 (i) and Lemma 5.2 (`flowAdv_good`).  Each
  reservation blow-up keeps forcing (Lemmas 6.2 and 6.3) and takes one level off the labels
  (Lemma 5.2); this is `Blow.Good.stack`.
* `cheaper_top_adversary` is the existence form of the corollary, and `Nk_le_cheapTop` is the
  bound on `N_k(K)`.  The form for inputs against a fixed algorithm is `cheaper_top`
  (`AppBDCheapTop.lean`).
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-- The play of the flow adversary of Theorem D.2 (on `K_m`, `m ≥ 1`, with block sizes
`b t ≥ minBlock m t`) against a proper algorithm, in the form used for stacking (`Blow.Good`): it
follows an input sequence with `∑ b_t` vertices and stops, with `⌊m/2⌋ + 1` colours in use; the
post-degrees are at most `D` if the blocks other than the first have at most `D` vertices; and
the graph, a blow-up of `K_m`, maps to `Tmpl(P)` if `m ≤ |J*(P)|` (Lemma 5.1 (i) and
Lemma 5.2). -/
theorem flowAdv_good {P : Type*} [PartialOrder P] [Fintype (Jst P)] {m D : ℕ} {b : ℕ → ℕ}
    (hm : 1 ≤ m) (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) (hD : ∀ t, 1 ≤ t → t < m → b t ≤ D)
    (hP : m ≤ Fintype.card (Jst P)) :
    Blow.Good (m / 2 + 1) (start b m) D P (flowAdv m b) := by
  intro A hA
  have hb' : ∀ t < m, m - t - 1 ≤ b t := fun t ht => (le_max_right _ _).trans (hb t ht)
  have hb1 : ∀ t < m, 1 ≤ b t := fun t ht => (le_max_left _ _).trans (hb t ht)
  obtain ⟨srv, h1, h2, h3⟩ := flowSeq_isOneLevelSeq A hb'
  have hdata : OneLevelData m b (playSeq (flowRule m b) A) srv := ⟨h1, h2, h3⟩
  refine ⟨truncSeq (playSeq (flowRule m b) A) (start b m), hdata.valid, start b m, ?_, le_rfl,
    fun w hw => hdata.postDeg_le hD w hw, ?_,
    (hdata.blowUp hb1).hasLabelling_of_jst (hasLabelling_clique_iff.2 hP)⟩
  · intro p
    rw [flowAdv_hist]
    exact (runHist_congr fun j hj => if_pos_trunc (lt_of_lt_of_le hj (min_le_right _ _))).symm
  · have e : (range (start b m)).image
        (runCol A (truncSeq (playSeq (flowRule m b) A) (start b m))) =
        (range (start b m)).image (flowCol m b A) :=
      image_congr fun i hi => runCol_congr fun j hj =>
        if_pos_trunc (lt_of_le_of_lt hj (mem_range.1 hi))
    rw [e]
    exact colours_ge hm hb' hb1 fun t ht => flowCol_properAt A hA hb' ht

/-- **The adversary of Corollary B.2**: the flow adversary of Theorem D.2 on `K_{2K-2}` with the
minimal blocks, and `j - 1` reservation blow-ups below it.  The first blow-up has `D = 2K - 4`,
each later one has `D` equal to the block size of the previous one. -/
noncomputable def cheapAdv (K j : ℕ) : Adversary :=
  Blow.stack K (2 * K - 4) (flowAdv (2 * K - 2) (minBlock (2 * K - 2))) (j - 1)

/-- The plays of `cheapAdv K j` under the hypotheses of Corollary B.2: against every proper
algorithm the play follows an input sequence for at most `cheapTopSize K j` vertices and stops
with `K` colours in use, and its graph is `k`-colourable (it has a `P_0(k)`-labelling). -/
theorem cheapAdv_good {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    Blow.Good K (cheapTopSize K j) (Blow.deg K (2 * K - 4) (j - 1)) (LabelPoset k 0)
      (cheapAdv K j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have htop : Blow.Good K ((2 * K - 2).choose 2 + 1) (2 * K - 4) (LabelPoset k (0 + n))
      (flowAdv (2 * K - 2) (minBlock (2 * K - 2))) := by
    have h := flowAdv_good (P := LabelPoset k n) (m := 2 * K - 2) (D := 2 * K - 4)
      (b := minBlock (2 * K - 2)) (by omega) (fun t _ => le_rfl)
      (fun t ht _ => by
        simp only [minBlock]
        omega) hP
    have e : (2 * K - 2) / 2 + 1 = K := by omega
    rw [start_minBlock (by omega), e] at h
    rw [Nat.zero_add]
    exact h
  have h := htop.stack (by omega : 2 ≤ K) (by omega : 1 ≤ 2 * K - 4) n 0
  have e : cheapTopSize K (n + 1) =
      ((2 * K - 2).choose 2 + 1) * ∏ l ∈ range n, Blow.deg K (2 * K - 4) (l + 1) := by
    rw [cheapTopSize, Nat.add_sub_cancel]
    congr 1
    exact prod_congr rfl fun i _ => (Blow.deg_succ_eq _ _ i).symm
  unfold cheapAdv
  rw [e, Nat.add_sub_cancel]
  exact h

/-- Under the hypotheses of Corollary B.2, every play of `cheapAdv K j` has at most
`cheapTopSize K j` vertices. -/
theorem cheapAdv_sizeLE {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    (cheapAdv K j).SizeLE (cheapTopSize K j) :=
  (cheapAdv_good hK hj hP).sizeLE

/-- Under the hypotheses of Corollary B.2, every graph presented by `cheapAdv K j` is
`k`-colourable (not only the final ones). -/
theorem cheapAdv_colorable {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) {Alg : OnlineAlg} (hAlg : Alg.IsProper)
    (p : ℕ) : ((cheapAdv K j).hist Alg p).graph.Colorable k :=
  hasLabelling_labelPoset_zero_iff.1 ((cheapAdv_good hK hj hP).hasLabelling hAlg p)

/-- **Corollary B.2 (a cheaper top).**  Let `K ≥ 3` and `j ≥ 1` with `2K - 2 ≤ |P_j(k)|`.  The
adversary `cheapAdv K j`, which runs the flow adversary of Theorem D.2 on `K_{2K-2}` and then
`j - 1` reservation blow-ups below it, forces `K` colours, all its final graphs are
`k`-colourable, and every play has at most `2^j K^{(j^2+j+2)/2}` vertices. -/
theorem cheaper_top_composed {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    (cheapAdv K j).Forces K ∧ ((cheapAdv K j).LandsIn fun _ G => G.Colorable k) ∧
      (cheapAdv K j).SizeLE (2 ^ j * K ^ ((j ^ 2 + j + 2) / 2)) :=
  ⟨(cheapAdv_good hK hj hP).forces, fun _ hAlg p _ => cheapAdv_colorable hK hj hP hAlg p,
    (cheapAdv_sizeLE hK hj hP).mono (cheapTopSize_le hK hj)⟩

/-- **Corollary B.2 (a cheaper top), existence form.**  If `K ≥ 3`, `j ≥ 1` and
`2K - 2 ≤ |P_j(k)|`, there is an adversary that forces `K` colours, all of whose final graphs are
`k`-colourable, and every play of which has at most `2^j K^{(j^2+j+2)/2}` vertices: the adversary
`cheapAdv K j`. -/
theorem cheaper_top_adversary {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    ∃ adv : Adversary, adv.Forces K ∧ (adv.LandsIn fun _ G => G.Colorable k) ∧
      adv.SizeLE (2 ^ j * K ^ ((j ^ 2 + j + 2) / 2)) :=
  ⟨cheapAdv K j, cheaper_top_composed hK hj hP⟩

/-- Corollary B.2 in terms of `N_k(K)`. -/
theorem Nk_le_cheapTop {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    Nk k K ≤ (2 ^ j * K ^ ((j ^ 2 + j + 2) / 2) : ℕ) := by
  obtain ⟨adv, hF, hL, hS⟩ := cheaper_top_adversary (k := k) hK hj hP
  exact Nk_le_iff.2 ⟨adv, hF, hS, hL⟩

end OnlineColouring.AppBD
