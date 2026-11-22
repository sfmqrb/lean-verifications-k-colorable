module

public import OnlineColouring.AppBDPJ
public import OnlineColouring.BlowTower

/-!
# The classes of Theorems D.4 and D.5 are not vacuous

`top_block` (Theorem D.4) and `partial_joins` (Theorem D.5) are proved for every adversary of the
classes `IsTopBlockAdv` and `IsPJAdv`.  This module shows that the two classes contain adversaries
that satisfy all the other hypotheses of the two theorems.  The witness is `Blow.tower K 1`, the
adversary of Theorem 6.4 with one level: the reservation blow-up `B(K_K)` of the clique, with
blocks of `R = (K-1)(K-2)+1` vertices, so that the block of the next vertex is `|h| / R`.

* `top_block_witness`: for `K ≥ 2`, `Blow.tower K 1` presents `K_K` blown up once
  (`IsTopBlockAdv`; in fact with one server per arc), and it forces `K` colours.
* `towerOne_isPJAdv`: the same adversary is a partial-join level over `K_K` (`IsPJAdv`) in which
  all the vertices of a block have the same earlier neighbours, one server in the reserve of each
  earlier block; `blowRes R (K-1) h` is the set of the vertices of the reserves of the complete
  blocks of `h`.
* `partial_joins_witness`: for `2 ≤ m ≤ 7 = |P_1(3)|`, the adversary `Blow.tower m 1` is a
  partial-join level over `K_m`, forces `m` colours, presents only `3`-colourable graphs, and its
  plays have at most `playSize m 1` vertices (Theorem 6.4).  So it satisfies every hypothesis of
  Theorem D.5, which shows that these hypotheses can hold together.  For these `m` the inequality
  of the theorem already follows from `N ≥ m` (its right side is negative), and for `m ≥ 8` the
  one-level tower is not `3`-colourable in every play (Theorem 1.5).

Both forms are read off from `Blow.sim`: against a proper algorithm, the play of `Blow.tower K 1`
follows the static blow-up `blowSeq R cliqueSeq σ` of the clique (`outSeq_eq`), with the server
positions `σ` chosen from the colours of the algorithm, and it stops after at most `K R`
vertices.  Before it stops, every complete block has a colour on at least `K - 1` of its vertices,
and the reserve of the block consists of `K - 1` of them (`towerOne_play`).
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-- The reserves of the complete blocks at the history `h`, for blocks of `R` vertices and
reserves of `D` vertices: the first `D` vertices, in the order `resOrder`, of every complete block
(Construction 6.1, step 3). -/
def blowRes (R D : ℕ) (h : History) : Finset ℕ :=
  (range (h.length / R)).biUnion fun w =>
    (range D).image fun r => w * R + resPos R D (colourAt h) w r

variable {K R : ℕ} {Alg : OnlineAlg}

/-! ### Histories of the static blow-up of the clique -/

theorem bidx_div {N : ℕ → Finset ℕ} {n i : ℕ} (hi : i ≤ n) :
    bidx (fun g : History => g.length / R) (runHist Alg N n) i = i / R := by
  simp only [bidx, runHist_take hi, length_runHist]

theorem nb_runHist {N : ℕ → Finset ℕ} {n i : ℕ} (hi : i < n) : nb (runHist Alg N n) i = N i := by
  rw [nb_eq_getElem (by rwa [length_runHist]), getElem_runHist]

theorem nb_outSeq {D n i : ℕ} (hi : i < n) :
    nb (runHist Alg (outSeq R D cliqueSeq Alg) n) i =
      blowSeq R cliqueSeq (resPos R D (outCol R D cliqueSeq Alg)) i := by
  rw [nb_runHist hi]
  exact congrFun (outSeq_eq cliqueSeq_valid) i

theorem colourAt_outSeq {D n i : ℕ} (hi : i < n) :
    colourAt (runHist Alg (outSeq R D cliqueSeq Alg) n) i = outCol R D cliqueSeq Alg i :=
  colourAt_runHist hi

/-- The reserves at a moment of the play, in terms of the colours of the whole play. -/
theorem mem_blowRes_outSeq (hR : 0 < R) {j x : ℕ} :
    x ∈ blowRes R (K - 1) (runHist Alg (outSeq R (K - 1) cliqueSeq Alg) j) ↔
      x / R < j / R ∧ ∃ r < K - 1,
        x = x / R * R + resPos R (K - 1) (outCol R (K - 1) cliqueSeq Alg) (x / R) r := by
  have hσ := resPos_blockPerm (D := K - 1) hR (outCol R (K - 1) cliqueSeq Alg)
  have hpos : ∀ w < j / R,
      resPos R (K - 1) (colourAt (runHist Alg (outSeq R (K - 1) cliqueSeq Alg) j)) w =
        resPos R (K - 1) (outCol R (K - 1) cliqueSeq Alg) w := by
    intro w hw
    apply resPos_congr
    intro t ht
    apply colourAt_runHist
    have h1 := Nat.mul_le_mul_right R hw
    have h2 := Nat.div_mul_le_self j R
    rw [Nat.succ_mul] at h1
    omega
  simp only [blowRes, length_runHist, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨w, hw, r, hr, rfl⟩
    rw [hpos w hw, div_add_lt hR (hσ.lt w r)]
    exact ⟨hw, r, hr, rfl⟩
  · rintro ⟨hx, r, hr, hxe⟩
    refine ⟨x / R, hx, r, hr, ?_⟩
    rw [hpos _ hx]
    exact hxe.symm

/-- A history of the blow-up of the clique `K_K` with blocks of `R ≥ K - 1` vertices and at most
`K` blocks has the form of Theorem D.4. -/
theorem topForm_outSeq (hR : 0 < R) (hKR : K - 1 ≤ R) {n : ℕ} (hn : n ≤ K * R) :
    TopForm (fun g => g.length / R) K (runHist Alg (outSeq R (K - 1) cliqueSeq Alg) n) := by
  have hσ := resPos_blockPerm (D := K - 1) hR (outCol R (K - 1) cliqueSeq Alg)
  have hlt : ∀ i < n, i / R < K := fun i hi => (Nat.div_lt_iff_lt_mul hR).2 (by omega)
  have hdeg : ∀ w < K, postDeg cliqueSeq K w ≤ R := fun w _ =>
    (postDeg_cliqueSeq_le K w).trans hKR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [length_runHist] at hi
    rw [bidx_div hi.le]
    exact hlt i hi
  · intro i j hij hj
    rw [length_runHist] at hj
    rw [bidx_div (hij.trans hj.le), bidx_div hj.le]
    exact Nat.div_le_div_right hij
  · intro i j hi hj hb
    rw [length_runHist] at hi hj
    rw [bidx_div hi.le, bidx_div hj.le] at hb
    rw [nb_outSeq hi, nb_outSeq hj]
    unfold blowSeq
    rw [hb]
  · intro i hi u hu
    rw [length_runHist] at hi
    rw [nb_outSeq hi] at hu
    have hui := lt_of_mem_blowSeq cliqueSeq_valid hR hσ hu
    refine ⟨hui, ?_⟩
    rw [bidx_div (hui.trans hi).le, bidx_div hi.le]
    exact mem_range.1 ((mem_blowSeq hR hσ).1 hu).1
  · intro i j hi hj u hui huj
    rw [length_runHist] at hi hj
    rw [nb_outSeq hi] at hui
    rw [nb_outSeq hj] at huj
    rw [bidx_div hi.le, bidx_div hj.le]
    exact block_eq_of_mem cliqueSeq_valid hR hσ hdeg hui huj (hlt i hi) (hlt j hj)

/-- A history of at most `T ≤ K R` vertices of the blow-up of the clique `K_K` with blocks of `R`
vertices is a play of a partial-join level over `K_K` whose reserves are those of
Construction 6.1, provided that before the moment `T` every complete block has a colour on at
least `K - 1` of its vertices (`hpop`). -/
theorem pjForm_outSeq (hR : 0 < R) {T n : ℕ} (hn : n ≤ T) (hT : T ≤ K * R)
    (hpop : ∀ t < T, ∀ v < t / R,
      K - 1 ≤ (clsList R (blockCol (outCol R (K - 1) cliqueSeq Alg) R v)
        (popular R (K - 1) (blockCol (outCol R (K - 1) cliqueSeq Alg) R v))).length) :
    PJForm (fun g => g.length / R) (blowRes R (K - 1)) K
      (runHist Alg (outSeq R (K - 1) cliqueSeq Alg) n) := by
  have hσ := resPos_blockPerm (D := K - 1) hR (outCol R (K - 1) cliqueSeq Alg)
  have hlt : ∀ i < n, i / R < K := fun i hi => (Nat.div_lt_iff_lt_mul hR).2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [length_runHist] at hi
    rw [bidx_div hi.le]
    exact hlt i hi
  · intro i j hij hj
    rw [length_runHist] at hj
    rw [bidx_div (hij.trans hj.le), bidx_div hj.le]
    exact Nat.div_le_div_right hij
  · intro i hi u hu
    rw [length_runHist] at hi
    rw [nb_outSeq hi] at hu
    have hui := lt_of_mem_blowSeq cliqueSeq_valid hR hσ hu
    refine ⟨hui, ?_⟩
    rw [bidx_div (hui.trans hi).le, bidx_div hi.le]
    exact mem_range.1 ((mem_blowSeq hR hσ).1 hu).1
  · -- every vertex has a server in each earlier block
    intro j hj t ht
    rw [length_runHist] at hj
    rw [bidx_div hj.le] at ht
    have hu : t * R + resPos R (K - 1) (outCol R (K - 1) cliqueSeq Alg) t
        (rank cliqueSeq t (j / R)) < j := by
      have h1 := Nat.mul_le_mul_right R ht
      have h2 := Nat.div_mul_le_self j R
      have h3 := hσ.lt t (rank cliqueSeq t (j / R))
      rw [Nat.succ_mul] at h1
      omega
    refine ⟨t * R + resPos R (K - 1) (outCol R (K - 1) cliqueSeq Alg) t
      (rank cliqueSeq t (j / R)), ?_, ?_⟩
    · rw [nb_outSeq hj]
      simp only [blowSeq, cliqueSeq, mem_image, mem_range]
      exact ⟨t, ht, rfl⟩
    · rw [bidx_div (hu.trans hj).le]
      exact div_add_lt hR (hσ.lt _ _)
  · -- the servers lie in the reserves
    intro j hj u hu
    rw [length_runHist] at hj
    rw [nb_outSeq hj] at hu
    rw [runHist_take hj.le, mem_blowRes_outSeq hR]
    obtain ⟨hw, hue⟩ := (mem_blowSeq hR hσ).1 hu
    exact ⟨mem_range.1 hw, rank cliqueSeq (u / R) (j / R),
      (rank_lt_rank (hlt j hj) hw).trans_le (postDeg_cliqueSeq_le K (u / R)), hue⟩
  · -- the reserve of a block does not change once the block is complete
    intro j j' hjj' hj' u hu hb
    rw [length_runHist] at hj'
    have hj : j ≤ n := hjj'.trans hj'.le
    rw [bidx_div (hu.le.trans hj), bidx_div hj] at hb
    rw [runHist_take hj, runHist_take hj'.le, mem_blowRes_outSeq hR, mem_blowRes_outSeq hR]
    exact ⟨fun h => ⟨hb.trans_le (Nat.div_le_div_right hjj'), h.2⟩, fun h => ⟨hb, h.2⟩⟩
  · -- the reserve of a complete block is monochromatic
    intro j hj u hu w hw hur hwr hb hbj
    rw [length_runHist] at hj
    rw [runHist_take hj.le, mem_blowRes_outSeq hR] at hur hwr
    rw [bidx_div (hu.trans hj).le, bidx_div (hw.trans hj).le] at hb
    have key : ∀ x, x / R < j / R →
        (∃ r < K - 1,
          x = x / R * R + resPos R (K - 1) (outCol R (K - 1) cliqueSeq Alg) (x / R) r) →
        outCol R (K - 1) cliqueSeq Alg x =
          popular R (K - 1) (blockCol (outCol R (K - 1) cliqueSeq Alg) R (x / R)) := by
      rintro x hx ⟨r, hr, hxe⟩
      have := blockCol_resOrder (hpop j (lt_of_lt_of_le hj hn) (x / R) hx) hr
      conv_lhs => rw [hxe]
      exact this
    rw [colourAt_outSeq (hu.trans hj), colourAt_outSeq (hw.trans hj), key u hur.1 hur.2,
      key w hwr.1 hwr.2, hb]

/-! ### The adversary of Theorem 6.4 with one level -/

/-- The play of `Blow.tower K 1` against a proper algorithm follows the outer sequence of the
reservation blow-up of the clique and stops after `T ≤ K R` vertices; before `T`, every complete
block has a colour on at least `K - 1` of its vertices. -/
theorem towerOne_play (hK : 2 ≤ K) (hAlg : Alg.IsProper) :
    ∃ T ≤ K * Blow.R K (K - 1),
      Blow.Follows (Blow.tower K 1) Alg (outSeq (Blow.R K (K - 1)) (K - 1) cliqueSeq Alg) T ∧
      ∀ t < T, ∀ v < t / Blow.R K (K - 1),
        K - 1 ≤ (clsList (Blow.R K (K - 1))
          (blockCol (outCol (Blow.R K (K - 1)) (K - 1) cliqueSeq Alg) (Blow.R K (K - 1)) v)
          (popular (Blow.R K (K - 1)) (K - 1)
            (blockCol (outCol (Blow.R K (K - 1)) (K - 1) cliqueSeq Alg)
              (Blow.R K (K - 1)) v))).length := by
  have hD : 1 ≤ K - 1 := by omega
  have hfol₀ : Blow.Follows (Adversary.clique K) (Blow.induced Alg K (K - 1)) cliqueSeq K :=
    Adversary.clique_hist K _
  obtain ⟨T, hTle, hfol, -, -, hkey⟩ := Blow.sim hD hAlg cliqueSeq_valid
    (hfol₀.tracks cliqueSeq_valid) (fun w _ => postDeg_cliqueSeq_le K w)
    (card_image_runCol_cliqueSeq (inducedAlg_isProper Alg _ _) K).ge
  refine ⟨T, hTle, hfol, fun t ht v hv => ?_⟩
  have hcls := ((hkey t ht).2.2 v hv).2
  have hblk : ∀ s < Blow.R K (K - 1),
      blockCol (colourAt (runHist Alg (outSeq (Blow.R K (K - 1)) (K - 1) cliqueSeq Alg) t))
        (Blow.R K (K - 1)) v s =
      blockCol (outCol (Blow.R K (K - 1)) (K - 1) cliqueSeq Alg) (Blow.R K (K - 1)) v s := by
    intro s hs
    unfold blockCol
    apply colourAt_runHist
    have h1 := Nat.mul_le_mul_right (Blow.R K (K - 1)) hv
    have h2 := Nat.div_mul_le_self t (Blow.R K (K - 1))
    rw [Nat.succ_mul] at h1
    omega
  rwa [Blow.indColour, popular_congr hblk, clsList_congr hblk] at hcls

/-- **The class of Theorem D.4 is not vacuous.**  For `K ≥ 2`, the adversary of Theorem 6.4 with
one level, the reservation blow-up `B(K_K)` of the clique, presents `K_K` blown up once, with
blocks of `R = (K-1)(K-2)+1` vertices, and it forces `K` colours.  So it satisfies the hypotheses
of `top_block`. -/
theorem top_block_witness (hK : 2 ≤ K) :
    IsTopBlockAdv (fun h => h.length / Blow.R K (K - 1)) K (Blow.tower K 1) ∧
      (Blow.tower K 1).Forces K := by
  refine ⟨fun Alg hAlg p => ?_, (Blow.tower_stackOK hK 1).1⟩
  obtain ⟨T, hTle, hfol, -⟩ := towerOne_play hK hAlg
  rw [hfol p]
  exact topForm_outSeq (Blow.R_pos _ _) (Blow.le_R hK) ((min_le_right _ _).trans hTle)

/-- For `K ≥ 2`, the adversary of Theorem 6.4 with one level is a partial-join level over `K_K`:
the vertices of a block have the same earlier neighbours, one server in the reserve of each earlier
block (`ρ = blowRes R (K-1)`). -/
theorem towerOne_isPJAdv (hK : 2 ≤ K) :
    IsPJAdv (fun h => h.length / Blow.R K (K - 1)) (blowRes (Blow.R K (K - 1)) (K - 1)) K
      (Blow.tower K 1) := by
  intro Alg hAlg p
  obtain ⟨T, hTle, hfol, hpop⟩ := towerOne_play hK hAlg
  rw [hfol p]
  exact pjForm_outSeq (Blow.R_pos _ _) (min_le_right _ _) hTle hpop

/-- **The class of Theorem D.5 is not vacuous.**  For `2 ≤ m ≤ 7`, the adversary of Theorem 6.4
with one level over `K_m` is a partial-join level over `K_m`, forces `m` colours, presents only
`3`-colourable graphs (`|P_1(3)| = 7`), and its plays have at most `playSize m 1` vertices.  So
it satisfies the hypotheses of `partial_joins` with `N = playSize m 1` (for these `m` the
inequality of `partial_joins` already follows from `N ≥ m`). -/
theorem partial_joins_witness {m : ℕ} (hm : 2 ≤ m) (hm7 : m ≤ 7) :
    IsPJAdv (fun h => h.length / Blow.R m (m - 1)) (blowRes (Blow.R m (m - 1)) (m - 1)) m
        (Blow.tower m 1) ∧
      (Blow.tower m 1).Forces m ∧ (Blow.tower m 1).LandsIn (fun _ G => G.Colorable 3) ∧
      (Blow.tower m 1).SizeLE (playSize m 1) := by
  have h7 : m ≤ Fintype.card (LabelPoset 3 1) := by
    rw [card_labelPoset_one]
    simpa using hm7
  obtain ⟨hF, -, -, hcol⟩ := Blow.theorem_6_4 hm h7
  exact ⟨towerOne_isPJAdv hm, hF, hcol, Blow.tower_sizeLE hm 1⟩

end OnlineColouring.AppBD
