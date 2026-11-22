module

public import OnlineColouring.StrRefBlocks
public import OnlineColouring.StrBlow

/-!
# Appendix B: a reservation blow-up with block and reserve sizes that depend on the node

Appendix B: *Let `𝒜'` be the adversary of Theorem 6.4 in which every block of a
node of level `ℓ` below `v_t` has `b_ℓ(t)` nodes and every reserve of such a node has size
`D_ℓ(t)`.*  This file treats one level of such an adversary.

## The construction

`Str.GB K bs ds A : Adversary` is Construction 6.1 for the inner adversary `A` in which the block
of the inner vertex `v` has `bs v` vertices and its reserve has `ds v` vertices (the layout of the
blocks is that of `StrRefBlocks.lean`).  Everything else is as in `Blow.B`: it stops as soon as
the algorithm has used `K` colours, and when `A` stops; `col(v)` is the first colour that occurs on
at least `ds v` vertices of the block of `v` (`popular`); `Res(v)` consists of the first `ds v`
vertices of that colour; reserves give up their vertices in arrival order.  For blocks of constant
size `(K-1)(D-1)+1` and reserves of constant size `D` it *is* `Blow.B K D` (`GB_const`).

## The forcing lemma

Lemma 6.2 does not apply to `𝒜'`: the block of a node below `v_t` is too small for the pigeonhole
over all `K - 1` colours.  The paper's argument is that the nodes of such a block see `t - 1`
distinct colours on their earlier neighbours, so only `K - t` colours are available to them.
`Str.gsim` is this argument for one level.  Let `ty v` be a number of distinct colours that the
inner vertex `v` is guaranteed to see on its earlier neighbours (`hrich`; for the clique, `v_t`
sees `t - 1` colours).  If the inner play against the induced algorithm follows `H` and stops
after `q₀` vertices with `K` colours in use, if the inner vertex `w` has post-degree at most `ds w`,
and if `bs v ≥ (K - 1 - ty v)(ds v - 1) + 1`, then the play of `GB K bs ds A` against a proper
algorithm follows the blow-up `gOutSeq bs ds H Alg` of `H` up to the first moment `T` at which `K`
colours are in use; and every vertex presented in the block of `v` again sees at least `ty v`
distinct colours on its earlier neighbours (they are servers with the induced colours of the
earlier neighbours of `v`), which is the hypothesis `hrich` for the next level.

The proof follows `Blow.sim` and Lemma 6.2: `faithful_of_lt` is "step 3 is possible" (by induction
along the play, with the pigeonhole over the `K - 1 - ty v` available colours),
`runCol_gInducedAlg_eq` is "the induced colouring is proper", and the induced algorithm
`gInduced Alg bs ds` is proper on every history by patching, as in `Blow.induced`.
-/

@[expose] public section

namespace OnlineColouring.Str

open Finset
open Blow (Follows Tracks clean)

/-! ### Reserves in blocks of variable size -/

/-- The colouring `col` restricted to the block of `w` (positions `0, …, bs w - 1`). -/
def gBlockCol (bs : ℕ → ℕ) (col : ℕ → ℕ) (w t : ℕ) : ℕ := col (off bs w + t)

/-- The position, in the block of `w`, of the `r`-th server taken from that block: the vertices of
the induced colour come first (the first `ds w` of them form the reserve), in arrival order. -/
def gResPos (bs ds : ℕ → ℕ) (col : ℕ → ℕ) (w r : ℕ) : ℕ :=
  (resOrder (bs w) (ds w) (gBlockCol bs col w)).getD r 0

/-- If the induced colour of a nonempty block occurs on at least `D` of its vertices, it is the
colour of one of its vertices (also for `D = 0`, where it is the colour of the first vertex). -/
theorem popular_mem_block {R D : ℕ} {bc : ℕ → ℕ} (hR : 0 < R)
    (h : D ≤ (clsList R bc (popular R D bc)).length) : ∃ t < R, bc t = popular R D bc := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine ⟨0, hR, ?_⟩
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    unfold popular
    rw [List.range_succ_eq_map, List.map_cons, List.find?_cons_of_pos (by simp)]
    rfl
  · exact popular_mem hD h

section Reserve

variable {bs ds : ℕ → ℕ}

theorem gResPos_gPerm (hbs : ∀ v, 0 < bs v) (col : ℕ → ℕ) : GPerm bs (gResPos bs ds col) where
  lt w t := by
    unfold gResPos
    rw [List.getD_eq_getElem?_getD]
    cases h : (resOrder (bs w) (ds w) (gBlockCol bs col w))[t]? with
    | none => simpa using hbs w
    | some a => simpa using mem_resOrder.1 (List.mem_of_getElem? h)
  inj w t t' ht ht' heq := by
    unfold gResPos at heq
    have hl := length_resOrder (R := bs w) (D := ds w) (gBlockCol bs col w)
    rw [List.getD_of_lt _ (by rw [hl]; exact ht), List.getD_of_lt _ (by rw [hl]; exact ht')] at heq
    exact ((resOrder_nodup _).getElem_inj_iff).1 heq

theorem gResPos_congr {col col' : ℕ → ℕ} {w : ℕ}
    (h : ∀ t < bs w, col (off bs w + t) = col' (off bs w + t)) :
    gResPos bs ds col w = gResPos bs ds col' w := by
  funext r
  unfold gResPos
  rw [resOrder_congr (bc := gBlockCol bs col w) (bc' := gBlockCol bs col' w) h]

end Reserve

/-! ### The outer adversary in structure mode -/

/-- The reservation adversary with block sizes `bs` and reserve sizes `ds`, in structure mode, for
a given inner input sequence `H`. -/
def gResAdv (bs ds : ℕ → ℕ) (H : ℕ → Finset ℕ) (h : History) : Finset ℕ :=
  gBlowSeq bs H (gResPos bs ds (colourAt h)) h.length

/-- The outer input presented to `X`. -/
def gOutSeq (bs ds : ℕ → ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) : ℕ → Finset ℕ :=
  playSeq (gResAdv bs ds H) X

/-- The colours that `X` gives to the outer vertices. -/
def gOutCol (bs ds : ℕ → ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) : ℕ → ℕ :=
  runCol X (gOutSeq bs ds H X)

/-- The induced colour of the inner vertex `v`. -/
def gIndCol (bs ds : ℕ → ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) (v : ℕ) : ℕ :=
  popular (bs v) (ds v) (gBlockCol bs (gOutCol bs ds H X) v)

/-- Step 3 is possible for the block of `v`: its induced colour occurs on at least `ds v` of its
vertices. -/
def Faithful (bs ds : ℕ → ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) (v : ℕ) : Prop :=
  ds v ≤ (clsList (bs v) (gBlockCol bs (gOutCol bs ds H X) v) (gIndCol bs ds H X v)).length

/-- The colour that the induced algorithm computes for the new inner vertex. -/
def gSimCol (X : OnlineAlg) (bs ds : ℕ → ℕ) (h : History) (s : Finset ℕ) : ℕ :=
  popular (bs h.length) (ds h.length)
    (gBlockCol bs (colourAt (play (gResAdv bs ds (innerSeq h s)) X (off bs (h.length + 1))))
      h.length)

/-- The induced algorithm on clean histories (a fresh colour if the simulated colour clashes). -/
def gInducedAlg (X : OnlineAlg) (bs ds : ℕ → ℕ) : OnlineAlg :=
  ⟨fun h s =>
    if gSimCol X bs ds h s ∈ nbrColours h s then OnlineAlg.fresh h s else gSimCol X bs ds h s⟩

/-- The induced algorithm `Alg'` of one level of `𝒜'`. -/
def gInduced (X : OnlineAlg) (bs ds : ℕ → ℕ) : OnlineAlg :=
  ⟨fun g s => (gInducedAlg X bs ds).step (clean g) (s ∩ range g.length)⟩

section Outer

variable {bs ds : ℕ → ℕ} {H : ℕ → Finset ℕ} {X : OnlineAlg}

theorem gInducedAlg_isProper (X : OnlineAlg) (bs ds : ℕ → ℕ) : (gInducedAlg X bs ds).IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro h s
  change (if gSimCol X bs ds h s ∈ nbrColours h s then OnlineAlg.fresh h s
    else gSimCol X bs ds h s) ∉ _
  split_ifs with hc
  · exact OnlineAlg.fresh_notMem h s
  · exact hc

/-- `Alg'` is proper on every history. -/
theorem gInduced_isProper (X : OnlineAlg) (bs ds : ℕ → ℕ) : (gInduced X bs ds).IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro g s
  have := (OnlineAlg.isProper_iff _).1 (gInducedAlg_isProper X bs ds) (clean g)
    (s ∩ range g.length)
  rw [Blow.nbrColours_clean] at this
  exact this

theorem runHist_gInduced {N : ℕ → Finset ℕ} (hN : ValidSeq N) (t : ℕ) :
    runHist (gInduced X bs ds) N t = runHist (gInducedAlg X bs ds) N t := by
  induction t with
  | zero => rw [runHist, runHist]
  | succ t ih =>
    rw [runHist_succ, runHist_succ, runCol, runCol]
    change _ ++ [(N t, (gInducedAlg X bs ds).step (clean (runHist (gInduced X bs ds) N t))
      (N t ∩ range (runHist (gInduced X bs ds) N t).length))] = _
    rw [Blow.clean_runHist hN, length_runHist, inter_eq_left.2 (hN t), ih]

theorem runCol_gInduced {N : ℕ → Finset ℕ} (hN : ValidSeq N) (t : ℕ) :
    runCol (gInduced X bs ds) N t = runCol (gInducedAlg X bs ds) N t := by
  have := runHist_gInduced (X := X) (bs := bs) (ds := ds) hN (t + 1)
  rw [runHist_succ, runHist_succ, runHist_gInduced hN] at this
  simpa using List.append_cancel_left this

/-- The outer input is the static blow-up of `H` with the server positions chosen from the colours
of `X`. -/
theorem gOutSeq_eq (hH : ValidSeq H) :
    gOutSeq bs ds H X = gBlowSeq bs H (gResPos bs ds (gOutCol bs ds H X)) := by
  funext p
  change gResAdv bs ds H (play (gResAdv bs ds H) X p) = _
  unfold gResAdv
  rw [length_play]
  apply gBlowSeq_congr_σ
  intro w hw
  apply gResPos_congr
  intro t ht
  apply colourAt_play
  have h₁ : w < blk bs p := mem_range.1 (hH _ hw)
  have h₂ := off_mono bs (Nat.succ_le_of_lt h₁)
  rw [off_succ] at h₂
  have h₃ := off_blk_le bs p
  omega

theorem gOutSeq_valid (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) : ValidSeq (gOutSeq bs ds H X) := by
  rw [gOutSeq_eq hH]
  exact gBlowSeq_valid hH hbs (gResPos_gPerm hbs _)

theorem gResAdv_congr {H' : ℕ → Finset ℕ} {V : ℕ} (hHH : ∀ i ≤ V, H i = H' i) {hist : History}
    (hl : blk bs hist.length ≤ V) : gResAdv bs ds H hist = gResAdv bs ds H' hist := by
  unfold gResAdv gBlowSeq
  rw [hHH _ hl]
  have hr : ∀ w, rank H w (blk bs hist.length) = rank H' w (blk bs hist.length) :=
    fun w => rank_congr fun i hi => hHH i (by omega)
  simp only [hr]

theorem play_gResAdv_congr (hbs : ∀ v, 0 < bs v) {H' : ℕ → Finset ℕ} {V : ℕ}
    (hHH : ∀ i ≤ V, H i = H' i) :
    play (gResAdv bs ds H) X (off bs (V + 1)) = play (gResAdv bs ds H') X (off bs (V + 1)) :=
  play_congr (fun _ hl => gResAdv_congr hHH (Nat.lt_succ_iff.1 ((blk_lt_iff hbs).2 hl))) _ le_rfl

/-- **The induced colouring is online.** -/
theorem gSimCol_runHist (hbs : ∀ v, 0 < bs v) (A' : OnlineAlg) (v : ℕ) :
    gSimCol X bs ds (runHist A' H v) (H v) = gIndCol bs ds H X v := by
  unfold gSimCol gIndCol
  rw [length_runHist, play_gResAdv_congr hbs (innerSeq_runHist A' H v)]
  apply popular_congr
  intro t ht
  unfold gBlockCol gOutCol gOutSeq
  apply colourAt_play
  rw [off_succ]
  omega

theorem runCol_gInducedAlg (hbs : ∀ v, 0 < bs v) (v : ℕ) :
    runCol (gInducedAlg X bs ds) H v =
      if gIndCol bs ds H X v ∈ nbrColours (runHist (gInducedAlg X bs ds) H v) (H v) then
        OnlineAlg.fresh (runHist (gInducedAlg X bs ds) H v) (H v) else gIndCol bs ds H X v := by
  change (if gSimCol X bs ds _ _ ∈ _ then _ else gSimCol X bs ds _ _) = _
  rw [gSimCol_runHist hbs]

/-- The server of the arc `w → v` is an earlier neighbour of every vertex of the block of `v`. -/
theorem gserver_mem_outSeq (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) {w v t : ℕ} (hw : w ∈ H v)
    (ht : t < bs v) :
    off bs w + gResPos bs ds (gOutCol bs ds H X) w (rank H w v) ∈
      gOutSeq bs ds H X (off bs v + t) := by
  have hσ : GPerm bs (gResPos bs ds (gOutCol bs ds H X)) := gResPos_gPerm hbs _
  rw [gOutSeq_eq hH, mem_gBlowSeq hbs hσ, blk_off_add hbs ht, blk_off_add hbs (hσ.lt _ _)]
  exact ⟨hw, rfl⟩

/-- All vertices of a block have the same earlier neighbours. -/
theorem gOutSeq_off_add (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) {v t : ℕ} (ht : t < bs v) :
    gOutSeq bs ds H X (off bs v + t) = gOutSeq bs ds H X (off bs v) := by
  rw [gOutSeq_eq hH]
  unfold gBlowSeq
  rw [blk_off_add hbs ht, blk_off hbs]

/-- If step 3 was possible for the block of `w`, the servers taken from it have the induced colour
of `w` (the post-degree of `w` is at most `ds w`, so they come from the reserve). -/
theorem gOutCol_server {m : ℕ} (hdeg : ∀ w < m, postDeg H m w ≤ ds w) (hH : ValidSeq H)
    {w v : ℕ} (hv : v < m) (hw : w ∈ H v) (hfw : Faithful bs ds H X w) :
    gOutCol bs ds H X (off bs w + gResPos bs ds (gOutCol bs ds H X) w (rank H w v)) =
      gIndCol bs ds H X w :=
  blockCol_resOrder hfw
    ((rank_lt_rank hv hw).trans_le (hdeg w ((mem_range.1 (hH v hw)).trans hv)))

/-- **The induced colouring is proper.**  If step 3 was possible for the first `V` blocks, the
induced algorithm gives each of the first `V` inner vertices its induced colour (no fallback is
used). -/
theorem runCol_gInducedAlg_eq (hX : X.IsProper) (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v)
    {m V : ℕ} (hdeg : ∀ w < m, postDeg H m w ≤ ds w) (hVm : V ≤ m)
    (hfaith : ∀ v < V, Faithful bs ds H X v) :
    ∀ v < V, runCol (gInducedAlg X bs ds) H v = gIndCol bs ds H X v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv
  rw [runCol_gInducedAlg hbs]
  split_ifs with hmem
  swap
  · rfl
  exfalso
  rw [nbrColours_runHist (hH v)] at hmem
  obtain ⟨w, hw, hwc⟩ := Finset.mem_image.1 hmem
  have hwv : w < v := mem_range.1 (hH v hw)
  rw [ih w hwv (hwv.trans hv)] at hwc
  obtain ⟨t, ht, htc⟩ := popular_mem_block (hbs v) (hfaith v hv)
  have hmemG := gserver_mem_outSeq (ds := ds) (X := X) hH hbs hw ht
  have hne := runCol_ne hX hmemG (mem_range.1 (gOutSeq_valid hH hbs _ hmemG))
  have hserv := gOutCol_server hdeg hH (lt_of_lt_of_le hv hVm) hw (hfaith w (hwv.trans hv))
  apply hne
  change gOutCol bs ds H X (off bs v + t) = gOutCol bs ds H X _
  rw [hserv, hwc]
  exact htc

/-- The colours that `v` sees on its earlier neighbours are seen by every vertex of the block of
`v` on its earlier neighbours: these are the servers, and they have the induced colours. -/
theorem image_subset_outSeq (hH : ValidSeq H) (hbs : ∀ v, 0 < bs v) {m : ℕ}
    (hdeg : ∀ w < m, postDeg H m w ≤ ds w) {v : ℕ} (hv : v < m)
    (hfaith : ∀ w < v, Faithful bs ds H X w)
    (heq : ∀ w < v, runCol (gInducedAlg X bs ds) H w = gIndCol bs ds H X w) {r : ℕ}
    (hr : r < bs v) :
    (H v).image (runCol (gInducedAlg X bs ds) H) ⊆
      (gOutSeq bs ds H X (off bs v + r)).image (gOutCol bs ds H X) := by
  intro c hc
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
  have hwv : w < v := mem_range.1 (hH v hw)
  rw [heq w hwv]
  exact mem_image.2 ⟨_, gserver_mem_outSeq hH hbs hw hr,
    gOutCol_server hdeg hH hv hw (hfaith w hwv)⟩

/-- **Step 3 is possible** (the pigeonhole of Appendix B).  Suppose that every inner vertex `v`
sees at least `ty v` distinct colours on its earlier neighbours, has post-degree at most `ds v`,
and that its block has at least `(K - 1 - ty v)(ds v - 1) + 1` vertices.  If `X` has used fewer
than `K` colours on the first `t` outer vertices, then every block that is complete at that
moment has a colour on at least `ds v` of its vertices. -/
theorem faithful_of_lt {K : ℕ} {ty : ℕ → ℕ} (hX : X.IsProper) (hH : ValidSeq H)
    (hbs : ∀ v, 0 < bs v) {q₀ : ℕ} (hdeg : ∀ w < q₀, postDeg H q₀ w ≤ ds w)
    (hrich : ∀ v < q₀, ty v ≤ ((H v).image (runCol (gInducedAlg X bs ds) H)).card)
    (hsize : ∀ v < q₀, (K - 1 - ty v) * (ds v - 1) + 1 ≤ bs v) {t : ℕ}
    (ht : ((range t).image (gOutCol bs ds H X)).card < K) :
    ∀ v < q₀, off bs (v + 1) ≤ t → Faithful bs ds H X v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv hvt
  have hprev : ∀ w < v, Faithful bs ds H X w := fun w hw =>
    ih w hw (hw.trans hv) ((off_mono bs (Nat.succ_le_succ hw.le)).trans hvt)
  have heq := runCol_gInducedAlg_eq hX hH hbs hdeg hv.le hprev
  have hvt' := hvt
  rw [off_succ] at hvt'
  -- the colours on the common earlier neighbours of the block
  have hNcard : ty v ≤ ((gOutSeq bs ds H X (off bs v)).image (gOutCol bs ds H X)).card := by
    refine (hrich v hv).trans (card_le_card ?_)
    have := image_subset_outSeq hH hbs hdeg hv hprev heq (hbs v)
    rwa [Nat.add_zero] at this
  -- the colours of the block avoid them
  have hdisj : Disjoint ((range (bs v)).image (gBlockCol bs (gOutCol bs ds H X) v))
      ((gOutSeq bs ds H X (off bs v)).image (gOutCol bs ds H X)) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hc
    obtain ⟨x, hx, hxc⟩ := mem_image.1 hc'
    rw [mem_range] at hr
    rw [← gOutSeq_off_add hH hbs hr] at hx
    exact runCol_ne hX hx (mem_range.1 (gOutSeq_valid hH hbs _ hx)) hxc.symm
  have hsub : (range (bs v)).image (gBlockCol bs (gOutCol bs ds H X) v) ∪
      (gOutSeq bs ds H X (off bs v)).image (gOutCol bs ds H X) ⊆
      (range t).image (gOutCol bs ds H X) := by
    intro c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨r, hr, rfl⟩ := mem_image.1 hc
      rw [mem_range] at hr
      exact mem_image.2 ⟨off bs v + r, mem_range.2 (by omega), rfl⟩
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      have := mem_range.1 (gOutSeq_valid hH hbs _ hx)
      exact mem_image.2 ⟨x, mem_range.2 (by omega), rfl⟩
  have hcard := (card_le_card hsub).trans_lt ht
  rw [card_union_of_disjoint hdisj] at hcard
  -- pigeonhole over the remaining `K - 1 - ty v` colours
  rcases Nat.eq_zero_or_pos (ds v) with h0 | hD
  · unfold Faithful
    rw [h0]
    exact Nat.zero_le _
  · have hs : (K - ty v - 1) * (ds v - 1) + 1 ≤ (range (bs v)).card := by
      rw [card_range, Nat.sub_right_comm]
      exact hsize v hv
    obtain ⟨b, -, hb⟩ := exists_large_colour_class (range (bs v))
      (gBlockCol bs (gOutCol bs ds H X) v) hs (by omega)
    exact popular_spec hD ⟨b, by rw [length_clsList]; exact hb⟩

end Outer

/-! ### The adversary -/

/-- The induced colour `col(v)` of the inner vertex `v`, read off from the outer history `h`. -/
def gIndColour (bs ds : ℕ → ℕ) (h : History) (v : ℕ) : ℕ :=
  popular (bs v) (ds v) (gBlockCol bs (colourAt h) v)

/-- The "algorithm" by which `GB` answers the inner adversary. -/
def gOracle (bs ds : ℕ → ℕ) (h : History) : OnlineAlg :=
  ⟨fun g _ => gIndColour bs ds h g.length⟩

/-- The inner play simulated by `GB` at the outer history `h`: one round per complete block. -/
def gInnerHist (bs ds : ℕ → ℕ) (A : Adversary) (h : History) : History :=
  A.hist (gOracle bs ds h) (blk bs h.length)

/-- **Construction 6.1 with block sizes `bs` and reserve sizes `ds`**: the reservation blow-up of
the inner adversary `A` in which the block of the inner vertex `v` has `bs v` vertices and its
reserve has `ds v` vertices.  See the module docstring. -/
def GB (K : ℕ) (bs ds : ℕ → ℕ) (A : Adversary) : Adversary :=
  ⟨fun h =>
    if K ≤ (usedColours h).card then none
    else (A.move (gInnerHist bs ds A h)).map fun s =>
      gResAdv bs ds
        (innerSeq (clean (gInnerHist bs ds A h)) (s ∩ range (gInnerHist bs ds A h).length)) h⟩

section Sim

variable {K : ℕ} {bs ds : ℕ → ℕ} {A : Adversary} {A' ind Alg : OnlineAlg} {H : ℕ → Finset ℕ}
  {q₀ : ℕ}

/-- A play against the induced algorithm that follows a valid sequence tracks it. -/
theorem follows_tracks (hH : ValidSeq H) (hF : Follows A (gInduced Alg bs ds) H q₀) :
    Tracks A (gInduced Alg bs ds) (gInducedAlg Alg bs ds) H q₀ := by
  intro q
  rw [hF q, Blow.clean_runHist hH, runHist_gInduced hH]

theorem tracks_hist_gOracle (hT : Tracks A A' ind H q₀) {h : History} {m : ℕ} (hm : m ≤ q₀)
    (hcol : ∀ i < m, gIndColour bs ds h i = runCol ind H i) :
    ∀ i ≤ m, A.hist (gOracle bs ds h) i = A.hist A' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have ih' := ih (Nat.le_of_succ_le hi)
    obtain ⟨s, hs, -, hstep⟩ := hT.move_lt (lt_of_lt_of_le hi hm)
    rw [Blow.hist_succ_some (by rw [ih']; exact hs), Blow.hist_succ_some hs, ih']
    congr 3
    change gIndColour bs ds h (A.hist A' i).length = _
    rw [hT.length i, min_eq_left (by omega), hcol i hi, hstep]

theorem tracks_move_GB (hT : Tracks A A' ind H q₀) {h : History}
    (hm : blk bs h.length < q₀) (hK : (usedColours h).card < K)
    (hcol : ∀ i < blk bs h.length, gIndColour bs ds h i = runCol ind H i) :
    (GB K bs ds A).move h = some (gResAdv bs ds H h) := by
  have hin : gInnerHist bs ds A h = A.hist A' (blk bs h.length) :=
    tracks_hist_gOracle hT hm.le hcol _ le_rfl
  obtain ⟨s, hs, hsH, -⟩ := hT.move_lt hm
  change (if K ≤ (usedColours h).card then none else _) = _
  rw [ite_eq_right (not_le.2 hK), hin, hs, Option.map_some]
  congr 1
  apply gResAdv_congr (V := blk bs h.length) _ le_rfl
  intro i hi
  rw [hT, hT.length, min_eq_left hm.le, hsH]
  exact innerSeq_runHist ind H _ i hi

/-- **The forcing lemma for one level of `𝒜'`.**  See the module docstring.  Suppose the play of
the inner adversary `A` against `A'` tracks the valid input sequence `H` (as run by the induced
algorithm) and stops after `q₀` vertices with `K` colours in use; the inner vertex `w` has
post-degree at most `ds w`; every inner vertex `v` sees at least `ty v` distinct colours on its
earlier neighbours; and `bs v ≥ (K - 1 - ty v)(ds v - 1) + 1`.  Then the play of `GB K bs ds A`
against the proper algorithm `Alg` follows the blow-up `gOutSeq bs ds H Alg` up to the first
moment `T ≤ off bs q₀` at which `Alg` has used `K` colours.  At every earlier moment `t`, the
vertex presented lies in the block of an inner vertex `v = blk bs t < q₀`, the inner play
simulated by `GB` is the play of `A` against `A'`, step 3 was possible for all complete blocks,
every earlier neighbour of the vertex is a server and has the induced colour of its node (the
colour that the induced algorithm gives that node), and the vertex sees at least `ty v` distinct
colours on its earlier neighbours. -/
theorem gsim {ty : ℕ → ℕ} (hbs : ∀ v, 0 < bs v) (hAlg : Alg.IsProper) (hH : ValidSeq H)
    (hT : Tracks A A' (gInducedAlg Alg bs ds) H q₀)
    (hdeg : ∀ w < q₀, postDeg H q₀ w ≤ ds w)
    (hrich : ∀ v < q₀, ty v ≤ ((H v).image (runCol (gInducedAlg Alg bs ds) H)).card)
    (hsize : ∀ v < q₀, (K - 1 - ty v) * (ds v - 1) + 1 ≤ bs v)
    (hforce : K ≤ ((range q₀).image (runCol (gInducedAlg Alg bs ds) H)).card) :
    ∃ T ≤ off bs q₀, Follows (GB K bs ds A) Alg (gOutSeq bs ds H Alg) T ∧
      K ≤ ((range T).image (gOutCol bs ds H Alg)).card ∧
      (∀ t < T, ((range t).image (gOutCol bs ds H Alg)).card < K) ∧
      ∀ t < T, blk bs t < q₀ ∧
        gInnerHist bs ds A (runHist Alg (gOutSeq bs ds H Alg) t) = A.hist A' (blk bs t) ∧
        (∀ v < blk bs t, Faithful bs ds H Alg v) ∧
        (∀ x ∈ gOutSeq bs ds H Alg t,
          gOutCol bs ds H Alg x = runCol (gInducedAlg Alg bs ds) H (blk bs x)) ∧
        ty (blk bs t) ≤ ((gOutSeq bs ds H Alg t).image (gOutCol bs ds H Alg)).card := by
  classical
  have hused : ∀ t, usedColours (runHist Alg (gOutSeq bs ds H Alg) t) =
      (range t).image (gOutCol bs ds H Alg) := fun t => usedColours_runHist Alg _ t
  -- `K` colours are in use when all blocks are complete
  have hS1 : K ≤ ((range (off bs q₀)).image (gOutCol bs ds H Alg)).card := by
    by_contra hlt
    rw [not_le] at hlt
    have hfaith : ∀ v < q₀, Faithful bs ds H Alg v := fun v hv =>
      faithful_of_lt hAlg hH hbs hdeg hrich hsize hlt v hv (off_mono bs (Nat.succ_le_of_lt hv))
    have heq := runCol_gInducedAlg_eq hAlg hH hbs hdeg le_rfl hfaith
    have hsub : (range q₀).image (runCol (gInducedAlg Alg bs ds) H) ⊆
        (range (off bs q₀)).image (gOutCol bs ds H Alg) := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
      rw [mem_range] at hv
      rw [heq v hv]
      obtain ⟨r, hr, hrc⟩ := popular_mem_block (hbs v) (hfaith v hv)
      have := off_mono bs (Nat.succ_le_of_lt hv)
      rw [off_succ] at this
      exact mem_image.2 ⟨off bs v + r, mem_range.2 (by omega), hrc⟩
    exact absurd (hforce.trans (card_le_card hsub)) (not_le.2 hlt)
  have hex : ∃ t, K ≤ ((range t).image (gOutCol bs ds H Alg)).card := ⟨_, hS1⟩
  have hTle := Nat.find_min' hex hS1
  have hTK := Nat.find_spec hex
  have hlt : ∀ t < Nat.find hex, ((range t).image (gOutCol bs ds H Alg)).card < K :=
    fun t ht => not_le.1 (Nat.find_min hex ht)
  generalize Nat.find hex = T at hTle hTK hlt
  -- before `T`, step 3 was possible for all complete blocks
  have key : ∀ t < T, blk bs t < q₀ ∧ (∀ v < blk bs t, Faithful bs ds H Alg v) ∧
      ∀ v < blk bs t, runCol (gInducedAlg Alg bs ds) H v = gIndCol bs ds H Alg v := by
    intro t ht
    have hm : blk bs t < q₀ := (blk_lt_iff hbs).2 (lt_of_lt_of_le ht hTle)
    have hfaith : ∀ v < blk bs t, Faithful bs ds H Alg v := fun v hv =>
      faithful_of_lt hAlg hH hbs hdeg hrich hsize (hlt t ht) v (hv.trans hm)
        ((off_mono bs (Nat.succ_le_of_lt hv)).trans (off_blk_le bs t))
    exact ⟨hm, hfaith, runCol_gInducedAlg_eq hAlg hH hbs hdeg hm.le hfaith⟩
  have hcolour : ∀ t < T, ∀ i < blk bs t,
      gIndColour bs ds (runHist Alg (gOutSeq bs ds H Alg) t) i =
        runCol (gInducedAlg Alg bs ds) H i := by
    intro t ht i hi
    rw [(key t ht).2.2 i hi]
    apply popular_congr
    intro r hr
    have := (off_mono bs (Nat.succ_le_of_lt hi)).trans (off_blk_le bs t)
    rw [off_succ] at this
    exact colourAt_runHist (by omega)
  have hmove : ∀ t < T, (GB K bs ds A).move (runHist Alg (gOutSeq bs ds H Alg) t) =
      some (gOutSeq bs ds H Alg t) := by
    intro t ht
    rw [tracks_move_GB hT (by rw [length_runHist]; exact (key t ht).1)
      (by rw [hused]; exact hlt t ht) (by rw [length_runHist]; exact hcolour t ht)]
    congr 1
    change gResAdv bs ds H (runHist Alg (playSeq (gResAdv bs ds H) Alg) t) =
      playSeq (gResAdv bs ds H) Alg t
    rw [runHist_playSeq]
    rfl
  have hstop : (GB K bs ds A).move (runHist Alg (gOutSeq bs ds H Alg) T) = none := by
    change (if K ≤ (usedColours (runHist Alg (gOutSeq bs ds H Alg) T)).card then none
      else _) = none
    rw [hused]
    exact ite_eq_left hTK
  refine ⟨T, hTle, follows_of_moves hmove hstop, hTK, hlt, fun t ht => ?_⟩
  obtain ⟨hm, hfaith, heq⟩ := key t ht
  refine ⟨hm, ?_, hfaith, ?_, (hrich _ hm).trans (card_le_card ?_)⟩
  · have := tracks_hist_gOracle hT hm.le (hcolour t ht) _ le_rfl
    unfold gInnerHist
    rw [length_runHist]
    exact this
  · intro x hx
    rw [gOutSeq_eq hH] at hx
    obtain ⟨hw, hxeq⟩ := (mem_gBlowSeq hbs (gResPos_gPerm hbs _)).1 hx
    have hwv : blk bs x < blk bs t := mem_range.1 (hH _ hw)
    have h1 := gOutCol_server hdeg hH hm hw (hfaith _ hwv)
    rw [← hxeq] at h1
    rw [heq _ hwv]
    exact h1
  · have h1 := image_subset_outSeq hH hbs hdeg hm hfaith heq (sub_off_blk_lt hbs t)
    rwa [Nat.add_sub_cancel' (off_blk_le bs t)] at h1

end Sim

/-! ### Constant sizes: Construction 6.1 -/

/-- With blocks of constant size `R = (K-1)(D-1)+1` and reserves of constant size `D`, the
construction is `B(𝒜)` of Construction 6.1. -/
theorem GB_const (K D : ℕ) (A : Adversary) :
    GB K (fun _ => Blow.R K D) (fun _ => D) A = Blow.B K D A := by
  have hR : 0 < Blow.R K D := Blow.R_pos K D
  have hbc : ∀ col : ℕ → ℕ, gBlockCol (fun _ => Blow.R K D) col = fun w => blockCol col
      (Blow.R K D) w := by
    intro col
    funext w t
    unfold gBlockCol blockCol
    rw [off_const]
  have hor : ∀ h : History, gOracle (fun _ => Blow.R K D) (fun _ => D) h = Blow.oracle K D h := by
    intro h
    unfold gOracle Blow.oracle gIndColour Blow.indColour
    rw [hbc]
  have hin : ∀ h : History,
      gInnerHist (fun _ => Blow.R K D) (fun _ => D) A h = Blow.innerHist K D A h := by
    intro h
    unfold gInnerHist Blow.innerHist
    rw [hor, blk_const hR]
  have hres : ∀ (N : ℕ → Finset ℕ) (h : History),
      gResAdv (fun _ => Blow.R K D) (fun _ => D) N h = resAdv (Blow.R K D) D N h := by
    intro N h
    unfold gResAdv resAdv
    rw [gBlowSeq_const hR]
    congr 1
    funext w r
    unfold gResPos resPos
    rw [hbc]
  unfold GB Blow.B
  congr 1
  funext h
  rw [hin]
  simp only [hres]

end OnlineColouring.Str
