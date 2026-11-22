module

public import OnlineColouring.SeqBlowUp
public import OnlineColouring.Play
public import OnlineColouring.Reservation

/-!
# One reservation blow-up against a fixed algorithm, and the induced algorithm

Construction 6.1 (reservation blow-up `B(𝒜)`) and Lemma 6.2 (forcing survives a blow-up), played
against one fixed algorithm and without the stop rule, so that every block is completed, as in
Section 7.  Other modules refer to this form as *structure mode*.  The adversary `B(𝒜)` of the
paper, with its stop rule and as an object of type `Adversary`, is `Blow.B` (`Blow.lean`), and
Lemma 6.2 for it is `Blow.lemma_6_2`; one level of the adversary `𝒜^str` of Section 7 is
`Str.Bstr` (`StrBlow.lean`).  Fix the block size `R`, the reserve size `D` and an inner input
sequence `H` whose first `m` vertices have post-degree at most `D`.

* `resAdv R D H` is the outer adversary.  When the outer vertex `p` is due, it lies in the block of
  the inner vertex `v = p / R`; its earlier neighbours are the servers of the arcs `w → v`
  (`w ∈ H v`).  The server of `w → v` is the vertex in position `resPos … w (rank H w v)` of the
  block of `w`: the blocks are listed with the vertices of the *induced colour* `popular R D` (the
  first colour that `A` used at least `D` times on the block, `0` if there is none) first, so the
  first `D` positions form the reserve, and the `r`-th later neighbour of `w` gets the `r`-th
  vertex of the reserve.  This is the tie-breaking rule of Construction 6.1.
* `outSeq R D H A` is the outer input played against `A`; `outSeq_eq` shows it is the static
  blow-up `blowSeq R H σ` with a block permutation `σ` read off from `A`'s colours.
* `inducedAlg A R D` is the induced algorithm `A'`: on an inner history it rebuilds the inner input
  so far, replays the outer adversary against `A` up to the end of the new block, and answers with
  the induced colour of that block (falling back to a fresh colour if that colour clashes, which
  makes `A'` proper by construction, `inducedAlg_isProper`).
* `simCol_runHist` (the induced colouring is online): on the actual inner input, the colour that
  `A'` computes for `v` is the induced colour `indCol` of the block of `v` in the actual outer play.
* `forcing_step` (Lemma 6.2 in this form): with `R = (K-1)(D-1)+1`, if `A'` uses `K`
  colours on the first `m` inner vertices, then `A` uses `K` colours on the first `m*R` outer
  vertices.  Either some block has no colour with `D` vertices, and then the block itself carries
  `K` colours (pigeonhole, `exists_large_colour_class`), or every induced colour is a colour of `A`
  and `A'` is faithful (`runCol_inducedAlg_eq`).
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Reserves -/

theorem List.getD_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- The positions `t < R` of a block on which the block colouring `bc` takes the value `c`. -/
def clsList (R : ℕ) (bc : ℕ → ℕ) (c : ℕ) : List ℕ := (List.range R).filter fun t => bc t = c

/-- The induced colour of a block: the first colour, in the order of the block, that occurs on at
least `D` of its vertices (`0` if there is none). -/
def popular (R D : ℕ) (bc : ℕ → ℕ) : ℕ :=
  (((List.range R).map bc).find? fun c => D ≤ (clsList R bc c).length).getD 0

/-- The order in which the vertices of a block are used as servers: first the vertices of the
induced colour (the first `D` of them form the reserve), then the others. -/
def resOrder (R D : ℕ) (bc : ℕ → ℕ) : List ℕ :=
  (List.range R).filter (fun t => decide (bc t = popular R D bc)) ++
    (List.range R).filter (fun t => !decide (bc t = popular R D bc))

/-- The colouring `col` restricted to the block of `w` (positions `0, …, R-1`). -/
def blockCol (col : ℕ → ℕ) (R w t : ℕ) : ℕ := col (w * R + t)

/-- The position, in the block of `w`, of the `r`-th server taken from that block. -/
def resPos (R D : ℕ) (col : ℕ → ℕ) (w r : ℕ) : ℕ := (resOrder R D (blockCol col R w)).getD r 0

variable {R D : ℕ}

theorem resOrder_perm (bc : ℕ → ℕ) : (resOrder R D bc).Perm (List.range R) :=
  List.filter_append_perm _ _

theorem mem_resOrder {bc : ℕ → ℕ} {t : ℕ} : t ∈ resOrder R D bc ↔ t < R := by
  rw [(resOrder_perm bc).mem_iff, List.mem_range]

theorem resOrder_nodup (bc : ℕ → ℕ) : (resOrder R D bc).Nodup :=
  (resOrder_perm bc).nodup_iff.2 List.nodup_range

theorem length_resOrder (bc : ℕ → ℕ) : (resOrder R D bc).length = R := by
  rw [(resOrder_perm bc).length_eq, List.length_range]

/-- Server positions permute the block. -/
theorem resPos_blockPerm (hR : 0 < R) (col : ℕ → ℕ) : BlockPerm R (resPos R D col) where
  lt w t := by
    unfold resPos
    rw [List.getD_eq_getElem?_getD]
    cases h : (resOrder R D (blockCol col R w))[t]? with
    | none => simpa using hR
    | some a => simpa using mem_resOrder.1 (List.mem_of_getElem? h)
  inj w t t' ht ht' heq := by
    unfold resPos at heq
    have hl := length_resOrder (R := R) (D := D) (blockCol col R w)
    rw [List.getD_of_lt _ (by rw [hl]; exact ht), List.getD_of_lt _ (by rw [hl]; exact ht')] at heq
    exact ((resOrder_nodup _).getElem_inj_iff).1 heq

theorem length_clsList (bc : ℕ → ℕ) (c : ℕ) :
    (clsList R bc c).length = ((range R).filter fun t => bc t = c).card := by
  unfold clsList
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext t
  simp

theorem popular_spec {bc : ℕ → ℕ} (hD : 1 ≤ D) (h : ∃ c, D ≤ (clsList R bc c).length) :
    D ≤ (clsList R bc (popular R D bc)).length := by
  obtain ⟨c, hc⟩ := h
  have hcmem : c ∈ (List.range R).map bc := by
    obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos (by omega : 0 < (clsList R bc c).length)
    simp only [clsList, List.mem_filter, List.mem_range, decide_eq_true_eq] at ht
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht.1, ht.2⟩
  unfold popular
  cases hf : ((List.range R).map bc).find? (fun c => D ≤ (clsList R bc c).length) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using hc) (hf c hcmem)
  | some c' =>
    simpa using List.find?_some hf

theorem popular_mem {bc : ℕ → ℕ} (hD : 1 ≤ D) (h : D ≤ (clsList R bc (popular R D bc)).length) :
    ∃ t < R, bc t = popular R D bc := by
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos (by omega :
    0 < (clsList R bc (popular R D bc)).length)
  simp only [clsList, List.mem_filter, List.mem_range, decide_eq_true_eq] at ht
  exact ⟨t, ht.1, ht.2⟩

/-- The first `D` servers taken from a block have the induced colour (when it occurs `D`
times). -/
theorem blockCol_resOrder {bc : ℕ → ℕ} (h : D ≤ (clsList R bc (popular R D bc)).length) {r : ℕ}
    (hr : r < D) : bc ((resOrder R D bc).getD r 0) = popular R D bc := by
  have hr' : r < (clsList R bc (popular R D bc)).length := lt_of_lt_of_le hr h
  have hmem : (resOrder R D bc).getD r 0 ∈ clsList R bc (popular R D bc) := by
    have hlen : r < (resOrder R D bc).length := by
      unfold resOrder
      rw [List.length_append]
      exact lt_of_lt_of_le hr' (Nat.le_add_right _ _)
    have heq : (resOrder R D bc)[r]'hlen = (clsList R bc (popular R D bc))[r]'hr' :=
      (List.getElem_append_left' hr' _).symm
    rw [List.getD_of_lt _ hlen, heq]
    exact List.getElem_mem _
  simp only [clsList, List.mem_filter, decide_eq_true_eq] at hmem
  exact hmem.2

theorem clsList_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) (c : ℕ) :
    clsList R bc c = clsList R bc' c := by
  unfold clsList
  apply List.filter_congr
  intro t ht
  rw [h t (List.mem_range.1 ht)]

theorem popular_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) :
    popular R D bc = popular R D bc' := by
  unfold popular
  rw [List.map_congr_left (fun t ht => h t (List.mem_range.1 ht))]
  simp only [clsList_congr h]

theorem resOrder_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) :
    resOrder R D bc = resOrder R D bc' := by
  unfold resOrder
  rw [popular_congr h]
  congr 1 <;> apply List.filter_congr <;> intro t ht <;> rw [h t (List.mem_range.1 ht)]

theorem resPos_congr {col col' : ℕ → ℕ} {w : ℕ}
    (h : ∀ t < R, col (w * R + t) = col' (w * R + t)) : resPos R D col w = resPos R D col' w := by
  funext r
  unfold resPos
  rw [resOrder_congr (bc := blockCol col R w) (bc' := blockCol col' R w) h]

/-! ### The outer adversary -/

/-- The reservation blow-up of Construction 6.1 as a rule that never stops: the next vertex is in
the block of `v = |h| / R` and its earlier neighbours are the servers of the arcs into `v`, read
off from the colours in the history. -/
def resAdv (R D : ℕ) (H : ℕ → Finset ℕ) (h : History) : Finset ℕ :=
  blowSeq R H (resPos R D (colourAt h)) h.length

/-- The outer input that the reservation adversary presents to `A`. -/
def outSeq (R D : ℕ) (H : ℕ → Finset ℕ) (A : OnlineAlg) : ℕ → Finset ℕ := playSeq (resAdv R D H) A

/-- The colours that `A` gives to the outer vertices. -/
def outCol (R D : ℕ) (H : ℕ → Finset ℕ) (A : OnlineAlg) : ℕ → ℕ := runCol A (outSeq R D H A)

/-- The induced colour of the inner vertex `v`: the induced colour of its block. -/
def indCol (R D : ℕ) (H : ℕ → Finset ℕ) (A : OnlineAlg) (v : ℕ) : ℕ :=
  popular R D (blockCol (outCol R D H A) R v)

variable {H : ℕ → Finset ℕ} {A : OnlineAlg}

theorem blowSeq_congr_σ {σ σ' : ℕ → ℕ → ℕ} {p : ℕ} (h : ∀ w ∈ H (p / R), σ w = σ' w) :
    blowSeq R H σ p = blowSeq R H σ' p := by
  unfold blowSeq
  apply Finset.image_congr
  intro w hw
  simp only [h w (Finset.mem_coe.1 hw)]

/-- The outer input is the static blow-up of `H` with the server positions chosen from `A`'s
colours. -/
theorem outSeq_eq (hH : ValidSeq H) :
    outSeq R D H A = blowSeq R H (resPos R D (outCol R D H A)) := by
  funext p
  change resAdv R D H (play (resAdv R D H) A p) = _
  unfold resAdv
  rw [length_play]
  apply blowSeq_congr_σ
  intro w hw
  apply resPos_congr
  intro t ht
  apply colourAt_play
  have h₁ : w < p / R := mem_range.1 (hH _ hw)
  have h₂ : w * R + R ≤ p / R * R := by
    have := Nat.mul_le_mul_right R h₁
    rwa [Nat.succ_mul] at this
  have h₃ := Nat.div_mul_le_self p R
  omega

theorem outSeq_valid (hH : ValidSeq H) (hR : 0 < R) : ValidSeq (outSeq R D H A) := by
  rw [outSeq_eq hH]
  exact blowSeq_valid hH hR (resPos_blockPerm hR _)

/-! ### The induced algorithm -/

/-- The inner input sequence that the induced algorithm reconstructs from its history `h` and the
earlier neighbours `s` of the new inner vertex. -/
def innerSeq (h : History) (s : Finset ℕ) (i : ℕ) : Finset ℕ :=
  if i < h.length then (h.getD i (∅, 0)).1 else if i = h.length then s else ∅

/-- The colour that the induced algorithm computes: replay the outer adversary against `A` on the
inner input so far, up to the end of the block of the new inner vertex, and take the induced
colour of that block. -/
def simCol (A : OnlineAlg) (R D : ℕ) (h : History) (s : Finset ℕ) : ℕ :=
  popular R D (blockCol (colourAt (play (resAdv R D (innerSeq h s)) A ((h.length + 1) * R)))
    R h.length)

/-- The induced algorithm `A'` (falling back to a fresh colour if the simulated colour clashes). -/
def inducedAlg (A : OnlineAlg) (R D : ℕ) : OnlineAlg :=
  ⟨fun h s => if simCol A R D h s ∈ nbrColours h s then OnlineAlg.fresh h s else simCol A R D h s⟩

theorem inducedAlg_isProper (A : OnlineAlg) (R D : ℕ) : (inducedAlg A R D).IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro h s
  change (if simCol A R D h s ∈ nbrColours h s then OnlineAlg.fresh h s else simCol A R D h s) ∉ _
  split_ifs with hc
  · exact OnlineAlg.fresh_notMem h s
  · exact hc

theorem resAdv_congr {H H' : ℕ → Finset ℕ} {V : ℕ} (hHH : ∀ i ≤ V, H i = H' i) {hist : History}
    (hl : hist.length / R ≤ V) : resAdv R D H hist = resAdv R D H' hist := by
  unfold resAdv blowSeq
  rw [hHH _ hl]
  have hr : ∀ w, rank H w (hist.length / R) = rank H' w (hist.length / R) :=
    fun w => rank_congr fun i hi => hHH i (by omega)
  simp only [hr]

theorem play_resAdv_congr {H H' : ℕ → Finset ℕ} {V : ℕ} (hR : 0 < R)
    (hHH : ∀ i ≤ V, H i = H' i) :
    play (resAdv R D H) A ((V + 1) * R) = play (resAdv R D H') A ((V + 1) * R) :=
  play_congr (fun _ hl => resAdv_congr hHH (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hR).2 hl)))
    _ le_rfl

theorem innerSeq_runHist (A' : OnlineAlg) (H : ℕ → Finset ℕ) (v : ℕ) :
    ∀ i ≤ v, innerSeq (runHist A' H v) (H v) i = H i := by
  intro i hi
  unfold innerSeq
  rw [length_runHist]
  rcases Nat.lt_or_eq_of_le hi with h | rfl
  · simp only [h, ↓reduceIte]
    rw [List.getD_of_lt _ (by simpa using h), getElem_runHist]
  · simp

/-- **The induced colouring is online.** On the actual inner input, the colour that the induced
algorithm computes for `v` is the induced colour of the block of `v` in the actual outer play. -/
theorem simCol_runHist (hR : 0 < R) (A' : OnlineAlg) (v : ℕ) :
    simCol A R D (runHist A' H v) (H v) = indCol R D H A v := by
  unfold simCol indCol
  rw [length_runHist, play_resAdv_congr hR (innerSeq_runHist A' H v)]
  apply popular_congr
  intro t ht
  unfold blockCol outCol outSeq
  apply colourAt_play
  rw [Nat.succ_mul]
  omega

theorem runCol_inducedAlg (hR : 0 < R) (v : ℕ) :
    runCol (inducedAlg A R D) H v =
      if indCol R D H A v ∈ nbrColours (runHist (inducedAlg A R D) H v) (H v) then
        OnlineAlg.fresh (runHist (inducedAlg A R D) H v) (H v) else indCol R D H A v := by
  change (if simCol A R D _ _ ∈ _ then _ else simCol A R D _ _) = _
  rw [simCol_runHist hR]

/-- The server of the arc `w → v` is an earlier neighbour of every vertex of the block of `v`. -/
theorem server_mem_outSeq (hH : ValidSeq H) (hR : 0 < R) {w v t : ℕ} (hw : w ∈ H v) (ht : t < R) :
    w * R + resPos R D (outCol R D H A) w (rank H w v) ∈ outSeq R D H A (v * R + t) := by
  have hσ : BlockPerm R (resPos R D (outCol R D H A)) := resPos_blockPerm hR _
  rw [outSeq_eq hH, mem_blowSeq hR hσ, div_add_lt hR ht, div_add_lt hR (hσ.lt _ _)]
  exact ⟨hw, rfl⟩

/-- If the block of `w` has a colour with `D` vertices, the servers taken from it have the induced
colour of `w` (the post-degree of `w` is at most `D`, so they come from the reserve). -/
theorem outCol_server (hD : 1 ≤ D) {m : ℕ} (hdeg : ∀ w < m, postDeg H m w ≤ D) (hH : ValidSeq H)
    {w v : ℕ} (hv : v < m) (hw : w ∈ H v)
    (hfw : ∃ c, D ≤ (clsList R (blockCol (outCol R D H A) R w) c).length) :
    outCol R D H A (w * R + resPos R D (outCol R D H A) w (rank H w v)) = indCol R D H A w :=
  blockCol_resOrder (popular_spec hD hfw)
    ((rank_lt_rank hv hw).trans_le (hdeg w ((mem_range.1 (hH v hw)).trans hv)))

/-- If the first `V` blocks each have a colour with `D` vertices, the induced algorithm gives each
of the first `V` inner vertices its induced colour (no fallback is ever used). -/
theorem runCol_inducedAlg_eq (hA : A.IsProper) (hH : ValidSeq H) (hR : 0 < R) (hD : 1 ≤ D)
    {m V : ℕ} (hdeg : ∀ w < m, postDeg H m w ≤ D) (hVm : V ≤ m)
    (hfaith : ∀ v < V, ∃ c, D ≤ (clsList R (blockCol (outCol R D H A) R v) c).length) :
    ∀ v < V, runCol (inducedAlg A R D) H v = indCol R D H A v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv
  rw [runCol_inducedAlg hR]
  split_ifs with hmem
  swap
  · rfl
  exfalso
  rw [nbrColours_runHist (hH v)] at hmem
  obtain ⟨w, hw, hwc⟩ := Finset.mem_image.1 hmem
  have hwv : w < v := mem_range.1 (hH v hw)
  rw [ih w hwv (hwv.trans hv)] at hwc
  obtain ⟨t, ht, htc⟩ := popular_mem hD (popular_spec hD (hfaith v hv))
  -- the outer vertex `v*R + t` has colour `indCol v` and is adjacent to the server of `w → v`,
  -- which has colour `indCol w`
  have hmemG := server_mem_outSeq (D := D) (A := A) hH hR hw ht
  have hne := runCol_ne hA hmemG (mem_range.1 (outSeq_valid hH hR _ hmemG))
  have hserv := outCol_server hD hdeg hH (lt_of_lt_of_le hv hVm) hw (hfaith w (hwv.trans hv))
  apply hne
  change outCol R D H A (v * R + t) = outCol R D H A _
  rw [hserv, hwc]
  exact htc

/-- **Lemma 6.2 (forcing survives a blow-up), against a fixed algorithm and without the stop
rule.** With `R = (K-1)(D-1)+1`, if the induced algorithm uses `K` colours on the first `m` inner
vertices (whose post-degrees are at most `D`), then `A` uses `K` colours on the first `m * R`
outer vertices. -/
theorem forcing_step {K D R m : ℕ} (hRdef : R = (K - 1) * (D - 1) + 1) (hD : 1 ≤ D)
    (hA : A.IsProper) (hH : ValidSeq H) (hdeg : ∀ w < m, postDeg H m w ≤ D)
    (hforce : K ≤ ((range m).image (runCol (inducedAlg A R D) H)).card) :
    K ≤ ((range (m * R)).image (outCol R D H A)).card := by
  have hR : 0 < R := by omega
  have hblock : ∀ v < m, ∀ t < R, v * R + t < m * R := by
    intro v hv t ht
    have := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hv)
    rw [Nat.succ_mul] at this
    omega
  by_cases hfaith : ∀ v < m, ∃ c, D ≤ (clsList R (blockCol (outCol R D H A) R v) c).length
  · -- every induced colour is a colour of `A`
    have heq := runCol_inducedAlg_eq hA hH hR hD hdeg le_rfl hfaith
    refine hforce.trans (card_le_card ?_)
    intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
    rw [mem_range] at hv
    rw [heq v hv]
    obtain ⟨t, ht, htc⟩ := popular_mem hD (popular_spec hD (hfaith v hv))
    exact mem_image.2 ⟨v * R + t, mem_range.2 (hblock v hv t ht), htc⟩
  · -- some block has no colour with `D` vertices, so it carries `K` colours
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

end OnlineColouring
