module

public import OnlineColouring.NumOneLevel
public import OnlineColouring.CertGame

/-!
# From the abstract one-level game to adversaries: lower bounds on `V(m)`

Paper: Appendix D.3 ("One level, exactly"): an adversary strategy of the abstract
game certifies the lower bound `V(m) ≥ C + 1`.

`exists_adv_of_win` (**abstraction lemma, lower bounds**): if the adversary beats the palette of
`C` colours in the abstract game (`Win C (sizesFrom m b 0) []`, `NumGame.lean`) and the blocks are
at least minimal (`b t ≥ max(1, m - t - 1)`), then there is an adversary of the form of
Theorem D.2 (`AppBD.IsOneLevelAdv m b adv`: against every proper algorithm it presents a
reservation blow-up of `K_m` with block sizes `b`, one unused server in each earlier block) that
forces `C + 1` colours.

The abstract game knows only the palette `{0, …, C - 1}`, while an algorithm may use any colours.
The invariant `AdvInv` therefore says: the position is legal (`Legal`), and either `C + 1` colours
are in use already, or some injective renaming `ρ` of the colours in use into the palette turns
the abstract position of the history into a winning position.  `AdvInv.exists_stepGood` is the
induction step: the adversary can choose servers such that the invariant holds after every proper
colouring of the next block (a new colour is renamed to an unused colour of the palette,
`exists_extend`; if none is left, `C + 1` colours are in use).  The adversary `winAdv` chooses
such servers (classically), and keeps choosing unused servers after it has won, so that it always
presents the whole blow-up.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

open Finset AppBD

/-! ### Histories extended by a block -/

/-- The entries of a block: all its vertices have the earlier-neighbour set `nb`, and `cs` lists
their colours. -/
def blockHist (nb : Finset ℕ) (cs : List ℕ) : History := cs.map fun c => (nb, c)

theorem length_blockHist (nb : Finset ℕ) (cs : List ℕ) : (blockHist nb cs).length = cs.length := by
  simp [blockHist]

theorem nbrsOf_blockHist {nb : Finset ℕ} {cs : List ℕ} (hcs : cs ≠ []) :
    nbrsOf (blockHist nb cs) = nb := by
  ext y
  rw [mem_nbrsOf]
  constructor
  · rintro ⟨e, he, hy⟩
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
    exact hy
  · intro hy
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hcs
    exact ⟨(nb, c), List.mem_map.2 ⟨c, hc, rfl⟩, hy⟩

theorem usedColours_append (h h' : History) :
    usedColours (h ++ h') = usedColours h ∪ usedColours h' := by
  ext c
  simp [usedColours]

theorem usedColours_blockHist (nb : Finset ℕ) (cs : List ℕ) :
    usedColours (blockHist nb cs) = cs.toFinset := by
  ext c
  simp [usedColours, blockHist]

theorem colourAt_append_left {h h' : History} {i : ℕ} (hi : i < h.length) :
    colourAt (h ++ h') i = colourAt h i := by
  simp [colourAt, List.getElem?_append_left hi]

theorem colourAt_append_right (h h' : History) (i : ℕ) :
    colourAt (h ++ h') (h.length + i) = colourAt h' i := by
  simp only [colourAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem colourAt_blockHist (nb : Finset ℕ) (cs : List ℕ) (i : ℕ) :
    colourAt (blockHist nb cs) i = cs.getD i 0 := by
  simp only [colourAt, blockHist, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cs[i]? <;> rfl

theorem runHist_block {A : OnlineAlg} {N : ℕ → Finset ℕ} {nb : Finset ℕ} {a : ℕ} :
    ∀ n, (∀ x, a ≤ x → x < a + n → N x = nb) →
      runHist A N (a + n) = runHist A N a ++ blockHist nb ((List.range' a n).map (runCol A N))
  | 0, _ => by simp [blockHist]
  | n + 1, hN => by
    rw [← Nat.add_assoc, runHist_succ, runHist_block n (fun x h1 h2 => hN x h1 (by omega)),
      hN (a + n) (by omega) (by omega), List.range'_1_concat, List.map_append, blockHist,
      blockHist, List.map_append, List.append_assoc]
    rfl

/-! ### Legal positions -/

/-- The history `h` is a legal position at the start of block `t`: it has the right length, all
servers so far are earlier vertices, and every earlier block has at least `m - t` unused
vertices. -/
structure Legal (m : ℕ) (b : ℕ → ℕ) (t : ℕ) (h : History) : Prop where
  len : h.length = start b t
  sub : ∀ y ∈ nbrsOf h, y < start b t
  free : ∀ s < t, m - t ≤ ((blk b s) \ nbrsOf h).card

section Next

variable {m : ℕ} {b : ℕ → ℕ} {t : ℕ} {h : History} {srv : ℕ → ℕ} {cs : List ℕ}

theorem image_srv_lt {U : Finset ℕ} (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) :
    ∀ y ∈ (range t).image srv, y < start b t := by
  intro y hy
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hy
  exact lt_of_mem_blk (hsrv s (mem_range.1 hs)).1 (mem_range.1 hs)

theorem nbrsOf_next (hcs : cs ≠ []) :
    nbrsOf (h ++ blockHist ((range t).image srv) cs) = nbrsOf h ∪ (range t).image srv := by
  rw [nbrsOf_append, nbrsOf_blockHist hcs]

theorem blk_sdiff_next (hL : Legal m b t h) (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ nbrsOf h) :
    blk b t \ (nbrsOf h ∪ (range t).image srv) = blk b t := by
  apply sdiff_eq_self_of_disjoint
  rw [disjoint_left]
  intro y hy hyU
  have hya := (mem_blk.1 hy).1
  rcases mem_union.1 hyU with hyU | hyU
  · have := hL.sub y hyU
    omega
  · have := image_srv_lt hsrv y hyU
    omega

/-- The abstract position after a block: the new block is a new row, and the earlier rows have
lost their servers. -/
theorem rowsOf_next (hL : Legal m b t h) (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ nbrsOf h)
    (hlen : cs.length = b t) :
    rowsOf b (h ++ blockHist ((range t).image srv) cs) (nbrsOf h ∪ (range t).image srv) (t + 1) =
      (cs : Multiset ℕ) :: rowsOf b h (nbrsOf h ∪ (range t).image srv) t := by
  have hrow : rowOf b (h ++ blockHist ((range t).image srv) cs)
      (nbrsOf h ∪ (range t).image srv) t = (cs : Multiset ℕ) := by
    rw [rowOf, blk_sdiff_next hL hsrv, blk_val, Multiset.map_coe]
    have hlist : (List.range' (start b t) (b t)).map
        (colourAt (h ++ blockHist ((range t).image srv) cs)) = cs := by
      conv_rhs => rw [← map_range'_getD cs (start b t), hlen]
      refine List.map_congr_left fun x hx => ?_
      rw [List.mem_range'_1] at hx
      have e : x = h.length + (x - start b t) := by
        rw [hL.len]
        omega
      conv_lhs => rw [e]
      rw [colourAt_append_right, colourAt_blockHist]
    rw [hlist]
  have hrows : rowsOf b (h ++ blockHist ((range t).image srv) cs)
      (nbrsOf h ∪ (range t).image srv) t = rowsOf b h (nbrsOf h ∪ (range t).image srv) t :=
    rowsOf_congr fun y hy => colourAt_append_left (by rw [hL.len]; exact hy)
  rw [rowsOf, hrow, hrows]

theorem Legal.next (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) (ht : t < m) (hL : Legal m b t h)
    (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ nbrsOf h) (hlen : cs.length = b t) :
    Legal m b (t + 1) (h ++ blockHist ((range t).image srv) cs) := by
  have hbt1 : 1 ≤ b t := (le_max_left _ _).trans (hb t ht)
  have hbt2 : m - t - 1 ≤ b t := (le_max_right _ _).trans (hb t ht)
  have hcs : cs ≠ [] := by
    intro e
    rw [e] at hlen
    simp only [List.length_nil] at hlen
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, length_blockHist, hL.len, hlen, start_succ]
  · intro y hy
    rw [nbrsOf_next hcs, mem_union] at hy
    have := start_mono b (Nat.le_add_right t 1)
    rcases hy with hy | hy
    · have := hL.sub y hy
      omega
    · have := image_srv_lt hsrv y hy
      omega
  · intro s hs
    rw [nbrsOf_next hcs]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · rw [sdiff_union_image hsrv hs, card_erase_of_mem (mem_sdiff.2 (hsrv s hs))]
      have := hL.free s hs
      omega
    · rw [blk_sdiff_next hL hsrv, card_blk]
      omega

/-- In a legal position at the start of a block `t < m`, every earlier block has an unused
vertex. -/
theorem Legal.exists_srv (ht : t < m) (hL : Legal m b t h) :
    ∃ srv : ℕ → ℕ, ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ nbrsOf h := by
  have hex : ∀ s, ∃ y, s < t → y ∈ blk b s ∧ y ∉ nbrsOf h := by
    intro s
    by_cases hs : s < t
    · have hpos : 0 < ((blk b s) \ nbrsOf h).card := by
        have := hL.free s hs
        omega
      obtain ⟨y, hy⟩ := card_pos.1 hpos
      exact ⟨y, fun _ => mem_sdiff.1 hy⟩
    · exact ⟨0, fun h' => absurd h' hs⟩
  choose srv hsrv using hex
  exact ⟨srv, fun s hs => hsrv s hs⟩

theorem rowsOf_congr_set {U U' : Finset ℕ} :
    ∀ {t : ℕ}, (∀ s < t, blk b s \ U = blk b s \ U') → rowsOf b h U t = rowsOf b h U' t
  | 0, _ => rfl
  | t + 1, hU => by
    rw [rowsOf, rowsOf, rowsOf_congr_set fun s hs => hU s (Nat.lt_succ_of_lt hs), rowOf, rowOf,
      hU t (Nat.lt_succ_self t)]

/-- **Picks are servers.**  A move of the abstract game from the (renamed) position of a history
is realised by a choice of unused servers. -/
theorem exists_srv_of_picked {U : Finset ℕ} (ρ : ℕ → ℕ) :
    ∀ (t : ℕ) {rows'' : List (Multiset ℕ)} {F'' : Finset ℕ},
      Picked ((rowsOf b h U t).map (Multiset.map ρ)) rows'' F'' →
        ∃ srv : ℕ → ℕ, (∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) ∧
          rows'' = (rowsOf b h (U ∪ (range t).image srv) t).map (Multiset.map ρ) ∧
          F'' = (((range t).image srv).image (colourAt h)).image ρ
  | 0, _, _, hP => by
    obtain ⟨rfl, rfl⟩ := hP
    exact ⟨fun _ => 0, fun s hs => absurd hs (Nat.not_lt_zero s), rfl, by simp⟩
  | t + 1, _, _, hP => by
    rw [rowsOf, List.map_cons] at hP
    obtain ⟨c', hc', rs', F', hP', rfl, rfl⟩ := hP
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hc'
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hc
    have hy' := mem_sdiff.1 (Finset.mem_def.2 hy)
    obtain ⟨srv0, hsrv0, rfl, rfl⟩ := exists_srv_of_picked ρ t hP'
    have hupd : ∀ s < t, Function.update srv0 t y s = srv0 s := fun s hs =>
      Function.update_of_ne (Nat.ne_of_lt hs) _ _
    have himg : (range (t + 1)).image (Function.update srv0 t y) =
        insert y ((range t).image srv0) := by
      rw [range_add_one, image_insert, Function.update_self]
      congr 1
      exact image_congr fun s hs => hupd s (mem_range.1 hs)
    have hsrv : ∀ s < t + 1, Function.update srv0 t y s ∈ blk b s ∧
        Function.update srv0 t y s ∉ U := by
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · rw [hupd s hs]
        exact hsrv0 s hs
      · rw [Function.update_self]
        exact hy'
    have hrows : rowsOf b h (U ∪ (range (t + 1)).image (Function.update srv0 t y)) t =
        rowsOf b h (U ∪ (range t).image srv0) t := by
      apply rowsOf_congr_set
      intro s hs
      rw [himg]
      ext z
      simp only [mem_sdiff, mem_union, mem_insert, not_or]
      constructor
      · rintro ⟨hz, hzU, -, hzn⟩
        exact ⟨hz, hzU, hzn⟩
      · rintro ⟨hz, hzU, hzn⟩
        refine ⟨hz, hzU, fun e => ?_, hzn⟩
        have := eq_of_mem_blk (e ▸ hz) hy'.1
        omega
    refine ⟨Function.update srv0 t y, hsrv, ?_, ?_⟩
    · rw [rowsOf, List.map_cons, rowOf_union hsrv (Nat.lt_succ_self t), Function.update_self,
        Multiset.map_erase_of_mem _ _ hc, hrows]
    · rw [himg, image_insert, image_insert]

theorem mem_usedColours_of_mem_rowsOf {U : Finset ℕ} :
    ∀ {t : ℕ}, start b t ≤ h.length → ∀ r ∈ rowsOf b h U t, ∀ c ∈ r, c ∈ usedColours h
  | 0, _, r, hr, _, _ => absurd hr List.not_mem_nil
  | t + 1, hlen, r, hr, c, hc => by
    rw [rowsOf, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hc
      have hyb := (mem_sdiff.1 (Finset.mem_def.2 hy)).1
      exact Cert.colourAt_mem_usedColours ((mem_blk.1 hyb).2.trans_le hlen)
    · exact mem_usedColours_of_mem_rowsOf ((start_mono b (Nat.le_succ t)).trans hlen) r hr c hc

end Next

/-! ### Renamings into the palette -/

/-- An injective map of `S` into the palette extends to an injective map of `S' ⊇ S` into the
palette if `S'` has at most `C` elements. -/
theorem exists_extend {C : ℕ} {S S' : Finset ℕ} (hS : S ⊆ S') (hcard : S'.card ≤ C) {ρ : ℕ → ℕ}
    (hinj : Set.InjOn ρ (S : Set ℕ)) (hlt : ∀ c ∈ S, ρ c < C) :
    ∃ ρ' : ℕ → ℕ, (∀ c ∈ S, ρ' c = ρ c) ∧ Set.InjOn ρ' (S' : Set ℕ) ∧ ∀ c ∈ S', ρ' c < C := by
  classical
  have hcS : (S.image ρ).card = S.card := card_image_of_injOn hinj
  have hsubC : S.image ρ ⊆ range C := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (hlt c hc)
  have hTc : (range C \ S.image ρ).card = C - S.card := by
    rw [card_sdiff_of_subset hsubC, card_range, hcS]
  have hDc : (S' \ S).card = S'.card - S.card := card_sdiff_of_subset hS
  have hle : (S' \ S).card ≤ (range C \ S.image ρ).card := by omega
  have hmemS : ∀ c ∈ S', c ∉ S' \ S → c ∈ S := fun c hc hD => by
    by_contra h
    exact hD (mem_sdiff.2 ⟨hc, h⟩)
  let g : ↥(S' \ S) → ↥(range C \ S.image ρ) := fun d =>
    (range C \ S.image ρ).equivFin.symm (Fin.castLE hle ((S' \ S).equivFin d))
  have hg : Function.Injective g := fun d d' hdd =>
    (S' \ S).equivFin.injective
      (Fin.castLE_injective hle ((range C \ S.image ρ).equivFin.symm.injective hdd))
  refine ⟨fun c => if hc : c ∈ S' \ S then (g ⟨c, hc⟩ : ℕ) else ρ c, ?_, ?_, ?_⟩
  · intro c hc
    have hD : c ∉ S' \ S := fun h => (mem_sdiff.1 h).2 hc
    simp only [hD, ↓reduceDIte]
  · intro c hc c' hc' heq
    rw [mem_coe] at hc hc'
    by_cases h1 : c ∈ S' \ S <;> by_cases h2 : c' ∈ S' \ S
    · simp only [h1, h2, ↓reduceDIte] at heq
      exact congrArg Subtype.val (hg (Subtype.ext heq))
    · simp only [h1, h2, ↓reduceDIte] at heq
      have hT1 := (g ⟨c, h1⟩).2
      rw [heq] at hT1
      exact absurd (mem_image_of_mem ρ (hmemS c' hc' h2)) (mem_sdiff.1 hT1).2
    · simp only [h1, h2, ↓reduceDIte] at heq
      have hT1 := (g ⟨c', h2⟩).2
      rw [← heq] at hT1
      exact absurd (mem_image_of_mem ρ (hmemS c hc h1)) (mem_sdiff.1 hT1).2
    · simp only [h1, h2, ↓reduceDIte] at heq
      exact hinj (mem_coe.2 (hmemS c hc h1)) (mem_coe.2 (hmemS c' hc' h2)) heq
  · intro c hc
    by_cases h1 : c ∈ S' \ S
    · simp only [h1, ↓reduceDIte]
      exact mem_range.1 (mem_sdiff.1 (g ⟨c, h1⟩).2).1
    · simp only [h1, ↓reduceDIte]
      exact hlt c (hmemS c hc h1)

/-! ### The invariant of the adversary -/

/-- The invariant: the position is legal, and either `C + 1` colours are in use, or the abstract
position, with the colours in use renamed injectively into the palette, is winning for the
adversary. -/
def AdvInv (C m : ℕ) (b : ℕ → ℕ) (t : ℕ) (h : History) : Prop :=
  Legal m b t h ∧ (C + 1 ≤ (usedColours h).card ∨
    ∃ ρ : ℕ → ℕ, Set.InjOn ρ (usedColours h : Set ℕ) ∧ (∀ c ∈ usedColours h, ρ c < C) ∧
      Win C (sizesFrom m b t) ((rowsOf b h (nbrsOf h) t).map (Multiset.map ρ)))

/-- `srv` is a good choice of servers for block `t`: one unused vertex in each earlier block, and
the invariant holds after every proper colouring of block `t`. -/
def StepGood (C m : ℕ) (b : ℕ → ℕ) (t : ℕ) (h : History) (srv : ℕ → ℕ) : Prop :=
  (∀ s < t, srv s ∈ blk b s ∧ srv s ∉ nbrsOf h) ∧
    ∀ cs : List ℕ, cs.length = b t →
      (∀ c ∈ cs, c ∉ ((range t).image srv).image (colourAt h)) →
        AdvInv C m b (t + 1) (h ++ blockHist ((range t).image srv) cs)

section Step

variable {C m : ℕ} {b : ℕ → ℕ} {t : ℕ} {h : History}

/-- **The induction step.**  From a position before a block `t < m` that satisfies the invariant
the adversary has a good choice of servers (blocks of sizes `b t ≥ max(1, m - t - 1)`). -/
theorem AdvInv.exists_stepGood (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) (ht : t < m)
    (hI : AdvInv C m b t h) : ∃ srv : ℕ → ℕ, StepGood C m b t h srv := by
  obtain ⟨hL, hI⟩ := hI
  have hbt1 : 1 ≤ b t := (le_max_left _ _).trans (hb t ht)
  rcases hI with hcard | ⟨ρ, hinj, hlt, hW⟩
  · obtain ⟨srv, hsrv⟩ := hL.exists_srv ht
    refine ⟨srv, hsrv, fun cs hlen _ => ⟨hL.next hb ht hsrv hlen, Or.inl ?_⟩⟩
    rw [usedColours_append]
    exact hcard.trans (card_le_card subset_union_left)
  · rw [sizesFrom_of_lt b ht] at hW
    obtain ⟨rows'', F'', hP, hall⟩ := hW
    obtain ⟨srv, hsrv, rfl, rfl⟩ := exists_srv_of_picked ρ t hP
    refine ⟨srv, hsrv, fun cs hlen hcs => ⟨hL.next hb ht hsrv hlen, ?_⟩⟩
    by_cases hcard : C + 1 ≤ (usedColours (h ++ blockHist ((range t).image srv) cs)).card
    · exact Or.inl hcard
    · right
      have hused : usedColours (h ++ blockHist ((range t).image srv) cs) =
          usedColours h ∪ cs.toFinset := by
        rw [usedColours_append, usedColours_blockHist]
      have hcsne : cs ≠ [] := by
        intro e
        rw [e] at hlen
        simp only [List.length_nil] at hlen
        omega
      obtain ⟨ρ', hagree, hinj', hlt'⟩ := exists_extend (S := usedColours h)
        (S' := usedColours (h ++ blockHist ((range t).image srv) cs))
        (by rw [hused]; exact subset_union_left) (by omega) hinj hlt
      refine ⟨ρ', hinj', hlt', ?_⟩
      rw [nbrsOf_next hcsne, rowsOf_next hL hsrv hlen, List.map_cons]
      have hrows : (rowsOf b h (nbrsOf h ∪ (range t).image srv) t).map (Multiset.map ρ') =
          (rowsOf b h (nbrsOf h ∪ (range t).image srv) t).map (Multiset.map ρ) :=
        List.map_congr_left fun r hr => Multiset.map_congr rfl fun c hc =>
          hagree c (mem_usedColours_of_mem_rowsOf (le_of_eq hL.len.symm) r hr c hc)
      rw [hrows]
      apply hall
      · rw [Multiset.card_map, Multiset.coe_card, hlen]
      · intro c' hc'
        obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hc'
        have hcmem : c ∈ usedColours (h ++ blockHist ((range t).image srv) cs) := by
          rw [hused]
          exact mem_union_right _ (List.mem_toFinset.2 (Multiset.mem_coe.1 hc))
        refine ⟨hlt' c hcmem, fun hF => ?_⟩
        obtain ⟨d, hd, hdc⟩ := mem_image.1 hF
        have hdu : d ∈ usedColours h := by
          obtain ⟨y, hy, rfl⟩ := mem_image.1 hd
          exact Cert.colourAt_mem_usedColours (by rw [hL.len]; exact image_srv_lt hsrv y hy)
        rw [← hagree d hdu] at hdc
        have hdc' : d = c := hinj' (mem_coe.2 (by rw [hused]; exact mem_union_left _ hdu))
          (mem_coe.2 hcmem) hdc
        exact hcs c (Multiset.mem_coe.1 hc) (hdc' ▸ hd)

end Step

/-! ### The adversary -/

open Classical in
/-- The servers that the adversary chooses for block `t` in the position `h`. -/
noncomputable def srvAt (C m : ℕ) (b : ℕ → ℕ) (t : ℕ) (h : History) : ℕ → ℕ :=
  if hex : ∃ srv : ℕ → ℕ, StepGood C m b t h srv then hex.choose else fun _ => 0

theorem srvAt_spec {C m : ℕ} {b : ℕ → ℕ} {t : ℕ} {h : History}
    (hex : ∃ srv : ℕ → ℕ, StepGood C m b t h srv) : StepGood C m b t h (srvAt C m b t h) := by
  simp only [srvAt, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- The rule of the adversary: the vertex number `h.length` lies in block `t`, and its earlier
neighbours are the servers chosen at the start of the block. -/
noncomputable def advRule (C m : ℕ) (b : ℕ → ℕ) (h : History) : Finset ℕ :=
  (range (blockOf b m h.length)).image
    (srvAt C m b (blockOf b m h.length) (h.take (start b (blockOf b m h.length))))

/-- The adversary that follows a winning strategy of the abstract game. -/
noncomputable def winAdv (C m : ℕ) (b : ℕ → ℕ) : Adversary :=
  boundedAdv (start b m) (advRule C m b)

/-- The input that `winAdv` presents against `A`. -/
noncomputable def advSeq (C m : ℕ) (b : ℕ → ℕ) (A : OnlineAlg) : ℕ → Finset ℕ :=
  playSeq (advRule C m b) A

section Play

variable {C m : ℕ} {b : ℕ → ℕ} (A : OnlineAlg)

theorem advSeq_eq {t x : ℕ} (ht : t < m) (hx : x ∈ blk b t) :
    advSeq C m b A x =
      (range t).image (srvAt C m b t (runHist A (advSeq C m b A) (start b t))) := by
  change advRule C m b (play (advRule C m b) A x) = _
  rw [← runHist_playSeq]
  unfold advRule
  rw [length_runHist, blockOf_of_mem ht hx, runHist_take (mem_blk.1 hx).1]
  rfl

theorem winAdv_hist (p : ℕ) :
    (winAdv C m b).hist A p = runHist A (advSeq C m b A) (min p (start b m)) := by
  rw [winAdv, boundedAdv_hist, advSeq, runHist_playSeq]

variable {A}

/-- If the adversary wins the abstract game and the blocks have sizes `b t ≥ max(1, m - t - 1)`,
the invariant holds at the start of every block of the play of `winAdv` against a proper
algorithm. -/
theorem advInv_play (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) (hW : Win C (sizesFrom m b 0) [])
    (hA : A.IsProper) :
    ∀ t ≤ m, AdvInv C m b t (runHist A (advSeq C m b A) (start b t))
  | 0, _ => by
    have h0 : start b 0 = 0 := by simp [start]
    rw [h0]
    refine ⟨⟨h0.symm, ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, Or.inr ⟨id, ?_, ?_, hW⟩⟩
    · intro y hy
      simp [nbrsOf, runHist] at hy
    · intro c hc
      simp [usedColours, runHist] at hc
    · intro c hc
      simp [usedColours, runHist] at hc
  | t + 1, ht => by
    have htm : t < m := ht
    have hI := advInv_play hb hW hA t htm.le
    have hgood := srvAt_spec (hI.exists_stepGood hb htm)
    have hN : ∀ x, start b t ≤ x → x < start b t + b t → advSeq C m b A x =
        (range t).image (srvAt C m b t (runHist A (advSeq C m b A) (start b t))) :=
      fun x h1 h2 => advSeq_eq A htm (mem_blk.2 ⟨h1, by rw [start_succ]; exact h2⟩)
    rw [start_succ, runHist_block (b t) hN]
    apply hgood.2
    · simp
    · intro c hc hmem
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_range'_1] at hx
      obtain ⟨y, hy, hyc⟩ := mem_image.1 hmem
      have hylt : y < start b t := image_srv_lt hgood.1 y hy
      rw [colourAt_runHist hylt] at hyc
      have hyN : y ∈ advSeq C m b A x := by
        rw [hN x hx.1 hx.2]
        exact hy
      exact runCol_ne hA hyN (by omega) hyc.symm

/-- Under the same hypotheses, `winAdv` presents a reservation blow-up of `K_m` with block sizes
`b`. -/
theorem advSeq_isOneLevelSeq (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t)
    (hW : Win C (sizesFrom m b 0) []) (hA : A.IsProper) :
    IsOneLevelSeq m b (advSeq C m b A) := by
  have hgood : ∀ t < m, StepGood C m b t (runHist A (advSeq C m b A) (start b t))
      (srvAt C m b t (runHist A (advSeq C m b A) (start b t))) := fun t ht =>
    srvAt_spec ((advInv_play hb hW hA t ht.le).exists_stepGood hb ht)
  have key : ∀ t < m, ∀ t' < m, ∀ s, s < t → t < t' →
      srvAt C m b t (runHist A (advSeq C m b A) (start b t)) s ≠
        srvAt C m b t' (runHist A (advSeq C m b A) (start b t')) s := by
    intro t ht t' ht' s hs htt' heq
    have hbt1 : 1 ≤ b t := (le_max_left _ _).trans (hb t ht)
    have hmem : start b t ∈ blk b t := mem_blk.2 ⟨le_rfl, by rw [start_succ]; omega⟩
    have h1 : srvAt C m b t (runHist A (advSeq C m b A) (start b t)) s ∈
        nbrsOf (runHist A (advSeq C m b A) (start b t')) :=
      mem_nbrsOf_runHist.2 ⟨start b t, lt_of_lt_of_le (mem_blk.1 hmem).2 (start_mono b htt'), by
        rw [advSeq_eq A ht hmem]
        exact mem_image_of_mem _ (mem_range.2 hs)⟩
    exact ((hgood t' ht').1 s (hs.trans htt')).2 (heq ▸ h1)
  refine ⟨fun t => srvAt C m b t (runHist A (advSeq C m b A) (start b t)),
    fun t ht s hs => ((hgood t ht).1 s hs).1, ?_, fun t ht x hx => advSeq_eq A ht hx⟩
  intro t ht t' ht' s hs hs' heq
  rcases lt_trichotomy t t' with hlt | hlt | hlt
  · exact absurd heq (key t ht t' ht' s hs hlt)
  · exact hlt
  · exact absurd heq.symm (key t' ht' t ht s hs' hlt)

end Play

/-- **Abstraction lemma, lower bounds.**  If the adversary beats the palette of `C` colours in
the abstract one-level game with block sizes `b t ≥ max(1, m - t - 1)`, then some adversary that
presents reservation blow-ups of `K_m` with block sizes `b` (one unused server in each earlier
block) forces `C + 1` colours. -/
theorem exists_adv_of_win {C m : ℕ} {b : ℕ → ℕ} (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t)
    (hW : Win C (sizesFrom m b 0) []) :
    ∃ adv : Adversary, IsOneLevelAdv m b adv ∧ adv.Forces (C + 1) := by
  refine ⟨winAdv C m b, fun A hA => ⟨advSeq C m b A, advSeq_isOneLevelSeq hb hW hA,
    winAdv_hist A⟩, fun A hA => ⟨start b m, ?_, ?_⟩⟩
  · rw [winAdv_hist, min_self]
    simp [winAdv, boundedAdv]
  · rw [winAdv_hist, min_self]
    obtain ⟨-, hc | ⟨ρ, -, -, hW'⟩⟩ := advInv_play hb hW hA m le_rfl
    · exact hc
    · rw [sizesFrom_self] at hW'
      exact absurd hW' (by simp [Win])

end Num

end OnlineColouring
