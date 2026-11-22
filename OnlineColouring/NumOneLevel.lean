module

public import OnlineColouring.AppBDOneLevel
public import OnlineColouring.NumGame
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.List.GetD

/-!
# From the abstract one-level game to algorithms: upper bounds on `V(m)`

Paper: Appendix D.3 ("One level, exactly"): "an algorithm strategy that survives
with `V(m)` colours" certifies the upper bound `V(m) ≤ C`.

The adversaries are those of Theorem D.2 (`AppBD.IsOneLevelAdv m b adv`, `AppBDOneLevel.lean`):
against every proper algorithm they present, block after block, a reservation blow-up of `K_m`
with block sizes `b`, one unused server in each earlier block.

* `nbrsOf h`: the vertices that have served in the history `h`; `rowOf b h U s`: the multiset of
  the colours of the vertices of block `s` outside `U`; `rowsOf b h U t`: the rows of the blocks
  `t - 1, …, 0`.  With `U = nbrsOf h` this is the position of the abstract game.
* `picked_rowsOf`: choosing one unused server in each earlier block is a move `Picked` of the
  abstract game.
* `stratAlg C m b`: the algorithm that reads the abstract position off the history and answers
  with a multiset from which it survives (`resp`, chosen classically from `Surv`), giving the
  `i`-th vertex of the block the `i`-th colour of that multiset.
* `not_forces_of_surv` (**abstraction lemma, upper bounds**): if all blocks are nonempty and
  `Surv C (sizesFrom m b 0) []`, i.e. the algorithm survives the abstract game with `C` colours,
  then no adversary of the form of Theorem D.2 forces `C + 1` colours.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

open Finset AppBD

/-! ### Blocks -/

theorem eq_of_mem_blk {b : ℕ → ℕ} {s s' x : ℕ} (h : x ∈ blk b s) (h' : x ∈ blk b s') :
    s = s' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := lt_of_mem_blk h hlt
    have := (mem_blk.1 h').1
    omega
  · have := lt_of_mem_blk h' hlt
    have := (mem_blk.1 h).1
    omega

theorem blk_val (b : ℕ → ℕ) (t : ℕ) :
    (blk b t).val = (List.range' (start b t) (b t) : Multiset ℕ) := by
  rw [blk, Nat.Ico_eq_range', start_succ, Nat.add_sub_cancel_left]

theorem map_range'_getD (L : List ℕ) (a : ℕ) :
    (List.range' a L.length).map (fun x => L.getD (x - a) 0) = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
    rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ h2]

/-- The sizes of the blocks `t, …, m - 1`. -/
def sizesFrom (m : ℕ) (b : ℕ → ℕ) (t : ℕ) : List ℕ := (List.range' t (m - t)).map b

theorem sizesFrom_of_lt {m t : ℕ} (b : ℕ → ℕ) (ht : t < m) :
    sizesFrom m b t = b t :: sizesFrom m b (t + 1) := by
  rw [sizesFrom, sizesFrom, show m - t = (m - (t + 1)) + 1 by omega, List.range'_succ,
    List.map_cons]

theorem sizesFrom_self (m : ℕ) (b : ℕ → ℕ) : sizesFrom m b m = [] := by
  simp [sizesFrom]

/-! ### The abstract position of a history -/

/-- The vertices that occur in an earlier-neighbour set of the history: the servers so far. -/
def nbrsOf (h : History) : Finset ℕ := h.toFinset.biUnion Prod.fst

theorem mem_nbrsOf {h : History} {y : ℕ} : y ∈ nbrsOf h ↔ ∃ e ∈ h, y ∈ e.1 := by
  simp [nbrsOf]

theorem nbrsOf_append (h h' : History) : nbrsOf (h ++ h') = nbrsOf h ∪ nbrsOf h' := by
  ext y
  simp only [mem_nbrsOf, mem_union, List.mem_append]
  constructor
  · rintro ⟨e, he | he, hy⟩
    · exact Or.inl ⟨e, he, hy⟩
    · exact Or.inr ⟨e, he, hy⟩
  · rintro (⟨e, he, hy⟩ | ⟨e, he, hy⟩)
    · exact ⟨e, Or.inl he, hy⟩
    · exact ⟨e, Or.inr he, hy⟩

theorem mem_nbrsOf_runHist {A : OnlineAlg} {N : ℕ → Finset ℕ} {p y : ℕ} :
    y ∈ nbrsOf (runHist A N p) ↔ ∃ x < p, y ∈ N x := by
  rw [mem_nbrsOf, runHist_eq_map]
  constructor
  · rintro ⟨e, he, hy⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact ⟨x, List.mem_range.1 hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨_, List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩, hy⟩

/-- The colours of the vertices of block `s` outside `U`. -/
def rowOf (b : ℕ → ℕ) (h : History) (U : Finset ℕ) (s : ℕ) : Multiset ℕ :=
  ((blk b s) \ U).val.map (colourAt h)

/-- The rows of the blocks `t - 1, …, 0`. -/
def rowsOf (b : ℕ → ℕ) (h : History) (U : Finset ℕ) : ℕ → List (Multiset ℕ)
  | 0 => []
  | t + 1 => rowOf b h U t :: rowsOf b h U t

section Rows

variable {b : ℕ → ℕ} {h : History} {U : Finset ℕ} {srv : ℕ → ℕ} {t : ℕ}

theorem sdiff_union_image (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) {s : ℕ} (hs : s < t) :
    blk b s \ (U ∪ (range t).image srv) = (blk b s \ U).erase (srv s) := by
  ext y
  simp only [mem_sdiff, mem_union, mem_image, mem_range, mem_erase, not_or, not_exists, not_and]
  constructor
  · rintro ⟨hy, hyU, hynb⟩
    exact ⟨fun e => hynb s hs e.symm, hy, hyU⟩
  · rintro ⟨hne, hy, hyU⟩
    refine ⟨hy, hyU, fun s' hs' e => ?_⟩
    have hss : s' = s := eq_of_mem_blk (e ▸ (hsrv s' hs').1) hy
    subst hss
    exact hne e.symm

/-- Serving removes the colour of the server from the row of its block. -/
theorem rowOf_union (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) {s : ℕ} (hs : s < t) :
    rowOf b h (U ∪ (range t).image srv) s = (rowOf b h U s).erase (colourAt h (srv s)) := by
  rw [rowOf, rowOf, sdiff_union_image hsrv hs, erase_val, Multiset.map_erase_of_mem]
  exact mem_sdiff.2 (hsrv s hs)

theorem colourAt_mem_rowOf (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) {s : ℕ} (hs : s < t) :
    colourAt h (srv s) ∈ rowOf b h U s :=
  Multiset.mem_map_of_mem _ (mem_sdiff.2 (hsrv s hs))

/-- **Servers are picks.**  Choosing one unused vertex in each earlier block is a move of the
abstract game. -/
theorem picked_rowsOf (hsrv : ∀ s < t, srv s ∈ blk b s ∧ srv s ∉ U) :
    ∀ t0 ≤ t, Picked (rowsOf b h U t0) (rowsOf b h (U ∪ (range t).image srv) t0)
      (((range t0).image srv).image (colourAt h))
  | 0, _ => ⟨rfl, by simp⟩
  | t0 + 1, ht0 => by
    refine ⟨colourAt h (srv t0), colourAt_mem_rowOf hsrv ht0, _, _,
      picked_rowsOf hsrv t0 (Nat.le_of_succ_le ht0), ?_, ?_⟩
    · rw [rowsOf, rowOf_union hsrv ht0]
    · rw [range_add_one, image_insert, image_insert]

theorem rowOf_congr {h' : History} {s : ℕ}
    (hc : ∀ y ∈ blk b s, colourAt h y = colourAt h' y) : rowOf b h U s = rowOf b h' U s :=
  Multiset.map_congr rfl fun y hy => hc y (mem_sdiff.1 (Finset.mem_def.2 hy)).1

theorem rowsOf_congr {h' : History} :
    ∀ {t : ℕ}, (∀ y < start b t, colourAt h y = colourAt h' y) → rowsOf b h U t = rowsOf b h' U t
  | 0, _ => rfl
  | t + 1, hc => by
    rw [rowsOf, rowsOf, rowsOf_congr fun y hy => hc y (hy.trans_le (start_mono b (Nat.le_succ t))),
      rowOf_congr fun y hy => hc y (mem_blk.1 hy).2]

end Rows

/-! ### The algorithm -/

open Classical in
/-- The answer of the algorithm: a multiset for the next block from which it survives, if there
is one. -/
noncomputable def resp (C bt : ℕ) (bs : List ℕ) (rows' : List (Multiset ℕ)) (F : Finset ℕ) :
    Multiset ℕ :=
  if h : ∃ M : Multiset ℕ, M.card = bt ∧ (∀ c ∈ M, c < C ∧ c ∉ F) ∧ Surv C bs (M :: rows')
  then h.choose else 0

theorem resp_spec {C bt : ℕ} {bs : List ℕ} {rows rows' : List (Multiset ℕ)} {F : Finset ℕ}
    (hS : Surv C (bt :: bs) rows) (hP : Picked rows rows' F) :
    (resp C bt bs rows' F).card = bt ∧ (∀ c ∈ resp C bt bs rows' F, c < C ∧ c ∉ F) ∧
      Surv C bs (resp C bt bs rows' F :: rows') := by
  have h := hS rows' F hP
  simp only [resp, h, ↓reduceDIte]
  exact h.choose_spec

/-- One step of the algorithm: the vertex number `h.length` lies in block `t`; the position after
the adversary's picks is read off the history up to the start of the block and the
earlier-neighbour set `nb`; the vertex gets the colour with its number in the sorted answer. -/
noncomputable def stratStep (C m : ℕ) (b : ℕ → ℕ) (h : History) (nb : Finset ℕ) : ℕ :=
  ((resp C (b (blockOf b m h.length)) (sizesFrom m b (blockOf b m h.length + 1))
    (rowsOf b (h.take (start b (blockOf b m h.length)))
      (nbrsOf (h.take (start b (blockOf b m h.length))) ∪ nb) (blockOf b m h.length))
    (nb.image (colourAt (h.take (start b (blockOf b m h.length)))))).sort (· ≤ ·)).getD
      (h.length - start b (blockOf b m h.length)) 0

/-- The algorithm that follows a surviving strategy of the abstract game (made proper on all
histories by `OnlineAlg.patch`). -/
noncomputable def stratAlg (C m : ℕ) (b : ℕ → ℕ) : OnlineAlg :=
  (⟨stratStep C m b⟩ : OnlineAlg).patch

theorem mem_of_mem_sort {M : Multiset ℕ} {c : ℕ} (h : c ∈ M.sort (· ≤ ·)) : c ∈ M := by
  rw [← Multiset.sort_eq M (· ≤ ·)]
  exact Multiset.mem_coe.2 h

section Upper

variable {C m : ℕ} {b : ℕ → ℕ}

/-- The invariant of the play of `stratAlg` against a one-level input with nonempty blocks, if
the algorithm survives the abstract game: all colours belong to the palette, and the algorithm
survives from the abstract position at the start of every block. -/
theorem stratAlg_inv (hb1 : ∀ t < m, 1 ≤ b t) (hS : Surv C (sizesFrom m b 0) [])
    {N : ℕ → Finset ℕ} {srv : ℕ → ℕ → ℕ}
    (h1 : ∀ t < m, ∀ s < t, srv t s ∈ blk b s)
    (h2 : ∀ t < m, ∀ t' < m, ∀ s, s < t → s < t' → srv t s = srv t' s → t = t')
    (h3 : ∀ t < m, ∀ x ∈ blk b t, N x = (range t).image (srv t)) :
    ∀ t ≤ m, (∀ x < start b t, runCol (stratAlg C m b) N x < C) ∧
      Surv C (sizesFrom m b t) (rowsOf b (runHist (stratAlg C m b) N (start b t))
        (nbrsOf (runHist (stratAlg C m b) N (start b t))) t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun x hx => absurd hx (by simp [start]), hS⟩
  | succ t ih =>
    intro htm
    have ht : t < m := htm
    obtain ⟨hcol, hSurv⟩ := ih ht.le
    -- every earlier-neighbour set lies before its vertex's block
    have hNlt : ∀ t' < m, ∀ x ∈ blk b t', ∀ y ∈ N x, y < start b t' := by
      intro t' ht' x hx y hy
      rw [h3 t' ht' x hx, mem_image] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact lt_of_mem_blk (h1 t' ht' s (mem_range.1 hs)) (mem_range.1 hs)
    -- the servers of block `t` are unused
    have hsrv : ∀ s < t, srv t s ∈ blk b s ∧
        srv t s ∉ nbrsOf (runHist (stratAlg C m b) N (start b t)) := by
      intro s hs
      refine ⟨h1 t ht s hs, fun hmem => ?_⟩
      obtain ⟨x, hx, hy⟩ := mem_nbrsOf_runHist.1 hmem
      obtain ⟨t', ht', hxt'⟩ := exists_mem_blk hx
      rw [h3 t' (ht'.trans ht) x hxt', mem_image] at hy
      obtain ⟨s', hs', hss⟩ := hy
      rw [mem_range] at hs'
      have hs_eq : s' = s := eq_of_mem_blk (hss ▸ h1 t' (ht'.trans ht) s' hs') (h1 t ht s hs)
      subst hs_eq
      have := h2 t' (ht'.trans ht) t ht s' hs' hs hss
      omega
    have hnbsub : ∀ y ∈ (range t).image (srv t), y < start b t := by
      intro y hy
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hy
      exact lt_of_mem_blk (h1 t ht s (mem_range.1 hs)) (mem_range.1 hs)
    have hP := picked_rowsOf (h := runHist (stratAlg C m b) N (start b t)) hsrv t le_rfl
    rw [sizesFrom_of_lt b ht] at hSurv
    obtain ⟨hMc, hMF, hMS⟩ := resp_spec hSurv hP
    generalize hM : resp C (b t) (sizesFrom m b (t + 1))
      (rowsOf b (runHist (stratAlg C m b) N (start b t))
        (nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪ (range t).image (srv t)) t)
      (((range t).image (srv t)).image (colourAt (runHist (stratAlg C m b) N (start b t)))) = M
      at hMc hMF hMS
    have hidx : ∀ x ∈ blk b t, x - start b t < (M.sort (· ≤ ·)).length := by
      intro x hx
      rw [Multiset.length_sort, hMc]
      have h4 := (mem_blk.1 hx).2
      have h5 := (mem_blk.1 hx).1
      rw [start_succ] at h4
      omega
    have hin : ∀ x ∈ blk b t, (M.sort (· ≤ ·)).getD (x - start b t) 0 ∈ M := by
      intro x hx
      rw [List.getD_eq_getElem _ _ (hidx x hx)]
      exact mem_of_mem_sort (List.getElem_mem (hidx x hx))
    -- the colours of block `t`
    have hcolx : ∀ x ∈ blk b t,
        runCol (stratAlg C m b) N x = (M.sort (· ≤ ·)).getD (x - start b t) 0 := by
      intro x hx
      have hxa : start b t ≤ x := (mem_blk.1 hx).1
      have hstep : stratStep C m b (runHist (stratAlg C m b) N x) (N x) =
          (M.sort (· ≤ ·)).getD (x - start b t) 0 := by
        unfold stratStep
        simp only [length_runHist]
        rw [blockOf_of_mem ht hx, runHist_take hxa, h3 t ht x hx, hM]
      have hNx : N x ⊆ range x := fun y hy =>
        mem_range.2 ((hNlt t ht x hx y hy).trans_le hxa)
      have hnot : stratStep C m b (runHist (stratAlg C m b) N x) (N x) ∉
          nbrColours (runHist (stratAlg C m b) N x) (N x) := by
        rw [hstep, nbrColours_runHist hNx, h3 t ht x hx]
        intro hmem
        obtain ⟨y, hy, hyc⟩ := mem_image.1 hmem
        refine (hMF _ (hin x hx)).2 (mem_image.2 ⟨y, hy, ?_⟩)
        rw [colourAt_runHist (hnbsub y hy), hyc]
      change (if stratStep C m b _ _ ∈ nbrColours _ _ then _ else _) = _
      simp only [hnot, ↓reduceIte]
      exact hstep
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Nat.lt_or_ge x (start b t) with hlt | hge
      · exact hcol x hlt
      · have hxb : x ∈ blk b t := mem_blk.2 ⟨hge, hx⟩
        rw [hcolx x hxb]
        exact (hMF _ (hin x hxb)).1
    · have hU1 : nbrsOf (runHist (stratAlg C m b) N (start b (t + 1))) =
          nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪ (range t).image (srv t) := by
        ext y
        rw [mem_nbrsOf_runHist, mem_union, mem_nbrsOf_runHist]
        constructor
        · rintro ⟨x, hx, hy⟩
          rcases Nat.lt_or_ge x (start b t) with hlt | hge
          · exact Or.inl ⟨x, hlt, hy⟩
          · right
            rwa [h3 t ht x (mem_blk.2 ⟨hge, hx⟩)] at hy
        · rintro (⟨x, hx, hy⟩ | hy)
          · exact ⟨x, hx.trans_le (start_mono b (Nat.le_succ t)), hy⟩
          · have hmem : start b t ∈ blk b t := mem_blk.2 ⟨le_rfl, by
              rw [start_succ]
              have := hb1 t ht
              omega⟩
            exact ⟨start b t, (mem_blk.1 hmem).2, by rwa [h3 t ht _ hmem]⟩
      have hdisj : blk b t \ (nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪
          (range t).image (srv t)) = blk b t := by
        apply sdiff_eq_self_of_disjoint
        rw [disjoint_left]
        intro y hy hyU
        have hya : start b t ≤ y := (mem_blk.1 hy).1
        rcases mem_union.1 hyU with hyU | hyU
        · obtain ⟨x, hx, hyx⟩ := mem_nbrsOf_runHist.1 hyU
          obtain ⟨t', ht', hxt'⟩ := exists_mem_blk hx
          have := hNlt t' (ht'.trans ht) x hxt' y hyx
          have := start_mono b ht'.le
          omega
        · have := hnbsub y hyU
          omega
      have hrow : rowOf b (runHist (stratAlg C m b) N (start b (t + 1)))
          (nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪ (range t).image (srv t)) t = M := by
        rw [rowOf, hdisj, blk_val, Multiset.map_coe]
        have hlist : (List.range' (start b t) (b t)).map
            (colourAt (runHist (stratAlg C m b) N (start b (t + 1)))) = M.sort (· ≤ ·) := by
          have hlen : b t = (M.sort (· ≤ ·)).length := by rw [Multiset.length_sort, hMc]
          conv_rhs => rw [← map_range'_getD (M.sort (· ≤ ·)) (start b t), ← hlen]
          refine List.map_congr_left fun x hx => ?_
          rw [List.mem_range'_1] at hx
          have hxb : x ∈ blk b t := mem_blk.2 ⟨hx.1, by rw [start_succ]; exact hx.2⟩
          rw [colourAt_runHist (mem_blk.1 hxb).2, hcolx x hxb]
        rw [hlist, Multiset.sort_eq]
      have hrows : rowsOf b (runHist (stratAlg C m b) N (start b (t + 1)))
          (nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪ (range t).image (srv t)) t =
          rowsOf b (runHist (stratAlg C m b) N (start b t))
          (nbrsOf (runHist (stratAlg C m b) N (start b t)) ∪ (range t).image (srv t)) t :=
        rowsOf_congr fun y hy => by
          rw [colourAt_runHist (hy.trans_le (start_mono b (Nat.le_succ t))),
            colourAt_runHist hy]
      rw [rowsOf, hU1, hrow, hrows]
      exact hMS

/-- **Abstraction lemma, upper bounds.**  If the algorithm survives the abstract one-level game
with the palette of `C` colours, then no adversary that presents reservation blow-ups of `K_m`
with nonempty blocks of sizes `b` (one unused server in each earlier block) forces `C + 1`
colours. -/
theorem not_forces_of_surv (hb1 : ∀ t < m, 1 ≤ b t) (hS : Surv C (sizesFrom m b 0) [])
    {adv : Adversary} (hadv : IsOneLevelAdv m b adv) : ¬ adv.Forces (C + 1) := by
  intro hF
  have hA : (stratAlg C m b).IsProper := OnlineAlg.patch_isProper _
  obtain ⟨N, ⟨srv, h1, h2, h3⟩, hhist⟩ := hadv (stratAlg C m b) hA
  obtain ⟨p, -, hp⟩ := hF (stratAlg C m b) hA
  rw [hhist, usedColours_runHist] at hp
  have hcol := (stratAlg_inv hb1 hS h1 h2 h3 m le_rfl).1
  have hsub : (range (min p (start b m))).image (runCol (stratAlg C m b) N) ⊆ range C := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    exact mem_range.2 (hcol x (lt_of_lt_of_le (mem_range.1 hx) (min_le_right _ _)))
  have := card_le_card hsub
  rw [card_range] at this
  omega

end Upper

end Num

end OnlineColouring
