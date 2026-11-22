module

public import OnlineColouring.AdvBasic

/-!
# Theorem D.4 (top block)

Appendix D.4, paragraph "The top block of a one-level construction": *Consider adversaries that
present the clique `K_K` blown up once, where the adversary may use any number of servers per arc
and chooses block sizes online.  Let the budget `b_s` be the supremum, possibly infinite, of the
sizes of `σ(v_s)` over all plays. … Every such adversary that forces `K` colours has
`b_1 ≥ binom(K-1, 2) + 1`, and more generally `b_s ≥ binom(K-s, 2) + 1` for `1 ≤ s ≤ K`.*

An adversary of this kind is one with `IsTopBlockAdv β K adv`, where `β : History → ℕ` gives the
block (`0, …, K-1`) of the next vertex: in every play the blocks arrive one after the other
(`TopForm.mono`), the vertices of a block have the same earlier neighbours (`same`), which lie in
earlier blocks (`nbr`), and a vertex serves at most one block (`once`).  Blocks may be empty and an
arc may have any number of servers, including none; this class contains the adversaries of the
paper, so the theorem is proved for a larger class.  The class is not vacuous: by
`top_block_witness` (`AppBDWitness.lean`), the adversary of Theorem 6.4 with one level belongs to
it and forces `K` colours.

`top_block`: if such an adversary forces `K` colours and `1 ≤ s ≤ K`, then in some play against
some proper algorithm the block of `v_s` has at least `binom(K-s, 2) + 1` vertices.

The proof is the paper's: the algorithm `topAlg β K (s-1)` gives the blocks before `v_s` their own
colours, colours the block of `v_s` in a staircase, and colours every later block with one colour
(a fresh colour of the staircase with the most unserved vertices if one is allowed, otherwise an
allowed colour in use, otherwise a new colour); the invariant `h(r) ≤ max(0, g + ρ - 1 - r)` is
`J.i1`.  One uniform argument covers all `s`: for `s ≥ K - 1` the staircase is empty and the
invariant gives `b_s ≥ 1`, which the paper derives from First-Fit.  The count of the rounds of
types (a) and (b) is the invariant `J.i3` (the number of colours in use is at most the number of
fresh colours plus the number of later blocks that have started).

The sentence after the theorem, about an exhaustive search for small `K`, reports a test of the
theorem and has no formal counterpart.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-! ### Histories of one-level blow-ups of `K_K` -/

section Form

variable (β : History → ℕ)

/-- The block of vertex `i` of the history `h`. -/
def bidx (h : History) (i : ℕ) : ℕ := β (h.take i)

/-- The earlier neighbours of vertex `i` of the history `h`. -/
def nb (h : History) (i : ℕ) : Finset ℕ := (h.getD i (∅, 0)).1

/-- The history `h` is a one-level blow-up of (a subgraph of) `K_K` with the blocks given by `β`:
the blocks `0, …, K-1` arrive in this order; the vertices of a block have the same earlier
neighbours, all in earlier blocks; every vertex serves at most one block. -/
structure TopForm (K : ℕ) (h : History) : Prop where
  lt : ∀ i < h.length, bidx β h i < K
  mono : ∀ i j, i ≤ j → j < h.length → bidx β h i ≤ bidx β h j
  same : ∀ i j, i < h.length → j < h.length → bidx β h i = bidx β h j → nb h i = nb h j
  nbr : ∀ i < h.length, ∀ u ∈ nb h i, u < i ∧ bidx β h u < bidx β h i
  once : ∀ i j, i < h.length → j < h.length → ∀ u, u ∈ nb h i → u ∈ nb h j →
    bidx β h i = bidx β h j

/-- An adversary that presents `K_K` blown up once, with any number of servers per arc and block
sizes chosen online; `β` names the block of the next vertex. -/
def IsTopBlockAdv (K : ℕ) (adv : Adversary) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, TopForm β K (adv.hist A p)

/-- The number of vertices of block `s` in the history `h`. -/
def blockCard (h : History) (s : ℕ) : ℕ :=
  ((range h.length).filter fun i => bidx β h i = s).card

variable {β}

theorem bidx_snoc {h : History} {x : Finset ℕ × ℕ} {i : ℕ} (hi : i ≤ h.length) :
    bidx β (h ++ [x]) i = bidx β h i := by
  unfold bidx
  rw [List.take_append_of_le_length hi]

theorem bidx_length (h : History) : bidx β h h.length = β h := by
  unfold bidx
  rw [List.take_length]

theorem nb_snoc_lt {h : History} {x : Finset ℕ × ℕ} {i : ℕ} (hi : i < h.length) :
    nb (h ++ [x]) i = nb h i := by
  simp [nb, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem nb_snoc_self {h : History} {x : Finset ℕ × ℕ} : nb (h ++ [x]) h.length = x.1 := by
  simp [nb, List.getD_eq_getElem?_getD]

theorem colourAt_snoc_lt {h : History} {x : Finset ℕ × ℕ} {i : ℕ} (hi : i < h.length) :
    colourAt (h ++ [x]) i = colourAt h i := by
  simp [colourAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem colourAt_snoc_self {h : History} {x : Finset ℕ × ℕ} :
    colourAt (h ++ [x]) h.length = x.2 := by
  simp [colourAt, List.getD_eq_getElem?_getD]

theorem mem_nbrColours {h : History} {s : Finset ℕ} {q : ℕ} :
    q ∈ nbrColours h s ↔ ∃ u ∈ s, u < h.length ∧ colourAt h u = q := by
  simp [nbrColours, and_assoc]

/-- What the form of `h ++ [(s, c)]` says about the new vertex. -/
structure SnocFacts (β : History → ℕ) (K : ℕ) (h : History) (s : Finset ℕ) : Prop where
  ft : β h < K
  flt : ∀ i < h.length, bidx β h i < K
  fmono : ∀ i < h.length, bidx β h i ≤ β h
  fmono' : ∀ i j, i ≤ j → j < h.length → bidx β h i ≤ bidx β h j
  fsame : ∀ i < h.length, bidx β h i = β h → nb h i = s
  fnbr : ∀ u ∈ s, u < h.length ∧ bidx β h u < β h
  fnbr' : ∀ i < h.length, ∀ u ∈ nb h i, u < i
  fonce : ∀ i < h.length, ∀ u ∈ s, u ∈ nb h i → bidx β h i = β h

theorem TopForm.snocFacts {K : ℕ} {h : History} {s : Finset ℕ} {c : ℕ}
    (hf : TopForm β K (h ++ [(s, c)])) : SnocFacts β K h s := by
  have hlen : (h ++ [(s, c)]).length = h.length + 1 := by simp
  have hn : h.length < (h ++ [(s, c)]).length := by omega
  have hlt : ∀ i < h.length, i < (h ++ [(s, c)]).length := fun i hi => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hf.lt _ hn
    rwa [bidx_snoc le_rfl, bidx_length] at this
  · intro i hi
    have := hf.lt i (hlt i hi)
    rwa [bidx_snoc hi.le] at this
  · intro i hi
    have := hf.mono i h.length hi.le hn
    rwa [bidx_snoc hi.le, bidx_snoc le_rfl, bidx_length] at this
  · intro i j hij hj
    have := hf.mono i j hij (hlt j hj)
    rwa [bidx_snoc (hij.trans hj.le), bidx_snoc hj.le] at this
  · intro i hi hb
    have := hf.same i h.length (hlt i hi) hn (by rw [bidx_snoc hi.le, bidx_snoc le_rfl,
      bidx_length, hb])
    rwa [nb_snoc_lt hi, nb_snoc_self] at this
  · intro u hu
    have := hf.nbr _ hn u (by rw [nb_snoc_self]; exact hu)
    rwa [bidx_snoc this.1.le, bidx_snoc le_rfl, bidx_length] at this
  · intro i hi u hu
    exact (hf.nbr i (hlt i hi) u (by rw [nb_snoc_lt hi]; exact hu)).1
  · intro i hi u hu hui
    have := hf.once i h.length (hlt i hi) hn u (by rw [nb_snoc_lt hi]; exact hui)
      (by rw [nb_snoc_self]; exact hu)
    rwa [bidx_snoc hi.le, bidx_snoc le_rfl, bidx_length] at this

end Form

/-! ### The quantities of the proof -/

section State

variable (β : History → ℕ) (s0 : ℕ)

/-- The vertices of block `s0` (the block `σ(v_s)` whose size is bounded). -/
def topSet (h : History) : Finset ℕ := (range h.length).filter fun i => bidx β h i = s0

/-- The vertices of the later blocks. -/
def lateSet (h : History) : Finset ℕ := (range h.length).filter fun i => s0 < bidx β h i

/-- `Q`: the colours used on block `s0`. -/
def Qc (h : History) : Finset ℕ := (topSet β s0 h).image (colourAt h)

/-- The colours used by the later blocks. -/
def Lc (h : History) : Finset ℕ := (lateSet β s0 h).image (colourAt h)

/-- The fresh colours: colours of `Q` that no later block has used. -/
def Fr (h : History) : Finset ℕ := Qc β s0 h \ Lc β s0 h

/-- The colours in use (on the blocks from `s0` on). -/
def Us (h : History) : Finset ℕ := Qc β s0 h ∪ Lc β s0 h

/-- The later blocks that have started. -/
def Dl (h : History) : Finset ℕ := (lateSet β s0 h).image (bidx β h)

/-- The number of vertices of colour `q` in block `s0`. -/
def cnt (h : History) (q : ℕ) : ℕ := ((topSet β s0 h).filter fun i => colourAt h i = q).card

/-- The vertices of colour `q` in block `s0` that have not served. -/
def Mset (h : History) (q : ℕ) : Finset ℕ :=
  (topSet β s0 h).filter fun i => colourAt h i = q ∧ ∀ j ∈ range h.length, i ∉ nb h j

/-- `m_q`: the number of vertices of colour `q` in block `s0` that have not served. -/
def Mq (h : History) (q : ℕ) : ℕ := (Mset β s0 h q).card

/-- The paper's `h(r)`, with `r = v`: the number of fresh colours `q` with `m_q ≥ v`. -/
def hcount (h : History) (v : ℕ) : ℕ := ((Fr β s0 h).filter fun q => v ≤ Mq β s0 h q).card

variable {β s0}

theorem filter_snoc (P : ℕ → Prop) [DecidablePred P] (h : History) (x : Finset ℕ × ℕ) :
    ((range (h ++ [x]).length).filter fun i => P (bidx β (h ++ [x]) i)) =
      if P (β h) then insert h.length ((range h.length).filter fun i => P (bidx β h i))
      else (range h.length).filter fun i => P (bidx β h i) := by
  have e : (h ++ [x]).length = h.length + 1 := by simp
  have e2 : ((range h.length).filter fun i => P (bidx β (h ++ [x]) i))
      = (range h.length).filter fun i => P (bidx β h i) :=
    filter_congr fun i hi => by rw [bidx_snoc (mem_range.1 hi).le]
  rw [e, range_add_one, filter_insert, bidx_snoc le_rfl, bidx_length, e2]

variable {h : History} {x : Finset ℕ × ℕ}

theorem topSet_lt {i : ℕ} (hi : i ∈ topSet β s0 h) : i < h.length :=
  mem_range.1 (mem_filter.1 hi).1

theorem lateSet_lt {i : ℕ} (hi : i ∈ lateSet β s0 h) : i < h.length :=
  mem_range.1 (mem_filter.1 hi).1

theorem topSet_snoc_ne (ht : β h ≠ s0) : topSet β s0 (h ++ [x]) = topSet β s0 h := by
  unfold topSet
  rw [filter_snoc (fun t => t = s0) h x]
  simp only [ht, ↓reduceIte]

theorem topSet_snoc_eq (ht : β h = s0) :
    topSet β s0 (h ++ [x]) = insert h.length (topSet β s0 h) := by
  unfold topSet
  rw [filter_snoc (fun t => t = s0) h x]
  simp only [ht, ↓reduceIte]

theorem lateSet_snoc_le (ht : β h ≤ s0) : lateSet β s0 (h ++ [x]) = lateSet β s0 h := by
  unfold lateSet
  rw [filter_snoc (fun t => s0 < t) h x]
  simp only [not_lt.2 ht, ↓reduceIte]

theorem lateSet_snoc_lt (ht : s0 < β h) :
    lateSet β s0 (h ++ [x]) = insert h.length (lateSet β s0 h) := by
  unfold lateSet
  rw [filter_snoc (fun t => s0 < t) h x]
  simp only [ht, ↓reduceIte]

theorem image_colourAt_snoc {S : Finset ℕ} (hS : ∀ i ∈ S, i < h.length) :
    S.image (colourAt (h ++ [x])) = S.image (colourAt h) :=
  image_congr fun i hi => colourAt_snoc_lt (hS i hi)

theorem image_bidx_snoc {S : Finset ℕ} (hS : ∀ i ∈ S, i < h.length) :
    S.image (bidx β (h ++ [x])) = S.image (bidx β h) :=
  image_congr fun i hi => bidx_snoc (hS i hi).le

theorem Qc_snoc_ne (ht : β h ≠ s0) : Qc β s0 (h ++ [x]) = Qc β s0 h := by
  rw [Qc, topSet_snoc_ne ht, image_colourAt_snoc fun i => topSet_lt]
  rfl

theorem Qc_snoc_eq (ht : β h = s0) : Qc β s0 (h ++ [x]) = insert x.2 (Qc β s0 h) := by
  rw [Qc, topSet_snoc_eq ht, image_insert, colourAt_snoc_self,
    image_colourAt_snoc fun i => topSet_lt]
  rfl

theorem Lc_snoc_le (ht : β h ≤ s0) : Lc β s0 (h ++ [x]) = Lc β s0 h := by
  rw [Lc, lateSet_snoc_le ht, image_colourAt_snoc fun i => lateSet_lt]
  rfl

theorem Lc_snoc_lt (ht : s0 < β h) : Lc β s0 (h ++ [x]) = insert x.2 (Lc β s0 h) := by
  rw [Lc, lateSet_snoc_lt ht, image_insert, colourAt_snoc_self,
    image_colourAt_snoc fun i => lateSet_lt]
  rfl

theorem Dl_snoc_le (ht : β h ≤ s0) : Dl β s0 (h ++ [x]) = Dl β s0 h := by
  rw [Dl, lateSet_snoc_le ht, image_bidx_snoc fun i => lateSet_lt]
  rfl

theorem Dl_snoc_lt (ht : s0 < β h) : Dl β s0 (h ++ [x]) = insert (β h) (Dl β s0 h) := by
  rw [Dl, lateSet_snoc_lt ht, image_insert, bidx_snoc le_rfl, bidx_length,
    image_bidx_snoc fun i => lateSet_lt]
  rfl

theorem cnt_snoc_ne (ht : β h ≠ s0) (q : ℕ) : cnt β s0 (h ++ [x]) q = cnt β s0 h q := by
  rw [cnt, topSet_snoc_ne ht]
  exact congrArg card (filter_congr fun i hi => by rw [colourAt_snoc_lt (topSet_lt hi)])

theorem cnt_snoc_eq (ht : β h = s0) (q : ℕ) :
    cnt β s0 (h ++ [x]) q = cnt β s0 h q + if x.2 = q then 1 else 0 := by
  have e : ((topSet β s0 h).filter fun i => colourAt (h ++ [x]) i = q)
      = (topSet β s0 h).filter fun i => colourAt h i = q :=
    filter_congr fun i hi => by rw [colourAt_snoc_lt (topSet_lt hi)]
  rw [cnt, topSet_snoc_eq ht, filter_insert, colourAt_snoc_self, e]
  split_ifs with hq
  · rw [card_insert_of_notMem fun hm => lt_irrefl _ (topSet_lt (mem_filter.1 hm).1)]
    rfl
  · rfl

theorem Mset_snoc_subset (ht : β h ≠ s0) (q : ℕ) : Mset β s0 (h ++ [x]) q ⊆ Mset β s0 h q := by
  intro i hi
  rw [Mset, topSet_snoc_ne ht, mem_filter] at hi
  have hin := topSet_lt hi.1
  refine mem_filter.2 ⟨hi.1, ?_, fun j hj => ?_⟩
  · rw [← colourAt_snoc_lt hin]
    exact hi.2.1
  · rw [mem_range] at hj
    rw [← nb_snoc_lt hj]
    exact hi.2.2 j (mem_range.2 (by simp; omega))

theorem Mq_snoc_le (ht : β h ≠ s0) (q : ℕ) : Mq β s0 (h ++ [x]) q ≤ Mq β s0 h q :=
  card_le_card (Mset_snoc_subset ht q)

theorem Mq_le_cnt (h : History) (q : ℕ) : Mq β s0 h q ≤ cnt β s0 h q :=
  card_le_card fun _ hi => mem_filter.2 ⟨(mem_filter.1 hi).1, (mem_filter.1 hi).2.1⟩

theorem hcount_le {h h' : History} (hFr : Fr β s0 h' ⊆ Fr β s0 h)
    (hM : ∀ q, Mq β s0 h' q ≤ Mq β s0 h q) (v : ℕ) : hcount β s0 h' v ≤ hcount β s0 h v :=
  card_le_card fun q hq =>
    mem_filter.2 ⟨hFr (mem_filter.1 hq).1, (mem_filter.1 hq).2.trans (hM q)⟩

theorem hcount_shift {h h' : History} (hFr : Fr β s0 h' ⊆ Fr β s0 h)
    (hM : ∀ q ∈ Fr β s0 h', Mq β s0 h' q + 1 ≤ Mq β s0 h q) (v : ℕ) :
    hcount β s0 h' v ≤ hcount β s0 h (v + 1) :=
  card_le_card fun q hq => by
    have := hM q (mem_filter.1 hq).1
    have := (mem_filter.1 hq).2
    exact mem_filter.2 ⟨hFr (mem_filter.1 hq).1, by omega⟩

end State

/-! ### The invariant -/

section Invariant

variable {β : History → ℕ} {K s0 : ℕ}

/-- The invariant of the proof of Theorem D.4.  `colLow`: the blocks before `s0` have their own
colours.  `stair`, `cap`: block `s0` is coloured in a staircase, colour `s0 + j` on at most
`K - s0 - 2 - j` vertices.  `i1`: the paper's invariant `h(r) ≤ max(0, g + ρ - 1 - r)`, with
`g = K - s0 - |Us|` and `ρ = |Fr|`.  `i2`: fewer than `K - s0` colours are in use.  `i3`: the
number of colours in use is at most the number of fresh colours plus the number of later blocks
that have started. -/
structure J (β : History → ℕ) (K s0 : ℕ) (h : History) : Prop where
  colLow : ∀ i < h.length, bidx β h i < s0 → colourAt h i = bidx β h i
  stair : ∀ i ∈ topSet β s0 h, ∃ j < K - s0 - 2, colourAt h i = s0 + j
  cap : ∀ j, cnt β s0 h (s0 + j) ≤ K - s0 - 2 - j
  i1 : ∀ v, 1 ≤ v →
    hcount β s0 h v ≤ (K - s0 - (Us β s0 h).card) + (Fr β s0 h).card - 1 - v
  i2 : (Us β s0 h).card + 1 ≤ K - s0
  i3 : (Us β s0 h).card ≤ (Fr β s0 h).card + (Dl β s0 h).card

/-- While no later block has started, the invariant is the staircase property. -/
theorem J.of_top {h : History} (hs0 : s0 < K)
    (hlow : ∀ i < h.length, bidx β h i < s0 → colourAt h i = bidx β h i)
    (hstair : ∀ i ∈ topSet β s0 h, ∃ j < K - s0 - 2, colourAt h i = s0 + j)
    (hcap : ∀ j, cnt β s0 h (s0 + j) ≤ K - s0 - 2 - j)
    (hlate : lateSet β s0 h = ∅) : J β K s0 h := by
  have hLc : Lc β s0 h = ∅ := by rw [Lc, hlate, image_empty]
  have hD : Dl β s0 h = ∅ := by rw [Dl, hlate, image_empty]
  have hFr : Fr β s0 h = Qc β s0 h := by rw [Fr, hLc, sdiff_empty]
  have hUs : Us β s0 h = Qc β s0 h := by rw [Us, hLc, union_empty]
  have hQ : Qc β s0 h ⊆ (range (K - s0 - 2)).image (s0 + ·) := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hq
    obtain ⟨j, hj, e⟩ := hstair i hi
    exact mem_image.2 ⟨j, mem_range.2 hj, e.symm⟩
  have hQcard : (Qc β s0 h).card ≤ K - s0 - 2 :=
    (card_le_card hQ).trans (card_image_le.trans (card_range _).le)
  refine ⟨hlow, hstair, hcap, fun v hv => ?_, ?_, ?_⟩
  · have hh : hcount β s0 h v ≤ K - s0 - 2 + 1 - v := by
      unfold hcount
      rw [hFr]
      have hsub : ((Qc β s0 h).filter fun q => v ≤ Mq β s0 h q)
          ⊆ (range (K - s0 - 2 + 1 - v)).image (s0 + ·) := by
        intro q hq
        rw [mem_filter] at hq
        obtain ⟨j, hj, rfl⟩ := mem_image.1 (hQ hq.1)
        have := hq.2.trans ((Mq_le_cnt h _).trans (hcap j))
        rw [mem_range] at hj
        exact mem_image.2 ⟨j, mem_range.2 (by omega), rfl⟩
      exact (card_le_card hsub).trans (card_image_le.trans (card_range _).le)
    rw [hUs, hFr]
    omega
  · rw [hUs]
    omega
  · rw [hUs, hFr]
    omega

theorem J.nil (hs0 : s0 < K) : J β K s0 [] :=
  J.of_top hs0 (by simp) (by simp [topSet]) (by simp [cnt, topSet]) (by simp [lateSet])

theorem colLow_snoc {h : History} {s : Finset ℕ} {c : ℕ} (hJ : J β K s0 h)
    (hc : β h < s0 → c = β h) :
    ∀ i < (h ++ [(s, c)]).length, bidx β (h ++ [(s, c)]) i < s0 →
      colourAt (h ++ [(s, c)]) i = bidx β (h ++ [(s, c)]) i := by
  intro i hi hb
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rw [bidx_snoc hi.le] at hb
    rw [colourAt_snoc_lt hi, bidx_snoc hi.le]
    exact hJ.colLow i hi hb
  · rw [bidx_snoc le_rfl, bidx_length] at hb
    rw [colourAt_snoc_self, bidx_snoc le_rfl, bidx_length]
    exact hc hb

theorem Fr_snoc_ne_le {h : History} {x : Finset ℕ × ℕ} (ht : β h < s0) :
    Fr β s0 (h ++ [x]) = Fr β s0 h := by
  rw [Fr, Qc_snoc_ne ht.ne, Lc_snoc_le ht.le]
  rfl

theorem Us_snoc_ne_le {h : History} {x : Finset ℕ × ℕ} (ht : β h < s0) :
    Us β s0 (h ++ [x]) = Us β s0 h := by
  rw [Us, Qc_snoc_ne ht.ne, Lc_snoc_le ht.le]
  rfl

/-- A vertex of a block before `s0` gets the colour of its block. -/
theorem J.snoc_low {h : History} {s : Finset ℕ} (hJ : J β K s0 h) (ht : β h < s0) :
    J β K s0 (h ++ [(s, β h)]) := by
  have hFr := Fr_snoc_ne_le (x := (s, β h)) ht
  have hUs := Us_snoc_ne_le (x := (s, β h)) ht
  refine ⟨colLow_snoc hJ fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [topSet_snoc_ne ht.ne] at hi
    rw [colourAt_snoc_lt (topSet_lt hi)]
    exact hJ.stair i hi
  · intro j
    rw [cnt_snoc_ne ht.ne]
    exact hJ.cap j
  · intro v hv
    rw [hUs, hFr]
    exact (hcount_le hFr.subset (Mq_snoc_le ht.ne) v).trans (hJ.i1 v hv)
  · rw [hUs]
    exact hJ.i2
  · rw [hUs, hFr, Dl_snoc_le ht.le]
    exact hJ.i3

/-- A vertex of block `s0` gets a staircase colour with spare capacity. -/
theorem J.snoc_top {h : History} {s : Finset ℕ} (hJ : J β K s0 h) (hs0 : s0 < K)
    (F : SnocFacts β K h s) (ht : β h = s0) {j : ℕ} (hj : j < K - s0 - 2)
    (hcap : cnt β s0 h (s0 + j) < K - s0 - 2 - j) : J β K s0 (h ++ [(s, s0 + j)]) := by
  refine J.of_top hs0 (colLow_snoc hJ fun hlt => absurd ht hlt.ne) ?_ ?_ ?_
  · intro i hi
    rw [topSet_snoc_eq ht, mem_insert] at hi
    rcases hi with rfl | hi
    · exact ⟨j, hj, colourAt_snoc_self⟩
    · rw [colourAt_snoc_lt (topSet_lt hi)]
      exact hJ.stair i hi
  · intro j'
    rw [cnt_snoc_eq ht]
    have := hJ.cap j'
    by_cases e : j = j'
    · subst e
      simp only [↓reduceIte]
      omega
    · have : ¬ (s0 + j = s0 + j') := by omega
      simp only [this, ↓reduceIte]
      omega
  · rw [lateSet_snoc_le ht.le]
    exact filter_eq_empty_iff.2 fun i hi => by
      have := F.fmono i (mem_range.1 hi)
      omega

theorem Fr_snoc_lt {h : History} {x : Finset ℕ × ℕ} (ht : s0 < β h) :
    Fr β s0 (h ++ [x]) = (Fr β s0 h).erase x.2 := by
  rw [Fr, Qc_snoc_ne ht.ne', Lc_snoc_lt ht]
  ext q
  simp only [Fr, mem_sdiff, mem_insert, mem_erase]
  tauto

theorem Us_snoc_lt {h : History} {x : Finset ℕ × ℕ} (ht : s0 < β h) :
    Us β s0 (h ++ [x]) = insert x.2 (Us β s0 h) := by
  rw [Us, Qc_snoc_ne ht.ne', Lc_snoc_lt ht, union_insert]
  rfl

theorem J.snoc_late {h : History} {s : Finset ℕ} {c : ℕ} (hJ : J β K s0 h) (ht : s0 < β h)
    (h1 : ∀ v, 1 ≤ v → hcount β s0 (h ++ [(s, c)]) v ≤
      (K - s0 - (Us β s0 (h ++ [(s, c)])).card) + (Fr β s0 (h ++ [(s, c)])).card - 1 - v)
    (h2 : (Us β s0 (h ++ [(s, c)])).card + 1 ≤ K - s0)
    (h3 : (Us β s0 (h ++ [(s, c)])).card
      ≤ (Fr β s0 (h ++ [(s, c)])).card + (Dl β s0 (h ++ [(s, c)])).card) :
    J β K s0 (h ++ [(s, c)]) := by
  refine ⟨colLow_snoc hJ fun hlt => absurd hlt (by omega), ?_, ?_, h1, h2, h3⟩
  · intro i hi
    rw [topSet_snoc_ne ht.ne'] at hi
    rw [colourAt_snoc_lt (topSet_lt hi)]
    exact hJ.stair i hi
  · intro j
    rw [cnt_snoc_ne ht.ne']
    exact hJ.cap j

/-- A fresh colour that is shown to the first vertex of a later block loses an unserved vertex. -/
theorem Mq_drop {h : History} {s : Finset ℕ} (hJ : J β K s0 h) (F : SnocFacts β K h s)
    (ht : s0 < β h) (hnew : β h ∉ Dl β s0 h) {q : ℕ} (hq : q ∈ Fr β s0 h)
    (hqF : q ∈ nbrColours h s) (c : ℕ) :
    Mq β s0 (h ++ [(s, c)]) q + 1 ≤ Mq β s0 h q := by
  obtain ⟨u, hus, hun, huq⟩ := mem_nbrColours.1 hqF
  rw [Fr, mem_sdiff] at hq
  obtain ⟨i, hi, hiq⟩ := mem_image.1 hq.1
  obtain ⟨j, hj, hij⟩ := hJ.stair i hi
  have hub : bidx β h u = s0 := by
    rcases lt_trichotomy (bidx β h u) s0 with hlt | heq | hgt
    · have := hJ.colLow u hun hlt
      omega
    · exact heq
    · exact absurd (mem_image.2 ⟨u, mem_filter.2 ⟨mem_range.2 hun, hgt⟩, huq⟩) hq.2
  have huM : u ∈ Mset β s0 h q := by
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_range.2 hun, hub⟩, huq, fun j' hj' hmem => hnew ?_⟩
    have e := F.fonce j' (mem_range.1 hj') u hus hmem
    exact mem_image.2 ⟨j', mem_filter.2 ⟨hj', by omega⟩, e⟩
  have hsub : Mset β s0 (h ++ [(s, c)]) q ⊆ (Mset β s0 h q).erase u := by
    intro i' hi'
    refine mem_erase.2 ⟨?_, Mset_snoc_subset ht.ne' q hi'⟩
    rintro rfl
    have := (mem_filter.1 hi').2.2 h.length (mem_range.2 (by simp))
    rw [nb_snoc_self] at this
    exact this hus
  have := card_le_card hsub
  rw [card_erase_of_mem huM] at this
  have hpos := card_pos.2 ⟨u, huM⟩
  unfold Mq
  omega

/-- A vertex of a later block that gets a colour already used by a later block (a later vertex
of its block, or a round of type (c)). -/
theorem J.snoc_late_used {h : History} {s : Finset ℕ} {c : ℕ} (hJ : J β K s0 h)
    (ht : s0 < β h) (hc : c ∈ Lc β s0 h) : J β K s0 (h ++ [(s, c)]) := by
  have hFr : Fr β s0 (h ++ [(s, c)]) = Fr β s0 h := by
    rw [Fr_snoc_lt ht]
    exact erase_eq_of_notMem fun hm => (mem_sdiff.1 hm).2 hc
  have hUs : Us β s0 (h ++ [(s, c)]) = Us β s0 h := by
    rw [Us_snoc_lt ht]
    exact insert_eq_of_mem (mem_union_right _ hc)
  have hD : (Dl β s0 h).card ≤ (Dl β s0 (h ++ [(s, c)])).card := by
    rw [Dl_snoc_lt ht]
    exact card_le_card (subset_insert _ _)
  refine hJ.snoc_late ht ?_ ?_ ?_
  · intro v hv
    rw [hUs, hFr]
    exact (hcount_le hFr.subset (Mq_snoc_le ht.ne') v).trans (hJ.i1 v hv)
  · rw [hUs]
    exact hJ.i2
  · rw [hUs, hFr]
    exact hJ.i3.trans (by omega)

/-- A round of type (b): the first vertex of a later block takes an allowed fresh colour with the
most unserved vertices. -/
theorem J.snoc_late_fresh {h : History} {s : Finset ℕ} {c : ℕ} (hJ : J β K s0 h)
    (F : SnocFacts β K h s) (ht : s0 < β h) (hnew : β h ∉ Dl β s0 h) (hc : c ∈ Fr β s0 h)
    (hmax : ∀ q ∈ Fr β s0 h, q ∉ nbrColours h s → Mq β s0 h q ≤ Mq β s0 h c) :
    J β K s0 (h ++ [(s, c)]) := by
  have hFr := Fr_snoc_lt (x := (s, c)) ht
  have hFrcard : (Fr β s0 (h ++ [(s, c)])).card + 1 = (Fr β s0 h).card := by
    rw [hFr, card_erase_of_mem hc]
    have := card_pos.2 ⟨c, hc⟩
    omega
  have hUs : Us β s0 (h ++ [(s, c)]) = Us β s0 h := by
    rw [Us_snoc_lt ht]
    exact insert_eq_of_mem (mem_union_left _ (mem_sdiff.1 hc).1)
  have hD : (Dl β s0 (h ++ [(s, c)])).card = (Dl β s0 h).card + 1 := by
    rw [Dl_snoc_lt ht, card_insert_of_notMem hnew]
  refine hJ.snoc_late ht ?_ ?_ ?_
  · intro v hv
    rw [hUs]
    have hi1 := hJ.i1 v hv
    by_cases hvc : v ≤ Mq β s0 h c
    · have hsub : ((Fr β s0 (h ++ [(s, c)])).filter fun q => v ≤ Mq β s0 (h ++ [(s, c)]) q)
          ⊆ ((Fr β s0 h).filter fun q => v ≤ Mq β s0 h q).erase c := by
        intro q hq
        rw [mem_filter, hFr, mem_erase] at hq
        exact mem_erase.2 ⟨hq.1.1, mem_filter.2 ⟨hq.1.2, hq.2.trans (Mq_snoc_le ht.ne' q)⟩⟩
      have hcm : c ∈ (Fr β s0 h).filter fun q => v ≤ Mq β s0 h q := mem_filter.2 ⟨hc, hvc⟩
      have hle := card_le_card hsub
      rw [card_erase_of_mem hcm] at hle
      have hpos := card_pos.2 ⟨c, hcm⟩
      unfold hcount at hi1 ⊢
      omega
    · have hsub : ((Fr β s0 (h ++ [(s, c)])).filter fun q => v ≤ Mq β s0 (h ++ [(s, c)]) q)
          ⊆ (Fr β s0 h).filter fun q => v + 1 ≤ Mq β s0 h q := by
        intro q hq
        rw [mem_filter, hFr, mem_erase] at hq
        refine mem_filter.2 ⟨hq.1.2, ?_⟩
        by_cases hqF : q ∈ nbrColours h s
        · have := Mq_drop hJ F ht hnew hq.1.2 hqF c
          omega
        · have := hmax q hq.1.2 hqF
          have := Mq_snoc_le (x := (s, c)) ht.ne' q
          omega
      have hle := card_le_card hsub
      have hi1' := hJ.i1 (v + 1) (by omega)
      unfold hcount at hi1' ⊢
      omega
  · rw [hUs]
    exact hJ.i2
  · rw [hUs]
    have := hJ.i3
    omega

/-- A round of type (a): every colour in use is forbidden and the block takes a new colour.  This
cannot happen when only one colour is left. -/
theorem J.snoc_late_new {h : History} {s : Finset ℕ} {c : ℕ} (hJ : J β K s0 h)
    (F : SnocFacts β K h s) (ht : s0 < β h) (hnew : β h ∉ Dl β s0 h)
    (hall : ∀ q ∈ Us β s0 h, q ∈ nbrColours h s) (hc : c ∉ Us β s0 h) :
    J β K s0 (h ++ [(s, c)]) := by
  have hFr : Fr β s0 (h ++ [(s, c)]) = Fr β s0 h := by
    rw [Fr_snoc_lt ht]
    exact erase_eq_of_notMem fun hm => hc (mem_union_left _ (mem_sdiff.1 hm).1)
  have hUs : (Us β s0 (h ++ [(s, c)])).card = (Us β s0 h).card + 1 := by
    rw [Us_snoc_lt ht, card_insert_of_notMem hc]
  have hD : (Dl β s0 (h ++ [(s, c)])).card = (Dl β s0 h).card + 1 := by
    rw [Dl_snoc_lt ht, card_insert_of_notMem hnew]
  have hdrop : ∀ q ∈ Fr β s0 h, Mq β s0 (h ++ [(s, c)]) q + 1 ≤ Mq β s0 h q := fun q hq =>
    Mq_drop hJ F ht hnew hq (hall q (mem_union_left _ (mem_sdiff.1 hq).1)) c
  have hDcard : (Dl β s0 h).card + 2 ≤ K - s0 := by
    have hsub : Dl β s0 h ⊆ (Ioo s0 K).erase (β h) := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hd
      rw [lateSet, mem_filter, mem_range] at hi
      exact mem_erase.2 ⟨fun e => hnew (e ▸ hd), mem_Ioo.2 ⟨hi.2, F.flt i hi.1⟩⟩
    have hle := card_le_card hsub
    rw [card_erase_of_mem (mem_Ioo.2 ⟨ht, F.ft⟩), Nat.card_Ioo] at hle
    have := F.ft
    omega
  have key : (Us β s0 h).card + 2 ≤ K - s0 := by
    by_contra hcon
    have h2 := hJ.i2
    have h3 := hJ.i3
    have h1 := hJ.i1 1 le_rfl
    have hlt : hcount β s0 h 1 < (Fr β s0 h).card := by omega
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Fr β s0 h, ¬ 1 ≤ Mq β s0 h q := by
      by_contra hne
      push Not at hne
      have e : ((Fr β s0 h).filter fun q => 1 ≤ Mq β s0 h q) = Fr β s0 h :=
        filter_true_of_mem hne
      unfold hcount at hlt
      rw [e] at hlt
      exact lt_irrefl _ hlt
    have := hdrop q hq
    omega
  refine hJ.snoc_late ht ?_ ?_ ?_
  · intro v hv
    rw [hUs, hFr]
    have := hcount_shift hFr.subset (fun q hq => hdrop q (hFr ▸ hq)) v
    have := hJ.i1 (v + 1) (by omega)
    omega
  · omega
  · rw [hFr]
    have := hJ.i3
    omega

end Invariant

/-! ### The algorithm -/

section Algorithm

theorem nb_eq_getElem {h : History} {i : ℕ} (hi : i < h.length) : nb h i = h[i].1 := by
  simp [nb, List.getD_eq_getElem?_getD, hi]

theorem colourAt_ne_of_isRunOf {A : OnlineAlg} (hA : A.IsProper) {h : History} (hr : IsRunOf A h)
    {i u : ℕ} (hi : i < h.length) (hu : u ∈ nb h i) (hui : u < i) :
    colourAt h i ≠ colourAt h u := by
  rw [colourAt_eq_getElem hi, colourAt_eq_getElem (hui.trans hi), hr i hi]
  rw [nb_eq_getElem hi] at hu
  have hlen : u < (h.take i).length := by
    rw [List.length_take]
    omega
  have := hA (h.take i) h[i].1 u hlen hu
  rwa [List.getElem_take] at this

theorem colourAt_mem_usedColours {h : History} {i : ℕ} (hi : i < h.length) :
    colourAt h i ∈ usedColours h := by
  rw [colourAt_eq_getElem hi, usedColours, List.mem_toFinset]
  exact List.mem_map.2 ⟨h[i], List.getElem_mem hi, rfl⟩

theorem exists_of_mem_usedColours {h : History} {q : ℕ} (hq : q ∈ usedColours h) :
    ∃ i < h.length, colourAt h i = q := by
  rw [usedColours, List.mem_toFinset] at hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨i, hi, colourAt_eq_getElem hi⟩

/-- The staircase holds `binom(n + 1, 2)` vertices. -/
theorem sum_range_sub (n : ℕ) : ∑ j ∈ range n, (n - j) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right, ← ih]
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    omega

variable (β : History → ℕ) (K s0 : ℕ)

/-- The algorithm of the proof of Theorem D.4, before patching.  A vertex of a block before `s0`
gets the colour of its block; a vertex of block `s0` gets the least staircase colour `s0 + j`,
`j < K - s0 - 2`, with fewer than `K - s0 - 2 - j` vertices; a vertex of a later block gets the
colour of its block if the block has started, and otherwise an allowed fresh colour with the most
unserved vertices, or else the least allowed colour in use, or else a new colour. -/
noncomputable def topRaw (h : History) (s : Finset ℕ) : ℕ :=
  if β h < s0 then β h
  else if β h = s0 then
    if hex : ∃ j, j < K - s0 - 2 ∧ cnt β s0 h (s0 + j) < K - s0 - 2 - j then s0 + Nat.find hex
    else 0
  else if β h ∈ Dl β s0 h then colourAt h (h.length - 1)
  else if h1 : (Fr β s0 h \ nbrColours h s).Nonempty then
    (exists_max_image _ (Mq β s0 h) h1).choose
  else if h2 : (Us β s0 h \ nbrColours h s).Nonempty then (Us β s0 h \ nbrColours h s).min' h2
  else (usedColours h).sup id + 1

/-- The algorithm of the proof of Theorem D.4. -/
noncomputable def topAlg : OnlineAlg := (⟨topRaw β K s0⟩ : OnlineAlg).patch

theorem topAlg_isProper : (topAlg β K s0).IsProper := OnlineAlg.patch_isProper _

variable {β K s0}

theorem exists_spare {h : History} (hJ : J β K s0 h)
    (hbud : (topSet β s0 h).card < (K - s0 - 1).choose 2) :
    ∃ j, j < K - s0 - 2 ∧ cnt β s0 h (s0 + j) < K - s0 - 2 - j := by
  by_contra hcon
  push Not at hcon
  have hmap : ∀ i ∈ topSet β s0 h, colourAt h i ∈ (range (K - s0 - 2)).image (s0 + ·) := by
    intro i hi
    obtain ⟨j, hj, e⟩ := hJ.stair i hi
    exact mem_image.2 ⟨j, mem_range.2 hj, e.symm⟩
  have h1 : (topSet β s0 h).card = ∑ j ∈ range (K - s0 - 2), cnt β s0 h (s0 + j) := by
    rw [card_eq_sum_card_fiberwise hmap, sum_image fun a _ b _ hab => by omega]
    rfl
  have h2 : ∑ j ∈ range (K - s0 - 2), (K - s0 - 2 - j)
      ≤ ∑ j ∈ range (K - s0 - 2), cnt β s0 h (s0 + j) :=
    sum_le_sum fun j hj => hcon j (mem_range.1 hj)
  rw [sum_range_sub] at h2
  have h3 : (K - s0 - 1).choose 2 ≤ (K - s0 - 2 + 1).choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  omega

theorem topRaw_spec {h : History} {s : Finset ℕ} (hs0 : s0 < K) (hJ : J β K s0 h)
    (hrun : IsRunOf (topAlg β K s0) h) (F : SnocFacts β K h s)
    (hbud : β h = s0 → (topSet β s0 h).card < (K - s0 - 1).choose 2) :
    topRaw β K s0 h s ∉ nbrColours h s ∧ J β K s0 (h ++ [(s, topRaw β K s0 h s)]) := by
  unfold topRaw
  split_ifs with c1 c2 hex c3 h1 h2
  · refine ⟨fun hm => ?_, hJ.snoc_low c1⟩
    obtain ⟨u, hus, hun, huq⟩ := mem_nbrColours.1 hm
    have := F.fnbr u hus
    have := hJ.colLow u hun (by omega)
    omega
  · obtain ⟨hj, hcap⟩ := Nat.find_spec hex
    refine ⟨fun hm => ?_, hJ.snoc_top hs0 F c2 hj hcap⟩
    obtain ⟨u, hus, hun, huq⟩ := mem_nbrColours.1 hm
    have := F.fnbr u hus
    have := hJ.colLow u hun (by omega)
    omega
  · exact absurd (exists_spare hJ (hbud c2)) hex
  · have ht : s0 < β h := by omega
    obtain ⟨i, hi, hib⟩ := mem_image.1 c3
    have hin := lateSet_lt hi
    have hn : h.length - 1 < h.length := by omega
    have hb : bidx β h (h.length - 1) = β h :=
      le_antisymm (F.fmono _ hn) (hib ▸ F.fmono' i (h.length - 1) (by omega) hn)
    have hLc : colourAt h (h.length - 1) ∈ Lc β s0 h :=
      mem_image.2 ⟨h.length - 1, mem_filter.2 ⟨mem_range.2 hn, by omega⟩, rfl⟩
    refine ⟨fun hm => ?_, hJ.snoc_late_used ht hLc⟩
    obtain ⟨u, hus, hun, huq⟩ := mem_nbrColours.1 hm
    have hnb : nb h (h.length - 1) = s := F.fsame _ hn hb
    have hu : u ∈ nb h (h.length - 1) := hnb ▸ hus
    exact colourAt_ne_of_isRunOf (topAlg_isProper β K s0) hrun hn hu (F.fnbr' _ hn u hu) huq.symm
  · have ht : s0 < β h := by omega
    have spec := (exists_max_image _ (Mq β s0 h) h1).choose_spec
    exact ⟨(mem_sdiff.1 spec.1).2, hJ.snoc_late_fresh F ht c3 (mem_sdiff.1 spec.1).1
      fun q hq hqF => spec.2 q (mem_sdiff.2 ⟨hq, hqF⟩)⟩
  · have ht : s0 < β h := by omega
    have hx := min'_mem _ h2
    rw [mem_sdiff] at hx
    have hLc : (Us β s0 h \ nbrColours h s).min' h2 ∈ Lc β s0 h := by
      rcases mem_union.1 hx.1 with hQ | hL
      · by_contra hL
        exact h1 ⟨_, mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ, hL⟩, hx.2⟩⟩
      · exact hL
    exact ⟨hx.2, hJ.snoc_late_used ht hLc⟩
  · have ht : s0 < β h := by omega
    have hsup : ∀ q ∈ usedColours h, q < (usedColours h).sup id + 1 := fun q hq =>
      Nat.lt_succ_of_le (le_sup (f := id) hq)
    have hUs : ∀ q ∈ Us β s0 h, q ∈ usedColours h := by
      intro q hq
      rcases mem_union.1 hq with hq | hq
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hq
        exact colourAt_mem_usedColours (topSet_lt hi)
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hq
        exact colourAt_mem_usedColours (lateSet_lt hi)
    refine ⟨fun hm => ?_, hJ.snoc_late_new F ht c3 (fun q hq => ?_) fun hm => ?_⟩
    · obtain ⟨u, -, hun, huq⟩ := mem_nbrColours.1 hm
      exact lt_irrefl _ (hsup _ (huq ▸ colourAt_mem_usedColours hun))
    · by_contra hqF
      exact h2 ⟨q, mem_sdiff.2 ⟨hq, hqF⟩⟩
    · exact lt_irrefl _ (hsup _ (hUs _ hm))

/-- One step of the play against `topAlg` keeps the invariant, as long as block `s0` has at most
`binom(K - s0 - 1, 2)` vertices. -/
theorem J.step {h : History} {s : Finset ℕ} {c : ℕ} (hs0 : s0 < K) (hJ : J β K s0 h)
    (hrun : IsRunOf (topAlg β K s0) h) (hf : TopForm β K (h ++ [(s, c)]))
    (hc : c = (topAlg β K s0).step h s)
    (hbud : blockCard β (h ++ [(s, c)]) s0 ≤ (K - s0 - 1).choose 2) :
    J β K s0 (h ++ [(s, c)]) := by
  have F := hf.snocFacts
  have hb' : β h = s0 → (topSet β s0 h).card < (K - s0 - 1).choose 2 := by
    intro ht
    have e : blockCard β (h ++ [(s, c)]) s0 = (topSet β s0 (h ++ [(s, c)])).card := rfl
    rw [e, topSet_snoc_eq ht, card_insert_of_notMem fun hm => lt_irrefl _ (topSet_lt hm)]
      at hbud
    omega
  obtain ⟨hnot, hJ'⟩ := topRaw_spec hs0 hJ hrun F hb'
  have e : c = topRaw β K s0 h s := by
    rw [hc]
    change (if topRaw β K s0 h s ∈ nbrColours h s then _ else _) = _
    simp only [hnot, ↓reduceIte]
  rw [e]
  exact hJ'

theorem J.card_usedColours_lt {h : History} (hJ : J β K s0 h) (hs0 : s0 < K) :
    (usedColours h).card < K := by
  have hsub : usedColours h ⊆ range s0 ∪ Us β s0 h := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := exists_of_mem_usedColours hq
    rcases lt_trichotomy (bidx β h i) s0 with hlt | heq | hgt
    · rw [hJ.colLow i hi hlt]
      exact mem_union_left _ (mem_range.2 hlt)
    · exact mem_union_right _ (mem_union_left _
        (mem_image_of_mem _ (mem_filter.2 ⟨mem_range.2 hi, heq⟩)))
    · exact mem_union_right _ (mem_union_right _
        (mem_image_of_mem _ (mem_filter.2 ⟨mem_range.2 hi, hgt⟩)))
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at h1
  have := hJ.i2
  omega

theorem top_block_inv {adv : Adversary} (hs0 : s0 < K) (hform : IsTopBlockAdv β K adv)
    (hbud : ∀ p, blockCard β (adv.hist (topAlg β K s0) p) s0 ≤ (K - s0 - 1).choose 2) :
    ∀ p, J β K s0 (adv.hist (topAlg β K s0) p) := by
  intro p
  induction p with
  | zero => exact J.nil hs0
  | succ p ih =>
    have hf := hform _ (topAlg_isProper β K s0) (p + 1)
    have hb := hbud (p + 1)
    cases hm : adv.move (adv.hist (topAlg β K s0) p) with
    | none =>
      have e : adv.hist (topAlg β K s0) (p + 1) = adv.hist (topAlg β K s0) p := by
        simp only [Adversary.hist, hm]
      rw [e]
      exact ih
    | some s =>
      have e : adv.hist (topAlg β K s0) (p + 1) = adv.hist (topAlg β K s0) p
          ++ [(s, (topAlg β K s0).step (adv.hist (topAlg β K s0) p) s)] := by
        simp only [Adversary.hist, hm]
      rw [e] at hf hb ⊢
      exact ih.step hs0 (adv.isRunOf_hist _ p) hf rfl hb

/-- **Theorem D.4 (top block).**  Let `adv` present `K_K` blown up once, with any number of
servers per arc and block sizes chosen online (`IsTopBlockAdv β K adv`), and suppose that it forces
`K` colours.  Then for every `s` with `1 ≤ s ≤ K`, in some play against some proper algorithm the
block of `v_s` (block `s - 1` here) has at least `binom(K - s, 2) + 1` vertices; that is,
`b_s ≥ binom(K - s, 2) + 1`, and in particular `b_1 ≥ binom(K - 1, 2) + 1`. -/
theorem top_block {K : ℕ} {adv : Adversary} {β : History → ℕ} (hform : IsTopBlockAdv β K adv)
    (hF : adv.Forces K) {s : ℕ} (hs1 : 1 ≤ s) (hsK : s ≤ K) :
    ∃ A : OnlineAlg, A.IsProper ∧
      ∃ p, (K - s).choose 2 + 1 ≤ blockCard β (adv.hist A p) (s - 1) := by
  by_contra hcon
  push Not at hcon
  have hA := topAlg_isProper β K (s - 1)
  have hbud : ∀ p, blockCard β (adv.hist (topAlg β K (s - 1)) p) (s - 1)
      ≤ (K - (s - 1) - 1).choose 2 := fun p => by
    have := hcon _ hA p
    rw [show K - (s - 1) - 1 = K - s by omega]
    omega
  obtain ⟨p, -, hp⟩ := hF _ hA
  have := (top_block_inv (by omega) hform hbud p).card_usedColours_lt (by omega)
  omega

end Algorithm

end OnlineColouring.AppBD
