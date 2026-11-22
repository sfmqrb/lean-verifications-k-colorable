module

public import OnlineColouring.Towers
public import Mathlib.Data.Fintype.EquivFin

/-!
# The online model

Section 4, paragraph "Online colouring", and Definition 4.1 (online chromatic numbers) of the
paper, for deterministic algorithms.  Randomized algorithms and `χ^rand_k(n)` are in
`RandModel.lean`.

* An *online input on `n` vertices* (`OnlineInput n`): the vertices `0, …, n-1` arrive in this
  order, and vertex `v` arrives together with its set `N⁻(v)` of earlier neighbours (`nbr v`,
  every element `< v`).  It determines the ordered graph `I.graph : SimpleGraph (Fin n)` (the
  arrival order is the order of `Fin n`), and conversely every graph on `Fin n` comes from exactly
  one online input (`OnlineInput.equivGraph`).
* A *history* is what the algorithm has seen when a new vertex arrives: the list of the earlier
  neighbour sets of the vertices presented so far together with the colours it gave them, in
  arrival order (entry `i` belongs to vertex `i`; vertices are named by their arrival index).
* A *deterministic online algorithm* (`OnlineAlg`) maps a history and the earlier-neighbour set of
  the new vertex to a colour in `ℕ`.  It is *proper* (`OnlineAlg.IsProper`) if the colour always
  differs from the colours of the new vertex's earlier neighbours.  Since the lower bounds
  quantify over algorithms after `n` and `k` are fixed, an algorithm may depend on `n` and `k`.
* Running `A` on an input (`runHist`, `runCol`, `OnlineInput.run`) colours the vertices one at a
  time; `OnlineInput.cost` is the number of distinct colours used.
* `ChiDetAtLeast k n K` ("`χ^det_k(n) ≥ K`"): every proper deterministic online algorithm uses at
  least `K` colours on some `k`-colourable online input on exactly `n` vertices.
* `chiDet k n` is `χ^det_k(n)` as in Definition 4.1: the minimum over proper deterministic
  algorithms of the maximum cost over `k`-colourable inputs on `n` vertices (`maxCost`); the
  minimum is attained (`exists_maxCost_eq_chiDet`), and
  `le_chiDet_iff : K ≤ chiDet k n ↔ ChiDetAtLeast k n K` (for `k ≥ 1`).
* Padding (`ChiDetAtLeast.mono`): an input on `m ≤ n` vertices can be completed by isolated
  vertices, so it suffices to exhibit inputs on *at most* `n` vertices.
* First-Fit as an online algorithm is `OnlineAlg.firstFit`.
* `OnlineAlg.IsProperOn n` and `OnlineAlg.patch`: a lower bound `ChiDetAtLeast k n K` also holds
  against algorithms that are proper only on the inputs on `n` vertices
  (`ChiDetAtLeast.of_isProperOn`).

Why "for every algorithm there is an input" is the min–max of Definition 4.1: for `k ≥ 1` the
maximum is over a finite nonempty set of costs and the minimum over a nonempty set of algorithms
(First-Fit is proper), so `min_A max_I cost ≥ K` iff every algorithm has an input of cost `≥ K`.

This file does not define adversaries.  The adversaries of Definition 4.2 are the type `Adversary`
(`LabellingCap.lean`, `AdvBasic.lean`), and Observation 4.3 (determinacy), `χ^det_k(n) ≥ K` if and
only if `N_k(K) ≤ n`, is proved in `Det.lean` (`Det.le_chiDet_iff_Nk_le`).  What this file proves
is the form in which the second sentence of the observation is used by the modules that work with
`ChiDetAtLeast`: it suffices to exhibit, for every algorithm, a `k`-colourable input on at most
`n` vertices on which the algorithm uses `K` colours (`le_chiDet_iff` with the padding lemma
`exists_input_of_seq`; stated for `chiDet` in `Det.le_chiDet_of_forall_alg`).  `Play.lean` shows
that a rule that never stops, played against one fixed algorithm, presents one fixed input.

We work internally with *sequences* `N : ℕ → Finset ℕ` of earlier-neighbour sets (only the first
`n` entries matter); `OnlineInput.seq` and `OnlineInput.ofSeq` translate.
-/

@[expose] public section

namespace OnlineColouring

/-! ### Histories and algorithms -/

/-- A history of a play: for each vertex presented so far, in arrival order, its set of earlier
neighbours (as arrival indices) and the colour the algorithm gave it. -/
abbrev History : Type := List (Finset ℕ × ℕ)

/-- The colour of vertex `i` in the history `h` (`0` if there is no such vertex). -/
def colourAt (h : History) (i : ℕ) : ℕ := (h.getD i (∅, 0)).2

theorem colourAt_eq_getElem {h : History} {i : ℕ} (hi : i < h.length) : colourAt h i = h[i].2 := by
  simp [colourAt, List.getElem?_eq_getElem hi]

/-- The colours of those vertices of `s` that have been presented in the history `h`. -/
def nbrColours (h : History) (s : Finset ℕ) : Finset ℕ :=
  (s.filter (· < h.length)).image (colourAt h)

/-- A deterministic online colouring algorithm: given the history of the play so far and the set
of earlier neighbours of the new vertex, it returns the colour of the new vertex. -/
structure OnlineAlg where
  /-- The colour given to the new vertex. -/
  step : History → Finset ℕ → ℕ

namespace OnlineAlg

/-- A proper online algorithm: the colour of the new vertex differs from the colours of all its
earlier neighbours. -/
def IsProper (A : OnlineAlg) : Prop :=
  ∀ (h : History) (s : Finset ℕ) (i : ℕ) (hi : i < h.length), i ∈ s → A.step h s ≠ h[i].2

theorem isProper_iff (A : OnlineAlg) : A.IsProper ↔ ∀ h s, A.step h s ∉ nbrColours h s := by
  constructor
  · intro hA h s hmem
    simp only [nbrColours, Finset.mem_image, Finset.mem_filter] at hmem
    obtain ⟨i, ⟨his, hi⟩, heq⟩ := hmem
    exact hA h s i hi his (by rw [← heq, colourAt_eq_getElem hi])
  · intro hA h s i hi his heq
    apply hA h s
    simp only [nbrColours, Finset.mem_image, Finset.mem_filter]
    exact ⟨i, ⟨his, hi⟩, by rw [colourAt_eq_getElem hi, heq]⟩

/-- A colour that is not among `nbrColours h s`. -/
def fresh (h : History) (s : Finset ℕ) : ℕ := (nbrColours h s).sup id + 1

theorem fresh_notMem (h : History) (s : Finset ℕ) : fresh h s ∉ nbrColours h s := by
  intro hmem
  have := Finset.le_sup (f := id) hmem
  simp only [fresh, id] at this
  omega

/-- First-Fit: the least colour not used on the earlier neighbours. -/
def firstFit : OnlineAlg :=
  ⟨fun h s => Nat.find (⟨fresh h s, fresh_notMem h s⟩ : ∃ c, c ∉ nbrColours h s)⟩

theorem firstFit_isProper : firstFit.IsProper := by
  rw [isProper_iff]
  intro h s
  exact Nat.find_spec (⟨fresh h s, fresh_notMem h s⟩ : ∃ c, c ∉ nbrColours h s)

end OnlineAlg

/-! ### Running an algorithm on a sequence of earlier-neighbour sets -/

section Run

variable (A : OnlineAlg) (N : ℕ → Finset ℕ)

/-- The history after the first `i` vertices of the input sequence `N` have been coloured by `A`. -/
def runHist : ℕ → History
  | 0 => []
  | i + 1 => runHist i ++ [(N i, A.step (runHist i) (N i))]

/-- The colour that `A` gives to vertex `i` of the input sequence `N`. -/
def runCol (i : ℕ) : ℕ := A.step (runHist A N i) (N i)

variable {A N}

theorem runHist_succ (i : ℕ) : runHist A N (i + 1) = runHist A N i ++ [(N i, runCol A N i)] := rfl

theorem runHist_eq_map (i : ℕ) :
    runHist A N i = (List.range i).map fun j => (N j, runCol A N j) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [runHist_succ, ih, List.range_succ, List.map_append, List.map_singleton]

@[simp] theorem length_runHist (i : ℕ) : (runHist A N i).length = i := by
  rw [runHist_eq_map]; simp

theorem getElem_runHist {i j : ℕ} (hj : j < (runHist A N i).length) :
    (runHist A N i)[j] = (N j, runCol A N j) := by
  simp only [runHist_eq_map, List.getElem_map, List.getElem_range]

theorem colourAt_runHist {i j : ℕ} (hj : j < i) : colourAt (runHist A N i) j = runCol A N j := by
  rw [colourAt_eq_getElem (by simpa using hj), getElem_runHist]

/-- The run is online: the history after `i` vertices depends only on the first `i` entries. -/
theorem runHist_congr {N' : ℕ → Finset ℕ} {i : ℕ} (h : ∀ j < i, N j = N' j) :
    runHist A N i = runHist A N' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih' := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    simp only [runHist, ih', h i (Nat.lt_succ_self i)]

theorem runCol_congr {N' : ℕ → Finset ℕ} {i : ℕ} (h : ∀ j ≤ i, N j = N' j) :
    runCol A N i = runCol A N' i := by
  unfold runCol
  rw [runHist_congr fun j hj => h j hj.le, h i le_rfl]

/-- The colours of the earlier neighbours, as seen by the algorithm. -/
theorem nbrColours_runHist {i : ℕ} (hN : N i ⊆ Finset.range i) :
    nbrColours (runHist A N i) (N i) = (N i).image (runCol A N) := by
  unfold nbrColours
  have hf : (N i).filter (· < (runHist A N i).length) = N i := by
    apply Finset.filter_true_of_mem
    intro j hj
    simpa using Finset.mem_range.1 (hN hj)
  rw [hf]
  apply Finset.image_congr
  intro j hj
  exact colourAt_runHist (Finset.mem_range.1 (hN hj))

/-- A proper algorithm colours the vertex `i` differently from each of its earlier neighbours. -/
theorem runCol_ne (hA : A.IsProper) {i j : ℕ} (hj : j ∈ N i) (hji : j < i) :
    runCol A N i ≠ runCol A N j := by
  have := hA (runHist A N i) (N i) j (by simpa using hji) hj
  rwa [getElem_runHist] at this

end Run

/-! ### Online inputs -/

/-- An online input on `n` vertices: vertex `v` arrives with its set `nbr v` of earlier
neighbours. -/
@[ext]
structure OnlineInput (n : ℕ) where
  /-- The earlier neighbours `N⁻(v)` of the vertex `v`. -/
  nbr : Fin n → Finset (Fin n)
  /-- Earlier neighbours are earlier. -/
  nbr_lt : ∀ v, ∀ u ∈ nbr v, u < v

/-- A sequence of earlier-neighbour sets is *valid* if every entry `i` is a subset of
`{0, …, i-1}`. -/
def ValidSeq (N : ℕ → Finset ℕ) : Prop := ∀ i, N i ⊆ Finset.range i

namespace OnlineInput

variable {n : ℕ}

/-- The ordered graph of an online input: `u ~ v` iff one is an earlier neighbour of the other. -/
def graph (I : OnlineInput n) : SimpleGraph (Fin n) where
  Adj u v := u ∈ I.nbr v ∨ v ∈ I.nbr u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by rcases h with h | h <;> exact lt_irrefl _ (I.nbr_lt v v h)⟩

theorem graph_adj {I : OnlineInput n} {u v : Fin n} :
    I.graph.Adj u v ↔ u ∈ I.nbr v ∨ v ∈ I.nbr u := Iff.rfl

/-- The online input as an ordered graph (the arrival order is the order of `Fin n`). -/
def toOrdGraph (I : OnlineInput n) : OrdGraph := ⟨Fin n, I.graph⟩

/-- Every graph on `Fin n` is presented by an online input, in the order of `Fin n`. -/
noncomputable def ofGraph (G : SimpleGraph (Fin n)) : OnlineInput n := by
  classical
  exact ⟨fun v => Finset.univ.filter fun u => u < v ∧ G.Adj u v,
    fun v u hu => (Finset.mem_filter.1 hu).2.1⟩

theorem mem_ofGraph_nbr {G : SimpleGraph (Fin n)} {u v : Fin n} :
    u ∈ (ofGraph G).nbr v ↔ u < v ∧ G.Adj u v := by
  classical
  unfold ofGraph
  simp

theorem graph_ofGraph (G : SimpleGraph (Fin n)) : (ofGraph G).graph = G := by
  ext u v
  rw [graph_adj, mem_ofGraph_nbr, mem_ofGraph_nbr]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · exact h.symm
  · intro h
    rcases lt_trichotomy u v with huv | rfl | hvu
    · exact Or.inl ⟨huv, h⟩
    · exact absurd h (G.loopless.irrefl _)
    · exact Or.inr ⟨hvu, h.symm⟩

theorem ofGraph_graph (I : OnlineInput n) : ofGraph I.graph = I := by
  ext v u
  rw [mem_ofGraph_nbr, graph_adj]
  constructor
  · rintro ⟨huv, h | h⟩
    · exact h
    · exact absurd (I.nbr_lt u v h) (not_lt.2 huv.le)
  · intro h
    exact ⟨I.nbr_lt v u h, Or.inl h⟩

/-- Online inputs on `n` vertices are exactly the graphs on `Fin n` (ordered by `Fin n`). -/
noncomputable def equivGraph : OnlineInput n ≃ SimpleGraph (Fin n) where
  toFun := graph
  invFun := ofGraph
  left_inv := ofGraph_graph
  right_inv := graph_ofGraph

/-- The input as a sequence of earlier-neighbour sets of arrival indices (empty after `n`). -/
def seq (I : OnlineInput n) (i : ℕ) : Finset ℕ :=
  if h : i < n then (I.nbr ⟨i, h⟩).map Fin.valEmbedding else ∅

theorem seq_valid (I : OnlineInput n) : ValidSeq I.seq := by
  intro i x hx
  unfold seq at hx
  split_ifs at hx with h
  · simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact Finset.mem_range.2 (I.nbr_lt _ u hu)
  · simp at hx

/-- The online input given by the first `n` entries of a valid sequence. -/
def ofSeq (N : ℕ → Finset ℕ) (hN : ValidSeq N) (n : ℕ) : OnlineInput n where
  nbr v := Finset.univ.filter fun u : Fin n => (u : ℕ) ∈ N v
  nbr_lt v _ hu := Finset.mem_range.1 (hN v (Finset.mem_filter.1 hu).2)

variable {N : ℕ → Finset ℕ} {hN : ValidSeq N}

theorem mem_ofSeq_nbr {u v : Fin n} : u ∈ (ofSeq N hN n).nbr v ↔ (u : ℕ) ∈ N v := by
  simp [ofSeq]

theorem ofSeq_adj {u v : Fin n} :
    (ofSeq N hN n).graph.Adj u v ↔ (u : ℕ) ∈ N v ∨ (v : ℕ) ∈ N u := by
  rw [graph_adj, mem_ofSeq_nbr, mem_ofSeq_nbr]

theorem seq_ofSeq {i : ℕ} (hi : i < n) : (ofSeq N hN n).seq i = N i := by
  ext x
  simp only [seq, hi, ↓reduceDIte, Finset.mem_map, mem_ofSeq_nbr, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hx
    exact ⟨⟨x, (Finset.mem_range.1 (hN i hx)).trans hi⟩, hx, rfl⟩

theorem ofSeq_seq (I : OnlineInput n) : ofSeq I.seq I.seq_valid n = I := by
  ext v u
  rw [mem_ofSeq_nbr]
  simp [seq, Fin.val_inj]

theorem ofSeq_congr {N' : ℕ → Finset ℕ} (h : N = N') :
    ofSeq N hN n = ofSeq N' (h ▸ hN) n := by
  subst h; rfl

/-! ### Running an algorithm on an online input -/

/-- The colouring produced by running `A` on the input `I`. -/
def run (I : OnlineInput n) (A : OnlineAlg) (v : Fin n) : ℕ := runCol A I.seq v

/-- The cost of `A` on `I`: the number of distinct colours used. -/
def cost (I : OnlineInput n) (A : OnlineAlg) : ℕ := (Finset.univ.image (I.run A)).card

/-- A proper algorithm produces a proper colouring. -/
theorem run_ne_of_adj (I : OnlineInput n) {A : OnlineAlg} (hA : A.IsProper) {u v : Fin n}
    (huv : I.graph.Adj u v) : I.run A u ≠ I.run A v := by
  have key : ∀ a b : Fin n, a ∈ I.nbr b → I.run A b ≠ I.run A a := by
    intro a b hab
    apply runCol_ne hA _ (I.nbr_lt b a hab)
    simp only [seq, b.2, ↓reduceDIte, Finset.mem_map, Fin.valEmbedding_apply]
    exact ⟨a, hab, rfl⟩
  rcases huv with h | h
  · exact (key u v h).symm
  · exact key v u h

theorem cost_le (I : OnlineInput n) (A : OnlineAlg) : I.cost A ≤ n :=
  Finset.card_image_le.trans (by simp)

theorem image_univ_fin (f : ℕ → ℕ) :
    (Finset.univ : Finset (Fin n)).image (fun v : Fin n => f v) = (Finset.range n).image f := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- The cost on `ofSeq N n` is the number of colours on the first `n` entries of `N`. -/
theorem cost_ofSeq (A : OnlineAlg) :
    (ofSeq N hN n).cost A = ((Finset.range n).image (runCol A N)).card := by
  unfold cost run
  have : (fun v : Fin n => runCol A (ofSeq N hN n).seq v) = fun v : Fin n => runCol A N v := by
    funext v
    exact runCol_congr fun j hj => seq_ofSeq (lt_of_le_of_lt hj v.2)
  rw [this, image_univ_fin]

end OnlineInput

/-! ### Lower bounds on the online chromatic number -/

/-- `ChiDetAtLeast k n K` is the statement `χ^det_k(n) ≥ K`: for every proper deterministic online
algorithm there is an online input on exactly `n` vertices whose graph is `k`-colourable and on
which the algorithm uses at least `K` colours. -/
def ChiDetAtLeast (k n K : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ I : OnlineInput n, I.graph.Colorable k ∧ K ≤ I.cost A

/-- The maximum cost of `A` over the `k`-colourable online inputs on `n` vertices. -/
noncomputable def maxCost (A : OnlineAlg) (k n : ℕ) : ℕ :=
  sSup {c | ∃ I : OnlineInput n, I.graph.Colorable k ∧ I.cost A = c}

/-- Definition 4.1 (online chromatic numbers): `χ^det_k(n)` is the minimum, over proper
deterministic online algorithms, of the maximum cost over all `k`-colourable online inputs on `n`
vertices. -/
noncomputable def chiDet (k n : ℕ) : ℕ :=
  sInf {c | ∃ A : OnlineAlg, A.IsProper ∧ maxCost A k n = c}

/-- The input with no edges. -/
def emptyInput (n : ℕ) : OnlineInput n :=
  ⟨fun _ => ∅, fun _ _ h => absurd h (Finset.notMem_empty _)⟩

theorem emptyInput_colorable {n k : ℕ} (hk : 1 ≤ k) : (emptyInput n).graph.Colorable k :=
  ⟨SimpleGraph.Coloring.mk (fun _ => (⟨0, hk⟩ : Fin k)) fun h => by
    rcases h with h | h <;> exact absurd h (Finset.notMem_empty _)⟩

theorem le_maxCost_iff {A : OnlineAlg} {k n K : ℕ} (hk : 1 ≤ k) :
    K ≤ maxCost A k n ↔ ∃ I : OnlineInput n, I.graph.Colorable k ∧ K ≤ I.cost A := by
  set S := {c | ∃ I : OnlineInput n, I.graph.Colorable k ∧ I.cost A = c}
  have hne : S.Nonempty := ⟨_, emptyInput n, emptyInput_colorable hk, rfl⟩
  have hbdd : BddAbove S := ⟨n, by rintro c ⟨I, -, rfl⟩; exact I.cost_le A⟩
  constructor
  · intro hK
    obtain ⟨I, hI, hc⟩ := Nat.sSup_mem hne hbdd
    exact ⟨I, hI, hc ▸ hK⟩
  · rintro ⟨I, hI, hK⟩
    exact hK.trans (le_csSup hbdd ⟨I, hI, rfl⟩)

/-- `chiDet` is a minimum over algorithms of a maximum over inputs, so `χ^det_k(n) ≥ K` holds
exactly when every algorithm has a `k`-colourable input on which it uses `K` colours. -/
theorem le_chiDet_iff {k n K : ℕ} (hk : 1 ≤ k) : K ≤ chiDet k n ↔ ChiDetAtLeast k n K := by
  set T := {c | ∃ A : OnlineAlg, A.IsProper ∧ maxCost A k n = c}
  have hne : T.Nonempty := ⟨_, OnlineAlg.firstFit, OnlineAlg.firstFit_isProper, rfl⟩
  constructor
  · intro hK A hA
    exact (le_maxCost_iff hk).1 (hK.trans (Nat.sInf_le ⟨A, hA, rfl⟩))
  · intro h
    apply le_csInf hne
    rintro c ⟨A, hA, rfl⟩
    exact (le_maxCost_iff hk).2 (h A hA)

/-- Sanity check (the definition is not vacuous): no algorithm is forced to use more than `n`
colours on `n` vertices. -/
theorem not_chiDetAtLeast_succ (k n : ℕ) : ¬ ChiDetAtLeast k n (n + 1) := by
  intro h
  obtain ⟨I, -, hI⟩ := h OnlineAlg.firstFit OnlineAlg.firstFit_isProper
  have := I.cost_le OnlineAlg.firstFit
  omega

/-- The minimum in `chiDet` is attained: some proper algorithm has maximum cost `chiDet k n`. -/
theorem exists_maxCost_eq_chiDet (k n : ℕ) :
    ∃ A : OnlineAlg, A.IsProper ∧ maxCost A k n = chiDet k n :=
  Nat.sInf_mem (s := {c | ∃ A : OnlineAlg, A.IsProper ∧ maxCost A k n = c})
    ⟨_, OnlineAlg.firstFit, OnlineAlg.firstFit_isProper, rfl⟩

/-! ### Padding with isolated vertices -/

/-- The sequence `N` cut off after `m` entries. -/
def truncSeq (N : ℕ → Finset ℕ) (m i : ℕ) : Finset ℕ := if i < m then N i else ∅

theorem truncSeq_valid {N : ℕ → Finset ℕ} (hN : ValidSeq N) (m : ℕ) : ValidSeq (truncSeq N m) := by
  intro i
  unfold truncSeq
  split_ifs
  · exact hN i
  · exact Finset.empty_subset _

/-- Appending isolated vertices keeps `k`-colourability (`k ≥ 1`). -/
theorem colorable_truncSeq {N : ℕ → Finset ℕ} (hN : ValidSeq N) {m n k : ℕ} (hk : 1 ≤ k)
    (hc : (OnlineInput.ofSeq N hN m).graph.Colorable k) :
    (OnlineInput.ofSeq (truncSeq N m) (truncSeq_valid hN m) n).graph.Colorable k := by
  obtain ⟨c⟩ := hc
  -- an edge of the padded graph joins two of the first `m` vertices
  have key : ∀ a b : Fin n, (a : ℕ) ∈ truncSeq N m b →
      ∃ (ha : (a : ℕ) < m) (hb : (b : ℕ) < m),
        (OnlineInput.ofSeq N hN m).graph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b hab
    unfold truncSeq at hab
    split_ifs at hab with hb
    · have hab' : (a : ℕ) < b := Finset.mem_range.1 (hN b hab)
      exact ⟨hab'.trans hb, hb, OnlineInput.ofSeq_adj.2 (Or.inl hab)⟩
    · simp at hab
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if h : (v : ℕ) < m then c ⟨v, h⟩ else ⟨0, hk⟩) ?_⟩
  intro u v huv
  rcases OnlineInput.ofSeq_adj.1 huv with h | h
  · obtain ⟨hu, hv, hadj⟩ := key u v h
    simp only [hu, hv, ↓reduceDIte]
    exact c.valid hadj
  · obtain ⟨hv, hu, hadj⟩ := key v u h
    simp only [hu, hv, ↓reduceDIte]
    exact (c.valid hadj).symm

/-- Appending isolated vertices does not decrease the number of colours used. -/
theorem le_cost_truncSeq {A : OnlineAlg} {N : ℕ → Finset ℕ} (hN : ValidSeq N) {m n K : ℕ}
    (hmn : m ≤ n) (hK : K ≤ ((Finset.range m).image (runCol A N)).card) :
    K ≤ (OnlineInput.ofSeq (truncSeq N m) (truncSeq_valid hN m) n).cost A := by
  rw [OnlineInput.cost_ofSeq]
  refine hK.trans (Finset.card_le_card ?_)
  intro c hc
  simp only [Finset.mem_image, Finset.mem_range] at hc ⊢
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨i, lt_of_lt_of_le hi hmn, runCol_congr fun j hj => ?_⟩
  simp [truncSeq, lt_of_le_of_lt hj hi]

/-- **Padding.** A `k`-colourable input on `m ≤ n` vertices on which `A` uses `K` colours gives
one on exactly `n` vertices. -/
theorem exists_input_of_seq {A : OnlineAlg} {N : ℕ → Finset ℕ} (hN : ValidSeq N) {m n k K : ℕ}
    (hk : 1 ≤ k) (hmn : m ≤ n) (hc : (OnlineInput.ofSeq N hN m).graph.Colorable k)
    (hK : K ≤ ((Finset.range m).image (runCol A N)).card) :
    ∃ I : OnlineInput n, I.graph.Colorable k ∧ K ≤ I.cost A :=
  ⟨OnlineInput.ofSeq (truncSeq N m) (truncSeq_valid hN m) n, colorable_truncSeq hN hk hc,
    le_cost_truncSeq hN hmn hK⟩

/-- `χ^det_k(n)` is non-decreasing in `n`: a bad input stays bad after appending isolated
vertices. -/
theorem ChiDetAtLeast.mono {k m n K : ℕ} (hk : 1 ≤ k) (hmn : m ≤ n) (h : ChiDetAtLeast k m K) :
    ChiDetAtLeast k n K := by
  intro A hA
  obtain ⟨I, hc, hK⟩ := h A hA
  rw [← OnlineInput.ofSeq_seq I] at hc hK
  rw [OnlineInput.cost_ofSeq] at hK
  exact exists_input_of_seq I.seq_valid hk hmn hc hK

/-- Every algorithm uses at least one colour on a nonempty input. -/
theorem chiDetAtLeast_one {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : ChiDetAtLeast k n 1 := by
  intro A _
  refine ⟨emptyInput n, emptyInput_colorable hk, ?_⟩
  unfold OnlineInput.cost
  apply Finset.card_pos.2
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn⟩)⟩

theorem chiDetAtLeast_of_le {k n K K' : ℕ} (hKK' : K' ≤ K) (h : ChiDetAtLeast k n K) :
    ChiDetAtLeast k n K' := by
  intro A hA
  obtain ⟨I, hc, hK⟩ := h A hA
  exact ⟨I, hc, hKK'.trans hK⟩

/-! ### Algorithms that are proper only on actual inputs -/

/-- `A` colours every online input on `n` vertices properly.  This is weaker than `IsProper`,
which also constrains histories that cannot occur. -/
def OnlineAlg.IsProperOn (A : OnlineAlg) (n : ℕ) : Prop :=
  ∀ (I : OnlineInput n) (u v : Fin n), I.graph.Adj u v → I.run A u ≠ I.run A v

theorem OnlineAlg.IsProper.isProperOn {A : OnlineAlg} (hA : A.IsProper) (n : ℕ) :
    A.IsProperOn n :=
  fun I _ _ h => I.run_ne_of_adj hA h

/-- `A` patched with a fresh colour wherever its colour would clash. -/
def OnlineAlg.patch (A : OnlineAlg) : OnlineAlg :=
  ⟨fun h s => if A.step h s ∈ nbrColours h s then OnlineAlg.fresh h s else A.step h s⟩

theorem OnlineAlg.patch_isProper (A : OnlineAlg) : A.patch.IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro h s
  change (if A.step h s ∈ nbrColours h s then OnlineAlg.fresh h s else A.step h s) ∉ _
  split_ifs with hc
  · exact OnlineAlg.fresh_notMem h s
  · exact hc

/-- On inputs on `n` vertices, the patched algorithm behaves exactly like `A`. -/
theorem OnlineAlg.run_patch {A : OnlineAlg} {n : ℕ} (hA : A.IsProperOn n) (I : OnlineInput n) :
    I.run A.patch = I.run A := by
  have key : ∀ i < n, runCol A.patch I.seq i = runCol A I.seq i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi
    have hhist : runHist A.patch I.seq i = runHist A I.seq i := by
      rw [runHist_eq_map, runHist_eq_map]
      exact List.map_congr_left fun j hj => by
        rw [ih j (List.mem_range.1 hj) ((List.mem_range.1 hj).trans hi)]
    change (if A.step _ _ ∈ nbrColours _ _ then _ else _) = _
    rw [hhist, nbrColours_runHist (I.seq_valid i), ite_eq_right]
    · rfl
    intro hmem
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hmem
    simp only [OnlineInput.seq, hi, ↓reduceDIte, Finset.mem_map, Fin.valEmbedding_apply] at hj
    obtain ⟨u, hu, rfl⟩ := hj
    exact hA I u ⟨i, hi⟩ (Or.inl hu) hji
  funext v
  exact key v v.2

/-- A lower bound `χ^det_k(n) ≥ K` also holds against algorithms that are only proper on the
inputs on `n` vertices: patching such an algorithm does not change its runs. -/
theorem ChiDetAtLeast.of_isProperOn {k n K : ℕ} (h : ChiDetAtLeast k n K) {A : OnlineAlg}
    (hA : A.IsProperOn n) : ∃ I : OnlineInput n, I.graph.Colorable k ∧ K ≤ I.cost A := by
  obtain ⟨I, hc, hK⟩ := h A.patch A.patch_isProper
  refine ⟨I, hc, ?_⟩
  unfold OnlineInput.cost at hK ⊢
  rwa [OnlineAlg.run_patch hA] at hK

end OnlineColouring
