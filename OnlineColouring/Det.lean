module

public import OnlineColouring.AdvBasic

/-!
# Determinacy: from "for every algorithm an input" to one adversary (Observation 4.3)

Observation 4.3 (determinacy): *We have `χ^det_k(n) ≥ K` if and only if `N_k(K) ≤ n`. In
particular, it suffices to exhibit, for every deterministic algorithm, an ordered `k`-colourable
graph on at most `n` vertices on which the algorithm uses `K` colours.*  The paper's argument, in
the paragraph
before the observation: `⇐` run the adversary and append isolated vertices; `⇒` the game is a
finite game of perfect information, so by Zermelo's theorem one of the two players has a winning
strategy.

## The determinacy lemma

`Det.exists_presents`: let `S` be a set of online inputs on exactly `n` vertices such that every
proper deterministic algorithm uses at least `K` colours on some member of `S`.  Then there is an
`Adversary` that *presents `S` and forces `K`* (`Det.Presents adv S K`): for every proper
algorithm `A` there is a member `I` of `S` with `K ≤ I.cost A` such that the history of the play
after `p` rounds is the run of `A` on the first `min p n` vertices of `I`, and the adversary
stops exactly after `n` rounds.  Consequences (`Det.Presents.*`): the adversary forces `K`
colours, has size at most `n`, lands in every class of ordered graphs that contains the graphs of
`S`, and the final graph of every play is the graph of a member of `S` in its arrival order
(`Presents.final_graph`).

The proof is Zermelo's backward induction, written out.  `Win S K d h` says that the adversary
wins from the position `h` with `d` rounds to go: for `d = 0`, `h` presents a member of `S` and
has at least `K` colours; for `d + 1`, there is a next vertex such that every proper colour leads
to a position won with `d` rounds to go.  If the start position is not won, the algorithm
`defender`, which at every position picks a proper colour that keeps the position not won (and a
fresh colour if there is none, so that it is proper on every history), uses fewer than `K`
colours on every member of `S`; so the start position is won (`win_nil`), and the adversary
`strat` that follows winning moves presents `S` and forces `K`.  The paper renames colours in
the order of first use to make the game finite; this is not needed here, since the induction is
over the number of remaining rounds only.

## Observation 4.3

* `Det.le_chiDet_iff_Nk_le`: `K ≤ chiDet k n ↔ Nk k K ≤ n` for `1 ≤ k`, with the predicate form
  `Det.chiDetAtLeast_iff_NkLE` (for `k = 0` the maximum in the definition of `chiDet` is over an
  empty set of inputs when `n ≥ 1`; the paper has `k ≥ 1` throughout).
* `Det.Nk_le_of_forall_alg`, `Det.le_chiDet_of_forall_alg`: the "In particular" sentence.

`⇐` needs one point that the paper does not mention.  An `Adversary` may name indices in a
neighbour set that are not earlier vertices; they are ignored by `History.graph` and by
properness, but an algorithm may react to them.  We therefore run the adversary against the
algorithm `cleanAlg A`, which behaves like `A` after such indices have been deleted
(`clean`); its play is a run of `A` on an honest online input with the same graph and the same
colours (`Det.exists_input_of_hist`, which turns a play of any adversary into an input).
-/

@[expose] public section

namespace OnlineColouring

namespace Det

open Finset

/-! ### Histories: prefixes and runs -/

theorem IsRunOf.of_append {A : OnlineAlg} {l l' : History} (h : IsRunOf A (l ++ l')) :
    IsRunOf A l := by
  intro i hi
  have h' := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at h'

theorem IsRunOf.last {A : OnlineAlg} {l : History} {a : Finset ℕ × ℕ}
    (h : IsRunOf A (l ++ [a])) : a.2 = A.step l a.1 := by
  have h' := h l.length (by simp)
  simpa using h'

/-- A history produced by `A` is the run of `A` on its own sequence of neighbour sets. -/
theorem eq_runHist_of_isRunOf {A : OnlineAlg} {N : ℕ → Finset ℕ} :
    ∀ {h : History}, IsRunOf A h → (∀ i (hi : i < h.length), h[i].1 = N i) →
      h = runHist A N h.length := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; rfl
  | append_singleton l a ih =>
    intro hrun hN
    have hl : l = runHist A N l.length := by
      refine ih (IsRunOf.of_append hrun) fun i hi => ?_
      have := hN i (by rw [List.length_append]; omega)
      rwa [List.getElem_append_left hi] at this
    have ha1 : a.1 = N l.length := by
      have := hN l.length (by simp)
      simpa using this
    have ha2 := IsRunOf.last hrun
    rw [List.length_append, List.length_singleton, runHist_succ, runCol, ← hl, ← ha1, ← ha2]

theorem hist_prefix_succ (adv : Adversary) (A : OnlineAlg) (p : ℕ) :
    adv.hist A p <+: adv.hist A (p + 1) := by
  rw [Adversary.hist]
  split
  · exact List.prefix_rfl
  · exact List.prefix_append _ _

theorem hist_prefix (adv : Adversary) (A : OnlineAlg) {p q : ℕ} (hpq : p ≤ q) :
    adv.hist A p <+: adv.hist A q := by
  induction q, hpq using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ q _ ih => exact ih.trans (hist_prefix_succ adv A q)

theorem hist_succ_of_none {adv : Adversary} {A : OnlineAlg} {p : ℕ}
    (h : adv.move (adv.hist A p) = none) : adv.hist A (p + 1) = adv.hist A p := by
  rw [Adversary.hist, h]

theorem hist_succ_of_some {adv : Adversary} {A : OnlineAlg} {p : ℕ} {s : Finset ℕ}
    (h : adv.move (adv.hist A p) = some s) :
    adv.hist A (p + 1) = adv.hist A p ++ [(s, A.step (adv.hist A p) s)] := by
  rw [Adversary.hist, h]

/-- Once the adversary has stopped, the history no longer changes. -/
theorem hist_eq_of_stopsAt {adv : Adversary} {A : OnlineAlg} {p : ℕ} (h : adv.StopsAt A p) :
    ∀ q, p ≤ q → adv.hist A q = adv.hist A p := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q _ ih =>
    rw [← ih]
    exact hist_succ_of_none (by rw [ih]; exact h)

/-! ### The graph of a run -/

theorem mem_seq_iff {n : ℕ} (I : OnlineInput n) (u v : Fin n) :
    (u : ℕ) ∈ I.seq v ↔ u ∈ I.nbr v := by
  simp [OnlineInput.seq, Fin.val_inj]

/-- The graph presented in the full run of `A` on `I` is the graph of `I`, in its arrival
order. -/
theorem graph_runHist (A : OnlineAlg) {n : ℕ} (I : OnlineInput n)
    (e : (runHist A I.seq n).length = n) :
    (runHist A I.seq n).graph = I.graph.comap (Fin.cast e) := by
  ext u v
  rw [History.graph_adj, SimpleGraph.comap_adj, OnlineInput.graph_adj]
  have key : ∀ a b : Fin (runHist A I.seq n).length,
      (((a : ℕ) < b ∧ (a : ℕ) ∈ ((runHist A I.seq n).get b).1) ↔
        Fin.cast e a ∈ I.nbr (Fin.cast e b)) := by
    intro a b
    rw [List.get_eq_getElem, getElem_runHist, ← mem_seq_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_range.1 (I.seq_valid _ h), h⟩
  rw [key u v, key v u]

/-- A class of ordered graphs does not see the name of the vertex type. -/
theorem class_cast {C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop} {m n : ℕ} (e : m = n)
    {G : SimpleGraph (Fin n)} (h : C n G) : C m (G.comap (Fin.cast e)) := by
  subst e
  have : G.comap (Fin.cast rfl) = G := by
    ext u v
    simp
  rwa [this]

/-! ### The game: winning positions -/

section Game

variable {n : ℕ} (S : Set (OnlineInput n)) (K : ℕ)

/-- `Win S K d h`: the adversary wins from the position `h` with `d` rounds to go. -/
def Win : ℕ → History → Prop
  | 0, h => ∃ I ∈ S, h.length = n ∧ (∀ i (hi : i < h.length), h[i].1 = I.seq i) ∧
      K ≤ (usedColours h).card
  | d + 1, h => ∃ s : Finset ℕ, ∀ c, c ∉ nbrColours h s → Win d (h ++ [(s, c)])

theorem win_zero {h : History} : Win S K 0 h ↔ ∃ I ∈ S, h.length = n ∧
    (∀ i (hi : i < h.length), h[i].1 = I.seq i) ∧ K ≤ (usedColours h).card := Iff.rfl

theorem win_succ {d : ℕ} {h : History} : Win S K (d + 1) h ↔
    ∃ s : Finset ℕ, ∀ c, c ∉ nbrColours h s → Win S K d (h ++ [(s, c)]) := Iff.rfl

open Classical in
/-- The algorithm's strategy: a proper colour that leads to a position that is not won by the
adversary, if there is one, and a fresh colour otherwise. -/
noncomputable def defender : OnlineAlg :=
  ⟨fun h s =>
    if hx : ∃ c, c ∉ nbrColours h s ∧ ¬ Win S K (n - h.length - 1) (h ++ [(s, c)]) then
      hx.choose
    else OnlineAlg.fresh h s⟩

theorem defender_isProper : (defender S K).IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro h s
  unfold defender
  dsimp only
  split
  · rename_i hx
    exact hx.choose_spec.1
  · exact OnlineAlg.fresh_notMem h s

/-- If the start position is not won, then no position of a play of `defender` is won. -/
theorem not_win_runHist (h0 : ¬ Win S K n []) (N : ℕ → Finset ℕ) :
    ∀ i ≤ n, ¬ Win S K (n - i) (runHist (defender S K) N i) := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have e : n - i = (n - (i + 1)) + 1 := by omega
    rw [e, win_succ] at h1
    push Not at h1
    obtain ⟨c, hc, hw⟩ := h1 (N i)
    have hx : ∃ c, c ∉ nbrColours (runHist (defender S K) N i) (N i) ∧
        ¬ Win S K (n - (runHist (defender S K) N i).length - 1)
          (runHist (defender S K) N i ++ [(N i, c)]) := by
      refine ⟨c, hc, ?_⟩
      rw [length_runHist]
      exact hw
    have hstep : runCol (defender S K) N i = hx.choose := by
      unfold runCol defender
      dsimp only
      exact dite_eq_left hx
    rw [runHist_succ, hstep]
    have := hx.choose_spec.2
    have e2 : n - (runHist (defender S K) N i).length - 1 = n - (i + 1) := by
      rw [length_runHist]
      omega
    exact fun hW => this ((congrArg (fun d => Win S K d _) e2).mpr hW)

/-- **Zermelo's theorem for this game.**  If every proper algorithm uses at least `K` colours on
some member of `S`, then the start position is won by the adversary. -/
theorem win_nil (h : ∀ A : OnlineAlg, A.IsProper → ∃ I ∈ S, K ≤ I.cost A) : Win S K n [] := by
  by_contra h0
  obtain ⟨I, hI, hK⟩ := h (defender S K) (defender_isProper S K)
  have h1 := not_win_runHist S K h0 I.seq n le_rfl
  rw [Nat.sub_self, win_zero] at h1
  apply h1
  refine ⟨I, hI, length_runHist n, fun i hi => by rw [getElem_runHist], ?_⟩
  rw [usedColours_runHist, ← OnlineInput.image_univ_fin]
  exact hK

open Classical in
/-- The adversary's strategy: a winning move if there is one; stop otherwise, and after `n`
vertices. -/
noncomputable def strat : Adversary :=
  ⟨fun h =>
    if hx : h.length < n ∧ ∃ s : Finset ℕ, ∀ c, c ∉ nbrColours h s →
        Win S K (n - h.length - 1) (h ++ [(s, c)]) then
      some hx.2.choose
    else none⟩

theorem strat_move_of_length {h : History} (hn : n ≤ h.length) : (strat S K).move h = none := by
  unfold strat
  dsimp only
  exact dite_eq_right fun hx => absurd hx.1 (not_lt.2 hn)

variable {S K}

/-- Along every play of `strat` from a won start position, after `p ≤ n` rounds `p` vertices
have been presented and the position is won with `n - p` rounds to go. -/
theorem strat_invariant (h0 : Win S K n []) {A : OnlineAlg} (hA : A.IsProper) :
    ∀ p ≤ n, ((strat S K).hist A p).length = p ∧ Win S K (n - p) ((strat S K).hist A p) := by
  intro p
  induction p with
  | zero => exact fun _ => ⟨rfl, h0⟩
  | succ p ih =>
    intro hp
    obtain ⟨hlen, hw⟩ := ih (by omega)
    have e : n - p = (n - (p + 1)) + 1 := by omega
    rw [e, win_succ] at hw
    have hx : ((strat S K).hist A p).length < n ∧ ∃ s : Finset ℕ,
        ∀ c, c ∉ nbrColours ((strat S K).hist A p) s →
          Win S K (n - ((strat S K).hist A p).length - 1)
            ((strat S K).hist A p ++ [(s, c)]) := by
      rw [hlen]
      exact ⟨by omega, hw⟩
    have hmove : (strat S K).move ((strat S K).hist A p) = some hx.2.choose := by
      unfold strat
      dsimp only
      exact dite_eq_left hx
    rw [hist_succ_of_some hmove]
    refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
    have := hx.2.choose_spec (A.step ((strat S K).hist A p) hx.2.choose)
      ((OnlineAlg.isProper_iff A).1 hA _ _)
    have e2 : n - ((strat S K).hist A p).length - 1 = n - (p + 1) := by omega
    exact (congrArg (fun d => Win S K d _) e2).mp this

theorem strat_move_ne_none (h0 : Win S K n []) {A : OnlineAlg} (hA : A.IsProper) {p : ℕ}
    (hp : p < n) : (strat S K).move ((strat S K).hist A p) ≠ none := by
  intro hnone
  have h1 := strat_invariant h0 hA (p + 1) hp
  rw [hist_succ_of_none hnone, (strat_invariant h0 hA p hp.le).1] at h1
  omega

end Game

/-! ### Adversaries that present a set of inputs -/

/-- `adv` *presents `S` and forces `K`*: in the play against any proper algorithm `A`, the
adversary presents some member `I` of `S` in full, in its arrival order, and then stops, and `A`
uses at least `K` colours on `I`.  (The history after `p` rounds is the run of `A` on the first
`min p n` vertices of `I`, and the adversary has stopped after `p` rounds iff `n ≤ p`.) -/
def Presents {n : ℕ} (adv : Adversary) (S : Set (OnlineInput n)) (K : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ I ∈ S, K ≤ I.cost A ∧
    ∀ p, adv.hist A p = runHist A I.seq (min p n) ∧ (adv.StopsAt A p ↔ n ≤ p)

/-- **The determinacy lemma.**  If every proper deterministic algorithm uses at least `K` colours
on some member of the set `S` of online inputs on `n` vertices, then one adversary presents `S`
and forces `K`. -/
theorem exists_presents {n K : ℕ} (S : Set (OnlineInput n))
    (h : ∀ A : OnlineAlg, A.IsProper → ∃ I ∈ S, K ≤ I.cost A) :
    ∃ adv : Adversary, Presents adv S K := by
  have h0 := win_nil S K h
  refine ⟨strat S K, fun A hA => ?_⟩
  obtain ⟨hlen, hw⟩ := strat_invariant h0 hA n le_rfl
  rw [Nat.sub_self, win_zero] at hw
  obtain ⟨I, hI, -, hseq, hK⟩ := hw
  have hstop : (strat S K).StopsAt A n := strat_move_of_length S K hlen.ge
  -- the histories of the play are runs of `A` on `I`
  have hrun : ∀ p ≤ n, (strat S K).hist A p = runHist A I.seq p := by
    intro p hp
    have hpre := hist_prefix (strat S K) A hp
    have hlp := (strat_invariant h0 hA p hp).1
    have := eq_runHist_of_isRunOf (N := I.seq) ((strat S K).isRunOf_hist A p) fun i hi => by
      rw [hpre.getElem hi]
      exact hseq i _
    rwa [hlp] at this
  have hfin : (strat S K).hist A n = runHist A I.seq n := hrun n le_rfl
  refine ⟨I, hI, ?_, fun p => ?_⟩
  · rw [hfin, usedColours_runHist, ← OnlineInput.image_univ_fin] at hK
    exact hK
  · rcases Nat.lt_or_ge p n with hp | hp
    · rw [min_eq_left hp.le]
      refine ⟨hrun p hp.le, ?_⟩
      constructor
      · exact fun hs => absurd hs (strat_move_ne_none h0 hA hp)
      · exact fun hnp => absurd hp (not_lt.2 hnp)
    · rw [min_eq_right hp, hist_eq_of_stopsAt hstop p hp]
      refine ⟨hfin, fun _ => hp, fun _ => ?_⟩
      change (strat S K).move ((strat S K).hist A p) = none
      rw [hist_eq_of_stopsAt hstop p hp]
      exact hstop

namespace Presents

variable {n K : ℕ} {adv : Adversary} {S : Set (OnlineInput n)}

/-- The whole play, in one statement: for every proper `A` there is a member `I` of `S` such
that every stopped history of the play is the full run of `A` on `I`. -/
theorem final_hist (h : Presents adv S K) {A : OnlineAlg} (hA : A.IsProper) :
    ∃ I ∈ S, K ≤ I.cost A ∧ ∀ p, adv.StopsAt A p → adv.hist A p = runHist A I.seq n := by
  obtain ⟨I, hI, hK, hp⟩ := h A hA
  refine ⟨I, hI, hK, fun p hs => ?_⟩
  have := (hp p).1
  rwa [min_eq_right ((hp p).2.1 hs)] at this

/-- The final graph of every play is the graph of a member of `S`, in its arrival order, and
the algorithm has used at least `K` colours on it. -/
theorem final_graph (h : Presents adv S K) {A : OnlineAlg} (hA : A.IsProper) :
    ∃ I ∈ S, K ≤ I.cost A ∧ ∀ p, adv.StopsAt A p →
      ∃ e : (adv.hist A p).length = n, (adv.hist A p).graph = I.graph.comap (Fin.cast e) := by
  obtain ⟨I, hI, hK, hp⟩ := h.final_hist hA
  refine ⟨I, hI, hK, fun p hs => ?_⟩
  have e : (adv.hist A p).length = n := by rw [hp p hs, length_runHist]
  refine ⟨e, ?_⟩
  have key : ∀ (h' : History) (e' : h'.length = n), h' = runHist A I.seq n →
      h'.graph = I.graph.comap (Fin.cast e') := by
    rintro h' e' rfl
    exact graph_runHist A I e'
  exact key _ e (hp p hs)

/-- The adversary forces `K` colours. -/
theorem forces (h : Presents adv S K) : adv.Forces K := by
  intro A hA
  obtain ⟨I, -, hK, hp⟩ := h A hA
  refine ⟨n, (hp n).2.2 le_rfl, ?_⟩
  rw [(hp n).1, min_self, usedColours_runHist, ← OnlineInput.image_univ_fin]
  exact hK

/-- The adversary has size at most `n`. -/
theorem sizeLE (h : Presents adv S K) : adv.SizeLE n := by
  intro A hA p
  obtain ⟨I, -, -, hp⟩ := h A hA
  rw [(hp p).1, length_runHist]
  exact min_le_right _ _

/-- The adversary lands in every class of ordered graphs that contains the graphs of `S`. -/
theorem landsIn (h : Presents adv S K) {C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop}
    (hC : ∀ I ∈ S, C n I.graph) : adv.LandsIn C := by
  intro A hA p hs
  obtain ⟨I, hI, -, hp⟩ := h.final_graph hA
  obtain ⟨e, hg⟩ := hp p hs
  rw [hg]
  exact class_cast e (hC I hI)

/-- Every play has exactly `n` vertices when it stops. -/
theorem length_of_stopsAt (h : Presents adv S K) {A : OnlineAlg} (hA : A.IsProper) {p : ℕ}
    (hs : adv.StopsAt A p) : (adv.hist A p).length = n := by
  obtain ⟨I, -, -, hp⟩ := h.final_hist hA
  rw [hp p hs, length_runHist]

theorem mono (h : Presents adv S K) {S' : Set (OnlineInput n)} {K' : ℕ} (hS : S ⊆ S')
    (hK : K' ≤ K) : Presents adv S' K' := by
  intro A hA
  obtain ⟨I, hI, hc, hp⟩ := h A hA
  exact ⟨I, hS hI, hK.trans hc, hp⟩

end Presents

/-! ### Deleting indices that are not earlier vertices -/

/-- The neighbour set of vertex `i` in `h`, restricted to the earlier vertices. -/
def cleanSet (h : History) (i : ℕ) : Finset ℕ := ((h.getD i (∅, 0)).1).filter (· < i)

/-- The history `h` with every neighbour set restricted to the earlier vertices. -/
def clean (h : History) : History :=
  (List.range h.length).map fun i => (cleanSet h i, colourAt h i)

@[simp] theorem length_clean (h : History) : (clean h).length = h.length := by simp [clean]

theorem cleanSet_valid (h : History) : ValidSeq (cleanSet h) := by
  intro i x hx
  exact Finset.mem_range.2 (Finset.mem_filter.1 hx).2

theorem cleanSet_append_left {l l' : History} {i : ℕ} (hi : i < l.length) :
    cleanSet (l ++ l') i = cleanSet l i := by
  simp [cleanSet, List.getElem?_append_left hi]

theorem colourAt_append_left {l l' : History} {i : ℕ} (hi : i < l.length) :
    colourAt (l ++ l') i = colourAt l i := by
  simp [colourAt, List.getElem?_append_left hi]

theorem clean_append (l : History) (s : Finset ℕ) (c : ℕ) :
    clean (l ++ [(s, c)]) = clean l ++ [(s.filter (· < l.length), c)] := by
  unfold clean
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · exact List.map_congr_left fun i hi => by
      rw [cleanSet_append_left (List.mem_range.1 hi), colourAt_append_left (List.mem_range.1 hi)]
  · simp [cleanSet, colourAt]

theorem colourAt_clean (h : History) {i : ℕ} (hi : i < h.length) :
    colourAt (clean h) i = colourAt h i := by
  rw [colourAt_eq_getElem (by simpa using hi)]
  simp [clean]

theorem nbrColours_clean (h : History) (s : Finset ℕ) :
    nbrColours (clean h) (s.filter (· < h.length)) = nbrColours h s := by
  unfold nbrColours
  rw [length_clean, Finset.filter_filter]
  have : (s.filter fun a => a < h.length ∧ a < h.length) = s.filter (· < h.length) := by
    ext a
    simp
  rw [this]
  exact Finset.image_congr fun i hi => colourAt_clean h (Finset.mem_filter.1 hi).2

theorem usedColours_clean (h : History) : usedColours (clean h) = usedColours h := by
  unfold usedColours
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < h.length := by simpa using h2
    simp [clean, colourAt, List.getElem?_eq_getElem hi]

/-- `A` behind a filter that deletes, from every neighbour set, the indices that are not earlier
vertices. -/
def cleanAlg (A : OnlineAlg) : OnlineAlg :=
  ⟨fun h s => A.step (clean h) (s.filter (· < h.length))⟩

theorem cleanAlg_isProper {A : OnlineAlg} (hA : A.IsProper) : (cleanAlg A).IsProper := by
  rw [OnlineAlg.isProper_iff] at hA ⊢
  intro h s
  rw [← nbrColours_clean]
  exact hA _ _

/-- A history produced by `cleanAlg A`, cleaned, is a run of `A` on an honest input sequence. -/
theorem clean_eq_runHist {A : OnlineAlg} :
    ∀ {h : History}, IsRunOf (cleanAlg A) h → clean h = runHist A (cleanSet h) h.length := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l a ih =>
    intro hrun
    have hl := ih (IsRunOf.of_append hrun)
    have ha2 : a.2 = A.step (clean l) (a.1.filter (· < l.length)) := IsRunOf.last hrun
    have hlast : cleanSet (l ++ [a]) l.length = a.1.filter (· < l.length) := by
      simp [cleanSet]
    have hcongr : runHist A (cleanSet (l ++ [a])) l.length = runHist A (cleanSet l) l.length :=
      runHist_congr fun j hj => cleanSet_append_left hj
    obtain ⟨s, c⟩ := a
    rw [clean_append, List.length_append, List.length_singleton, runHist_succ, runCol, hcongr,
      ← hl, hlast]
    exact congrArg (fun x => clean l ++ [(s.filter (· < l.length), x)]) ha2

/-- The honest input given by a history has the graph of the history. -/
theorem graph_ofSeq_cleanSet (h : History) :
    (OnlineInput.ofSeq (cleanSet h) (cleanSet_valid h) h.length).graph = h.graph := by
  ext u v
  rw [OnlineInput.ofSeq_adj, History.graph_adj]
  have key : ∀ a b : Fin h.length,
      ((a : ℕ) ∈ cleanSet h b ↔ (a : ℕ) < b ∧ (a : ℕ) ∈ (h.get b).1) := by
    intro a b
    simp [cleanSet, and_comm]
  rw [key u v, key v u]

/-- **From a play to an input.**  A stopped or unstopped play of any adversary against
`cleanAlg A` is a run of `A` on an honest online input: there is an input on the vertices
presented so far with the graph of the history, on which the cost of `A` is the number of colours
of the history. -/
theorem exists_input_of_hist (adv : Adversary) (A : OnlineAlg) (p : ℕ) :
    ∃ I : OnlineInput (adv.hist (cleanAlg A) p).length,
      I.graph = (adv.hist (cleanAlg A) p).graph ∧
      I.cost A = (usedColours (adv.hist (cleanAlg A) p)).card := by
  refine ⟨OnlineInput.ofSeq (cleanSet _) (cleanSet_valid _) _, graph_ofSeq_cleanSet _, ?_⟩
  rw [OnlineInput.cost_ofSeq, ← usedColours_runHist,
    ← clean_eq_runHist (adv.isRunOf_hist (cleanAlg A) p), usedColours_clean]

/-! ### Observation 4.3 -/

/-- Padding, for inputs: a `k`-colourable input on `m ≤ n` vertices on which `A` uses `K` colours
gives one on exactly `n` vertices. -/
theorem exists_input_of_le {A : OnlineAlg} {m n k K : ℕ} (hk : 1 ≤ k) (hmn : m ≤ n)
    (I : OnlineInput m) (hc : I.graph.Colorable k) (hK : K ≤ I.cost A) :
    ∃ I' : OnlineInput n, I'.graph.Colorable k ∧ K ≤ I'.cost A := by
  rw [← OnlineInput.ofSeq_seq I] at hc hK
  rw [OnlineInput.cost_ofSeq] at hK
  exact exists_input_of_seq I.seq_valid hk hmn hc hK

/-- Observation 4.3, `⇐` ("run the adversary and append isolated vertices"). -/
theorem chiDetAtLeast_of_NkLE {k n K : ℕ} (hk : 1 ≤ k) (h : NkLE k K n) :
    ChiDetAtLeast k n K := by
  obtain ⟨adv, hF, hS, hL⟩ := h
  intro A hA
  have hA' := cleanAlg_isProper hA
  obtain ⟨p, hstop, hK⟩ := hF (cleanAlg A) hA'
  have hc := hL (cleanAlg A) hA' p hstop
  have hlen := hS (cleanAlg A) hA' p
  have hrun := clean_eq_runHist (adv.isRunOf_hist (cleanAlg A) p)
  rw [← usedColours_clean, hrun, usedColours_runHist] at hK
  rw [← graph_ofSeq_cleanSet] at hc
  exact exists_input_of_seq (cleanSet_valid _) hk hlen hc hK

/-- Observation 4.3, `⇒` (Zermelo's theorem). -/
theorem NkLE_of_chiDetAtLeast {k n K : ℕ} (h : ChiDetAtLeast k n K) : NkLE k K n := by
  obtain ⟨adv, hadv⟩ := exists_presents {I : OnlineInput n | I.graph.Colorable k} h
  exact ⟨adv, hadv.forces, hadv.sizeLE, hadv.landsIn fun I hI => hI⟩

theorem chiDetAtLeast_iff_NkLE {k n K : ℕ} (hk : 1 ≤ k) : ChiDetAtLeast k n K ↔ NkLE k K n :=
  ⟨NkLE_of_chiDetAtLeast, chiDetAtLeast_of_NkLE hk⟩

/-- **Observation 4.3 (determinacy).**  `χ^det_k(n) ≥ K` if and only if `N_k(K) ≤ n`. -/
theorem le_chiDet_iff_Nk_le {k n K : ℕ} (hk : 1 ≤ k) : K ≤ chiDet k n ↔ Nk k K ≤ n := by
  rw [le_chiDet_iff hk, Nk_le_iff, chiDetAtLeast_iff_NkLE hk]

/-- **Observation 4.3, "In particular".**  It suffices to exhibit, for every deterministic
algorithm, an ordered `k`-colourable graph on at most `n` vertices on which the algorithm uses `K`
colours: then `N_k(K) ≤ n`. -/
theorem Nk_le_of_forall_alg {k n K : ℕ} (hk : 1 ≤ k)
    (h : ∀ A : OnlineAlg, A.IsProper →
      ∃ m ≤ n, ∃ I : OnlineInput m, I.graph.Colorable k ∧ K ≤ I.cost A) : Nk k K ≤ n := by
  rw [Nk_le_iff, ← chiDetAtLeast_iff_NkLE hk]
  intro A hA
  obtain ⟨m, hmn, I, hc, hK⟩ := h A hA
  exact exists_input_of_le hk hmn I hc hK

/-- Observation 4.3, "In particular", for `χ^det`. -/
theorem le_chiDet_of_forall_alg {k n K : ℕ} (hk : 1 ≤ k)
    (h : ∀ A : OnlineAlg, A.IsProper →
      ∃ m ≤ n, ∃ I : OnlineInput m, I.graph.Colorable k ∧ K ≤ I.cost A) : K ≤ chiDet k n :=
  (le_chiDet_iff_Nk_le hk).2 (Nk_le_of_forall_alg hk h)

end Det

end OnlineColouring
