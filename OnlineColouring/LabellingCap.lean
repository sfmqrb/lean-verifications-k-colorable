module

public import OnlineColouring.TowerGrowth
public import OnlineColouring.Forcing

/-!
# Adversaries (Definition 4.2) and Proposition 9.4 (a cap for adversaries that commit to labels)

Proposition 9.4 (a cap for adversaries that commit to labels): *If
an adversary forces `K` colours and commits to labels from a poset `P`, then `K ≤ |J*(P)|`.  In
particular, an adversary that forces `K` colours can commit to labels from `P_j(k)` only if
`j ≥ lg* K - lg* k - 1`.*

For a nonempty poset `P`, an adversary *commits to labels from `P`* if, right after the algorithm
has coloured a vertex `v`, it assigns a label `ψ(v) ∈ P` that is a function of the history so far
(the graph presented and the colours given), such that `ψ(u) ≰ ψ(v)` for every edge `uv` with `u`
earlier.

## Formalization

A history (`History`, from `Online.lean`) is exactly "the graph presented and the colours
given": the list of the pairs `(N⁻(i), colour of i)`.  So a labelling rule is a function
`ψ : History → P`, and the label of vertex `i` in a play with history `h` is
`ψ (h.take (i + 1))`, i.e. `ψ` applied to the history right after `i` was coloured.
`LabelsHist ψ h` says that these labels form a `P`-labelling of the ordered graph of `h`.

* `labelAlg ψ` is the algorithm of the paper's proof: it colours the new vertex `v` with (a number
  of) the down-set `U(v) = {p ∈ P : ψ(u) ≰ p for all u ∈ N⁻(v)}` (`labelSet`).  It only needs `ψ`,
  not the adversary.  If `U(v)` is empty it takes the number `0`, and where its number clashes
  with the colour of an earlier neighbour it falls back to a fresh colour, so it is proper on
  every history (`labelAlg_isProper`); in plays where `ψ` is a labelling neither happens
  (`label_mem_labelSet`, `labelAlg_colour`).  The paper numbers the nonempty down-sets in the
  order of their first appearance; here the numbering of `J*(P)` is fixed in advance (`jstCode`).
* Core statement (`card_usedColours_le_of_labelsHist`): on every history produced by `labelAlg ψ`
  on which `ψ` is a labelling, at most `|J*(P)|` colours are used.

Three forms of the proposition:

* Inputs (`OnlineInput.cost_labelAlg_le`): on every online input on which the labels
  `v ↦ ψ(history after v)` of the run of `labelAlg ψ` form a `P`-labelling, `labelAlg ψ` uses at
  most `|J*(P)|` colours.
* "For every algorithm an input" (`le_card_jst_of_labelled_inputs`), the form of the modules that
  prove lower bounds through inputs against a fixed algorithm: if `ψ : History → P` is fixed and
  every proper algorithm `A` has an input on which it uses `K` colours and on which `ψ` labels the
  run of `A`, then `K ≤ |J*(P)|`.  Here `ψ` is fixed before `A`, as in the paper, where the
  labelling rule is part of the adversary.  This matters: if `ψ` could depend on `A`, it could
  label every hard input of Theorem 1.2 by its final `k`-colouring (labels from `P_0(k)`),
  contradicting `K ≤ 2^k - 1`.
* Adversaries (`Adversary.le_card_jst`), with Definition 4.2 (adversaries) formalized literally:
  `Adversary` is a rule `History → Option (Finset ℕ)` (`none` = stop), `Adversary.Forces K` says
  that every play against every proper algorithm stops with at least `K` colours in use, and
  `Adversary.CommitsTo ψ` says that in every play against every proper algorithm the labels given
  by `ψ` form a `P`-labelling.  This is the proposition as the paper states it.  The other notions
  of Definition 4.2 (size, post-degree, landing in a class of ordered graphs) and `N_k(K)` are in
  `AdvBasic.lean`.

Corollaries: `Adversary.logStar_sub_le_of_commitsTo` (labels from `P_j(k)` need
`j ≥ lg* K - lg* k - 1`) and `Adversary.le_two_pow_of_commitsTo_colouring` (an adversary that
commits to a proper `k`-colouring, i.e. labels from `P_0(k)`, forces at most `2^k - 1` colours:
the transparent model, and the stricter known-graph game of the remark at the end of Section 7).

Non-vacuity: `Adversary.clique_forces` and `Adversary.clique_commitsTo` show that the clique
adversary `Adversary.clique K` forces `K` colours and commits to labels from the chain
`(Fin K)ᵒᵈ` (vertex `i` gets label `i`), so `Forces` and `CommitsTo` are satisfiable together.
The bound is attained there: the chain on `K` elements has `K` nonempty down-sets.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Histories produced by an algorithm -/

/-- `h` is a history that `A` produces: the colour of every vertex is the colour that `A` gives
it, given the history before it and its earlier-neighbour set. -/
def IsRunOf (A : OnlineAlg) (h : History) : Prop :=
  ∀ i (hi : i < h.length), h[i].2 = A.step (h.take i) h[i].1

theorem isRunOf_nil (A : OnlineAlg) : IsRunOf A [] := fun _ hi => absurd hi (by simp)

theorem IsRunOf.append_step {A : OnlineAlg} {h : History} (hh : IsRunOf A h) (s : Finset ℕ) :
    IsRunOf A (h ++ [(s, A.step h s)]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rw [List.getElem_append_left hi, List.take_append_of_le_length hi.le]
    exact hh i hi
  · simp

theorem isRunOf_runHist (A : OnlineAlg) (N : ℕ → Finset ℕ) (p : ℕ) :
    IsRunOf A (runHist A N p) := by
  induction p with
  | zero => exact isRunOf_nil A
  | succ p ih => exact ih.append_step (N p)

theorem runHist_take {A : OnlineAlg} {N : ℕ → Finset ℕ} {p q : ℕ} (hq : q ≤ p) :
    (runHist A N p).take q = runHist A N q := by
  rw [runHist_eq_map, runHist_eq_map, ← List.map_take, List.take_range, min_eq_left hq]

/-- The colours used in a history. -/
def usedColours (h : History) : Finset ℕ := (h.map Prod.snd).toFinset

theorem usedColours_runHist (A : OnlineAlg) (N : ℕ → Finset ℕ) (n : ℕ) :
    usedColours (runHist A N n) = (range n).image (runCol A N) := by
  ext c
  simp [usedColours, runHist_eq_map]

/-! ### Labels along a history -/

variable {P : Type*} [PartialOrder P]

/-- `ψ` labels the history `h`: if `u` is an earlier neighbour of `v`, then `ψ(u) ≰ ψ(v)`, where
the label of the vertex `i` is `ψ` of the history right after `i` was coloured. -/
def LabelsHist (ψ : History → P) (h : History) : Prop :=
  ∀ i j (hj : j < h.length), i < j → i ∈ h[j].1 → ¬ ψ (h.take (i + 1)) ≤ ψ (h.take (j + 1))

/-- The labels that `ψ` gives along the run of `A` on `I`: the label of `v` is `ψ` of the history
right after `v` was coloured. -/
def runLabel {n : ℕ} (ψ : History → P) (A : OnlineAlg) (I : OnlineInput n) (v : Fin n) : P :=
  ψ (runHist A I.seq (v + 1))

theorem labelsHist_runHist {ψ : History → P} {n : ℕ} {A : OnlineAlg} {I : OnlineInput n}
    (hψ : IsLabelling I.graph (runLabel ψ A I)) : LabelsHist ψ (runHist A I.seq n) := by
  intro i j hj hij hmem
  rw [length_runHist] at hj
  rw [getElem_runHist] at hmem
  simp only [OnlineInput.seq, hj, ↓reduceDIte, Finset.mem_map, Fin.valEmbedding_apply] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  rw [runHist_take (by omega), runHist_take (by omega)]
  exact hψ (Fin.lt_def.2 hij) (Or.inl hu)

theorem take_take_succ {h : History} {i u : ℕ} (hu : u < i) :
    (h.take i).take (u + 1) = h.take (u + 1) := by
  rw [List.take_take, min_eq_left (by omega)]

/-! ### The label-down-set algorithm -/

variable [Fintype P] [DecidableLE P]

/-- `U(v)`: the labels `p` such that `ψ(u) ≰ p` for every earlier neighbour `u` of the new vertex
(`s` is its earlier-neighbour set, `h` the history before it). -/
def labelSet (ψ : History → P) (h : History) (s : Finset ℕ) : Finset P :=
  univ.filter fun p => ∀ u ∈ s, u < h.length → ¬ ψ (h.take (u + 1)) ≤ p

theorem mem_labelSet {ψ : History → P} {h : History} {s : Finset ℕ} {p : P} :
    p ∈ labelSet ψ h s ↔ ∀ u ∈ s, u < h.length → ¬ ψ (h.take (u + 1)) ≤ p := by
  simp [labelSet]

/-- `U(v)` is a down-set. -/
theorem isLowerFinset_labelSet (ψ : History → P) (h : History) (s : Finset ℕ) :
    IsLowerFinset (labelSet ψ h s) := by
  intro a ha b hba
  rw [mem_labelSet] at ha ⊢
  exact fun u hu hul hle => ha u hu hul (hle.trans hba)

section Labels

variable {ψ : History → P} {h : History}

/-- The label of `v` lies in `U(v)`. -/
theorem label_mem_labelSet (hlab : LabelsHist ψ h) {i : ℕ} (hi : i < h.length) :
    ψ (h.take (i + 1)) ∈ labelSet ψ (h.take i) h[i].1 := by
  rw [mem_labelSet]
  intro u hu hul
  rw [List.length_take, lt_min_iff] at hul
  rw [take_take_succ hul.1]
  exact hlab u i hi hul.1 hu

/-- The label of an earlier neighbour `u` of `v` does not lie in `U(v)`. -/
theorem label_notMem_labelSet {i u : ℕ} (hi : i < h.length) (hu : u ∈ h[i].1) (hui : u < i) :
    ψ (h.take (u + 1)) ∉ labelSet ψ (h.take i) h[i].1 := by
  rw [mem_labelSet]
  intro hall
  have := hall u hu (by rw [List.length_take]; omega)
  rw [take_take_succ hui] at this
  exact this le_rfl

end Labels

variable [DecidableEq P]

/-- A fixed numbering of the nonempty down-sets of `P` by natural numbers. -/
noncomputable def jstCode (d : Jst P) : ℕ := (Fintype.equivFin (Jst P) d : ℕ)

theorem jstCode_injective : Function.Injective (jstCode (P := P)) :=
  fun _ _ h => (Fintype.equivFin (Jst P)).injective (Fin.ext h)

/-- The colour of `U(v)` (`0` if `U(v)` is empty, which does not happen in labelled plays). -/
noncomputable def labelCol (ψ : History → P) (h : History) (s : Finset ℕ) : ℕ :=
  if hD : (labelSet ψ h s).Nonempty then
    jstCode (Jst.mk (labelSet ψ h s) (isLowerFinset_labelSet ψ h s) hD)
  else 0

/-- **The algorithm of Proposition 9.4.**  It colours the new vertex by its down-set `U(v)`,
patched with a fresh colour whenever that colour would clash (`OnlineAlg.patch`), so that it is
proper on every history. -/
noncomputable def labelAlg (ψ : History → P) : OnlineAlg := (⟨labelCol ψ⟩ : OnlineAlg).patch

theorem labelAlg_isProper (ψ : History → P) : (labelAlg ψ).IsProper :=
  OnlineAlg.patch_isProper _

variable {ψ : History → P} {h : History}

theorem labelCol_eq (hlab : LabelsHist ψ h) {i : ℕ} (hi : i < h.length) :
    labelCol ψ (h.take i) h[i].1 = jstCode (Jst.mk (labelSet ψ (h.take i) h[i].1)
      (isLowerFinset_labelSet _ _ _) ⟨_, label_mem_labelSet hlab hi⟩) := by
  rw [labelCol, dite_eq_left ⟨_, label_mem_labelSet hlab hi⟩]

/-- **The colouring of `labelAlg ψ` in a labelled play.**  If `labelAlg ψ` produced `h` and `ψ`
labels `h`, then every vertex is coloured by (the number of) its down-set `U(v)`: the fallback
is never used. -/
theorem labelAlg_colour (hrun : IsRunOf (labelAlg ψ) h) (hlab : LabelsHist ψ h) :
    ∀ i (hi : i < h.length), h[i].2 = labelCol ψ (h.take i) h[i].1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  rw [hrun i hi]
  change (if labelCol ψ _ _ ∈ nbrColours _ _ then _ else labelCol ψ _ _) = _
  refine ite_eq_right ?_
  intro hmem
  simp only [nbrColours, mem_image, mem_filter, List.length_take] at hmem
  obtain ⟨u, ⟨hu, hul⟩, hcol⟩ := hmem
  have hui : u < i := (lt_min_iff.1 hul).1
  have huh : u < h.length := hui.trans hi
  rw [colourAt_eq_getElem (by rw [List.length_take]; exact hul), List.getElem_take,
    ih u hui huh, labelCol_eq hlab huh, labelCol_eq hlab hi] at hcol
  have hD : labelSet ψ (h.take u) h[u].1 = labelSet ψ (h.take i) h[i].1 :=
    congrArg Jst.val (jstCode_injective hcol)
  have hmemu := label_mem_labelSet hlab huh
  rw [hD] at hmemu
  exact label_notMem_labelSet hi hu hui hmemu

/-- **Core of Proposition 9.4.**  On every history produced by `labelAlg ψ` on which `ψ` is a
labelling, at most `|J*(P)|` colours are used. -/
theorem card_usedColours_le_of_labelsHist (hrun : IsRunOf (labelAlg ψ) h)
    (hlab : LabelsHist ψ h) : (usedColours h).card ≤ Fintype.card (Jst P) := by
  have hsub : usedColours h ⊆ univ.image (jstCode (P := P)) := by
    intro c hc
    simp only [usedColours, List.mem_toFinset, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [labelAlg_colour hrun hlab i hi, labelCol_eq hlab hi]
    exact mem_image_of_mem _ (mem_univ _)
  exact (card_le_card hsub).trans (card_image_le.trans (by rw [card_univ]))

/-! ### Proposition 9.4 for online inputs -/

/-- **Proposition 9.4, input form.**  If the labels that `ψ` gives along the run of `labelAlg ψ` on
the input `I` form a `P`-labelling of `I`, then `labelAlg ψ` uses at most `|J*(P)|` colours on
`I`. -/
theorem OnlineInput.cost_labelAlg_le {n : ℕ} (I : OnlineInput n)
    (hψ : IsLabelling I.graph (runLabel ψ (labelAlg ψ) I)) :
    I.cost (labelAlg ψ) ≤ Fintype.card (Jst P) := by
  have h := card_usedColours_le_of_labelsHist (isRunOf_runHist (labelAlg ψ) I.seq n)
    (labelsHist_runHist hψ)
  rwa [usedColours_runHist, ← OnlineInput.image_univ_fin] at h

/-- **Proposition 9.4, "for every algorithm an input" form.**  Fix a labelling rule
`ψ : History → P`.  If every proper algorithm `A` has an input on which it uses at least `K`
colours and along whose run the labels given by `ψ` form a `P`-labelling, then `K ≤ |J*(P)|`. -/
theorem le_card_jst_of_labelled_inputs {n K : ℕ} (ψ : History → P)
    (h : ∀ A : OnlineAlg, A.IsProper →
      ∃ I : OnlineInput n, K ≤ I.cost A ∧ IsLabelling I.graph (runLabel ψ A I)) :
    K ≤ Fintype.card (Jst P) := by
  obtain ⟨I, hK, hψ⟩ := h (labelAlg ψ) (labelAlg_isProper ψ)
  exact hK.trans (I.cost_labelAlg_le hψ)

end OnlineColouring

/-! ### Adversaries (Definition 4.2) -/

namespace OnlineColouring

/-- An adversary (Definition 4.2): a deterministic rule that, given the history of the
play, either stops (`none`) or presents a new vertex together with its set of earlier neighbours
(as arrival indices; indices that are not earlier vertices are ignored by `History.graph` and by
properness, but an algorithm may react to them). -/
structure Adversary where
  /-- The next move. -/
  move : History → Option (Finset ℕ)

namespace Adversary

/-- The history after `p` rounds of the play of `adv` against `A`.  Once `adv` has stopped, the
history no longer changes. -/
def hist (adv : Adversary) (A : OnlineAlg) : ℕ → History
  | 0 => []
  | p + 1 =>
    match adv.move (hist adv A p) with
    | none => hist adv A p
    | some s => hist adv A p ++ [(s, A.step (hist adv A p) s)]

/-- `adv` forces `K` colours: every play against every proper deterministic online algorithm is
finite (reaches a history at which `adv` stops) and ends with at least `K` colours in use. -/
def Forces (adv : Adversary) (K : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper →
    ∃ p, adv.move (adv.hist A p) = none ∧ K ≤ (usedColours (adv.hist A p)).card

/-- `adv` commits to labels from `P` via the rule `ψ`: in every play against every proper
deterministic algorithm, the label `ψ(v)`, computed from the history right after `v` was coloured,
satisfies `ψ(u) ≰ ψ(v)` for every edge `uv` with `u` earlier. -/
def CommitsTo {P : Type*} [PartialOrder P] (adv : Adversary) (ψ : History → P) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, LabelsHist ψ (adv.hist A p)

theorem isRunOf_hist (adv : Adversary) (A : OnlineAlg) (p : ℕ) : IsRunOf A (adv.hist A p) := by
  induction p with
  | zero => exact isRunOf_nil A
  | succ p ih =>
    rw [hist]
    split
    · exact ih
    · exact ih.append_step _

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]

/-- **Proposition 9.4 (a cap for adversaries that commit to labels).**  If an adversary forces `K`
colours and commits to labels from `P`, then `K ≤ |J*(P)|`. -/
theorem le_card_jst {adv : Adversary} {K : ℕ} {ψ : History → P} (hK : adv.Forces K)
    (hψ : adv.CommitsTo ψ) : K ≤ Fintype.card (Jst P) := by
  obtain ⟨p, -, hp⟩ := hK (labelAlg ψ) (labelAlg_isProper ψ)
  exact hp.trans (card_usedColours_le_of_labelsHist (adv.isRunOf_hist _ p)
    (hψ _ (labelAlg_isProper ψ) p))

/-- **Proposition 9.4, second statement.**  An adversary that forces `K` colours can commit to
labels from `P_j(k)` only if `j ≥ lg* K - lg* k - 1`. -/
theorem logStar_sub_le_of_commitsTo {adv : Adversary} {K k j : ℕ} {ψ : History → LabelPoset k j}
    (hK : adv.Forces K) (hψ : adv.CommitsTo ψ) : logStar K - logStar k - 1 ≤ j := by
  have h : K ≤ Fintype.card (LabelPoset k (j + 1)) := le_card_jst hK hψ
  have := logStar_sub_logStar_le h
  omega

/-- For `P = P_0(k)` (an adversary that commits to a proper `k`-colouring vertex by vertex, the
transparent model) Proposition 9.4 gives at most `|P_1(k)| = 2^k - 1` colours. -/
theorem le_two_pow_of_commitsTo_colouring {adv : Adversary} {K k : ℕ}
    {ψ : History → LabelPoset k 0} (hK : adv.Forces K) (hψ : adv.CommitsTo ψ) :
    K ≤ 2 ^ k - 1 := by
  have h : K ≤ Fintype.card (LabelPoset k 1) := le_card_jst hK hψ
  rwa [card_labelPoset_one] at h

/-! ### Non-vacuity: the clique adversary -/

/-- The clique adversary: it presents `K` vertices, each adjacent to all earlier ones, and
stops. -/
def clique (K : ℕ) : Adversary :=
  ⟨fun h => if h.length < K then some (Finset.range h.length) else none⟩

theorem clique_hist (K : ℕ) (A : OnlineAlg) :
    ∀ p, (clique K).hist A p = runHist A cliqueSeq (min p K) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [hist, ih]
    rcases Nat.lt_or_ge p K with hp | hp
    · have hmove : (clique K).move (runHist A cliqueSeq (min p K)) = some (cliqueSeq p) := by
        simp [clique, cliqueSeq, min_eq_left hp.le, hp]
      rw [hmove, min_eq_left hp.le, min_eq_left (by omega : p + 1 ≤ K)]
      rfl
    · have hmove : (clique K).move (runHist A cliqueSeq (min p K)) = none := by
        simp [clique, min_eq_right hp]
      rw [hmove, min_eq_right hp, min_eq_right (by omega : K ≤ p + 1)]

/-- The clique adversary forces `K` colours. -/
theorem clique_forces (K : ℕ) : (clique K).Forces K := by
  intro A hA
  refine ⟨K, ?_, ?_⟩
  · rw [clique_hist, min_self]
    simp [clique]
  · rw [clique_hist, min_self, usedColours_runHist, card_image_runCol_cliqueSeq hA]

/-- The clique adversary commits to labels from the chain on `K` elements, ordered so that earlier
vertices get larger labels: the label of the `i`-th vertex is `i` in `(Fin K)ᵒᵈ`. -/
def cliqueLabel (K : ℕ) (hK : 1 ≤ K) (h : History) : (Fin K)ᵒᵈ :=
  OrderDual.toDual ⟨min (h.length - 1) (K - 1), by omega⟩

theorem clique_commitsTo (K : ℕ) (hK : 1 ≤ K) : (clique K).CommitsTo (cliqueLabel K hK) := by
  intro A _ p i j hj hij _
  rw [clique_hist] at hj ⊢
  rw [length_runHist] at hj
  simp only [cliqueLabel, OrderDual.toDual_le_toDual, Fin.le_def, List.length_take,
    length_runHist]
  omega

/-- So the hypotheses of Proposition 9.4 are satisfiable.  (The bound is tight here: the chain on
`K` elements has exactly `K` nonempty down-sets; this count is not formalized.) -/
example (K : ℕ) (hK : 1 ≤ K) : K ≤ Fintype.card (Jst (Fin K)ᵒᵈ) :=
  le_card_jst (clique_forces K) (clique_commitsTo K hK)

end Adversary

end OnlineColouring
