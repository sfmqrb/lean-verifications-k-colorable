module

public import OnlineColouring.BlowUp
public import OnlineColouring.Cliques

/-!
# Label posets and the colourability of iterated blow-ups

* `labelPoset k j` is the label poset `P_j(k)`: `P_0(k)` is the antichain on `Fin k` and
  `P_{j+1}(k) = J*(P_j(k))`.  It is bundled (`FinPoset`) so that the recursion can carry the
  `Fintype`/decidability instances; `LabelPoset k j` is its carrier type, and
  `LabelPoset k (j+1)` is definitionally `Jst (LabelPoset k j)`.
* `OrdGraph` bundles an ordered graph (a `SimpleGraph` on a linearly ordered type).
* `IsFullTower m j G`: `G` is obtained from the arrival-ordered clique `K_m` by `j` successive
  full blow-ups.  This is the full `j`-level tower over `K_m` of Definition 4.7 (towers), first
  sentence.  The `j`-level towers of the last sentence of that definition, the initial segments
  of a full `j`-level tower, possibly followed by isolated vertices, are `IsPaddedTower`
  (`CeilingPadded.lean`).
* `IsTower m j G`: the same without fullness, that is, `G` is a `j`-fold blow-up of `K_m` as in
  Corollary 5.4.
* Corollary 5.4 (colourability of iterated blow-ups): `IsTower.colorable`,
  `IsTower.colorable_induce` and `IsFullTower.le_card`; as an equivalence,
  `IsFullTower.colorable_iff`.  The hypotheses `k ≥ 2` and `m ≥ 1` of the paper are not needed.
-/

@[expose] public section

namespace OnlineColouring

/-- A finite poset with decidable equality and decidable order, bundled. -/
structure FinPoset where
  /-- The underlying type. -/
  carrier : Type
  [instPartialOrder : PartialOrder carrier]
  [instFintype : Fintype carrier]
  [instDecidableEq : DecidableEq carrier]
  [instDecidableLE : DecidableLE carrier]

attribute [instance] FinPoset.instPartialOrder FinPoset.instFintype FinPoset.instDecidableEq
  FinPoset.instDecidableLE

namespace FinPoset

/-- Bundle a finite poset. -/
def of (P : Type) [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P] : FinPoset := ⟨P⟩

/-- `J*` on bundled finite posets. -/
def jst (P : FinPoset) : FinPoset := of (Jst P.carrier)

end FinPoset

/-- The label posets: `labelPoset k 0 = P_0(k)` is the antichain on `Fin k`, and
`labelPoset k (j+1) = J*(labelPoset k j)`. -/
def labelPoset (k : ℕ) : ℕ → FinPoset
  | 0 => FinPoset.of (Anti (Fin k))
  | j + 1 => (labelPoset k j).jst

/-- The label poset `P_j(k)` as a type. -/
abbrev LabelPoset (k j : ℕ) : Type := (labelPoset k j).carrier

theorem labelPoset_zero (k : ℕ) : LabelPoset k 0 = Anti (Fin k) := rfl

theorem labelPoset_succ (k j : ℕ) : LabelPoset k (j + 1) = Jst (LabelPoset k j) := rfl

@[simp] theorem card_labelPoset_zero (k : ℕ) : Fintype.card (LabelPoset k 0) = k := by
  change Fintype.card (Fin k) = k
  simp

/-- A `P_0(k)`-labelling is a proper `k`-colouring. -/
theorem hasLabelling_labelPoset_zero_iff {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {k : ℕ} : HasLabelling G (LabelPoset k 0) ↔ G.Colorable k :=
  hasLabelling_anti_fin_iff_colorable

/-- An ordered graph: a simple graph on a linearly ordered type (the arrival order). -/
structure OrdGraph where
  /-- The vertex type. -/
  V : Type
  [instLinearOrder : LinearOrder V]
  /-- The graph. -/
  G : SimpleGraph V

attribute [instance] OrdGraph.instLinearOrder

/-- The arrival-ordered clique `K_m = (v_1, …, v_m)`. -/
def OrdGraph.clique (m : ℕ) : OrdGraph := ⟨Fin m, ⊤⟩

/-- `IsTower m j G`: the ordered graph `G` is a `j`-fold blow-up of the clique `K_m`, i.e. there
are ordered graphs `K_m = H^{(j)}, H^{(j-1)}, …, H^{(0)} = G`, each a blow-up of the previous
one. -/
inductive IsTower (m : ℕ) : ℕ → OrdGraph → Prop
  | clique : IsTower m 0 (OrdGraph.clique m)
  | blowUp {j : ℕ} {H G : OrdGraph} :
      IsTower m j H → Nonempty (BlowUp H.G G.G) → IsTower m (j + 1) G

/-- `IsFullTower m j G`: a `j`-fold blow-up of `K_m` in which all `j` blow-ups are full.  This is
the full `j`-level tower over `K_m` of Definition 4.7. -/
inductive IsFullTower (m : ℕ) : ℕ → OrdGraph → Prop
  | clique : IsFullTower m 0 (OrdGraph.clique m)
  | blowUp {j : ℕ} {H G : OrdGraph} :
      IsFullTower m j H → (∃ B : BlowUp H.G G.G, B.IsFull) → IsFullTower m (j + 1) G

theorem IsFullTower.isTower {m j : ℕ} {G : OrdGraph} (h : IsFullTower m j G) : IsTower m j G := by
  induction h with
  | clique => exact .clique
  | blowUp _ hB ih =>
    obtain ⟨B, -⟩ := hB
    exact .blowUp ih ⟨B⟩

/-- Labels descend through iterated blow-ups: if `m ≤ |P_{i+j}(k)|`, then every `j`-fold blow-up
of `K_m` has a `P_i(k)`-labelling. -/
theorem IsTower.hasLabelling {m j : ℕ} {G : OrdGraph} (hT : IsTower m j G) (k : ℕ) :
    ∀ i, m ≤ Fintype.card (LabelPoset k (i + j)) → HasLabelling G.G (LabelPoset k i) := by
  induction hT with
  | clique =>
    intro i hm
    exact hasLabelling_clique_iff.2 hm
  | @blowUp j H G _ hB ih =>
    intro i hm
    obtain ⟨B⟩ := hB
    have e : i + (j + 1) = i + 1 + j := by omega
    rw [e] at hm
    exact B.hasLabelling_of_jst (ih (i + 1) hm)

/-- Labels ascend through a full tower: if a `j`-fold full blow-up of `K_m` has a
`P_i(k)`-labelling, then `m ≤ |P_{i+j}(k)|`. -/
theorem IsFullTower.le_card_of_hasLabelling {m j : ℕ} {G : OrdGraph} (hT : IsFullTower m j G)
    (k : ℕ) : ∀ i, HasLabelling G.G (LabelPoset k i) → m ≤ Fintype.card (LabelPoset k (i + j)) := by
  induction hT with
  | clique =>
    intro i h
    exact hasLabelling_clique_iff.1 h
  | @blowUp j H G _ hB ih =>
    intro i h
    obtain ⟨B, hBfull⟩ := hB
    have h' : HasLabelling H.G (LabelPoset k (i + 1)) := B.hasLabelling_jst_of_full hBfull h
    have e : i + 1 + j = i + (j + 1) := by omega
    rw [← e]
    exact ih (i + 1) h'

/-- **Corollary 5.4 (colourability of iterated blow-ups), first sentence.** If `m ≤ |P_j(k)|`,
then every `j`-fold blow-up of `K_m` is `k`-colourable. -/
theorem IsTower.colorable {m j k : ℕ} {G : OrdGraph} (hT : IsTower m j G)
    (hm : m ≤ Fintype.card (LabelPoset k j)) : G.G.Colorable k := by
  have hm' : m ≤ Fintype.card (LabelPoset k (0 + j)) := by rw [Nat.zero_add]; exact hm
  exact hasLabelling_labelPoset_zero_iff.1 (hT.hasLabelling k 0 hm')

/-- **Corollary 5.4 (colourability of iterated blow-ups), first sentence, induced subgraphs.**
If `m ≤ |P_j(k)|`, then every induced ordered subgraph of a `j`-fold blow-up of `K_m` is
`k`-colourable. -/
theorem IsTower.colorable_induce {m j k : ℕ} {G : OrdGraph} (hT : IsTower m j G)
    (hm : m ≤ Fintype.card (LabelPoset k j)) (s : Set G.V) : (G.G.induce s).Colorable k := by
  have hm' : m ≤ Fintype.card (LabelPoset k (0 + j)) := by rw [Nat.zero_add]; exact hm
  exact hasLabelling_labelPoset_zero_iff.1 ((hT.hasLabelling k 0 hm').induce s)

/-- **Corollary 5.4 (colourability of iterated blow-ups), converse.** If a `j`-fold blow-up of
`K_m` in which all `j` blow-ups are full is `k`-colourable, then `m ≤ |P_j(k)|`. -/
theorem IsFullTower.le_card {m j k : ℕ} {G : OrdGraph} (hT : IsFullTower m j G)
    (hG : G.G.Colorable k) : m ≤ Fintype.card (LabelPoset k j) := by
  have := hT.le_card_of_hasLabelling k 0 (hasLabelling_labelPoset_zero_iff.2 hG)
  rwa [Nat.zero_add] at this

/-- The threshold is exact: a full `j`-fold blow-up of `K_m` is `k`-colourable iff
`m ≤ |P_j(k)|`. -/
theorem IsFullTower.colorable_iff {m j k : ℕ} {G : OrdGraph} (hT : IsFullTower m j G) :
    G.G.Colorable k ↔ m ≤ Fintype.card (LabelPoset k j) :=
  ⟨hT.le_card, hT.isTower.colorable⟩

end OnlineColouring
