module

public import OnlineColouring.CeilingAsymptotic
public import OnlineColouring.Growth
public import OnlineColouring.PadGraph
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 1.5 (a ceiling for towers), for towers in the sense of Definition 4.7

Definition 4.7 ends with: *"A `j`-level tower is an initial segment of a full `j`-level tower,
possibly followed by isolated vertices."*  `Ceiling.lean` and `CeilingAsymptotic.lean` prove
Theorem 1.5 for initial segments `G.G.induce S` of full towers.  This file adds the trailing
isolated vertices and states both sentences of the theorem for towers in this sense.

* `IsPaddedTower m j H`: the ordered graph `H` (a simple graph on the linear order `V`, which is
  the arrival order) is a `j`-level tower over `K_m` in the sense of Definition 4.7.  There is a
  set `U` of vertices such that
  1. every vertex outside `U` comes after every vertex of `U` and is isolated in `H`, and
  2. `H[U]` with its arrival order is isomorphic, as an ordered graph (a graph isomorphism that is
     strictly monotone, hence an order isomorphism), to an initial segment `G.G.induce S` (`S` a
     down-set) of a finite full `j`-fold blow-up `G` of `K_m`.
  "Presented subtree by subtree" needs no extra condition: every blow-up satisfies
  `BlowUp.lt_of_π_lt` (Definition 4.6 (i)), so the descendants of every node form an interval
  and the intervals come in the order of the nodes (for the top vertices:
  `IsFullTowerAnc.lt_of_lt`, `Paper.ordConnected_subtree`); an initial segment of the
  presentation is exactly a down-set `S`.
* `firstFit_iso`: First-Fit commutes with ordered-graph isomorphisms.
* `range_firstFit_eq_of_isolated`: trailing isolated vertices do not change the set of First-Fit
  colours, provided the part before them is nonempty (its first vertex already has colour `0`).
* `IsPaddedTower.ceiling` (**Theorem 1.5, first sentence**): `c ≤ |P_j(k)|` and
  `|V(H)| ≥ choose(c-1, i+1)` for every `i ≤ j`, where `c` is the number of First-Fit colours.
  `IsPaddedTower.ceiling_of_two_le` states it with the paper's hypothesis `c ≥ 2`, which is not
  needed.
* `IsPaddedTower.firstFit_pow_le`: the asymptotic bound `c ^ (lg* n - lg* k - 3) ≤ n` for
  `|V(H)| ≤ n` and `lg* n ≥ 8`; `exists_threshold_firstFit_pow_le` is the sentence "there is
  `n_k` such that for every `n ≥ n_k` ..." (with `n_k = tow 7 + 1` for every `k`), and
  `exists_threshold_le_rpow` (**Theorem 1.5, second sentence**) is the same in the paper's real
  form `c ≤ n^{1/(lg* n - lg* k - 3)}`.
* Towers in this sense: `IsFullTower.isPaddedTower`, `IsFullTower.isPaddedTower_induce` (initial
  segments) and `IsPaddedTower.of_orderEmbedding`, `IsPaddedTower.padGraph` (appending isolated
  vertices, e.g. `padGraph` of `PadGraph.lean`).

First-Fit is the colouring `firstFit H` of the ordered graph (`FirstFit.lean`), and
`c = (Set.range (firstFit H)).ncard` is its number of colours; `Paper.ceiling_online` and
`Paper.exists_threshold_online` (`PaperFirstFit.lean`) state the theorem for the cost of the
online algorithm First-Fit.  The hypothesis `k ≥ 3` of the theorem is not needed.
-/

@[expose] public section

namespace OnlineColouring

/-! ### First-Fit and isomorphisms of ordered graphs -/

section Iso

variable {V W : Type*} [LinearOrder V] [WellFoundedLT V] [LinearOrder W] [WellFoundedLT W]
  {G₁ : SimpleGraph V} {G₂ : SimpleGraph W}

/-- First-Fit commutes with isomorphisms of ordered graphs: if `e` is a graph isomorphism that
preserves the arrival order, then `e x` gets the colour of `x`. -/
theorem firstFit_iso (e : G₁ ≃g G₂) (he : StrictMono e) (x : V) :
    firstFit G₂ (e x) = firstFit G₁ x := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
  rw [firstFit_eq, firstFit_eq]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h u hu hadj hn
    exact h (e u) (he hu) (e.map_adj_iff.2 hadj) (by rw [ih u hu]; exact hn)
  · intro h w hw hadj hn
    obtain ⟨u, rfl⟩ := e.surjective w
    have hu : u < x := he.lt_iff_lt.1 hw
    exact h u hu (e.map_adj_iff.1 hadj) (by rw [← ih u hu]; exact hn)

/-- Isomorphic ordered graphs get the same set of First-Fit colours. -/
theorem range_firstFit_iso (e : G₁ ≃g G₂) (he : StrictMono e) :
    Set.range (firstFit G₂) = Set.range (firstFit G₁) := by
  ext n
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective w
    exact ⟨x, (firstFit_iso e he x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e x, firstFit_iso e he x⟩

end Iso

/-- The inverse of a strictly monotone isomorphism of graphs on linear orders is strictly
monotone. -/
theorem strictMono_iso_symm {V W : Type*} [LinearOrder V] [LinearOrder W] {G₁ : SimpleGraph V}
    {G₂ : SimpleGraph W} (e : G₁ ≃g G₂) (he : StrictMono e) : StrictMono e.symm := by
  intro x y h
  rw [← he.lt_iff_lt, RelIso.apply_symm_apply, RelIso.apply_symm_apply]
  exact h

/-! ### Trailing isolated vertices -/

section Padded

variable {V : Type*} [LinearOrder V]

/-- If every vertex outside `U` comes after every vertex of `U`, then `U` is a down-set. -/
theorem isLowerSet_of_forall_lt {U : Set V} (h : ∀ u ∈ U, ∀ v ∉ U, u < v) : IsLowerSet U := by
  intro a b hba ha
  by_contra hb
  exact absurd (h a ha b hb) (not_lt.2 hba)

/-- **Trailing isolated vertices.** If `U` is a nonempty initial segment and every vertex outside
`U` is isolated, then First-Fit uses the same colours on `H` as on `H[U]`: the vertices outside
`U` get colour `0`, which the first vertex of `U` already has. -/
theorem range_firstFit_eq_of_isolated [WellFoundedLT V] {H : SimpleGraph V} {U : Set V}
    (hU : IsLowerSet U) (hiso : ∀ v ∉ U, ∀ u, ¬ H.Adj u v) (hne : U.Nonempty) :
    Set.range (firstFit H) = Set.range (firstFit (H.induce U)) := by
  obtain ⟨a, haU, hmin⟩ := (wellFounded_lt (α := V)).has_min U hne
  have ha0 : firstFit H a = 0 := firstFit_eq_zero H fun u hu _ => hmin u (hU hu.le haU) hu
  ext n
  simp only [Set.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    by_cases hv : v ∈ U
    · exact ⟨⟨v, hv⟩, firstFit_induce_of_isLowerSet H hU ⟨v, hv⟩⟩
    · refine ⟨⟨a, haU⟩, ?_⟩
      rw [firstFit_induce_of_isLowerSet H hU, ha0, firstFit_eq_zero H fun u _ => hiso v hv u]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (firstFit_induce_of_isLowerSet H hU x).symm⟩

/-- **Towers in the sense of Definition 4.7**: `IsPaddedTower m j H` says that
the ordered graph `H` (arrival order = the order of `V`) is an initial segment of a full `j`-level
tower over `K_m`, presented subtree by subtree, possibly followed by isolated vertices.  That is,
there is a set `U` of vertices such that
1. every vertex outside `U` comes after every vertex of `U` and is isolated in `H`, and
2. `H[U]` is isomorphic, as an ordered graph (by a graph isomorphism `e` that is strictly
   monotone, i.e. also an order isomorphism), to `G.G.induce S` for a finite full `j`-fold
   blow-up `G` of `K_m` and a down-set `S` of its arrival order.
(The presentation of `G` is subtree by subtree because of `BlowUp.lt_of_π_lt`.) -/
def IsPaddedTower (m j : ℕ) (H : SimpleGraph V) : Prop :=
  ∃ U : Set V, (∀ u ∈ U, ∀ v ∉ U, u < v) ∧ (∀ v ∉ U, ∀ u, ¬ H.Adj u v) ∧
    ∃ (G : OrdGraph) (S : Set G.V) (e : H.induce U ≃g G.G.induce S),
      Finite G.V ∧ IsFullTower m j G ∧ IsLowerSet S ∧ StrictMono e

/-- `k ≤ |P_j(k)|`. -/
theorem le_card_labelPoset (k : ℕ) : ∀ j, k ≤ Fintype.card (LabelPoset k j)
  | 0 => (card_labelPoset_zero k).ge
  | j + 1 => (le_card_labelPoset k j).trans (card_labelPoset_le_succ k j)

/-- On a finite ordered graph First-Fit uses at most `|V|` colours. -/
theorem ncard_range_firstFit_le [Finite V] (H : SimpleGraph V) :
    (Set.range (firstFit H)).ncard ≤ Nat.card V := by
  rw [← Set.image_univ, ← Set.ncard_univ V]
  exact Set.ncard_image_le Set.finite_univ

namespace IsPaddedTower

variable {m j k : ℕ} {H : SimpleGraph V}

/-- **Theorem 1.5 (a ceiling for towers), towers followed by isolated vertices.** If First-Fit
uses `c` colours on a `k`-colourable `j`-level tower `H` (an initial segment of a full tower,
possibly followed by isolated vertices), then `c ≤ |P_j(k)|` and `|V(H)| ≥ choose(c-1, i+1)` for
every `i ≤ j`.  The paper's hypotheses `c ≥ 2` and `k ≥ 3` are not needed. -/
theorem ceiling [Finite V] (hH : IsPaddedTower m j H) (hc : H.Colorable k) :
    (Set.range (firstFit H)).ncard ≤ Fintype.card (LabelPoset k j) ∧
      ∀ i ≤ j, ((Set.range (firstFit H)).ncard - 1).choose (i + 1) ≤ Nat.card V := by
  obtain ⟨U, hlt, hiso, G, S, e, hfin, hT, hS, he⟩ := hH
  have hU : IsLowerSet U := isLowerSet_of_forall_lt hlt
  rcases U.eq_empty_or_nonempty with rfl | hne
  · -- only isolated vertices: First-Fit uses at most one colour
    have hsub : Set.range (firstFit H) ⊆ {0} := by
      rintro _ ⟨v, rfl⟩
      exact firstFit_eq_zero H fun u _ => hiso v (Set.notMem_empty v) u
    have hc1 : (Set.range (firstFit H)).ncard ≤ 1 :=
      (Set.ncard_le_ncard hsub (Set.finite_singleton 0)).trans (Set.ncard_singleton 0).le
    refine ⟨?_, fun i _ => ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- a `0`-colourable graph is empty
        have := hc.isEmpty
        rw [Set.range_eq_empty, Set.ncard_empty]
        exact Nat.zero_le _
      · exact hc1.trans (hk.trans_le (le_card_labelPoset k j))
    · rw [show (Set.range (firstFit H)).ncard - 1 = 0 by omega, Nat.choose_zero_succ]
      exact Nat.zero_le _
  · have := hfin
    obtain ⟨τ, hτ⟩ := hT.exists_anc
    have hrange : Set.range (firstFit H) = Set.range (firstFit (G.G.induce S)) := by
      rw [range_firstFit_eq_of_isolated hU hiso hne, range_firstFit_iso e he]
    have hcS : (G.G.induce S).Colorable k :=
      (hc.of_hom (SimpleGraph.Embedding.induce U).toHom).of_hom e.symm.toHom
    have hcard : S.ncard ≤ Nat.card V := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_congr e.toEquiv]
      exact Finite.card_subtype_le _
    obtain ⟨h1, h2⟩ := hτ.ceiling hS hcS
    rw [hrange]
    exact ⟨h1, fun i hi => (h2 i hi).trans hcard⟩

/-- **Theorem 1.5, first sentence, as stated in the paper** (with its hypothesis `c ≥ 2`): if
First-Fit uses `c ≥ 2` colours on a `k`-colourable `j`-level tower `H`, then `c ≤ |P_j(k)|` and
`|V(H)| ≥ choose(c-1, i+1)` for every `0 ≤ i ≤ j`. -/
theorem ceiling_of_two_le [Finite V] (hH : IsPaddedTower m j H) (hc : H.Colorable k)
    (_h2 : 2 ≤ (Set.range (firstFit H)).ncard) :
    (Set.range (firstFit H)).ncard ≤ Fintype.card (LabelPoset k j) ∧
      ∀ i ≤ j, ((Set.range (firstFit H)).ncard - 1).choose (i + 1) ≤ Nat.card V :=
  hH.ceiling hc

/-- **Theorem 1.5 (a ceiling for towers), asymptotic form, towers followed by isolated
vertices.** If First-Fit uses `c` colours on a `k`-colourable tower `H` with at most `n`
vertices, where `lg* n ≥ 8`, then `c ^ (lg* n - lg* k - 3) ≤ n` (natural subtraction; for a
positive exponent this is `c ≤ n^{1/(lg* n - lg* k - 3)}`). -/
theorem firstFit_pow_le [Finite V] (hH : IsPaddedTower m j H) (hc : H.Colorable k) {n : ℕ}
    (hVn : Nat.card V ≤ n) (hn : 8 ≤ logStar n) :
    (Set.range (firstFit H)).ncard ^ (logStar n - logStar k - 3) ≤ n := by
  obtain ⟨hP, hsize⟩ := hH.ceiling hc
  exact pow_logStar_le hn ((ncard_range_firstFit_le H).trans hVn) (logStar_sub_logStar_le hP)
    fun i hi => (hsize i hi).trans hVn

/-- **Theorem 1.5, asymptotic form, in real numbers**: if moreover `lg* n ≥ lg* k + 4` (so that the
exponent is positive), then `c ≤ n^{1/(lg* n - lg* k - 3)}`. -/
theorem le_rpow [Finite V] (hH : IsPaddedTower m j H) (hc : H.Colorable k) {n : ℕ}
    (hVn : Nat.card V ≤ n) (hn : 8 ≤ logStar n) (hk : logStar k + 4 ≤ logStar n) :
    ((Set.range (firstFit H)).ncard : ℝ) ≤
      (n : ℝ) ^ (1 / ((logStar n : ℝ) - logStar k - 3)) := by
  have hpow := hH.firstFit_pow_le hc hVn hn
  set e := logStar n - logStar k - 3 with he
  have hecast : ((logStar n : ℝ) - logStar k - 3) = (e : ℝ) := by
    rw [he, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  have hepos : (0 : ℝ) < e := by
    rw [← hecast]
    have : ((logStar k + 4 : ℕ) : ℝ) ≤ (logStar n : ℝ) := by exact_mod_cast hk
    push_cast at this
    linarith
  rw [hecast, one_div, Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _) hepos,
    Real.rpow_natCast]
  exact_mod_cast hpow

end IsPaddedTower

/-! ### Towers in this sense -/

/-- A finite full `j`-fold blow-up of `K_m` is a tower in this sense (`U = V`, `S = V(G)`, no
isolated vertices). -/
theorem IsFullTower.isPaddedTower {m j : ℕ} {G : OrdGraph} [Finite G.V] (hT : IsFullTower m j G) :
    IsPaddedTower m j G.G :=
  ⟨Set.univ, fun _ _ v hv => absurd (Set.mem_univ v) hv, fun v hv => absurd (Set.mem_univ v) hv,
    G, Set.univ, RelIso.refl _, inferInstance, hT, isLowerSet_univ, strictMono_id⟩

/-- An initial segment `S` (a down-set) of a finite full `j`-fold blow-up of `K_m` is a tower in
this sense (`U = S`, no isolated vertices). -/
theorem IsFullTower.isPaddedTower_induce {m j : ℕ} {G : OrdGraph} [Finite G.V]
    (hT : IsFullTower m j G) {S : Set G.V} (hS : IsLowerSet S) :
    IsPaddedTower m j (G.G.induce S) :=
  ⟨Set.univ, fun _ _ v hv => absurd (Set.mem_univ v) hv, fun v hv => absurd (Set.mem_univ v) hv,
    G, S, SimpleGraph.induceUnivIso _, inferInstance, hT, hS, fun _ _ h => h⟩

/-- **Appending isolated vertices.** Let `f : V ↪o V'` embed `H` as an initial segment of `H'`
(the image of `f` is a down-set, `H'.Adj (f a) (f b) ↔ H.Adj a b`), and let every vertex of `H'`
outside the image of `f` be isolated.  If `H` is a tower, so is `H'`. -/
theorem IsPaddedTower.of_orderEmbedding {V V' : Type*} [LinearOrder V] [LinearOrder V'] {m j : ℕ}
    {H : SimpleGraph V} {H' : SimpleGraph V'} (hH : IsPaddedTower m j H) (f : V ↪o V')
    (hf : IsLowerSet (Set.range f)) (hadj : ∀ a b, H'.Adj (f a) (f b) ↔ H.Adj a b)
    (hiso : ∀ v ∉ Set.range f, ∀ u, ¬ H'.Adj u v) : IsPaddedTower m j H' := by
  obtain ⟨U, hlt, hisoU, G, S, e, hfin, hT, hS, he⟩ := hH
  -- the isomorphism `H[U] ≃ H'[f(U)]`, which preserves the order
  let g : H.induce U ≃g H'.induce (f '' U) :=
    ⟨Equiv.Set.image f U f.injective, fun {a b} => hadj a b⟩
  have hg : StrictMono g := fun a b h => f.strictMono h
  refine ⟨f '' U, ?_, ?_, G, S, e.comp g.symm, hfin, hT, hS,
    he.comp (strictMono_iso_symm g hg)⟩
  · rintro _ ⟨u, hu, rfl⟩ v' hv'
    by_cases hr : v' ∈ Set.range f
    · obtain ⟨v, rfl⟩ := hr
      have hv : v ∉ U := fun hv => hv' ⟨v, hv, rfl⟩
      exact f.strictMono (hlt u hu v hv)
    · by_contra hle
      exact hr (hf (not_lt.1 hle) ⟨u, rfl⟩)
  · intro v' hv' u' h
    by_cases hr : v' ∈ Set.range f
    · obtain ⟨v, rfl⟩ := hr
      have hv : v ∉ U := fun hv => hv' ⟨v, hv, rfl⟩
      by_cases hu : u' ∈ Set.range f
      · obtain ⟨u, rfl⟩ := hu
        exact hisoU v hv u ((hadj u v).1 h)
      · exact hiso u' hu (f v) h.symm
    · exact hiso v' hr u' h

/-- **Appending isolated vertices**, for `padGraph` (`PadGraph.lean`): if the ordered graph `G` on
`Fin N` is a tower, so is `G` followed by isolated vertices up to `N' ≥ N`. -/
theorem IsPaddedTower.padGraph {m j N N' : ℕ} {G : SimpleGraph (Fin N)}
    (hG : IsPaddedTower m j G) (hN : N ≤ N') :
    IsPaddedTower m j (OnlineColouring.padGraph G N') := by
  refine hG.of_orderEmbedding (Fin.castLEOrderEmb hN) ?_ ?_ ?_
  · intro a b hba ⟨x, hx⟩
    refine ⟨⟨b, lt_of_le_of_lt hba (hx ▸ x.2)⟩, rfl⟩
  · intro a b
    rw [padGraph_adj]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨a.2, b.2, h⟩⟩
  · rintro v hv u ⟨_, hvN, _⟩
    exact hv ⟨⟨v, hvN⟩, rfl⟩

end Padded

/-! ### The threshold `n_k` -/

universe u

/-- **Theorem 1.5, second sentence.** There is `n_k` (here `n_k = tow 7 + 1` for every `k`) such
that for every `n ≥ n_k`, First-Fit uses `c` colours with `c ^ (lg* n - lg* k - 3) ≤ n` on every
`k`-colourable tower (followed by isolated vertices or not) with at most `n` vertices. -/
theorem exists_threshold_firstFit_pow_le (k : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ (m j : ℕ) (V : Type u) [LinearOrder V] [Finite V] (H : SimpleGraph V),
      IsPaddedTower m j H → H.Colorable k → Nat.card V ≤ n →
        (Set.range (firstFit H)).ncard ^ (logStar n - logStar k - 3) ≤ n :=
  ⟨tow 7 + 1, fun _ hn _ _ _ _ _ _ hH hc hVn =>
    hH.firstFit_pow_le hc hVn (eight_le_logStar (Nat.lt_iff_add_one_le.2 hn))⟩

/-- **Theorem 1.5, second sentence, in the paper's real form.** There is `n_k` such that for every
`n ≥ n_k`, First-Fit uses at most `n^{1/(lg* n - lg* k - 3)}` colours on every `k`-colourable
tower (followed by isolated vertices or not) with at most `n` vertices. -/
theorem exists_threshold_le_rpow (k : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ (m j : ℕ) (V : Type u) [LinearOrder V] [Finite V] (H : SimpleGraph V),
      IsPaddedTower m j H → H.Colorable k → Nat.card V ≤ n →
        ((Set.range (firstFit H)).ncard : ℝ) ≤
          (n : ℝ) ^ (1 / ((logStar n : ℝ) - logStar k - 3)) := by
  refine ⟨tow (max 7 (logStar k + 3)) + 1, fun n hn m j V _ _ H hH hc hVn => ?_⟩
  have hlt : tow (max 7 (logStar k + 3)) < n := Nat.lt_iff_add_one_le.2 hn
  have hL : max 7 (logStar k + 3) < logStar n := by
    by_contra h
    push Not at h
    have := logStar_le_iff.1 h
    omega
  exact hH.le_rpow hc hVn (by omega) (by omega)

end OnlineColouring
