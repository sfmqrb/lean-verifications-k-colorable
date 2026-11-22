module

public import OnlineColouring.Towers
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Set.Card

/-!
# First-Fit, and Lemma 9.5 (First-Fit commutes with blow-ups)

The paragraph on First-Fit of Section 4 and Lemma 9.5.

* `firstFit G : V → ℕ` is First-Fit on the ordered graph `G` (the order of `V` is the arrival
  order): each vertex gets the least colour not used by its earlier neighbours.  It is defined
  by well-founded recursion, so `V` only needs `[WellFoundedLT V]` (every finite linear order
  qualifies).  Colours are the natural numbers `0, 1, 2, …`.  This is the colouring that the
  online algorithm `OnlineAlg.firstFit` of `Online.lean` produces (`Paper.run_firstFit_eq`,
  `PaperFirstFit.lean`).
* `firstFit_ne_of_adj`, `firstFitColoring`: on a finite ordered graph First-Fit is a proper
  colouring; `firstFit_le_ncard`: a vertex with `d` earlier neighbours gets a colour `≤ d`, so
  First-Fit uses at most one more colour than the largest number of earlier neighbours.
* `firstFit_induce_of_isLowerSet`: First-Fit on an initial segment (a down-set of the arrival
  order) agrees with First-Fit on the whole graph.
* `firstFit_top_fin`: on the arrival-ordered clique `K_m` (on `Fin m`), vertex `t` gets colour `t`.
* `BlowUp.firstFit_eq` (**Lemma 9.5**, first sentence): on a full blow-up `G` of `H`, every
  vertex `x` gets the First-Fit colour of its block node `π x` on `H`;
  `BlowUp.firstFit_induce_eq`: the same on an initial segment of a full blow-up.
* `firstFit_eq_zero`: a vertex without earlier neighbours (e.g. an appended isolated vertex) gets
  the smallest colour `0`.
* `IsFullTowerAnc m j G τ`: a full `j`-fold blow-up of `K_m` together with its *ancestor map*
  `τ : V(G) → Fin m` (the composite of the block maps; `τ x = t` means that `x` is a descendant of
  the top vertex `t`).  `IsFullTower m j G ↔ ∃ τ, IsFullTowerAnc m j G τ`.
* `IsFullTowerAnc.firstFit_eq` (**Lemma 9.5**, second sentence, for a full tower): on a full
  tower First-Fit gives every descendant of the top vertex `t` the colour `t`, the `t`-th smallest
  colour when top vertices and colours are both counted from `0`;
  `IsFullTower.ncard_range_firstFit`: it uses exactly `m` colours.
* `IsFullTowerAnc.firstFit_induce_eq`, `IsFullTowerAnc.ncard_range_firstFit_induce` (**Lemma 9.5**,
  second sentence, as stated): the same on an initial segment `S` of a full tower: the colours
  used are the top vertices with a descendant in `S`.
-/

@[expose] public section

namespace OnlineColouring

section FirstFit

variable {V : Type*} [LinearOrder V] [WellFoundedLT V]

/-- **First-Fit** on the ordered graph `G`: every vertex gets the least colour (a natural number)
that is not used on its earlier neighbours.  Colours start at `0`. -/
noncomputable def firstFit (G : SimpleGraph V) : V → ℕ :=
  (wellFounded_lt (α := V)).fix fun v rec => sInf {n | ∀ u (h : u < v), G.Adj u v → rec u h ≠ n}

/-- The defining equation of First-Fit. -/
theorem firstFit_eq (G : SimpleGraph V) (v : V) :
    firstFit G v = sInf {n | ∀ u, u < v → G.Adj u v → firstFit G u ≠ n} :=
  (wellFounded_lt (α := V)).fix_eq _ v

/-- The earlier neighbours of `v`. -/
def earlierNbrs (G : SimpleGraph V) (v : V) : Set V := {u | u < v ∧ G.Adj u v}

/-- If `v` has finitely many earlier neighbours, its First-Fit colour is not used on any of
them. -/
theorem firstFit_mem_of_finite (G : SimpleGraph V) (v : V) (hfin : (earlierNbrs G v).Finite) :
    firstFit G v ∈ {n | ∀ u, u < v → G.Adj u v → firstFit G u ≠ n} := by
  have hne : {n | ∀ u, u < v → G.Adj u v → firstFit G u ≠ n}.Nonempty := by
    obtain ⟨n, hn⟩ := (hfin.image (firstFit G)).exists_notMem
    exact ⟨n, fun u hu hadj h => hn ⟨u, ⟨hu, hadj⟩, h⟩⟩
  rw [firstFit_eq]
  exact Nat.sInf_mem hne

/-- First-Fit is proper on edges `uv` (`u` earlier) when `v` has finitely many earlier
neighbours. -/
theorem firstFit_ne_of_lt (G : SimpleGraph V) {u v : V} (huv : u < v) (hadj : G.Adj u v)
    (hfin : (earlierNbrs G v).Finite) : firstFit G u ≠ firstFit G v :=
  firstFit_mem_of_finite G v hfin u huv hadj

/-- On a finite ordered graph First-Fit is a proper colouring. -/
theorem firstFit_ne_of_adj [Finite V] (G : SimpleGraph V) {u v : V} (hadj : G.Adj u v) :
    firstFit G u ≠ firstFit G v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact firstFit_ne_of_lt G huv hadj (Set.toFinite _)
  · exact absurd hadj (G.loopless.irrefl _)
  · exact (firstFit_ne_of_lt G hvu hadj.symm (Set.toFinite _)).symm

/-- First-Fit as a proper colouring of a finite ordered graph with colours in `ℕ`. -/
noncomputable def firstFitColoring [Finite V] (G : SimpleGraph V) : G.Coloring ℕ :=
  SimpleGraph.Coloring.mk (firstFit G) fun hadj => firstFit_ne_of_adj G hadj

/-- First-Fit gives a vertex with `d` earlier neighbours a colour at most `d`; so it uses at most
`D + 1` colours if no vertex has more than `D` earlier neighbours. -/
theorem firstFit_le_ncard (G : SimpleGraph V) (v : V) (hfin : (earlierNbrs G v).Finite) :
    firstFit G v ≤ (earlierNbrs G v).ncard := by
  classical
  set F := firstFit G '' earlierNbrs G v with hF
  have hFfin : F.Finite := hfin.image _
  -- some colour `n ≤ |F|` is not used on an earlier neighbour
  obtain ⟨n, hn, hnF⟩ : ∃ n, n ≤ F.ncard ∧ n ∉ F := by
    by_contra h
    push Not at h
    have hsub : ((Finset.range (F.ncard + 1) : Finset ℕ) : Set ℕ) ⊆ F := fun n hn =>
      h n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
    have := Set.ncard_le_ncard hsub hFfin
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    omega
  have hmem : n ∈ {n | ∀ u, u < v → G.Adj u v → firstFit G u ≠ n} :=
    fun u hu hadj h => hnF ⟨u, ⟨hu, hadj⟩, h⟩
  rw [firstFit_eq]
  exact (Nat.sInf_le hmem).trans (hn.trans (Set.ncard_image_le hfin))

/-- A vertex without earlier neighbours (for instance an appended isolated vertex) gets colour
`0`. -/
theorem firstFit_eq_zero (G : SimpleGraph V) {v : V} (h : ∀ u, u < v → ¬ G.Adj u v) :
    firstFit G v = 0 := by
  rw [firstFit_eq]
  refine Nat.eq_zero_of_le_zero (Nat.sInf_le ?_)
  intro u hu hadj
  exact absurd hadj (h u hu)

/-- First-Fit on an initial segment (a down-set of the arrival order) agrees with First-Fit on
the whole ordered graph. -/
theorem firstFit_induce_of_isLowerSet (G : SimpleGraph V) {S : Set V} (hS : IsLowerSet S)
    (x : S) : firstFit (G.induce S) x = firstFit G x := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
  rw [firstFit_eq, firstFit_eq]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h u hu hadj hn
    have huS : u ∈ S := hS hu.le x.2
    exact h ⟨u, huS⟩ hu hadj (by rw [ih ⟨u, huS⟩ hu]; exact hn)
  · intro h u hu hadj hn
    exact h u hu hadj (by rw [← ih u hu]; exact hn)

end FirstFit

/-- **First-Fit on the clique.** On the arrival-ordered clique `K_m = (0, 1, …, m-1)`,
First-Fit gives vertex `t` colour `t`. -/
theorem firstFit_top_fin {m : ℕ} (t : Fin m) : firstFit (⊤ : SimpleGraph (Fin m)) t = t := by
  induction t using WellFoundedLT.induction with
  | ind t ih =>
  rw [firstFit_eq]
  set S := {n | ∀ u, u < t → (⊤ : SimpleGraph (Fin m)).Adj u t → firstFit ⊤ u ≠ n} with hS
  have ht : (t : ℕ) ∈ S := by
    intro u hu _ h
    rw [ih u hu] at h
    exact hu.ne (Fin.ext h)
  refine le_antisymm (Nat.sInf_le ht) ?_
  by_contra hlt
  push Not at hlt
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨_, ht⟩
  have hs : sInf S < m := hlt.trans t.isLt
  have hlt' : (⟨sInf S, hs⟩ : Fin m) < t := hlt
  exact hmem ⟨sInf S, hs⟩ hlt' ((SimpleGraph.top_adj _ _).2 hlt'.ne) (by rw [ih _ hlt'])

namespace BlowUp

variable {V W : Type*} [LinearOrder V] [LinearOrder W] {H : SimpleGraph V} {G : SimpleGraph W}

/-- The arrival order of a blow-up is well-founded only if that of `H` is: a section of the
block map is strictly monotone. -/
theorem wellFoundedLT (B : BlowUp H G) [WellFoundedLT W] : WellFoundedLT V := by
  choose s hs using B.π_surjective
  refine StrictMono.wellFoundedLT (f := s) fun v v' h => B.lt_of_π_lt ?_
  rw [hs, hs]
  exact h

/-- If the blow-up `G` is finite, so is `H` (the block map is onto). -/
theorem finite (B : BlowUp H G) [Finite W] : Finite V :=
  Finite.of_surjective B.π B.π_surjective

/-- **Lemma 9.5 (First-Fit commutes with blow-ups).** On a full blow-up `G` of `H`, First-Fit
colours every vertex of the block `σ(v)` with the colour that First-Fit gives to `v` on `H`. -/
theorem firstFit_eq [WellFoundedLT V] [WellFoundedLT W] (B : BlowUp H G) (hB : B.IsFull)
    (x : W) : firstFit G x = firstFit H (B.π x) := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
  rw [OnlineColouring.firstFit_eq, OnlineColouring.firstFit_eq]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · -- an earlier neighbour `w` of `π x` has a server `y` in its block (fullness)
    intro h w hw hadj hn
    obtain ⟨y, hy, hys⟩ := hB hw hadj
    have hyx : y < x := B.lt_of_π_lt (by rw [hy]; exact hw)
    have hyadj : G.Adj y x := B.adj_of_serve hys
    exact h y hyx hyadj (by rw [ih y hyx, hy]; exact hn)
  · -- an earlier neighbour `y` of `x` serves the arc `π y → π x`
    intro h y hyx hadj hn
    obtain ⟨hlt, hHadj⟩ := B.serve_spec (B.serve_eq_of_adj hyx hadj)
    exact h (B.π y) hlt hHadj (by rw [← ih y hyx]; exact hn)

/-- **Lemma 9.5 (First-Fit commutes with blow-ups), initial segments.** On an initial segment `S` of
a full blow-up `G` of `H`, First-Fit colours every vertex of the block `σ(v)` with the colour that
First-Fit gives to `v` on `H`. -/
theorem firstFit_induce_eq [WellFoundedLT V] [WellFoundedLT W] (B : BlowUp H G) (hB : B.IsFull)
    {S : Set W} (hS : IsLowerSet S) (x : S) : firstFit (G.induce S) x = firstFit H (B.π x) := by
  rw [firstFit_induce_of_isLowerSet G hS x, B.firstFit_eq hB]

end BlowUp

/-! ### Full towers with their ancestor maps -/

/-- `IsFullTowerAnc m j G τ`: `G` is a full `j`-fold blow-up of the arrival-ordered clique `K_m`
(on `Fin m`), and `τ : V(G) → Fin m` is the composite of the `j` block maps, so that `τ x = t`
says that `x` is a descendant of the top vertex `t`. -/
inductive IsFullTowerAnc (m : ℕ) : ℕ → (G : OrdGraph) → (G.V → Fin m) → Prop
  | clique : IsFullTowerAnc m 0 (OrdGraph.clique m) (id : Fin m → Fin m)
  | blowUp {j : ℕ} {H G : OrdGraph} {τ : H.V → Fin m} (B : BlowUp H.G G.G) (hB : B.IsFull) :
      IsFullTowerAnc m j H τ → IsFullTowerAnc m (j + 1) G (τ ∘ B.π)

namespace IsFullTowerAnc

variable {m j : ℕ} {G : OrdGraph} {τ : G.V → Fin m}

theorem isFullTower (hT : IsFullTowerAnc m j G τ) : IsFullTower m j G := by
  induction hT with
  | clique => exact .clique
  | blowUp B hB _ ih => exact .blowUp ih ⟨B, hB⟩

/-- Every vertex has an ancestor at the top, and every top vertex has a descendant. -/
theorem surjective (hT : IsFullTowerAnc m j G τ) : Function.Surjective τ := by
  induction hT with
  | clique => exact Function.surjective_id
  | blowUp B _ _ ih => exact ih.comp B.π_surjective

/-- The descendants of the top vertices arrive one subtree after the other: if the ancestor of
`x` comes before the ancestor of `y`, then `x` comes before `y`. -/
theorem lt_of_lt (hT : IsFullTowerAnc m j G τ) {x y : G.V} (h : τ x < τ y) : x < y := by
  induction hT with
  | clique => exact h
  | blowUp B _ _ ih => exact B.lt_of_π_lt (ih h)

theorem firstFit_eq_aux (hT : IsFullTowerAnc m j G τ) :
    ∀ [WellFoundedLT G.V] (x : G.V), firstFit G.G x = τ x := by
  induction hT with
  | clique => exact fun x => firstFit_top_fin x
  | @blowUp j H G τ B hB _ ih =>
    intro _ x
    have hwf : WellFoundedLT H.V := B.wellFoundedLT
    rw [B.firstFit_eq hB]
    exact ih (B.π x)

/-- **Lemma 9.5 (First-Fit commutes with blow-ups), full towers.** On a full tower over `K_m`,
First-Fit gives every descendant of the top vertex `t` colour `t`. -/
theorem firstFit_eq (hT : IsFullTowerAnc m j G τ) [WellFoundedLT G.V] (x : G.V) :
    firstFit G.G x = τ x :=
  hT.firstFit_eq_aux x

/-- On a full tower over `K_m`, the First-Fit colours are exactly `0, 1, …, m-1`. -/
theorem range_firstFit (hT : IsFullTowerAnc m j G τ) [WellFoundedLT G.V] :
    Set.range (firstFit G.G) = Set.Iio m := by
  ext n
  simp only [Set.mem_range, Set.mem_Iio]
  constructor
  · rintro ⟨x, rfl⟩
    rw [hT.firstFit_eq]
    exact (τ x).isLt
  · intro hn
    obtain ⟨x, hx⟩ := hT.surjective ⟨n, hn⟩
    exact ⟨x, by rw [hT.firstFit_eq, hx]⟩

/-- **Lemma 9.5 (First-Fit commutes with blow-ups), initial segments.** On an initial segment `S` of
a full tower, First-Fit gives every descendant of the top vertex `t` colour `t`. -/
theorem firstFit_induce_eq (hT : IsFullTowerAnc m j G τ) [WellFoundedLT G.V] {S : Set G.V}
    (hS : IsLowerSet S) (x : S) : firstFit (G.G.induce S) x = τ x := by
  rw [firstFit_induce_of_isLowerSet G.G hS x, hT.firstFit_eq]

/-- On an initial segment `S` of a full tower, the First-Fit colours are the (indices of the)
top vertices with a descendant in `S`. -/
theorem range_firstFit_induce (hT : IsFullTowerAnc m j G τ) [WellFoundedLT G.V] {S : Set G.V}
    (hS : IsLowerSet S) :
    Set.range (firstFit (G.G.induce S)) = (fun t : Fin m => (t : ℕ)) '' (τ '' S) := by
  ext n
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨τ x, ⟨x, x.2, rfl⟩, (hT.firstFit_induce_eq hS x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, hT.firstFit_induce_eq hS _⟩

/-- **Lemma 9.5 (First-Fit commutes with blow-ups), counting.** On an initial segment `S` of a full
tower, First-Fit uses exactly as many colours as there are top vertices with a descendant
in `S`. -/
theorem ncard_range_firstFit_induce (hT : IsFullTowerAnc m j G τ) [WellFoundedLT G.V]
    {S : Set G.V} (hS : IsLowerSet S) :
    (Set.range (firstFit (G.G.induce S))).ncard = (τ '' S).ncard := by
  rw [hT.range_firstFit_induce hS, Set.ncard_image_of_injective _ Fin.val_injective]

end IsFullTowerAnc

/-- Every full tower carries an ancestor map. -/
theorem IsFullTower.exists_anc {m j : ℕ} {G : OrdGraph} (hT : IsFullTower m j G) :
    ∃ τ : G.V → Fin m, IsFullTowerAnc m j G τ := by
  induction hT with
  | clique => exact ⟨id, .clique⟩
  | blowUp _ hB ih =>
    obtain ⟨τ, hτ⟩ := ih
    obtain ⟨B, hBf⟩ := hB
    exact ⟨τ ∘ B.π, .blowUp B hBf hτ⟩

theorem isFullTower_iff_exists_anc {m j : ℕ} {G : OrdGraph} :
    IsFullTower m j G ↔ ∃ τ : G.V → Fin m, IsFullTowerAnc m j G τ :=
  ⟨IsFullTower.exists_anc, fun ⟨_, hτ⟩ => hτ.isFullTower⟩

/-- **Lemma 9.5 (First-Fit commutes with blow-ups), consequence.** On a full `j`-fold blow-up of the
arrival-ordered clique `K_m`, First-Fit uses exactly the colours `0, …, m-1`. -/
theorem IsFullTower.range_firstFit {m j : ℕ} {G : OrdGraph} (hT : IsFullTower m j G)
    [WellFoundedLT G.V] : Set.range (firstFit G.G) = Set.Iio m := by
  obtain ⟨τ, hτ⟩ := hT.exists_anc
  exact hτ.range_firstFit

/-- On a full `j`-fold blow-up of `K_m`, First-Fit uses exactly `m` colours. -/
theorem IsFullTower.ncard_range_firstFit {m j : ℕ} {G : OrdGraph} (hT : IsFullTower m j G)
    [WellFoundedLT G.V] : (Set.range (firstFit G.G)).ncard = m := by
  rw [hT.range_firstFit, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

end OnlineColouring
