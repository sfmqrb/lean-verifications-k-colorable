module

public import OnlineColouring.FirstFit
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset

/-!
# Theorem 1.5 (a ceiling for towers), first sentence, for initial segments of full towers

Theorem 1.5: let `k ≥ 3`; if First-Fit uses `c ≥ 2` colours on a `k`-colourable `j`-level tower
`G`, then `c ≤ |P_j(k)|` and `|V(G)| ≥ choose(c-1, i+1)` for every `0 ≤ i ≤ j`.

This file proves it, without the hypotheses on `k` and `c`, for full towers
(`IsFullTower.ceiling`, where `c = m` and even `|V(G)| ≥ choose(m, i+1)` holds) and for initial
segments of full towers (`IsFullTowerAnc.ceiling`).  An initial segment is a down-set `S` of the
arrival order; since a `BlowUp` requires the blocks to arrive one after the other, every full
tower is presented subtree by subtree (`IsFullTowerAnc.lt_of_lt`), so these are exactly the
initial segments of Definition 4.7.  Towers in the sense of Definition 4.7 (initial segments of
full towers, possibly followed by isolated vertices) are treated in `CeilingPadded.lean`, and the
asymptotic sentence of the theorem in `CeilingAsymptotic.lean`.

* **The size bound.**  `arcWalks G A i` is the set of walks `u 0 → ⋯ → u i` along arcs of `G`
  (each step goes to a later neighbour) inside `A`.  For a full blow-up `G` of `H`, the map
  `(u_0, …, u_{i+1}) ↦ (ρ(u_0,u_1), …, ρ(u_i,u_{i+1}))`, where `ρ(w,v) = B.server w v` is a chosen
  server of the arc `w → v`, is injective from walks with `i+1` arcs among the nodes whose block
  lies in `A` (`B.whole A`) into walks with `i` arcs in `A` (`BlowUp.ncard_arcWalks_succ_le`).
  Iterating it down the full tower (`IsFullTowerAnc.ncard_arcWalks_le`) and counting the walks of
  the transitive tournament `K_m` (`choose_le_ncard_arcWalks_top`) gives the bound.
* **The poset bound.**  The restriction of a full blow-up to an initial segment `S` is a full
  blow-up of the restriction of `H` to the nodes with a vertex in `S`
  (`BlowUp.exists_restrict`, the paper's "alive nodes"), so Lemma 5.3 applies level by level
  (`IsFullTowerAnc.ncard_image_le_of_colorable`).
-/

@[expose] public section

namespace OnlineColouring

/-! ### Walks along arcs -/

section ArcWalk

variable {V : Type*} [LinearOrder V]

/-- `arcWalks G A i`: the walks `u 0 → u 1 → ⋯ → u i` with `i` arcs in the ordered graph `G`
(every step goes from a vertex to a later neighbour) all of whose vertices lie in `A`. -/
def arcWalks (G : SimpleGraph V) (A : Set V) (i : ℕ) : Set (Fin (i + 1) → V) :=
  {u | (∀ a, u a ∈ A) ∧ ∀ a : Fin i, u a.castSucc < u a.succ ∧ G.Adj (u a.castSucc) (u a.succ)}

/-- Walks with no arc are vertices. -/
theorem ncard_arcWalks_zero (G : SimpleGraph V) (A : Set V) :
    (arcWalks G A 0).ncard = A.ncard := by
  refine Set.ncard_congr (fun u _ => u 0) (fun u hu => hu.1 0) ?_ ?_
  · intro u u' _ _ h
    funext a
    have ha : a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ha
    exact h
  · intro v hv
    exact ⟨fun _ => v, ⟨fun _ => hv, fun a => a.elim0⟩, rfl⟩

/-- **Walks in a transitive tournament.** The arrival-ordered clique has at least
`choose(|C|, i+1)` walks with `i` arcs inside `C` (one for each `(i+1)`-subset of `C`). -/
theorem choose_le_ncard_arcWalks_top {m : ℕ} (C : Set (Fin m)) (i : ℕ) :
    C.ncard.choose (i + 1) ≤ (arcWalks (⊤ : SimpleGraph (Fin m)) C i).ncard := by
  classical
  let P := C.toFinset.powersetCard (i + 1)
  have hP : P.card = C.ncard.choose (i + 1) := by
    rw [Finset.card_powersetCard, Set.ncard_eq_toFinset_card']
  let f : P → arcWalks (⊤ : SimpleGraph (Fin m)) C i := fun s =>
    ⟨fun a => s.1.orderEmbOfFin (Finset.mem_powersetCard.1 s.2).2 a, by
      refine ⟨fun a => ?_, fun a => ?_⟩
      · have := s.1.orderEmbOfFin_mem (Finset.mem_powersetCard.1 s.2).2 a
        exact Set.mem_toFinset.1 ((Finset.mem_powersetCard.1 s.2).1 this)
      · have hlt := (s.1.orderEmbOfFin (Finset.mem_powersetCard.1 s.2).2).strictMono
          (Fin.castSucc_lt_succ (i := a))
        exact ⟨hlt, (SimpleGraph.top_adj _ _).2 hlt.ne⟩⟩
  have hf : Function.Injective f := by
    intro s s' h
    have h' := congrArg (fun g => Set.range g) (congrArg Subtype.val h)
    simp only [f] at h'
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← Finset.range_orderEmbOfFin s.1 (Finset.mem_powersetCard.1 s.2).2,
      ← Finset.range_orderEmbOfFin s'.1 (Finset.mem_powersetCard.1 s'.2).2]
    exact h'
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe, hP] at this

end ArcWalk

/-! ### One level: servers, the walk map, and restriction to initial segments -/

namespace BlowUp

variable {V W : Type*} [LinearOrder V] [LinearOrder W] {H : SimpleGraph V} {G : SimpleGraph W}

/-- The nodes whose whole block lies in `A` (the *completely presented* nodes if `A` is the set
of presented vertices). -/
def whole (B : BlowUp H G) (A : Set W) : Set V := {v | ∀ x, B.π x = v → x ∈ A}

/-- Blocks are nonempty and disjoint, so there are at most `|A|` nodes whose block lies in `A`. -/
theorem ncard_whole_le [Finite W] (B : BlowUp H G) (A : Set W) :
    (B.whole A).ncard ≤ A.ncard := by
  choose s hs using B.π_surjective
  refine Set.ncard_le_ncard_of_injOn s (fun v hv => hv _ (hs v)) ?_
  intro v _ v' _ h
  rw [← hs v, ← hs v', h]

open scoped Classical in
/-- A chosen server `ρ(w, v)` of the arc `w → v` (in the block of `w`); if the arc is not served,
an arbitrary vertex of the block of `w`. -/
noncomputable def server (B : BlowUp H G) (w v : V) : W :=
  if h : ∃ x, B.π x = w ∧ B.serve x = some v then h.choose else (B.π_surjective w).choose

theorem π_server (B : BlowUp H G) (w v : V) : B.π (B.server w v) = w := by
  unfold server
  split_ifs with h
  · exact h.choose_spec.1
  · exact (B.π_surjective w).choose_spec

theorem serve_server (B : BlowUp H G) (hB : B.IsFull) {w v : V} (hwv : w < v)
    (hadj : H.Adj w v) : B.serve (B.server w v) = some v := by
  have h : ∃ x, B.π x = w ∧ B.serve x = some v := hB hwv hadj
  unfold server
  split_ifs
  exact h.choose_spec.2

/-- **The walk map (proof of Theorem 1.5, size bound).** In a full blow-up, a walk
`u_0 → ⋯ → u_{i+1}` of nodes whose blocks lie in `A` maps to the walk
`ρ(u_0,u_1) → ⋯ → ρ(u_i,u_{i+1})` with one arc fewer in `A`, injectively: `ρ(u_a,u_{a+1})`
determines its block `u_a`, and the last server determines the arc it serves. -/
theorem ncard_arcWalks_succ_le [Finite W] (B : BlowUp H G) (hB : B.IsFull) (A : Set W)
    (i : ℕ) : (arcWalks H (B.whole A) (i + 1)).ncard ≤ (arcWalks G A i).ncard := by
  let f : (Fin (i + 2) → V) → (Fin (i + 1) → W) := fun u a =>
    B.server (u a.castSucc) (u a.succ)
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_
  · rintro u ⟨huA, hu⟩
    refine ⟨fun a => huA a.castSucc _ (B.π_server _ _), fun a => ?_⟩
    have h1 := hu a.castSucc
    have e : (a.castSucc.succ : Fin (i + 2)) = a.succ.castSucc := Fin.succ_castSucc a
    refine ⟨B.lt_of_π_lt ?_, B.adj_of_serve ?_⟩
    · simp only [f, B.π_server]
      rw [← e]
      exact h1.1
    · simp only [f, B.π_server]
      rw [B.serve_server hB h1.1 h1.2, e]
  · rintro u ⟨-, hu⟩ u' ⟨-, hu'⟩ h
    funext b
    induction b using Fin.lastCases with
    | last =>
      have h1 := B.serve_server hB (hu (Fin.last i)).1 (hu (Fin.last i)).2
      have h2 := B.serve_server hB (hu' (Fin.last i)).1 (hu' (Fin.last i)).2
      have hf : f u (Fin.last i) = f u' (Fin.last i) := congrFun h (Fin.last i)
      simp only [f] at hf
      rw [hf, h2] at h1
      rw [← Fin.succ_last]
      exact (Option.some.inj h1).symm
    | cast a =>
      have hf : B.π (f u a) = B.π (f u' a) := congrArg B.π (congrFun h a)
      simpa only [f, B.π_server] using hf

/-- The nodes with a vertex in an initial segment form an initial segment. -/
theorem isLowerSet_image (B : BlowUp H G) {S : Set W} (hS : IsLowerSet S) :
    IsLowerSet (B.π '' S) := by
  rintro a b hba ⟨x, hx, rfl⟩
  obtain ⟨y, rfl⟩ := B.π_surjective b
  rcases hba.lt_or_eq with h | h
  · exact ⟨y, hS (B.lt_of_π_lt h).le hx, rfl⟩
  · exact ⟨x, hx, h.symm⟩

/-- **Alive nodes (proof of Theorem 1.5, poset bound).** The restriction of a full blow-up `G` of
`H` to an initial segment `S` is a full blow-up of `H` restricted to the nodes that have a vertex
in `S`: if `v` has a vertex in `S` and `w → v` is an arc, the whole block of `w` arrives before
that vertex, so the server of `w → v` lies in `S`. -/
theorem exists_restrict (B : BlowUp H G) (hB : B.IsFull) {S : Set W} (hS : IsLowerSet S) :
    ∃ B' : BlowUp (H.induce (B.π '' S)) (G.induce S), B'.IsFull := by
  classical
  let T := B.π '' S
  let π' : S → T := fun x => ⟨B.π x, Set.mem_image_of_mem _ x.2⟩
  let serve' : S → Option T := fun x =>
    (B.serve x).bind fun v => if h : v ∈ T then some ⟨v, h⟩ else none
  have hserve : ∀ x v, serve' x = some v ↔ B.serve x = some v.1 := by
    intro x v
    simp only [serve']
    cases hx : B.serve x with
    | none => simp
    | some w =>
      simp only [Option.bind_some, Option.some.injEq]
      split_ifs with hw
      · simp only [Option.some.injEq, Subtype.ext_iff]
      · simp only [false_iff]
        rintro rfl
        exact hw v.2
  refine ⟨
    { π := π'
      serve := serve'
      π_surjective := ?_
      lt_of_π_lt := ?_
      serve_spec := ?_
      adj_iff := ?_ }, ?_⟩
  · rintro ⟨v, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro x y h
    exact B.lt_of_π_lt h
  · intro x v h
    exact B.serve_spec ((hserve x v).1 h)
  · intro x u
    rw [hserve, hserve]
    exact B.adj_iff x u
  · intro w v hwv hadj
    obtain ⟨y, hy, hyv⟩ := v.2
    obtain ⟨x, hxw, hxs⟩ := hB hwv hadj
    have hxS : x ∈ S := hS (B.lt_of_π_lt (by rw [hxw, hyv]; exact hwv)).le hy
    exact ⟨⟨x, hxS⟩, Subtype.ext hxw, (hserve _ _).2 hxs⟩

end BlowUp

/-! ### Iterating down the full tower -/

/-- The top vertices all of whose descendants lie in `A` (the completely presented top vertices
if `A` is the set of presented vertices). -/
def towerWhole {m : ℕ} {X : Type*} (τ : X → Fin m) (A : Set X) : Set (Fin m) :=
  {t | ∀ x, τ x = t → x ∈ A}

theorem towerWhole_comp {m : ℕ} {V W : Type*} [LinearOrder V] [LinearOrder W]
    {H : SimpleGraph V} {G : SimpleGraph W} (B : BlowUp H G) (τ : V → Fin m) (A : Set W) :
    towerWhole (τ ∘ B.π) A = towerWhole τ (B.whole A) := by
  ext t
  simp only [towerWhole, BlowUp.whole, Set.mem_ofPred_eq, Function.comp]
  constructor
  · intro h v hv x hx
    exact h x (by rw [hx, hv])
  · intro h x hx
    exact h (B.π x) hx x rfl

theorem towerWhole_id {m : ℕ} (A : Set (Fin m)) : towerWhole (id : Fin m → Fin m) A = A := by
  ext t
  simp [towerWhole]

theorem towerWhole_univ {m : ℕ} {X : Type*} (τ : X → Fin m) :
    towerWhole τ Set.univ = Set.univ := by
  ext t
  simp [towerWhole]

namespace IsFullTowerAnc

variable {m j : ℕ} {G : OrdGraph} {τ : G.V → Fin m}

/-- Walks with `i + j` arcs among the top vertices whose subtrees lie in `A` map injectively to
walks with `i` arcs in `A`. -/
theorem ncard_arcWalks_add_le (hT : IsFullTowerAnc m j G τ) :
    ∀ [Finite G.V] (A : Set G.V) (i : ℕ),
      (arcWalks (⊤ : SimpleGraph (Fin m)) (towerWhole τ A) (i + j)).ncard ≤
        (arcWalks G.G A i).ncard := by
  induction hT with
  | clique =>
    intro _ A i
    have h : towerWhole (X := (OrdGraph.clique m).V) (@id (Fin m)) A = A := towerWhole_id A
    rw [h]
    exact le_rfl
  | @blowUp j H G τ B hB _ ih =>
    intro _ A i
    have : Finite H.V := B.finite
    rw [towerWhole_comp, show i + (j + 1) = (i + 1) + j by omega]
    exact (ih (B.whole A) (i + 1)).trans (B.ncard_arcWalks_succ_le hB A i)

/-- **The size bound, iterated.** For `i ≤ j`, there are at most `|A|` walks with `i` arcs
among the top vertices whose subtrees lie in `A`: applying the walk map `i` times turns them
into distinct nodes of level `j - i` whose subtrees lie in `A`. -/
theorem ncard_arcWalks_le (hT : IsFullTowerAnc m j G τ) :
    ∀ [Finite G.V] (A : Set G.V) (i : ℕ), i ≤ j →
      (arcWalks (⊤ : SimpleGraph (Fin m)) (towerWhole τ A) i).ncard ≤ A.ncard := by
  induction hT with
  | clique =>
    intro _ A i hi
    obtain rfl : i = 0 := by omega
    have h : towerWhole (X := (OrdGraph.clique m).V) (@id (Fin m)) A = A := towerWhole_id A
    rw [h]
    exact (ncard_arcWalks_zero _ _).le
  | @blowUp j H G τ B hB hT' ih =>
    intro _ A i hi
    have : Finite H.V := B.finite
    rw [towerWhole_comp]
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · exact (ih (B.whole A) i (by omega)).trans (B.ncard_whole_le A)
    · obtain rfl : i = j + 1 := by omega
      calc (arcWalks ⊤ (towerWhole τ (B.whole A)) (j + 1)).ncard
          = (arcWalks ⊤ (towerWhole τ (B.whole A)) (1 + j)).ncard := by rw [Nat.add_comm j 1]
        _ ≤ (arcWalks H.G (B.whole A) 1).ncard := hT'.ncard_arcWalks_add_le (B.whole A) 1
        _ ≤ (arcWalks G.G A 0).ncard := B.ncard_arcWalks_succ_le hB A 0
        _ = A.ncard := ncard_arcWalks_zero _ _

/-- **Theorem 1.5, size bound, general form.** If `C` top vertices have all their descendants in
`A`, then `|A| ≥ choose(C, i+1)` for every `i ≤ j`. -/
theorem choose_ncard_towerWhole_le (hT : IsFullTowerAnc m j G τ) [Finite G.V] (A : Set G.V)
    {i : ℕ} (hi : i ≤ j) : (towerWhole τ A).ncard.choose (i + 1) ≤ A.ncard :=
  (choose_le_ncard_arcWalks_top _ i).trans (hT.ncard_arcWalks_le A i hi)

/-- In an initial segment `S`, all top vertices with a descendant in `S` except the last one have
all their descendants in `S`. -/
theorem ncard_image_sub_one_le (hT : IsFullTowerAnc m j G τ) {S : Set G.V}
    (hS : IsLowerSet S) : (τ '' S).ncard - 1 ≤ (towerWhole τ S).ncard := by
  classical
  rcases (τ '' S).eq_empty_or_nonempty with he | hne
  · simp [he]
  have hne' : (τ '' S).toFinset.Nonempty := Set.toFinset_nonempty.2 hne
  set M := (τ '' S).toFinset.max' hne' with hM
  have hMmem : M ∈ τ '' S := Set.mem_toFinset.1 (Finset.max'_mem _ _)
  obtain ⟨x₀, hx₀, hx₀M⟩ := id hMmem
  have hsub : τ '' S \ {M} ⊆ towerWhole τ S := by
    rintro t ⟨ht, htM⟩ y hy
    have hle : t ≤ M := Finset.le_max' _ _ (Set.mem_toFinset.2 ht)
    have hlt : τ y < τ x₀ := by
      rw [hy, hx₀M]
      exact lt_of_le_of_ne hle htM
    exact hS (hT.lt_of_lt hlt).le hx₀
  rw [← Set.ncard_sdiff_singleton_of_mem hMmem]
  exact Set.ncard_le_ncard hsub

/-- Labels ascend through the alive part of a full tower: if an initial segment `S` has a
`P_i(k)`-labelling, then the clique on the top vertices with a descendant in `S` has a
`P_{i+j}(k)`-labelling, so there are at most `|P_{i+j}(k)|` of them. -/
theorem ncard_image_le_of_hasLabelling (hT : IsFullTowerAnc m j G τ) (k : ℕ) :
    ∀ (S : Set G.V), IsLowerSet S → ∀ i, HasLabelling (G.G.induce S) (LabelPoset k i) →
      (τ '' S).ncard ≤ Fintype.card (LabelPoset k (i + j)) := by
  induction hT with
  | clique =>
    intro S _ i h
    have hid : Set.image (α := (OrdGraph.clique m).V) (@id (Fin m)) S = S := Set.image_id S
    rw [hid]
    obtain ⟨f, hf⟩ := h
    have hf' : IsLabelling (⊤ : SimpleGraph S) f := fun u v huv _ =>
      hf huv (show (⊤ : SimpleGraph (Fin m)).Adj u.1 v.1 from
        (SimpleGraph.top_adj _ _).2 fun h => huv.ne (Subtype.ext h))
    have := Nat.card_le_card_of_injective f hf'.injective_of_top
    rwa [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
  | @blowUp j H G τ B hB _ ih =>
    intro S hS i h
    obtain ⟨B', hB'⟩ := B.exists_restrict hB hS
    have h' : HasLabelling (H.G.induce (B.π '' S)) (LabelPoset k (i + 1)) :=
      B'.hasLabelling_jst_of_full hB' h
    rw [Set.image_comp]
    have := ih (B.π '' S) (B.isLowerSet_image hS) (i + 1) h'
    rwa [show i + 1 + j = i + (j + 1) by omega] at this

/-- **Theorem 1.5, poset bound, initial segments.** If an initial segment `S` of a full
`j`-fold blow-up of `K_m` is `k`-colourable, then at most `|P_j(k)|` top vertices have a
descendant in `S`. -/
theorem ncard_image_le_of_colorable (hT : IsFullTowerAnc m j G τ) {S : Set G.V}
    (hS : IsLowerSet S) {k : ℕ} (hc : (G.G.induce S).Colorable k) :
    (τ '' S).ncard ≤ Fintype.card (LabelPoset k j) := by
  have := hT.ncard_image_le_of_hasLabelling k S hS 0 (hasLabelling_labelPoset_zero_iff.2 hc)
  rwa [Nat.zero_add] at this

/-- **Theorem 1.5, size bound, initial segments.** If `c` top vertices have a descendant in the
initial segment `S`, then `|S| ≥ choose(c-1, i+1)` for every `i ≤ j`. -/
theorem choose_le_ncard (hT : IsFullTowerAnc m j G τ) [Finite G.V] {S : Set G.V}
    (hS : IsLowerSet S) {i : ℕ} (hi : i ≤ j) :
    ((τ '' S).ncard - 1).choose (i + 1) ≤ S.ncard :=
  (Nat.choose_le_choose _ (hT.ncard_image_sub_one_le hS)).trans
    (hT.choose_ncard_towerWhole_le S hi)

/-- **Theorem 1.5 (a ceiling for towers), initial segments of full towers.** Let `S` be a
`k`-colourable initial segment of a full `j`-fold blow-up of `K_m`, and let `c` be the
number of colours First-Fit uses on it.  Then `c ≤ |P_j(k)|` and `|S| ≥ choose(c-1, i+1)` for
every `i ≤ j`. -/
theorem ceiling (hT : IsFullTowerAnc m j G τ) [Finite G.V] {S : Set G.V} (hS : IsLowerSet S)
    {k : ℕ} (hc : (G.G.induce S).Colorable k) :
    (Set.range (firstFit (G.G.induce S))).ncard ≤ Fintype.card (LabelPoset k j) ∧
      ∀ i ≤ j, ((Set.range (firstFit (G.G.induce S))).ncard - 1).choose (i + 1) ≤ S.ncard := by
  rw [hT.ncard_range_firstFit_induce hS]
  exact ⟨hT.ncard_image_le_of_colorable hS hc, fun i hi => hT.choose_le_ncard hS hi⟩

end IsFullTowerAnc

/-- **Theorem 1.5 (a ceiling for towers), full towers.** On a `k`-colourable full `j`-fold
blow-up `G` of `K_m`, First-Fit uses exactly `m` colours, `m ≤ |P_j(k)|`, and
`|V(G)| ≥ choose(m, i+1)` for every `i ≤ j`. -/
theorem IsFullTower.ceiling {m j k : ℕ} {G : OrdGraph} [Finite G.V] (hT : IsFullTower m j G)
    (hc : G.G.Colorable k) :
    (Set.range (firstFit G.G)).ncard = m ∧ m ≤ Fintype.card (LabelPoset k j) ∧
      ∀ i ≤ j, m.choose (i + 1) ≤ Nat.card G.V := by
  refine ⟨hT.ncard_range_firstFit, hT.le_card hc, fun i hi => ?_⟩
  obtain ⟨τ, hτ⟩ := hT.exists_anc
  have := hτ.choose_ncard_towerWhole_le Set.univ hi
  rwa [towerWhole_univ, Set.ncard_univ, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this

/-- **Theorem 1.5, full towers, in the paper's form** `|V(G)| ≥ choose(c-1, i+1)` with `c = m`. -/
theorem IsFullTower.choose_pred_le {m j : ℕ} {G : OrdGraph} [Finite G.V]
    (hT : IsFullTower m j G) {i : ℕ} (hi : i ≤ j) : (m - 1).choose (i + 1) ≤ Nat.card G.V := by
  obtain ⟨τ, hτ⟩ := hT.exists_anc
  have := hτ.choose_ncard_towerWhole_le Set.univ hi
  rw [towerWhole_univ, Set.ncard_univ, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this
  exact (Nat.choose_le_choose _ (Nat.sub_le m 1)).trans this

end OnlineColouring
