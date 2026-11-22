module

public import OnlineColouring.UWiringE
public import OnlineColouring.PadGraph
public import OnlineColouring.OddGirth

/-!
# Lemma 8.2 (one graph), for every wiring of `R_j(m)`

`UTowerE.lean` defines the uniform tower with one server map per node (top servers `τ s t`, maps
`φ s t k g`), and `UWiringE.lean` the sample space `EΩ m j A` of the paper's random wiring
`R_j(m)` (Construction 8.1).  This file proves Lemma 8.2 for every wiring `ω : EΩ m j A`.  The
paper has `A = 2m`; of this hypothesis, the statements for general `A` use only `0 < A` and, for
the isomorphism with the fixed digraph, `m ≤ A`.

* `IsResTower m A j G`: `G` is a `j`-fold *reservation* blow-up of `K_m` in which every block has
  exactly `A` nodes (every arc is served by exactly one node: `BlowUp.IsReservation`).
  `ueInput_isResTower`, `uInputE_isResTower`: the presented graph of every wiring is one.
* `uInputE_cliqueFree`: it is triangle-free (`j ≥ 1`); colourability is `uInputE_colorable` of
  `UWiringE.lean`.
* `ueSeq_seqIso`: two towers with distinct top servers per root and injective server maps are
  isomorphic as digraphs oriented by arrival.  As in the paper, the isomorphism is built level by
  level by the argument of Lemma 7.1 (`exists_perm_extend` of `Iso.lean`): the node `y` goes to
  the child `π_{y/A}(y mod A)` of the image of its parent, where the permutation `π_x` of the
  children of `x` extends the partial bijection forced by the servers in the block of `x`.
* `gSeq A j`, `Gjm j m`: the fixed digraph `G_j(m)` (the top server of the arc `v_s → v_t` is the
  child `t mod A` of `v_s`, and every bijection below the top is the identity) and its underlying
  graph on `m (2m)^j` vertices.  `uSeqE_seqIso_gSeq`, `uInputE_iso_Gjm`: every wiring presents a
  digraph isomorphic to it.
* `uniform_graph`: Lemma 8.2, all four statements together.
-/

@[expose] public section

namespace OnlineColouring

namespace Rjm

open Finset

/-! ### Iterated reservation blow-ups with blocks of one size -/

/-- `IsResTower m A j G`: the ordered graph `G` is a `j`-fold reservation blow-up of the clique
`K_m` in which every block has exactly `A` nodes. -/
inductive IsResTower (m A : ℕ) : ℕ → OrdGraph → Prop
  | clique : IsResTower m A 0 (OrdGraph.clique m)
  | blowUp {j : ℕ} {H G : OrdGraph} :
      IsResTower m A j H →
      (∃ B : BlowUp H.G G.G, B.IsReservation ∧ ∀ v : H.V, Nat.card {x : G.V // B.π x = v} = A) →
      IsResTower m A (j + 1) G

theorem IsResTower.isFullTower {m A j : ℕ} {G : OrdGraph} (h : IsResTower m A j G) :
    IsFullTower m j G := by
  induction h with
  | clique => exact .clique
  | blowUp _ hB ih =>
    obtain ⟨B, hB, -⟩ := hB
    exact .blowUp ih ⟨B, hB.isFull⟩

theorem IsResTower.isTower {m A j : ℕ} {G : OrdGraph} (h : IsResTower m A j G) : IsTower m j G :=
  h.isFullTower.isTower

/-- The blocks `{x : x / A = v}` have exactly `A` elements. -/
theorem card_divMap_fiber {M A : ℕ} (hA : 0 < A) (v : Fin M) :
    Nat.card {x : Fin (M * A) // divMap rfl x = v} = A := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hlt : ∀ i : Fin A, (v : ℕ) * A + i < M * A := fun i =>
    calc (v : ℕ) * A + i < v * A + A := by have := i.2; omega
      _ = (v + 1) * A := by ring
      _ ≤ M * A := Nat.mul_le_mul_right _ v.2
  have h := card_bij (s := (univ : Finset (Fin A)))
    (t := univ.filter fun x : Fin (M * A) => divMap rfl x = v)
    (fun i _ => ⟨(v : ℕ) * A + i, hlt i⟩)
    (fun i _ => by
      rw [mem_filter]
      exact ⟨mem_univ _, Fin.ext (div_mul_add_of_lt i.2)⟩)
    (fun i _ i' _ h => by
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega))
    (fun x hx => by
      have hx' : (x : ℕ) / A = v := congrArg Fin.val (mem_filter.1 hx).2
      refine ⟨⟨(x : ℕ) % A, Nat.mod_lt _ hA⟩, mem_univ _, Fin.ext ?_⟩
      change (v : ℕ) * A + (x : ℕ) % A = x
      rw [← hx', Nat.mul_comm]
      exact Nat.div_add_mod _ _)
  rw [← h, card_univ, Fintype.card_fin]

section Tower

variable {A : ℕ} {τ : ℕ → ℕ → ℕ} {φ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}

/-- The blow-up structure of the tower at depth `k + 1` over the tower at depth `k`. -/
noncomputable def ueBlowUp (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    BlowUp (ueInput hA hτ hφ m k).graph (ueInput hA hτ hφ m (k + 1)).graph := by
  refine divBlowUp hA rfl _ _ ?_ ?_ ?_
  · intro x y hxy
    obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
    refine mem_ueInput_nbr.2 (mem_ueSeq.2 ⟨s, ?_, ?_⟩)
    · change s < y / A / A ^ k
      rwa [← div_pow_succ]
    · change ueNb A τ φ k s (y / A) = x / A
      rw [← hsx, ueNb_succ_div hA hτ hφ]
  · intro x y y' hyy hxy
    obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
    refine (mem_ueInput_nbr (k := k + 1)).2 ?_
    have hr : (y : ℕ) / A ^ (k + 1) = y' / A ^ (k + 1) := by
      rw [div_pow_succ, div_pow_succ, hyy]
    exact mem_ueSeq.2 ⟨s, hr ▸ hs, (ueNb_congr hyy.symm).trans hsx⟩
  · intro x y y' hxy hxy'
    obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
    obtain ⟨s', hs', hsx'⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy')
    have hss : s = s' := by
      have h₁ := ueNb_div_pow hA hτ hφ (k + 1) s y
      have h₂ := ueNb_div_pow hA hτ hφ (k + 1) s' y'
      rw [hsx] at h₁
      rw [hsx'] at h₂
      rw [← h₁, ← h₂]
    subst hss
    exact ueNb_inj hA hτ hφ hφinj (hinj s) k hs (root_lt y.2) hs' (root_lt y'.2)
      (hsx.trans hsx'.symm)

theorem ueBlowUp_π (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    (ueBlowUp hA hτ hφ hφinj hinj k).π = divMap rfl := rfl

theorem ueBlowUp_serve (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    (ueBlowUp hA hτ hφ hφinj hinj k).serve = divServe rfl (ueInput hA hτ hφ m (k + 1)) := rfl

/-- **Every arc is served by exactly one node**: the arc `w → v` at depth `k`, with `w` below the
root `s`, is served by the neighbour below `s` of the children of `v`, and by no other child of
`w`. -/
theorem ueBlowUp_isReservation (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    (ueBlowUp hA hτ hφ hφinj hinj k).IsReservation := by
  intro w v hwv hadj
  -- `w` is an earlier neighbour of `v`
  have hwv' : w ∈ (ueInput hA hτ hφ m k).nbr v := by
    rcases OnlineInput.graph_adj.1 hadj with h | h
    · exact h
    · exact absurd ((ueInput hA hτ hφ m k).nbr_lt _ _ h) (lt_asymm hwv)
  obtain ⟨s, hs, hsw⟩ := mem_ueSeq.1 (mem_ueInput_nbr.1 hwv')
  -- a child of `v` and its neighbour below `s`
  have hy₀ : (v : ℕ) * A < utSize A m (k + 1) := Nat.mul_lt_mul_of_pos_right v.2 hA
  let y₀ : Fin (utSize A m (k + 1)) := ⟨(v : ℕ) * A, hy₀⟩
  have hy₀v : (y₀ : ℕ) / A = v := Nat.mul_div_cancel _ hA
  have hy₀r : (y₀ : ℕ) / A ^ (k + 1) = (v : ℕ) / A ^ k := by rw [div_pow_succ, hy₀v]
  have hsm : s < m := lt_trans hs (root_lt v.2)
  let x₀ : Fin (utSize A m (k + 1)) :=
    ⟨ueNb A τ φ (k + 1) s y₀, by
      apply lt_utSize_of_root hA
      rw [ueNb_div_pow hA hτ hφ]
      exact hsm⟩
  have hx₀y₀ : x₀ ∈ (ueInput hA hτ hφ m (k + 1)).nbr y₀ :=
    mem_ueInput_nbr.2 (mem_ueSeq.2 ⟨s, by rw [hy₀r]; exact hs, rfl⟩)
  have hG3 : ∀ x y y' : Fin (utSize A m (k + 1)), x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y →
      x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y' → (y : ℕ) / A = y' / A := by
    intro x y y' hxy hxy'
    obtain ⟨s₁, hs₁, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
    obtain ⟨s₂, hs₂, hsx'⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy')
    have hss : s₁ = s₂ := by
      have h₁ := ueNb_div_pow hA hτ hφ (k + 1) s₁ y
      have h₂ := ueNb_div_pow hA hτ hφ (k + 1) s₂ y'
      rw [hsx] at h₁
      rw [hsx'] at h₂
      rw [← h₁, ← h₂]
    subst hss
    exact ueNb_inj hA hτ hφ hφinj (hinj s₁) k hs₁ (root_lt y.2) hs₂ (root_lt y'.2)
      (hsx.trans hsx'.symm)
  have hπy₀ : divMap (M := utSize A m k) rfl y₀ = v := Fin.ext hy₀v
  refine ⟨x₀, ⟨?_, ?_⟩, ?_⟩
  · rw [ueBlowUp_π]
    apply Fin.ext
    change ueNb A τ φ (k + 1) s y₀ / A = w
    rw [ueNb_succ_div hA hτ hφ, hy₀v, hsw]
  · exact (divServe_of_mem (hM := rfl) (G := ueInput hA hτ hφ m (k + 1)) hG3 hx₀y₀).trans
      (congrArg some hπy₀)
  · rintro x ⟨hxw, hxs⟩
    rw [ueBlowUp_serve] at hxs
    rw [ueBlowUp_π] at hxw
    obtain ⟨y, hxy, hyv⟩ := divServe_spec hxs
    have hyv' : (y : ℕ) / A = v := congrArg Fin.val hyv
    obtain ⟨s', hs', hs'x⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
    have hxw' : (x : ℕ) / A = w := congrArg Fin.val hxw
    have hss : s' = s := by
      have h₁ := ueNb_div_pow hA hτ hφ (k + 1) s' y
      have h₂ := ueNb_div_pow hA hτ hφ k s v
      rw [hs'x, div_pow_succ, hxw'] at h₁
      rw [hsw] at h₂
      rw [← h₁, ← h₂]
    apply Fin.ext
    change (x : ℕ) = ueNb A τ φ (k + 1) s y₀
    rw [← hs'x, hss]
    exact ueNb_congr (by rw [hyv', hy₀v])

/-- **The tower is an iterated reservation blow-up of `K_m` with all blocks of size `A`.** -/
theorem ueInput_isResTower (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    IsResTower m A k (ueInput hA hτ hφ m k).toOrdGraph := by
  induction k with
  | zero =>
    have h : (ueInput hA hτ hφ m 0).toOrdGraph = OrdGraph.clique m := by
      unfold ueInput
      rw [OnlineInput.ofSeq_congr ueSeq_zero]
      exact ofSeq_cliqueSeq m
    rw [h]
    exact .clique
  | succ k ih =>
    exact .blowUp ih ⟨ueBlowUp hA hτ hφ hφinj hinj k, ueBlowUp_isReservation hA hτ hφ hφinj hinj k,
      fun v => card_divMap_fiber hA v⟩

/-! ### The level-by-level isomorphism -/

variable {τ' : ℕ → ℕ → ℕ} {φ' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}

/-- The digit of a server depends only on the parent of the node. -/
theorem ueDig_congr {k s t y y' : ℕ} (h : y / A = y' / A) :
    ueDig A τ φ k s t y = ueDig A τ φ k s t y' := by
  cases k with
  | zero => rfl
  | succ k => simp only [ueDig, h]

/-- The neighbour below a root `s < m` is a node of the tower. -/
theorem ueNb_lt_utSize (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    {m k s : ℕ} (hs : s < m) (y : ℕ) : ueNb A τ φ k s y < utSize A m k := by
  apply lt_utSize_of_root hA
  rw [ueNb_div_pow hA hτ hφ]
  exact hs

/-- The invariant of the isomorphism at depth `k`: `F` is injective on the nodes, keeps the root,
maps sibling sets to sibling sets and commutes with the neighbour maps. -/
structure UEIsoAt (A : ℕ) (τ τ' : ℕ → ℕ → ℕ) (φ φ' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (m k : ℕ)
    (F : ℕ → ℕ) : Prop where
  inj : ∀ y < utSize A m k, ∀ y' < utSize A m k, F y = F y' → y = y'
  root : ∀ y < utSize A m k, F y / A ^ k = y / A ^ k
  sib : ∀ y < utSize A m k, ∀ y' < utSize A m k, y / A = y' / A → F y / A = F y' / A
  nb : ∀ y < utSize A m k, ∀ s < y / A ^ k, F (ueNb A τ φ k s y) = ueNb A τ' φ' k s (F y)

theorem ueIsoAt_zero (m : ℕ) : UEIsoAt A τ τ' φ φ' m 0 id where
  inj _ _ _ _ h := h
  root _ _ := rfl
  sib _ _ _ _ h := h
  nb _ _ _ _ := rfl

/-- **The induction step** (the argument of Lemma 7.1, one level down). -/
theorem UEIsoAt.succ (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hτ' : ∀ s t, τ' s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A) (hφ' : ∀ s t k g i, φ' s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i')
    (hφinj' : ∀ s t k g i i', i < A → i' < A → φ' s t k g i = φ' s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t')
    (hinj' : ∀ s t t', s < t → t < m → s < t' → t' < m → τ' s t = τ' s t' → t = t')
    {k : ℕ} {F : ℕ → ℕ} (hF : UEIsoAt A τ τ' φ φ' m k F) :
    ∃ F' : ℕ → ℕ, UEIsoAt A τ τ' φ φ' m (k + 1) F' := by
  -- the nodes `u` of depth `k` whose `s`-neighbour is `x` (with `s` the root of `x`)
  let S : ℕ → Set ℕ := fun x =>
    {u | u < utSize A m k ∧ x / A ^ k < u / A ^ k ∧ ueNb A τ φ k (x / A ^ k) u = x}
  let f : ℕ → ℕ → Fin A := fun x u =>
    ⟨ueDig A τ φ k (x / A ^ k) (u / A ^ k) (u * A), ueDig_lt hτ hφ _ _ _ _⟩
  let g : ℕ → ℕ → Fin A := fun x u =>
    ⟨ueDig A τ' φ' k (x / A ^ k) (u / A ^ k) (F u * A), ueDig_lt hτ' hφ' _ _ _ _⟩
  -- two nodes with the same `s`-neighbour are siblings (for `k ≥ 1`)
  have hsibS : ∀ x, ∀ u ∈ S x, ∀ u' ∈ S x, 1 ≤ k → u / A = u' / A := by
    intro x u hu u' hu' hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ueNb_inj hA hτ hφ hφinj (hinj (x / A ^ (k' + 1))) k' hu.2.1 (root_lt hu.1) hu'.2.1
      (root_lt hu'.1) (hu.2.2.trans hu'.2.2.symm)
  have hf : ∀ x, Set.InjOn (f x) (S x) := by
    intro x u hu u' hu' he
    have he' := congrArg Fin.val he
    simp only [f] at he'
    cases k with
    | zero =>
      have a1 := hu.2.1
      have a2 := hu'.2.1
      simp only [ueDig, pow_zero, Nat.div_one] at he' a1 a2
      exact hinj _ _ _ a1 hu.1 a2 hu'.1 he'
    | succ k =>
      have hp := hsibS x u hu u' hu' (by omega)
      have hr : u / A ^ (k + 1) = u' / A ^ (k + 1) := by rw [div_pow_succ, div_pow_succ, hp]
      simp only [ueDig, Nat.mul_div_cancel _ hA, hr, hp] at he'
      have hm := hφinj _ _ _ _ _ _ (Nat.mod_lt _ hA) (Nat.mod_lt _ hA) he'
      rw [← Nat.div_add_mod u A, ← Nat.div_add_mod u' A, hp, hm]
  have hg : ∀ x, Set.InjOn (g x) (S x) := by
    intro x u hu u' hu' he
    have he' := congrArg Fin.val he
    simp only [g] at he'
    cases k with
    | zero =>
      have a1 := hu.2.1
      have a2 := hu'.2.1
      simp only [ueDig, pow_zero, Nat.div_one] at he' a1 a2
      exact hinj' _ _ _ a1 hu.1 a2 hu'.1 he'
    | succ k =>
      have hp := hsibS x u hu u' hu' (by omega)
      have hr : u / A ^ (k + 1) = u' / A ^ (k + 1) := by rw [div_pow_succ, div_pow_succ, hp]
      have hdiv := hF.sib u hu.1 u' hu'.1 hp
      simp only [ueDig, Nat.mul_div_cancel _ hA, hr, hdiv] at he'
      have hm := hφinj' _ _ _ _ _ _ (Nat.mod_lt _ hA) (Nat.mod_lt _ hA) he'
      have hFe : F u = F u' := by
        rw [← Nat.div_add_mod (F u) A, ← Nat.div_add_mod (F u') A, hdiv, hm]
      exact hF.inj u hu.1 u' hu'.1 hFe
  choose π hπ using fun x => exists_perm_extend (hf x) (hg x)
  -- the new map: the child `i` of `u` goes to the child `π_u(i)` of `F u`
  let ψ : ℕ → ℕ := fun y => F (y / A) * A + (π (y / A) ⟨y % A, Nat.mod_lt _ hA⟩ : ℕ)
  have hψdiv : ∀ y, ψ y / A = F (y / A) := fun y => div_mul_add_of_lt (Fin.isLt _)
  have hψmod : ∀ y, ψ y % A = π (y / A) ⟨y % A, Nat.mod_lt _ hA⟩ :=
    fun y => mod_mul_add_of_lt (Fin.isLt _)
  have hψroot : ∀ y < utSize A m (k + 1), ψ y / A ^ (k + 1) = y / A ^ (k + 1) := by
    intro y hy
    rw [div_pow_succ, div_pow_succ, hψdiv, hF.root _ (div_lt_utSize hy)]
  refine ⟨ψ, ⟨?_, hψroot, ?_, ?_⟩⟩
  · -- injectivity
    intro y hy y' hy' he
    have h₁ : F (y / A) = F (y' / A) := by rw [← hψdiv, ← hψdiv, he]
    have hp := hF.inj _ (div_lt_utSize hy) _ (div_lt_utSize hy') h₁
    have h₂ := hψmod y
    rw [he, hψmod y', hp] at h₂
    have h₃ : (⟨y' % A, Nat.mod_lt _ hA⟩ : Fin A) = ⟨y % A, Nat.mod_lt _ hA⟩ :=
      (π (y' / A)).injective (Fin.ext h₂)
    have hm : y' % A = y % A := congrArg Fin.val h₃
    rw [← Nat.div_add_mod y A, ← Nat.div_add_mod y' A, hp, hm]
  · -- siblings
    intro y _ y' _ h
    rw [hψdiv, hψdiv, h]
  · -- the neighbour maps
    intro y hy s hs
    set u := y / A with hu_def
    have hu : u < utSize A m k := div_lt_utSize hy
    have ht : y / A ^ (k + 1) = u / A ^ k := div_pow_succ y k
    set x := ueNb A τ φ k s u with hx_def
    have hxs : x / A ^ k = s := ueNb_div_pow hA hτ hφ k s u
    have hsu : s < u / A ^ k := ht ▸ hs
    have huS : u ∈ S x := ⟨hu, hxs ▸ hsu, by rw [hxs]⟩
    have hπu := hπ x u huS
    -- the image of the neighbour
    have hz : ueNb A τ φ (k + 1) s y = x * A + ueDig A τ φ k s (u / A ^ k) (u * A) := by
      rw [ueNb, ← hu_def, ← ht, ← hx_def]
      congr 1
      exact ueDig_congr (by rw [Nat.mul_div_cancel _ hA])
    have hzdiv : ueNb A τ φ (k + 1) s y / A = x := by
      rw [hz]; exact div_mul_add_of_lt (ueDig_lt hτ hφ _ _ _ _)
    have hzmod : ueNb A τ φ (k + 1) s y % A = ueDig A τ φ k s (u / A ^ k) (u * A) := by
      rw [hz]; exact mod_mul_add_of_lt (ueDig_lt hτ hφ _ _ _ _)
    have hfx : (⟨ueNb A τ φ (k + 1) s y % A, Nat.mod_lt _ hA⟩ : Fin A) = f x u := by
      apply Fin.ext
      simp only [f, hxs, hzmod]
    change F (ueNb A τ φ (k + 1) s y / A) * A +
        (π (ueNb A τ φ (k + 1) s y / A) ⟨ueNb A τ φ (k + 1) s y % A, Nat.mod_lt _ hA⟩ : ℕ) = _
    rw [hfx]
    simp only [hzdiv]
    rw [hπu, hF.nb u hu s hsu]
    rw [ueNb, hψdiv, ← hu_def, hψroot y hy, ht]
    simp only [g, hxs]
    congr 1
    exact ueDig_congr (by rw [hψdiv, Nat.mul_div_cancel _ hA])

/-- **The isomorphism, at every depth.** -/
theorem exists_ueIsoAt (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hτ' : ∀ s t, τ' s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A) (hφ' : ∀ s t k g i, φ' s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i')
    (hφinj' : ∀ s t k g i i', i < A → i' < A → φ' s t k g i = φ' s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t')
    (hinj' : ∀ s t t', s < t → t < m → s < t' → t' < m → τ' s t = τ' s t' → t = t') :
    ∀ k, ∃ F : ℕ → ℕ, UEIsoAt A τ τ' φ φ' m k F := by
  intro k
  induction k with
  | zero => exact ⟨id, ueIsoAt_zero m⟩
  | succ k ih =>
    obtain ⟨F, hF⟩ := ih
    exact hF.succ hA hτ hτ' hφ hφ' hφinj hφinj' hinj hinj'

/-- **Lemma 8.2 (isomorphism part), for arbitrary server maps.** Two uniform towers whose top
servers are distinct for each root and whose server maps are injective are isomorphic as digraphs
oriented by arrival. -/
theorem ueSeq_seqIso (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hτ' : ∀ s t, τ' s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A) (hφ' : ∀ s t k g i, φ' s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i')
    (hφinj' : ∀ s t k g i i', i < A → i' < A → φ' s t k g i = φ' s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t')
    (hinj' : ∀ s t t', s < t → t < m → s < t' → t' < m → τ' s t = τ' s t' → t = t') (k : ℕ) :
    SeqIso (ueSeq A τ φ k) (ueSeq A τ' φ' k) (utSize A m k) := by
  obtain ⟨F, hF⟩ := exists_ueIsoAt hA hτ hτ' hφ hφ' hφinj hφinj' hinj hinj' k
  have hlt : ∀ y : Fin (utSize A m k), F y < utSize A m k := fun y =>
    lt_utSize_of_root hA (by rw [hF.root y y.2]; exact root_lt y.2)
  let E : Fin (utSize A m k) → Fin (utSize A m k) := fun y => ⟨F y, hlt y⟩
  have hE : Function.Injective E := fun y y' h =>
    Fin.ext (hF.inj y y.2 y' y'.2 (congrArg Fin.val h))
  let e := Equiv.ofBijective E (Finite.injective_iff_bijective.1 hE)
  refine ⟨e, fun u v => ?_⟩
  change (u : ℕ) ∈ ueSeq A τ φ k v ↔ F u ∈ ueSeq A τ' φ' k (F v)
  rw [mem_ueSeq, mem_ueSeq, hF.root v v.2]
  constructor
  · rintro ⟨s, hs, hsu⟩
    exact ⟨s, hs, by rw [← hsu, hF.nb v v.2 s hs]⟩
  · rintro ⟨s, hs, hsu⟩
    refine ⟨s, hs, hF.inj _ (ueNb_lt_utSize hA hτ hφ (lt_trans hs (root_lt v.2)) v) _ u.2 ?_⟩
    rw [hF.nb v v.2 s hs, hsu]

end Tower

/-! ### The fixed digraph `G_j(m)` -/

/-- The canonical uniform tower with blocks of size `A`: the arc `v_s → v_t` is served by the
child `t mod A` of `v_s`, and every bijection below the top is the identity. -/
def gSeq (A j : ℕ) : ℕ → Finset ℕ :=
  ueSeq A (fun _ t => t % A) (fun _ _ _ _ i => i % A) j

theorem gSeq_valid (A j : ℕ) : ValidSeq (gSeq A j) := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · cases j with
    | zero =>
      unfold gSeq
      rw [ueSeq_zero]
      exact cliqueSeq_valid
    | succ j =>
      intro y x hx
      simp [gSeq, ueSeq] at hx
  · exact ueSeq_valid hA (fun _ _ => Nat.mod_lt _ hA) (fun _ _ _ _ _ => Nat.mod_lt _ hA) j

theorem gTop_inj {A m : ℕ} (hmA : m ≤ A) :
    ∀ s t t', s < t → t < m → s < t' → t' < m →
      (fun (_ t : ℕ) => t % A) s t = (fun (_ t : ℕ) => t % A) s t' → t = t' := by
  intro s t t' _ ht _ ht' h
  simp only at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

theorem gPhi_inj {A : ℕ} : ∀ (s t k g i i' : ℕ), i < A → i' < A →
    (fun (_ _ _ _ i : ℕ) => i % A) s t k g i = (fun (_ _ _ _ i : ℕ) => i % A) s t k g i' →
      i = i' := by
  intro _ _ _ _ i i' hi hi' h
  simp only at h
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h

/-- **The graph `G_j(m)`** of Lemma 8.2, on `m (2m)^j` vertices (the underlying graph of the
digraph `gSeq (2m) j` on its first `m (2m)^j` vertices). -/
def Gjm (j m : ℕ) : SimpleGraph (Fin (m * (2 * m) ^ j)) :=
  (OnlineInput.ofSeq (gSeq (2 * m) j) (gSeq_valid (2 * m) j) _).graph

variable {m j A : ℕ}

/-- **Lemma 8.2, isomorphism as digraphs oriented by arrival.** For every wiring `ω`, the
presented digraph is isomorphic to the fixed digraph `gSeq A j` on `m A^j` vertices. -/
theorem uSeqE_seqIso_gSeq (hmA : m ≤ A) (hA : 0 < A) (ω : EΩ m j A) :
    SeqIso (uSeqE ω) (gSeq A j) (m * A ^ j) := by
  have h : SeqIso (uSeqE ω) (gSeq A j) (utSize A m j) :=
    ueSeq_seqIso hA (tauE_lt ω hA) (fun _ _ => Nat.mod_lt _ hA) (phiE_lt ω hA)
      (fun _ _ _ _ _ => Nat.mod_lt _ hA) (phiE_inj ω) gPhi_inj (tauE_inj ω) (gTop_inj hmA) j
  rwa [utSize_eq] at h

/-- **Lemma 8.2, first statement.** For every wiring, the presented graph is a `j`-fold
reservation blow-up of `K_m` with all blocks of size `A`. -/
theorem uInputE_isResTower (hA : 0 < A) (ω : EΩ m j A) :
    IsResTower m A j (uInputE hA ω).toOrdGraph :=
  ueInput_isResTower hA (tauE_lt ω hA) (phiE_lt ω hA) (phiE_inj ω) (tauE_inj ω) j

/-- **Lemma 8.2, triangle-freeness.** -/
theorem uInputE_cliqueFree (hA : 0 < A) (hj : 1 ≤ j) (ω : EΩ m j A) :
    (uInputE hA ω).graph.CliqueFree 3 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact (uInputE_isResTower hA ω).isTower.cliqueFree_three

/-- **Lemma 8.2, isomorphism of the presented graphs.** Every wiring of `R_j(m)` presents a graph
isomorphic to `G_j(m)`. -/
theorem uInputE_iso_Gjm (hA : 0 < 2 * m) (ω : EΩ m j (2 * m)) :
    Nonempty ((uInputE hA ω).graph ≃g Gjm j m) := by
  have hseq : SeqIso (uSeqE ω) (gSeq (2 * m) j) (utSize (2 * m) m j) :=
    ueSeq_seqIso hA (tauE_lt ω hA) (fun _ _ => Nat.mod_lt _ hA) (phiE_lt ω hA)
      (fun _ _ _ _ _ => Nat.mod_lt _ hA) (phiE_inj ω) gPhi_inj (tauE_inj ω)
      (gTop_inj (by omega)) j
  obtain ⟨e₁⟩ := hseq.graphIso (ueSeq_valid hA (tauE_lt ω hA) (phiE_lt ω hA) j)
    (gSeq_valid (2 * m) j)
  obtain ⟨e₂⟩ := ofSeq_graph_iso_of_eq (H := gSeq (2 * m) j) (hH := gSeq_valid (2 * m) j)
    (utSize_eq (2 * m) m j)
  exact ⟨e₁.trans e₂⟩

/-- **Lemma 8.2 (one graph).** Let `j ≥ 1`, `m ≥ 1` and `A = 2m`.  For every wiring `ω` of
`R_j(m)`, the presented graph is a `j`-fold reservation blow-up of `K_m` with all blocks of size
`A`; it is triangle-free; it is `k`-colourable whenever `m ≤ |P_j(k)|`; and, as a digraph oriented
by arrival, it is isomorphic to the fixed digraph `gSeq (2m) j` (whose underlying graph is
`Gjm j m`), which does not depend on `ω`. -/
theorem uniform_graph (hj : 1 ≤ j) (hA : 0 < 2 * m) (ω : EΩ m j (2 * m)) :
    IsResTower m (2 * m) j (uInputE hA ω).toOrdGraph ∧
      (uInputE hA ω).graph.CliqueFree 3 ∧
      (∀ k, m ≤ Fintype.card (LabelPoset k j) → (uInputE hA ω).graph.Colorable k) ∧
      SeqIso (uSeqE ω) (gSeq (2 * m) j) (m * (2 * m) ^ j) ∧
      Nonempty ((uInputE hA ω).graph ≃g Gjm j m) :=
  ⟨uInputE_isResTower hA ω, uInputE_cliqueFree hA hj ω, fun _ hP => uInputE_colorable ω hA hP,
    uSeqE_seqIso_gSeq (by omega) hA ω, uInputE_iso_Gjm hA ω⟩

/-- `G_j(m)` is itself presented by a tower: it is a `j`-fold reservation blow-up of `K_m` with
blocks of size `2m`, up to the identification of `m (2m)^j` with the number of leaves. -/
theorem gInput_isResTower (hA : 0 < 2 * m) :
    IsResTower m (2 * m) j
      (ueInput (τ := fun _ t => t % (2 * m)) (φ := fun _ _ _ _ i => i % (2 * m)) hA
        (fun _ _ => Nat.mod_lt _ hA) (fun _ _ _ _ _ => Nat.mod_lt _ hA) m j).toOrdGraph :=
  ueInput_isResTower hA _ _ gPhi_inj (gTop_inj (by omega)) j

/-- `G_j(m)` is `k`-colourable when `m ≤ |P_j(k)|`. -/
theorem Gjm_colorable {k : ℕ} (hm : 1 ≤ m) (hP : m ≤ Fintype.card (LabelPoset k j)) :
    (Gjm j m).Colorable k := by
  have hA : 0 < 2 * m := by omega
  have hc := (gInput_isResTower (j := j) hA).isTower.colorable hP
  obtain ⟨e⟩ := ofSeq_graph_iso_of_eq (H := gSeq (2 * m) j) (hH := gSeq_valid (2 * m) j)
    (utSize_eq (2 * m) m j)
  exact SimpleGraph.Colorable.of_hom e.symm.toHom hc

/-- `G_j(m)` is triangle-free for `j ≥ 1`. -/
theorem Gjm_cliqueFree (hm : 1 ≤ m) (hj : 1 ≤ j) : (Gjm j m).CliqueFree 3 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hA : 0 < 2 * m := by omega
  have hc := (gInput_isResTower (j := j + 1) hA).isTower.cliqueFree_three
  obtain ⟨e⟩ := ofSeq_graph_iso_of_eq (H := gSeq (2 * m) (j + 1))
    (hH := gSeq_valid (2 * m) (j + 1)) (utSize_eq (2 * m) m (j + 1))
  exact hc.comap ⟨e.symm.toEmbedding.toCopy⟩

end Rjm

end OnlineColouring
