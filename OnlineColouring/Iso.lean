module

public import OnlineColouring.SeqBlowUp
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The server assignment does not matter (Lemma 7.1)

`SeqIso H H' m`: the first `m` vertices of the input sequences `H` and `H'` form isomorphic
digraphs, with every edge oriented from the earlier endpoint (an earlier neighbour) to the later
one.  The isomorphism need not respect the arrival order.

* `SeqIso.blowSeq` (Lemma 7.1): if `H ≅ H'` and all post-degrees are at most `R`, then
  `blowSeq R H σ ≅ blowSeq R H' σ'` for all block permutations `σ, σ'`.  The isomorphism maps
  blocks to blocks: inside the block of `w` it is a permutation `π_w` of the positions with
  `π_w(σ_w(rank H w v)) = σ'_{φ w}(rank H' (φ w) (φ v))` for every out-neighbour `v` of `w`
  (`exists_perm_extend`).  The statement that records "blocks to blocks" in its conclusion is
  `Paper.blowSeq_iso_blocks` (`PaperStatements.lean`).
* `SeqIso.truncSeq`: appending the same isolated vertices keeps the isomorphism.
* `SeqIso.graphIso`: an isomorphism of digraphs is an isomorphism of the underlying graphs.
* `cliqueFree_three_ofSeq`: a sequence in which no vertex serves two adjacent vertices gives a
  triangle-free graph (Remark 6.5), and blow-ups have this property (`notMem_of_mem_blowSeq`).

In the terms of Section 7, a digraph `H` on `[m]` is an input sequence (`u → v` iff `u ∈ H v`),
its out-degrees are the post-degrees `postDeg H m w`, and a server assignment `ρ` is a block
permutation: `ρ(w, v)` is the vertex in position `σ_w(r)` of the block of `w` when `v` is the
`r`-th out-neighbour of `w`, with `σ_w` injective on `[R]`.  `blowSeq R H σ` is `Bl_ρ(H)`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-- The first `m` vertices of `H` and of `H'` form isomorphic digraphs (arcs go from an earlier
neighbour to the vertex). -/
def SeqIso (H H' : ℕ → Finset ℕ) (m : ℕ) : Prop :=
  ∃ φ : Fin m ≃ Fin m, ∀ u v : Fin m, (u : ℕ) ∈ H v ↔ (φ u : ℕ) ∈ H' (φ v)

theorem SeqIso.refl (H : ℕ → Finset ℕ) (m : ℕ) : SeqIso H H m :=
  ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

/-- Isomorphic digraphs have isomorphic underlying graphs. -/
theorem SeqIso.graphIso {H H' : ℕ → Finset ℕ} {m : ℕ} (hH : ValidSeq H) (hH' : ValidSeq H')
    (h : SeqIso H H' m) :
    Nonempty ((OnlineInput.ofSeq H hH m).graph ≃g (OnlineInput.ofSeq H' hH' m).graph) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨⟨φ, fun {u v} => ?_⟩⟩
  rw [OnlineInput.ofSeq_adj, OnlineInput.ofSeq_adj, hφ u v, hφ v u]

/-- A partial bijection of a finite type extends to a permutation. -/
theorem exists_perm_extend {ι α : Type*} [Finite α] {s : Set ι} {f g : ι → α}
    (hf : Set.InjOn f s) (hg : Set.InjOn g s) :
    ∃ π : Equiv.Perm α, ∀ i ∈ s, π (f i) = g i := by
  classical
  let e : (f '' s) ≃ (g '' s) :=
    (Equiv.Set.imageOfInjOn f s hf).symm.trans (Equiv.Set.imageOfInjOn g s hg)
  refine ⟨e.extendSubtype, fun i hi => ?_⟩
  have hmem : f i ∈ f '' s := Set.mem_image_of_mem f hi
  rw [Equiv.extendSubtype_apply_of_mem e (f i) hmem]
  have h₁ : (Equiv.Set.imageOfInjOn f s hf).symm ⟨f i, hmem⟩ = ⟨i, hi⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  change ((Equiv.Set.imageOfInjOn g s hg) ((Equiv.Set.imageOfInjOn f s hf).symm ⟨f i, hmem⟩) :
    α) = g i
  rw [h₁]
  rfl

variable {R : ℕ} {H : ℕ → Finset ℕ} {σ : ℕ → ℕ → ℕ}

/-- Membership in a blow-up in terms of block and position. -/
theorem mem_blowSeq_iff_mod (hR : 0 < R) (hσ : BlockPerm R σ) {x p : ℕ} :
    x ∈ blowSeq R H σ p ↔ x / R ∈ H (p / R) ∧ x % R = σ (x / R) (rank H (x / R) (p / R)) := by
  rw [mem_blowSeq hR hσ]
  have := Nat.div_add_mod' x R
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by omega⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by omega⟩

theorem rank_lt_of_postDeg {m w v : ℕ} (hdeg : postDeg H m w ≤ R) (hv : v < m) (hw : w ∈ H v) :
    rank H w v < R :=
  (rank_lt_rank hv hw).trans_le hdeg

/-- **Lemma 7.1 (the server assignment does not matter).** -/
theorem SeqIso.blowSeq {H' : ℕ → Finset ℕ} {σ' : ℕ → ℕ → ℕ} {m : ℕ} (hR : 0 < R)
    (hσ : BlockPerm R σ) (hσ' : BlockPerm R σ') (hdeg : ∀ w < m, postDeg H m w ≤ R)
    (hdeg' : ∀ w < m, postDeg H' m w ≤ R) (h : SeqIso H H' m) :
    SeqIso (OnlineColouring.blowSeq R H σ) (OnlineColouring.blowSeq R H' σ') (m * R) := by
  obtain ⟨φ, hφ⟩ := h
  -- the positions of the servers in the block of `w`, and where they must go
  let f : Fin m → Fin m → Fin R := fun w v => ⟨σ w (rank H w v), hσ.lt _ _⟩
  let g : Fin m → Fin m → Fin R := fun w v => ⟨σ' (φ w) (rank H' (φ w) (φ v)), hσ'.lt _ _⟩
  let s : Fin m → Set (Fin m) := fun w => {v | (w : ℕ) ∈ H v}
  have hf : ∀ w, Set.InjOn (f w) (s w) := by
    intro w v₁ hv₁ v₂ hv₂ he
    have he' : σ w (rank H w v₁) = σ w (rank H w v₂) := congrArg Fin.val he
    have hr := hσ.inj w _ _ (rank_lt_of_postDeg (hdeg w w.2) v₁.2 hv₁)
      (rank_lt_of_postDeg (hdeg w w.2) v₂.2 hv₂) he'
    exact Fin.ext (rank_inj hv₁ hv₂ hr)
  have hg : ∀ w, Set.InjOn (g w) (s w) := by
    intro w v₁ hv₁ v₂ hv₂ he
    have hv₁' : (φ w : ℕ) ∈ H' (φ v₁) := (hφ w v₁).1 hv₁
    have hv₂' : (φ w : ℕ) ∈ H' (φ v₂) := (hφ w v₂).1 hv₂
    have he' : σ' (φ w) (rank H' (φ w) (φ v₁)) = σ' (φ w) (rank H' (φ w) (φ v₂)) :=
      congrArg Fin.val he
    have hr := hσ'.inj (φ w) _ _ (rank_lt_of_postDeg (hdeg' _ (φ w).2) (φ v₁).2 hv₁')
      (rank_lt_of_postDeg (hdeg' _ (φ w).2) (φ v₂).2 hv₂') he'
    exact φ.injective (Fin.ext (rank_inj hv₁' hv₂' hr))
  choose π hπ using fun w => exists_perm_extend (hf w) (hg w)
  -- the isomorphism: block `w` goes to block `φ w`, position `t` to position `π w t`
  let Ψ : Fin (m * R) ≃ Fin (m * R) :=
    (finProdFinEquiv.symm.trans (Equiv.prodShear φ π)).trans finProdFinEquiv
  have hΨ : ∀ x : Fin (m * R),
      (Ψ x : ℕ) = (π x.divNat x.modNat : ℕ) + R * (φ x.divNat : ℕ) := fun x => rfl
  have hΨdiv : ∀ x : Fin (m * R), (Ψ x : ℕ) / R = φ x.divNat := by
    intro x
    rw [hΨ, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (π _ _).2, Nat.zero_add]
  have hΨmod : ∀ x : Fin (m * R), (Ψ x : ℕ) % R = π x.divNat x.modNat := by
    intro x
    rw [hΨ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (π _ _).2]
  refine ⟨Ψ, fun x u => ?_⟩
  rw [mem_blowSeq_iff_mod hR hσ, mem_blowSeq_iff_mod hR hσ', hΨdiv, hΨdiv, hΨmod]
  change (x.divNat : ℕ) ∈ H u.divNat ∧ (x.modNat : ℕ) = σ x.divNat (rank H x.divNat u.divNat) ↔
    (φ x.divNat : ℕ) ∈ H' (φ u.divNat) ∧
      (π x.divNat x.modNat : ℕ) = σ' (φ x.divNat) (rank H' (φ x.divNat) (φ u.divNat))
  rw [← hφ]
  constructor
  · rintro ⟨hw, ht⟩
    refine ⟨hw, ?_⟩
    have : x.modNat = f x.divNat u.divNat := Fin.ext ht
    rw [this, hπ _ _ hw]
  · rintro ⟨hw, ht⟩
    refine ⟨hw, ?_⟩
    have h₁ : π x.divNat x.modNat = g x.divNat u.divNat := Fin.ext ht
    rw [← hπ _ _ hw] at h₁
    exact congrArg Fin.val ((π x.divNat).injective h₁)

/-- Appending the same isolated vertices to isomorphic digraphs keeps them isomorphic. -/
theorem SeqIso.truncSeq {H' : ℕ → Finset ℕ} {m n : ℕ} (hH : ValidSeq H) (hH' : ValidSeq H')
    (hmn : m ≤ n) (h : SeqIso H H' m) :
    SeqIso (OnlineColouring.truncSeq H m) (OnlineColouring.truncSeq H' m) n := by
  classical
  obtain ⟨φ, hφ⟩ := h
  let e : Fin m ≃ {x : Fin n // (x : ℕ) < m} :=
    { toFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hmn⟩, i.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ψ : Equiv.Perm (Fin n) := Equiv.Perm.extendDomain (φ : Equiv.Perm (Fin m)) e
  have hψ₁ : ∀ x : Fin n, ∀ hx : (x : ℕ) < m, (ψ x : ℕ) = φ ⟨x, hx⟩ := by
    intro x hx
    change ((Equiv.Perm.extendDomain (φ : Equiv.Perm (Fin m)) e x : Fin n) : ℕ) = _
    rw [Equiv.Perm.extendDomain_apply_subtype _ e hx]
    rfl
  have hψ₂ : ∀ x : Fin n, ¬ (x : ℕ) < m → ψ x = x :=
    fun x hx => Equiv.Perm.extendDomain_apply_not_subtype (φ : Equiv.Perm (Fin m)) e hx
  refine ⟨ψ, fun u v => ?_⟩
  unfold OnlineColouring.truncSeq
  by_cases hv : (v : ℕ) < m
  · have hψv := hψ₁ v hv
    rw [ite_eq_left hv, hψv, ite_eq_left (φ ⟨v, hv⟩).2]
    by_cases hu : (u : ℕ) < m
    · rw [hψ₁ u hu]
      exact hφ ⟨u, hu⟩ ⟨v, hv⟩
    · rw [hψ₂ u hu]
      constructor
      · intro h; exact absurd ((mem_range.1 (hH _ h)).trans hv) hu
      · intro h; exact absurd ((mem_range.1 (hH' _ h)).trans (φ ⟨v, hv⟩).2) hu
  · rw [ite_eq_right hv, hψ₂ v hv, ite_eq_right hv]
    simp

/-! ### Triangle-freeness -/

/-- A graph in which the earliest vertex of a triangle cannot exist is triangle-free. -/
theorem cliqueFree_three_of {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (h : ∀ x y z, x < y → x < z → G.Adj x y → G.Adj x z → ¬ G.Adj y z) : G.CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  rcases lt_or_gt_of_ne hab.ne with h1 | h1 <;> rcases lt_or_gt_of_ne hac.ne with h2 | h2
  · exact h a b c h1 h2 hab hac hbc
  · exact h c a b h2 (h2.trans h1) hac.symm hbc.symm hab
  · exact h b a c h1 (h1.trans h2) hab.symm hbc hac
  · rcases lt_or_gt_of_ne hbc.ne with h3 | h3
    · exact h b a c h1 h3 hab.symm hbc hac
    · exact h c a b h2 h3 hac.symm hbc.symm hab

/-- If no vertex is an earlier neighbour of two adjacent vertices among the first `m`, the graph of
the first `m` vertices is triangle-free. -/
theorem cliqueFree_three_ofSeq {N : ℕ → Finset ℕ} (hN : ValidSeq N) {m : ℕ}
    (h : ∀ x u u', u < m → u' < m → x ∈ N u → x ∈ N u' → u ∉ N u') :
    (OnlineInput.ofSeq N hN m).graph.CliqueFree 3 := by
  apply cliqueFree_three_of
  intro x y z hxy hxz hy hz hyz
  have earlier : ∀ a b : Fin m, a < b → (OnlineInput.ofSeq N hN m).graph.Adj a b →
      (a : ℕ) ∈ N b := by
    intro a b hab hadj
    rcases OnlineInput.ofSeq_adj.1 hadj with h' | h'
    · exact h'
    · exact absurd (mem_range.1 (hN _ h')) (not_lt.2 (Fin.lt_def.1 hab).le)
  rcases lt_or_gt_of_ne hyz.ne with hlt | hlt
  · exact h x y z y.2 z.2 (earlier x y hxy hy) (earlier x z hxz hz) (earlier y z hlt hyz)
  · exact h x z y z.2 y.2 (earlier x z hxz hz) (earlier x y hxy hy) (earlier z y hlt hyz.symm)

/-- In a blow-up no vertex is an earlier neighbour of two adjacent vertices. -/
theorem notMem_of_mem_blowSeq (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ) {m : ℕ}
    (hdeg : ∀ w < m, postDeg H m w ≤ R) {x u u' : ℕ} (hu : u < m * R) (hu' : u' < m * R)
    (hx : x ∈ OnlineColouring.blowSeq R H σ u) (hx' : x ∈ OnlineColouring.blowSeq R H σ u') :
    u ∉ OnlineColouring.blowSeq R H σ u' := by
  intro huu'
  have hdiv : ∀ p < m * R, p / R < m := fun p hp =>
    Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hp (Nat.mul_comm m R))
  have e := block_eq_of_mem hH hR hσ hdeg hx hx' (hdiv u hu) (hdiv u' hu')
  obtain ⟨hw, -⟩ := (mem_blowSeq hR hσ).1 huu'
  have := mem_range.1 (hH _ hw)
  omega

theorem truncSeq_notMem {N : ℕ → Finset ℕ} {M : ℕ}
    (h : ∀ x u u', u < M → u' < M → x ∈ N u → x ∈ N u' → u ∉ N u') :
    ∀ x u u', x ∈ OnlineColouring.truncSeq N M u → x ∈ OnlineColouring.truncSeq N M u' →
      u ∉ OnlineColouring.truncSeq N M u' := by
  intro x u u' hx hx'
  unfold OnlineColouring.truncSeq at hx hx' ⊢
  by_cases hu : u < M
  · by_cases hu' : u' < M
    · rw [ite_eq_left hu] at hx
      rw [ite_eq_left hu'] at hx' ⊢
      exact h x u u' hu hu' hx hx'
    · rw [ite_eq_right hu'] at hx'
      simp at hx'
  · rw [ite_eq_right hu] at hx
    simp at hx

end OnlineColouring
