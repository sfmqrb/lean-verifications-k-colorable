module

public import OnlineColouring.Labels
public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Fintype.Sort

/-!
# Cliques and antichains

Lemma 5.1 (cliques and antichains) of the paper:

* (i) the arrival-ordered clique `K_m` has a `P`-labelling iff `m ≤ |P|`
  (`hasLabelling_clique_iff`);
* (ii) if `P` has an antichain of size `k'`, every `k'`-colourable ordered graph has a
  `P`-labelling (`hasLabelling_of_colorable`).
-/

@[expose] public section

namespace OnlineColouring

variable {P : Type*} [PartialOrder P]

/-- A labelling of a complete ordered graph is injective. -/
theorem IsLabelling.injective_of_top {V : Type*} [LinearOrder V] {f : V → P}
    (hf : IsLabelling (⊤ : SimpleGraph V) f) : Function.Injective f := by
  intro u v h
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · exact hf huv ((SimpleGraph.top_adj u v).2 hne) h.le
  · exact hf hvu ((SimpleGraph.top_adj v u).2 (Ne.symm hne)) h.symm.le

/-- A finite poset can be listed so that larger elements come first: there is a bijection
`e : Fin |P| → P` with `e s ≰ e t` whenever `s < t`.  (We take a linear extension of the dual
order and list it increasingly.) -/
theorem exists_enum_not_le [Fintype P] :
    ∃ e : Fin (Fintype.card P) → P, ∀ ⦃s t⦄, s < t → ¬ e s ≤ e t := by
  classical
  let _ : Fintype (LinearExtension Pᵒᵈ) := inferInstanceAs (Fintype Pᵒᵈ)
  let g : Fin (Fintype.card P) ≃o LinearExtension Pᵒᵈ := monoEquivOfFin _ rfl
  let toP : LinearExtension Pᵒᵈ → P := fun x => OrderDual.ofDual x
  refine ⟨fun s => toP (g s), fun s t hst hle => ?_⟩
  -- `e s ≤ e t` in `P` means `g t ≤ g s` in `Pᵒᵈ`, hence in the linear extension.
  have h₁ : OrderDual.toDual (toP (g t)) ≤ OrderDual.toDual (toP (g s)) :=
    OrderDual.toDual_le_toDual.2 hle
  have h₂ : toLinearExtension (OrderDual.toDual (toP (g t))) ≤
      toLinearExtension (OrderDual.toDual (toP (g s))) := toLinearExtension.monotone h₁
  have h₃ : g t ≤ g s := h₂
  exact absurd (g.le_iff_le.1 h₃) (not_le.2 hst)

/-- **Lemma 5.1 (i).** The arrival-ordered clique `K_m` on `Fin m` has a `P`-labelling if and
only if `m ≤ |P|`. -/
theorem hasLabelling_clique_iff [Fintype P] {m : ℕ} :
    HasLabelling (⊤ : SimpleGraph (Fin m)) P ↔ m ≤ Fintype.card P := by
  constructor
  · rintro ⟨f, hf⟩
    simpa using Fintype.card_le_of_injective f hf.injective_of_top
  · intro hm
    obtain ⟨e, he⟩ := exists_enum_not_le (P := P)
    refine ⟨fun s => e (Fin.castLE hm s), fun s t hst _ => he ?_⟩
    exact (Fin.castLE_lt_castLE_iff hm).2 hst

/-- **Lemma 5.1 (ii).** If `P` has an antichain `A` of size at least `k'`, then every
`k'`-colourable ordered graph has a `P`-labelling. -/
theorem hasLabelling_of_colorable {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {A : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P)) {k' : ℕ} (hk : k' ≤ A.card)
    (hG : G.Colorable k') : HasLabelling G P := by
  obtain ⟨c⟩ := hG
  -- an injection of the `k'` colours into the antichain
  let ι : Fin k' → P := fun i => (A.equivFin.symm (Fin.castLE hk i) : P)
  have hι : Function.Injective ι := by
    intro i j h
    have := Subtype.ext h
    simpa [Fin.ext_iff] using this
  refine ⟨fun v => ι (c v), fun u v _ hadj => ?_⟩
  have hne : ι (c u) ≠ ι (c v) := fun h => c.valid hadj (hι h)
  exact hA (A.equivFin.symm _).2 (A.equivFin.symm _).2 hne

end OnlineColouring
