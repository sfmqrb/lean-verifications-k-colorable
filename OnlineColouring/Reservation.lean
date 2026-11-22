module

public import Mathlib.Combinatorics.Pigeonhole

/-!
# The pigeonhole step of the reservation blow-up

The paragraph "Step 3 is possible" of the proof of Lemma 6.2 (forcing survives a blow-up): when
the block `σ(v)` of `R = (K-1)(D-1)+1` vertices of Construction 6.1 has been coloured with fewer
than `K` colours, some colour occurs on at least `D` of its vertices, so a monochromatic reserve
of size `D` can be chosen.

The online game itself is formalized in `Online.lean`, `Play.lean` and `Structure.lean`, where
`exists_large_colour_class` is used in `forcing_step`.
-/

@[expose] public section

namespace OnlineColouring

/-- **Step 3 of Construction 6.1 is possible.** If a set `s` of at least `(K-1)(D-1)+1` vertices is
coloured by `c` with fewer than `K` colours, then some colour `b` that occurs on `s` is used on at
least `D` vertices of `s`. -/
theorem exists_large_colour_class {α β : Type*} [DecidableEq β] (s : Finset α) (c : α → β)
    {K D : ℕ} (hs : (K - 1) * (D - 1) + 1 ≤ s.card) (hK : (s.image c).card < K) :
    ∃ b ∈ s.image c, D ≤ (s.filter fun x => c x = b).card := by
  have hmaps : ∀ a ∈ s, c a ∈ s.image c := fun a ha => Finset.mem_image_of_mem c ha
  have hn : (s.image c).card * (D - 1) < s.card := by
    have : (s.image c).card * (D - 1) ≤ (K - 1) * (D - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨b, hb, hlt⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hn
  exact ⟨b, hb, by omega⟩

/-- The reserve of step 3 of Construction 6.1: a monochromatic subset of the block of size
exactly `D`. -/
theorem exists_monochromatic_reserve {α β : Type*} [DecidableEq β] (s : Finset α) (c : α → β)
    {K D : ℕ} (hs : (K - 1) * (D - 1) + 1 ≤ s.card) (hK : (s.image c).card < K) :
    ∃ b : β, ∃ r ⊆ s, r.card = D ∧ ∀ x ∈ r, c x = b := by
  obtain ⟨b, -, hb⟩ := exists_large_colour_class s c hs hK
  obtain ⟨r, hr, hrD⟩ := Finset.exists_subset_card_eq hb
  refine ⟨b, r, hr.trans (Finset.filter_subset _ _), hrD, fun x hx => ?_⟩
  exact (Finset.mem_filter.1 (hr hx)).2

end OnlineColouring
