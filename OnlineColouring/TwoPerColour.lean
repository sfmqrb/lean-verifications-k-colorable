module

public import OnlineColouring.Online
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lemma B.3 (two vertices per colour), for First-Fit on an input and for `χ^det`

Lemma B.3 (two vertices per colour) of Appendix B: *For `c ≥ k`, `N_k(c) ≥ 2c - k`.*  The proof
lets the algorithm play First-Fit: two singleton colour classes `{y_a}`, `{y_b}` with `a < b` are
adjacent (when `y_b` was coloured, colour `a` was on an earlier neighbour of `y_b`, which can only
be `y_a`), so the singleton classes form a clique and there are at most `k` of them; every other
class has at least two vertices.

Formal statements.

* `OnlineInput.two_mul_cost_firstFit_le`: on every `k`-colourable online input with `n` vertices,
  First-Fit (`OnlineAlg.firstFit`) uses `c` colours with `2c ≤ n + k`.
* `ChiDetAtLeast.two_mul_sub_le`: if `ChiDetAtLeast k n c` (every proper algorithm can be forced
  to `c` colours on a `k`-colourable input with `n` vertices, i.e. `N_k(c) ≤ n` by Observation
  4.3), then `2c - k ≤ n`.  In `ℕ` the subtraction truncates, so the paper's hypothesis `c ≥ k` is
  not needed.
* `two_mul_chiDet_le`: `2 χ^det_k(n) ≤ n + k` (for `k ≥ 1`).

The lemma for the number `N_k(c)` itself, as the paper states it, is `Cert.le_Nk`
(`CertLower.lean`).  Colours are `0, 1, …` here; the argument does not depend on the smallest
colour.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-- The First-Fit property of the online First-Fit algorithm: every colour below the colour of
`v` occurs on an earlier neighbour of `v`. -/
theorem OnlineInput.exists_nbr_of_lt_run_firstFit {n : ℕ} (I : OnlineInput n) (v : Fin n) {a : ℕ}
    (ha : a < I.run OnlineAlg.firstFit v) :
    ∃ u ∈ I.nbr v, I.run OnlineAlg.firstFit u = a := by
  have hmem : a ∈ nbrColours (runHist OnlineAlg.firstFit I.seq v) (I.seq v) := by
    by_contra hnot
    exact Nat.find_min _ ha hnot
  rw [nbrColours_runHist (I.seq_valid v)] at hmem
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hmem
  simp only [OnlineInput.seq, v.2, ↓reduceDIte, Finset.mem_map, Fin.valEmbedding_apply] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨u, hu, rfl⟩

/-- If every value of `f` on `s` is taken at least twice, then `f` takes at most `|s|/2` values
on `s`. -/
theorem two_mul_card_image_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (h : ∀ x ∈ s, ∃ y ∈ s, y ≠ x ∧ f y = f x) : 2 * (s.image f).card ≤ s.card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := f) (t := s.image f) fun x hx => mem_image_of_mem f hx,
    Nat.mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro b hb
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  obtain ⟨y, hy, hyx, hfy⟩ := h x hx
  exact one_lt_card.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩, y, mem_filter.2 ⟨hy, hfy⟩, hyx.symm⟩

/-- **Two vertices per colour.**  On a `k`-colourable online input with `n` vertices, First-Fit
uses `c` colours with `2c ≤ n + k`: the vertices whose colour class is a singleton form a clique
(so there are at most `k` of them), and every other colour class has at least two vertices. -/
theorem OnlineInput.two_mul_cost_firstFit_le {n k : ℕ} (I : OnlineInput n)
    (hc : I.graph.Colorable k) : 2 * I.cost OnlineAlg.firstFit ≤ n + k := by
  classical
  set f := I.run OnlineAlg.firstFit
  -- the vertices whose colour class is a singleton
  set T : Finset (Fin n) := univ.filter fun v => ∀ u, f u = f v → u = v with hT
  have hmemT : ∀ v, v ∈ T ↔ ∀ u, f u = f v → u = v := by simp [hT]
  -- they form a clique
  have hclique : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → I.graph.Adj u v := by
    have key : ∀ u ∈ T, ∀ v ∈ T, f u < f v → I.graph.Adj u v := by
      intro u hu v _ hlt
      obtain ⟨w, hw, hfw⟩ := I.exists_nbr_of_lt_run_firstFit v hlt
      have hwu : w = u := (hmemT u).1 hu w hfw
      subst hwu
      exact Or.inl hw
    intro u hu v hv huv
    rcases lt_trichotomy (f u) (f v) with h | h | h
    · exact key u hu v hv h
    · exact absurd ((hmemT v).1 hv u h) huv
    · exact (key v hv u hu h).symm
  -- so there are at most `k` of them
  have hTk : T.card ≤ k := by
    obtain ⟨C⟩ := hc
    have := card_le_card_of_injOn C (t := (univ : Finset (Fin k)))
      (fun _ _ => mem_coe.2 (mem_univ _)) fun u hu v hv huv => by
        by_contra hne
        exact C.valid (hclique u hu v hv hne) huv
    simpa using this
  -- every colour outside `T` is used at least twice outside `T`
  have hpair : 2 * ((univ \ T).image f).card ≤ (univ \ T).card := by
    apply two_mul_card_image_le
    intro v hv
    have hvT : v ∉ T := (mem_sdiff.1 hv).2
    rw [hmemT] at hvT
    push Not at hvT
    obtain ⟨u, hfu, huv⟩ := hvT
    refine ⟨u, mem_sdiff.2 ⟨mem_univ _, fun huT => huv.symm ?_⟩, huv, hfu⟩
    exact (hmemT u).1 huT v hfu.symm
  have hcost : I.cost OnlineAlg.firstFit ≤ T.card + ((univ \ T).image f).card := by
    unfold OnlineInput.cost
    calc (univ.image f).card = ((T ∪ (univ \ T)).image f).card := by
          rw [union_sdiff_of_subset (subset_univ T)]
      _ ≤ (T.image f).card + ((univ \ T).image f).card := by
          rw [image_union]; exact card_union_le _ _
      _ ≤ T.card + ((univ \ T).image f).card := by
          gcongr; exact card_image_le
  have hsplit : T.card + (univ \ T).card = n := by
    rw [Nat.add_comm, card_sdiff_add_card_eq_card (subset_univ T), card_univ, Fintype.card_fin]
  omega

/-- **Lemma B.3 (two vertices per colour)**, for the predicate `ChiDetAtLeast`.  If every proper
algorithm can be forced to use `c` colours on some `k`-colourable input with `n` vertices, then
`2c - k ≤ n`. -/
theorem ChiDetAtLeast.two_mul_sub_le {k n c : ℕ} (h : ChiDetAtLeast k n c) : 2 * c - k ≤ n := by
  obtain ⟨I, hI, hc⟩ := h OnlineAlg.firstFit OnlineAlg.firstFit_isProper
  have := I.two_mul_cost_firstFit_le hI
  omega

/-- The same bound for the online chromatic number: `2 χ^det_k(n) ≤ n + k` (for `k ≥ 1`). -/
theorem two_mul_chiDet_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : 2 * chiDet k n ≤ n + k := by
  have := ((le_chiDet_iff hk).1 (le_refl (chiDet k n))).two_mul_sub_le
  omega

end OnlineColouring
