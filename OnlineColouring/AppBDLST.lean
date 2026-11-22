module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Nat.Log

/-!
# The algorithm of Lovász, Saks and Trotter for bipartite graphs (used in Theorem D.5)

Proof of Theorem D.5: *colour `u` by … the colour that the algorithm of Lovász, Saks and Trotter
gives `u` inside its group … it is bipartite and receives at most `τ := 2 ⌊log₂ N⌋ + 1`
colours.*

The algorithm colours a bipartite graph online: a new vertex `v` receives the least colour that
does not occur on the opposite side of its connected component in the graph presented so far.
The opposite side consists of the earlier vertices joined to `v` by a walk of odd length.

This file proves the bound in a static form.  The vertices are natural numbers in arrival order,
`G` is the final graph, `restrictLE G v` is the graph presented when `v` arrives, and
`OddReach G v w` says that `w` is on the opposite side of the component of `v` at that time.
`IsLSTColouring G S ℓ` says that `ℓ` is the colouring that the algorithm produces on the vertex
set `S` (colours `0, 1, …`).

* `two_pow_le_card_of_isLSTColouring`: if `G` is bipartite, a vertex with colour `ℓ v` lies in a
  component with at least `2^⌈ℓ v / 2⌉` vertices.
* `lst_colour_le`: hence `ℓ v ≤ 2 ⌊log₂ |S|⌋`, so at most `2 log₂ |S| + 1` colours are used.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-- The graph `G` restricted to the vertices `≤ v`: the graph presented when `v` arrives. -/
def restrictLE (G : SimpleGraph ℕ) (v : ℕ) : SimpleGraph ℕ where
  Adj a b := a ≤ v ∧ b ≤ v ∧ G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.2.2⟩

theorem restrictLE_mono (G : SimpleGraph ℕ) {v w : ℕ} (h : v ≤ w) :
    restrictLE G v ≤ restrictLE G w :=
  fun _ _ hab => ⟨hab.1.trans h, hab.2.1.trans h, hab.2.2⟩

/-- `w` is joined to `v` by a walk of odd length in the graph presented when `v` arrives. -/
def OddReach (G : SimpleGraph ℕ) (v w : ℕ) : Prop :=
  ∃ p : (restrictLE G v).Walk v w, Odd p.length

/-- `ℓ` is the colouring of the vertex set `S` produced by the algorithm of Lovász, Saks and
Trotter: the colour of `v` is the least colour that does not occur on an earlier vertex joined to
`v` by a walk of odd length. -/
def IsLSTColouring (G : SimpleGraph ℕ) (S : Finset ℕ) (ℓ : ℕ → ℕ) : Prop :=
  ∀ v ∈ S, (∀ k < ℓ v, ∃ w ∈ S, w < v ∧ OddReach G v w ∧ ℓ w = k) ∧
    ∀ w ∈ S, w < v → OddReach G v w → ℓ w ≠ ℓ v

section Bound

variable {G : SimpleGraph ℕ} (χ : G.Coloring Bool)

/-- The colouring `χ` on the restricted graph. -/
def restrictColoring (v : ℕ) : (restrictLE G v).Coloring Bool :=
  SimpleGraph.Coloring.mk χ fun h => χ.valid h.2.2

theorem OddReach.ne {v w : ℕ} (h : OddReach G v w) : χ v ≠ χ w := by
  obtain ⟨p, hp⟩ := h
  have := ((restrictColoring χ v).odd_length_iff_not_congr p).1 hp
  change (¬ χ v = true ↔ χ w = true) at this
  intro e
  rw [e] at this
  exact (not_iff_self) this

theorem oddReach_of_reachable {v w : ℕ} (h : (restrictLE G v).Reachable v w) (hne : χ v ≠ χ w) :
    OddReach G v w := by
  obtain ⟨p⟩ := h
  refine ⟨p, ((restrictColoring χ v).odd_length_iff_not_congr p).2 ?_⟩
  change (¬ χ v = true ↔ χ w = true)
  cases hv : χ v <;> cases hw : χ w <;> simp_all

theorem OddReach.reachable {v w : ℕ} (h : OddReach G v w) : (restrictLE G v).Reachable v w :=
  h.elim fun p _ => ⟨p⟩

open scoped Classical in
/-- The component of `v` in the graph presented when `v` arrives, inside `S`. -/
noncomputable def compAt (G : SimpleGraph ℕ) (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  S.filter fun w => (restrictLE G v).Reachable v w

theorem mem_compAt {S : Finset ℕ} {v w : ℕ} :
    w ∈ compAt G S v ↔ w ∈ S ∧ (restrictLE G v).Reachable v w := by
  classical
  simp [compAt]

theorem compAt_subset {S : Finset ℕ} {v w : ℕ} (hwv : w ≤ v) (hw : w ∈ compAt G S v) :
    compAt G S w ⊆ compAt G S v := by
  intro x hx
  rw [mem_compAt] at hx hw ⊢
  exact ⟨hx.1, hw.2.trans (hx.2.mono (restrictLE_mono G hwv))⟩

/-- **The Lovász–Saks–Trotter bound.**  If `G` is bipartite, a vertex with colour `ℓ v` lies in a
component with at least `2^⌈ℓ v / 2⌉` vertices. -/
theorem two_pow_le_card_of_isLSTColouring (χ : G.Coloring Bool) {S : Finset ℕ} {ℓ : ℕ → ℕ}
    (hℓ : IsLSTColouring G S ℓ) :
    ∀ k v, v ∈ S → ℓ v = k → 2 ^ ((k + 1) / 2) ≤ (compAt G S v).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro v hv hk
  have hvC : v ∈ compAt G S v := mem_compAt.2 ⟨hv, SimpleGraph.Reachable.refl _⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact card_pos.2 ⟨v, hvC⟩
    · have hk1 : k = 1 := by omega
      subst hk1
      obtain ⟨w, hwS, hwv, hodd, -⟩ := (hℓ v hv).1 0 (by omega)
      have hwC : w ∈ compAt G S v := mem_compAt.2 ⟨hwS, hodd.reachable⟩
      exact one_lt_card.2 ⟨v, hvC, w, hwC, hwv.ne'⟩
  · obtain ⟨u₁, hu₁S, hu₁v, hodd₁, hℓ₁⟩ := (hℓ v hv).1 (k - 1) (by omega)
    obtain ⟨u₂, hu₂S, hu₂v, hodd₂, hℓ₂⟩ := (hℓ v hv).1 (k - 2) (by omega)
    obtain ⟨u₃, hu₃S, hu₃u₁, hodd₃, hℓ₃⟩ := (hℓ u₁ hu₁S).1 (k - 2) (by omega)
    have hχ1 := hodd₁.ne χ
    have hχ2 := hodd₂.ne χ
    have hχ3 := hodd₃.ne χ
    have hχ23 : χ u₂ ≠ χ u₃ := by
      cases h1 : χ v <;> cases h2 : χ u₁ <;> cases h3 : χ u₂ <;> cases h4 : χ u₃ <;> simp_all
    have hu₂C : u₂ ∈ compAt G S v := mem_compAt.2 ⟨hu₂S, hodd₂.reachable⟩
    have hu₃C : u₃ ∈ compAt G S v := mem_compAt.2 ⟨hu₃S, hodd₁.reachable.trans
      (hodd₃.reachable.mono (restrictLE_mono G hu₁v.le))⟩
    have hdisj : Disjoint (compAt G S u₂) (compAt G S u₃) := by
      refine disjoint_left.2 fun x hx2 hx3 => ?_
      rw [mem_compAt] at hx2 hx3
      rcases lt_trichotomy u₂ u₃ with hlt | heq | hgt
      · have hr : (restrictLE G u₃).Reachable u₃ u₂ :=
          hx3.2.trans (hx2.2.mono (restrictLE_mono G hlt.le)).symm
        exact (hℓ u₃ hu₃S).2 u₂ hu₂S hlt (oddReach_of_reachable χ hr hχ23.symm)
          (hℓ₂.trans hℓ₃.symm)
      · exact hχ23 (heq ▸ rfl)
      · have hr : (restrictLE G u₂).Reachable u₂ u₃ :=
          hx2.2.trans (hx3.2.mono (restrictLE_mono G hgt.le)).symm
        exact (hℓ u₂ hu₂S).2 u₃ hu₃S hgt (oddReach_of_reachable χ hr hχ23)
          (hℓ₃.trans hℓ₂.symm)
    have h2 := ih (k - 2) (by omega) u₂ hu₂S hℓ₂
    have h3 := ih (k - 2) (by omega) u₃ hu₃S hℓ₃
    have hsub : compAt G S u₂ ∪ compAt G S u₃ ⊆ compAt G S v :=
      union_subset (compAt_subset hu₂v.le hu₂C) (compAt_subset (hu₃u₁.trans hu₁v).le hu₃C)
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at hcard
    have e : (k + 1) / 2 = (k - 2 + 1) / 2 + 1 := by omega
    rw [e, pow_succ]
    omega

/-- The algorithm of Lovász, Saks and Trotter uses the colours `0, …, 2 ⌊log₂ n⌋` only on a
bipartite graph with `n` vertices: at most `2 log₂ n + 1` colours. -/
theorem lst_colour_le (χ : G.Coloring Bool) {S : Finset ℕ} {ℓ : ℕ → ℕ}
    (hℓ : IsLSTColouring G S ℓ) {v : ℕ} (hv : v ∈ S) : ℓ v ≤ 2 * Nat.log 2 S.card := by
  have h1 := two_pow_le_card_of_isLSTColouring χ hℓ (ℓ v) v hv rfl
  have h2 : (compAt G S v).card ≤ S.card := by
    classical
    exact card_le_card (filter_subset _ _)
  have h3 := Nat.le_log_of_pow_le Nat.one_lt_two (h1.trans h2)
  omega

end Bound

end OnlineColouring.AppBD
