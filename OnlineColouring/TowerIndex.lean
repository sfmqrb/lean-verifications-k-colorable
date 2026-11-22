module

public import OnlineColouring.Forcing

/-!
# Towers with `A` children per node: indexing, and a blow-up criterion

Shared arithmetic for the uniform towers of Section 8 (`UTowerE.lean`, `UWiringE.lean`).  In a
full `j`-level tower over `K_m` in which every node of positive level has exactly `A` children,
the nodes at depth `k` (level `j - k`) are numbered `0, …, m A^k - 1` in arrival order.  The
parent of the node `y` is `y / A`, its position among its siblings is `y % A`, and its root (the
top vertex above it) is `y / A^k`.

* `divBlowUp` (a blow-up criterion): let `A ≥ 1`, let `G` be an online input on `M * A` vertices
  and `Hin` one on `M` vertices.  If every edge `x → y` of `G` projects to an edge
  `x / A → y / A` of `Hin`, the earlier neighbours of `y` depend only on `y / A`, and a vertex is
  an earlier neighbour within one block only, then `G` is a blow-up of `Hin` (Definition 4.6) with
  blocks `{y | y / A = v}` (`divMap` is the block map and `divServe` the serve map).
* `utSize A m k = m A^k` is the number of nodes at depth `k` (`utSize_eq`).
* Index arithmetic: `div_pow_succ`, `root_lt`, `lt_utSize_of_root`, `div_lt_utSize`,
  `lt_of_div_lt`, `div_mul_add_of_lt`, `mod_mul_add_of_lt`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### A generic blow-up criterion -/

section DivBlowUp

variable {M M' A : ℕ}

theorem div_lt_of_lt_mul' (hM : M' = M * A) {x : ℕ} (hx : x < M') : x / A < M :=
  Nat.div_lt_of_lt_mul (by rw [hM] at hx; rwa [Nat.mul_comm] at hx)

/-- The block map `x ↦ x / A`. -/
def divMap (hM : M' = M * A) (x : Fin M') : Fin M := ⟨x / A, div_lt_of_lt_mul' hM x.2⟩

open Classical in
/-- The serve map: `x` serves the block of `y / A` if `x` is an earlier neighbour of `y`. -/
noncomputable def divServe (hM : M' = M * A) (G : OnlineInput M') (x : Fin M') : Option (Fin M) :=
  if h : ∃ y : Fin M', x ∈ G.nbr y then some (divMap hM h.choose) else none

theorem divServe_spec {hM : M' = M * A} {G : OnlineInput M'} {x : Fin M'} {v : Fin M}
    (h : divServe hM G x = some v) : ∃ y : Fin M', x ∈ G.nbr y ∧ divMap hM y = v := by
  classical
  unfold divServe at h
  split_ifs at h with hex
  cases h
  exact ⟨_, hex.choose_spec, rfl⟩

theorem divServe_of_mem {hM : M' = M * A} {G : OnlineInput M'}
    (G3 : ∀ x y y' : Fin M', x ∈ G.nbr y → x ∈ G.nbr y' → (y : ℕ) / A = y' / A)
    {x y : Fin M'} (hy : x ∈ G.nbr y) : divServe hM G x = some (divMap hM y) := by
  classical
  have hex : ∃ y : Fin M', x ∈ G.nbr y := ⟨y, hy⟩
  unfold divServe
  rw [dite_eq_left hex]
  congr 1
  exact Fin.ext (G3 _ _ _ hex.choose_spec hy)

/-- **A blow-up criterion.** Let `A ≥ 1`, let `G` be an input on `M * A` vertices and `Hin` one
on `M` vertices.  If (1) every edge `x → y` of `G` projects to an edge `x/A → y/A` of `Hin`,
(2) the earlier neighbours of `y` depend only on `y / A`, and (3) a vertex is an earlier neighbour
only within one block, then `G` is a blow-up of `Hin` with blocks `{y : y / A = v}`. -/
noncomputable def divBlowUp (hA : 0 < A) (hM : M' = M * A) (Hin : OnlineInput M)
    (G : OnlineInput M')
    (G1 : ∀ x y : Fin M', x ∈ G.nbr y → divMap hM x ∈ Hin.nbr (divMap hM y))
    (G2 : ∀ x y y' : Fin M', (y : ℕ) / A = y' / A → x ∈ G.nbr y → x ∈ G.nbr y')
    (G3 : ∀ x y y' : Fin M', x ∈ G.nbr y → x ∈ G.nbr y' → (y : ℕ) / A = y' / A) :
    BlowUp Hin.graph G.graph where
  π := divMap hM
  serve := divServe hM G
  π_surjective v := by
    refine ⟨⟨v * A, ?_⟩, Fin.ext (Nat.mul_div_cancel _ hA)⟩
    rw [hM]
    exact Nat.mul_lt_mul_of_pos_right v.2 hA
  lt_of_π_lt x y h := Fin.lt_def.2 (Nat.lt_of_div_lt_div (Fin.lt_def.1 h))
  serve_spec x v h := by
    obtain ⟨y, hy, rfl⟩ := divServe_spec h
    have := G1 x y hy
    exact ⟨Hin.nbr_lt _ _ this, Or.inl this⟩
  adj_iff x u := by
    have key : ∀ a b : Fin M', a ∈ G.nbr b ↔ a < b ∧ divServe hM G a = some (divMap hM b) := by
      intro a b
      constructor
      · intro hab
        exact ⟨G.nbr_lt _ _ hab, divServe_of_mem G3 hab⟩
      · rintro ⟨-, hs⟩
        obtain ⟨y, hy, hyb⟩ := divServe_spec hs
        exact G2 a y b (congrArg Fin.val hyb) hy
    rw [OnlineInput.graph_adj, key, key]

end DivBlowUp

/-! ### The number of nodes at each depth -/

variable (A : ℕ)

/-- The number of nodes at depth `k`: `m A^k`. -/
def utSize (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => utSize m k * A

theorem utSize_eq (m k : ℕ) : utSize A m k = m * A ^ k := by
  induction k with
  | zero => simp [utSize]
  | succ k ih => rw [utSize, ih, pow_succ, Nat.mul_assoc]

variable {A}

/-! ### Index arithmetic -/

theorem div_pow_succ (y k : ℕ) : y / A ^ (k + 1) = y / A / A ^ k := by
  rw [pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]

theorem root_lt {m k y : ℕ} (hy : y < utSize A m k) : y / A ^ k < m := by
  rw [utSize_eq] at hy
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hy)

theorem lt_utSize_of_root (hA : 0 < A) {m k y : ℕ} (h : y / A ^ k < m) : y < utSize A m k := by
  rw [utSize_eq]
  exact (Nat.div_lt_iff_lt_mul (pow_pos hA k)).1 h

theorem div_lt_utSize {m k y : ℕ} (hy : y < utSize A m (k + 1)) : y / A < utSize A m k :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hy)

theorem lt_of_div_lt {j A : ℕ} (hA : 0 < A) {x t : ℕ} (h : x / A ^ j < t) : x < t * A ^ j :=
  (Nat.div_lt_iff_lt_mul (pow_pos hA j)).1 h

theorem div_mul_add_of_lt {a r A : ℕ} (hr : r < A) : (a * A + r) / A = a := by
  have hA : 0 < A := lt_of_le_of_lt (Nat.zero_le r) hr
  rw [Nat.mul_comm, Nat.mul_add_div hA, Nat.div_eq_of_lt hr, Nat.add_zero]

theorem mod_mul_add_of_lt {a r A : ℕ} (hr : r < A) : (a * A + r) % A = r := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

end OnlineColouring
