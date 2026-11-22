module

public import OnlineColouring.UTowerE
public import OnlineColouring.Phases
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Fintype.Perm

/-!
# The random wiring `R_j(m)` (Construction 8.1)

Construction 8.1: in phase `t`, for each `s < t` independently, the top server `x_s(v_t)`
is a uniformly random child of `v_s` among those that have not served, and every bijection
`σ(u) → σ(x_s(u))` below the top (for every node `u` of level `≥ 2` below `v_t`, including
`u = v_t`) is uniformly random, independently of everything else.

The randomness is a point `ω` of the finite product `EΩ m j A`.  The coordinate of the pair
`(t, s)` is `EZ A j t s`:
* a rank `r ∈ Fin (A - (t - s - 1))`: the top server is the `r`-th child of `v_s`, in increasing
  order, among the `A - (t - s - 1)` children that have not served in the phases `s+1, …, t-1`
  (`pickR`).  Every rank gives a different unused child and every unused child has a rank, so a
  uniform rank is a uniform unused child;
* a permutation `P k g ∈ Perm (Fin A)` for every depth `k ≤ j - 2` and every node `g < A^k` at that
  depth below `v_t`: the bijection from the children of that node to the children of its server.

Under the uniform distribution on `EΩ m j A`, all these coordinates are independent and uniform:
this is `R_j(m)`.  (Coordinates `(t, s)` with `s ≥ t` are not used.)

* `uInputE`: the presented input of a realization, a full `j`-level tower over `K_m`
  (`Det.uInputE_isFullTower` in `DetTower.lean`), `k`-colourable when `m ≤ |P_j(k)|`
  (`uInputE_colorable`);
* online-ness: the input of the phases `< t` depends only on the coordinates of those phases;
* `ueNb_updateE`: in the realization `update ω t X`, the earlier neighbour below `s` of a leaf of
  phase `t` is `nbOfE ω s t y (X s)`, a function of the single coordinate `X s`;
* `card_le_card_fiber_mul` (the counting behind Lemma 8.4): every eligible leaf `x` of `s` is the
  neighbour for at least a fraction `A^{-j}` of the values of that coordinate.  The exact
  statement, that the neighbour is uniform over the eligible leaves and independent for different
  `s`, is proved in `ExplUniform.lean`.

The sample space is called `EΩ`, and the declarations about it carry the suffix `E`
(`uInputE`, `uColE`, `eligE`, …).
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### The `r`-th number outside a finite set -/

/-- The `r`-th natural number (counting from `0`) that is not in `S`. -/
noncomputable def pickR (S : Finset ℕ) (r : ℕ) : ℕ := Nat.nth (fun x => x ∉ S) r

theorem infinite_notMem (S : Finset ℕ) : (Set.ofPred fun x : ℕ => x ∉ S).Infinite := by
  have h : (Set.ofPred fun x : ℕ => x ∉ S) = ((S : Set ℕ))ᶜ := by
    ext x
    simp
  rw [h]
  exact S.finite_toSet.infinite_compl

theorem pickR_notMem (S : Finset ℕ) (r : ℕ) : pickR S r ∉ S :=
  Nat.nth_mem_of_infinite (infinite_notMem S) r

theorem pickR_injective (S : Finset ℕ) : Function.Injective (pickR S) :=
  Nat.nth_injective (infinite_notMem S)

theorem count_notMem {A : ℕ} {S : Finset ℕ} (hS : S ⊆ range A) :
    Nat.count (fun x => x ∉ S) A = A - S.card := by
  rw [Nat.count_eq_card_filter_range]
  have h : (range A \ S).card = A - S.card := by rw [card_sdiff_of_subset hS, card_range]
  rw [← h]
  congr 1
  ext x
  simp

theorem pickR_lt {A : ℕ} {S : Finset ℕ} (hS : S ⊆ range A) {r : ℕ} (hr : r < A - S.card) :
    pickR S r < A :=
  Nat.nth_lt_of_lt_count (by rw [count_notMem hS]; exact hr)

/-- Every number `x < A` outside `S ⊆ [A]` is `pickR S r` for some `r < A - |S|`. -/
theorem exists_pickR_eq {A : ℕ} {S : Finset ℕ} (hS : S ⊆ range A) {x : ℕ} (hx : x ∉ S)
    (hxA : x < A) : ∃ r < A - S.card, pickR S r = x := by
  refine ⟨Nat.count (fun x => x ∉ S) x, ?_, ?_⟩
  · rw [← count_notMem hS]
    exact Nat.count_strict_mono hx hxA
  · unfold pickR
    exact Nat.nth_count hx

/-! ### The sample space -/

/-- The coordinate of the pair `(t, s)`: a rank among the unused children of `v_s`, and one
permutation of the positions `[A]` for every node at depth `k ≤ j - 2` below `v_t`. -/
abbrev EZ (A j t s : ℕ) : Type :=
  Fin (A - (t - s - 1)) × ((k : Fin (j - 1)) → Fin (A ^ (k : ℕ)) → Equiv.Perm (Fin A))

/-- The sample space of the random wiring `R_j(m)`. -/
abbrev EΩ (m j A : ℕ) : Type := (t : Fin m) → (s : Fin m) → EZ A j t s

theorem nonempty_EΩ {m j A : ℕ} (hmA : m ≤ A) : Nonempty (EΩ m j A) :=
  ⟨fun t s => (⟨0, by have := t.2; omega⟩, fun _ _ => 1)⟩

variable {m j A : ℕ}

/-- The rank coordinate of the arc `v_s → v_t`. -/
def rrE (ω : EΩ m j A) (s t : ℕ) : ℕ :=
  if h : t < m ∧ s < m then ((ω ⟨t, h.1⟩ ⟨s, h.2⟩).1 : ℕ) else 0

theorem rrE_lt (ω : EΩ m j A) {s t : ℕ} (ht : t < m) (hs : s < m) :
    rrE ω s t < A - (t - s - 1) := by
  unfold rrE
  rw [dite_eq_left ⟨ht, hs⟩]
  exact (ω ⟨t, ht⟩ ⟨s, hs⟩).1.isLt

/-- The children of the root `s` used as top servers by the phases `s+1, …, s+i`. -/
noncomputable def usedTopE (ω : EΩ m j A) (s : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | i + 1 => insert (pickR (usedTopE ω s i) (rrE ω s (s + 1 + i))) (usedTopE ω s i)

/-- The top server of the arc `v_s → v_t`: the child of rank `rrE ω s t` among the unused ones. -/
noncomputable def topCE (ω : EΩ m j A) (s t : ℕ) : ℕ :=
  pickR (usedTopE ω s (t - s - 1)) (rrE ω s t)

/-- The top server, reduced modulo `A` (it is already `< A` in the relevant range). -/
noncomputable def tauE (ω : EΩ m j A) (s t : ℕ) : ℕ := topCE ω s t % A

/-- The bijection that a coordinate assigns to the node `g` at depth `k` (identity outside the
range of the coordinate). -/
def permOf {t s : ℕ} (z : EZ A j t s) (k g : ℕ) : Equiv.Perm (Fin A) :=
  if h : k < j - 1 ∧ 0 < A then z.2 ⟨k, h.1⟩ ⟨g % A ^ k, Nat.mod_lt _ (pow_pos h.2 k)⟩ else 1

/-- A family of bijections as a server map on the positions `i < A` (and `0` elsewhere). -/
def phiOf (P : ℕ → ℕ → Equiv.Perm (Fin A)) (k g i : ℕ) : ℕ :=
  if hi : i < A then (P k g ⟨i, hi⟩ : ℕ) else 0

/-- The bijection of the arc pair `(t, s)` at the node `g` at depth `k`. -/
def permE (ω : EΩ m j A) (s t k g : ℕ) : Equiv.Perm (Fin A) :=
  if h : t < m ∧ s < m then permOf (ω ⟨t, h.1⟩ ⟨s, h.2⟩) k g else 1

/-- The server maps below the top. -/
def phiE (ω : EΩ m j A) (s t : ℕ) : ℕ → ℕ → ℕ → ℕ := phiOf (permE ω s t)

theorem phiOf_lt (hA : 0 < A) (P : ℕ → ℕ → Equiv.Perm (Fin A)) (k g i : ℕ) :
    phiOf P k g i < A := by
  unfold phiOf
  split_ifs
  · exact Fin.isLt _
  · exact hA

theorem phiOf_inj (P : ℕ → ℕ → Equiv.Perm (Fin A)) (k g : ℕ) {i i' : ℕ} (hi : i < A)
    (hi' : i' < A) (h : phiOf P k g i = phiOf P k g i') : i = i' := by
  unfold phiOf at h
  rw [dite_eq_left hi, dite_eq_left hi'] at h
  have := (P k g).injective (Fin.ext h)
  exact congrArg Fin.val this

variable (ω : EΩ m j A)

theorem usedTopE_succ (s i : ℕ) :
    usedTopE ω s (i + 1) = insert (topCE ω s (s + 1 + i)) (usedTopE ω s i) := by
  rw [usedTopE, topCE, show s + 1 + i - s - 1 = i by omega]

theorem card_usedTopE (s i : ℕ) : (usedTopE ω s i).card = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [usedTopE, card_insert_of_notMem (pickR_notMem _ _), ih]

theorem usedTopE_mono (s : ℕ) {i i' : ℕ} (h : i ≤ i') : usedTopE ω s i ⊆ usedTopE ω s i' := by
  induction i' with
  | zero => rw [Nat.le_zero.1 h]
  | succ i' ih =>
    rcases Nat.lt_or_eq_of_le h with h' | rfl
    · exact (ih (by omega)).trans (by rw [usedTopE]; exact subset_insert _ _)
    · exact subset_refl _

theorem usedTopE_subset {s : ℕ} (hs : s < m) {i : ℕ} (hi : s + i < m) :
    usedTopE ω s i ⊆ range A := by
  induction i with
  | zero => exact empty_subset _
  | succ i ih =>
    rw [usedTopE]
    refine insert_subset (mem_range.2 (pickR_lt (ih (by omega)) ?_)) (ih (by omega))
    rw [card_usedTopE]
    have := rrE_lt ω (s := s) (t := s + 1 + i) (by omega) hs
    rwa [show s + 1 + i - s - 1 = i by omega] at this

theorem topCE_notMem (s t : ℕ) : topCE ω s t ∉ usedTopE ω s (t - s - 1) := pickR_notMem _ _

theorem topCE_mem {s t : ℕ} (h : s < t) : topCE ω s t ∈ usedTopE ω s (t - s) := by
  obtain ⟨i, rfl⟩ : ∃ i, t = s + 1 + i := ⟨t - s - 1, by omega⟩
  rw [show s + 1 + i - s = i + 1 by omega, usedTopE_succ]
  exact mem_insert_self _ _

theorem topCE_lt {s t : ℕ} (hst : s < t) (ht : t < m) : topCE ω s t < A := by
  unfold topCE
  apply pickR_lt (usedTopE_subset ω (by omega : s < m) (by omega : s + (t - s - 1) < m))
  rw [card_usedTopE]
  exact rrE_lt ω ht (by omega)

theorem tauE_lt (hA : 0 < A) (s t : ℕ) : tauE ω s t < A := Nat.mod_lt _ hA

theorem tauE_eq {s t : ℕ} (hst : s < t) (ht : t < m) : tauE ω s t = topCE ω s t :=
  Nat.mod_eq_of_lt (topCE_lt ω hst ht)

/-- The top servers of a root are distinct. -/
theorem tauE_inj :
    ∀ s t t', s < t → t < m → s < t' → t' < m → tauE ω s t = tauE ω s t' → t = t' := by
  intro s t t' hst htm hst' htm' heq
  rw [tauE_eq ω hst htm, tauE_eq ω hst' htm'] at heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h₁ := topCE_mem ω hst
    have h₂ := topCE_notMem ω s t'
    rw [heq] at h₁
    exact h₂ (usedTopE_mono ω s (by omega) h₁)
  · have h₁ := topCE_mem ω hst'
    have h₂ := topCE_notMem ω s t
    rw [← heq] at h₁
    exact h₂ (usedTopE_mono ω s (by omega) h₁)

theorem phiE_lt (hA : 0 < A) : ∀ s t k g i, phiE ω s t k g i < A :=
  fun _ _ k g i => phiOf_lt hA _ k g i

theorem phiE_inj :
    ∀ s t k g i i', i < A → i' < A → phiE ω s t k g i = phiE ω s t k g i' → i = i' :=
  fun _ _ k g _ _ hi hi' h => phiOf_inj _ k g hi hi' h

/-! ### The presented input -/

/-- The presented input sequence (the leaves of the tower, phase by phase). -/
noncomputable def uSeqE (ω : EΩ m j A) : ℕ → Finset ℕ := ueSeq A (tauE ω) (phiE ω) j

/-- The presented input of the realization `ω`, on `m A^j` vertices. -/
noncomputable def uInputE (hA : 0 < A) (ω : EΩ m j A) : OnlineInput (utSize A m j) :=
  ueInput (τ := tauE ω) (φ := phiE ω) hA (tauE_lt ω hA) (phiE_lt ω hA) m j

theorem uInputE_seq (hA : 0 < A) {i : ℕ} (hi : i < utSize A m j) :
    (uInputE hA ω).seq i = uSeqE ω i :=
  OnlineInput.seq_ofSeq (hN := ueSeq_valid hA (tauE_lt ω hA) (phiE_lt ω hA) j) hi

/-- **Every realization is `k`-colourable** when `m ≤ |P_j(k)|`. -/
theorem uInputE_colorable (hA : 0 < A) {kk : ℕ}
    (hm : m ≤ Fintype.card (LabelPoset kk j)) : (uInputE hA ω).graph.Colorable kk :=
  ueInput_colorable hA (tauE_lt ω hA) (phiE_lt ω hA) (phiE_inj ω) (tauE_inj ω) hm

/-! ### Online-ness -/

/-- `ω` and `ω'` agree on the coordinates of the phases `< T`. -/
def AgreeBelowE (ω ω' : EΩ m j A) (T : ℕ) : Prop := ∀ t : Fin m, (t : ℕ) < T → ω t = ω' t

variable {ω}

theorem AgreeBelowE.symm {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) :
    AgreeBelowE ω' ω T :=
  fun t ht => (h t ht).symm

theorem rrE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) {s t : ℕ} (ht : t < T) :
    rrE ω s t = rrE ω' s t := by
  unfold rrE
  split_ifs with hst
  · rw [h ⟨t, hst.1⟩ ht]
  · rfl

theorem permE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) {s t : ℕ} (ht : t < T)
    (k g : ℕ) : permE ω s t k g = permE ω' s t k g := by
  unfold permE
  split_ifs with hst
  · rw [h ⟨t, hst.1⟩ ht]
  · rfl

theorem phiE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) {s t : ℕ} (ht : t < T)
    (k g i : ℕ) : phiE ω s t k g i = phiE ω' s t k g i := by
  simp only [phiE, phiOf, permE_congr h ht]

theorem usedTopE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) (s : ℕ) :
    ∀ i, s + i < T → usedTopE ω s i = usedTopE ω' s i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [usedTopE, usedTopE, ih (by omega), rrE_congr h (by omega)]

theorem topCE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) {s t : ℕ} (ht : t < T) :
    topCE ω s t = topCE ω' s t := by
  unfold topCE
  rw [rrE_congr h ht]
  by_cases hst : s < t
  · rw [usedTopE_congr h s _ (by omega)]
  · rw [show t - s - 1 = 0 by omega]; rfl

theorem uSeqE_congr {ω' : EΩ m j A} {T : ℕ} (h : AgreeBelowE ω ω' T) {y : ℕ}
    (hy : y / A ^ j < T) : uSeqE ω y = uSeqE ω' y := by
  unfold uSeqE ueSeq
  apply image_congr
  intro s _
  exact ueNb_congr_param (by unfold tauE; rw [topCE_congr h hy])
    (fun k g i => phiE_congr h hy k g i) j rfl

/-- The colours given by the algorithm `alg` to the presented vertices. -/
noncomputable def uColE (alg : OnlineAlg) (ω : EΩ m j A) : ℕ → ℕ := runCol alg (uSeqE ω)

/-- **The colours of the first `T` phases depend only on the coordinates of the first `T`
phases.** -/
theorem uColE_congr (alg : OnlineAlg) {ω' : EΩ m j A} {T : ℕ}
    (h : AgreeBelowE ω ω' T) {i : ℕ} (hi : i < T * A ^ j) : uColE alg ω i = uColE alg ω' i := by
  unfold uColE
  apply runCol_congr
  intro i' hi'
  apply uSeqE_congr h
  exact Nat.div_lt_of_lt_mul (by
    have := lt_of_le_of_lt hi' hi
    rwa [Nat.mul_comm] at this)

theorem agreeBelowE_update (ω : EΩ m j A) (t : Fin m) (X : (s : Fin m) → EZ A j t s) :
    AgreeBelowE ω (Function.update ω t X) t := by
  intro t' ht'
  rw [Function.update_of_ne]
  intro he
  rw [he] at ht'
  exact lt_irrefl _ ht'

/-! ### Eligible leaves and the neighbours of a leaf -/

/-- The eligible leaves of the root `s` at the start of phase `t`: those below children that have
not served yet. -/
noncomputable def eligE (ω : EΩ m j A) (s t : ℕ) : Finset ℕ :=
  (phase A j s).filter fun y => (y / A ^ (j - 1)) % A ∉ usedTopE ω s (t - s - 1)

theorem eligE_congr {ω' : EΩ m j A} {t : ℕ} (h : AgreeBelowE ω ω' t) (s : ℕ) :
    eligE ω s t = eligE ω' s t := by
  unfold eligE
  by_cases hst : s < t
  · rw [usedTopE_congr h s _ (by omega)]
  · rw [show t - s - 1 = 0 by omega]; rfl

theorem eligE_subset (s t : ℕ) : eligE ω s t ⊆ phase A j s := filter_subset _ _

/-- The neighbour below `s` of the leaf `y` of phase `t`, when the coordinate of `(t, s)` is
`z`. -/
noncomputable def nbOfE (ω : EΩ m j A) (s t y : ℕ) (z : EZ A j t s) : ℕ :=
  ueNb A (fun _ _ => pickR (usedTopE ω s (t - s - 1)) z.1 % A) (fun _ _ => phiOf (permOf z)) j s y

theorem nbOfE_div (hA : 0 < A) (ω : EΩ m j A) (s t y : ℕ) (z : EZ A j t s) :
    nbOfE ω s t y z / A ^ j = s :=
  ueNb_div_pow hA (fun _ _ => Nat.mod_lt _ hA) (fun _ _ => phiOf_lt hA _) j s y

/-- In the realization `update ω t X`, the neighbour below `s` of a leaf of phase `t` is
`nbOfE ω s t y (X s)`. -/
theorem ueNb_updateE (t : Fin m) (X : (s : Fin m) → EZ A j t s) (s : Fin m) {y : ℕ}
    (hy : y / A ^ j = t) :
    ueNb A (tauE (Function.update ω t X)) (phiE (Function.update ω t X)) j s y =
      nbOfE ω s t y (X s) := by
  apply ueNb_congr_param _ _ j hy
  · unfold tauE topCE
    have hrr : rrE (Function.update ω t X) s t = ((X s).1 : ℕ) := by
      simp [rrE, t.2, s.2]
    rw [hrr]
    congr 2
    by_cases hst : (s : ℕ) < t
    · exact usedTopE_congr (agreeBelowE_update ω t X).symm s _ (by omega)
    · rw [show (t : ℕ) - s - 1 = 0 by omega]; rfl
  · intro k g i
    have hp : permE (Function.update ω t X) s t = permOf (X s) := by
      funext k g
      simp [permE, t.2, s.2]
    simp only [phiE, hp]

variable (ω)

/-- **The neighbour is determined by the rank and by the bijections along the path.** If the
coordinate `z` gives the top child `(x / A^(j-1)) % A` and its bijections along the ancestors of
`y` send their positions to the digits of `x`, then the neighbour of `y` below `s` is `x`. -/
theorem nbOfE_eq_of_digits (hj : 1 ≤ j) {s t y x : ℕ} (z : EZ A j t s) (hxs : x / A ^ j = s)
    (htop : pickR (usedTopE ω s (t - s - 1)) z.1 % A = (x / A ^ (j - 1)) % A)
    (hlow : ∀ k, k + 2 ≤ j → phiOf (permOf z) k (y / A ^ (j - k)) ((y / A ^ (j - k - 1)) % A) =
      (x / A ^ (j - k - 2)) % A) :
    nbOfE ω s t y z = x := by
  unfold nbOfE
  have key : ∀ k, k ≤ j →
      ueNb A (fun _ _ => pickR (usedTopE ω s (t - s - 1)) z.1 % A) (fun _ _ => phiOf (permOf z))
        k s (y / A ^ (j - k)) = x / A ^ (j - k) := by
    intro k
    induction k with
    | zero => intro _; simp [ueNb, hxs]
    | succ k ih =>
      intro hk
      have e₁ : y / A ^ (j - (k + 1)) / A = y / A ^ (j - k) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, show j - (k + 1) + 1 = j - k by omega]
      have e₂ : x / A ^ (j - (k + 1)) / A = x / A ^ (j - k) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, show j - (k + 1) + 1 = j - k by omega]
      rw [ueNb, e₁, ih (by omega), ← e₂]
      conv_rhs => rw [← Nat.div_add_mod (x / A ^ (j - (k + 1))) A, Nat.mul_comm]
      congr 1
      cases k with
      | zero =>
        simp only [ueDig]
        rw [htop, show j - (0 + 1) = j - 1 by omega]
      | succ k =>
        simp only [ueDig]
        have e₄ : y / A ^ (j - (k + 1)) / A = y / A ^ (j - k) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show j - (k + 1) + 1 = j - k by omega]
        rw [e₁, e₄]
        have := hlow k (by omega)
        rw [show j - k - 1 = j - (k + 1) by omega, show j - k - 2 = j - (k + 1 + 1) by omega]
          at this
        exact this
  have := key j le_rfl
  simpa using this

/-- **The counting behind Lemma 8.4.** For `s < t < m` and every eligible leaf `x` of `s` at the
start of phase `t`, at least a fraction `A^{-j}` of the values `z` of the coordinate of `(t, s)`
make `x` the neighbour of the leaf `y` below `s`.  (The fraction is exactly
`1 / ((A - (t - s - 1)) A^(j-1))`, the same for every eligible leaf, so the neighbour is uniform:
`Expl.card_fiber_mul_card_eligE` in `ExplUniform.lean`.)

The proof is an injection `z ↦ (z', rank of z, the values of z's bijections on the path of y)`,
where `z'` is `z` corrected to hit `x`: its rank is the rank of `x`'s top child, and each bijection
on the path of `y` is composed with a swap. -/
theorem card_le_card_fiber_mul (hA : 0 < A) (hj : 1 ≤ j) {s t y x : ℕ}
    (hst : s < t) (htm : t < m) (hx : x ∈ eligE ω s t) :
    Fintype.card (EZ A j t s) ≤
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card * A ^ j := by
  classical
  have hxs : x / A ^ j = s := (mem_phase hA).1 (mem_filter.1 hx).1
  have hc₀U : (x / A ^ (j - 1)) % A ∉ usedTopE ω s (t - s - 1) := (mem_filter.1 hx).2
  have hU := usedTopE_subset ω (by omega : s < m) (by omega : s + (t - s - 1) < m)
  obtain ⟨r₀, hr₀, hpick⟩ := exists_pickR_eq hU hc₀U (Nat.mod_lt _ hA)
  rw [card_usedTopE] at hr₀
  -- the ancestors of `y` (local indices), their positions, and the digits of `x`
  let a : (k : Fin (j - 1)) → Fin (A ^ (k : ℕ)) :=
    fun k => ⟨(y / A ^ (j - k)) % A ^ (k : ℕ), Nat.mod_lt _ (pow_pos hA _)⟩
  let d : Fin (j - 1) → Fin A := fun k => ⟨(y / A ^ (j - k - 1)) % A, Nat.mod_lt _ hA⟩
  let e : Fin (j - 1) → Fin A := fun k => ⟨(x / A ^ (j - k - 2)) % A, Nat.mod_lt _ hA⟩
  -- the correction of a coordinate
  let N : EZ A j t s → EZ A j t s := fun z =>
    (⟨r₀, hr₀⟩, fun k g => if g = a k then Equiv.swap (z.2 k (a k) (d k)) (e k) * z.2 k (a k)
      else z.2 k g)
  have hN : ∀ z, nbOfE ω s t y (N z) = x := by
    intro z
    apply nbOfE_eq_of_digits ω hj (N z) hxs
    · change pickR (usedTopE ω s (t - s - 1)) r₀ % A = (x / A ^ (j - 1)) % A
      rw [hpick, Nat.mod_mod]
    · intro k hk
      have hk' : k < j - 1 := by omega
      have hdA : (y / A ^ (j - k - 1)) % A < A := Nat.mod_lt _ hA
      have hp : permOf (N z) k (y / A ^ (j - k)) =
          Equiv.swap (z.2 ⟨k, hk'⟩ (a ⟨k, hk'⟩) (d ⟨k, hk'⟩)) (e ⟨k, hk'⟩) *
            z.2 ⟨k, hk'⟩ (a ⟨k, hk'⟩) := by
        unfold permOf
        rw [dite_eq_left ⟨hk', hA⟩]
        change (if (⟨(y / A ^ (j - k)) % A ^ k, _⟩ : Fin (A ^ k)) = a ⟨k, hk'⟩ then _ else _) = _
        rw [ite_eq_left rfl]
      unfold phiOf
      rw [dite_eq_left hdA, hp, Equiv.Perm.mul_apply]
      have hdd : (⟨(y / A ^ (j - k - 1)) % A, hdA⟩ : Fin A) = d ⟨k, hk'⟩ := rfl
      rw [hdd, Equiv.swap_apply_left]
  -- the injection
  let F : EZ A j t s → {z : EZ A j t s // nbOfE ω s t y z = x} ×
      (Fin (A - (t - s - 1)) × (Fin (j - 1) → Fin A)) :=
    fun z => (⟨N z, hN z⟩, (z.1, fun k => z.2 k (a k) (d k)))
  have hFinj : Function.Injective F := by
    intro z w hzw
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hzw
    obtain ⟨hNzw, h1, h2⟩ := hzw
    refine Prod.ext h1 ?_
    funext k g
    have hk := congrFun h2 k
    have hg := congrFun (congrFun (congrArg Prod.snd hNzw) k) g
    simp only [N] at hg
    by_cases hga : g = a k
    · rw [hga] at hg ⊢
      rw [ite_eq_left rfl, ite_eq_left rfl, hk] at hg
      exact mul_left_cancel hg
    · rw [ite_eq_right hga, ite_eq_right hga] at hg
      exact hg
  have hcard := Fintype.card_le_of_injective F hFinj
  have hR : Fintype.card ({z : EZ A j t s // nbOfE ω s t y z = x} ×
      (Fin (A - (t - s - 1)) × (Fin (j - 1) → Fin A))) =
      (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card *
        ((A - (t - s - 1)) * A ^ (j - 1)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_subtype, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  calc Fintype.card (EZ A j t s)
      ≤ (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card *
          ((A - (t - s - 1)) * A ^ (j - 1)) := hcard.trans_eq hR
    _ ≤ (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card * A ^ j := by
        apply Nat.mul_le_mul_left
        calc (A - (t - s - 1)) * A ^ (j - 1) ≤ A * A ^ (j - 1) :=
              Nat.mul_le_mul_right _ (Nat.sub_le _ _)
          _ = A ^ j := by rw [← pow_succ']; congr 1; omega

/-- **Colour counting for one coordinate.** For `s < t < m`, a colour `c` and a leaf `y`, the
values `z` of the coordinate of `(t, s)` for which the neighbour of `y` below `s` has colour `c`
form at least a fraction `(# eligible leaves of s of colour c) / A^j`. -/
theorem card_mul_card_colour_le (hA : 0 < A) (hj : 1 ≤ j) (col : ℕ → ℕ)
    {s t y : ℕ} (hst : s < t) (htm : t < m) (c : ℕ) :
    Fintype.card (EZ A j t s) * ((eligE ω s t).filter fun x => col x = c).card ≤
      (univ.filter fun z : EZ A j t s => col (nbOfE ω s t y z) = c).card * A ^ j := by
  classical
  set E := (eligE ω s t).filter fun x => col x = c
  have h1 : (univ.filter fun z : EZ A j t s => nbOfE ω s t y z ∈ E) ⊆
      univ.filter fun z : EZ A j t s => col (nbOfE ω s t y z) = c := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact (mem_filter.1 hz).2
  have h2 : (univ.filter fun z : EZ A j t s => nbOfE ω s t y z ∈ E).card =
      ∑ x ∈ E, (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card := by
    rw [card_eq_sum_card_fiberwise (f := nbOfE ω s t y)
      (s := univ.filter fun z : EZ A j t s => nbOfE ω s t y z ∈ E) (t := E)
      (fun z hz => (mem_filter.1 hz).2)]
    apply sum_congr rfl
    intro x hx
    congr 1
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hx, h⟩
  calc Fintype.card (EZ A j t s) * E.card = ∑ _x ∈ E, Fintype.card (EZ A j t s) := by
        rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ x ∈ E, (univ.filter fun z : EZ A j t s => nbOfE ω s t y z = x).card * A ^ j :=
        sum_le_sum fun x hx => card_le_card_fiber_mul ω hA hj hst htm (mem_filter.1 hx).1
    _ = (univ.filter fun z : EZ A j t s => nbOfE ω s t y z ∈ E).card * A ^ j := by
        rw [h2, sum_mul]
    _ ≤ (univ.filter fun z : EZ A j t s => col (nbOfE ω s t y z) = c).card * A ^ j :=
        Nat.mul_le_mul_right _ (card_le_card h1)

end OnlineColouring
