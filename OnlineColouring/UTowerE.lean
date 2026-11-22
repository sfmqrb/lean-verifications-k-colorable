module

public import OnlineColouring.TowerIndex

/-!
# The uniform reservation tower with one server bijection per node

As in `TowerIndex.lean`, nodes at depth `k` (level `j - k`) are numbered `0, …, m A^k - 1` in
arrival order, the parent of `y` is `y / A`, its position among its siblings is `y % A`, and its
root is `y / A^k`.  The servers are given by

* `τ s t`: the child of the root `s` that serves the arc `v_s → v_t` (the *top server*);
* `φ s t k g i`: below the top, for the node `g` at depth `k` of the subtree of `v_t` and its child
  at position `i`, the position of the corresponding server among the children of `x_s(g)`.

So the server map from the children of `g` to the children of `x_s(g)` is `i ↦ φ s t k g i`, an
arbitrary map for every node `g`.  This is the structure of the random wiring `R_j(m)`
(Construction 8.1), where every such map is an independent uniform bijection (`UWiringE.lean`).

* `ueNb k s y`: the earlier neighbour below the root `s` of the node `y` at depth `k`;
* `ueInput_isTower`, `ueInput_colorable`: if the top servers of each root are distinct and every
  map `φ s t k g` is injective on `[A]`, then for every `d` the graph at depth `d` is a `d`-fold
  blow-up of `K_m`, and the graph at depth `j` is `kk`-colourable as soon as `m ≤ |P_j(kk)|`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

variable (A : ℕ) (τ : ℕ → ℕ → ℕ) (φ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)

/-- The position of the server of a node at depth `k + 1` (root `t`) inside the server of its
parent: the top server `τ s t` for `k = 0`; for a node `y` at depth `k + 2`, whose parent `y / A`
sits at position `(y / A) % A` inside the grandparent `y / A / A` (at depth `k`), it is
`φ s t k (y / A / A) ((y / A) % A)`. -/
def ueDig : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, s, t, _ => τ s t
  | k + 1, s, t, y => φ s t k (y / A / A) ((y / A) % A)

/-- The earlier neighbour below the root `s` of the node `y` at depth `k`. -/
def ueNb : ℕ → ℕ → ℕ → ℕ
  | 0, s, _ => s
  | k + 1, s, y => ueNb k s (y / A) * A + ueDig A τ φ k s (y / A ^ (k + 1)) y

/-- The earlier neighbours of the node `y` at depth `k`. -/
def ueSeq (k y : ℕ) : Finset ℕ := (range (y / A ^ k)).image fun s => ueNb A τ φ k s y

variable {A τ φ}

theorem ueDig_lt (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A) (k s t y : ℕ) :
    ueDig A τ φ k s t y < A := by
  cases k with
  | zero => exact hτ s t
  | succ k => exact hφ _ _ _ _ _

theorem ueNb_succ_div (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (k s y : ℕ) : ueNb A τ φ (k + 1) s y / A = ueNb A τ φ k s (y / A) := by
  rw [ueNb, Nat.mul_comm, Nat.mul_add_div hA, Nat.div_eq_of_lt (ueDig_lt hτ hφ _ _ _ _),
    Nat.add_zero]

theorem ueNb_succ_mod (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A) (k s y : ℕ) :
    ueNb A τ φ (k + 1) s y % A = ueDig A τ φ k s (y / A ^ (k + 1)) y := by
  rw [ueNb, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (ueDig_lt hτ hφ _ _ _ _)]

/-- The neighbour below `s` lies below `s`. -/
theorem ueNb_div_pow (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (k s y : ℕ) : ueNb A τ φ k s y / A ^ k = s := by
  induction k generalizing y with
  | zero => simp [ueNb]
  | succ k ih =>
    rw [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ueNb_succ_div hA hτ hφ, ih]

/-- The neighbour of `y` depends only on the parent of `y`. -/
theorem ueNb_congr {k s y y' : ℕ} (h : y / A = y' / A) :
    ueNb A τ φ (k + 1) s y = ueNb A τ φ (k + 1) s y' := by
  have hr : y / A ^ (k + 1) = y' / A ^ (k + 1) := by rw [div_pow_succ, div_pow_succ, h]
  cases k with
  | zero => simp only [ueNb, ueDig, hr]
  | succ k => simp only [ueNb, ueDig, hr, h]

/-- The neighbour below `s` of a node with root `t` only uses `τ s t` and `φ s t`. -/
theorem ueNb_congr_param {τ' : ℕ → ℕ → ℕ} {φ' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {s t : ℕ}
    (hτ : τ s t = τ' s t) (hφ : ∀ k g i, φ s t k g i = φ' s t k g i) (k : ℕ) {y : ℕ}
    (hy : y / A ^ k = t) : ueNb A τ φ k s y = ueNb A τ' φ' k s y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    have hy' : y / A / A ^ k = t := by rw [← div_pow_succ]; exact hy
    rw [ueNb, ueNb, ih hy', hy]
    congr 1
    cases k with
    | zero => exact hτ
    | succ k => simp only [ueDig, hφ]

/-- **Injectivity:** the neighbours below `s` of two nodes in the root range coincide only if the
nodes are siblings, provided the top servers of `s` are distinct and every server map is
injective. -/
theorem ueNb_inj (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m s : ℕ}
    (hinj : ∀ t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ)
    {y y' : ℕ} (hy : s < y / A ^ (k + 1)) (hym : y / A ^ (k + 1) < m)
    (hy' : s < y' / A ^ (k + 1)) (hym' : y' / A ^ (k + 1) < m)
    (h : ueNb A τ φ (k + 1) s y = ueNb A τ φ (k + 1) s y') : y / A = y' / A := by
  induction k generalizing y y' with
  | zero =>
    have hd := congrArg (· % A) h
    simp only [ueNb_succ_mod hτ hφ, ueDig] at hd
    rw [pow_one] at hy hym hy' hym' hd
    exact hinj _ _ hy hym hy' hym' hd
  | succ k ih =>
    have hdiv := congrArg (· / A) h
    simp only [ueNb_succ_div hA hτ hφ] at hdiv
    rw [div_pow_succ y] at hy hym
    rw [div_pow_succ y'] at hy' hym'
    have hpar := ih hy hym hy' hym' hdiv
    have hmod := congrArg (· % A) h
    simp only [ueNb_succ_mod hτ hφ, ueDig] at hmod
    have hroot : y / A ^ (k + 1 + 1) = y' / A ^ (k + 1 + 1) := by
      rw [div_pow_succ y, div_pow_succ y', div_pow_succ (y / A), div_pow_succ (y' / A), hpar]
    rw [hroot, hpar] at hmod
    have hm := hφinj _ _ _ _ _ _ (Nat.mod_lt _ hA) (Nat.mod_lt _ hA) hmod
    rw [← Nat.div_add_mod (y / A) A, ← Nat.div_add_mod (y' / A) A, hpar, hm]

/-- The neighbours are earlier. -/
theorem ueSeq_valid (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (k : ℕ) : ValidSeq (ueSeq A τ φ k) := by
  intro y x hx
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hx
  apply mem_range.2
  apply Nat.lt_of_div_lt_div (c := A ^ k)
  rw [ueNb_div_pow hA hτ hφ]
  exact mem_range.1 hs

theorem mem_ueSeq {k x y : ℕ} :
    x ∈ ueSeq A τ φ k y ↔ ∃ s < y / A ^ k, ueNb A τ φ k s y = x := by
  simp [ueSeq]

theorem ueSeq_zero : ueSeq A τ φ 0 = cliqueSeq := by
  funext y
  simp [ueSeq, ueNb, cliqueSeq]

/-- The ordered graph of the nodes at depth `k` (level `j - k`), on `m A^k` vertices; for `k = j`
it is the presented graph. -/
def ueInput (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A) (m k : ℕ) :
    OnlineInput (utSize A m k) :=
  OnlineInput.ofSeq (ueSeq A τ φ k) (ueSeq_valid hA hτ hφ k) (utSize A m k)

theorem mem_ueInput_nbr {hA : 0 < A} {hτ : ∀ s t, τ s t < A}
    {hφ : ∀ s t k g i, φ s t k g i < A} {m k : ℕ} {x y : Fin (utSize A m k)} :
    x ∈ (ueInput hA hτ hφ m k).nbr y ↔ (x : ℕ) ∈ ueSeq A τ φ k y :=
  OnlineInput.mem_ofSeq_nbr

/-- **The tower is an iterated blow-up of `K_m`.** If the top servers of each root are distinct and
the server maps are injective, the graph at depth `k` is a `k`-fold blow-up of `K_m`
(`IsTower m k`). -/
theorem ueInput_isTower (hA : 0 < A) (hτ : ∀ s t, τ s t < A) (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    IsTower m k (ueInput hA hτ hφ m k).toOrdGraph := by
  induction k with
  | zero =>
    have h : (ueInput hA hτ hφ m 0).toOrdGraph = OrdGraph.clique m := by
      unfold ueInput
      rw [OnlineInput.ofSeq_congr ueSeq_zero]
      exact ofSeq_cliqueSeq m
    rw [h]
    exact .clique
  | succ k ih =>
    refine .blowUp ih ⟨divBlowUp hA rfl _ _ ?_ ?_ ?_⟩
    · -- (1) edges project to edges
      intro x y hxy
      obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
      refine mem_ueInput_nbr.2 (mem_ueSeq.2 ⟨s, ?_, ?_⟩)
      · change s < y / A / A ^ k
        rwa [← div_pow_succ]
      · change ueNb A τ φ k s (y / A) = x / A
        rw [← hsx, ueNb_succ_div hA hτ hφ]
    · -- (2) the neighbours depend only on the parent
      intro x y y' hyy hxy
      obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
      refine (mem_ueInput_nbr (k := k + 1)).2 ?_
      have hr : (y : ℕ) / A ^ (k + 1) = y' / A ^ (k + 1) := by
        rw [div_pow_succ, div_pow_succ, hyy]
      exact mem_ueSeq.2 ⟨s, hr ▸ hs, (ueNb_congr hyy.symm).trans hsx⟩
    · -- (3) a vertex is a neighbour within one block only
      intro x y y' hxy hxy'
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

/-- **Colourability of the tower.** -/
theorem ueInput_colorable (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m j kk : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t')
    (hm : m ≤ Fintype.card (LabelPoset kk j)) :
    (ueInput hA hτ hφ m j).graph.Colorable kk :=
  (ueInput_isTower hA hτ hφ hφinj hinj j).colorable hm

end OnlineColouring
