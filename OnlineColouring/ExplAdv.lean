module

public import OnlineColouring.DetTower
public import OnlineColouring.RjmGraph

/-!
# Theorem 8.5 (ii) by the paper's proof: the explicit adaptive adversary

Theorem 8.5 (ii) and its proof (Section 8.3): *There is a deterministic adaptive
adversary, every play of which is a uniform tower over `K_m` with `j` levels, that forces every
deterministic online algorithm to use at least `⌈X_m⌉` colours.*  Proof in the paper: *at the
start of phase `t` the adversary knows the history and can compute `H_t` for every legal wiring
of phase `t`, since `H_t` depends only on the wiring and on the colours of earlier phases.  Given
the earlier phases, the random wiring of phase `t` is uniform over the legal wirings of phase
`t`, and `E[H_t | history] ≤ 1/4` by the proof of (i), so some legal wiring has `H_t ≤ 1/4`.  The
adversary plays the first such wiring in a fixed order.  Then (8.1) gives
`(3m+1)/4 ≤ C(1+b) + m/4` in every play, so `C ≥ X_m`, and `C` is an integer.*

`DetTower.lean` proves the statement through determinacy.  This file follows the paper's proof
and constructs the adversary as an explicit `Adversary` object `Expl.adv m j`.

## The construction

The legal wirings of phase `t` are given by the values `X : EW m j A t` of the coordinate `ω t`
of a point `ω : EΩ m j A` of the sample space of `R_j(m)` (`UWiringE.lean`): for every `s < t`, a
rank among the unused children of `v_s` and a bijection for every node of level `≥ 2` below `v_t`,
including `v_t` (the components with `s ≥ t` are not used).

* `uMC`, `qMC`, `HMC`: the quantities `u_c(t)`, `q_t(c)`, `H_t` of the analysis, written as
  functions of the colours `col : ℕ → ℕ` of the presented vertices instead of an algorithm;
  `HME_eq_HMC : HME b alg ω t = HMC b (uColE alg ω) ω t` holds by definition.
* `HMC_congr`: **`H_t` depends only on the wirings of the phases `≤ t` and on the colours of the
  phases `< t`.**
* `firstSat P d`: the first element of a finite type, in the fixed order `Fintype.equivFin`, that
  satisfies `P` (`firstSat_spec`, `firstSat_le`, `firstSat_unique`), and `d` if there is none.
* `Good b θ col ω t X`: the wiring `X` of phase `t` has `H_t ≤ θ`, given the wirings `ω` of the
  earlier phases and the colours `col`.  `exists_good`: if `b ≥ 1` and `m e^{-b} ≤ θ`, a good
  wiring exists for all colours and earlier wirings, because the mean of `H_t` over the wirings
  of phase `t` is at most `m e^{-b}` (`sum_HME_update_le`, which is
  `E[H_t | history] ≤ m e^{-b}`).
* `build ω₀ b θ col T`: the wirings of the phases `< T` chosen by the adversary when the colours
  are `col`: phase by phase, the first good wiring.  It only uses the colours of the phases
  `< T - 1` (`build_congr`).
* `advOf ω₀ b θ`: the adversary.  At a history `h` with `p = |h| < m A^j` presented vertices it
  presents the vertex `p` with the earlier neighbours it has in the tower whose wirings of the
  phases `≤ p / A^j` are `build … (colours of h) (p / A^j + 1)`; after `m A^j` vertices it stops.
  `advOf_move_take`: its move depends only on the history before the current phase and on `p`,
  that is, the wiring of a phase is chosen when the phase starts.
* `Expl.adv m j = advOf (baseW m j) (ln 4m) (1/4)` for `A = 2m`.

## Results

* `hist_advOf`, `stopsAt_advOf_iff`: every play against an algorithm `alg` presents, vertex by
  vertex, the uniform tower `uSeqE ω` of one wiring `ω = playW … alg`, in full, and then stops.
* `playW_apply`, `playW_le`: for every phase `t`, the wiring `ω t` is the first wiring `X` of
  phase `t` in the fixed order with `H_t ≤ θ` (and `ω₀ t` if there is none), where
  `H_t = HME b alg (update ω t X) t` is computed with the wirings of the earlier phases and the
  colours given so far.
* `HME_playW_le`: if every phase has a good wiring, `H_t ≤ θ` in every phase of every play.
* `advW_apply`, `advW_le`, `HME_advW_le`: the same for `adv m j`, whose realized wiring against
  `alg` is `advW m j alg`.
* `uniformBound_le_numColsE`: `C ≥ X_m` in every play against a proper algorithm (inequality
  (8.1) with `∑ H_t ≤ m/4`).
* **`adv_presents`** (Theorem 8.5 (ii)): `Det.Presents (adv m j) (Set.range (uInputE hA))
  ⌈uniformBound m⌉₊`, and `uniform_tower_adversary` with the consequences spelled out: the
  adversary forces `⌈X_m⌉` colours, every play has exactly `m (2m)^j` vertices, and the final graph
  of every play is the presented graph of a wiring of `R_j(m)`, in its arrival order: a `j`-fold
  reservation blow-up of `K_m` with all blocks of size `2m` (`Rjm.IsResTower`), isomorphic to
  `G_j(m)`, and `k`-colourable whenever `m ≤ |P_j(k)|`.

The statement of Theorem 8.5 (ii) is the same as in `DetTower.lean`; here the adversary is the
paper's.  "Deterministic online algorithm" means a proper one, as everywhere in the library; the
play itself (`hist_advOf`, `playW_apply`, `HME_playW_le`) is described for every algorithm.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset

variable {m j A : ℕ}

/-! ### The quantities of the analysis as functions of the colours -/

/-- `u_c(t)`: the weight of the eligible vertices of colour `c` at the start of phase `t`, for the
colours `col`. -/
noncomputable def uMC (col : ℕ → ℕ) (ω : EΩ m j A) (c t : ℕ) : ℝ :=
  ∑ s ∈ range t, (((eligE ω s t).filter fun y => col y = c).card : ℝ) / (A ^ j : ℕ)

/-- `q_t(c)`: the fraction of the vertices of phase `t` without an earlier neighbour of colour
`c`, for the colours `col`. -/
noncomputable def qMC (col : ℕ → ℕ) (ω : EΩ m j A) (c t : ℕ) : ℝ :=
  (((phase A j t).filter fun y =>
    ∀ s < t, col (ueNb A (tauE ω) (phiE ω) j s y) ≠ c).card : ℝ) / (A ^ j : ℕ)

/-- `H_t`: the sum of `q_t(c)` over the colours `c` used before phase `t` with `u_c(t) ≥ b`, for
the colours `col`. -/
noncomputable def HMC (b : ℝ) (col : ℕ → ℕ) (ω : EΩ m j A) (t : ℕ) : ℝ :=
  ∑ c ∈ ((range (t * A ^ j)).image col).filter (fun c => b ≤ uMC col ω c t), qMC col ω c t

/-- The `H_t` of a play of `alg` is the `H_t` of its colours. -/
theorem HME_eq_HMC (b : ℝ) (alg : OnlineAlg) (ω : EΩ m j A) (t : ℕ) :
    HME b alg ω t = HMC b (uColE alg ω) ω t := rfl

theorem uMC_congr {col col' : ℕ → ℕ} {ω ω' : EΩ m j A} {t : ℕ} (hA : 0 < A)
    (hω : AgreeBelowE ω ω' t) (hcol : ∀ i < t * A ^ j, col i = col' i) (c : ℕ) :
    uMC col ω c t = uMC col' ω' c t := by
  unfold uMC
  apply sum_congr rfl
  intro s hs
  rw [eligE_congr hω s]
  congr 3
  apply filter_congr
  intro y hy
  rw [hcol y (lt_of_div_lt hA (by
    rw [(mem_phase hA).1 (eligE_subset (ω := ω') s t hy)]; exact mem_range.1 hs))]

theorem qMC_congr {col col' : ℕ → ℕ} {ω ω' : EΩ m j A} {t : ℕ} (hA : 0 < A)
    (hω : AgreeBelowE ω ω' (t + 1)) (hcol : ∀ i < t * A ^ j, col i = col' i) (c : ℕ) :
    qMC col ω c t = qMC col' ω' c t := by
  unfold qMC
  congr 3
  apply filter_congr
  intro y hy
  have hyt : y / A ^ j = t := (mem_phase hA).1 hy
  have hnb : ∀ s, ueNb A (tauE ω) (phiE ω) j s y = ueNb A (tauE ω') (phiE ω') j s y := by
    intro s
    exact ueNb_congr_param (by unfold tauE; rw [topCE_congr hω (Nat.lt_succ_self t)])
      (fun k g i => phiE_congr hω (Nat.lt_succ_self t) k g i) j hyt
  apply forall₂_congr
  intro s hs
  rw [hnb s, hcol _ (lt_of_div_lt hA (by
    rw [ueNb_div_pow hA (tauE_lt ω' hA) (phiE_lt ω' hA)]; exact hs))]

/-- **`H_t` depends only on the wirings of the phases `≤ t` and on the colours of the phases
`< t`.** -/
theorem HMC_congr {b : ℝ} {col col' : ℕ → ℕ} {ω ω' : EΩ m j A} {t : ℕ} (hA : 0 < A)
    (hω : AgreeBelowE ω ω' (t + 1)) (hcol : ∀ i < t * A ^ j, col i = col' i) :
    HMC b col ω t = HMC b col' ω' t := by
  have hω' : AgreeBelowE ω ω' t := fun s hs => hω s (Nat.lt_succ_of_lt hs)
  have himg : (range (t * A ^ j)).image col = (range (t * A ^ j)).image col' :=
    image_congr fun i hi => hcol i (mem_range.1 hi)
  unfold HMC
  rw [himg]
  simp only [uMC_congr hA hω' hcol, qMC_congr hA hω hcol]

/-! ### The first element with a property, in a fixed order -/

open Classical in
/-- The first element of the finite type `α`, in the fixed order given by the enumeration
`Fintype.equivFin α`, that satisfies `P`; the element `d` if no element satisfies `P`. -/
noncomputable def firstSat {α : Type*} [Fintype α] (P : α → Prop) (d : α) : α :=
  if h : ∃ n : ℕ, ∃ x : α, P x ∧ (Fintype.equivFin α x : ℕ) = n then (Nat.find_spec h).choose
  else d

theorem firstSat_spec {α : Type*} [Fintype α] {P : α → Prop} (d : α) (h : ∃ x, P x) :
    P (firstSat P d) := by
  classical
  obtain ⟨x, hx⟩ := h
  have h' : ∃ n : ℕ, ∃ x : α, P x ∧ (Fintype.equivFin α x : ℕ) = n := ⟨_, x, hx, rfl⟩
  unfold firstSat
  rw [dite_eq_left h']
  exact (Nat.find_spec h').choose_spec.1

/-- `firstSat P d` comes first, in the fixed order, among the elements that satisfy `P`. -/
theorem firstSat_le {α : Type*} [Fintype α] {P : α → Prop} (d : α) {y : α} (hy : P y) :
    Fintype.equivFin α (firstSat P d) ≤ Fintype.equivFin α y := by
  classical
  have h' : ∃ n : ℕ, ∃ x : α, P x ∧ (Fintype.equivFin α x : ℕ) = n := ⟨_, y, hy, rfl⟩
  unfold firstSat
  rw [dite_eq_left h', Fin.le_def, (Nat.find_spec h').choose_spec.2]
  exact Nat.find_min' h' ⟨y, hy, rfl⟩

/-- `firstSat P d` is the only element that satisfies `P` and comes first among the elements that
satisfy `P`. -/
theorem firstSat_unique {α : Type*} [Fintype α] {P : α → Prop} (d : α) {x : α} (hx : P x)
    (hmin : ∀ y, P y → Fintype.equivFin α x ≤ Fintype.equivFin α y) : firstSat P d = x :=
  (Fintype.equivFin α).injective
    (le_antisymm (firstSat_le d hx) (hmin _ (firstSat_spec d ⟨x, hx⟩)))

theorem firstSat_congr {α : Type*} [Fintype α] {P Q : α → Prop} (d : α) (h : ∀ x, P x ↔ Q x) :
    firstSat P d = firstSat Q d := by
  have hPQ : P = Q := funext fun x => propext (h x)
  rw [hPQ]

/-! ### The wirings chosen by the adversary -/

/-- The legal wirings of the phase `t`, given by the values of the coordinate `ω t` of a point
`ω : EΩ m j A` (the components with `s ≥ t` are not used). -/
abbrev EW (m j A : ℕ) (t : Fin m) : Type := (s : Fin m) → EZ A j t s

/-- The wiring `X` of phase `t` is *good*: `H_t ≤ θ`, for the wirings `ω` of the earlier phases
and the colours `col` (only the colours of the earlier phases matter, `HMC_congr`). -/
def Good (b θ : ℝ) (col : ℕ → ℕ) (ω : EΩ m j A) (t : Fin m) (X : EW m j A t) : Prop :=
  HMC b col (Function.update ω t X) t ≤ θ

/-- The algorithm that gives the `i`-th presented vertex the colour `col i`, whatever it sees.
It is used only to apply `sum_HME_update_le` to arbitrary colours. -/
def colAlg (col : ℕ → ℕ) : OnlineAlg := ⟨fun h _ => col h.length⟩

theorem uColE_colAlg (col : ℕ → ℕ) (ω : EΩ m j A) : uColE (colAlg col) ω = col := by
  funext i
  simp [uColE, runCol, colAlg]

/-- **A good wiring exists.** Let `b ≥ 1`.  For all colours and all wirings of the earlier phases,
the mean of `H_t` over the wirings of phase `t` is at most `m e^{-b}`
(`E[H_t | history] ≤ m e^{-b}`), so some wiring of phase `t` has `H_t ≤ θ` whenever
`m e^{-b} ≤ θ`. -/
theorem exists_good (hA : 0 < A) (hj : 1 ≤ j) {b θ : ℝ} (hb : 1 ≤ b)
    (hθ : (m : ℝ) * Real.exp (-b) ≤ θ) (col : ℕ → ℕ) (ω : EΩ m j A) (t : Fin m) :
    ∃ X : EW m j A t, Good b θ col ω t X := by
  by_contra hcon
  push Not at hcon
  have hne : Nonempty (EW m j A t) := ⟨ω t⟩
  have hsum := sum_HME_update_le hA hj (colAlg col) ω t hb
  have hlt : ∑ _X : EW m j A t, θ <
      ∑ X : EW m j A t, HME b (colAlg col) (Function.update ω t X) t := by
    apply sum_lt_sum_of_nonempty univ_nonempty
    intro X _
    rw [HME_eq_HMC, uColE_colAlg]
    exact not_le.1 (hcon X)
  rw [sum_const, card_univ, nsmul_eq_mul] at hlt
  have hpos : (0 : ℝ) ≤ (Fintype.card (EW m j A t) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hθ hpos
  linarith

/-- The wirings of the phases `< T` chosen by the adversary for the colours `col`: starting from
the base wiring `ω₀`, the coordinate of each phase `t < T` is replaced, in increasing order of
`t`, by the first good wiring of phase `t` (and left as in `ω₀` if there is none, which does not
happen under the hypotheses of `exists_good`). -/
noncomputable def build (ω₀ : EΩ m j A) (b θ : ℝ) (col : ℕ → ℕ) : ℕ → EΩ m j A
  | 0 => ω₀
  | T + 1 =>
    if hT : T < m then
      Function.update (build ω₀ b θ col T) ⟨T, hT⟩
        (firstSat (Good b θ col (build ω₀ b θ col T) ⟨T, hT⟩) (ω₀ ⟨T, hT⟩))
    else build ω₀ b θ col T

section Build

variable (ω₀ : EΩ m j A) (b θ : ℝ) (col : ℕ → ℕ)

theorem build_succ_of_lt {T : ℕ} (hT : T < m) :
    build ω₀ b θ col (T + 1) = Function.update (build ω₀ b θ col T) ⟨T, hT⟩
      (firstSat (Good b θ col (build ω₀ b θ col T) ⟨T, hT⟩) (ω₀ ⟨T, hT⟩)) := by
  rw [build, dite_eq_left hT]

theorem build_succ_of_not_lt {T : ℕ} (hT : ¬ T < m) :
    build ω₀ b θ col (T + 1) = build ω₀ b θ col T := by
  rw [build, dite_eq_right hT]

theorem build_agree_succ (T : ℕ) :
    AgreeBelowE (build ω₀ b θ col T) (build ω₀ b θ col (T + 1)) T := by
  intro t ht
  by_cases hT : T < m
  · rw [build_succ_of_lt ω₀ b θ col hT, Function.update_of_ne]
    intro he
    rw [he] at ht
    exact lt_irrefl _ ht
  · rw [build_succ_of_not_lt ω₀ b θ col hT]

/-- Later phases do not change the wirings of earlier phases. -/
theorem build_agree {T T' : ℕ} (h : T ≤ T') :
    AgreeBelowE (build ω₀ b θ col T) (build ω₀ b θ col T') T := by
  induction T', h using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ T' hTT' ih =>
    intro t ht
    rw [ih t ht]
    exact build_agree_succ ω₀ b θ col T' t (lt_of_lt_of_le ht hTT')

variable {col}

/-- **The wirings of the phases `< T` are determined by the colours of the phases `< T - 1`:** the
wiring of a phase is chosen from the history before that phase. -/
theorem build_congr (hA : 0 < A) {col' : ℕ → ℕ} :
    ∀ T, (∀ i < (T - 1) * A ^ j, col i = col' i) →
      build ω₀ b θ col T = build ω₀ b θ col' T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
    intro h
    rw [Nat.add_sub_cancel] at h
    have ih' := ih fun i hi =>
      h i (lt_of_lt_of_le hi (Nat.mul_le_mul_right _ (Nat.sub_le T 1)))
    by_cases hT : T < m
    · rw [build_succ_of_lt ω₀ b θ col hT, build_succ_of_lt ω₀ b θ col' hT, ih']
      congr 1
      apply firstSat_congr
      intro X
      unfold Good
      rw [HMC_congr hA (fun _ _ => rfl) h]
    · rw [build_succ_of_not_lt ω₀ b θ col hT, build_succ_of_not_lt ω₀ b θ col' hT, ih']

variable (col)

/-- The wiring chosen for the phase `T` is good. -/
theorem HMC_build_le (hgood : ∀ (ω : EΩ m j A) (t : Fin m), ∃ X, Good b θ col ω t X) {T : ℕ}
    (hT : T < m) : HMC b col (build ω₀ b θ col (T + 1)) T ≤ θ := by
  rw [build_succ_of_lt ω₀ b θ col hT]
  exact firstSat_spec _ (hgood _ ⟨T, hT⟩)

end Build

/-! ### The adversary -/

/-- **The explicit adaptive adversary** (proof of Theorem 8.5 (ii)), for the heavy-colour
threshold `b` and the bound `θ` on `H_t`.  Given the history `h` with `p = |h|` presented
vertices: if `p < m A^j`, it presents the vertex `p` of the uniform tower whose wirings of the
phases `≤ p / A^j` are the first good ones for the colours of `h` (`build`); otherwise it stops. -/
noncomputable def advOf (ω₀ : EΩ m j A) (b θ : ℝ) : Adversary :=
  ⟨fun h => if h.length < m * A ^ j then
      some (uSeqE (build ω₀ b θ (colourAt h) (h.length / A ^ j + 1)) h.length)
    else none⟩

section Play

variable (ω₀ : EΩ m j A) (b θ : ℝ)

theorem advOf_move_of_lt {h : History} (hl : h.length < m * A ^ j) :
    (advOf ω₀ b θ).move h =
      some (uSeqE (build ω₀ b θ (colourAt h) (h.length / A ^ j + 1)) h.length) := by
  change (if h.length < m * A ^ j then _ else none) = _
  rw [ite_eq_left hl]

theorem advOf_move_of_le {h : History} (hl : m * A ^ j ≤ h.length) :
    (advOf ω₀ b θ).move h = none := by
  change (if h.length < m * A ^ j then _ else none) = _
  rw [ite_eq_right (not_lt.2 hl)]

theorem colourAt_of_prefix {h h' : History} (hp : h <+: h') {i : ℕ} (hi : i < h.length) :
    colourAt h i = colourAt h' i := by
  rw [colourAt_eq_getElem hi, colourAt_eq_getElem (lt_of_lt_of_le hi hp.length_le),
    hp.getElem hi]

theorem colourAt_take {h : History} {q i : ℕ} (hi : i < q) (hq : q ≤ h.length) :
    colourAt (h.take q) i = colourAt h i :=
  colourAt_of_prefix (List.take_prefix q h) (by rw [List.length_take]; omega)

/-- **The wiring of a phase is chosen at the start of the phase.** The move of the adversary at a
history `h` depends only on the number `p = |h|` of presented vertices and on the history before
the current phase `p / A^j`. -/
theorem advOf_move_take (hA : 0 < A) {h : History} (hl : h.length < m * A ^ j) :
    (advOf ω₀ b θ).move h = some (uSeqE (build ω₀ b θ
      (colourAt (h.take (h.length / A ^ j * A ^ j))) (h.length / A ^ j + 1)) h.length) := by
  rw [advOf_move_of_lt ω₀ b θ hl]
  congr 2
  apply build_congr ω₀ b θ hA
  intro i hi
  rw [Nat.add_sub_cancel] at hi
  exact (colourAt_take hi (Nat.div_mul_le_self _ _)).symm

/-- The wiring that the adversary plays against the algorithm `alg`: the one it has built from the
colours of the complete play. -/
noncomputable def playW (alg : OnlineAlg) : EΩ m j A :=
  build ω₀ b θ (colourAt ((advOf ω₀ b θ).hist alg (m * A ^ j))) m

theorem hist_advOf_of_le (hA : 0 < A) (alg : OnlineAlg) :
    ∀ p ≤ m * A ^ j,
      (advOf ω₀ b θ).hist alg p = runHist alg (uSeqE (playW ω₀ b θ alg)) p := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
    intro hp
    have hp' : p < m * A ^ j := hp
    have ih' := ih hp'.le
    have hlen : ((advOf ω₀ b θ).hist alg p).length = p := by rw [ih', length_runHist]
    have ht : p / A ^ j < m := (Nat.div_lt_iff_lt_mul (pow_pos hA j)).2 hp'
    have hset : uSeqE (build ω₀ b θ (colourAt ((advOf ω₀ b θ).hist alg p)) (p / A ^ j + 1)) p =
        uSeqE (playW ω₀ b θ alg) p := by
      refine uSeqE_congr ?_ (Nat.lt_succ_self _)
      have h1 : build ω₀ b θ (colourAt ((advOf ω₀ b θ).hist alg p)) (p / A ^ j + 1) =
          build ω₀ b θ (colourAt ((advOf ω₀ b θ).hist alg (m * A ^ j))) (p / A ^ j + 1) := by
        apply build_congr ω₀ b θ hA
        intro i hi
        rw [Nat.add_sub_cancel] at hi
        exact colourAt_of_prefix (Det.hist_prefix _ alg hp'.le)
          (by rw [hlen]; exact lt_of_lt_of_le hi (Nat.div_mul_le_self p _))
      rw [h1]
      exact build_agree ω₀ b θ _ ht
    have hmove : (advOf ω₀ b θ).move ((advOf ω₀ b θ).hist alg p) =
        some (uSeqE (playW ω₀ b θ alg) p) := by
      rw [advOf_move_of_lt ω₀ b θ (by rw [hlen]; exact hp'), hlen, hset]
    rw [Det.hist_succ_of_some hmove, ih', runHist_succ]
    rfl

/-- **Every play presents a uniform tower.** The history of the play against `alg` after `p`
rounds is the run of `alg` on the first `min p (m A^j)` vertices of the uniform tower with the
wiring `playW … alg`. -/
theorem hist_advOf (hA : 0 < A) (alg : OnlineAlg) (p : ℕ) :
    (advOf ω₀ b θ).hist alg p =
      runHist alg (uSeqE (playW ω₀ b θ alg)) (min p (m * A ^ j)) := by
  rcases Nat.le_total p (m * A ^ j) with hp | hp
  · rw [min_eq_left hp]
    exact hist_advOf_of_le ω₀ b θ hA alg p hp
  · rw [min_eq_right hp]
    have hfin := hist_advOf_of_le ω₀ b θ hA alg (m * A ^ j) le_rfl
    have hstop : (advOf ω₀ b θ).StopsAt alg (m * A ^ j) :=
      advOf_move_of_le ω₀ b θ (by rw [hfin, length_runHist])
    rw [Det.hist_eq_of_stopsAt hstop p hp]
    exact hfin

/-- The adversary stops exactly after `m A^j` rounds. -/
theorem stopsAt_advOf_iff (hA : 0 < A) (alg : OnlineAlg) (p : ℕ) :
    (advOf ω₀ b θ).StopsAt alg p ↔ m * A ^ j ≤ p := by
  have hlen : ((advOf ω₀ b θ).hist alg p).length = min p (m * A ^ j) := by
    rw [hist_advOf ω₀ b θ hA, length_runHist]
  constructor
  · intro hs
    by_contra hlt
    have hlt' : p < m * A ^ j := not_le.1 hlt
    have hmove := advOf_move_of_lt ω₀ b θ (h := (advOf ω₀ b θ).hist alg p)
      (by rw [hlen, min_eq_left hlt'.le]; exact hlt')
    have hs' : (advOf ω₀ b θ).move ((advOf ω₀ b θ).hist alg p) = none := hs
    rw [hmove] at hs'
    exact Option.some_ne_none _ hs'
  · intro hp
    exact advOf_move_of_le ω₀ b θ (by rw [hlen, min_eq_right hp])

/-- The colours in the complete play are the colours that `alg` gives on the uniform tower with
the wiring `playW … alg`. -/
theorem colourAt_hist (hA : 0 < A) (alg : OnlineAlg) {i : ℕ} (hi : i < m * A ^ j) :
    colourAt ((advOf ω₀ b θ).hist alg (m * A ^ j)) i = uColE alg (playW ω₀ b θ alg) i := by
  rw [hist_advOf_of_le ω₀ b θ hA alg (m * A ^ j) le_rfl]
  exact colourAt_runHist hi

/-- **The rule of the adversary, in terms of the play.** In the play against `alg`, with realized
wiring `ω = playW … alg`, the wiring `ω t` of every phase `t` is the first wiring `X` of phase
`t`, in the fixed order, with `H_t ≤ θ` (and `ω₀ t` if there is none), where
`H_t = HME b alg (update ω t X) t` is the value of `H_t` if phase `t` is wired by `X` after the
earlier phases of the play. -/
theorem playW_apply (hA : 0 < A) (alg : OnlineAlg) (t : Fin m) :
    playW ω₀ b θ alg t =
      firstSat (fun X : EW m j A t =>
        HME b alg (Function.update (playW ω₀ b θ alg) t X) t ≤ θ) (ω₀ t) := by
  set col := colourAt ((advOf ω₀ b θ).hist alg (m * A ^ j)) with hcol
  have h1 : playW ω₀ b θ alg t = build ω₀ b θ col ((t : ℕ) + 1) t :=
    (build_agree ω₀ b θ col (Nat.succ_le_of_lt t.2) t (Nat.lt_succ_self _)).symm
  rw [h1, build_succ_of_lt ω₀ b θ col t.2, Function.update_self]
  apply firstSat_congr
  intro X
  unfold Good
  rw [HME_eq_HMC]
  have hagree : AgreeBelowE (Function.update (build ω₀ b θ col t) ⟨t, t.2⟩ X)
      (Function.update (playW ω₀ b θ alg) t X) ((t : ℕ) + 1) := by
    intro t' ht'
    by_cases he : t' = t
    · subst he
      rw [Function.update_self, Function.update_self]
    · have hne : t' ≠ (⟨t, t.2⟩ : Fin m) := he
      rw [Function.update_of_ne hne, Function.update_of_ne he]
      refine build_agree ω₀ b θ col t.2.le t' ?_
      have : (t' : ℕ) ≠ t := fun h => he (Fin.ext h)
      omega
  rw [HMC_congr hA hagree fun i hi => ?_]
  exact (colourAt_hist ω₀ b θ hA alg (lt_of_lt_of_le hi (Nat.mul_le_mul_right _ t.2.le))).trans
    (uColE_update alg (playW ω₀ b θ alg) t X hi).symm

/-- The wiring of phase `t` comes first, in the fixed order, among the wirings of phase `t` with
`H_t ≤ θ`. -/
theorem playW_le (hA : 0 < A) (alg : OnlineAlg) (t : Fin m) {X : EW m j A t}
    (hX : HME b alg (Function.update (playW ω₀ b θ alg) t X) t ≤ θ) :
    Fintype.equivFin (EW m j A t) (playW ω₀ b θ alg t) ≤ Fintype.equivFin (EW m j A t) X := by
  rw [playW_apply ω₀ b θ hA alg t]
  exact firstSat_le _ hX

/-- **In every play, `H_t ≤ θ` in every phase** (when good wirings exist). -/
theorem HME_playW_le (hA : 0 < A)
    (hgood : ∀ (col : ℕ → ℕ) (ω : EΩ m j A) (t : Fin m), ∃ X, Good b θ col ω t X)
    (alg : OnlineAlg) {t : ℕ} (ht : t < m) : HME b alg (playW ω₀ b θ alg) t ≤ θ := by
  set col := colourAt ((advOf ω₀ b θ).hist alg (m * A ^ j)) with hcol
  have h1 : HME b alg (playW ω₀ b θ alg) t = HMC b col (build ω₀ b θ col (t + 1)) t := by
    rw [HME_eq_HMC]
    refine HMC_congr hA (build_agree ω₀ b θ col (Nat.succ_le_of_lt ht)).symm fun i hi => ?_
    exact (colourAt_hist ω₀ b θ hA alg
      (lt_of_lt_of_le hi (Nat.mul_le_mul_right _ ht.le))).symm
  rw [h1]
  exact HMC_build_le ω₀ b θ col (hgood col) ht

end Play

/-! ### Theorem 8.5 (ii) -/

/-- **Inequality (8.1) along the play.** For `A = 2m`, a threshold `b ≥ 1` and `θ ≥ m e^{-b}`, in
the play of the adversary against a proper algorithm, `(3m+1)/4 ≤ C (b + 1) + m θ`, where `C` is
the number of colours used. -/
theorem perPlay_playW (hm : 1 ≤ m) (hj : 1 ≤ j) {b θ : ℝ} (hb : 1 ≤ b)
    (hθ : (m : ℝ) * Real.exp (-b) ≤ θ) (ω₀ : EΩ m j (2 * m)) {alg : OnlineAlg}
    (halg : alg.IsProper) :
    ((3 * m + 1) / 4 : ℝ) ≤ numColsE alg (playW ω₀ b θ alg) * (b + 1) + m * θ := by
  have hA : 0 < 2 * m := by omega
  have h := perPlay_boundE hm hj halg (lt_of_lt_of_le one_pos hb) (playW ω₀ b θ alg)
  have hH : ∑ t ∈ range m, HME b alg (playW ω₀ b θ alg) t ≤ ∑ _t ∈ range m, θ :=
    sum_le_sum fun t ht => HME_playW_le ω₀ b θ hA
      (fun col ω t => exists_good hA hj hb hθ col ω t) alg (mem_range.1 ht)
  rw [sum_const, card_range, nsmul_eq_mul] at hH
  linarith

/-- The base wiring: rank `0` and identity bijections everywhere.  It only serves as the default
value in the definition of the adversary; for `j ≥ 1` and `m ≥ 2` the default is not used, because
every phase has a good wiring (`exists_good`). -/
def baseW (m j : ℕ) : EΩ m j (2 * m) :=
  fun t s => (⟨0, by have := t.2; omega⟩, fun _ _ => 1)

/-- **The adversary of Theorem 8.5 (ii)**: at the start of each phase it plays the first wiring of
that phase, in a fixed order, with `H_t ≤ 1/4`, where heavy means `u_c(t) ≥ ln 4m`. -/
noncomputable def adv (m j : ℕ) : Adversary := advOf (baseW m j) (Real.log (4 * m)) (1 / 4)

/-- The wiring that `adv m j` plays against `alg`. -/
noncomputable def advW (m j : ℕ) (alg : OnlineAlg) : EΩ m j (2 * m) :=
  playW (baseW m j) (Real.log (4 * m)) (1 / 4) alg

/-- **`H_t ≤ 1/4` in every phase of every play** of `adv m j`. -/
theorem HME_advW_le (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg) {t : ℕ} (ht : t < m) :
    HME (Real.log (4 * m)) alg (advW m j alg) t ≤ 1 / 4 :=
  HME_playW_le _ _ _ (by omega)
    (fun col ω t => exists_good (by omega) hj (one_le_log_four_mul hm)
      (mul_exp_neg_log (by omega)).le col ω t) alg ht

/-- **The rule of `adv m j`.** In the play against `alg`, with realized wiring `ω = advW m j alg`,
the wiring `ω t` of every phase `t` is the first wiring `X` of phase `t`, in the fixed order, with
`H_t ≤ 1/4` (and `baseW m j t` if there is none), where `H_t` is computed for the wirings of the
earlier phases of the play, the wiring `X` of phase `t`, and the colours that `alg` has given
before phase `t`. -/
theorem advW_apply (hm : 1 ≤ m) (alg : OnlineAlg) (t : Fin m) :
    advW m j alg t = firstSat (fun X : EW m j (2 * m) t =>
      HME (Real.log (4 * m)) alg (Function.update (advW m j alg) t X) t ≤ 1 / 4)
        (baseW m j t) :=
  playW_apply _ _ _ (by omega) alg t

/-- The wiring of phase `t` comes first, in the fixed order, among the wirings of phase `t` with
`H_t ≤ 1/4`. -/
theorem advW_le (hm : 1 ≤ m) (alg : OnlineAlg) (t : Fin m) {X : EW m j (2 * m) t}
    (hX : HME (Real.log (4 * m)) alg (Function.update (advW m j alg) t X) t ≤ 1 / 4) :
    Fintype.equivFin (EW m j (2 * m) t) (advW m j alg t) ≤
      Fintype.equivFin (EW m j (2 * m) t) X :=
  playW_le _ _ _ (by omega) alg t hX

/-- **`C ≥ X_m` in every play** of `adv m j` against a proper algorithm. -/
theorem uniformBound_le_numColsE (hm : 2 ≤ m) (hj : 1 ≤ j) {alg : OnlineAlg}
    (halg : alg.IsProper) : uniformBound m ≤ numColsE alg (advW m j alg) := by
  have hb : 1 ≤ Real.log (4 * m) := one_le_log_four_mul hm
  have h := perPlay_playW (by omega) hj hb (mul_exp_neg_log (by omega)).le (baseW m j) halg
  unfold uniformBound
  rw [div_le_iff₀ (by linarith)]
  change _ ≤ (numColsE alg (advW m j alg) : ℝ) * (Real.log (4 * m) + 1) + m * (1 / 4) at h
  linarith

/-- **Theorem 8.5 (ii), with the paper's adversary.**  For `j ≥ 1` and `m ≥ 2`, the adversary
`adv m j` presents, against every proper deterministic algorithm, the uniform tower of a wiring
`ω` of `R_j(m)` in full (the history of the play is the run of the algorithm on `uInputE ω`) and
then stops, and the algorithm uses at least `⌈X_m⌉` colours. -/
theorem adv_presents (hj : 1 ≤ j) (hm : 2 ≤ m) (hA : 0 < 2 * m) :
    Det.Presents (adv m j) (Set.range (uInputE (m := m) (j := j) hA)) ⌈uniformBound m⌉₊ := by
  intro alg halg
  refine ⟨uInputE hA (advW m j alg), ⟨_, rfl⟩, ?_, fun p => ⟨?_, ?_⟩⟩
  · rw [numColsE_eq_cost]
    exact Nat.ceil_le.2 (uniformBound_le_numColsE hm hj halg)
  · refine (hist_advOf _ _ _ hA alg p).trans ?_
    rw [← utSize_eq]
    exact (runHist_congr fun i hi =>
      uInputE_seq (advW m j alg) hA (lt_of_lt_of_le hi (min_le_right _ _))).symm
  · rw [utSize_eq]
    exact stopsAt_advOf_iff _ _ _ hA alg p

/-- **Theorem 8.5 (ii)** (`thm:T` (ii)), with everything spelled out.  For `j ≥ 1` and `m ≥ 2`
the explicit adversary `adv m j`
* forces every proper deterministic online algorithm to use at least `⌈X_m⌉` colours;
* presents at most `m (2m)^j` vertices in every play;
* in every play, presents a uniform tower over `K_m` with `j` levels: there is a wiring `ω` of
  `R_j(m)` such that the history after `p` rounds is the run of the algorithm on the first
  `min p (m (2m)^j)` vertices of the tower `uSeqE ω`, and `H_t ≤ 1/4` in every phase;
* lands in the `j`-fold reservation blow-ups of `K_m` with all blocks of size `2m`, in the graphs
  isomorphic to `G_j(m)`, and in the `k`-colourable graphs whenever `m ≤ |P_j(k)|`. -/
theorem uniform_tower_adversary (hj : 1 ≤ j) (hm : 2 ≤ m) :
    (adv m j).Forces ⌈uniformBound m⌉₊ ∧ (adv m j).SizeLE (m * (2 * m) ^ j) ∧
      (∀ alg : OnlineAlg, ∃ ω : EΩ m j (2 * m),
        (∀ p, (adv m j).hist alg p = runHist alg (uSeqE ω) (min p (m * (2 * m) ^ j))) ∧
        ∀ t < m, HME (Real.log (4 * m)) alg ω t ≤ 1 / 4) ∧
      ((adv m j).LandsIn fun n G => Rjm.IsResTower m (2 * m) j ⟨Fin n, G⟩) ∧
      ((adv m j).LandsIn fun n G =>
        ∃ e : n = m * (2 * m) ^ j, Nonempty (G ≃g (Rjm.Gjm j m).comap (Fin.cast e))) ∧
      ∀ k, m ≤ Fintype.card (LabelPoset k j) → (adv m j).LandsIn fun _ G => G.Colorable k := by
  have hA : 0 < 2 * m := by omega
  have hadv := adv_presents hj hm hA
  refine ⟨hadv.forces, ?_, fun alg => ⟨advW m j alg, fun p => hist_advOf _ _ _ hA alg p,
    fun t ht => HME_advW_le hm hj alg ht⟩, ?_, ?_, ?_⟩
  · rw [← utSize_eq]
    exact hadv.sizeLE
  · refine hadv.landsIn (C := fun n G => Rjm.IsResTower m (2 * m) j ⟨Fin n, G⟩) ?_
    rintro _ ⟨ω, rfl⟩
    exact Rjm.uInputE_isResTower hA ω
  · refine hadv.landsIn (C := fun n G =>
      ∃ e : n = m * (2 * m) ^ j, Nonempty (G ≃g (Rjm.Gjm j m).comap (Fin.cast e))) ?_
    rintro _ ⟨ω, rfl⟩
    obtain ⟨e⟩ := Rjm.uInputE_iso_Gjm hA ω
    refine ⟨utSize_eq (2 * m) m j, ⟨e.trans ?_⟩⟩
    exact (SimpleGraph.Iso.comap (finCongr (utSize_eq (2 * m) m j)) (Rjm.Gjm j m)).symm
  · intro k hk
    refine hadv.landsIn (C := fun _ G => G.Colorable k) ?_
    rintro _ ⟨ω, rfl⟩
    exact uInputE_colorable ω hA hk

end Expl

end OnlineColouring
