module

public import OnlineColouring.AppBDMatching
public import OnlineColouring.AdvBasic

/-!
# The flow adversary: one level with minimal blocks (Theorem D.2 and Lemma D.3), combinatorial part

Appendix D.2 ("One level with minimal blocks").  The clique `K_m` is blown up
once; the block of `v_t` has `b_t ≥ max(1, m - t)` vertices; when the block of `v_t` starts, the
adversary picks one vertex of each earlier block that has not served yet to serve `v_t`.

Indexing.  Blocks and phases are numbered `0, …, m-1` here (the paper's `v_t` is block `t - 1`),
and the vertices are the positions `0, 1, …` in arrival order: block `t` is the interval
`blk b t = [start b t, start b (t+1))`.  The window of phase `t` is `m - t` (the paper's
`W_{t+1}`).

The flow.  The paper's matrix `Y_t` satisfies `Y_t(s, c) ≤ a_s(c)`, the number of unused vertices
of colour `c` in block `s`.  We represent `Y_t` by a set `R` of unused vertices: `Y_t(s, c)` is the
number of vertices of `R` in block `s` with colour `c`.  Row sums, column sums, tightness and
`|Y_t|` become cardinalities, a matching `M_t` is a subset of `R` with at most one vertex in each
block and of each colour, and `Y_t - M_t` is `R \ M_t`.

Step (a).  The matching `M_t` is a set `M ⊆ R` with `IsMatching`: it covers every tight row and
every tight column and has at most average size.  Its existence is `exists_matching`
(`AppBDMatching.lean`), which is proved from the Birkhoff–von Neumann theorem where the paper
uses Kőnig's edge-colouring theorem.  The server of a block is chosen as in the paper
(`IsServer`): the matched vertex if the block is matched, and otherwise an unused vertex outside
the flow.

Step (b).  As in the paper, after the algorithm has coloured `σ(v_t)` the adversary keeps the
rows of `Y_t - M_t` and adds a row for `t` that is maximal subject to `Y_{t+1}(t, c) ≤ a_t(c)`
and to all row and column sums being at most the next window `W_{t+1}`.  The new row is a set
`Z` of vertices of block `t` with `IsFill`: it has at most `W_{t+1}` elements, it keeps all
column sums at most `W_{t+1}`, and it is maximal, that is, it is full or every colour of a vertex
of block `t` outside `Z` is tight.  The flow after the phase is `(R \ M) ∪ Z` (`nextState`).

Everything in this file is stated for an arbitrary colouring `col` of the positions; the
adversary object and the play are in `AppBDOneLevel.lean`.

* `state m b col t`: the pair (served vertices, flow) before phase `t`.
* `Inv`, `inv_state`: the feasibility invariant (steps "(a) is possible" and
  "`Y' := Y_t - M_t` is feasible").
* `phi0`, `phi0_gain`: **Lemma D.3**, with the phases numbered from `0` and for an arbitrary
  colouring that is proper at the block (`ProperAt`).  In the paper's numbering, for the play
  against a proper algorithm, the lemma is `phi_gain` (`AppBDOneLevel.lean`).
* `colours_ge`: the counting argument of the proof of **Theorem D.2**.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-! ### Blocks -/

/-- The first position of block `t`. -/
def start (b : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ range t, b s

/-- The positions of block `t`. -/
def blk (b : ℕ → ℕ) (t : ℕ) : Finset ℕ := Ico (start b t) (start b (t + 1))

/-- The block that contains the position `x` (for `x < start b m`). -/
def blockOf (b : ℕ → ℕ) (m x : ℕ) : ℕ := ((range m).filter fun s => start b (s + 1) ≤ x).card

theorem start_succ (b : ℕ → ℕ) (t : ℕ) : start b (t + 1) = start b t + b t :=
  sum_range_succ _ _

theorem start_mono (b : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) : start b s ≤ start b t :=
  sum_le_sum_of_subset (range_mono h)

theorem card_blk (b : ℕ → ℕ) (t : ℕ) : (blk b t).card = b t := by
  rw [blk, Nat.card_Ico, start_succ]
  omega

theorem mem_blk {b : ℕ → ℕ} {t x : ℕ} : x ∈ blk b t ↔ start b t ≤ x ∧ x < start b (t + 1) :=
  mem_Ico

theorem lt_of_mem_blk {b : ℕ → ℕ} {s t x : ℕ} (hx : x ∈ blk b s) (hst : s < t) :
    x < start b t :=
  (mem_blk.1 hx).2.trans_le (start_mono b hst)

theorem blockOf_of_mem {b : ℕ → ℕ} {m t x : ℕ} (ht : t < m) (hx : x ∈ blk b t) :
    blockOf b m x = t := by
  have : ((range m).filter fun s => start b (s + 1) ≤ x) = range t := by
    ext s
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨-, hs⟩
      by_contra hst
      have := start_mono b (show t + 1 ≤ s + 1 by omega)
      have := (mem_blk.1 hx).2
      omega
    · intro hs
      have := start_mono b (show s + 1 ≤ t by omega)
      have := (mem_blk.1 hx).1
      exact ⟨by omega, by omega⟩
  rw [blockOf, this, card_range]

theorem exists_mem_blk {b : ℕ → ℕ} {m x : ℕ} (hx : x < start b m) : ∃ t < m, x ∈ blk b t := by
  induction m with
  | zero => simp [start] at hx
  | succ m ih =>
    rcases Nat.lt_or_ge x (start b m) with h | h
    · obtain ⟨t, ht, hxt⟩ := ih h
      exact ⟨t, by omega, hxt⟩
    · exact ⟨m, by omega, mem_blk.2 ⟨h, hx⟩⟩

theorem mem_blk_blockOf {b : ℕ → ℕ} {m x : ℕ} (hx : x < start b m) :
    x ∈ blk b (blockOf b m x) ∧ blockOf b m x < m := by
  obtain ⟨t, ht, hxt⟩ := exists_mem_blk hx
  rw [blockOf_of_mem ht hxt]
  exact ⟨hxt, ht⟩

theorem blockOf_lt {b : ℕ → ℕ} {m t x : ℕ} (ht : t ≤ m) (hx : x < start b t) :
    blockOf b m x < t := by
  obtain ⟨hmem, -⟩ := mem_blk_blockOf (hx.trans_le (start_mono b ht))
  by_contra h
  have := start_mono b (not_lt.1 h)
  have := (mem_blk.1 hmem).1
  omega

/-! ### One phase of the adversary -/

section Phase

variable (m : ℕ) (b : ℕ → ℕ) (col : ℕ → ℕ)

/-- Step (a): `M` is a matching in the flow `R` (at most one vertex in each block and of each
colour) that covers every tight row and every tight column for the window `W`, and has at most
average size, `|M| ≤ |R| / W`. -/
def IsMatching (R : Finset ℕ) (W : ℕ) (M : Finset ℕ) : Prop :=
  M ⊆ R ∧ Set.InjOn (blockOf b m) M ∧ Set.InjOn col M ∧
    (∀ s, (R.filter fun x => blockOf b m x = s).card = W → ∃ x ∈ M, blockOf b m x = s) ∧
    (∀ c, (R.filter fun x => col x = c).card = W → ∃ x ∈ M, col x = c) ∧
    W * M.card ≤ R.card

/-- Step (a): `x` may serve from block `s`.  It is an unused vertex of block `s`; if `M` matches
block `s`, it is the matched vertex, and otherwise it is a vertex outside the flow `R` (a vertex
of a colour `c` with `a_s(c) > Y(s, c)`). -/
def IsServer (used R M : Finset ℕ) (s x : ℕ) : Prop :=
  x ∈ blk b s ∧ x ∉ used ∧ (x ∈ M ∨ (x ∉ R ∧ ∀ y ∈ M, blockOf b m y ≠ s))

/-- Step (b): `Z` is the new row for block `t`, added to the rows `R'` of `Y_t - M_t`.  It
consists of at most `W'` vertices of block `t`, keeps all column sums at most `W'`, and is
maximal: it is full, or every colour of a vertex of block `t` outside `Z` is tight. -/
def IsFill (R' : Finset ℕ) (W' t : ℕ) (Z : Finset ℕ) : Prop :=
  Z ⊆ blk b t ∧ Z.card ≤ W' ∧ (∀ c, ((R' ∪ Z).filter fun x => col x = c).card ≤ W') ∧
    (Z.card = W' ∨
      ∀ x ∈ blk b t, x ∉ Z → ((R' ∪ Z).filter fun y => col y = col x).card = W')

/-- The state of the adversary before a phase: the vertices that have served, and the flow. -/
structure FlowState where
  /-- The vertices that have served. -/
  used : Finset ℕ
  /-- The flow `Y_t`, as a set of unused vertices. -/
  R : Finset ℕ

/-- The matching `M_t` played in phase `t`. -/
noncomputable def matchingOf (σ : FlowState) (t : ℕ) : Finset ℕ :=
  Classical.epsilon (IsMatching m b col σ.R (m - t))

/-- The vertex of block `s` that serves block `t`. -/
noncomputable def serverOf (σ : FlowState) (t s : ℕ) : ℕ :=
  Classical.epsilon (IsServer m b σ.used σ.R (matchingOf m b col σ t) s)

/-- The servers of block `t`: the common set of earlier neighbours of its vertices. -/
noncomputable def serversOf (σ : FlowState) (t : ℕ) : Finset ℕ :=
  (range t).image (serverOf m b col σ t)

/-- The new row of the flow, chosen after block `t` has been coloured. -/
noncomputable def fillOf (σ : FlowState) (t : ℕ) : Finset ℕ :=
  Classical.epsilon (IsFill b col (σ.R \ matchingOf m b col σ t) (m - (t + 1)) t)

/-- The state after phase `t`. -/
noncomputable def nextState (σ : FlowState) (t : ℕ) : FlowState :=
  ⟨σ.used ∪ serversOf m b col σ t, (σ.R \ matchingOf m b col σ t) ∪ fillOf m b col σ t⟩

/-- The state before phase `t`. -/
noncomputable def state : ℕ → FlowState
  | 0 => ⟨∅, ∅⟩
  | t + 1 => nextState m b col (state t) t

/-- The feasibility invariant before phase `t`, for the window `m - t`: the flow consists of
unused vertices of earlier blocks, all row and column sums are at most the window, and every
earlier block still has at least `m - t` unused vertices. -/
structure Inv (t : ℕ) (σ : FlowState) : Prop where
  used_sub : σ.used ⊆ range (start b t)
  R_sub : σ.R ⊆ range (start b t)
  disj : Disjoint σ.R σ.used
  row : ∀ s, (σ.R.filter fun x => blockOf b m x = s).card ≤ m - t
  colm : ∀ c, (σ.R.filter fun x => col x = c).card ≤ m - t
  free : ∀ s < t, m - t ≤ (blk b s \ σ.used).card

variable {m b col}

theorem Inv.isMatching {t : ℕ} {σ : FlowState} (h : Inv m b col t σ) (ht : t < m) :
    IsMatching m b col σ.R (m - t) (matchingOf m b col σ t) :=
  Classical.epsilon_spec
    (exists_matching σ.R (blockOf b m) col (by omega : 0 < m - t) h.row h.colm)

theorem Inv.isServer {t s : ℕ} {σ : FlowState} (h : Inv m b col t σ) (ht : t < m)
    (hs : s < t) :
    IsServer m b σ.used σ.R (matchingOf m b col σ t) s (serverOf m b col σ t s) := by
  apply Classical.epsilon_spec
  obtain ⟨hMR, -, -, hrow, -, -⟩ := h.isMatching ht
  by_cases hM : ∃ y ∈ matchingOf m b col σ t, blockOf b m y = s
  · obtain ⟨y, hy, hys⟩ := hM
    have hyR := hMR hy
    have hylt : y < start b m :=
      (mem_range.1 (h.R_sub hyR)).trans_le (start_mono b ht.le)
    refine ⟨y, ?_, fun hu => disjoint_left.1 h.disj hyR hu, Or.inl hy⟩
    rw [← hys]
    exact (mem_blk_blockOf hylt).1
  · have hlt : (σ.R.filter fun x => blockOf b m x = s).card < (blk b s \ σ.used).card := by
      refine lt_of_lt_of_le (lt_of_le_of_ne (h.row s) fun heq => hM (hrow s heq)) (h.free s hs)
    obtain ⟨x, hx, hxR⟩ := exists_mem_notMem_of_card_lt_card hlt
    rw [mem_sdiff] at hx
    refine ⟨x, hx.1, hx.2, Or.inr ⟨fun hR => hxR ?_, fun y hy hys => hM ⟨y, hy, hys⟩⟩⟩
    exact mem_filter.2 ⟨hR, blockOf_of_mem (hs.trans ht) hx.1⟩

/-- Removing a matching that covers the tight fibres lowers every fibre bound by one. -/
theorem card_filter_sdiff_le {α : Type*} [DecidableEq α] {R M : Finset ℕ} {f : ℕ → α} {a : α}
    {W : ℕ} (hle : (R.filter fun x => f x = a).card ≤ W)
    (hcov : (R.filter fun x => f x = a).card = W → ∃ x ∈ M, f x = a) (hMR : M ⊆ R) :
    ((R \ M).filter fun x => f x = a).card ≤ W - 1 := by
  rcases hle.eq_or_lt with heq | hlt
  · obtain ⟨x, hxM, hxa⟩ := hcov heq
    have hsub : ((R \ M).filter fun x => f x = a) ⊆ (R.filter fun x => f x = a).erase x := by
      intro y hy
      rw [mem_filter, mem_sdiff] at hy
      exact mem_erase.2 ⟨fun hyx => hy.1.2 (hyx ▸ hxM), mem_filter.2 ⟨hy.1.1, hy.2⟩⟩
    refine (card_le_card hsub).trans ?_
    rw [card_erase_of_mem (mem_filter.2 ⟨hMR hxM, hxa⟩), heq]
  · refine (card_le_card (filter_subset_filter _ sdiff_subset)).trans ?_
    omega

theorem exists_isFill {R' : Finset ℕ} {W' : ℕ} (t : ℕ)
    (h : ∀ c, (R'.filter fun x => col x = c).card ≤ W') : ∃ Z, IsFill b col R' W' t Z := by
  classical
  let 𝒵 : Finset (Finset ℕ) := (blk b t).powerset.filter fun Z =>
    Z.card ≤ W' ∧ ∀ c, ((R' ∪ Z).filter fun x => col x = c).card ≤ W'
  have hne : 𝒵.Nonempty :=
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp, by simpa using h⟩⟩
  obtain ⟨Z, hZ, hmax⟩ := exists_max_image 𝒵 card hne
  obtain ⟨hZsub, hZcard, hZcol⟩ := mem_filter.1 hZ
  rw [mem_powerset] at hZsub
  refine ⟨Z, hZsub, hZcard, hZcol, ?_⟩
  by_cases hfull : Z.card = W'
  · exact Or.inl hfull
  right
  intro x hx hxZ
  by_contra hne
  have hlt : ((R' ∪ Z).filter fun y => col y = col x).card < W' :=
    lt_of_le_of_ne (hZcol _) hne
  have hmem : insert x Z ∈ 𝒵 := by
    refine mem_filter.2 ⟨mem_powerset.2 (insert_subset hx hZsub), ?_, fun c => ?_⟩
    · rw [card_insert_of_notMem hxZ]
      omega
    · rw [union_insert, filter_insert]
      split_ifs with hc
      · refine (card_insert_le _ _).trans ?_
        rw [← hc]
        omega
      · exact hZcol c
  have := hmax _ hmem
  rw [card_insert_of_notMem hxZ] at this
  omega

theorem Inv.colm_sdiff {t : ℕ} {σ : FlowState} (h : Inv m b col t σ) (ht : t < m) (c : ℕ) :
    ((σ.R \ matchingOf m b col σ t).filter fun x => col x = c).card ≤ m - (t + 1) := by
  obtain ⟨hMR, -, -, -, hcol, -⟩ := h.isMatching ht
  exact card_filter_sdiff_le (h.colm c) (hcol c) hMR

theorem Inv.isFill {t : ℕ} {σ : FlowState} (h : Inv m b col t σ) (ht : t < m) :
    IsFill b col (σ.R \ matchingOf m b col σ t) (m - (t + 1)) t (fillOf m b col σ t) :=
  Classical.epsilon_spec (exists_isFill t (h.colm_sdiff ht))

theorem Inv.next {t : ℕ} {σ : FlowState} (h : Inv m b col t σ) (ht : t < m)
    (hb : ∀ t < m, m - t - 1 ≤ b t) : Inv m b col (t + 1) (nextState m b col σ t) := by
  obtain ⟨hMR, -, -, hrow, -, -⟩ := h.isMatching ht
  have hsrv := fun s (hs : s < t) => h.isServer ht hs
  obtain ⟨hZsub, hZcard, hZcol, -⟩ := h.isFill ht
  have hSlt : ∀ x ∈ serversOf m b col σ t, x < start b t := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hx
    exact lt_of_mem_blk (hsrv s (mem_range.1 hs)).1 (mem_range.1 hs)
  have hstep := start_mono b (Nat.le_succ t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact mem_range.2 ((mem_range.1 (h.used_sub hx)).trans_le hstep)
    · exact mem_range.2 ((hSlt x hx).trans_le hstep)
  · intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact mem_range.2 ((mem_range.1 (h.R_sub (mem_sdiff.1 hx).1)).trans_le hstep)
    · exact mem_range.2 (mem_blk.1 (hZsub hx)).2
  · refine disjoint_left.2 fun x hx hx' => ?_
    rcases mem_union.1 hx with hx | hx
    · rw [mem_sdiff] at hx
      rcases mem_union.1 hx' with hx' | hx'
      · exact disjoint_left.1 h.disj hx.1 hx'
      · obtain ⟨s, hs, rfl⟩ := mem_image.1 hx'
        rcases (hsrv s (mem_range.1 hs)).2.2 with h1 | h1
        · exact hx.2 h1
        · exact h1.1 hx.1
    · have hge := (mem_blk.1 (hZsub hx)).1
      rcases mem_union.1 hx' with hx' | hx'
      · have := mem_range.1 (h.used_sub hx')
        omega
      · have := hSlt x hx'
        omega
  · intro s
    change (((σ.R \ matchingOf m b col σ t) ∪ fillOf m b col σ t).filter _).card ≤ _
    rcases eq_or_ne s t with rfl | hst
    · refine (card_le_card ?_).trans hZcard
      intro x hx
      rw [mem_filter, mem_union] at hx
      rcases hx.1 with hxR | hxZ
      · have := blockOf_lt ht.le (mem_range.1 (h.R_sub (mem_sdiff.1 hxR).1))
        omega
      · exact hxZ
    · refine (card_le_card ?_).trans (card_filter_sdiff_le (h.row s) (hrow s) hMR)
      intro x hx
      rw [mem_filter, mem_union] at hx
      rcases hx.1 with hxR | hxZ
      · exact mem_filter.2 ⟨hxR, hx.2⟩
      · exact absurd ((blockOf_of_mem ht (hZsub hxZ)).symm.trans hx.2) (Ne.symm hst)
  · exact hZcol
  · intro s hs
    change _ ≤ (blk b s \ (σ.used ∪ serversOf m b col σ t)).card
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hst | rfl
    · have hsub : (blk b s \ σ.used).erase (serverOf m b col σ t s)
          ⊆ blk b s \ (σ.used ∪ serversOf m b col σ t) := by
        intro x hx
        rw [mem_erase, mem_sdiff] at hx
        refine mem_sdiff.2 ⟨hx.2.1, fun hmem => ?_⟩
        rcases mem_union.1 hmem with hu | hS
        · exact hx.2.2 hu
        · obtain ⟨s', hs', rfl⟩ := mem_image.1 hS
          rw [mem_range] at hs'
          have e1 := blockOf_of_mem (hs'.trans ht) (hsrv s' hs').1
          have e3 : blockOf b m (serverOf m b col σ t s') = s :=
            blockOf_of_mem (hst.trans ht) hx.2.1
          exact hx.1 (by rw [show s' = s from e1.symm.trans e3])
      refine le_trans ?_ (card_le_card hsub)
      have := h.free s hst
      have := pred_card_le_card_erase (s := blk b s \ σ.used) (a := serverOf m b col σ t s)
      omega
    · have heq : blk b s \ (σ.used ∪ serversOf m b col σ s) = blk b s := by
        refine sdiff_eq_self_of_disjoint (disjoint_left.2 fun x hx hx' => ?_)
        have hge := (mem_blk.1 hx).1
        rcases mem_union.1 hx' with hx' | hx'
        · have := mem_range.1 (h.used_sub hx')
          omega
        · have := hSlt x hx'
          omega
      rw [heq, card_blk]
      have := hb s ht
      omega

end Phase

/-! ### The potential (Lemma D.3) -/

section Potential

variable {m : ℕ} {b : ℕ → ℕ} {col : ℕ → ℕ}

theorem inv_state (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t ≤ m) :
    Inv m b col t (state m b col t) := by
  induction t with
  | zero =>
    exact ⟨by simp [state], by simp [state], by simp [state], by simp [state], by simp [state],
      by simp⟩
  | succ t ih => exact (ih (by omega)).next (by omega) hb

variable (m b col)

/-- `Sat(Y_t)`: the saturated colours, whose column of the flow is tight for the window `m - t`. -/
noncomputable def sat (t : ℕ) : Finset ℕ :=
  ((state m b col t).R.image col).filter fun c =>
    ((state m b col t).R.filter fun x => col x = c).card = m - t

/-- The potential `|Y| / W + |Sat(Y)|` before phase `t` (phases numbered from `0`). -/
noncomputable def phi0 (t : ℕ) : ℚ :=
  ((state m b col t).R.card : ℚ) / ((m : ℚ) - t) + (sat m b col t).card

/-- The colouring `col` is proper at block `t`: no vertex of block `t` has the colour of one of
the servers of block `t` (its earlier neighbours). -/
def ProperAt (t : ℕ) : Prop :=
  ∀ x ∈ blk b t, ∀ y ∈ serversOf m b col (state m b col t) t, col x ≠ col y

variable {m b col}

/-- `Forb_t` contains every tight column of `Y_t`, because `M_t` covers them: a colour that occurs
in block `t` is not saturated before phase `t`. -/
theorem notMem_sat (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t < m)
    (hp : ProperAt m b col t) {x : ℕ} (hx : x ∈ blk b t) : col x ∉ sat m b col t := by
  intro hc
  have hinv : Inv m b col t (state m b col t) := inv_state hb ht.le
  obtain ⟨hMR, hinjB, -, -, hcol, -⟩ := hinv.isMatching ht
  obtain ⟨y, hy, hyc⟩ := hcol _ (mem_filter.1 hc).2
  have hs : blockOf b m y < t := blockOf_lt ht.le (mem_range.1 (hinv.R_sub (hMR hy)))
  have hsrv := hinv.isServer ht hs
  rcases hsrv.2.2 with h1 | h1
  · have e : blockOf b m (serverOf m b col (state m b col t) t (blockOf b m y))
        = blockOf b m y := blockOf_of_mem (hs.trans ht) hsrv.1
    have := hinjB h1 hy e
    exact hp x hx _ (mem_image_of_mem _ (mem_range.2 hs)) (by rw [this, hyc])
  · exact h1.2 y hy rfl

/-- **Lemma D.3 (potential gain at one level)**, phases numbered from `0`: if the colouring is
proper at block `t` and `t + 1 < m`, then `Φ` grows by at least one in phase `t`. -/
theorem phi0_gain (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t + 1 < m)
    (hp : ProperAt m b col t) : phi0 m b col t + 1 ≤ phi0 m b col (t + 1) := by
  have hinv : Inv m b col t (state m b col t) := inv_state hb (by omega)
  obtain ⟨hMR, -, hinjC, -, -, hMcard⟩ := hinv.isMatching (by omega)
  obtain ⟨hZsub, hZcard, hZcol, hZmax⟩ := hinv.isFill (by omega)
  set σ := state m b col t with hσ
  set M := matchingOf m b col σ t with hM
  set Z := fillOf m b col σ t with hZ
  have hR1 : (state m b col (t + 1)).R = (σ.R \ M) ∪ Z := rfl
  have hdisj : Disjoint (σ.R \ M) Z := by
    refine disjoint_left.2 fun x hx hx' => ?_
    have := mem_range.1 (hinv.R_sub (mem_sdiff.1 hx).1)
    have := (mem_blk.1 (hZsub hx')).1
    omega
  have hcardR1 : (state m b col (t + 1)).R.card = σ.R.card - M.card + Z.card := by
    rw [hR1, card_union_of_disjoint hdisj, card_sdiff_of_subset hMR]
  -- saturated colours stay saturated
  have hsat : ∀ c ∈ sat m b col t, c ∈ sat m b col (t + 1) := by
    intro c hc
    have hc2 : (σ.R.filter fun x => col x = c).card = m - t := (mem_filter.1 hc).2
    have h1 : (M.filter fun x => col x = c).card ≤ 1 :=
      card_le_one.2 fun a ha a' ha' =>
        hinjC (mem_filter.1 ha).1 (mem_filter.1 ha').1
          ((mem_filter.1 ha).2.trans (mem_filter.1 ha').2.symm)
    have h2 : (σ.R.filter fun x => col x = c) \ (M.filter fun x => col x = c)
        ⊆ ((state m b col (t + 1)).R.filter fun x => col x = c) := by
      intro y hy
      rw [mem_sdiff, mem_filter, mem_filter] at hy
      rw [hR1]
      exact mem_filter.2 ⟨mem_union_left _ (mem_sdiff.2 ⟨hy.1.1, fun h => hy.2 ⟨h, hy.1.2⟩⟩),
        hy.1.2⟩
    have h3 := (le_card_sdiff (M.filter fun x => col x = c)
      (σ.R.filter fun x => col x = c)).trans (card_le_card h2)
    have h4 : ((state m b col (t + 1)).R.filter fun x => col x = c).card ≤ m - (t + 1) := hZcol c
    have h5 : ((state m b col (t + 1)).R.filter fun x => col x = c).card = m - (t + 1) := by
      omega
    refine mem_filter.2 ⟨?_, h5⟩
    obtain ⟨y, hy⟩ := card_pos.1 (by rw [h5]; omega :
      0 < ((state m b col (t + 1)).R.filter fun x => col x = c).card)
    exact mem_image.2 ⟨y, (mem_filter.1 hy).1, (mem_filter.1 hy).2⟩
  -- arithmetic
  have hmt : (t : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : t + 2 ≤ m)
  set W : ℚ := (m : ℚ) - t with hW
  have hWcast : ((m - t : ℕ) : ℚ) = W := by
    rw [Nat.cast_sub (show t ≤ m by omega)]
  have hW1cast : (m : ℚ) - ((t + 1 : ℕ) : ℚ) = W - 1 := by
    push_cast
    ring
  have hMc : W * M.card ≤ σ.R.card := by
    rw [← hWcast]
    exact_mod_cast hMcard
  have hMle : M.card ≤ σ.R.card := card_le_card hMR
  have e1 : ((state m b col (t + 1)).R.card : ℚ) = (σ.R.card : ℚ) - M.card + Z.card := by
    rw [hcardR1]
    push_cast [Nat.cast_sub hMle]
    ring
  have hWpos : (0 : ℚ) < W := by linarith
  have hW1pos : (0 : ℚ) < W - 1 := by linarith
  have key : (σ.R.card : ℚ) / W ≤ ((σ.R.card : ℚ) - M.card) / (W - 1) := by
    rw [div_le_div_iff₀ hWpos hW1pos]
    nlinarith
  have hsatle : ((sat m b col t).card : ℚ) ≤ (sat m b col (t + 1)).card := by
    exact_mod_cast card_le_card hsat
  rw [phi0, phi0, e1, hW1cast]
  by_cases hfull : Z.card = m - (t + 1)
  · have hz : (Z.card : ℚ) = W - 1 := by
      rw [hfull, Nat.cast_sub (show t + 1 ≤ m by omega)]
      push_cast
      ring
    rw [hz, add_div, div_self hW1pos.ne']
    linarith
  · have hmax := hZmax.resolve_left hfull
    have hlt : Z.card < (blk b t).card := by
      rw [card_blk]
      have := hb t (by omega)
      omega
    obtain ⟨x, hx, hxZ⟩ := exists_mem_notMem_of_card_lt_card hlt
    have h6 : ((state m b col (t + 1)).R.filter fun y => col y = col x).card = m - (t + 1) :=
      hmax x hx hxZ
    have hmem : col x ∈ sat m b col (t + 1) := by
      refine mem_filter.2 ⟨?_, h6⟩
      obtain ⟨y, hy⟩ := card_pos.1 (by rw [h6]; omega :
        0 < ((state m b col (t + 1)).R.filter fun y => col y = col x).card)
      exact mem_image.2 ⟨y, (mem_filter.1 hy).1, (mem_filter.1 hy).2⟩
    have hnot : col x ∉ sat m b col t := notMem_sat hb (by omega) hp hx
    have hins : insert (col x) (sat m b col t) ⊆ sat m b col (t + 1) :=
      insert_subset hmem hsat
    have hcard := card_le_card hins
    rw [card_insert_of_notMem hnot] at hcard
    have hcard' : ((sat m b col t).card : ℚ) + 1 ≤ (sat m b col (t + 1)).card := by
      exact_mod_cast hcard
    have : ((σ.R.card : ℚ) - M.card) / (W - 1)
        ≤ ((σ.R.card : ℚ) - M.card + Z.card) / (W - 1) :=
      div_le_div_of_nonneg_right (by simp) hW1pos.le
    linarith

/-- **Theorem D.2, the counting argument.**  Let `m ≥ 1` and `b t ≥ max(1, m - t - 1)` for
`t < m`.  If the colouring `col` of the positions is proper at every block (every vertex of block
`t` avoids the colours of the servers that the flow adversary picks for block `t`), then it uses
at least `⌊m/2⌋ + 1` colours. -/
theorem colours_ge (hm : 1 ≤ m) (hb : ∀ t < m, m - t - 1 ≤ b t) (hb1 : ∀ t < m, 1 ≤ b t)
    (hp : ∀ t < m, ProperAt m b col t) :
    m / 2 + 1 ≤ ((range (start b m)).image col).card := by
  set U := (range (start b m)).image col with hU
  by_contra hcon
  have hUC : U.card ≤ m / 2 := by omega
  rcases Nat.eq_zero_or_pos (m / 2) with hC | hC
  · have h0 : 0 < start b m := by
      have h1 := start_mono b hm
      have h2 := hb1 0 (by omega)
      rw [start_succ] at h1
      omega
    have : 0 < U.card := card_pos.2 ⟨_, mem_image_of_mem col (mem_range.2 h0)⟩
    omega
  set t := 2 * (m / 2) - 1 with ht
  have htm : t < m := by omega
  have hphi : ∀ s, s < m → (s : ℚ) ≤ phi0 m b col s := by
    intro s
    induction s with
    | zero =>
      intro _
      simp [phi0, state]
    | succ s ih =>
      intro hs
      have h1 := phi0_gain hb hs (hp s (by omega))
      have h2 := ih (by omega)
      push_cast
      linarith
  have hinv : Inv m b col t (state m b col t) := inv_state hb htm.le
  have hx0 : start b t ∈ blk b t := by
    refine mem_blk.2 ⟨le_rfl, ?_⟩
    rw [start_succ]
    have := hb1 t htm
    omega
  have hc0 : col (start b t) ∉ sat m b col t := notMem_sat hb htm (hp t htm) hx0
  have hc0U : col (start b t) ∈ U :=
    mem_image_of_mem _ (mem_range.2 (lt_of_mem_blk hx0 htm))
  have hRU : ∀ x ∈ (state m b col t).R, col x ∈ U := fun x hx =>
    mem_image_of_mem _
      (mem_range.2 ((mem_range.1 (hinv.R_sub hx)).trans_le (start_mono b htm.le)))
  have hsatU : sat m b col t ⊆ U.erase (col (start b t)) := by
    intro c hc
    refine mem_erase.2 ⟨fun h => hc0 (h ▸ hc), ?_⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_filter.1 hc).1
    exact hRU y hy
  have hU1 := card_pos.2 ⟨_, hc0U⟩
  have hsatcard : (sat m b col t).card + 1 ≤ U.card := by
    have := card_le_card hsatU
    rw [card_erase_of_mem hc0U] at this
    omega
  have hfib0 : ((state m b col t).R.filter fun x => col x = col (start b t)).card < m - t := by
    refine lt_of_le_of_ne (hinv.colm _) fun heq => hc0 (mem_filter.2 ⟨?_, heq⟩)
    obtain ⟨y, hy⟩ := card_pos.1 (by rw [heq]; omega :
      0 < ((state m b col t).R.filter fun x => col x = col (start b t)).card)
    exact mem_image.2 ⟨y, (mem_filter.1 hy).1, (mem_filter.1 hy).2⟩
  have hRcard : (state m b col t).R.card + 1 ≤ U.card * (m - t) := by
    rw [card_eq_sum_card_fiberwise (f := col) (t := U) hRU, ← add_sum_erase U _ hc0U]
    have h1 := sum_le_card_nsmul (U.erase (col (start b t)))
      (fun c => ((state m b col t).R.filter fun x => col x = c).card) (m - t)
      (fun c _ => hinv.colm c)
    rw [card_erase_of_mem hc0U, smul_eq_mul] at h1
    have h2 : (U.card - 1) * (m - t) + (m - t) = U.card * (m - t) := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  have hWpos : (0 : ℚ) < (m : ℚ) - t := by
    have : (t : ℚ) < m := by exact_mod_cast htm
    linarith
  have h3 : ((state m b col t).R.card : ℚ) / ((m : ℚ) - t) < U.card := by
    rw [div_lt_iff₀ hWpos]
    have : (((state m b col t).R.card + 1 : ℕ) : ℚ) ≤ ((U.card * (m - t) : ℕ) : ℚ) := by
      exact_mod_cast hRcard
    rw [Nat.cast_mul, Nat.cast_sub htm.le] at this
    push_cast at this
    linarith
  have h4 : ((sat m b col t).card : ℚ) + 1 ≤ U.card := by exact_mod_cast hsatcard
  have h5 : (U.card : ℚ) ≤ (m / 2 : ℕ) := by exact_mod_cast hUC
  have h6 : (t : ℚ) = 2 * ((m / 2 : ℕ) : ℚ) - 1 := by
    rw [ht, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h7 := hphi t htm
  rw [phi0] at h7
  linarith

end Potential

/-! ### The strategy reads only the colours of earlier blocks -/

section Congr

variable {m : ℕ} {b : ℕ → ℕ} {col col' : ℕ → ℕ}

theorem IsMatching.congr {R M : Finset ℕ} {W : ℕ} (h : ∀ x ∈ R, col x = col' x)
    (hM : IsMatching m b col R W M) : IsMatching m b col' R W M := by
  obtain ⟨hMR, hB, hC, hrow, hcol, hcard⟩ := hM
  refine ⟨hMR, hB, ?_, hrow, ?_, hcard⟩
  · intro x hx y hy hxy
    apply hC hx hy
    rw [h x (hMR hx), h y (hMR hy)]
    exact hxy
  · intro c hc
    rw [filter_congr (s := R) (p := fun x => col' x = c) (q := fun x => col x = c)
      (fun x hx => by rw [h x hx])] at hc
    obtain ⟨x, hx, hxc⟩ := hcol c hc
    exact ⟨x, hx, by rw [← h x (hMR hx)]; exact hxc⟩

theorem isMatching_congr {R : Finset ℕ} {W : ℕ} (h : ∀ x ∈ R, col x = col' x) :
    IsMatching m b col R W = IsMatching m b col' R W :=
  funext fun _ => propext ⟨.congr h, .congr fun x hx => (h x hx).symm⟩

theorem IsFill.congr {R' Z : Finset ℕ} {W' t : ℕ} (h : ∀ x ∈ R' ∪ blk b t, col x = col' x)
    (hZ : IsFill b col R' W' t Z) : IsFill b col' R' W' t Z := by
  obtain ⟨hsub, hcard, hcol, hmax⟩ := hZ
  have hmem : ∀ x ∈ R' ∪ Z, col x = col' x := fun x hx =>
    h x (union_subset_union_right hsub hx)
  refine ⟨hsub, hcard, fun c => ?_, hmax.imp id fun hm x hx hxZ => ?_⟩
  · rw [filter_congr (s := R' ∪ Z) (p := fun x => col' x = c) (q := fun x => col x = c)
      (fun x hx => by rw [hmem x hx])]
    exact hcol c
  · rw [← hm x hx hxZ]
    congr 1
    exact filter_congr fun y hy => by rw [hmem y hy, h x (mem_union_right _ hx)]

theorem isFill_congr {R' : Finset ℕ} {W' t : ℕ} (h : ∀ x ∈ R' ∪ blk b t, col x = col' x) :
    IsFill b col R' W' t = IsFill b col' R' W' t :=
  funext fun _ => propext ⟨.congr h, .congr fun x hx => (h x hx).symm⟩

theorem matchingOf_congr {σ : FlowState} {t : ℕ} (h : ∀ x ∈ σ.R, col x = col' x) :
    matchingOf m b col σ t = matchingOf m b col' σ t := by
  unfold matchingOf
  rw [isMatching_congr h]

theorem serversOf_congr {σ : FlowState} {t : ℕ} (h : ∀ x ∈ σ.R, col x = col' x) :
    serversOf m b col σ t = serversOf m b col' σ t := by
  unfold serversOf serverOf
  rw [matchingOf_congr h]

theorem nextState_congr {σ : FlowState} {t : ℕ} (hR : σ.R ⊆ range (start b t))
    (h : ∀ x < start b (t + 1), col x = col' x) :
    nextState m b col σ t = nextState m b col' σ t := by
  have hstep := start_mono b (Nat.le_succ t)
  have h1 : ∀ x ∈ σ.R, col x = col' x := fun x hx =>
    h x ((mem_range.1 (hR hx)).trans_le hstep)
  unfold nextState fillOf
  rw [serversOf_congr h1, matchingOf_congr h1, isFill_congr]
  intro x hx
  rcases mem_union.1 hx with hx | hx
  · exact h1 x (mem_sdiff.1 hx).1
  · exact h x (mem_blk.1 hx).2

/-- The state before phase `t` depends only on the colours of the blocks before `t`. -/
theorem state_congr (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t ≤ m)
    (h : ∀ x < start b t, col x = col' x) : state m b col t = state m b col' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hstep := start_mono b (Nat.le_succ t)
    have e := ih (by omega) fun x hx => h x (hx.trans_le hstep)
    change nextState m b col (state m b col t) t = nextState m b col' (state m b col' t) t
    rw [← e]
    exact nextState_congr (inv_state hb (by omega)).R_sub h

/-- The servers of block `t` depend only on the colours of the blocks before `t`. -/
theorem servers_congr (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t ≤ m)
    (h : ∀ x < start b t, col x = col' x) :
    serversOf m b col (state m b col t) t = serversOf m b col' (state m b col' t) t := by
  rw [← state_congr hb ht h]
  exact serversOf_congr fun x hx =>
    h x (mem_range.1 ((inv_state hb ht).R_sub hx))

end Congr

end OnlineColouring.AppBD
