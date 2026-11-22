module

public import OnlineColouring.AppBDFlow
public import OnlineColouring.Play

/-!
# Theorem D.2 (one level, minimal blocks): the flow adversary

Theorem D.2 (one level, minimal blocks) of Appendix D.2, with the setting
that precedes it: *Consider, for `m ≥ 1`, reservation blow-ups of `K_m = (v_1, …, v_m)` in which
the block of `v_t` has `b_t ≥ max(1, m - t)` vertices … When the block of `v_t` starts, the
adversary picks one vertex of each earlier block that has not served yet to serve `v_t` … There
is an adversary of this form that forces `⌊m/2⌋ + 1` colours.*

"An adversary of this form" is `IsOneLevelAdv m b adv`: in every play against a proper algorithm
the adversary presents, block after block, a reservation blow-up of `K_m` with block sizes `b`
(`IsOneLevelSeq`): all vertices of block `t` have the same earlier neighbours, one server in each
earlier block, and no vertex serves two blocks.  It presents all `∑ b_t` vertices and stops.

* `flowAdv m b`: the flow adversary (an `Adversary`); its strategy is `AppBDFlow.lean`.
* `flowAdv_isOneLevelAdv`, `flowAdv_forces`.
* `one_level_minimal_blocks`: **Theorem D.2**, blocks numbered `0, …, m-1`.
* `one_level_minimal_blocks_paper`: the same with the paper's numbering `b_1, …, b_m`.
* `phi`, `phi_gain`: **Lemma D.3** for the play of the flow adversary against a proper algorithm,
  with the paper's numbering of the phases.

The hypothesis `m ≥ 1` of the paper is needed: for `m = 0` no vertex is presented and no colour
is forced.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-- The adversary that presents exactly `n` vertices, choosing the earlier neighbours of each by
the rule `f`, and then stops. -/
def boundedAdv (n : ℕ) (f : History → Finset ℕ) : Adversary :=
  ⟨fun h => if h.length < n then some (f h) else none⟩

theorem boundedAdv_hist (n : ℕ) (f : History → Finset ℕ) (A : OnlineAlg) :
    ∀ p, (boundedAdv n f).hist A p = play f A (min p n) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Adversary.hist, ih]
    rcases Nat.lt_or_ge p n with hp | hp
    · have hmove : (boundedAdv n f).move (play f A (min p n)) = some (f (play f A p)) := by
        simp [boundedAdv, min_eq_left hp.le, hp]
      rw [hmove, min_eq_left hp.le, min_eq_left (by omega : p + 1 ≤ n)]
      rfl
    · have hmove : (boundedAdv n f).move (play f A (min p n)) = none := by
        simp [boundedAdv, min_eq_right hp]
      rw [hmove, min_eq_right hp, min_eq_right (by omega : n ≤ p + 1)]

/-- The input sequence `N` (earlier-neighbour sets of the positions) is a reservation blow-up of
`K_m` with block sizes `b`, one server per arc: the vertices of block `t` have the common set of
earlier neighbours `{srv t s : s < t}`, where `srv t s` lies in block `s`, and no vertex serves
two blocks. -/
def IsOneLevelSeq (m : ℕ) (b : ℕ → ℕ) (N : ℕ → Finset ℕ) : Prop :=
  ∃ srv : ℕ → ℕ → ℕ, (∀ t < m, ∀ s < t, srv t s ∈ blk b s) ∧
    (∀ t < m, ∀ t' < m, ∀ s, s < t → s < t' → srv t s = srv t' s → t = t') ∧
    ∀ t < m, ∀ x ∈ blk b t, N x = (range t).image (srv t)

/-- "An adversary of this form": against every proper algorithm it presents a reservation blow-up
of `K_m` with block sizes `b` (all `start b m = ∑_{t<m} b t` vertices) and stops. -/
def IsOneLevelAdv (m : ℕ) (b : ℕ → ℕ) (adv : Adversary) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ N : ℕ → Finset ℕ, IsOneLevelSeq m b N ∧
    ∀ p, adv.hist A p = runHist A N (min p (start b m))

/-- The rule of the flow adversary: the earlier neighbours of the next vertex are the servers that
the flow strategy picks for its block, computed from the colours in the history. -/
noncomputable def flowRule (m : ℕ) (b : ℕ → ℕ) (h : History) : Finset ℕ :=
  serversOf m b (colourAt h) (state m b (colourAt h) (blockOf b m h.length))
    (blockOf b m h.length)

/-- The flow adversary of Theorem D.2. -/
noncomputable def flowAdv (m : ℕ) (b : ℕ → ℕ) : Adversary :=
  boundedAdv (start b m) (flowRule m b)

section Play

variable {m : ℕ} {b : ℕ → ℕ} (A : OnlineAlg)

/-- The colouring that `A` produces against the flow adversary. -/
noncomputable def flowCol (m : ℕ) (b : ℕ → ℕ) (A : OnlineAlg) : ℕ → ℕ :=
  runCol A (playSeq (flowRule m b) A)

theorem flowSeq_eq (hb : ∀ t < m, m - t - 1 ≤ b t) {t x : ℕ} (ht : t < m) (hx : x ∈ blk b t) :
    playSeq (flowRule m b) A x
      = serversOf m b (flowCol m b A) (state m b (flowCol m b A) t) t := by
  change flowRule m b (play (flowRule m b) A x) = _
  unfold flowRule
  rw [length_play, blockOf_of_mem ht hx]
  exact servers_congr hb ht.le fun y hy => colourAt_play (hy.trans_le (mem_blk.1 hx).1)

theorem used_mono (col : ℕ → ℕ) {s t : ℕ} (h : s ≤ t) :
    (state m b col s).used ⊆ (state m b col t).used := by
  induction t with
  | zero => rw [Nat.le_zero.1 h]
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans subset_union_left
    · exact subset_rfl

theorem flowSeq_isOneLevelSeq (hb : ∀ t < m, m - t - 1 ≤ b t) :
    IsOneLevelSeq m b (playSeq (flowRule m b) A) := by
  set col := flowCol m b A with hcol
  have hsrv : ∀ t < m, ∀ s < t, IsServer m b (state m b col t).used (state m b col t).R
      (matchingOf m b col (state m b col t) t) s (serverOf m b col (state m b col t) t s) :=
    fun t ht s hs => (inv_state hb ht.le).isServer ht hs
  have key : ∀ t < m, ∀ t' < m, ∀ s, s < t → t < t' →
      serverOf m b col (state m b col t) t s ≠ serverOf m b col (state m b col t') t' s := by
    intro t ht t' ht' s hs htt' heq
    have h1 : serverOf m b col (state m b col t) t s ∈ (state m b col (t + 1)).used :=
      mem_union_right _ (mem_image_of_mem _ (mem_range.2 hs))
    exact (hsrv t' ht' s (hs.trans htt')).2.1 (heq ▸ used_mono col (by omega) h1)
  refine ⟨fun t s => serverOf m b col (state m b col t) t s, fun t ht s hs => (hsrv t ht s hs).1,
    ?_, fun t ht x hx => flowSeq_eq A hb ht hx⟩
  intro t ht t' ht' s hs hs' heq
  rcases lt_trichotomy t t' with h | h | h
  · exact absurd heq (key t ht t' ht' s hs h)
  · exact h
  · exact absurd heq.symm (key t' ht' t ht s hs' h)

theorem flowAdv_hist (p : ℕ) :
    (flowAdv m b).hist A p = runHist A (playSeq (flowRule m b) A) (min p (start b m)) := by
  rw [flowAdv, boundedAdv_hist, runHist_playSeq]

/-- The flow adversary is an adversary of the form considered in Theorem D.2, if
`b t ≥ m - t - 1` for `t < m`. -/
theorem flowAdv_isOneLevelAdv (hb : ∀ t < m, m - t - 1 ≤ b t) : IsOneLevelAdv m b (flowAdv m b) :=
  fun A _ => ⟨_, flowSeq_isOneLevelSeq A hb, flowAdv_hist A⟩

theorem flowCol_properAt (hA : A.IsProper) (hb : ∀ t < m, m - t - 1 ≤ b t) {t : ℕ} (ht : t < m) :
    ProperAt m b (flowCol m b A) t := by
  intro x hx y hy
  have hy' : y ∈ playSeq (flowRule m b) A x := by rwa [flowSeq_eq A hb ht hx]
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hy
  rw [mem_range] at hs
  have hlt := lt_of_mem_blk ((inv_state (col := flowCol m b A) hb ht.le).isServer ht hs).1 hs
  exact runCol_ne hA hy' (hlt.trans_le (mem_blk.1 hx).1)

/-- The flow adversary forces `⌊m/2⌋ + 1` colours, if `m ≥ 1` and `b t ≥ max(1, m - t - 1)` for
`t < m`. -/
theorem flowAdv_forces (hm : 1 ≤ m) (hb : ∀ t < m, m - t - 1 ≤ b t) (hb1 : ∀ t < m, 1 ≤ b t) :
    (flowAdv m b).Forces (m / 2 + 1) := by
  intro A hA
  refine ⟨start b m, ?_, ?_⟩
  · rw [flowAdv_hist, min_self]
    simp [flowAdv, boundedAdv]
  · rw [flowAdv_hist, min_self, usedColours_runHist]
    exact colours_ge hm hb hb1 fun t ht => flowCol_properAt A hA hb ht

end Play

/-- **Theorem D.2 (one level, minimal blocks).**  Blocks numbered `0, …, m-1`: if `m ≥ 1` and
block `t` has `b t ≥ max(1, m - t - 1)` vertices, there is an adversary of this form (a
one-level reservation blow-up of `K_m` with block sizes `b`, one unused server per earlier block)
that forces `⌊m/2⌋ + 1` colours. -/
theorem one_level_minimal_blocks {m : ℕ} {b : ℕ → ℕ} (hm : 1 ≤ m)
    (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) :
    ∃ adv : Adversary, IsOneLevelAdv m b adv ∧ adv.Forces (m / 2 + 1) :=
  ⟨flowAdv m b, flowAdv_isOneLevelAdv fun t ht => (le_max_right _ _).trans (hb t ht),
    flowAdv_forces hm (fun t ht => (le_max_right _ _).trans (hb t ht))
      fun t ht => (le_max_left _ _).trans (hb t ht)⟩

/-- **Theorem D.2** with the paper's numbering: the block of `v_t`, `1 ≤ t ≤ m`, has
`b t ≥ max(1, m - t)` vertices. -/
theorem one_level_minimal_blocks_paper {m : ℕ} {b : ℕ → ℕ} (hm : 1 ≤ m)
    (hb : ∀ t, 1 ≤ t → t ≤ m → max 1 (m - t) ≤ b t) :
    ∃ adv : Adversary, IsOneLevelAdv m (fun s => b (s + 1)) adv ∧ adv.Forces (m / 2 + 1) :=
  one_level_minimal_blocks hm fun t ht => by
    have := hb (t + 1) (by omega) (by omega)
    rwa [show m - (t + 1) = m - t - 1 by omega] at this

/-! ### Lemma D.3 with the paper's numbering -/

/-- The potential `Φ_t = |Y_t| / W_t + |Sat(Y_t)|` of the paper (`1 ≤ t ≤ m`, `W_t = m - t + 1`)
in the play of the flow adversary against `A`. -/
noncomputable def phi (m : ℕ) (b : ℕ → ℕ) (A : OnlineAlg) (t : ℕ) : ℚ :=
  phi0 m b (flowCol m b A) (t - 1)

/-- **Lemma D.3 (potential gain at one level).**  In the play of the flow adversary against a
proper algorithm, `Φ_{t+1} ≥ Φ_t + 1` for `1 ≤ t ≤ m - 1`. -/
theorem phi_gain {m : ℕ} {b : ℕ → ℕ} {A : OnlineAlg} (hA : A.IsProper)
    (hb : ∀ t < m, max 1 (m - t - 1) ≤ b t) {t : ℕ} (ht1 : 1 ≤ t) (htm : t ≤ m - 1) :
    phi m b A t + 1 ≤ phi m b A (t + 1) := by
  have hb' : ∀ t < m, m - t - 1 ≤ b t := fun t ht => (le_max_right _ _).trans (hb t ht)
  have := phi0_gain (t := t - 1) hb' (by omega) (flowCol_properAt A hA hb' (by omega))
  rwa [show t - 1 + 1 = t by omega] at this

/-- `Φ_1 = 0`. -/
theorem phi_one (m : ℕ) (b : ℕ → ℕ) (A : OnlineAlg) : phi m b A 1 = 0 := by
  simp [phi, phi0, state, sat]

end OnlineColouring.AppBD
