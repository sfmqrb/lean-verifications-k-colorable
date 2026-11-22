module

public import OnlineColouring.NumOneLevelAdv

/-!
# The one-level values `V(m)`: definition and general facts

Paper, Appendix D.3 ("One level, exactly"): *"For the minimal one-level game
of Appendix D.2 (blocks of sizes `max(1, m - t)` over `K_m`, one server per arc), let `V(m)` be
the largest number of colours an adversary can force.  Theorem D.2 gives `V(m) ≥ ⌊m/2⌋ + 1`,
First-Fit gives `V(m) ≤ m` … and `m = 11` follows by monotonicity."*

* `minBlock m t = max 1 (m - t - 1)`: the size of block `t` when the blocks are numbered
  `0, …, m - 1` (the paper numbers them `1, …, m`; the block of `v_t` has `max(1, m - t)`
  vertices).
* `Forceable m`: the set of all `c` such that some adversary `adv` with
  `AppBD.IsOneLevelAdv m (minBlock m) adv` (the adversaries of Theorem D.2, `AppBDOneLevel.lean`:
  against every proper algorithm `adv` presents, block after block, a reservation blow-up of `K_m`
  with these block sizes, one unused server in each earlier block, and stops) forces `c` colours
  (`Adversary.Forces`, Definition 4.2).
* `V m = sSup (Forceable m)`; "`V(m) = v`" is proved in the form `IsGreatest (Forceable m) v`
  (`V_eq`).
* `succ_mem_forceable_iff`: **the abstract game computes `V`**: `C + 1` colours can be forced iff
  the adversary beats the palette of `C` colours in the abstract game of `NumGame.lean`.
* `forceable_le_self`, `V_le_self`: `V(m) ≤ m` (the First-Fit bound, here by the strategy of the
  abstract game that gives every block one allowed colour, `surv_self`).
* `half_mem_forceable`, `half_le_V`: `V(m) ≥ ⌊m/2⌋ + 1` for `m ≥ 1` (Theorem D.2).
* `forceable_subset_succ`, `V_mono`: **monotonicity**, `V(m) ≤ V(m + 1)` (an extra first block
  does not hurt the adversary: `Win.cons_row` of `NumGame.lean`, `win_succ`).
-/

@[expose] public section

namespace OnlineColouring

namespace Num

open AppBD

/-- The size of block `t` (blocks numbered `0, …, m - 1`) in the minimal one-level game over
`K_m`: `max(1, m - t - 1)`.  In the paper's numbering the block of `v_t`, `1 ≤ t ≤ m`, has
`max(1, m - t)` vertices. -/
def minBlock (m t : ℕ) : ℕ := max 1 (m - t - 1)

/-- The numbers of colours that some adversary of the minimal one-level game over `K_m`
forces. -/
def Forceable (m : ℕ) : Set ℕ :=
  {c | ∃ adv : Adversary, IsOneLevelAdv m (minBlock m) adv ∧ adv.Forces c}

/-- `V(m)`: the largest number of colours that an adversary can force in the minimal one-level
game over `K_m`. -/
noncomputable def V (m : ℕ) : ℕ := sSup (Forceable m)

theorem forces_mono {adv : Adversary} {K K' : ℕ} (h : adv.Forces K) (hK : K' ≤ K) :
    adv.Forces K' :=
  fun A hA => (h A hA).imp fun _ hp => ⟨hp.1, hK.trans hp.2⟩

/-- An algorithm strategy of the abstract game with `C` colours bounds `V(m)` by `C`. -/
theorem forceable_le_of_surv {m C : ℕ} (hS : Surv C (sizesFrom m (minBlock m) 0) []) {c : ℕ}
    (hc : c ∈ Forceable m) : c ≤ C := by
  obtain ⟨adv, hadv, hF⟩ := hc
  by_contra hlt
  exact not_forces_of_surv (fun t _ => le_max_left _ _) hS hadv (forces_mono hF (by omega))

/-- An adversary strategy of the abstract game against `C` colours shows `V(m) ≥ C + 1`. -/
theorem mem_forceable_of_win {m C : ℕ} (hW : Win C (sizesFrom m (minBlock m) 0) []) :
    C + 1 ∈ Forceable m :=
  exists_adv_of_win (fun _ _ => le_rfl) hW

/-- **The abstract game computes `V(m)`.**  Some adversary of the minimal one-level game over
`K_m` forces `C + 1` colours if and only if the adversary beats the palette of `C` colours in the
abstract game. -/
theorem succ_mem_forceable_iff {m C : ℕ} :
    C + 1 ∈ Forceable m ↔ Win C (sizesFrom m (minBlock m) 0) [] := by
  constructor
  · rintro ⟨adv, hadv, hF⟩
    rw [win_iff_not_surv]
    exact fun hS => not_forces_of_surv (fun t _ => le_max_left _ _) hS hadv hF
  · exact mem_forceable_of_win

/-- Theorem D.2: `⌊m/2⌋ + 1` colours can be forced, for `m ≥ 1`. -/
theorem half_mem_forceable {m : ℕ} (hm : 1 ≤ m) : m / 2 + 1 ∈ Forceable m :=
  one_level_minimal_blocks hm fun _ _ => le_rfl

theorem V_eq {m v : ℕ} (h : IsGreatest (Forceable m) v) : V m = v := h.csSup_eq

theorem le_V {m C c : ℕ} (hub : ∀ c ∈ Forceable m, c ≤ C) (hc : c ∈ Forceable m) : c ≤ V m :=
  le_csSup ⟨C, hub⟩ hc

theorem V_le {m C : ℕ} (hub : ∀ c ∈ Forceable m, c ≤ C) : V m ≤ C :=
  csSup_le' hub

/-! ### The First-Fit bound `V(m) ≤ m` -/

theorem Picked.length_eq : ∀ {rows rows' : List (Multiset ℕ)} {F : Finset ℕ},
    Picked rows rows' F → rows'.length = rows.length ∧ F.card ≤ rows.length
  | [], _, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, le_rfl⟩
  | r :: rows, _, _, h => by
    obtain ⟨c, -, rs', F', hP, rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := Picked.length_eq hP
    refine ⟨by rw [List.length_cons, List.length_cons, h1], ?_⟩
    have := Finset.card_insert_le c F'
    rw [List.length_cons]
    omega

/-- With as many colours as blocks the algorithm survives: it gives each block one colour that
is not forbidden. -/
theorem surv_self {C : ℕ} : ∀ {bs : List ℕ} {rows : List (Multiset ℕ)},
    rows.length + bs.length ≤ C → Surv C bs rows
  | [], _, _ => trivial
  | bt :: bs, rows, h => by
    intro rows' F hP
    obtain ⟨hlen, hF⟩ := Picked.length_eq hP
    rw [List.length_cons] at h
    obtain ⟨c, hc, hcF⟩ : ∃ c ∈ Finset.range C, c ∉ F := by
      by_contra hcon
      have hsub : Finset.range C ⊆ F := fun c hc => by
        by_contra hcF
        exact hcon ⟨c, hc, hcF⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
    refine ⟨Multiset.replicate bt c, Multiset.card_replicate _ _, fun c' hc' => ?_,
      surv_self (by rw [List.length_cons, hlen]; omega)⟩
    rw [Multiset.eq_of_mem_replicate hc']
    exact ⟨Finset.mem_range.1 hc, hcF⟩

theorem length_sizesFrom (m : ℕ) (b : ℕ → ℕ) (t : ℕ) : (sizesFrom m b t).length = m - t := by
  simp [sizesFrom]

/-- **`V(m) ≤ m`** (the First-Fit bound of Appendix D.3). -/
theorem forceable_le_self {m c : ℕ} (hc : c ∈ Forceable m) : c ≤ m :=
  forceable_le_of_surv (surv_self (by rw [length_sizesFrom]; simp)) hc

theorem V_le_self (m : ℕ) : V m ≤ m := V_le fun _ => forceable_le_self

/-- **`V(m) ≥ ⌊m/2⌋ + 1`** for `m ≥ 1` (Theorem D.2). -/
theorem half_le_V {m : ℕ} (hm : 1 ≤ m) : m / 2 + 1 ≤ V m :=
  le_V (fun _ => forceable_le_self) (half_mem_forceable hm)

/-! ### Monotonicity -/

theorem sizesFrom_succ (m : ℕ) :
    sizesFrom (m + 1) (minBlock (m + 1)) 0 = max 1 m :: sizesFrom m (minBlock m) 0 := by
  rw [sizesFrom_of_lt _ (Nat.succ_pos m)]
  congr 1
  rw [sizesFrom, sizesFrom, show m + 1 - (0 + 1) = m - 0 by omega, List.range'_succ_left,
    List.map_map]
  refine List.map_congr_left fun t _ => ?_
  change max 1 (m + 1 - (t + 1) - 1) = max 1 (m - t - 1)
  congr 1
  omega

/-- A winning strategy of the abstract game for `K_m` gives one for `K_{m+1}`: the adversary
ignores the first block, except for taking its servers there. -/
theorem win_succ {C m : ℕ} (h : Win C (sizesFrom m (minBlock m) 0) []) :
    Win C (sizesFrom (m + 1) (minBlock (m + 1)) 0) [] := by
  rw [sizesFrom_succ]
  refine ⟨[], ∅, ⟨rfl, rfl⟩, fun M hM _ => Win.cons_row ?_ h⟩
  rw [hM, length_sizesFrom]
  exact le_max_right _ _

/-- **Monotonicity** (Appendix D.3: "`m = 11` follows by monotonicity").  Every number of
colours that can be forced over `K_m` can be forced over `K_{m+1}`. -/
theorem forceable_subset_succ (m : ℕ) : Forceable m ⊆ Forceable (m + 1) := by
  intro c hc
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · obtain ⟨adv, hadv, hF⟩ := half_mem_forceable (m := m + 1) (Nat.succ_pos m)
    exact ⟨adv, hadv, forces_mono hF (Nat.zero_le _)⟩
  · obtain ⟨C, rfl⟩ : ∃ C, c = C + 1 := ⟨c - 1, by omega⟩
    exact succ_mem_forceable_iff.2 (win_succ (succ_mem_forceable_iff.1 hc))

/-- **`V(m) ≤ V(m + 1)`.** -/
theorem V_le_succ (m : ℕ) : V m ≤ V (m + 1) :=
  V_le fun _ hc => le_V (fun _ => forceable_le_self) (forceable_subset_succ m hc)

theorem V_mono : Monotone V := monotone_nat_of_le_succ V_le_succ

end Num

end OnlineColouring
