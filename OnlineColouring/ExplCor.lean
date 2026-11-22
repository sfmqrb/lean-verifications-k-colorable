module

public import OnlineColouring.ExplKnown
public import OnlineColouring.ExplProper
public import OnlineColouring.DetValue

/-!
# Consequences of the explicit adversary of Theorem 8.5 (ii), by the paper's routes

The paper uses the adversary of Theorem 8.5 (ii) in the proof of Theorem 1.3 for `G′` and in the
proof of Corollary 9.6.  Both uses are proved with the explicit adversary `Expl.adv m j` of
`ExplAdv.lean`, without determinacy.  The first one (`χ_ol(G_j(m)) ≥ ⌈X_m⌉`,
`Expl.Gjm_onlineChromaticAtLeast`) is in `ExplKnown.lean`, because `MainLogStar.lean` uses it.
This file has the second one and two further consequences of the adversary.

* `N_k`: `nkLE_uniform`, `Nk_le_uniform`: `N_k(⌈X_m⌉) ≤ m (2m)^j` whenever `m ≤ |P_j(k)|`.
* Proof of Corollary 9.6, lower bound (Section 9.3): *the adversary of Theorem 8.5 (ii),
  with the parameters of the proof of Theorem 1.1, has size at most `n` and forces
  `⌈X_m⌉ ≥ n^{1/(lg* n+3)}` colours, and by Lemma 8.2 each of its plays is a `k`-colourable
  tower.*
  `adv_landsIn_isColTower`, `adv_forces_rpow` (`k ≥ 3`, `n ≥ 2^406`) and
  `adv_forces_rpow_of_four_le` (`k ≥ 4`, `n ≥ 2^201`): for suitable `m`, `j` the adversary
  `adv m j` forces `⌈n^{1/(lg* n+3)}⌉` (resp. `⌈n^{1/(lg* n+1)}⌉`) colours, has size at most
  `n` (no isolated vertices are appended) and lands in the `k`-colourable towers;
  `towerForces_rpow`, `towerForces_rpow_of_four_le` restate this with `Det.TowerForces`.
* Properness (`ExplProper.lean`): `adv_forces_properAgainst`: the adversary forces `⌈X_m⌉` colours
  against every algorithm that answers properly in its play against it.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset

/-! ### `N_k` -/

/-- `N_k(⌈X_m⌉) ≤ m (2m)^j` whenever `m ≤ |P_j(k)|`, witnessed by the explicit adversary. -/
theorem nkLE_uniform {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) :
    NkLE k ⌈uniformBound m⌉₊ (m * (2 * m) ^ j) :=
  ⟨adv m j, (uniform_tower_adversary hj hm).1, (uniform_tower_adversary hj hm).2.1,
    (uniform_tower_adversary hj hm).2.2.2.2.2 k hP⟩

theorem Nk_le_uniform {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) :
    Nk k ⌈uniformBound m⌉₊ ≤ ((m * (2 * m) ^ j : ℕ) : ℕ∞) :=
  Nk_le_iff.2 (nkLE_uniform hj hm hP)

/-! ### Properness only in the play -/

/-- The adversary forces `⌈X_m⌉` colours against every algorithm that answers properly in its
play against it (it need not be proper on other histories). -/
theorem adv_forces_properAgainst {j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m) {A : OnlineAlg}
    (hA : ProperAgainst (adv m j) A) :
    ∃ p, (adv m j).move ((adv m j).hist A p) = none ∧
      ⌈uniformBound m⌉₊ ≤ (usedColours ((adv m j).hist A p)).card :=
  forces_iff_properAgainst.1 (uniform_tower_adversary hj hm).1 A hA

/-! ### The lower bound of Corollary 9.6 -/

/-- Every play of the adversary is a `k`-colourable tower in the sense of Definition 4.7, if
`m ≤ |P_j(k)|`. -/
theorem adv_landsIn_isColTower {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) : (adv m j).LandsIn (Det.IsColTower k) := by
  have hA : 0 < 2 * m := by omega
  refine (adv_presents hj hm hA).landsIn (C := Det.IsColTower k) ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨uInputE_colorable ω hA hP, m, j, Det.uInputE_isPaddedTower hA ω⟩

theorem forces_mono {adv : Adversary} {K K' : ℕ} (h : adv.Forces K) (hK : K' ≤ K) :
    adv.Forces K' := by
  intro A hA
  obtain ⟨p, hp, hc⟩ := h A hA
  exact ⟨p, hp, hK.trans hc⟩

/-- `UniformParams k n x`: there are parameters `j ≥ 1`, `m ≥ 2` of a uniform tower with at most
`n` vertices, `m ≤ |P_j(k)|` and `X_m ≥ x`. -/
def UniformParams (k n : ℕ) (x : ℝ) : Prop :=
  ∃ m j, 1 ≤ j ∧ 2 ≤ m ∧ m * (2 * m) ^ j ≤ n ∧ m ≤ Fintype.card (LabelPoset k j) ∧
    x ≤ uniformBound m

/-- With such parameters, the explicit adversary forces `⌈x⌉` colours with at most `n` vertices
and lands in the `k`-colourable towers. -/
theorem UniformParams.adv {k n : ℕ} {x : ℝ} (h : UniformParams k n x) :
    ∃ m j, (adv m j).Forces ⌈x⌉₊ ∧ (adv m j).SizeLE n ∧ (adv m j).LandsIn (Det.IsColTower k) := by
  obtain ⟨m, j, hj, hm, hn, hP, hx⟩ := h
  exact ⟨m, j, forces_mono (uniform_tower_adversary hj hm).1 (Nat.ceil_mono hx),
    (uniform_tower_adversary hj hm).2.1.mono hn, adv_landsIn_isColTower hj hm hP⟩

theorem uniformParams_hmono : ∀ (k n : ℕ) (x x' : ℝ), 1 ≤ k → UniformParams k n x → x' ≤ x →
    UniformParams k n x' := by
  rintro k n x x' - ⟨m, j, hj, hm, hn, hP, hx⟩ hx'
  exact ⟨m, j, hj, hm, hn, hP, hx'.trans hx⟩

theorem uniformParams_hpad : ∀ (k n n' : ℕ) (x : ℝ), 1 ≤ k → UniformParams k n x → n ≤ n' →
    UniformParams k n' x := by
  rintro k n n' x - ⟨m, j, hj, hm, hn, hP, hx⟩ hn'
  exact ⟨m, j, hj, hm, hn.trans hn', hP, hx⟩

theorem uniformParams_hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m →
    m ≤ Fintype.card (LabelPoset k j) → UniformParams k (m * (2 * m) ^ j) (uniformBound m) :=
  fun _ j m _ hj hm hP => ⟨m, j, hj, hm, le_rfl, hP, le_rfl⟩

/-- **Corollary 9.6, lower bound, with the paper's adversary.** For `k ≥ 3` and `n ≥ 2^406`, for
suitable `m` and `j` the adversary `adv m j` of Theorem 8.5 (ii) has size at most `n`, forces
`⌈n^{1/(lg* n + 3)}⌉` colours, and each of its plays is a `k`-colourable tower. -/
theorem adv_forces_rpow {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ^ 406 ≤ n) :
    ∃ m j, (adv m j).Forces ⌈(n : ℝ) ^ (1 / (logStar n + 3 : ℝ))⌉₊ ∧ (adv m j).SizeLE n ∧
      (adv m j).LandsIn (Det.IsColTower k) := by
  obtain ⟨m, j, h1, h2, h3⟩ := (Rjm.logStar_three_large UniformParams uniformParams_hmono
    uniformParams_hpad uniformParams_hcore hn).adv
  exact ⟨m, j, h1, h2, fun A hA p hp => (h3 A hA p hp).mono hk⟩

/-- For `k ≥ 4` and `n ≥ 2^201`, the same with `⌈n^{1/(lg* n + 1)}⌉` colours. -/
theorem adv_forces_rpow_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    ∃ m j, (adv m j).Forces ⌈(n : ℝ) ^ (1 / (logStar n + 1 : ℝ))⌉₊ ∧ (adv m j).SizeLE n ∧
      (adv m j).LandsIn (Det.IsColTower k) :=
  (Rjm.logStar_of_four_le_large UniformParams uniformParams_hmono uniformParams_hpad
    uniformParams_hcore hk hn).adv

/-- Corollary 9.6, lower bound, in the form of `Det.towerForces_rpow`, with the explicit
adversary. -/
theorem towerForces_rpow {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ^ 406 ≤ n) :
    Det.TowerForces k n ⌈(n : ℝ) ^ (1 / (logStar n + 3 : ℝ))⌉₊ := by
  obtain ⟨m, j, h⟩ := adv_forces_rpow hk hn
  exact ⟨adv m j, h⟩

theorem towerForces_rpow_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    Det.TowerForces k n ⌈(n : ℝ) ^ (1 / (logStar n + 1 : ℝ))⌉₊ := by
  obtain ⟨m, j, h⟩ := adv_forces_rpow_of_four_le hk hn
  exact ⟨adv m j, h⟩

end Expl

end OnlineColouring
