module

public import OnlineColouring.Det
public import OnlineColouring.PlayBound

/-!
# Theorem 6.4 as a consequence of determinacy

Theorem 6.4: *Let `k ≥ 2`, `K ≥ 2` and `j ≥ 1` with `|P_j(k)| ≥ K`, and put
`b_ℓ := (K-1)^{j-ℓ+1}(K-2)+1` for `1 ≤ ℓ ≤ j`. There is an adversary that forces every
deterministic online algorithm to use `K` colours, all of whose final graphs are `k`-colourable,
and every play of which has at most `(K-1) ∏_{ℓ=1}^{j} b_ℓ + 1 ≤ K^{(j+1)(j+2)/2}` vertices.*

The adversary of the paper's proof (Construction 6.1 iterated, with its stop rule) is
`Blow.tower`, and the theorem for it is `Blow.theorem_6_4` (`BlowTower.lean`).  This file gives a
second, independent proof of the statement: `Det.iterated_reservation_adversary_exists` obtains
an adversary by the determinacy lemma `Det.exists_presents` from the per-algorithm form
`iterated_reservation_adversary_play` (`PlayBound.lean`: every proper algorithm uses `K` colours
on some `k`-colourable input on exactly `playSize K j = (K-1) ∏ b_ℓ + 1` vertices).  That
adversary always presents exactly `playSize K j` vertices.  The hypotheses `k ≥ 2` and `j ≥ 1`
are not needed.

* `Det.Nk_le_playSize`: `N_k(K) ≤ (K-1) ∏ b_ℓ + 1` if `K ≥ 2` and `|P_j(k)| ≥ K`.
* `Det.iterated_reservation_adversary_exists_tower`: under the same hypotheses there is an
  adversary of size at most `K ∏ b_ℓ` that forces `K` colours and every final graph of which is a
  `k`-colourable `j`-fold full blow-up of `K_K` (`IsFullTower`).
-/

@[expose] public section

namespace OnlineColouring

namespace Det

open Finset

/-- **Theorem 6.4 (the iterated reservation adversary), existence form.**  If `K ≥ 2` and
`|P_j(k)| ≥ K`, there is an adversary that forces `K` colours, all of whose final graphs are
`k`-colourable, and every play of which has at most
`(K-1) ∏_{ℓ=1}^{j} b_ℓ + 1 ≤ K^{(j+1)(j+2)/2}` vertices, where `b_ℓ = blockSize K j ℓ`. -/
theorem iterated_reservation_adversary_exists {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    ∃ adv : Adversary, adv.Forces K ∧ (adv.LandsIn fun _ G => G.Colorable k) ∧
      adv.SizeLE ((K - 1) * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ + 1) ∧
      (K - 1) * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ + 1 ≤ K ^ ((j + 1) * (j + 2) / 2) := by
  obtain ⟨adv, hadv⟩ := exists_presents {I : OnlineInput (playSize K j) | I.graph.Colorable k}
    (iterated_reservation_adversary_play hK hKj)
  exact ⟨adv, hadv.forces, hadv.landsIn fun I hI => hI, hadv.sizeLE, playSize_le hK j⟩

/-- Theorem 6.4 in terms of `N_k(K)`: `N_k(K) ≤ (K-1) ∏ b_ℓ + 1`. -/
theorem Nk_le_playSize {k K j : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    Nk k K ≤ playSize K j := by
  obtain ⟨adv, hF, hL, hS, -⟩ := iterated_reservation_adversary_exists hK hKj
  exact Nk_le_iff.2 ⟨adv, hF, hS, hL⟩

/-- Theorem 6.4 in structure mode (no stop rule): there is an adversary that forces `K` colours,
has size at most `K ∏ b_ℓ`, and every final graph of which is a `k`-colourable `j`-fold full
blow-up of `K_K`. -/
theorem iterated_reservation_adversary_exists_tower {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    ∃ adv : Adversary, adv.Forces K ∧ adv.SizeLE (K * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ) ∧
      adv.LandsIn fun n G => IsFullTower K j ⟨Fin n, G⟩ ∧ G.Colorable k := by
  obtain ⟨adv, hadv⟩ := exists_presents
    {I : OnlineInput (K * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ) |
      IsFullTower K j I.toOrdGraph ∧ I.graph.Colorable k}
    (fun A hA => by
      obtain ⟨I, h1, h2, h3⟩ := iterated_reservation_adversary hK hKj A hA
      exact ⟨I, ⟨h1, h2⟩, h3⟩)
  exact ⟨adv, hadv.forces, hadv.sizeLE,
    hadv.landsIn (C := fun n G => IsFullTower K j ⟨Fin n, G⟩ ∧ G.Colorable k) fun I hI => hI⟩

end Det

end OnlineColouring
