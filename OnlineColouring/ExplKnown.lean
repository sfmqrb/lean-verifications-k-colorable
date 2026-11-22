module

public import OnlineColouring.ExplAdv
public import OnlineColouring.KnownGame

/-!
# `χ_ol(G_j(m)) ≥ ⌈X_m⌉`, from the adversary of Theorem 8.5 (ii)

The proof of Theorem 1.3 for `G′` (Section 8.4): *every play of the adversary of
Theorem 8.5 (ii) … is a presentation of `G′` …, so Theorem 8.5 (ii) gives
`χ_ol(G′) ≥ ⌈X_m⌉`*.

* `Expl.onlineChromaticAtLeast_of_forces` is the general step: an adversary that forces `K`
  colours and lands in the presentations of `G` shows `χ_ol(G) ≥ K`.
* `Expl.Gjm_onlineChromaticAtLeast` is the application to the adversary `Expl.adv m j` of
  Theorem 8.5 (ii) and to `G_j(m)`.

`MainLogStar.lean` derives the bounds on `χ_ol(G′)` of Theorem 1.3 from the second statement
(`Rjm.uniform_known_graph`, `known_graph_uniform_three` and the declarations next to it).
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset

/-! ### From adversaries to the online chromatic number of a graph -/

/-- **From an adversary to `χ_ol`.** If an adversary forces `K` colours and the final graph of
every play is a presentation of `G` (it has `N` vertices and is isomorphic to `G`), then
`χ_ol(G) ≥ K`. -/
theorem onlineChromaticAtLeast_of_forces {N K : ℕ} {G : SimpleGraph (Fin N)} {adv : Adversary}
    (hF : adv.Forces K)
    (hL : adv.LandsIn fun n H => ∃ e : n = N, Nonempty (H ≃g G.comap (Fin.cast e))) :
    OnlineChromaticAtLeast G K := by
  intro A hA
  have hA' := Det.cleanAlg_isProper hA
  obtain ⟨p, hstop, hK⟩ := hF (Det.cleanAlg A) hA'
  obtain ⟨e, ⟨iso⟩⟩ := hL (Det.cleanAlg A) hA' p hstop
  obtain ⟨I, hIg, hIc⟩ := Det.exists_input_of_hist adv A p
  obtain ⟨I', ⟨e'⟩, hc⟩ := OnlineInput.exists_cast e I
  refine ⟨I', ⟨?_⟩, ?_⟩
  · rw [hIg] at e'
    exact (e'.trans iso).trans (SimpleGraph.Iso.comap (finCongr e) G)
  · rw [hc, hIc]
    exact hK

/-- **`χ_ol(G_j(m)) ≥ ⌈X_m⌉`, from the adversary of Theorem 8.5 (ii)**, as in the paper's proof
of Theorem 1.3 for `G′`: every play of the adversary is a presentation of `G_j(m)`. -/
theorem Gjm_onlineChromaticAtLeast {j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m) :
    OnlineChromaticAtLeast (Rjm.Gjm j m) ⌈uniformBound m⌉₊ :=
  onlineChromaticAtLeast_of_forces (uniform_tower_adversary hj hm).1
    (uniform_tower_adversary hj hm).2.2.2.2.1

end Expl

end OnlineColouring
