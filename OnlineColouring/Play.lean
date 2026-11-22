module

public import OnlineColouring.Online

/-!
# Adaptive adversaries that never stop

A never-stopping adaptive adversary (an adversary in the sense of Definition 4.2 without the
option to stop) is a rule `adv : History → Finset ℕ` that chooses the earlier-neighbour set of
the next vertex from the history of the play.  Against a fixed deterministic algorithm `A` the
play is determined (`play adv A`), and the vertices presented form one fixed input sequence
`playSeq adv A`; running `A` on that input reproduces the play (`runHist_playSeq`).  So an
adaptive rule played against one deterministic algorithm is just an input, which is how the
second sentence of Observation 4.3 (determinacy) is used.  The reservation blow-ups that complete
every block, as in Section 7, are rules of this kind (`resAdv` in `Structure.lean`).  Adversaries
that may stop are the type `Adversary` (`LabellingCap.lean`), and Observation 4.3 itself is
proved in `Det.lean`.
-/

@[expose] public section

namespace OnlineColouring

variable (adv : History → Finset ℕ) (A : OnlineAlg)

/-- The first `p` moves of the play of the adversary `adv` against the algorithm `A`. -/
def play : ℕ → History
  | 0 => []
  | p + 1 => play p ++ [(adv (play p), A.step (play p) (adv (play p)))]

/-- The input presented by `adv` against `A`: entry `p` is the earlier-neighbour set of the
`p`-th vertex. -/
def playSeq (p : ℕ) : Finset ℕ := adv (play adv A p)

variable {adv A}

theorem play_succ (p : ℕ) :
    play adv A (p + 1) = play adv A p ++ [(adv (play adv A p), A.step (play adv A p)
      (adv (play adv A p)))] := rfl

/-- Running `A` on the input presented by `adv` reproduces the play. -/
theorem runHist_playSeq (p : ℕ) : runHist A (playSeq adv A) p = play adv A p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [runHist_succ, play_succ, runCol, ih]; rfl

@[simp] theorem length_play (p : ℕ) : (play adv A p).length = p := by
  rw [← runHist_playSeq]; simp

theorem colourAt_play {p i : ℕ} (hi : i < p) :
    colourAt (play adv A p) i = runCol A (playSeq adv A) i := by
  rw [← runHist_playSeq, colourAt_runHist hi]

/-- Two adversaries that agree on all histories of length `< P` produce the same first `P`
moves. -/
theorem play_congr {adv' : History → Finset ℕ} {P : ℕ}
    (h : ∀ hist : History, hist.length < P → adv hist = adv' hist) :
    ∀ p ≤ P, play adv A p = play adv' A p := by
  intro p hp
  induction p with
  | zero => rfl
  | succ p ih =>
    have ih' := ih (Nat.le_of_succ_le hp)
    have hl : (play adv' A p).length < P := by rw [length_play]; omega
    rw [play_succ, play_succ, ih', h _ hl]

end OnlineColouring
