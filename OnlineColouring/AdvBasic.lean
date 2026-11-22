module

public import OnlineColouring.LabellingCap

/-!
# Adversaries: final graphs, size, post-degree, `N_k(K)` (Definition 4.2)

Definition 4.2 (adversaries): *An adversary is a deterministic rule that, given the history of a
play (the ordered graph presented so far and the colours given to it), either stops or presents a
new vertex together with its set of earlier neighbours. It forces `K` colours if every play
against every deterministic online algorithm is finite and ends with at least `K` colours in use.
It has size at most `N` and post-degree at most `D` if in every play at most `N` vertices are
presented and every vertex receives at most `D` later neighbours. It lands in a class of ordered
graphs if the final graph of every play belongs to the class.*  After the definition, the paper
lets `N_k(K)` be the least size of an adversary that forces `K` colours and lands in the
`k`-colourable graphs.

`Adversary`, `Adversary.hist` (the history after `p` rounds) and `Adversary.Forces` are in
`LabellingCap.lean`. This file adds the remaining notions of the definition. All results about
adversary objects (Observation 4.3, Lemma 6.2, Theorem 6.4, Theorem 8.5 (ii), ...) use these
definitions.

* `History.graph h`: the ordered graph presented in the history `h` (vertex `i` is entry `i`; an
  index in a neighbour set that is not an earlier vertex is ignored, as in `nbrColours`).
* `History.postDeg h i`: the number of later neighbours of vertex `i` in `h`.
* `Adversary.StopsAt`, `Adversary.SizeLE`, `Adversary.PostDegLE`, `Adversary.LandsIn`.
* `NkLE k K n` ("`N_k(K) ≤ n`") and `Nk k K : ℕ∞` (`⊤` if no adversary forces `K` colours on
  `k`-colourable graphs).
-/

@[expose] public section

namespace OnlineColouring

/-- The ordered graph presented in the history `h`: vertex `i` is entry `i`, and `u < v` are
adjacent iff `u` belongs to the earlier-neighbour set of `v`. -/
def History.graph (h : History) : SimpleGraph (Fin h.length) :=
  SimpleGraph.fromRel fun u v => (u : ℕ) < v ∧ (u : ℕ) ∈ (h.get v).1

theorem History.graph_adj {h : History} {u v : Fin h.length} :
    h.graph.Adj u v ↔
      ((u : ℕ) < v ∧ (u : ℕ) ∈ (h.get v).1) ∨ ((v : ℕ) < u ∧ (v : ℕ) ∈ (h.get u).1) := by
  simp only [History.graph, SimpleGraph.fromRel_adj, ne_eq]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨fun e => (lt_irrefl (u : ℕ)) (by simpa [e] using h.1), Or.inl h⟩
    · exact ⟨fun e => (lt_irrefl (v : ℕ)) (by simpa [e] using h.1), Or.inr h⟩

/-- The post-degree of vertex `i` in the history `h`: its number of later neighbours. -/
def History.postDeg (h : History) (i : ℕ) : ℕ :=
  ((Finset.range h.length).filter fun v => i < v ∧ i ∈ (h.getD v (∅, 0)).1).card

namespace Adversary

/-- The play of `adv` against `A` has stopped after `p` rounds. -/
def StopsAt (adv : Adversary) (A : OnlineAlg) (p : ℕ) : Prop :=
  adv.move (adv.hist A p) = none

/-- `adv` has size at most `N`: in every play at most `N` vertices are presented. -/
def SizeLE (adv : Adversary) (N : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, (adv.hist A p).length ≤ N

/-- `adv` has post-degree at most `D`: in every play every vertex receives at most `D` later
neighbours. -/
def PostDegLE (adv : Adversary) (D : ℕ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p i, (adv.hist A p).postDeg i ≤ D

/-- `adv` lands in the class `C` of ordered graphs: the final graph of every play belongs to `C`.
(A class of ordered graphs is a predicate on graphs on `Fin n`, ordered by `Fin n`.) -/
def LandsIn (adv : Adversary) (C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, adv.StopsAt A p → C _ (adv.hist A p).graph

theorem SizeLE.mono {adv : Adversary} {N N' : ℕ} (h : adv.SizeLE N) (hN : N ≤ N') :
    adv.SizeLE N' := fun A hA p => (h A hA p).trans hN

end Adversary

/-- "`N_k(K) ≤ n`": some adversary of size at most `n` forces `K` colours and lands in the
`k`-colourable graphs. -/
def NkLE (k K n : ℕ) : Prop :=
  ∃ adv : Adversary, adv.Forces K ∧ adv.SizeLE n ∧ adv.LandsIn fun _ G => G.Colorable k

theorem NkLE.mono {k K n n' : ℕ} (h : NkLE k K n) (hn : n ≤ n') : NkLE k K n' := by
  obtain ⟨adv, hF, hS, hL⟩ := h
  exact ⟨adv, hF, hS.mono hn, hL⟩

/-- `N_k(K)`: the least size of an adversary that forces `K` colours and lands in the
`k`-colourable graphs (`⊤` if there is none). -/
noncomputable def Nk (k K : ℕ) : ℕ∞ := ⨅ (n : ℕ) (_ : NkLE k K n), (n : ℕ∞)

theorem Nk_le_iff {k K n : ℕ} : Nk k K ≤ n ↔ NkLE k K n := by
  constructor
  · intro h
    by_contra hn
    have hlt : ∀ m, NkLE k K m → n < m := fun m hm => by
      by_contra hmn
      exact hn (hm.mono (not_lt.mp hmn))
    have : (n : ℕ∞) < Nk k K := by
      apply lt_of_lt_of_le (b := ((n + 1 : ℕ) : ℕ∞))
      · exact_mod_cast Nat.lt_succ_self n
      · exact le_iInf₂ fun m hm => by exact_mod_cast hlt m hm
    exact absurd h (not_le.mpr this)
  · intro h
    exact iInf₂_le n h

end OnlineColouring
