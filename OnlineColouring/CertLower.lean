module

public import OnlineColouring.AdvBasic
public import OnlineColouring.TwoPerColour

/-!
# Lemma B.3 (two vertices per colour) for `N_k(c)`

Lemma B.3 (two vertices per colour) of Appendix B: *For `c ≥ k`, `N_k(c) ≥ 2c - k`*, where
`N_k(c)` is the least number of vertices with which an adversary forces `c` colours on
`k`-colourable graphs (Definition 4.2, `Nk` in `AdvBasic.lean`).

`TwoPerColour.lean` proves the First-Fit count for online inputs
(`OnlineInput.two_mul_cost_firstFit_le`) and the bound for `χ^det`.  Here the same count is
applied to the play of an arbitrary adversary against First-Fit, which gives the lemma for `Nk`
itself: `two_mul_sub_le_of_nkLE` and `le_Nk`.  (The hypothesis `c ≥ k` of the paper is not needed:
for `c < k` the bound `2c - k ≤ N_k(c)` is weaker than the trivial `c ≤ N_k(c)` but still true;
in `ℕ` the subtraction is truncated.)

The play of an adversary against First-Fit is turned into an online input by deleting from every
presented neighbour set the indices that are not earlier vertices (`seqOf`); First-Fit ignores
them, and so does `History.graph`.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

open Finset

/-- The earlier-neighbour sets of a history, as a valid sequence. -/
def seqOf (H : History) (v : ℕ) : Finset ℕ := ((H.getD v (∅, 0)).1).filter (· < v)

theorem seqOf_valid (H : History) : ValidSeq (seqOf H) :=
  fun _ _ hx => mem_range.2 (mem_filter.1 hx).2

theorem firstFit_step_congr {h h' : History} {s s' : Finset ℕ}
    (he : nbrColours h s = nbrColours h' s') :
    OnlineAlg.firstFit.step h s = OnlineAlg.firstFit.step h' s' :=
  Nat.find_congr' fun {c} => by rw [he]

/-- First-Fit gives the vertices of the cleaned sequence the colours they have in the history. -/
theorem runCol_seqOf {H : History} (hH : IsRunOf OnlineAlg.firstFit H) :
    ∀ j (hj : j < H.length), runCol OnlineAlg.firstFit (seqOf H) j = H[j].2 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [hH j hj]
    apply firstFit_step_congr
    have hl : (H.take j).length = j := by simp; omega
    simp only [nbrColours, length_runHist, hl]
    have hf : (seqOf H j).filter (· < j) = (H[j].1).filter (· < j) := by
      simp [seqOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, filter_filter]
    rw [hf]
    refine image_congr fun u hu => ?_
    have hu' : u < j := (mem_filter.1 hu).2
    rw [colourAt_runHist hu', ih u hu' (by omega),
      colourAt_eq_getElem (by simpa using (by omega : u < j ∧ u < H.length))]
    simp

theorem usedColours_eq_image_runCol {H : History} (hH : IsRunOf OnlineAlg.firstFit H) :
    usedColours H = (range H.length).image (runCol OnlineAlg.firstFit (seqOf H)) := by
  ext c
  simp only [usedColours, List.mem_toFinset, List.mem_map, mem_image, mem_range]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨i, hi, runCol_seqOf hH i hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨H[i], List.getElem_mem hi, (runCol_seqOf hH i hi).symm⟩

theorem graph_ofSeq_seqOf (H : History) :
    (OnlineInput.ofSeq (seqOf H) (seqOf_valid H) H.length).graph = H.graph := by
  ext u v
  rw [OnlineInput.ofSeq_adj, History.graph_adj]
  simp only [seqOf, mem_filter, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem u.2,
    List.getElem?_eq_getElem v.2, Option.getD_some, List.get_eq_getElem]
  tauto

/-- **Lemma B.3 (two vertices per colour)** for histories: if First-Fit produced the history `H` and
its graph is `k`-colourable, then `2 · (number of colours) ≤ |H| + k`. -/
theorem two_mul_card_usedColours_le {H : History} {k : ℕ} (hH : IsRunOf OnlineAlg.firstFit H)
    (hc : H.graph.Colorable k) : 2 * (usedColours H).card ≤ H.length + k := by
  have h := (OnlineInput.ofSeq (seqOf H) (seqOf_valid H) H.length).two_mul_cost_firstFit_le
    (by rw [graph_ofSeq_seqOf]; exact hc)
  rwa [OnlineInput.cost_ofSeq, ← usedColours_eq_image_runCol hH] at h

/-- **Lemma B.3 (two vertices per colour)** (`N_k(c) ≥ 2c - k`): an adversary that forces `c`
colours and lands in the `k`-colourable graphs has size at least `2c - k`. -/
theorem two_mul_sub_le_of_nkLE {k c n : ℕ} (h : NkLE k c n) : 2 * c - k ≤ n := by
  obtain ⟨adv, hF, hS, hL⟩ := h
  obtain ⟨p, hstop, hc⟩ := hF OnlineAlg.firstFit OnlineAlg.firstFit_isProper
  have h1 := two_mul_card_usedColours_le (adv.isRunOf_hist OnlineAlg.firstFit p)
    (hL OnlineAlg.firstFit OnlineAlg.firstFit_isProper p hstop)
  have h2 := hS OnlineAlg.firstFit OnlineAlg.firstFit_isProper p
  omega

/-- **Lemma B.3 (two vertices per colour)**, as a statement about `N_k(c)`. -/
theorem le_Nk (k c : ℕ) : ((2 * c - k : ℕ) : ℕ∞) ≤ Nk k c :=
  le_iInf₂ fun _ hn => by exact_mod_cast two_mul_sub_le_of_nkLE hn

/-- An adversary with `2c - k` vertices is optimal. -/
theorem Nk_eq_of_nkLE {k c : ℕ} (h : NkLE k c (2 * c - k)) : Nk k c = ((2 * c - k : ℕ) : ℕ∞) :=
  le_antisymm (Nk_le_iff.2 h) (le_Nk k c)

end Cert

end OnlineColouring
