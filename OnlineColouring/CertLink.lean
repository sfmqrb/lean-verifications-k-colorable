module

public import OnlineColouring.CertNumbers
public import OnlineColouring.StrRefTower
public import OnlineColouring.AppBDCheapTopAdv

/-!
# The size formulas of `CertNumbers.lean` are the size bounds of the adversaries

`CertNumbers.lean` evaluates two formulas that are written there without reference to an
adversary:

* `Cert.refinedSize K j`, the bound `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` of Proposition B.1 (Table 3,
  and the comparison with the smaller instances of Appendix B at the end of Section 8.4);
* `Cert.cheapTop K j`, the number of vertices of the adversary of Corollary B.2 (the numbers
  `7 176`, `20 944`, `3 685` and `2 658 754 560` after the corollary).

This file proves that they are the size bounds of the adversaries themselves.

* `Cert.refinedSize_eq_refSize`: `Cert.refinedSize K j = Str.refSize K j`, the bound proved for
  the adversary `𝒜' = Str.refTower K j` in `Str.proposition_B_1`.  Consequently
  `Cert.NkLE_refinedSize`: if `|P_j(k)| ≥ K`, then `N_k(K) ≤ Cert.refinedSize K j`.
* `Cert.cheapTop_eq_cheapTopSize`: `Cert.cheapTop K j = AppBD.cheapTopSize K j`, the bound proved
  for the adversary `AppBD.cheapAdv K j` in `AppBD.cheapAdv_sizeLE`.  Consequently
  `Cert.cheapAdv_sizeLE_cheapTop`: under the hypotheses of Corollary B.2 every play of
  `AppBD.cheapAdv K j` has at most `Cert.cheapTop K j` vertices.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

open Finset

/-- The reserve sizes `D_ℓ(t)` of `CertNumbers.lean` are those of `StrRefTower.lean`. -/
theorem refD_eq_str (K d t : ℕ) : refD K d t = Str.refD K d t := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih =>
    simp only [refD, Str.refD, Str.bOf]
    exact Finset.sup_congr rfl fun t' _ => by rw [ih]

/-- The block sizes `b_ℓ(t)` of `CertNumbers.lean` are those of `StrRefTower.lean`. -/
theorem refB_eq_str (K d t : ℕ) : refB K d t = Str.refB K d t := by
  simp only [refB, Str.refB, Str.bOf, refD_eq_str]

/-- The formula `Cert.refinedSize` is the size bound `Str.refSize` of Proposition B.1. -/
theorem refinedSize_eq_refSize (K j : ℕ) : refinedSize K j = Str.refSize K j := by
  unfold refinedSize Str.refSize
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.prod_bij (fun d _ => j - d) ?_ ?_ ?_ ?_
  · intro d hd
    have := Finset.mem_range.1 hd
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro a ha b hb h
    have := Finset.mem_range.1 ha
    have := Finset.mem_range.1 hb
    have h' : j - a = j - b := h
    omega
  · intro ℓ hℓ
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hℓ
    exact ⟨j - ℓ, Finset.mem_range.2 (by omega), show j - (j - ℓ) = ℓ by omega⟩
  · intro d hd
    have := Finset.mem_range.1 hd
    simp only [Str.bl, refB_eq_str]
    congr 1
    omega

/-- Proposition B.1 with the formula of `CertNumbers.lean`: if `|P_j(k)| ≥ K`, then
`N_k(K) ≤ Cert.refinedSize K j`. -/
theorem NkLE_refinedSize {k K j : ℕ} (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    NkLE k K (refinedSize K j) := by
  rw [refinedSize_eq_refSize]
  exact Str.NkLE_refSize hKj

/-- The block sizes below the flow adversary in closed form. -/
theorem cheapBlock_eq (K i : ℕ) : cheapBlock K i = (K - 1) ^ (i + 1) * (2 * K - 4 - 1) + 1 := by
  induction i with
  | zero => simp [cheapBlock]
  | succ i ih =>
    rw [cheapBlock, ih, Nat.add_sub_cancel, pow_succ (K - 1) (i + 1)]
    ring

/-- The formula `Cert.cheapTop` is the size bound `AppBD.cheapTopSize` of Corollary B.2. -/
theorem cheapTop_eq_cheapTopSize (K j : ℕ) : cheapTop K j = AppBD.cheapTopSize K j := by
  unfold cheapTop AppBD.cheapTopSize
  congr 1
  exact Finset.prod_congr rfl fun i _ => cheapBlock_eq K i

/-- Corollary B.2 with the formula of `CertNumbers.lean`: under its hypotheses every play of
`AppBD.cheapAdv K j` has at most `Cert.cheapTop K j` vertices. -/
theorem cheapAdv_sizeLE_cheapTop {k K j : ℕ} (hK : 3 ≤ K) (hj : 1 ≤ j)
    (hP : 2 * K - 2 ≤ Fintype.card (LabelPoset k j)) :
    (AppBD.cheapAdv K j).SizeLE (cheapTop K j) := by
  rw [cheapTop_eq_cheapTopSize]
  exact AppBD.cheapAdv_sizeLE hK hj hP

end Cert

end OnlineColouring
