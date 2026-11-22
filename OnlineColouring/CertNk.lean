module

public import OnlineColouring.CertLower
public import OnlineColouring.CertK3
public import OnlineColouring.CertK3C9
public import OnlineColouring.CertK4
public import OnlineColouring.CertK4C10
public import OnlineColouring.CertK5
public import OnlineColouring.CertK5C11
public import OnlineColouring.CertK5C12
public import OnlineColouring.CertK6
public import OnlineColouring.CertK6C13

/-!
# Proposition B.4 (exact values)

Proposition B.4 (exact values) of Appendix B: *For `3 ≤ c ≤ 9` we have `N_3(c) = 2c - 3`, and
`N_3(10) ≥ 17`. For `k ≤ c ≤ c_k` with `(k, c_k) = (4, 10), (5, 12), (6, 13)`, `N_k(c) = 2c - k`.*

Here `N_k(c) = Nk k c : ℕ∞` is the least size of an adversary that forces `c` colours and lands
in the `k`-colourable graphs (Definition 4.2, `AdvBasic.lean`).

* Lower bounds: Lemma B.3 (two vertices per colour): `Cert.le_Nk` (`CertLower.lean`).
* Upper bounds: the thirty adversary strategies of the supplementary material
  (`repro/certificates/dag_k*_C*.gen.txt`), checked by the Lean kernel with the verified
  checker of `CertCheck.lean` (`Cert.nkLE_3_3`, …, `Cert.nkLE_6_13` in the nine modules `CertK*`);
  no `native_decide`.

`prop_small` is the proposition as stated.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

/-- **Proposition B.4 (exact values), `k = 3`:** `N_3(c) = 2c - 3` for `3 ≤ c ≤ 9`. -/
theorem Nk_three {c : ℕ} (h3 : 3 ≤ c) (h9 : c ≤ 9) : Nk 3 c = ((2 * c - 3 : ℕ) : ℕ∞) := by
  apply Nk_eq_of_nkLE
  interval_cases c
  exacts [nkLE_3_3, nkLE_3_4, nkLE_3_5, nkLE_3_6, nkLE_3_7, nkLE_3_8, nkLE_3_9]

/-- **Proposition B.4 (exact values):** `N_3(10) ≥ 17`. -/
theorem Nk_three_ten : (17 : ℕ∞) ≤ Nk 3 10 := le_Nk 3 10

/-- **Proposition B.4 (exact values), `k = 4`:** `N_4(c) = 2c - 4` for `4 ≤ c ≤ 10`. -/
theorem Nk_four {c : ℕ} (h4 : 4 ≤ c) (h10 : c ≤ 10) : Nk 4 c = ((2 * c - 4 : ℕ) : ℕ∞) := by
  apply Nk_eq_of_nkLE
  interval_cases c
  exacts [nkLE_4_4, nkLE_4_5, nkLE_4_6, nkLE_4_7, nkLE_4_8, nkLE_4_9, nkLE_4_10]

/-- **Proposition B.4 (exact values), `k = 5`:** `N_5(c) = 2c - 5` for `5 ≤ c ≤ 12`. -/
theorem Nk_five {c : ℕ} (h5 : 5 ≤ c) (h12 : c ≤ 12) : Nk 5 c = ((2 * c - 5 : ℕ) : ℕ∞) := by
  apply Nk_eq_of_nkLE
  interval_cases c
  exacts [nkLE_5_5, nkLE_5_6, nkLE_5_7, nkLE_5_8, nkLE_5_9, nkLE_5_10, nkLE_5_11, nkLE_5_12]

/-- **Proposition B.4 (exact values), `k = 6`:** `N_6(c) = 2c - 6` for `6 ≤ c ≤ 13`. -/
theorem Nk_six {c : ℕ} (h6 : 6 ≤ c) (h13 : c ≤ 13) : Nk 6 c = ((2 * c - 6 : ℕ) : ℕ∞) := by
  apply Nk_eq_of_nkLE
  interval_cases c
  exacts [nkLE_6_6, nkLE_6_7, nkLE_6_8, nkLE_6_9, nkLE_6_10, nkLE_6_11, nkLE_6_12, nkLE_6_13]

/-- **Proposition B.4 (exact values)**, as stated: `N_3(c) = 2c - 3` for `3 ≤ c ≤ 9`,
`N_3(10) ≥ 17`, and `N_k(c) = 2c - k` for `k ≤ c ≤ c_k` with
`(k, c_k) = (4, 10), (5, 12), (6, 13)`. -/
theorem prop_small :
    (∀ c, 3 ≤ c → c ≤ 9 → Nk 3 c = ((2 * c - 3 : ℕ) : ℕ∞)) ∧ (17 : ℕ∞) ≤ Nk 3 10 ∧
      ∀ k ck, (k, ck) ∈ [(4, 10), (5, 12), (6, 13)] → ∀ c, k ≤ c → c ≤ ck →
        Nk k c = ((2 * c - k : ℕ) : ℕ∞) := by
  refine ⟨fun c => Nk_three, Nk_three_ten, fun k ck hk c h1 h2 => ?_⟩
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Nk_four h1 h2
  · exact Nk_five h1 h2
  · exact Nk_six h1 h2

end Cert

end OnlineColouring
