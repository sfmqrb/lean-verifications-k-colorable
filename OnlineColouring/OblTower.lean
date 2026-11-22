module

public import OnlineColouring.OblProb
public import OnlineColouring.ProbForcing

/-!
# Theorem C.3 (iterated oblivious blow-ups)

Theorem C.3 (`thm:Lrand`) of Appendix C, as stated.

* For `K`, `j` and block sizes `b : ℕ → ℕ` (used at `ℓ = 1, …, j`), `towN K j b ℓ = N_ℓ` and
  `towD K j b ℓ = D_ℓ` are the paper's sequences: `N_j = K`, `D_j = K - 1`, and
  `N_{ℓ-1} = N_ℓ b_ℓ`, `D_{ℓ-1} = b_ℓ` for `ℓ = j, …, 1` (`towN_self`, `towD_self`, `towN_pred`,
  `towD_pred`); in closed form `N_ℓ = K ∏_{ℓ < i ≤ j} b_i`.
* `oblivious_towers`: let `k ≥ 2`, `K ≥ 2`, `j ≥ 1` with `|P_j(k)| ≥ K`, `ε ∈ (0,1)` and positive
  `b_1, …, b_j`.  If `∑_{ℓ=1}^{j} N_ℓ D_ℓ exp(-b_ℓ/((K-1) D_ℓ)) ≤ ε`, then
  `ProbForcing k N_0 K (1 - ε)`: there is a distribution over `k`-colourable online inputs on
  exactly `N_0` vertices on which every proper deterministic online algorithm uses at least `K`
  colours with probability at least `1 - ε`.

The proof is the paper's: `ℋ_j` is the point mass on the arrival-ordered clique `K_K`
(`level_clique`), `ℋ_{ℓ-1} = OB_{b_ℓ}(ℋ_ℓ)` with `δ ≡ D_ℓ` (`Level.step`, by Lemma C.2 with the
sufficient condition for (c)), and the losses add up.  The hypotheses `k ≥ 2`, `j ≥ 1`,
`0 < ε < 1` and the positivity of the `b_ℓ` are part of the paper's statement; the proof does not
use them.
-/

@[expose] public section

namespace OnlineColouring

namespace Obl

open Finset
open scoped ENNReal

/-! ### The sequences `N_ℓ` and `D_ℓ` -/

/-- `N_ℓ = K ∏_{ℓ < i ≤ j} b_i`: the number of vertices at level `ℓ`. -/
def towN (K j : ℕ) (b : ℕ → ℕ) (ℓ : ℕ) : ℕ := K * ∏ i ∈ Ioc ℓ j, b i

/-- `D_ℓ`: the post-degree bound at level `ℓ`; `D_j = K - 1` and `D_ℓ = b_{ℓ+1}` for `ℓ < j`. -/
def towD (K j : ℕ) (b : ℕ → ℕ) (ℓ : ℕ) : ℕ := if ℓ = j then K - 1 else b (ℓ + 1)

theorem towN_self (K j : ℕ) (b : ℕ → ℕ) : towN K j b j = K := by
  simp [towN]

theorem towD_self (K j : ℕ) (b : ℕ → ℕ) : towD K j b j = K - 1 := by
  simp [towD]

theorem Ioc_eq_insert {l j : ℕ} (h : l < j) : Ioc l j = insert (l + 1) (Ioc (l + 1) j) := by
  ext i
  simp only [mem_Ioc, mem_insert]
  omega

/-- `N_{ℓ-1} = N_ℓ b_ℓ`, written with `ℓ = l + 1 ≤ j`. -/
theorem towN_pred (K : ℕ) {j l : ℕ} (b : ℕ → ℕ) (h : l < j) :
    towN K j b l = towN K j b (l + 1) * b (l + 1) := by
  unfold towN
  rw [Ioc_eq_insert h, prod_insert (by simp)]
  ring

/-- `D_{ℓ-1} = b_ℓ`, written with `ℓ = l + 1 ≤ j`. -/
theorem towD_pred (K : ℕ) {j l : ℕ} (b : ℕ → ℕ) (h : l < j) : towD K j b l = b (l + 1) := by
  unfold towD
  rw [ite_eq_right (Nat.ne_of_lt h)]

/-! ### One level -/

/-- `Level k K n D ℓ ρ`: a distribution `ℋ_ℓ` over ordered graphs on exactly `n` vertices that
map to `T(P_ℓ(k))` and have post-degrees at most `D`, on which every proper deterministic online
algorithm uses at least `K` colours with probability at least `ρ`. -/
def Level (k K n D ℓ : ℕ) (ρ : ℝ) : Prop :=
  ∃ 𝓗 : PMF (OnlineInput n),
    (∀ I ∈ 𝓗.support, HasLabelling I.graph (LabelPoset k ℓ)) ∧
    (∀ I ∈ 𝓗.support, ∀ m < n, postDeg I.seq n m ≤ D) ∧
    ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K

/-- Post-degrees on `n` vertices are at most `n - 1`. -/
theorem postDeg_seq_le {n : ℕ} (I : OnlineInput n) (m : ℕ) : postDeg I.seq n m ≤ n - 1 := by
  unfold postDeg rank
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hsub : ((range n).filter fun v => m ∈ I.seq v) ⊆ (range n).erase 0 := by
      intro v hv
      have hm := mem_range.1 (I.seq_valid v (mem_filter.1 hv).2)
      exact mem_erase.2 ⟨by omega, (mem_filter.1 hv).1⟩
    calc _ ≤ ((range n).erase 0).card := card_le_card hsub
      _ = n - 1 := by rw [card_erase_of_mem (mem_range.2 h), card_range]

/-- A proper algorithm uses `K` colours on the clique `K_K`. -/
theorem cost_clique {K : ℕ} {A : OnlineAlg} (hA : A.IsProper) :
    (OnlineInput.ofGraph (⊤ : SimpleGraph (Fin K))).cost A = K := by
  unfold OnlineInput.cost
  rw [card_image_of_injective, card_univ, Fintype.card_fin]
  intro u v huv
  by_contra hne
  refine OnlineInput.run_ne_of_adj _ hA ?_ huv
  rw [OnlineInput.graph_ofGraph]
  exact hne

/-- **The top level:** the point mass on the arrival-ordered clique `K_K`, which maps to
`T(P_j(k))` if `K ≤ |P_j(k)|`, has post-degrees at most `K - 1`, and forces `K` colours with
probability `1`. -/
theorem level_clique {k K j : ℕ} (hP : K ≤ Fintype.card (LabelPoset k j)) :
    Level k K K (K - 1) j 1 := by
  refine ⟨PMF.pure (OnlineInput.ofGraph ⊤), fun I hI => ?_, fun I _ m _ => postDeg_seq_le I m,
    fun A hA => ?_⟩
  · rw [PMF.mem_support_pure_iff] at hI
    rw [hI, OnlineInput.graph_ofGraph]
    exact hasLabelling_clique_iff.2 hP
  · have hmem : OnlineInput.ofGraph (⊤ : SimpleGraph (Fin K)) ∈
        {I : OnlineInput K | K ≤ I.cost A} := by
      change K ≤ (OnlineInput.ofGraph (⊤ : SimpleGraph (Fin K))).cost A
      rw [cost_clique hA]
    unfold probAtLeast
    rw [PMF.toOuterMeasure_pure_apply, ite_eq_left hmem]
    simp

/-- **One oblivious blow-up** (Lemma C.2 with `δ ≡ D` and the sufficient condition for (c)): from
level `ℓ + 1` on `n` vertices with post-degrees at most `D` to level `ℓ` on `n R` vertices with
post-degrees at most `R`, losing `n D exp(-R/((K-1)D))`. -/
theorem Level.step {k K n D ℓ : ℕ} {ρ : ℝ} (hK : 2 ≤ K) (h : Level k K n D (ℓ + 1) ρ) (R : ℕ) :
    Level k K (n * R) R ℓ
      (ρ - (n : ℝ) * D * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D))) := by
  obtain ⟨𝓗, hlab, hdeg, hforce⟩ := h
  obtain ⟨h₁, h₂⟩ := oblivious_blowup (R := R) (δ := fun _ => D) (P := LabelPoset k ℓ) 𝓗 hK
    hdeg hlab hforce (cond_c_of_weak hK (fun _ _ => le_rfl) le_rfl)
  refine ⟨OB R (fun _ => D) 𝓗, h₁, fun J hJ m _ => ?_, h₂⟩
  obtain ⟨I, -, ω, rfl⟩ := mem_support_OB hJ
  exact postDeg_obInput_le I ω m

/-! ### Theorem C.3 -/

/-- The loss at level `ℓ`: `N_ℓ D_ℓ exp(-b_ℓ/((K-1) D_ℓ))`. -/
noncomputable def towLoss (K j : ℕ) (b : ℕ → ℕ) (ℓ : ℕ) : ℝ :=
  (towN K j b ℓ : ℝ) * towD K j b ℓ *
    Real.exp (-(b ℓ : ℝ) / (((K : ℝ) - 1) * towD K j b ℓ))

/-- The levels of the iterated oblivious blow-up: `ℋ_ℓ` for `ℓ = j - d`. -/
theorem level_tower {k K j : ℕ} (hK : 2 ≤ K) (hP : K ≤ Fintype.card (LabelPoset k j))
    (b : ℕ → ℕ) : ∀ d ≤ j, Level k K (towN K j b (j - d)) (towD K j b (j - d)) (j - d)
      (1 - ∑ ℓ ∈ Ioc (j - d) j, towLoss K j b ℓ) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, towN_self, towD_self, Ioc_self, sum_empty, sub_zero]
    exact level_clique hP
  | succ d ih =>
    intro hd
    have hlt : j - (d + 1) < j := by omega
    have e : j - d = j - (d + 1) + 1 := by omega
    have h := ih (by omega)
    rw [e] at h
    have h' := h.step hK (b (j - (d + 1) + 1))
    rw [towN_pred K b hlt, towD_pred K b hlt, Ioc_eq_insert hlt, sum_insert (by simp),
      ← sub_sub, sub_right_comm]
    exact h'

/-- **Theorem C.3 (iterated oblivious blow-ups).** Let `k ≥ 2`, `K ≥ 2`, `j ≥ 1` with
`|P_j(k)| ≥ K`, and `ε ∈ (0,1)`.  Put `N_j = K` and `D_j = K - 1`, and for `ℓ = j, …, 1` choose
positive integers `b_ℓ` and put `N_{ℓ-1} = N_ℓ b_ℓ` and `D_{ℓ-1} = b_ℓ` (`towN`, `towD`).  If
`∑_{ℓ=1}^{j} N_ℓ D_ℓ exp(-b_ℓ/((K-1) D_ℓ)) ≤ ε`, then there is a distribution over ordered
`k`-colourable graphs on exactly `N_0` vertices on which every proper deterministic online
algorithm uses at least `K` colours with probability at least `1 - ε`. -/
theorem oblivious_towers {k K j : ℕ} (_ : 2 ≤ k) (hK : 2 ≤ K) (_ : 1 ≤ j)
    (hP : K ≤ Fintype.card (LabelPoset k j)) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1) (b : ℕ → ℕ)
    (_ : ∀ ℓ ∈ Icc 1 j, 0 < b ℓ)
    (hstar : ∑ ℓ ∈ Icc 1 j, (towN K j b ℓ : ℝ) * towD K j b ℓ *
        Real.exp (-(b ℓ : ℝ) / (((K : ℝ) - 1) * towD K j b ℓ)) ≤ ε) :
    ProbForcing k (towN K j b 0) K (1 - ε) := by
  have h := level_tower hK hP b j le_rfl
  rw [Nat.sub_self] at h
  obtain ⟨𝓗, hlab, -, hforce⟩ := h
  refine ⟨𝓗, fun I hI => hasLabelling_labelPoset_zero_iff.1 (hlab I hI), fun A hA => ?_⟩
  have e : Ioc 0 j = Icc 1 j := by
    ext i
    simp only [mem_Ioc, mem_Icc]
    omega
  have h₁ : 1 - ε ≤ probAtLeast 𝓗 A K := by
    refine le_trans ?_ (hforce A hA)
    rw [e]
    unfold towLoss
    linarith
  have hset : {I : OnlineInput (towN K j b 0) | (K : ℝ) ≤ (I.cost A : ℝ)} =
      {I | K ≤ I.cost A} := by
    ext I
    simp
  rw [hset]
  exact ofReal_le_toOuterMeasure h₁

end Obl

end OnlineColouring
