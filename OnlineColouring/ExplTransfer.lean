module

public import OnlineColouring.OblTower
public import OnlineColouring.Transfer

/-!
# Transfer for randomized algorithms (Appendix D.5)

Appendix D.5, paragraph "Transfer for randomized algorithms": *The proof of
Theorem 1.4 also works for oblivious adversaries, with Lemma C.2 in place of Lemma 6.2.  If a
distribution on `k'`-colourable graphs with `N` vertices and post-degree at most `D` forces
`K ≥ 2` colours with probability `ρ > 0` (so `N, D ≥ 1`), `0 < ε < 1`, and the `j` of the proof
of Theorem 1.4 is at least `1` (otherwise there is nothing to do), then `j` oblivious blow-ups with
`R_1 = ⌈(K-1) D ln(j N D/ε)⌉` and `R_{i+1} = ⌈(K-1) R_i ln(j N R_1⋯R_i · R_i/ε)⌉` give a
distribution on `k`-colourable graphs that forces `K` colours with probability `ρ - ε`.*

## Formalization

* A distribution on `k'`-colourable graphs with `N` vertices and post-degree at most `D` that
  forces `K` colours with probability `ρ` is `𝓗 : PMF (OnlineInput N)` such that every
  `I` in its support has `I.graph.Colorable k'` and `postDeg I.seq N v ≤ D` for every `v < N`, and
  `ρ ≤ probAtLeast 𝓗 A K` for every proper deterministic algorithm `A` (as in Lemma C.2,
  `OblProb.lean`).
* `trR K j ε N D i` is the block size `R_i` (with `R_0 = D`) and `trN K j ε N D i` the number of
  vertices `N_i = N R_1 ⋯ R_i` after `i` blow-ups.  `trR_one`, `trR_succ_eq` and `trN_eq_prod`
  are the formulas of the paper, literally; the ceiling is `⌈·⌉₊` (a negative logarithm, which
  occurs only if `ε > j N_i R_i`, gives the block size `0`; then `ρ - ε < 0` and the claim is
  empty).
* `trDist K j ε D 𝓗 i` is the distribution after `i` oblivious blow-ups:
  `ℋ_0 = ℋ` and `ℋ_{i+1} = OB_{R_{i+1}}(ℋ_i)` with `δ ≡ R_i` (Construction C.1, `Obl.OB`).
* `j = j(k,k')` is the `j` of the proof of Theorem 1.4: the least `j` with `width(P_j(k)) ≥ k'`
  (`HasAntichain (LabelPoset k j) k'`); it is at most `lg* k' + 1` for `k ≥ 3`.

## Results

* `transfer_rand_of_antichain`: the statement for every `j` with `width(P_j(k)) ≥ k'`, for
  `K ≥ 2` and `ε > 0`: every graph in the support of `ℋ_j` is `k`-colourable, has post-degrees
  at most `R_j`, and every proper deterministic algorithm uses at least `K` colours on `ℋ_j` with
  probability at least `ρ - ε`.
* **`transfer_rand`**: the statement quoted above, with `j = j(k,k') ≤ lg* k' + 1` (`k ≥ 3`).
* `probForcing_transfer`: the statement for every `j` with `width(P_j(k)) ≥ k'` in terms of
  `ProbForcing` (post-degree bound `N - 1`).
* `loss_le`: one blow-up with block size `⌈(K-1) d ln(j n d/ε)⌉` loses at most `ε/j`
  (the sufficient condition for (c) stated after Lemma C.2).

The proof is the paper's: `k'`-colourable graphs map to `Tmpl(P_j(k))` (Lemma 5.1 (ii)), each
oblivious blow-up lowers the level by one (Lemma C.2, first conclusion) and loses at most `ε/j`
(Lemma C.2, second conclusion, with the sufficient condition for (c)), and graphs that map to
`Tmpl(P_0(k))` are `k`-colourable.  No hypothesis on `N`, `D` or `ρ` is needed, and of the
paper's `K ≥ 2`, `ρ > 0`, `0 < ε < 1` and `j ≥ 1` only `K ≥ 2` and `ε > 0` are used; the
parameters of the paragraph are correct as stated.
-/

@[expose] public section

namespace OnlineColouring

namespace Expl

open Finset
open scoped ENNReal

/-! ### The block sizes `R_i` and the sizes `N_i` -/

/-- The block size of an oblivious blow-up of a distribution on `n` vertices with post-degree at
most `d`: `⌈(K-1) d ln(j n d/ε)⌉`. -/
noncomputable def trBlock (K j : ℕ) (ε : ℝ) (n d : ℕ) : ℕ :=
  ⌈((K : ℝ) - 1) * d * Real.log (j * n * d / ε)⌉₊

/-- `(N_i, R_i)`: the number of vertices and the block size after `i` oblivious blow-ups, starting
from `(N_0, R_0) = (N, D)`. -/
noncomputable def trState (K j : ℕ) (ε : ℝ) (N D : ℕ) : ℕ → ℕ × ℕ
  | 0 => (N, D)
  | i + 1 =>
    ((trState K j ε N D i).1 * trBlock K j ε (trState K j ε N D i).1 (trState K j ε N D i).2,
      trBlock K j ε (trState K j ε N D i).1 (trState K j ε N D i).2)

/-- `N_i = N R_1 ⋯ R_i`: the number of vertices after `i` oblivious blow-ups. -/
noncomputable def trN (K j : ℕ) (ε : ℝ) (N D i : ℕ) : ℕ := (trState K j ε N D i).1

/-- `R_i`: the block size of the `i`-th oblivious blow-up, for `i ≥ 1`; `R_0 = D`.  It is also the
post-degree bound after `i` blow-ups. -/
noncomputable def trR (K j : ℕ) (ε : ℝ) (N D i : ℕ) : ℕ := (trState K j ε N D i).2

section Sizes

variable (K j : ℕ) (ε : ℝ) (N D : ℕ)

theorem trN_zero : trN K j ε N D 0 = N := rfl

theorem trR_zero : trR K j ε N D 0 = D := rfl

theorem trN_succ (i : ℕ) : trN K j ε N D (i + 1) = trN K j ε N D i * trR K j ε N D (i + 1) := rfl

theorem trR_succ (i : ℕ) : trR K j ε N D (i + 1) =
    ⌈((K : ℝ) - 1) * trR K j ε N D i *
      Real.log (j * trN K j ε N D i * trR K j ε N D i / ε)⌉₊ := rfl

/-- `N_i = N R_1 ⋯ R_i`. -/
theorem trN_eq_prod (i : ℕ) : trN K j ε N D i = N * ∏ l ∈ range i, trR K j ε N D (l + 1) := by
  induction i with
  | zero => simp [trN_zero]
  | succ i ih => rw [trN_succ, ih, prod_range_succ, Nat.mul_assoc]

/-- The paper's `R_1 = ⌈(K-1) D ln(j N D/ε)⌉`. -/
theorem trR_one :
    trR K j ε N D 1 = ⌈((K : ℝ) - 1) * D * Real.log (j * N * D / ε)⌉₊ := rfl

/-- The paper's `R_{i+1} = ⌈(K-1) R_i ln(j N R_1⋯R_i · R_i/ε)⌉`. -/
theorem trR_succ_eq (i : ℕ) : trR K j ε N D (i + 1) =
    ⌈((K : ℝ) - 1) * trR K j ε N D i *
      Real.log (j * N * (∏ l ∈ range i, (trR K j ε N D (l + 1) : ℝ)) * trR K j ε N D i / ε)⌉₊ := by
  have h : (j : ℝ) * (trN K j ε N D i : ℝ) * trR K j ε N D i / ε =
      j * N * (∏ l ∈ range i, (trR K j ε N D (l + 1) : ℝ)) * trR K j ε N D i / ε := by
    rw [trN_eq_prod]
    push_cast
    ring
  rw [trR_succ, h]

end Sizes

/-- **One blow-up loses at most `ε/j`.** With the block size `R = ⌈(K-1) d ln(j n d/ε)⌉`, the
quantity `n d exp(-R/((K-1)d))` of the sufficient condition for (c) of Lemma C.2 is at most
`ε/j`. -/
theorem loss_le {K j : ℕ} (hK : 2 ≤ K) (hj : 1 ≤ j) {ε : ℝ} (hε : 0 < ε) (n d : ℕ) :
    (n : ℝ) * d * Real.exp (-(trBlock K j ε n d : ℝ) / (((K : ℝ) - 1) * d)) ≤ ε / j := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hεj : 0 ≤ ε / j := (div_pos hε hj').le
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hεj
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simpa using hεj
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hK' : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have ha : (0 : ℝ) < ((K : ℝ) - 1) * d := mul_pos hK' hd'
  have hxpos : (0 : ℝ) < j * n * d / ε := by positivity
  have hceil : ((K : ℝ) - 1) * d * Real.log (j * n * d / ε) ≤ (trBlock K j ε n d : ℝ) :=
    Nat.le_ceil _
  have h1 : -(trBlock K j ε n d : ℝ) / (((K : ℝ) - 1) * d) ≤ -Real.log (j * n * d / ε) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ ha]
    linarith
  have hexp : Real.exp (-(trBlock K j ε n d : ℝ) / (((K : ℝ) - 1) * d)) ≤
      (j * n * d / ε)⁻¹ :=
    calc Real.exp (-(trBlock K j ε n d : ℝ) / (((K : ℝ) - 1) * d))
        ≤ Real.exp (-Real.log (j * n * d / ε)) := Real.exp_le_exp.2 h1
      _ = (j * n * d / ε)⁻¹ := by rw [Real.exp_neg, Real.exp_log hxpos]
  calc (n : ℝ) * d * Real.exp (-(trBlock K j ε n d : ℝ) / (((K : ℝ) - 1) * d))
      ≤ n * d * (j * n * d / ε)⁻¹ := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = ε / j := by field_simp

/-! ### Levels -/

/-- `IsLevel k K ℓ ρ D 𝓗`: the distribution `𝓗` over ordered graphs on exactly `n` vertices is
supported on graphs that map to `T(P_ℓ(k))` and have post-degrees at most `D`, and every proper
deterministic online algorithm uses at least `K` colours on it with probability at least `ρ`. -/
def IsLevel (k K ℓ : ℕ) (ρ : ℝ) (D : ℕ) {n : ℕ} (𝓗 : PMF (OnlineInput n)) : Prop :=
  (∀ I ∈ 𝓗.support, HasLabelling I.graph (LabelPoset k ℓ)) ∧
    (∀ I ∈ 𝓗.support, ∀ v < n, postDeg I.seq n v ≤ D) ∧
    ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K

theorem IsLevel.mono {k K ℓ D n : ℕ} {ρ ρ' : ℝ} {𝓗 : PMF (OnlineInput n)}
    (h : IsLevel k K ℓ ρ D 𝓗) (hρ : ρ' ≤ ρ) : IsLevel k K ℓ ρ' D 𝓗 :=
  ⟨h.1, h.2.1, fun A hA => hρ.trans (h.2.2 A hA)⟩

/-- **One oblivious blow-up** (Lemma C.2 with `δ ≡ D` and the sufficient condition for (c)). -/
theorem IsLevel.step {k K ℓ D n : ℕ} {ρ : ℝ} {𝓗 : PMF (OnlineInput n)} (hK : 2 ≤ K)
    (h : IsLevel k K (ℓ + 1) ρ D 𝓗) (R : ℕ) :
    IsLevel k K ℓ (ρ - (n : ℝ) * D * Real.exp (-(R : ℝ) / (((K : ℝ) - 1) * D))) R
      (Obl.OB R (fun _ => D) 𝓗) := by
  obtain ⟨hlab, hdeg, hforce⟩ := h
  obtain ⟨h₁, h₂⟩ := Obl.oblivious_blowup (R := R) (δ := fun _ => D) (P := LabelPoset k ℓ) 𝓗 hK
    hdeg hlab hforce (Obl.cond_c_of_weak hK (fun _ _ => le_rfl) le_rfl)
  refine ⟨h₁, fun J hJ v _ => ?_, h₂⟩
  obtain ⟨I, -, ω, rfl⟩ := Obl.mem_support_OB hJ
  exact Obl.postDeg_obInput_le I ω v

/-! ### The iterated oblivious blow-up -/

/-- The distribution after `i` oblivious blow-ups with the block sizes `R_1, …, R_i`:
`ℋ_0 = ℋ` and `ℋ_{i+1} = OB_{R_{i+1}}(ℋ_i)` with the post-degree bound `δ ≡ R_i`. -/
noncomputable def trDist (K j : ℕ) (ε : ℝ) {N : ℕ} (D : ℕ) (𝓗 : PMF (OnlineInput N)) :
    (i : ℕ) → PMF (OnlineInput (trN K j ε N D i))
  | 0 => 𝓗
  | i + 1 => Obl.OB (trR K j ε N D (i + 1)) (fun _ => trR K j ε N D i) (trDist K j ε D 𝓗 i)

/-- After `i ≤ j` blow-ups the graphs map to `T(P_{j-i}(k))`, the post-degrees are at most `R_i`,
and the forcing probability is at least `ρ - i ε/j`. -/
theorem isLevel_trDist {k K j N D : ℕ} (hK : 2 ≤ K) {ε ρ : ℝ} (hε : 0 < ε)
    {𝓗 : PMF (OnlineInput N)} (h : IsLevel k K j ρ D 𝓗) :
    ∀ i ℓ, i + ℓ = j →
      IsLevel k K ℓ (ρ - i * (ε / j)) (trR K j ε N D i) (trDist K j ε D 𝓗 i) := by
  intro i
  induction i with
  | zero =>
    intro ℓ hℓ
    rw [Nat.zero_add] at hℓ
    have e : ρ - ((0 : ℕ) : ℝ) * (ε / j) = ρ := by simp
    rw [e, hℓ]
    exact h
  | succ i ih =>
    intro ℓ hℓ
    have hj : 1 ≤ j := by omega
    have h1 := (ih (ℓ + 1) (by omega)).step hK (trR K j ε N D (i + 1))
    have hloss : (trN K j ε N D i : ℝ) * trR K j ε N D i *
        Real.exp (-(trR K j ε N D (i + 1) : ℝ) / (((K : ℝ) - 1) * trR K j ε N D i)) ≤ ε / j :=
      loss_le hK hj hε _ _
    refine IsLevel.mono h1 ?_
    push_cast
    linarith

/-! ### The transfer -/

/-- **Transfer for randomized algorithms, for every sufficient number of levels.** Let `K ≥ 2`,
`ε > 0`, and let `j` satisfy `width(P_j(k)) ≥ k'`.  If the distribution `ℋ` on `k'`-colourable
ordered graphs with `N` vertices and post-degree at most `D` forces `K` colours with probability
`ρ`, then `j` oblivious blow-ups with the block sizes `R_1, …, R_j` give a distribution `ℋ_j` on
`k`-colourable graphs with `N R_1 ⋯ R_j` vertices and post-degree at most `R_j` that forces `K`
colours with probability `ρ - ε`. -/
theorem transfer_rand_of_antichain {k k' j K N D : ℕ} (hK : 2 ≤ K)
    (hj : HasAntichain (LabelPoset k j) k') {ε ρ : ℝ} (hε : 0 < ε) (𝓗 : PMF (OnlineInput N))
    (hcol : ∀ I ∈ 𝓗.support, I.graph.Colorable k')
    (hdeg : ∀ I ∈ 𝓗.support, ∀ v < N, postDeg I.seq N v ≤ D)
    (hforce : ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K) :
    (∀ J ∈ (trDist K j ε D 𝓗 j).support, J.graph.Colorable k) ∧
      (∀ J ∈ (trDist K j ε D 𝓗 j).support, ∀ v < trN K j ε N D j,
        postDeg J.seq (trN K j ε N D j) v ≤ trR K j ε N D j) ∧
      ∀ A : OnlineAlg, A.IsProper → ρ - ε ≤ probAtLeast (trDist K j ε D 𝓗 j) A K := by
  obtain ⟨Ach, hAch, hcard⟩ := hj
  have h0 : IsLevel k K j ρ D 𝓗 :=
    ⟨fun I hI => hasLabelling_of_colorable hAch hcard.ge (hcol I hI), hdeg, hforce⟩
  obtain ⟨h1, h2, h3⟩ := isLevel_trDist hK hε h0 j 0 (Nat.add_zero j)
  refine ⟨fun J hJ => hasLabelling_labelPoset_zero_iff.1 (h1 J hJ), h2,
    fun A hA => le_trans ?_ (h3 A hA)⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · have e : (j : ℝ) = 0 := by exact_mod_cast hj0
    rw [e, zero_mul, sub_zero]
    linarith
  · have hj' : (0 : ℝ) < j := by exact_mod_cast hj0
    have e : (j : ℝ) * (ε / j) = ε := by field_simp
    rw [e]

/-- **Transfer for randomized algorithms** (Appendix D.5).  Let `k ≥ 3`.
For `j = j(k,k')`, the least `j` with `width(P_j(k)) ≥ k'` (the `j` of the proof of Theorem 1.4;
it is at most `lg* k' + 1`): if a distribution `ℋ` on `k'`-colourable graphs with `N` vertices
and post-degree at most `D` forces `K ≥ 2` colours with probability `ρ`, and `ε > 0` (the paper's
hypotheses `ε < 1`, `ρ > 0` and `j ≥ 1` are not needed), then `j` oblivious blow-ups with
`R_1 = ⌈(K-1) D ln(jND/ε)⌉` and `R_{i+1} = ⌈(K-1) R_i ln(j N R_1⋯R_i · R_i/ε)⌉` (`trR_one`,
`trR_succ_eq`) give a distribution on `k`-colourable graphs, with `N R_1 ⋯ R_j` vertices
(`trN_eq_prod`), that forces `K` colours with probability `ρ - ε`. -/
theorem transfer_rand {k k' : ℕ} (hk : 3 ≤ k) :
    ∃ j ≤ logStar k' + 1, HasAntichain (LabelPoset k j) k' ∧
      (∀ i < j, ¬ HasAntichain (LabelPoset k i) k') ∧
      ∀ (K N D : ℕ) (ε ρ : ℝ) (𝓗 : PMF (OnlineInput N)), 2 ≤ K → 0 < ε →
        (∀ I ∈ 𝓗.support, I.graph.Colorable k') →
        (∀ I ∈ 𝓗.support, ∀ v < N, postDeg I.seq N v ≤ D) →
        (∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K) →
        (∀ J ∈ (trDist K j ε D 𝓗 j).support, J.graph.Colorable k) ∧
          ∀ A : OnlineAlg, A.IsProper → ρ - ε ≤ probAtLeast (trDist K j ε D 𝓗 j) A K := by
  classical
  have hex : ∃ j, HasAntichain (LabelPoset k j) k' := ⟨_, hasAntichain_labelPoset_logStar hk k'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (hasAntichain_labelPoset_logStar hk k'),
    Nat.find_spec hex, fun i hi => Nat.find_min hex hi,
    fun K N D ε ρ 𝓗 hK hε hcol hdeg hforce => ?_⟩
  obtain ⟨h1, -, h3⟩ :=
    transfer_rand_of_antichain hK (Nat.find_spec hex) hε 𝓗 hcol hdeg hforce
  exact ⟨h1, h3⟩

/-- **Transfer for randomized algorithms, in terms of `ProbForcing`.** If some distribution over
`k'`-colourable ordered graphs on `N` vertices forces `K ≥ 2` colours with probability `ρ` and
`width(P_j(k)) ≥ k'`, then for every `ε > 0` some distribution over `k`-colourable ordered graphs
on `N R_1 ⋯ R_j` vertices forces `K` colours with probability `ρ - ε`; here the block sizes are
those of the paper with `D = N - 1`, which bounds every post-degree. -/
theorem probForcing_transfer {k k' j K N : ℕ} (hK : 2 ≤ K)
    (hj : HasAntichain (LabelPoset k j) k') {ε ρ : ℝ} (hε : 0 < ε)
    (h : ProbForcing k' N K ρ) : ProbForcing k (trN K j ε N (N - 1) j) K (ρ - ε) := by
  obtain ⟨𝓗, hcol, hD⟩ := h
  have hset : ∀ (n : ℕ) (A : OnlineAlg),
      {I : OnlineInput n | (K : ℝ) ≤ (I.cost A : ℝ)} = {I | K ≤ I.cost A} := by
    intro n A
    ext I
    simp
  have hforce : ∀ A : OnlineAlg, A.IsProper → ρ ≤ probAtLeast 𝓗 A K := by
    intro A hA
    have := hD A hA
    rw [hset] at this
    exact (ENNReal.ofReal_le_iff_le_toReal (toOuterMeasure_ne_top 𝓗 _)).1 this
  obtain ⟨h1, -, h3⟩ := transfer_rand_of_antichain hK hj hε 𝓗 hcol
    (fun I _ v _ => Obl.postDeg_seq_le I v) hforce
  refine ⟨trDist K j ε (N - 1) 𝓗 j, h1, fun A hA => ?_⟩
  rw [hset]
  exact ofReal_le_toOuterMeasure (h3 A hA)

end Expl

end OnlineColouring
