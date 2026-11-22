module

public import OnlineColouring.LogStarGeneric
public import OnlineColouring.RjmGraph
public import OnlineColouring.UExact
public import OnlineColouring.KnownGame
public import OnlineColouring.ExplKnown

/-!
# Theorem 1.1, Theorem 1.3 for `G′`, and Corollary 8.6

The main theorems that come from uniform towers (Section 8.4).  The proofs follow the paper:
they go through the random wiring `R_j(m)` of Construction 8.1 (`EΩ`, `UWiringE.lean`), Lemma 8.2
for it (`RjmGraph.lean`), Theorem 8.5 (i) and the first statement of Corollary 8.6 for it
(`UExact.lean`), and they choose the parameters as in the paper (`LogStarGeneric.lean`: the
number of levels is `Rjm.jMin k n`, the least `j ≥ 1` with `|P_j(k)| ≥ n`, and Lemma A.1 gives
the second bounds).

Supporting statements, in the namespace `Rjm`:

* Theorem 8.5 (ii) in per-algorithm form: `Rjm.exists_numColsE_ge` (against every proper
  algorithm some wiring has at least `X_m` colours, because the mean over the wirings is at least
  `X_m`) and `Rjm.uniform_tower_detE`.  The adversary of Theorem 8.5 (ii) itself is `Expl.adv`
  (`ExplAdv.lean`).
* The known graph: `χ_ol(G_j(m)) ≥ ⌈X_m⌉` is `Expl.Gjm_onlineChromaticAtLeast` (`ExplKnown.lean`),
  proved as in the paper from the adversary of Theorem 8.5 (ii), every play of which is a
  presentation of `G_j(m)`.  `Rjm.Gjm_randKnownAtLeast` is the randomized known-graph bound `X_m`
  (Yao's principle over `R_j(m)`, every outcome of which presents `G_j(m)`), and
  `Rjm.uniform_known_graph` combines the two for `G′ = G_j(m)` plus isolated vertices, which is
  `k`-colourable and triangle-free.  `Rjm.Gjm_onlineChromaticAtLeast` is a second proof of the
  first bound, by averaging over the wirings; it is not used.
* `Rjm.chiRand_three_ge_uniform`, `Rjm.chiRand_ge_uniform_of_four_le`,
  `Rjm.chiRand_three_ge_rpow`, `Rjm.chiRand_ge_rpow_of_four_le`: the bounds of Theorem 1.1 for
  `χ^rand`, one at a time; `Rjm.probForcing_rpow_div`: the chain (8.2) for Corollary 8.6.

The theorems:

* **Theorem 1.1**: `main_logStar_three` (`k = 3`) and `main_logStar_of_four_le` (`k ≥ 4`), each
  with all statements of the theorem.  The bounds for `χ^det` alone, which follow from
  `χ^det ≥ χ^rand` as in the paper, are `chiDet_three_ge_uniform`,
  `chiDet_ge_uniform_of_four_le`, `chiDet_three_ge_rpow` and `chiDet_ge_rpow_of_four_le`.
* **Theorem 1.3, the graph `G′`**: `known_graph_uniform_three`, `known_graph_uniform_of_four_le`,
  and for `N ≥ 2^406` (`k ≥ 4`: `N ≥ 2^201`) `known_graph_uniform_three_large`,
  `known_graph_uniform_of_four_le_large`.  Since `χ_ol` is an integer, `χ_ol(G′) ≥ x` is stated as
  `OnlineChromaticAtLeast G′ ⌈x⌉₊`.  The statement of the theorem with `χ_ol` as a number, with
  `G` and `G′` together and with one graph `G′` for both bounds is `Paper.known_graphs_three`,
  `Paper.known_graphs_of_four_le` (`PaperStatements.lean`).
* **Corollary 8.6, second statement**: `probForcing_logStar_three`,
  `probForcing_logStar_of_four_le`.  The first statement is `uniform_tower_eps_probE`
  (`UExact.lean`).
-/

@[expose] public section

namespace OnlineColouring

open Finset Real

/-! ### The hypotheses of the generic argument for `χ^rand` -/

theorem chiRand_hmono : ∀ (k n : ℕ) (x x' : ℝ), 1 ≤ k → ChiRandAtLeast k n x → x' ≤ x →
    ChiRandAtLeast k n x' :=
  fun _ _ _ _ _ h hx => h.le_of_le hx

theorem chiRand_hpad : ∀ (k n n' : ℕ) (x : ℝ), 1 ≤ k → ChiRandAtLeast k n x → n ≤ n' →
    ChiRandAtLeast k n' x :=
  fun _ _ _ _ hk h hn => h.pad hn hk

theorem chiRand_hbase : ∀ k n, 1 ≤ k → 1 ≤ n → ChiRandAtLeast k n 1 :=
  fun _ _ hk hn => chiRandAtLeast_one hk hn

namespace Rjm

/-! ### Theorem 8.5 (ii) for `R_j(m)`, per algorithm -/

/-- Against every proper algorithm, some wiring of `R_j(m)` has at least `X_m` colours, because
the mean over the wirings is at least `X_m` (`avg_numCols_geE`, Theorem 8.5 (i)). -/
theorem exists_numColsE_ge {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (alg : OnlineAlg)
    (halg : alg.IsProper) : ∃ ω : EΩ m j (2 * m), uniformBound m ≤ numColsE alg ω := by
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  by_contra hcon
  push Not at hcon
  have havg := avg_numCols_geE (j := j) hm hj alg halg
  have hQ : (0 : ℝ) < Fintype.card (EΩ m j (2 * m)) := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hQ] at havg
  have hlt : ∑ ω : EΩ m j (2 * m), (numColsE alg ω : ℝ) <
      ∑ _ω : EΩ m j (2 * m), uniformBound m :=
    sum_lt_sum_of_nonempty univ_nonempty fun ω _ => hcon ω
  rw [sum_const, card_univ, nsmul_eq_mul] at hlt
  linarith

/-- **Theorem 8.5 (ii) through `R_j(m)`, per algorithm.** For `j ≥ 1`, `m ≥ 2` and
`m ≤ |P_j(k)|`, every proper deterministic algorithm uses at least `⌈(2m+1)/(4(1+ln 4m))⌉` colours
on some `k`-colourable input on `m (2m)^j` vertices (`ChiDetAtLeast`); the proof takes a wiring of
the uniform tower. -/
theorem uniform_tower_detE {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) :
    ChiDetAtLeast k (m * (2 * m) ^ j) ⌈uniformBound m⌉₊ := by
  intro alg halg
  have hA : 0 < 2 * m := by omega
  obtain ⟨ω, hω⟩ := exists_numColsE_ge hm hj alg halg
  have hcol := uInputE_colorable ω hA hP
  have hk : 1 ≤ k :=
    one_le_of_colorable (by rw [utSize_eq]; exact Nat.mul_pos (by omega) (pow_pos hA j)) hcol
  have hK : ⌈uniformBound m⌉₊ ≤ (uInputE hA ω).cost alg := by
    rw [numColsE_eq_cost]
    exact Nat.ceil_le.2 hω
  refine ⟨padInput (uInputE hA ω) _, colorable_padInput hk hcol _, ?_⟩
  exact hK.trans (cost_le_padInput (utSize_eq (2 * m) m j).le _ alg)

/-! ### The known graph `G_j(m)` -/

/-- **`χ_ol(G_j(m)) ≥ ⌈X_m⌉`, by averaging**: every proper deterministic online algorithm, which
may depend on the graph, uses at least `⌈(2m+1)/(4(1+ln 4m))⌉` colours on some presentation of
`G_j(m)`, namely on some wiring of `R_j(m)`.  The paper's proof, from the adversary of
Theorem 8.5 (ii), is `Expl.Gjm_onlineChromaticAtLeast`; Theorem 1.3 is derived from that one. -/
theorem Gjm_onlineChromaticAtLeast {j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m) :
    OnlineChromaticAtLeast (Gjm j m) ⌈uniformBound m⌉₊ := by
  intro alg halg
  have hA : 0 < 2 * m := by omega
  obtain ⟨ω, hω⟩ := exists_numColsE_ge hm hj alg halg
  obtain ⟨e⟩ := uInputE_iso_Gjm hA ω
  obtain ⟨I, ⟨e'⟩, hc⟩ := OnlineInput.exists_cast (utSize_eq (2 * m) m j) (uInputE hA ω)
  refine ⟨I, ⟨e'.trans e⟩, ?_⟩
  rw [hc, numColsE_eq_cost]
  exact Nat.ceil_le.2 hω

/-- **Randomized algorithms on `G_j(m)`**: every proper randomized online algorithm, which may
depend on the graph, has expected cost at least `(2m+1)/(4(1+ln 4m))` on some presentation of
`G_j(m)`: Yao's principle over `R_j(m)`, every outcome of which presents `G_j(m)`. -/
theorem Gjm_randKnownAtLeast {j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m) :
    RandKnownAtLeast (Gjm j m) (uniformBound m) := by
  intro μ hμ
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  have hA : 0 < 2 * m := by omega
  obtain ⟨I, hID, hI⟩ := exists_support_le_expCost
    (unifInput fun ω : EΩ m j (2 * m) => uInputE hA ω) (fun alg halg => by
      rw [detExpCost_unifInput]
      simp only [numColsE_eq_cost hA]
      exact avg_numCols_geE hm hj alg halg) μ hμ
  obtain ⟨ω, rfl⟩ := mem_support_unifInput hID
  obtain ⟨e⟩ := uInputE_iso_Gjm hA ω
  obtain ⟨I', ⟨e'⟩, hc⟩ := OnlineInput.exists_cast (utSize_eq (2 * m) m j) (uInputE hA ω)
  exact ⟨I', ⟨e'.trans e⟩, hI.trans (expCost_mono μ fun A => (hc A).ge)⟩

/-- **Theorem 1.3, the graph `G′`, before the choice of parameters.** For `j ≥ 1`, `m ≥ 2`,
`m ≤ |P_j(k)|` and `N ≥ m (2m)^j`, the graph `G′ = G_j(m)` plus `N - m(2m)^j` isolated vertices is
`k`-colourable and triangle-free, `χ_ol(G′) ≥ ⌈X_m⌉` (every play of the adversary of
Theorem 8.5 (ii) is a presentation of `G_j(m)`), and every randomized algorithm that knows `G′` has
expected cost at least `X_m` on some presentation of `G′` (every outcome of `R_j(m)` is a
presentation of `G_j(m)`). -/
theorem uniform_known_graph {k j m N : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) (hN : m * (2 * m) ^ j ≤ N) :
    (padGraph (Gjm j m) N).Colorable k ∧ (padGraph (Gjm j m) N).CliqueFree 3 ∧
      OnlineChromaticAtLeast (padGraph (Gjm j m) N) ⌈uniformBound m⌉₊ ∧
      RandKnownAtLeast (padGraph (Gjm j m) N) (uniformBound m) := by
  have hc := Gjm_colorable (j := j) (by omega : 1 ≤ m) hP
  have hk : 1 ≤ k := one_le_of_colorable (Nat.mul_pos (by omega) (pow_pos (by omega) j)) hc
  exact ⟨padGraph_colorable hk hc, padGraph_cliqueFree (Gjm_cliqueFree (by omega) hj),
    (Expl.Gjm_onlineChromaticAtLeast hj hm).pad hN, (Gjm_randKnownAtLeast hj hm).pad hN⟩

theorem knownQ_uniform {k j m : ℕ} (hj : 1 ≤ j) (hm : 2 ≤ m)
    (hP : m ≤ Fintype.card (LabelPoset k j)) : KnownQ k (m * (2 * m) ^ j) (uniformBound m) :=
  ⟨Gjm j m, Gjm_colorable (by omega) hP, Gjm_cliqueFree (by omega) hj,
    Expl.Gjm_onlineChromaticAtLeast hj hm, Gjm_randKnownAtLeast hj hm⟩

/-! ### The uniform tower as the hypothesis `hcore` of the generic argument -/

theorem chiRand_hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
    ChiRandAtLeast k (m * (2 * m) ^ j) (uniformBound m) :=
  fun _ _ _ _ hj hm hP => uniform_tower_randE hj hm hP

theorem knownQ_hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m → m ≤ Fintype.card (LabelPoset k j) →
    KnownQ k (m * (2 * m) ^ j) (uniformBound m) :=
  fun _ _ _ _ hj hm hP => knownQ_uniform hj hm hP

/-! ### Theorem 1.1 for `χ^rand` -/

/-- **Theorem 1.1, `k = 3`:** `χ^rand_3(n) ≥ n^{1/(L+2)} / (8 (1 + ln 4n))` for `n ≥ 3`. -/
theorem chiRand_three_ge_uniform {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand 3 n :=
  (le_chiRand_iff (by norm_num)).2 (logStar_three ChiRandAtLeast chiRand_hmono
    chiRand_hpad chiRand_hcore chiRand_hbase hn)

/-- **Theorem 1.1, `k ≥ 4`:** `χ^rand_k(n) ≥ n^{1/L} / (8 (1 + ln 4n))` for `n ≥ 3`. -/
theorem chiRand_ge_uniform_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand k n :=
  (le_chiRand_iff (by omega)).2 (logStar_of_four_le ChiRandAtLeast chiRand_hmono
    chiRand_hpad chiRand_hcore chiRand_hbase hk hn)

/-- **Theorem 1.1, `k = 3`, second sentence:**
`χ^det_3(n) ≥ χ^rand_3(n) ≥ n^{1/(L+3)}` for `n ≥ 2^406`. -/
theorem chiRand_three_ge_rpow {n : ℕ} (hn : 2 ^ 406 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 3 : ℝ)) ≤ chiRand 3 n ∧ chiRand 3 n ≤ chiDet 3 n :=
  ⟨(le_chiRand_iff (by norm_num)).2 (logStar_three_large ChiRandAtLeast chiRand_hmono
    chiRand_hpad chiRand_hcore hn), chiRand_le_chiDet (by norm_num)⟩

/-- **Theorem 1.1, `k ≥ 4`, second sentence:**
`χ^det_k(n) ≥ χ^rand_k(n) ≥ n^{1/(L+1)}` for `n ≥ 2^201`. -/
theorem chiRand_ge_rpow_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 1 : ℝ)) ≤ chiRand k n ∧ chiRand k n ≤ chiDet k n :=
  ⟨(le_chiRand_iff (by omega)).2 (logStar_of_four_le_large ChiRandAtLeast chiRand_hmono
    chiRand_hpad chiRand_hcore hk hn), chiRand_le_chiDet (by omega)⟩

/-! ### The chain (8.2) for Corollary 8.6 -/

/-- **(8.2) for the corollary, through `R_j(m)`.** If `|P_j(k)| ≥ n ≥ 1`, `j ≥ 1` and
`0 < ε < 1`, the random wiring `R_j(m)` with `m = ⌊(n/2^j)^{1/(j+1)}⌋`, followed by isolated
vertices, forces `n^{1/(j+1)}/(8(1+ln(4n/ε)))` colours with probability at least `1 - ε` (and the
edgeless input does if `m ≤ 1`); the statement is
`ProbForcing k n (n^{1/(j+1)}/(8(1+ln(4n/ε)))) (1 - ε)`. -/
theorem probForcing_rpow_div {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hnP : n ≤ Fintype.card (LabelPoset k j)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing k n ((n : ℝ) ^ ((1 : ℝ) / ((j : ℝ) + 1)) / (8 * (1 + Real.log (4 * n / ε))))
      (1 - ε) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (4 * n / ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε0]
    linarith)
  rcases lt_or_ge (levelM n j) 2 with hM | hM
  · -- `m ≤ 1`: the bound is below `1`
    refine (probForcing_one hk hn (by linarith)).of_le ?_
    have h1 := rpow_le_two_mul_levelM hn j
    rw [div_le_one (by linarith)]
    linarith
  · have hnM := two_pow_mul_levelM_pow n j
    have hMn := levelM_le hn j
    set M := levelM n j
    have hm2 : 2 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast hM)
    have hmM : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le (by linarith)
    have hmn : ⌊M⌋₊ ≤ n := by exact_mod_cast hmM.trans hMn
    have hsize : ⌊M⌋₊ * (2 * ⌊M⌋₊) ^ j ≤ n := by
      have h : ((⌊M⌋₊ * (2 * ⌊M⌋₊) ^ j : ℕ) : ℝ) ≤ n := by
        push_cast
        rw [← hnM]
        calc ((⌊M⌋₊ : ℕ) : ℝ) * (2 * (⌊M⌋₊ : ℝ)) ^ j = 2 ^ j * (⌊M⌋₊ : ℝ) ^ (j + 1) := by ring
          _ ≤ 2 ^ j * M ^ (j + 1) := by gcongr
      exact_mod_cast h
    exact ((uniform_tower_epsE hj hm2 (hmn.trans hnP) hε0 hε1).pad hsize hk).of_le
      (rpow_div_le_epsBound hn hM hε0 hε1)

end Rjm

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1 for `χ^det`, `k = 3`:** `χ^det_3(n) ≥ n^{1/(L+2)} / (8 (1 + ln 4n))`, from
`χ^det ≥ χ^rand`. -/
theorem chiDet_three_ge_uniform {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiDet 3 n :=
  (Rjm.chiRand_three_ge_uniform hn).trans (chiRand_le_chiDet (by norm_num))

/-- **Theorem 1.1 for `χ^det`, `k ≥ 4`:** `χ^det_k(n) ≥ n^{1/L} / (8 (1 + ln 4n))`. -/
theorem chiDet_ge_uniform_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiDet k n :=
  (Rjm.chiRand_ge_uniform_of_four_le hk hn).trans (chiRand_le_chiDet (by omega))

/-- **Theorem 1.1 for `χ^det`, `k = 3`:** `χ^det_3(n) ≥ n^{1/(L+3)}` for `n ≥ 2^406`. -/
theorem chiDet_three_ge_rpow {n : ℕ} (hn : 2 ^ 406 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 3 : ℝ)) ≤ chiDet 3 n :=
  (Rjm.chiRand_three_ge_rpow hn).1.trans (Rjm.chiRand_three_ge_rpow hn).2

/-- **Theorem 1.1 for `χ^det`, `k ≥ 4`:** `χ^det_k(n) ≥ n^{1/(L+1)}` for `n ≥ 2^201`. -/
theorem chiDet_ge_rpow_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 1 : ℝ)) ≤ chiDet k n :=
  (Rjm.chiRand_ge_rpow_of_four_le hk hn).1.trans (Rjm.chiRand_ge_rpow_of_four_le hk hn).2

/-- **Theorem 1.1, `k = 3`, all statements together.** -/
theorem main_logStar_three {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand 3 n ∧
      chiRand 3 n ≤ chiDet 3 n ∧
      (2 ^ 406 ≤ n → (n : ℝ) ^ (1 / (logStar n + 3 : ℝ)) ≤ chiRand 3 n) :=
  ⟨Rjm.chiRand_three_ge_uniform hn, chiRand_le_chiDet (by norm_num),
    fun h => (Rjm.chiRand_three_ge_rpow h).1⟩

/-- **Theorem 1.1, `k ≥ 4`, all statements together.** -/
theorem main_logStar_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) :
    (n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n))) ≤ chiRand k n ∧
      chiRand k n ≤ chiDet k n ∧
      (2 ^ 201 ≤ n → (n : ℝ) ^ (1 / (logStar n + 1 : ℝ)) ≤ chiRand k n) :=
  ⟨Rjm.chiRand_ge_uniform_of_four_le hk hn, chiRand_le_chiDet (by omega),
    fun h => (Rjm.chiRand_ge_rpow_of_four_le hk h).1⟩

/-! ### Theorem 1.3, the graph `G′` -/

/-- **Theorem 1.3 (known graphs), the graph `G′`, `k = 3`.** -/
theorem known_graph_uniform_three {N : ℕ} (hN : 3 ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable 3 ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G
        ⌈(N : ℝ) ^ (1 / (logStar N + 2 : ℝ)) / (8 * (1 + Real.log (4 * N)))⌉₊ ∧
      RandKnownAtLeast G ((N : ℝ) ^ (1 / (logStar N + 2 : ℝ)) / (8 * (1 + Real.log (4 * N)))) :=
  Rjm.logStar_three KnownQ knownQ_hmono knownQ_hpad Rjm.knownQ_hcore knownQ_hbase hN

/-- **Theorem 1.3 (known graphs), the graph `G′`, `k ≥ 4`.** -/
theorem known_graph_uniform_of_four_le {N k : ℕ} (hk : 4 ≤ k) (hN : 3 ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G
        ⌈(N : ℝ) ^ (1 / (logStar N : ℝ)) / (8 * (1 + Real.log (4 * N)))⌉₊ ∧
      RandKnownAtLeast G ((N : ℝ) ^ (1 / (logStar N : ℝ)) / (8 * (1 + Real.log (4 * N)))) :=
  Rjm.logStar_of_four_le KnownQ knownQ_hmono knownQ_hpad Rjm.knownQ_hcore knownQ_hbase hk hN

/-- **Theorem 1.3 (known graphs), the graph `G′`, `k = 3`, `N ≥ 2^406`:** both bounds with
`N^{1/(L+3)}`. -/
theorem known_graph_uniform_three_large {N : ℕ} (hN : 2 ^ 406 ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable 3 ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G ⌈(N : ℝ) ^ (1 / (logStar N + 3 : ℝ))⌉₊ ∧
      RandKnownAtLeast G ((N : ℝ) ^ (1 / (logStar N + 3 : ℝ))) :=
  Rjm.logStar_three_large KnownQ knownQ_hmono knownQ_hpad Rjm.knownQ_hcore hN

/-- **Theorem 1.3 (known graphs), the graph `G′`, `k ≥ 4`, `N ≥ 2^201`:** both bounds with
`N^{1/(L+1)}`. -/
theorem known_graph_uniform_of_four_le_large {N k : ℕ} (hk : 4 ≤ k) (hN : 2 ^ 201 ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G ⌈(N : ℝ) ^ (1 / (logStar N + 1 : ℝ))⌉₊ ∧
      RandKnownAtLeast G ((N : ℝ) ^ (1 / (logStar N + 1 : ℝ))) :=
  Rjm.logStar_of_four_le_large KnownQ knownQ_hmono knownQ_hpad Rjm.knownQ_hcore hk hN

/-! ### Corollary 8.6, second statement -/

/-- **Corollary 8.6 (forcing with high probability), `k = 3`.** For every `n ≥ 3`, every
`0 < ε < 1` and `L = lg* n` there is a distribution over `3`-colourable online inputs on `n`
vertices on which every proper deterministic online algorithm uses at least
`n^{1/(L+2)}/(8(1+ln(4n/ε)))` colours with probability at least `1 - ε`. -/
theorem probForcing_logStar_three {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing 3 n ((n : ℝ) ^ (1 / (logStar n + 2 : ℝ)) / (8 * (1 + Real.log (4 * n / ε))))
      (1 - ε) := by
  obtain ⟨hj, hnP⟩ := Rjm.jMin_spec (k := 3) (n := n) (J := logStar n + 1) (by omega)
    (le_card_labelPoset_three (by omega))
  have hjL := Rjm.jMin_three_le (n := n) (by omega)
  refine (Rjm.probForcing_rpow_div (k := 3) (j := Rjm.jMin 3 n) (by norm_num) (by omega) hj hnP
    hε0 hε1).of_le ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (4 * n / ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε0]
    linarith)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Rjm.rpow_inv_anti (by omega) (by positivity)
  have : ((Rjm.jMin 3 n : ℕ) : ℝ) ≤ (logStar n : ℝ) + 1 := by exact_mod_cast hjL
  linarith

/-- **Corollary 8.6 (forcing with high probability), `k ≥ 4`.** For every `n ≥ 3`, every
`0 < ε < 1` and `L = lg* n` there is a distribution over `k`-colourable online inputs on `n`
vertices on which every proper deterministic online algorithm uses at least
`n^{1/L}/(8(1+ln(4n/ε)))` colours with probability at least `1 - ε`. -/
theorem probForcing_logStar_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 3 ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ProbForcing k n ((n : ℝ) ^ (1 / (logStar n : ℝ)) / (8 * (1 + Real.log (4 * n / ε))))
      (1 - ε) := by
  have hL := two_le_logStar hn
  obtain ⟨hj, hnP⟩ := Rjm.jMin_spec (k := k) (n := n) (J := max 1 (logStar n - 1))
    (le_max_left _ _) (le_card_labelPoset_of_four_le hk n)
  have hjL := Rjm.jMin_le_of_four_le hk n
  refine (Rjm.probForcing_rpow_div (k := k) (j := Rjm.jMin k n) (by omega) (by omega) hj hnP
    hε0 hε1).of_le ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (4 * n / ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε0]
    linarith)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Rjm.rpow_inv_anti (by omega) (by positivity)
  have : Rjm.jMin k n + 1 ≤ logStar n := by omega
  exact_mod_cast this

end OnlineColouring
