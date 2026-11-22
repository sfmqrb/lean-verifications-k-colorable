module

public import OnlineColouring.StrTower

/-!
# Theorem 1.3 for the graph `G`

The proof of Theorem 1.3 for `G` (Section 7), in outline: `G` consists of `H_j(K)` and
`N - |V(H_j(K))|` isolated vertices, with `K` and `j` chosen as in the proof of Theorem 1.2.
For every deterministic algorithm, run `𝒜^str` against it and append the isolated vertices; by
Lemma 7.2 the result is `G` with some presentation order, and the algorithm uses at least `K`
colours on it.

* `known_graph`: if `K ≥ 2`, `|P_j(k)| ≥ K` and `N ≥ K b_j ⋯ b_1`, then `G = knownGraph K j N` is
  `k`-colourable (Corollary 5.4, `knownGraph_colorable`) and `χ_ol(G) ≥ K`
  (`Str.known_graph_adversary`: the adversary `𝒜^str`, Lemma 7.2, and the isolated vertices).
* `known_graph_three`, `known_graph_of_four_le`: the same with the number of levels of the proof
  of Theorem 1.2 (`exists_levels_three`, `exists_levels_of_four_le`); `G` is triangle-free
  (`knownGraph_cliqueFree`).
* `known_graph_three_floor`, `known_graph_of_four_le_floor`: the statements of Theorem 1.3 about
  `G`, `χ_ol(G) ≥ ⌊N^{2/((L+2)(L+3))}⌋` for `k = 3` and `χ_ol(G) ≥ ⌊N^{2/(L(L+1))}⌋` for `k ≥ 4`.

The statements about `G′` are in `MainLogStar.lean`, and both graphs appear together in
`Paper.known_graphs_three`, `Paper.known_graphs_of_four_le` (`PaperStatements.lean`).
-/

@[expose] public section

namespace OnlineColouring

/-- **Theorem 1.3, core.** If `K ≥ 2`, `|P_j(k)| ≥ K` and `N ≥ K b_j ⋯ b_1`, then `H_j(K)` padded to
`N` vertices is `k`-colourable and has online chromatic number at least `K`: against every proper
algorithm, the play of `𝒜^str` followed by isolated vertices is a presentation of it (Lemma 7.2)
on which the algorithm uses `K` colours. -/
theorem known_graph {k K j N : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j))
    (hN : towerSize K j ≤ N) :
    (knownGraph K j N).Colorable k ∧ OnlineChromaticAtLeast (knownGraph K j N) K :=
  ⟨knownGraph_colorable hK hKj, Str.known_graph_adversary hK hN⟩

/-- **Theorem 1.3, `k = 3`.** For `L = lg* N` and every `K ≥ 2` with `K^((L+2)(L+3)/2) ≤ N`, there
is a triangle-free `3`-colourable graph `G` on `N` vertices with `χ_ol(G) ≥ K`. -/
theorem known_graph_three {N K : ℕ} (hK : 2 ≤ K)
    (hKN : K ^ ((logStar N + 2) * (logStar N + 3) / 2) ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable 3 ∧ G.CliqueFree 3 ∧ OnlineChromaticAtLeast G K := by
  obtain ⟨j, hj, hKj, hjN⟩ := exists_levels_three hK hKN
  obtain ⟨hc, hol⟩ := known_graph hK hKj ((towerSize_le hK j).trans hjN)
  exact ⟨_, hc, knownGraph_cliqueFree hK hj, hol⟩

/-- **Theorem 1.3, `k ≥ 4`.** For `N ≥ 3`, `L = lg* N` and every `K ≥ 2` with `K^(L(L+1)/2) ≤ N`,
there is a triangle-free `k`-colourable graph `G` on `N` vertices with `χ_ol(G) ≥ K`. -/
theorem known_graph_of_four_le {N k K : ℕ} (hN : 3 ≤ N) (hk : 4 ≤ k) (hK : 2 ≤ K)
    (hKN : K ^ (logStar N * (logStar N + 1) / 2) ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧ OnlineChromaticAtLeast G K := by
  obtain ⟨j, hj, hKj, hjN⟩ := exists_levels_of_four_le hN hk hK hKN
  obtain ⟨hc, hol⟩ := known_graph hK hKj ((towerSize_le hK j).trans hjN)
  exact ⟨_, hc, knownGraph_cliqueFree hK hj, hol⟩

/-! ### The floor form -/

/-- **Theorem 1.3, `k = 3`, floor form.** For `N ≥ 3` and `L = lg* N` there is a triangle-free
`3`-colourable graph `G` on `N` vertices with `χ_ol(G) ≥ ⌊N^{2/((L+2)(L+3))}⌋`. -/
theorem known_graph_three_floor {N : ℕ} (hN : 3 ≤ N) :
    ∃ G : SimpleGraph (Fin N), G.Colorable 3 ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G ⌊(N : ℝ) ^ ((2 : ℝ) / ((logStar N + 2) * (logStar N + 3)))⌋₊ := by
  set L := logStar N
  rcases Nat.lt_or_ge ⌊(N : ℝ) ^ ((2 : ℝ) / ((L + 2) * (L + 3)))⌋₊ 2 with hK | hK
  · exact exists_known_graph_of_le_one (by omega) (by norm_num) (by omega)
  · apply known_graph_three hK
    have heven : Even ((L + 2) * (L + 3)) := Nat.even_mul_succ_self (L + 2)
    have := floor_rpow_pow_le (n := N) (c := (L + 2) * (L + 3)) (by positivity) heven
    push_cast at this
    exact this

/-- **Theorem 1.3, `k ≥ 4`, floor form.** For `N ≥ 3` and `L = lg* N` there is a triangle-free
`k`-colourable graph `G` on `N` vertices with `χ_ol(G) ≥ ⌊N^{2/(L(L+1))}⌋`. -/
theorem known_graph_of_four_le_floor {N k : ℕ} (hN : 3 ≤ N) (hk : 4 ≤ k) :
    ∃ G : SimpleGraph (Fin N), G.Colorable k ∧ G.CliqueFree 3 ∧
      OnlineChromaticAtLeast G ⌊(N : ℝ) ^ ((2 : ℝ) / (logStar N * (logStar N + 1)))⌋₊ := by
  have hL : 2 ≤ logStar N := two_le_logStar hN
  set L := logStar N
  rcases Nat.lt_or_ge ⌊(N : ℝ) ^ ((2 : ℝ) / (L * (L + 1)))⌋₊ 2 with hK | hK
  · exact exists_known_graph_of_le_one (by omega) (by omega) (by omega)
  · apply known_graph_of_four_le hN hk hK
    have heven : Even (L * (L + 1)) := Nat.even_mul_succ_self L
    have := floor_rpow_pow_le (n := N) (c := L * (L + 1)) (by positivity) heven
    push_cast at this
    exact this

end OnlineColouring
