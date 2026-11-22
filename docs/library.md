# The library: building, trust base, layout and conventions

## Building: details

The steps are those of `README.md`.

**Why step 2 comes first.** Lake compiles independent modules in parallel. Most of the generated modules do not
depend on each other (only `NumAdv10T`, `NumAdv10C*` and `NumAdv10` import other generated modules), and the kernel
needs between 0.8 and 4 GB to check each of them. If a plain `lake build` starts them together, the job can run
out of memory. Built one at a time, each stays within 4 GB; step 3 then finds them
up to date. The modules `CertK*` have to be rebuilt only after a change to `CertCheck.lean` or to a module that it
imports, directly or indirectly (`CertGame`, `AdvBasic`, `LabellingCap`, `Forcing`, `Structure`, `SeqBlowUp`,
`Reservation`, `Counting`, `Play`, `Online`, `TowerGrowth`, `BaseFacts`, `Growth`, `Towers`, `Cliques`, `BlowUp`,
`Labels`). The modules `NumAlg*` and `NumAdv*` depend, apart from each other, only on Mathlib and on `NumGame`,
`NumGameCheck` and `NumGameSkip`, and `NumP3`, `NumP4` on `NumPoset`, `BaseFacts` and the modules that these import
(`Growth`, `Towers`, `Cliques`, `BlowUp`, `Labels`). After a change to one of these, repeat step 2 before step 3.
Most of the time of step 2 goes into the twelve modules `NumAdv10C*`, which check the certificate for `V(10) ≥ 7`
(about 48 minutes of processor time); up to three of them can be built at the same time within 12 GB.

**What to expect.** Step 3 ends with a line that begins with `Build completed successfully` and prints no warning. Step 4 prints
one line for each of the declarations listed there. Each line must read
`'OnlineColouring.X' depends on axioms: [propext, Classical.choice, Quot.sound]`, with this list or a part of it, or
`'OnlineColouring.X' does not depend on any axioms`. A `sorry` would appear in such a list as `sorryAx`, and
`native_decide` as `Lean.ofReduceBool` or `Lean.trustCompiler`.

**Times**, measured on a machine with 48 cores:

| Step | Time |
|---|---|
| 2 | About ten minutes for the nine modules `CertK*`, between 10 seconds (`CertK5`) and 3 minutes 22 seconds (`CertK3C9`) each, and about an hour for the modules `Num*`, of which 48 minutes are the twelve modules `NumAdv10C*`. The tables in `docs/cert_converter.md` and `docs/num_generators.md` have the time and the memory of each module. |
| 3 | Each of the other modules compiles in 1 to 4 seconds, 2.7 minutes for all of them when compiled one after the other; lake compiles them in parallel. |
| 4 | About 3 seconds. |

To check a single file after an edit, without writing build products:

```
lake env lean OnlineColouring/<Module>.lean
```

This prints the errors and warnings of that file. It uses the build products of the imported modules, so these must
have been built (`lake build OnlineColouring.<Import>`).

## The trust base

The kernel checks the proofs, so a reader does not have to read them. What a reader has to check is that the
statements say what the paper says. The statements are built from the definitions in this section and from
Mathlib's definitions of simple graphs (`SimpleGraph`, `SimpleGraph.Colorable`, `SimpleGraph.CliqueFree`, graph
isomorphisms `≃g`), of real powers and logarithms (`Real.rpow`, `Real.log`, the natural logarithm) and of discrete
probability distributions (`PMF`). Auxiliary definitions that occur only inside proofs, the certificate data and the
certificate checker are not part of the trust base.

All names are relative to the namespace `OnlineColouring`. The last column says how the declaration corresponds to
the paper's definition.

### The online model and the online chromatic numbers (Section 4, Definition 4.1)

| Paper | Lean | File | Correspondence |
|---|---|---|---|
| Ordered graph on `n` vertices, earlier neighbours `N⁻(v)` | `OnlineInput`, `OnlineInput.graph` | `Online.lean` | The vertices are `0, …, n-1` in arrival order, and `nbr v` is the set of the earlier neighbours of `v`. By `OnlineInput.equivGraph` the inputs on `n` vertices are exactly the graphs on `Fin n`. |
| What the algorithm has seen | `History` | `Online.lean` | The list, in arrival order, of the pairs (set of earlier neighbours, colour) of the vertices presented so far. |
| Deterministic online algorithm | `OnlineAlg` | `Online.lean` | A function `step` from the history and the set `N⁻(v)` of the new vertex to the colour of `v`. This is all the algorithm learns. Every theorem quantifies the algorithm after `k` and `n`, so the algorithm may know both. |
| "a colour … that differs from the colours of `N⁻(v)`" | `OnlineAlg.IsProper` | `Online.lean` | For every history and every neighbour set, the answer differs from the colour of every listed earlier vertex. |
| The run of an algorithm on an input, and its cost | `runHist`, `runCol`, `OnlineInput.run`, `OnlineInput.cost` | `Online.lean` | The vertices are coloured in arrival order, each from the history of the earlier ones, and no colour is changed. The cost is the number of distinct colours. |
| `χ^det_k(n)` | `chiDet`, `maxCost`, `exists_maxCost_eq_chiDet` | `Online.lean` | `maxCost A k n` is the largest cost of `A` on a `k`-colourable input on `n` vertices, and `chiDet k n` is the least `maxCost A k n` over the proper algorithms `A`. The theorem says that the minimum is attained. For `k ≥ 1`, `le_chiDet_iff` unfolds `K ≤ chiDet k n` into `ChiDetAtLeast k n K`: every proper algorithm uses at least `K` colours on some `k`-colourable input on `n` vertices. |
| Randomized online algorithm, expected cost | `IsProperRand`, `expCost` | `RandModel.lean` | A randomized algorithm is a `PMF OnlineAlg`, a discrete probability distribution over deterministic algorithms; it is proper if every algorithm in its support is. `expCost μ I` is the expected cost of `μ` on the input `I`, which is fixed before the algorithm draws (an oblivious adversary). |
| `χ^rand_k(n)` | `chiRand`, `Paper.chiRand_isLeast` | `RandModel.lean`, `PaperRand.lean` | `chiRand k n` is the infimum, over the proper randomized algorithms, of the maximum expected cost over the `k`-colourable inputs on `n` vertices. The theorem says that this infimum is a minimum, as in the definition. For `k ≥ 1`, `le_chiRand_iff` unfolds `x ≤ chiRand k n` into `ChiRandAtLeast k n x`. |
| First-Fit | `OnlineAlg.firstFit`, `firstFit` | `Online.lean`, `FirstFit.lean` | The least colour not used on the earlier neighbours, as an online algorithm and as a colouring of an ordered graph. The two agree (`Paper.run_firstFit_eq`, `Paper.cost_firstFit_eq`). |
| A distribution over inputs: expected cost and probability of using `K` colours (Lemma 4.4) | `detExpCost`, `probAtLeast` | `RandModel.lean` | For a `PMF (OnlineInput N)` and a deterministic algorithm. |
| A distribution over `k`-colourable graphs on `n` vertices on which every deterministic algorithm uses `x` colours with probability `p` (Corollary 8.6, Appendix C, Appendix D.5) | `ProbForcing` | `ProbForcing.lean` | `ProbForcing k n x p`: there is a `PMF (OnlineInput n)` with all inputs of its support `k`-colourable such that, for every proper deterministic algorithm, the inputs of cost at least `x` have probability at least `p`. |

### Adversaries (Definition 4.2)

| Paper | Lean | File | Correspondence |
|---|---|---|---|
| Adversary | `Adversary` | `LabellingCap.lean` | A function `move` from the history to `none` (stop) or `some s` (present a new vertex with the set `s` of earlier neighbours). |
| Play | `Adversary.hist` | `LabellingCap.lean` | `adv.hist A p` is the history after `p` rounds against the algorithm `A`. It no longer changes once the adversary has stopped (`Adversary.StopsAt`). |
| Forces `K` colours | `Adversary.Forces` | `LabellingCap.lean` | Against every proper algorithm the play reaches a history at which the adversary stops, and at least `K` colours are in use there (`usedColours`). |
| The graph presented, post-degree | `History.graph`, `History.postDeg` | `AdvBasic.lean` | Vertex `i` is entry `i` of the history, and `u < v` are adjacent if and only if `u` is listed in the neighbour set of `v`. The post-degree of a vertex is its number of later neighbours. |
| Size at most `N`, post-degree at most `D` | `Adversary.SizeLE`, `Adversary.PostDegLE` | `AdvBasic.lean` | In every play against a proper algorithm, at most `N` vertices are presented, and every vertex receives at most `D` later neighbours. |
| Lands in a class of ordered graphs | `Adversary.LandsIn` | `AdvBasic.lean` | A class is a predicate on the graphs on `Fin n`, for all `n`. The graph of every play, taken when the adversary has stopped, belongs to the class. |
| `N_k(K)` | `Nk`, `NkLE`, `Nk_le_iff` | `AdvBasic.lean` | `Nk k K : ℕ∞` is the least `n` such that some adversary of size at most `n` forces `K` colours and lands in the `k`-colourable graphs, and `⊤` if there is no such adversary. `NkLE k K n` is the statement `N_k(K) ≤ n`. |
| Commits to labels from `P` (Proposition 9.4) | `Adversary.CommitsTo` | `LabellingCap.lean` | A rule `ψ` from histories to `P` gives every vertex a label right after the vertex was coloured, and `ψ(u) ≰ ψ(v)` for every edge `uv` with `u` earlier, in every play against a proper algorithm. |

### Posets, labellings, blow-ups and towers (Section 4, Definitions 4.5 to 4.7)

| Paper | Lean | File | Correspondence |
|---|---|---|---|
| `J*(P)` | `Jst`, `IsLowerFinset` | `Labels.lean` | The nonempty down-sets of `P`, as a subtype of `Finset P`, ordered by inclusion. `Jst.lowerSetEmbedding` embeds it into the lower sets of Mathlib, and for finite `P` every nonempty lower set is in the image (`Jst.exists_lowerSet_eq`, which assumes `[Finite P]`). |
| `P_j(k)` | `LabelPoset`, `labelPoset` | `Towers.lean` | `LabelPoset k 0` is `Anti (Fin k)`, the colours `0, …, k-1` with the discrete order, and `LabelPoset k (j+1)` is `Jst (LabelPoset k j)` by definition. `labelPoset k j` bundles the type with its order and its finiteness. |
| `width(P)` | `width`, `HasAntichain` | `Growth.lean` | `width P` is the largest size of an antichain. `HasAntichain P w` says that `P` has an antichain with exactly `w` elements, and `le_width_iff` shows that this is `w ≤ width P`. |
| Ordered graph, in general | `SimpleGraph V` with `[LinearOrder V]`, `OrdGraph` | `Towers.lean` | The order of the vertex type is the arrival order. `OrdGraph` bundles the type, the order and the graph. |
| `P`-labelling, "maps to `Tmpl(P)`" (Definition 4.5) | `IsLabelling`, `HasLabelling` | `Labels.lean` | `IsLabelling G f`: `f u ≰ f v` for every edge `uv` with `u < v`. `HasLabelling G P`: some labelling exists. The template digraph is not defined as an object. |
| Blow-up, full blow-up, reservation blow-up (Definition 4.6) | `BlowUp`, `BlowUp.IsFull`, `BlowUp.IsReservation` | `BlowUp.lean` | The structure has the block map `π` (surjective, so the blocks are nonempty) and the partial map `serve`. Its fields `lt_of_π_lt`, `serve_spec` and `adj_iff` are conditions (i), (ii) and (iii). That the blocks are independent follows (`BlowUp.not_adj_of_π_eq`). |
| Tower (Definition 4.7) | `IsFullTower`, `IsPaddedTower`, `IsTower` | `Towers.lean`, `CeilingPadded.lean` | `IsFullTower m j G`: `G` arises from the arrival-ordered clique on `m` vertices by `j` full blow-ups. `IsPaddedTower m j H`, the tower of the last sentence of the definition: an initial segment of a finite full tower, possibly followed by isolated vertices. `IsTower` is `IsFullTower` without fullness and is used for colourability. |
| `tow`, `lg*` | `tow`, `logStar` | `TowerGrowth.lean` | `tow 0 = 1` and `tow (i+1) = 2 ^ tow i`. `logStar x` is the least `i` with `x ≤ tow i`. |

### Known graphs (Theorem 1.3, Section 7)

| Paper | Lean | File | Correspondence |
|---|---|---|---|
| Presentation of `G` | `Nonempty (I.graph ≃g G)` | | An online input `I` whose graph is isomorphic to `G`. The graph `G` has the vertex set `Fin N`. |
| `χ_ol(G)` | `Paper.chiOl`, `OnlineChromaticAtLeast`, `Paper.le_chiOl_iff` | `PaperStatements.lean`, `KnownGraphs.lean` | `Paper.chiOl G` is the least `c` such that some proper algorithm uses at most `c` colours on every presentation of `G`. `OnlineChromaticAtLeast G K` says that every proper algorithm uses at least `K` colours on some presentation of `G`; the algorithm is quantified after `G`, so it may know `G`. The theorem shows that this is `K ≤ Paper.chiOl G`. |
| Randomized algorithms that know `G` | `RandKnownAtLeast` | `KnownGame.lean` | `RandKnownAtLeast G x`: every proper randomized algorithm has expected cost at least `x` on some presentation of `G`. |

### Uniform towers and the random wiring (Section 8)

| Paper | Lean | File | Correspondence |
|---|---|---|---|
| Uniform tower, wiring | `ueSeq`, `ueNb`, `ueInput`, `utSize` | `UTowerE.lean`, `TowerIndex.lean` | The nodes at depth `d` below the top are numbered `0, …, mA^d - 1` in arrival order, and the parent of `y` is `y / A`. A wiring consists of the top servers `τ s t` and of the maps `φ s t d g` between the children of a node and the children of its server. `ueNb d s y` is the earlier neighbour of `y` below the top vertex `v_s`. The tower has `utSize A m j = mA^j` presented vertices. |
| `R_j(m)` (Construction 8.1) | `EΩ`, `EZ`, `uInputE`, `unifPMF` | `UWiringE.lean`, `RandModel.lean` | A point `ω` of `EΩ m j A` has, for every pair `(t, s)`, a rank among the children of `v_s` that have not served before phase `t`, and a permutation of the `A` positions for every node of level at least 2 below `v_t`. `R_j(m)` is the uniform distribution on `EΩ m j (2m)`: the top server is a uniformly random unused child, all bijections are uniformly random, and all choices are independent. The coordinates with `s ≥ t` are not used. `uInputE ω` is the input that the wiring `ω` presents. |
| `G_j(m)` (Lemma 8.2) | `Rjm.Gjm` | `RjmGraph.lean` | The graph on `m(2m)^j` vertices presented by one fixed wiring. Every wiring presents an isomorphic graph (`Rjm.uInputE_iso_Gjm`). |
| The bound `X_m` of Theorem 8.5 and the bound of Corollary 8.6 | `uniformBound`, `epsBound` | `UniformBound.lean` | `X_m = (2m+1)/(4(1+ln 4m))` and `(2m+1)/(4(1+ln(4m/ε)))`. |
| Number of colours used against a wiring | `numColsE` | `UExact.lean` | `numColsE alg ω` is the number of distinct colours that `alg` uses on the tower of the wiring `ω`; it is the cost of `alg` on `uInputE ω` (`numColsE_eq_cost`). |

## Layout

The modules are listed by the section of the paper that they belong to. Within a group they are in import order.
`PAPER_MAP.md` gives the declaration for each statement.

Most declarations are in the namespace `OnlineColouring`. The sub-namespaces are `Paper` (statements in the literal
wording of the paper, and the facts showing that the conventions below change nothing), `Det` (determinacy), `Blow`
(the adversaries of Sections 6 and 9), `Str` (the adversaries of Section 7 and of Proposition B.1), `Rjm` (uniform
towers), `Expl` (the adversary of Theorem 8.5 (ii), properness, the transfer for randomized algorithms), `Obl`
(Appendix C), `AppBD` (Corollary B.2 and Appendix D), `Cert` (the exact values of Appendix B and the numbers computed
from closed formulas), `Num` (the computed values of Section 5, Appendix A and Appendix D.3) and `BaseFacts` (the
antichain of Lemma 5.5 (iii)).

**Sections 4 and 5: posets, labels, blow-ups, towers**

| Module | Content |
|---|---|
| `Labels` | Posets, the discrete order `Anti`, down-sets, `J*(P)`, labellings (Definition 4.5). |
| `BlowUp` | Blow-ups, full blow-ups and reservation blow-ups (Definition 4.6); Lemmas 5.2 and 5.3. |
| `Cliques` | Lemma 5.1 (cliques and antichains). |
| `Towers` | The label posets `P_j(k)`, `j`-fold blow-ups of `K_m` and full towers (Definition 4.7), Corollary 5.4. |
| `Growth` | Antichains and `width`; Lemma 5.5 (i) and (ii). |
| `BaseFacts` | `card P_1(3) = 7`, `card P_2(3) = 18` and the antichain of Lemma 5.5 (iii). |
| `TowerGrowth` | `tow`, `lg*`, the recursion `T_i`, Lemma 5.6 and Corollary 5.7. |
| `Existence` | Every ordered graph has a reservation blow-up, so the full `j`-fold blow-ups of Corollary 5.4 exist. |

**Section 4: the online model, adversaries, determinacy, Yao's principle**

| Module | Content |
|---|---|
| `Online` | Histories, algorithms, properness, inputs, runs, cost, `χ^det`, First-Fit as an algorithm, padding with isolated vertices. |
| `Play` | Adaptive rules that never stop: against a fixed algorithm, a play is one input. |
| `RandModel` | Randomized algorithms, expected cost, `χ^rand`, Lemma 4.4 for the predicate `ChiRandAtLeast`, uniform distributions. |
| `DetYao` | Lemma 4.4 (Yao's principle) for the number `χ^rand_k(n)`. |
| `ProbForcing` | The predicate `ProbForcing`, its closure properties, and probabilities under uniform distributions. |
| `LabellingCap` | Adversaries, plays and forcing (Definition 4.2); commitment to labels and Proposition 9.4. |
| `AdvBasic` | The graph of a play, size, post-degree, landing in a class, `N_k(K)` (Definition 4.2). |
| `Det` | Observation 4.3 (determinacy), with a general lemma that turns "for every algorithm an input" into one adversary. |
| `PaperRand` | Definition 4.1: the minimum in `χ^rand_k(n)` is attained, by a distribution with finite support. |
| `PaperMeasure` | Definition 4.1: arbitrary probability measures over algorithms give the same `χ^rand_k(n)`. |
| `PaperStatements` | Statements in the wording of the paper: monotonicity of `χ^rand`, Lemma 4.4, `χ_ol(G)`, "subtree by subtree" in Definition 4.7, Lemmas 5.5 and 5.6 with `width`, Theorem 1.1 with the least number of levels, the last sentence of Theorem 1.2, Theorems 1.3 and 1.4, Lemma 7.1. |
| `PaperFirstFit` | The algorithm First-Fit produces the First-Fit colouring; Theorem 1.5 for its cost; Lemma 5.3 with its labelling. |
| `ExplProper` | Properness is needed only on the histories that occur: equivalences for every notion of the library. |

**Section 6: reservation blow-ups, Theorem 1.2**

| Module | Content |
|---|---|
| `Counting` | The block sizes `b_ℓ`, the size bound `(K-1) ∏ b_ℓ + 1` of Theorem 6.4 and its bound `K^{(j+1)(j+2)/2}`, the entries of Table 2. |
| `Reservation` | The pigeonhole step of Construction 6.1: a block with fewer than `K` colours has `D` vertices of one colour. |
| `SeqBlowUp` | Reservation blow-ups with blocks of equal size, as sequences of neighbour sets. |
| `Structure` | One reservation blow-up played against a fixed algorithm, and the induced algorithm (Lemma 6.2 without the stop rule). |
| `Forcing` | Theorem 6.4 against a fixed algorithm: an input that is a full tower and on which the algorithm uses `K` colours. |
| `PlayBound` | The same with the size `(K-1) b_j ⋯ b_1 + 1` of the theorem. |
| `OddGirth` | Remark 6.5: blow-ups are triangle-free, and a `j`-fold blow-up of `K_K` is bipartite or has odd girth at least `2j + 3`. |
| `Blow` | Construction 6.1 and Lemma 6.2: the adversary `B(𝒜)`; the servers have the induced colour. |
| `BlowStack` | Lemma 6.3 (stacking). |
| `BlowTower` | Theorem 6.4 for the adversary of the paper, proved from Lemma 6.3; First-Fit on its plays (Remark 6.5). |
| `DetBlow` | Theorem 6.4 once more, by determinacy from the forms against a fixed algorithm: with the vertex bound from `PlayBound`, and with full towers as final graphs from `Forcing`. |
| `MainTheorem` | Theorem 1.2, from the adversary of Theorem 6.4 and Observation 4.3. |
| `Asymptotic` | Monotonicity of `χ^det`; the asymptotic form of Theorem 1.2; Theorem 1.4, second sentence. |

**Section 7: known graphs**

| Module | Content |
|---|---|
| `Iso` | Lemma 7.1 (the server assignment does not matter). |
| `KnownGraphs` | `χ_ol(G) ≥ K` as a predicate, the digraph `H_j(K)`, the graph `G` of Theorem 1.3 and its colourability. |
| `PadGraph` | Appending isolated vertices to a graph. |
| `KnownGame` | The known-graph game for deterministic and for randomized algorithms: monotonicity, padding, invariance under isomorphism. |
| `StrBlow` | One reservation blow-up of the adversary `𝒜^str`, which completes every block. |
| `StrTower` | The adversary `𝒜^str`, Lemma 7.2, and `χ_ol(G) ≥ K` from Alice's strategy of playing `𝒜^str` and then the isolated vertices. |
| `StrKnown` | Theorem 1.3 for `G`. |

**Section 8 and Appendix A: uniform towers, Theorem 1.1**

| Module | Content |
|---|---|
| `TowerIndex` | The numbering of the nodes of a tower in which every node has `A` children, and a criterion for blow-ups. |
| `UTowerE` | The uniform tower that is determined by its top servers and its server bijections. |
| `Phases` | The phases of a uniform tower. |
| `UWiringE` | Construction 8.1: the sample space of `R_j(m)`, the presented input, eligible vertices, and the counting behind Lemma 8.4. |
| `RjmGraph` | Lemma 8.2 (one graph) and the graph `G_j(m)`. |
| `MassArith` | The real-number lemmas behind Lemmas 8.3 and 8.4 and inequality (8.1). |
| `UniformBound` | The bound `X_m` of Theorem 8.5 and the bound of Corollary 8.6. |
| `UExact` | Unused mass, inequality (8.1), Theorem 8.5 (i), and the first statement of Corollary 8.6. |
| `RjmMass` | Lemmas 8.3 and 8.4 as stated in the paper. |
| `ExplUniform` | The proof of Lemma 8.4 in exact form: the earlier neighbours of a vertex are uniform and independent. |
| `DetTower` | Uniform towers are full towers; Theorem 8.5 (ii) from determinacy. |
| `ExplAdv` | Theorem 8.5 (ii): the adaptive adversary of the paper's proof. |
| `ExplKnown` | `χ_ol(G_j(m)) ≥ ⌈X_m⌉` from that adversary (the proof of Theorem 1.3 for `G′`). |
| `UniformArith` | The chain of inequalities (8.2). |
| `UniformThresholds` | Lemma A.1 (thresholds). |
| `LogStarGeneric` | The choice of the parameters in the proof of Theorem 1.1, for an abstract predicate. |
| `MainLogStar` | Theorem 1.1, Theorem 1.3 for `G′`, and Corollary 8.6. |
| `ExplCor` | Further consequences of the adversary of Theorem 8.5 (ii): bounds on `N_k`, the lower bound of Corollary 9.6. |
| `CertOvertake` | Section 8.4: where the uniform towers overtake the explicit construction. |
| `CertLink` | The size formulas of `CertNumbers` for Proposition B.1 and Corollary B.2 are the size bounds proved for the adversaries (`Str.refSize`, `AppBD.cheapTopSize`). |

**Section 9: transfer, slowly growing chromatic number, limits**

| Module | Content |
|---|---|
| `Transfer` | Theorem 1.4, first sentence, with the sizes of its proof and the two examples after it. |
| `BlowPairing` | Construction 9.1 and Lemma 9.2 (the pairing top). |
| `BlowSlow` | Theorem 9.3. |
| `FirstFit` | First-Fit on an ordered graph, and Lemma 9.5 (First-Fit commutes with blow-ups). |
| `Ceiling` | Theorem 1.5, first sentence, for initial segments of full towers. |
| `CeilingAsymptotic` | Theorem 1.5, second sentence, for initial segments of full towers. |
| `CeilingPadded` | Theorem 1.5 for towers in the sense of Definition 4.7. |
| `DetValue` | Corollary 9.6 (the value of towers); adversaries that land in `k`-colourable `j`-level towers force at most `card P_j(k)` colours. |

**Appendix B: smaller instances and exact small cases**

| Module | Content |
|---|---|
| `TwoPerColour` | Lemma B.3 for First-Fit on an input and for `χ^det`: `2 χ^det_k(n) ≤ n + k`. |
| `CertLower` | Lemma B.3 for `N_k(c)`. |
| `StrRefBlocks` | Blow-ups with blocks of variable size, as sequences of neighbour sets. |
| `StrRefBlow` | One reservation blow-up with block and reserve sizes that depend on the node. |
| `StrRefTower` | Proposition B.1 (smaller blocks) and the entries of Table 3. |
| `AppBDCheapTop` | Corollary B.2 (a cheaper top), against a fixed algorithm. |
| `AppBDCheapTopAdv` | Corollary B.2 for the adversary that it names: the flow adversary of Theorem D.2 with `j - 1` reservation blow-ups below it. |
| `CertGame` | Forcing from a position, and the transfer lemma that the certificates use. |
| `CertCheck` | The certificate checker and the proof that it is sound. |
| `CertK3`, `CertK3C9`, `CertK4`, `CertK4C10`, `CertK5`, `CertK5C11`, `CertK5C12`, `CertK6`, `CertK6C13` | Generated: the adversary strategies as data, and the kernel checks of `N_k(c) ≤ 2c - k`. |
| `CertNk` | Proposition B.4 (exact values). |
| `CertNumbers` | The numbers that the paper computes from closed formulas: Tables 2 and 3, the numbers after Corollary B.2, and those of Appendices D.3, D.5 and D.6. |

**Computed values with kernel-checked certificates (Section 5, Appendix A, Appendix D.3)**

| Module | Content |
|---|---|
| `NumPoset` | A verified counter of down-sets on bit masks, with checkers for chain covers and antichains. |
| `NumTwo` | `card P_j(2) = j + 2` and `width(P_j(2)) = 2` for all `j`. |
| `NumP3`, `NumP4` | Partly generated: codings of `P_1(3)`, `P_2(3)`, `P_3(3)` and `P_1(4)`; the sizes `81`, `8569`, `166`, the widths, and the antichain of 235 elements of `P_4(3)`. |
| `NumValues` | The sentence "The first values are …" of Section 5 as one statement (`Num.first_values`). |
| `NumGame`, `NumGameCheck`, `NumGameSkip` | The abstract one-level game on multisets of colours, and checkers for algorithm and adversary certificates with their soundness proofs. |
| `NumOneLevel`, `NumOneLevelAdv`, `NumVDef` | The link between the abstract game and adversaries of the one-level form (`AppBD.IsOneLevelAdv`); the definition of `V(m)`, its monotonicity and the bounds `⌊m/2⌋ + 1 ≤ V(m) ≤ m`. |
| `NumAlgSmall`, `NumAlg11`, `NumAdvSmall`, `NumAdv8`, `NumAdv9` | Generated: certificates for the upper bounds (`m = 4, …, 11`) and the lower bounds (`m = 4, …, 9`), with their kernel checks. |
| `NumV` | `V(4), …, V(9)`, and `6 ≤ V(10), V(11) ≤ 7`. |
| `NumAdv10D0`–`D13`, `NumAdv10T`, `NumAdv10C0`–`C11`, `NumAdv10` | Generated: the certificate for `V(10) ≥ 7` (107 285 positions) and its kernel checks. |
| `NumV10` | The whole table of Appendix D.3: `V(4), …, V(11) = 3, 4, 4, 5, 6, 6, 7, 7` (`Num.V_table_full`). |

**Appendix C: oblivious blow-ups**

| Module | Content |
|---|---|
| `OblCount` | Counting and mixing lemmas for uniform distributions on products; also used for Lemma 8.4. |
| `Oblivious` | The oblivious blow-up for one outcome of the hidden indices. |
| `OblProb` | Construction C.1 and Lemma C.2. |
| `OblTower` | Theorem C.3 (iterated oblivious blow-ups). |
| `OblCor` | Corollary C.4 (high probability). |

**Appendix D: further results**

| Module | Content |
|---|---|
| `ReservationFree` | Proposition D.1 (reservation-free levels). |
| `AppBDMatching` | A matching that covers all tight rows and columns, the combinatorial step of Theorem D.2. |
| `AppBDFlow` | The flow adversary of Theorem D.2 and the potential of Lemma D.3: the combinatorial part. |
| `AppBDOneLevel` | Theorem D.2 (one level, minimal blocks) and Lemma D.3. |
| `AppBDTopBlock` | Theorem D.4 (top block). |
| `AppBDLST` | The algorithm of Lovász, Saks and Trotter on bipartite graphs, with its bound. |
| `AppBDPJArith` | Theorem D.5: the summation. |
| `AppBDPJ` | Theorem D.5 (partial joins). |
| `AppBDPJAsymp` | Theorem D.5: the two asymptotic statements. |
| `AppBDWitness` | Theorems D.4 (for `K ≥ 2`) and D.5 (over `K_m` with `2 ≤ m ≤ 7`): the adversary of Theorem 6.4 with one level satisfies their hypotheses. |
| `ExplTransfer` | Appendix D.5: the transfer for randomized algorithms. |
| `ExplTransferSize` | The size of the transferred distribution. |
| `ExplTransferPoly` | Lower bounds that hold with constant probability transfer between values of `k`. |

## Conventions and deliberate differences

The formal statements have the quantifiers, hypotheses and constants of the paper. `PAPER_MAP.md` records, row by
row, every hypothesis that a formal statement adds or drops. The following conventions hold throughout.

**Colours are natural numbers, starting at `0`.** The paper's colours are natural numbers as well, and only the
number of distinct colours enters a statement. First-Fit gives the least colour, which is `0`.

**Indices start at `0`.** The vertices of an input on `n` vertices are `0, …, n-1`. The top vertices `v_1, …, v_m`
of a tower, its phases and the blocks of a blow-up are numbered `0, …, m-1`. Where the numbering enters a formula,
the docstring gives the translation: for example, the unused mass `u_c(m+1)` at the end of the play is
`uME alg ω c m`, and block `t` of Theorem D.2 has at least `max 1 (m - t - 1)` vertices
(`AppBD.one_level_minimal_blocks`; `AppBD.one_level_minimal_blocks_paper` states the theorem with the numbering of
the paper). Where a level `ℓ` enters a statement (`blockSize K j ℓ`, `Str.bl K j ℓ t`, `Obl.towN K j b ℓ`), it is
numbered as in the paper, with the presented vertices at level `0`; the definitions for uniform towers count the
depth below the top vertices instead (`utSize`, `ueNb`).

**A neighbour set may list indices that are not earlier vertices.** An algorithm is a function of an arbitrary
history and an arbitrary finite set of natural numbers, and the move of an adversary is an arbitrary finite set.
Indices that do not belong to earlier vertices are ignored by everything that gives the set a meaning: the graph of
a history (`History.graph`), properness (`OnlineAlg.IsProper`) and the colours of the neighbours (`nbrColours`).
An online input cannot contain such indices (`OnlineInput.nbr_lt`). The freedom does not strengthen adversaries:
Observation 4.3 holds for them as stated (`Det.le_chiDet_iff_Nk_le`).

**Properness is required on all histories.** `OnlineAlg.IsProper` constrains an algorithm on every history,
including histories that cannot arise in any play, whereas the paper asks for a proper colour only in the plays that
occur. `ExplProper.lean` shows that this changes nothing: an algorithm that answers properly where it matters can
be changed on the other histories without changing any play. For every notion of the library there is an
equivalence with the weakest sensible hypothesis: `Expl.chiDetAtLeast_iff_properOn` and
`Expl.chiDet_eq_sInf_properOn` for `χ^det`, `Expl.chiRandAtLeast_iff_properOn` and `Expl.chiRand_eq_iInf_properOn`
for `χ^rand`, `Expl.onlineChromaticAtLeast_iff_properOn`, `Expl.chiOl_eq_sInf_properOn` and
`Expl.randKnownAtLeast_iff_properOn` for known graphs, `Expl.probForcing_iff_properOn` for distributions over
inputs, and `Expl.forces_iff_properAgainst`, `Expl.sizeLE_iff_properAgainst`, `Expl.postDegLE_iff_properAgainst`,
`Expl.landsIn_iff_properAgainst`, `Expl.nkLE_iff_properAgainst` and `Expl.commitsTo_iff_properAgainst` for
adversaries.

**Randomized algorithms are discrete distributions.** A randomized algorithm is a `PMF OnlineAlg`, a probability
distribution with countable support. The paper says "probability distributions over deterministic ones" and remarks
that finite support suffices. `PaperRand.lean` proves the remark: every proper randomized algorithm has the same
expected cost on every `k`-colourable input on `n` vertices as one with finite support
(`Paper.exists_finite_support_expCost_eq`), and the minimum in the definition of `χ^rand_k(n)` is attained by a
distribution with finite support (`Paper.chiRand_isLeast`, `Paper.chiRand_isLeast_finite`,
`Paper.exists_finite_support_minimizer`). `PaperMeasure.lean` extends this to arbitrary probability measures: for
every σ-algebra on the deterministic algorithms that makes the costs measurable, and every probability measure
concentrated on proper algorithms, some proper randomized algorithm with finite support has the same expected
costs (`Paper.exists_finite_support_of_measure`), so the measure does not beat `χ^rand_k(n)`
(`Paper.chiRand_le_of_measure`).

**Predicates next to numbers.** Most proofs work with the predicates `ChiDetAtLeast k n K`, `ChiRandAtLeast k n x`,
`OnlineChromaticAtLeast G K` and `NkLE k K n`, which say that the respective number is at least, or at most, the
given bound. The numbers themselves are `chiDet`, `chiRand`, `Paper.chiOl` and `Nk`, and the equivalences are
`le_chiDet_iff`, `le_chiRand_iff`, `Paper.le_chiOl_iff` and `Nk_le_iff`. The first two need `k ≥ 1`: for `k = 0` and
`n ≥ 1` there is no `k`-colourable input.

**Two forms of the adversary theorems.** By Observation 4.3 a lower bound on `χ^det` can be proved by exhibiting
one adversary, or by exhibiting an input for every algorithm. The library has both forms of the main constructions:
the modules `Structure`, `Forcing`, `KnownGraphs` and `Transfer` work with inputs against a fixed algorithm, and the
modules `Blow*`, `Str*` and `ExplAdv` define the adversaries of the paper as objects of type `Adversary` and prove
the paper's statements about them. Theorems 1.2 and 1.3 are derived from the adversaries, as in the paper, and
Theorem 1.4 from the form with inputs. `PAPER_MAP.md` lists, in its last section, where a formal proof takes a
route that differs from the paper's.

**The suffix `E`.** The declarations about the sample space `EΩ` of the random wiring `R_j(m)` of Construction 8.1
carry the suffix `E`: `uInputE`, `uSeqE`, `uColE`, `eligE`, `uME`, `numColsE`, `avg_numCols_geE`,
`uniform_tower_randE` and others. The suffix distinguishes them from the declarations about a tower with an
arbitrary wiring (`ueSeq`, `ueInput`), on which they are built, and has no other meaning.

**Real numbers.** `ln` is `Real.log`, and `n^{1/x}` is a real power (`Real.rpow`) of the cast of `n`. The paper's
`lg* n` is the natural number `logStar n`, cast to a real number inside exponents. `⌊x⌋₊` and `⌈x⌉₊` are the floor
and the ceiling as natural numbers.

## The generated certificate data

Proposition B.4 gives the exact values `N_k(c) = 2c - k` for thirty pairs `(k, c)`. Its upper bounds rest on
adversary strategies that were found by computer search and are part of the supplementary material of the paper
(`repro/certificates/dag_k*_C*.gen.txt`). In the library, `CertCheck.lean` defines a checker for such
strategies and proves it sound (`Cert.nkLE_of_cert`). The nine modules `CertK*.lean` contain the thirty strategies
as Lean data, together with the theorems `Cert.nkLE_3_3`, …, `Cert.nkLE_6_13`, which the kernel proves by
evaluating the checker (`decide +kernel`, without `native_decide`). `CertNk.lean` combines them with the lower bound
of Lemma B.3 into Proposition B.4 (`Cert.prop_small`).

The nine data modules are generated and should not be edited. They were written by a converter that translates the
strategy files and adds the witnesses that the checker verifies. The converter is not trusted, because the kernel
checks everything it writes. `docs/cert_converter.md` contains the two programs of the converter, the command that
regenerates the nine modules (the result is identical to the modules in the library, byte for byte), and the time
and memory that the kernel needs for each module. After regenerating, rebuild the modules one at a time, as in
step 2 of `README.md`.

The modules `Num*` treat the other computed values in the same way. `NumPoset.lean` proves a counter of down-sets
correct, and `NumP3.lean`, `NumP4.lean` evaluate it on explicit codings of the posets, which gives the sizes `81`,
`8569` and `166`; no enumeration is trusted, because completeness follows from the count. For the one-level values
`V(m)` of Appendix D.3, `NumGameCheck.lean` and `NumGameSkip.lean` define checkers for certificates of an abstract
game and prove them sound, `NumOneLevel.lean` and `NumOneLevelAdv.lean` prove that the abstract game decides what
adversaries of the one-level form can force, and the generated modules contain the certificates: those of the
supplementary material for the upper bounds and for the lower bounds up to `m = 7`, and certificates with null moves,
produced with a patched copy of the solver, for `m = 8, 9, 10`. `docs/num_generators.md` contains the generators, the patch and
the time and memory of each kernel check.

The numbers that the paper computes from closed formulas (the entries of Tables 2 and 3, the sizes after Corollary
B.2, the numbers of Section 8.4 and of Appendices D.3, D.5 and D.6) need no certificates: `Counting.lean`,
`StrRefTower.lean`, `CertNumbers.lean` and `CertOvertake.lean` define the formulas as in the paper and evaluate them
in the kernel or with `norm_num`; `CertLink.lean` proves that the formulas of `CertNumbers.lean` for Proposition B.1
and Corollary B.2 are the size bounds of the adversaries.

## What is not formalized

`PAPER_MAP.md` has the complete list in its section "Not formalized". In short:

| Paper item | Status |
|---|---|
| The best escape probabilities in the table of Appendix D.5, and the remark after Corollary C.4 that quotes one of them | Not formalized. |
| The remarks after Lemma A.1 that the thresholds `2^406` and `2^201` cannot be halved and on the bound for `j = 5`, and the table of minima in the proof of the lemma | Not formalized. |
| Section 8.4: that no number of levels other than `j = 4` lets the uniform towers win earlier | Not formalized; the facts for `j = 4` are. |
| Appendix D.5: that the closed form `1 - ∏ surj(R, d)` is the probability that First-Fit escapes, and its asymptotic consequence | Not formalized; the closed form and its values are. |
| Appendix D.3: the number of colours for which the reservation adversary fits into the minimal blocks. Appendix D.6: the growth rate of the recursion for Li's construction | Not formalized. |
| Table 2, caption: that `log(bound)/log K` approaches `(j+1)(j+2)/2` as `K` grows | Not formalized; the rows of the table are. |
| Appendix D.5, explicit instances: the statement about the two distributions | Not stated separately; the evaluation of condition (c) and Lemma C.2 are formalized. |
| Step (a) of the flow adversary of Theorem D.2: Kőnig's decomposition into matchings | Only the consequence that is used. |
| Remark after Lemma 6.2: that the graph presented by `B(𝒜)` is itself a blow-up of the inner graph restricted to the blocks that have started | Not stated in this form; the form with complete blocks is, and the graphs of a play are initial segments of it. |
| Table 1, caption: lower bounds for `k = 3` hold for larger `k`, for randomized algorithms. Section 3: the remark on presentations that stay connected. Figure 4: the curve of the adversary of Theorem 6.4 | Not formalized. |

The results that the paper quotes from the literature (Table 1, Section 3), the plays traced as illustrations in
Figures 1 and 3 and the sentences that report runs of programs are outside the scope of the library. The open
problems of Section 10 contain nothing to formalize.
