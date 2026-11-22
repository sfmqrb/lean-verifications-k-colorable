module

public import OnlineColouring.StrBlow
public import OnlineColouring.BlowTower
public import OnlineColouring.KnownGraphs

/-!
# Section 7: the adversary `𝒜^str` and Lemma 7.2 (one final graph)

Section 7: the paragraph "Completing every block", Lemma 7.2 (`lem:K`) and the proof of
Theorem 1.3 for `G`.

## The objects

* `Str.strTower K j : Adversary` is `𝒜^str`: the clique `K_K` (`Adversary.clique K`) with `j`
  blow-ups `Str.Bstr` below it (`StrBlow.lean`: Construction 6.1 without the stop rule, and with
  a most frequent colour in step 3 if no colour occurs `D` times).  The parameters are those of
  `Blow.tower K j`, the adversary of Theorem 6.4: the `i`-th blow-up below the clique has
  `D = levelDeg K (i-1)` and blocks of size `levelDeg K i = (K-1)^i (K-2) + 1 = b_{j-i+1}`.
* `Str.HjK K j` is the digraph `H_j(K)` of the paper, on the vertex set `Fin (towerSize K j)`,
  `towerSize K j = K · b_j ⋯ b_1`: there is an arc `u → v` iff `u ∈ canonSeq K j v`
  (`canonSeq` is defined in `KnownGraphs.lean`).  `HjK_zero`: `H^{(j)} = K_K` is the transitive
  tournament on `K` vertices.  `HjK_succ`: each further level is `Bl_ρ` of the previous one with
  blocks `S(w) = {wR, …, wR+R-1}` of size `R = levelDeg K (i+1)` and the server assignment
  `ρ(w, v) = wR + (r mod R)`, where `v` is the `r`-th out-neighbour of `w` (`r = 0, 1, …`).
  The graph of Theorem 1.3, `knownGraph K j N` (used by `known_graph_three_floor`), is the
  underlying graph of `H_j(K)` followed by `N - K b_j ⋯ b_1` isolated vertices.
* `Str.IsBlTower K j H`: the sequence `H` arises from `K_K` by `j` applications of `Bl_ρ` with
  blocks of sizes `b_j, …, b_1` and arbitrary server assignments.  "By Lemma 7.1, `H_j(K)` is well
  defined up to isomorphism" is `IsBlTower.spec` (every such `H` is isomorphic to `canonSeq K j`)
  and `IsBlTower.seqIso`; `canonSeq K j` is the representative with `ρ(w, v) = wR + (r mod R)`.
* `Str.arcRel h` is the digraph of a history `h`, oriented by arrival (`u → v` iff `u` is an
  earlier neighbour of `v`); `History.graph h` is its underlying graph.

## Results

Everything except forcing is proved against *every* `OnlineAlg`, proper or not: the adversary and
all its inner rules are functions of arbitrary histories, and the proofs apply the statement of
the level above to the induced algorithm `strInduced`, which is not proper in general.

* `Str.strTower_spec`: the play of `𝒜^str` against any algorithm follows a valid input sequence
  `H` for exactly `towerSize K j` vertices and then stops; `H` is an `IsBlTower K j` (the paper's
  proof: `G^{(ℓ-1)} = Bl_ρ(G^{(ℓ)})` with `ρ(w, v) = x_{w,v}`), hence isomorphic to `H_j(K)` as a
  digraph (`SeqIso`, Lemma 7.1 once per level).
* **Lemma 7.2** `Str.lemma_7_2`: when the play of `𝒜^str` against any algorithm has stopped, the
  final graph, oriented by arrival, is isomorphic to `H_j(K)`: `arcRel h ≃r HjK K j`.  Variants:
  `lemma_7_2_seq` (the form of `Iso.lean`: the final history is the run on an input `H` with
  `SeqIso H (canonSeq K j) (towerSize K j)`), `lemma_7_2_graph` (graph isomorphism of the
  underlying graphs), `lemma_7_2_landsIn` (`𝒜^str` lands in the class `IsHjK K j`).
* Size: `strTower_stopsAt_iff` (the play stops after exactly `towerSize K j` rounds),
  `strTower_length`, `strTower_sizeLE`, and `towerSize_eq`, `towerSize_le` of `Forcing.lean`.
* "All these adversaries are rules defined on every history": `strTower_move_eq_none_iff` (on
  *every* history `h`, whatever its colours, `𝒜^str` stops iff `|h| ≥ towerSize K j`) and
  `strTower_move_valid` (its moves name earlier vertices only); `strTower_inner` (in every play,
  at every moment, also after the `K`-th colour, the play that the lowest blow-up runs internally
  is the play of the inner adversary `strTower K j` against the induced algorithm; since this
  holds for every algorithm, it applies in turn to the blow-ups above, with the induced
  algorithms in place of `X`: `strTower_inner_all`).  `strInduced_not_isProper`: an explicit play
  (`K = 3`, one level) in which the colouring reported to the inner adversary is improper.
* "Until the algorithm uses its `K`-th colour, `𝒜^str` makes exactly the moves of the adversary of
  Theorem 6.4": `strTower_move_eq` (on every history with fewer than `K` colours the two
  adversaries make the same move), `strTower_hist_eq_tower` (the two plays coincide up to the
  first moment with `K` colours).  "So it also forces `K` colours": `strTower_forces`.
* Colourability: `strTower_colorable`, `strTower_landsIn_colorable`.
* The proof of Theorem 1.3 for `G`: `Str.strPad K j N` is Alice's strategy (play `𝒜^str`, then
  present isolated vertices up to `N` vertices).  `strPad_final_graph`: the final graph of every
  play is isomorphic to `G = knownGraph K j N`; `strPad_legal`: at every moment the presented
  graph is isomorphic to an induced subgraph of `G`, so her moves are legal; `strPad_forces`: she
  forces `K` colours; `known_graph_adversary`: hence `χ_ol(G) ≥ K`.  The statements of
  Theorem 1.3 about `G` are derived from it in `StrKnown.lean`.
-/

@[expose] public section

namespace OnlineColouring.Str

open Finset
open Blow (Follows clean R deg stack tower)

/-! ### The adversary `𝒜^str` -/

/-- `A` with `i` blow-ups `Bstr` below it, with the parameters of `Blow.stack`. -/
def strStack (K D : ℕ) (A : Adversary) : ℕ → Adversary
  | 0 => A
  | i + 1 => Bstr K (deg K D i) (strStack K D A i)

/-- **The adversary `𝒜^str` of Section 7**: the clique `K_K` with `j` blow-ups below it that
complete every block. -/
def strTower (K j : ℕ) : Adversary := strStack K (K - 1) (Adversary.clique K) j

theorem strTower_succ {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    strTower K (j + 1) = Bstr K (levelDeg K j) (strTower K j) := by
  rw [← Blow.deg_eq_levelDeg hK j]
  rfl

/-! ### The graph `H_j(K)` -/

/-- **The digraph `H_j(K)`** on `K b_j ⋯ b_1` vertices: an arc `u → v` iff `u ∈ canonSeq K j v`. -/
def HjK (K j : ℕ) (u v : Fin (towerSize K j)) : Prop := (u : ℕ) ∈ canonSeq K j v

/-- `H^{(j)} = K_K`, viewed as a transitive tournament. -/
theorem HjK_zero (K : ℕ) (u v : Fin (towerSize K 0)) : HjK K 0 u v ↔ u < v := by
  change (u : ℕ) ∈ range v ↔ u < v
  rw [mem_range, Fin.lt_def]

/-- `H^{(ℓ-1)} = Bl_ρ(H^{(ℓ)})` with blocks of size `R = levelDeg K (j+1)`: the vertex `x` lies in
the block `S(x / R)`, and there is an arc `x → p` iff `x / R → p / R` is an arc of the previous
level and `x` is the server `ρ(x / R, p / R)`, the vertex in position `r mod R` of its block, where
`p / R` is the `r`-th out-neighbour of `x / R`. -/
theorem HjK_succ (K j : ℕ) (x p : Fin (towerSize K (j + 1))) :
    HjK K (j + 1) x p ↔
      (x : ℕ) / levelDeg K (j + 1) ∈ canonSeq K j ((p : ℕ) / levelDeg K (j + 1)) ∧
      (x : ℕ) % levelDeg K (j + 1) =
        rank (canonSeq K j) ((x : ℕ) / levelDeg K (j + 1)) ((p : ℕ) / levelDeg K (j + 1)) %
          levelDeg K (j + 1) :=
  mem_blowSeq_iff_mod (one_le_levelDeg K (j + 1)) (modPerm (one_le_levelDeg K (j + 1)))

/-- `IsBlTower K j H`: the input sequence `H` is obtained from the transitive tournament `K_K` by
`j` applications of `Bl_ρ`, with blocks of sizes `b_j, …, b_1` and arbitrary server assignments
(`blowSeq R H σ` is `Bl_ρ(H)` for `ρ(w, v) = wR + σ_w(r)`, where `v` is the `r`-th out-neighbour of
`w`; every server assignment arises in this way from a block permutation `σ`). -/
inductive IsBlTower (K : ℕ) : ℕ → (ℕ → Finset ℕ) → Prop
  | clique : IsBlTower K 0 cliqueSeq
  | blow {j : ℕ} {H : ℕ → Finset ℕ} {σ : ℕ → ℕ → ℕ} :
      IsBlTower K j H → BlockPerm (levelDeg K (j + 1)) σ →
        IsBlTower K (j + 1) (blowSeq (levelDeg K (j + 1)) H σ)

theorem canonSeq_isBlTower (K j : ℕ) : IsBlTower K j (canonSeq K j) := by
  induction j with
  | zero => exact .clique
  | succ j ih => exact .blow ih (modPerm (one_le_levelDeg K (j + 1)))

/-- **`H_j(K)` is well defined up to isomorphism** (Lemma 7.1 once per level): every sequence
obtained from `K_K` by `j` applications of `Bl_ρ` with blocks of sizes `b_j, …, b_1` is isomorphic,
as a digraph on its first `K b_j ⋯ b_1` vertices, to `canonSeq K j`.  Its out-degrees are at most
`levelDeg K j`. -/
theorem IsBlTower.spec {K : ℕ} (hK : 2 ≤ K) {j : ℕ} {H : ℕ → Finset ℕ} (h : IsBlTower K j H) :
    ValidSeq H ∧ (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
      SeqIso H (canonSeq K j) (towerSize K j) := by
  induction h with
  | clique =>
    exact ⟨cliqueSeq_valid, fun w _ => by rw [levelDeg_zero hK]; exact postDeg_cliqueSeq_le K w,
      SeqIso.refl _ _⟩
  | @blow j H σ _ hσ ih =>
    obtain ⟨hH, hdeg, hiso⟩ := ih
    have hR : 0 < levelDeg K (j + 1) := one_le_levelDeg K (j + 1)
    have hdeg' : ∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K (j + 1) :=
      fun w hw => (hdeg w hw).trans (levelDeg_le_succ hK j)
    have hdegc' : ∀ w < towerSize K j,
        postDeg (canonSeq K j) (towerSize K j) w ≤ levelDeg K (j + 1) :=
      fun w hw => ((canonSeq_spec hK j).2 w hw).trans (levelDeg_le_succ hK j)
    exact ⟨blowSeq_valid hH hR hσ, fun w _ => postDeg_blowSeq_le hH hR hσ hdeg' w,
      hiso.blowSeq hR hσ (modPerm hR) hdeg' hdegc'⟩

theorem seqIso_symm {H H' : ℕ → Finset ℕ} {m : ℕ} (h : SeqIso H H' m) : SeqIso H' H m := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun u v => ?_⟩
  rw [hφ (φ.symm u) (φ.symm v), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem seqIso_trans {H H' H'' : ℕ → Finset ℕ} {m : ℕ} (h : SeqIso H H' m)
    (h' : SeqIso H' H'' m) : SeqIso H H'' m := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  exact ⟨φ.trans ψ, fun u v => (hφ u v).trans (hψ (φ u) (φ v))⟩

/-- Any two such sequences are isomorphic on their first `K b_j ⋯ b_1` vertices: the server
assignments do not matter. -/
theorem IsBlTower.seqIso {K : ℕ} (hK : 2 ≤ K) {j : ℕ} {H H' : ℕ → Finset ℕ}
    (h : IsBlTower K j H) (h' : IsBlTower K j H') : SeqIso H H' (towerSize K j) :=
  seqIso_trans (h.spec hK).2.2 (seqIso_symm (h'.spec hK).2.2)

/-- The digraph of a history, oriented by arrival: an arc `u → v` iff `u` is an earlier neighbour
of `v`. -/
def arcRel (h : History) (u v : Fin h.length) : Prop := (u : ℕ) < v ∧ (u : ℕ) ∈ (h.get v).1

/-- The class of ordered graphs whose orientation by arrival is isomorphic to `H_j(K)`. -/
def IsHjK (K j : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  Nonempty ((fun u v : Fin n => u < v ∧ G.Adj u v) ≃r HjK K j)

theorem arcRel_iff_graph (h : History) (u v : Fin h.length) :
    arcRel h u v ↔ u < v ∧ h.graph.Adj u v := by
  rw [History.graph_adj]
  constructor
  · exact fun hh => ⟨Fin.lt_def.2 hh.1, Or.inl hh⟩
  · rintro ⟨huv, hh | hh⟩
    · exact hh
    · exact absurd (Fin.lt_def.1 huv) (lt_asymm hh.1)

/-- The final history of a play that follows a valid sequence `H` isomorphic to `H₀`: its digraph
is isomorphic to that of `H₀`. -/
theorem arcRel_iso {X : OnlineAlg} {H H₀ : ℕ → Finset ℕ} {n : ℕ} (hH : ValidSeq H)
    (hiso : SeqIso H H₀ n) {h : History} (hh : h = runHist X H n) :
    Nonempty (arcRel h ≃r fun u v : Fin n => (u : ℕ) ∈ H₀ v) := by
  subst hh
  obtain ⟨φ, hφ⟩ := hiso
  have hlen : (runHist X H n).length = n := length_runHist n
  refine ⟨⟨(finCongr hlen).trans φ, ?_⟩⟩
  intro u v
  change ((φ (finCongr hlen u) : ℕ) ∈ H₀ (φ (finCongr hlen v))) ↔
    ((u : ℕ) < v ∧ (u : ℕ) ∈ ((runHist X H n).get v).1)
  rw [← hφ]
  simp only [finCongr_apply, Fin.val_cast, List.get_eq_getElem, getElem_runHist]
  exact ⟨fun hm => ⟨mem_range.1 (hH _ hm), hm⟩, fun hm => hm.2⟩

/-- An isomorphism of the digraphs is an isomorphism of the underlying graphs. -/
theorem graph_iso_of_arcRel_iso {h : History} {H₀ : ℕ → Finset ℕ} (hH₀ : ValidSeq H₀) {n : ℕ}
    (e : arcRel h ≃r fun u v : Fin n => (u : ℕ) ∈ H₀ v) :
    Nonempty (h.graph ≃g (OnlineInput.ofSeq H₀ hH₀ n).graph) :=
  ⟨⟨e.toEquiv, fun {u v} => by
    rw [OnlineInput.ofSeq_adj, History.graph_adj]
    exact or_congr (e.map_rel_iff (a := u) (b := v)) (e.map_rel_iff (a := v) (b := u))⟩⟩

/-- A prefix of a play that follows a sequence `H` isomorphic to `H₀`: its graph is isomorphic to
an induced subgraph of the graph of `H₀`. -/
theorem graph_embedding_of_prefix {X : OnlineAlg} {H H₀ : ℕ → Finset ℕ} {n t : ℕ}
    (hH : ValidSeq H) (hH₀ : ValidSeq H₀) (ht : t ≤ n) (hiso : SeqIso H H₀ n) {h : History}
    (hh : h = runHist X H t) : Nonempty (h.graph ↪g (OnlineInput.ofSeq H₀ hH₀ n).graph) := by
  subst hh
  obtain ⟨φ, hφ⟩ := hiso
  have hle : (runHist X H t).length ≤ n := by rw [length_runHist]; exact ht
  refine ⟨⟨⟨fun u => φ (Fin.castLE hle u),
    fun u v huv => Fin.castLE_injective hle (φ.injective huv)⟩, ?_⟩⟩
  intro u v
  change (OnlineInput.ofSeq H₀ hH₀ n).graph.Adj (φ (Fin.castLE hle u)) (φ (Fin.castLE hle v)) ↔ _
  rw [OnlineInput.ofSeq_adj, ← hφ, ← hφ, Blow.graph_runHist_adj]
  simp only [Fin.val_castLE]
  constructor
  · rintro (hm | hm)
    · exact Or.inl ⟨mem_range.1 (hH _ hm), hm⟩
    · exact Or.inr ⟨mem_range.1 (hH _ hm), hm⟩
  · rintro (hm | hm)
    · exact Or.inl hm.2
    · exact Or.inr hm.2

/-! ### The play of `𝒜^str` -/

/-- **The play of `𝒜^str`** against an arbitrary algorithm `X` (proper or not).  It follows a valid
input sequence `H` for exactly `towerSize K j = K b_j ⋯ b_1` vertices and then stops.  The sequence
`H` is obtained from `K_K` by `j` applications of `Bl_ρ` with blocks of sizes `b_j, …, b_1`
(`IsBlTower`; the server assignment `ρ(w, v) = x_{w,v}` is read off from the reserves), so its
first `towerSize K j` vertices have post-degree at most `levelDeg K j` and form a digraph
isomorphic to `H_j(K)`.  They form a `j`-fold full blow-up of `K_K` in which every vertex has at
most `K - 1` earlier neighbours. -/
theorem strTower_spec {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ X : OnlineAlg, ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H),
      Follows (strTower K j) X H (towerSize K j) ∧
      (∀ w < towerSize K j, postDeg H (towerSize K j) w ≤ levelDeg K j) ∧
      SeqIso H (canonSeq K j) (towerSize K j) ∧
      IsFullTower K j (OnlineInput.ofSeq H hH (towerSize K j)).toOrdGraph ∧
      (∀ v < towerSize K j, (H v).card ≤ K - 1) ∧ IsBlTower K j H := by
  induction j with
  | zero =>
    intro X
    refine ⟨cliqueSeq, cliqueSeq_valid, Adversary.clique_hist K X, ?_, SeqIso.refl _ _, ?_, ?_,
      .clique⟩
    · intro w _
      rw [levelDeg_zero hK]
      exact postDeg_cliqueSeq_le K w
    · change IsFullTower K 0 (OnlineInput.ofSeq cliqueSeq cliqueSeq_valid K).toOrdGraph
      rw [ofSeq_cliqueSeq]
      exact .clique
    · intro v hv
      change v < K at hv
      rw [cliqueSeq, card_range]
      omega
  | succ j ih =>
    intro X
    obtain ⟨H, hH, hfol, hdeg, -, htower, hcard, hbl⟩ := ih (strInduced X K (levelDeg K j))
    rw [strTower_succ hK j]
    have hRj : levelDeg K (j + 1) = R K (levelDeg K j) := levelDeg_succ K j
    set D := levelDeg K j with hDdef
    set m := towerSize K j with hmdef
    have hR : 0 < R K D := Blow.R_pos K D
    have hDR : D ≤ R K D := Blow.le_R hK
    have hσ := strResPos_blockPerm (D := D) hR (strOutCol (R K D) D H X)
    have hdeg' : ∀ w < m, postDeg H m w ≤ R K D := fun w hw => (hdeg w hw).trans hDR
    have hsize : towerSize K (j + 1) = m * R K D := by rw [← hRj]; rfl
    have hG := strOutSeq_eq (D := D) (X := X) hH (R := R K D)
    -- the play follows `Bl_ρ` of the inner sequence, with `ρ` read off from the reserves
    have hbl' : IsBlTower K (j + 1)
        (blowSeq (R K D) H (strResPos (R K D) D (strOutCol (R K D) D H X))) := by
      rw [← hRj] at hσ ⊢
      exact .blow hbl hσ
    obtain ⟨-, hdegB, hisoB⟩ := hbl'.spec hK
    refine ⟨blowSeq (R K D) H (strResPos (R K D) D (strOutCol (R K D) D H X)),
      blowSeq_valid hH hR hσ, ?_, hdegB, hisoB, ?_, ?_, hbl'⟩
    · rw [hsize, ← hG]
      exact Bstr_follows hH hfol
    · rw [hsize]
      exact .blowUp htower
        ⟨blowUpOf hH hR hσ hdeg', (blowUpOf_isReservation hH hR hσ hdeg').isFull⟩
    · intro v hv
      rw [hsize] at hv
      refine card_image_le.trans (hcard _ ?_)
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hv)

/-- The play of `𝒜^str` against any algorithm stops after exactly `K b_j ⋯ b_1` rounds. -/
theorem strTower_stopsAt_iff {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (X : OnlineAlg) {p : ℕ} :
    (strTower K j).StopsAt X p ↔ towerSize K j ≤ p := by
  obtain ⟨H, hH, hfol, -⟩ := strTower_spec hK j X
  exact follows_stopsAt_iff hfol

/-- After `p` rounds, `𝒜^str` has presented `min p (K b_j ⋯ b_1)` vertices. -/
theorem strTower_length {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (X : OnlineAlg) (p : ℕ) :
    ((strTower K j).hist X p).length = min p (towerSize K j) := by
  obtain ⟨H, hH, hfol, -⟩ := strTower_spec hK j X
  exact follows_length hfol p

/-- Every block is completed: the final graph of every play of `𝒜^str` has exactly
`K b_j ⋯ b_1` vertices. -/
theorem strTower_final_length {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (X : OnlineAlg) {p : ℕ}
    (hp : (strTower K j).StopsAt X p) :
    ((strTower K j).hist X p).length = K * ∏ ℓ ∈ Icc 1 j, blockSize K j ℓ := by
  rw [strTower_length hK j X p, min_eq_right ((strTower_stopsAt_iff hK j X).1 hp), towerSize_eq]

/-- `𝒜^str` has size at most `K b_j ⋯ b_1 ≤ K^((j+1)(j+2)/2)` (see `towerSize_eq`,
`towerSize_le`). -/
theorem strTower_sizeLE {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : (strTower K j).SizeLE (towerSize K j) :=
  fun X _ p => (strTower_length hK j X p).le.trans (min_le_right _ _)

/-! ### Lemma 7.2 -/

/-- **Lemma 7.2 (one final graph), in the form of `Iso.lean`.**  When the play of `𝒜^str` against
any algorithm has stopped, the history is the run of the algorithm on an input sequence `H` whose
first `K b_j ⋯ b_1` vertices form a digraph isomorphic to `H_j(K)`. -/
theorem lemma_7_2_seq {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (Alg : OnlineAlg) {p : ℕ}
    (hp : (strTower K j).StopsAt Alg p) :
    ∃ H : ℕ → Finset ℕ, ValidSeq H ∧
      (strTower K j).hist Alg p = runHist Alg H (towerSize K j) ∧
      SeqIso H (canonSeq K j) (towerSize K j) := by
  obtain ⟨H, hH, hfol, -, hiso, -⟩ := strTower_spec hK j Alg
  refine ⟨H, hH, ?_, hiso⟩
  rw [hfol p, min_eq_right ((follows_stopsAt_iff hfol).1 hp)]

/-- **Lemma 7.2 (one final graph).**  Against every deterministic algorithm, the final graph of
`𝒜^str`, oriented by arrival, is isomorphic to `H_j(K)`.  (The algorithm need not be proper.) -/
theorem lemma_7_2 {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (Alg : OnlineAlg) {p : ℕ}
    (hp : (strTower K j).StopsAt Alg p) :
    Nonempty (arcRel ((strTower K j).hist Alg p) ≃r HjK K j) := by
  obtain ⟨H, hH, hhist, hiso⟩ := lemma_7_2_seq hK j Alg hp
  exact arcRel_iso hH hiso hhist

/-- Lemma 7.2 for the underlying graphs: the final graph of `𝒜^str` is isomorphic to the graph of
`H_j(K)`. -/
theorem lemma_7_2_graph {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (Alg : OnlineAlg) {p : ℕ}
    (hp : (strTower K j).StopsAt Alg p) :
    Nonempty (((strTower K j).hist Alg p).graph ≃g
      (OnlineInput.ofSeq (canonSeq K j) (canonSeq_valid K j) (towerSize K j)).graph) := by
  obtain ⟨e⟩ := lemma_7_2 hK j Alg hp
  exact graph_iso_of_arcRel_iso (canonSeq_valid K j) e

/-- Lemma 7.2 in the terms of Definition 4.2: `𝒜^str` lands in the class of ordered graphs whose
orientation by arrival is isomorphic to `H_j(K)`. -/
theorem lemma_7_2_landsIn {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : (strTower K j).LandsIn (IsHjK K j) := by
  intro Alg _ p hp
  obtain ⟨e⟩ := lemma_7_2 hK j Alg hp
  refine ⟨⟨e.toEquiv, fun {u v} => ?_⟩⟩
  rw [← arcRel_iff_graph]
  exact e.map_rel_iff

/-! ### The rules are defined on every history -/

theorem innerSeq_clean_valid (g : History) (s : Finset ℕ) :
    ValidSeq (innerSeq (clean g) (s ∩ range g.length)) := by
  intro i
  unfold innerSeq
  rw [Blow.length_clean]
  split_ifs with h1 h2
  · rw [Blow.getD_clean h1]
    exact inter_subset_right
  · rw [h2]
    exact inter_subset_right
  · exact empty_subset _

/-- On every history, a move of `Bstr K D A` names earlier vertices only. -/
theorem Bstr_move_valid (K D : ℕ) (A : Adversary) {h : History} {s : Finset ℕ}
    (hs : (Bstr K D A).move h = some s) : s ⊆ range h.length := by
  change (A.move (strInnerHist K D A h)).map _ = some s at hs
  obtain ⟨s', -, rfl⟩ := Option.map_eq_some_iff.1 hs
  intro x hx
  exact mem_range.2 (lt_of_mem_blowSeq (innerSeq_clean_valid _ _) (Blow.R_pos K D)
    (strResPos_blockPerm (Blow.R_pos K D) _) hx)

/-- **`𝒜^str` is defined on every history**: whatever the colours in `h` (they need not form a
proper colouring, and `h` need not arise in a play), `𝒜^str` stops at `h` if and only if `h` has
at least `K b_j ⋯ b_1` vertices. -/
theorem strTower_move_eq_none_iff {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (h : History) :
    (strTower K j).move h = none ↔ towerSize K j ≤ h.length := by
  induction j generalizing h with
  | zero =>
    change (if h.length < K then some (range h.length) else none) = none ↔ K ≤ h.length
    split_ifs with hlt
    · simp only [false_iff, not_le]
      exact hlt
    · simp only [true_iff]
      exact not_lt.1 hlt
  | succ j ih =>
    rw [strTower_succ hK j]
    change (((strTower K j).move (strInnerHist K (levelDeg K j) (strTower K j) h)).map _) = none ↔ _
    rw [Option.map_eq_none_iff, ih]
    have hlen : (strInnerHist K (levelDeg K j) (strTower K j) h).length =
        min (h.length / R K (levelDeg K j)) (towerSize K j) := strTower_length hK j _ _
    have hRj : levelDeg K (j + 1) = R K (levelDeg K j) := levelDeg_succ K j
    have hsize : towerSize K (j + 1) = towerSize K j * R K (levelDeg K j) := by
      rw [← hRj]
      rfl
    rw [hlen, hsize, ← Nat.le_div_iff_mul_le (Blow.R_pos K _)]
    omega

/-- On every history, a move of `𝒜^str` names earlier vertices only. -/
theorem strTower_move_valid (K j : ℕ) {h : History} {s : Finset ℕ}
    (hs : (strTower K j).move h = some s) : s ⊆ range h.length := by
  cases j with
  | zero =>
    change (if h.length < K then some (range h.length) else none) = some s at hs
    split_ifs at hs with hlt
    · rw [← Option.some.inj hs]
  | succ j => exact Bstr_move_valid _ _ _ hs

/-- **The inner play of `𝒜^str`.**  In every play against any algorithm `X`, at every moment, also
after the `K`-th colour, the play that the lowest blow-up runs internally is the play of the inner
adversary `strTower K j` against the induced algorithm `strInduced X K D`, which need not be
proper.  (For the blow-ups above, apply the statement to the induced algorithm.) -/
theorem strTower_inner {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (X : OnlineAlg) (p : ℕ) :
    strInnerHist K (levelDeg K j) (strTower K j) ((strTower K (j + 1)).hist X p) =
      (strTower K j).hist (strInduced X K (levelDeg K j))
        (((strTower K (j + 1)).hist X p).length / R K (levelDeg K j)) := by
  obtain ⟨H, hH, hfol, -⟩ := strTower_spec hK j (strInduced X K (levelDeg K j))
  rw [strTower_succ hK j]
  exact Bstr_inner hH hfol p

/-- The algorithm that the adversary `strTower K i` faces inside `strTower K (i + d)` when the
latter plays against `X`: the `d`-fold induced algorithm. -/
def strAlgAt (K i : ℕ) : ℕ → OnlineAlg → OnlineAlg
  | 0, X => X
  | d + 1, X => strAlgAt K i d (strInduced X K (levelDeg K (i + d)))

/-- The play of `strTower K i` that is run inside `strTower K (i + d)` at the history `h` (the
inner play of the inner play …, `d` times). -/
def strInnerAt (K i : ℕ) : ℕ → History → History
  | 0, h => h
  | d + 1, h => strInnerAt K i d (strInnerHist K (levelDeg K (i + d)) (strTower K (i + d)) h)

/-- **The inner plays of `𝒜^str` at all levels.**  In every play of `𝒜^str = strTower K (i + d)`
against any algorithm `X`, at every moment, the play of the adversary `strTower K i` of the level
`d` blow-ups higher that is run internally is a play of that adversary against the `d`-fold
induced algorithm `strAlgAt K i d X`. -/
theorem strTower_inner_all {K : ℕ} (hK : 2 ≤ K) (i d : ℕ) :
    ∀ (X : OnlineAlg) (p : ℕ), ∃ q,
      strInnerAt K i d ((strTower K (i + d)).hist X p) =
        (strTower K i).hist (strAlgAt K i d X) q := by
  induction d with
  | zero => exact fun X p => ⟨p, rfl⟩
  | succ d ih =>
    intro X p
    obtain ⟨q, hq⟩ := ih (strInduced X K (levelDeg K (i + d)))
      (((strTower K (i + d + 1)).hist X p).length / R K (levelDeg K (i + d)))
    refine ⟨q, ?_⟩
    change strInnerAt K i d (strInnerHist K (levelDeg K (i + d)) (strTower K (i + d))
      ((strTower K (i + d + 1)).hist X p)) =
        (strTower K i).hist (strAlgAt K i d (strInduced X K (levelDeg K (i + d)))) q
    rw [strTower_inner hK (i + d) X p]
    exact hq

/-- The algorithm of `strInduced_not_isProper`: it gives the vertices `0, …, 8` the colours
`0, 1, 2, 1, 1, 1, 0, 0, 0` (patched with fresh colours, so that it is proper on every history). -/
def exampleAlg : OnlineAlg :=
  (⟨fun h _ => [0, 1, 2, 1, 1, 1, 0, 0, 0].getD h.length 0⟩ : OnlineAlg).patch

/-- **After the `K`-th colour, the colourings reported to the inner adversaries may be improper.**
Take `K = 3` and one level (`D = 2`, blocks of size `3`).  The proper algorithm `exampleAlg` uses
three colours on the block of `v_1`, so no colour occurs twice there and `col(v_1) = 0`; it gives
the block of `v_2` the colour `1` and the block of `v_3`, whose servers both have colour `1`, the
colour `0`.  So the induced algorithm, against which the clique plays inside `𝒜^str`, gives the
adjacent vertices `v_1` and `v_3` the same colour: it is not proper.  This is why the results of
this file are proved for arbitrary algorithms. -/
theorem strInduced_not_isProper :
    exampleAlg.IsProper ∧
      runCol (strInduced exampleAlg 3 2) cliqueSeq 2 =
        runCol (strInduced exampleAlg 3 2) cliqueSeq 0 ∧
      ¬ (strInduced exampleAlg 3 2).IsProper := by
  have h : runCol (strInduced exampleAlg 3 2) cliqueSeq 2 =
      runCol (strInduced exampleAlg 3 2) cliqueSeq 0 := by decide +kernel
  exact ⟨OnlineAlg.patch_isProper _, h,
    fun hP => runCol_ne hP (mem_range.2 (by norm_num : 0 < 2)) (by norm_num) h⟩

/-! ### Until the `K`-th colour: the adversary of Theorem 6.4 -/

/-- **Until the algorithm uses its `K`-th colour, `𝒜^str` makes exactly the moves of the adversary
of Theorem 6.4**: on every history with fewer than `K` colours, the two adversaries make the same
move. -/
theorem strTower_move_eq {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {h : History}
    (hh : (usedColours h).card < K) : (strTower K j).move h = (tower K j).move h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    exact Bstr_move_eq (Blow.one_le_deg (by omega) j) (fun g hg => ih hg) hh

/-- Two adversaries that make the same moves on all histories with fewer than `K` colours have
the same play against `X` as long as fewer than `K` colours are in use. -/
theorem hist_eq_of_move_eq {K : ℕ} {A A' : Adversary}
    (hA : ∀ g : History, (usedColours g).card < K → A'.move g = A.move g) (X : OnlineAlg) :
    ∀ p, (∀ q < p, (usedColours (A.hist X q)).card < K) → A'.hist X p = A.hist X p := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
    intro hlt
    have ih' := ih fun q hq => hlt q (Nat.lt_succ_of_lt hq)
    have hmv := hA _ (hlt p (Nat.lt_succ_self p))
    cases hm : A.move (A.hist X p) with
    | none =>
      rw [Blow.hist_succ_none hm, Blow.hist_succ_none (by rw [ih', hmv]; exact hm), ih']
    | some s =>
      rw [Blow.hist_succ_some hm, Blow.hist_succ_some (by rw [ih', hmv]; exact hm), ih']

/-- The plays of `𝒜^str` and of the adversary of Theorem 6.4 against the same algorithm coincide
up to the first moment at which `K` colours are in use (where the latter stops). -/
theorem strTower_hist_eq_tower {K : ℕ} (hK : 2 ≤ K) (j : ℕ) (X : OnlineAlg) (p : ℕ)
    (hp : ∀ q < p, (usedColours ((tower K j).hist X q)).card < K) :
    (strTower K j).hist X p = (tower K j).hist X p :=
  hist_eq_of_move_eq (fun _ hg => strTower_move_eq hK j hg) X p hp

/-- The colours in use at the end of a play of `𝒜^str` against a proper algorithm: at least `K`
on the first `towerSize K j` vertices of the sequence that the play follows. -/
theorem strTower_colours {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper) :
    K ≤ (usedColours ((strTower K j).hist Alg (towerSize K j))).card := by
  obtain ⟨H, hH, T, -, -, -, -, hfolT, hTK, hlt⟩ := Blow.tower_play hK j Alg hAlg
  have heq : (strTower K j).hist Alg T = (tower K j).hist Alg T := by
    apply strTower_hist_eq_tower hK j Alg T
    intro q hq
    rw [hfolT q, min_eq_left hq.le, usedColours_runHist]
    exact hlt q hq
  obtain ⟨H', hH', hfol, -⟩ := strTower_spec hK j Alg
  have hT : T ≤ towerSize K j := by
    have h1 := congrArg List.length heq
    rw [follows_length hfol, follows_length hfolT, min_self] at h1
    omega
  have hsub : usedColours ((strTower K j).hist Alg T) ⊆
      usedColours ((strTower K j).hist Alg (towerSize K j)) := by
    rw [hfol T, hfol (towerSize K j), min_self, min_eq_left hT, usedColours_runHist,
      usedColours_runHist]
    exact image_subset_image (range_subset_range.2 hT)
  refine le_trans ?_ (card_le_card hsub)
  rw [heq, hfolT T, min_self, usedColours_runHist]
  exact hTK

/-- **`𝒜^str` forces `K` colours.** -/
theorem strTower_forces {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : (strTower K j).Forces K :=
  fun Alg hAlg => ⟨towerSize K j, (strTower_stopsAt_iff hK j Alg).2 le_rfl,
    strTower_colours hK j hAlg⟩

/-! ### Colourability -/

/-- Every graph presented by `𝒜^str` (against any algorithm) is `k`-colourable if
`|P_j(k)| ≥ K`. -/
theorem strTower_colorable {k K j : ℕ} (hK : 2 ≤ K) (hKj : K ≤ Fintype.card (LabelPoset k j))
    (X : OnlineAlg) (p : ℕ) : ((strTower K j).hist X p).graph.Colorable k := by
  obtain ⟨H, hH, hfol, -, -, htower, -⟩ := strTower_spec hK j X
  rw [hfol p]
  exact hasLabelling_labelPoset_zero_iff.1 (Blow.hasLabelling_runHist hH (min_le_right _ _)
    (hasLabelling_labelPoset_zero_iff.2 (htower.isTower.colorable hKj)))

theorem strTower_landsIn_colorable {k K j : ℕ} (hK : 2 ≤ K)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    (strTower K j).LandsIn fun _ G => G.Colorable k :=
  fun X _ p _ => strTower_colorable hK hKj X p

/-! ### The known-graph game (proof of Theorem 1.3 for `G`) -/

/-- **Alice's strategy in the known-graph game**: play `𝒜^str`, then present isolated vertices
until `N` vertices have been presented. -/
def strPad (K j N : ℕ) : Adversary :=
  ⟨fun h => if h.length < towerSize K j then (strTower K j).move h
    else if h.length < N then some ∅ else none⟩

/-- The play of `strPad K j N` against any algorithm `X`: it follows `H` for `K b_j ⋯ b_1`
vertices, where `H` is the sequence that `𝒜^str` follows against `X`, then presents isolated
vertices, and stops after exactly `N` vertices. -/
theorem strPad_spec {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {N : ℕ} (hN : towerSize K j ≤ N)
    (X : OnlineAlg) :
    ∃ H : ℕ → Finset ℕ, ValidSeq H ∧ Follows (strTower K j) X H (towerSize K j) ∧
      Follows (strPad K j N) X (truncSeq H (towerSize K j)) N ∧
      SeqIso H (canonSeq K j) (towerSize K j) := by
  obtain ⟨H, hH, hfol, -, hiso, -⟩ := strTower_spec hK j X
  refine ⟨H, hH, hfol, follows_of_moves (fun t ht => ?_) ?_, hiso⟩
  · change (if (runHist X (truncSeq H (towerSize K j)) t).length < towerSize K j then _
      else if (runHist X (truncSeq H (towerSize K j)) t).length < N then some ∅ else none) = _
    rw [length_runHist]
    by_cases htm : t < towerSize K j
    · have hrun : runHist X (truncSeq H (towerSize K j)) t = runHist X H t :=
        runHist_congr fun i hi => by simp [truncSeq, hi.trans htm]
      have hmv := follows_move_lt hfol htm
      rw [hfol t, min_eq_left htm.le] at hmv
      rw [ite_eq_left htm, hrun, hmv]
      simp [truncSeq, htm]
    · rw [ite_eq_right htm, ite_eq_left ht]
      simp [truncSeq, htm]
  · change (if (runHist X (truncSeq H (towerSize K j)) N).length < towerSize K j then _
      else if (runHist X (truncSeq H (towerSize K j)) N).length < N then some ∅ else none) = _
    rw [length_runHist, ite_eq_right (by omega), ite_eq_right (lt_irrefl N)]

/-- Alice's play has exactly `N` vertices. -/
theorem strPad_stopsAt_iff {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {N : ℕ} (hN : towerSize K j ≤ N)
    (X : OnlineAlg) {p : ℕ} : (strPad K j N).StopsAt X p ↔ N ≤ p := by
  obtain ⟨H, -, -, hfol, -⟩ := strPad_spec hK j hN X
  exact follows_stopsAt_iff hfol

/-- **The final graph of Alice's play is `G`**: against every algorithm, the final graph of
`strPad K j N` is isomorphic to `knownGraph K j N` (`H_j(K)` and `N - K b_j ⋯ b_1` isolated
vertices). -/
theorem strPad_final_graph {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {N : ℕ} (hN : towerSize K j ≤ N)
    (X : OnlineAlg) {p : ℕ} (hp : (strPad K j N).StopsAt X p) :
    Nonempty (((strPad K j N).hist X p).graph ≃g knownGraph K j N) := by
  obtain ⟨H, hH, -, hfol, hiso⟩ := strPad_spec hK j hN X
  have hhist : (strPad K j N).hist X p = runHist X (truncSeq H (towerSize K j)) N := by
    rw [hfol p, min_eq_right ((follows_stopsAt_iff hfol).1 hp)]
  obtain ⟨e⟩ := arcRel_iso (truncSeq_valid hH _) (hiso.truncSeq hH (canonSeq_valid K j) hN)
    hhist
  exact graph_iso_of_arcRel_iso (truncSeq_valid (canonSeq_valid K j) _) e

/-- **Alice's moves are legal**: at every moment of every play, the graph presented so far is
isomorphic to an induced subgraph of `G = knownGraph K j N`. -/
theorem strPad_legal {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {N : ℕ} (hN : towerSize K j ≤ N)
    (X : OnlineAlg) (p : ℕ) :
    Nonempty (((strPad K j N).hist X p).graph ↪g knownGraph K j N) := by
  obtain ⟨H, hH, -, hfol, hiso⟩ := strPad_spec hK j hN X
  exact graph_embedding_of_prefix (truncSeq_valid hH _) (truncSeq_valid (canonSeq_valid K j) _)
    (min_le_right p N) (hiso.truncSeq hH (canonSeq_valid K j) hN) (hfol p)

/-- The colours of a proper algorithm on the sequence that `𝒜^str` follows against it. -/
theorem strTower_card_image {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {Alg : OnlineAlg}
    (hAlg : Alg.IsProper) {H : ℕ → Finset ℕ}
    (hfol : Follows (strTower K j) Alg H (towerSize K j)) :
    K ≤ ((range (towerSize K j)).image (runCol Alg H)).card := by
  have := strTower_colours hK j hAlg
  rwa [hfol, min_self, usedColours_runHist] at this

/-- **Alice forces `K` colours**: Bob, a deterministic algorithm that may have `G` built in, ends
with at least `K` colours in use. -/
theorem strPad_forces {K : ℕ} (hK : 2 ≤ K) (j : ℕ) {N : ℕ} (hN : towerSize K j ≤ N) :
    (strPad K j N).Forces K := by
  intro Alg hAlg
  obtain ⟨H, hH, hfolT, hfol, -⟩ := strPad_spec hK j hN Alg
  refine ⟨N, (follows_stopsAt_iff hfol).2 le_rfl, ?_⟩
  rw [hfol N, min_self, usedColours_runHist, ← OnlineInput.cost_ofSeq (hN := truncSeq_valid hH _)]
  exact le_cost_truncSeq hH hN (strTower_card_image hK j hAlg hfolT)

/-- **Theorem 1.3 for `G`, through the adversary `𝒜^str`.**  If `K ≥ 2` and `N ≥ K b_j ⋯ b_1`,
then `χ_ol(knownGraph K j N) ≥ K`: against every proper algorithm, the play of `𝒜^str` followed by
isolated vertices is a presentation of `knownGraph K j N` on which the algorithm uses at least `K`
colours.  (`known_graph_of_inputs` in `KnownGraphs.lean` proves the same statement from inputs
against a fixed algorithm.) -/
theorem known_graph_adversary {K j N : ℕ} (hK : 2 ≤ K) (hN : towerSize K j ≤ N) :
    OnlineChromaticAtLeast (knownGraph K j N) K := by
  intro Alg hAlg
  obtain ⟨H, hH, hfolT, -, hiso⟩ := strPad_spec hK j hN Alg
  exact ⟨_, (hiso.truncSeq hH (canonSeq_valid K j) hN).graphIso _ _,
    le_cost_truncSeq hH hN (strTower_card_image hK j hAlg hfolT)⟩

end OnlineColouring.Str
