module

public import OnlineColouring.Blow

/-!
# Lemma 6.3: stacking reservation blow-ups

Lemma 6.3: *Let `𝒜_j` be an adversary of bounded size and post-degree that forces `K ≥ 2` colours,
and for `i = j-1, …, 0` let `𝒜_i := B(𝒜_{i+1})`, with `D` equal to the post-degree bound of
`𝒜_{i+1}`.  Then every `𝒜_i` forces `K` colours.  Moreover, in every play of `𝒜_0` against a
deterministic algorithm `Alg`, as long as `Alg` has used at most `K - 1` colours, the following
holds at every level: the play that `𝒜_i` runs internally is the play of `𝒜_{i+1}` against the
induced algorithm of level `i`; step 3 is possible; and every colour seen is a colour of `Alg`.
In particular, the server of every arc out of a node `w` of any level has the induced colour
`col(w)`.*

* `Blow.stack K D A i` is `A` with `i` reservation blow-ups below it; the first uses the
  post-degree bound `D` of `A`, each later one the block size of the previous one
  (`Blow.deg K D i`: `deg 0 = D`, `deg (i+1) = (K-1)(deg i - 1) + 1`; in closed form
  `deg (i+1) = (K-1)^(i+1) (D-1) + 1`, `Blow.deg_succ_eq`).
* `Blow.stack_lemma` (first statement; Lemma 6.2 once per level): if `A` forces `K` colours, has
  size at most `N` and post-degree at most `D`, then `stack K D A i` forces `K` colours, has size
  at most `N · ∏_{l=1}^{i} deg l` and post-degree at most `deg i`.
* `Blow.lemma_6_3` is the lemma: `stack K D A i` forces `K` colours, and at every moment of a
  play of `stack K D A i` against a proper algorithm `Alg` at which `Alg` has used at most `K - 1`
  colours, the invariant `Blow.StackOK` holds.  The invariant says, for the lowest blow-up: the
  play that it runs internally is the play of the level above against the induced algorithm;
  every complete block has its induced colour on `deg` of its vertices (step 3 is possible);
  every colour of the internal play is a colour of `Alg` (the invariant carries the set `C` of
  the colours of `Alg` through all levels); the earlier neighbours of the vertex presented next
  are servers, one for each arc into the current node, and the server of the arc out of `w` has
  the induced colour `col(w)` (`Blow.server_colour`); and the same holds for the internal play,
  one level up, with the induced algorithm in the place of `Alg`.  Since every vertex is
  presented at such a moment, the server statement covers every arc of every level.
  `Blow.remark_6_3` is another name of `Blow.lemma_6_3`.  The proof of Theorem 6.4
  (`BlowTower.lean`) uses the lemma for forcing and for "the play ends no later than the first
  vertex below `v_K`".

The second half of the file is the form of Lemma 6.2 that also carries the graphs:
`Blow.Good K N D P A` says that against every proper algorithm the play of `A` follows a valid
input sequence `H` for `q ≤ N` vertices and stops there with `K` colours in use, with
post-degrees at most `D`, and that the graph presented has a `P`-labelling.  `Good.blow` is
Lemma 6.2 together with Lemma 5.2 (labels descend through blow-ups): if `A` is good for
`J*(P)`, then `B(𝒜)` is good for `P`.  `good_of_valid` shows that every adversary whose moves name
earlier vertices only is good as soon as it forces, has the size and post-degree, and its graphs
are labelled.  These are used for Theorem 9.3 (`BlowSlow.lean`) and for Corollary B.2
(`AppBDCheapTopAdv.lean`).
-/

@[expose] public section

namespace OnlineColouring.Blow

open Finset

/-! ### Stacks -/

/-- The post-degree bound after `i` blow-ups below an adversary of post-degree at most `D`; for
`i ≥ 1` it is also the block size of the `i`-th blow-up. -/
def deg (K D : ℕ) : ℕ → ℕ
  | 0 => D
  | i + 1 => R K (deg K D i)

/-- `A` with `i` reservation blow-ups below it. -/
def stack (K D : ℕ) (A : Adversary) : ℕ → Adversary
  | 0 => A
  | i + 1 => B K (deg K D i) (stack K D A i)

theorem one_le_deg {K D : ℕ} (hD : 1 ≤ D) : ∀ i, 1 ≤ deg K D i
  | 0 => hD
  | _ + 1 => R_pos _ _

/-- The block sizes of a stack in closed form: `deg K D (i+1) = (K-1)^(i+1) (D-1) + 1`. -/
theorem deg_succ_eq (K D : ℕ) : ∀ i, deg K D (i + 1) = (K - 1) ^ (i + 1) * (D - 1) + 1
  | 0 => by simp [deg, R]
  | i + 1 => by
    rw [deg, deg_succ_eq K D i, R, Nat.add_sub_cancel, pow_succ (K - 1) (i + 1)]
    ring

/-- **Lemma 6.2, once per level.** -/
theorem stack_lemma {K D N : ℕ} (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary} (hF : A.Forces K)
    (hS : A.SizeLE N) (hP : A.PostDegLE D) (i : ℕ) :
    (stack K D A i).Forces K ∧ (stack K D A i).SizeLE (N * ∏ l ∈ range i, deg K D (l + 1)) ∧
      (stack K D A i).PostDegLE (deg K D i) := by
  induction i with
  | zero => exact ⟨hF, by rw [prod_range_zero, Nat.mul_one]; exact hS, hP⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3, -⟩ := lemma_6_2 hK (one_le_deg hD i) ih.1 ih.2.1 ih.2.2
    refine ⟨h1, ?_, h3⟩
    rw [prod_range_succ, ← Nat.mul_assoc, Nat.mul_comm]
    exact h2

theorem mem_usedColours_iff {h : History} {c : ℕ} :
    c ∈ usedColours h ↔ ∃ i < h.length, colourAt h i = c := by
  constructor
  · intro hc
    simp only [usedColours, List.mem_toFinset, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, hi, colourAt_eq_getElem hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact colourAt_mem_usedColours hi

/-- **The invariant of Lemma 6.3** for the outer history `h` of `stack K D A i` against `Alg`;
`C` is the set of colours of the algorithm that colours the presented graph.  For `i + 1` levels,
with `R` the block size of the lowest blow-up, `m = |h| / R` the number of complete blocks, `Alg'`
the induced algorithm and `g` the play of `stack K D A i` against `Alg'` for `m` rounds, it says:

* the play that `stack K D A (i + 1)` runs internally at `h` is `g`, and `g` has `m` vertices;
* for every complete block `v < m`: the induced colour `col(v)` is the colour of `v` in `g`, it
  occurs on at least `deg K D i` vertices of the block (step 3 is possible), and it is a colour
  used in `h`;
* the servers have the induced colour: if the level above presents the inner vertex `m` with the
  set `s'` of earlier neighbours, then the earlier neighbours of the outer vertex presented next
  are servers `srv w`, one for every earlier neighbour `w < m` of `m`, and `srv w` lies in the
  block of `w` and has the colour `col(w)`;
* every colour seen at this level, that is, every colour of `g`, belongs to `C`;
* the invariant holds for `g`, with `Alg'` in the place of `Alg` and the same `C`. -/
def StackOK (K D : ℕ) (A : Adversary) (C : Finset ℕ) : ℕ → OnlineAlg → History → Prop
  | 0, _, _ => True
  | i + 1, Alg, h =>
    innerHist K (deg K D i) (stack K D A i) h =
        (stack K D A i).hist (induced Alg K (deg K D i)) (h.length / R K (deg K D i)) ∧
      ((stack K D A i).hist (induced Alg K (deg K D i)) (h.length / R K (deg K D i))).length =
        h.length / R K (deg K D i) ∧
      (∀ v < h.length / R K (deg K D i),
        indColour K (deg K D i) h v =
            colourAt ((stack K D A i).hist (induced Alg K (deg K D i))
              (h.length / R K (deg K D i))) v ∧
          deg K D i ≤ ((range (R K (deg K D i))).filter fun u =>
            colourAt h (v * R K (deg K D i) + u) = indColour K (deg K D i) h v).card ∧
          indColour K (deg K D i) h v ∈ usedColours h) ∧
      (∀ s' : Finset ℕ,
        (stack K D A i).move ((stack K D A i).hist (induced Alg K (deg K D i))
            (h.length / R K (deg K D i))) = some s' →
          ∃ srv : ℕ → ℕ,
            (stack K D A (i + 1)).move h =
                some ((s' ∩ range (h.length / R K (deg K D i))).image srv) ∧
              ∀ w ∈ s', w < h.length / R K (deg K D i) →
                srv w / R K (deg K D i) = w ∧
                  colourAt h (srv w) = indColour K (deg K D i) h w) ∧
      usedColours ((stack K D A i).hist (induced Alg K (deg K D i))
        (h.length / R K (deg K D i))) ⊆ C ∧
      StackOK K D A C i (induced Alg K (deg K D i))
        ((stack K D A i).hist (induced Alg K (deg K D i)) (h.length / R K (deg K D i)))

/-- The invariant of Lemma 6.3, for every set `C` that contains the colours of the history. -/
theorem stackOK_of_subset {K D N : ℕ} (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary}
    (hF : A.Forces K) (hS : A.SizeLE N) (hP : A.PostDegLE D) (i : ℕ) :
    ∀ Alg : OnlineAlg, Alg.IsProper → ∀ p,
      (usedColours ((stack K D A i).hist Alg p)).card ≤ K - 1 →
      ∀ C : Finset ℕ, usedColours ((stack K D A i).hist Alg p) ⊆ C →
        StackOK K D A C i Alg ((stack K D A i).hist Alg p) := by
  induction i with
  | zero => intro _ _ _ _ _ _; trivial
  | succ i ih =>
    intro Alg hAlg p hp C hC
    obtain ⟨h1, h2, h3⟩ := stack_lemma hK hD hF hS hP i
    have hDi := one_le_deg (K := K) hD i
    obtain ⟨hA', hmore⟩ := (lemma_6_2 hK hDi h1 h2 h3).2.2.2 Alg hAlg
    obtain ⟨hin, hlen, hcol⟩ := hmore p hp
    have hsub : usedColours ((stack K D A i).hist (induced Alg K (deg K D i))
        (((B K (deg K D i) (stack K D A i)).hist Alg p).length / R K (deg K D i))) ⊆
        usedColours ((B K (deg K D i) (stack K D A i)).hist Alg p) := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := mem_usedColours_iff.1 hc
      rw [hlen] at hv
      obtain ⟨e, -, hmem⟩ := hcol v hv
      rw [← e]
      exact hmem
    exact ⟨hin, hlen, hcol, fun s' hs' => server_colour hK hDi h1 h2 h3 hAlg hp hs',
      hsub.trans hC, ih _ hA' _ ((card_le_card hsub).trans hp) C (hsub.trans hC)⟩

/-- **Lemma 6.3 (stacking).**  Let `A` be an adversary of size at most `N` and post-degree at
most `D ≥ 1` that forces `K ≥ 2` colours, and let `stack K D A i` be `A` with `i` reservation
blow-ups below it, each with `D` equal to the post-degree bound of the adversary above it.  Then
`stack K D A i` forces `K` colours.  Moreover, at every moment of a play of `stack K D A i`
against a proper algorithm `Alg` at which `Alg` has used at most `K - 1` colours, the invariant
`StackOK` holds: at every level, the play that the level runs internally is the play of the level
above against the induced algorithm, step 3 is possible, every colour seen is a colour of `Alg`,
and the server of every arc out of a node `w` has the induced colour `col(w)`. -/
theorem lemma_6_3 {K D N : ℕ} (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary} (hF : A.Forces K)
    (hS : A.SizeLE N) (hP : A.PostDegLE D) (i : ℕ) :
    (stack K D A i).Forces K ∧
      ∀ Alg : OnlineAlg, Alg.IsProper → ∀ p,
        (usedColours ((stack K D A i).hist Alg p)).card ≤ K - 1 →
        StackOK K D A (usedColours ((stack K D A i).hist Alg p)) i Alg
          ((stack K D A i).hist Alg p) :=
  ⟨(stack_lemma hK hD hF hS hP i).1, fun Alg hAlg p hp =>
    stackOK_of_subset hK hD hF hS hP i Alg hAlg p hp _ subset_rfl⟩

/-- Another name of `lemma_6_3`. -/
alias remark_6_3 := lemma_6_3

/-! ### Histories of runs as ordered graphs -/

section Graphs

variable {N : ℕ → Finset ℕ} {X : OnlineAlg} {P : Type*} [PartialOrder P]

theorem graph_runHist_adj {t : ℕ} {u v : Fin (runHist X N t).length} :
    (runHist X N t).graph.Adj u v ↔
      ((u : ℕ) < v ∧ (u : ℕ) ∈ N v) ∨ ((v : ℕ) < u ∧ (v : ℕ) ∈ N u) := by
  rw [History.graph_adj]
  simp only [List.get_eq_getElem, getElem_runHist]

/-- The graph of a run on a valid sequence has a `P`-labelling if a longer initial segment of the
sequence has one. -/
theorem hasLabelling_runHist (hN : ValidSeq N) {t n : ℕ} (htn : t ≤ n)
    (h : HasLabelling (OnlineInput.ofSeq N hN n).graph P) :
    HasLabelling (runHist X N t).graph P := by
  obtain ⟨f, hf⟩ := h
  have hle : (runHist X N t).length ≤ n := by rw [length_runHist]; exact htn
  refine ⟨f ∘ Fin.castLEOrderEmb hle, hf.comap _ fun x y hadj => ?_⟩
  rw [graph_runHist_adj] at hadj
  rw [OnlineInput.ofSeq_adj]
  rcases hadj with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem hasLabelling_ofSeq_of_runHist (hN : ValidSeq N) {t : ℕ}
    (h : HasLabelling (runHist X N t).graph P) :
    HasLabelling (OnlineInput.ofSeq N hN t).graph P := by
  obtain ⟨f, hf⟩ := h
  have hle : t ≤ (runHist X N t).length := by rw [length_runHist]
  refine ⟨f ∘ Fin.castLEOrderEmb hle, hf.comap _ fun x y hadj => ?_⟩
  rw [OnlineInput.ofSeq_adj] at hadj
  rw [graph_runHist_adj]
  rcases hadj with h | h
  · exact Or.inl ⟨mem_range.1 (hN _ h), h⟩
  · exact Or.inr ⟨mem_range.1 (hN _ h), h⟩

theorem hasLabelling_ofSeq_of_le (hN : ValidSeq N) {t n : ℕ} (htn : t ≤ n)
    (h : HasLabelling (OnlineInput.ofSeq N hN n).graph P) :
    HasLabelling (OnlineInput.ofSeq N hN t).graph P := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ∘ Fin.castLEOrderEmb htn, hf.comap _ fun x y hadj => ?_⟩
  rw [OnlineInput.ofSeq_adj] at hadj ⊢
  exact hadj

theorem rank_eq_zero_of_le (hN : ValidSeq N) {i m : ℕ} (h : m ≤ i) : rank N i m = 0 := by
  unfold rank
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v hv hmem
  have := mem_range.1 (hN v hmem)
  rw [mem_range] at hv
  omega

/-- On a valid sequence the post-degrees of a run are those of the sequence. -/
theorem postDeg_runHist_eq (hN : ValidSeq N) (t i : ℕ) :
    (runHist X N t).postDeg i = rank N i t := by
  unfold History.postDeg rank
  rw [length_runHist]
  congr 1
  apply filter_congr
  intro v hv
  rw [mem_range] at hv
  rw [List.getD_of_lt _ (by simpa using hv), getElem_runHist]
  exact ⟨fun h => h.2, fun h => ⟨mem_range.1 (hN v h), h⟩⟩

end Graphs

/-! ### Good adversaries: Lemma 6.2 with the graphs -/

/-- `A` is *good*: against every proper algorithm its play follows a valid input sequence `H` for
`q ≤ N` vertices and then stops with at least `K` colours in use; the first `q` vertices of `H`
have post-degree at most `D`, and their graph has a `P`-labelling. -/
def Good (K N D : ℕ) (P : Type*) [PartialOrder P] (A : Adversary) : Prop :=
  ∀ Alg : OnlineAlg, Alg.IsProper → ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H) (q : ℕ),
    Follows A Alg H q ∧ q ≤ N ∧ (∀ w < q, postDeg H q w ≤ D) ∧
    K ≤ ((range q).image (runCol Alg H)).card ∧
    HasLabelling (OnlineInput.ofSeq H hH q).graph P

section Good

variable {K N D : ℕ} {P : Type*} [PartialOrder P] {A : Adversary}

theorem Good.forces (h : Good K N D P A) : A.Forces K := by
  intro Alg hAlg
  obtain ⟨H, hH, q, hfol, -, -, hK, -⟩ := h Alg hAlg
  refine ⟨q, ?_, ?_⟩
  · rw [hfol q, min_self]
    exact hfol.stop
  · rw [hfol q, min_self, usedColours_runHist]
    exact hK

theorem Good.sizeLE (h : Good K N D P A) : A.SizeLE N := by
  intro Alg hAlg p
  obtain ⟨H, hH, q, hfol, hq, -⟩ := h Alg hAlg
  rw [hfol p, length_runHist]
  exact (min_le_right _ _).trans hq

theorem Good.postDegLE (h : Good K N D P A) : A.PostDegLE D := by
  intro Alg hAlg p i
  obtain ⟨H, hH, q, hfol, -, hdeg, -⟩ := h Alg hAlg
  rw [hfol p]
  refine (postDeg_runHist_le _ _ _ _).trans ((rank_mono _ _ (min_le_right p q)).trans ?_)
  rcases Nat.lt_or_ge i q with hi | hi
  · exact hdeg i hi
  · rw [rank_eq_zero_of_le hH hi]
    exact Nat.zero_le _

/-- Every graph presented by a good adversary has a `P`-labelling. -/
theorem Good.hasLabelling (h : Good K N D P A) {Alg : OnlineAlg} (hAlg : Alg.IsProper) (p : ℕ) :
    HasLabelling (A.hist Alg p).graph P := by
  obtain ⟨H, hH, q, hfol, -, -, -, hlab⟩ := h Alg hAlg
  rw [hfol p]
  exact hasLabelling_runHist hH (min_le_right _ _) hlab

theorem Good.landsIn (h : Good K N D P A) : A.LandsIn fun _ G => HasLabelling G P :=
  fun _ hAlg p _ => h.hasLabelling hAlg p

/-- **Lemma 6.2 with Lemma 5.2.**  If `A` is good for the labels `J*(P)`, then `B(𝒜)` is good for
the labels `P`, with size `N·R` and post-degree `R`. -/
theorem Good.blow (hK : 2 ≤ K) (hD : 1 ≤ D) (h : Good K N D (Jst P) A) :
    Good K (N * R K D) (R K D) P (B K D A) := by
  intro Alg hAlg
  obtain ⟨H, hH, q, hfol', hq, hdeg, hK', hlab⟩ := h _ (induced_isProper Alg K D)
  have hrc : runCol (induced Alg K D) H = runCol (inducedAlg Alg (R K D) D) H :=
    funext (runCol_induced hH K D)
  rw [hrc] at hK'
  have hR : 0 < R K D := R_pos K D
  have hσ := resPos_blockPerm (D := D) hR (outCol (R K D) D H Alg)
  have hdeg' : ∀ w < q, postDeg H q w ≤ R K D := fun w hw => (hdeg w hw).trans (le_R hK)
  have hG := outSeq_eq (D := D) (A := Alg) hH (R := R K D)
  obtain ⟨T, hTle, hfol, hTK, -, -⟩ := sim hD hAlg hH (hfol'.tracks hH) hdeg hK'
  refine ⟨blowSeq (R K D) H (resPos (R K D) D (outCol (R K D) D H Alg)),
    blowSeq_valid hH hR hσ, T, ?_, hTle.trans (Nat.mul_le_mul_right _ hq), fun w _ => ?_, ?_, ?_⟩
  · rw [← hG]
    exact hfol
  · exact (rank_mono _ _ hTle).trans (postDeg_blowSeq_le hH hR hσ hdeg' w)
  · rw [← hG]
    exact hTK
  · exact hasLabelling_ofSeq_of_le _ hTle
      ((blowUpOf hH hR hσ hdeg').hasLabelling_of_jst hlab)

/-- An adversary whose moves name earlier vertices only is good as soon as it forces `K` colours,
has size at most `N` and post-degree at most `D`, and all its graphs have `P`-labellings. -/
theorem good_of_valid (hF : A.Forces K) (hS : A.SizeLE N) (hP : A.PostDegLE D)
    (hval : ∀ (h : History) (s : Finset ℕ), A.move h = some s → s ⊆ range h.length)
    (hL : ∀ Alg : OnlineAlg, Alg.IsProper → ∀ p, HasLabelling (A.hist Alg p).graph P) :
    Good K N D P A := by
  classical
  intro Alg hAlg
  obtain ⟨q, hq, hqK⟩ := hF Alg hAlg
  have hex : ∃ q, A.move (A.hist Alg q) = none := ⟨q, hq⟩
  have hstop := Nat.find_spec hex
  have hlt : ∀ q' < Nat.find hex, A.move (A.hist Alg q') ≠ none := fun q' h => Nat.find_min hex h
  have hle : Nat.find hex ≤ q := Nat.find_min' hex hq
  generalize Nat.find hex = q₀ at hstop hlt hle
  have hH := inSeq_valid A Alg
  have key : ∀ q' ≤ q₀, A.hist Alg q' = runHist Alg (inSeq A Alg) q' := by
    intro q'
    induction q' with
    | zero => intro _; rw [runHist, Adversary.hist]
    | succ q' ih =>
      intro hq'
      have ih' := ih (Nat.le_of_succ_le hq')
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 (hlt q' hq')
      have hsub := hval _ s hs
      rw [ih', length_runHist] at hsub
      have hHq : inSeq A Alg q' = s := by simp [inSeq, hs, inter_eq_left.2 hsub]
      rw [hist_succ_some hs, runHist_succ, runCol, hHq, ih']
  have hfol : Follows A Alg (inSeq A Alg) q₀ := by
    intro p
    rcases le_total p q₀ with hp | hp
    · rw [min_eq_left hp]
      exact key p hp
    · rw [min_eq_right hp, hist_eq_of_stop hstop p hp]
      exact key q₀ le_rfl
  have h0 := key q₀ le_rfl
  refine ⟨_, hH, q₀, hfol, ?_, fun w _ => ?_, ?_, ?_⟩
  · have := hS Alg hAlg q₀
    rwa [h0, length_runHist] at this
  · have := hP Alg hAlg q₀ w
    rwa [h0, postDeg_runHist_eq hH] at this
  · rw [← usedColours_runHist, ← h0, ← hist_eq_of_stop hstop q hle]
    exact hqK
  · have := hL Alg hAlg q₀
    rw [h0] at this
    exact hasLabelling_ofSeq_of_runHist hH this

end Good

/-- `i` blow-ups below an adversary that is good for the labels `P_{i'+i}(k)` give an adversary
that is good for the labels `P_{i'}(k)`. -/
theorem Good.stack {K N D k : ℕ} (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary} (i : ℕ) :
    ∀ i', Good K N D (LabelPoset k (i' + i)) A →
      Good K (N * ∏ l ∈ range i, deg K D (l + 1)) (deg K D i) (LabelPoset k i')
        (stack K D A i) := by
  induction i with
  | zero => intro i' h; rw [prod_range_zero, Nat.mul_one]; exact h
  | succ i ih =>
    intro i' h
    have e : i' + (i + 1) = i' + 1 + i := by omega
    rw [e] at h
    have h' : Good K (N * ∏ l ∈ range i, deg K D (l + 1)) (deg K D i)
        (Jst (LabelPoset k i')) (Blow.stack K D A i) := ih (i' + 1) h
    have := h'.blow hK (one_le_deg hD i)
    rw [prod_range_succ, ← Nat.mul_assoc]
    exact this

end OnlineColouring.Blow
