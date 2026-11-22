module

public import OnlineColouring.Structure

/-!
# The oblivious blow-up for one outcome of the hidden indices (Construction C.1, Lemma C.2)

Appendix C.  This file contains the part of Construction C.1 and of the proof of Lemma C.2 in
which the hidden indices are fixed: the presented graph for one family `ι` of indices, and Steps 2
and 3 of the proof of the lemma.  The distribution `OB_R(ℋ)`, Step 1 and the lemma itself are in
`OblProb.lean`.

* `obSeq R H ι` is the presented input sequence: the inner vertex `v` (an entry of the inner
  sequence `H`) becomes the block `v*R, …, v*R+R-1`; vertex `w*R+t` of the block of `w` has the
  hidden index `ι w t`, and every vertex of the block of `v` is joined to the whole *index class*
  `I(w, a) = {w*R+t : t < R, ι w t = a}` for every earlier neighbour `w` of `v`, where `v` is the
  `a`-th later neighbour of `w` (`a = rank H w v`, counted from `0`).  The input does not depend on
  any colours.
* `obBlowUpOf`: every outcome is a blow-up of the inner graph (Definition 4.6): `x` serves
  the arc to the `ι(x)`-th later neighbour of its block's vertex, if there is one.
  `postDeg_obSeq_le`: the post-degrees of the outcome are at most `R`.
* For a deterministic algorithm `A` with colouring `col = obCol A R H ι` of the presented graph:
  `popCol R c col m` is the popular colour `π(v_m)` of block `m` (the first colour, in block order,
  that occurs at least `c` times; the paper takes the most frequent colour, and only uses that it
  occurs `⌈R/(K-1)⌉` times when `T_m` fails), and `EvT`, `EvC`, `EvE` are the events
  `T_m`, `C_m`, `E_m = ¬T_m ∧ ¬C_m` of the paper.
* `simAlg A K R c δ ι` is the simulated inner algorithm `A'_ι` of Step 2: on any history it rebuilds
  the inner graph so far, rebuilds the presented graph up to the end of the new block, runs `A` on
  it, and answers `2 π(v_m)` (palette `(0, π(v_m))`) if `m` is not switched and `2m+1` (palette
  `(1, m)`) if it is.  It is defined on every history, and `simAlg_run_proper` shows that it colours
  *every* input properly when `A` is proper, `c ≥ 1` and `(K-1)(c-1)+1 ≤ R` (the paper's
  argument); `OnlineAlg.patch` then turns it into an algorithm that is proper on every history
  (`IsProper`) without changing any of these runs (`runCol_patch_of_proper`, `runCol_simAlgP`).
* `comparison` (Step 3): for such `c`, if the post-degrees of `H` are at most `δ`, `A` uses at
  most `K-1` colours and no `E_m` occurs, then `A'_ι` uses at most `K-1` colours.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Ranks are monotone -/

theorem rank_mono {H : ℕ → Finset ℕ} {w v v' : ℕ} (h : v ≤ v') : rank H w v ≤ rank H w v' := by
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-! ### The presented sequence -/

/-- The index class `I(w, a)`: the positions `t < R` of the block of `w` with index `a`. -/
def idxClass (R : ℕ) (ι : ℕ → ℕ → ℕ) (w a : ℕ) : Finset ℕ := (range R).filter fun t => ι w t = a

/-- The oblivious blow-up of `H` with blocks of size `R` and hidden indices `ι`: the earlier
neighbours of the presented vertex `p` (in the block of `v = p / R`) are the index classes
`I(w, rank H w v)` of the earlier neighbours `w` of `v`. -/
def obSeq (R : ℕ) (H : ℕ → Finset ℕ) (ι : ℕ → ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (H (p / R)).biUnion fun w => (idxClass R ι w (rank H w (p / R))).image fun t => w * R + t

variable {R : ℕ} {H : ℕ → Finset ℕ} {ι : ℕ → ℕ → ℕ}

theorem mem_obSeq' {x p : ℕ} :
    x ∈ obSeq R H ι p ↔ ∃ w ∈ H (p / R), ∃ t < R, ι w t = rank H w (p / R) ∧ w * R + t = x := by
  simp [obSeq, idxClass, and_assoc]

theorem mem_obSeq (hR : 0 < R) {x p : ℕ} :
    x ∈ obSeq R H ι p ↔ x / R ∈ H (p / R) ∧ ι (x / R) (x % R) = rank H (x / R) (p / R) := by
  rw [mem_obSeq']
  constructor
  · rintro ⟨w, hw, t, ht, hι, rfl⟩
    have h₁ : (w * R + t) / R = w := div_add_lt hR ht
    have h₂ : (w * R + t) % R = t := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt ht
    rw [h₁, h₂]
    exact ⟨hw, hι⟩
  · rintro ⟨hw, hι⟩
    exact ⟨x / R, hw, x % R, Nat.mod_lt _ hR, hι, Nat.div_add_mod' x R⟩

theorem lt_of_mem_obSeq (hH : ValidSeq H) {x p : ℕ} (hx : x ∈ obSeq R H ι p) : x < p := by
  obtain ⟨w, hw, t, ht, -, rfl⟩ := mem_obSeq'.1 hx
  have h₁ : w < p / R := mem_range.1 (hH _ hw)
  have h₂ : w * R + R ≤ p / R * R := by
    have := Nat.mul_le_mul_right R h₁
    rwa [Nat.succ_mul] at this
  have h₃ : p / R * R ≤ p := Nat.div_mul_le_self p R
  omega

theorem obSeq_valid (hH : ValidSeq H) : ValidSeq (obSeq R H ι) :=
  fun _ _ hx => mem_range.2 (lt_of_mem_obSeq hH hx)

theorem obSeq_div (hR : 0 < R) (p : ℕ) : obSeq R H ι (p / R * R) = obSeq R H ι p := by
  unfold obSeq
  rw [Nat.mul_div_cancel _ hR]

/-- The vertex `w*R+t` (`t < R`) is an earlier neighbour of every vertex of the block of `v` if
`w ∈ H v` and its index is `rank H w v`. -/
theorem mem_obSeq_of {w v t t' : ℕ} (hw : w ∈ H v) (ht : t < R) (ht' : t' < R)
    (hι : ι w t = rank H w v) : w * R + t ∈ obSeq R H ι (v * R + t') := by
  have hR : 0 < R := by omega
  rw [mem_obSeq', div_add_lt hR ht']
  exact ⟨w, hw, t, ht, hι, rfl⟩

/-- A presented vertex serves at most one block. -/
theorem block_eq_of_mem_obSeq (hR : 0 < R) {x p₁ p₂ : ℕ} (h₁ : x ∈ obSeq R H ι p₁)
    (h₂ : x ∈ obSeq R H ι p₂) : p₁ / R = p₂ / R := by
  obtain ⟨hw₁, hι₁⟩ := (mem_obSeq hR).1 h₁
  obtain ⟨hw₂, hι₂⟩ := (mem_obSeq hR).1 h₂
  exact rank_inj hw₁ hw₂ (hι₁.symm.trans hι₂)

/-- The earlier neighbours of a presented vertex of the block of `v` depend only on `H` up to `v`
and on the indices of the blocks before `v`. -/
theorem obSeq_congr (hH : ValidSeq H) {H' : ℕ → Finset ℕ} {ι' : ℕ → ℕ → ℕ} {p : ℕ}
    (hHH : ∀ i ≤ p / R, H i = H' i) (hιι : ∀ w < p / R, ι w = ι' w) :
    obSeq R H ι p = obSeq R H' ι' p := by
  unfold obSeq
  rw [← hHH _ le_rfl]
  apply biUnion_congr rfl
  intro w hw
  have hw' : w < p / R := mem_range.1 (hH _ hw)
  have hr : rank H w (p / R) = rank H' w (p / R) := rank_congr fun i hi => hHH i hi.le
  unfold idxClass
  rw [hr, hιι w hw']

/-! ### The blow-up structure -/

section BlowUpStructure

open Classical in
/-- The serve map of an oblivious blow-up: `x` serves the arc into `v` iff `x` is an earlier
neighbour of the first vertex `v*R` of the block of `v`. -/
noncomputable def obServe (R : ℕ) (H : ℕ → Finset ℕ) (ι : ℕ → ℕ → ℕ) (m : ℕ) (x : Fin (m * R)) :
    Option (Fin m) :=
  if h : ∃ v : Fin m, (x : ℕ) ∈ obSeq R H ι (v * R) then some h.choose else none

variable {m : ℕ}

theorem obServe_eq_some (hR : 0 < R) {x : Fin (m * R)} {v : Fin m} :
    obServe R H ι m x = some v ↔ (x : ℕ) ∈ obSeq R H ι (v * R) := by
  classical
  unfold obServe
  constructor
  · intro hs
    split_ifs at hs with h
    · cases hs
      exact h.choose_spec
  · intro hx
    have h : ∃ v : Fin m, (x : ℕ) ∈ obSeq R H ι (v * R) := ⟨v, hx⟩
    rw [dite_eq_left_of_eq_true (eq_true h)]
    congr 1
    apply Fin.ext
    have e := block_eq_of_mem_obSeq hR h.choose_spec hx
    rwa [Nat.mul_div_cancel _ hR, Nat.mul_div_cancel _ hR] at e

theorem mem_obSeq_iff_obServe (hR : 0 < R) (x u : Fin (m * R)) :
    (x : ℕ) ∈ obSeq R H ι u ↔ obServe R H ι m x = some (blockMap R m u) := by
  rw [obServe_eq_some hR]
  change _ ↔ (x : ℕ) ∈ obSeq R H ι (u / R * R)
  rw [obSeq_div hR]

/-- **Every outcome of the oblivious blow-up is a blow-up** of the inner graph (Definition
"blow-up"): the first `m * R` presented vertices form a blow-up of the first `m` vertices of `H`. -/
noncomputable def obBlowUpOf (hH : ValidSeq H) (hR : 0 < R) :
    BlowUp (OnlineInput.ofSeq H hH m).graph
      (OnlineInput.ofSeq (obSeq R H ι) (obSeq_valid hH) (m * R)).graph where
  π := blockMap R m
  serve := obServe R H ι m
  π_surjective v := ⟨⟨v * R, Nat.mul_lt_mul_of_pos_right v.2 hR⟩,
    Fin.ext (Nat.mul_div_cancel _ hR)⟩
  lt_of_π_lt x y h := Fin.lt_def.2 (Nat.lt_of_div_lt_div (Fin.lt_def.1 h))
  serve_spec x v h := by
    have hx := (obServe_eq_some hR).1 h
    obtain ⟨hw, -⟩ := (mem_obSeq hR).1 hx
    rw [Nat.mul_div_cancel _ hR] at hw
    exact ⟨Fin.lt_def.2 (mem_range.1 (hH _ hw)), OnlineInput.ofSeq_adj.2 (Or.inl hw)⟩
  adj_iff x u := by
    rw [OnlineInput.ofSeq_adj, mem_obSeq_iff_obServe hR, mem_obSeq_iff_obServe hR]
    constructor
    · rintro (h | h)
      · refine Or.inl ⟨?_, h⟩
        have := (mem_obSeq_iff_obServe hR x u).2 h
        exact Fin.lt_def.2 (lt_of_mem_obSeq hH this)
      · refine Or.inr ⟨?_, h⟩
        have := (mem_obSeq_iff_obServe hR u x).2 h
        exact Fin.lt_def.2 (lt_of_mem_obSeq hH this)
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h

/-- Every presented vertex has post-degree at most `R`: it is joined to at most one later block. -/
theorem postDeg_obSeq_le (hR : 0 < R) (n x : ℕ) : postDeg (obSeq R H ι) n x ≤ R := by
  unfold postDeg rank
  set S := (range n).filter fun u => x ∈ obSeq R H ι u
  rcases S.eq_empty_or_nonempty with hS | ⟨u₀, hu₀⟩
  · rw [hS, card_empty]; exact Nat.zero_le _
  · have hu₀' := mem_filter.1 hu₀
    have hsub : S ⊆ Ico (u₀ / R * R) (u₀ / R * R + R) := by
      intro u hu
      have e := block_eq_of_mem_obSeq hR (mem_filter.1 hu).2 hu₀'.2
      rw [mem_Ico, ← e]
      exact ⟨Nat.div_mul_le_self u R, Nat.lt_div_mul_add hR⟩
    calc S.card ≤ (Ico (u₀ / R * R) (u₀ / R * R + R)).card := card_le_card hsub
      _ = R := by simp

end BlowUpStructure

/-! ### Colours, popular colours and the events `T_m`, `C_m`, `E_m` -/

/-- The colouring of the presented graph by `A`. -/
def obCol (A : OnlineAlg) (R : ℕ) (H : ℕ → Finset ℕ) (ι : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  runCol A (obSeq R H ι)

/-- The number of colours used by `A` on the first `N` entries of the sequence `H`. -/
def colsOn (A : OnlineAlg) (H : ℕ → Finset ℕ) (N : ℕ) : ℕ := ((range N).image (runCol A H)).card

/-- The popular colour `π(v_m)` of block `m`: the first colour, in the order of the block, that
occurs on at least `c` of its vertices. -/
abbrev popCol (R c : ℕ) (col : ℕ → ℕ) (m : ℕ) : ℕ := popular R c (blockCol col R m)

/-- `T_m`: at least `K` colours are used by the end of block `m`. -/
def EvT (K R : ℕ) (col : ℕ → ℕ) (m : ℕ) : Prop := K ≤ ((range ((m + 1) * R)).image col).card

/-- `C_m`: every index class `I(v_m, a)`, `a < δ m`, contains a vertex of the popular colour. -/
def EvC (R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) (col : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ a < δ m, ∃ t < R, ι m t = a ∧ col (m * R + t) = popCol R c col m

/-- `E_m = ¬T_m ∧ ¬C_m`. -/
def EvE (K R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) (col : ℕ → ℕ) (m : ℕ) : Prop :=
  ¬ EvT K R col m ∧ ¬ EvC R c δ ι col m

/-- "Switched at `m`": `T_m` holds, or `C_l` fails for some `l ≤ m`, or some `v_l` with `l < m` has
more than `δ(l)` later neighbours among `v_0, …, v_m`. -/
def Switched (K R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) (H : ℕ → Finset ℕ) (col : ℕ → ℕ) (m : ℕ) :
    Prop :=
  EvT K R col m ∨ (∃ l ≤ m, ¬ EvC R c δ ι col l) ∨ (∃ l < m, δ l < rank H l (m + 1))

section Events

variable {K c : ℕ} {δ : ℕ → ℕ} {col col' : ℕ → ℕ} {m : ℕ}

theorem block_lt {l m t : ℕ} (hl : l ≤ m) (ht : t < R) : l * R + t < (m + 1) * R :=
  calc l * R + t < l * R + R := by omega
    _ = (l + 1) * R := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (m + 1) * R := Nat.mul_le_mul_right R (by omega)

theorem popCol_congr (h : ∀ i < (m + 1) * R, col i = col' i) {l : ℕ} (hl : l ≤ m) :
    popCol R c col l = popCol R c col' l :=
  popular_congr fun _ ht => h _ (block_lt hl ht)

theorem evT_congr (h : ∀ i < (m + 1) * R, col i = col' i) {K : ℕ} :
    EvT K R col m ↔ EvT K R col' m := by
  unfold EvT
  rw [image_congr fun i hi => h i (mem_range.1 hi)]

theorem evC_congr (h : ∀ i < (m + 1) * R, col i = col' i) {l : ℕ} (hl : l ≤ m) :
    EvC R c δ ι col l ↔ EvC R c δ ι col' l := by
  unfold EvC
  rw [popCol_congr h hl]
  constructor
  · intro hC a ha
    obtain ⟨t, ht, h₁, h₂⟩ := hC a ha
    exact ⟨t, ht, h₁, (h _ (block_lt hl ht)).symm.trans h₂⟩
  · intro hC a ha
    obtain ⟨t, ht, h₁, h₂⟩ := hC a ha
    exact ⟨t, ht, h₁, (h _ (block_lt hl ht)).trans h₂⟩

theorem switched_congr (h : ∀ i < (m + 1) * R, col i = col' i) {H' : ℕ → Finset ℕ}
    (hHH : ∀ i < m + 1, H i = H' i) :
    Switched K R c δ ι H col m ↔ Switched K R c δ ι H' col' m := by
  unfold Switched
  have hr : ∀ l, rank H l (m + 1) = rank H' l (m + 1) := fun l => rank_congr hHH
  simp only [hr, evT_congr h]
  constructor
  · rintro (h₁ | ⟨l, hl, hC⟩ | h₃)
    · exact Or.inl h₁
    · exact Or.inr (Or.inl ⟨l, hl, (evC_congr h hl).not.1 hC⟩)
    · exact Or.inr (Or.inr h₃)
  · rintro (h₁ | ⟨l, hl, hC⟩ | h₃)
    · exact Or.inl h₁
    · exact Or.inr (Or.inl ⟨l, hl, (evC_congr h hl).not.2 hC⟩)
    · exact Or.inr (Or.inr h₃)

theorem evT_mono {l : ℕ} (hlm : l ≤ m) (hT : EvT K R col l) : EvT K R col m := by
  refine hT.trans (card_le_card (image_subset_image (range_subset_range.2 ?_)))
  exact Nat.mul_le_mul_right R (Nat.succ_le_succ hlm)

/-- Switching is monotone. -/
theorem switched_mono {l : ℕ} (hlm : l ≤ m) (hs : Switched K R c δ ι H col l) :
    Switched K R c δ ι H col m := by
  rcases hs with hT | ⟨l', hl', hC⟩ | ⟨l', hl', hd⟩
  · exact Or.inl (evT_mono hlm hT)
  · exact Or.inr (Or.inl ⟨l', hl'.trans hlm, hC⟩)
  · exact Or.inr (Or.inr ⟨l', by omega, hd.trans_le (rank_mono (by omega))⟩)

/-- If `T_m` fails, the popular colour of block `m` occurs at least `c` times in it
(pigeonhole: `R ≥ (K-1)(c-1)+1` vertices with at most `K-1` colours). -/
theorem popCol_spec (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R) (hT : ¬ EvT K R col m) :
    c ≤ (clsList R (blockCol col R m) (popCol R c col m)).length := by
  apply popular_spec hc
  have hlt : ((range R).image (blockCol col R m)).card < K := by
    refine lt_of_le_of_lt (card_le_card ?_) (not_le.1 hT)
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
    exact mem_image.2 ⟨m * R + t, mem_range.2 (block_lt le_rfl (mem_range.1 ht)), rfl⟩
  obtain ⟨b, -, hb⟩ := exists_large_colour_class (range R) (blockCol col R m)
    (by rwa [card_range]) hlt
  exact ⟨b, by rwa [length_clsList]⟩

/-- If `T_m` fails, the popular colour of block `m` is the colour of a vertex of block `m` (for
`c ≥ 1` and `R ≥ (K-1)(c-1)+1`). -/
theorem popCol_mem (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R) (hT : ¬ EvT K R col m) :
    ∃ t < R, col (m * R + t) = popCol R c col m :=
  popular_mem hc (popCol_spec hc hRc hT)

end Events

/-! ### The simulated inner algorithm -/

open Classical in
/-- The simulated inner algorithm `A'_ι` with tagged palettes (Step 2).  On a history `h` with
`m = |h|` inner vertices and the earlier neighbours `s` of `v_m`, it rebuilds the inner graph
`innerSeq h s` up to `v_m` and the presented graph from it and `ι`, runs `A` on it, and gives `v_m`
the colour `2 π(v_m)` if `m` is not switched and `2m+1` if it is. -/
noncomputable def simAlg (A : OnlineAlg) (K R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) : OnlineAlg :=
  ⟨fun h s =>
    if Switched K R c δ ι (innerSeq h s) (obCol A R (innerSeq h s) ι) h.length then
      2 * h.length + 1
    else 2 * popCol R c (obCol A R (innerSeq h s) ι) h.length⟩

variable {A : OnlineAlg} {K c : ℕ} {δ : ℕ → ℕ}

theorem obCol_congr (hH : ValidSeq H) {H' : ℕ → Finset ℕ} {ι' : ℕ → ℕ → ℕ} {m : ℕ}
    (hHH : ∀ i ≤ m, H i = H' i) (hιι : ∀ w < m, ι w = ι' w) :
    ∀ i < (m + 1) * R, obCol A R H ι i = obCol A R H' ι' i := by
  intro i hi
  unfold obCol
  apply runCol_congr
  intro j hj
  have hjm : j / R ≤ m := by
    have := (Nat.div_lt_iff_lt_mul (by
      rcases Nat.eq_zero_or_pos R with hR | hR
      · subst hR; simp at hi
      · exact hR)).2 (lt_of_le_of_lt hj hi)
    omega
  exact obSeq_congr hH (fun i' hi' => hHH i' (hi'.trans hjm))
    (fun w hw => hιι w (lt_of_lt_of_le hw hjm))

open Classical in
/-- On an actual inner input, the simulated colour of `v_m` is computed from the actual presented
graph and the actual colouring of `A`. -/
theorem runCol_simAlg (hH : ValidSeq H) (m : ℕ) :
    runCol (simAlg A K R c δ ι) H m =
      if Switched K R c δ ι H (obCol A R H ι) m then 2 * m + 1
      else 2 * popCol R c (obCol A R H ι) m := by
  have hin := innerSeq_runHist (simAlg A K R c δ ι) H m
  have hcol : ∀ i < (m + 1) * R,
      obCol A R (innerSeq (runHist (simAlg A K R c δ ι) H m) (H m)) ι i = obCol A R H ι i :=
    obCol_congr (fun i => by
        rcases lt_or_ge i (m + 1) with h | h
        · rw [hin i (by omega)]; exact hH i
        · unfold innerSeq
          rw [length_runHist]
          simp only [show ¬ i < m by omega, show i ≠ m by omega, ↓reduceIte]
          exact empty_subset _)
      hin (fun _ _ => rfl)
  change (if Switched K R c δ ι _ _ (runHist _ H m).length then _ else _) = _
  rw [length_runHist, switched_congr hcol (H' := H) (fun i hi => hin i (by omega)),
    popCol_congr hcol le_rfl]

/-- **Step 2: the simulated algorithm colours every input properly** if `A` is proper, `c ≥ 1` and
`(K-1)(c-1)+1 ≤ R` (for every valid inner sequence `H` and every index family `ι`, without any
assumption on `H`). -/
theorem simAlg_run_proper (hA : A.IsProper) (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R)
    (hH : ValidSeq H) (m : ℕ) {l : ℕ} (hl : l ∈ H m) :
    runCol (simAlg A K R c δ ι) H m ≠ runCol (simAlg A K R c δ ι) H l := by
  classical
  have hlm : l < m := mem_range.1 (hH m hl)
  rw [runCol_simAlg hH, runCol_simAlg hH]
  set col := obCol A R H ι
  by_cases hm : Switched K R c δ ι H col m
  · rw [ite_eq_left hm]
    split_ifs <;> omega
  · have hl' : ¬ Switched K R c δ ι H col l := fun h => hm (switched_mono hlm.le h)
    rw [ite_eq_right hm, ite_eq_right hl']
    have hT : ¬ EvT K R col m := fun h => hm (Or.inl h)
    have hC : EvC R c δ ι col l := by
      by_contra h
      exact hm (Or.inr (Or.inl ⟨l, hlm.le, h⟩))
    have hdeg : rank H l (m + 1) ≤ δ l := by
      by_contra h
      exact hm (Or.inr (Or.inr ⟨l, hlm, not_le.1 h⟩))
    have ha : rank H l m < δ l := (rank_lt_rank (Nat.lt_succ_self m) hl).trans_le hdeg
    obtain ⟨t, ht, hιt, hcolt⟩ := hC _ ha
    obtain ⟨t', ht', hcolt'⟩ := popCol_mem hc hRc hT
    have hR : 0 < R := by omega
    have hx := mem_obSeq_of (ι := ι) hl ht ht' hιt
    have hne := runCol_ne hA hx (lt_of_mem_obSeq hH hx)
    intro heq
    apply hne
    change col (m * R + t') = col (l * R + t)
    rw [hcolt, hcolt']
    omega

/-! ### Patching -/

/-- On a valid sequence whose run is proper, the patched algorithm runs exactly like `A`. -/
theorem runCol_patch_of_proper {A : OnlineAlg} {H : ℕ → Finset ℕ} (hH : ValidSeq H)
    (hprop : ∀ i, ∀ l ∈ H i, runCol A H i ≠ runCol A H l) :
    ∀ i, runCol A.patch H i = runCol A H i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  have hhist : runHist A.patch H i = runHist A H i := by
    rw [runHist_eq_map, runHist_eq_map]
    exact List.map_congr_left fun j hj => by rw [ih j (List.mem_range.1 hj)]
  have hnot : A.step (runHist A H i) (H i) ∉ (H i).image (runCol A H) := by
    intro hmem
    obtain ⟨l, hl, hli⟩ := mem_image.1 hmem
    exact hprop i l hl hli.symm
  change (if A.step _ _ ∈ nbrColours _ _ then _ else _) = _
  rw [hhist, nbrColours_runHist (hH i), ite_eq_right hnot]
  rfl

/-- The simulated algorithm, patched so as to be proper on every history; it runs like
`simAlg` on every valid sequence if `A` is proper, `c ≥ 1` and `(K-1)(c-1)+1 ≤ R`
(`runCol_simAlgP`). -/
noncomputable def simAlgP (A : OnlineAlg) (K R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) : OnlineAlg :=
  (simAlg A K R c δ ι).patch

theorem simAlgP_isProper (A : OnlineAlg) (K R c : ℕ) (δ : ℕ → ℕ) (ι : ℕ → ℕ → ℕ) :
    (simAlgP A K R c δ ι).IsProper :=
  OnlineAlg.patch_isProper _

theorem runCol_simAlgP (hA : A.IsProper) (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R)
    (hH : ValidSeq H) : ∀ i, runCol (simAlgP A K R c δ ι) H i = runCol (simAlg A K R c δ ι) H i :=
  runCol_patch_of_proper hH fun i _ hl => simAlg_run_proper hA hc hRc hH i hl

/-! ### Step 3: the comparison -/

/-- **Step 3.** Let `c ≥ 1` and `(K-1)(c-1)+1 ≤ R`, and let the inner sequence `H` have
post-degrees at most `δ` on its first `N` vertices.  If `A` uses at most `K-1` colours on the first
`N*R` presented vertices and no `E_m` (`m < N`) occurs, then the simulated algorithm uses at most
`K-1` colours on the first `N` inner vertices (every colour of `A'_ι` is twice a colour of
`A`). -/
theorem comparison (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R)
    (hH : ValidSeq H) {N : ℕ} (hdeg : ∀ w < N, postDeg H N w ≤ δ w)
    (hT : colsOn A (obSeq R H ι) (N * R) < K)
    (hE : ∀ m < N, ¬ EvE K R c δ ι (obCol A R H ι) m) :
    colsOn (simAlg A K R c δ ι) H N < K := by
  classical
  set col := obCol A R H ι
  have hnotT : ∀ m < N, ¬ EvT K R col m := by
    intro m hm hTm
    refine absurd (hTm.trans (card_le_card (image_subset_image (range_subset_range.2 ?_))))
      (not_le.2 hT)
    exact Nat.mul_le_mul_right R (Nat.succ_le_of_lt hm)
  have hC : ∀ m < N, EvC R c δ ι col m := by
    intro m hm
    by_contra h
    exact hE m hm ⟨hnotT m hm, h⟩
  have hns : ∀ m < N, ¬ Switched K R c δ ι H col m := by
    rintro m hm (h | ⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact hnotT m hm h
    · exact h (hC l (by omega))
    · exact absurd (h.trans_le ((rank_mono (by omega)).trans (hdeg l (by omega)))) (lt_irrefl _)
  refine lt_of_le_of_lt ?_ hT
  unfold colsOn
  calc ((range N).image (runCol (simAlg A K R c δ ι) H)).card
      ≤ (((range (N * R)).image col).image fun x => 2 * x).card := by
        apply card_le_card
        intro y hy
        obtain ⟨m, hm, rfl⟩ := mem_image.1 hy
        have hm' := mem_range.1 hm
        rw [runCol_simAlg hH, ite_eq_right (hns m hm')]
        obtain ⟨t, ht, hct⟩ := popCol_mem hc hRc (hnotT m hm')
        refine mem_image.2 ⟨col (m * R + t), mem_image.2 ⟨m * R + t, mem_range.2 ?_, rfl⟩, ?_⟩
        · have := block_lt (le_refl m) ht
          exact lt_of_lt_of_le this (Nat.mul_le_mul_right R (Nat.succ_le_of_lt hm'))
        · rw [hct]
    _ ≤ ((range (N * R)).image col).card := card_image_le

/-- **Step 3, as an inclusion of events.** Under the same hypotheses on `c`, `R` and `H`: if the
simulated algorithm uses at least `K` colours, then `A` uses at least `K` colours or some `E_m`
occurs. -/
theorem comparison' (hc : 1 ≤ c) (hRc : (K - 1) * (c - 1) + 1 ≤ R)
    (hH : ValidSeq H) {N : ℕ} (hdeg : ∀ w < N, postDeg H N w ≤ δ w)
    (hK : K ≤ colsOn (simAlg A K R c δ ι) H N) :
    K ≤ colsOn A (obSeq R H ι) (N * R) ∨ ∃ m < N, EvE K R c δ ι (obCol A R H ι) m := by
  by_contra h
  push Not at h
  exact absurd hK (not_le.2 (comparison hc hRc hH hdeg h.1 h.2))

end OnlineColouring
