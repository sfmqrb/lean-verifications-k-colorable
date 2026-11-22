module

public import OnlineColouring.BlowStack

/-!
# Section 7, "Completing every block": one reservation blow-up of `𝒜^str`

Section 7, paragraph "Completing every block": *Let `𝒜^str` be the adversary of
Theorem 6.4 with two changes.  It never stops early, so every block of a node of level `ℓ` has
exactly `b_ℓ` nodes.  In step 3, if no colour occurs `D` times in `σ(v)`, it takes for `col(v)`
a most frequent colour of `σ(v)` and fills `Res(v)` with `D` vertices of `σ(v)` chosen by a fixed
rule, which is possible because `b_ℓ ≥ D`.  Until the algorithm uses its `K`-th colour, `𝒜^str`
makes exactly the moves of the adversary of Theorem 6.4, so it also forces `K` colours.  After
the `K`-th colour, the colourings reported to the inner adversaries may be improper.  This does
no harm: all these adversaries are rules defined on every history, and from then on we use only
the graph they build (the block sizes, the reserves of `D` vertices, and one server per
arc).*

This file treats one level.  `Str.Bstr K D A : Adversary` is Construction 6.1 (`Blow.B K D A`)
with these two changes:

* there is no stop rule: `Bstr K D A` stops only when the inner adversary `A` stops;
* step 3 uses `Str.strPopular R D`: if some colour occurs on at least `D` vertices of the block, it
  is the first such colour, exactly as in Construction 6.1 (`popular`); otherwise it is a most
  frequent colour of the block (`Str.frequent`: among the colours with the largest number of
  occurrences, the one that appears first; `frequent_spec`).

**The fixed rule for the reserve** (`Str.strResOrder`): the vertices of `σ(v)` of colour `col(v)`
in arrival order, followed by the other vertices of `σ(v)` in arrival order; `Res(v)` consists of
the first `D` vertices of this list, and the `r`-th later inner neighbour of `v` is served by its
`r`-th vertex.  If step 3 of Construction 6.1 is possible this is the rule of `Blow.B`.

Main results (no hypothesis on the algorithm `X`: it need not be proper, and neither is the
induced algorithm):

* `Str.strInduced X K D`: the induced algorithm of the level.  It answers the inner vertex `v`
  with `col(v)` and has no fallback, so it is in general *not* proper.
* `Str.Bstr_follows`: if the play of `A` against `strInduced X K D` follows a valid input sequence
  `H` for `q₀` vertices and then stops, then the play of `Bstr K D A` against `X` follows the
  structure-mode sequence `strOutSeq R D H X` for exactly `q₀ · R` vertices and then stops.
  `strOutSeq_eq`: this sequence is the static reservation blow-up `blowSeq R H σ` for a block
  permutation `σ`.
* `Str.Bstr_inner`: at every moment of that play the inner play simulated by `Bstr K D A` is the
  play of `A` against `strInduced X K D`.
* `Str.Bstr_move_eq`: on every history with fewer than `K` colours, `Bstr K D A'` makes the move
  of `Blow.B K D A`, provided `A'` and `A` make the same moves on all such histories.
-/

@[expose] public section

namespace OnlineColouring.Str

open Finset
open Blow (Follows clean R)

/-! ### Step 3 with the fallback -/

/-- The largest number of vertices of the block that have the same colour. -/
def maxCount (R : ℕ) (bc : ℕ → ℕ) : ℕ := (range R).sup fun t => (clsList R bc (bc t)).length

/-- A most frequent colour of the block: among the colours that occur on the largest number of
vertices of the block, the one that appears first (`0` for an empty block). -/
def frequent (R : ℕ) (bc : ℕ → ℕ) : ℕ := popular R (maxCount R bc) bc

/-- The induced colour `col(v)` in `𝒜^str`: if some colour occurs on at least `D` vertices of the
block, the first such colour (as in Construction 6.1); otherwise a most frequent colour of the
block. -/
def strPopular (R D : ℕ) (bc : ℕ → ℕ) : ℕ :=
  if D ≤ (clsList R bc (popular R D bc)).length then popular R D bc else frequent R bc

/-- The order in which the vertices of a block are used as servers in `𝒜^str`: first the vertices
of the induced colour, then the others; the first `D` of them form the reserve. -/
def strResOrder (R D : ℕ) (bc : ℕ → ℕ) : List ℕ :=
  (List.range R).filter (fun t => decide (bc t = strPopular R D bc)) ++
    (List.range R).filter (fun t => !decide (bc t = strPopular R D bc))

/-- The position, in the block of `w`, of the `r`-th server taken from that block. -/
def strResPos (R D : ℕ) (col : ℕ → ℕ) (w r : ℕ) : ℕ :=
  (strResOrder R D (blockCol col R w)).getD r 0

section Rule

variable {R D : ℕ}

theorem clsList_eq_nil {bc : ℕ → ℕ} {c : ℕ} (h : ∀ t < R, bc t ≠ c) : clsList R bc c = [] := by
  unfold clsList
  rw [List.filter_eq_nil_iff]
  intro t ht
  simpa using h t (List.mem_range.1 ht)

theorem length_clsList_le_maxCount (bc : ℕ → ℕ) (c : ℕ) :
    (clsList R bc c).length ≤ maxCount R bc := by
  by_cases h : ∃ t < R, bc t = c
  · obtain ⟨t, ht, rfl⟩ := h
    exact Finset.le_sup (f := fun t => (clsList R bc (bc t)).length) (mem_range.2 ht)
  · push Not at h
    rw [clsList_eq_nil h]
    exact Nat.zero_le _

/-- **`frequent` is a most frequent colour of the block.**  For a nonempty block it is the colour
of one of its vertices, and no colour occurs on more vertices of the block. -/
theorem frequent_spec (hR : 0 < R) (bc : ℕ → ℕ) :
    (∃ t < R, bc t = frequent R bc) ∧
      ∀ c, (clsList R bc c).length ≤ (clsList R bc (frequent R bc)).length := by
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_mem_eq_sup (range R) ⟨0, mem_range.2 hR⟩
    fun t => (clsList R bc (bc t)).length
  have ht₀' : maxCount R bc = (clsList R bc (bc t₀)).length := ht₀
  have h1 : 1 ≤ maxCount R bc := by
    have h0 : 0 ∈ clsList R bc (bc 0) := by
      simp [clsList, hR]
    exact (List.length_pos_of_mem h0).trans_le (length_clsList_le_maxCount bc _)
  have hspec : maxCount R bc ≤ (clsList R bc (frequent R bc)).length :=
    popular_spec h1 ⟨bc t₀, ht₀'.le⟩
  exact ⟨popular_mem h1 hspec, fun c => (length_clsList_le_maxCount bc c).trans hspec⟩

theorem maxCount_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) :
    maxCount R bc = maxCount R bc' := by
  unfold maxCount
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [clsList_congr h, h t (mem_range.1 ht)]

theorem strPopular_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) :
    strPopular R D bc = strPopular R D bc' := by
  unfold strPopular frequent
  rw [popular_congr h, clsList_congr h, maxCount_congr h, popular_congr h]

/-- If step 3 of Construction 6.1 is possible, `𝒜^str` takes the colour of Construction 6.1. -/
theorem strPopular_eq_popular {bc : ℕ → ℕ}
    (h : D ≤ (clsList R bc (popular R D bc)).length) : strPopular R D bc = popular R D bc :=
  ite_eq_left h

/-- Otherwise it takes a most frequent colour. -/
theorem strPopular_eq_frequent {bc : ℕ → ℕ}
    (h : ¬ D ≤ (clsList R bc (popular R D bc)).length) : strPopular R D bc = frequent R bc :=
  ite_eq_right h

/-- **Step 3 of `𝒜^str`, in the terms of the paper.**  If some colour occurs `D` times in the
block, `col(v)` is the colour chosen in Construction 6.1, and it occurs `D` times.  If no colour
occurs `D` times, `col(v)` is a most frequent colour of the block. -/
theorem strPopular_spec (hR : 0 < R) (hD : 1 ≤ D) (bc : ℕ → ℕ) :
    ((∃ c, D ≤ (clsList R bc c).length) →
      strPopular R D bc = popular R D bc ∧ D ≤ (clsList R bc (strPopular R D bc)).length) ∧
    ((¬ ∃ c, D ≤ (clsList R bc c).length) →
      ∀ c, (clsList R bc c).length ≤ (clsList R bc (strPopular R D bc)).length) := by
  constructor
  · intro h
    have h1 := popular_spec hD h
    rw [strPopular_eq_popular h1]
    exact ⟨rfl, h1⟩
  · intro h
    rw [strPopular_eq_frequent fun h1 => h ⟨_, h1⟩]
    exact (frequent_spec hR bc).2

/-- The induced colour of `𝒜^str` is the colour of a vertex of the block (`D ≥ 1`, and the block
is not empty). -/
theorem strPopular_mem (hR : 0 < R) (hD : 1 ≤ D) (bc : ℕ → ℕ) :
    ∃ t < R, bc t = strPopular R D bc := by
  by_cases h : D ≤ (clsList R bc (popular R D bc)).length
  · rw [strPopular_eq_popular h]
    exact popular_mem hD h
  · rw [strPopular_eq_frequent h]
    exact (frequent_spec hR bc).1

theorem strResOrder_perm (bc : ℕ → ℕ) : (strResOrder R D bc).Perm (List.range R) :=
  List.filter_append_perm _ _

theorem mem_strResOrder {bc : ℕ → ℕ} {t : ℕ} : t ∈ strResOrder R D bc ↔ t < R := by
  rw [(strResOrder_perm bc).mem_iff, List.mem_range]

theorem strResOrder_nodup (bc : ℕ → ℕ) : (strResOrder R D bc).Nodup :=
  (strResOrder_perm bc).nodup_iff.2 List.nodup_range

theorem length_strResOrder (bc : ℕ → ℕ) : (strResOrder R D bc).length = R := by
  rw [(strResOrder_perm bc).length_eq, List.length_range]

/-- **The reserve of `𝒜^str`.**  The first `D ≤ R` entries of `strResOrder` are `D` distinct
vertices of the block ("fills `Res(v)` with `D` vertices of `σ(v)` chosen by a fixed rule, which
is possible because `b_ℓ ≥ D`"). -/
theorem strReserve (hDR : D ≤ R) (bc : ℕ → ℕ) :
    ((strResOrder R D bc).take D).length = D ∧ ((strResOrder R D bc).take D).Nodup ∧
      ∀ t ∈ (strResOrder R D bc).take D, t < R := by
  refine ⟨?_, (strResOrder_nodup bc).sublist (List.take_sublist _ _), fun t ht => ?_⟩
  · rw [List.length_take, length_strResOrder, min_eq_left hDR]
  · exact mem_strResOrder.1 (List.mem_of_mem_take ht)

/-- Server positions permute the block. -/
theorem strResPos_blockPerm (hR : 0 < R) (col : ℕ → ℕ) : BlockPerm R (strResPos R D col) where
  lt w t := by
    unfold strResPos
    rw [List.getD_eq_getElem?_getD]
    cases h : (strResOrder R D (blockCol col R w))[t]? with
    | none => simpa using hR
    | some a => simpa using mem_strResOrder.1 (List.mem_of_getElem? h)
  inj w t t' ht ht' heq := by
    unfold strResPos at heq
    have hl := length_strResOrder (R := R) (D := D) (blockCol col R w)
    rw [List.getD_of_lt _ (by rw [hl]; exact ht), List.getD_of_lt _ (by rw [hl]; exact ht')] at heq
    exact ((strResOrder_nodup _).getElem_inj_iff).1 heq

theorem strResOrder_congr {bc bc' : ℕ → ℕ} (h : ∀ t < R, bc t = bc' t) :
    strResOrder R D bc = strResOrder R D bc' := by
  unfold strResOrder
  rw [strPopular_congr h]
  congr 1 <;> apply List.filter_congr <;> intro t ht <;> rw [h t (List.mem_range.1 ht)]

theorem strResPos_congr {col col' : ℕ → ℕ} {w : ℕ}
    (h : ∀ t < R, col (w * R + t) = col' (w * R + t)) :
    strResPos R D col w = strResPos R D col' w := by
  funext r
  unfold strResPos
  rw [strResOrder_congr (bc := blockCol col R w) (bc' := blockCol col' R w) h]

/-- If step 3 of Construction 6.1 is possible for the block of `w`, its servers are those of
Construction 6.1. -/
theorem strResPos_eq_resPos {col : ℕ → ℕ} {w : ℕ}
    (h : D ≤ (clsList R (blockCol col R w) (popular R D (blockCol col R w))).length) :
    strResPos R D col w = resPos R D col w := by
  funext r
  unfold strResPos strResOrder resPos resOrder
  rw [strPopular_eq_popular h]

end Rule

/-! ### The outer adversary in structure mode -/

/-- The reservation adversary of `𝒜^str` in structure mode, for a given inner input sequence `H`:
the next vertex is in the block of `v = |h| / R` and its earlier neighbours are the servers of the
arcs into `v`. -/
def strResAdv (R D : ℕ) (H : ℕ → Finset ℕ) (h : History) : Finset ℕ :=
  blowSeq R H (strResPos R D (colourAt h)) h.length

/-- The outer input presented to `X`. -/
def strOutSeq (R D : ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) : ℕ → Finset ℕ :=
  playSeq (strResAdv R D H) X

/-- The colours that `X` gives to the outer vertices. -/
def strOutCol (R D : ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) : ℕ → ℕ :=
  runCol X (strOutSeq R D H X)

/-- The induced colour of the inner vertex `v`. -/
def strIndCol (R D : ℕ) (H : ℕ → Finset ℕ) (X : OnlineAlg) (v : ℕ) : ℕ :=
  strPopular R D (blockCol (strOutCol R D H X) R v)

section Outer

variable {R D : ℕ} {H : ℕ → Finset ℕ} {X : OnlineAlg}

/-- The outer input is the static blow-up of `H` with the server positions chosen from the colours
of `X`. -/
theorem strOutSeq_eq (hH : ValidSeq H) :
    strOutSeq R D H X = blowSeq R H (strResPos R D (strOutCol R D H X)) := by
  funext p
  change strResAdv R D H (play (strResAdv R D H) X p) = _
  unfold strResAdv
  rw [length_play]
  apply blowSeq_congr_σ
  intro w hw
  apply strResPos_congr
  intro t ht
  apply colourAt_play
  have h₁ : w < p / R := mem_range.1 (hH _ hw)
  have h₂ : w * R + R ≤ p / R * R := by
    have := Nat.mul_le_mul_right R h₁
    rwa [Nat.succ_mul] at this
  have h₃ := Nat.div_mul_le_self p R
  omega

theorem strOutSeq_valid (hH : ValidSeq H) (hR : 0 < R) : ValidSeq (strOutSeq R D H X) := by
  rw [strOutSeq_eq hH]
  exact blowSeq_valid hH hR (strResPos_blockPerm hR _)

theorem strResAdv_congr {H' : ℕ → Finset ℕ} {V : ℕ} (hHH : ∀ i ≤ V, H i = H' i)
    {hist : History} (hl : hist.length / R ≤ V) :
    strResAdv R D H hist = strResAdv R D H' hist := by
  unfold strResAdv blowSeq
  rw [hHH _ hl]
  have hr : ∀ w, rank H w (hist.length / R) = rank H' w (hist.length / R) :=
    fun w => rank_congr fun i hi => hHH i (by omega)
  simp only [hr]

theorem play_strResAdv_congr {H' : ℕ → Finset ℕ} {V : ℕ} (hR : 0 < R)
    (hHH : ∀ i ≤ V, H i = H' i) :
    play (strResAdv R D H) X ((V + 1) * R) = play (strResAdv R D H') X ((V + 1) * R) :=
  play_congr
    (fun _ hl => strResAdv_congr hHH (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hR).2 hl)))
    _ le_rfl

end Outer

/-! ### The induced algorithm -/

/-- The colour that the induced algorithm computes: replay the outer adversary against `X` on the
inner input so far, up to the end of the block of the new inner vertex, and take the induced
colour of that block. -/
def strSimCol (X : OnlineAlg) (R D : ℕ) (h : History) (s : Finset ℕ) : ℕ :=
  strPopular R D
    (blockCol (colourAt (play (strResAdv R D (innerSeq h s)) X ((h.length + 1) * R))) R h.length)

/-- **The induced algorithm of one level of `𝒜^str`.**  It answers the new inner vertex with the
induced colour of its block.  There is no fallback: once `X` has used `K` colours, the colouring
it produces may be improper. -/
def strInduced (X : OnlineAlg) (K D : ℕ) : OnlineAlg :=
  ⟨fun g s => strSimCol X (R K D) D (clean g) (s ∩ range g.length)⟩

theorem strSimCol_runHist {R D : ℕ} {H : ℕ → Finset ℕ} {X : OnlineAlg} (hR : 0 < R)
    (A' : OnlineAlg) (v : ℕ) :
    strSimCol X R D (runHist A' H v) (H v) = strIndCol R D H X v := by
  unfold strSimCol strIndCol
  rw [length_runHist, play_strResAdv_congr hR (innerSeq_runHist A' H v)]
  apply strPopular_congr
  intro t ht
  unfold blockCol strOutCol strOutSeq
  apply colourAt_play
  rw [Nat.succ_mul]
  omega

/-- On a valid input sequence, the induced algorithm gives every inner vertex the induced colour
of its block. -/
theorem runCol_strInduced {K D : ℕ} {H : ℕ → Finset ℕ} {X : OnlineAlg} (hH : ValidSeq H)
    (v : ℕ) : runCol (strInduced X K D) H v = strIndCol (R K D) D H X v := by
  change strSimCol X (R K D) D (clean (runHist (strInduced X K D) H v))
    (H v ∩ range (runHist (strInduced X K D) H v).length) = _
  rw [Blow.clean_runHist hH, length_runHist, inter_eq_left.2 (hH v),
    strSimCol_runHist (Blow.R_pos K D)]

/-! ### The adversary -/

/-- The induced colour `col(v)` of the inner vertex `v`, read off from the outer history `h`. -/
def strIndColour (K D : ℕ) (h : History) (v : ℕ) : ℕ :=
  strPopular (R K D) D (blockCol (colourAt h) (R K D) v)

/-- The "algorithm" by which `Bstr` answers the inner adversary. -/
def strOracle (K D : ℕ) (h : History) : OnlineAlg := ⟨fun g _ => strIndColour K D h g.length⟩

/-- The inner play simulated by `Bstr` at the outer history `h`. -/
def strInnerHist (K D : ℕ) (A : Adversary) (h : History) : History :=
  A.hist (strOracle K D h) (h.length / R K D)

/-- **One reservation blow-up of `𝒜^str`**: Construction 6.1 without the stop rule and with the
fallback in step 3.  See the module docstring. -/
def Bstr (K D : ℕ) (A : Adversary) : Adversary :=
  ⟨fun h => (A.move (strInnerHist K D A h)).map fun s =>
    strResAdv (R K D) D
      (innerSeq (clean (strInnerHist K D A h)) (s ∩ range (strInnerHist K D A h).length)) h⟩

/-! ### Plays that follow a sequence -/

section Follows

variable {A : Adversary} {X : OnlineAlg} {H : ℕ → Finset ℕ} {q₀ : ℕ}

theorem follows_move_lt (hF : Follows A X H q₀) {q : ℕ} (hq : q < q₀) :
    A.move (A.hist X q) = some (H q) := by
  have h0 := hF q
  have h1 := hF (q + 1)
  rw [min_eq_left hq.le] at h0
  rw [min_eq_left (Nat.succ_le_of_lt hq)] at h1
  cases hm : A.move (A.hist X q) with
  | none =>
    rw [Blow.hist_succ_none hm, h0] at h1
    have := congrArg List.length h1
    simp at this
  | some s =>
    rw [Blow.hist_succ_some hm, h0, runHist_succ] at h1
    have h2 := List.append_cancel_left h1
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h2
    rw [h2.1]

theorem follows_length (hF : Follows A X H q₀) (p : ℕ) : (A.hist X p).length = min p q₀ := by
  rw [hF p, length_runHist]

/-- A play that follows a sequence for `q₀` vertices stops exactly after `q₀` rounds. -/
theorem follows_stopsAt_iff (hF : Follows A X H q₀) {p : ℕ} : A.StopsAt X p ↔ q₀ ≤ p := by
  constructor
  · intro hp
    by_contra hlt
    have := follows_move_lt hF (not_le.1 hlt)
    rw [Adversary.StopsAt] at hp
    rw [hp] at this
    exact absurd this (by simp)
  · intro hp
    rw [Adversary.StopsAt, hF p, min_eq_right hp]
    exact hF.stop

/-- If `A` presents `G t` at the run of `X` on the first `t < T` vertices of `G` and stops at the
run on the first `T` vertices, then its play against `X` follows `G` for `T` vertices. -/
theorem follows_of_moves {G : ℕ → Finset ℕ} {T : ℕ}
    (hmove : ∀ t < T, A.move (runHist X G t) = some (G t))
    (hstop : A.move (runHist X G T) = none) : Follows A X G T := by
  intro p
  induction p with
  | zero => rw [Nat.zero_min, runHist, Adversary.hist]
  | succ p ih =>
    rcases Nat.lt_or_ge p T with hp | hp
    · rw [min_eq_left hp.le] at ih
      rw [Blow.hist_succ_some (by rw [ih]; exact hmove p hp), ih,
        min_eq_left (Nat.succ_le_of_lt hp), runHist_succ, runCol]
    · rw [min_eq_right hp] at ih
      rw [Blow.hist_succ_none (by rw [ih]; exact hstop), ih, min_eq_right (by omega)]

end Follows

/-! ### The play of one level -/

section Level

variable {K D : ℕ} {A : Adversary} {X : OnlineAlg} {H : ℕ → Finset ℕ} {q₀ : ℕ}

/-- If the induced colours read off from `h` are those of the structure-mode play on `H`, then the
inner play simulated at `h` is the play of `A` against the induced algorithm. -/
theorem hist_strOracle (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) {h : History}
    {m : ℕ} (hm : m ≤ q₀)
    (hcol : ∀ i < m, strIndColour K D h i = strIndCol (R K D) D H X i) :
    ∀ i ≤ m, A.hist (strOracle K D h) i = A.hist (strInduced X K D) i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have ih' := ih (Nat.le_of_succ_le hi)
    have hs := follows_move_lt hF (lt_of_lt_of_le hi hm)
    rw [Blow.hist_succ_some (by rw [ih']; exact hs), Blow.hist_succ_some hs, ih']
    congr 3
    change strIndColour K D h (A.hist (strInduced X K D) i).length =
      (strInduced X K D).step (A.hist (strInduced X K D) i) (H i)
    rw [hF i, min_eq_left (by omega), length_runHist, hcol i hi, ← runCol_strInduced hH i]
    rfl

/-- The induced colours of the complete blocks, read off from a history of the structure-mode
play. -/
theorem strIndColour_runHist (t : ℕ) :
    ∀ i < t / R K D,
      strIndColour K D (runHist X (strOutSeq (R K D) D H X) t) i =
        strIndCol (R K D) D H X i := by
  intro i hi
  apply strPopular_congr
  intro u hu
  have := (Nat.mul_le_mul_right (R K D) (Nat.succ_le_of_lt hi)).trans (Nat.div_mul_le_self t _)
  rw [Nat.succ_mul] at this
  exact colourAt_runHist (by omega)

/-- **The inner play.**  At every moment `t ≤ q₀ · R` of the structure-mode play, the inner play
simulated by `Bstr K D A` is the play of `A` against the induced algorithm `strInduced X K D`,
for one round per complete block. -/
theorem strInnerHist_runHist (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) {t : ℕ}
    (ht : t / R K D ≤ q₀) :
    strInnerHist K D A (runHist X (strOutSeq (R K D) D H X) t) =
      A.hist (strInduced X K D) (t / R K D) := by
  unfold strInnerHist
  rw [length_runHist]
  exact hist_strOracle hH hF ht (strIndColour_runHist t) _ le_rfl

theorem Bstr_move_lt (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) {t : ℕ}
    (ht : t < q₀ * R K D) :
    (Bstr K D A).move (runHist X (strOutSeq (R K D) D H X) t) =
      some (strOutSeq (R K D) D H X t) := by
  have hR : 0 < R K D := Blow.R_pos K D
  have hm : t / R K D < q₀ := (Nat.div_lt_iff_lt_mul hR).2 ht
  have hin := strInnerHist_runHist (X := X) hH hF hm.le
  have hs := follows_move_lt hF hm
  change (A.move (strInnerHist K D A _)).map _ = _
  rw [hin, hs, Option.map_some]
  congr 1
  rw [hF, min_eq_left hm.le, Blow.clean_runHist hH, length_runHist, inter_eq_left.2 (hH _),
    strResAdv_congr (V := t / R K D) (innerSeq_runHist _ H _) (by rw [length_runHist])]
  change strResAdv (R K D) D H (runHist X (playSeq (strResAdv (R K D) D H) X) t) =
    playSeq (strResAdv (R K D) D H) X t
  rw [runHist_playSeq]
  rfl

theorem Bstr_move_stop (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) :
    (Bstr K D A).move (runHist X (strOutSeq (R K D) D H X) (q₀ * R K D)) = none := by
  have hR : 0 < R K D := Blow.R_pos K D
  have hm : q₀ * R K D / R K D = q₀ := Nat.mul_div_cancel _ hR
  have hin := strInnerHist_runHist (X := X) (t := q₀ * R K D) hH hF hm.le
  change (A.move (strInnerHist K D A _)).map _ = _
  rw [hin, hm, hF q₀, min_self, hF.stop]
  rfl

/-- **One level of `𝒜^str`.**  If the play of `A` against the induced algorithm follows the valid
input sequence `H` for `q₀` vertices and then stops, then the play of `Bstr K D A` against `X`
follows the reservation blow-up `strOutSeq R D H X` of `H` for exactly `q₀ · R` vertices and then
stops.  Nothing is assumed about `X`. -/
theorem Bstr_follows (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) :
    Follows (Bstr K D A) X (strOutSeq (R K D) D H X) (q₀ * R K D) :=
  follows_of_moves (fun _ ht => Bstr_move_lt hH hF ht) (Bstr_move_stop hH hF)

/-- **The inner play of `𝒜^str`, at every moment of every play** (also after the `K`-th colour):
it is the play of the inner adversary against the induced algorithm `strInduced X K D`, which
need not be proper. -/
theorem Bstr_inner (hH : ValidSeq H) (hF : Follows A (strInduced X K D) H q₀) (p : ℕ) :
    strInnerHist K D A ((Bstr K D A).hist X p) =
      A.hist (strInduced X K D) (((Bstr K D A).hist X p).length / R K D) := by
  have hR : 0 < R K D := Blow.R_pos K D
  rw [Bstr_follows hH hF p, length_runHist]
  apply strInnerHist_runHist hH hF
  exact (Nat.div_le_div_right (min_le_right _ _)).trans (Nat.mul_div_cancel _ hR).le

end Level

/-! ### Before the `K`-th colour: the moves of Construction 6.1 -/

theorem usedColours_eq_image (h : History) :
    usedColours h = (range h.length).image (colourAt h) := by
  ext c
  rw [Blow.mem_usedColours_iff, mem_image]
  simp only [mem_range]

theorem usedColours_append (h : History) (s : Finset ℕ) (c : ℕ) :
    usedColours (h ++ [(s, c)]) = insert c (usedColours h) := by
  ext x
  simp [usedColours]

theorem length_hist_le (A : Adversary) (X : OnlineAlg) (p : ℕ) : (A.hist X p).length ≤ p := by
  induction p with
  | zero => simp [Adversary.hist]
  | succ p ih =>
    cases hm : A.move (A.hist X p) with
    | none => rw [Blow.hist_succ_none hm]; omega
    | some s => rw [Blow.hist_succ_some hm, List.length_append, List.length_singleton]; omega

/-- **Until the `K`-th colour, the moves are those of Construction 6.1.**  Let `A'` and `A` make
the same moves on every history with fewer than `K` colours.  Then on every history `h` with
fewer than `K` colours, `Bstr K D A'` makes the move of `B(𝒜) = Blow.B K D A`.  (No assumption on
how `h` arose.) -/
theorem Bstr_move_eq {K D : ℕ} (hD : 1 ≤ D) {A A' : Adversary}
    (hA : ∀ g : History, (usedColours g).card < K → A'.move g = A.move g) {h : History}
    (hh : (usedColours h).card < K) : (Bstr K D A').move h = (Blow.B K D A).move h := by
  -- a complete block has a colour on `D` vertices (pigeonhole)
  have hblock : ∀ v, (v + 1) * R K D ≤ h.length →
      D ≤ (clsList (R K D) (blockCol (colourAt h) (R K D) v)
        (popular (R K D) D (blockCol (colourAt h) (R K D) v))).length := fun v hv =>
    popular_spec hD (Blow.exists_reserve hv (by rw [← usedColours_eq_image]; exact hh))
  have hcol : ∀ v, (v + 1) * R K D ≤ h.length →
      strIndColour K D h v = Blow.indColour K D h v :=
    fun v hv => strPopular_eq_popular (hblock v hv)
  have hmem : ∀ v, (v + 1) * R K D ≤ h.length → Blow.indColour K D h v ∈ usedColours h := by
    intro v hv
    obtain ⟨u, hu, hcu⟩ := popular_mem hD (hblock v hv)
    have hlt : v * R K D + u < h.length := by
      rw [Nat.succ_mul] at hv
      omega
    have h2 := Blow.colourAt_mem_usedColours hlt
    have hcu' : colourAt h (v * R K D + u) = Blow.indColour K D h v := hcu
    rwa [hcu'] at h2
  -- the two simulated inner plays coincide, and they show colours of `h` only
  have key : ∀ i ≤ h.length / R K D,
      A'.hist (strOracle K D h) i = A.hist (Blow.oracle K D h) i ∧
        usedColours (A.hist (Blow.oracle K D h) i) ⊆ usedColours h := by
    intro i
    induction i with
    | zero => intro _; exact ⟨rfl, by simp [Adversary.hist, usedColours]⟩
    | succ i ih =>
      intro hi
      obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hi)
      have hmv := hA _ (lt_of_le_of_lt (card_le_card ih2) hh)
      cases hm : A.move (A.hist (Blow.oracle K D h) i) with
      | none =>
        rw [Blow.hist_succ_none hm, Blow.hist_succ_none (by rw [ih1, hmv]; exact hm)]
        exact ⟨ih1, ih2⟩
      | some s =>
        have hlen : ((A.hist (Blow.oracle K D h) i).length + 1) * R K D ≤ h.length := by
          have h1 := length_hist_le A (Blow.oracle K D h) i
          exact (Nat.mul_le_mul_right _ (by omega)).trans (Nat.div_mul_le_self _ _)
        rw [Blow.hist_succ_some hm, Blow.hist_succ_some (by rw [ih1, hmv]; exact hm), ih1]
        refine ⟨?_, ?_⟩
        · congr 3
          exact hcol _ hlen
        · rw [usedColours_append]
          exact insert_subset (hmem _ hlen) ih2
  obtain ⟨hin, hsub⟩ := key _ le_rfl
  have hin' : strInnerHist K D A' h = Blow.innerHist K D A h := hin
  have hlen := length_hist_le A (Blow.oracle K D h) (h.length / R K D)
  change (A'.move (strInnerHist K D A' h)).map _ =
    if K ≤ (usedColours h).card then none else (A.move (Blow.innerHist K D A h)).map _
  have hmv : A'.move (Blow.innerHist K D A h) = A.move (Blow.innerHist K D A h) :=
    hA _ (lt_of_le_of_lt (card_le_card hsub) hh)
  rw [ite_eq_right (not_le.2 hh), hin', hmv]
  cases A.move (Blow.innerHist K D A h) with
  | none => rfl
  | some s =>
    rw [Option.map_some, Option.map_some]
    congr 1
    apply blowSeq_congr_σ
    intro w hw
    apply strResPos_eq_resPos
    apply hblock
    -- `w` is an earlier inner vertex, so its block is complete
    have hw' : w < h.length / R K D := by
      unfold innerSeq at hw
      rw [Blow.length_clean] at hw
      change (Blow.innerHist K D A h).length ≤ h.length / R K D at hlen
      split_ifs at hw with h1 h2
      · omega
      · have := mem_range.1 (mem_inter.1 hw).2
        omega
      · simp at hw
    exact (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hw')).trans (Nat.div_mul_le_self _ _)

end OnlineColouring.Str
