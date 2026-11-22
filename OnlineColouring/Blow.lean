module

public import OnlineColouring.AdvBasic
public import OnlineColouring.PlayBound

/-!
# Construction 6.1 and Lemma 6.2: the reservation blow-up `B(𝒜)` as an adversary

Construction 6.1 (`con:blowup`) and Lemma 6.2 (`lem:force`, forcing survives a blow-up) of
Section 6.

## The construction

`Blow.B K D A : Adversary` is the adversary `B(𝒜)` of Construction 6.1 for the inner adversary
`A`, with parameters `K` (the number of colours to force), `D` (the post-degree bound of `A`) and
block size `Blow.R K D = (K-1)(D-1)+1`.  It is a function of the outer history `h` alone:

* It stops if `Alg` has used `K` colours (`K ≤ |usedColours h|`).
* Otherwise let `m = |h| / R` be the number of complete blocks.  The block of the inner vertex `v`
  consists of the outer vertices `vR, …, vR+R-1`.  `B(𝒜)` replays `A` for `m` rounds, answering
  the `v`-th inner vertex with the induced colour `col(v) = Blow.indColour K D h v` of its block
  (`Blow.innerHist`).  If `A` stops, `B(𝒜)` stops.  If `A` presents the inner vertex `m` with
  earlier neighbours `W`, the next outer vertex gets the earlier neighbours `{x_{w,m} : w ∈ W}`.

**The tie-breaking rule** of Construction 6.1 (implemented by `popular` and `resOrder` of
`Structure.lean`):
* `col(v)` is, among the colours used on at least `D` vertices of `σ(v)`, the one whose first
  occurrence in `σ(v)` is earliest;
* `Res(v)` consists of the `D` earliest vertices of `σ(v)` of colour `col(v)`;
* the server `x_{w,v}` removed from `Res(w)` is its earliest remaining vertex, so the `r`-th later
  inner neighbour of `w` (`r = 0, 1, …`) is served by the `r`-th vertex of `Res(w)`.

The definition is total: if no colour occurs `D` times on a block (this happens only when `K`
colours are in use, and then `B(𝒜)` has stopped), `col(v)` is `0`; if `A` exceeded the post-degree
`D`, further servers would be taken from the rest of the block.  Neighbour sets presented by `A`
are read modulo the convention of `Adversary` that indices which are not earlier vertices are
ignored (`Blow.clean`).

## Lemma 6.2

`Blow.lemma_6_2`: if `A` forces `K` colours, has size at most `N` and post-degree at most `D`
(`K ≥ 2`, `D ≥ 1`), then `B(𝒜)` forces `K` colours, has size at most `R·N` and post-degree at most
`R`.  Moreover, for every proper `Alg` the algorithm `Alg' = Blow.induced Alg K D` is proper (on
every history), and at every moment `p` of the play of `B(𝒜)` against `Alg` at which `Alg` has used
at most `K - 1` colours, with `h` the outer history and `m = |h| / R` the number of complete
blocks:
* the inner play that `B(𝒜)` has simulated (`innerHist K D A h`: the inner graph with the induced
  colours) *is* the play `A.hist Alg' m` of `A` against `Alg'`, and it has `m` vertices;
* so for every `v < m` the induced colour `col(v)` is the colour that `Alg'` gives `v` against `A`;
* `col(v)` occurs on at least `D` vertices of the block of `v` ("step 3 is possible"), and it is a
  colour used by `Alg`.

`Alg'` is the induced algorithm `inducedAlg` of `Structure.lean`, precomposed with `clean`.  As in
the paper's proof, it carries out steps 1 to 3 against `Alg` for the inner vertices so far,
without the stop rule, and answers with the induced colour of the new block if that colour differs
from the colours it gave to the earlier neighbours, and with a colour not used on them (a fresh
colour) otherwise.  It is proper on every history and depends only on `Alg`, `K` and `D`.

The proof follows the paper.  The technical core `Blow.sim` is stated for an inner adversary that
*tracks* a valid input sequence `H` against `Alg'` (`Blow.Tracks`); then `B(𝒜)` follows the outer
sequence `outSeq R D H Alg` of `Structure.lean` up to the first moment `T` at which `Alg` has used
`K` colours (`Blow.Follows`).  This form is reused for the stacked constructions
(`BlowStack.lean`, `BlowTower.lean`).  `Blow.exists_play` is `sim` under the hypotheses of the
lemma.

## The servers have the induced colour

`Blow.server_colour` is the last sentence of Lemma 6.3 for one blow-up: under the hypotheses of
Lemma 6.2, at every moment at which `Alg` has used at most `K - 1` colours, the earlier neighbours
of the outer vertex that `B(𝒜)` presents next are servers `x_{w,m}`, one in the block of each
earlier neighbour `w` of the current inner vertex `m`, and `x_{w,m}` has the induced colour
`col(w)`: it comes from `Res(w)`, since step 3 was possible for `w` and `w` has at most `D` later
neighbours.
-/

@[expose] public section

namespace OnlineColouring.Blow

open Finset

/-! ### Plays -/

variable {A : Adversary} {Alg : OnlineAlg}

theorem hist_succ_none {p : ℕ} (h : A.move (A.hist Alg p) = none) :
    A.hist Alg (p + 1) = A.hist Alg p := by
  rw [Adversary.hist, h]

theorem hist_succ_some {p : ℕ} {s : Finset ℕ} (h : A.move (A.hist Alg p) = some s) :
    A.hist Alg (p + 1) = A.hist Alg p ++ [(s, Alg.step (A.hist Alg p) s)] := by
  rw [Adversary.hist, h]

/-- Once the adversary has stopped, the history no longer changes. -/
theorem hist_eq_of_stop {p : ℕ} (h : A.move (A.hist Alg p) = none) :
    ∀ q, p ≤ q → A.hist Alg q = A.hist Alg p := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => rfl
  | succ q _ ih => rw [hist_succ_none (by rw [ih]; exact h), ih]

/-- The play of `A` against `Alg` follows the input sequence `H` and stops after `T` vertices. -/
def Follows (A : Adversary) (Alg : OnlineAlg) (H : ℕ → Finset ℕ) (T : ℕ) : Prop :=
  ∀ p, A.hist Alg p = runHist Alg H (min p T)

theorem Follows.stop {H : ℕ → Finset ℕ} {T : ℕ} (hF : Follows A Alg H T) :
    A.move (runHist Alg H T) = none := by
  have h0 := hF T
  have h1 := hF (T + 1)
  rw [min_self] at h0
  rw [min_eq_right (Nat.le_succ T)] at h1
  cases hm : A.move (A.hist Alg T) with
  | none => rwa [h0] at hm
  | some s =>
    rw [hist_succ_some hm, h0] at h1
    have := congrArg List.length h1
    simp at this

/-! ### Cleaning a history -/

/-- The history `h` with every earlier-neighbour set restricted to the earlier vertices (indices
that are not earlier vertices are ignored by everybody). -/
def clean (h : History) : History :=
  (List.range h.length).map fun i => ((h.getD i (∅, 0)).1 ∩ range i, colourAt h i)

@[simp] theorem length_clean (h : History) : (clean h).length = h.length := by
  simp [clean]

theorem clean_append (h : History) (s : Finset ℕ) (c : ℕ) :
    clean (h ++ [(s, c)]) = clean h ++ [(s ∩ range h.length, c)] := by
  unfold clean
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp [colourAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · simp [colourAt, List.getD_eq_getElem?_getD]

theorem colourAt_clean (h : History) (i : ℕ) : colourAt (clean h) i = colourAt h i := by
  unfold clean colourAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i h.length with hi | hi
  · simp [hi, List.getD_eq_getElem?_getD]
  · simp [hi]

theorem nbrColours_clean (h : History) (s : Finset ℕ) :
    nbrColours (clean h) (s ∩ range h.length) = nbrColours h s := by
  unfold nbrColours
  rw [length_clean]
  have : (s ∩ range h.length).filter (· < h.length) = s.filter (· < h.length) := by
    ext x
    simp only [mem_filter, mem_inter, mem_range]
    tauto
  rw [this]
  exact image_congr fun i _ => colourAt_clean h i

theorem usedColours_clean (h : History) : usedColours (clean h) = usedColours h := by
  ext c
  simp only [usedColours, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [length_clean] at hi
    refine ⟨h[i], List.getElem_mem _, ?_⟩
    rw [← colourAt_eq_getElem (h := clean h) (by simpa using hi), colourAt_clean,
      colourAt_eq_getElem hi]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < (clean h).length := by simpa using hi
    refine ⟨(clean h)[i], List.getElem_mem _, ?_⟩
    rw [← colourAt_eq_getElem hi', colourAt_clean, colourAt_eq_getElem hi]

/-- A run on a valid input sequence is clean. -/
theorem clean_runHist {N : ℕ → Finset ℕ} (hN : ValidSeq N) (X : OnlineAlg) (t : ℕ) :
    clean (runHist X N t) = runHist X N t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runHist_succ, clean_append, ih, length_runHist, inter_eq_left.2 (hN t)]

/-! ### The construction -/

/-- The block size `R = (K-1)(D-1)+1` of Construction 6.1. -/
def R (K D : ℕ) : ℕ := (K - 1) * (D - 1) + 1

theorem R_pos (K D : ℕ) : 0 < R K D := Nat.succ_pos _

theorem le_R {K D : ℕ} (hK : 2 ≤ K) : D ≤ R K D := by
  unfold R
  have : D - 1 ≤ (K - 1) * (D - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The induced colour `col(v)` of the inner vertex `v`, read off from the outer history `h`: the
first colour, in the order of the block `vR, …, vR+R-1`, that occurs on at least `D` of its
vertices. -/
def indColour (K D : ℕ) (h : History) (v : ℕ) : ℕ :=
  popular (R K D) D (blockCol (colourAt h) (R K D) v)

/-- The "algorithm" by which `B(𝒜)` answers the inner adversary: the inner vertex `v` gets the
induced colour of its block in the outer history `h`. -/
def oracle (K D : ℕ) (h : History) : OnlineAlg := ⟨fun g _ => indColour K D h g.length⟩

/-- The inner play simulated by `B(𝒜)` at the outer history `h`: the inner adversary `A` is run
for one round per complete block and shown the induced colours. -/
def innerHist (K D : ℕ) (A : Adversary) (h : History) : History :=
  A.hist (oracle K D h) (h.length / R K D)

/-- **Construction 6.1: the reservation blow-up `B(𝒜)`.**  See the module docstring. -/
def B (K D : ℕ) (A : Adversary) : Adversary :=
  ⟨fun h =>
    if K ≤ (usedColours h).card then none
    else (A.move (innerHist K D A h)).map fun s =>
      resAdv (R K D) D
        (innerSeq (clean (innerHist K D A h)) (s ∩ range (innerHist K D A h).length)) h⟩

/-- The induced algorithm `Alg'` of Lemma 6.2 for the inner game. -/
def induced (Alg : OnlineAlg) (K D : ℕ) : OnlineAlg :=
  ⟨fun g s => (inducedAlg Alg (R K D) D).step (clean g) (s ∩ range g.length)⟩

theorem induced_step (Alg : OnlineAlg) (K D : ℕ) (g : History) (s : Finset ℕ) :
    (induced Alg K D).step g s =
      (inducedAlg Alg (R K D) D).step (clean g) (s ∩ range g.length) := rfl

/-- `Alg'` is proper on every history. -/
theorem induced_isProper (Alg : OnlineAlg) (K D : ℕ) : (induced Alg K D).IsProper := by
  rw [OnlineAlg.isProper_iff]
  intro g s
  have := (OnlineAlg.isProper_iff _).1 (inducedAlg_isProper Alg (R K D) D) (clean g)
    (s ∩ range g.length)
  rwa [nbrColours_clean, ← induced_step] at this

/-- On a valid input sequence, `Alg'` runs like `inducedAlg`. -/
theorem runHist_induced {N : ℕ → Finset ℕ} (hN : ValidSeq N) (K D : ℕ) (t : ℕ) :
    runHist (induced Alg K D) N t = runHist (inducedAlg Alg (R K D) D) N t := by
  induction t with
  | zero => rw [runHist, runHist]
  | succ t ih =>
    rw [runHist_succ, runHist_succ, runCol, runCol, induced_step, clean_runHist hN,
      length_runHist, inter_eq_left.2 (hN t), ih]

theorem runCol_induced {N : ℕ → Finset ℕ} (hN : ValidSeq N) (K D : ℕ) (t : ℕ) :
    runCol (induced Alg K D) N t = runCol (inducedAlg Alg (R K D) D) N t := by
  have := runHist_induced (Alg := Alg) hN K D (t + 1)
  rw [runHist_succ, runHist_succ, runHist_induced hN] at this
  simpa using List.append_cancel_left this

/-! ### Tracking -/

/-- The play of `A` against `A'` is, after cleaning, the run of `ind` on the input sequence `H`,
and it stops after `q₀` vertices. -/
def Tracks (A : Adversary) (A' ind : OnlineAlg) (H : ℕ → Finset ℕ) (q₀ : ℕ) : Prop :=
  ∀ q, clean (A.hist A' q) = runHist ind H (min q q₀)

section Tracks

variable {A' ind : OnlineAlg} {H : ℕ → Finset ℕ} {q₀ : ℕ}

theorem Tracks.length (hT : Tracks A A' ind H q₀) (q : ℕ) : (A.hist A' q).length = min q q₀ := by
  have := congrArg List.length (hT q)
  simpa using this

theorem Tracks.move_lt (hT : Tracks A A' ind H q₀) {q : ℕ} (hq : q < q₀) :
    ∃ s, A.move (A.hist A' q) = some s ∧ s ∩ range q = H q ∧
      A'.step (A.hist A' q) s = runCol ind H q := by
  cases hm : A.move (A.hist A' q) with
  | none =>
    have h1 := hT.length (q + 1)
    rw [hist_succ_none hm, hT.length q] at h1
    omega
  | some s =>
    refine ⟨s, rfl, ?_⟩
    have h1 := hT (q + 1)
    rw [hist_succ_some hm, clean_append, hT q, hT.length q, min_eq_left hq.le,
      min_eq_left (Nat.succ_le_of_lt hq), runHist_succ] at h1
    simpa using List.append_cancel_left h1

theorem Tracks.move_stop (hT : Tracks A A' ind H q₀) : A.move (A.hist A' q₀) = none := by
  cases hm : A.move (A.hist A' q₀) with
  | none => rfl
  | some s =>
    have h1 := hT.length (q₀ + 1)
    rw [hist_succ_some hm, List.length_append, hT.length q₀] at h1
    simp at h1

/-- A play that follows a valid sequence tracks it. -/
theorem Follows.tracks {K D : ℕ} (hH : ValidSeq H)
    (hF : Follows A (induced Alg K D) H q₀) :
    Tracks A (induced Alg K D) (inducedAlg Alg (R K D) D) H q₀ := by
  intro q
  rw [hF q, clean_runHist hH, runHist_induced hH]

/-- If the induced colours read off from `h` are the colours of `ind` on `H`, then the inner play
simulated at `h` is the play against `A'`. -/
theorem Tracks.hist_oracle {K D : ℕ} (hT : Tracks A A' ind H q₀) {h : History} {m : ℕ}
    (hm : m ≤ q₀) (hcol : ∀ i < m, indColour K D h i = runCol ind H i) :
    ∀ i ≤ m, A.hist (oracle K D h) i = A.hist A' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have ih' := ih (Nat.le_of_succ_le hi)
    obtain ⟨s, hs, -, hstep⟩ := hT.move_lt (lt_of_lt_of_le hi hm)
    rw [hist_succ_some (by rw [ih']; exact hs), hist_succ_some hs, ih']
    congr 3
    change indColour K D h (A.hist A' i).length = _
    rw [hT.length i, min_eq_left (by omega), hcol i hi, hstep]

/-- The move of `B(𝒜)` at an outer history `h` with fewer than `K` colours whose current inner
vertex exists and whose complete blocks have the induced colours of `ind` on `H`: it is the move
of the structure-mode reservation adversary `resAdv` on `H`. -/
theorem Tracks.move_B {K D : ℕ} (hT : Tracks A A' ind H q₀) {h : History}
    (hm : h.length / R K D < q₀) (hK : (usedColours h).card < K)
    (hcol : ∀ i < h.length / R K D, indColour K D h i = runCol ind H i) :
    (B K D A).move h = some (resAdv (R K D) D H h) := by
  have hin : innerHist K D A h = A.hist A' (h.length / R K D) :=
    hT.hist_oracle hm.le hcol _ le_rfl
  obtain ⟨s, hs, hsH, -⟩ := hT.move_lt hm
  change (if K ≤ (usedColours h).card then none else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.2 hK)), hin, hs, Option.map_some]
  congr 1
  apply resAdv_congr (V := h.length / R K D) _ le_rfl
  intro i hi
  rw [hT, hT.length, min_eq_left hm.le, hsH]
  exact innerSeq_runHist ind H _ i hi

end Tracks

/-! ### The simulation -/

theorem colourAt_mem_usedColours {h : History} {i : ℕ} (hi : i < h.length) :
    colourAt h i ∈ usedColours h := by
  rw [colourAt_eq_getElem hi]
  simp only [usedColours, List.mem_toFinset, List.mem_map]
  exact ⟨h[i], List.getElem_mem _, rfl⟩

section Sim

variable {K D : ℕ} {A' : OnlineAlg} {H : ℕ → Finset ℕ} {q₀ : ℕ}

/-- **Step 3 is possible** (pigeonhole).  A complete block among the first `t` outer vertices, on
which fewer than `K` colours are in use, has a colour that occurs on at least `D` of its
vertices. -/
theorem exists_reserve {col : ℕ → ℕ} {t v : ℕ} (hv : (v + 1) * R K D ≤ t)
    (hK : ((range t).image col).card < K) :
    ∃ c, D ≤ (clsList (R K D) (blockCol col (R K D) v) c).length := by
  have hlt : ((range (R K D)).image (blockCol col (R K D) v)).card < K := by
    refine lt_of_le_of_lt (card_le_card ?_) hK
    intro c hc
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hc
    rw [mem_range] at hu
    refine mem_image.2 ⟨v * R K D + u, mem_range.2 ?_, rfl⟩
    rw [Nat.succ_mul] at hv
    omega
  obtain ⟨b, -, hb⟩ := exists_large_colour_class (range (R K D)) (blockCol col (R K D) v)
    (by rw [card_range]; exact le_of_eq rfl) hlt
  exact ⟨b, by rw [length_clsList]; exact hb⟩

/-- **The simulation behind Lemma 6.2.**  Suppose the play of the inner adversary `A` against
`A'` tracks the valid input sequence `H` (as run by `inducedAlg Alg R D`) and stops after `q₀`
vertices, of post-degree at most `D`, with `K` colours in use.  Then the play of `B(𝒜)` against
the proper algorithm `Alg` follows the structure-mode outer sequence `outSeq R D H Alg` up to the
first moment `T ≤ q₀·R` at which `Alg` has used `K` colours.  At every earlier moment `t < T` the
inner play simulated by `B(𝒜)` is the play of `A` against `A'`, every complete block `v` has the
induced colour `runCol (inducedAlg Alg R D) H v`, and this colour occurs on at least `D` vertices
of the block. -/
theorem sim (hD : 1 ≤ D) (hAlg : Alg.IsProper) (hH : ValidSeq H)
    (hT : Tracks A A' (inducedAlg Alg (R K D) D) H q₀)
    (hdeg : ∀ w < q₀, postDeg H q₀ w ≤ D)
    (hforce : K ≤ ((range q₀).image (runCol (inducedAlg Alg (R K D) D) H)).card) :
    ∃ T ≤ q₀ * R K D, Follows (B K D A) Alg (outSeq (R K D) D H Alg) T ∧
      K ≤ ((range T).image (outCol (R K D) D H Alg)).card ∧
      (∀ t < T, ((range t).image (outCol (R K D) D H Alg)).card < K) ∧
      ∀ t < T, t / R K D < q₀ ∧
        innerHist K D A (runHist Alg (outSeq (R K D) D H Alg) t) = A.hist A' (t / R K D) ∧
        ∀ v < t / R K D,
          indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v =
            runCol (inducedAlg Alg (R K D) D) H v ∧
          D ≤ (clsList (R K D)
            (blockCol (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) (R K D) v)
            (indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v)).length := by
  classical
  have hR : 0 < R K D := R_pos K D
  have hused : ∀ t, usedColours (runHist Alg (outSeq (R K D) D H Alg) t) =
      (range t).image (outCol (R K D) D H Alg) := fun t => usedColours_runHist Alg _ t
  have hS1 : K ≤ ((range (q₀ * R K D)).image (outCol (R K D) D H Alg)).card :=
    forcing_step (K := K) rfl hD hAlg hH hdeg hforce
  have hex : ∃ t, K ≤ ((range t).image (outCol (R K D) D H Alg)).card := ⟨_, hS1⟩
  have hTle := Nat.find_min' hex hS1
  have hTK := Nat.find_spec hex
  have hlt : ∀ t < Nat.find hex, ((range t).image (outCol (R K D) D H Alg)).card < K :=
    fun t ht => not_le.1 (Nat.find_min hex ht)
  generalize Nat.find hex = T at hTle hTK hlt
  have key : ∀ t < T, t / R K D < q₀ ∧ ∀ v < t / R K D,
      indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v =
        runCol (inducedAlg Alg (R K D) D) H v ∧
      D ≤ (clsList (R K D)
        (blockCol (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) (R K D) v)
        (indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v)).length := by
    intro t ht
    have hm : t / R K D < q₀ := (Nat.div_lt_iff_lt_mul hR).2 (lt_of_lt_of_le ht hTle)
    have hblock : ∀ v < t / R K D, (v + 1) * R K D ≤ t := by
      intro v hv
      exact (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hv)).trans (Nat.div_mul_le_self t _)
    have hfaith : ∀ v < t / R K D,
        ∃ c, D ≤ (clsList (R K D) (blockCol (outCol (R K D) D H Alg) (R K D) v) c).length :=
      fun v hv => exists_reserve (hblock v hv) (hlt t ht)
    have heq := runCol_inducedAlg_eq hAlg hH hR hD hdeg hm.le hfaith
    have hbc : ∀ v < t / R K D, ∀ u < R K D,
        blockCol (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) (R K D) v u =
          blockCol (outCol (R K D) D H Alg) (R K D) v u := by
      intro v hv u hu
      have := hblock v hv
      rw [Nat.succ_mul] at this
      exact colourAt_runHist (by omega)
    refine ⟨hm, fun v hv => ⟨?_, ?_⟩⟩
    · rw [heq v hv]
      exact popular_congr (hbc v hv)
    · obtain ⟨c, hc⟩ := hfaith v hv
      exact popular_spec hD ⟨c, by rw [clsList_congr (hbc v hv)]; exact hc⟩
  have hmove : ∀ t < T, (B K D A).move (runHist Alg (outSeq (R K D) D H Alg) t) =
      some (outSeq (R K D) D H Alg t) := by
    intro t ht
    obtain ⟨hm, hc⟩ := key t ht
    rw [hT.move_B (by rw [length_runHist]; exact hm) (by rw [hused]; exact hlt t ht)
      (by rw [length_runHist]; exact fun i hi => (hc i hi).1)]
    congr 1
    change resAdv (R K D) D H (runHist Alg (playSeq (resAdv (R K D) D H) Alg) t) =
      playSeq (resAdv (R K D) D H) Alg t
    rw [runHist_playSeq]
    rfl
  have hstop : (B K D A).move (runHist Alg (outSeq (R K D) D H Alg) T) = none := by
    change (if K ≤ (usedColours (runHist Alg (outSeq (R K D) D H Alg) T)).card then none
      else _) = none
    rw [hused]
    exact ite_eq_left_of_eq_true _ _ (eq_true hTK)
  have hfol : Follows (B K D A) Alg (outSeq (R K D) D H Alg) T := by
    intro p
    induction p with
    | zero => rw [Nat.zero_min, runHist, Adversary.hist]
    | succ p ih =>
      rcases Nat.lt_or_ge p T with hp | hp
      · rw [min_eq_left hp.le] at ih
        rw [hist_succ_some (by rw [ih]; exact hmove p hp), ih,
          min_eq_left (Nat.succ_le_of_lt hp), runHist_succ, runCol]
      · rw [min_eq_right hp] at ih
        rw [hist_succ_none (by rw [ih]; exact hstop), ih, min_eq_right (by omega)]
  refine ⟨T, hTle, hfol, hTK, hlt, fun t ht => ?_⟩
  obtain ⟨hm, hc⟩ := key t ht
  refine ⟨hm, ?_, hc⟩
  have := hT.hist_oracle (K := K) (D := D) (h := runHist Alg (outSeq (R K D) D H Alg) t) hm.le
    (fun i hi => (hc i hi).1) _ le_rfl
  unfold innerHist
  rw [length_runHist]
  exact this

end Sim

/-! ### Lemma 6.2 -/

/-- The input that `A` presents against `A'`, with every earlier-neighbour set restricted to the
earlier vertices (empty once `A` has stopped). -/
def inSeq (A : Adversary) (A' : OnlineAlg) (i : ℕ) : Finset ℕ :=
  (A.move (A.hist A' i)).getD ∅ ∩ range i

theorem inSeq_valid (A : Adversary) (A' : OnlineAlg) : ValidSeq (inSeq A A') :=
  fun _ => inter_subset_right

/-- A play that stops after `q₀` vertices tracks its own (cleaned) input. -/
theorem tracks_inSeq {K D q₀ : ℕ}
    (hlt : ∀ q < q₀, A.move (A.hist (induced Alg K D) q) ≠ none)
    (hstop : A.move (A.hist (induced Alg K D) q₀) = none) :
    Tracks A (induced Alg K D) (inducedAlg Alg (R K D) D) (inSeq A (induced Alg K D)) q₀ := by
  have key : ∀ q ≤ q₀, clean (A.hist (induced Alg K D) q) =
      runHist (inducedAlg Alg (R K D) D) (inSeq A (induced Alg K D)) q ∧
      (A.hist (induced Alg K D) q).length = q := by
    intro q
    induction q with
    | zero => intro _; rw [runHist, Adversary.hist]; exact ⟨rfl, rfl⟩
    | succ q ih =>
      intro hq
      obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hq)
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 (hlt q hq)
      have hHq : inSeq A (induced Alg K D) q = s ∩ range q := by simp [inSeq, hs]
      rw [hist_succ_some hs]
      refine ⟨?_, by simp [ih2]⟩
      rw [clean_append, ih2, runHist_succ, runCol, ← ih1, hHq, induced_step, ih2]
  intro q
  rcases le_total q q₀ with hq | hq
  · rw [min_eq_left hq]
    exact (key q hq).1
  · rw [min_eq_right hq, hist_eq_of_stop hstop q hq]
    exact (key q₀ le_rfl).1

theorem getD_clean {h : History} {v : ℕ} (hv : v < h.length) :
    (clean h).getD v (∅, 0) = ((h.getD v (∅, 0)).1 ∩ range v, colourAt h v) := by
  unfold clean
  simp [List.getD_eq_getElem?_getD, hv]

/-- Along a tracked play, the post-degrees of the input sequence are those of the history. -/
theorem Tracks.postDeg_eq {A' ind : OnlineAlg} {H : ℕ → Finset ℕ} {q₀ : ℕ}
    (hT : Tracks A A' ind H q₀) (w : ℕ) : postDeg H q₀ w = (A.hist A' q₀).postDeg w := by
  have hlen : (A.hist A' q₀).length = q₀ := by rw [hT.length, min_self]
  have hH : ∀ v < q₀, ((A.hist A' q₀).getD v (∅, 0)).1 ∩ range v = H v := by
    intro v hv
    have h1 := getD_clean (h := A.hist A' q₀) (v := v) (by rw [hlen]; exact hv)
    have h2 := hT q₀
    rw [min_self] at h2
    rw [h2, List.getD_of_lt _ (by simpa using hv), getElem_runHist] at h1
    exact (congrArg Prod.fst h1).symm
  unfold postDeg rank History.postDeg
  rw [hlen]
  congr 1
  apply filter_congr
  intro v hv
  rw [mem_range] at hv
  rw [← hH v hv, mem_inter, mem_range, and_comm]

theorem rank_mono (H : ℕ → Finset ℕ) (w : ℕ) {m m' : ℕ} (h : m ≤ m') :
    rank H w m ≤ rank H w m' :=
  card_le_card (filter_subset_filter _ (range_mono h))

/-- The post-degrees of a run are bounded by those of its input sequence. -/
theorem postDeg_runHist_le (X : OnlineAlg) (N : ℕ → Finset ℕ) (t i : ℕ) :
    (runHist X N t).postDeg i ≤ rank N i t := by
  unfold History.postDeg rank
  rw [length_runHist]
  apply card_le_card
  intro v hv
  rw [mem_filter, mem_range] at hv ⊢
  refine ⟨hv.1, ?_⟩
  have := hv.2.2
  rwa [List.getD_of_lt _ (by simpa using hv.1), getElem_runHist] at this

section Lemma

variable {K D N : ℕ}

/-- The play of `B(𝒜)` against a proper algorithm `Alg`, when `A` forces `K` colours, has size at
most `N` and post-degree at most `D`: the inner play against `Alg'` tracks a valid input sequence
`H` and stops after `q₀ ≤ N` vertices, and `sim` applies. -/
theorem exists_sim (Alg : OnlineAlg) (hF : A.Forces K) (hS : A.SizeLE N)
    (hP : A.PostDegLE D) :
    ∃ (H : ℕ → Finset ℕ) (_ : ValidSeq H) (q₀ : ℕ), q₀ ≤ N ∧
      Tracks A (induced Alg K D) (inducedAlg Alg (R K D) D) H q₀ ∧
      (∀ w < q₀, postDeg H q₀ w ≤ D) ∧
      K ≤ ((range q₀).image (runCol (inducedAlg Alg (R K D) D) H)).card := by
  classical
  have hA' := induced_isProper Alg K D
  obtain ⟨q, hq, hqK⟩ := hF _ hA'
  have hex : ∃ q, A.move (A.hist (induced Alg K D) q) = none := ⟨q, hq⟩
  have hstop := Nat.find_spec hex
  have hlt : ∀ q' < Nat.find hex, A.move (A.hist (induced Alg K D) q') ≠ none :=
    fun q' h => Nat.find_min hex h
  have hle : Nat.find hex ≤ q := Nat.find_min' hex hq
  generalize Nat.find hex = q₀ at hstop hlt hle
  have hT := tracks_inSeq hlt hstop
  have hlen : (A.hist (induced Alg K D) q₀).length = q₀ := by rw [hT.length, min_self]
  refine ⟨_, inSeq_valid A _, q₀, ?_, hT, fun w _ => ?_, ?_⟩
  · rw [← hlen]
    exact hS _ hA' q₀
  · rw [hT.postDeg_eq]
    exact hP _ hA' q₀ w
  · have h2 := hT q₀
    rw [min_self] at h2
    rw [← usedColours_runHist, ← h2, usedColours_clean, ← hist_eq_of_stop hstop q hle]
    exact hqK

/-- **The play of `B(𝒜)`** against a proper algorithm `Alg`, when `A` forces `K` colours, has size
at most `N` and post-degree at most `D` (`exists_sim` followed by `sim`): the inner play against
`Alg'` tracks a valid input sequence `H` and stops after `q₀ ≤ N` vertices, and the play of `B(𝒜)`
follows the outer sequence `outSeq R D H Alg` up to the first moment `T ≤ q₀·R` at which `Alg` has
used `K` colours.  At every earlier moment `t < T` the inner play simulated by `B(𝒜)` is the play
of `A` against `Alg'`, and every complete block has its induced colour on at least `D` of its
vertices. -/
theorem exists_play (hD : 1 ≤ D) {A : Adversary} (hF : A.Forces K) (hS : A.SizeLE N)
    (hP : A.PostDegLE D) {Alg : OnlineAlg} (hAlg : Alg.IsProper) :
    ∃ (H : ℕ → Finset ℕ) (_ : ValidSeq H) (q₀ T : ℕ), q₀ ≤ N ∧ T ≤ q₀ * R K D ∧
      Tracks A (induced Alg K D) (inducedAlg Alg (R K D) D) H q₀ ∧
      (∀ w < q₀, postDeg H q₀ w ≤ D) ∧
      Follows (B K D A) Alg (outSeq (R K D) D H Alg) T ∧
      K ≤ ((range T).image (outCol (R K D) D H Alg)).card ∧
      (∀ t < T, ((range t).image (outCol (R K D) D H Alg)).card < K) ∧
      ∀ t < T, t / R K D < q₀ ∧
        innerHist K D A (runHist Alg (outSeq (R K D) D H Alg) t) =
          A.hist (induced Alg K D) (t / R K D) ∧
        ∀ v < t / R K D,
          indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v =
            runCol (inducedAlg Alg (R K D) D) H v ∧
          D ≤ (clsList (R K D)
            (blockCol (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) (R K D) v)
            (indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v)).length := by
  obtain ⟨H, hH, q₀, hqN, hT, hdeg, hforce⟩ := exists_sim Alg hF hS hP
  obtain ⟨T, hTle, hfol, hTK, hlt, hmore⟩ := sim hD hAlg hH hT hdeg hforce
  exact ⟨H, hH, q₀, T, hqN, hTle, hT, hdeg, hfol, hTK, hlt, hmore⟩

/-- **Lemma 6.2 (forcing survives a blow-up).**  Suppose that `A` forces `K ≥ 2` colours, has size
at most `N`, and has post-degree at most `D ≥ 1`.  Then `B(𝒜)` forces `K` colours, has size at most
`R·N`, and has post-degree at most `R = (K-1)(D-1)+1`.  Moreover, for every proper `Alg` the
algorithm `Alg' = induced Alg K D` is proper, and at every moment `p` of the play of `B(𝒜)`
against `Alg` at which `Alg` has used at most `K - 1` colours, with `h` the outer history and
`m = |h| / R` the number of complete blocks: the inner play simulated by `B(𝒜)` is the play of `A`
against `Alg'` for `m` rounds, which has `m` vertices; and for every `v < m` the induced colour
`col(v)` is the colour that `Alg'` gives `v` against `A`, it occurs on at least `D` vertices of
the block of `v`, and it is a colour used by `Alg`. -/
theorem lemma_6_2 (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary} (hF : A.Forces K)
    (hS : A.SizeLE N) (hP : A.PostDegLE D) :
    (B K D A).Forces K ∧ (B K D A).SizeLE (R K D * N) ∧ (B K D A).PostDegLE (R K D) ∧
    ∀ Alg : OnlineAlg, Alg.IsProper → (induced Alg K D).IsProper ∧
      ∀ p, (usedColours ((B K D A).hist Alg p)).card ≤ K - 1 →
        innerHist K D A ((B K D A).hist Alg p) =
          A.hist (induced Alg K D) (((B K D A).hist Alg p).length / R K D) ∧
        (A.hist (induced Alg K D) (((B K D A).hist Alg p).length / R K D)).length =
          ((B K D A).hist Alg p).length / R K D ∧
        ∀ v < ((B K D A).hist Alg p).length / R K D,
          indColour K D ((B K D A).hist Alg p) v =
            colourAt (A.hist (induced Alg K D) (((B K D A).hist Alg p).length / R K D)) v ∧
          D ≤ ((range (R K D)).filter fun u =>
            colourAt ((B K D A).hist Alg p) (v * R K D + u) =
              indColour K D ((B K D A).hist Alg p) v).card ∧
          indColour K D ((B K D A).hist Alg p) v ∈ usedColours ((B K D A).hist Alg p) := by
  have hR : 0 < R K D := R_pos K D
  have main : ∀ Alg : OnlineAlg, Alg.IsProper →
      ∃ (H : ℕ → Finset ℕ) (_ : ValidSeq H) (q₀ T : ℕ), q₀ ≤ N ∧ T ≤ q₀ * R K D ∧
        Tracks A (induced Alg K D) (inducedAlg Alg (R K D) D) H q₀ ∧
        (∀ w < q₀, postDeg H q₀ w ≤ D) ∧
        Follows (B K D A) Alg (outSeq (R K D) D H Alg) T ∧
        K ≤ ((range T).image (outCol (R K D) D H Alg)).card ∧
        ∀ t < T, t / R K D < q₀ ∧
          innerHist K D A (runHist Alg (outSeq (R K D) D H Alg) t) =
            A.hist (induced Alg K D) (t / R K D) ∧
          ∀ v < t / R K D,
            indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v =
              runCol (inducedAlg Alg (R K D) D) H v ∧
            D ≤ (clsList (R K D)
              (blockCol (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) (R K D) v)
              (indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v)).length := by
    intro Alg hAlg
    obtain ⟨H, hH, q₀, T, hqN, hTle, hT, hdeg, hfol, hTK, -, hmore⟩ :=
      exists_play hD hF hS hP hAlg
    exact ⟨H, hH, q₀, T, hqN, hTle, hT, hdeg, hfol, hTK, hmore⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Alg hAlg
    obtain ⟨H, hH, q₀, T, -, -, -, -, hfol, hTK, -⟩ := main Alg hAlg
    refine ⟨T, ?_, ?_⟩
    · rw [hfol T, min_self]
      exact hfol.stop
    · rw [hfol T, min_self, usedColours_runHist]
      exact hTK
  · intro Alg hAlg p
    obtain ⟨H, hH, q₀, T, hqN, hTle, -, -, hfol, -, -⟩ := main Alg hAlg
    rw [hfol p, length_runHist]
    calc min p T ≤ T := min_le_right _ _
      _ ≤ q₀ * R K D := hTle
      _ ≤ N * R K D := Nat.mul_le_mul_right _ hqN
      _ = R K D * N := Nat.mul_comm _ _
  · intro Alg hAlg p i
    obtain ⟨H, hH, q₀, T, -, hTle, -, hdeg, hfol, -, -⟩ := main Alg hAlg
    rw [hfol p]
    refine (postDeg_runHist_le _ _ _ _).trans
      ((rank_mono _ _ ((min_le_right p T).trans hTle)).trans ?_)
    rw [outSeq_eq hH]
    exact postDeg_blowSeq_le hH hR (resPos_blockPerm hR _)
      (fun w hw => (hdeg w hw).trans (le_R hK)) i
  · intro Alg hAlg
    refine ⟨induced_isProper Alg K D, fun p hp => ?_⟩
    obtain ⟨H, hH, q₀, T, -, -, hT, -, hfol, hTK, hmore⟩ := main Alg hAlg
    rw [hfol p] at hp ⊢
    have ht : min p T < T := by
      by_contra hcon
      have hTe : min p T = T := le_antisymm (min_le_right _ _) (not_lt.1 hcon)
      rw [hTe, usedColours_runHist] at hp
      have hTK' : K ≤ ((range T).image (runCol Alg (outSeq (R K D) D H Alg))).card := hTK
      omega
    generalize min p T = t at hp ht
    obtain ⟨hm, hin, hc⟩ := hmore t ht
    rw [length_runHist]
    have hlen : (A.hist (induced Alg K D) (t / R K D)).length = t / R K D := by
      rw [hT.length, min_eq_left hm.le]
    refine ⟨hin, hlen, fun v hv => ?_⟩
    obtain ⟨hc1, hc2⟩ := hc v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [hc1, ← colourAt_clean, hT, min_eq_left hm.le, colourAt_runHist hv]
    · rw [length_clsList] at hc2
      exact hc2
    · obtain ⟨u, hu, hcu⟩ := popular_mem hD hc2
      have hvt : v * R K D + u < t := by
        have := (Nat.mul_le_mul_right (R K D) (Nat.succ_le_of_lt hv)).trans
          (Nat.div_mul_le_self t _)
        rw [Nat.succ_mul] at this
        omega
      have := colourAt_mem_usedColours (h := runHist Alg (outSeq (R K D) D H Alg) t)
        (i := v * R K D + u) (by rw [length_runHist]; exact hvt)
      have hcu' : colourAt (runHist Alg (outSeq (R K D) D H Alg) t) (v * R K D + u) =
          indColour K D (runHist Alg (outSeq (R K D) D H Alg) t) v := hcu
      rw [← hcu']
      exact this

/-- **The servers have the induced colour** (the last sentence of Lemma 6.3, for one blow-up).
Under the hypotheses of Lemma 6.2, consider a moment `p` of the play of `B(𝒜)` against a proper
algorithm `Alg` at which `Alg` has used at most `K - 1` colours, with `h` the outer history and
`m = |h| / R` the number of complete blocks, and suppose that the inner adversary `A`, in its play
against `Alg'`, presents the inner vertex `m` with the set `s'` of earlier neighbours.  Then the
earlier neighbours of the outer vertex that `B(𝒜)` presents next are the servers `srv w` of the
arcs `w → m`, one for every earlier neighbour `w` of `m`; the server `srv w` lies in the block of
`w` and has the induced colour `col(w)`.  (Every arc of the inner graph into `m` is covered, and
every vertex of the play is presented at such a moment, so this is the statement for all arcs.) -/
theorem server_colour (hK : 2 ≤ K) (hD : 1 ≤ D) {A : Adversary} (hF : A.Forces K)
    (hS : A.SizeLE N) (hP : A.PostDegLE D) {Alg : OnlineAlg} (hAlg : Alg.IsProper) {p : ℕ}
    (hp : (usedColours ((B K D A).hist Alg p)).card ≤ K - 1) {s' : Finset ℕ}
    (hs' : A.move (A.hist (induced Alg K D) (((B K D A).hist Alg p).length / R K D)) =
      some s') :
    ∃ srv : ℕ → ℕ,
      (B K D A).move ((B K D A).hist Alg p) =
        some ((s' ∩ range (((B K D A).hist Alg p).length / R K D)).image srv) ∧
      ∀ w ∈ s', w < ((B K D A).hist Alg p).length / R K D →
        srv w / R K D = w ∧
          colourAt ((B K D A).hist Alg p) (srv w) = indColour K D ((B K D A).hist Alg p) w := by
  have hR : 0 < R K D := R_pos K D
  obtain ⟨H, hH, q₀, T, -, -, hT, hdeg, hfol, hTK, hlt, hmore⟩ := exists_play hD hF hS hP hAlg
  rw [hfol p] at hp hs' ⊢
  have ht : min p T < T := by
    by_contra hcon
    have hTe : min p T = T := le_antisymm (min_le_right _ _) (not_lt.1 hcon)
    rw [hTe, usedColours_runHist] at hp
    have hTK' : K ≤ ((range T).image (runCol Alg (outSeq (R K D) D H Alg))).card := hTK
    omega
  generalize min p T = t at hp hs' ht ⊢
  obtain ⟨hm, -, hc⟩ := hmore t ht
  rw [length_runHist] at hs' ⊢
  obtain ⟨s, hs, hsH, -⟩ := hT.move_lt hm
  obtain rfl : s = s' := Option.some.inj (hs.symm.trans hs')
  refine ⟨fun w => w * R K D + resPos (R K D) D
      (colourAt (runHist Alg (outSeq (R K D) D H Alg) t)) w (rank H w (t / R K D)), ?_, ?_⟩
  · rw [hT.move_B (by rw [length_runHist]; exact hm)
      (by rw [usedColours_runHist]; exact hlt t ht)
      (by rw [length_runHist]; exact fun i hi => (hc i hi).1), hsH]
    unfold resAdv blowSeq
    rw [length_runHist]
  · intro w hw hwm
    have hwH : w ∈ H (t / R K D) := by
      rw [← hsH]
      exact mem_inter.2 ⟨hw, mem_range.2 hwm⟩
    refine ⟨div_add_lt hR ((resPos_blockPerm hR _).lt _ _), ?_⟩
    exact blockCol_resOrder (hc w hwm).2
      ((rank_lt_rank hm hwH).trans_le (hdeg w (hwm.trans hm)))

end Lemma

end OnlineColouring.Blow
