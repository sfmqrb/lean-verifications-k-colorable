module

public import OnlineColouring.BlowStack

/-!
# Construction 9.1 and Lemma 9.2: the pairing top as an adversary

Construction 9.1 (`con:pairing`) and Lemma 9.2 (`lem:pairing`) of Section 9, an adversary of
Kawarabayashi, Yoneda and Yoneda.

`Blow.pairing ℓ : Adversary` is the pairing top with `2ℓ` base colours `0, …, 2ℓ-1`, grouped
into the pairs `{2s, 2s+1}`, `s < ℓ` (the paper numbers them from `1`).

* The `i`-th vertex (`i = 0, …, 2^ℓ - 1`) gets the vector `X_i ∈ {0,1}^ℓ` of the binary digits of
  `i` (`bitN i s`); it *chooses* the base colour `2s + X_i(s)` from the pair `s` (`Chosen i b`).
* The pairing state is a function of the history (`Blow.phi ℓ h : ℕ → Option ℕ`; `none` means
  unpaired, `some b` means paired with base colour `φ = b`), computed vertex by vertex
  (`pairStep`): if the algorithm gave the new vertex `v` the colour of an earlier unpaired vertex
  `u` (the earliest such `u`; in plays against proper algorithms there is at most one), then `u`
  and `v` become paired, with the least `s` such that `X_u(s) ≠ X_v(s)` (`diffBit`; this is the
  tie-breaking rule), `φ(u) = 2s + X_u(s)` and `φ(v) = 2s + X_v(s)`.
* The new vertex `v` is joined to every earlier paired vertex whose base colour is not chosen by
  `X_v`, and to no unpaired vertex (`pairNbrs`).  The adversary stops after `2^ℓ` vertices.

`Blow.lemma_9_2` (for `ℓ ≥ 1`): the pairing top presents `2^ℓ` vertices (every play stops exactly
when `2^ℓ` vertices have been presented), forces `2^(ℓ-1)` colours, and every graph it presents is
`2ℓ`-colourable.  The proof is the paper's: the invariant `PInv` records that unpaired vertices
have distinct colours, that the two vertices of a pair have the two base colours of one pair and
that no third vertex has their colour, and that every earlier neighbour of `w` is paired with a
base colour not chosen by `X_w`.
-/

@[expose] public section

namespace OnlineColouring.Blow

open Finset

/-! ### Vectors and base colours -/

/-- `X_i(s)`: the `s`-th binary digit of `i`. -/
def bitN (i s : ℕ) : ℕ := (i.testBit s).toNat

theorem bitN_le_one (i s : ℕ) : bitN i s ≤ 1 := Bool.toNat_le _

/-- The base colour `b` is chosen by the vector `X_v`: `b = 2s + X_v(s)` for its pair `s = b/2`. -/
def Chosen (v b : ℕ) : Prop := b = 2 * (b / 2) + bitN v (b / 2)

theorem chosen_mk (v s : ℕ) : (2 * s + bitN v s) / 2 = s ∧ Chosen v (2 * s + bitN v s) := by
  have h := bitN_le_one v s
  have h1 : (2 * s + bitN v s) / 2 = s := by omega
  exact ⟨h1, by unfold Chosen; rw [h1]⟩

/-- The least `s < ℓ` with `X_u(s) ≠ X_v(s)` (`0` if there is none). -/
def diffBit (ℓ u v : ℕ) : ℕ :=
  ((List.range ℓ).find? fun s => u.testBit s != v.testBit s).getD 0

theorem diffBit_spec {ℓ u v : ℕ} (hu : u < 2 ^ ℓ) (hv : v < 2 ^ ℓ) (huv : u ≠ v) :
    diffBit ℓ u v < ℓ ∧ bitN u (diffBit ℓ u v) ≠ bitN v (diffBit ℓ u v) := by
  obtain ⟨s, hs⟩ : ∃ s, u.testBit s ≠ v.testBit s := by
    by_contra hcon
    push Not at hcon
    exact huv (Nat.eq_of_testBit_eq hcon)
  have hsℓ : s < ℓ := by
    by_contra hcon
    have h2 : 2 ^ ℓ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h2)] at hs
    exact hs rfl
  unfold diffBit
  cases hf : (List.range ℓ).find? fun s => u.testBit s != v.testBit s with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (bne_iff_ne.2 hs) (hf s (List.mem_range.2 hsℓ))
  | some s' =>
    have h1 := List.find?_some hf
    have h2 := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    refine ⟨h2, ?_⟩
    simp only [Option.getD_some, bitN]
    intro hcon
    have he : u.testBit s' = v.testBit s' := by
      revert hcon
      cases u.testBit s' <;> cases v.testBit s' <;> simp
    exact bne_iff_ne.1 h1 he

/-! ### The pairing state -/

/-- One step of the pairing: the new vertex `v = |h|` received the colour `c`. -/
def pairStep (ℓ : ℕ) (φ : ℕ → Option ℕ) (h : History) (c : ℕ) : ℕ → Option ℕ :=
  match (List.range h.length).find? fun u => decide (φ u = none ∧ colourAt h u = c) with
  | none => φ
  | some u =>
    Function.update
      (Function.update φ u (some (2 * diffBit ℓ u h.length + bitN u (diffBit ℓ u h.length))))
      h.length (some (2 * diffBit ℓ u h.length + bitN h.length (diffBit ℓ u h.length)))

/-- The pairing state of a reversed history. -/
def phiRev (ℓ : ℕ) : History → ℕ → Option ℕ
  | [] => fun _ => none
  | x :: t => pairStep ℓ (phiRev ℓ t) t.reverse x.2

/-- The pairing state `φ` after the history `h`: `none` for unpaired vertices, `some b` for a
paired vertex with base colour `b`. -/
def phi (ℓ : ℕ) (h : History) : ℕ → Option ℕ := phiRev ℓ h.reverse

theorem phi_nil (ℓ : ℕ) : phi ℓ [] = fun _ => none := rfl

theorem phi_append (ℓ : ℕ) (h : History) (x : Finset ℕ × ℕ) :
    phi ℓ (h ++ [x]) = pairStep ℓ (phi ℓ h) h x.2 := by
  unfold phi
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, phiRev,
    List.reverse_reverse]

open Classical in
/-- The earlier neighbours of the next vertex `v = |h|`: the paired vertices whose base colour is
not chosen by `X_v`. -/
noncomputable def pairNbrs (ℓ : ℕ) (h : History) : Finset ℕ :=
  (range h.length).filter fun u => ∃ b, phi ℓ h u = some b ∧ ¬ Chosen h.length b

/-- **Construction 9.1: the pairing top.** -/
noncomputable def pairing (ℓ : ℕ) : Adversary :=
  ⟨fun h => if h.length < 2 ^ ℓ then some (pairNbrs ℓ h) else none⟩

theorem mem_pairNbrs {ℓ : ℕ} {h : History} {u : ℕ} :
    u ∈ pairNbrs ℓ h ↔ u < h.length ∧ ∃ b, phi ℓ h u = some b ∧ ¬ Chosen h.length b := by
  classical
  simp [pairNbrs]

/-! ### The invariant -/

/-- The invariant of the pairing top. -/
structure PInv (ℓ : ℕ) (h : History) : Prop where
  /-- Vertices not yet presented are unpaired. -/
  none_ge : ∀ u, h.length ≤ u → phi ℓ h u = none
  /-- At most one unpaired vertex has a given colour. -/
  unp : ∀ u u', u < h.length → u' < h.length → phi ℓ h u = none → phi ℓ h u' = none →
    colourAt h u = colourAt h u' → u = u'
  /-- A paired vertex `u` has a base colour chosen by `X_u`, and a partner `u'` of the same
  colour with the other base colour of the same pair; no third vertex has their colour. -/
  paired : ∀ u b, u < h.length → phi ℓ h u = some b →
    b / 2 < ℓ ∧ Chosen u b ∧ ∃ u' < h.length, u' ≠ u ∧ colourAt h u' = colourAt h u ∧
      (∃ b', phi ℓ h u' = some b' ∧ b' / 2 = b / 2 ∧ b' ≠ b) ∧
      ∀ w < h.length, colourAt h w = colourAt h u → w = u ∨ w = u'
  /-- Every earlier neighbour of `w` is paired, with a base colour not chosen by `X_w`. -/
  nbr : ∀ w < h.length, ∀ u ∈ (h.getD w (∅, 0)).1,
    u < w ∧ ∃ b, phi ℓ h u = some b ∧ ¬ Chosen w b

theorem pinv_nil (ℓ : ℕ) : PInv ℓ [] where
  none_ge _ _ := rfl
  unp u _ hu := absurd hu (by simp)
  paired u _ hu := absurd hu (by simp)
  nbr w hw := absurd hw (by simp)

theorem colourAt_append_lt {h : History} {x : Finset ℕ × ℕ} {u : ℕ} (hu : u < h.length) :
    colourAt (h ++ [x]) u = colourAt h u := by
  simp [colourAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

theorem colourAt_append_self (h : History) (x : Finset ℕ × ℕ) :
    colourAt (h ++ [x]) h.length = x.2 := by
  simp [colourAt, List.getD_eq_getElem?_getD]

theorem getD_append_lt {h : History} {x : Finset ℕ × ℕ} {u : ℕ} (hu : u < h.length) :
    (h ++ [x]).getD u (∅, 0) = h.getD u (∅, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

theorem getD_append_self (h : History) (x : Finset ℕ × ℕ) :
    (h ++ [x]).getD h.length (∅, 0) = x := by
  simp [List.getD_eq_getElem?_getD]

/-- **The invariant is preserved** when the pairing top presents a vertex and the algorithm
colours it properly. -/
theorem PInv.step {ℓ : ℕ} {h : History} (inv : PInv ℓ h) (hn : h.length < 2 ^ ℓ) {c : ℕ}
    (hc : ∀ u ∈ pairNbrs ℓ h, colourAt h u ≠ c) : PInv ℓ (h ++ [(pairNbrs ℓ h, c)]) := by
  have hlen : (h ++ [(pairNbrs ℓ h, c)]).length = h.length + 1 := by simp
  have hphi := phi_append ℓ h (pairNbrs ℓ h, c)
  -- no paired vertex has the colour `c`
  have F : ∀ u < h.length, ∀ b, phi ℓ h u = some b → colourAt h u ≠ c := by
    intro u hu b hb
    obtain ⟨-, -, u', hu', -, hcu, ⟨b', hb', hb2, hbb⟩, -⟩ := inv.paired u b hu hb
    by_cases hch : Chosen h.length b
    · have hnch : ¬ Chosen h.length b' := by
        intro hch'
        unfold Chosen at hch hch'
        rw [hb2] at hch'
        exact hbb (hch'.trans hch.symm)
      rw [← hcu]
      exact hc u' (mem_pairNbrs.2 ⟨hu', b', hb', hnch⟩)
    · exact hc u (mem_pairNbrs.2 ⟨hu, b, hb, hch⟩)
  have hnbr : ∀ w < h.length + 1, ∀ u ∈ ((h ++ [(pairNbrs ℓ h, c)]).getD w (∅, 0)).1,
      u < w ∧ ∃ b, phi ℓ h u = some b ∧ ¬ Chosen w b := by
    intro w hw u hu
    rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw' | rfl
    · rw [getD_append_lt hw'] at hu
      exact inv.nbr w hw' u hu
    · rw [getD_append_self] at hu
      exact mem_pairNbrs.1 hu
  cases hfind : (List.range h.length).find? fun u =>
      decide (phi ℓ h u = none ∧ colourAt h u = c) with
  | none =>
    have hphi' : phi ℓ (h ++ [(pairNbrs ℓ h, c)]) = phi ℓ h := by
      rw [hphi]
      simp only [pairStep, hfind]
    have hnone : ∀ u < h.length, phi ℓ h u = none → colourAt h u ≠ c := by
      intro u hu hpu hcu
      rw [List.find?_eq_none] at hfind
      have := hfind u (List.mem_range.2 hu)
      simp [hpu, hcu] at this
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [hlen] at hu
      rw [hphi']
      exact inv.none_ge u (by omega)
    · intro u u' hu hu' hpu hpu' hcc
      rw [hlen] at hu hu'
      rw [hphi'] at hpu hpu'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with hu' | rfl
      · rw [colourAt_append_lt hu, colourAt_append_lt hu'] at hcc
        exact inv.unp u u' hu hu' hpu hpu' hcc
      · rw [colourAt_append_lt hu, colourAt_append_self] at hcc
        exact absurd hcc (hnone u hu hpu)
      · rw [colourAt_append_lt hu', colourAt_append_self] at hcc
        exact absurd hcc.symm (hnone u' hu' hpu')
      · rfl
    · intro u b hu hpu
      rw [hlen] at hu
      rw [hphi'] at hpu
      have hun : u < h.length := by
        by_contra hcon
        rw [inv.none_ge u (not_lt.1 hcon)] at hpu
        cases hpu
      obtain ⟨h1, h2, u', hu', hne, hcu, hb', hall⟩ := inv.paired u b hun hpu
      refine ⟨h1, h2, u', by omega, hne, ?_, ?_, ?_⟩
      · rw [colourAt_append_lt hu', colourAt_append_lt hun]
        exact hcu
      · rw [hphi']
        exact hb'
      · intro w hw hcw
        rw [hlen] at hw
        rw [colourAt_append_lt hun] at hcw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
        · rw [colourAt_append_lt hw] at hcw
          exact hall w hw hcw
        · rw [colourAt_append_self] at hcw
          exact absurd hcw.symm (F u hun b hpu)
    · intro w hw u hu
      rw [hlen] at hw
      rw [hphi']
      exact hnbr w hw u hu
  | some u₀ =>
    have h0 := List.find?_some hfind
    simp only [decide_eq_true_eq] at h0
    obtain ⟨hp0, hc0⟩ := h0
    have hu0 : u₀ < h.length := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    obtain ⟨hs, hbit⟩ := diffBit_spec (hu0.trans hn) hn (ne_of_lt hu0)
    have hphi' : phi ℓ (h ++ [(pairNbrs ℓ h, c)]) =
        Function.update (Function.update (phi ℓ h) u₀
          (some (2 * diffBit ℓ u₀ h.length + bitN u₀ (diffBit ℓ u₀ h.length))))
          h.length (some (2 * diffBit ℓ u₀ h.length + bitN h.length (diffBit ℓ u₀ h.length))) := by
      rw [hphi]
      simp only [pairStep, hfind]
    generalize diffBit ℓ u₀ h.length = s at hs hbit hphi'
    obtain ⟨hb0, hch0⟩ := chosen_mk u₀ s
    obtain ⟨hbn, hchn⟩ := chosen_mk h.length s
    have hne : 2 * s + bitN u₀ s ≠ 2 * s + bitN h.length s := by omega
    generalize 2 * s + bitN u₀ s = b₀ at hb0 hch0 hne hphi'
    generalize 2 * s + bitN h.length s = bₙ at hbn hchn hne hphi'
    have hphin : phi ℓ (h ++ [(pairNbrs ℓ h, c)]) h.length = some bₙ := by
      rw [hphi', Function.update_self]
    have hphi0 : phi ℓ (h ++ [(pairNbrs ℓ h, c)]) u₀ = some b₀ := by
      rw [hphi', Function.update_of_ne (ne_of_lt hu0), Function.update_self]
    have hphio : ∀ w, w ≠ h.length → w ≠ u₀ →
        phi ℓ (h ++ [(pairNbrs ℓ h, c)]) w = phi ℓ h w := by
      intro w h1 h2
      rw [hphi', Function.update_of_ne h1, Function.update_of_ne h2]
    have hpers : ∀ w b, phi ℓ h w = some b → phi ℓ (h ++ [(pairNbrs ℓ h, c)]) w = some b := by
      intro w b hw
      rw [hphio w ?_ ?_, hw]
      · rintro rfl
        rw [inv.none_ge _ le_rfl] at hw
        cases hw
      · rintro rfl
        rw [hp0] at hw
        cases hw
    have hunp : ∀ w < h.length + 1, phi ℓ (h ++ [(pairNbrs ℓ h, c)]) w = none →
        w < h.length ∧ phi ℓ h w = none := by
      intro w hw hpw
      have h1 : w ≠ h.length := by
        rintro rfl
        rw [hphin] at hpw
        cases hpw
      have h2 : w ≠ u₀ := by
        rintro rfl
        rw [hphi0] at hpw
        cases hpw
      rw [hphio w h1 h2] at hpw
      exact ⟨by omega, hpw⟩
    -- a vertex before the new one with colour `c` is `u₀`
    have hcl : ∀ w < h.length, colourAt h w = c → w = u₀ := by
      intro w hw hcw
      cases hpw : phi ℓ h w with
      | none => exact inv.unp w u₀ hw hu0 hpw hp0 (hcw.trans hc0.symm)
      | some bw => exact absurd hcw (F w hw bw hpw)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [hlen] at hu
      rw [hphio u (by omega) (by omega)]
      exact inv.none_ge u (by omega)
    · intro u u' hu hu' hpu hpu' hcc
      rw [hlen] at hu hu'
      obtain ⟨hu1, hu2⟩ := hunp u hu hpu
      obtain ⟨hu1', hu2'⟩ := hunp u' hu' hpu'
      rw [colourAt_append_lt hu1, colourAt_append_lt hu1'] at hcc
      exact inv.unp u u' hu1 hu1' hu2 hu2' hcc
    · intro u b hu hpu
      rw [hlen] at hu
      by_cases hun : u = h.length
      · subst hun
        rw [hphin] at hpu
        cases hpu
        refine ⟨by rw [hbn]; exact hs, hchn, u₀, by omega, ne_of_lt hu0, ?_,
          ⟨b₀, hphi0, by rw [hb0, hbn], hne⟩, ?_⟩
        · rw [colourAt_append_lt hu0, colourAt_append_self]
          exact hc0
        · intro w hw hcw
          rw [hlen] at hw
          rw [colourAt_append_self] at hcw
          rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
          · rw [colourAt_append_lt hw] at hcw
            exact Or.inr (hcl w hw hcw)
          · exact Or.inl rfl
      by_cases hu0' : u = u₀
      · subst hu0'
        rw [hphi0] at hpu
        cases hpu
        refine ⟨by rw [hb0]; exact hs, hch0, h.length, by omega, Ne.symm hun, ?_,
          ⟨bₙ, hphin, by rw [hb0, hbn], hne.symm⟩, ?_⟩
        · rw [colourAt_append_lt hu0, colourAt_append_self]
          exact hc0.symm
        · intro w hw hcw
          rw [hlen] at hw
          rw [colourAt_append_lt hu0, hc0] at hcw
          rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
          · rw [colourAt_append_lt hw] at hcw
            exact Or.inl (hcl w hw hcw)
          · exact Or.inr rfl
      · have hul : u < h.length := by omega
        rw [hphio u hun hu0'] at hpu
        obtain ⟨h1, h2, u', hu', hne', hcu, ⟨b', hb', hb2⟩, hall⟩ := inv.paired u b hul hpu
        refine ⟨h1, h2, u', by omega, hne', ?_, ⟨b', hpers u' b' hb', hb2⟩, ?_⟩
        · rw [colourAt_append_lt hu', colourAt_append_lt hul]
          exact hcu
        · intro w hw hcw
          rw [hlen] at hw
          rw [colourAt_append_lt hul] at hcw
          rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
          · rw [colourAt_append_lt hw] at hcw
            exact hall w hw hcw
          · rw [colourAt_append_self] at hcw
            exact absurd hcw.symm (F u hul b hpu)
    · intro w hw u hu
      rw [hlen] at hw
      obtain ⟨h1, b, hb, hb'⟩ := hnbr w hw u hu
      exact ⟨h1, b, hpers u b hb, hb'⟩

/-! ### The play -/

theorem pairing_move (ℓ : ℕ) (h : History) :
    (pairing ℓ).move h = if h.length < 2 ^ ℓ then some (pairNbrs ℓ h) else none := rfl

/-- Against a proper algorithm, the invariant holds throughout the play, and after `p` rounds
`min p 2^ℓ` vertices have been presented. -/
theorem pairing_hist (ℓ : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper) :
    ∀ p, PInv ℓ ((pairing ℓ).hist Alg p) ∧ ((pairing ℓ).hist Alg p).length = min p (2 ^ ℓ) := by
  intro p
  induction p with
  | zero =>
    rw [Adversary.hist]
    exact ⟨pinv_nil ℓ, by simp⟩
  | succ p ih =>
    obtain ⟨inv, hlen⟩ := ih
    by_cases hn : ((pairing ℓ).hist Alg p).length < 2 ^ ℓ
    · have hm : (pairing ℓ).move ((pairing ℓ).hist Alg p) =
          some (pairNbrs ℓ ((pairing ℓ).hist Alg p)) := by
        rw [pairing_move]
        simp only [hn, ↓reduceIte]
      rw [hist_succ_some hm]
      refine ⟨inv.step hn ?_, ?_⟩
      · intro u hu
        have hul := (mem_pairNbrs.1 hu).1
        rw [colourAt_eq_getElem hul]
        exact (hAlg _ _ u hul hu).symm
      · rw [List.length_append, List.length_singleton, hlen]
        omega
    · have hm : (pairing ℓ).move ((pairing ℓ).hist Alg p) = none := by
        rw [pairing_move]
        simp only [hn, ↓reduceIte]
      rw [hist_succ_none hm]
      exact ⟨inv, by omega⟩

/-! ### Consequences of the invariant -/

theorem usedColours_eq_image (h : History) :
    usedColours h = (range h.length).image (colourAt h) := by
  ext c
  rw [mem_usedColours_iff]
  simp only [mem_image, mem_range]

/-- Every colour is used at most twice, so `n` vertices carry at least `n / 2` colours. -/
theorem PInv.length_le {ℓ : ℕ} {h : History} (inv : PInv ℓ h) :
    h.length ≤ 2 * (usedColours h).card := by
  rw [usedColours_eq_image]
  have := card_le_mul_card_image (f := colourAt h) (range h.length) 2 ?_
  · rwa [card_range] at this
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.1 ha
  rw [mem_range] at hu
  cases hpu : phi ℓ h u with
  | some b =>
    obtain ⟨-, -, u', -, -, -, -, hall⟩ := inv.paired u b hu hpu
    refine (card_le_card (t := {u, u'}) ?_).trans card_le_two
    intro w hw
    rw [mem_filter, mem_range] at hw
    rw [mem_insert, mem_singleton]
    exact hall w hw.1 hw.2
  | none =>
    refine (card_le_card (t := {u}) ?_).trans ((card_singleton u).le.trans one_le_two)
    intro w hw
    rw [mem_filter, mem_range] at hw
    rw [mem_singleton]
    cases hpw : phi ℓ h w with
    | none => exact inv.unp w u hw.1 hu hpw hpu hw.2
    | some bw =>
      obtain ⟨-, -, w', -, -, -, ⟨b', hb', -⟩, hall⟩ := inv.paired w bw hw.1 hpw
      rcases hall u hu hw.2.symm with h1 | h1
      · exact h1.symm
      · rw [h1, hb'] at hpu
        cases hpu

/-- The base colours form a proper `2ℓ`-colouring (unpaired vertices get the base colour that
their vector chooses from the first pair). -/
theorem PInv.colorable {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {h : History} (inv : PInv ℓ h) :
    h.graph.Colorable (2 * ℓ) := by
  have hβ : ∀ v, v < h.length → (phi ℓ h v).getD (bitN v 0) < 2 * ℓ ∧
      Chosen v ((phi ℓ h v).getD (bitN v 0)) := by
    intro v hv
    cases hpv : phi ℓ h v with
    | none =>
      have := bitN_le_one v 0
      have h2 := (chosen_mk v 0).2
      rw [Nat.mul_zero, Nat.zero_add] at h2
      exact ⟨by rw [Option.getD_none]; omega, h2⟩
    | some b =>
      obtain ⟨h1, h2, -⟩ := inv.paired v b hv hpv
      exact ⟨by rw [Option.getD_some]; omega, h2⟩
  have key : ∀ u v : Fin h.length, (u : ℕ) < v → (u : ℕ) ∈ (h.get v).1 →
      (phi ℓ h u).getD (bitN u 0) ≠ (phi ℓ h v).getD (bitN v 0) := by
    intro u v _ huv heq
    have hmem : (u : ℕ) ∈ (h.getD v (∅, 0)).1 := by
      rw [List.getD_of_lt _ v.2]
      exact huv
    obtain ⟨-, b, hb, hnch⟩ := inv.nbr v v.2 u hmem
    rw [hb, Option.getD_some] at heq
    rw [heq] at hnch
    exact hnch (hβ v v.2).2
  refine ⟨SimpleGraph.Coloring.mk
    (fun v : Fin h.length => (⟨(phi ℓ h v).getD (bitN v 0), (hβ v v.2).1⟩ : Fin (2 * ℓ))) ?_⟩
  intro u v hadj heq
  rw [Fin.mk.injEq] at heq
  rcases History.graph_adj.1 hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key u v h1 h2 heq
  · exact key v u h1 h2 heq.symm

/-- **Lemma 9.2 (the pairing top).**  For `ℓ ≥ 1`, the pairing top presents `2^ℓ` vertices (a play
has stopped exactly when `2^ℓ` vertices have been presented, and never has more), forces
`2^(ℓ-1)` colours, and every graph it presents is `2ℓ`-colourable. -/
theorem lemma_9_2 {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∀ Alg : OnlineAlg, Alg.IsProper → ∀ p,
      (pairing ℓ).StopsAt Alg p ↔ ((pairing ℓ).hist Alg p).length = 2 ^ ℓ) ∧
    (pairing ℓ).SizeLE (2 ^ ℓ) ∧
    (pairing ℓ).Forces (2 ^ (ℓ - 1)) ∧
    ∀ Alg : OnlineAlg, Alg.IsProper → ∀ p, ((pairing ℓ).hist Alg p).graph.Colorable (2 * ℓ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Alg hAlg p
    have hlen := (pairing_hist ℓ hAlg p).2
    unfold Adversary.StopsAt
    rw [pairing_move]
    constructor
    · intro h
      by_contra hne
      have hlt : ((pairing ℓ).hist Alg p).length < 2 ^ ℓ := by omega
      simp [hlt] at h
    · intro h
      simp [h]
  · intro Alg hAlg p
    rw [(pairing_hist ℓ hAlg p).2]
    exact min_le_right _ _
  · intro Alg hAlg
    obtain ⟨inv, hlen⟩ := pairing_hist ℓ hAlg (2 ^ ℓ)
    rw [min_self] at hlen
    refine ⟨2 ^ ℓ, ?_, ?_⟩
    · rw [pairing_move]
      simp [hlen]
    · have h1 := inv.length_le
      rw [hlen] at h1
      have h2 : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  · intro Alg hAlg p
    exact (pairing_hist ℓ hAlg p).1.colorable hℓ

end OnlineColouring.Blow
