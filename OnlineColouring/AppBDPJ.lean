module

public import OnlineColouring.AppBDTopBlock
public import OnlineColouring.AppBDLST
public import OnlineColouring.AppBDPJArith
public import Mathlib.Data.Finset.Sort

/-!
# Theorem D.5 (partial joins)

Appendix D.4, paragraph "One partial-join level": *In a partial-join level the vertices of the
block of `v_t` may have different earlier neighbourhoods, all inside the reserves (monochromatic
subsets) of earlier blocks, with at least one neighbour in each; forcing is then automatic once
every play reaches the last block … If a partial-join level over `K_m` forces `m` colours, is
`3`-colourable in every play against every algorithm and has at most `N` vertices, then
`N ≥ m³ / (3 (2 log₂ N + 1)) - m²` …*

The model.  `IsPJAdv β ρ m adv`: in every play of `adv` against a proper algorithm the history has
the form `PJForm`, where `β g` is the block (`0, …, m-1`) of the vertex presented at the history
`g` and `ρ g` is the set of reserve vertices selected so far.  "Forcing is then automatic once
every play reaches the last block" is `pj_forces`, and the hypothesis "forces `m` colours" of the
theorem is `adv.Forces m`.  The hypotheses of the theorem can be met for `2 ≤ m ≤ 7`: see
`partial_joins_witness` (`AppBDWitness.lean`).

`partial_joins` is the inequality of the theorem.  The proof is the paper's:

* `rriAlg β ρ m i N` is `RR_i` (round robin up to block `i`, then the hub strategy), and `RR` is
  `RR_m`.  The palettes are the colours of `[m-1]` that the earlier neighbours do not show.
* `rr_bound`: `|B_i| ≥ (m-1-i)(|R_i|-1)+1` in the play against `RR`.
* `hub_colour_lt`, `hub_card_usedColours_le`: if `|R_i| (2 ⌊log₂ N⌋ + 1) ≤ m-2-i`, then `RR_i`
  uses only colours of `[m-1]`.  The colours inside a group are those of the algorithm of Lovász,
  Saks and Trotter (`lstL`, `isLSTColouring_grp`); a group is bipartite because it avoids the
  colour of its hub in a `3`-colouring (`exists_coloring_grp`); the bound `2 ⌊log₂ N⌋ + 1` on
  their number is `lst_colour_le` (`AppBDLST.lean`).
* `plays_agree`: the plays against `RR` and `RR_i` coincide until the first vertex after block
  `i`, so they have the same reserve `R_i`.
* `pj_arith` (`AppBDPJArith.lean`): the summation.

The asymptotic statements of the theorem are in `AppBDPJAsymp.lean`.
-/

@[expose] public section

namespace OnlineColouring.AppBD

open Finset

/-! ### Prefixes of a history -/

section Take

variable {β : History → ℕ} {H : History} {u w : ℕ}

theorem bidx_take (hw : w ≤ u) : bidx β (H.take u) w = bidx β H w := by
  unfold bidx
  rw [List.take_take, min_eq_left hw]

theorem nb_take (hw : w < u) : nb (H.take u) w = nb H w := by
  simp [nb, List.getD_eq_getElem?_getD, hw]

theorem colourAt_take (hw : w < u) : colourAt (H.take u) w = colourAt H w := by
  simp [colourAt, List.getD_eq_getElem?_getD, hw]

theorem length_take_of_le (hu : u ≤ H.length) : (H.take u).length = u := by
  rw [List.length_take]
  exact min_eq_left hu

theorem colourAt_eq_step {A : OnlineAlg} (hr : IsRunOf A H) (hu : u < H.length) :
    colourAt H u = A.step (H.take u) (nb H u) := by
  rw [colourAt_eq_getElem hu, nb_eq_getElem hu]
  exact hr u hu

theorem nbrColours_take {s : Finset ℕ} (hu : u ≤ H.length) (hs : ∀ x ∈ s, x < u) :
    nbrColours (H.take u) s = s.image (colourAt H) := by
  ext q
  rw [mem_nbrColours, mem_image, length_take_of_le hu]
  constructor
  · rintro ⟨x, hx, hxu, rfl⟩
    exact ⟨x, hx, (colourAt_take hxu).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hs x hx, colourAt_take (hs x hx)⟩

end Take

/-! ### Partial-join levels -/

/-- The history `h` is a play of a partial-join level over `K_m`.  `β` names the block
(`0, …, m-1`) of the next vertex and `ρ g` is the set of reserve vertices that the adversary has
selected when the history is `g`.  The blocks arrive one after the other (`mono`); the earlier
neighbours of a vertex lie in earlier blocks (`nbr`), with at least one in each (`cover`), and
inside the reserves (`res`); the reserve of a block does not change once a later block has
started (`stab`), and it is monochromatic (`resMono`). -/
structure PJForm (β : History → ℕ) (ρ : History → Finset ℕ) (m : ℕ) (h : History) : Prop where
  lt : ∀ j < h.length, bidx β h j < m
  mono : ∀ j j', j ≤ j' → j' < h.length → bidx β h j ≤ bidx β h j'
  nbr : ∀ j < h.length, ∀ u ∈ nb h j, u < j ∧ bidx β h u < bidx β h j
  cover : ∀ j < h.length, ∀ t < bidx β h j, ∃ u ∈ nb h j, bidx β h u = t
  res : ∀ j < h.length, ∀ u ∈ nb h j, u ∈ ρ (h.take j)
  stab : ∀ j j', j ≤ j' → j' < h.length → ∀ u < j, bidx β h u < bidx β h j →
    (u ∈ ρ (h.take j) ↔ u ∈ ρ (h.take j'))
  resMono : ∀ j < h.length, ∀ u < j, ∀ w < j, u ∈ ρ (h.take j) → w ∈ ρ (h.take j) →
    bidx β h u = bidx β h w → bidx β h u < bidx β h j → colourAt h u = colourAt h w

/-- A partial-join level over `K_m`: every play against a proper algorithm has the form
`PJForm`. -/
def IsPJAdv (β : History → ℕ) (ρ : History → Finset ℕ) (m : ℕ) (adv : Adversary) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, PJForm β ρ m (adv.hist A p)

section FormFacts

variable {β : History → ℕ} {ρ : History → Finset ℕ} {m : ℕ} {H : History}

theorem PJForm.lt_of_bidx_lt (hf : PJForm β ρ m H) {u w : ℕ} (hw : w < H.length)
    (hb : bidx β H w < bidx β H u) : w < u := by
  by_contra h
  have := hf.mono u w (not_lt.1 h) hw
  omega

/-- If an earlier neighbour of `u` and an earlier neighbour of `u'` lie in the same block, they
have the same colour: both belong to the reserve of that block. -/
theorem PJForm.sameCol (hf : PJForm β ρ m H) {u u' w w' : ℕ} (hu : u < H.length)
    (hu' : u' < H.length) (hw : w ∈ nb H u) (hw' : w' ∈ nb H u')
    (hb : bidx β H w = bidx β H w') : colourAt H w = colourAt H w' := by
  obtain ⟨hwu, hwb⟩ := hf.nbr u hu w hw
  obtain ⟨hwu', hwb'⟩ := hf.nbr u' hu' w' hw'
  have r := hf.res u hu w hw
  have r' := hf.res u' hu' w' hw'
  rcases le_total u u' with h | h
  · have r2 := (hf.stab u u' h hu' w hwu hwb).1 r
    exact hf.resMono u' hu' w (hwu.trans_le h) w' hwu' r2 r' hb (hb ▸ hwb')
  · have r2' := (hf.stab u' u h hu w' hwu' hwb').1 r'
    exact hf.resMono u hu w hwu w' (hwu'.trans_le h) r r2' hb hwb

/-- Neighbours of a vertex that lie in the blocks before block `t` show at most `t` colours. -/
theorem PJForm.card_image_le (hf : PJForm β ρ m H) {u : ℕ} (hu : u < H.length) {S : Finset ℕ}
    (hS : S ⊆ nb H u) {t : ℕ} (hSt : ∀ w ∈ S, bidx β H w < t) :
    (S.image (colourAt H)).card ≤ t := by
  classical
  rw [← card_range t]
  refine card_le_card_of_injOn
    (fun c => if h : ∃ w ∈ S, colourAt H w = c then bidx β H h.choose else 0) ?_ ?_
  · intro c hc
    obtain ⟨w, hw, rfl⟩ := mem_image.1 (mem_coe.1 hc)
    have hex : ∃ w' ∈ S, colourAt H w' = colourAt H w := ⟨w, hw, rfl⟩
    simp only [hex, ↓reduceDIte, coe_range, Set.mem_Iio]
    exact hSt _ hex.choose_spec.1
  · intro c hc c' hc' heq
    obtain ⟨w, hw, rfl⟩ := mem_image.1 (mem_coe.1 hc)
    obtain ⟨w', hw', rfl⟩ := mem_image.1 (mem_coe.1 hc')
    have hex : ∃ x ∈ S, colourAt H x = colourAt H w := ⟨w, hw, rfl⟩
    have hex' : ∃ x ∈ S, colourAt H x = colourAt H w' := ⟨w', hw', rfl⟩
    simp only [hex, hex', ↓reduceDIte] at heq
    rw [← hex.choose_spec.2, ← hex'.choose_spec.2]
    exact hf.sameCol hu hu (hS hex.choose_spec.1) (hS hex'.choose_spec.1) heq

/-- The vertices of a block see the same colours. -/
theorem PJForm.image_eq (hf : PJForm β ρ m H) {u u' : ℕ} (hu : u < H.length)
    (hu' : u' < H.length) (hb : bidx β H u = bidx β H u') :
    (nb H u).image (colourAt H) = (nb H u').image (colourAt H) := by
  have key : ∀ a a', a < H.length → a' < H.length → bidx β H a = bidx β H a' →
      (nb H a).image (colourAt H) ⊆ (nb H a').image (colourAt H) := by
    intro a a' ha ha' hab c hc
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
    obtain ⟨w', hw', hwb⟩ := hf.cover a' ha' (bidx β H w) (hab ▸ (hf.nbr a ha w hw).2)
    exact mem_image.2 ⟨w', hw', hf.sameCol ha' ha hw' hw hwb⟩
  exact (key u u' hu hu' hb).antisymm (key u' u hu' hu hb.symm)

end FormFacts

/-! ### Palettes -/

/-- The colours of `[m-1]` outside `F`, in increasing order. -/
def palette (m : ℕ) (F : Finset ℕ) : List ℕ := (range (m - 1) \ F).sort (· ≤ ·)

theorem mem_palette {m : ℕ} {F : Finset ℕ} {c : ℕ} : c ∈ palette m F ↔ c < m - 1 ∧ c ∉ F := by
  simp [palette]

theorem palette_nodup (m : ℕ) (F : Finset ℕ) : (palette m F).Nodup := sort_nodup _ _

theorem le_length_palette (m : ℕ) (F : Finset ℕ) : m - 1 - F.card ≤ (palette m F).length := by
  rw [palette, length_sort]
  have := le_card_sdiff F (range (m - 1))
  rwa [card_range] at this

theorem getD_eq_getElem' {l : List ℕ} {a : ℕ} (ha : a < l.length) : l.getD a 0 = l[a] := by
  simp [List.getD_eq_getElem?_getD, ha]

theorem getD_mem_palette {m : ℕ} {F : Finset ℕ} {a : ℕ} (ha : a < (palette m F).length) :
    (palette m F).getD a 0 ∈ palette m F := by
  rw [getD_eq_getElem' ha]
  exact List.getElem_mem ha

theorem getD_palette_inj {m : ℕ} {F : Finset ℕ} {a a' : ℕ} (ha : a < (palette m F).length)
    (ha' : a' < (palette m F).length)
    (h : (palette m F).getD a 0 = (palette m F).getD a' 0) : a = a' := by
  rw [getD_eq_getElem' ha, getD_eq_getElem' ha'] at h
  exact (palette_nodup m F).getElem_inj_iff.1 h

/-! ### The algorithms `RR` and `RR_i` -/

section Algorithms

variable (β : History → ℕ) (ρ : History → Finset ℕ) (m i N : ℕ)

/-- The number of earlier vertices in the block of the next vertex. -/
def posIn (g : History) : ℕ := ((range g.length).filter fun w => bidx β g w = β g).card

/-- Round robin: the `t`-th vertex of a block gets the `(t mod q)`-th colour of its palette, the
colours of `[m-1]` that its earlier neighbours do not have (`q` is the size of the palette). -/
def rrRaw (g : History) (s : Finset ℕ) : ℕ :=
  (palette m (nbrColours g s)).getD (posIn β g % (palette m (nbrColours g s)).length) 0

/-- The hub of a vertex of a block after `i`: its earliest neighbour in block `i`. -/
noncomputable def hub (g : History) (w : ℕ) : ℕ := sInf {x | x ∈ nb g w ∧ bidx β g x = i}

/-- The group of the hub `x`: the vertices of the blocks after `i` whose hub is `x`. -/
noncomputable def grp (g : History) (x : ℕ) : Finset ℕ :=
  (range g.length).filter fun w => i < bidx β g w ∧ hub β i g w = x

/-- The graph induced on the group of `x`. -/
noncomputable def grpGraph (g : History) (x : ℕ) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ a ∈ grp β i g x ∧ b ∈ grp β i g x ∧ (a ∈ nb g b ∨ b ∈ nb g a)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The colour that the algorithm of Lovász, Saks and Trotter gives the next vertex inside its
group: the least colour that does not occur on a vertex of the group joined to it by a walk of odd
length. -/
noncomputable def lstL (h : History) (s : Finset ℕ) : ℕ :=
  sInf {k | ∀ w, (hw : w < h.length) →
    w ∈ grp β i (h ++ [(s, 0)]) (hub β i (h ++ [(s, 0)]) h.length) →
    OddReach (grpGraph β i (h ++ [(s, 0)]) (hub β i (h ++ [(s, 0)]) h.length)) h.length w →
    lstL (h.take w) (nb h w) ≠ k}
termination_by h.length
decreasing_by
  rw [List.length_take]
  omega

/-- The colours of the earlier neighbours in the blocks up to `i`. -/
def exclSet (g : History) (s : Finset ℕ) : Finset ℕ :=
  (s.filter fun w => bidx β g w ≤ i).image (colourAt g)

/-- The reserve of block `i`, as selected when the history is `g`. -/
def Rset (g : History) : Finset ℕ :=
  (range g.length).filter fun u => bidx β g u = i ∧ u ∈ ρ g

/-- `RR_i` before patching: round robin up to block `i`; a later vertex is coloured by the pair
(hub, colour of Lovász–Saks–Trotter inside the group of the hub), which is mapped into the colours
of `[m-1]` that the reserves of the blocks up to `i` do not have. -/
noncomputable def rriRaw (g : History) (s : Finset ℕ) : ℕ :=
  if β g ≤ i then rrRaw β m g s
  else (palette m (exclSet β i g s)).getD
    (((Rset β ρ i g).filter (· < hub β i (g ++ [(s, 0)]) g.length)).card
      * (2 * Nat.log 2 N + 1) + lstL β i g s) 0

/-- The algorithm `RR_i` of the proof of Theorem D.5; `RR` is `RR_m`. -/
noncomputable def rriAlg : OnlineAlg := (⟨rriRaw β ρ m i N⟩ : OnlineAlg).patch

theorem rriAlg_isProper : (rriAlg β ρ m i N).IsProper := OnlineAlg.patch_isProper _

/-- The position of `u` in its block. -/
def posOf (H : History) (u : ℕ) : ℕ :=
  ((range u).filter fun w => bidx β H w = bidx β H u).card

end Algorithms

/-! ### Round robin -/

section RoundRobin

variable {β : History → ℕ} {ρ : History → Finset ℕ} {m i₀ N : ℕ} {H : History}

theorem posOf_lt_posOf {u u' : ℕ} (h : u < u') (hb : bidx β H u = bidx β H u') :
    posOf β H u < posOf β H u' := by
  unfold posOf
  have hmem : u ∈ (range u').filter fun w => bidx β H w = bidx β H u' :=
    mem_filter.2 ⟨mem_range.2 h, hb⟩
  have hsub : ((range u).filter fun w => bidx β H w = bidx β H u)
      ⊆ ((range u').filter fun w => bidx β H w = bidx β H u').erase u := by
    intro w hw
    rw [mem_filter, mem_range] at hw
    exact mem_erase.2 ⟨hw.1.ne, mem_filter.2 ⟨mem_range.2 (hw.1.trans h), hw.2.trans hb⟩⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hmem] at this
  have := card_pos.2 ⟨u, hmem⟩
  omega

theorem posOf_lt_blockCard {u : ℕ} (hu : u < H.length) :
    posOf β H u < blockCard β H (bidx β H u) := by
  unfold posOf blockCard
  have hmem : u ∈ (range H.length).filter fun w => bidx β H w = bidx β H u :=
    mem_filter.2 ⟨mem_range.2 hu, rfl⟩
  have hsub : ((range u).filter fun w => bidx β H w = bidx β H u)
      ⊆ ((range H.length).filter fun w => bidx β H w = bidx β H u).erase u := by
    intro w hw
    rw [mem_filter, mem_range] at hw
    exact mem_erase.2 ⟨hw.1.ne, mem_filter.2 ⟨mem_range.2 (hw.1.trans hu), hw.2⟩⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hmem] at this
  have := card_pos.2 ⟨u, hmem⟩
  omega

/-- A vertex of a block `t ≤ i₀`, `t + 1 < m`, is coloured by round robin from its palette, which
has at least `m - 1 - t` colours; its colour lies in `[m-1]`. -/
theorem early_colour (hf : PJForm β ρ m H) (hr : IsRunOf (rriAlg β ρ m i₀ N) H) {u : ℕ}
    (hu : u < H.length) (ht : bidx β H u ≤ i₀) (htm : bidx β H u + 1 < m) :
    colourAt H u = (palette m ((nb H u).image (colourAt H))).getD
        (posOf β H u % (palette m ((nb H u).image (colourAt H))).length) 0 ∧
      m - 1 - bidx β H u ≤ (palette m ((nb H u).image (colourAt H))).length ∧
      colourAt H u < m - 1 := by
  set F := (nb H u).image (colourAt H) with hFdef
  set P := palette m F with hP
  have hF : F.card ≤ bidx β H u :=
    hf.card_image_le hu subset_rfl fun w hw => (hf.nbr u hu w hw).2
  have hlen : m - 1 - bidx β H u ≤ P.length := le_trans (by omega) (le_length_palette m F)
  have hpos : 0 < P.length := by omega
  have hnc : nbrColours (H.take u) (nb H u) = F :=
    nbrColours_take hu.le fun x hx => (hf.nbr u hu x hx).1
  have hposIn : posIn β (H.take u) = posOf β H u := by
    unfold posIn posOf
    rw [length_take_of_le hu.le]
    exact congrArg card (filter_congr fun w hw => by
      rw [bidx_take (mem_range.1 hw).le]
      rfl)
  have hraw : rriRaw β ρ m i₀ N (H.take u) (nb H u) = P.getD (posOf β H u % P.length) 0 := by
    have hc : β (H.take u) ≤ i₀ := ht
    unfold rriRaw
    simp only [hc, ↓reduceIte]
    unfold rrRaw
    rw [hnc, hposIn]
  have hmem : P.getD (posOf β H u % P.length) 0 ∈ P := getD_mem_palette (Nat.mod_lt _ hpos)
  have hcol : colourAt H u = P.getD (posOf β H u % P.length) 0 := by
    rw [colourAt_eq_step hr hu]
    change (if rriRaw β ρ m i₀ N (H.take u) (nb H u) ∈ nbrColours (H.take u) (nb H u)
      then _ else _) = _
    rw [hraw, hnc]
    simp only [(mem_palette.1 hmem).2, ↓reduceIte]
    exact hraw
  exact ⟨hcol, hlen, hcol ▸ (mem_palette.1 hmem).1⟩

theorem mem_Rset_take {i n u : ℕ} (hn : n ≤ H.length) :
    u ∈ Rset β ρ i (H.take n) ↔ u < n ∧ bidx β H u = i ∧ u ∈ ρ (H.take n) := by
  unfold Rset
  rw [mem_filter, mem_range, length_take_of_le hn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rwa [bidx_take h1.le] at h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rwa [bidx_take h1.le], h3⟩

/-- **Round robin** (the first step of the proof of Theorem D.5): since the reserve `R_i` is
monochromatic, `|B_i| ≥ (m-1-i)(|R_i|-1)+1` (blocks numbered from `0`). -/
theorem rr_bound (hf : PJForm β ρ m H) (hr : IsRunOf (rriAlg β ρ m i₀ N) H) {i n : ℕ}
    (hi : i ≤ i₀) (him : i + 1 < m) (hn : n < H.length) (hbn : i < bidx β H n) :
    (m - 1 - i) * ((Rset β ρ i (H.take n)).card - 1) + 1 ≤ blockCard β H i := by
  set R := Rset β ρ i (H.take n) with hR
  have hRmem : ∀ u ∈ R, u < n ∧ bidx β H u = i ∧ u ∈ ρ (H.take n) := fun u hu =>
    (mem_Rset_take hn.le).1 hu
  obtain ⟨w₀, hw₀, hw₀b⟩ := hf.cover n hn i hbn
  have hw₀lt : w₀ < H.length := (hf.nbr n hn w₀ hw₀).1.trans hn
  have hB1 : 1 ≤ blockCard β H i :=
    card_pos.2 ⟨w₀, mem_filter.2 ⟨mem_range.2 hw₀lt, hw₀b⟩⟩
  set P := palette m ((nb H w₀).image (colourAt H)) with hP
  have hpal : ∀ u, u < H.length → bidx β H u = i →
      palette m ((nb H u).image (colourAt H)) = P := by
    intro u hu hb
    rw [hP, hf.image_eq hu hw₀lt (hb.trans hw₀b.symm)]
  have hq : m - 1 - i ≤ P.length := by
    have := (early_colour hf hr hw₀lt (by omega) (by omega)).2.1
    rwa [hw₀b] at this
  have hqpos : 0 < P.length := by omega
  have hcol : ∀ u ∈ R, colourAt H u = P.getD (posOf β H u % P.length) 0 := by
    intro u hu
    obtain ⟨hun, hub, -⟩ := hRmem u hu
    have := (early_colour hf hr (hun.trans hn) (by omega) (by omega)).1
    rwa [hpal u (hun.trans hn) hub] at this
  have hmono : ∀ u ∈ R, ∀ u' ∈ R, colourAt H u = colourAt H u' := by
    intro u hu u' hu'
    obtain ⟨hun, hub, hur⟩ := hRmem u hu
    obtain ⟨hun', hub', hur'⟩ := hRmem u' hu'
    exact hf.resMono n hn u hun u' hun' hur hur' (hub.trans hub'.symm) (hub ▸ hbn)
  have hmod : ∀ u ∈ R, ∀ u' ∈ R, posOf β H u % P.length = posOf β H u' % P.length := by
    intro u hu u' hu'
    apply getD_palette_inj (Nat.mod_lt _ hqpos) (Nat.mod_lt _ hqpos)
    rw [← hcol u hu, ← hcol u' hu', hmono u hu u' hu']
  have hcard : R.card ≤ (blockCard β H i - 1) / P.length + 1 := by
    rw [← card_range ((blockCard β H i - 1) / P.length + 1)]
    refine card_le_card_of_injOn (fun u => posOf β H u / P.length) ?_ ?_
    · intro u hu
      obtain ⟨hun, hub, -⟩ := hRmem u (mem_coe.1 hu)
      have := posOf_lt_blockCard (β := β) (hun.trans hn)
      rw [hub] at this
      exact mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))))
    · intro u hu u' hu' hdiv
      have hdiv' : posOf β H u / P.length = posOf β H u' / P.length := hdiv
      have hm := hmod u (mem_coe.1 hu) u' (mem_coe.1 hu')
      have hpp : posOf β H u = posOf β H u' := by
        rw [← Nat.div_add_mod (posOf β H u) P.length, ← Nat.div_add_mod (posOf β H u') P.length,
          hdiv', hm]
      have hbb : bidx β H u = bidx β H u' :=
        (hRmem u (mem_coe.1 hu)).2.1.trans (hRmem u' (mem_coe.1 hu')).2.1.symm
      rcases lt_trichotomy u u' with h | h | h
      · exact absurd hpp (posOf_lt_posOf h hbb).ne
      · exact h
      · exact absurd hpp.symm (posOf_lt_posOf h hbb.symm).ne
  have h0 : R.card - 1 ≤ (blockCard β H i - 1) / P.length := Nat.sub_le_of_le_add hcard
  have h1 : P.length * (R.card - 1) ≤ blockCard β H i - 1 :=
    (Nat.mul_le_mul_left _ h0).trans (Nat.mul_div_le _ _)
  have h2 : (m - 1 - i) * (R.card - 1) ≤ P.length * (R.card - 1) := Nat.mul_le_mul_right _ hq
  omega

end RoundRobin

/-! ### The hub strategy -/

section Hub

variable {β : History → ℕ} {ρ : History → Finset ℕ} {m i N : ℕ} {H : History}

theorem hub_mem (hf : PJForm β ρ m H) {a : ℕ} (ha : a < H.length) (hia : i < bidx β H a) :
    hub β i H a ∈ nb H a ∧ bidx β H (hub β i H a) = i := by
  obtain ⟨x, hx, hxb⟩ := hf.cover a ha i hia
  exact Nat.sInf_mem (s := {x | x ∈ nb H a ∧ bidx β H x = i}) ⟨x, hx, hxb⟩

/-- The history that the algorithm sees when `u` arrives, with `u` appended. -/
def viewAt (H : History) (u : ℕ) : History := H.take u ++ [(nb H u, 0)]

theorem length_viewAt {u : ℕ} (hu : u < H.length) : (viewAt H u).length = u + 1 := by
  simp [viewAt, length_take_of_le hu.le]

theorem bidx_viewAt {u w : ℕ} (hu : u < H.length) (hw : w ≤ u) :
    bidx β (viewAt H u) w = bidx β H w := by
  unfold viewAt
  rw [bidx_snoc (by rw [length_take_of_le hu.le]; exact hw), bidx_take hw]

theorem nb_viewAt {u w : ℕ} (hu : u < H.length) (hw : w ≤ u) : nb (viewAt H u) w = nb H w := by
  unfold viewAt
  rcases hw.lt_or_eq with h | rfl
  · rw [nb_snoc_lt (by rw [length_take_of_le hu.le]; exact h), nb_take h]
  · have := nb_snoc_self (h := H.take w) (x := (nb H w, 0))
    rwa [length_take_of_le hu.le] at this

theorem hub_viewAt (hf : PJForm β ρ m H) {u w : ℕ} (hu : u < H.length) (hw : w ≤ u) :
    hub β i (viewAt H u) w = hub β i H w := by
  unfold hub
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [nb_viewAt hu hw]
  constructor
  · rintro ⟨hx, hb⟩
    have hxw := (hf.nbr w (lt_of_le_of_lt hw hu) x hx).1
    exact ⟨hx, by rwa [bidx_viewAt hu (hxw.le.trans hw)] at hb⟩
  · rintro ⟨hx, hb⟩
    have hxw := (hf.nbr w (lt_of_le_of_lt hw hu) x hx).1
    exact ⟨hx, by rwa [bidx_viewAt hu (hxw.le.trans hw)]⟩

theorem mem_grp_viewAt (hf : PJForm β ρ m H) {u w x : ℕ} (hu : u < H.length) :
    w ∈ grp β i (viewAt H u) x ↔ w ≤ u ∧ w ∈ grp β i H x := by
  unfold grp
  rw [mem_filter, mem_filter, mem_range, mem_range, length_viewAt hu]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hw : w ≤ u := by omega
    rw [bidx_viewAt hu hw] at h2
    rw [hub_viewAt hf hu hw] at h3
    exact ⟨hw, lt_of_le_of_lt hw hu, h2, h3⟩
  · rintro ⟨hw, -, h2, h3⟩
    refine ⟨by omega, ?_, ?_⟩
    · rwa [bidx_viewAt hu hw]
    · rwa [hub_viewAt hf hu hw]

theorem restrictLE_grpGraph_viewAt (hf : PJForm β ρ m H) {u x : ℕ} (hu : u < H.length) :
    restrictLE (grpGraph β i (viewAt H u) x) u = restrictLE (grpGraph β i H x) u := by
  ext a b
  change (a ≤ u ∧ b ≤ u ∧ a ≠ b ∧ a ∈ grp β i (viewAt H u) x ∧ b ∈ grp β i (viewAt H u) x ∧
      (a ∈ nb (viewAt H u) b ∨ b ∈ nb (viewAt H u) a)) ↔
    (a ≤ u ∧ b ≤ u ∧ a ≠ b ∧ a ∈ grp β i H x ∧ b ∈ grp β i H x ∧ (a ∈ nb H b ∨ b ∈ nb H a))
  constructor
  · rintro ⟨ha, hb, hne, hga, hgb, hadj⟩
    rw [nb_viewAt hu hb, nb_viewAt hu ha] at hadj
    exact ⟨ha, hb, hne, ((mem_grp_viewAt hf hu).1 hga).2, ((mem_grp_viewAt hf hu).1 hgb).2, hadj⟩
  · rintro ⟨ha, hb, hne, hga, hgb, hadj⟩
    rw [← nb_viewAt hu hb, ← nb_viewAt hu ha] at hadj
    exact ⟨ha, hb, hne, (mem_grp_viewAt hf hu).2 ⟨ha, hga⟩, (mem_grp_viewAt hf hu).2 ⟨hb, hgb⟩,
      hadj⟩

theorem oddReach_congr {G G' : SimpleGraph ℕ} {v w : ℕ} (h : restrictLE G v = restrictLE G' v) :
    OddReach G v w ↔ OddReach G' v w := by
  unfold OddReach
  rw [h]

/-- The Lovász–Saks–Trotter colour of `v` in terms of the final history. -/
theorem lstL_eq (hf : PJForm β ρ m H) {v : ℕ} (hv : v < H.length) :
    lstL β i (H.take v) (nb H v) = sInf {k | ∀ w, w < v → w ∈ grp β i H (hub β i H v) →
      OddReach (grpGraph β i H (hub β i H v)) v w → lstL β i (H.take w) (nb H w) ≠ k} := by
  rw [lstL]
  have elen : (H.take v).length = v := length_take_of_le hv.le
  have ehub : hub β i (viewAt H v) v = hub β i H v := hub_viewAt hf hv le_rfl
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  rw [elen]
  change (∀ w, w < v → w ∈ grp β i (viewAt H v) (hub β i (viewAt H v) v) →
    OddReach (grpGraph β i (viewAt H v) (hub β i (viewAt H v) v)) v w →
    lstL β i ((H.take v).take w) (nb (H.take v) w) ≠ k) ↔ _
  rw [ehub]
  constructor
  · intro hT w hw hg ho
    have := hT w hw ((mem_grp_viewAt hf hv).2 ⟨hw.le, hg⟩)
      ((oddReach_congr (restrictLE_grpGraph_viewAt hf hv)).2 ho)
    rwa [List.take_take, min_eq_left hw.le, nb_take hw] at this
  · intro hT w hw hg ho
    rw [List.take_take, min_eq_left hw.le, nb_take hw]
    exact hT w hw ((mem_grp_viewAt hf hv).1 hg).2
      ((oddReach_congr (restrictLE_grpGraph_viewAt hf hv)).1 ho)

/-- Inside every group the colours `lstL` are those of the algorithm of Lovász, Saks and
Trotter. -/
theorem isLSTColouring_grp (hf : PJForm β ρ m H) (x : ℕ) :
    IsLSTColouring (grpGraph β i H x) (grp β i H x)
      (fun w => lstL β i (H.take w) (nb H w)) := by
  intro v hv
  have hv' := mem_filter.1 hv
  have hvlen : v < H.length := mem_range.1 hv'.1
  have hx : hub β i H v = x := hv'.2.2
  have heq := lstL_eq (i := i) hf hvlen
  rw [hx] at heq
  set T : Set ℕ := {k | ∀ w, w < v → w ∈ grp β i H x → OddReach (grpGraph β i H x) v w →
    lstL β i (H.take w) (nb H w) ≠ k} with hT
  have hne : T.Nonempty := by
    refine ⟨((range v).image fun w => lstL β i (H.take w) (nb H w)).sup id + 1,
      fun w hw _ _ heq' => ?_⟩
    have := le_sup (f := id) (mem_image_of_mem (fun w => lstL β i (H.take w) (nb H w))
      (mem_range.2 hw))
    simp only [id] at this
    omega
  constructor
  · intro k hk
    change k < lstL β i (H.take v) (nb H v) at hk
    rw [heq] at hk
    have hnot := Nat.notMem_of_lt_sInf hk
    rw [hT, Set.mem_ofPred_eq] at hnot
    push Not at hnot
    obtain ⟨w, hwv, hwg, hodd, hk'⟩ := hnot
    exact ⟨w, hwg, hwv, hodd, hk'⟩
  · intro w hwg hwv hodd
    change lstL β i (H.take w) (nb H w) ≠ lstL β i (H.take v) (nb H v)
    rw [heq]
    exact Nat.sInf_mem hne w hwv hwg hodd

theorem graph_adj_of_mem {x w : ℕ} (hw : w < H.length) (hx : x ∈ nb H w) (hxw : x < w) :
    H.graph.Adj ⟨x, hxw.trans hw⟩ ⟨w, hw⟩ := by
  rw [History.graph_adj]
  rw [nb_eq_getElem hw] at hx
  exact Or.inl ⟨hxw, hx⟩

/-- Every group is bipartite: in a `3`-colouring it avoids the colour of its hub. -/
theorem exists_coloring_grp (hf : PJForm β ρ m H) (hc : H.graph.Colorable 3) (x : ℕ) :
    Nonempty ((grpGraph β i H x).Coloring Bool) := by
  obtain ⟨c⟩ := hc
  let cc : ℕ → ℕ := fun a => if h : a < H.length then (c ⟨a, h⟩ : ℕ) else 0
  refine ⟨SimpleGraph.Coloring.mk (fun a => decide (cc a = if cc x = 0 then 1 else 0)) ?_⟩
  rintro a b ⟨hne, hga, hgb, hadj⟩
  have ha' := mem_filter.1 hga
  have hb' := mem_filter.1 hgb
  have ha : a < H.length := mem_range.1 ha'.1
  have hb : b < H.length := mem_range.1 hb'.1
  have hxa := hub_mem hf ha ha'.2.1
  have hxb := hub_mem hf hb hb'.2.1
  rw [ha'.2.2] at hxa
  rw [hb'.2.2] at hxb
  have hxa_lt := (hf.nbr a ha x hxa.1).1
  have hxb_lt := (hf.nbr b hb x hxb.1).1
  have hx : x < H.length := hxa_lt.trans ha
  have e1 : cc a ≠ cc x := by
    simp only [cc, ha, hx, ↓reduceDIte]
    exact fun e => c.valid (graph_adj_of_mem ha hxa.1 hxa_lt) (Fin.ext e.symm)
  have e2 : cc b ≠ cc x := by
    simp only [cc, hb, hx, ↓reduceDIte]
    exact fun e => c.valid (graph_adj_of_mem hb hxb.1 hxb_lt) (Fin.ext e.symm)
  have e3 : cc a ≠ cc b := by
    simp only [cc, ha, hb, ↓reduceDIte]
    rcases hadj with h | h
    · exact fun e => c.valid (graph_adj_of_mem hb h (hf.nbr b hb a h).1) (Fin.ext e)
    · exact fun e => c.valid (graph_adj_of_mem ha h (hf.nbr a ha b h).1) (Fin.ext e.symm)
  have b1 : cc a < 3 := by
    simp only [cc, ha, ↓reduceDIte]
    exact (c ⟨a, ha⟩).2
  have b2 : cc b < 3 := by
    simp only [cc, hb, ↓reduceDIte]
    exact (c ⟨b, hb⟩).2
  have b3 : cc x < 3 := by
    simp only [cc, hx, ↓reduceDIte]
    exact (c ⟨x, hx⟩).2
  rw [Ne, decide_eq_decide]
  intro hiff
  split_ifs at hiff <;> omega

/-- Inside a group at most `2 ⌊log₂ N⌋ + 1` colours occur, if the graph of `H` is `3`-colourable
and `H` has at most `N` vertices. -/
theorem lstL_le (hf : PJForm β ρ m H) (hc : H.graph.Colorable 3) (hN : H.length ≤ N) {v : ℕ}
    (hv : v < H.length) (hiv : i < bidx β H v) :
    lstL β i (H.take v) (nb H v) ≤ 2 * Nat.log 2 N := by
  obtain ⟨χ⟩ := exists_coloring_grp (i := i) hf hc (hub β i H v)
  have hvg : v ∈ grp β i H (hub β i H v) := mem_filter.2 ⟨mem_range.2 hv, hiv, rfl⟩
  have h1 := lst_colour_le χ (isLSTColouring_grp hf (hub β i H v)) hvg
  have h2 : (grp β i H (hub β i H v)).card ≤ N :=
    (card_filter_le _ _).trans (by rw [card_range]; exact hN)
  have h3 := Nat.log_mono_right (b := 2) h2
  omega

/-- The pair (hub, colour inside the group) of a vertex after block `i`, as a number. -/
noncomputable def hubCode (β : History → ℕ) (ρ : History → Finset ℕ) (i N : ℕ) (H : History)
    (n u : ℕ) : ℕ :=
  ((Rset β ρ i (H.take n)).filter (· < hub β i H u)).card * (2 * Nat.log 2 N + 1)
    + lstL β i (H.take u) (nb H u)

/-- The colours that the reserves of the blocks up to `i` show to the vertex `u`. -/
def exclAt (β : History → ℕ) (i : ℕ) (H : History) (u : ℕ) : Finset ℕ :=
  ((nb H u).filter fun w => bidx β H w ≤ i).image (colourAt H)

theorem exclSet_take (hf : PJForm β ρ m H) {u : ℕ} (hu : u < H.length) :
    exclSet β i (H.take u) (nb H u) = exclAt β i H u := by
  unfold exclSet exclAt
  have e : ((nb H u).filter fun w => bidx β (H.take u) w ≤ i)
      = (nb H u).filter fun w => bidx β H w ≤ i :=
    filter_congr fun w hw => by rw [bidx_take (hf.nbr u hu w hw).1.le]
  rw [e]
  exact image_congr fun w hw => colourAt_take (hf.nbr u hu w (mem_filter.1 hw).1).1

theorem exclAt_eq (hf : PJForm β ρ m H) {u u' : ℕ} (hu : u < H.length) (hu' : u' < H.length)
    (hb : i < bidx β H u) (hb' : i < bidx β H u') : exclAt β i H u = exclAt β i H u' := by
  have key : ∀ a a', a < H.length → a' < H.length → i < bidx β H a' →
      exclAt β i H a ⊆ exclAt β i H a' := by
    intro a a' ha ha' hia' c hc
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
    rw [mem_filter] at hw
    obtain ⟨w', hw', hwb⟩ := hf.cover a' ha' (bidx β H w) (by omega)
    exact mem_image.2 ⟨w', mem_filter.2 ⟨hw', by omega⟩, hf.sameCol ha' ha hw' hw.1 hwb⟩
  exact (key u u' hu hu' hb').antisymm (key u' u hu' hu hb)

theorem card_exclAt_le (hf : PJForm β ρ m H) {u : ℕ} (hu : u < H.length) :
    (exclAt β i H u).card ≤ i + 1 :=
  hf.card_image_le hu (filter_subset _ _) fun _ hw => Nat.lt_succ_of_le (mem_filter.1 hw).2

theorem Rset_take_eq (hf : PJForm β ρ m H) {u n : ℕ} (hu : u < H.length) (hn : n < H.length)
    (hb : i < bidx β H u) (hbn : i < bidx β H n) :
    Rset β ρ i (H.take u) = Rset β ρ i (H.take n) := by
  have key : ∀ a a', a < H.length → a' < H.length → i < bidx β H a → i < bidx β H a' →
      Rset β ρ i (H.take a) ⊆ Rset β ρ i (H.take a') := by
    intro a a' ha ha' hia hia' w hw
    rw [mem_Rset_take ha.le] at hw
    rw [mem_Rset_take ha'.le]
    obtain ⟨hwa, hwb, hwr⟩ := hw
    have hwa' : w < a' := hf.lt_of_bidx_lt (hwa.trans ha) (by omega)
    refine ⟨hwa', hwb, ?_⟩
    rcases le_total a a' with h | h
    · exact (hf.stab a a' h ha' w hwa (by omega)).1 hwr
    · exact (hf.stab a' a h ha w hwa' (by omega)).2 hwr
  exact (key u n hu hn hb hbn).antisymm (key n u hn hu hbn hb)

theorem code_inj {a b a' b' L : ℕ} (hb : b < L) (hb' : b' < L) (h : a * L + b = a' * L + b') :
    a = a' ∧ b = b' := by
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · have h1 : (a + 1) * L ≤ a' * L := Nat.mul_le_mul_right L hlt
    have h2 : (a + 1) * L = a * L + L := by ring
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : (a' + 1) * L ≤ a * L := Nat.mul_le_mul_right L hgt
    have h2 : (a' + 1) * L = a' * L + L := by ring
    omega

/-- The hypotheses of the analysis of `RR_i`: `H` is a play of a partial-join level against
`RR_i` with at most `N` vertices whose graph is `3`-colourable, the vertex `n` lies after block
`i`, and the reserve `R_i` is small: `|R_i| (2 ⌊log₂ N⌋ + 1) ≤ m - 2 - i`. -/
structure HubCtx (β : History → ℕ) (ρ : History → Finset ℕ) (m i N : ℕ) (H : History) (n : ℕ) :
    Prop where
  form : PJForm β ρ m H
  run : IsRunOf (rriAlg β ρ m i N) H
  him : i + 1 < m
  hn : n < H.length
  hbn : i < bidx β H n
  col3 : H.graph.Colorable 3
  size : H.length ≤ N
  small : (Rset β ρ i (H.take n)).card * (2 * Nat.log 2 N + 1) ≤ m - 2 - i

/-- **The hub strategy** (the second step of the proof of Theorem D.5): if the reserve `R_i` is
small, `RR_i` uses only colours of `[m-1]`. -/
theorem hub_colour_lt {n : ℕ} (C : HubCtx β ρ m i N H n) :
    ∀ u, u < H.length → colourAt H u < m - 1 ∧ (i < bidx β H u →
      colourAt H u = (palette m (exclAt β i H n)).getD (hubCode β ρ i N H n u) 0 ∧
      hubCode β ρ i N H n u < (palette m (exclAt β i H n)).length) := by
  have hf := C.form
  set R := Rset β ρ i (H.take n) with hR
  set P := palette m (exclAt β i H n) with hP
  set L := 2 * Nat.log 2 N + 1 with hL
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu
  by_cases hb : bidx β H u ≤ i
  · exact ⟨(early_colour hf C.run hu hb (by have := C.him; omega)).2.2,
      fun h => absurd h (by omega)⟩
  have hb' : i < bidx β H u := by omega
  have hnc : nbrColours (H.take u) (nb H u) = (nb H u).image (colourAt H) :=
    nbrColours_take hu.le fun x hx => (hf.nbr u hu x hx).1
  have hraw : rriRaw β ρ m i N (H.take u) (nb H u) = P.getD (hubCode β ρ i N H n u) 0 := by
    have hc : ¬ β (H.take u) ≤ i := hb
    have ehub : hub β i (H.take u ++ [(nb H u, 0)]) (H.take u).length = hub β i H u := by
      rw [length_take_of_le hu.le]
      exact hub_viewAt hf hu le_rfl
    unfold rriRaw
    simp only [hc, ↓reduceIte]
    rw [exclSet_take hf hu, exclAt_eq hf hu C.hn hb' C.hbn, Rset_take_eq hf hu C.hn hb' C.hbn,
      ehub]
    rfl
  -- the hub and its rank
  obtain ⟨hxn, hxb⟩ := hub_mem hf hu hb'
  have hxu := (hf.nbr u hu _ hxn).1
  have hxR : hub β i H u ∈ R := by
    rw [hR, ← Rset_take_eq hf hu C.hn hb' C.hbn, mem_Rset_take hu.le]
    exact ⟨hxu, hxb, hf.res u hu _ hxn⟩
  have hrank : (R.filter (· < hub β i H u)).card < R.card :=
    card_lt_card (filter_ssubset.2 ⟨_, hxR, lt_irrefl _⟩)
  have hℓ := lstL_le hf C.col3 C.size hu hb'
  have hcodelt : hubCode β ρ i N H n u < P.length := by
    have h1 : ((R.filter (· < hub β i H u)).card + 1) * L ≤ R.card * L :=
      Nat.mul_le_mul_right L hrank
    have h2 : ((R.filter (· < hub β i H u)).card + 1) * L
        = (R.filter (· < hub β i H u)).card * L + L := by ring
    have h3 : R.card * L ≤ m - 2 - i := C.small
    have h4 : m - 1 - (exclAt β i H n).card ≤ P.length := le_length_palette m _
    have h5 := card_exclAt_le (i := i) hf C.hn
    have hL' : L = 2 * Nat.log 2 N + 1 := rfl
    have h6 : hubCode β ρ i N H n u
        = (R.filter (· < hub β i H u)).card * L + lstL β i (H.take u) (nb H u) := rfl
    omega
  have hmem : P.getD (hubCode β ρ i N H n u) 0 ∈ P := getD_mem_palette hcodelt
  have hnot : P.getD (hubCode β ρ i N H n u) 0 ∉ (nb H u).image (colourAt H) := by
    intro hm
    obtain ⟨w, hw, hwc⟩ := mem_image.1 hm
    obtain ⟨hwu, hwb⟩ := hf.nbr u hu w hw
    by_cases hwi : bidx β H w ≤ i
    · apply (mem_palette.1 hmem).2
      rw [← hwc, ← exclAt_eq hf hu C.hn hb' C.hbn]
      exact mem_image.2 ⟨w, mem_filter.2 ⟨hw, hwi⟩, rfl⟩
    · have hwi' : i < bidx β H w := by omega
      have hwlen : w < H.length := hwu.trans hu
      obtain ⟨hwcol, hwlt⟩ := (ih w hwu hwlen).2 hwi'
      have hcode : hubCode β ρ i N H n w = hubCode β ρ i N H n u :=
        getD_palette_inj hwlt hcodelt (hwcol.symm.trans hwc)
      have hℓw := lstL_le hf C.col3 C.size hwlen hwi'
      have hL' : L = 2 * Nat.log 2 N + 1 := rfl
      obtain ⟨hrk, hℓeq⟩ := code_inj (L := L) (by omega) (by omega) hcode
      -- equal ranks: equal hubs
      obtain ⟨hyn, hyb⟩ := hub_mem hf hwlen hwi'
      have hyR : hub β i H w ∈ R := by
        rw [hR, ← Rset_take_eq hf hwlen C.hn hwi' C.hbn, mem_Rset_take hwlen.le]
        exact ⟨(hf.nbr w hwlen _ hyn).1, hyb, hf.res w hwlen _ hyn⟩
      have hrank_lt : ∀ y y', y ∈ R → y < y' →
          (R.filter (· < y)).card < (R.filter (· < y')).card := by
        intro y y' hy hyy'
        refine card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
        · rw [mem_filter] at hz ⊢
          exact ⟨hz.1, hz.2.trans hyy'⟩
        · exact lt_irrefl y (mem_filter.1 (hsub (mem_filter.2 ⟨hy, hyy'⟩))).2
      have hhub : hub β i H w = hub β i H u := by
        rcases lt_trichotomy (hub β i H w) (hub β i H u) with h | h | h
        · exact absurd hrk (hrank_lt _ _ hyR h).ne
        · exact h
        · exact absurd hrk.symm (hrank_lt _ _ hxR h).ne
      have hgu : u ∈ grp β i H (hub β i H u) := mem_filter.2 ⟨mem_range.2 hu, hb', rfl⟩
      have hgw : w ∈ grp β i H (hub β i H u) := mem_filter.2 ⟨mem_range.2 hwlen, hwi', hhub⟩
      have hadj : (restrictLE (grpGraph β i H (hub β i H u)) u).Adj u w :=
        ⟨le_rfl, hwu.le, hwu.ne', hgu, hgw, Or.inr hw⟩
      have hodd : OddReach (grpGraph β i H (hub β i H u)) u w :=
        ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp⟩
      exact ((isLSTColouring_grp hf (hub β i H u)) u hgu).2 w hgw hwu hodd hℓeq
  have hcol : colourAt H u = P.getD (hubCode β ρ i N H n u) 0 := by
    rw [colourAt_eq_step C.run hu]
    change (if rriRaw β ρ m i N (H.take u) (nb H u) ∈ nbrColours (H.take u) (nb H u)
      then _ else _) = _
    rw [hraw, hnc]
    simp only [hnot, ↓reduceIte]
    exact hraw
  exact ⟨hcol ▸ (mem_palette.1 hmem).1, fun _ => ⟨hcol, hcodelt⟩⟩

theorem hub_card_usedColours_le {n : ℕ} (C : HubCtx β ρ m i N H n) :
    (usedColours H).card ≤ m - 1 := by
  have hsub : usedColours H ⊆ range (m - 1) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := exists_of_mem_usedColours hq
    exact mem_range.2 (hub_colour_lt C u hu).1
  have := card_le_card hsub
  rwa [card_range] at this

end Hub

/-! ### The plays against `RR` and `RR_i` -/

section Plays

theorem hist_of_stop {adv : Adversary} {A : OnlineAlg} {p : ℕ}
    (h : adv.move (adv.hist A p) = none) : ∀ q, p ≤ q → adv.hist A q = adv.hist A p := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => rfl
  | succ q _ ih => simp only [Adversary.hist, ih, h]

theorem hist_succ_some {adv : Adversary} {A : OnlineAlg} {p : ℕ} {s : Finset ℕ}
    (h : adv.move (adv.hist A p) = some s) :
    adv.hist A (p + 1) = adv.hist A p ++ [(s, A.step (adv.hist A p) s)] := by
  simp only [Adversary.hist, h]

theorem hist_take {adv : Adversary} {A : OnlineAlg} {p q : ℕ} (hpq : p ≤ q) :
    (adv.hist A q).take (adv.hist A p).length = adv.hist A p := by
  induction q, hpq using Nat.le_induction with
  | base => exact List.take_length
  | succ q _ ih =>
    cases hm : adv.move (adv.hist A q) with
    | none =>
      rw [hist_of_stop hm (q + 1) (Nat.le_succ q)]
      exact ih
    | some s =>
      have hlen := congrArg List.length ih
      rw [List.length_take] at hlen
      rw [hist_succ_some hm, List.take_append_of_le_length (by omega)]
      exact ih

/-- The plays of an adversary against two algorithms that agree on the histories with `Pr`
coincide until a vertex is presented at a history without `Pr`. -/
theorem plays_agree {adv : Adversary} {A A' : OnlineAlg} {Pr : History → Prop}
    (hstep : ∀ g s, Pr g → A.step g s = A'.step g s) :
    ∀ p, adv.hist A p = adv.hist A' p ∨ ∃ p' < p, adv.hist A p' = adv.hist A' p' ∧
      ∃ s, adv.move (adv.hist A p') = some s ∧ ¬ Pr (adv.hist A p') := by
  intro p
  induction p with
  | zero => exact Or.inl rfl
  | succ p ih =>
    rcases ih with h | ⟨p', hp', rest⟩
    · cases hm : adv.move (adv.hist A p) with
      | none =>
        left
        rw [hist_of_stop hm (p + 1) (Nat.le_succ p),
          hist_of_stop (h ▸ hm) (p + 1) (Nat.le_succ p)]
        exact h
      | some s =>
        by_cases hP : Pr (adv.hist A p)
        · left
          rw [hist_succ_some hm, hist_succ_some (h ▸ hm), ← h, hstep _ s hP]
        · exact Or.inr ⟨p, Nat.lt_succ_self p, h, s, hm, hP⟩
    · exact Or.inr ⟨p', Nat.lt_succ_of_lt hp', rest⟩

variable {β : History → ℕ} {ρ : History → Finset ℕ} {m N : ℕ}

theorem rriAlg_step_eq {i : ℕ} {g : History} {s : Finset ℕ} (hg : β g ≤ i) (him : i ≤ m) :
    (rriAlg β ρ m i N).step g s = (rriAlg β ρ m m N).step g s := by
  have e : rriRaw β ρ m i N g s = rriRaw β ρ m m N g s := by
    unfold rriRaw
    simp only [hg, hg.trans him, ↓reduceIte]
  change (if rriRaw β ρ m i N g s ∈ nbrColours g s then _ else _)
    = (if rriRaw β ρ m m N g s ∈ nbrColours g s then _ else _)
  rw [e]
  split_ifs
  · rfl
  · exact e

/-- **Theorem D.5 (partial joins).**  If a partial-join level over `K_m` (`IsPJAdv`, forcing `m`
colours) is `3`-colourable in every play against every algorithm and has at most `N` vertices,
then `N ≥ m³ / (3 (2 log₂ N + 1)) - m²`. -/
theorem partial_joins {adv : Adversary} (hadv : IsPJAdv β ρ m adv) (hF : adv.Forces m)
    (h3 : adv.LandsIn fun _ G => G.Colorable 3) (hN : adv.SizeLE N) :
    (m : ℝ) ^ 3 / (3 * (2 * Real.logb 2 N + 1)) - (m : ℝ) ^ 2 ≤ N := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hA' := rriAlg_isProper β ρ m m N
  obtain ⟨p₁, hstop₁, hK₁⟩ := hF _ hA'
  have hfH : PJForm β ρ m (adv.hist (rriAlg β ρ m m N) p₁) := hadv _ hA' p₁
  have hrH := adv.isRunOf_hist (rriAlg β ρ m m N) p₁
  have hlenH := hN _ hA' p₁
  generalize hHdef : adv.hist (rriAlg β ρ m m N) p₁ = H at *
  have hused : (usedColours H).card ≤ H.length := by
    rw [usedColours]
    exact (List.toFinset_card_le _).trans (by rw [List.length_map])
  have hN1 : 1 ≤ N := by omega
  have hlast : ∃ u₀, u₀ < H.length ∧ bidx β H u₀ = m - 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : usedColours H ⊆ range (m - 1) := by
      intro q hq
      obtain ⟨u, hu, rfl⟩ := exists_of_mem_usedColours hq
      have hlt := hfH.lt u hu
      have hne := hcon u hu
      exact mem_range.2 (early_colour hfH hrH hu (by omega) (by omega)).2.2
    have := card_le_card hsub
    rw [card_range] at this
    omega
  obtain ⟨u₀, hu₀, hbu₀⟩ := hlast
  refine pj_arith hm hN1 (blockCard β H) ?_ ?_
  · have hsum := card_eq_sum_card_fiberwise (s := range H.length) (t := range m)
      (f := bidx β H) fun u hu => mem_coe.2 (mem_range.2 (hfH.lt u (mem_range.1 hu)))
    rw [card_range] at hsum
    have e : ∑ t ∈ range m, blockCard β H t = H.length := hsum.symm
    omega
  · intro i him
    have hA := rriAlg_isProper β ρ m i N
    obtain ⟨p₂, hstop₂, hK₂⟩ := hF _ hA
    have hfH' : PJForm β ρ m (adv.hist (rriAlg β ρ m i N) p₂) := hadv _ hA p₂
    have hrH' := adv.isRunOf_hist (rriAlg β ρ m i N) p₂
    have hlenH' := hN _ hA p₂
    have hcol' := h3 _ hA p₂ hstop₂
    have hagree := plays_agree (adv := adv) (A := rriAlg β ρ m i N) (A' := rriAlg β ρ m m N)
      (Pr := fun g => β g ≤ i) (fun g s hg => rriAlg_step_eq hg (by omega)) (max p₁ p₂)
    have hH : adv.hist (rriAlg β ρ m m N) (max p₁ p₂) = H := by
      rw [← hHdef]
      exact hist_of_stop (hHdef ▸ hstop₁) _ (le_max_left _ _)
    have hH' := hist_of_stop hstop₂ _ (le_max_right p₁ p₂)
    generalize hH'def : adv.hist (rriAlg β ρ m i N) p₂ = H' at *
    obtain ⟨n, hnH, hnH', htake, hbn⟩ : ∃ n, n < H.length ∧ n < H'.length ∧
        H'.take n = H.take n ∧ i < bidx β H n := by
      rcases hagree with heq | ⟨p', hp', heq, s, hmove, hnP⟩
      · rw [hH, hH'] at heq
        exact ⟨u₀, hu₀, heq ▸ hu₀, by rw [heq], by omega⟩
      · have hlt : p' + 1 ≤ max p₁ p₂ := hp'
        have e1 := hist_succ_some hmove
        have e1' := hist_succ_some (heq ▸ hmove)
        have t1 := hist_take (adv := adv) (A := rriAlg β ρ m i N) hlt
        have t1' := hist_take (adv := adv) (A := rriAlg β ρ m m N) hlt
        rw [hH', e1] at t1
        rw [hH, e1', ← heq] at t1'
        generalize adv.hist (rriAlg β ρ m i N) p' = g at *
        have l1 := congrArg List.length t1
        have l1' := congrArg List.length t1'
        simp only [List.length_take, List.length_append, List.length_singleton] at l1 l1'
        have k1 : H'.take g.length = g := by
          have := congrArg (List.take g.length) t1
          rwa [List.take_take, List.length_append, List.length_singleton,
            min_eq_left (Nat.le_succ _), List.take_append_of_le_length le_rfl,
            List.take_length] at this
        have k1' : H.take g.length = g := by
          have := congrArg (List.take g.length) t1'
          rwa [List.take_take, List.length_append, List.length_singleton,
            min_eq_left (Nat.le_succ _), List.take_append_of_le_length le_rfl,
            List.take_length] at this
        refine ⟨g.length, by omega, by omega, k1.trans k1'.symm, ?_⟩
        change i < β (H.take g.length)
        rw [k1']
        exact not_le.1 hnP
    refine ⟨(Rset β ρ i (H.take n)).card, rr_bound hfH hrH (by omega) him hnH hbn, ?_⟩
    by_contra hcon
    have hbn' : i < bidx β H' n := by
      change i < β (H'.take n)
      rw [htake]
      exact hbn
    have C : HubCtx β ρ m i N H' n :=
      ⟨hfH', hrH', him, hnH', hbn', hcol', hlenH', by rw [htake]; omega⟩
    have := hub_card_usedColours_le C
    omega

/-- **"Forcing is then automatic."**  A partial-join level every play of which ends with a vertex
in the last block forces `m` colours: that vertex sees the `m - 1` distinct colours of the
reserves of the earlier blocks. -/
theorem pj_forces {adv : Adversary} (hm : 1 ≤ m) (hadv : IsPJAdv β ρ m adv)
    (hfin : ∀ A : OnlineAlg, A.IsProper → ∃ p, adv.StopsAt A p ∧
      ∃ u, u < (adv.hist A p).length ∧ bidx β (adv.hist A p) u = m - 1) :
    adv.Forces m := by
  intro A hA
  obtain ⟨p, hstop, u, hu, hbu⟩ := hfin A hA
  refine ⟨p, hstop, ?_⟩
  have hf := hadv A hA p
  have hr := adv.isRunOf_hist A p
  generalize adv.hist A p = H at *
  choose! w hw using fun t (ht : t < m - 1) => hf.cover u hu t (by omega)
  have hwlen : ∀ t, t < m - 1 → w t < H.length := fun t ht =>
    (hf.nbr u hu _ (hw t ht).1).1.trans hu
  have hne : ∀ t t', t < t' → t' < m - 1 → colourAt H (w t') ≠ colourAt H (w t) := by
    intro t t' htt' ht'
    obtain ⟨x, hx, hxb⟩ := hf.cover (w t') (hwlen t' ht') t (by rw [(hw t' ht').2]; exact htt')
    have e : colourAt H x = colourAt H (w t) :=
      hf.sameCol (hwlen t' ht') hu hx (hw t (by omega)).1 (hxb.trans (hw t (by omega)).2.symm)
    rw [← e]
    exact colourAt_ne_of_isRunOf hA hr (hwlen t' ht') hx (hf.nbr _ (hwlen t' ht') x hx).1
  have hneu : ∀ t, t < m - 1 → colourAt H u ≠ colourAt H (w t) := fun t ht =>
    colourAt_ne_of_isRunOf hA hr hu (hw t ht).1 (hf.nbr u hu _ (hw t ht).1).1
  rw [← card_range m]
  refine card_le_card_of_injOn
    (fun t => if t < m - 1 then colourAt H (w t) else colourAt H u) ?_ ?_
  · intro t _
    by_cases ht : t < m - 1
    · simp only [ht, ↓reduceIte]
      exact mem_coe.2 (colourAt_mem_usedColours (hwlen t ht))
    · simp only [ht, ↓reduceIte]
      exact mem_coe.2 (colourAt_mem_usedColours hu)
  · intro t ht t' ht' heq
    rw [mem_coe, mem_range] at ht ht'
    by_cases h1 : t < m - 1 <;> by_cases h2 : t' < m - 1 <;>
      simp only [h1, h2, ↓reduceIte] at heq
    · rcases lt_trichotomy t t' with h | h | h
      · exact absurd heq.symm (hne t t' h h2)
      · exact h
      · exact absurd heq (hne t' t h h1)
    · exact absurd heq.symm (hneu t h1)
    · exact absurd heq (hneu t' h2)
    · omega

end Plays

end OnlineColouring.AppBD
