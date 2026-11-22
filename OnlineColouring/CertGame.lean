module

public import OnlineColouring.AdvBasic

/-!
# Forcing positions and the transfer lemma (for the computer-assisted upper bounds on `N_k(c)`)

Proposition B.4 (exact values) of Appendix B.  The upper bounds `N_k(c) ≤ 2c - k` are certified
by adversary strategies stored as DAGs of positions.  This file contains the mathematics behind
the certificates; nothing here is computed.  The checker is in `CertCheck.lean`, and the
proposition is `Cert.prop_small` (`CertNk.lean`).

* `KCol k h f`: `f` is a proper `k`-colouring of the graph presented in the history `h`
  (`KCol.colorable`: then `h.graph` is `k`-colourable).
* `Force k C n h` ("from the position `h` the adversary forces `C` colours within `n` further
  vertices on a `k`-colourable graph"): either `h` already has `C` colours and a `k`-colourable
  graph, or `n > 0` and there is a neighbour set `s` such that for *every* colour `x` that a proper
  algorithm may give the new vertex (every `x ∉ nbrColours h s`, not only the colours `1..m+1`),
  the position `h ++ [(s, x)]` is forcing within `n - 1` vertices.  A position is a history; its
  colouring need not be proper.
* `nkLE_of_force`: `Force k C n []` implies `NkLE k C n`, i.e. `N_k(C) ≤ n` in the sense of
  Definition 4.2 (`AdvBasic.lean`): the adversary that follows the forcing positions forces `C`
  colours, presents at most `n` vertices in every play and lands in the `k`-colourable graphs.
* `Dom k A B p σ` (the position `A` dominates the position `B`): `p` maps the vertices of `B`
  injectively to vertices of `A`, `σ` is a bijection from the colours of `B` to the colours of `A`
  compatible with `p`, and every proper `k`-colouring of `B`, transported by `p`, extends to a
  proper `k`-colouring of `A`.
* `Force.transfer` (the transfer lemma of the certificate checker): if `A` dominates `B` and `B`
  is forcing within `n` vertices, so is `A`.  `Force.recolour`: the name of a new colour does not
  matter.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

open Finset

/-! ### Proper colourings of a history -/

/-- `f` is a proper `k`-colouring of the graph presented in the history `h`. -/
def KCol (k : ℕ) (h : History) (f : ℕ → ℕ) : Prop :=
  (∀ i < h.length, f i < k) ∧
    ∀ (v : ℕ) (hv : v < h.length), ∀ u ∈ h[v].1, u < v → f u ≠ f v

theorem KCol.colorable {k : ℕ} {h : History} {f : ℕ → ℕ} (hf : KCol k h f) :
    h.graph.Colorable k := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => (⟨f v, hf.1 v v.2⟩ : Fin k)) ?_⟩
  intro u v huv heq
  rw [History.graph_adj] at huv
  have heq' : f u = f v := congrArg Fin.val heq
  rcases huv with ⟨hlt, hmem⟩ | ⟨hlt, hmem⟩
  · exact hf.2 v v.2 u (by simpa using hmem) hlt heq'
  · exact hf.2 u u.2 v (by simpa using hmem) hlt heq'.symm

theorem KCol.of_snoc {k : ℕ} {h : History} {e : Finset ℕ × ℕ} {f : ℕ → ℕ}
    (hf : KCol k (h ++ [e]) f) : KCol k h f := by
  refine ⟨fun i hi => hf.1 i (by simp; omega), fun v hv u hu huv => ?_⟩
  have hv' : v < (h ++ [e]).length := by simp; omega
  refine hf.2 v hv' u ?_ huv
  rwa [List.getElem_append_left hv]

theorem KCol.snoc {k : ℕ} {h : History} {g : ℕ → ℕ} (hg : KCol k h g) {c : ℕ} (hc : c < k)
    (s : Finset ℕ) (x : ℕ) (hs : ∀ u ∈ s, u < h.length → g u ≠ c) :
    KCol k (h ++ [(s, x)]) (Function.update g h.length c) := by
  constructor
  · intro i hi
    rcases eq_or_ne i h.length with rfl | hne
    · simpa using hc
    · rw [Function.update_of_ne hne]
      exact hg.1 i (by simp at hi; omega)
  · intro v hv u hu huv
    rcases eq_or_ne v h.length with rfl | hne
    · rw [Function.update_self, Function.update_of_ne (Nat.ne_of_lt huv)]
      simp only [List.getElem_concat_length] at hu
      exact hs u hu huv
    · have hv' : v < h.length := by simp at hv; omega
      rw [List.getElem_append_left hv'] at hu
      rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
      exact hg.2 v hv' u hu huv

/-! ### Colours of a history -/

theorem usedColours_snoc (h : History) (s : Finset ℕ) (x : ℕ) :
    usedColours (h ++ [(s, x)]) = insert x (usedColours h) := by
  ext c
  simp only [usedColours, List.map_append, List.map_cons, List.map_nil, List.mem_toFinset,
    List.mem_append, List.mem_singleton, mem_insert]
  tauto

theorem colourAt_snoc_lt {h : History} {e : Finset ℕ × ℕ} {i : ℕ} (hi : i < h.length) :
    colourAt (h ++ [e]) i = colourAt h i := by
  simp [colourAt, List.getElem?_append_left hi]

theorem colourAt_snoc_length (h : History) (s : Finset ℕ) (x : ℕ) :
    colourAt (h ++ [(s, x)]) h.length = x := by
  simp [colourAt]

theorem colourAt_mem_usedColours {h : History} {i : ℕ} (hi : i < h.length) :
    colourAt h i ∈ usedColours h := by
  rw [colourAt_eq_getElem hi]
  simp only [usedColours, List.mem_toFinset, List.mem_map]
  exact ⟨h[i], List.getElem_mem hi, rfl⟩

theorem exists_colourAt_of_mem_usedColours {h : History} {c : ℕ} (hc : c ∈ usedColours h) :
    ∃ i < h.length, colourAt h i = c := by
  simp only [usedColours, List.mem_toFinset, List.mem_map] at hc
  obtain ⟨e, he, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ⟨i, hi, colourAt_eq_getElem hi⟩

theorem nbrColours_subset_usedColours (h : History) (s : Finset ℕ) :
    nbrColours h s ⊆ usedColours h := by
  intro c hc
  simp only [nbrColours, mem_image, mem_filter] at hc
  obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hc
  exact colourAt_mem_usedColours hi

/-! ### Forcing positions -/

/-- The adversary may stop at `h`: at least `C` colours are in use and the graph is
`k`-colourable. -/
def Stop (k C : ℕ) (h : History) : Prop :=
  C ≤ (usedColours h).card ∧ ∃ f, KCol k h f

/-- From the position `h` the adversary forces `C` colours within `n` further vertices, on a
`k`-colourable graph. -/
def Force (k C : ℕ) : ℕ → History → Prop
  | 0, h => Stop k C h
  | n + 1, h =>
    Stop k C h ∨ ∃ s : Finset ℕ, ∀ x, x ∉ nbrColours h s → Force k C n (h ++ [(s, x)])

variable {k C : ℕ}

theorem Force.succ : ∀ {n : ℕ} {h : History}, Force k C n h → Force k C (n + 1) h
  | 0, _, hF => Or.inl hF
  | _ + 1, _, hF => by
    rcases hF with hS | ⟨s, hs⟩
    · exact Or.inl hS
    · exact Or.inr ⟨s, fun x hx => (hs x hx).succ⟩

theorem Force.mono {n n' : ℕ} {h : History} (hF : Force k C n h) (hn : n ≤ n') :
    Force k C n' h := by
  induction hn with
  | refl => exact hF
  | step _ ih => exact ih.succ

theorem Force.of_stop {n : ℕ} {h : History} (hS : Stop k C h) : Force k C n h :=
  Force.mono (n := 0) hS (Nat.zero_le n)

/-! ### From a forcing position to an adversary -/

/-- The least `m` with `Force k C m h` (`0` if there is none). -/
noncomputable def rank (k C : ℕ) (h : History) : ℕ := sInf {m | Force k C m h}

/-- A neighbour set that lowers the rank. -/
noncomputable def sel (k C : ℕ) (h : History) : Finset ℕ :=
  Classical.epsilon fun s : Finset ℕ =>
    ∀ x, x ∉ nbrColours h s → Force k C (rank k C h - 1) (h ++ [(s, x)])

open Classical in
/-- The adversary that follows the forcing positions: it stops when the position permits it (or
is not forcing), and otherwise presents a vertex that lowers the rank. -/
noncomputable def adv (k C : ℕ) : Adversary :=
  ⟨fun h => if Stop k C h ∨ ¬ ∃ m, Force k C m h then none else some (sel k C h)⟩

theorem sel_spec {h : History} {m : ℕ} (hS : ¬ Stop k C h) (hm : Force k C m h) :
    (∀ x, x ∉ nbrColours h (sel k C h) →
      Force k C (rank k C h - 1) (h ++ [(sel k C h, x)])) ∧ 1 ≤ rank k C h ∧ rank k C h ≤ m := by
  have hne : {m | Force k C m h}.Nonempty := ⟨m, hm⟩
  have hr : Force k C (rank k C h) h := Nat.sInf_mem hne
  have hle : rank k C h ≤ m := Nat.sInf_le hm
  obtain ⟨r, hr'⟩ : ∃ r, rank k C h = r + 1 := by
    rcases Nat.eq_zero_or_pos (rank k C h) with h0 | hpos
    · rw [h0] at hr
      exact absurd hr hS
    · exact ⟨rank k C h - 1, by omega⟩
  refine ⟨?_, by omega, hle⟩
  rw [hr'] at hr
  rcases hr with hS' | hex
  · exact absurd hS' hS
  · have := Classical.epsilon_spec (p := fun s : Finset ℕ =>
      ∀ x, x ∉ nbrColours h s → Force k C (rank k C h - 1) (h ++ [(s, x)]))
      (by simpa [hr'] using hex)
    exact this

open Classical in
theorem adv_move_of_stop {h : History} (hS : Stop k C h) : (adv k C).move h = none := by
  change (if Stop k C h ∨ ¬ ∃ m, Force k C m h then none else some (sel k C h)) = none
  simp [hS]

open Classical in
theorem adv_move_of_not_stop {h : History} {m : ℕ} (hS : ¬ Stop k C h) (hm : Force k C m h) :
    (adv k C).move h = some (sel k C h) := by
  have hex : ∃ m, Force k C m h := ⟨m, hm⟩
  change (if Stop k C h ∨ ¬ ∃ m, Force k C m h then none else some (sel k C h)) = _
  simp [hS, hex]

theorem stop_of_adv_move {h : History} {m : ℕ} (hm : Force k C m h)
    (hmv : (adv k C).move h = none) : Stop k C h := by
  by_contra hS
  rw [adv_move_of_not_stop hS hm] at hmv
  exact absurd hmv (by simp)

theorem adv_hist_succ_of_stop {A : OnlineAlg} {p : ℕ}
    (hS : Stop k C ((adv k C).hist A p)) : (adv k C).hist A (p + 1) = (adv k C).hist A p := by
  simp only [Adversary.hist, adv_move_of_stop hS]

theorem adv_hist_succ_of_not_stop {A : OnlineAlg} {p m : ℕ}
    (hS : ¬ Stop k C ((adv k C).hist A p)) (hm : Force k C m ((adv k C).hist A p)) :
    (adv k C).hist A (p + 1) = (adv k C).hist A p ++
      [(sel k C ((adv k C).hist A p),
        A.step ((adv k C).hist A p) (sel k C ((adv k C).hist A p)))] := by
  simp only [Adversary.hist, adv_move_of_not_stop hS hm]

theorem adv_invariant {n : ℕ} (hF : Force k C n []) {A : OnlineAlg} (hA : A.IsProper) (p : ℕ) :
    ∃ m, Force k C m ((adv k C).hist A p) ∧ ((adv k C).hist A p).length + m ≤ n ∧
      (Stop k C ((adv k C).hist A p) ∨ ((adv k C).hist A p).length = p) := by
  induction p with
  | zero => exact ⟨n, hF, by simp [Adversary.hist], Or.inr rfl⟩
  | succ p ih =>
    obtain ⟨m, hm, hlen, hor⟩ := ih
    by_cases hS : Stop k C ((adv k C).hist A p)
    · rw [adv_hist_succ_of_stop hS]
      exact ⟨m, hm, hlen, Or.inl hS⟩
    · obtain ⟨hsel, hr1, hrm⟩ := sel_spec hS hm
      rw [adv_hist_succ_of_not_stop hS hm]
      refine ⟨rank k C ((adv k C).hist A p) - 1,
        hsel _ ((A.isProper_iff.1 hA) _ _), ?_, Or.inr ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · rcases hor with hS' | hl
        · exact absurd hS' hS
        · simp [hl]

/-- **From forcing positions to `N_k(C)`.**  If the empty position is forcing within `n` vertices,
then `N_k(C) ≤ n`. -/
theorem nkLE_of_force {n : ℕ} (hF : Force k C n []) : NkLE k C n := by
  refine ⟨adv k C, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨m, hm, hlen, hor⟩ := adv_invariant hF hA n
    have hS : Stop k C ((adv k C).hist A n) := by
      rcases hor with hS | hl
      · exact hS
      · have : m = 0 := by omega
        subst this
        exact hm
    exact ⟨n, adv_move_of_stop hS, hS.1⟩
  · intro A hA p
    obtain ⟨m, -, hlen, -⟩ := adv_invariant hF hA p
    omega
  · intro A hA p hstop
    obtain ⟨m, hm, -, -⟩ := adv_invariant hF hA p
    have hS : Stop k C ((adv k C).hist A p) := stop_of_adv_move hm hstop
    obtain ⟨f, hf⟩ := hS.2
    exact hf.colorable

/-! ### Domination and the transfer lemma -/

/-- The position `A` dominates the position `B` via the vertex map `p` and the colour map `σ`. -/
structure Dom (k : ℕ) (A B : History) (p σ : ℕ → ℕ) : Prop where
  p_lt : ∀ i < B.length, p i < A.length
  p_inj : ∀ i < B.length, ∀ j < B.length, p i = p j → i = j
  σ_inj : ∀ c ∈ usedColours B, ∀ c' ∈ usedColours B, σ c = σ c' → c = c'
  σ_img : (usedColours B).image σ = usedColours A
  col : ∀ i < B.length, colourAt A (p i) = σ (colourAt B i)
  ext : ∀ f, KCol k B f → ∃ g, KCol k A g ∧ ∀ i < B.length, g (p i) = f i

theorem Dom.stop {A B : History} {p σ : ℕ → ℕ} (hD : Dom k A B p σ) (hS : Stop k C B) :
    Stop k C A := by
  obtain ⟨hc, f, hf⟩ := hS
  obtain ⟨g, hg, -⟩ := hD.ext f hf
  refine ⟨?_, g, hg⟩
  rw [← hD.σ_img, card_image_of_injOn (fun c hc c' hc' h => hD.σ_inj c hc c' hc' h)]
  exact hc

theorem Dom.congr {A B : History} {p σ σ' : ℕ → ℕ} (hD : Dom k A B p σ)
    (h : ∀ c ∈ usedColours B, σ' c = σ c) : Dom k A B p σ' where
  p_lt := hD.p_lt
  p_inj := hD.p_inj
  σ_inj c hc c' hc' he := hD.σ_inj c hc c' hc' (by rwa [h c hc, h c' hc'] at he)
  σ_img := by rw [← hD.σ_img]; exact image_congr fun c hc => h c hc
  col i hi := by rw [hD.col i hi, h _ (colourAt_mem_usedColours hi)]
  ext := hD.ext

theorem Dom.nbrColours {A B : History} {p σ : ℕ → ℕ} (hD : Dom k A B p σ) (s : Finset ℕ) :
    nbrColours A ((s.filter (· < B.length)).image p) = (nbrColours B s).image σ := by
  ext c
  simp only [OnlineColouring.nbrColours, mem_image, mem_filter]
  constructor
  · rintro ⟨_, ⟨⟨i, ⟨his, hi⟩, rfl⟩, -⟩, rfl⟩
    exact ⟨colourAt B i, ⟨i, ⟨his, hi⟩, rfl⟩, (hD.col i hi).symm⟩
  · rintro ⟨_, ⟨i, ⟨his, hi⟩, rfl⟩, rfl⟩
    exact ⟨p i, ⟨⟨i, ⟨his, hi⟩, rfl⟩, hD.p_lt i hi⟩, hD.col i hi⟩

/-- Domination survives a move: the adversary presents `s` at `B` and the image of `s` at `A`,
and the answers correspond under `σ`. -/
theorem Dom.snoc {A B : History} {p σ : ℕ → ℕ} (hD : Dom k A B p σ) (s : Finset ℕ) (x : ℕ)
    (hx : ∀ c ∈ usedColours B, σ c = σ x → c = x) :
    Dom k (A ++ [((s.filter (· < B.length)).image p, σ x)]) (B ++ [(s, x)])
      (Function.update p B.length A.length) σ where
  p_lt i hi := by
    rcases eq_or_ne i B.length with rfl | hne
    · simp
    · rw [Function.update_of_ne hne]
      have := hD.p_lt i (by simp at hi; omega)
      simp; omega
  p_inj i hi j hj hij := by
    simp only [List.length_append, List.length_singleton] at hi hj
    rcases eq_or_ne i B.length with rfl | hne <;> rcases eq_or_ne j B.length with rfl | hne'
    · rfl
    · rw [Function.update_self, Function.update_of_ne hne'] at hij
      have := hD.p_lt j (by omega)
      omega
    · rw [Function.update_self, Function.update_of_ne hne] at hij
      have := hD.p_lt i (by omega)
      omega
    · rw [Function.update_of_ne hne, Function.update_of_ne hne'] at hij
      exact hD.p_inj i (by omega) j (by omega) hij
  σ_inj c hc c' hc' he := by
    rw [usedColours_snoc, mem_insert] at hc hc'
    rcases hc with rfl | hc <;> rcases hc' with rfl | hc'
    · rfl
    · exact (hx c' hc' he.symm).symm
    · exact hx c hc he
    · exact hD.σ_inj c hc c' hc' he
  σ_img := by rw [usedColours_snoc, usedColours_snoc, image_insert, hD.σ_img]
  col i hi := by
    simp only [List.length_append, List.length_singleton] at hi
    rcases eq_or_ne i B.length with rfl | hne
    · rw [Function.update_self, colourAt_snoc_length, colourAt_snoc_length]
    · have hi' : i < B.length := by omega
      rw [Function.update_of_ne hne, colourAt_snoc_lt (hD.p_lt i hi'), colourAt_snoc_lt hi']
      exact hD.col i hi'
  ext f hf := by
    obtain ⟨g, hg, hgf⟩ := hD.ext f hf.of_snoc
    have hBl : B.length < (B ++ [(s, x)]).length := by simp
    refine ⟨Function.update g A.length (f B.length), hg.snoc (hf.1 _ hBl) _ _ ?_, ?_⟩
    · intro u hu _
      simp only [mem_image, mem_filter] at hu
      obtain ⟨i, ⟨his, hi⟩, rfl⟩ := hu
      rw [hgf i hi]
      exact hf.2 B.length hBl i (by simpa using his) hi
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases eq_or_ne i B.length with rfl | hne
      · rw [Function.update_self, Function.update_self]
      · have hi' : i < B.length := by omega
        rw [Function.update_of_ne hne, Function.update_of_ne (Nat.ne_of_lt (hD.p_lt i hi'))]
        exact hgf i hi'

/-- **Transfer lemma.**  If `A` dominates `B` and the adversary forces `C` colours from `B` within
`n` further vertices, it does so from `A`. -/
theorem Force.transfer : ∀ {n : ℕ} {A B : History} {p σ : ℕ → ℕ}, Dom k A B p σ →
    Force k C n B → Force k C n A
  | 0, _, _, _, _, hD, hF => hD.stop hF
  | n + 1, A, B, p, σ, hD, hF => by
    rcases hF with hS | ⟨s, hs⟩
    · exact Or.inl (hD.stop hS)
    · refine Or.inr ⟨(s.filter (· < B.length)).image p, fun y hy => ?_⟩
      rw [hD.nbrColours s] at hy
      by_cases hyu : y ∈ usedColours A
      · rw [← hD.σ_img] at hyu
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hyu
        have hxn : x ∉ nbrColours B s := fun h => hy (mem_image_of_mem σ h)
        exact Force.transfer (hD.snoc s x fun c hc he => hD.σ_inj c hc x hx he) (hs x hxn)
      · obtain ⟨x, hx⟩ := (usedColours B).exists_notMem
        have hxn : x ∉ nbrColours B s := fun h => hx (nbrColours_subset_usedColours B s h)
        have hne : ∀ c ∈ usedColours B, c ≠ x := fun c hc h => hx (h ▸ hc)
        have hD' : Dom k A B p (Function.update σ x y) :=
          hD.congr fun c hc => Function.update_of_ne (hne c hc) _ _
        have hsn := hD'.snoc s x fun c hc he => by
          exfalso
          apply hyu
          rw [Function.update_self, Function.update_of_ne (hne c hc)] at he
          rw [← hD.σ_img, ← he]
          exact mem_image_of_mem σ hc
        rw [Function.update_self] at hsn
        exact Force.transfer hsn (hs x hxn)

theorem Dom.refl_of_fix {B : History} {σ : ℕ → ℕ} (h : ∀ c ∈ usedColours B, σ c = c) :
    Dom k B B id σ where
  p_lt _ hi := hi
  p_inj _ _ _ _ h := h
  σ_inj c hc c' hc' he := by rwa [h c hc, h c' hc'] at he
  σ_img := by
    conv_rhs => rw [← image_id (s := usedColours B)]
    exact image_congr fun c hc => h c hc
  col i hi := (h _ (colourAt_mem_usedColours hi)).symm
  ext f hf := ⟨f, hf, fun _ _ => rfl⟩

/-- The name of a new colour does not matter. -/
theorem Force.recolour {n : ℕ} {B : History} {s : Finset ℕ} {x x' : ℕ}
    (hs : ∀ u ∈ s, u < B.length) (hx : x ∉ usedColours B) (hx' : x' ∉ usedColours B)
    (hF : Force k C n (B ++ [(s, x)])) : Force k C n (B ++ [(s, x')]) := by
  have hne : ∀ c ∈ usedColours B, c ≠ x := fun c hc h => hx (h ▸ hc)
  have hD : Dom k B B id (Function.update id x x') :=
    Dom.refl_of_fix fun c hc => Function.update_of_ne (hne c hc) _ _
  have hsn := hD.snoc s x fun c hc he => by
    exfalso
    rw [Function.update_self, Function.update_of_ne (hne c hc)] at he
    exact hx' (he ▸ hc)
  rw [Function.update_self, filter_true_of_mem hs, image_id] at hsn
  exact Force.transfer hsn hF

end Cert

end OnlineColouring
