module

public import OnlineColouring.DetTower
public import OnlineColouring.PaperFirstFit
public import OnlineColouring.LogStarGeneric

/-!
# Corollary 9.6: the value of towers

Corollary 9.6: *Fix `k ≥ 3`, and let `V_k(n)` be the largest `K` such that some adversary of size
at most `n` forces `K` colours and lands in the `k`-colourable towers. There is `n_k` such that
for every `n ≥ n_k`, `n^{1/(lg* n + 3)} ≤ V_k(n) ≤ n^{1/(lg* n - lg* k - 3)}`.  Equivalently,
`V_k(n) = n^{1/(lg* n + c)}` for a real number `c = c(k,n)` with `-lg* k - 3 ≤ c ≤ 3`, which may
be negative.*

## Formalization

* `Det.IsColTower k n G`: the ordered graph `G` on `Fin n` is `k`-colourable and a tower in the
  sense of Definition 4.7 (`IsPaddedTower m j G` for some `m`, `j`: an initial segment of a full
  `j`-level tower over `K_m`, presented subtree by subtree, possibly followed by isolated
  vertices).
* `Det.TowerForces k n K`: some adversary forces `K` colours, has size at most `n`, and lands in
  the `k`-colourable towers (Definition 4.2: the final graph of every play is one).
* `Det.towerValue k n` is `V_k(n)`: the largest such `K` (`towerValue_le`: it is at most `n`;
  `towerForces_towerValue`: the maximum is attained as soon as some such adversary exists).
* `Det.TowerForcesAll` asks that every graph presented during a play (after any number of rounds)
  is a `k`-colourable tower, not only the final one.  This gives the same value
  (`Det.towerForcesAll_iff`, `Det.towerValue_eq_all`), because initial segments of towers are
  towers (`Det.isPaddedTower_of_initial`, `Det.isColTower_of_prefix`).
* `Det.value_of_towers` (**Corollary 9.6**, first form): for `k ≥ 3` there is `n₀` such that for
  all `n ≥ n₀`, `n^{1/(lg* n + 3)} ≤ towerValue k n ≤ n^{1/(lg* n - lg* k - 3)}`.
* `Det.value_of_towers_exponent` (**Corollary 9.6**, second form): for `n ≥ n₀` there is a real
  `c` with `-lg* k - 3 ≤ c ≤ 3`, `lg* n + c > 0` and `towerValue k n = n^{1/(lg* n + c)}`.

Upper bound (`Det.towerForces_le_rpow`): play First-Fit against the adversary (as
`cleanAlg OnlineAlg.firstFit`); its play is a run of First-Fit on an honest input
(`Det.exists_input_of_hist`), the online First-Fit is the First-Fit of the ordered graph
(`Det.run_firstFit_eq`), and Theorem 1.5 (`exists_threshold_le_rpow`) bounds its colours.

The same argument with the first sentence of Theorem 1.5 gives `Det.forces_le_card_labelPoset`:
an adversary all of whose final graphs are `k`-colourable `j`-level towers forces at most
`|P_j(k)|` colours.  For `k = 3` and `j = 1` this is the sentence after the proof of Theorem 1.2,
"no one-level tower over a clique can force more" than `7` colours
(`Det.forces_le_seven_of_one_level`).

Lower bound (`Det.towerForces_rpow` for `n ≥ 2^406`, and `Det.towerForces_rpow_of_four_le` for
`k ≥ 4`, `n ≥ 2^201`, with exponent `1/(lg* n + 1)`): the wirings of `R_j(m)` are full towers
(`Det.uInputE_isFullTower`), so the per-algorithm form of Theorem 8.5 (ii) lands in the towers;
the parameters of the proof of Theorem 1.1 (`Rjm.logStar_three_large`, with padding by isolated
vertices, which keeps towers) give, for every algorithm, a `3`-colourable tower on `n` vertices
with `⌈n^{1/(lg* n + 3)}⌉` colours, and determinacy (`Det.exists_presents`) turns this into one
adversary.  The paper's proof uses the adversary of Theorem 8.5 (ii) directly; that form is
`Expl.adv_forces_rpow` (`ExplCor.lean`).
-/

@[expose] public section

namespace OnlineColouring

namespace Det

open Finset

/-- Every realization of the wiring is a tower in the sense of Definition 4.7. -/
theorem uInputE_isPaddedTower {m j A : ℕ} (hA : 0 < A) (ω : EΩ m j A) :
    IsPaddedTower m j (uInputE hA ω).graph := by
  have : Finite (uInputE hA ω).toOrdGraph.V := inferInstanceAs (Finite (Fin _))
  exact (uInputE_isFullTower hA ω).isPaddedTower

/-! ### The online First-Fit is the First-Fit of the ordered graph -/

theorem runCol_firstFit_eq {n : ℕ} (I : OnlineInput n) :
    ∀ i (hi : i < n), runCol OnlineAlg.firstFit I.seq i = firstFit I.graph ⟨i, hi⟩ :=
  fun i hi => Paper.run_firstFit_eq I ⟨i, hi⟩

/-- The colouring of the online First-Fit on `I` is the First-Fit colouring of the ordered graph
of `I` (`Paper.run_firstFit_eq`, as an equality of functions). -/
theorem run_firstFit_eq {n : ℕ} (I : OnlineInput n) :
    I.run OnlineAlg.firstFit = firstFit I.graph :=
  funext (Paper.run_firstFit_eq I)

theorem cost_firstFit_eq {n : ℕ} (I : OnlineInput n) :
    I.cost OnlineAlg.firstFit = (Set.range (firstFit I.graph)).ncard :=
  Paper.cost_firstFit_eq I

/-! ### Tower adversaries and their value -/

/-- The class of `k`-colourable towers (Definition 4.7): `G`, ordered by `Fin n`, is
`k`-colourable and is an initial segment of a full `j`-level tower over `K_m`, possibly followed
by isolated vertices, for some `m` and `j`. -/
def IsColTower (k n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.Colorable k ∧ ∃ m j, IsPaddedTower m j G

/-- Some adversary of size at most `n` forces `K` colours and lands in the `k`-colourable
towers. -/
def TowerForces (k n K : ℕ) : Prop :=
  ∃ adv : Adversary, adv.Forces K ∧ adv.SizeLE n ∧ adv.LandsIn (IsColTower k)

/-- `V_k(n)` of Corollary 9.6: the largest `K` such that some adversary of size at most `n` forces
`K` colours and lands in the `k`-colourable towers. -/
noncomputable def towerValue (k n : ℕ) : ℕ := sSup {K | TowerForces k n K}

theorem IsColTower.mono {k k' n : ℕ} {G : SimpleGraph (Fin n)} (h : IsColTower k n G)
    (hk : k ≤ k') : IsColTower k' n G :=
  ⟨h.1.mono hk, h.2⟩

theorem TowerForces.mono_k {k k' n K : ℕ} (h : TowerForces k n K) (hk : k ≤ k') :
    TowerForces k' n K := by
  obtain ⟨adv, hF, hS, hL⟩ := h
  exact ⟨adv, hF, hS, fun A hA p hp => (hL A hA p hp).mono hk⟩

/-- No adversary of size at most `n` forces more than `n` colours. -/
theorem TowerForces.le {k n K : ℕ} (h : TowerForces k n K) : K ≤ n := by
  obtain ⟨adv, hF, hS, -⟩ := h
  obtain ⟨p, -, hK⟩ := hF _ OnlineAlg.firstFit_isProper
  exact hK.trans ((List.toFinset_card_le _).trans
    ((List.length_map (f := Prod.snd) (as := adv.hist _ p)).le.trans
      (hS _ OnlineAlg.firstFit_isProper p)))

theorem bddAbove_towerForces (k n : ℕ) : BddAbove {K | TowerForces k n K} :=
  ⟨n, fun _ h => TowerForces.le h⟩

theorem le_towerValue {k n K : ℕ} (h : TowerForces k n K) : K ≤ towerValue k n :=
  le_csSup (bddAbove_towerForces k n) h

theorem towerValue_le (k n : ℕ) : towerValue k n ≤ n := by
  rcases Set.eq_empty_or_nonempty {K | TowerForces k n K} with h | h
  · unfold towerValue
    rw [h, csSup_empty]
    exact bot_le
  · exact csSup_le h fun _ hK => TowerForces.le hK

/-- The maximum is attained (as soon as some tower adversary exists). -/
theorem towerForces_towerValue {k n K : ℕ} (h : TowerForces k n K) :
    TowerForces k n (towerValue k n) :=
  Nat.sSup_mem ⟨K, h⟩ (bddAbove_towerForces k n)

/-! ### Every graph presented during a play is a tower -/

section Initial

variable {V V' : Type*} [LinearOrder V] [LinearOrder V']

/-- **Initial segments of towers are towers.**  If `f : V ↪o V'` embeds the ordered graph `H` as
an initial segment of the tower `H'`, then `H` is a tower. -/
theorem isPaddedTower_of_initial {m j : ℕ} {H : SimpleGraph V} {H' : SimpleGraph V'}
    (hH : IsPaddedTower m j H') (f : V ↪o V') (hf : IsLowerSet (Set.range f))
    (hadj : ∀ a b, H'.Adj (f a) (f b) ↔ H.Adj a b) : IsPaddedTower m j H := by
  obtain ⟨U', hlt, hiso, G, S, e, hfin, hT, hS, he⟩ := hH
  let S' : Set G.V := {g | ∃ (u : V) (hu : f u ∈ U'), ((e ⟨f u, hu⟩ : S) : G.V) = g}
  let F : {u : V // u ∈ f ⁻¹' U'} → {g : G.V // g ∈ S'} :=
    fun a => ⟨(e ⟨f a.1, a.2⟩ : S), a.1, a.2, rfl⟩
  have hinj : Function.Injective F := by
    intro a b hab
    have h0 : ((e ⟨f a.1, a.2⟩ : S) : G.V) = (e ⟨f b.1, b.2⟩ : S) :=
      congrArg (fun x : {g : G.V // g ∈ S'} => (x : G.V)) hab
    have h1 : (e ⟨f a.1, a.2⟩ : S) = e ⟨f b.1, b.2⟩ := Subtype.ext h0
    have h2 := e.injective h1
    exact Subtype.ext (f.injective (congrArg Subtype.val h2))
  have hsurj : Function.Surjective F := by
    rintro ⟨g, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  refine ⟨f ⁻¹' U', ?_, ?_, G, S', ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩, hfin, hT, ?_, ?_⟩
  · intro u hu v hv
    exact f.lt_iff_lt.1 (hlt (f u) hu (f v) hv)
  · intro v hv u h
    exact hiso (f v) hv (f u) ((hadj u v).2 h)
  · intro a b
    change G.G.Adj (e ⟨f a.1, a.2⟩ : S) (e ⟨f b.1, b.2⟩ : S) ↔ H.Adj a.1 b.1
    rw [← hadj]
    exact e.map_adj_iff (v := ⟨f a.1, a.2⟩) (w := ⟨f b.1, b.2⟩)
  · rintro g g' hle ⟨u, hu, rfl⟩
    have hgS : g' ∈ S := hS hle (e ⟨f u, hu⟩).2
    have hw : e.symm ⟨g', hgS⟩ ≤ ⟨f u, hu⟩ := by
      by_contra hcon
      have h1 := he (not_le.1 hcon)
      rw [RelIso.apply_symm_apply] at h1
      exact absurd hle (not_le.2 h1)
    obtain ⟨u', hu'⟩ : ((e.symm ⟨g', hgS⟩ : U') : V') ∈ Set.range f := hf hw ⟨u, rfl⟩
    have hmem : f u' ∈ U' := by
      rw [hu']
      exact (e.symm ⟨g', hgS⟩).2
    refine ⟨u', hmem, ?_⟩
    have h2 : (⟨f u', hmem⟩ : U') = e.symm ⟨g', hgS⟩ := Subtype.ext hu'
    rw [h2, RelIso.apply_symm_apply]
  · intro a b hab
    change ((e ⟨f a.1, a.2⟩ : S) : G.V) < (e ⟨f b.1, b.2⟩ : S)
    exact he (show (⟨f a.1, a.2⟩ : U') < ⟨f b.1, b.2⟩ from f.lt_iff_lt.2 hab)

end Initial

/-- The graph of a prefix of a history `h` that presents a `k`-colourable tower is a
`k`-colourable tower. -/
theorem isColTower_of_prefix {k : ℕ} {h' h : History} (hp : h' <+: h)
    (hc : IsColTower k h.length h.graph) : IsColTower k h'.length h'.graph := by
  have hle : h'.length ≤ h.length := hp.length_le
  have key : ∀ b : Fin h'.length, h.get (Fin.castLE hle b) = h'.get b := by
    intro b
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact (hp.getElem b.2).symm
  have hadj : ∀ a b : Fin h'.length,
      h.graph.Adj (Fin.castLEOrderEmb hle a) (Fin.castLEOrderEmb hle b) ↔ h'.graph.Adj a b := by
    intro a b
    rw [History.graph_adj, History.graph_adj]
    change (_ ∧ _ ∈ (h.get (Fin.castLE hle b)).1) ∨ (_ ∧ _ ∈ (h.get (Fin.castLE hle a)).1) ↔ _
    rw [key, key]
    rfl
  obtain ⟨hcol, m, j, hT⟩ := hc
  refine ⟨hcol.of_hom ⟨Fin.castLEOrderEmb hle, fun {a b} hab => (hadj a b).2 hab⟩, m, j,
    isPaddedTower_of_initial hT (Fin.castLEOrderEmb hle) ?_ hadj⟩
  intro a b hba ⟨x, hx⟩
  exact ⟨⟨b, lt_of_le_of_lt hba (hx ▸ x.2)⟩, rfl⟩

/-- Every graph that `adv` presents (after any number of rounds of any play) belongs to the
class `C`. -/
def PresentsOnly (adv : Adversary) (C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∀ p, C _ (adv.hist A p).graph

theorem PresentsOnly.landsIn {adv : Adversary} {C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop}
    (h : PresentsOnly adv C) : adv.LandsIn C := fun A hA p _ => h A hA p

/-- If all plays of `adv` are finite and its final graphs are `k`-colourable towers, then every
graph it presents is a `k`-colourable tower, because initial segments of towers are towers
(`isColTower_of_prefix`). -/
theorem presentsOnly_of_landsIn {adv : Adversary} {k K : ℕ} (hF : adv.Forces K)
    (hL : adv.LandsIn (IsColTower k)) : PresentsOnly adv (IsColTower k) := by
  intro A hA p
  obtain ⟨p₀, hstop, -⟩ := hF A hA
  rcases le_total p p₀ with h | h
  · exact isColTower_of_prefix (hist_prefix adv A h) (hL A hA p₀ hstop)
  · rw [hist_eq_of_stopsAt hstop p h]
    exact hL A hA p₀ hstop

/-- Some adversary of size at most `n` forces `K` colours, and every graph it presents is a
`k`-colourable tower. -/
def TowerForcesAll (k n K : ℕ) : Prop :=
  ∃ adv : Adversary, adv.Forces K ∧ adv.SizeLE n ∧ PresentsOnly adv (IsColTower k)

/-- `TowerForcesAll` and `TowerForces` agree: for an adversary that forces `K` colours it is the
same to ask that every graph presented during a play is a `k`-colourable tower or that the final
graph of every play is one. -/
theorem towerForcesAll_iff {k n K : ℕ} : TowerForcesAll k n K ↔ TowerForces k n K := by
  constructor
  · rintro ⟨adv, hF, hS, hP⟩
    exact ⟨adv, hF, hS, hP.landsIn⟩
  · rintro ⟨adv, hF, hS, hL⟩
    exact ⟨adv, hF, hS, presentsOnly_of_landsIn hF hL⟩

theorem towerValue_eq_all (k n : ℕ) : towerValue k n = sSup {K | TowerForcesAll k n K} := by
  unfold towerValue
  congr 1
  ext K
  exact towerForcesAll_iff.symm

/-! ### Upper bound: First-Fit -/

/-- Against an adversary that lands in the `k`-colourable towers, First-Fit uses the First-Fit
colours of a `k`-colourable tower; so the number `K` of colours forced is at most the number of
First-Fit colours of a `k`-colourable tower with at most `n` vertices. -/
theorem TowerForces.exists_tower {k n K : ℕ} (h : TowerForces k n K) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)), N ≤ n ∧ IsColTower k N G ∧
      K ≤ (Set.range (firstFit G)).ncard := by
  obtain ⟨adv, hF, hS, hL⟩ := h
  have hA := cleanAlg_isProper OnlineAlg.firstFit_isProper
  obtain ⟨p, hstop, hK⟩ := hF _ hA
  obtain ⟨I, hg, hcost⟩ := exists_input_of_hist adv OnlineAlg.firstFit p
  refine ⟨_, _, hS _ hA p, hL _ hA p hstop, ?_⟩
  rw [← hg, ← cost_firstFit_eq, hcost]
  exact hK

/-- **A ceiling for adversaries that land in towers** (Theorem 1.5, first sentence, for
adversaries).  If an adversary forces `K` colours and each of its final graphs is a
`k`-colourable `j`-level tower in the sense of Definition 4.7, then `K ≤ |P_j(k)|`: First-Fit,
played against the adversary, uses at most `|P_j(k)|` colours on the final graph. -/
theorem forces_le_card_labelPoset {adv : Adversary} {k j K : ℕ} (hF : adv.Forces K)
    (hL : adv.LandsIn fun _ G => G.Colorable k ∧ ∃ m, IsPaddedTower m j G) :
    K ≤ Fintype.card (LabelPoset k j) := by
  have hA := cleanAlg_isProper OnlineAlg.firstFit_isProper
  obtain ⟨p, hstop, hK⟩ := hF _ hA
  obtain ⟨I, hg, hcost⟩ := exists_input_of_hist adv OnlineAlg.firstFit p
  obtain ⟨hc, m, hT⟩ := hL _ hA p hstop
  refine le_trans ?_ (hT.ceiling hc).1
  rw [← hg, ← cost_firstFit_eq, hcost]
  exact hK

/-- **"No one-level tower over a clique can force more"** (the sentence after the proof of
Theorem 1.2).  An adversary all of whose final graphs are `3`-colourable one-level towers
(Definition 4.7: an initial segment of a full blow-up of a clique `K_m`, possibly followed by
isolated vertices) forces at most `|P_1(3)| = 7` colours. -/
theorem forces_le_seven_of_one_level {adv : Adversary} {K : ℕ} (hF : adv.Forces K)
    (hL : adv.LandsIn fun _ G => G.Colorable 3 ∧ ∃ m, IsPaddedTower m 1 G) : K ≤ 7 :=
  card_labelPoset_three_one ▸ forces_le_card_labelPoset hF hL

/-- **Corollary 9.6, upper bound.**  There is `n_k` such that for every `n ≥ n_k`, an adversary
of size at most `n` that lands in the `k`-colourable towers forces at most
`n^{1/(lg* n - lg* k - 3)}` colours. -/
theorem towerForces_le_rpow (k : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ K, TowerForces k n K →
      (K : ℝ) ≤ (n : ℝ) ^ (1 / ((logStar n : ℝ) - logStar k - 3)) := by
  obtain ⟨n₀, hn₀⟩ := exists_threshold_le_rpow.{0} k
  refine ⟨n₀, fun n hn K hK => ?_⟩
  obtain ⟨N, G, hNn, ⟨hc, m, j, hT⟩, hKG⟩ := hK.exists_tower
  have := hn₀ n hn m j (Fin N) G hT hc (by rw [Nat.card_fin]; exact hNn)
  exact le_trans (by exact_mod_cast hKG) this

/-! ### Lower bound: uniform towers with the parameters of Theorem 1.1 -/

/-- Every proper deterministic algorithm uses at least `⌈x⌉` colours on some `k`-colourable
tower on exactly `n` vertices. -/
def TowerInputs (k n : ℕ) (x : ℝ) : Prop :=
  ∀ A : OnlineAlg, A.IsProper → ∃ I : OnlineInput n, IsColTower k n I.graph ∧ ⌈x⌉₊ ≤ I.cost A

/-- Determinacy for towers (`Det.exists_presents`): if every proper algorithm uses at least `⌈x⌉`
colours on some `k`-colourable tower on `n` vertices, then one adversary of size at most `n`
forces `⌈x⌉` colours and lands in the `k`-colourable towers. -/
theorem TowerInputs.towerForces {k n : ℕ} {x : ℝ} (h : TowerInputs k n x) :
    TowerForces k n ⌈x⌉₊ := by
  obtain ⟨adv, hadv⟩ := exists_presents {I : OnlineInput n | IsColTower k n I.graph} h
  exact ⟨adv, hadv.forces, hadv.sizeLE, hadv.landsIn fun I hI => hI⟩

theorem towerInputs_hmono : ∀ (k n : ℕ) (x x' : ℝ), 1 ≤ k → TowerInputs k n x → x' ≤ x →
    TowerInputs k n x' := by
  intro k n x x' _ h hx A hA
  obtain ⟨I, hI, hc⟩ := h A hA
  exact ⟨I, hI, (Nat.ceil_mono hx).trans hc⟩

/-- Appending isolated vertices keeps towers. -/
theorem towerInputs_hpad : ∀ (k n n' : ℕ) (x : ℝ), 1 ≤ k → TowerInputs k n x → n ≤ n' →
    TowerInputs k n' x := by
  intro k n n' x hk h hn A hA
  obtain ⟨I, ⟨hc, m, j, hT⟩, hcost⟩ := h A hA
  refine ⟨padInput I n', ⟨colorable_padInput hk hc n', m, j, ?_⟩,
    hcost.trans (cost_le_padInput hn I A)⟩
  rw [padInput_graph]
  exact hT.padGraph hn

theorem exists_cast_class {C : ∀ n : ℕ, SimpleGraph (Fin n) → Prop} {n n' : ℕ} (h : n = n')
    (I : OnlineInput n) (hC : C n I.graph) :
    ∃ I' : OnlineInput n', C n' I'.graph ∧ ∀ A, I'.cost A = I.cost A := by
  subst h
  exact ⟨I, hC, fun _ => rfl⟩

/-- Theorem 8.5 (ii), per algorithm, landing in the towers. -/
theorem towerInputs_hcore : ∀ k j m, 1 ≤ k → 1 ≤ j → 2 ≤ m →
    m ≤ Fintype.card (LabelPoset k j) → TowerInputs k (m * (2 * m) ^ j) (uniformBound m) := by
  intro k j m _ hj hm hP A hA
  have hA2 : 0 < 2 * m := by omega
  obtain ⟨ω, hω⟩ := exists_realization hm hj hA2 A hA
  obtain ⟨I', hI', hcost⟩ := exists_cast_class (C := IsColTower k) (utSize_eq (2 * m) m j)
    (uInputE hA2 ω) ⟨uInputE_colorable ω hA2 hP, m, j, uInputE_isPaddedTower hA2 ω⟩
  exact ⟨I', hI', by rw [hcost]; exact hω⟩

/-- **Corollary 9.6, lower bound.**  For `k ≥ 3` and `n ≥ 2^406` some adversary of size at most
`n` forces `⌈n^{1/(lg* n + 3)}⌉` colours and lands in the `k`-colourable towers (indeed in the
`3`-colourable ones). -/
theorem towerForces_rpow {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ^ 406 ≤ n) :
    TowerForces k n ⌈(n : ℝ) ^ (1 / (logStar n + 3 : ℝ))⌉₊ :=
  (TowerInputs.towerForces (Rjm.logStar_three_large TowerInputs towerInputs_hmono
    towerInputs_hpad towerInputs_hcore hn)).mono_k hk

/-- For `k ≥ 4` and `n ≥ 2^201` the same with `⌈n^{1/(lg* n + 1)}⌉` colours. -/
theorem towerForces_rpow_of_four_le {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ^ 201 ≤ n) :
    TowerForces k n ⌈(n : ℝ) ^ (1 / (logStar n + 1 : ℝ))⌉₊ :=
  TowerInputs.towerForces (Rjm.logStar_of_four_le_large TowerInputs towerInputs_hmono
    towerInputs_hpad towerInputs_hcore hk hn)

/-! ### Corollary 9.6 -/

/-- **Corollary 9.6 (the value of towers), two-sided form.**  For `k ≥ 3` there is `n₀` such
that for every `n ≥ n₀` the largest number of colours that an adversary of size at most `n` can
force while landing in the `k`-colourable towers lies between `n^{1/(lg* n + 3)}` and
`n^{1/(lg* n - lg* k - 3)}`. -/
theorem value_of_towers {k : ℕ} (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ (1 / ((logStar n : ℝ) + 3)) ≤ towerValue k n ∧
      (towerValue k n : ℝ) ≤ (n : ℝ) ^ (1 / ((logStar n : ℝ) - logStar k - 3)) := by
  obtain ⟨n₀, hn₀⟩ := towerForces_le_rpow k
  refine ⟨max n₀ (2 ^ 406), fun n hn => ?_⟩
  have h1 := towerForces_rpow hk ((le_max_right _ _).trans hn)
  refine ⟨(Nat.le_ceil _).trans (by exact_mod_cast le_towerValue h1), ?_⟩
  exact hn₀ n ((le_max_left _ _).trans hn) _ (towerForces_towerValue h1)

/-- **Corollary 9.6 (the value of towers).**  For fixed `k ≥ 3` there is `n₀` such that for
every `n ≥ n₀` the largest number of colours that an adversary of size at most `n` can force
while landing in the `k`-colourable towers is `n^{1/(lg* n + c)}` for a real number `c = c(k, n)`
with `-lg* k - 3 ≤ c ≤ 3` (and `lg* n + c > 0`). -/
theorem value_of_towers_exponent {k : ℕ} (hk : 3 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ c : ℝ, -(logStar k : ℝ) - 3 ≤ c ∧ c ≤ 3 ∧
      0 < (logStar n : ℝ) + c ∧
      (towerValue k n : ℝ) = (n : ℝ) ^ (1 / ((logStar n : ℝ) + c)) := by
  obtain ⟨n₀, hn₀⟩ := value_of_towers hk
  refine ⟨max n₀ (tow (logStar k + 3) + 1), fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hnt : tow (logStar k + 3) < n := Nat.lt_iff_add_one_le.2 ((le_max_right _ _).trans hn)
  have hL : logStar k + 4 ≤ logStar n := by
    by_contra h
    push Not at h
    have := logStar_le_iff.1 (show logStar n ≤ logStar k + 3 by omega)
    omega
  have hn1 : (1 : ℝ) < n := by
    have h0 : tow 0 ≤ tow (logStar k + 3) := tow_mono (Nat.zero_le _)
    rw [tow_zero] at h0
    have : 1 < n := lt_of_le_of_lt h0 hnt
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  have hLr : ((logStar k : ℝ) + 4) ≤ (logStar n : ℝ) := by exact_mod_cast hL
  have hk0 : (0 : ℝ) ≤ (logStar k : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) < (logStar n : ℝ) - logStar k - 3 := by linarith
  have hp : (0 : ℝ) < (logStar n : ℝ) + 3 := by linarith
  set V : ℝ := (towerValue k n : ℝ) with hV
  have hV1 : 1 < V :=
    lt_of_lt_of_le (Real.one_lt_rpow hn1 (one_div_pos.2 hp)) h1
  have hV0 : 0 < V := by linarith
  have hlV : 0 < Real.log V := Real.log_pos hV1
  have hln : 0 < Real.log n := Real.log_pos hn1
  have e1 : Real.log n ≤ ((logStar n : ℝ) + 3) * Real.log V := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) h1
    rw [Real.log_rpow hn0, one_div, inv_mul_le_iff₀ hp] at this
    exact this
  have e2 : ((logStar n : ℝ) - logStar k - 3) * Real.log V ≤ Real.log n := by
    have := Real.log_le_log hV0 h2
    rw [Real.log_rpow hn0, one_div, le_inv_mul_iff₀ hd] at this
    exact this
  refine ⟨Real.log n / Real.log V - logStar n, ?_, ?_, ?_, ?_⟩
  · have := (le_div_iff₀ hlV).2 e2
    linarith
  · have := (div_le_iff₀ hlV).2 e1
    linarith
  · have : (logStar n : ℝ) + (Real.log n / Real.log V - logStar n) = Real.log n / Real.log V := by
      ring
    rw [this]
    exact div_pos hln hlV
  · have : (logStar n : ℝ) + (Real.log n / Real.log V - logStar n) = Real.log n / Real.log V := by
      ring
    rw [this, one_div_div, Real.rpow_def_of_pos hn0, mul_div_cancel₀ _ hln.ne', Real.exp_log hV0]

end Det

end OnlineColouring
