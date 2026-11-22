module

public import OnlineColouring.Towers

/-!
# Growth of `J*`

Lemma 5.5 (growth) of the paper, parts (i) and (ii); part (iii) is in `BaseFacts.lean`.

* (i) if `A` is an antichain of `P` with `|A| = w ≥ 1`, then `U ↦ ↓U` is an order embedding of the
  nonempty subsets of `A` into `J*(P)` (`downEmbedding`); hence `|J*(P)| ≥ 2^w - 1`
  (`HasAntichain.two_pow_sub_one_le_card_jst`) and `J*(P)` has an antichain of size
  `choose w ⌊w/2⌋` (`HasAntichain.jst`);
* (ii) `|J*(P)| ≤ 2^|P| - 1` (`card_jst_le`), and `p ↦ ↓{p}` embeds `P` into `J*(P)`
  (`principalEmbedding`).

We express "`width P ≥ w`" as `HasAntichain P w` (there is an antichain of exactly `w`
elements); `width` itself is also defined, with `le_width_iff`.  The lemma with `width`, as the
paper states it, is `Paper.le_width_jst` (`PaperStatements.lean`).
-/

@[expose] public section

namespace OnlineColouring

open Finset

variable {P : Type*} [PartialOrder P]

/-! ### Antichains and width -/

/-- `P` has an antichain with exactly `w` elements (equivalently, `width P ≥ w`). -/
def HasAntichain (P : Type*) [PartialOrder P] (w : ℕ) : Prop :=
  ∃ A : Finset P, IsAntichain (· ≤ ·) (A : Set P) ∧ A.card = w

theorem HasAntichain.mono {w w' : ℕ} (h : HasAntichain P w) (hw : w' ≤ w) :
    HasAntichain P w' := by
  obtain ⟨A, hA, rfl⟩ := h
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq hw
  exact ⟨B, hA.subset (by simpa using hBA), hB⟩

theorem HasAntichain.le_card [Fintype P] {w : ℕ} (h : HasAntichain P w) :
    w ≤ Fintype.card P := by
  obtain ⟨A, -, rfl⟩ := h
  exact Finset.card_le_univ A

theorem hasAntichain_of_orderEmbedding {Q : Type*} [PartialOrder Q] (e : P ↪o Q) {w : ℕ}
    (h : HasAntichain P w) : HasAntichain Q w := by
  classical
  obtain ⟨A, hA, rfl⟩ := h
  refine ⟨A.map e.toEmbedding, ?_, by simp⟩
  intro a ha b hb hab hle
  simp only [coe_map, Set.mem_image, mem_coe] at ha hb
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exact hA ha hb (fun h => hab (by rw [h])) (e.le_iff_le.1 hle)

/-- The width of a finite poset: the largest size of an antichain. -/
noncomputable def width (P : Type*) [PartialOrder P] [Fintype P] : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset P)).filter
    fun A : Finset P => IsAntichain (· ≤ ·) (↑A : Set P)).sup Finset.card

theorem le_width_iff [Fintype P] {w : ℕ} : w ≤ width P ↔ HasAntichain P w := by
  classical
  unfold width
  constructor
  · intro hw
    have hne : ((Finset.univ : Finset (Finset P)).filter
        fun A : Finset P => IsAntichain (· ≤ ·) (↑A : Set P)).Nonempty :=
      ⟨∅, by simp⟩
    obtain ⟨A, hA, hAw⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    refine HasAntichain.mono ⟨A, hA, rfl⟩ ?_
    convert hw using 1
    convert hAw.symm
  · rintro ⟨A, hA, rfl⟩
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hA⟩)

/-- Every set of an antichain-ordered type is an antichain: `Anti α` has an antichain with `|α|`
elements. -/
theorem hasAntichain_anti (α : Type*) [Fintype α] : HasAntichain (Anti α) (Fintype.card α) :=
  ⟨Finset.univ, Anti.isAntichain _, Finset.card_univ⟩

/-! ### Down-closures -/

section NonemptySubsets

variable {α : Type*}

/-- The nonempty subsets of a finset `A`, ordered by inclusion. -/
abbrev NonemptySubsets (A : Finset α) : Type _ := {U : Finset α // U ⊆ A ∧ U.Nonempty}

theorem card_nonemptySubsets [Fintype α] [DecidableEq α] (A : Finset α) :
    Fintype.card (NonemptySubsets A) = 2 ^ A.card - 1 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun U : Finset α => U ⊆ A ∧ U.Nonempty) = A.powerset.erase ∅ := by
    ext U
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  rw [this, Finset.card_erase_of_mem (Finset.empty_mem_powerset A), Finset.card_powerset]

end NonemptySubsets

section DownClosure

variable [Fintype P] [DecidableLE P]

/-- The down-closure `↓U` of a finset. -/
def downClosure (U : Finset P) : Finset P := Finset.univ.filter fun p => ∃ a ∈ U, p ≤ a

@[simp] theorem mem_downClosure {U : Finset P} {p : P} : p ∈ downClosure U ↔ ∃ a ∈ U, p ≤ a := by
  simp [downClosure]

theorem subset_downClosure (U : Finset P) : U ⊆ downClosure U :=
  fun a ha => mem_downClosure.2 ⟨a, ha, le_rfl⟩

theorem isLowerFinset_downClosure (U : Finset P) : IsLowerFinset (downClosure U) := by
  intro a ha b hba
  obtain ⟨c, hc, hac⟩ := mem_downClosure.1 ha
  exact mem_downClosure.2 ⟨c, hc, hba.trans hac⟩

/-- `↓U` as an element of `J*(P)`, for nonempty `U`. -/
def Jst.down (U : Finset P) (hU : U.Nonempty) : Jst P :=
  Jst.mk (downClosure U) (isLowerFinset_downClosure U) (hU.mono (subset_downClosure U))

@[simp] theorem Jst.mem_down {U : Finset P} {hU : U.Nonempty} {p : P} :
    p ∈ Jst.down U hU ↔ ∃ a ∈ U, p ≤ a :=
  mem_downClosure

theorem Jst.down_le_down_iff_forall {U U' : Finset P} {hU : U.Nonempty} {hU' : U'.Nonempty} :
    Jst.down U hU ≤ Jst.down U' hU' ↔ ∀ a ∈ U, ∃ b ∈ U', a ≤ b := by
  constructor
  · intro h a ha
    exact Jst.mem_down.1 ((Jst.le_iff_forall.1 h) a (Jst.mem_down.2 ⟨a, ha, le_rfl⟩))
  · intro h
    rw [Jst.le_iff_forall]
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Jst.mem_down.1 hp
    obtain ⟨b, hb, hab⟩ := h a ha
    exact Jst.mem_down.2 ⟨b, hb, hpa.trans hab⟩

/-- On subsets of an antichain, `U ↦ ↓U` reflects inclusion. -/
theorem Jst.down_le_down_iff {A U U' : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P))
    (hUA : U ⊆ A) (hUA' : U' ⊆ A) {hU : U.Nonempty} {hU' : U'.Nonempty} :
    Jst.down U hU ≤ Jst.down U' hU' ↔ U ⊆ U' := by
  rw [Jst.down_le_down_iff_forall]
  constructor
  · intro h a ha
    obtain ⟨b, hb, hab⟩ := h a ha
    by_contra hne
    have hab' : a ≠ b := fun h => hne (h ▸ hb)
    exact hA (mem_coe.2 (hUA ha)) (mem_coe.2 (hUA' hb)) hab' hab
  · intro h a ha
    exact ⟨a, h ha, le_rfl⟩

/-- **Lemma 5.5 (i).** If `A` is an antichain, then `U ↦ ↓U` is an order embedding of the
nonempty subsets of `A` into `J*(P)`. -/
def downEmbedding {A : Finset P} (hA : IsAntichain (· ≤ ·) (A : Set P)) :
    NonemptySubsets A ↪o Jst P :=
  OrderEmbedding.ofMapLEIff (fun U => Jst.down U.1 U.2.2)
    fun U U' => Jst.down_le_down_iff hA U.2.1 U'.2.1

/-- **Lemma 5.5 (i), counting.** An antichain of size `w` gives `|J*(P)| ≥ 2^w - 1`. -/
theorem HasAntichain.two_pow_sub_one_le_card_jst [DecidableEq P] {w : ℕ} (h : HasAntichain P w) :
    2 ^ w - 1 ≤ Fintype.card (Jst P) := by
  obtain ⟨A, hA, rfl⟩ := h
  rw [← card_nonemptySubsets A]
  exact Fintype.card_le_of_embedding (downEmbedding hA).toEmbedding

theorem choose_succ_half_eq_choose_half (w : ℕ) : w.choose ((w + 1) / 2) = w.choose (w / 2) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' w
  · congr 1
    omega
  · have h₁ : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h₂ : (2 * m + 1) / 2 = m := by omega
    rw [h₁, h₂, Nat.choose_symm_half]

omit [Fintype P] [DecidableLE P] in
/-- **Lemma 5.5 (i), width.** An antichain of size `w ≥ 1` in `P` gives an antichain of size
`choose w ⌊w/2⌋` in `J*(P)`: the down-closures of the `⌈w/2⌉`-subsets of the antichain. -/
theorem HasAntichain.jst [Finite P] {w : ℕ} (h : HasAntichain P w) (hw : 1 ≤ w) :
    HasAntichain (Jst P) (w.choose (w / 2)) := by
  classical
  have := Fintype.ofFinite P
  obtain ⟨A, hA, rfl⟩ := h
  set r := (A.card + 1) / 2 with hr
  have hr1 : 1 ≤ r := by omega
  let F : {U // U ∈ A.powersetCard r} → NonemptySubsets A := fun U =>
    ⟨U.1, (Finset.mem_powersetCard.1 U.2).1,
      Finset.card_pos.1 (by rw [(Finset.mem_powersetCard.1 U.2).2]; omega)⟩
  have hF : Function.Injective F := by
    intro U U' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  let e : {U // U ∈ A.powersetCard r} ↪ Jst P := ⟨downEmbedding hA ∘ F,
    (downEmbedding hA).injective.comp hF⟩
  refine ⟨(A.powersetCard r).attach.map e, ?_, ?_⟩
  · intro a ha b hb hab hle
    simp only [coe_map, Set.mem_image, mem_coe, Finset.mem_attach, true_and] at ha hb
    obtain ⟨U, rfl⟩ := ha
    obtain ⟨U', rfl⟩ := hb
    have hsub : (F U).1 ⊆ (F U').1 := (downEmbedding hA).le_iff_le.1 hle
    have hcard : U'.1.card ≤ U.1.card := by
      rw [(Finset.mem_powersetCard.1 U.2).2, (Finset.mem_powersetCard.1 U'.2).2]
    have := Finset.eq_of_subset_of_card_le hsub hcard
    exact hab (congrArg e (Subtype.ext this))
  · rw [Finset.card_map, Finset.card_attach, Finset.card_powersetCard, hr,
      choose_succ_half_eq_choose_half]

/-- **Lemma 5.5 (ii).** `|J*(P)| ≤ 2^|P| - 1`. -/
theorem card_jst_le [DecidableEq P] : Fintype.card (Jst P) ≤ 2 ^ Fintype.card P - 1 := by
  have h : Fintype.card {s : Finset P // s.Nonempty} = 2 ^ Fintype.card P - 1 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun s : Finset P => s.Nonempty) = Finset.univ.erase ∅ := by
      ext s
      simp [Finset.nonempty_iff_ne_empty]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_finset]
  rw [← h]
  exact Fintype.card_le_of_injective (fun s : Jst P => (⟨s.val, s.2.2⟩ : {s : Finset P // _}))
    fun s t hst => by
      have h' := congrArg Subtype.val hst
      exact Jst.val_injective h'

/-- **Lemma 5.5 (ii).** `p ↦ ↓{p}` is an order embedding of `P` into `J*(P)`. -/
def principalEmbedding : P ↪o Jst P :=
  OrderEmbedding.ofMapLEIff (fun p => Jst.down {p} (Finset.singleton_nonempty p)) fun p q => by
    rw [Jst.down_le_down_iff_forall]
    simp

theorem card_le_card_jst [DecidableEq P] : Fintype.card P ≤ Fintype.card (Jst P) :=
  Fintype.card_le_of_embedding (principalEmbedding (P := P)).toEmbedding

omit [Fintype P] [DecidableLE P] in
/-- In the antichain every finset is a down-set, so `|J*(Anti α)| = 2^|α| - 1`. -/
theorem card_jst_anti (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Jst (Anti α)) = 2 ^ Fintype.card α - 1 :=
  le_antisymm card_jst_le (hasAntichain_anti α).two_pow_sub_one_le_card_jst

end DownClosure

/-! ### Consequences for the label posets -/

/-- `|P_1(k)| = 2^k - 1`. -/
theorem card_labelPoset_one (k : ℕ) : Fintype.card (LabelPoset k 1) = 2 ^ k - 1 := by
  have := card_jst_anti (Fin k)
  rw [Fintype.card_fin] at this
  exact this

/-- `|P_{j+1}(k)| ≤ 2^{|P_j(k)|} - 1`. -/
theorem card_labelPoset_succ_le (k j : ℕ) :
    Fintype.card (LabelPoset k (j + 1)) ≤ 2 ^ Fintype.card (LabelPoset k j) - 1 :=
  card_jst_le (P := LabelPoset k j)

/-- `|P_j(k)| ≤ |P_{j+1}(k)|`. -/
theorem card_labelPoset_le_succ (k j : ℕ) :
    Fintype.card (LabelPoset k j) ≤ Fintype.card (LabelPoset k (j + 1)) :=
  card_le_card_jst (P := LabelPoset k j)

/-- `P_0(k)` has an antichain of size `k`. -/
theorem hasAntichain_labelPoset_zero (k : ℕ) : HasAntichain (LabelPoset k 0) k := by
  have := hasAntichain_anti (Fin k)
  rw [Fintype.card_fin] at this
  exact this

/-- An antichain of size `w ≥ 1` in `P_j(k)` gives one of size `choose w ⌊w/2⌋` in
`P_{j+1}(k)`. -/
theorem HasAntichain.labelPoset_succ {k j w : ℕ} (h : HasAntichain (LabelPoset k j) w)
    (hw : 1 ≤ w) : HasAntichain (LabelPoset k (j + 1)) (w.choose (w / 2)) :=
  HasAntichain.jst (P := LabelPoset k j) h hw

end OnlineColouring
