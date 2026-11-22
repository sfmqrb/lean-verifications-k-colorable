module

public import OnlineColouring.Growth
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.GetD

/-!
# Coded posets: counting down-sets by kernel computation

Paper: Section 5, the sentence after Corollary 5.7, "The first values are
`|P_j(2)| = j + 2`, `|P_j(3)| = 3, 7, 18, 81, 8569` and `|P_j(4)| = 4, 15, 166`", the widths of
`P_j(3)`, and the antichain of `P_4(3)` used in the remark after Lemma A.1.  This file contains
the mathematics behind those computations; the data are in `NumP3.lean` and `NumP4.lean`, and
the values are collected in `Num.first_values` (`NumValues.lean`).

`decide` on `Finset (Finset …)` cannot reach these sizes (`P_4(3)` consists of the down-sets of a
poset with 81 elements), so the computations are done on natural numbers used as bit masks, and
this file proves that they compute the right thing.

* `IsCoding P n dn idx`: `idx : P → ℕ` numbers the elements of the finite poset `P` by
  `0, …, n - 1` along a linear extension, and bit `i` of `dn j` says whether the element number
  `i` lies below the element number `j`.
* `mask`/`unmask`: finsets of `P` as bit masks.
* `cnt dn f S`: the number of down-sets of the subposet with bit mask `S` (all its elements have
  numbers below `f`): the largest element is either left out, or it is taken together with
  everything below it.  `IsCoding.cnt_mask` proves this, and `IsCoding.card_jst_add_one`
  concludes `|J*(P)| + 1 = cnt dn n (2^n - 1)`.
* `IsCoding.jst`: from a list `L` of bit masks that passes the Bool checks `chkMasks` (strictly
  increasing, positive, each a down-set) and has `cnt … - 1` entries, and a table `rows` that
  passes `chkRows` (bit `a` of row `b` says whether `L[a] ⊆ L[b]`), one gets a coding of `J*(P)`:
  the nonempty down-set `D` gets the position of its mask in `L`.  Completeness of `L` follows
  from the count, so nothing has to be searched.
* `IsCoding.width_le` (a cover by `w` chains, checked by `chkChains`, gives `width P ≤ w`),
  `IsCoding.hasAntichain` (an antichain given by the numbers of its elements, `chkAnti`),
  `IsCoding.exists_layer`, `IsCoding.hasAntichain_jst` (a list of down-set masks with the same
  number of elements gives an antichain of `J*(P)`).

All Bool checks are meant to be evaluated by the kernel (`decide +kernel`).
-/

@[expose] public section

namespace OnlineColouring

namespace Num

open Finset

/-! ### Bit masks -/

/-- The number whose bits `0, …, n - 1` are `f 0, …, f (n - 1)`. -/
def ofBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.bit (f 0) (ofBits (fun i => f (i + 1)) n)

theorem testBit_ofBits (f : ℕ → Bool) (n i : ℕ) :
    (ofBits f n).testBit i = (decide (i < n) && f i) := by
  induction n generalizing f i with
  | zero => simp [ofBits]
  | succ n ih =>
    cases i with
    | zero => simp [ofBits]
    | succ i => simp [ofBits, Nat.testBit_bit_succ, ih]

theorem eq_of_testBit_iff {x y : ℕ} (h : ∀ i, x.testBit i = true ↔ y.testBit i = true) :
    x = y :=
  Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 (h i)

theorem lt_of_testBit {m n i : ℕ} (hm : m < 2 ^ n) (hi : m.testBit i = true) : i < n := by
  by_contra h
  have h' : m < 2 ^ i := hm.trans_le (Nat.pow_le_pow_right (by decide) (not_lt.1 h))
  rw [Nat.testBit_lt_two_pow h'] at hi
  exact Bool.false_ne_true hi

/-! ### Codings -/

/-- `idx` codes the finite poset `P` by the numbers `0, …, n - 1`: it is a bijection onto them,
it is monotone (a linear extension of `P`), and bit `i` of `dn j` says whether the element with
number `i` lies below the element with number `j`. -/
structure IsCoding (P : Type*) [PartialOrder P] (n : ℕ) (dn : ℕ → ℕ) (idx : P → ℕ) : Prop where
  lt : ∀ p, idx p < n
  inj : Function.Injective idx
  surj : ∀ i < n, ∃ p, idx p = i
  le_iff : ∀ p q, p ≤ q ↔ (dn (idx q)).testBit (idx p) = true
  mono : ∀ p q, p ≤ q → idx p ≤ idx q

section Mask

variable {P : Type*}

/-- The bit mask of a finset of `P`. -/
def mask (idx : P → ℕ) (n : ℕ) (s : Finset P) : ℕ :=
  ofBits (fun i => decide (∃ p ∈ s, idx p = i)) n

/-- The finset of `P` with bit mask `m`. -/
def unmask [Fintype P] (idx : P → ℕ) (m : ℕ) : Finset P :=
  univ.filter fun p => m.testBit (idx p) = true

theorem mem_unmask [Fintype P] {idx : P → ℕ} {m : ℕ} {p : P} :
    p ∈ unmask idx m ↔ m.testBit (idx p) = true := by
  simp [unmask]

theorem unmask_zero [Fintype P] (idx : P → ℕ) : unmask idx 0 = ∅ := by
  ext p
  simp [mem_unmask]

variable [PartialOrder P] {n : ℕ} {dn : ℕ → ℕ} {idx : P → ℕ}

theorem IsCoding.testBit_mask (hc : IsCoding P n dn idx) (s : Finset P) (i : ℕ) :
    (mask idx n s).testBit i = true ↔ ∃ p ∈ s, idx p = i := by
  rw [mask, testBit_ofBits]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ⟨p, hp, h⟩ => ⟨h ▸ hc.lt p, p, hp, h⟩⟩

theorem IsCoding.testBit_mask_idx (hc : IsCoding P n dn idx) (s : Finset P) (p : P) :
    (mask idx n s).testBit (idx p) = true ↔ p ∈ s := by
  rw [hc.testBit_mask]
  exact ⟨fun ⟨q, hq, h⟩ => hc.inj h ▸ hq, fun h => ⟨p, h, rfl⟩⟩

theorem IsCoding.unmask_mask [Fintype P] (hc : IsCoding P n dn idx) (s : Finset P) :
    unmask idx (mask idx n s) = s := by
  ext p
  rw [mem_unmask, hc.testBit_mask_idx]

theorem IsCoding.mask_unmask [Fintype P] (hc : IsCoding P n dn idx) {m : ℕ} (hm : m < 2 ^ n) :
    mask idx n (unmask idx m) = m := by
  apply eq_of_testBit_iff
  intro i
  rw [hc.testBit_mask]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact mem_unmask.1 hp
  · intro hi
    obtain ⟨p, rfl⟩ := hc.surj i (lt_of_testBit hm hi)
    exact ⟨p, mem_unmask.2 hi, rfl⟩

theorem IsCoding.mask_injective (hc : IsCoding P n dn idx) :
    Function.Injective (mask idx n) := fun s t h => by
  ext p
  rw [← hc.testBit_mask_idx s p, h, hc.testBit_mask_idx t p]

theorem IsCoding.mask_empty (hc : IsCoding P n dn idx) : mask idx n (∅ : Finset P) = 0 := by
  apply eq_of_testBit_iff
  intro i
  rw [hc.testBit_mask]
  simp

theorem IsCoding.mask_univ [Fintype P] (hc : IsCoding P n dn idx) :
    mask idx n (univ : Finset P) = 2 ^ n - 1 := by
  apply eq_of_testBit_iff
  intro i
  rw [hc.testBit_mask, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  constructor
  · rintro ⟨p, -, rfl⟩
    exact hc.lt p
  · intro hi
    obtain ⟨p, rfl⟩ := hc.surj i hi
    exact ⟨p, mem_univ _, rfl⟩

theorem IsCoding.subset_iff (hc : IsCoding P n dn idx) (s t : Finset P) :
    s ⊆ t ↔ mask idx n s &&& mask idx n t = mask idx n s := by
  constructor
  · intro h
    apply eq_of_testBit_iff
    intro i
    rw [Nat.testBit_land, Bool.and_eq_true, hc.testBit_mask, hc.testBit_mask]
    exact ⟨fun h' => h'.1, fun ⟨p, hp, hi⟩ => ⟨⟨p, hp, hi⟩, p, h hp, hi⟩⟩
  · intro h p hp
    have h1 := (hc.testBit_mask_idx s p).2 hp
    rw [← h, Nat.testBit_land, Bool.and_eq_true] at h1
    exact (hc.testBit_mask_idx t p).1 h1.2

/-! ### Counting the down-sets -/

variable [DecidableEq P] [DecidableLE P]

/-- The down-sets of the subposet induced on `S`. -/
def relLower (S : Finset P) : Finset (Finset P) :=
  S.powerset.filter fun D => ∀ d ∈ D, ∀ s ∈ S, s ≤ d → s ∈ D

theorem mem_relLower {S D : Finset P} :
    D ∈ relLower S ↔ D ⊆ S ∧ ∀ d ∈ D, ∀ s ∈ S, s ≤ d → s ∈ D := by
  simp [relLower]

theorem relLower_empty : relLower (∅ : Finset P) = {∅} := by
  ext D
  rw [mem_relLower, mem_singleton, subset_empty]
  exact ⟨fun h => h.1, fun h => ⟨h, by simp⟩⟩

theorem relLower_univ [Fintype P] :
    relLower (univ : Finset P) = univ.filter (IsLowerFinset (P := P)) := by
  ext D
  simp [mem_relLower, IsLowerFinset]

/-- A down-set of `S` either avoids a maximal element `x` of `S`, and is then a down-set of
`S - x`, or it contains `x` together with everything of `S` below `x`, and what remains is a
down-set of `S - ↓x`. -/
theorem card_relLower_split {S : Finset P} {x : P} (hx : x ∈ S)
    (hmax : ∀ s ∈ S, x ≤ s → s = x) :
    (relLower S).card =
      (relLower (S.erase x)).card + (relLower (S.filter fun s => ¬ s ≤ x)).card := by
  have h1 : (relLower S).filter (fun D => x ∉ D) = relLower (S.erase x) := by
    ext D
    simp only [mem_filter, mem_relLower]
    constructor
    · rintro ⟨⟨hDS, hD⟩, hxD⟩
      exact ⟨fun d hd => mem_erase.2 ⟨fun h => hxD (h ▸ hd), hDS hd⟩,
        fun d hd s hs hsd => hD d hd s (mem_of_mem_erase hs) hsd⟩
    · rintro ⟨hDS, hD⟩
      have hxD : x ∉ D := fun h => (mem_erase.1 (hDS h)).1 rfl
      refine ⟨⟨fun d hd => mem_of_mem_erase (hDS hd), fun d hd s hs hsd => ?_⟩, hxD⟩
      by_cases hsx : s = x
      · subst hsx
        have h := hmax d (mem_of_mem_erase (hDS hd)) hsd
        exact absurd (h ▸ hd) hxD
      · exact hD d hd s (mem_erase.2 ⟨hsx, hs⟩) hsd
  have h2 : ((relLower S).filter (fun D => ¬ x ∉ D)).card =
      (relLower (S.filter fun s => ¬ s ≤ x)).card := by
    refine card_nbij' (fun D => D.filter fun s => ¬ s ≤ x)
      (fun D => D ∪ S.filter fun s => s ≤ x) ?_ ?_ ?_ ?_
    · intro D hD
      rw [mem_coe, mem_filter, mem_relLower] at hD
      rw [mem_coe, mem_relLower]
      obtain ⟨⟨hDS, hD⟩, -⟩ := hD
      refine ⟨fun d hd => ?_, fun d hd s hs hsd => ?_⟩
      · rw [mem_filter] at hd ⊢
        exact ⟨hDS hd.1, hd.2⟩
      · rw [mem_filter] at hd hs ⊢
        exact ⟨hD d hd.1 s hs.1 hsd, hs.2⟩
    · intro D hD
      rw [mem_coe, mem_relLower] at hD
      rw [mem_coe, mem_filter, mem_relLower]
      obtain ⟨hDS, hD⟩ := hD
      refine ⟨⟨fun d hd => ?_, fun d hd s hs hsd => ?_⟩, ?_⟩
      · rcases mem_union.1 hd with h | h
        · exact (mem_filter.1 (hDS h)).1
        · exact (mem_filter.1 h).1
      · by_cases hsx : s ≤ x
        · exact mem_union_right _ (mem_filter.2 ⟨hs, hsx⟩)
        · rcases mem_union.1 hd with h | h
          · exact mem_union_left _ (hD d h s (mem_filter.2 ⟨hs, hsx⟩) hsd)
          · exact absurd (hsd.trans (mem_filter.1 h).2) hsx
      · exact not_not.2 (mem_union_right _ (mem_filter.2 ⟨hx, le_rfl⟩))
    · intro D hD
      rw [mem_coe, mem_filter, mem_relLower] at hD
      obtain ⟨⟨hDS, hD⟩, hxD⟩ := hD
      ext p
      simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact hD x (not_not.1 hxD) p h.1 h.2
      · intro hp
        by_cases hpx : p ≤ x
        · exact Or.inr ⟨hDS hp, hpx⟩
        · exact Or.inl ⟨hp, hpx⟩
    · intro D hD
      rw [mem_coe, mem_relLower] at hD
      ext p
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨h | h, hpx⟩
        · exact h
        · exact absurd h.2 hpx
      · intro hp
        exact ⟨Or.inl hp, (mem_filter.1 (hD.1 hp)).2⟩
  rw [← h1, ← h2, card_filter_add_card_filter_not]

/-- `cnt dn f S`: the number of down-sets of the subposet with bit mask `S`, all of whose
elements have numbers below `f`.  The element `f - 1`, if present, is maximal: a down-set
either avoids it, or contains everything of `S` below it. -/
def cnt (dn : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, S =>
    if S.testBit f then cnt dn f (S ^^^ 2 ^ f) + cnt dn f (S ^^^ (S &&& dn f))
    else cnt dn f S

omit [PartialOrder P] [DecidableEq P] [DecidableLE P] in
theorem cnt_zero (dn : ℕ → ℕ) : ∀ f, cnt dn f 0 = 1
  | 0 => rfl
  | f + 1 => by
    rw [cnt, Nat.zero_testBit]
    simpa using cnt_zero dn f

/-- `cnt` for a table given as a list: the first argument lists the rows of the elements
`f - 1, …, 0` in this order, so that no row has to be looked up, and the recursion stops as soon
as no element is left.  This is the function that the kernel evaluates. -/
def cntL : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 1
  | d :: ds, f, S =>
    if S = 0 then 1
    else if S.testBit (f - 1) then
      cntL ds (f - 1) (S ^^^ 2 ^ (f - 1)) + cntL ds (f - 1) (S ^^^ (S &&& d))
    else cntL ds (f - 1) S

omit [PartialOrder P] [DecidableEq P] [DecidableLE P] in
theorem cntL_eq (rows : List ℕ) : ∀ f, f ≤ rows.length → ∀ S,
    cntL (rows.take f).reverse f S = cnt (fun j => rows.getD j 0) f S
  | 0, _, S => by simp [cntL, cnt]
  | f + 1, hf, S => by
    have hlt : f < rows.length := hf
    have ht : (rows.take (f + 1)).reverse = rows[f] :: (rows.take f).reverse := by
      rw [List.take_succ_eq_append_getElem hlt, List.reverse_append]
      rfl
    rw [ht, cntL, cnt]
    simp only [Nat.add_sub_cancel]
    by_cases hS : S = 0
    · subst hS
      simp [cnt_zero]
    · simp only [hS, ↓reduceIte]
      rw [cntL_eq rows f hlt.le, cntL_eq rows f hlt.le, cntL_eq rows f hlt.le,
        List.getD_eq_getElem _ _ hlt]

omit [PartialOrder P] [DecidableEq P] [DecidableLE P] in
/-- The kernel evaluates `cntL`; the theorems are stated for `cnt`. -/
theorem cnt_eq_of_cntL {rows : List ℕ} {n N : ℕ} (hn : rows.length = n)
    (h : cntL rows.reverse n (2 ^ n - 1) = N) :
    cnt (fun j => rows.getD j 0) n (2 ^ n - 1) = N := by
  subst hn
  rw [← cntL_eq rows rows.length le_rfl, List.take_length]
  exact h

theorem IsCoding.cnt_mask (hc : IsCoding P n dn idx) :
    ∀ (f : ℕ) (S : Finset P), (∀ p ∈ S, idx p < f) →
      cnt dn f (mask idx n S) = (relLower S).card := by
  intro f
  induction f with
  | zero =>
    intro S hS
    have hS' : S = ∅ := eq_empty_of_forall_notMem fun p hp => absurd (hS p hp) (Nat.not_lt_zero _)
    subst hS'
    simp [cnt, relLower_empty]
  | succ f ih =>
    intro S hS
    rw [cnt]
    by_cases hf : (mask idx n S).testBit f = true
    · simp only [hf, ↓reduceIte]
      obtain ⟨x, hx, rfl⟩ := (hc.testBit_mask S f).1 hf
      have hmax : ∀ s ∈ S, x ≤ s → s = x := fun s hs hxs =>
        hc.inj (le_antisymm (Nat.lt_succ_iff.1 (hS s hs)) (hc.mono _ _ hxs))
      have e1 : mask idx n S ^^^ 2 ^ idx x = mask idx n (S.erase x) := by
        apply eq_of_testBit_iff
        intro i
        rw [Nat.testBit_xor, Nat.testBit_two_pow, hc.testBit_mask]
        by_cases hi : idx x = i
        · subst hi
          rw [(hc.testBit_mask_idx S x).2 hx]
          simp only [decide_true, Bool.xor_self, Bool.false_eq_true, false_iff, not_exists,
            not_and]
          intro p hp hpx
          exact (mem_erase.1 hp).1 (hc.inj hpx)
        · simp only [hi, decide_false, Bool.xor_false]
          rw [hc.testBit_mask]
          constructor
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, mem_erase.2 ⟨fun h => hi (h ▸ rfl), hp⟩, rfl⟩
          · rintro ⟨p, hp, rfl⟩
            exact ⟨p, mem_of_mem_erase hp, rfl⟩
      have e2 : mask idx n S ^^^ (mask idx n S &&& dn (idx x)) =
          mask idx n (S.filter fun s => ¬ s ≤ x) := by
        apply eq_of_testBit_iff
        intro i
        rw [Nat.testBit_xor, Nat.testBit_land, hc.testBit_mask]
        by_cases ha : ∃ p ∈ S, idx p = i
        · obtain ⟨p, hp, rfl⟩ := ha
          rw [(hc.testBit_mask_idx S p).2 hp]
          simp only [Bool.true_and, Bool.true_xor, Bool.not_eq_true', ← Bool.not_eq_true,
            ← hc.le_iff]
          constructor
          · intro hpx
            exact ⟨p, mem_filter.2 ⟨hp, hpx⟩, rfl⟩
          · rintro ⟨q, hq, hqp⟩
            have := hc.inj hqp
            subst this
            exact (mem_filter.1 hq).2
        · have hf' : (mask idx n S).testBit i = false := by
            rw [← Bool.not_eq_true, hc.testBit_mask]
            exact ha
          rw [hf']
          simp only [Bool.false_and, Bool.xor_self, Bool.false_eq_true, false_iff, not_exists,
            not_and]
          intro p hp hpi
          exact ha ⟨p, (mem_filter.1 hp).1, hpi⟩
      rw [e1, e2, ih _ ?_, ih _ ?_, card_relLower_split hx hmax]
      · intro p hp
        have h1 := hS p (mem_filter.1 hp).1
        have h2 : idx p ≠ idx x := fun h => (mem_filter.1 hp).2 (hc.inj h ▸ le_rfl)
        omega
      · intro p hp
        have h1 := hS p (mem_of_mem_erase hp)
        have h2 : idx p ≠ idx x := fun h => (mem_erase.1 hp).1 (hc.inj h)
        omega
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      apply ih
      intro p hp
      have h1 := hS p hp
      have h2 : idx p ≠ f := fun h => hf ((hc.testBit_mask S f).2 ⟨p, hp, h⟩)
      omega

/-- The number of all down-sets of `P` (including the empty one) is `cnt dn n (2^n - 1)`. -/
theorem IsCoding.card_lower [Fintype P] (hc : IsCoding P n dn idx) :
    (univ.filter (IsLowerFinset (P := P))).card = cnt dn n (2 ^ n - 1) := by
  rw [← hc.mask_univ, hc.cnt_mask n univ (fun p _ => hc.lt p), relLower_univ]

omit [DecidableEq P] [DecidableLE P] in
theorem isLowerFinset_empty : IsLowerFinset (∅ : Finset P) := fun a ha => absurd ha (by simp)

theorem card_jst_add_one [Fintype P] :
    Fintype.card (Jst P) + 1 = (univ.filter (IsLowerFinset (P := P))).card := by
  have h : Fintype.card (Jst P) =
      (univ.filter fun s : Finset P => IsLowerFinset s ∧ s.Nonempty).card :=
    Fintype.card_subtype _
  have h2 : (univ.filter fun s : Finset P => IsLowerFinset s ∧ s.Nonempty) =
      (univ.filter (IsLowerFinset (P := P))).erase ∅ := by
    ext s
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have h3 : (∅ : Finset P) ∈ univ.filter (IsLowerFinset (P := P)) :=
    mem_filter.2 ⟨mem_univ _, isLowerFinset_empty⟩
  rw [h, h2, card_erase_of_mem h3]
  have := card_pos.2 ⟨_, h3⟩
  omega

/-- **The count.**  `|J*(P)| + 1 = cnt dn n (2^n - 1)`. -/
theorem IsCoding.card_jst_add_one [Fintype P] (hc : IsCoding P n dn idx) :
    Fintype.card (Jst P) + 1 = cnt dn n (2 ^ n - 1) := by
  rw [Num.card_jst_add_one, hc.card_lower]

theorem IsCoding.card_jst [Fintype P] (hc : IsCoding P n dn idx) {N : ℕ}
    (h : cnt dn n (2 ^ n - 1) = N + 1) : Fintype.card (Jst P) = N := by
  have := hc.card_jst_add_one
  omega

omit [DecidableEq P] [DecidableLE P] in
/-- The number of elements of `P` is `n`. -/
theorem IsCoding.card_eq [Fintype P] (hc : IsCoding P n dn idx) : Fintype.card P = n := by
  classical
  have h : (univ : Finset P).image idx = range n := by
    ext i
    simp only [mem_image, mem_univ, true_and, mem_range]
    exact ⟨fun ⟨p, hp⟩ => hp ▸ hc.lt p, fun hi => hc.surj i hi⟩
  rw [← card_univ, ← card_image_of_injective _ hc.inj, h, card_range]

end Mask

/-! ### Bool checks -/

/-- The list is strictly increasing and all its entries exceed `a`. -/
def incr : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: l => decide (a < b) && incr b l

theorem incr_sound : ∀ {l : List ℕ} {a : ℕ}, incr a l = true →
    l.Pairwise (· < ·) ∧ ∀ b ∈ l, a < b
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | b :: l, a, h => by
    rw [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hp, hb⟩ := incr_sound h.2
    refine ⟨List.pairwise_cons.2 ⟨hb, hp⟩, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (hb c hc)

/-- With every element `i < f` the mask `m` contains all elements below `i`. -/
def closedUpTo (dn : ℕ → ℕ) (m : ℕ) : ℕ → Bool
  | 0 => true
  | f + 1 => (!m.testBit f || dn f &&& m == dn f) && closedUpTo dn m f

theorem closedUpTo_sound {dn : ℕ → ℕ} {m : ℕ} : ∀ {f : ℕ}, closedUpTo dn m f = true →
    ∀ i < f, m.testBit i = true → ∀ j, (dn i).testBit j = true → m.testBit j = true
  | 0, _, i, hi, _, _, _ => absurd hi (Nat.not_lt_zero i)
  | f + 1, h, i, hi, hmi, j, hj => by
    rw [closedUpTo, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact closedUpTo_sound h.2 i hi hmi j hj
    · rcases h.1 with h1 | h1
      · rw [h1] at hmi
        exact absurd hmi Bool.false_ne_true
      · have h2 : (dn i &&& m).testBit j = (dn i).testBit j := by rw [h1]
        rw [Nat.testBit_land, hj, Bool.true_and] at h2
        exact h2

/-- The Bool check for a list of down-set masks: strictly increasing, positive, below `2^n`,
and each entry is a down-set. -/
def chkMasks (dn : ℕ → ℕ) (n : ℕ) (L : List ℕ) : Bool :=
  incr 0 L && L.all fun m => decide (m < 2 ^ n) && closedUpTo dn m n

/-- Bit `i + a` of `r` says whether `l[a] ⊆ mj`. -/
def chkRow (r mj : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, mi :: l => (r.testBit i == (mi &&& mj == mi)) && chkRow r mj (i + 1) l

/-- The table check: `rows` has one row for each entry of `l`, and bit `a` of the row of `mj`
says whether `L[a] ⊆ mj`. -/
def chkRows (L : List ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | mj :: l, r :: rs => chkRow r mj 0 L && chkRows L l rs
  | _, _ => false

theorem chkRow_sound {r mj : ℕ} : ∀ {l : List ℕ} {i : ℕ}, chkRow r mj i l = true →
    ∀ a (ha : a < l.length), r.testBit (i + a) = (l[a] &&& mj == l[a])
  | [], _, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | mi :: l, i, h, a, ha => by
    rw [chkRow, Bool.and_eq_true, beq_iff_eq] at h
    cases a with
    | zero => simpa using h.1
    | succ a =>
      have h2 := chkRow_sound h.2 a (by simpa using ha)
      rw [show i + (a + 1) = i + 1 + a by omega]
      simpa using h2

theorem chkRows_sound {L : List ℕ} : ∀ {l rs : List ℕ}, chkRows L l rs = true →
    ∀ b (hb : b < l.length), ∀ a (ha : a < L.length),
      (rs.getD b 0).testBit a = (L[a] &&& l[b] == L[a])
  | [], [], _, b, hb, _, _ => absurd hb (Nat.not_lt_zero b)
  | [], _ :: _, h, _, _, _, _ => by simp [chkRows] at h
  | _ :: _, [], h, _, _, _, _ => by simp [chkRows] at h
  | mj :: l, r :: rs, h, b, hb, a, ha => by
    rw [chkRows, Bool.and_eq_true] at h
    cases b with
    | zero =>
      have h2 := chkRow_sound h.1 a ha
      simpa using h2
    | succ b => simpa using chkRows_sound h.2 b (by simpa using hb) a ha

/-- The number of elements `i < f` of the mask `m`. -/
def pop (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | f + 1 => pop m f + (m.testBit f).toNat

/-- The elements `j, j + 1, …` (with chain numbers `l`) that lie in the chain `ci` of the element
`i` are comparable with `i`. -/
def chkChainRow (dn : ℕ → ℕ) (i ci : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, cj :: l =>
    (ci != cj || (dn j).testBit i || (dn i).testBit j) && chkChainRow dn i ci (j + 1) l

/-- `chkChainRow` for the elements `i, i + 1, …` with chain numbers `l`. -/
def chkChainRows (dn : ℕ → ℕ) (ch : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, ci :: l => chkChainRow dn i ci 0 ch && chkChainRows dn ch (i + 1) l

/-- Chain cover check: every entry of `ch` is below `w`, and elements with the same entry are
comparable. -/
def chkChains (dn : ℕ → ℕ) (w : ℕ) (ch : List ℕ) : Bool :=
  ch.all (fun c => decide (c < w)) && chkChainRows dn ch 0 ch

theorem chkChainRow_sound {dn : ℕ → ℕ} {i ci : ℕ} : ∀ {l : List ℕ} {j : ℕ},
    chkChainRow dn i ci j l = true → ∀ a (ha : a < l.length), ci = l[a] →
      (dn (j + a)).testBit i = true ∨ (dn i).testBit (j + a) = true
  | [], _, _, a, ha, _ => absurd ha (Nat.not_lt_zero a)
  | cj :: l, j, h, a, ha, hc => by
    rw [chkChainRow, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, bne_iff_ne] at h
    cases a with
    | zero =>
      rcases h.1 with (h1 | h1) | h1
      · exact absurd (by simpa using hc) h1
      · exact Or.inl h1
      · exact Or.inr h1
    | succ a =>
      have h2 := chkChainRow_sound h.2 a (by simpa using ha) (by simpa using hc)
      rw [show j + (a + 1) = j + 1 + a by omega]
      exact h2

theorem chkChainRows_sound {dn : ℕ → ℕ} {ch : List ℕ} : ∀ {l : List ℕ} {i : ℕ},
    chkChainRows dn ch i l = true → ∀ b (hb : b < l.length), ∀ a (ha : a < ch.length),
      l[b] = ch[a] → (dn a).testBit (i + b) = true ∨ (dn (i + b)).testBit a = true
  | [], _, _, b, hb, _, _, _ => absurd hb (Nat.not_lt_zero b)
  | ci :: l, i, h, b, hb, a, ha, hc => by
    rw [chkChainRows, Bool.and_eq_true] at h
    cases b with
    | zero =>
      have h2 := chkChainRow_sound h.1 a ha (by simpa using hc)
      simpa using h2
    | succ b =>
      have h2 := chkChainRows_sound h.2 b (by simpa using hb) a ha (by simpa using hc)
      rw [show i + (b + 1) = i + 1 + b by omega]
      exact h2

/-- Antichain check: the list of element numbers is strictly increasing, below `n`, and its
entries are pairwise incomparable. -/
def chkAnti (dn : ℕ → ℕ) (n : ℕ) (a : List ℕ) : Bool :=
  incr 0 (a.map (· + 1)) && a.all (fun i => decide (i < n)) &&
    a.all fun i => a.all fun j => i == j || !(dn j).testBit i

/-- Layer check: a strictly increasing list of positive down-set masks with `r` elements each. -/
def chkLayer (dn : ℕ → ℕ) (n r : ℕ) (A : List ℕ) : Bool :=
  incr 0 A && A.all fun m => decide (m < 2 ^ n) && closedUpTo dn m n && pop m n == r

/-! ### The coding of `J*(P)` -/

section Jst

variable {P : Type*} [PartialOrder P] {n : ℕ} {dn : ℕ → ℕ} {idx : P → ℕ}

theorem IsCoding.isLowerFinset_unmask [Fintype P] (hc : IsCoding P n dn idx) {m : ℕ}
    (h : closedUpTo dn m n = true) : IsLowerFinset (unmask idx m) := by
  intro a ha b hba
  rw [mem_unmask] at ha ⊢
  exact closedUpTo_sound h (idx a) (hc.lt a) ha (idx b) ((hc.le_iff b a).1 hba)

theorem chkMasks_sound {L : List ℕ} (h : chkMasks dn n L = true) :
    L.Pairwise (· < ·) ∧ ∀ m ∈ L, 0 < m ∧ m < 2 ^ n ∧ closedUpTo dn m n = true := by
  rw [chkMasks, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hp, h0⟩ := incr_sound h.1
  refine ⟨hp, fun m hm => ?_⟩
  have := h.2 m hm
  rw [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨h0 m hm, this.1, this.2⟩

theorem nodup_of_pairwise_lt {L : List ℕ} (h : L.Pairwise (· < ·)) : L.Nodup :=
  h.imp fun hab => ne_of_lt hab

/-- Completeness of a checked list of the right length: it contains the mask of every nonempty
down-set. -/
theorem IsCoding.mask_mem [Finite P] (hc : IsCoding P n dn idx) {L : List ℕ}
    (hL : chkMasks dn n L = true) (hcnt : cnt dn n (2 ^ n - 1) = L.length + 1)
    {s : Finset P} (hs : IsLowerFinset s) (hne : s.Nonempty) : mask idx n s ∈ L := by
  classical
  have := Fintype.ofFinite P
  obtain ⟨hp, hall⟩ := chkMasks_sound hL
  set T : Finset ℕ := insert 0 L.toFinset with hT
  have h0 : (0 : ℕ) ∉ L.toFinset := fun h => absurd (hall 0 (List.mem_toFinset.1 h)).1 (lt_irrefl 0)
  have hTc : T.card = L.length + 1 := by
    rw [hT, card_insert_of_notMem h0, List.toFinset_card_of_nodup (nodup_of_pairwise_lt hp)]
  have hTlt : ∀ m ∈ T, m < 2 ^ n := by
    intro m hm
    rcases mem_insert.1 hm with rfl | hm
    · exact Nat.two_pow_pos n
    · exact (hall m (List.mem_toFinset.1 hm)).2.1
  have himg : T.image (unmask idx) ⊆ univ.filter (IsLowerFinset (P := P)) := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := mem_image.1 ht
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rcases mem_insert.1 hm with rfl | hm
    · rw [unmask_zero]
      exact isLowerFinset_empty
    · exact hc.isLowerFinset_unmask (hall m (List.mem_toFinset.1 hm)).2.2
  have hinj : Set.InjOn (unmask idx) (T : Set ℕ) := by
    intro m hm m' hm' h
    rw [← hc.mask_unmask (hTlt m hm), h, hc.mask_unmask (hTlt m' hm')]
  have heq : T.image (unmask idx) = univ.filter (IsLowerFinset (P := P)) := by
    apply eq_of_subset_of_card_le himg
    rw [card_image_of_injOn hinj, hTc, hc.card_lower, hcnt]
  have hmem : s ∈ T.image (unmask idx) := by
    rw [heq]
    exact mem_filter.2 ⟨mem_univ _, hs⟩
  obtain ⟨m, hm, rfl⟩ := mem_image.1 hmem
  rw [hc.mask_unmask (hTlt m hm)]
  rcases mem_insert.1 hm with rfl | hm
  · rw [unmask_zero] at hne
    exact absurd hne not_nonempty_empty
  · exact List.mem_toFinset.1 hm

/-- The number of a nonempty down-set of `P`: the position of its mask in the list `L`. -/
def jstIdx (idx : P → ℕ) (n : ℕ) (L : List ℕ) (D : Jst P) : ℕ := L.idxOf (mask idx n D.val)

/-- **The next level.**  A checked list `L` of down-set masks with `cnt … - 1` entries and a
checked table `rows` code `J*(P)`: the nonempty down-set `D` gets the position of its mask in
`L`. -/
theorem IsCoding.jst [Finite P] (hc : IsCoding P n dn idx) {L rows : List ℕ}
    (hL : chkMasks dn n L = true) (hcnt : cnt dn n (2 ^ n - 1) = L.length + 1)
    (hrows : chkRows L L rows = true) :
    IsCoding (Jst P) L.length (fun j => rows.getD j 0) (jstIdx idx n L) := by
  have := Fintype.ofFinite P
  obtain ⟨hp, hall⟩ := chkMasks_sound hL
  have hmem : ∀ D : Jst P, mask idx n D.val ∈ L := fun D =>
    hc.mask_mem hL hcnt D.isLower (by obtain ⟨p, hp⟩ := D.nonempty; exact ⟨p, hp⟩)
  have hlt : ∀ D : Jst P, L.idxOf (mask idx n D.val) < L.length := fun D =>
    List.idxOf_lt_length_iff.2 (hmem D)
  have hget : ∀ D : Jst P, L[L.idxOf (mask idx n D.val)]'(hlt D) = mask idx n D.val := fun D =>
    List.getElem_idxOf (hlt D)
  refine ⟨hlt, ?_, ?_, ?_, ?_⟩
  · intro D D' h
    exact Jst.val_injective (hc.mask_injective ((List.idxOf_inj (hmem D)).1 h))
  · intro i hi
    obtain ⟨h0, h2, hcl⟩ := hall L[i] (List.getElem_mem hi)
    have hne : (unmask idx L[i] : Finset P).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro h
      have := hc.mask_unmask (idx := idx) h2
      rw [h, hc.mask_empty] at this
      omega
    refine ⟨Jst.mk (unmask idx L[i]) (hc.isLowerFinset_unmask hcl) hne, ?_⟩
    change L.idxOf (mask idx n (unmask idx L[i])) = i
    rw [hc.mask_unmask h2]
    exact (nodup_of_pairwise_lt hp).idxOf_getElem i hi
  · intro D D'
    have h1 := chkRows_sound hrows _ (hlt D') _ (hlt D)
    rw [hget, hget] at h1
    change D ≤ D' ↔ (rows.getD (L.idxOf (mask idx n D'.val)) 0).testBit
      (L.idxOf (mask idx n D.val)) = true
    rw [h1, beq_iff_eq, Jst.le_iff, hc.subset_iff]
  · intro D D' h
    have h1 : mask idx n D.val ≤ mask idx n D'.val := by
      rw [← (hc.subset_iff _ _).1 (Jst.le_iff.1 h)]
      exact Nat.and_le_right
    by_contra hlt'
    have h2 := (List.pairwise_iff_getElem.1 hp) _ _ (hlt D') (hlt D) (not_le.1 hlt')
    rw [hget, hget] at h2
    omega

/-! ### Width and antichains -/

theorem width_le_of_forall [Fintype P] {w : ℕ}
    (h : ∀ A : Finset P, IsAntichain (· ≤ ·) (A : Set P) → A.card ≤ w) : width P ≤ w := by
  by_contra hlt
  obtain ⟨A, hA, hAc⟩ := le_width_iff.1 (Nat.succ_le_of_lt (not_le.1 hlt))
  have := h A hA
  omega

theorem width_le_card [Fintype P] : width P ≤ Fintype.card P :=
  width_le_of_forall fun A _ => card_le_univ A

/-- **Width from a chain cover.**  If the elements of `P` are distributed over `w` chains, then
`width P ≤ w`. -/
theorem IsCoding.width_le [Fintype P] (hc : IsCoding P n dn idx) {w : ℕ} {ch : List ℕ}
    (hn : ch.length = n) (h : chkChains dn w ch = true) : width P ≤ w := by
  rw [chkChains, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hw, hch⟩ := h
  refine width_le_of_forall fun A hA => ?_
  have hlt : ∀ p, idx p < ch.length := fun p => hn ▸ hc.lt p
  have hmaps : ∀ p ∈ A, ch.getD (idx p) 0 ∈ range w := by
    intro p _
    rw [List.getD_eq_getElem _ _ (hlt p), mem_range]
    simpa using hw _ (List.getElem_mem (hlt p))
  have hinj : Set.InjOn (fun p => ch.getD (idx p) 0) (A : Set P) := by
    intro p hp q hq hpq
    simp only [List.getD_eq_getElem _ _ (hlt p), List.getD_eq_getElem _ _ (hlt q)] at hpq
    have h2 := chkChainRows_sound hch (idx p) (hlt p) (idx q) (hlt q) hpq
    rw [Nat.zero_add] at h2
    by_contra hne
    rcases h2 with h2 | h2
    · exact hA hp hq hne ((hc.le_iff p q).2 h2)
    · exact hA hq hp (Ne.symm hne) ((hc.le_iff q p).2 h2)
  simpa using card_le_card_of_injOn _ hmaps hinj

/-- **An antichain from the numbers of its elements.** -/
theorem IsCoding.hasAntichain [Finite P] (hc : IsCoding P n dn idx) {a : List ℕ}
    (h : chkAnti dn n a = true) : HasAntichain P a.length := by
  classical
  have := Fintype.ofFinite P
  rw [chkAnti, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hinc, hlt⟩, hanti⟩ := h
  have hnd : a.Nodup := by
    have := (incr_sound hinc).1
    rw [List.pairwise_map] at this
    exact this.imp fun hab => by omega
  refine ⟨univ.filter fun p => idx p ∈ a, ?_, ?_⟩
  · intro p hp q hq hne hle
    rw [mem_coe, mem_filter] at hp hq
    have h1 := hanti _ hp.2
    rw [List.all_eq_true] at h1
    have h2 := h1 _ hq.2
    rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', ← Bool.not_eq_true, ← hc.le_iff] at h2
    rcases h2 with h2 | h2
    · exact hne (hc.inj h2)
    · exact h2 hle
  · have himg : (univ.filter fun p => idx p ∈ a).image idx = a.toFinset := by
      ext i
      simp only [mem_image, mem_filter, mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hi
        obtain ⟨p, rfl⟩ := hc.surj i (by simpa using hlt i hi)
        exact ⟨p, hi, rfl⟩
    rw [← card_image_of_injective _ hc.inj, himg, List.toFinset_card_of_nodup hnd]

theorem IsCoding.pop_mask (hc : IsCoding P n dn idx) (s : Finset P) :
    ∀ f, pop (mask idx n s) f = (s.filter fun p => idx p < f).card
  | 0 => by simp [pop]
  | f + 1 => by
    classical
    rw [pop, hc.pop_mask s f]
    have hu : (s.filter fun p => idx p < f + 1) =
        (s.filter fun p => idx p < f) ∪ (s.filter fun p => idx p = f) := by
      ext p
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hp, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
      · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
        · exact ⟨hp, by omega⟩
        · exact ⟨hp, by omega⟩
    have hd : Disjoint (s.filter fun p => idx p < f) (s.filter fun p => idx p = f) := by
      rw [disjoint_left]
      intro p hp hp'
      have h1 := (mem_filter.1 hp).2
      have h2 := (mem_filter.1 hp').2
      omega
    rw [hu, card_union_of_disjoint hd]
    congr 1
    by_cases h : (mask idx n s).testBit f = true
    · obtain ⟨x, hx, rfl⟩ := (hc.testBit_mask s f).1 h
      have h1 : (s.filter fun p => idx p = idx x) = {x} := by
        ext p
        simp only [mem_filter, mem_singleton]
        exact ⟨fun hp => hc.inj hp.2, fun hp => by subst hp; exact ⟨hx, rfl⟩⟩
      rw [h, h1]
      rfl
    · have h1 : (s.filter fun p => idx p = f) = ∅ :=
        filter_eq_empty_iff.2 fun p hp hpf => h ((hc.testBit_mask s f).2 ⟨p, hp, hpf⟩)
      rw [Bool.not_eq_true] at h
      rw [h, h1]
      rfl

theorem IsCoding.pop_mask_eq_card (hc : IsCoding P n dn idx) (s : Finset P) :
    pop (mask idx n s) n = s.card := by
  rw [hc.pop_mask s n, filter_true_of_mem fun p _ => hc.lt p]

/-- Down-sets with the same number of elements are pairwise incomparable. -/
theorem isAntichain_of_card_eq {r : ℕ} {F : Finset (Jst P)} (h : ∀ D ∈ F, D.val.card = r) :
    IsAntichain (· ≤ ·) (F : Set (Jst P)) := by
  intro D hD D' hD' hne hle
  apply hne
  apply Jst.val_injective
  apply eq_of_subset_of_card_le (Jst.le_iff.1 hle)
  rw [h D (mem_coe.1 hD), h D' (mem_coe.1 hD')]

/-- **A layer of `J*(P)`.**  A checked list of `A.length` down-set masks with `r` elements each
gives `A.length` nonempty down-sets of `P` with exactly `r` elements. -/
theorem IsCoding.exists_layer [Finite P] (hc : IsCoding P n dn idx) {A : List ℕ} {r : ℕ}
    (h : chkLayer dn n r A = true) :
    ∃ F : Finset (Jst P), F.card = A.length ∧ ∀ D ∈ F, D.val.card = r := by
  classical
  have := Fintype.ofFinite P
  rw [chkLayer, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinc, hall⟩ := h
  obtain ⟨hp, h0⟩ := incr_sound hinc
  have hall' : ∀ m ∈ A, m < 2 ^ n ∧ closedUpTo dn m n = true ∧ pop m n = r := by
    intro m hm
    have := hall m hm
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨univ.filter fun D : Jst P => mask idx n D.val ∈ A, ?_, ?_⟩
  · have himg : (univ.filter fun D : Jst P => mask idx n D.val ∈ A).image
        (fun D => mask idx n D.val) = A.toFinset := by
      ext m
      simp only [mem_image, mem_filter, mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨D, hD, rfl⟩
        exact hD
      · intro hm
        obtain ⟨h2, hcl, -⟩ := hall' m hm
        have hne : (unmask idx m : Finset P).Nonempty := by
          rw [nonempty_iff_ne_empty]
          intro he
          have := hc.mask_unmask (idx := idx) h2
          rw [he, hc.mask_empty] at this
          have := h0 m hm
          omega
        refine ⟨Jst.mk (unmask idx m) (hc.isLowerFinset_unmask hcl) hne, ?_, ?_⟩
        · change mask idx n (unmask idx m) ∈ A
          rwa [hc.mask_unmask h2]
        · exact hc.mask_unmask h2
    have hinj : Function.Injective fun D : Jst P => mask idx n D.val := fun D D' hDD =>
      Jst.val_injective (hc.mask_injective hDD)
    rw [← card_image_of_injective _ hinj, himg,
      List.toFinset_card_of_nodup (nodup_of_pairwise_lt hp)]
  · intro D hD
    rw [mem_filter] at hD
    rw [← hc.pop_mask_eq_card]
    exact (hall' _ hD.2).2.2

/-- A layer is an antichain of `J*(P)`. -/
theorem IsCoding.hasAntichain_jst [Finite P] (hc : IsCoding P n dn idx) {A : List ℕ} {r : ℕ}
    (h : chkLayer dn n r A = true) : HasAntichain (Jst P) A.length := by
  obtain ⟨F, hF, hr⟩ := hc.exists_layer h
  exact ⟨F, isAntichain_of_card_eq hr, hF⟩

end Jst

/-! ### The antichain `P_0(k)` -/

/-- The coding of the antichain on `Fin k`. -/
theorem isCoding_anti (k : ℕ) :
    IsCoding (Anti (Fin k)) k (fun i => 2 ^ i) (fun p => ((Anti.val p : Fin k) : ℕ)) where
  lt p := (Anti.val p).2
  inj p q h := Fin.ext h
  surj i hi := ⟨Anti.mk ⟨i, hi⟩, rfl⟩
  le_iff p q := by
    rw [Nat.testBit_two_pow, decide_eq_true_eq, Anti.le_iff]
    exact ⟨fun h => h ▸ rfl, fun h => (Fin.ext h).symm⟩
  mono p q h := by
    rw [Anti.le_iff] at h
    rw [h]

/-- The numbering of `P_0(k)`: the element `c` (a colour) gets the number `c`. -/
def idxAnti (k : ℕ) (p : LabelPoset k 0) : ℕ := ((Anti.val p : Fin k) : ℕ)

/-- The coding of `P_0(k)`. -/
theorem isCoding_labelPoset_zero (k : ℕ) :
    IsCoding (LabelPoset k 0) k (fun i => 2 ^ i) (idxAnti k) :=
  isCoding_anti k

end Num

end OnlineColouring
