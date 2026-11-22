module

public import OnlineColouring.NumGameCheck
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Function

/-!
# A checker for adversary certificates with null moves

Paper: Appendix D.3, the table of `V(m)`, lower bounds.

The adversary certificates of `NumGameCheck.lean` (`DLem`) answer every multiset that the algorithm
may give to the next block.  Often the adversary does not need the next block at all: after its
picks, the position *without* a new row is already winning.  By `Win.cons_row` (an extra row with
enough elements does not hurt the adversary) it then wins whatever the algorithm does, and one
reference replaces the whole list of answers.  Certificates that use this "null move" are much
smaller: for `m = 9` the certificate has 2 458 positions instead of 41 243, and for `m = 10` it has
107 285 positions instead of 3 194 237.

A lemma (`SLem`) therefore records the number `t` of the next block (the number of rows is no
longer `t`, because skipped blocks leave no row), the rows, the picks, the flag `skip` and the
references.  `chkSLem` checks a lemma, and `win_of_supto` concludes `Win C B []`.

To keep the certificates small, a reference carries only the renaming `σ` of the colours, not its
inverse: `permOK1` checks that `σ` maps the palette onto itself (the bit mask of its values is
`2^C - 1`), and `permOK1_sound` derives a left inverse.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-- The bit mask of the values of the renaming `sg` on the colours listed. -/
def valMask (sg : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: l => 2 ^ permFn sg c ||| valMask sg l

theorem testBit_valMask (sg : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    (valMask sg l).testBit i = true ↔ ∃ c ∈ l, permFn sg c = i
  | [], i => by simp [valMask]
  | c :: l, i => by
    rw [valMask, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
      testBit_valMask sg l i]
    simp

/-- `sg` codes a renaming that maps the palette `{0, …, C - 1}` onto itself. -/
def permOK1 (C sg : ℕ) : Bool := valMask sg (List.range C) == 2 ^ C - 1

theorem permOK1_sound {C sg : ℕ} (h : permOK1 C sg = true) :
    ∃ τ : ℕ → ℕ, ∀ c < C, permFn sg c < C ∧ τ (permFn sg c) = c := by
  rw [permOK1, beq_iff_eq] at h
  have hbit : ∀ i, (∃ c < C, permFn sg c = i) ↔ i < C := by
    intro i
    have := testBit_valMask sg (List.range C) i
    rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at this
    simpa using this.symm
  have himg : (Finset.range C).image (permFn sg) = Finset.range C := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    exact hbit i
  have hinj : Set.InjOn (permFn sg) (Finset.range C : Set ℕ) :=
    Finset.card_image_iff.1 (by rw [himg])
  refine ⟨Function.invFunOn (permFn sg) (Finset.range C : Set ℕ), fun c hc => ?_⟩
  exact ⟨(hbit _).1 ⟨c, hc, rfl⟩,
    hinj.leftInvOn_invFunOn (Finset.mem_coe.2 (Finset.mem_range.2 hc))⟩

/-- A lemma of an adversary certificate with null moves: the number of the next block, the
position, the colours picked, and either (`skip = true`) one reference for the position after the
picks without a new row, or (`skip = false`) a reference for every allowed multiset for the next
block, in the order of `allMs`.  A reference consists of the lemma referred to and the renaming
(coded as for `permFn`). -/
structure SLem where
  /-- The number of the next block. -/
  t : ℕ
  /-- The rows of the position. -/
  rows : List (List ℕ)
  /-- The colour picked in each row. -/
  picks : List ℕ
  /-- The adversary wins without the next block. -/
  skip : Bool
  /-- The references. -/
  resp : List (ℕ × ℕ)

instance : Inhabited SLem := ⟨⟨0, [], [], false, []⟩⟩

/-- The adversary beats the palette from the position of the lemma. -/
def SGood (C : ℕ) (B : List ℕ) (L : SLem) : Prop :=
  Win C (B.drop L.t) (toRows L.rows)

/-- The check of a reference: an earlier lemma for the block `t'` whose position is `rows` up to
the renaming and the order of the rows. -/
def chkSRef (C : ℕ) (T : ℕ → SLem) (i t' : ℕ) (rows : List (List ℕ)) (e : ℕ × ℕ) : Bool :=
  decide (e.1 < i) && (T e.1).t == t' && permOK1 C e.2 &&
    (renameRows e.2 rows).isPerm (T e.1).rows

/-- The check of the lemma number `i`. -/
def chkSLem (C : ℕ) (B : List ℕ) (T : ℕ → SLem) (i : ℕ) : Bool :=
  match B.drop (T i).t, applyPicks (T i).rows (T i).picks with
  | bt :: bs', some rows' =>
    (T i).rows.all (fun r => r.all fun c => decide (c < C)) &&
      (if (T i).skip then
        decide (bs'.length ≤ bt) &&
          (match (T i).resp with
          | [e] => chkSRef C T i ((T i).t + 1) rows' e
          | _ => false)
      else
        zipAll (fun M e => chkSRef C T i ((T i).t + 1) (M :: rows') e)
          (allMs (allowed C (T i).picks) bt) (T i).resp)
  | _, _ => false

theorem win_of_chkSRef {C : ℕ} {B bs' : List ℕ} {T : ℕ → SLem} {i t' : ℕ}
    {rows : List (List ℕ)} {e : ℕ × ℕ} (h : chkSRef C T i t' rows e = true)
    (ih : ∀ j < i, SGood C B (T j)) (hB : B.drop t' = bs')
    (hrows : ∀ r ∈ toRows rows, ∀ c ∈ r, c < C) : Win C bs' (toRows rows) := by
  simp only [chkSRef, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hji, ht⟩, hperm⟩, hisp⟩ := h
  have hj := ih _ hji
  rw [SGood, ht, hB] at hj
  have h2 := hj.perm (toRows_perm hisp).symm
  rw [toRows_renameRows] at h2
  obtain ⟨τ, hτ⟩ := permOK1_sound hperm
  exact Win.of_map (σ := permFn e.2) (τ := τ) hτ hrows h2

theorem sGood_of_chk {C : ℕ} {B : List ℕ} {T : ℕ → SLem} {i : ℕ}
    (h : chkSLem C B T i = true) (ih : ∀ j < i, SGood C B (T j)) : SGood C B (T i) := by
  rw [SGood]
  rw [chkSLem] at h
  rcases hB : B.drop (T i).t with _ | ⟨bt, bs'⟩
  · rw [hB] at h
    simp at h
  · rcases hpk : applyPicks (T i).rows (T i).picks with _ | rows'
    · rw [hB, hpk] at h
      simp at h
    · rw [hB, hpk] at h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨hpal, hrest⟩ := h
      obtain ⟨hP, -, hsub⟩ := picked_of_applyPicks hpk
      have hdrop : B.drop ((T i).t + 1) = bs' := by
        rw [← List.tail_drop, hB]
        rfl
      have hrows' : ∀ r ∈ toRows rows', ∀ c ∈ r, c < C := by
        intro r hr c hc
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
        obtain ⟨r0, hr0, hx⟩ := hsub r' hr'
        exact hpal r0 hr0 c (hx c (Multiset.mem_coe.1 hc))
      refine ⟨toRows rows', (T i).picks.toFinset, hP, fun M hM hMF => ?_⟩
      by_cases hskip : (T i).skip = true
      · simp only [hskip, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hrest
        obtain ⟨hlen, href⟩ := hrest
        rcases hresp : (T i).resp with _ | ⟨e, _ | ⟨e', l⟩⟩
        · rw [hresp] at href
          simp at href
        · rw [hresp] at href
          exact Win.cons_row (by rw [hM]; exact hlen) (win_of_chkSRef href ih hdrop hrows')
        · rw [hresp] at href
          simp at href
      · simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hrest
        obtain ⟨l, hl, rfl⟩ := exists_mem_allMs (allowed C (T i).picks) bt M hM (fun c hc => by
          rw [allowed, List.mem_filter, List.mem_range, Bool.not_eq_true']
          refine ⟨(hMF c hc).1, ?_⟩
          rw [← Bool.not_eq_true, List.contains_iff_mem]
          exact fun hmem => (hMF c hc).2 (List.mem_toFinset.2 hmem))
        obtain ⟨e, -, he⟩ := zipAll_sound hrest l hl
        refine win_of_chkSRef (rows := l :: rows') he ih hdrop ?_
        intro r hr c hc
        rw [toRows, List.map_cons, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact (hMF c hc).1
        · exact hrows' r hr c hc

/-- All lemmas below `n` are good. -/
def SUpto (C : ℕ) (B : List ℕ) (T : ℕ → SLem) (n : ℕ) : Prop := ∀ j < n, SGood C B (T j)

/-- The check of the lemmas `lo, …, lo + len - 1`. -/
def chkSRange (C : ℕ) (B : List ℕ) (T : ℕ → SLem) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => chkSRange C B T lo len && chkSLem C B T (lo + len)

theorem SUpto.zero {C : ℕ} {B : List ℕ} {T : ℕ → SLem} : SUpto C B T 0 :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem SUpto.add {C : ℕ} {B : List ℕ} {T : ℕ → SLem} {lo : ℕ} (h : SUpto C B T lo) :
    ∀ {len : ℕ}, chkSRange C B T lo len = true → SUpto C B T (lo + len)
  | 0, _ => h
  | len + 1, hc => by
    rw [chkSRange, Bool.and_eq_true] at hc
    have h1 : SUpto C B T (lo + len) := h.add hc.1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < lo + len + 1 from hj) with hj | rfl
    · exact h1 j hj
    · exact sGood_of_chk hc.2 h1

/-- **Soundness of the checker with null moves.**  If all lemmas up to the root `r` are checked
and the root is the empty position before block `0`, the adversary beats the palette in the whole
game. -/
theorem win_of_supto {C : ℕ} {B : List ℕ} {T : ℕ → SLem} {r : ℕ} (h : SUpto C B T (r + 1))
    (hr : (T r).t = 0 ∧ (T r).rows = []) : Win C B [] := by
  have := h r (Nat.lt_succ_self r)
  rw [SGood, hr.1, hr.2] at this
  exact this

end Num

end OnlineColouring
