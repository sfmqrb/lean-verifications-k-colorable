module

public import OnlineColouring.NumGame
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Data.Finset.Dedup

/-!
# Verified checkers for one-level certificates

Paper: Appendix D.3, the table of `V(m)`.  The certificates of the supplementary
material (`repro/certificates/one_m*_C*_ALG.txt`, `one_m*_C*_ADV.txt`) are strategies for the
abstract one-level game of `NumGame.lean`.  This file contains two checkers, written as Bool
functions that the kernel evaluates (`decide +kernel`), and their soundness proofs.

A certificate is a table of *lemmas*, numbered so that every reference goes to a smaller number.
A lemma is a position: the list of its rows, each row a list of colours.

* Algorithm certificates (`ALem`, upper bounds `V(m) ≤ C`): the lemma lists, for every way of
  picking one colour from each row (in the order of the verified enumeration `allPicks`), the
  colours `M` of the next block, a reference to the lemma for the position `M :: rows'`, and the
  renaming of the colours (with its inverse) under which that position is, up to the order of the
  rows, the position of the lemma referred to.  `chkALem` checks all this, and
  `AUpto.add`/`surv_of_aupto` conclude `Surv C B []`.
* Adversary certificates (`DLem`, lower bounds `V(m) ≥ C + 1`): the lemma gives the picks of the
  adversary and, for every multiset of allowed colours of the palette (in the order of the verified
  enumeration `allMs`), a reference and a renaming.  `chkDLem`, `DUpto.add`, `win_of_dupto`
  conclude `Win C B []`.

The converter that writes the tables from the certificates is not trusted.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-! ### Small verified list functions -/

/-- The distinct elements of a list. -/
def distinct : List ℕ → List ℕ
  | [] => []
  | a :: l => if l.contains a then distinct l else a :: distinct l

theorem mem_distinct {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ∈ distinct l
  | b :: l, h => by
    rw [distinct]
    by_cases hc : l.contains b = true
    · simp only [hc, ↓reduceIte]
      rcases List.mem_cons.1 h with rfl | h
      · exact mem_distinct (List.contains_iff_mem.1 hc)
      · exact mem_distinct h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_distinct h)

/-- Insertion into a sorted list. -/
def ins (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

/-- Insertion sort. -/
def sortRow : List ℕ → List ℕ
  | [] => []
  | a :: l => ins a (sortRow l)

theorem ins_perm (a : ℕ) : ∀ l : List ℕ, (ins a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    rw [ins]
    by_cases h : a ≤ b
    · simp only [h, ↓reduceIte]
      exact List.Perm.refl _
    · simp only [h, ↓reduceIte]
      exact ((ins_perm a l).cons b).trans (List.Perm.swap a b l)

theorem sortRow_perm : ∀ l : List ℕ, (sortRow l).Perm l
  | [] => List.Perm.refl _
  | a :: l => (ins_perm a (sortRow l)).trans ((sortRow_perm l).cons a)

/-- `f` holds for all pairs of corresponding entries, and the lists have the same length. -/
def zipAll {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: l, b :: l' => f a b && zipAll f l l'
  | _, _ => false

theorem zipAll_sound {α β : Type} {f : α → β → Bool} : ∀ {l : List α} {l' : List β},
    zipAll f l l' = true → ∀ a ∈ l, ∃ b ∈ l', f a b = true
  | [], [], _, a, ha => absurd ha List.not_mem_nil
  | [], _ :: _, h, _, _ => by simp [zipAll] at h
  | _ :: _, [], h, _, _ => by simp [zipAll] at h
  | a' :: l, b' :: l', h, a, ha => by
    rw [zipAll, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b', List.mem_cons_self, h.1⟩
    · obtain ⟨b, hb, hf⟩ := zipAll_sound h.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hf⟩

/-- A table stored as a tree of lists with four levels: the entry `i` is at the positions
`i / 4096`, `i / 256 % 16`, `i / 16 % 16` and `i % 16`.  The positions at the three lower levels
are below 16, so that a lookup takes at most 48 list steps below the top level. -/
def tbl {α : Type} [Inhabited α] (t : List (List (List (List α)))) (i : ℕ) : α :=
  (((t.getD (i / 4096) []).getD (i / 256 % 16) []).getD (i / 16 % 16) []).getD (i % 16) default

/-! ### Renamings of the palette -/

/-- A renaming of the colours `0, …, 7`, coded by a number: the colour `c` is renamed to the
`c`-th octal digit of `sg`. -/
def permFn (sg c : ℕ) : ℕ := (sg >>> (3 * c)) % 8

/-- `sg` and `tu` code mutually inverse renamings of the palette `{0, …, C - 1}`. -/
def permOK (C sg tu : ℕ) : Bool :=
  (List.range C).all fun c =>
    decide (permFn sg c < C) && decide (permFn tu c < C) &&
      permFn tu (permFn sg c) == c && permFn sg (permFn tu c) == c

theorem permOK_sound {C sg tu : ℕ} (h : permOK C sg tu = true) :
    (∀ c < C, permFn sg c < C ∧ permFn tu (permFn sg c) = c) ∧
      ∀ c < C, permFn tu c < C ∧ permFn sg (permFn tu c) = c := by
  rw [permOK, List.all_eq_true] at h
  have h' : ∀ c < C, (permFn sg c < C ∧ permFn tu c < C) ∧ permFn tu (permFn sg c) = c ∧
      permFn sg (permFn tu c) = c := by
    intro c hc
    have := h c (List.mem_range.2 hc)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  exact ⟨fun c hc => ⟨(h' c hc).1.1, (h' c hc).2.1⟩, fun c hc => ⟨(h' c hc).1.2, (h' c hc).2.2⟩⟩

/-- The rows of a position as multisets. -/
def toRows (rows : List (List ℕ)) : List (Multiset ℕ) := rows.map Multiset.ofList

/-- Rename the colours of a position and sort every row. -/
def renameRows (sg : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map fun r => sortRow (r.map (permFn sg))

theorem toRows_renameRows (sg : ℕ) (rows : List (List ℕ)) :
    toRows (renameRows sg rows) = (toRows rows).map (Multiset.map (permFn sg)) := by
  rw [toRows, renameRows, toRows, List.map_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  change ((sortRow (r.map (permFn sg)) : List ℕ) : Multiset ℕ) = _
  rw [Multiset.coe_eq_coe.2 (sortRow_perm _)]
  rfl

theorem toRows_perm {l₁ l₂ : List (List ℕ)} (h : l₁.isPerm l₂ = true) :
    (toRows l₁).Perm (toRows l₂) :=
  List.Perm.map Multiset.ofList (List.isPerm_iff.1 h)

/-! ### Picks -/

/-- All ways to remove one element from each row, each with the list of the removed elements. -/
def allPicks : List (List ℕ) → List (List (List ℕ) × List ℕ)
  | [] => [([], [])]
  | r :: rs =>
    (allPicks rs).flatMap fun p => (distinct r).map fun c => (r.erase c :: p.1, c :: p.2)

theorem length_of_mem_allPicks : ∀ {rows : List (List ℕ)} {p : List (List ℕ) × List ℕ},
    p ∈ allPicks rows → p.1.length = rows.length
  | [], p, h => by
    rw [allPicks, List.mem_singleton] at h
    rw [h]
  | r :: rs, p, h => by
    rw [allPicks, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
    simp [length_of_mem_allPicks hq]

/-- `allPicks` is complete. -/
theorem exists_mem_allPicks : ∀ {rows : List (List ℕ)} {rows' : List (Multiset ℕ)}
    {F : Finset ℕ}, Picked (toRows rows) rows' F →
      ∃ p ∈ allPicks rows, rows' = toRows p.1 ∧ F = p.2.toFinset
  | [], _, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨([], []), by simp [allPicks], rfl, rfl⟩
  | r :: rs, _, _, h => by
    obtain ⟨c, hc, rs', F', hP, rfl, rfl⟩ := h
    obtain ⟨p, hp, rfl, rfl⟩ := exists_mem_allPicks hP
    refine ⟨(r.erase c :: p.1, c :: p.2), ?_, ?_, ?_⟩
    · rw [allPicks, List.mem_flatMap]
      exact ⟨p, hp, List.mem_map.2 ⟨c, mem_distinct (Multiset.mem_coe.1 hc), rfl⟩⟩
    · simp [toRows]
    · simp

/-- Remove the picked colour from each row (`none` if a pick is not in its row or the lengths
differ). -/
def applyPicks : List (List ℕ) → List ℕ → Option (List (List ℕ))
  | [], [] => some []
  | r :: rs, c :: cs =>
    if r.contains c then (applyPicks rs cs).map fun rs' => r.erase c :: rs' else none
  | _, _ => none

theorem picked_of_applyPicks : ∀ {rows : List (List ℕ)} {picks : List ℕ}
    {rows' : List (List ℕ)}, applyPicks rows picks = some rows' →
      Picked (toRows rows) (toRows rows') picks.toFinset ∧ rows'.length = rows.length ∧
        ∀ r' ∈ rows', ∃ r ∈ rows, ∀ c ∈ r', c ∈ r
  | [], [], rows', h => by
    simp only [applyPicks, Option.some.injEq] at h
    subst h
    exact ⟨⟨rfl, rfl⟩, rfl, fun r' hr' => absurd hr' List.not_mem_nil⟩
  | [], _ :: _, _, h => by simp [applyPicks] at h
  | _ :: _, [], _, h => by simp [applyPicks] at h
  | r :: rs, c :: cs, rows', h => by
    rw [applyPicks] at h
    by_cases hc : r.contains c = true
    · simp only [hc, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨rs', hrs, rfl⟩ := h
      obtain ⟨hP, hlen, hsub⟩ := picked_of_applyPicks hrs
      refine ⟨⟨c, Multiset.mem_coe.2 (List.contains_iff_mem.1 hc), toRows rs', cs.toFinset, hP,
        by simp [toRows], by simp⟩, by simp [hlen], ?_⟩
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨r, List.mem_cons_self, fun x hx => List.mem_of_mem_erase hx⟩
      · obtain ⟨r0, hr0, hx⟩ := hsub r' hr'
        exact ⟨r0, List.mem_cons_of_mem _ hr0, hx⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-! ### Multisets of a given size -/

/-- All lists with `n` entries from the list `al` in which equal entries are adjacent and the
entries come in the order of `al`: one for each multiset of size `n` over `al`. -/
def allMs : List ℕ → ℕ → List (List ℕ)
  | [], n => if n = 0 then [[]] else []
  | a :: al, n =>
    (List.range (n + 1)).flatMap fun k => (allMs al (n - k)).map fun l => List.replicate k a ++ l

/-- `allMs` is complete. -/
theorem exists_mem_allMs : ∀ (al : List ℕ) (n : ℕ) (M : Multiset ℕ), M.card = n →
    (∀ c ∈ M, c ∈ al) → ∃ l ∈ allMs al n, (l : Multiset ℕ) = M
  | [], n, M, hn, hM => by
    have hM0 : M = 0 := Multiset.eq_zero_of_forall_notMem fun c hc => List.not_mem_nil (hM c hc)
    subst hM0
    rw [Multiset.card_zero] at hn
    subst hn
    exact ⟨[], by simp [allMs], rfl⟩
  | a :: al, n, M, hn, hM => by
    have hsplit := Multiset.filter_add_not (fun c => c = a) M
    rw [Multiset.filter_eq'] at hsplit
    have hk : M.count a ≤ n := hn ▸ Multiset.count_le_card a M
    have hcard : (M.filter fun c => ¬ c = a).card = n - M.count a := by
      have := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.card_replicate, hn] at this
      omega
    obtain ⟨l, hl, hlM⟩ := exists_mem_allMs al (n - M.count a) (M.filter fun c => ¬ c = a) hcard
      (fun c hc => by
        rw [Multiset.mem_filter] at hc
        rcases List.mem_cons.1 (hM c hc.1) with h | h
        · exact absurd h hc.2
        · exact h)
    refine ⟨List.replicate (M.count a) a ++ l, ?_, ?_⟩
    · rw [allMs, List.mem_flatMap]
      exact ⟨M.count a, List.mem_range.2 (by omega), List.mem_map.2 ⟨l, hl, rfl⟩⟩
    · rw [← Multiset.coe_add, hlM, Multiset.coe_replicate, hsplit]

/-! ### Algorithm certificates -/

/-- A lemma of an algorithm certificate: a position and, for every way of picking, the colours of
the next block, the lemma referred to, and the renaming with its inverse. -/
structure ALem where
  /-- The rows of the position. -/
  rows : List (List ℕ)
  /-- For every element of `allPicks rows`: the next block, the reference, the renaming and its
  inverse (coded as for `permFn`). -/
  resp : List (List ℕ × ℕ × ℕ × ℕ)

instance : Inhabited ALem := ⟨⟨[], []⟩⟩

/-- The algorithm survives from the position of the lemma. -/
def AGood (C : ℕ) (B : List ℕ) (L : ALem) : Prop :=
  Surv C (B.drop L.rows.length) (toRows L.rows)

/-- The check of one response; `bs` lists the sizes of the remaining blocks. -/
def chkAResp (C : ℕ) (bs : List ℕ) (T : ℕ → ALem) (i : ℕ) (p : List (List ℕ) × List ℕ)
    (e : List ℕ × ℕ × ℕ × ℕ) : Bool :=
  match bs with
  | [] => true
  | bt :: bs' =>
    e.1.length == bt && e.1.all (fun c => decide (c < C) && !p.2.contains c) &&
      (bs'.isEmpty || (decide (e.2.1 < i) && permOK C e.2.2.1 e.2.2.2 &&
        (renameRows e.2.2.1 (e.1 :: p.1)).isPerm (T e.2.1).rows))

/-- The check of the lemma number `i`. -/
def chkALem (C : ℕ) (B : List ℕ) (T : ℕ → ALem) (i : ℕ) : Bool :=
  zipAll (chkAResp C (B.drop (T i).rows.length) T i) (allPicks (T i).rows) (T i).resp

theorem aGood_of_chk {C : ℕ} {B : List ℕ} {T : ℕ → ALem} {i : ℕ}
    (h : chkALem C B T i = true) (ih : ∀ j < i, AGood C B (T j)) : AGood C B (T i) := by
  rw [AGood]
  rw [chkALem] at h
  rcases hB : B.drop (T i).rows.length with _ | ⟨bt, bs'⟩
  · trivial
  · rw [hB] at h
    intro rows' F hP
    obtain ⟨p, hp, rfl, rfl⟩ := exists_mem_allPicks hP
    obtain ⟨e, -, he⟩ := zipAll_sound h p hp
    simp only [chkAResp, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', Bool.or_eq_true, List.isEmpty_iff] at he
    obtain ⟨⟨hlen, hall⟩, hrest⟩ := he
    refine ⟨(e.1 : Multiset ℕ), by simpa using hlen, ?_, ?_⟩
    · intro c hc
      have hc' := hall c (Multiset.mem_coe.1 hc)
      refine ⟨hc'.1, fun hF => ?_⟩
      have h1 : p.2.contains c = true := List.contains_iff_mem.2 (List.mem_toFinset.1 hF)
      rw [hc'.2] at h1
      exact Bool.false_ne_true h1
    · rcases hrest with hnil | ⟨⟨hji, hperm⟩, hisp⟩
      · rw [hnil]
        trivial
      · have hj := ih _ hji
        rw [AGood] at hj
        have hlenj : (T e.2.1).rows.length = (T i).rows.length + 1 := by
          have := (List.isPerm_iff.1 hisp).length_eq
          rw [renameRows, List.length_map, List.length_cons, length_of_mem_allPicks hp] at this
          exact this.symm
        have hdrop : B.drop (T e.2.1).rows.length = bs' := by
          rw [hlenj, ← List.tail_drop, hB]
          rfl
        rw [hdrop] at hj
        have h2 := hj.perm (toRows_perm hisp).symm
        rw [toRows_renameRows] at h2
        exact Surv.of_map (permOK_sound hperm).2 h2

/-- All lemmas below `n` are good. -/
def AUpto (C : ℕ) (B : List ℕ) (T : ℕ → ALem) (n : ℕ) : Prop := ∀ j < n, AGood C B (T j)

/-- The check of the lemmas `lo, …, lo + len - 1`. -/
def chkARange (C : ℕ) (B : List ℕ) (T : ℕ → ALem) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => chkARange C B T lo len && chkALem C B T (lo + len)

theorem AUpto.zero {C : ℕ} {B : List ℕ} {T : ℕ → ALem} : AUpto C B T 0 :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem AUpto.add {C : ℕ} {B : List ℕ} {T : ℕ → ALem} {lo : ℕ} (h : AUpto C B T lo) :
    ∀ {len : ℕ}, chkARange C B T lo len = true → AUpto C B T (lo + len)
  | 0, _ => h
  | len + 1, hc => by
    rw [chkARange, Bool.and_eq_true] at hc
    have h1 : AUpto C B T (lo + len) := h.add hc.1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < lo + len + 1 from hj) with hj | rfl
    · exact h1 j hj
    · exact aGood_of_chk hc.2 h1

/-- **Soundness of the algorithm checker.**  If all lemmas up to the root `r` are checked and the
root is the empty position, the algorithm survives the whole game with the palette. -/
theorem surv_of_aupto {C : ℕ} {B : List ℕ} {T : ℕ → ALem} {r : ℕ} (h : AUpto C B T (r + 1))
    (hr : (T r).rows = []) : Surv C B [] := by
  have := h r (Nat.lt_succ_self r)
  rw [AGood, hr] at this
  exact this

/-! ### Adversary certificates -/

/-- A lemma of an adversary certificate: a position, the colours that the adversary picks (one in
each row), and for every allowed multiset for the next block the lemma referred to and the
renaming with its inverse. -/
structure DLem where
  /-- The rows of the position. -/
  rows : List (List ℕ)
  /-- The colour picked in each row. -/
  picks : List ℕ
  /-- For every element of `allMs`: the reference, the renaming and its inverse (coded as for
  `permFn`). -/
  resp : List (ℕ × ℕ × ℕ)

instance : Inhabited DLem := ⟨⟨[], [], []⟩⟩

/-- The adversary beats the palette from the position of the lemma. -/
def DGood (C : ℕ) (B : List ℕ) (L : DLem) : Prop :=
  Win C (B.drop L.rows.length) (toRows L.rows)

/-- The colours of the palette that are not picked. -/
def allowed (C : ℕ) (picks : List ℕ) : List ℕ := (List.range C).filter fun c => !picks.contains c

/-- The check of the lemma number `i`. -/
def chkDLem (C : ℕ) (B : List ℕ) (T : ℕ → DLem) (i : ℕ) : Bool :=
  match B.drop (T i).rows.length, applyPicks (T i).rows (T i).picks with
  | bt :: _, some rows' =>
    (T i).rows.all (fun r => r.all fun c => decide (c < C)) &&
      zipAll (fun M e => decide (e.1 < i) && permOK C e.2.1 e.2.2 &&
          (renameRows e.2.1 (M :: rows')).isPerm (T e.1).rows)
        (allMs (allowed C (T i).picks) bt) (T i).resp
  | _, _ => false

theorem dGood_of_chk {C : ℕ} {B : List ℕ} {T : ℕ → DLem} {i : ℕ}
    (h : chkDLem C B T i = true) (ih : ∀ j < i, DGood C B (T j)) : DGood C B (T i) := by
  rw [DGood]
  rw [chkDLem] at h
  rcases hB : B.drop (T i).rows.length with _ | ⟨bt, bs'⟩
  · rw [hB] at h
    simp at h
  · rcases hpk : applyPicks (T i).rows (T i).picks with _ | rows'
    · rw [hB, hpk] at h
      simp at h
    · rw [hB, hpk] at h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨hpal, hzip⟩ := h
      obtain ⟨hP, hlen, hsub⟩ := picked_of_applyPicks hpk
      refine ⟨toRows rows', (T i).picks.toFinset, hP, fun M hM hMF => ?_⟩
      obtain ⟨l, hl, rfl⟩ := exists_mem_allMs (allowed C (T i).picks) bt M hM (fun c hc => by
        rw [allowed, List.mem_filter, List.mem_range, Bool.not_eq_true']
        refine ⟨(hMF c hc).1, ?_⟩
        rw [← Bool.not_eq_true, List.contains_iff_mem]
        exact fun hmem => (hMF c hc).2 (List.mem_toFinset.2 hmem))
      obtain ⟨e, -, he⟩ := zipAll_sound hzip l hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      obtain ⟨⟨hji, hperm⟩, hisp⟩ := he
      have hj := ih _ hji
      rw [DGood] at hj
      have hlenj : (T e.1).rows.length = (T i).rows.length + 1 := by
        have := (List.isPerm_iff.1 hisp).length_eq
        rw [renameRows, List.length_map, List.length_cons, hlen] at this
        exact this.symm
      have hdrop : B.drop (T e.1).rows.length = bs' := by
        rw [hlenj, ← List.tail_drop, hB]
        rfl
      rw [hdrop] at hj
      have h2 := hj.perm (toRows_perm hisp).symm
      rw [toRows_renameRows] at h2
      refine Win.of_map (σ := permFn e.2.1) (τ := permFn e.2.2) (permOK_sound hperm).1 ?_ h2
      intro r hr c hc
      rw [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact (hMF c hc).1
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
        obtain ⟨r0, hr0, hx⟩ := hsub r' hr'
        exact hpal r0 hr0 c (hx c (Multiset.mem_coe.1 hc))

/-- All lemmas below `n` are good. -/
def DUpto (C : ℕ) (B : List ℕ) (T : ℕ → DLem) (n : ℕ) : Prop := ∀ j < n, DGood C B (T j)

/-- The check of the lemmas `lo, …, lo + len - 1`. -/
def chkDRange (C : ℕ) (B : List ℕ) (T : ℕ → DLem) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => chkDRange C B T lo len && chkDLem C B T (lo + len)

theorem DUpto.zero {C : ℕ} {B : List ℕ} {T : ℕ → DLem} : DUpto C B T 0 :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem DUpto.add {C : ℕ} {B : List ℕ} {T : ℕ → DLem} {lo : ℕ} (h : DUpto C B T lo) :
    ∀ {len : ℕ}, chkDRange C B T lo len = true → DUpto C B T (lo + len)
  | 0, _ => h
  | len + 1, hc => by
    rw [chkDRange, Bool.and_eq_true] at hc
    have h1 : DUpto C B T (lo + len) := h.add hc.1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < lo + len + 1 from hj) with hj | rfl
    · exact h1 j hj
    · exact dGood_of_chk hc.2 h1

/-- **Soundness of the adversary checker.**  If all lemmas up to the root `r` are checked and the
root is the empty position, the adversary beats the palette in the whole game. -/
theorem win_of_dupto {C : ℕ} {B : List ℕ} {T : ℕ → DLem} {r : ℕ} (h : DUpto C B T (r + 1))
    (hr : (T r).rows = []) : Win C B [] := by
  have := h r (Nat.lt_succ_self r)
  rw [DGood, hr] at this
  exact this

end Num

end OnlineColouring
