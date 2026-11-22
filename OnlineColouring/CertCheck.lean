module

public import OnlineColouring.CertGame

/-!
# A verified checker for adversary strategy DAGs (upper bounds on `N_k(c)`)

Proposition B.4 (exact values) of Appendix B, upper bounds.  The supplementary material
(`repro/certificates/dag_k*_C*.gen.txt`) stores adversary strategies as DAGs of
*lemmas*; the Python program `check_adversary_dag.py` replays them.  This file is a Lean version
of that checker together with a proof that it is sound: if `checkLem` accepts every lemma of a
table `T` and the last lemma starts from the empty position with height at most `N`, then
`NkLE k C N`, i.e. `N_k(C) ≤ N` in the sense of Definition 4.2 (`nkLE_of_cert`).

A lemma (`Lem`) consists of a start position `pos` (for each vertex its set of earlier neighbours,
as a bit mask, and its colour; the colours are exactly `1..m`), the earlier neighbours `nb` (a bit
mask) of the vertex that the
adversary presents, a bound `h` on the number of further vertices, and for every answer
`x ∈ {1, …, m+1}` an outcome: `none` (the adversary stops: `C` colours are in use) or
`some (j, p, sig, wits)` (continue with the earlier lemma `j`, whose start position is dominated
by the current position via the vertex map `p` and the colour map `sig`).  In all certificates of
the paper every lemma consists of one move, so this is the format of the files, up to syntax and
up to the witnesses `wit`, `sig`, `wits`, which the files leave to the checker to find and which
the (untrusted) converter listed in `docs/cert_converter.md` adds.  The converter also
renumbers the vertices of every start position so that the enumeration of its colourings has
few dead ends; any numbering is sound, because a position is just a history.

What the checker verifies, for every answer `x` that is legal (not the colour of a neighbour):
* outcome `none`: at least `C` colours are in use, and the graph is `k`-colourable (`wit` is a
  proper `k`-colouring, verified by `isColM`);
* outcome `some (j, p, sig, wits)`: `j` is an earlier lemma with smaller height, `p` is injective
  into the current position, the colours correspond under the injective map `sig` (`colCheck`),
  and every proper `k`-colouring of the start position of lemma `j`, transported by `p`, extends
  to a proper `k`-colouring of the current position (`allExt`: all colourings are enumerated up to
  renaming of the colours, and for each of them the next element of `wits` must be an extension,
  verified by `isColM` and `agree`).

Soundness rests on `Force.transfer` and `Force.recolour` of `CertGame.lean`.  Answers outside
`{1, …, m+1}` are covered by `Force.recolour`, and the enumeration up to renaming by the
invariance of extendability under permutations of the colours.  Unlike the Python checker, the
Lean checker does not test that the graph stays `k`-colourable after *every* move, only at the
end of every play; this is what Definition 4.2 asks for (and it implies the former, since the
graphs of a play are nested).

The checker is evaluated by the kernel (`decide +kernel`), without `native_decide`.  It is
written with the primitive operations on `Nat` that the kernel evaluates with GMP (`Nat.land`,
`Nat.lor`, `Nat.shiftRight`, `Nat.ble`, …) and with sets of vertices and colours as bit masks.
-/

@[expose] public section

namespace OnlineColouring

namespace Cert

open Finset

/-! ### Arithmetic on bit masks, written with the primitives that the kernel evaluates fast -/

/-- Bit `v` of `a` (equal to `a.testBit v`, see `tb_eq`). -/
def tb (a v : ℕ) : Bool := Nat.ble 1 (Nat.land (Nat.shiftRight a v) 1)

theorem tb_eq (a v : ℕ) : tb a v = a.testBit v := by
  change Nat.ble 1 ((a >>> v) &&& 1) = (1 &&& (a >>> v) != 0)
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (a >>> v) with h | h <;> rw [h] <;> rfl

theorem lor_eq (x y : ℕ) : Nat.lor x y = x ||| y := rfl

theorem land_eq (x y : ℕ) : Nat.land x y = x &&& y := rfl

theorem pow_eq (x y : ℕ) : Nat.pow x y = x ^ y := rfl

/-- The set of the positions of the binary digits `1` of `m`. -/
def bits (m : ℕ) : Finset ℕ := (range m).filter fun i => m.testBit i

theorem mem_bits {m i : ℕ} : i ∈ bits m ↔ m.testBit i = true := by
  simp only [bits, mem_filter, mem_range, and_iff_right_iff_imp]
  intro h
  exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit h)

theorem testBit_and_eq_zero {a b u : ℕ} (h : a &&& b = 0) (ha : a.testBit u = true)
    (hb : b.testBit u = true) : False := by
  have := Nat.testBit_and a b u
  rw [h, Nat.zero_testBit, ha, hb] at this
  simp at this

theorem lt_of_testBit {a n u : ℕ} (h : a < 2 ^ n) (hu : a.testBit u = true) : u < n := by
  by_contra hn
  have : a < 2 ^ u := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hn))
  rw [Nat.testBit_lt_two_pow this] at hu
  simp at hu

theorem getD_of_lt {l : List ℕ} {i : ℕ} (d : ℕ) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Identity functions that make the kernel evaluate a number, a Boolean, or a list of numbers
completely before it is used. -/
def forceNat {α : Type} : ℕ → (ℕ → α) → α
  | 0, f => f 0
  | a + 1, f => f (a + 1)

theorem forceNat_eq {α : Type} : ∀ (a : ℕ) (f : ℕ → α), forceNat a f = f a
  | 0, _ => rfl
  | _ + 1, _ => rfl

@[inherit_doc forceNat]
def forceBool {α : Type} : Bool → (Bool → α) → α
  | true, f => f true
  | false, f => f false

theorem forceBool_eq {α : Type} : ∀ (b : Bool) (f : Bool → α), forceBool b f = f b
  | true, _ => rfl
  | false, _ => rfl

@[inherit_doc forceNat]
def forceList {α : Type} : List ℕ → (List ℕ → α) → α
  | [], f => f []
  | 0 :: l, f => forceList l fun l' => f (0 :: l')
  | (a + 1) :: l, f => forceList l fun l' => f ((a + 1) :: l')

theorem forceList_eq {α : Type} : ∀ (l : List ℕ) (f : List ℕ → α), forceList l f = f l
  | [], _ => rfl
  | 0 :: l, f => by rw [forceList, forceList_eq l]
  | (_ + 1) :: l, f => by rw [forceList, forceList_eq l]

/-- The colours `l[j]` of the vertices `j` with bit `u + j` of `N` set, as a bit mask. -/
def forbMask (N : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: l, u => Nat.lor (bif tb N u then Nat.pow 2 a else 0) (forceNat (u + 1) (forbMask N l))

theorem forbMask_spec {N : ℕ} : ∀ (l : List ℕ) (u c : ℕ), (forbMask N l u).testBit c = true →
    ∃ j, ∃ hj : j < l.length, N.testBit (u + j) = true ∧ l[j] = c
  | [], _, _, h => by simp [forbMask] at h
  | a :: l, u, c, h => by
    rw [forbMask, forceNat_eq, lor_eq, Nat.testBit_or, Bool.or_eq_true, tb_eq] at h
    rcases h with h | h
    · cases hN : N.testBit u
      · simp [hN] at h
      · rw [hN, Bool.cond_true, pow_eq, Nat.testBit_two_pow, decide_eq_true_eq] at h
        exact ⟨0, by simp, by simpa using hN, by simpa using h⟩
    · obtain ⟨j, hj, hN, hc⟩ := forbMask_spec l (u + 1) c h
      exact ⟨j + 1, by simpa using hj, by rw [← hN]; congr 1; omega, by simpa using hc⟩

/-- A list of numbers without repetition, none of which is a bit of `M`. -/
def nodupMask : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, M => !tb M a && forceNat (Nat.lor M (Nat.pow 2 a)) (nodupMask l)

theorem nodupMask_sound : ∀ {l : List ℕ} {M : ℕ}, nodupMask l M = true →
    l.Nodup ∧ ∀ a ∈ l, M.testBit a = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | a :: l, M, h => by
    simp only [nodupMask, forceNat_eq, Bool.and_eq_true, Bool.not_eq_true', tb_eq] at h
    obtain ⟨ih1, ih2⟩ := nodupMask_sound h.2
    have hbit : ∀ b ∈ l, M.testBit b = false ∧ a ≠ b := by
      intro b hb
      have := ih2 b hb
      rw [lor_eq, pow_eq, Nat.testBit_or, Bool.or_eq_false_iff, Nat.testBit_two_pow,
        decide_eq_false_iff_not] at this
      exact this
    refine ⟨List.nodup_cons.2 ⟨fun ha => (hbit a ha).2 rfl, ih1⟩, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact (hbit b hb).1

/-! ### Positions -/

/-- A position of the certificate: for every vertex, in order of arrival, the set of its earlier
neighbours (as a bit mask) and its colour. -/
abbrev Pos : Type := List (ℕ × ℕ)

/-- The history that a position stands for. -/
def toHist (P : Pos) : History := P.map fun e => (bits e.1, e.2)

@[simp] theorem length_toHist (P : Pos) : (toHist P).length = P.length := by simp [toHist]

theorem toHist_snoc (P : Pos) (nb : ℕ) (x : ℕ) :
    toHist (P ++ [(nb, x)]) = toHist P ++ [(bits nb, x)] := by simp [toHist]

theorem colourAt_toHist (P : Pos) (w : ℕ) : colourAt (toHist P) w = (P.getD w (0, 0)).2 := by
  simp only [colourAt, toHist, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[w]? <;> rfl

theorem getElem_toHist (P : Pos) (v : ℕ) (hv : v < (toHist P).length) :
    ((toHist P)[v]).1 = bits (P.getD v (0, 0)).1 := by
  have hv' : v < P.length := by simpa using hv
  simp [toHist, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv']

/-- The set of colours of a position, as a bit mask. -/
def colMask : Pos → ℕ
  | [] => 0
  | e :: P => Nat.lor (Nat.pow 2 e.2) (colMask P)

theorem testBit_colMask {c : ℕ} : ∀ {P : Pos}, (colMask P).testBit c = true ↔ ∃ e ∈ P, e.2 = c
  | [] => by simp [colMask]
  | e :: P => by
    rw [colMask, lor_eq, pow_eq, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, testBit_colMask (P := P)]
    simp

/-- The colours of the position are exactly `1, …, m`. -/
def validCols (P : Pos) (m : ℕ) : Bool :=
  Nat.beq (colMask P) (Nat.sub (Nat.pow 2 (Nat.succ m)) 2)

theorem testBit_two_pow_succ_sub_two (m c : ℕ) :
    (2 ^ (m + 1) - 2).testBit c = true ↔ 1 ≤ c ∧ c ≤ m := by
  have h : 2 ^ (m + 1) - 2 = 2 ^ 1 * (2 ^ m - 1) := by
    have := Nat.one_le_two_pow (n := m)
    rw [pow_succ]
    omega
  rw [h, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem usedColours_of_validCols {P : Pos} {m : ℕ} (h : validCols P m = true) :
    usedColours (toHist P) = Icc 1 m := by
  have h' : colMask P = 2 ^ (m + 1) - 2 := Nat.eq_of_beq_eq_true h
  ext c
  rw [mem_Icc, ← testBit_two_pow_succ_sub_two, ← h', testBit_colMask]
  simp only [usedColours, toHist, List.map_map, List.mem_toFinset, List.mem_map,
    Function.comp_apply]

/-! ### Checking a colouring -/

/-- Some class contains the vertex `v`. -/
def anyBit (v : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => tb a v || anyBit v l

/-- No class that contains the vertex `v` meets the set `N`. -/
def allOK (N v : ℕ) : List ℕ → Bool
  | [] => true
  | a :: l => (!tb a v || Nat.beq (Nat.land a N) 0) && allOK N v l

/-- `anyBit` and `allOK` for the vertices `v, v + 1, …` of the position. -/
def colOK (cls : List ℕ) : Pos → ℕ → Bool
  | [], _ => true
  | e :: P, v => anyBit v cls && allOK e.1 v cls && forceNat (v + 1) (colOK cls P)

/-- The colour classes `cls` (a list of at most `k` bit masks) cover the vertices of `P`, and no
class contains a vertex together with one of its earlier neighbours. -/
def isColM (k : ℕ) (P : Pos) (cls : List ℕ) : Bool :=
  Nat.ble cls.length k && colOK cls P 0

theorem anyBit_spec {v : ℕ} : ∀ {l : List ℕ}, anyBit v l = true → ∃ a ∈ l, a.testBit v = true
  | [], h => by simp [anyBit] at h
  | a :: l, h => by
    rw [anyBit, Bool.or_eq_true, tb_eq] at h
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · obtain ⟨b, hb, hbv⟩ := anyBit_spec h
      exact ⟨b, by simp [hb], hbv⟩

theorem allOK_spec {N v : ℕ} : ∀ {l : List ℕ}, allOK N v l = true →
    ∀ a ∈ l, a.testBit v = true → a &&& N = 0
  | [], _ => by simp
  | a :: l, h => by
    rw [allOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', tb_eq] at h
    intro b hb hbv
    rcases List.mem_cons.1 hb with rfl | hb
    · rcases h.1 with h1 | h1
      · rw [hbv] at h1
        exact absurd h1 (by simp)
      · exact Nat.eq_of_beq_eq_true h1
    · exact allOK_spec h.2 b hb hbv

theorem colOK_spec {cls : List ℕ} : ∀ {P : Pos} {v : ℕ}, colOK cls P v = true →
    ∀ j < P.length, (∃ a ∈ cls, a.testBit (v + j) = true) ∧
      ∀ a ∈ cls, a.testBit (v + j) = true → a &&& (P.getD j (0, 0)).1 = 0
  | [], _, _ => by simp
  | e :: P, v, h => by
    rw [colOK, forceNat_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    intro j hj
    rcases j with _ | j
    · exact ⟨anyBit_spec h.1.1, by simpa using allOK_spec h.1.2⟩
    · have := colOK_spec h.2 j (by simpa using hj)
      rw [show v + 1 + j = v + (j + 1) by omega] at this
      simpa using this

theorem isColM_spec {k : ℕ} {P : Pos} {cls : List ℕ} (h : isColM k P cls = true) :
    cls.length ≤ k ∧ ∀ v < P.length, (∃ a ∈ cls, a.testBit v = true) ∧
      ∀ a ∈ cls, a.testBit v = true → a &&& (P.getD v (0, 0)).1 = 0 := by
  rw [isColM, Bool.and_eq_true] at h
  refine ⟨Nat.le_of_ble_eq_true h.1, fun v hv => ?_⟩
  simpa using colOK_spec h.2 v hv

/-- Every choice of a class for every vertex is a proper colouring. -/
theorem kCol_of_isColM {k : ℕ} {P : Pos} {cls : List ℕ} (h : isColM k P cls = true)
    {g : ℕ → ℕ} (hg : ∀ v < P.length, (cls.getD (g v) 0).testBit v = true) :
    KCol k (toHist P) g := by
  obtain ⟨hlen, hall⟩ := isColM_spec h
  have hlt : ∀ v < P.length, g v < cls.length := by
    intro v hv
    by_contra hn
    have := hg v hv
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hn)] at this
  refine ⟨fun i hi => lt_of_lt_of_le (hlt i (by simpa using hi)) hlen, fun v hv u hu huv he => ?_⟩
  have hv' : v < P.length := by simpa using hv
  rw [getElem_toHist P v hv, mem_bits] at hu
  have hmem : cls.getD (g v) 0 ∈ cls := by
    rw [getD_of_lt _ (hlt v hv')]
    exact List.getElem_mem _
  exact testBit_and_eq_zero ((hall v hv').2 _ hmem (hg v hv')) (he ▸ hg u (by omega)) hu

theorem selector_of_isColM {k : ℕ} {P : Pos} {cls : List ℕ} (h : isColM k P cls = true) :
    ∀ v < P.length, (cls.getD (cls.findIdx fun a => a.testBit v) 0).testBit v = true := by
  intro v hv
  have hex := ((isColM_spec h).2 v hv).1
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [getD_of_lt _ hlt]
  exact List.findIdx_getElem (w := hlt)

/-- A proper colouring does not depend on the colours of the position. -/
theorem KCol.congr_fst {k : ℕ} {h h' : History} {f : ℕ → ℕ}
    (he : h.map Prod.fst = h'.map Prod.fst) (hf : KCol k h f) : KCol k h' f := by
  have hl : h.length = h'.length := by simpa using congrArg List.length he
  refine ⟨fun i hi => hf.1 i (hl ▸ hi), fun v hv u hu huv => ?_⟩
  have hv' : v < h.length := hl ▸ hv
  have h1 : (h.map Prod.fst)[v]? = (h'.map Prod.fst)[v]? := by rw [he]
  simp only [List.getElem?_map, List.getElem?_eq_getElem hv, List.getElem?_eq_getElem hv',
    Option.map_some, Option.some.injEq] at h1
  exact hf.2 v hv' u (h1 ▸ hu) huv

/-! ### Every colouring of `B` extends to `A` -/

/-- Vertex `p[i]` lies in the class `cls[fl[i]]`, for every `i < fl.length`. -/
def agree (cls : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: fl, w :: p => tb (cls.getD c 0) w && agree cls fl p

theorem agree_spec {cls : List ℕ} : ∀ {fl p : List ℕ}, agree cls fl p = true →
    ∀ i < fl.length, (cls.getD (fl.getD i 0) 0).testBit (p.getD i 0) = true
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [agree] at h
  | c :: fl, w :: p, h => by
    rw [agree, Bool.and_eq_true, tb_eq] at h
    intro i hi
    rcases i with _ | i
    · simpa using h.1
    · simpa using agree_spec h.2 i (by simpa using hi)

/-- The witness `cls` (the first of the list of witnesses) shows that the colouring `fl` of the
vertices of `B`, transported by `p`, extends to a proper `k`-colouring of `A`.  Returns the
remaining witnesses. -/
def endCheck (k : ℕ) (A : Pos) (p fl : List ℕ) : List (List ℕ) → Option (List (List ℕ))
  | [] => none
  | cls :: w => bif isColM k A cls && agree cls fl p then some w else none

/-- Runs `step c` for `c = c₀, …, c₀ + n - 1`, threading a state. -/
def foldCols {W : Type} (step : ℕ → W → Option W) : ℕ → ℕ → W → Option W
  | 0, _, w => some w
  | n + 1, c, w =>
    match step c w with
    | some w' => forceNat (c + 1) fun c' => foldCols step n c' w'
    | none => none

theorem foldCols_some {W : Type} {step : ℕ → W → Option W} : ∀ (n c : ℕ) (w w' : W),
    foldCols step n c w = some w' → ∀ j < n, ∃ w1 w2, step (c + j) w1 = some w2
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, c, w, w', h, j, hj => by
    rw [foldCols] at h
    split at h
    · rename_i w1 hw1
      rw [forceNat_eq] at h
      rcases j with _ | j
      · exact ⟨w, w1, hw1⟩
      · obtain ⟨w2, w3, h23⟩ := foldCols_some n (c + 1) w1 w' h j (by omega)
        exact ⟨w2, w3, by rw [← h23]; congr 1; omega⟩
    · exact absurd h (by simp)

/-- Every proper `k`-colouring of `B` that extends the partial colouring `fl` of the first
`fl.length` vertices (whose colours are all below `m`), transported by `p`, extends to a proper
`k`-colouring of `A`; the extensions are taken from the list of witnesses, in the order of the
enumeration.  The first argument is the list of the vertices of `B` that are not yet coloured.
Only the colours `0, …, m` are tried for the next vertex: a colour above `m` can be exchanged
with `m`. -/
def allExt (k : ℕ) (A : Pos) (p : List ℕ) :
    Pos → List ℕ → ℕ → List (List ℕ) → Option (List (List ℕ))
  | [], fl, _, w => endCheck k A p fl w
  | e :: rest, fl, m, w =>
    forceNat (forbMask e.1 fl 0) fun fm =>
      foldCols (fun c w => bif tb fm c then some w else
          forceList (fl ++ [c]) fun fl' =>
            forceNat (max m (c + 1)) fun m' => allExt k A p rest fl' m' w)
        (min (m + 1) k) 0 w

theorem KCol.perm {k : ℕ} {h : History} {f : ℕ → ℕ} (hf : KCol k h f) (π : Equiv.Perm ℕ)
    (hπ : ∀ c < k, π c < k) : KCol k h fun i => π (f i) :=
  ⟨fun i hi => hπ _ (hf.1 i hi), fun v hv u hu huv he => hf.2 v hv u hu huv (π.injective he)⟩

theorem swap_lt {k a b : ℕ} (ha : a < k) (hb : b < k) : ∀ c < k, Equiv.swap a b c < k := by
  intro c hc
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

open Classical in
theorem endCheck_sound {k : ℕ} {A : Pos} {p fl : List ℕ} {w w' : List (List ℕ)}
    (h : endCheck k A p fl w = some w')
    (hp : ∀ i < fl.length, ∀ j < fl.length, p.getD i 0 = p.getD j 0 → i = j) :
    ∃ g, KCol k (toHist A) g ∧ ∀ i < fl.length, g (p.getD i 0) = fl.getD i 0 := by
  rcases w with _ | ⟨cls, w⟩
  · simp [endCheck] at h
  · rw [endCheck] at h
    cases hc : (isColM k A cls && agree cls fl p)
    · simp [hc] at h
    · rw [Bool.and_eq_true] at hc
      obtain ⟨hcol, hag⟩ := hc
      have hag := agree_spec hag
      let g : ℕ → ℕ := fun v =>
        if hv : ∃ i < fl.length, p.getD i 0 = v then fl.getD (Classical.choose hv) 0
        else cls.findIdx fun a => a.testBit v
      have hgp : ∀ i < fl.length, g (p.getD i 0) = fl.getD i 0 := by
        intro i hi
        have hv : ∃ j < fl.length, p.getD j 0 = p.getD i 0 := ⟨i, hi, rfl⟩
        have hs := Classical.choose_spec hv
        simp only [g, hv, ↓reduceDIte]
        rw [hp _ hs.1 _ hi hs.2]
      refine ⟨g, kCol_of_isColM hcol fun v hv => ?_, hgp⟩
      by_cases hex : ∃ i < fl.length, p.getD i 0 = v
      · obtain ⟨i, hi, rfl⟩ := hex
        rw [hgp i hi]
        exact hag i hi
      · simp only [g, hex, ↓reduceDIte]
        exact selector_of_isColM hcol v hv

theorem allExt_sound {k : ℕ} {A B : Pos} {p : List ℕ}
    (hp : ∀ i < B.length, ∀ j < B.length, p.getD i 0 = p.getD j 0 → i = j) :
    ∀ (rest : Pos) (fl : List ℕ) (m : ℕ) (w w' : List (List ℕ)),
    allExt k A p rest fl m w = some w' → B.drop fl.length = rest → fl.length ≤ B.length →
    (∀ c ∈ fl, c < m) →
    ∀ f : ℕ → ℕ, (∀ u < fl.length, f u = fl.getD u 0) → KCol k (toHist B) f →
      ∃ g, KCol k (toHist A) g ∧ ∀ i < B.length, g (p.getD i 0) = f i
  | [], fl, m, w, w', h, hdrop, hle, _, f, hf, _ => by
    have hl : fl.length = B.length := by
      have := List.drop_eq_nil_iff.1 hdrop
      omega
    rw [allExt] at h
    obtain ⟨g, hg, hgf⟩ := endCheck_sound h (hl ▸ hp)
    exact ⟨g, hg, fun i hi => by rw [hgf i (by omega), hf i (by omega)]⟩
  | e :: rest, fl, m, w, w', h, hdrop, hle, hfl, f, hf, hK => by
    have hv : fl.length < B.length := by
      by_contra hn
      rw [List.drop_eq_nil_iff.2 (not_lt.1 hn)] at hdrop
      exact absurd hdrop (by simp)
    rw [List.drop_eq_getElem_cons hv, List.cons.injEq] at hdrop
    obtain ⟨he, hrest⟩ := hdrop
    have hv' : fl.length < (toHist B).length := by simpa using hv
    rw [allExt, forceNat_eq] at h
    have hfold := foldCols_some _ _ _ _ h
    -- the main step, for a colouring whose next colour is among the colours that are tried
    have key : ∀ f' : ℕ → ℕ, (∀ u < fl.length, f' u = fl.getD u 0) → KCol k (toHist B) f' →
        f' fl.length < min (m + 1) k →
        ∃ g, KCol k (toHist A) g ∧ ∀ i < B.length, g (p.getD i 0) = f' i := by
      intro f' hf' hK' hc
      obtain ⟨w1, w2, h12⟩ := hfold _ hc
      rw [Nat.zero_add, forceList_eq, forceNat_eq] at h12
      cases hbit : tb (forbMask e.1 fl 0) (f' fl.length)
      · rw [hbit, Bool.cond_false] at h12
        refine allExt_sound hp rest (fl ++ [f' fl.length]) _ w1 w2 h12 (by simpa using hrest)
          (by simp; omega) ?_ f' ?_ hK'
        · intro c hc'
          rcases List.mem_append.1 hc' with hc' | hc'
          · exact lt_of_lt_of_le (hfl c hc') (le_max_left _ _)
          · rw [List.mem_singleton.1 hc']
            exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
        · intro u hu
          simp only [List.length_append, List.length_singleton] at hu
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hu) with hu' | rfl
          · rw [hf' u hu']
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu']
          · simp
      · exfalso
        rw [tb_eq] at hbit
        obtain ⟨j, hj, hN, hcj⟩ := forbMask_spec _ _ _ hbit
        refine hK'.2 fl.length hv' j ?_ hj ?_
        · rw [getElem_toHist B _ hv', mem_bits, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hv, Option.getD_some, he]
          simpa using hN
        · rw [hf' j hj, getD_of_lt _ hj, hcj]
    have hck : f fl.length < k := hK.1 _ hv'
    by_cases hc : f fl.length < m + 1
    · exact key f hf hK (lt_min hc hck)
    · have hmk : m < k := by omega
      have hfix : ∀ u < fl.length, Equiv.swap (f fl.length) m (f u) = f u := by
        intro u hu
        have hlt : f u < m := by
          rw [hf u hu, getD_of_lt _ hu]
          exact hfl _ (List.getElem_mem hu)
        exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
      obtain ⟨g, hg, hgf⟩ := key (fun i => Equiv.swap (f fl.length) m (f i))
        (fun u hu => by rw [hfix u hu, hf u hu]) (hK.perm _ (swap_lt hck hmk))
        (by rw [Equiv.swap_apply_left]; exact lt_min (Nat.lt_succ_self _) hmk)
      refine ⟨fun i => Equiv.swap (f fl.length) m (g i), hg.perm _ (swap_lt hck hmk),
        fun i hi => ?_⟩
      change Equiv.swap (f fl.length) m (g (p.getD i 0)) = f i
      rw [hgf i hi, Equiv.swap_apply_self]

/-! ### Domination -/

/-- The colour of vertex `p[i]` of `A` is `sig[c - 1]`, where `c` is the colour of vertex `i` of
`B`; and `p` and `B` have the same length. -/
def colCheck (A : Pos) (sig : List ℕ) : List ℕ → Pos → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | w :: p, e :: B =>
    Nat.beq (A.getD w (0, 0)).2 (sig.getD (Nat.pred e.2) 0) && Nat.ble (Nat.succ w) A.length &&
      colCheck A sig p B

theorem colCheck_spec {A : Pos} {sig : List ℕ} : ∀ {p : List ℕ} {B : Pos},
    colCheck A sig p B = true → p.length = B.length ∧ ∀ i < B.length,
      p.getD i 0 < A.length ∧
        colourAt (toHist A) (p.getD i 0) = sig.getD (colourAt (toHist B) i - 1) 0
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [colCheck] at h
  | _ :: _, [], h => by simp [colCheck] at h
  | w :: p, e :: B, h => by
    rw [colCheck, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hl, hi⟩ := colCheck_spec h3
    refine ⟨by simp [hl], fun i hi' => ?_⟩
    rcases i with _ | i
    · refine ⟨by simpa using Nat.le_of_ble_eq_true h2, ?_⟩
      rw [colourAt_toHist, colourAt_toHist]
      simpa using Nat.eq_of_beq_eq_true h1
    · have := hi i (by simpa using hi')
      rw [colourAt_toHist] at this ⊢
      rw [colourAt_toHist]
      rw [colourAt_toHist] at this
      simpa using this

/-- The Boolean test that the position `A` (with `mA` colours) dominates the position `B` (with
`mB` colours) via the vertex map `p` and the colour map `c ↦ sig[c - 1]`; `wits` are the
extensions of the colourings of `B`. -/
def domCheck (k : ℕ) (A : Pos) (mA : ℕ) (mB : ℕ) (B : Pos) (p sig : List ℕ)
    (wits : List (List ℕ)) : Bool :=
  Nat.beq mA mB && Nat.beq sig.length mB && nodupMask sig 0 && nodupMask p 0 &&
    colCheck A sig p B && (allExt k A p B [] 0 wits).isSome

theorem dom_of_domCheck {k : ℕ} {A B : Pos} {mA mB : ℕ} {p sig : List ℕ}
    {wits : List (List ℕ)} (h : domCheck k A mA mB B p sig wits = true)
    (hA : usedColours (toHist A) = Icc 1 mA) (hB : usedColours (toHist B) = Icc 1 mB) :
    Dom k (toHist A) (toHist B) (fun i => p.getD i 0) (fun c => sig.getD (c - 1) 0) := by
  simp only [domCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hm, hsl⟩, hsn⟩, hnd⟩, hcol⟩, hext⟩ := h
  have hm := Nat.eq_of_beq_eq_true hm
  have hsl := Nat.eq_of_beq_eq_true hsl
  have hsn := (nodupMask_sound hsn).1
  have hnd := (nodupMask_sound hnd).1
  obtain ⟨hlen, hcs⟩ := colCheck_spec hcol
  have hpinj : ∀ i < B.length, ∀ j < B.length, p.getD i 0 = p.getD j 0 → i = j := by
    intro i hi j hj hij
    rw [getD_of_lt _ (hlen ▸ hi), getD_of_lt _ (hlen ▸ hj)] at hij
    exact (List.Nodup.getElem_inj_iff hnd).1 hij
  have hinj : ∀ c ∈ usedColours (toHist B), ∀ c' ∈ usedColours (toHist B),
      sig.getD (c - 1) 0 = sig.getD (c' - 1) 0 → c = c' := by
    intro c hc c' hc' he
    rw [hB, mem_Icc] at hc hc'
    rw [getD_of_lt _ (by omega), getD_of_lt _ (by omega)] at he
    have := (List.Nodup.getElem_inj_iff hsn).1 he
    omega
  refine ⟨fun i hi => by simpa using (hcs i (by simpa using hi)).1, ?_, hinj, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    rw [length_toHist] at hi hj
    exact hpinj i hi j hj hij
  · apply eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
      obtain ⟨i, hi, rfl⟩ := exists_colourAt_of_mem_usedColours hc'
      rw [length_toHist] at hi
      rw [← (hcs i hi).2]
      exact colourAt_mem_usedColours (by simpa using (hcs i hi).1)
    · rw [card_image_of_injOn (fun c hc c' hc' he => hinj c hc c' hc' he), hA, hB, hm]
  · intro i hi
    rw [length_toHist] at hi
    exact (hcs i hi).2
  · intro f hf
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 hext
    obtain ⟨g, hg, hgf⟩ :=
      allExt_sound hpinj B [] 0 wits w' hw' (by simp) (by simp) (by simp) f (by simp) hf
    exact ⟨g, hg, fun i hi => hgf i (by simpa using hi)⟩

/-! ### Lemmas and the checker -/

/-- An outcome of a lemma: `none` (the adversary stops), or `some (j, p, sig, wits)`: continue
with the lemma `j`, whose start position is dominated via the vertex map `p` and the colour map
`sig`, with the colourings `wits` as witnesses. -/
abbrev Out : Type := Option (ℕ × List ℕ × List ℕ × List (List ℕ))

/-- A lemma of a certificate: from the position `pos` (with colours `1..m`) the adversary presents
a vertex with earlier neighbours `nb` and forces the target number of colours within `h` further
vertices; `outs` lists the outcome for every answer `1, …, m+1`, and `wit` is a proper colouring
(colour classes as bit masks) of the graph after the move, used when the adversary stops. -/
structure Lem where
  /-- A bound on the number of further vertices. -/
  h : ℕ
  /-- The number of colours of the start position. -/
  m : ℕ
  /-- The start position. -/
  pos : Pos
  /-- The earlier neighbours of the presented vertex, as a bit mask. -/
  nb : ℕ
  /-- A proper colouring of the graph after the move. -/
  wit : List ℕ
  /-- The outcomes, indexed by the answer minus one. -/
  outs : List Out

/-- A default lemma (never accepted by the checker). -/
def Lem.nil : Lem := ⟨0, 0, [], 0, [], []⟩

/-- The table of lemmas stored in chunks of `c` lemmas each (lists of lists make the lookup by
the kernel fast, and keep the list literals short). -/
def table (c : ℕ) (chunks : List (List Lem)) (i : ℕ) : Lem :=
  ((chunks.getD (i / c) []).getD (i % c) Lem.nil)

/-- Checks one outcome: `A` is the position after the answer, `mA` its number of colours, `h`
the height of the lemma that is being checked, and `wOK` says whether the witness colouring of
the lemma is valid. -/
def checkOut (k C : ℕ) (T : ℕ → Lem) (i h : ℕ) (A : Pos) (mA : ℕ) (wOK : Bool) : Out → Bool
  | none => Nat.ble C mA && wOK
  | some (j, p, sig, wits) =>
    match T j with
    | ⟨hj, mj, posj, _, _, _⟩ =>
      Nat.ble (Nat.succ j) i && Nat.ble (Nat.succ hj) h && domCheck k A mA mj posj p sig wits

/-- Checks the outcomes of the answers `x, x + 1, …`; `fm` is the set of forbidden answers. -/
def checkOuts (k C : ℕ) (T : ℕ → Lem) (i h m : ℕ) (pos : Pos) (nb fm : ℕ) (wOK : Bool) :
    List Out → ℕ → Bool
  | [], _ => true
  | o :: outs, x =>
    (tb fm x || checkOut k C T i h (pos ++ [(nb, x)]) (max m x) wOK o) &&
      forceNat (x + 1) (checkOuts k C T i h m pos nb fm wOK outs)

/-- Checks the lemma `L`, which is entry `i` of the table `T`. -/
def checkLemL (k C : ℕ) (T : ℕ → Lem) (i : ℕ) : Lem → Bool
  | ⟨h, m, pos, nb, wit, outs⟩ =>
    validCols pos m && Nat.ble (Nat.succ nb) (Nat.pow 2 pos.length) && Nat.ble 1 h &&
      Nat.beq outs.length (Nat.succ m) &&
      forceNat (forbMask nb (pos.map Prod.snd) 0) fun fm =>
        forceBool (isColM k (pos ++ [(nb, 0)]) wit) fun wOK =>
          checkOuts k C T i h m pos nb fm wOK outs 1

/-- Checks entry `i` of the table `T`. -/
def checkLem (k C : ℕ) (T : ℕ → Lem) (i : ℕ) : Bool := checkLemL k C T i (T i)

/-- Checks the entries `lo, …, lo + len - 1` of the table `T`. -/
def checkRange (k C : ℕ) (T : ℕ → Lem) (lo len : ℕ) : Bool :=
  (List.range' lo len).all (checkLem k C T)

/-- The last of the `n` lemmas starts from the empty position and has height at most `N`. -/
def rootCheck (T : ℕ → Lem) (n N : ℕ) : Bool :=
  match T (n - 1) with
  | ⟨h, _, pos, _, _, _⟩ => pos.isEmpty && decide (h ≤ N)

variable {k C : ℕ}

theorem validCols_of_checkLem {T : ℕ → Lem} {i : ℕ} (h : checkLem k C T i = true) :
    usedColours (toHist (T i).pos) = Icc 1 (T i).m := by
  unfold checkLem at h
  generalize T i = L at h ⊢
  obtain ⟨h', m, pos, nb, wit, outs⟩ := L
  simp only [checkLemL, Bool.and_eq_true] at h
  exact usedColours_of_validCols h.1.1.1.1

theorem force_of_checkOut {T : ℕ → Lem} {i h : ℕ} {A : Pos} {mA : ℕ} {wOK : Bool} {o : Out}
    (hc : checkOut k C T i h A mA wOK o = true)
    (hA : usedColours (toHist A) = Icc 1 mA)
    (hw : wOK = true → ∃ f, KCol k (toHist A) f)
    (hprev : ∀ j < i, checkLem k C T j = true ∧ Force k C (T j).h (toHist (T j).pos)) :
    Force k C (h - 1) (toHist A) := by
  rcases o with _ | ⟨j, p, sig, wits⟩
  · simp only [checkOut, Bool.and_eq_true] at hc
    exact Force.of_stop ⟨by rw [hA]; simpa using Nat.le_of_ble_eq_true hc.1, hw hc.2⟩
  · simp only [checkOut] at hc
    have hv := fun hj : j < i => validCols_of_checkLem (hprev j hj).1
    have hF := fun hj : j < i => (hprev j hj).2
    generalize T j = L at hc hv hF
    obtain ⟨hj, mj, posj, nbj, witj, outsj⟩ := L
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hji, hlt⟩, hdom⟩ := hc
    have hji : j < i := Nat.le_of_ble_eq_true hji
    have hlt : hj < h := Nat.le_of_ble_eq_true hlt
    exact Force.mono (Force.transfer (dom_of_domCheck hdom hA (hv hji)) (hF hji))
      (by change hj ≤ h - 1; omega)

theorem checkOuts_spec {T : ℕ → Lem} {i h m : ℕ} {pos : Pos} {nb fm : ℕ} {wOK : Bool} :
    ∀ {outs : List Out} {x : ℕ}, checkOuts k C T i h m pos nb fm wOK outs x = true →
    ∀ j < outs.length, fm.testBit (x + j) = true ∨
      checkOut k C T i h (pos ++ [(nb, x + j)]) (max m (x + j)) wOK (outs.getD j none) = true
  | [], _, _ => by simp
  | o :: outs, x, hc => by
    rw [checkOuts, forceNat_eq, Bool.and_eq_true, Bool.or_eq_true, tb_eq] at hc
    intro j hj
    rcases j with _ | j
    · simpa using hc.1
    · have := checkOuts_spec hc.2 j (by simpa using hj)
      rw [show x + 1 + j = x + (j + 1) by omega] at this
      simpa using this

theorem force_of_checkLem {T : ℕ → Lem} {i : ℕ} (hc : checkLem k C T i = true)
    (hprev : ∀ j < i, checkLem k C T j = true ∧ Force k C (T j).h (toHist (T j).pos)) :
    Force k C (T i).h (toHist (T i).pos) := by
  unfold checkLem at hc
  generalize T i = L at hc ⊢
  obtain ⟨h, m, pos, nb, wit, outs⟩ := L
  simp only [checkLemL, forceNat_eq, forceBool_eq, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hval, hnb⟩, hpos⟩, hol⟩, houts⟩ := hc
  have hnb : nb < 2 ^ pos.length := Nat.le_of_ble_eq_true hnb
  have hpos : 1 ≤ h := Nat.le_of_ble_eq_true hpos
  have hol : outs.length = m + 1 := Nat.eq_of_beq_eq_true hol
  have houts := checkOuts_spec houts
  have hused := usedColours_of_validCols hval
  change Force k C h (toHist pos)
  -- answers in `1..m+1`
  have key : ∀ x, 1 ≤ x → x ≤ m + 1 → x ∉ nbrColours (toHist pos) (bits nb) →
      Force k C (h - 1) (toHist pos ++ [(bits nb, x)]) := by
    intro x hx1 hxm hx
    have hx' : 1 + (x - 1) = x := by omega
    rcases houts (x - 1) (by omega) with hbit | hout
    · exfalso
      apply hx
      rw [hx'] at hbit
      obtain ⟨u, hu, hN, hux⟩ := forbMask_spec _ _ _ hbit
      simp only [List.length_map] at hu
      simp only [nbrColours, mem_image, mem_filter, mem_bits, length_toHist]
      refine ⟨u, ⟨by simpa using hN, hu⟩, ?_⟩
      rw [colourAt_toHist, ← hux]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
    · rw [hx'] at hout
      rw [← toHist_snoc]
      refine force_of_checkOut hout ?_ (fun hw => ?_) hprev
      · rw [toHist_snoc, usedColours_snoc, hused]
        ext c
        simp only [mem_insert, mem_Icc]
        omega
      · exact ⟨_, (kCol_of_isColM hw (selector_of_isColM hw)).congr_fst
          (by simp [toHist_snoc])⟩
  have hstep : ∀ x, x ∉ nbrColours (toHist pos) (bits nb) →
      Force k C (h - 1) (toHist pos ++ [(bits nb, x)]) := by
    intro x hx
    by_cases hx' : 1 ≤ x ∧ x ≤ m + 1
    · exact key x hx'.1 hx'.2 hx
    · have hm1 : m + 1 ∉ usedColours (toHist pos) := by rw [hused]; simp
      have hxu : x ∉ usedColours (toHist pos) := by rw [hused, mem_Icc]; omega
      refine Force.recolour (fun u hu => ?_) hm1 hxu
        (key (m + 1) (by omega) le_rfl
          fun hmem => hm1 (nbrColours_subset_usedColours _ _ hmem))
      simpa using lt_of_testBit hnb (mem_bits.1 hu)
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  exact Or.inr ⟨bits nb, hstep⟩

/-- **Soundness of the checker.**  If the first `n` lemmas of the table are accepted, then each of
their start positions is forcing within the height of its lemma. -/
theorem force_of_checkAll {T : ℕ → Lem} {n : ℕ} (hall : ∀ i < n, checkLem k C T i = true) :
    ∀ i < n, Force k C (T i).h (toHist (T i).pos) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    exact force_of_checkLem (hall i hi) fun j hj => ⟨hall j (by omega), ih j hj (by omega)⟩

theorem checkLem_of_checkRange {T : ℕ → Lem} {lo len : ℕ} (h : checkRange k C T lo len = true)
    {i : ℕ} (h1 : lo ≤ i) (h2 : i < lo + len) : checkLem k C T i = true := by
  simp only [checkRange, List.all_eq_true] at h
  exact h i (List.mem_range'_1.2 ⟨h1, h2⟩)

/-- **From a certificate to `N_k(C) ≤ N`.** -/
theorem nkLE_of_cert {T : ℕ → Lem} {n N : ℕ} (hall : ∀ i < n, checkLem k C T i = true)
    (hpos : 0 < n) (hroot : rootCheck T n N = true) : NkLE k C N := by
  have hF := force_of_checkAll hall (n - 1) (by omega)
  unfold rootCheck at hroot
  generalize T (n - 1) = L at hroot hF
  obtain ⟨h, m, pos, nb, outs⟩ := L
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hroot
  obtain ⟨rfl, hN⟩ := hroot
  exact nkLE_of_force (Force.mono hF hN)

/-- The first `n` lemmas of the table are accepted. -/
def Upto (k C : ℕ) (T : ℕ → Lem) (n : ℕ) : Prop := ∀ i < n, checkLem k C T i = true

theorem Upto.zero {T : ℕ → Lem} : Upto k C T 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem Upto.add {T : ℕ → Lem} {lo len : ℕ} (h : Upto k C T lo)
    (hr : checkRange k C T lo len = true) : Upto k C T (lo + len) := fun i hi => by
  rcases Nat.lt_or_ge i lo with h1 | h1
  · exact h i h1
  · exact checkLem_of_checkRange hr h1 hi

/-- **From a certificate to `N_k(C) ≤ N`**, with the table checked in pieces. -/
theorem Upto.nkLE {T : ℕ → Lem} {n N : ℕ} (hall : Upto k C T n) (hpos : 0 < n)
    (hroot : rootCheck T n N = true) : NkLE k C N := nkLE_of_cert hall hpos hroot

end Cert

end OnlineColouring
