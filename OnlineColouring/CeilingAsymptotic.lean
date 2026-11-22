module

public import OnlineColouring.Ceiling
public import OnlineColouring.TowerGrowth

/-!
# Theorem 1.5 (a ceiling for towers), second sentence, for initial segments of full towers

The last sentence of Theorem 1.5: for large `n`, First-Fit uses at most
`n^{1/(lg* n - lg* k - 3)}` colours on every `k`-colourable tower with at most `n` vertices.

Here it is stated without reals, as `c ^ (lg* n - lg* k - 3) ≤ n` (natural subtraction; for an
exponent `e ≥ 1` this is `c ≤ n^{1/e}`), for initial segments of full towers
(`IsFullTowerAnc.firstFit_pow_le`) and for full towers (`IsFullTower.pow_le`).  The threshold is
explicit and does not depend on `k`: `lg* n ≥ 8`, i.e. `n > tow 7`.  The form of the theorem with
a real exponent, for towers in the sense of Definition 4.7, is `exists_threshold_le_rpow`
(`CeilingPadded.lean`).

The proof is organised differently from the paper's: it works with `n` throughout, where the
paper first bounds `c` in terms of the number of vertices of `G`, and instead of the least `λ`
with `|P_λ(k)| ≥ c` (which needs `k ≥ 3` to bound `λ ≤ lg* c + 1`) it applies the size bound with
`i = min(j, lg* c + 1)`.  So the statement holds for every `k`.

* If `lg* c ≤ L - 3` (where `L = lg* n`), then `c^e ≤ tow(L-3)^{L-3} ≤ tow(L-1) < n`
  (`pow_le_tow_add_two`).
* Otherwise `c > tow(L-3)`, and with `r = i + 1` we have `e + 2 ≤ r ≤ L + 2` and
  `choose(c-1, r) ≤ n`.  From `(c-r)^r ≤ r! · choose(c-1, r) ≤ r^r n` and
  `c^e r^r ≤ (c-r)^r` (`pow_le_of_choose_le`, which holds because `c` is huge compared with `r`,
  `caseB_bounds`) we get `c^e ≤ n`.
-/

@[expose] public section

namespace OnlineColouring

/-! ### Elementary inequalities -/

theorem two_mul_le_two_pow (x : ℕ) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · norm_num
    · rw [pow_succ]
      omega

theorem mul_self_le_two_pow {x : ℕ} (hx : 4 ≤ x) : x * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ]
    nlinarith

theorem two_le_tow_succ (i : ℕ) : 2 ≤ tow (i + 1) := by
  have := lt_tow (i + 1)
  omega

/-- `tow b ≥ (b + 6)² + 1` for `b ≥ 4`. -/
theorem sq_add_one_le_tow {b : ℕ} (hb : 4 ≤ b) : (b + 6) ^ 2 + 1 ≤ tow b := by
  induction b, hb using Nat.le_induction with
  | base => rw [tow_four]; norm_num
  | succ b hb ih =>
    rw [tow_succ]
    have h1 : 2 ^ ((b + 6) ^ 2 + 1) ≤ 2 ^ tow b := Nat.pow_le_pow_right (by norm_num) ih
    have h2 := two_mul_le_two_pow ((b + 6) ^ 2 + 1)
    have h3 : (b + 1 + 6) ^ 2 + 1 ≤ 2 * ((b + 6) ^ 2 + 1) := by nlinarith
    omega

/-- Case A of the asymptotic bound: for `a ≥ 2`, `c ≤ tow a` and `e ≤ a` give
`c^e ≤ tow (a + 2)`. -/
theorem pow_le_tow_add_two {a c e : ℕ} (ha : 2 ≤ a) (hc : c ≤ tow a) (he : e ≤ a) :
    c ^ e ≤ tow (a + 2) := by
  set x := tow a with hx
  have hx4 : 4 ≤ x := by
    have : tow 2 ≤ tow a := tow_mono ha
    simpa [tow] using this
  have hx1 : 1 ≤ x := by omega
  calc c ^ e ≤ x ^ e := Nat.pow_le_pow_left hc e
    _ ≤ x ^ a := Nat.pow_le_pow_right hx1 he
    _ ≤ x ^ x := Nat.pow_le_pow_right hx1 (lt_tow a).le
    _ ≤ (2 ^ x) ^ x := Nat.pow_le_pow_left Nat.lt_two_pow_self.le x
    _ = 2 ^ (x * x) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 ^ x) := Nat.pow_le_pow_right (by norm_num) (mul_self_le_two_pow hx4)
    _ = tow (a + 2) := by rw [tow_succ, tow_succ]

/-- Case B of the asymptotic bound, the counting step: if `e + 2 ≤ r`, `2r ≤ c`,
`(2r)^r ≤ (c-r)²` and `choose(c-1, r) ≤ n`, then `c^e ≤ n`. -/
theorem pow_le_of_choose_le {c r e n : ℕ} (hr : e + 2 ≤ r) (h2r : 2 * r ≤ c)
    (hsq : (2 * r) ^ r ≤ (c - r) ^ 2) (hch : (c - 1).choose r ≤ n) : c ^ e ≤ n := by
  have hc1 : 1 ≤ c := by omega
  set d := c - r with hd
  have hd1 : 1 ≤ d := by omega
  -- `(c - r)^r ≤ r! · choose(c-1, r) ≤ r^r · n`
  have h1 : d ^ r ≤ r ^ r * n := by
    have e1 : c - 1 + 1 - r = d := by omega
    have := Nat.pow_sub_le_descFactorial (c - 1) r
    rw [e1, Nat.descFactorial_eq_factorial_mul_choose] at this
    exact this.trans (Nat.mul_le_mul (Nat.factorial_le_pow r) hch)
  -- `c^e · r^r ≤ (c - r)^r`
  have h2 : c ^ e * r ^ r ≤ d ^ r := by
    have hc2d : c ≤ 2 * d := by omega
    calc c ^ e * r ^ r ≤ (2 * d) ^ e * r ^ r := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc2d e)
      _ = 2 ^ e * r ^ r * d ^ e := by rw [mul_pow]; ring
      _ ≤ 2 ^ r * r ^ r * d ^ e :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
            (by omega)))
      _ = (2 * r) ^ r * d ^ e := by rw [mul_pow]
      _ ≤ d ^ 2 * d ^ e := Nat.mul_le_mul_right _ hsq
      _ = d ^ (2 + e) := by rw [pow_add]
      _ ≤ d ^ r := Nat.pow_le_pow_right hd1 (by omega)
  have hrpos : 0 < r ^ r := Nat.pow_pos (by omega)
  have : c ^ e * r ^ r ≤ n * r ^ r := by
    calc c ^ e * r ^ r ≤ d ^ r := h2
      _ ≤ r ^ r * n := h1
      _ = n * r ^ r := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right this hrpos

/-- Case B of the asymptotic bound, the size step: if `b ≥ 4`, `c > tow (b+1)` and
`r ≤ b + 6`, then `c` is huge compared with `r`. -/
theorem caseB_bounds {b c r : ℕ} (hb : 4 ≤ b) (hc : tow (b + 1) < c) (hr : r ≤ b + 6) :
    2 * r ≤ c ∧ (2 * r) ^ r ≤ (c - r) ^ 2 := by
  set R := b + 6 with hR
  set Q := 2 ^ (R * R) with hQ
  have hRQ : R ≤ Q := by
    have h1 : R ≤ R * R := Nat.le_mul_self R
    have h2 : R * R < 2 ^ (R * R) := Nat.lt_two_pow_self
    omega
  -- `c > tow (b+1) = 2 ^ tow b ≥ 2 ^ (R² + 1) = 2 Q`
  have hcQ : 2 * Q < c := by
    have h1 : R ^ 2 + 1 ≤ tow b := sq_add_one_le_tow hb
    have h2 : 2 ^ (R ^ 2 + 1) ≤ 2 ^ tow b := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : 2 ^ (R ^ 2 + 1) = 2 * Q := by rw [hQ, pow_succ, sq]; ring
    rw [tow_succ] at hc
    omega
  refine ⟨by omega, ?_⟩
  calc (2 * r) ^ r ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left (two_mul_le_two_pow r) r
    _ = 2 ^ (r * r) := by rw [← pow_mul]
    _ ≤ Q := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hr hr)
    _ ≤ c - r := by omega
    _ ≤ (c - r) ^ 2 := by
      rw [sq]
      exact Nat.le_mul_self _

/-- **Theorem 1.5, asymptotic form, arithmetic core.** Let `L = lg* n ≥ 8`.  If `c ≤ n`,
`lg* c - lg* k ≤ j` and `choose(c-1, i+1) ≤ n` for every `i ≤ j`, then
`c ^ (L - lg* k - 3) ≤ n`. -/
theorem pow_logStar_le {n k c j : ℕ} (hL : 8 ≤ logStar n) (hcn : c ≤ n)
    (hj : logStar c - logStar k ≤ j) (hsize : ∀ i ≤ j, (c - 1).choose (i + 1) ≤ n) :
    c ^ (logStar n - logStar k - 3) ≤ n := by
  set L := logStar n with hLdef
  set e := L - logStar k - 3 with he
  have hn : tow (L - 1) < n := by
    by_contra h
    push Not at h
    have := logStar_le_iff.2 h
    omega
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · rw [he0, pow_zero]
    omega
  have hcL : logStar c ≤ L := logStar_le_iff.2 (hcn.trans (le_tow_logStar n))
  by_cases hA : logStar c ≤ L - 3
  · -- Case A: `c ≤ tow (L - 3)`
    have hc : c ≤ tow (L - 3) := (le_tow_logStar c).trans (tow_mono hA)
    have := pow_le_tow_add_two (a := L - 3) (by omega) hc (by omega : e ≤ L - 3)
    rw [show L - 3 + 2 = L - 1 by omega] at this
    omega
  · -- Case B: `c > tow (L - 3)`
    push Not at hA
    have hc : tow (L - 3) < c := lt_tow_of_lt_logStar hA
    set i := min j (logStar c + 1) with hi_def
    have hi : i ≤ j := min_le_left _ _
    have hie : e + 1 ≤ i := by
      rw [hi_def, le_min_iff]
      constructor <;> omega
    have hir : i ≤ logStar c + 1 := min_le_right _ _
    obtain ⟨h2r, hsq⟩ := caseB_bounds (b := L - 4) (r := i + 1) (by omega)
      (by rwa [show L - 4 + 1 = L - 3 by omega]) (by omega)
    exact pow_le_of_choose_le (by omega) h2r hsq (hsize i hi)

/-- **Theorem 1.5 (a ceiling for towers), asymptotic form, initial segments.** Let `S` be a
`k`-colourable initial segment with at most `n` vertices of a full `j`-fold blow-up of `K_m`, and
let `c` be the number of colours First-Fit uses on it.  If `lg* n ≥ 8`, then
`c ^ (lg* n - lg* k - 3) ≤ n` (natural subtraction; for a positive exponent this is
`c ≤ n^{1/(lg* n - lg* k - 3)}`). -/
theorem IsFullTowerAnc.firstFit_pow_le {m j : ℕ} {G : OrdGraph} {τ : G.V → Fin m}
    (hT : IsFullTowerAnc m j G τ) [Finite G.V] {S : Set G.V} (hS : IsLowerSet S) {k n : ℕ}
    (hc : (G.G.induce S).Colorable k) (hSn : S.ncard ≤ n) (hn : 8 ≤ logStar n) :
    (Set.range (firstFit (G.G.induce S))).ncard ^ (logStar n - logStar k - 3) ≤ n := by
  obtain ⟨hP, hsize⟩ := hT.ceiling hS hc
  have hcS : (Set.range (firstFit (G.G.induce S))).ncard ≤ S.ncard := by
    rw [hT.ncard_range_firstFit_induce hS]
    exact Set.ncard_image_le (Set.toFinite S)
  exact pow_logStar_le hn (hcS.trans hSn) (logStar_sub_logStar_le hP)
    fun i hi => (hsize i hi).trans hSn

/-- **Theorem 1.5, asymptotic form, full towers.** If a full `j`-fold blow-up of `K_m` is
`k`-colourable and has at most `n` vertices, where `lg* n ≥ 8`, then the number `c` of colours
that First-Fit uses (which is `m`) satisfies `c ^ (lg* n - lg* k - 3) ≤ n` (natural subtraction;
for a positive exponent this is `c ≤ n^{1/(lg* n - lg* k - 3)}`). -/
theorem IsFullTower.pow_le {m j k n : ℕ} {G : OrdGraph} [Finite G.V] (hT : IsFullTower m j G)
    (hc : G.G.Colorable k) (hGn : Nat.card G.V ≤ n) (hn : 8 ≤ logStar n) :
    (Set.range (firstFit G.G)).ncard ^ (logStar n - logStar k - 3) ≤ n := by
  obtain ⟨hm, hP, hsize⟩ := hT.ceiling hc
  rw [hm]
  have hmn : m ≤ n := by
    have := hsize 0 (Nat.zero_le j)
    rw [Nat.choose_one_right] at this
    exact this.trans hGn
  exact pow_logStar_le hn hmn (logStar_sub_logStar_le hP)
    fun i hi => ((Nat.choose_le_choose _ (Nat.sub_le m 1)).trans (hsize i hi)).trans hGn

/-- `lg* n ≥ 8` holds for all `n > tow 7`, so `n₀ = tow 7 + 1` is an explicit threshold. -/
theorem eight_le_logStar {n : ℕ} (hn : tow 7 < n) : 8 ≤ logStar n := by
  by_contra h
  push Not at h
  have := logStar_le_iff.1 (show logStar n ≤ 7 by omega)
  omega

end OnlineColouring
