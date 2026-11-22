module

public import OnlineColouring.BlowPairing
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem 9.3: polynomial bounds at chromatic number `log log n`

Theorem 9.3: *Let `K ≥ 2`, `ℓ = ⌈log K⌉ + 1` and `c ≥ 1`.  If `width(P_{c-1}(m)) ≥ 2ℓ`, then an
adversary forces `K` colours on `m`-colourable graphs with at most `4^c K^{c(c+1)/2}` vertices.
In particular, if `n ≥ 16` and `binom(m, ⌊m/2⌋) ≥ log n`, then `χ^det_m(n) ≥ ⌊(n/16)^{1/3}⌋`;
this holds for some `m ≤ log log n + log log log n + 3`.*  Logarithms are binary.

* `Blow.slowAdv K c` is the adversary of the paper's proof: the pairing top with
  `ℓ = ⌈log K⌉ + 1 = Nat.clog 2 K + 1` (Construction 9.1), which has `N₀ = 2^ℓ` vertices and
  post-degree at most `N₀ - 1`, with `c - 1` reservation blow-ups below it
  (`stack K (N₀ - 1) (pairing ℓ) (c - 1)`).
* `theorem_9_3`: it forces `K` colours, every play has at most `4^c K^{c(c+1)/2}` vertices, and
  all its final graphs are `m`-colourable; `theorem_9_3_NkLE` is the same as
  `N_m(K) ≤ 4^c K^{c(c+1)/2}`.  (`slowAdv_good` is the form with the input sequences, from which
  the bound on `χ^det` is read off by `Good.chiDetAtLeast`, without the theorems of `Det.lean`.)
* `theorem_9_3_chiDet` (first "in particular"): if `n ≥ 16` and `log₂ n ≤ binom(m, ⌊m/2⌋)`, then
  `χ^det_m(n) ≥ ⌊(n/16)^{1/3}⌋`.
* `exists_m_le` (second "in particular"): for every `n ≥ 16` there is
  `m ≤ log log n + log log log n + 3` with `log₂ n ≤ binom(m, ⌊m/2⌋)`; `theorem_9_3_loglog`
  combines the two.
-/

@[expose] public section

namespace OnlineColouring.Blow

open Finset

/-! ### General facts about adversaries -/

theorem forces_mono {A : Adversary} {K K' : ℕ} (h : A.Forces K) (hK : K' ≤ K) : A.Forces K' := by
  intro Alg hAlg
  obtain ⟨p, hp, hc⟩ := h Alg hAlg
  exact ⟨p, hp, hK.trans hc⟩

theorem postDeg_le_pred (h : History) (i : ℕ) : h.postDeg i ≤ h.length - 1 := by
  unfold History.postDeg
  refine (card_le_card (t := Ico 1 h.length) ?_).trans (by simp)
  intro v hv
  rw [mem_filter, mem_range] at hv
  rw [mem_Ico]
  omega

/-- An adversary of size at most `N` has post-degree at most `N - 1`. -/
theorem postDegLE_of_sizeLE {A : Adversary} {N : ℕ} (h : A.SizeLE N) : A.PostDegLE (N - 1) := by
  intro Alg hAlg p i
  have := h Alg hAlg p
  have := postDeg_le_pred (A.hist Alg p) i
  omega

/-- From a good adversary for `P_0(k)` to a lower bound on `χ^det_k` (the easy direction of
Observation 4.3 for adversaries whose moves name earlier vertices only). -/
theorem Good.chiDetAtLeast {K N D k n : ℕ} {A : Adversary} (h : Good K N D (LabelPoset k 0) A)
    (hK : 1 ≤ K) (hn : N ≤ n) : ChiDetAtLeast k n K := by
  intro Alg hAlg
  obtain ⟨H, hH, q, -, hq, -, hKq, hlab⟩ := h Alg hAlg
  have hc := hasLabelling_labelPoset_zero_iff.1 hlab
  have hq1 : 1 ≤ q := by
    have := hKq.trans card_image_le
    rw [card_range] at this
    omega
  exact exists_input_of_seq hH (one_le_of_colorable hq1 hc) (hq.trans hn) hc hKq

/-! ### The pairing top is good -/

theorem pairing_valid (ℓ : ℕ) (h : History) (s : Finset ℕ) (hs : (pairing ℓ).move h = some s) :
    s ⊆ range h.length := by
  rw [pairing_move] at hs
  split_ifs at hs
  cases hs
  intro u hu
  exact mem_range.2 (mem_pairNbrs.1 hu).1

/-- The pairing top with `ℓ ≥ 1` is good for every poset with an antichain of size `2ℓ`
(Lemma 5.1 (ii)). -/
theorem pairing_good {ℓ K : ℕ} (hℓ : 1 ≤ ℓ) (hK : K ≤ 2 ^ (ℓ - 1)) {P : Type*} [PartialOrder P]
    (hP : HasAntichain P (2 * ℓ)) : Good K (2 ^ ℓ) (2 ^ ℓ - 1) P (pairing ℓ) := by
  obtain ⟨-, hS, hF, hcol⟩ := lemma_9_2 hℓ
  obtain ⟨S, hS1, hS2⟩ := hP
  exact good_of_valid (forces_mono hF hK) hS (postDegLE_of_sizeLE hS) (pairing_valid ℓ)
    fun Alg hAlg p => hasLabelling_of_colorable hS1 hS2.ge (hcol Alg hAlg p)

/-! ### Counting -/

theorem R_le_mul {K D : ℕ} (hK : 1 ≤ K) (hD : 1 ≤ D) : R K D ≤ K * D := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  unfold R
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  nlinarith

theorem deg_le_pow_mul {K D : ℕ} (hK : 1 ≤ K) (hD : 1 ≤ D) (i : ℕ) : deg K D i ≤ K ^ i * D := by
  induction i with
  | zero => simp [deg]
  | succ i ih =>
    calc deg K D (i + 1) = R K (deg K D i) := rfl
      _ ≤ K * deg K D i := R_le_mul hK (one_le_deg hD i)
      _ ≤ K * (K ^ i * D) := Nat.mul_le_mul_left _ ih
      _ = K ^ (i + 1) * D := by ring

theorem succ_mul_succ_succ_div_two' (j : ℕ) :
    (j + 1) * (j + 2) / 2 = j * (j + 1) / 2 + (j + 1) := by
  have : (j + 1) * (j + 2) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

/-- The paper's count: `N` vertices at the top, post-degree `D ≤ N`, and `j` blow-ups give at most
`N^{j+1} K^{j(j+1)/2}` vertices. -/
theorem stackSize_le {K D N : ℕ} (hK : 1 ≤ K) (hD : 1 ≤ D) (hDN : D ≤ N) (j : ℕ) :
    N * ∏ l ∈ range j, deg K D (l + 1) ≤ N ^ (j + 1) * K ^ (j * (j + 1) / 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, ← Nat.mul_assoc]
    have e : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + (j + 1) :=
      succ_mul_succ_succ_div_two' j
    calc N * (∏ l ∈ range j, deg K D (l + 1)) * deg K D (j + 1)
        ≤ N ^ (j + 1) * K ^ (j * (j + 1) / 2) * (K ^ (j + 1) * N) :=
          Nat.mul_le_mul ih ((deg_le_pow_mul hK hD _).trans (Nat.mul_le_mul_left _ hDN))
      _ = N ^ (j + 1 + 1) * K ^ ((j + 1) * (j + 1 + 1) / 2) := by
          rw [e, pow_succ, pow_add]; ring

theorem two_pow_clog_lt {K : ℕ} (hK : 2 ≤ K) : 2 ^ Nat.clog 2 K < 2 * K := by
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (show 1 < K by omega)
  have h2 : 1 ≤ Nat.clog 2 K := Nat.clog_pos (by norm_num) hK
  obtain ⟨t, ht⟩ : ∃ t, Nat.clog 2 K = t + 1 := ⟨Nat.clog 2 K - 1, by omega⟩
  rw [ht] at h1 ⊢
  rw [Nat.pred_succ] at h1
  rw [pow_succ]
  omega

/-! ### Theorem 9.3 -/

/-- **The adversary of Theorem 9.3**: the pairing top with `ℓ = ⌈log K⌉ + 1`, with `c - 1`
reservation blow-ups below it. -/
noncomputable def slowAdv (K c : ℕ) : Adversary :=
  stack K (2 ^ (Nat.clog 2 K + 1) - 1) (pairing (Nat.clog 2 K + 1)) (c - 1)

/-- Theorem 9.3 with the input sequences. -/
theorem slowAdv_good {K c m : ℕ} (hK : 2 ≤ K) (hc : 1 ≤ c)
    (hw : HasAntichain (LabelPoset m (c - 1)) (2 * (Nat.clog 2 K + 1))) :
    Good K (4 ^ c * K ^ (c * (c + 1) / 2)) (deg K (2 ^ (Nat.clog 2 K + 1) - 1) (c - 1))
      (LabelPoset m 0) (slowAdv K c) := by
  obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hw ⊢
  have hpow : K ≤ 2 ^ (Nat.clog 2 K + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    exact Nat.le_pow_clog (by norm_num) K
  have hN : 2 ^ (Nat.clog 2 K + 1) ≤ 4 * K := by
    have := two_pow_clog_lt hK
    rw [pow_succ]
    omega
  have hD : 1 ≤ 2 ^ (Nat.clog 2 K + 1) - 1 := by
    have : 2 ≤ 2 ^ (Nat.clog 2 K + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.clog 2 K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hw' : HasAntichain (LabelPoset m (0 + j)) (2 * (Nat.clog 2 K + 1)) := by
    rw [Nat.zero_add]
    exact hw
  have hg := (pairing_good (Nat.succ_pos _) hpow hw').stack (by omega) hD j 0
  intro Alg hAlg
  obtain ⟨H, hH, q, hfol, hq, hrest⟩ := hg Alg hAlg
  refine ⟨H, hH, q, hfol, hq.trans ?_, hrest⟩
  calc 2 ^ (Nat.clog 2 K + 1) * ∏ l ∈ range j, deg K (2 ^ (Nat.clog 2 K + 1) - 1) (l + 1)
      ≤ (2 ^ (Nat.clog 2 K + 1)) ^ (j + 1) * K ^ (j * (j + 1) / 2) :=
        stackSize_le (by omega) hD (Nat.sub_le _ _) j
    _ ≤ (4 * K) ^ (j + 1) * K ^ (j * (j + 1) / 2) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN _)
    _ = 4 ^ (j + 1) * K ^ ((j + 1) * (j + 1 + 1) / 2) := by
        rw [succ_mul_succ_succ_div_two' j, mul_pow, pow_add K]; ring

/-- **Theorem 9.3.**  Let `K ≥ 2`, `ℓ = ⌈log K⌉ + 1` and `c ≥ 1`.  If `width(P_{c-1}(m)) ≥ 2ℓ`,
then the adversary `slowAdv K c` forces `K` colours, every play has at most `4^c K^{c(c+1)/2}`
vertices, and all its final graphs are `m`-colourable. -/
theorem theorem_9_3 {K c m : ℕ} (hK : 2 ≤ K) (hc : 1 ≤ c)
    (hw : 2 * (Nat.clog 2 K + 1) ≤ width (LabelPoset m (c - 1))) :
    (slowAdv K c).Forces K ∧ (slowAdv K c).SizeLE (4 ^ c * K ^ (c * (c + 1) / 2)) ∧
      (slowAdv K c).LandsIn fun _ G => G.Colorable m := by
  have hg := slowAdv_good hK hc (le_width_iff.1 hw)
  exact ⟨hg.forces, hg.sizeLE,
    fun Alg hAlg p _ => hasLabelling_labelPoset_zero_iff.1 (hg.hasLabelling hAlg p)⟩

/-- Theorem 9.3 in terms of `N_m(K)`. -/
theorem theorem_9_3_NkLE {K c m : ℕ} (hK : 2 ≤ K) (hc : 1 ≤ c)
    (hw : 2 * (Nat.clog 2 K + 1) ≤ width (LabelPoset m (c - 1))) :
    NkLE m K (4 ^ c * K ^ (c * (c + 1) / 2)) :=
  ⟨slowAdv K c, theorem_9_3 hK hc hw⟩

/-! ### The two "in particular" statements -/

/-- `16 K^3 ≤ n` for `K = ⌊(n/16)^{1/3}⌋`. -/
theorem sixteen_mul_floor_cube_le (n : ℕ) :
    16 * ⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ ^ 3 ≤ n := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) / 16 := by positivity
  have h1 : (⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ≤ ((n : ℝ) / 16) ^ ((1 : ℝ) / 3) :=
    Nat.floor_le (Real.rpow_nonneg h0 _)
  have h2 : (⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 3 ≤ (n : ℝ) / 16 := by
    calc (⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 3
        ≤ (((n : ℝ) / 16) ^ ((1 : ℝ) / 3)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3
      _ = (n : ℝ) / 16 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
        norm_num
  have h3 : (16 : ℝ) * (⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 3 ≤ n := by linarith
  exact_mod_cast h3

/-- **Theorem 9.3, first "in particular".**  If `n ≥ 16` and `binom(m, ⌊m/2⌋) ≥ log n`, then
`χ^det_m(n) ≥ ⌊(n/16)^{1/3}⌋`. -/
theorem theorem_9_3_chiDetAtLeast {m n : ℕ} (hn : 16 ≤ n)
    (hm : Real.logb 2 n ≤ (m.choose (m / 2) : ℝ)) :
    ChiDetAtLeast m n ⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : ∀ t : ℕ, 2 ^ t ≤ n → (t : ℝ) ≤ Real.logb 2 n := by
    intro t ht
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_natCast]
    exact_mod_cast ht
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m = 0 := by omega
    have h4 := hlog 4 (by omega)
    rw [hm0] at hm
    norm_num at hm h4
    linarith
  have hK3 := sixteen_mul_floor_cube_le n
  generalize ⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ = K at hK3 ⊢
  rcases Nat.lt_or_ge K 2 with hK | hK
  · exact chiDetAtLeast_of_le (by omega) (chiDetAtLeast_one hm1 (by omega))
  -- `2ℓ ≤ log n`
  have hP := two_pow_clog_lt hK
  have hKK : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2ℓ : 2 ^ (2 * (Nat.clog 2 K + 1)) ≤ n := by
    have e : 2 ^ (2 * (Nat.clog 2 K + 1)) = 4 * (2 ^ Nat.clog 2 K) ^ 2 := by ring
    rw [e]
    have h5 : 4 * (2 ^ Nat.clog 2 K) ^ 2 ≤ 4 * (2 * K) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP.le 2)
    have h6 : 4 * (2 * K) ^ 2 = 16 * K ^ 2 := by ring
    linarith
  have hw : HasAntichain (LabelPoset m (2 - 1)) (2 * (Nat.clog 2 K + 1)) := by
    refine ((hasAntichain_labelPoset_zero m).labelPoset_succ hm1).mono ?_
    have := (hlog _ h2ℓ).trans hm
    exact_mod_cast this
  have hg := slowAdv_good hK (by norm_num : 1 ≤ 2) hw
  refine hg.chiDetAtLeast (by omega) ?_
  norm_num
  exact hK3

/-- The same for `chiDet`. -/
theorem theorem_9_3_chiDet {m n : ℕ} (hn : 16 ≤ n)
    (hm : Real.logb 2 n ≤ (m.choose (m / 2) : ℝ)) :
    ⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ ≤ chiDet m n := by
  have h := theorem_9_3_chiDetAtLeast hn hm
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m = 0 := by omega
    subst hm0
    obtain ⟨I, hI, -⟩ := h OnlineAlg.firstFit OnlineAlg.firstFit_isProper
    have := one_le_of_colorable (by omega : 1 ≤ n) hI
    omega
  exact (le_chiDet_iff hm1).2 h

/-- **Theorem 9.3, second "in particular".**  For every `n ≥ 16` there
is `m ≤ log log n + log log log n + 3` with `binom(m, ⌊m/2⌋) ≥ log n`. -/
theorem exists_m_le {n : ℕ} (hn : 16 ≤ n) :
    ∃ m : ℕ, Real.logb 2 n ≤ (m.choose (m / 2) : ℝ) ∧
      (m : ℝ) ≤ Real.logb 2 (Real.logb 2 n) + Real.logb 2 (Real.logb 2 (Real.logb 2 n)) + 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : (4 : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos]
    have : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by norm_num
    rw [this]
    exact_mod_cast hn
  have hLpos : (0 : ℝ) < Real.logb 2 n := by linarith
  have hx : (2 : ℝ) ≤ Real.logb 2 (Real.logb 2 n) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hLpos]
    have : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by norm_num
    rw [this]
    exact hL
  generalize Real.logb 2 n = L at hL hLpos hx ⊢
  have hLx : (2 : ℝ) ^ Real.logb 2 L = L := Real.rpow_logb (by norm_num) (by norm_num) hLpos
  generalize Real.logb 2 L = x at hx hLx ⊢
  have hxpos : (0 : ℝ) < x := by linarith
  have hy : (1 : ℝ) ≤ Real.logb 2 x := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hxpos]
    simpa using hx
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hy3 : Real.logb 2 x ≤ 3 * x - 4 := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have := Real.log_le_sub_one_of_pos hxpos
    nlinarith
  have hxy : (2 : ℝ) ^ Real.logb 2 x = x := Real.rpow_logb (by norm_num) (by norm_num) hxpos
  generalize Real.logb 2 x = y at hy hy3 hxy ⊢
  have hxy0 : (0 : ℝ) ≤ x + y := by linarith
  refine ⟨⌈x + y⌉₊ + 2, ?_, ?_⟩
  swap
  · have := Nat.ceil_lt_add_one hxy0
    push_cast
    linarith
  -- `2^m ≥ 4 L x ≥ (m + 1) L`
  have hceil : (⌈x + y⌉₊ : ℝ) < x + y + 1 := Nat.ceil_lt_add_one hxy0
  have h1 : L * x ≤ (2 : ℝ) ^ ⌈x + y⌉₊ := by
    calc L * x = (2 : ℝ) ^ (x + y) := by
          rw [Real.rpow_add (by norm_num), hLx, hxy]
      _ ≤ (2 : ℝ) ^ ((⌈x + y⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = (2 : ℝ) ^ ⌈x + y⌉₊ := Real.rpow_natCast _ _
  have h2 := two_pow_le_succ_mul_choose_half (⌈x + y⌉₊ + 2)
  have h2' : (2 : ℝ) ^ (⌈x + y⌉₊ + 2) ≤
      ((⌈x + y⌉₊ + 2 : ℕ) + 1 : ℝ) * ((⌈x + y⌉₊ + 2).choose ((⌈x + y⌉₊ + 2) / 2) : ℝ) := by
    exact_mod_cast h2
  generalize ((⌈x + y⌉₊ + 2).choose ((⌈x + y⌉₊ + 2) / 2) : ℝ) = C at h2' ⊢
  rw [pow_add] at h2'
  push_cast at h2'
  have hM0 : (0 : ℝ) ≤ (⌈x + y⌉₊ : ℝ) := Nat.cast_nonneg _
  generalize (2 : ℝ) ^ ⌈x + y⌉₊ = P at h1 h2'
  generalize (⌈x + y⌉₊ : ℝ) = M at hceil h2' hM0
  norm_num at h2'
  have hMpos : 0 < M + 2 + 1 := by linarith
  have h3 : (M + 2 + 1) * L ≤ (M + 2 + 1) * C := by
    have h4 := mul_nonneg (by linarith : 0 ≤ 4 * x - (M + 2 + 1)) hLpos.le
    linarith
  exact le_of_mul_le_mul_left h3 hMpos

/-- **Theorem 9.3, both "in particular" statements together.**  For every `n ≥ 16` there is
`m ≤ log log n + log log log n + 3` with `χ^det_m(n) ≥ ⌊(n/16)^{1/3}⌋`. -/
theorem theorem_9_3_loglog {n : ℕ} (hn : 16 ≤ n) :
    ∃ m : ℕ, (m : ℝ) ≤ Real.logb 2 (Real.logb 2 n) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 n)) + 3 ∧
      ⌊((n : ℝ) / 16) ^ ((1 : ℝ) / 3)⌋₊ ≤ chiDet m n := by
  obtain ⟨m, hm1, hm2⟩ := exists_m_le hn
  exact ⟨m, hm2, theorem_9_3_chiDet hn hm1⟩

end OnlineColouring.Blow
