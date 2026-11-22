module

public import OnlineColouring.StrRefBlow
public import OnlineColouring.Det

/-!
# Proposition B.1 (smaller blocks): the adversary `𝒜'`

Appendix B: *For `1 ≤ t ≤ K` put `D_j(t) := K - t`, the post-degree of `v_t`, and for
`ℓ = j, …, 1`*

  `b_ℓ(t) := (K-t)(D_ℓ(t) - 1) + 1`,  `D_{ℓ-1}(t) := max_{t < t' ≤ K} b_ℓ(t')`,

*with the maximum of the empty set equal to `0`.  …  Let `𝒜'` be the adversary of Theorem 6.4 in
which every block of a node of level `ℓ` below `v_t` has `b_ℓ(t)` nodes and every reserve of such
a node has size `D_ℓ(t)`.*

*Proposition B.1.  If `|P_j(k)| ≥ K`, then `𝒜'` forces `K` colours on `k`-colourable graphs, and
every play has at most `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` vertices.*

## The objects

* `Str.Dl K j ℓ t`, `Str.bl K j ℓ t` are the paper's `D_ℓ(t)` and `b_ℓ(t)` (`Dl_top`, `bl_eq`,
  `Dl_pred` are the three defining equations; `bl_eq` puts `b_ℓ(t) = 1` when `D_ℓ(t) = 0`, which
  is the value of the paper's formula, see `refB_int`).  Internally they are `refD K i t`,
  `refB K i t` with `i = j - ℓ` the number of blow-ups between the clique and level `ℓ`.
* `Str.refTower K j : Adversary` is `𝒜'`: `refTower K 0` is the clique `K_K`, and
  `refTower K (i+1) = GB K (lvlBs K i) (lvlDs K i) (refTower K i)` is Construction 6.1
  (`StrRefBlow.lean`) in which the block of the inner vertex `v`, a node of level `ℓ = j - i` (if
  the tower has `j` levels), has `lvlBs K i v = b_ℓ(t)` vertices and its reserve has
  `lvlDs K i v = D_ℓ(t)` vertices, where `v_t` is the top vertex above `v`.  The top vertex above a
  vertex is read off from its arrival index: `lvlTop K 0 v = v` for the clique (`v_t` has index
  `t - 1`), and the top vertex above an outer vertex is the top vertex above the inner vertex whose
  block contains it (`lvlTop_succ`).

## Results

* `Str.proposition_B_1`: if `K ≤ |P_j(k)|`, then `refTower K j` forces `K` colours, lands in the
  `k`-colourable graphs, and has size at most `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)`.  No further
  hypothesis on `K`, `j`, `k` is needed.  `refTower_colorable`: every graph presented is
  `k`-colourable.  `NkLE_refSize`: `N_k(K) ≤ ∑_t ∏_ℓ b_ℓ(t)`.
* `refTower_play` is the induction over the levels (one application of `gsim` per level).  Its
  invariants are the statements of the paper's proof: a node of level `ℓ - 1` below `v_t` has
  post-degree at most `D_{ℓ-1}(t)` ("a reserve of `D_{ℓ-1}(t)` nodes suffices"); every node below
  `v_t` has exactly one earlier neighbour below each `v_s` with `s < t` and no others; and that
  server has the induced colour `col(v_s)`, the colour that the `j`-fold induced algorithm
  `topAlg K j Alg` gives `v_s`.  Hence every node below `v_t` sees exactly `t - 1` distinct colours
  on its earlier neighbours (`refTower_rich`), which is the hypothesis `hrich` of `gsim` for the
  next level.
* `refSize_table`: the column "Proposition B.1" of Table 3 (12, 77, 14 484, 70 558, 3 591 642);
  `NkLE_table`: the corresponding instances (`N_3(7) ≤ 77`, `N_3(8) ≤ 14 484`, …).
  `refSize_le_playSize`: the bound is never larger than the bound `(K-1) ∏ b_ℓ + 1` of
  Theorem 6.4 (`refD_le_levelDeg`: `b_ℓ(t) ≤ b_ℓ`).  `chiDetAtLeast_of_refSize`: the lower bound
  on `χ^det_k` that follows by Observation 4.3.
* Remarks on the definitions: `refD_eq_zero_iff` (`D_ℓ(t) = 0` iff `t = K`), `refB_int` (so
  `b_ℓ(t) = (K-t)(D_ℓ(t)-1)+1` holds over `ℤ` for all `1 ≤ t ≤ K`, as in the paper, and the case
  distinction in `bOf` is not needed), `refD_succ_of_lt` (`D_{ℓ-1}(t) = b_ℓ(t+1)` for `t < K`,
  because `b_ℓ(t)` is non-increasing in `t`).
-/

@[expose] public section

namespace OnlineColouring.Str

open Finset
open Blow (Follows Tracks clean)

/-! ### The block and reserve sizes -/

/-- The size of a block below `v_t` whose node has a reserve of size `D`:
`(K-t)(D-1)+1` if `D ≥ 1`, and `1` if `D = 0`. -/
def bOf (K t D : ℕ) : ℕ := if 1 ≤ D then (K - t) * (D - 1) + 1 else 1

/-- `refD K i t` is the reserve size `D_ℓ(t)` of the nodes below `v_t` at the level `ℓ` that lies
`i` blow-ups below the clique (`ℓ = j - i` in a tower with `j` levels). -/
def refD (K : ℕ) : ℕ → ℕ → ℕ
  | 0, t => K - t
  | i + 1, t => (Ioc t K).sup fun t' => bOf K t' (refD K i t')

/-- `refB K i t` is the block size `b_ℓ(t)` of the nodes below `v_t` at the level `ℓ` that lies `i`
blow-ups below the clique. -/
def refB (K i t : ℕ) : ℕ := bOf K t (refD K i t)

/-- The paper's `D_ℓ(t)` for a tower with `j` levels. -/
def Dl (K j ℓ t : ℕ) : ℕ := refD K (j - ℓ) t

/-- The paper's `b_ℓ(t)` for a tower with `j` levels. -/
def bl (K j ℓ t : ℕ) : ℕ := refB K (j - ℓ) t

/-- `D_j(t) = K - t`. -/
theorem Dl_top (K j t : ℕ) : Dl K j j t = K - t := by
  simp [Dl, refD]

/-- `b_ℓ(t) = (K-t)(D_ℓ(t)-1)+1` if `D_ℓ(t) ≥ 1`, and `b_ℓ(t) = 1` if `D_ℓ(t) = 0`. -/
theorem bl_eq (K j ℓ t : ℕ) :
    bl K j ℓ t = if 1 ≤ Dl K j ℓ t then (K - t) * (Dl K j ℓ t - 1) + 1 else 1 := rfl

/-- `D_{ℓ-1}(t) = max_{t < t' ≤ K} b_ℓ(t')` for `1 ≤ ℓ ≤ j` (`0` if there is no such `t'`). -/
theorem Dl_pred (K j ℓ t : ℕ) (hℓ : 1 ≤ ℓ) (hℓj : ℓ ≤ j) :
    Dl K j (ℓ - 1) t = (Ioc t K).sup (bl K j ℓ) := by
  have e : j - (ℓ - 1) = (j - ℓ) + 1 := by omega
  unfold Dl
  rw [e]
  rfl

theorem bOf_pos (K t D : ℕ) : 0 < bOf K t D := by
  unfold bOf
  split_ifs <;> omega

theorem refB_pos (K i t : ℕ) : 0 < refB K i t := bOf_pos _ _ _

/-- With truncated subtraction the two cases of `b_ℓ(t)` are one formula. -/
theorem bOf_eq (K t D : ℕ) : bOf K t D = (K - t) * (D - 1) + 1 := by
  unfold bOf
  split_ifs with h
  · rfl
  · have h0 : D = 0 := by omega
    subst h0
    simp

/-- `D_ℓ(t) = 0` exactly for `t = K` (in the range `t ≤ K`): only the nodes below the last top
vertex have an empty reserve. -/
theorem refD_eq_zero_iff (K i t : ℕ) : refD K i t = 0 ↔ K ≤ t := by
  cases i with
  | zero =>
    change K - t = 0 ↔ K ≤ t
    omega
  | succ i =>
    change ((Ioc t K).sup fun t' => bOf K t' (refD K i t')) = 0 ↔ K ≤ t
    constructor
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      have hmem : t + 1 ∈ Ioc t K := mem_Ioc.2 ⟨Nat.lt_succ_self t, hlt⟩
      have h1 := Finset.le_sup (f := fun t' => bOf K t' (refD K i t')) hmem
      have h2 := bOf_pos K (t + 1) (refD K i (t + 1))
      omega
    · intro h
      rw [Ioc_eq_empty (not_lt.2 h), sup_empty]
      rfl

/-- **The paper's formula for `b_ℓ(t)`**: for `t ≤ K`, `b_ℓ(t) = (K-t)(D_ℓ(t)-1)+1` as integers.
The case distinction in `bOf` is not needed, because `D_ℓ(t) = 0` only for `t = K`. -/
theorem refB_int {K i t : ℕ} (ht : t ≤ K) :
    (refB K i t : ℤ) = ((K : ℤ) - t) * ((refD K i t : ℤ) - 1) + 1 := by
  rw [refB, bOf_eq]
  rcases Nat.eq_zero_or_pos (refD K i t) with h0 | hpos
  · have hKt : K = t := le_antisymm ((refD_eq_zero_iff K i t).1 h0) ht
    subst hKt
    simp [h0]
  · push_cast [Nat.cast_sub ht, Nat.cast_sub hpos]
    ring

/-- A reserve is never larger than its block. -/
theorem refD_le_refB (K i t : ℕ) : refD K i t ≤ refB K i t := by
  rw [refB, bOf_eq]
  rcases Nat.lt_or_ge t K with h | h
  · have h1 : refD K i t - 1 ≤ (K - t) * (refD K i t - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [(refD_eq_zero_iff K i t).2 h]
    exact Nat.zero_le _

theorem refB_le_refD_succ {K i t t' : ℕ} (h1 : t < t') (h2 : t' ≤ K) :
    refB K i t' ≤ refD K (i + 1) t :=
  Finset.le_sup (f := fun t' => bOf K t' (refD K i t')) (mem_Ioc.2 ⟨h1, h2⟩)

theorem bOf_le_bOf {K t t' D D' : ℕ} (ht : t ≤ t') (hD : D' ≤ D) : bOf K t' D' ≤ bOf K t D := by
  rw [bOf_eq, bOf_eq]
  exact Nat.succ_le_succ (Nat.mul_le_mul (Nat.sub_le_sub_left ht K) (Nat.sub_le_sub_right hD 1))

/-- `D_ℓ(t)` is non-increasing in `t`. -/
theorem refD_antitone (K i : ℕ) {t t' : ℕ} (h : t ≤ t') : refD K i t' ≤ refD K i t := by
  cases i with
  | zero => exact Nat.sub_le_sub_left h K
  | succ i => exact Finset.sup_mono (Ioc_subset_Ioc_left h)

/-- `b_ℓ(t)` is non-increasing in `t`. -/
theorem refB_antitone (K i : ℕ) {t t' : ℕ} (h : t ≤ t') : refB K i t' ≤ refB K i t :=
  bOf_le_bOf h (refD_antitone K i h)

/-- The maximum in the definition of `D_{ℓ-1}(t)` is attained at `t' = t + 1`:
`D_{ℓ-1}(t) = b_ℓ(t+1)` for `t < K`. -/
theorem refD_succ_of_lt {K t : ℕ} (i : ℕ) (h : t < K) : refD K (i + 1) t = refB K i (t + 1) := by
  apply le_antisymm
  · exact Finset.sup_le fun t' ht' => refB_antitone K i (mem_Ioc.1 ht').1
  · exact refB_le_refD_succ (Nat.lt_succ_self t) h

/-! ### The adversary `𝒜'` -/

/-- The top vertex above the vertex with arrival index `v` at the level `i` blow-ups below the
clique: `lvlTop K i v = t - 1` if that vertex lies below `v_t`.  For the clique, `v_t` has index
`t - 1`; the top vertex above an outer vertex is the top vertex above the inner vertex whose block
contains it. -/
def lvlTop (K : ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | i + 1, p => lvlTop K i (blk (fun v => refB K i (lvlTop K i v + 1)) p)

/-- The size of the block of the inner vertex `v` in the `(i+1)`-st blow-up: `b_ℓ(t)` if `v` lies
below `v_t` (`ℓ = j - i`). -/
def lvlBs (K i v : ℕ) : ℕ := refB K i (lvlTop K i v + 1)

/-- The size of the reserve of the inner vertex `v` in the `(i+1)`-st blow-up: `D_ℓ(t)` if `v`
lies below `v_t`. -/
def lvlDs (K i v : ℕ) : ℕ := refD K i (lvlTop K i v + 1)

theorem lvlTop_succ (K i p : ℕ) : lvlTop K (i + 1) p = lvlTop K i (blk (lvlBs K i) p) := rfl

/-- **The adversary `𝒜'` of Appendix B** with `j` levels: the clique `K_K`, and `j` times
Construction 6.1 in which every block of a node of level `ℓ` below `v_t` has `b_ℓ(t)` nodes and
every reserve of such a node has size `D_ℓ(t)`. -/
def refTower (K : ℕ) : ℕ → Adversary
  | 0 => Adversary.clique K
  | i + 1 => GB K (lvlBs K i) (lvlDs K i) (refTower K i)

theorem refTower_succ (K i : ℕ) :
    refTower K (i + 1) = GB K (lvlBs K i) (lvlDs K i) (refTower K i) := rfl

/-- In a tower with `j` levels, the inner vertices of the `(i+1)`-st blow-up are the nodes of
level `ℓ = j - i`; the block of such a node below `v_t` has `b_ℓ(t)` vertices. -/
theorem lvlBs_eq_bl {K j i : ℕ} (hi : i ≤ j) (v : ℕ) :
    lvlBs K i v = bl K j (j - i) (lvlTop K i v + 1) := by
  unfold lvlBs bl
  rw [Nat.sub_sub_self hi]

/-- The reserve of a node of level `ℓ = j - i` below `v_t` has `D_ℓ(t)` vertices. -/
theorem lvlDs_eq_Dl {K j i : ℕ} (hi : i ≤ j) (v : ℕ) :
    lvlDs K i v = Dl K j (j - i) (lvlTop K i v + 1) := by
  unfold lvlDs Dl
  rw [Nat.sub_sub_self hi]

/-! ### Counting -/

/-- The number of vertices below the top vertex `v_{t+1}` at the level `i` blow-ups below the
clique. -/
def lvlCnt (K i t : ℕ) : ℕ := ∏ i' ∈ range i, refB K i' (t + 1)

/-- The number of vertices at the level `i` blow-ups below the clique, if all blocks are
complete. -/
def lvlSize (K i : ℕ) : ℕ := off (lvlCnt K i) K

theorem lvlCnt_pos (K i t : ℕ) : 0 < lvlCnt K i t :=
  prod_pos fun i' _ => refB_pos K i' (t + 1)

theorem lvlCnt_succ (K i t : ℕ) : lvlCnt K (i + 1) t = lvlCnt K i t * refB K i (t + 1) :=
  prod_range_succ _ _

theorem lvlSize_zero (K : ℕ) : lvlSize K 0 = K := by
  simp [lvlSize, off, lvlCnt]

/-- The vertices below `v_{t+1}` form the `t`-th interval of lengths `lvlCnt K i`; and the blocks
of the inner vertices below `v_1, …, v_t` contain `∑_{s<t} lvlCnt K (i+1) s` vertices. -/
theorem lvlTop_eq (K i : ℕ) :
    (∀ v, lvlTop K i v = blk (lvlCnt K i) v) ∧
      ∀ t, off (lvlBs K i) (off (lvlCnt K i) t) = off (lvlCnt K (i + 1)) t := by
  have step : ∀ i, (∀ v, lvlTop K i v = blk (lvlCnt K i) v) →
      ∀ t, off (lvlBs K i) (off (lvlCnt K i) t) = off (lvlCnt K (i + 1)) t := by
    intro i hP t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [off_succ (lvlCnt K i), off_add, ih, off_succ (lvlCnt K (i + 1)), lvlCnt_succ]
      congr 1
      have hc : ∀ r ∈ range (lvlCnt K i t),
          lvlBs K i (off (lvlCnt K i) t + r) = refB K i (t + 1) := by
        intro r hr
        unfold lvlBs
        rw [hP, blk_off_add (lvlCnt_pos K i) (mem_range.1 hr)]
      rw [sum_congr rfl hc, sum_const, card_range, smul_eq_mul]
  induction i with
  | zero =>
    have h0 : ∀ v, lvlTop K 0 v = blk (lvlCnt K 0) v := by
      intro v
      have : lvlCnt K 0 = fun _ => 1 := by
        funext t
        simp [lvlCnt]
      rw [this, blk_const Nat.one_pos, Nat.div_one]
      rfl
    exact ⟨h0, step 0 h0⟩
  | succ i ih =>
    obtain ⟨hP, hQ⟩ := ih
    have hP' : ∀ p, lvlTop K (i + 1) p = blk (lvlCnt K (i + 1)) p := by
      intro p
      have hbs : ∀ v, 0 < lvlBs K i v := fun v => refB_pos K i _
      rw [lvlTop_succ, hP]
      set t := blk (lvlCnt K (i + 1)) p with ht
      have h1 : off (lvlCnt K (i + 1)) t ≤ p := off_blk_le _ p
      have h2 : p < off (lvlCnt K (i + 1)) (t + 1) := lt_off_blk_succ (lvlCnt_pos K (i + 1)) p
      rw [← hQ] at h1 h2
      exact blk_eq (lvlCnt_pos K i) ((le_blk_iff hbs).2 h1) ((blk_lt_iff hbs).2 h2)
    exact ⟨hP', step (i + 1) hP'⟩

/-- A vertex lies below one of the `K` top vertices iff its index is smaller than the size of its
level. -/
theorem lvlTop_lt_iff (K i v : ℕ) : lvlTop K i v < K ↔ v < lvlSize K i := by
  rw [(lvlTop_eq K i).1, blk_lt_iff (lvlCnt_pos K i)]
  rfl

theorem off_lvlBs_lvlSize (K i : ℕ) : off (lvlBs K i) (lvlSize K i) = lvlSize K (i + 1) :=
  (lvlTop_eq K i).2 K

/-- The size of the lowest level: `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)`. -/
theorem lvlSize_eq (K j : ℕ) : lvlSize K j = ∑ t ∈ Icc 1 K, ∏ ℓ ∈ Icc 1 j, bl K j ℓ t := by
  unfold lvlSize off lvlCnt bl
  refine Finset.sum_nbij' (fun t => t + 1) (fun t => t - 1) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_range, mem_Icc] at ht ⊢
    omega
  · intro t ht
    simp only [mem_range, mem_Icc] at ht ⊢
    omega
  · intro t _
    omega
  · intro t ht
    simp only [mem_Icc] at ht
    omega
  · intro t _
    refine Finset.prod_nbij' (fun i => j - i) (fun ℓ => j - ℓ) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_range, mem_Icc] at hi ⊢
      omega
    · intro ℓ hℓ
      simp only [mem_range, mem_Icc] at hℓ ⊢
      omega
    · intro i hi
      simp only [mem_range] at hi
      omega
    · intro ℓ hℓ
      simp only [mem_Icc] at hℓ
      omega
    · intro i hi
      simp only [mem_range] at hi
      have e : j - (j - i) = i := by omega
      rw [e]

/-- The size bound of `𝒜'`: every play has at most `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` vertices. -/
def refSize (K j : ℕ) : ℕ := ∑ t ∈ Icc 1 K, ∏ ℓ ∈ Icc 1 j, bl K j ℓ t

/-! ### The play of `𝒜'` -/

/-- The post-degree of `v_t` in the clique `K_K` is at most `K - t`. -/
theorem postDeg_cliqueSeq_le_sub (K w : ℕ) : postDeg cliqueSeq K w ≤ K - (w + 1) := by
  unfold postDeg rank
  have hsub : (range K).filter (fun v => w ∈ cliqueSeq v) ⊆ Ico (w + 1) K := by
    intro v hv
    simp only [cliqueSeq, mem_filter, mem_range] at hv
    exact mem_Ico.2 ⟨hv.2, hv.1⟩
  exact (card_le_card hsub).trans (by simp)

/-- The algorithm that the clique faces when `𝒜'` with `j` levels plays against `Alg`: the
`j`-fold induced algorithm.  The colour it gives to the `t`-th vertex of the clique is the induced
colour `col(v_t)` of the top vertex `v_t`. -/
def topAlg (K : ℕ) : ℕ → OnlineAlg → OnlineAlg
  | 0, Alg => Alg
  | j + 1, Alg => topAlg K j (gInduced Alg (lvlBs K j) (lvlDs K j))

theorem topAlg_isProper (K j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper) :
    (topAlg K j Alg).IsProper := by
  induction j generalizing Alg with
  | zero => exact hAlg
  | succ j ih => exact ih (gInduced_isProper Alg _ _)

/-- If the earlier neighbours of `v` are one vertex below each of the first `top v` top vertices,
and the one below `v_s` has the colour that the proper algorithm `Y` gives the `s`-th vertex of
the clique, then `v` sees exactly `top v` distinct colours. -/
theorem card_image_runCol_eq {X Y : OnlineAlg} (hY : Y.IsProper) {H : ℕ → Finset ℕ}
    {top : ℕ → ℕ} {v : ℕ} (hcol : ∀ w ∈ H v, runCol X H w = runCol Y cliqueSeq (top w))
    (himg : (H v).image top = range (top v)) : ((H v).image (runCol X H)).card = top v := by
  have h1 : (H v).image (runCol X H) = (range (top v)).image (runCol Y cliqueSeq) := by
    rw [← himg, image_image]
    exact image_congr fun w hw => hcol w hw
  rw [h1, card_image_runCol_cliqueSeq hY]

/-- **The induction of Proposition B.1.**  Against every proper algorithm `Alg`, the play of
`refTower K j` follows a valid input sequence `H` and stops at the first moment `T` at which `Alg`
has used `K` colours; `T` is at most the size of the level.  Among the first `T` vertices of `H`:

* a vertex below `v_t` has post-degree at most `D_ℓ(t)`;
* every vertex below `v_t` has exactly one earlier neighbour below each `v_s` with `s < t`, and no
  other earlier neighbours (`lvlTop K j` maps `H v` bijectively onto `{0, …, lvlTop K j v - 1}`);
* the earlier neighbour below `v_s` has the induced colour `col(v_s)`, the colour that the
  `j`-fold induced algorithm `topAlg K j Alg` gives `v_s` in the clique.

The graph has a `P_{j'}(k)`-labelling whenever `K ≤ |P_{j'+j}(k)|`. -/
theorem refTower_play (K j : ℕ) :
    ∀ Alg : OnlineAlg, Alg.IsProper →
      ∃ (H : ℕ → Finset ℕ) (hH : ValidSeq H) (T : ℕ),
        Follows (refTower K j) Alg H T ∧ T ≤ lvlSize K j ∧
        (∀ w < T, postDeg H T w ≤ lvlDs K j w) ∧
        (∀ v < T, (∀ w ∈ H v, ∀ w' ∈ H v, lvlTop K j w = lvlTop K j w' → w = w') ∧
          (H v).image (lvlTop K j) = range (lvlTop K j v)) ∧
        (∀ v < T, ∀ w ∈ H v,
          runCol Alg H w = runCol (topAlg K j Alg) cliqueSeq (lvlTop K j w)) ∧
        K ≤ ((range T).image (runCol Alg H)).card ∧
        (∀ t < T, ((range t).image (runCol Alg H)).card < K) ∧
        ∀ k j' : ℕ, K ≤ Fintype.card (LabelPoset k (j' + j)) →
          HasLabelling (OnlineInput.ofSeq H hH T).graph (LabelPoset k j') := by
  induction j with
  | zero =>
    intro Alg hAlg
    refine ⟨cliqueSeq, cliqueSeq_valid, K, Adversary.clique_hist K Alg, (lvlSize_zero K).ge,
      fun w _ => postDeg_cliqueSeq_le_sub K w, fun v _ => ⟨fun w _ w' _ h => h, ?_⟩,
      fun v _ w _ => rfl, (card_image_runCol_cliqueSeq hAlg K).ge, ?_, ?_⟩
    · have h : (cliqueSeq v).image (lvlTop K 0) = (cliqueSeq v).image id :=
        image_congr fun w _ => rfl
      rw [h, image_id]
      rfl
    · intro t ht
      rw [card_image_runCol_cliqueSeq hAlg t]
      exact ht
    · intro k j' hk
      rw [ofSeq_cliqueSeq_graph]
      exact hasLabelling_clique_iff.2 hk
  | succ j ih =>
    intro Alg hAlg
    have hbs : ∀ v, 0 < lvlBs K j v := fun v => refB_pos K j _
    have hA' := gInduced_isProper Alg (lvlBs K j) (lvlDs K j)
    obtain ⟨H, hH, q₀, hfol', hq₀, hdeg, hserv, hcolv, hforce, -, hlab⟩ :=
      ih (gInduced Alg (lvlBs K j) (lvlDs K j)) hA'
    have hrc : runCol (gInduced Alg (lvlBs K j) (lvlDs K j)) H =
        runCol (gInducedAlg Alg (lvlBs K j) (lvlDs K j)) H := funext (runCol_gInduced hH)
    rw [hrc] at hcolv hforce
    have hT := follows_tracks hH hfol'
    -- every node below `v_t` sees `t - 1` distinct induced colours
    have hrich : ∀ v < q₀, lvlTop K j v ≤
        ((H v).image (runCol (gInducedAlg Alg (lvlBs K j) (lvlDs K j)) H)).card := fun v hv =>
      (card_image_runCol_eq (topAlg_isProper K j hA') (hcolv v hv) (hserv v hv).2).ge
    -- arcs go from below `v_s` to below `v_t` with `s < t`
    have harc : ∀ v < q₀, ∀ w ∈ H v, lvlTop K j w < lvlTop K j v := by
      intro v hv w hw
      have := mem_image_of_mem (lvlTop K j) hw
      rw [(hserv v hv).2] at this
      exact mem_range.1 this
    have hsize : ∀ v < q₀,
        (K - 1 - lvlTop K j v) * (lvlDs K j v - 1) + 1 ≤ lvlBs K j v := by
      intro v _
      unfold lvlBs lvlDs refB
      rw [bOf_eq, Nat.sub_sub, Nat.add_comm 1]
    obtain ⟨T, hTle, hfol, hTK, hlt, hmore⟩ :=
      gsim (ty := lvlTop K j) hbs hAlg hH hT hdeg hrich hsize hforce
    have hσ := gResPos_gPerm (ds := lvlDs K j) hbs (gOutCol (lvlBs K j) (lvlDs K j) H Alg)
    have hG := gOutSeq_eq (bs := lvlBs K j) (ds := lvlDs K j) (X := Alg) hH
    have hdeg' : ∀ w < q₀, postDeg H q₀ w ≤ lvlBs K j w :=
      fun w hw => (hdeg w hw).trans (refD_le_refB K j _)
    refine ⟨gBlowSeq (lvlBs K j) H (gResPos (lvlBs K j) (lvlDs K j)
        (gOutCol (lvlBs K j) (lvlDs K j) H Alg)), gBlowSeq_valid hH hbs hσ, T, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [← hG]
      exact hfol
    · rw [← off_lvlBs_lvlSize]
      exact hTle.trans (off_mono _ hq₀)
    · -- a vertex below `v_t` serves at most one block, which lies below some `v_{t'}`, `t' > t`
      intro x _
      refine (Blow.rank_mono _ _ hTle).trans ?_
      apply postDeg_gBlowSeq_le hH hbs hσ hdeg'
      intro v hv hw
      have h1 := harc v hv _ hw
      have h2 : lvlTop K j v < K := (lvlTop_lt_iff K j v).2 (lt_of_lt_of_le hv hq₀)
      exact refB_le_refD_succ (Nat.succ_lt_succ h1) h2
    · -- the earlier neighbours are the servers `x_{w,v}`, one in the block of each `w ∈ N⁻(v)`
      intro u huT
      have hv := (hmore u huT).1
      obtain ⟨hinj, himg⟩ := hserv _ hv
      constructor
      · intro x hx x' hx' htop
        obtain ⟨hw, hxeq⟩ := (mem_gBlowSeq hbs hσ).1 hx
        obtain ⟨hw', hxeq'⟩ := (mem_gBlowSeq hbs hσ).1 hx'
        have hblk : blk (lvlBs K j) x = blk (lvlBs K j) x' := hinj _ hw _ hw' htop
        rw [hxeq, hxeq', hblk]
      · ext s
        rw [lvlTop_succ, ← himg]
        constructor
        · intro hs
          obtain ⟨x, hx, rfl⟩ := mem_image.1 hs
          exact mem_image.2 ⟨_, ((mem_gBlowSeq hbs hσ).1 hx).1, rfl⟩
        · intro hs
          obtain ⟨w, hw, rfl⟩ := mem_image.1 hs
          refine mem_image.2 ⟨_, mem_image.2 ⟨w, hw, rfl⟩, ?_⟩
          rw [lvlTop_succ, blk_off_add hbs (hσ.lt _ _)]
    · -- and the server `x_{w,v}` has the induced colour of `w`
      intro u huT x hx
      have hv := (hmore u huT).1
      have hx' := hx
      rw [← hG] at hx' ⊢
      exact ((hmore u huT).2.2.2.1 x hx').trans (hcolv _ hv _ ((mem_gBlowSeq hbs hσ).1 hx).1)
    · rw [← hG]
      exact hTK
    · rw [← hG]
      exact hlt
    · intro k j' hk
      have e : j' + (j + 1) = j' + 1 + j := by omega
      rw [e] at hk
      exact Blow.hasLabelling_ofSeq_of_le _ hTle
        ((gBlowUpOf hH hbs hσ hdeg').hasLabelling_of_jst (hlab k (j' + 1) hk))

/-- In a play of `𝒜'`, every vertex below `v_t` sees exactly `t - 1` distinct colours on its
earlier neighbours. -/
theorem refTower_rich (K j : ℕ) {Alg : OnlineAlg} (hAlg : Alg.IsProper) (p : ℕ)
    (v : ℕ) (hv : v < ((refTower K j).hist Alg p).length) :
    (nbrColours (((refTower K j).hist Alg p).take v)
      (((refTower K j).hist Alg p).getD v (∅, 0)).1).card = lvlTop K j v := by
  obtain ⟨H, hH, T, hfol, -, -, hserv, hcolv, -⟩ := refTower_play K j Alg hAlg
  rw [hfol p] at hv ⊢
  rw [length_runHist] at hv
  have hvT : v < T := lt_of_lt_of_le hv (min_le_right _ _)
  rw [runHist_take hv.le, List.getD_of_lt _ (by rw [length_runHist]; exact hv), getElem_runHist,
    nbrColours_runHist (hH v)]
  exact card_image_runCol_eq (topAlg_isProper K j hAlg) (hcolv v hvT) (hserv v hvT).2

/-! ### Proposition B.1 -/

/-- `𝒜'` forces `K` colours. -/
theorem refTower_forces (K j : ℕ) : (refTower K j).Forces K := by
  intro Alg hAlg
  obtain ⟨H, hH, T, hfol, -, -, -, -, hTK, -, -⟩ := refTower_play K j Alg hAlg
  refine ⟨T, ?_, ?_⟩
  · rw [hfol T, min_self]
    exact hfol.stop
  · rw [hfol T, min_self, usedColours_runHist]
    exact hTK

/-- Every play of `𝒜'` has at most `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` vertices. -/
theorem refTower_sizeLE (K j : ℕ) : (refTower K j).SizeLE (refSize K j) := by
  intro Alg hAlg p
  obtain ⟨H, hH, T, hfol, hT, -⟩ := refTower_play K j Alg hAlg
  rw [hfol p, length_runHist, refSize, ← lvlSize_eq]
  exact (min_le_right _ _).trans hT

/-- Every graph presented by `𝒜'` is `k`-colourable if `|P_j(k)| ≥ K` ("colourability is
unchanged, because Lemma 5.2 does not depend on the block sizes"). -/
theorem refTower_colorable {k K j : ℕ} (hKj : K ≤ Fintype.card (LabelPoset k j))
    {Alg : OnlineAlg} (hAlg : Alg.IsProper) (p : ℕ) :
    ((refTower K j).hist Alg p).graph.Colorable k := by
  obtain ⟨H, hH, T, hfol, -, -, -, -, -, -, hlab⟩ := refTower_play K j Alg hAlg
  rw [hfol p]
  have hl := hlab k 0 (by rwa [Nat.zero_add])
  exact hasLabelling_labelPoset_zero_iff.1 (Blow.hasLabelling_runHist hH (min_le_right _ _) hl)

/-- **Proposition B.1 (smaller blocks).**  If `|P_j(k)| ≥ K`, then `𝒜' = refTower K j` forces `K`
colours on `k`-colourable graphs (it forces `K` colours and lands in the `k`-colourable graphs),
and every play has at most `∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)` vertices. -/
theorem proposition_B_1 {k K j : ℕ} (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    (refTower K j).Forces K ∧ ((refTower K j).LandsIn fun _ G => G.Colorable k) ∧
      (refTower K j).SizeLE (∑ t ∈ Icc 1 K, ∏ ℓ ∈ Icc 1 j, bl K j ℓ t) :=
  ⟨refTower_forces K j, fun _ hAlg p _ => refTower_colorable hKj hAlg p, refTower_sizeLE K j⟩

/-- Proposition B.1 in terms of `N_k(K)`. -/
theorem NkLE_refSize {k K j : ℕ} (hKj : K ≤ Fintype.card (LabelPoset k j)) :
    NkLE k K (refSize K j) :=
  ⟨refTower K j, (proposition_B_1 hKj).1, (proposition_B_1 hKj).2.2, (proposition_B_1 hKj).2.1⟩

/-! ### Comparison with Theorem 6.4 -/

/-- The reserves and blocks of `𝒜'` are never larger than those of the adversary of Theorem 6.4:
`D_ℓ(t)` is at most its post-degree bound and `b_ℓ(t) ≤ b_ℓ`. -/
theorem refD_le_levelDeg (K i : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    refD K i t ≤ levelDeg K i ∧ refB K i t ≤ levelDeg K (i + 1) := by
  induction i generalizing t with
  | zero =>
    have h0 : refD K 0 t ≤ levelDeg K 0 := by
      change K - t ≤ (K - 1) ^ 0 * (K - 2) + 1
      rw [pow_zero, Nat.one_mul]
      omega
    refine ⟨h0, ?_⟩
    rw [refB, bOf_eq, levelDeg_succ]
    exact Nat.succ_le_succ (Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h0 1))
  | succ i ih =>
    have h0 : refD K (i + 1) t ≤ levelDeg K (i + 1) :=
      Finset.sup_le fun t' ht' => (ih (by have := (mem_Ioc.1 ht').1; omega)).2
    refine ⟨h0, ?_⟩
    rw [refB, bOf_eq, levelDeg_succ]
    exact Nat.succ_le_succ (Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h0 1))

/-- The bound of Proposition B.1 is at most the bound `(K-1) ∏ b_ℓ + 1` of Theorem 6.4. -/
theorem refSize_le_playSize (K j : ℕ) : refSize K j ≤ playSize K j := by
  unfold refSize playSize
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
  apply Nat.add_le_add
  · calc ∑ t ∈ Icc 1 K', ∏ ℓ ∈ Icc 1 j, bl (K' + 1) j ℓ t
        ≤ ∑ _t ∈ Icc 1 K', ∏ ℓ ∈ Icc 1 j, blockSize (K' + 1) j ℓ := by
          refine Finset.sum_le_sum fun t ht => ?_
          refine Finset.prod_le_prod fun ℓ _ => ?_
          exact (refD_le_levelDeg (K' + 1) (j - ℓ) (mem_Icc.1 ht).1).2
      _ = K' * ∏ ℓ ∈ Icc 1 j, blockSize (K' + 1) j ℓ := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  · refine le_of_eq (Finset.prod_eq_one fun ℓ _ => ?_)
    unfold bl refB
    rw [(refD_eq_zero_iff _ _ _).2 le_rfl]
    rfl

/-- So `𝒜'` has at most `K^((j+1)(j+2)/2)` vertices as well. -/
theorem refSize_le_pow {K : ℕ} (hK : 2 ≤ K) (j : ℕ) : refSize K j ≤ K ^ ((j + 1) * (j + 2) / 2) :=
  (refSize_le_playSize K j).trans (playSize_le hK j)

/-! ### Table 3 -/

/-- The column "Proposition B.1" of Table 3 (`tab:refined`). -/
theorem refSize_table :
    refSize 4 1 = 12 ∧ refSize 7 1 = 77 ∧ refSize 8 2 = 14484 ∧ refSize 10 2 = 70558 ∧
      refSize 18 2 = 3591642 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The column "Theorem 6.4" of Table 3 (the rows that are not in `playSize_table`). -/
theorem playSize_table_B : playSize 4 1 = 22 ∧ playSize 10 2 = 426394 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **The instances of Table 3**: `𝒜'` forces `4`, `7`, `8`, `10`, `18` colours on `3`-colourable
graphs with at most `12`, `77`, `14 484`, `70 558`, `3 591 642` vertices
(`|P_1(3)| = 7`, `|P_2(3)| = 18`). -/
theorem NkLE_table :
    NkLE 3 4 12 ∧ NkLE 3 7 77 ∧ NkLE 3 8 14484 ∧ NkLE 3 10 70558 ∧ NkLE 3 18 3591642 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := refSize_table
  have c1 : Fintype.card (LabelPoset 3 1) = 7 := card_labelPoset_three_one
  have c2 : Fintype.card (LabelPoset 3 2) = 18 := card_labelPoset_three_two
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1]
    exact NkLE_refSize (by rw [c1]; norm_num)
  · rw [← h2]
    exact NkLE_refSize (by rw [c1])
  · rw [← h3]
    exact NkLE_refSize (by rw [c2]; norm_num)
  · rw [← h4]
    exact NkLE_refSize (by rw [c2]; norm_num)
  · rw [← h5]
    exact NkLE_refSize (by rw [c2])

/-- Proposition B.1 as a lower bound (Observation 4.3): `χ^det_k(n) ≥ K` for every
`n ≥ ∑_{t=1}^{K} ∏_{ℓ=1}^{j} b_ℓ(t)`, if `k ≥ 1` and `|P_j(k)| ≥ K`. -/
theorem chiDetAtLeast_of_refSize {k K j n : ℕ} (hk : 1 ≤ k)
    (hKj : K ≤ Fintype.card (LabelPoset k j)) (hn : refSize K j ≤ n) : ChiDetAtLeast k n K :=
  Det.chiDetAtLeast_of_NkLE hk ((NkLE_refSize hKj).mono hn)

end OnlineColouring.Str
