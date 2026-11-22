module

public import OnlineColouring.Online

/-!
# Blow-ups with blocks of equal size, as input sequences

The static shape of the reservation blow-up of Construction 6.1 when every block is completed.
This is the digraph `Bl_ρ(H)` of Section 7, where the server assignment `ρ` is given by a family
`σ` of permutations of positions.  Let `H : ℕ → Finset ℕ` be an input sequence (its first `m`
entries form the inner ordered graph) and `R ≥ 1` a block size.  The blow-up `blowSeq R H σ` has
the vertices `w*R, …, w*R+R-1` in the block of the inner vertex `w`.  The arc `w → v` of the inner
graph (`w ∈ H v`) is served by the vertex `w*R + σ w (rank H w v)` of the block of `w`, where
`rank H w v` is the number of later neighbours of `w` that arrive before `v`, and `σ w` permutes
the positions `0, …, R-1` of the block (`BlockPerm`).  Every vertex of the block of `v` has exactly
the servers of the arcs into `v` as earlier neighbours.

* `blowSeq_valid`: the result is a valid input sequence.
* `blowUpOf`: its first `m*R` vertices form a `BlowUp` (Definition 4.6) of the first `m` vertices
  of `H`, provided every inner vertex has post-degree at most `R`; `blowUpOf_isReservation`: it is
  a reservation blow-up.  This is the remark after the proof of Lemma 6.2 (the graph presented by
  `B(𝒜)` is a reservation blow-up of the inner graph, restricted to the blocks that have started)
  when every block that has started is complete.
* `postDeg_blowSeq_le`: every vertex of the blow-up has post-degree at most `R`.
-/

@[expose] public section

namespace OnlineColouring

open Finset

/-! ### Ranks and post-degrees -/

/-- `rank H w v`: the number of vertices `v' < v` that have `w` as an earlier neighbour. -/
def rank (H : ℕ → Finset ℕ) (w v : ℕ) : ℕ := ((range v).filter fun v' => w ∈ H v').card

/-- The post-degree of `w` among the first `m` vertices of `H`. -/
abbrev postDeg (H : ℕ → Finset ℕ) (m w : ℕ) : ℕ := rank H w m

variable {H : ℕ → Finset ℕ}

theorem rank_lt_rank {w v₁ v₂ : ℕ} (h : v₁ < v₂) (hw : w ∈ H v₁) : rank H w v₁ < rank H w v₂ := by
  apply card_lt_card
  have hsub : ((range v₁).filter fun v' => w ∈ H v') ⊆ (range v₂).filter fun v' => w ∈ H v' := by
    intro x hx
    simp only [mem_filter, mem_range] at hx ⊢
    exact ⟨hx.1.trans h, hx.2⟩
  rw [ssubset_iff_of_subset hsub]
  exact ⟨v₁, by simp [h, hw], by simp⟩

theorem rank_inj {w v₁ v₂ : ℕ} (hw₁ : w ∈ H v₁) (hw₂ : w ∈ H v₂)
    (h : rank H w v₁ = rank H w v₂) : v₁ = v₂ := by
  rcases lt_trichotomy v₁ v₂ with hlt | heq | hgt
  · exact absurd h (rank_lt_rank hlt hw₁).ne
  · exact heq
  · exact absurd h (rank_lt_rank hgt hw₂).ne'

theorem rank_congr {H' : ℕ → Finset ℕ} {w v : ℕ} (h : ∀ i < v, H i = H' i) :
    rank H w v = rank H' w v := by
  unfold rank
  congr 1
  apply filter_congr
  intro x hx
  rw [h x (mem_range.1 hx)]

/-! ### The blow-up sequence -/

/-- `σ` permutes the positions `0, …, R-1` of every block (and never leaves the block). -/
structure BlockPerm (R : ℕ) (σ : ℕ → ℕ → ℕ) : Prop where
  lt : ∀ w t, σ w t < R
  inj : ∀ w t t', t < R → t' < R → σ w t = σ w t' → t = t'

/-- The blow-up of `H` with blocks of size `R`: vertex `p` lies in the block of `p / R`, and its
earlier neighbours are the servers `w*R + σ w (rank H w (p/R))` of the arcs `w → p/R`. -/
def blowSeq (R : ℕ) (H : ℕ → Finset ℕ) (σ : ℕ → ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (H (p / R)).image fun w => w * R + σ w (rank H w (p / R))

variable {R : ℕ} {σ : ℕ → ℕ → ℕ}

theorem div_add_lt {w t : ℕ} (hR : 0 < R) (ht : t < R) : (w * R + t) / R = w := by
  rw [Nat.mul_comm, Nat.mul_add_div hR, Nat.div_eq_of_lt ht, Nat.add_zero]

theorem mem_blowSeq (hR : 0 < R) (hσ : BlockPerm R σ) {x p : ℕ} :
    x ∈ blowSeq R H σ p ↔
      x / R ∈ H (p / R) ∧ x = x / R * R + σ (x / R) (rank H (x / R) (p / R)) := by
  unfold blowSeq
  simp only [mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [div_add_lt hR (hσ.lt _ _)]
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, hx⟩
    exact ⟨x / R, hw, hx.symm⟩

theorem blowSeq_div (hR : 0 < R) (p : ℕ) : blowSeq R H σ (p / R * R) = blowSeq R H σ p := by
  unfold blowSeq
  rw [Nat.mul_div_cancel _ hR]

theorem lt_of_mem_blowSeq (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ) {x p : ℕ}
    (hx : x ∈ blowSeq R H σ p) : x < p := by
  obtain ⟨hw, hxeq⟩ := (mem_blowSeq hR hσ).1 hx
  have h₁ : x / R < p / R := mem_range.1 (hH _ hw)
  have h₂ : x / R * R + R ≤ p / R * R := by
    have := Nat.mul_le_mul_right R h₁
    rwa [Nat.succ_mul] at this
  have h₃ : p / R * R ≤ p := Nat.div_mul_le_self p R
  have h₄ := hσ.lt (x / R) (rank H (x / R) (p / R))
  omega

theorem blowSeq_valid (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ) :
    ValidSeq (blowSeq R H σ) :=
  fun _ _ hx => mem_range.2 (lt_of_mem_blowSeq hH hR hσ hx)

/-- A vertex serves at most one block among the first `m`: if `x` is an earlier neighbour of `p₁`
and of `p₂`, both in the first `m` blocks, then `p₁` and `p₂` are in the same block. -/
theorem block_eq_of_mem (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ) {m : ℕ}
    (hdeg : ∀ w < m, postDeg H m w ≤ R) {x p₁ p₂ : ℕ}
    (hx₁ : x ∈ blowSeq R H σ p₁) (hx₂ : x ∈ blowSeq R H σ p₂) (h₁ : p₁ / R < m) (h₂ : p₂ / R < m) :
    p₁ / R = p₂ / R := by
  obtain ⟨hw₁, hx₁⟩ := (mem_blowSeq hR hσ).1 hx₁
  obtain ⟨hw₂, hx₂⟩ := (mem_blowSeq hR hσ).1 hx₂
  set w := x / R
  have hwm : w < m := (mem_range.1 (hH _ hw₁)).trans h₁
  have hr₁ : rank H w (p₁ / R) < R := (rank_lt_rank h₁ hw₁).trans_le (hdeg w hwm)
  have hr₂ : rank H w (p₂ / R) < R := (rank_lt_rank h₂ hw₂).trans_le (hdeg w hwm)
  have hσeq : σ w (rank H w (p₁ / R)) = σ w (rank H w (p₂ / R)) := by omega
  exact rank_inj hw₁ hw₂ (hσ.inj w _ _ hr₁ hr₂ hσeq)

/-! ### The blow-up structure -/

section BlowUpOf

/-- The block map of the blow-up. -/
def blockMap (R m : ℕ) (x : Fin (m * R)) : Fin m :=
  ⟨x / R, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq x.2 (Nat.mul_comm m R))⟩

open Classical in
/-- The serve map of the blow-up: `x` serves the arc into `v` iff `x` is an earlier neighbour of the
first vertex `v*R` of the block of `v`. -/
noncomputable def serveMap (R : ℕ) (H : ℕ → Finset ℕ) (σ : ℕ → ℕ → ℕ) (m : ℕ) (x : Fin (m * R)) :
    Option (Fin m) :=
  if h : ∃ v : Fin m, (x : ℕ) ∈ blowSeq R H σ (v * R) then some h.choose else none

variable {m : ℕ}

theorem serveMap_eq_some (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ R) {x : Fin (m * R)} {v : Fin m} :
    serveMap R H σ m x = some v ↔ (x : ℕ) ∈ blowSeq R H σ (v * R) := by
  classical
  unfold serveMap
  constructor
  · intro hs
    split_ifs at hs with h
    · cases hs
      exact h.choose_spec
  · intro hx
    have h : ∃ v : Fin m, (x : ℕ) ∈ blowSeq R H σ (v * R) := ⟨v, hx⟩
    rw [dite_eq_left_of_eq_true (eq_true h)]
    congr 1
    apply Fin.ext
    have e := block_eq_of_mem hH hR hσ hdeg h.choose_spec hx
      (by rw [Nat.mul_div_cancel _ hR]; exact h.choose.2)
      (by rw [Nat.mul_div_cancel _ hR]; exact v.2)
    rwa [Nat.mul_div_cancel _ hR, Nat.mul_div_cancel _ hR] at e

theorem mem_blowSeq_iff_serveMap (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ R) (x u : Fin (m * R)) :
    (x : ℕ) ∈ blowSeq R H σ u ↔ serveMap R H σ m x = some (blockMap R m u) := by
  rw [serveMap_eq_some hH hR hσ hdeg]
  change _ ↔ (x : ℕ) ∈ blowSeq R H σ (u / R * R)
  rw [blowSeq_div hR]

/-- The first `m * R` vertices of `blowSeq R H σ` form a blow-up of the first `m` vertices of
`H`. -/
noncomputable def blowUpOf (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ R) :
    BlowUp (OnlineInput.ofSeq H hH m).graph
      (OnlineInput.ofSeq (blowSeq R H σ) (blowSeq_valid hH hR hσ) (m * R)).graph where
  π := blockMap R m
  serve := serveMap R H σ m
  π_surjective v := ⟨⟨v * R, Nat.mul_lt_mul_of_pos_right v.2 hR⟩,
    Fin.ext (Nat.mul_div_cancel _ hR)⟩
  lt_of_π_lt x y h := Fin.lt_def.2 (Nat.lt_of_div_lt_div (Fin.lt_def.1 h))
  serve_spec x v h := by
    have hx := (serveMap_eq_some hH hR hσ hdeg).1 h
    obtain ⟨hw, -⟩ := (mem_blowSeq hR hσ).1 hx
    rw [Nat.mul_div_cancel _ hR] at hw
    refine ⟨Fin.lt_def.2 (mem_range.1 (hH _ hw)), OnlineInput.ofSeq_adj.2 (Or.inl hw)⟩
  adj_iff x u := by
    rw [OnlineInput.ofSeq_adj, mem_blowSeq_iff_serveMap hH hR hσ hdeg,
      mem_blowSeq_iff_serveMap hH hR hσ hdeg]
    constructor
    · rintro (h | h)
      · refine Or.inl ⟨?_, h⟩
        have := (mem_blowSeq_iff_serveMap hH hR hσ hdeg x u).2 h
        exact Fin.lt_def.2 (lt_of_mem_blowSeq hH hR hσ this)
      · refine Or.inr ⟨?_, h⟩
        have := (mem_blowSeq_iff_serveMap hH hR hσ hdeg u x).2 h
        exact Fin.lt_def.2 (lt_of_mem_blowSeq hH hR hσ this)
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h

/-- It is a reservation blow-up: the arc `w → v` is served by `w*R + σ w (rank H w v)` only. -/
theorem blowUpOf_isReservation (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ R) :
    (blowUpOf hH hR hσ hdeg).IsReservation := by
  intro w v hwv hadj
  have hw : (w : ℕ) ∈ H v := by
    rcases OnlineInput.ofSeq_adj.1 hadj with h | h
    · exact h
    · exact absurd (mem_range.1 (hH _ h)) (not_lt.2 (Fin.lt_def.1 hwv).le)
  have hlt : (w : ℕ) * R + σ w (rank H w v) < m * R := by
    have h₁ := hσ.lt w (rank H w v)
    have h₂ : (w : ℕ) * R + R ≤ m * R := by
      have := Nat.mul_le_mul_right R (Nat.succ_le_of_lt w.2)
      rwa [Nat.succ_mul] at this
    omega
  set x : Fin (m * R) := ⟨w * R + σ w (rank H w v), hlt⟩
  have hπ : blockMap R m x = w := Fin.ext (div_add_lt hR (hσ.lt _ _))
  have hmem : (x : ℕ) ∈ blowSeq R H σ (v * R) := by
    rw [mem_blowSeq hR hσ, Nat.mul_div_cancel _ hR]
    change _ ∧ (w : ℕ) * R + σ w (rank H w v) = _
    rw [div_add_lt hR (hσ.lt _ _)]
    exact ⟨hw, rfl⟩
  refine ⟨x, ⟨hπ, (serveMap_eq_some hH hR hσ hdeg).2 hmem⟩, ?_⟩
  rintro y ⟨hyw, hyv⟩
  have hy := (serveMap_eq_some hH hR hσ hdeg).1 hyv
  obtain ⟨-, hyeq⟩ := (mem_blowSeq hR hσ).1 hy
  have hyw' : (y : ℕ) / R = w := congrArg Fin.val hyw
  rw [Nat.mul_div_cancel _ hR, hyw'] at hyeq
  exact Fin.ext hyeq

/-- Every vertex of the blow-up has post-degree at most `R`. -/
theorem postDeg_blowSeq_le (hH : ValidSeq H) (hR : 0 < R) (hσ : BlockPerm R σ)
    (hdeg : ∀ w < m, postDeg H m w ≤ R) (x : ℕ) :
    postDeg (blowSeq R H σ) (m * R) x ≤ R := by
  unfold postDeg rank
  set S := (range (m * R)).filter fun u => x ∈ blowSeq R H σ u
  rcases S.eq_empty_or_nonempty with hS | ⟨u₀, hu₀⟩
  · rw [hS, card_empty]; exact Nat.zero_le _
  · have hu₀' := mem_filter.1 hu₀
    have hdiv : ∀ u < m * R, u / R < m := fun u hu =>
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hu)
    have hsub : S ⊆ Ico (u₀ / R * R) (u₀ / R * R + R) := by
      intro u hu
      have hu' := mem_filter.1 hu
      have e := block_eq_of_mem hH hR hσ hdeg hu'.2 hu₀'.2
        (hdiv u (mem_range.1 hu'.1)) (hdiv u₀ (mem_range.1 hu₀'.1))
      rw [mem_Ico, ← e]
      exact ⟨Nat.div_mul_le_self u R, Nat.lt_div_mul_add hR⟩
    calc S.card ≤ (Ico (u₀ / R * R) (u₀ / R * R + R)).card := card_le_card hsub
      _ = R := by simp

end BlowUpOf

end OnlineColouring
