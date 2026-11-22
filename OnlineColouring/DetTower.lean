module

public import OnlineColouring.Det
public import OnlineColouring.UExact

/-!
# Uniform towers are full towers; Theorem 8.5 (ii) as a consequence of determinacy

Theorem 8.5 (ii): *There is a deterministic adaptive adversary, every play of which is a uniform
tower over `K_m` with `j` levels, that forces every deterministic online algorithm to use at
least `⌈X_m⌉` colours*, where `X_m = (2m+1)/(4(1+ln 4m))`, `j ≥ 1`, `m ≥ 2`.

## What "every play of which is a uniform tower" means

The uniform tower is the full `j`-level tower over `K_m` in which every node of positive level
has exactly `A = 2m` children, presented phase by phase in depth-first order, with some *wiring*:
top servers `x_s(v_t)` that are children of `v_s` that have not served before, and a bijection
`σ(u) → σ(x_s(u))` for every `s < t` and every node `u` of level `≥ 2` below `v_t`, including
`u = v_t`.  The legal wirings are given by the points `ω` of the sample space `EΩ m j (2m)` of
the random wiring `R_j(m)` (`UWiringE.lean`; the coordinates with `s ≥ t` are not used), and
`uInputE ω` is the presented ordered graph of the wiring `ω`.  So
"every play of which is a uniform tower over `K_m` with `j` levels" is formalized as: the final
graph of every play is the presented graph `(uInputE ω).graph` of some wiring `ω`, in its arrival
order, that is, the adversary `Det.Presents` the set `Set.range (uInputE hA)`.

## Results

* `Det.ueInput_isFullTower`, `Det.uInputE_isFullTower`: the presented graph of every wiring is a
  `j`-fold *full* blow-up of `K_m` (`IsFullTower m j`), hence a tower in the sense of
  Definition 4.7 (`Det.uInputE_isPaddedTower`, `DetValue.lean`).  This is the fullness part of
  Lemma 8.2 (`Rjm.uniform_graph` in `RjmGraph.lean` states the lemma with reservation blow-ups).
  Fullness: the arc `w → v` between nodes at depth `k` is served by the earlier neighbour, below
  the root of `w`, of the first child of `v`.
* `Det.exists_realization`: Theorem 8.5 (ii) in per-algorithm form: every proper algorithm uses
  at least `⌈X_m⌉` colours on some wiring.
* `Det.uniform_tower_adversary`, `Det.uniform_tower_adversary_graph`: Theorem 8.5 (ii), obtained
  from determinacy (`Det.exists_presents`) applied to the set of wirings and Theorem 8.5 (i)
  (`avg_numCols_geE`: the mean number of colours over the wirings is at least `X_m`, so some
  wiring has at least `X_m` colours).

The adversary of the paper's proof, which chooses in every phase the first wiring with
`H_t ≤ 1/4`, is `Expl.adv` (`ExplAdv.lean`); `Expl.adv_presents` is Theorem 8.5 (ii) for it,
with the same statement as `Det.uniform_tower_adversary`.
-/

@[expose] public section

namespace OnlineColouring

namespace Det

open Finset

/-! ### The tower with one bijection per node is a full tower -/

section Full

variable {A : ℕ} {τ : ℕ → ℕ → ℕ} {φ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}

/-- **The uniform tower is a full tower.**  If the top servers of each root are distinct and the
server maps are injective, the graph at depth `k` is a `k`-fold full blow-up of `K_m`. -/
theorem ueInput_isFullTower (hA : 0 < A) (hτ : ∀ s t, τ s t < A)
    (hφ : ∀ s t k g i, φ s t k g i < A)
    (hφinj : ∀ s t k g i i', i < A → i' < A → φ s t k g i = φ s t k g i' → i = i') {m : ℕ}
    (hinj : ∀ s t t', s < t → t < m → s < t' → t' < m → τ s t = τ s t' → t = t') (k : ℕ) :
    IsFullTower m k (ueInput hA hτ hφ m k).toOrdGraph := by
  induction k with
  | zero =>
    have h : (ueInput hA hτ hφ m 0).toOrdGraph = OrdGraph.clique m := by
      unfold ueInput
      rw [OnlineInput.ofSeq_congr ueSeq_zero]
      exact ofSeq_cliqueSeq m
    rw [h]
    exact .clique
  | succ k ih =>
    have G1 : ∀ x y : Fin (utSize A m (k + 1)), x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y →
        divMap rfl x ∈ (ueInput hA hτ hφ m k).nbr (divMap rfl y) := by
      intro x y hxy
      obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
      refine mem_ueInput_nbr.2 (mem_ueSeq.2 ⟨s, ?_, ?_⟩)
      · change s < y / A / A ^ k
        rwa [← div_pow_succ]
      · change ueNb A τ φ k s (y / A) = x / A
        rw [← hsx, ueNb_succ_div hA hτ hφ]
    have G2 : ∀ x y y' : Fin (utSize A m (k + 1)), (y : ℕ) / A = y' / A →
        x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y → x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y' := by
      intro x y y' hyy hxy
      obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
      refine (mem_ueInput_nbr (k := k + 1)).2 ?_
      have hr : (y : ℕ) / A ^ (k + 1) = y' / A ^ (k + 1) := by
        rw [div_pow_succ, div_pow_succ, hyy]
      exact mem_ueSeq.2 ⟨s, hr ▸ hs, (ueNb_congr hyy.symm).trans hsx⟩
    have G3 : ∀ x y y' : Fin (utSize A m (k + 1)),
        x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y → x ∈ (ueInput hA hτ hφ m (k + 1)).nbr y' →
        (y : ℕ) / A = y' / A := by
      intro x y y' hxy hxy'
      obtain ⟨s, hs, hsx⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy)
      obtain ⟨s', hs', hsx'⟩ := mem_ueSeq.1 ((mem_ueInput_nbr (k := k + 1)).1 hxy')
      have hss : s = s' := by
        have h₁ := ueNb_div_pow hA hτ hφ (k + 1) s y
        have h₂ := ueNb_div_pow hA hτ hφ (k + 1) s' y'
        rw [hsx] at h₁
        rw [hsx'] at h₂
        rw [← h₁, ← h₂]
      subst hss
      exact ueNb_inj hA hτ hφ hφinj (hinj s) k hs (root_lt y.2) hs' (root_lt y'.2)
        (hsx.trans hsx'.symm)
    refine .blowUp ih ⟨divBlowUp hA rfl _ _ G1 G2 G3, ?_⟩
    -- fullness: the arc `w → v` is served by the neighbour below `w`'s root of `v`'s first child
    intro (w : Fin (utSize A m k)) (v : Fin (utSize A m k)) hwv hadj
    have hmem : w ∈ (ueInput hA hτ hφ m k).nbr v := by
      rcases hadj with h | h
      · exact h
      · exact absurd ((ueInput hA hτ hφ m k).nbr_lt _ _ h) (not_lt.2 hwv.le)
    obtain ⟨s, hs, hsw⟩ := mem_ueSeq.1 (mem_ueInput_nbr.1 hmem)
    have hyA : (v : ℕ) * A < utSize A m (k + 1) := Nat.mul_lt_mul_of_pos_right v.2 hA
    have hydiv : (v : ℕ) * A / A = v := Nat.mul_div_cancel _ hA
    have hxmem : ueNb A τ φ (k + 1) s (v * A) ∈ ueSeq A τ φ (k + 1) (v * A) :=
      mem_ueSeq.2 ⟨s, by rw [div_pow_succ, hydiv]; exact hs, rfl⟩
    have hxlt : ueNb A τ φ (k + 1) s (v * A) < v * A :=
      mem_range.1 (ueSeq_valid hA hτ hφ (k + 1) _ hxmem)
    have hxy : (⟨ueNb A τ φ (k + 1) s (v * A), hxlt.trans hyA⟩ : Fin (utSize A m (k + 1))) ∈
        (ueInput hA hτ hφ m (k + 1)).nbr ⟨v * A, hyA⟩ := mem_ueInput_nbr.2 hxmem
    refine ⟨⟨ueNb A τ φ (k + 1) s (v * A), hxlt.trans hyA⟩, ?_, ?_⟩
    · apply Fin.ext
      change ueNb A τ φ (k + 1) s (v * A) / A = w
      rw [ueNb_succ_div hA hτ hφ, hydiv]
      exact hsw
    · exact (divServe_of_mem (hM := rfl) G3 hxy).trans (congrArg some (Fin.ext hydiv))

end Full

variable {m j A : ℕ}

/-- Every realization of the wiring is a `j`-fold full blow-up of `K_m`. -/
theorem uInputE_isFullTower (hA : 0 < A) (ω : EΩ m j A) :
    IsFullTower m j (uInputE hA ω).toOrdGraph :=
  ueInput_isFullTower hA (tauE_lt ω hA) (phiE_lt ω hA) (phiE_inj ω) (tauE_inj ω) j

/-! ### Theorem 8.5 (ii) -/

/-- Theorem 8.5 (ii), per algorithm, for `R_j(m)`: against every proper algorithm, some
realization has at least `⌈X_m⌉` colours, because the mean over the realizations is at least
`X_m`. -/
theorem exists_realization (hm : 2 ≤ m) (hj : 1 ≤ j) (hA : 0 < 2 * m) (alg : OnlineAlg)
    (halg : alg.IsProper) :
    ∃ ω : EΩ m j (2 * m), ⌈uniformBound m⌉₊ ≤ (uInputE hA ω).cost alg := by
  have : Nonempty (EΩ m j (2 * m)) := nonempty_EΩ (by omega)
  obtain ⟨ω, hω⟩ : ∃ ω : EΩ m j (2 * m), uniformBound m ≤ numColsE alg ω := by
    by_contra hcon
    push Not at hcon
    have havg := avg_numCols_geE (j := j) hm hj alg halg
    have hQ : (0 : ℝ) < Fintype.card (EΩ m j (2 * m)) := by exact_mod_cast Fintype.card_pos
    rw [le_div_iff₀ hQ] at havg
    have hlt : ∑ ω : EΩ m j (2 * m), (numColsE alg ω : ℝ) <
        ∑ _ω : EΩ m j (2 * m), uniformBound m :=
      sum_lt_sum_of_nonempty univ_nonempty fun ω _ => hcon ω
    rw [sum_const, card_univ, nsmul_eq_mul] at hlt
    linarith
  refine ⟨ω, ?_⟩
  rw [numColsE_eq_cost]
  exact Nat.ceil_le.2 hω

/-- **Theorem 8.5 (ii).**  For `j ≥ 1` and `m ≥ 2` there is an adversary that, against every
proper deterministic algorithm, presents in full the uniform tower of some wiring `ω` of
`R_j(m)` (the history of the play is the run of the algorithm on `uInputE ω`) and then stops,
and the algorithm uses at least `⌈X_m⌉` colours. -/
theorem uniform_tower_adversary (hj : 1 ≤ j) (hm : 2 ≤ m) (hA : 0 < 2 * m) :
    ∃ adv : Adversary,
      Presents adv (Set.range (uInputE (m := m) (j := j) hA)) ⌈uniformBound m⌉₊ :=
  exists_presents _ fun alg halg => by
    obtain ⟨ω, hω⟩ := exists_realization hm hj hA alg halg
    exact ⟨_, ⟨ω, rfl⟩, hω⟩

/-- **Theorem 8.5 (ii), unpacked.**  There is an adversary that forces `⌈X_m⌉` colours, every
play of which has exactly `m (2m)^j` vertices when it stops, and the final graph of every play is
the presented graph of a uniform tower over `K_m` with `j` levels: the graph of `uInputE ω` for a
wiring `ω`, in its arrival order.  This graph is a `j`-fold full blow-up of `K_m`, and it is
`k`-colourable whenever `m ≤ |P_j(k)|`. -/
theorem uniform_tower_adversary_graph (hj : 1 ≤ j) (hm : 2 ≤ m) (hA : 0 < 2 * m) :
    ∃ adv : Adversary, adv.Forces ⌈uniformBound m⌉₊ ∧ adv.SizeLE (m * (2 * m) ^ j) ∧
      (∀ A : OnlineAlg, A.IsProper → ∃ ω : EΩ m j (2 * m), ∀ p, adv.StopsAt A p →
        ∃ e : (adv.hist A p).length = utSize (2 * m) m j,
          (adv.hist A p).graph = (uInputE hA ω).graph.comap (Fin.cast e)) ∧
      (adv.LandsIn fun n G => IsFullTower m j ⟨Fin n, G⟩) ∧
      ∀ k, m ≤ Fintype.card (LabelPoset k j) → adv.LandsIn fun _ G => G.Colorable k := by
  obtain ⟨adv, hadv⟩ := uniform_tower_adversary hj hm hA
  refine ⟨adv, hadv.forces, ?_, ?_, ?_, ?_⟩
  · rw [← utSize_eq]
    exact hadv.sizeLE
  · intro A hA'
    obtain ⟨I, ⟨ω, rfl⟩, -, hp⟩ := hadv.final_graph hA'
    exact ⟨ω, hp⟩
  · refine hadv.landsIn (C := fun n G => IsFullTower m j ⟨Fin n, G⟩) ?_
    rintro _ ⟨ω, rfl⟩
    exact uInputE_isFullTower hA ω
  · intro k hk
    refine hadv.landsIn (C := fun _ G => G.Colorable k) ?_
    rintro _ ⟨ω, rfl⟩
    exact uInputE_colorable ω hA hk

end Det

end OnlineColouring
