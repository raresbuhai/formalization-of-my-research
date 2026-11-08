module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rounding a pseudo-expectation to one cluster

One round of the algorithm of [BS23, Theorem 1.3] reads two tables off a pseudo-expectation:
`mw i = Ẽ[wᵢ]` and `mww i i' = Ẽ[wᵢ wᵢ']`. It picks a pivot `i₀` with probability proportional to
`max (mw i₀) 0` and outputs the set `C(i₀) = {i : mw i₀ ≤ 2 mww i₀ i}`
(`BS23.SmallRadius.RoundData.roundSet`). This file proves, with pure real arithmetic, that `C(i₀)`
is close to the cluster `T` of the pivot for most pivots.

The data (`BS23.SmallRadius.RoundData`) are the cluster `cl i` of each point and the two tables;
the clusters are `T_c = {i : cl i = c}` (`BS23.SmallRadius.RoundData.clSet`) of sizes `τ_c`
(`BS23.SmallRadius.RoundData.csize`). The hypotheses (`BS23.SmallRadius.RoundData.Hyp`), with
an objective level `τs`, slack `γ`, cross mass `ε` and soundness error `err`:

* `mww i i' ≥ -err` and `mw i - mww i i' ≥ -err` (Booleanity, up to `err`);
* `∑ mw ≥ τs - γ` (the objective is nearly optimal);
* `(∑ mw)² ≤ ∑∑ mww` (Cauchy–Schwarz, exact: `Ẽ (∑ w - c)² ≥ 0`);
* `∑_{cl i ≠ cl i'} mww i i' ≤ ε` (identifiability);
* `τ_c ≤ τs` for every cluster `c`, `0 ≤ γ ≤ τs/2`, `0 ≤ err` and `τs ≤ N`.

The matrix `mww` need not be symmetric, and `mww i i` need not equal `mw i`.

With `Z = ∑ max (mw i) 0` (`BS23.SmallRadius.RoundData.Z`):

* `BS23.SmallRadius.RoundData.weighted_error_le`:
  `∑_{i₀} max (mw i₀) 0 · |C(i₀) ∆ T_{cl i₀}| ≤ 2 (γ Z + 2 ε + 3 N² err)`;
* `BS23.SmallRadius.RoundData.weighted_small_le`: for `θ > 0`, the pivots in clusters of size
  `≤ τs - θ` have weight `∑ max (mw i₀) 0 ≤ (γ Z + ε + 3 N² err) / θ`;
* `BS23.SmallRadius.RoundData.weighted_large_le` (Markov) and
  `BS23.SmallRadius.RoundData.weighted_fail_le` (both failure modes at once): the pivots with
  `|C(i₀) ∆ T_{cl i₀}| > E` or in a cluster of size `≤ τs - θ` have weight
  `≤ 2 (γ Z + 2 ε + 3 N² err) / E + (γ Z + ε + 3 N² err) / θ`.
* `BS23.SmallRadius.RoundData.Hyp.half_le_Z`: `τs / 2 ≤ Z`.

**Proof.** Let `W = ∑ mw` and `Φ i = ∑_{cl i' = cl i} (mw i - mww i i')`. Then
`(τs - γ) W ≤ W² ≤ ∑_i (τ_{cl i} mw i - Φ i) + ε`, so
`∑ Φ + ∑_i (τs - τ_{cl i}) mw i ≤ γ W + ε` (`BS23.SmallRadius.RoundData.Hyp.key`), with
`γ W ≤ γ Z`. The first sum is at least `-N² err`; the second is at least `-2 N² err`, as
`mw i ≥ -2 err` and `0 ≤ τs - τ_{cl i} ≤ N`. For a pivot `i₀` with `m = mw i₀ > 0`, a point of
`T \ C(i₀)` has `m < 2 (m - mww i₀ i)` and a point of `C(i₀) \ T` has `m ≤ 2 mww i₀ i`, so
`m |C(i₀) ∆ T| ≤ 2 ∑_{i ∈ T} (m - mww i₀ i)⁺ + 2 ∑_{i ∉ T} (mww i₀ i)⁺`, and positive parts are at
most the value plus `err` (`BS23.SmallRadius.RoundData.Hyp.pivot_le`). Summing over `i₀` gives
`2 (∑ Φ + ε + N² err)`.
-/

@[expose] public section

namespace BS23.SmallRadius

open Finset
open scoped symmDiff

/-- The tables read off a pseudo-expectation in one round: the cluster `cl i` of each of the `N`
points, `mw i = Ẽ[wᵢ]` and `mww i i' = Ẽ[wᵢ wᵢ']`. -/
structure RoundData (N K : ℕ) where
  /-- The true cluster of each point. -/
  cl : Fin N → Fin K
  /-- `Ẽ[wᵢ]`. -/
  mw : Fin N → ℝ
  /-- `Ẽ[wᵢ wᵢ']`. -/
  mww : Fin N → Fin N → ℝ

namespace RoundData

variable {N K : ℕ} (D : RoundData N K)

/-- The cluster `T_c = {i : cl i = c}`. -/
def clSet (c : Fin K) : Finset (Fin N) := univ.filter (D.cl · = c)

/-- The size `τ_c = |T_c|` of a cluster. -/
def csize (c : Fin K) : ℕ := (D.clSet c).card

/-- The total positive weight `Z = ∑ max (mw i) 0` of the pivots. -/
noncomputable def Z : ℝ := ∑ i, max (D.mw i) 0

/-- The set output for the pivot `i₀`: `{i : mw i₀ ≤ 2 mww i₀ i}`. -/
noncomputable def roundSet (i₀ : Fin N) : Finset (Fin N) :=
  univ.filter fun i ↦ D.mw i₀ ≤ 2 * D.mww i₀ i

/-- The hypotheses on the tables of one round (objective level `τs`, objective slack `γ`, cross
mass `ε`, soundness error `err`). -/
structure Hyp (τs γ ε err : ℝ) : Prop where
  mww_ge : ∀ i i', -err ≤ D.mww i i'
  sub_ge : ∀ i i', -err ≤ D.mw i - D.mww i i'
  obj : τs - γ ≤ ∑ i, D.mw i
  cs : (∑ i, D.mw i) ^ 2 ≤ ∑ i, ∑ i', D.mww i i'
  cross : ∑ i, ∑ i' with D.cl i ≠ D.cl i', D.mww i i' ≤ ε
  size : ∀ c, (D.csize c : ℝ) ≤ τs
  hγ : 0 ≤ γ ∧ γ ≤ τs / 2
  err_nonneg : 0 ≤ err
  le_card : τs ≤ N

theorem mem_clSet {c : Fin K} {i : Fin N} : i ∈ D.clSet c ↔ D.cl i = c := by
  simp [clSet]

theorem mem_roundSet {i₀ i : Fin N} : i ∈ D.roundSet i₀ ↔ D.mw i₀ ≤ 2 * D.mww i₀ i := by
  simp [roundSet]

theorem Z_nonneg : 0 ≤ D.Z := sum_nonneg fun _ _ ↦ le_max_right _ _

theorem sum_mw_le_Z : ∑ i, D.mw i ≤ D.Z := sum_le_sum fun _ _ ↦ le_max_left _ _

/-- The in-cluster defect `Φ i = ∑_{cl i' = cl i} (mw i - mww i i')` of a point. -/
noncomputable def defect (i : Fin N) : ℝ := ∑ i' with D.cl i = D.cl i', (D.mw i - D.mww i i')

theorem card_filter_cl_eq (i : Fin N) :
    (univ.filter fun i' ↦ D.cl i = D.cl i').card = D.csize (D.cl i) := by
  unfold csize clSet
  congr 1
  exact filter_congr fun _ _ ↦ eq_comm

theorem csize_le_card (c : Fin K) : (D.csize c : ℝ) ≤ N := by
  have : D.csize c ≤ N := (card_le_univ _).trans_eq (Fintype.card_fin N)
  exact_mod_cast this

variable {D} {τs γ ε err : ℝ}

theorem Hyp.mw_ge (h : D.Hyp τs γ ε err) (i : Fin N) : -(2 * err) ≤ D.mw i := by
  have := h.sub_ge i i
  have := h.mww_ge i i
  linarith

theorem Hyp.tau_nonneg (h : D.Hyp τs γ ε err) : 0 ≤ τs := by
  linarith [h.hγ.1, h.hγ.2]

theorem Hyp.sub_le_Z (h : D.Hyp τs γ ε err) : τs - γ ≤ D.Z := h.obj.trans D.sum_mw_le_Z

theorem Hyp.half_le_Z (h : D.Hyp τs γ ε err) : τs / 2 ≤ D.Z := by
  linarith [h.sub_le_Z, h.hγ.2]

theorem Hyp.defect_ge (h : D.Hyp τs γ ε err) (i : Fin N) : -(N * err) ≤ D.defect i := by
  unfold defect
  rw [sum_filter]
  have : ∑ _j : Fin N, -err ≤ ∑ i', if D.cl i = D.cl i' then D.mw i - D.mww i i' else 0 := by
    refine sum_le_sum fun i' _ ↦ ?_
    split_ifs
    · exact h.sub_ge i i'
    · linarith [h.err_nonneg]
  simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using this

/-- **The key inequality**: `∑ Φ + ∑_i (τs - τ_{cl i}) mw i ≤ γ W + ε`. -/
theorem Hyp.key (h : D.Hyp τs γ ε err) :
    ∑ i, D.defect i + ∑ i, (τs - D.csize (D.cl i)) * D.mw i ≤ γ * ∑ i, D.mw i + ε := by
  set W := ∑ i, D.mw i with hW
  have hW0 : 0 ≤ W := by linarith [h.obj, h.hγ.2, h.tau_nonneg]
  have hsq : (τs - γ) * W ≤ W * W := mul_le_mul_of_nonneg_right h.obj hW0
  have hsplit : ∑ i, ∑ i', D.mww i i' =
      ∑ i, ((D.csize (D.cl i) : ℝ) * D.mw i - D.defect i) +
        ∑ i, ∑ i' with D.cl i ≠ D.cl i', D.mww i i' := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_filter_add_sum_filter_not univ (fun i' ↦ D.cl i = D.cl i')]
    congr 1
    rw [defect, sum_sub_distrib, sum_const, card_filter_cl_eq, nsmul_eq_mul]
    ring
  have h1 : ∑ i, ((D.csize (D.cl i) : ℝ) * D.mw i - D.defect i) =
      ∑ i, (D.csize (D.cl i) : ℝ) * D.mw i - ∑ i, D.defect i := sum_sub_distrib _ _
  have h2 : ∑ i, (τs - D.csize (D.cl i)) * D.mw i =
      τs * W - ∑ i, (D.csize (D.cl i) : ℝ) * D.mw i := by
    simp_rw [sub_mul]
    rw [sum_sub_distrib, hW, mul_sum]
  have hcs := h.cs
  rw [← hW, sq] at hcs
  linarith [h.cross]

/-- `∑ Φ ≤ γ Z + ε + 2 N² err`. -/
theorem Hyp.sum_defect_le (h : D.Hyp τs γ ε err) :
    ∑ i, D.defect i ≤ γ * D.Z + ε + 2 * N ^ 2 * err := by
  have hk := h.key
  have hγZ : γ * ∑ i, D.mw i ≤ γ * D.Z := mul_le_mul_of_nonneg_left D.sum_mw_le_Z h.hγ.1
  have hlow : ∑ _i : Fin N, -(2 * N * err) ≤ ∑ i, (τs - D.csize (D.cl i)) * D.mw i := by
    refine sum_le_sum fun i _ ↦ ?_
    have hc0 : 0 ≤ τs - D.csize (D.cl i) := by linarith [h.size (D.cl i)]
    have hcN : τs - D.csize (D.cl i) ≤ N := by
      have : (0 : ℝ) ≤ D.csize (D.cl i) := Nat.cast_nonneg _
      linarith [h.le_card]
    have := mul_le_mul_of_nonneg_left (h.mw_ge i) hc0
    nlinarith [h.err_nonneg]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  nlinarith

/-- `∑_i (τs - τ_{cl i}) (mw i)⁺ ≤ γ Z + ε + 3 N² err`. -/
theorem Hyp.sum_gap_le (h : D.Hyp τs γ ε err) :
    ∑ i, (τs - D.csize (D.cl i)) * max (D.mw i) 0 ≤ γ * D.Z + ε + 3 * N ^ 2 * err := by
  have hk := h.key
  have hγZ : γ * ∑ i, D.mw i ≤ γ * D.Z := mul_le_mul_of_nonneg_left D.sum_mw_le_Z h.hγ.1
  have hΦ : ∑ _i : Fin N, -(N * err) ≤ ∑ i, D.defect i := sum_le_sum fun i _ ↦ h.defect_ge i
  have hup : ∑ i, (τs - D.csize (D.cl i)) * max (D.mw i) 0 ≤
      ∑ i, ((τs - D.csize (D.cl i)) * D.mw i + 2 * N * err) := by
    refine sum_le_sum fun i _ ↦ ?_
    have hc0 : 0 ≤ τs - D.csize (D.cl i) := by linarith [h.size (D.cl i)]
    have hcN : τs - D.csize (D.cl i) ≤ N := by
      have : (0 : ℝ) ≤ D.csize (D.cl i) := Nat.cast_nonneg _
      linarith [h.le_card]
    have hmax : max (D.mw i) 0 ≤ D.mw i + 2 * err :=
      max_le (by linarith [h.err_nonneg]) (by linarith [h.mw_ge i])
    have := mul_le_mul_of_nonneg_left hmax hc0
    nlinarith [h.err_nonneg]
  rw [sum_add_distrib] at hup
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hup hΦ
  nlinarith

/-! ### One pivot -/

/-- The pointwise bound for one pivot `i₀` and one point `i` of `C(i₀) ∆ T_{cl i₀}`. -/
theorem max_le_of_mem_symmDiff {i₀ i : Fin N} (hi : i ∈ D.roundSet i₀ ∆ D.clSet (D.cl i₀)) :
    max (D.mw i₀) 0 ≤ 2 * (if D.cl i₀ = D.cl i then max (D.mw i₀ - D.mww i₀ i) 0
      else max (D.mww i₀ i) 0) := by
  rw [mem_symmDiff, mem_roundSet, mem_clSet] at hi
  rcases hi with ⟨hC, hT⟩ | ⟨hT, hC⟩
  · rw [ite_eq_right (Ne.symm hT)]
    exact max_le (by linarith [le_max_left (D.mww i₀ i) 0]) (by positivity)
  · rw [ite_eq_left hT.symm]
    exact max_le (by linarith [le_max_left (D.mw i₀ - D.mww i₀ i) 0]) (by positivity)

/-- One pivot: `(mw i₀)⁺ |C(i₀) ∆ T| ≤ 2 (Φ i₀ + ∑_{cl i ≠ cl i₀} mww i₀ i) + 2 N err`. -/
theorem Hyp.pivot_le (h : D.Hyp τs γ ε err) (i₀ : Fin N) :
    max (D.mw i₀) 0 * (D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card ≤
      2 * (D.defect i₀ + ∑ i with D.cl i₀ ≠ D.cl i, D.mww i₀ i) + 2 * N * err := by
  set g : Fin N → ℝ := fun i ↦ if D.cl i₀ = D.cl i then max (D.mw i₀ - D.mww i₀ i) 0
      else max (D.mww i₀ i) 0 with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i ↦ by
    simp only [hg]
    split_ifs <;> exact le_max_right _ _
  have h1 : max (D.mw i₀) 0 * (D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card ≤
      ∑ i ∈ D.roundSet i₀ ∆ D.clSet (D.cl i₀), 2 * g i := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi ↦ D.max_le_of_mem_symmDiff hi
  have h2 : ∑ i ∈ D.roundSet i₀ ∆ D.clSet (D.cl i₀), 2 * g i ≤ ∑ i, 2 * g i :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ by linarith [hg0 i]
  have h3 : ∑ i, 2 * g i ≤ ∑ i, 2 * ((if D.cl i₀ = D.cl i then D.mw i₀ - D.mww i₀ i
      else D.mww i₀ i) + err) := by
    refine sum_le_sum fun i _ ↦ ?_
    simp only [hg]
    split_ifs
    · linarith [max_le (by linarith [h.err_nonneg] : D.mw i₀ - D.mww i₀ i ≤
        D.mw i₀ - D.mww i₀ i + err) (by linarith [h.sub_ge i₀ i] : (0 : ℝ) ≤
        D.mw i₀ - D.mww i₀ i + err)]
    · linarith [max_le (by linarith [h.err_nonneg] : D.mww i₀ i ≤ D.mww i₀ i + err)
        (by linarith [h.mww_ge i₀ i] : (0 : ℝ) ≤ D.mww i₀ i + err)]
  have h4 : ∑ i, 2 * ((if D.cl i₀ = D.cl i then D.mw i₀ - D.mww i₀ i else D.mww i₀ i) + err) =
      2 * (D.defect i₀ + ∑ i with D.cl i₀ ≠ D.cl i, D.mww i₀ i) + 2 * N * err := by
    rw [← mul_sum, sum_add_distrib, sum_ite, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, defect]
    simp only [ne_eq]
    ring
  linarith

/-! ### Summing over the pivots -/

/-- **The weighted rounding error**:
`∑_{i₀} (mw i₀)⁺ |C(i₀) ∆ T_{cl i₀}| ≤ 2 (γ Z + 2 ε + 3 N² err)`. -/
theorem weighted_error_le (h : D.Hyp τs γ ε err) :
    ∑ i₀, max (D.mw i₀) 0 * (D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card ≤
      2 * (γ * D.Z + 2 * ε + 3 * N ^ 2 * err) := by
  have h1 := sum_le_sum fun i₀ (_ : i₀ ∈ univ) ↦ h.pivot_le i₀
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  have := h.sum_defect_le
  have := h.cross
  nlinarith

/-- **Pivots in small clusters**: for `θ > 0`, the pivots whose cluster has size `≤ τs - θ` have
weight `∑ (mw i₀)⁺ ≤ (γ Z + ε + 3 N² err) / θ`. -/
theorem weighted_small_le (h : D.Hyp τs γ ε err) {θ : ℝ} (hθ : 0 < θ) :
    ∑ i₀ with (D.csize (D.cl i₀) : ℝ) ≤ τs - θ, max (D.mw i₀) 0 ≤
      (γ * D.Z + ε + 3 * N ^ 2 * err) / θ := by
  rw [le_div_iff₀ hθ, sum_mul]
  refine le_trans ?_ h.sum_gap_le
  rw [sum_filter]
  refine sum_le_sum fun i _ ↦ ?_
  have hc0 : 0 ≤ τs - D.csize (D.cl i) := by linarith [h.size (D.cl i)]
  have hm : 0 ≤ max (D.mw i) 0 := le_max_right _ _
  split_ifs with hs
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hm
  · exact mul_nonneg hc0 hm

/-- **Markov**: for `E > 0`, the pivots with `|C(i₀) ∆ T_{cl i₀}| > E` have weight
`∑ (mw i₀)⁺ ≤ 2 (γ Z + 2 ε + 3 N² err) / E`. -/
theorem weighted_large_le (h : D.Hyp τs γ ε err) {E : ℝ} (hE : 0 < E) :
    ∑ i₀ with E < ((D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card : ℝ), max (D.mw i₀) 0 ≤
      2 * (γ * D.Z + 2 * ε + 3 * N ^ 2 * err) / E := by
  rw [le_div_iff₀ hE, sum_mul]
  refine le_trans ?_ (weighted_error_le h)
  rw [sum_filter]
  refine sum_le_sum fun i _ ↦ ?_
  have hm : 0 ≤ max (D.mw i) 0 := le_max_right _ _
  split_ifs with hs
  · exact mul_le_mul_of_nonneg_left hs.le hm
  · exact mul_nonneg hm (Nat.cast_nonneg _)

/-- **Failed pivots**: for `E, θ > 0`, the pivots with `|C(i₀) ∆ T_{cl i₀}| > E` or whose cluster
has size `≤ τs - θ` have weight
`∑ (mw i₀)⁺ ≤ 2 (γ Z + 2 ε + 3 N² err) / E + (γ Z + ε + 3 N² err) / θ`. -/
theorem weighted_fail_le (h : D.Hyp τs γ ε err) {E θ : ℝ} (hE : 0 < E) (hθ : 0 < θ) :
    ∑ i₀ with E < ((D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card : ℝ) ∨
        (D.csize (D.cl i₀) : ℝ) ≤ τs - θ, max (D.mw i₀) 0 ≤
      2 * (γ * D.Z + 2 * ε + 3 * N ^ 2 * err) / E + (γ * D.Z + ε + 3 * N ^ 2 * err) / θ := by
  refine le_trans ?_ (add_le_add (weighted_large_le h hE) (weighted_small_le h hθ))
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ ?_
  have hm : 0 ≤ max (D.mw i) 0 := le_max_right _ _
  split_ifs <;> simp_all

end RoundData

end BS23.SmallRadius
