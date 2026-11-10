module

public import ABBKS26.Common.Basic
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A coordinate grid and rational approximation for finite-dimensional sphere nets. -/

@[expose] public section

namespace ABBKS26.Tree.CompleteAux

noncomputable section

open Matrix Common
open scoped BigOperators


/-- Rounding orthonormal coordinates to a finite grid costs at most `r / m` in norm. -/
theorem grid_cover {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r m : ℕ} (b : OrthonormalBasis (Fin r) ℝ E) (hm : 0 < m)
    (v : E) (hv : ‖v‖ ≤ 1) :
    ∃ g : Fin r → Fin (2 * m + 1),
      ‖(∑ i, ((g i : ℝ) / m - 1) • b i) - v‖ ≤ (r : ℝ) / m := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let a : Fin r → ℝ := fun i ↦ (b.repr v).ofLp i
  have ha (i : Fin r) : |a i| ≤ 1 := by
    calc |a i| = ‖(b.repr v).ofLp i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖b.repr v‖ := PiLp.norm_apply_le _ _
      _ = ‖v‖ := b.repr.norm_map _
      _ ≤ 1 := hv
  have ha0 (i : Fin r) : 0 ≤ (m : ℝ) * (a i + 1) := by
    have := (abs_le.mp (ha i)).1
    exact mul_nonneg hm'.le (by linarith)
  let g : Fin r → Fin (2 * m + 1) := fun i ↦
    ⟨⌊(m : ℝ) * (a i + 1)⌋₊, by
      have h := Nat.floor_le (ha0 i)
      have hupper := (abs_le.mp (ha i)).2
      have hle : (⌊(m : ℝ) * (a i + 1)⌋₊ : ℝ) ≤ 2 * m := by nlinarith
      have : ⌊(m : ℝ) * (a i + 1)⌋₊ ≤ 2 * m := by exact_mod_cast hle
      omega⟩
  have herror (i : Fin r) : |(g i : ℝ) / m - 1 - a i| ≤ 1 / m := by
    have hlo := Nat.floor_le (ha0 i)
    have hhi := Nat.lt_floor_add_one ((m : ℝ) * (a i + 1))
    change |(⌊(m : ℝ) * (a i + 1)⌋₊ : ℝ) / m - 1 - a i| ≤ 1 / m
    have hmul : (⌊(m : ℝ) * (a i + 1)⌋₊ : ℝ) / m * m =
        ⌊(m : ℝ) * (a i + 1)⌋₊ := div_mul_cancel₀ _ hm'.ne'
    have hinv : (1 : ℝ) / m * m = 1 := one_div_mul_cancel hm'.ne'
    apply abs_le.mpr
    constructor <;> nlinarith
  refine ⟨g, ?_⟩
  calc ‖(∑ i, ((g i : ℝ) / m - 1) • b i) - v‖ =
      ‖∑ i, (((g i : ℝ) / m - 1) - a i) • b i‖ := by
        rw [← b.sum_repr v, ← Finset.sum_sub_distrib]
        simp only [sub_smul, a]
    _ ≤ ∑ i, ‖(((g i : ℝ) / m - 1) - a i) • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin r, (1 / (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one] using herror i
    _ = (r : ℝ) / m := by simp [div_eq_mul_inv]

/-- The explicit grid fits the advertised bound, with room for rational approximation. -/
theorem grid_size (D : ℕ) (α : ℚ) (hD : 0 < D) (hα : 0 < α ∧ α ≤ 1 / 100) :
    let m := ⌈8 * (D : ℚ) / α⌉₊
    0 < m ∧ 2 * m + 1 ≤ 1 + ⌈64 * (D : ℚ) / α⌉₊ ∧
      (D : ℝ) / m ≤ (α : ℝ) / 8 := by
  dsimp
  have hα0 := hα.1
  have hD' : (1 : ℚ) ≤ D := by exact_mod_cast hD
  have hq : (0 : ℚ) < 8 * D / α := by positivity
  have hm := Nat.le_ceil (8 * (D : ℚ) / α)
  have hm0 : 0 < ⌈8 * (D : ℚ) / α⌉₊ := by
    have : (0 : ℚ) < ⌈8 * (D : ℚ) / α⌉₊ := hq.trans_le hm
    exact_mod_cast this
  refine ⟨hm0, ?_, ?_⟩
  · have hmhi := Nat.ceil_lt_add_one hq.le
    have hbig := Nat.le_ceil (64 * (D : ℚ) / α)
    have hsmall : (2 : ℚ) ≤ 48 * D / α := by
      apply (le_div_iff₀ hα.1).mpr
      nlinarith [hα.2]
    have hle : (2 : ℚ) * ⌈8 * (D : ℚ) / α⌉₊ ≤ ⌈64 * (D : ℚ) / α⌉₊ := by
      ring_nf at hmhi hbig hsmall ⊢
      linarith
    have hle' : 2 * ⌈8 * (D : ℚ) / α⌉₊ ≤ ⌈64 * (D : ℚ) / α⌉₊ := by
      exact_mod_cast hle
    omega
  · have hm' : (0 : ℝ) < ⌈8 * (D : ℚ) / α⌉₊ := by exact_mod_cast hm0
    have hα' : (0 : ℝ) < α := by exact_mod_cast hα.1
    have hmreal : 8 * (D : ℝ) / α ≤ ⌈8 * (D : ℚ) / α⌉₊ := by
      exact_mod_cast hm
    rw [div_le_iff₀ hm']
    have h := (div_le_iff₀ hα').mp hmreal
    nlinarith


/-- Relating the squared norm `sqnorm` to the Euclidean norm. -/
theorem norm_sq {d : ℕ} (v : Vec d) : ‖WithLp.toLp 2 v‖ ^ 2 = sqnorm v := by
  simpa only [sqnorm, dotProduct, pow_two] using
    EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)

end

end ABBKS26.Tree.CompleteAux
