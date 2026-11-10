module

public import ABBKS26.Tree.Split
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-! Helpers for the finite expectation gap and its probability bound. -/

@[expose] public section

namespace ABBKS26.Tree.CompleteAux

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Common
open scoped BigOperators

private theorem step_bound (m : ℕ) (f : Fin (m + 1) → ℝ) (L : ℝ)
    (h : ∀ i : Fin m, f i.succ - f i.castSucc ≤ L) :
    f (Fin.last m) - f 0 ≤ m * L := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (fun i ↦ f i.castSucc) (fun i ↦ h i.castSucc)
    have hl := h (Fin.last m)
    simp only [Nat.cast_add, Nat.cast_one] at *
    have he : (Fin.last m).succ = Fin.last (m + 1) := rfl
    rw [he] at hl
    change f (Fin.last m).castSucc - f 0 ≤ (m : ℝ) * L at hp
    linarith

/-- A finite real set with a large spread has an empty gap between two of its elements. -/
theorem expectation_gap {s : Finset ℝ} {a b L : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hspread : ((s.card : ℝ) - 1) * L < b - a) :
    ∃ lo ∈ s, ∃ hi ∈ s, lo + L < hi ∧ ∀ x ∈ s, x ≤ lo ∨ hi ≤ x := by
  classical
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard)
  let e := s.orderIsoOfFin hm
  let f : Fin (m + 1) → ℝ := fun i ↦ (e i : ℝ)
  have hmono : Monotone f := fun i j hij ↦ e.monotone hij
  have hlow : f 0 ≤ a := by
    simpa [f] using hmono (Fin.zero_le (e.symm ⟨a, ha⟩))
  have hhigh : b ≤ f (Fin.last m) := by
    simpa [f] using hmono (Fin.le_last (e.symm ⟨b, hb⟩))
  have hgap : ∃ i : Fin m, L < f i.succ - f i.castSucc := by
    by_contra h
    have hstep : ∀ i : Fin m, f i.succ - f i.castSucc ≤ L := by
      simpa only [not_exists, not_lt] using h
    have hbound := step_bound m f L hstep
    rw [hm] at hspread
    push_cast at hspread
    linarith
  obtain ⟨i, hi⟩ := hgap
  refine ⟨f i.castSucc, (e i.castSucc).2, f i.succ, (e i.succ).2, by linarith, ?_⟩
  intro x hx
  let j := e.symm ⟨x, hx⟩
  have hej : f j = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  by_cases hji : j ≤ i.castSucc
  · exact Or.inl (hej ▸ hmono hji)
  · have hij : i.succ ≤ j := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    exact Or.inr (hej ▸ hmono hij)

/-- Every rational quadratic statistic has a second moment under any Gaussian. -/
theorem statistic_memLp {d : ℕ} (q : Statistic d) (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) :
    MemLp (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp) 2
      (multivariateGaussian μ S) := by
  have : ENNReal.HolderTriple 4 4 2 := by
    apply ENNReal.HolderTriple.of_toReal
    constructor <;> norm_num
  let ν := multivariateGaussian μ S
  have hc (i : Fin d) (p : ENNReal) (hp : p ≠ ⊤) :
      MemLp (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) p ν :=
    IsGaussian.memLp_dual ν (EuclideanSpace.proj i) p hp
  have hquad : MemLp (fun y : EuclideanSpace ℝ (Fin d) ↦
      ∑ i, ∑ j, (q.A i j : ℝ) * (y.ofLp i * y.ofLp j)) 2 ν := by
    apply memLp_finsetSum
    intro i _
    apply memLp_finsetSum
    intro j _
    exact ((hc i 4 (by norm_num)).mul (hc j 4 (by norm_num))).const_mul _
  have hlin : MemLp (fun y : EuclideanSpace ℝ (Fin d) ↦
      ∑ i, (q.b i : ℝ) * y.ofLp i) 2 ν := by
    apply memLp_finsetSum
    intro i _
    exact (hc i 2 (by norm_num)).const_mul _
  convert (hquad.add hlin).add (memLp_const (q.c : ℝ)) using 1
  ext y
  simp only [Statistic.eval, qform, dotProduct, mulVec, map_apply,
    Finset.mul_sum, Pi.add_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change y.ofLp i * ((q.A i j : ℝ) * y.ofLp j) = _
  ring

/-- Chebyshev's inequality in real-valued measure notation. -/
theorem tail_bound {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : MemLp f 2 ν) (c r V : ℝ)
    (hc : c = ∫ x, f x ∂ν) (hr : 0 < r) (hvar : variance f ν ≤ V) :
    ν.real {x | r ≤ |f x - c|} ≤ V / r ^ 2 := by
  rw [hc]
  have h := meas_ge_le_variance_div_sq hf hr
  have hv : 0 ≤ variance f ν / r ^ 2 :=
    div_nonneg (variance_nonneg f ν) (sq_nonneg r)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hv] at hreal
  exact hreal.trans (div_le_div_of_nonneg_right hvar (sq_nonneg r))

end

end ABBKS26.Tree.CompleteAux
