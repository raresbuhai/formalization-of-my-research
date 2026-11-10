module

public import ABBKS26.Centered.Poly
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ABBKS26.Robust.FilterAuxMoments
public import ABBKS26.Robust.FilterAuxStatistics

/-!
# The quadratic filter

A filter on quadratic features of the points, used for robust isotropic position ([ABBKS26,
Fact 3.21]) and inside the Frobenius clustering step ([ABBKS26, Fact 3.22]): each failing
iteration removes mostly corrupted weight or exhibits a direction of large spread, and a
passing iteration gives accurate second moments.
-/

@[expose] public section

namespace ABBKS26.Robust

noncomputable section


open Matrix

open Common Matrix MvPolynomial
open scoped BigOperators
variable {n k d : ℕ}

structure Reference (n k d : ℕ) where
  model : FrameModel k d
  label : Fin n → Fin k
  reference : Finset (Fin n)
  good : Finset (Fin n)
  block : Finset (Fin n)
  clean : Fin n → Vec d
  observed : Fin n → Vec d

def Reference.contamination (D : Reference n k d) : ℝ :=
  max (((D.block \ D.good).card : ℝ) / D.block.card)
    (max (((D.reference \ D.good).card : ℝ) / D.reference.card) (2 / D.block.card))

def Reference.mean (D : Reference n k d) : Vec d :=
  (D.reference.card : ℝ)⁻¹ • ∑ l ∈ D.reference, D.clean l

def Reference.cov (D : Reference n k d) : Mat d :=
  (D.reference.card : ℝ)⁻¹ • ∑ l ∈ D.reference,
    vecMulVec (D.clean l - D.mean) (D.clean l - D.mean)

def Reference.Valid (D : Reference n k d) (π : ℝ) : Prop :=
  D.model.Valid π ∧ D.good ⊆ D.reference ∧ D.good ⊆ D.block ∧
    (∀ l ∈ D.good, D.observed l = D.clean l) ∧ D.reference.Nonempty ∧ D.cov.PosDef ∧
    ∀ j, D.model.weight j =
      ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ) / D.reference.card

/-- The finite clean reference has uniform polynomial moment resilience in every frame. -/
def Reference.Resilient (D : Reference n k d) (s : ℕ) (θ : ℝ) : Prop :=
  ∀ (T : Mat d) (a : Vec d) (j : Fin k) (r : ℕ), r ≤ s →
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    SoS.coeffNorm1
      ((C (Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, lin (T *ᵥ (D.clean l - a)) ^ r) -
        IdCov.hmom r (lin (T *ᵥ (D.model.mean j - a)))
          (quad (T * D.model.cov j * Tᵀ))) ≤
      (θ / (d + 1 : ℝ) ^ (2 * s)) * (1 + SoS.coeffNorm1 (lin (T *ᵥ (D.model.mean j - a))) +
        SoS.coeffNorm1 (quad (T * D.model.cov j * Tᵀ))) ^ r

structure FilterState (n d : ℕ) where
  weights : Fin n → ℝ
  center : Vec d
  frame : Mat d
  featureCov : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ
  power : ℕ

def FilterState.mass (st : FilterState n d) (s : Finset (Fin n)) : ℝ :=
  ∑ l ∈ s, st.weights l

def feature (x : Vec d) : (Fin d × Fin d) → ℝ := fun ij ↦ x ij.1 * x ij.2

def FilterState.score (D : Reference n k d) (st : FilterState n d) (l : Fin n) : ℝ :=
  let y := st.frame *ᵥ (D.observed l - st.center)
  let c := (st.mass D.block)⁻¹ • ∑ i ∈ D.block,
    st.weights i • feature (st.frame *ᵥ (D.observed i - st.center))
  (feature y - c) ⬝ᵥ (st.featureCov ^ st.power *ᵥ (feature y - c))

def TypeA (D : Reference n k d) (st : FilterState n d) : Prop :=
  (∑ l ∈ D.good, st.weights l * st.score D l) ≤
    ∑ l ∈ D.block \ D.good, st.weights l * st.score D l

def sigmaSq (π R : ℝ) : ℝ := 600 / π ^ 2 + 2 * R ^ 2

def maxContamination (π R : ℝ) : ℝ := 1 / (64000 * sigmaSq π R)

def IterationInvariant (D : Reference n k d) (st : FilterState n d) (π : ℝ) : Prop :=
  D.Valid π ∧ D.Resilient 4 (1 / 10000) ∧
  (∀ l, 0 ≤ st.weights l ∧ st.weights l ≤ 1) ∧
  (∀ l, l ∉ D.block → st.weights l = 0) ∧
  (st.frame.det ≠ 0) ∧ st.featureCov.PosSemidef ∧ Even st.power ∧ 2 ≤ st.power ∧
  (d * d : ℝ) ^ (1 / (st.power : ℝ)) ≤ Real.sqrt 2 ∧
  (D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good) ≤ 2 * D.contamination ∧
  (D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good) ≤ 4 * D.contamination ∧
  0.9 * D.reference.card ≤ st.mass D.block ∧
  st.center = (st.mass D.block)⁻¹ • ∑ l ∈ D.block, st.weights l • D.observed l

def weightedCov (D : Reference n k d) (st : FilterState n d) : Mat d :=
  (st.mass D.block)⁻¹ • ∑ l ∈ D.block,
    st.weights l • vecMulVec (D.observed l - st.center) (D.observed l - st.center)


def referenceFeatureCov (D : Reference n k d) (st : FilterState n d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  let φ := fun l ↦ feature (st.frame *ᵥ (D.clean l - st.center))
  let c := (D.reference.card : ℝ)⁻¹ • ∑ l ∈ D.reference, φ l
  (D.reference.card : ℝ)⁻¹ • ∑ l ∈ D.reference, vecMulVec (φ l - c) (φ l - c)


def FrameNormalized (D : Reference n k d) (st : FilterState n d) : Prop :=
  (∃ q : Vec d, (∀ i, 1 ≤ q i ∧ q i < 4) ∧
    st.frame * weightedCov D st * st.frameᵀ = diagonal q) ∧
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let c := (st.mass D.block)⁻¹ • ∑ l ∈ D.block, st.weights l • φ l
  st.featureCov = (st.mass D.block)⁻¹ •
    ∑ l ∈ D.block, st.weights l • vecMulVec (φ l - c) (φ l - c)

def Pass (st : FilterState n d) (π R : ℝ) : Prop :=
  (st.featureCov ^ st.power).trace ≤ (16 * sigmaSq π R) ^ st.power

def betweenVariance (D : Reference n k d) (T : Mat d) (a : Vec d)
    (A : Mat d) : ℝ :=
  let c := fun j ↦ (A * (T * D.model.cov j * Tᵀ)).trace +
    qform A (T *ᵥ (D.model.mean j - a))
  ∑ j, D.model.weight j * (c j - ∑ i, D.model.weight i * c i) ^ 2

private theorem projected_moment (D : Reference n k d) (θ : ℝ)
    (hres : D.Resilient 4 θ) (i : Fin d) (u a : Vec d) (j : Fin k)
    (r : ℕ) (hr : r ≤ 4) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ r -
      IdCov.hmom r (u ⬝ᵥ (D.model.mean j - a)) (qform (D.model.cov j) u)| ≤
      (θ / (d + 1 : ℝ) ^ 8) *
        (1 + |u ⬝ᵥ (D.model.mean j - a)| + |qform (D.model.cov j) u|) ^ r := by
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  have h := hres (vecMulVec (Pi.single i 1) u) a j r hr
  dsimp only at h ⊢
  simp only [FilterAux.lin_projection, FilterAux.quad_projection] at h
  have he : (C (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (C (u ⬝ᵥ (D.clean l - a)) * X i) ^ r) -
      IdCov.hmom r (C (u ⬝ᵥ (D.model.mean j - a)) * X i)
        (C (qform (D.model.cov j) u) * X i ^ 2) =
      C ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ r -
        IdCov.hmom r (u ⬝ᵥ (D.model.mean j - a)) (qform (D.model.cov j) u)) *
          (X i : RPoly d) ^ r := by
    rw [FilterAux.hmom_monomial]
    simp only [mul_pow, ← map_pow, ← Finset.sum_mul, ← map_sum]
    rw [← mul_assoc, ← C_mul, ← sub_mul, ← C_sub]
  change SoS.coeffNorm1 ((C (Cj.card : ℝ)⁻¹ *
    ∑ l ∈ Cj, (C (u ⬝ᵥ (D.clean l - a)) * X i) ^ r) - _) ≤ _ at h
  rw [he] at h
  simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, X_pow_eq_monomial,
    SoS.coeffNorm1_monomial, abs_one, mul_one] using h

private theorem qform_scale (A : Mat d) (c : ℝ) (u : Vec d) :
    qform A (c • u) = c ^ 2 * qform A u := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private theorem component_moments (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π)
    (hθ : 0 ≤ θ) (hres : D.Resilient 4 θ) (i : Fin d) (u a : Vec d)
    (hu : u ≠ 0) (j : Fin k) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    let m := (u ⬝ᵥ (D.model.mean j - a)) ^ 2 + qform (D.model.cov j) u
    (1 - 9 * (θ / (d + 1 : ℝ) ^ 8)) * m ≤
        (Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2 ∧
      (Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4 ≤
        (3 + 81 * (θ / (d + 1 : ℝ) ^ 8)) * m ^ 2 := by
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  let μ := u ⬝ᵥ (D.model.mean j - a)
  let S := qform (D.model.cov j) u
  have hS : 0 < S := by
    simpa only [S, qform, star_trivial] using (hD.1.2.2.2 j).dotProduct_mulVec_pos hu
  apply FilterAux.scalar_moment_bounds _ _ μ S _ hS (by positivity)
  · intro c
    have h := projected_moment D θ hres i (c • u) a j 2 (by omega)
    dsimp only at h
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      qform_scale, FilterAux.hmom_two] at h
    have he : (Cj.card : ℝ)⁻¹ * (c ^ 2 * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2) -
        ((c * μ) ^ 2 + c ^ 2 * S) =
        c ^ 2 * ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2 -
          (μ ^ 2 + S)) := by ring
    simp only [μ, S, mul_pow] at he
    rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg c) hS.le)] at h
    exact h
  · intro c
    have h := projected_moment D θ hres i (c • u) a j 4 (by omega)
    dsimp only at h
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      qform_scale, FilterAux.hmom_four] at h
    have he : (Cj.card : ℝ)⁻¹ * (c ^ 4 * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
        ((c * μ) ^ 4 + 6 * (c * μ) ^ 2 * (c ^ 2 * S) + 3 * (c ^ 2 * S) ^ 2) =
        c ^ 4 * ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
          c ^ 4 * (μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2) := by ring
    simp only [μ, S, mul_pow] at he
    rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg c) hS.le)] at h
    dsimp only [μ, S, Cj]
    linarith only [(abs_le.mp h).2]

private theorem component_card_pos (D : Reference n k d) (π : ℝ)
    (hD : D.Valid π) (j : Fin k) :
    0 < (D.reference.filter (fun l ↦ D.label l = j)).card := by
  have hw : 0 < D.model.weight j := hD.1.1.trans_le (hD.1.2.1 j)
  rw [hD.2.2.2.2.2.2 j] at hw
  by_contra hn
  have he : (D.reference.filter (fun l ↦ D.label l = j)).card = 0 := by omega
  simp [he] at hw

private theorem centered_projection_moments (D : Reference n k d) (π θ : ℝ)
    (hD : D.Valid π) (hθ : 0 ≤ θ) (hres : D.Resilient 4 θ) (j : Fin k) (u : Vec d) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    let S := qform (D.model.cov j) u
    let δ := θ / (d + 1 : ℝ) ^ 8
    let E := fun r ↦ (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - D.model.mean j)) ^ r
    E 1 ^ 2 ≤ 4 * δ ^ 2 * S ∧ |E 2 - S| ≤ 4 * δ * S ∧
      |E 4 - 3 * S ^ 2| ≤ 16 * δ * S ^ 2 := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  let S := qform (D.model.cov j) u
  let δ := θ / (d + 1 : ℝ) ^ 8
  let E := fun r ↦ (Cj.card : ℝ)⁻¹ *
    ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - D.model.mean j)) ^ r
  have hS : 0 < S := by
    simpa only [S, qform, star_trivial] using (hD.1.2.2.2 j).dotProduct_mulVec_pos hu
  let c := (Real.sqrt S)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hS)
  have hcS : c ^ 2 * S = 1 := by
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hS.le, inv_mul_cancel₀ hS.ne']
  have hδ : 0 ≤ δ := by positivity
  have hmoment (r : ℕ) (hr : r ≤ 4) :
      |c ^ r * E r - IdCov.hmom r 0 (c ^ 2 * S)| ≤ δ * 2 ^ r := by
    have hh := projected_moment D θ hres i (c • u) (D.model.mean j) j r hr
    dsimp only at hh
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      sub_self, dotProduct_zero, qform_scale] at hh
    have he : (Cj.card : ℝ)⁻¹ *
        (c ^ r * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - D.model.mean j)) ^ r) = c ^ r * E r := by
      dsimp only [E]
      ring
    change |(Cj.card : ℝ)⁻¹ * (c ^ r * _) - _| ≤ _ at hh
    rw [he] at hh
    change |c ^ r * E r - IdCov.hmom r 0 (c ^ 2 * S)| ≤
      δ * (1 + |(0 : ℝ)| + |c ^ 2 * S|) ^ r at hh
    simpa only [hcS, abs_zero, abs_one, add_zero, one_add_one_eq_two] using hh
  have h₁ : |c * E 1| ≤ 2 * δ := by
    have hh := hmoment 1 (by omega)
    norm_num [IdCov.hmom, IdCov.hermCoeff] at hh
    rw [abs_mul]
    linarith only [hh]
  have h₂ : c ^ 2 * |E 2 - S| ≤ 4 * δ := by
    have hh := hmoment 2 (by omega)
    rw [FilterAux.hmom_two] at hh
    norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_add] at hh
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg c)] at hh
    nlinarith only [hh]
  have h₄ : c ^ 4 * |E 4 - 3 * S ^ 2| ≤ 16 * δ := by
    have hh := hmoment 4 (by omega)
    rw [FilterAux.hmom_four] at hh
    norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_add, zero_mul, add_zero] at hh
    have he : c ^ 4 * E 4 - 3 * (c ^ 2 * S) ^ 2 =
        c ^ 4 * (E 4 - 3 * S ^ 2) := by ring
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg hc.le 4)] at hh
    nlinarith only [hh]
  have hcS₄ : c ^ 4 * S ^ 2 = 1 := by
    calc
      _ = (c ^ 2 * S) ^ 2 := by ring
      _ = 1 := by rw [hcS]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have hh := (pow_le_pow_left₀ (abs_nonneg _) h₁ 2)
    rw [sq_abs, mul_pow] at hh
    calc
      E 1 ^ 2 = S * (c ^ 2 * E 1 ^ 2) := by
        nlinarith only [congrArg (fun z : ℝ ↦ z * E 1 ^ 2) hcS]
      _ ≤ S * (2 * δ) ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hh hS.le]
      _ = _ := by ring
  · calc
      |E 2 - S| = S * (c ^ 2 * |E 2 - S|) := by
        nlinarith only [congrArg (fun z : ℝ ↦ z * |E 2 - S|) hcS]
      _ ≤ S * (4 * δ) := mul_le_mul_of_nonneg_left h₂ hS.le
      _ = _ := by ring
  · calc
      |E 4 - 3 * S ^ 2| = S ^ 2 * (c ^ 4 * |E 4 - 3 * S ^ 2|) := by
        nlinarith only [congrArg (fun z : ℝ ↦ z * |E 4 - 3 * S ^ 2|) hcS₄]
      _ ≤ S ^ 2 * (16 * δ) := mul_le_mul_of_nonneg_left h₄ (sq_nonneg S)
      _ = _ := by ring

private theorem reference_cov_qform (D : Reference n k d) (u : Vec d) :
    qform D.cov u = (D.reference.card : ℝ)⁻¹ *
      ∑ l ∈ D.reference, (u ⬝ᵥ (D.clean l - D.mean)) ^ 2 := by
  simp only [Reference.cov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_comm u, pow_two]

private theorem reference_partition (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (f : Fin n → ℝ) :
    (∑ j, D.model.weight j *
      ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j), f l) =
      (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, f l := by
  classical
  have he (j : Fin k) : D.model.weight j *
      ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ =
      (D.reference.card : ℝ)⁻¹ := by
    rw [hD.2.2.2.2.2.2 j, div_eq_mul_inv]
    have hc : ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (component_card_pos D π hD j).ne'
    field_simp
  simp only [he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem resilience_delta (θ : ℝ) (hθ : 0 ≤ θ) (i : Fin d) :
    0 ≤ θ / (d + 1 : ℝ) ^ 8 ∧ θ / (d + 1 : ℝ) ^ 8 ≤ θ / 256 := by
  have hd : (2 : ℝ) ≤ d + 1 := by
    have hn : 1 ≤ d := by have hi := i.isLt; omega
    exact_mod_cast (by omega : 2 ≤ d + 1)
  have hpow : (256 : ℝ) ≤ (d + 1 : ℝ) ^ 8 := by
    exact_mod_cast (show (2 : ℝ) ^ 8 ≤ (d + 1 : ℝ) ^ 8 from
      pow_le_pow_left₀ (by norm_num) hd 8)
  exact ⟨by positivity, div_le_div_of_nonneg_left hθ (by norm_num) hpow⟩

private theorem component_second_le (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (u : Vec d) (j : Fin k) :
    D.model.weight j *
      (((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j),
          (u ⬝ᵥ (D.clean l - D.mean)) ^ 2) ≤ qform D.cov u := by
  rw [reference_cov_qform, ← reference_partition D π hD]
  rw [← mul_assoc]
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro i _
  exact mul_nonneg (mul_nonneg (hD.1.1.le.trans (hD.1.2.1 i)) (by positivity))
    (Finset.sum_nonneg fun l _ ↦ sq_nonneg _)

private theorem population_second_le (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : D.Resilient 4 θ) (u : Vec d) (j : Fin k) :
    D.model.weight j * ((u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 +
      qform (D.model.cov j) u) ≤ (1 + θ) * qform D.cov u := by
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := (u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 + qform (D.model.cov j) u
  have hδ := resilience_delta θ hθ.1 i
  have hw : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hm : 0 ≤ m := add_nonneg (sq_nonneg _) (by
    simpa only [qform, star_trivial] using
      (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
  have hprod : 1 ≤ (1 + θ) * (1 - 9 * δ) := by
    dsimp only [δ]
    nlinarith only [hδ.1, hδ.2, hθ.1,
      mul_nonneg (sub_nonneg.mpr hθ.2) hδ.1]
  have he := (component_moments D π θ hD hθ.1 hres i u D.mean hu j).1
  have he' : (1 - 9 * δ) * (D.model.weight j * m) ≤ qform D.cov u := by
    have hh := mul_le_mul_of_nonneg_left he hw
    have hb := component_second_le D π hD u j
    dsimp only [δ, m]
    nlinarith only [hh, hb]
  calc
    _ ≤ (1 + θ) * (1 - 9 * δ) * (D.model.weight j * m) :=
      le_mul_of_one_le_left (mul_nonneg hw hm) hprod
    _ = (1 + θ) * ((1 - 9 * δ) * (D.model.weight j * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he' (by linarith only [hθ.1])

private theorem population_second_sum_le (D : Reference n k d) (π θ : ℝ)
    (hD : D.Valid π) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : D.Resilient 4 θ)
    (i : Fin d) (u : Vec d) (hu : u ≠ 0) :
    (∑ j, D.model.weight j * ((u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 +
      qform (D.model.cov j) u)) ≤ (1 + θ) * qform D.cov u := by
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := fun j ↦ (u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 + qform (D.model.cov j) u
  have hδ := resilience_delta θ hθ.1 i
  have hprod : 1 ≤ (1 + θ) * (1 - 9 * δ) := by
    dsimp only [δ]
    nlinarith only [hδ.1, hδ.2, hθ.1,
      mul_nonneg (sub_nonneg.mpr hθ.2) hδ.1]
  have hm : 0 ≤ ∑ j, D.model.weight j * m j := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hD.1.1.le.trans (hD.1.2.1 j))
    exact add_nonneg (sq_nonneg _) (by
      simpa only [qform, star_trivial] using
        (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
  have he : (1 - 9 * δ) * ∑ j, D.model.weight j * m j ≤ qform D.cov u := by
    rw [reference_cov_qform, ← reference_partition D π hD]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_left
      (component_moments D π θ hD hθ.1 hres i u D.mean hu j).1
      (hD.1.1.le.trans (hD.1.2.1 j))
    dsimp only [m, δ]
    nlinarith only [hh]
  calc
    _ ≤ (1 + θ) * (1 - 9 * δ) * (∑ j, D.model.weight j * m j) :=
      le_mul_of_one_le_left hm hprod
    _ = (1 + θ) * ((1 - 9 * δ) * ∑ j, D.model.weight j * m j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by linarith only [hθ.1])

private theorem qform_conjugate (T S : Mat d) (v : Vec d) :
    qform (T * S * Tᵀ) v = qform S (Tᵀ *ᵥ v) := by
  simp only [qform, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]


/-- Resilience controls component second moments in every reference frame. -/
theorem component_bounds
    (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100)
    (hres : D.Resilient 4 θ) (T : Mat d) (hT : T.det ≠ 0) :
    ∀ j, LE (D.model.weight j • (T * D.model.cov j * Tᵀ))
      ((1 + 10 * θ) • (T * D.cov * Tᵀ)) := by
  intro j v
  by_cases hv : v = 0
  · subst v
    simp [qform]
  have hu : Tᵀ *ᵥ v ≠ 0 := by
    intro he
    apply hv
    exact Matrix.mulVec_injective_of_det_ne_zero
      (show Tᵀ.det ≠ 0 by simpa only [Matrix.det_transpose] using hT) (by simpa using he)
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
  change D.model.weight j * qform (T * D.model.cov j * Tᵀ) v ≤
    (1 + 10 * θ) * qform (T * D.cov * Tᵀ) v
  rw [qform_conjugate, qform_conjugate]
  have he := population_second_le D π θ hD hθ hres (Tᵀ *ᵥ v) j
  have hw : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hm : 0 ≤ qform D.cov (Tᵀ *ᵥ v) := by
    exact le_of_lt (by simpa only [qform, star_trivial] using
      hD.2.2.2.2.2.1.dotProduct_mulVec_pos hu)
  nlinarith only [he, mul_nonneg hw (sq_nonneg
    ((Tᵀ *ᵥ v) ⬝ᵥ (D.model.mean j - D.mean))), mul_nonneg hθ.1 hm]


/-- Reference directional fourth moments obey a dimension-free bound. -/
theorem directional_fourth
    (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000)) (u : Vec d) :
    (∑ l ∈ D.reference, (u ⬝ᵥ (D.clean l - D.mean)) ^ 4) / D.reference.card ≤
      (4 / π) * qform D.cov u ^ 2 := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let θ : ℝ := 1 / 10000
  let m := fun j ↦ (u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 + qform (D.model.cov j) u
  let M := qform D.cov u
  let E := (∑ l ∈ D.reference, (u ⬝ᵥ (D.clean l - D.mean)) ^ 4) /
    D.reference.card
  have hθ : 0 ≤ θ ∧ θ ≤ 1 / 100 := by norm_num [θ]
  have hM : 0 ≤ M := by
    simpa only [M, qform, star_trivial] using
      hD.2.2.2.2.2.1.posSemidef.dotProduct_mulVec_nonneg u
  have hw (j : Fin k) : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hm (j : Fin k) : 0 ≤ m j := add_nonneg (sq_nonneg _) (by
    simpa only [qform, star_trivial] using
      (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
  have hpop (j : Fin k) : D.model.weight j * m j ≤ (1 + θ) * M :=
    population_second_le D π θ hD hθ hres u j
  have hsum : (∑ j, D.model.weight j * m j) ≤ (1 + θ) * M :=
    population_second_sum_le D π θ hD hθ hres i u hu
  have hδ := resilience_delta θ hθ.1 i
  have hc : 3 + 81 * (θ / (d + 1 : ℝ) ^ 8) ≤ (31 / 10 : ℝ) := by
    norm_num [θ] at hδ ⊢
    linarith only [hδ.2]
  have he4 : E ≤ (31 / 10 : ℝ) * ∑ j, D.model.weight j * m j ^ 2 := by
    dsimp only [E]
    rw [div_eq_inv_mul, ← reference_partition D π hD, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hb := (component_moments D π θ hD hθ.1 hres i u D.mean hu j).2
    have hh := mul_le_mul_of_nonneg_left hb (hw j)
    have hcoef := mul_le_mul_of_nonneg_right hc (mul_nonneg (hw j) (sq_nonneg (m j)))
    dsimp only [m] at hcoef ⊢
    nlinarith only [hh, hcoef]
  have hsquare : π * (∑ j, D.model.weight j * m j ^ 2) ≤ (1 + θ) ^ 2 * M ^ 2 := by
    calc
      _ ≤ ((1 + θ) * M) * ∑ j, D.model.weight j * m j := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        have hb : π * m j ≤ (1 + θ) * M :=
          (mul_le_mul_of_nonneg_right (hD.1.2.1 j) (hm j)).trans (hpop j)
        have hh := mul_le_mul_of_nonneg_right hb (mul_nonneg (hw j) (hm j))
        nlinarith only [hh]
      _ ≤ ((1 + θ) * M) * ((1 + θ) * M) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num [θ]) hM)
      _ = _ := by ring
  have hbound : π * E ≤ 4 * M ^ 2 := by
    calc
      _ ≤ π * ((31 / 10 : ℝ) * ∑ j, D.model.weight j * m j ^ 2) :=
        mul_le_mul_of_nonneg_left he4 hD.1.1.le
      _ = (31 / 10 : ℝ) * (π * ∑ j, D.model.weight j * m j ^ 2) := by ring
      _ ≤ (31 / 10 : ℝ) * ((1 + θ) ^ 2 * M ^ 2) := by gcongr
      _ ≤ 4 * M ^ 2 := by
        have hc' : (31 / 10 : ℝ) * (1 + θ) ^ 2 ≤ 4 := by norm_num [θ]
        nlinarith only [mul_le_mul_of_nonneg_right hc' (sq_nonneg M)]
  change E ≤ (4 / π) * M ^ 2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD.1.1).2
  nlinarith only [hbound]

/-- Quadratic population variance and empirical center error are controlled. -/
theorem quadratic_resilience
    (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : D.Resilient 4 θ)
    (T A : Mat d) (a : Vec d) (hT : T.det ≠ 0) (hA : Aᵀ = A)
    (hn : frobSq A ≤ 1) (hM : LE (T * D.cov * Tᵀ) (6 • (1 : Mat d)))
    (ha : sqnorm (T *ᵥ (a - D.mean)) ≤ 1) :
    ∀ j, let μ := T *ᵥ (D.model.mean j - a)
      let S := T * D.model.cov j * Tᵀ
      2 * (A * S * A * S).trace + 4 * qform (A * S * A) μ ≤ (20 / π) ^ 2 := by
  intro j
  let S := T * D.model.cov j * Tᵀ
  let ν := T *ᵥ (D.model.mean j - D.mean)
  let δ := T *ᵥ (a - D.mean)
  let c : ℝ := (61 / 10) / π
  have hπ : 0 < π := hD.1.1
  have hπ1 : π ≤ 1 := by
    calc
      _ ≤ D.model.weight j := hD.1.2.1 j
      _ ≤ ∑ i, D.model.weight i := Finset.single_le_sum
        (fun i _ ↦ hπ.le.trans (hD.1.2.1 i)) (Finset.mem_univ j)
      _ = 1 := hD.1.2.2.1
  have hc : 0 ≤ c := by positivity
  have hθ' : 0 ≤ θ ∧ θ ≤ 1 / 100 := ⟨hθ.1, hθ.2.trans (by norm_num)⟩
  have hSn : S.PosSemidef := by
    simpa only [S, conjTranspose_eq_transpose_of_trivial] using
      (hD.1.2.2.2 j).posSemidef.mul_mul_conjTranspose_same T
  rw [show (6 • (1 : Mat d)) = (6 : ℝ) • 1 from
    (Nat.cast_smul_eq_nsmul ℝ 6 (1 : Mat d)).symm] at hM
  have hM' (v : Vec d) : qform (T * D.cov * Tᵀ) v ≤ 6 * sqnorm v := by
    simpa only [qform, sqnorm, smul_mulVec, dotProduct_smul, one_mulVec, smul_eq_mul]
      using hM v
  have hS (v : Vec d) : qform S v ≤ c * sqnorm v := by
    have hs : 0 ≤ qform S v := by
      simpa only [qform, star_trivial] using hSn.dotProduct_mulVec_nonneg v
    have hw : π * qform S v ≤ D.model.weight j * qform S v :=
      mul_le_mul_of_nonneg_right (hD.1.2.1 j) hs
    have hb := component_bounds D π θ hD hθ' hres T hT j v
    change qform (D.model.weight j • S) v ≤ _ at hb
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hb
    change D.model.weight j * qform S v ≤
      (1 + 10 * θ) * qform (T * D.cov * Tᵀ) v at hb
    have hh := mul_le_mul_of_nonneg_left (hM' v) (by linarith only [hθ.1] :
      0 ≤ 1 + 10 * θ)
    have hcoef : 6 * (1 + 10 * θ) ≤ (61 / 10 : ℝ) := by linarith only [hθ.2]
    have hu := mul_le_mul_of_nonneg_right hcoef (Rounding.DetRoundAux.sqnorm_nonneg v)
    dsimp only [c]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hπ).2
    nlinarith only [hw, hb, hh, hu]
  have hν : sqnorm ν ≤ c := by
    have he := population_second_le D π θ hD hθ' hres (Tᵀ *ᵥ ν) j
    have heq : (Tᵀ *ᵥ ν) ⬝ᵥ (D.model.mean j - D.mean) = sqnorm ν := by
      change _ = ν ⬝ᵥ (T *ᵥ (D.model.mean j - D.mean))
      rw [dotProduct_mulVec, ← mulVec_transpose]
    rw [heq] at he
    rw [show qform D.cov (Tᵀ *ᵥ ν) = qform (T * D.cov * Tᵀ) ν from
      (qform_conjugate T D.cov ν).symm] at he
    have hcov : 0 ≤ qform (D.model.cov j) (Tᵀ *ᵥ ν) := by
      simpa only [qform, star_trivial] using
        (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg _
    have hwm := mul_nonneg (hπ.le.trans (hD.1.2.1 j)) hcov
    have hb : π * sqnorm ν ^ 2 ≤ (61 / 10 : ℝ) * sqnorm ν := by
      have hw := mul_le_mul_of_nonneg_right (hD.1.2.1 j) (sq_nonneg (sqnorm ν))
      have hh := mul_le_mul_of_nonneg_left (hM' ν)
        (by linarith only [hθ.1] : 0 ≤ 1 + θ)
      have hcoef : 6 * (1 + θ) ≤ (61 / 10 : ℝ) := by linarith only [hθ.2]
      have hu := mul_le_mul_of_nonneg_right hcoef
        (Rounding.DetRoundAux.sqnorm_nonneg ν)
      nlinarith only [he, hwm, hw, hh, hu]
    by_cases hz : sqnorm ν = 0
    · rw [hz]
      exact hc
    · have hnν : 0 < sqnorm ν := lt_of_le_of_ne
        (Rounding.DetRoundAux.sqnorm_nonneg ν) (Ne.symm hz)
      dsimp only [c]
      apply (le_div_iff₀ hπ).2
      apply (mul_le_mul_iff_right₀ hnν).mp
      nlinarith only [hb]
  have hμ : T *ᵥ (D.model.mean j - a) = ν - δ := by
    dsimp only [ν, δ]
    rw [← mulVec_sub]
    congr 1
    abel
  have hb := FilterAux.quadratic_variance_le A S ν δ hA hn hSn c hc hS hν ha
  change 2 * (A * S * A * S).trace + 4 * qform (A * S * A)
    (T *ᵥ (D.model.mean j - a)) ≤ _
  rw [hμ]
  apply hb.trans
  dsimp only [c]
  have he : 8 * ((61 / 10 : ℝ) / π) ^ 2 + 12 * ((61 / 10 : ℝ) / π) =
      (8 * (61 / 10 : ℝ) ^ 2 + 12 * (61 / 10 : ℝ) * π) / π ^ 2 := by
    field_simp
  rw [he, show (20 / π) ^ 2 = (20 : ℝ) ^ 2 / π ^ 2 from div_pow _ _ _]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hπ)).2
  norm_num
  linarith only [hπ1]


private theorem retained_sum (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (w f : Fin n → ℝ) :
    (∑ l ∈ D.reference, (if l ∈ D.good then w l else 0) * f l) =
      ∑ l ∈ D.good, w l * f l := by
  classical
  calc
    _ = ∑ l ∈ D.good, (if l ∈ D.good then w l else 0) * f l :=
      (Finset.sum_subset hD.2.1 (fun l _ hl ↦ by simp [hl])).symm
    _ = _ := Finset.sum_congr rfl fun l hl ↦ by simp [hl]

private theorem reference_centered_sum (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (u : Vec d) : (∑ l ∈ D.reference, u ⬝ᵥ (D.clean l - D.mean)) = 0 := by
  have hN : (D.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hD.2.2.2.2.1).ne'
  simp only [dotProduct_sub, Finset.sum_sub_distrib, Reference.mean,
    dotProduct_smul, smul_eq_mul, ← dotProduct_sum, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

private theorem weighted_cov_qform (D : Reference n k d) (st : FilterState n d)
    (u : Vec d) :
    qform (weightedCov D st) u = (st.mass D.block)⁻¹ *
      ∑ l ∈ D.block, st.weights l * (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
  simp only [weightedCov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_comm u]
  ring

private theorem reference_pi_le_one (D : Reference n k d) (π : ℝ) (hD : D.Valid π) :
    π ≤ 1 := by
  obtain ⟨l, _⟩ := hD.2.2.2.2.1
  calc
    _ ≤ D.model.weight (D.label l) := hD.1.2.1 _
    _ ≤ ∑ j, D.model.weight j := Finset.single_le_sum
      (fun j _ ↦ hD.1.1.le.trans (hD.1.2.1 j)) (Finset.mem_univ _)
    _ = 1 := hD.1.2.2.1

private theorem reference_statistic_shift (D : Reference n k d) (st : FilterState n d)
    (π : ℝ) (hi : IterationInvariant D st π) (he : D.contamination ≤ 1 / 400)
    (x y : Fin n → ℝ) (hxy : ∀ l ∈ D.good, x l = y l) :
    let μG := (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, x l
    let μw := (st.mass D.block)⁻¹ * ∑ l ∈ D.block, st.weights l * y l
    let VG := (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2
    let Vw := (st.mass D.block)⁻¹ *
      ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2
    (μw - μG) ^ 2 ≤
      4 * ((D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)) * Vw +
      5 * ((D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good)) * VG := by
  classical
  rcases hi with ⟨hD, _, hw, _, _, _, _, _, _, hbad, _, hmass, _⟩
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  let G : Finset (Fin n ⊕ Fin n) := D.reference.map Function.Embedding.inl
  let B : Finset (Fin n ⊕ Fin n) := (D.block \ D.good).map Function.Embedding.inr
  let z := Sum.elim x y
  let w := Sum.elim r st.weights
  let μG := N⁻¹ * ∑ l ∈ D.reference, x l
  let μw := W⁻¹ * ∑ l ∈ D.block, st.weights l * y l
  let VG := N⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2
  let Vw := W⁻¹ * ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  let ω := N⁻¹ * W
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hω : 0.9 ≤ ω := by
    dsimp only [ω]
    rw [← div_eq_inv_mul, le_div_iff₀ hN]
    exact hmass
  have hβ : β ≤ ω / 16 := by
    change β ≤ 2 * D.contamination at hbad
    linarith only [hbad, he, hω]
  have hm : W = st.mass D.good + st.mass (D.block \ D.good) := by
    have hh := Finset.sum_sdiff hD.2.2.1 (f := st.weights)
    dsimp only [W, FilterState.mass]
    linarith only [hh]
  have hr : (∑ l ∈ D.reference, r l) = st.mass D.good := by
    simpa only [r, mul_one, FilterState.mass] using
      retained_sum D π hD st.weights (fun _ ↦ 1)
  have hsum (f g : Fin n → ℝ) (hfg : ∀ l ∈ D.good, f l = g l) :
      (∑ l ∈ D.reference, r l * f l) +
        (∑ l ∈ D.block \ D.good, st.weights l * g l) =
      ∑ l ∈ D.block, st.weights l * g l := by
    rw [retained_sum D π hD]
    have hgood : (∑ l ∈ D.good, st.weights l * f l) =
        ∑ l ∈ D.good, st.weights l * g l :=
      Finset.sum_congr rfl fun l hl ↦ by rw [hfg l hl]
    rw [hgood, add_comm, Finset.sum_sdiff hD.2.2.1]
  have hdis : Disjoint G B := Finset.disjoint_map_inl_map_inr _ _
  have hwhole (f : (Fin n ⊕ Fin n) → ℝ) :
      (∑ l ∈ G ∪ B, f l) =
        (∑ l ∈ D.reference, f (Sum.inl l)) +
          ∑ l ∈ D.block \ D.good, f (Sum.inr l) := by
    rw [Finset.sum_union hdis]
    simp only [G, B, Finset.sum_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply]
  have hweight : (∑ l ∈ G ∪ B, w l) = W := by
    rw [hwhole]
    change (∑ l ∈ D.reference, r l) + st.mass (D.block \ D.good) = W
    rw [hr, hm]
  apply FilterAux.weighted_mean_shift_general z w G B hdis
    (fun l ↦ by
      cases l with
      | inl l =>
        change 0 ≤ r l ∧ r l ≤ 1
        dsimp only [r]
        split_ifs
        · exact hw l
        · norm_num
      | inr l => exact hw l)
    hD.2.2.2.2.1.map μG μw VG Vw β ρ ω
  · simp only [G, Finset.card_map, Finset.sum_map, z, Sum.elim_inl,
      Function.Embedding.inl_apply]
    rfl
  · rw [hweight, hwhole]
    change μw = W⁻¹ * ((∑ l ∈ D.reference, r l * x l) +
      ∑ l ∈ D.block \ D.good, st.weights l * y l)
    rw [hsum x y hxy]
  · simp only [G, B, Finset.card_map, Finset.sum_map, w, Sum.elim_inr,
      Function.Embedding.inr_apply]
    rfl
  · simp only [G, Finset.card_map, Finset.sum_map, w, Sum.elim_inl,
      Function.Embedding.inl_apply, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, hr]
    rfl
  · dsimp only [ω, ρ, β]
    rw [hm]
    field_simp
    ring
  · exact hω
  · exact hβ
  · simp only [G, Finset.card_map, Finset.sum_map, z, Sum.elim_inl,
      Function.Embedding.inl_apply]
    rfl
  · rw [hweight, hwhole]
    change Vw = W⁻¹ * ((∑ l ∈ D.reference, r l * (x l - μw) ^ 2) +
      ∑ l ∈ D.block \ D.good, st.weights l * (y l - μw) ^ 2)
    rw [hsum _ _ (fun l hl ↦ by rw [hxy l hl])]

private theorem good_feature_form_le (D : Reference n k d) (st : FilterState n d)
    (π : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ 1 / 400) (a : (Fin d × Fin d) → ℝ) :
    let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
    let c := (st.mass D.block)⁻¹ • ∑ l ∈ D.block, st.weights l • φ l
    (∑ l ∈ D.good, st.weights l * (a ⬝ᵥ (φ l - c)) ^ 2) ≤
      D.reference.card *
        ((1 + 5 * ((D.reference.card : ℝ)⁻¹ *
          (D.reference.card - st.mass D.good))) *
            (a ⬝ᵥ (referenceFeatureCov D st *ᵥ a)) +
          4 * ((D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)) *
            (a ⬝ᵥ (st.featureCov *ᵥ a))) := by
  classical
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let φ₀ := fun l ↦ feature (st.frame *ᵥ (D.clean l - st.center))
  let x := fun l ↦ a ⬝ᵥ φ₀ l
  let y := fun l ↦ a ⬝ᵥ φ l
  let μG := N⁻¹ * ∑ l ∈ D.reference, x l
  let μw := W⁻¹ * ∑ l ∈ D.block, st.weights l * y l
  let VG := N⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2
  let Vw := W⁻¹ * ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hxy (l : Fin n) (hl : l ∈ D.good) : x l = y l := by
    dsimp only [x, y, φ₀, φ]
    rw [hi.1.2.2.2.1 l hl]
  have hshift : (μw - μG) ^ 2 ≤ 4 * β * Vw + 5 * ρ * VG :=
    reference_statistic_shift D st π hi he x y hxy
  have hVG : a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) = VG := by
    simpa only [referenceFeatureCov, one_smul, one_mul] using
      FilterAux.feature_covariance_form D.reference (fun _ ↦ 1) φ₀ N a
  have hVw : a ⬝ᵥ (st.featureCov *ᵥ a) = Vw := by
    rw [hf.2]
    exact FilterAux.feature_covariance_form D.block st.weights φ W a
  have hsum : (∑ l ∈ D.reference, (x l - μw) ^ 2) =
      N * (VG + (μw - μG) ^ 2) := by
    have hh := FilterAux.average_sq_center D.reference hi.1.2.2.2.2.1 x μw
    change VG = N⁻¹ * (∑ l ∈ D.reference, (x l - μw) ^ 2) - (μG - μw) ^ 2 at hh
    have hh' : VG + (μw - μG) ^ 2 =
        N⁻¹ * ∑ l ∈ D.reference, (x l - μw) ^ 2 := by
      nlinarith only [hh]
    rw [hh', ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hgood : (∑ l ∈ D.good, st.weights l * (y l - μw) ^ 2) ≤
      ∑ l ∈ D.reference, (x l - μw) ^ 2 := by
    calc
      _ ≤ ∑ l ∈ D.good, (x l - μw) ^ 2 := by
        apply Finset.sum_le_sum
        intro l hl
        rw [hxy l hl]
        exact mul_le_of_le_one_left (sq_nonneg _) (hi.2.2.1 l).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hi.1.2.1
        (fun l _ _ ↦ sq_nonneg _)
  have hc : ∀ l, a ⬝ᵥ (φ l - W⁻¹ • ∑ i ∈ D.block, st.weights i • φ i) =
      y l - μw := by
    intro l
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_sum, smul_eq_mul]
    rfl
  change (∑ l ∈ D.good, st.weights l *
    (a ⬝ᵥ (φ l - W⁻¹ • ∑ i ∈ D.block, st.weights i • φ i)) ^ 2) ≤ _
  simp_rw [hc]
  rw [hVG, hVw]
  change _ ≤ N * ((1 + 5 * ρ) * VG + 4 * β * Vw)
  rw [hsum] at hgood
  nlinarith only [hgood, mul_le_mul_of_nonneg_left hshift hN.le]

/-- A normalized frame has a lower covariance bound before the first type B. -/
theorem covariance_lower
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) :
    LE ((0.68 : ℝ) • (st.frame * D.cov * st.frameᵀ))
      (st.frame * weightedCov D st * st.frameᵀ) := by
  classical
  rcases hi with ⟨hD, hres, hw, _, _, _, _, _, _, hbad, hrem, hmass, _⟩
  rcases hf with ⟨_, _⟩
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hW : 0 < W := by linarith only [hmass, hN]
  have hπ : 0 < π := hD.1.1
  have hπ1 : π ≤ 1 := by
    obtain ⟨l, _⟩ := hD.2.2.2.2.1
    calc
      _ ≤ D.model.weight (D.label l) := hD.1.2.1 _
      _ ≤ ∑ j, D.model.weight j := Finset.single_le_sum
        (fun j _ ↦ hπ.le.trans (hD.1.2.1 j)) (Finset.mem_univ _)
      _ = 1 := hD.1.2.2.1
  have heπ : D.contamination ≤ π / 400 := he.trans (min_le_right _ _)
  have he1 : D.contamination ≤ 1 / 400 := by linarith only [heπ, hπ1]
  have hgood : st.mass D.good ≤ N := by
    calc
      _ ≤ (D.good.card : ℝ) := by
        simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_le_sum fun l (_ : l ∈ D.good) ↦ (hw l).2)
      _ ≤ N := by
        dsimp only [N]
        exact_mod_cast Finset.card_le_card hD.2.1
  have hbad' : st.mass (D.block \ D.good) ≤ 2 * D.contamination * N := by
    rw [← div_eq_inv_mul] at hbad
    exact (div_le_iff₀ hN).mp hbad
  have hrem' : N - st.mass D.good ≤ 4 * D.contamination * N := by
    rw [← div_eq_inv_mul] at hrem
    exact (div_le_iff₀ hN).mp hrem
  have hmass_eq : W = st.mass D.good + st.mass (D.block \ D.good) := by
    have hh := Finset.sum_sdiff hD.2.2.1 (f := st.weights)
    dsimp only [W, FilterState.mass]
    linarith only [hh]
  have hWupper : W ≤ (11 / 10 : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_right he1 hN.le
    nlinarith only [hmass_eq, hgood, hbad', hh, hN.le]
  intro v
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
  change (0.68 : ℝ) * qform (st.frame * D.cov * st.frameᵀ) v ≤
    qform (st.frame * weightedCov D st * st.frameᵀ) v
  rw [qform_conjugate, qform_conjugate]
  let u := st.frameᵀ *ᵥ v
  let g := qform D.cov u
  let x := fun l ↦ u ⬝ᵥ (D.clean l - D.mean)
  let a := u ⬝ᵥ (st.center - D.mean)
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  have hg : 0 ≤ g := by
    simpa only [g, qform, star_trivial] using
      hD.2.2.2.2.2.1.posSemidef.dotProduct_mulVec_nonneg u
  have hr (l : Fin n) (_ : l ∈ D.reference) : 0 ≤ r l ∧ r l ≤ 1 := by
    dsimp only [r]
    split_ifs
    · exact hw l
    · norm_num
  have hsecond : (∑ l ∈ D.reference, x l ^ 2) = N * g := by
    dsimp only [g]
    rw [reference_cov_qform]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hfourth : (∑ l ∈ D.reference, x l ^ 4) ≤ N * (4 / π) * g ^ 2 := by
    have hh := (div_le_iff₀ hN).mp (directional_fourth D π hD hres u)
    dsimp only [g, x]
    nlinarith only [hh]
  have hrmass : (∑ l ∈ D.reference, (1 - r l)) ≤ N * π / 100 := by
    have heq : (∑ l ∈ D.reference, r l) = st.mass D.good := by
      simpa only [r, mul_one, FilterState.mass] using retained_sum D π hD st.weights (fun _ ↦ 1)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, heq]
    change N - st.mass D.good ≤ _
    have hh := mul_le_mul_of_nonneg_right heπ hN.le
    nlinarith only [hrem', hh]
  have hret := FilterAux.retained_variance_lower D.reference r x hr N g π a hN rfl hg
    ⟨hπ, hπ1⟩ (reference_centered_sum D π hD u) hsecond hfourth hrmass
  have hsum : (∑ l ∈ D.reference, r l * (x l - a) ^ 2) ≤
      ∑ l ∈ D.block, st.weights l * (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
    rw [retained_sum D π hD]
    calc
      _ = ∑ l ∈ D.good, st.weights l *
          (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hD.2.2.2.1 l hl]
        congr 2
        dsimp only [x, a]
        rw [← dotProduct_sub]
        congr 1
        abel
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1
        (fun l _ _ ↦ mul_nonneg (hw l).1 (sq_nonneg _))
  have hcov : (3 / 4 : ℝ) * N * g ≤ W * qform (weightedCov D st) u := by
    rw [weighted_cov_qform]
    change _ ≤ W * (W⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]
    exact hret.trans hsum
  have hh := mul_le_mul_of_nonneg_right hWupper hg
  apply (mul_le_mul_iff_right₀ hW).mp
  change W * ((0.68 : ℝ) * g) ≤ W * qform (weightedCov D st) u
  nlinarith only [hcov, hh, mul_nonneg hN.le hg]

private theorem frame_covariance_bounds (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) (v : Vec d) :
    qform (st.frame * D.cov * st.frameᵀ) v ≤ 6 * sqnorm v ∧
      qform (st.frame * weightedCov D st * st.frameᵀ) v ≤ 4 * sqnorm v := by
  obtain ⟨q, hq, hframe⟩ := hf.1
  have hC : qform (st.frame * weightedCov D st * st.frameᵀ) v ≤ 4 * sqnorm v := by
    rw [hframe]
    simp only [qform, mulVec_diagonal, sqnorm, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_right (hq i).2.le (sq_nonneg (v i))]
  have hl := covariance_lower D st π R hi hf he v
  change qform ((0.68 : ℝ) • (st.frame * D.cov * st.frameᵀ)) v ≤ _ at hl
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hl
  change (0.68 : ℝ) * qform (st.frame * D.cov * st.frameᵀ) v ≤
    qform (st.frame * weightedCov D st * st.frameᵀ) v at hl
  exact ⟨by linarith only [hl, hC, Rounding.DetRoundAux.sqnorm_nonneg v], hC⟩

private theorem point_mean_shift (D : Reference n k d) (st : FilterState n d)
    (π : ℝ) (hi : IterationInvariant D st π) (he : D.contamination ≤ 1 / 400)
    (u : Vec d) :
    (u ⬝ᵥ (st.center - D.mean)) ^ 2 ≤
      4 * ((D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)) *
        qform (weightedCov D st) u +
      5 * ((D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good)) *
        qform D.cov u := by
  have hh := reference_statistic_shift D st π hi he
    (fun l ↦ u ⬝ᵥ D.clean l) (fun l ↦ u ⬝ᵥ D.observed l)
    (fun l hl ↦ by rw [hi.1.2.2.2.1 l hl])
  have hμG : (D.reference.card : ℝ)⁻¹ *
      (∑ l ∈ D.reference, u ⬝ᵥ D.clean l) = u ⬝ᵥ D.mean := by
    simp only [Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  have hμw : (st.mass D.block)⁻¹ *
      (∑ l ∈ D.block, st.weights l * (u ⬝ᵥ D.observed l)) = u ⬝ᵥ st.center := by
    rcases hi with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcenter⟩
    rw [hcenter]
    simp only [dotProduct_smul, dotProduct_sum, smul_eq_mul]
  dsimp only at hh
  rw [hμG, hμw] at hh
  simp only [← dotProduct_sub] at hh
  rw [← reference_cov_qform, ← weighted_cov_qform] at hh
  exact hh

private theorem frame_mean_shift (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) :
    sqnorm (st.frame *ᵥ (st.center - D.mean)) ≤ 180 * D.contamination := by
  classical
  let N : ℝ := D.reference.card
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  let δ := st.frame *ᵥ (st.center - D.mean)
  have hε : D.contamination ≤ 1 / 400 := by
    have hh := he.trans (min_le_right _ _)
    linarith only [hh, reference_pi_le_one D π hi.1]
  have hβ : β ≤ 2 * D.contamination := hi.2.2.2.2.2.2.2.2.2.1
  have hρ : ρ ≤ 4 * D.contamination := hi.2.2.2.2.2.2.2.2.2.2.1
  have hβ0 : 0 ≤ β := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun l _ ↦ (hi.2.2.1 l).1
  have hρ0 : 0 ≤ ρ := by
    apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    calc
      st.mass D.good ≤ (D.good.card : ℝ) := by
        simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
          Finset.sum_le_sum (fun l (_ : l ∈ D.good) ↦ (hi.2.2.1 l).2)
      _ ≤ N := by
        dsimp only [N]
        exact_mod_cast Finset.card_le_card hi.1.2.1
  have hh := point_mean_shift D st π hi hε (st.frameᵀ *ᵥ δ)
  have hdot : (st.frameᵀ *ᵥ δ) ⬝ᵥ (st.center - D.mean) = sqnorm δ := by
    change _ = δ ⬝ᵥ (st.frame *ᵥ (st.center - D.mean))
    rw [dotProduct_mulVec, ← mulVec_transpose]
  rw [hdot, ← qform_conjugate st.frame D.cov,
    ← qform_conjugate st.frame (weightedCov D st)] at hh
  have hb := frame_covariance_bounds D st π R hi hf he δ
  have hh' : sqnorm δ ^ 2 ≤ (152 * D.contamination) * sqnorm δ := by
    have h₁ := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0 ≤ 5 * ρ)
    have h₂ := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 4 * β)
    have h₃ := mul_le_mul_of_nonneg_right hβ (Rounding.DetRoundAux.sqnorm_nonneg δ)
    have h₄ := mul_le_mul_of_nonneg_right hρ (Rounding.DetRoundAux.sqnorm_nonneg δ)
    nlinarith only [hh, h₁, h₂, h₃, h₄]
  have hn := Rounding.DetRoundAux.sqnorm_nonneg δ
  have hε0 : 0 ≤ D.contamination := by
    dsimp only [Reference.contamination]
    positivity
  change sqnorm δ ≤ _
  nlinarith only [hh', hn, hε0, mul_nonneg hε0 hn]

private theorem component_statistic_bounds (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) (j : Fin k) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    let S := st.frame * D.model.cov j * st.frameᵀ
    let ν := st.frame *ᵥ (D.model.mean j - D.mean)
    let f := fun l ↦ qform A (st.frame *ᵥ (D.clean l - D.mean)) -
      ((A * S).trace + qform A ν)
    FilterAux.average Cj (f ^ 2) ≤ (121 / 10 : ℝ) * ((61 / 10 : ℝ) / π) ^ 2 ∧
      (FilterAux.average Cj f) ^ 2 ≤ ((61 / 10 : ℝ) / π) ^ 2 / 100000 := by
  classical
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  let S := st.frame * D.model.cov j * st.frameᵀ
  let ν := st.frame *ᵥ (D.model.mean j - D.mean)
  let x := fun l ↦ st.frame *ᵥ (D.clean l - D.model.mean j)
  let c : ℝ := (61 / 10) / π
  let δ : ℝ := (1 / 10000) / (d + 1 : ℝ) ^ 8
  have hπ : 0 < π := hi.1.1.1
  have hc : 0 ≤ c := by positivity
  have hδ : 0 ≤ δ := by positivity
  have hS : S.PosSemidef := by
    simpa only [S, conjTranspose_eq_transpose_of_trivial] using
      (hi.1.1.2.2.2 j).posSemidef.mul_mul_conjTranspose_same st.frame
  have hSn (u : Vec d) : 0 ≤ qform S u := by
    simpa only [qform, star_trivial] using hS.dotProduct_mulVec_nonneg u
  have hdot (u : Vec d) :
      (st.frameᵀ *ᵥ u) ⬝ᵥ (D.model.mean j - D.mean) = u ⬝ᵥ ν := by
    dsimp only [ν]
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have hpop (u : Vec d) :
      π * ((u ⬝ᵥ ν) ^ 2 + qform S u) ≤ (6.01 : ℝ) * sqnorm u := by
    have hh := population_second_le D π (1 / 10000) hi.1 (by norm_num)
      hi.2.1 (st.frameᵀ *ᵥ u) j
    rw [hdot, ← qform_conjugate st.frame D.cov,
      ← qform_conjugate st.frame (D.model.cov j)] at hh
    change D.model.weight j * ((u ⬝ᵥ ν) ^ 2 + qform S u) ≤ _ at hh
    have h₁ := mul_le_mul_of_nonneg_right (hi.1.1.2.1 j)
      (add_nonneg (sq_nonneg (u ⬝ᵥ ν)) (hSn u))
    have h₂ := mul_le_mul_of_nonneg_left
      (frame_covariance_bounds D st π R hi hf he u).1
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 10000)
    nlinarith only [hh, h₁, h₂, Rounding.DetRoundAux.sqnorm_nonneg u]
  have hupper (u : Vec d) : qform S u ≤ c * sqnorm u := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
    nlinarith only [hpop u, mul_nonneg hπ.le (sq_nonneg (u ⬝ᵥ ν)),
      Rounding.DetRoundAux.sqnorm_nonneg u]
  have hν : sqnorm ν ≤ c := by
    have hh := hpop ν
    change π * (sqnorm ν ^ 2 + qform S ν) ≤ _ at hh
    by_cases hz : sqnorm ν = 0
    · rw [hz]
      exact hc
    · have hν0 : 0 < sqnorm ν := lt_of_le_of_ne
        (Rounding.DetRoundAux.sqnorm_nonneg ν) (Ne.symm hz)
      dsimp only [c]
      apply (le_div_iff₀ hπ).2
      apply (mul_le_mul_iff_right₀ hν0).mp
      nlinarith only [hh, mul_nonneg hπ.le (hSn ν), hν0.le]
  have hd : δ * ((d : ℝ) ^ 2 + 1) ≤ 1 / 10000 := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hd1 : 1 ≤ (d + 1 : ℝ) := by linarith only [hd0]
    have hpow : (d : ℝ) ^ 2 + 1 ≤ (d + 1 : ℝ) ^ 8 := by
      have hh := pow_le_pow_right₀ hd1 (show 2 ≤ 8 by omega)
      nlinarith only [hh, hd0]
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (d + 1 : ℝ) ^ 8)]
    nlinarith only [hpow]
  have hm (u : Vec d) := centered_projection_moments D π (1 / 10000) hi.1
    (by norm_num) hi.2.1 j (st.frameᵀ *ᵥ u)
  have heq (u : Vec d) (l : Fin n) :
      (st.frameᵀ *ᵥ u) ⬝ᵥ (D.clean l - D.model.mean j) = u ⬝ᵥ x l := by
    dsimp only [x]
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have hm' (u : Vec d) :
      (FilterAux.average Cj (fun l ↦ u ⬝ᵥ x l)) ^ 2 ≤ 4 * δ ^ 2 * qform S u ∧
      |FilterAux.average Cj (fun l ↦ (u ⬝ᵥ x l) ^ 2) - qform S u| ≤
        4 * δ * qform S u ∧
      |FilterAux.average Cj (fun l ↦ (u ⬝ᵥ x l) ^ 4) - 3 * qform S u ^ 2| ≤
        16 * δ * qform S u ^ 2 := by
    have hh := hm u
    dsimp only at hh
    simp only [heq, pow_one] at hh
    rw [← qform_conjugate st.frame (D.model.cov j)] at hh
    exact hh
  have hcomp := FilterAux.component_moment_estimate Cj
    (Finset.card_pos.mp (component_card_pos D π hi.1 j)) x A S ν hA hn hS c δ hc hδ hd
    hupper hν (fun u ↦ (hm' u).1) (fun u ↦ (hm' u).2.1) (fun u ↦ (hm' u).2.2)
  have hx (l : Fin n) : x l + ν = st.frame *ᵥ (D.clean l - D.mean) := by
    dsimp only [x, ν]
    rw [← mulVec_add]
    congr 1
    abel
  simpa only [hx] using hcomp

private theorem reference_base_variance (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) :
    let x := fun l ↦ qform A (st.frame *ᵥ (D.clean l - D.mean))
    FilterAux.average D.reference (fun l ↦ (x l - FilterAux.average D.reference x) ^ 2) ≤
      (12101 / 1000 : ℝ) * ((61 / 10 : ℝ) / π) ^ 2 +
        (101 / 100 : ℝ) * betweenVariance D st.frame D.mean A := by
  classical
  let x := fun l ↦ qform A (st.frame *ᵥ (D.clean l - D.mean))
  let Cj := fun j ↦ D.reference.filter (fun l ↦ D.label l = j)
  let c := fun j ↦ (A * (st.frame * D.model.cov j * st.frameᵀ)).trace +
    qform A (st.frame *ᵥ (D.model.mean j - D.mean))
  let b := ∑ j, D.model.weight j * c j
  let B : ℝ := (12101 / 1000) * ((61 / 10 : ℝ) / π) ^ 2
  have hcomp (j : Fin k) : FilterAux.average (Cj j) (fun l ↦ (x l - b) ^ 2) ≤
      B + (101 / 100 : ℝ) * (c j - b) ^ 2 := by
    have hh := component_statistic_bounds D st π R hi hf he A hA hn j
    have hh' := FilterAux.average_change_center (Cj j)
      (Finset.card_pos.mp (component_card_pos D π hi.1 j)) x (c j) b
      ((121 / 10 : ℝ) * ((61 / 10 : ℝ) / π) ^ 2)
      (((61 / 10 : ℝ) / π) ^ 2 / 100000) hh.1 hh.2
    dsimp only [B]
    linarith only [hh']
  have hpart : FilterAux.average D.reference (fun l ↦ (x l - b) ^ 2) =
      ∑ j, D.model.weight j * FilterAux.average (Cj j) (fun l ↦ (x l - b) ^ 2) := by
    simpa only [FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using
      (reference_partition D π hi.1 (fun l ↦ (x l - b) ^ 2)).symm
  have hb : betweenVariance D st.frame D.mean A =
      ∑ j, D.model.weight j * (c j - b) ^ 2 := rfl
  have hbound : FilterAux.average D.reference (fun l ↦ (x l - b) ^ 2) ≤
      B + (101 / 100 : ℝ) * betweenVariance D st.frame D.mean A := by
    rw [hpart]
    calc
      _ ≤ ∑ j, D.model.weight j * (B + (101 / 100 : ℝ) * (c j - b) ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcomp j)
          (hi.1.1.1.le.trans (hi.1.1.2.1 j))
      _ = _ := by
        rw [hb]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [hi.1.1.2.2.1, one_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hh := FilterAux.average_sq_center D.reference hi.1.2.2.2.2.1 x b
  change FilterAux.average D.reference (fun l ↦ (x l - FilterAux.average D.reference x) ^ 2)
    ≤ _
  dsimp only [B] at hbound
  linarith only [hh, hbound, sq_nonneg (FilterAux.average D.reference x - b)]

private theorem sigmaSq_ge600 (π R : ℝ) (hπ : 0 < π) (hπ1 : π ≤ 1) :
    600 ≤ sigmaSq π R := by
  have hs : π ^ 2 ≤ 1 := by nlinarith only [hπ.le, hπ1]
  have hh : (600 : ℝ) ≤ 600 / π ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hπ)).mpr (by nlinarith only [hs])
  dsimp only [sigmaSq]
  nlinarith only [hh, sq_nonneg R]

private theorem contamination_le_small (D : Reference n k d) (π R : ℝ)
    (hD : D.Valid π)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) :
    D.contamination ≤ 1 / 64000 := by
  have hs := sigmaSq_ge600 π R hD.1.1 (reference_pi_le_one D π hD)
  apply (he.trans (min_le_left _ _)).trans
  dsimp only [maxContamination]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 64000)
  linarith only [hs]

private theorem reference_quadratic_variance (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) :
    let y := fun l ↦ qform A (st.frame *ᵥ (D.clean l - st.center))
    FilterAux.average D.reference (fun l ↦ (y l - FilterAux.average D.reference y) ^ 2) ≤
      600 / π ^ 2 + 2 * betweenVariance D st.frame D.mean A := by
  let E := FilterAux.average D.reference
  let z := fun l ↦ st.frame *ᵥ (D.clean l - D.mean)
  let δ := st.frame *ᵥ (st.center - D.mean)
  let b := A *ᵥ δ
  let x := fun l ↦ qform A (z l)
  let t := fun l ↦ b ⬝ᵥ z l
  let y := fun l ↦ qform A (st.frame *ᵥ (D.clean l - st.center))
  have hE : E 1 = 1 := FilterAux.average_one D.reference hi.1.2.2.2.2.1
  have htx (l : Fin n) : t l =
      (st.frameᵀ *ᵥ b) ⬝ᵥ (D.clean l - D.mean) := by
    dsimp only [t, z]
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have ht0 : E t = 0 := by
    change (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, t l = 0
    simp_rw [htx]
    rw [reference_centered_sum D π hi.1, mul_zero]
  have hy : y = x - (2 : ℝ) • t + qform A δ • (1 : Fin n → ℝ) := by
    ext l
    have hz : st.frame *ᵥ (D.clean l - st.center) = z l + -δ := by
      dsimp only [z, δ]
      rw [← mulVec_neg, ← mulVec_add]
      congr 1
      abel
    change qform A (st.frame *ᵥ (D.clean l - st.center)) =
      x l - 2 * t l + qform A δ * 1
    rw [hz, FilterAux.qform_add_symmetric A hA]
    simp only [mulVec_neg, neg_dotProduct, qform, dotProduct_neg, neg_neg]
    dsimp only [x, t, b, qform]
    ring
  have hmy : E y = E x + qform A δ := by
    rw [hy, E.map_add, E.map_sub, E.map_smul, E.map_smul, ht0, hE]
    simp only [smul_eq_mul, mul_zero, mul_one, sub_zero]
  have hvar : E (fun l ↦ (y l - E y) ^ 2) ≤
      (9 / 8 : ℝ) * E (fun l ↦ (x l - E x) ^ 2) + 36 * E (t ^ 2) := by
    calc
      _ ≤ E ((9 / 8 : ℝ) • (fun l ↦ (x l - E x) ^ 2) + (36 : ℝ) • t ^ 2) := by
        apply FilterAux.average_mono
        intro l _
        rw [hmy, hy]
        change (x l - 2 * t l + qform A δ * 1 - (E x + qform A δ)) ^ 2 ≤
          (9 / 8 : ℝ) * (x l - E x) ^ 2 + 36 * t l ^ 2
        nlinarith only [sq_nonneg (x l - E x + 16 * t l)]
      _ = _ := by rw [E.map_add, E.map_smul, E.map_smul]; rfl
  have ht2 : E (t ^ 2) = qform (st.frame * D.cov * st.frameᵀ) b := by
    rw [qform_conjugate, reference_cov_qform]
    change (D.reference.card : ℝ)⁻¹ * (∑ l ∈ D.reference, t l ^ 2) = _
    simp_rw [htx]
  have ht2le : E (t ^ 2) ≤ 6 * sqnorm δ := by
    rw [ht2]
    have hh := (FilterAux.sqnorm_mulVec_le A δ).trans
      (mul_le_of_le_one_left (Rounding.DetRoundAux.sqnorm_nonneg δ) hn)
    have hh' := (frame_covariance_bounds D st π R hi hf he b).1
    change qform (st.frame * D.cov * st.frameᵀ) b ≤ _
    linarith only [hh, hh']
  have hδ : sqnorm δ ≤ 180 / 64000 :=
    (frame_mean_shift D st π R hi hf he).trans (by
      have hh := contamination_le_small D π R hi.1 he
      linarith only [hh])
  have hbase := reference_base_variance D st π R hi hf he A hA hn
  have hbet : 0 ≤ betweenVariance D st.frame D.mean A := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hi.1.1.1.le.trans (hi.1.1.2.1 j)) (sq_nonneg _)
  have hπ : 0 < π := hi.1.1.1
  have hπ2 : π ^ 2 ≤ 1 := by
    nlinarith only [hπ.le, reference_pi_le_one D π hi.1]
  have hnum : (9 / 8 : ℝ) * (12101 / 1000) * ((61 / 10 : ℝ) / π) ^ 2 + 1 ≤
      600 / π ^ 2 := by
    have hh : (9 / 8 : ℝ) * (12101 / 1000) * ((61 / 10 : ℝ) / π) ^ 2 + 1 =
        ((9 / 8 : ℝ) * (12101 / 1000) * (61 / 10) ^ 2 + π ^ 2) / π ^ 2 := by
      field_simp
    rw [hh]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hπ)).2
    norm_num
    linarith only [hπ2]
  change E (fun l ↦ (y l - E y) ^ 2) ≤ _
  change E (fun l ↦ (x l - E x) ^ 2) ≤ _ at hbase
  nlinarith only [hvar, ht2le, hδ, hbase, hnum, hbet]

private theorem reference_feature_bound
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (M : ℝ) (hbet : ∀ A, Aᵀ = A → frobSq A ≤ 1 →
      betweenVariance D st.frame D.mean A ≤ M) :
    ∀ a : (Fin d × Fin d) → ℝ,
      a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤ (600 / π ^ 2 + 2 * M) * (a ⬝ᵥ a) := by
  classical
  intro a
  by_cases ha : a = 0
  · simp [ha]
  have hn0 : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hn : 0 < a ⬝ᵥ a := lt_of_le_of_ne hn0 (by
    intro hz
    exact ha (dotProduct_self_eq_zero.mp hz.symm))
  let r := Real.sqrt (a ⬝ᵥ a)
  let b := r⁻¹ • a
  let A : Mat d := fun i j ↦ b (i, j)
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have hrs : r ^ 2 = a ⬝ᵥ a := Real.sq_sqrt hn0
  have hb : b ⬝ᵥ b = 1 := by
    dsimp only [b]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    calc
      r⁻¹ * (r⁻¹ * (a ⬝ᵥ a)) = (r ^ 2)⁻¹ * (a ⬝ᵥ a) := by rw [← inv_pow]; ring
      _ = 1 := by rw [hrs, inv_mul_cancel₀ hn.ne']
  have hA : frobSq A ≤ 1 := by
    have heq : frobSq A = b ⬝ᵥ b := by
      simp only [A, frobSq, dotProduct, Fintype.sum_prod_type, pow_two]
    rw [heq, hb]
  let B := FilterAux.symmetricPart A
  have hB : Bᵀ = B := FilterAux.symmetricPart_symmetric A
  have hnB : frobSq B ≤ 1 := (FilterAux.symmetricPart_frob_le A).trans hA
  have hdot (z : Vec d) : qform B z = b ⬝ᵥ feature z := by
    rw [FilterAux.qform_symmetricPart]
    simp only [qform, dotProduct, mulVec, Finset.mul_sum,
      feature, Fintype.sum_prod_type, A]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hv := reference_quadratic_variance D st π R hi hf he B hB hnB
  dsimp only at hv
  simp_rw [hdot] at hv
  have hcov := FilterAux.feature_covariance_form D.reference (fun _ ↦ 1)
    (fun l ↦ feature (st.frame *ᵥ (D.clean l - st.center))) D.reference.card b
  simp only [one_smul, one_mul] at hcov
  change b ⬝ᵥ (referenceFeatureCov D st *ᵥ b) = _ at hcov
  have hbound : b ⬝ᵥ (referenceFeatureCov D st *ᵥ b) ≤ (600 / π ^ 2 + 2 * M) := by
    rw [hcov]
    have hh := hbet B hB hnB
    change FilterAux.average D.reference (fun l ↦
      (b ⬝ᵥ feature (st.frame *ᵥ (D.clean l - st.center)) -
        FilterAux.average D.reference (fun i ↦
          b ⬝ᵥ feature (st.frame *ᵥ (D.clean i - st.center)))) ^ 2) ≤ _
    linarith only [hv, hh]
  have hab : a = r • b := by
    simp only [b, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  calc
    a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) =
        r ^ 2 * (b ⬝ᵥ (referenceFeatureCov D st *ᵥ b)) := by
      conv_lhs => rw [hab]
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    _ ≤ r ^ 2 * (600 / π ^ 2 + 2 * M) := mul_le_mul_of_nonneg_left hbound (sq_nonneg r)
    _ = _ := by rw [hrs, mul_comm]

/-- A non-far reference bounds its centered quadratic-feature covariance. -/
theorem feature_variance
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hbet : ∀ A, Aᵀ = A → frobSq A ≤ 1 →
      betweenVariance D st.frame D.mean A ≤ R ^ 2) :
    ∀ a : (Fin d × Fin d) → ℝ,
      a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤ sigmaSq π R * (a ⬝ᵥ a) := by
  exact reference_feature_bound D st π R hi hf he (R ^ 2) hbet

private theorem typeA_of_column_bound
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hvar : ∀ j : Fin d × Fin d,
      let a := fun i ↦ (st.featureCov ^ (st.power / 2)) i j
      a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤
        (3 * sigmaSq π R) * (a ⬝ᵥ a))
    (hfail : ¬ Pass st π R) : TypeA D st := by
  classical
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let σ := sigmaSq π R
  let H := st.featureCov ^ (st.power / 2)
  let a := fun j i ↦ H i j
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let c := W⁻¹ • ∑ i ∈ D.block, st.weights i • φ i
  let t := (st.featureCov ^ st.power).trace
  let u := (st.featureCov ^ (st.power + 1)).trace
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hmass : 0.9 * N ≤ W := hi.2.2.2.2.2.2.2.2.2.2.2.1
  have hW : 0 < W := by linarith only [hmass, hN]
  have hσ : 0 < σ := by
    dsimp only [σ, sigmaSq]
    exact add_pos_of_pos_of_nonneg (div_pos (by norm_num) (sq_pos_of_pos hi.1.1.1))
      (mul_nonneg (by norm_num) (sq_nonneg R))
  have he1 : D.contamination ≤ 1 / 400 := by
    have hh := he.trans (min_le_right _ _)
    have hπ1 := reference_pi_le_one D π hi.1
    linarith only [hh, hπ1]
  have hβ : β ≤ 1 / 200 := by
    have hh : β ≤ 2 * D.contamination := hi.2.2.2.2.2.2.2.2.2.1
    linarith only [hh, he1]
  have hρ : ρ ≤ 1 / 100 := by
    have hh : ρ ≤ 4 * D.contamination := hi.2.2.2.2.2.2.2.2.2.2.1
    linarith only [hh, he1]
  have hH : Hᵀ = H := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (hi.2.2.2.2.2.1.pow (st.power / 2)).1.eq
  have hHH : H * H = st.featureCov ^ st.power := by
    dsimp only [H]
    rw [← pow_add]
    congr 1
    obtain ⟨m, hm⟩ := hi.2.2.2.2.2.2.1
    omega
  have hnorm : (∑ j, a j ⬝ᵥ a j) = t := by
    rw [FilterAux.column_norm_sum, hH, hHH]
  have hform : (∑ j, a j ⬝ᵥ (st.featureCov *ᵥ a j)) = u := by
    rw [FilterAux.column_form_sum, hH, Matrix.trace_mul_cycle, hHH, ← pow_succ]
  have hscore (l : Fin n) : st.score D l = ∑ j, (a j ⬝ᵥ (φ l - c)) ^ 2 := by
    change (φ l - c) ⬝ᵥ ((st.featureCov ^ st.power) *ᵥ (φ l - c)) = _
    rw [← hHH]
    exact FilterAux.column_square_sum H hH _
  have hvariance (j : Fin d × Fin d) :
      (∑ l ∈ D.block, st.weights l * (a j ⬝ᵥ (φ l - c)) ^ 2) =
        W * (a j ⬝ᵥ (st.featureCov *ᵥ a j)) := by
    rw [hf.2]
    have hh := FilterAux.covariance_sum_form D.block st.weights (fun l ↦ φ l - c)
      W (a j)
    change _ = W * (_ ⬝ᵥ (_ *ᵥ _))
    rw [hh, ← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]
  have htotal : (∑ l ∈ D.block, st.weights l * st.score D l) = W * u := by
    simp_rw [hscore, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hvariance]
    rw [← Finset.mul_sum, hform]
  have hgood : (∑ l ∈ D.good, st.weights l * st.score D l) ≤
      N * ((1 + 5 * ρ) * (3 * σ) * t + 4 * β * u) := by
    simp_rw [hscore, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j, N * ((1 + 5 * ρ) *
          (a j ⬝ᵥ (referenceFeatureCov D st *ᵥ a j)) +
          4 * β * (a j ⬝ᵥ (st.featureCov *ᵥ a j))) :=
        Finset.sum_le_sum fun j _ ↦ good_feature_form_le D st π hi hf he1 (a j)
      _ = N * ((1 + 5 * ρ) *
          (∑ j, a j ⬝ᵥ (referenceFeatureCov D st *ᵥ a j)) + 4 * β * u) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hform]
      _ ≤ _ := by
        have hv : (∑ j, a j ⬝ᵥ (referenceFeatureCov D st *ᵥ a j)) ≤ (3 * σ) * t := by
          rw [← hnorm, Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ ↦ hvar j
        have hρ0 : 0 ≤ ρ := by
          dsimp only [ρ]
          apply mul_nonneg (by positivity)
          apply sub_nonneg.mpr
          calc
            st.mass D.good ≤ (D.good.card : ℝ) := by
              simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
                Finset.sum_le_sum (fun l (_ : l ∈ D.good) ↦ (hi.2.2.1 l).2)
            _ ≤ N := by
              dsimp only [N]
              exact_mod_cast Finset.card_le_card hi.1.2.1
        have hh := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 1 + 5 * ρ)
        have hh' := mul_le_mul_of_nonneg_left hh hN.le
        nlinarith only [hh']
  have hu : 0 ≤ u := (hi.2.2.2.2.2.1.pow _).trace_nonneg
  have hlarge : 8 * σ * t < u := by
    apply FilterAux.failed_trace_large st.featureCov hi.2.2.2.2.2.1 st.power
      hi.2.2.2.2.2.2.2.1 σ hσ
    · simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
        hi.2.2.2.2.2.2.2.2.1
    · exact lt_of_not_ge hfail
  have hcoeff : (1 + 5 * ρ) * (3 * σ) * t + 4 * β * u ≤ (21 / 50 : ℝ) * u := by
    have ht : 0 ≤ σ * t := mul_nonneg hσ.le (hi.2.2.2.2.2.1.pow _).trace_nonneg
    nlinarith only [hlarge, hu, mul_nonneg (sub_nonneg.mpr hρ) ht,
      mul_nonneg (sub_nonneg.mpr hβ) hu]
  have hgood' : 2 * (∑ l ∈ D.good, st.weights l * st.score D l) ≤ W * u := by
    have hh := mul_le_mul_of_nonneg_left hcoeff hN.le
    have hh' := mul_le_mul_of_nonneg_right hmass hu
    nlinarith only [hgood, hh, hh', mul_nonneg hN.le hu]
  have hsplit := Finset.sum_sdiff hi.1.2.2.1
    (f := fun l ↦ st.weights l * st.score D l)
  change (∑ l ∈ D.good, st.weights l * st.score D l) ≤ _
  linarith only [hsplit, htotal, hgood']

/-- A non-far reference forces each failed iteration to remove mostly bad mass. -/
theorem nonfar_typeA
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hbet : ∀ A, Aᵀ = A → frobSq A ≤ 1 →
      betweenVariance D st.frame D.mean A ≤ R ^ 2)
    (hfail : ¬ Pass st π R) : TypeA D st := by
  apply typeA_of_column_bound D st π R hi hf he ?_ hfail
  intro j
  let a := fun i ↦ (st.featureCov ^ (st.power / 2)) i j
  have hh := feature_variance D st π R hi hf he hbet a
  have hσ : 0 ≤ sigmaSq π R := (by norm_num : (0 : ℝ) ≤ 600).trans
    (sigmaSq_ge600 π R hi.1.1.1 (reference_pi_le_one D π hi.1))
  have hn : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  nlinarith only [hh, mul_nonneg hσ hn]

private theorem matrix_feature_form_bound (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) :
    let a := fun ij : Fin d × Fin d ↦ A ij.1 ij.2
    a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤
      600 / π ^ 2 + 2 * betweenVariance D st.frame D.mean A := by
  let a := fun ij : Fin d × Fin d ↦ A ij.1 ij.2
  have hdot (z : Vec d) : qform A z = a ⬝ᵥ feature z := by
    simp only [qform, dotProduct, mulVec, Finset.mul_sum,
      feature, Fintype.sum_prod_type, a]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hh := reference_quadratic_variance D st π R hi hf he A hA hn
  dsimp only at hh
  simp_rw [hdot] at hh
  have hc := FilterAux.feature_covariance_form D.reference (fun _ ↦ 1)
    (fun l ↦ feature (st.frame *ᵥ (D.clean l - st.center))) D.reference.card a
  simp only [one_smul, one_mul] at hc
  change a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) = _ at hc
  change a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤ _
  rw [hc]
  exact hh

private theorem power_column_symmetric (D : Reference n k d) (st : FilterState n d)
    (π : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (j : Fin d × Fin d) :
    (fun i l ↦ (st.featureCov ^ (st.power / 2)) (i, l) j : Mat d)ᵀ =
      (fun i l ↦ (st.featureCov ^ (st.power / 2)) (i, l) j : Mat d) := by
  classical
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let c := (st.mass D.block)⁻¹ • ∑ l ∈ D.block, st.weights l • φ l
  have hφ (l : Fin n) (i k : Fin d) : φ l (i, k) = φ l (k, i) := mul_comm _ _
  have hc (i k : Fin d) : c (i, k) = c (k, i) := by
    dsimp only [c]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hφ]
  have hrow (i k : Fin d) (a : Fin d × Fin d) :
      st.featureCov (i, k) a = st.featureCov (k, i) a := by
    rw [hf.2]
    simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
      Pi.sub_apply, smul_eq_mul]
    change (st.mass D.block)⁻¹ *
      (∑ l ∈ D.block, st.weights l * ((φ l (i, k) - c (i, k)) * (φ l a - c a))) =
      (st.mass D.block)⁻¹ *
      (∑ l ∈ D.block, st.weights l * ((φ l (k, i) - c (k, i)) * (φ l a - c a)))
    simp_rw [hφ _ i k, hc i k]
  have hp : st.power / 2 ≠ 0 := by
    have hh := hi.2.2.2.2.2.2.2.1
    omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp
  funext i k
  change (st.featureCov ^ (st.power / 2)) (k, i) j =
    (st.featureCov ^ (st.power / 2)) (i, k) j
  rw [hq, pow_succ', Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hrow k i a]

/-- The first type-B failure supplies a large-spread recorded column. -/
theorem typeB_candidate
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hfail : ¬ Pass st π R) (hb : ¬ TypeA D st) :
    ∃ j : Fin d × Fin d,
      let a := fun i ↦ (st.featureCov ^ (st.power / 2)) i j
      (∑ i, a i ^ 2) ≠ 0 ∧
      sigmaSq π R ≤ betweenVariance D st.frame D.mean
        (fun i l ↦ a (i, l) / Real.sqrt (∑ i, a i ^ 2)) := by
  classical
  by_contra! hnone
  apply hb
  apply typeA_of_column_bound D st π R hi hf he ?_ hfail
  intro j
  let v := fun i ↦ (st.featureCov ^ (st.power / 2)) i j
  let N := ∑ i, v i ^ 2
  have hnorm : N = v ⬝ᵥ v := by simp only [N, dotProduct, pow_two]
  by_cases hN : N = 0
  · have hv : v = 0 := dotProduct_self_eq_zero.mp (hnorm ▸ hN)
    change v ⬝ᵥ (referenceFeatureCov D st *ᵥ v) ≤ (3 * sigmaSq π R) * (v ⬝ᵥ v)
    simp [hv]
  have hN0 : 0 < N := lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (Ne.symm hN)
  let r := Real.sqrt N
  let b := r⁻¹ • v
  let A : Mat d := fun i l ↦ b (i, l)
  have hr : 0 < r := Real.sqrt_pos.mpr hN0
  have hrs : r ^ 2 = N := Real.sq_sqrt hN0.le
  have hbentry (i : Fin d × Fin d) : b i = v i / r := by
    simp only [b, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbn : b ⬝ᵥ b = 1 := by
    simp only [b, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hnorm]
    calc
      r⁻¹ * (r⁻¹ * N) = (r ^ 2)⁻¹ * N := by rw [← inv_pow]; ring
      _ = 1 := by rw [hrs, inv_mul_cancel₀ hN]
  have hA : Aᵀ = A := by
    have hh := power_column_symmetric D st π hi hf j
    ext i l
    change b (l, i) = b (i, l)
    rw [hbentry, hbentry]
    congr 1
    exact congrFun (congrFun hh i) l
  have hnA : frobSq A ≤ 1 := by
    have hh : frobSq A = b ⬝ᵥ b := by
      simp only [A, frobSq, dotProduct, Fintype.sum_prod_type, pow_two]
    rw [hh, hbn]
  have hbet : betweenVariance D st.frame D.mean A < sigmaSq π R := by
    apply lt_of_not_ge
    intro hh
    apply hnone j
    change N ≠ 0 ∧ sigmaSq π R ≤
      betweenVariance D st.frame D.mean (fun i l ↦ v (i, l) / r)
    exact ⟨hN, by simpa only [A, hbentry] using hh⟩
  have hh := matrix_feature_form_bound D st π R hi hf he A hA hnA
  have hσ : 600 / π ^ 2 ≤ sigmaSq π R := by
    dsimp only [sigmaSq]
    nlinarith only [sq_nonneg R]
  have hform : b ⬝ᵥ (referenceFeatureCov D st *ᵥ b) ≤ 3 * sigmaSq π R := by
    change b ⬝ᵥ (referenceFeatureCov D st *ᵥ b) ≤ _ at hh
    linarith only [hh, hbet, hσ]
  have hvb : v = r • b := by
    simp only [b, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  change v ⬝ᵥ (referenceFeatureCov D st *ᵥ v) ≤ (3 * sigmaSq π R) * (v ⬝ᵥ v)
  calc
    _ = r ^ 2 * (b ⬝ᵥ (referenceFeatureCov D st *ᵥ b)) := by
      conv_lhs => rw [hvb]
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    _ ≤ r ^ 2 * (3 * sigmaSq π R) := mul_le_mul_of_nonneg_left hform (sq_nonneg r)
    _ = _ := by rw [hrs, hnorm]; ring

private theorem component_sum (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (j : Fin k) (f : Fin n → ℝ) :
    (∑ l ∈ D.reference.filter (fun l ↦ D.label l = j), f l) =
      D.reference.card * D.model.weight j *
        FilterAux.average (D.reference.filter (fun l ↦ D.label l = j)) f := by
  have hN : (D.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hD.2.2.2.2.1).ne'
  have hC : ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (component_card_pos D π hD j).ne'
  rw [hD.2.2.2.2.2.2 j]
  simp only [FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk]
  field_simp

private theorem block_mass_upper (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) :
    st.mass D.block ≤ (101 / 100 : ℝ) * D.reference.card := by
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hbad := hi.2.2.2.2.2.2.2.2.2.1
  rw [← div_eq_inv_mul, div_le_iff₀ hN] at hbad
  have hgood : st.mass D.good ≤ (D.reference.card : ℝ) := by
    calc
      _ ≤ (D.good.card : ℝ) := by
        simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
          Finset.sum_le_sum (fun l (_ : l ∈ D.good) ↦ (hi.2.2.1 l).2)
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hi.1.2.1
  have hsplit := Finset.sum_sdiff hi.1.2.2.1 (f := st.weights)
  change st.mass (D.block \ D.good) + st.mass D.good = st.mass D.block at hsplit
  have hh := mul_le_mul_of_nonneg_right (contamination_le_small D π R hi.1 he) hN.le
  nlinarith only [hsplit, hgood, hbad, hh, hN.le]

private theorem retained_component_mass (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) (j : Fin k) :
    D.reference.card * D.model.weight j / 2 ≤
      ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j),
        if l ∈ D.good then st.weights l else 0 := by
  classical
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hrem := hi.2.2.2.2.2.2.2.2.2.2.1
  rw [← div_eq_inv_mul, div_le_iff₀ hN] at hrem
  have hr : (∑ l ∈ D.reference, r l) = st.mass D.good := by
    simpa only [r, mul_one, FilterState.mass] using
      retained_sum D π hi.1 st.weights (fun _ ↦ 1)
  have hcard : (Cj.card : ℝ) = D.reference.card * D.model.weight j := by
    dsimp only [Cj]
    rw [hi.1.2.2.2.2.2.2 j]
    field_simp
  have hdrop : (∑ l ∈ Cj, (1 - r l)) ≤ ∑ l ∈ D.reference, (1 - r l) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro l _ _
    dsimp only [r]
    split_ifs
    · exact sub_nonneg.mpr (hi.2.2.1 l).2
    · norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    hr, hcard] at hdrop
  have hε := he.trans (min_le_right _ _)
  have hw := hi.1.1.2.1 j
  have hsmall : 4 * D.contamination ≤ D.model.weight j / 2 := by
    linarith only [hε, hw, hi.1.1.1]
  have hh := mul_le_mul_of_nonneg_right hsmall hN.le
  change _ ≤ ∑ l ∈ Cj, r l
  nlinarith only [hdrop, hrem, hh]

private theorem pass_feature_bound (st : FilterState n d) (π R : ℝ)
    (hA : st.featureCov.PosSemidef) (hp : 2 ≤ st.power) (hπ : 0 < π)
    (hπ1 : π ≤ 1) (hpass : Pass st π R) (a : (Fin d × Fin d) → ℝ) :
    a ⬝ᵥ (st.featureCov *ᵥ a) ≤ (16 * sigmaSq π R) * (a ⬝ᵥ a) := by
  apply FilterAux.qform_upper_of_trace_power st.featureCov hA st.power (by omega)
    (16 * sigmaSq π R) ?_ hpass a
  have hh := sigmaSq_ge600 π R hπ hπ1
  linarith only [hh]

private theorem current_component_within (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) :
    let δ := st.frame *ᵥ (st.center - D.mean)
    let c := fun j ↦ (A * (st.frame * D.model.cov j * st.frameᵀ)).trace +
      qform A (st.frame *ᵥ (D.model.mean j - D.mean))
    (∑ j, ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j),
      (qform A (st.frame *ᵥ (D.clean l - st.center)) - qform A δ - c j) ^ 2) ≤
      D.reference.card * sigmaSq π R := by
  let N : ℝ := D.reference.card
  let δ := st.frame *ᵥ (st.center - D.mean)
  let z := fun l ↦ st.frame *ᵥ (D.clean l - D.mean)
  let b := A *ᵥ δ
  let t := fun l ↦ b ⬝ᵥ z l
  let Cj := fun j ↦ D.reference.filter (fun l ↦ D.label l = j)
  let c := fun j ↦ (A * (st.frame * D.model.cov j * st.frameᵀ)).trace +
    qform A (st.frame *ᵥ (D.model.mean j - D.mean))
  let f := fun j l ↦ qform A (z l) - c j
  let g := fun j l ↦ qform A (st.frame *ᵥ (D.clean l - st.center)) - qform A δ - c j
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hmean : (∑ j, ∑ l ∈ Cj j, f j l ^ 2) ≤
      N * ((121 / 10 : ℝ) * ((61 / 10 : ℝ) / π) ^ 2) := by
    calc
      _ = N * ∑ j, D.model.weight j * FilterAux.average (Cj j) (fun l ↦ f j l ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [N, Cj, mul_assoc] using component_sum D π hi.1 j (fun l ↦ f j l ^ 2)
      _ ≤ N * ∑ j, D.model.weight j *
          ((121 / 10 : ℝ) * ((61 / 10 : ℝ) / π) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hN.le
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (component_statistic_bounds D st π R hi hf he A hA hn j).1
          (hi.1.1.1.le.trans (hi.1.1.2.1 j))
      _ = _ := by rw [← Finset.sum_mul, hi.1.1.2.2.1, one_mul]
  have ht : (∑ l ∈ D.reference, t l ^ 2) =
      N * qform (st.frame * D.cov * st.frameᵀ) b := by
    rw [qform_conjugate, reference_cov_qform]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    dsimp only [t, z]
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have hsmall : 36 * (∑ l ∈ D.reference, t l ^ 2) ≤ N := by
    have hb := (FilterAux.sqnorm_mulVec_le A δ).trans
      (mul_le_of_le_one_left (Rounding.DetRoundAux.sqnorm_nonneg δ) hn)
    have hq := (frame_covariance_bounds D st π R hi hf he b).1
    have hδ := (frame_mean_shift D st π R hi hf he).trans (show
        180 * D.contamination ≤ 180 / 64000 by
      linarith only [contamination_le_small D π R hi.1 he])
    have hh : qform (st.frame * D.cov * st.frameᵀ) b ≤ (1080 / 64000 : ℝ) := by
      linarith only [hb, hq, hδ]
    rw [ht]
    nlinarith only [mul_le_mul_of_nonneg_left hh hN.le, hN.le]
  have hpoint (j : Fin k) (l : Fin n) :
      g j l ^ 2 ≤ (9 / 8 : ℝ) * f j l ^ 2 + 36 * t l ^ 2 := by
    have hz : st.frame *ᵥ (D.clean l - st.center) = z l - δ := by
      dsimp only [z, δ]
      rw [← mulVec_sub]
      congr 1
      abel
    dsimp only [g, f, t]
    rw [hz, FilterAux.qform_sub_symmetric A hA]
    change (qform A (z l) - 2 * (b ⬝ᵥ z l) + qform A δ - qform A δ - c j) ^ 2 ≤ _
    nlinarith only [sq_nonneg (qform A (z l) - c j + 16 * (b ⬝ᵥ z l))]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun l (_ : l ∈ Cj j) ↦ hpoint j l))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [FilterAux.sum_filter_partition] at hh
  have hπ : 0 < π := hi.1.1.1
  have hπ2 : π ^ 2 ≤ 1 := by
    nlinarith only [hπ.le, reference_pi_le_one D π hi.1]
  have hc : (9 / 8 : ℝ) * (121 / 10) * ((61 / 10 : ℝ) / π) ^ 2 + 1 ≤
      sigmaSq π R := by
    have heq : (9 / 8 : ℝ) * (121 / 10) * ((61 / 10 : ℝ) / π) ^ 2 + 1 =
        ((9 / 8 : ℝ) * (121 / 10) * (61 / 10) ^ 2 + π ^ 2) / π ^ 2 := by
      field_simp
    rw [heq]
    have hnum : (9 / 8 : ℝ) * (121 / 10) * (61 / 10) ^ 2 + π ^ 2 ≤ 600 := by
      norm_num
      linarith only [hπ2]
    apply ((div_le_div_iff_of_pos_right (sq_pos_of_pos hπ)).2 hnum).trans
    dsimp only [sigmaSq]
    nlinarith only [sq_nonneg R]
  have hc' := mul_le_mul_of_nonneg_left hc hN.le
  change (∑ j, ∑ l ∈ Cj j, g j l ^ 2) ≤ _
  nlinarith only [hh, hmean, hsmall, hc']

/-- A clean pass controls every between-component quadratic variance. -/
theorem pass_spread
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hp : Pass st π R) (A : Mat d) (hA : Aᵀ = A) (hnorm : frobSq A ≤ 1) :
    betweenVariance D st.frame D.mean A ≤ 80 * sigmaSq π R := by
  classical
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let σ := sigmaSq π R
  let δ := st.frame *ᵥ (st.center - D.mean)
  let a := fun ij : Fin d × Fin d ↦ A ij.1 ij.2
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let v := W⁻¹ • ∑ l ∈ D.block, st.weights l • φ l
  let x := fun l ↦ qform A (st.frame *ᵥ (D.clean l - st.center)) - qform A δ
  let c := fun j ↦ (A * (st.frame * D.model.cov j * st.frameᵀ)).trace +
    qform A (st.frame *ᵥ (D.model.mean j - D.mean))
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  let μ := a ⬝ᵥ v - qform A δ
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hmass : 0.9 * N ≤ W := hi.2.2.2.2.2.2.2.2.2.2.2.1
  have hW : 0 < W := by linarith only [hmass, hN]
  have hσ : 0 ≤ σ := (by norm_num : (0 : ℝ) ≤ 600).trans
    (sigmaSq_ge600 π R hi.1.1.1 (reference_pi_le_one D π hi.1))
  have hdot (z : Vec d) : qform A z = a ⬝ᵥ feature z := by
    simp only [qform, dotProduct, mulVec, Finset.mul_sum, feature, a,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnorma : a ⬝ᵥ a ≤ 1 := by
    simpa only [a, frobSq, dotProduct, Fintype.sum_prod_type, pow_two] using hnorm
  have hApass : a ⬝ᵥ (st.featureCov *ᵥ a) ≤ 16 * σ := by
    have hh := pass_feature_bound st π R hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.2.1
      hi.1.1.1 (reference_pi_le_one D π hi.1) hp a
    have hh' := mul_le_mul_of_nonneg_left hnorma (by positivity : 0 ≤ 16 * σ)
    nlinarith only [hh, hh']
  have hfull : (∑ l ∈ D.block, st.weights l * (a ⬝ᵥ (φ l - v)) ^ 2) =
      W * (a ⬝ᵥ (st.featureCov *ᵥ a)) := by
    rw [hf.2]
    have hh := FilterAux.covariance_sum_form D.block st.weights (fun l ↦ φ l - v) W a
    rw [hh, ← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]
  have hgood : (∑ l ∈ D.reference, r l * (x l - μ) ^ 2) ≤
      ∑ l ∈ D.block, st.weights l * (a ⬝ᵥ (φ l - v)) ^ 2 := by
    rw [retained_sum D π hi.1]
    calc
      _ = ∑ l ∈ D.good, st.weights l * (a ⬝ᵥ (φ l - v)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro l hl
        have hx : x l - μ = a ⬝ᵥ (φ l - v) := by
          dsimp only [x, μ, φ]
          rw [hi.1.2.2.2.1 l hl, hdot, dotProduct_sub]
          ring
        rw [hx]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hi.1.2.2.1
        (fun l _ _ ↦ mul_nonneg (hi.2.2.1 l).1 (sq_nonneg _))
  have hvar : (∑ l ∈ D.reference, r l * (x l - μ) ^ 2) ≤
      N * ((101 / 100 : ℝ) * 16 * σ) := by
    rw [hfull] at hgood
    have h₁ := mul_le_mul_of_nonneg_left hApass hW.le
    have h₂ := mul_le_mul_of_nonneg_right (block_mass_upper D st π R hi he)
      (by positivity : 0 ≤ 16 * σ)
    nlinarith only [hgood, h₁, h₂]
  have hr (l : Fin n) (_ : l ∈ D.reference) : 0 ≤ r l ∧ r l ≤ 1 := by
    dsimp only [r]
    split_ifs
    · exact hi.2.2.1 l
    · norm_num
  have hh := FilterAux.between_le_of_retained D.reference D.label r x D.model.weight c
    hr hi.1.1.2.2.1 N σ ((101 / 100 : ℝ) * 16 * σ) μ hN
    (retained_component_mass D st π R hi he)
    (current_component_within D st π R hi hf he A hA hnorm) hvar
  change betweenVariance D st.frame D.mean A ≤ _ at hh
  nlinarith only [hh, hσ]


private theorem pass_feature_mean_shift (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) (hp : Pass st π R)
    (a : (Fin d × Fin d) → ℝ) (hn : a ⬝ᵥ a ≤ 1) :
    let x := fun l ↦ a ⬝ᵥ feature (st.frame *ᵥ (D.clean l - st.center))
    let y := fun l ↦ a ⬝ᵥ feature (st.frame *ᵥ (D.observed l - st.center))
    ((st.mass D.block)⁻¹ * (∑ l ∈ D.block, st.weights l * y l) -
      (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, x l) ^ 2 ≤
      3348 * D.contamination * sigmaSq π R := by
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let σ := sigmaSq π R
  let x := fun l ↦ a ⬝ᵥ feature (st.frame *ᵥ (D.clean l - st.center))
  let y := fun l ↦ a ⬝ᵥ feature (st.frame *ᵥ (D.observed l - st.center))
  let μG := N⁻¹ * ∑ l ∈ D.reference, x l
  let μw := W⁻¹ * ∑ l ∈ D.block, st.weights l * y l
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  have hε : D.contamination ≤ 1 / 400 := by
    have hh := he.trans (min_le_right _ _)
    linarith only [hh, reference_pi_le_one D π hi.1]
  have hε0 : 0 ≤ D.contamination := by
    dsimp only [Reference.contamination]
    positivity
  have hσ : 0 ≤ σ := (by norm_num : (0 : ℝ) ≤ 600).trans
    (sigmaSq_ge600 π R hi.1.1.1 (reference_pi_le_one D π hi.1))
  have hβ : β ≤ 2 * D.contamination := hi.2.2.2.2.2.2.2.2.2.1
  have hρ : ρ ≤ 4 * D.contamination := hi.2.2.2.2.2.2.2.2.2.2.1
  have hVG : a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) =
      N⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2 := by
    simpa only [referenceFeatureCov, one_smul, one_mul] using
      FilterAux.feature_covariance_form D.reference (fun _ ↦ 1)
        (fun l ↦ feature (st.frame *ᵥ (D.clean l - st.center))) N a
  have hVw : a ⬝ᵥ (st.featureCov *ᵥ a) =
      W⁻¹ * ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2 := by
    rw [hf.2]
    exact FilterAux.feature_covariance_form D.block st.weights
      (fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))) W a
  have hh := reference_statistic_shift D st π hi hε x y
    (fun l hl ↦ by dsimp only [x, y]; rw [hi.1.2.2.2.1 l hl])
  change (μw - μG) ^ 2 ≤ 4 * β * _ + 5 * ρ * _ at hh
  rw [← hVG, ← hVw] at hh
  have hVG0 : 0 ≤ a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) := by
    rw [hVG]
    positivity
  have hVw0 : 0 ≤ a ⬝ᵥ (st.featureCov *ᵥ a) := by
    simpa only [star_trivial] using hi.2.2.2.2.2.1.dotProduct_mulVec_nonneg a
  have hpass : a ⬝ᵥ (st.featureCov *ᵥ a) ≤ 16 * σ := by
    have h₁ := pass_feature_bound st π R hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.2.1
      hi.1.1.1 (reference_pi_le_one D π hi.1) hp a
    have h₂ := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 16 * σ)
    nlinarith only [h₁, h₂]
  have href : a ⬝ᵥ (referenceFeatureCov D st *ᵥ a) ≤ 161 * σ := by
    have h₁ := reference_feature_bound D st π R hi hf he (80 * σ)
      (pass_spread D st π R hi hf he hp) a
    have h₂ := mul_le_mul_of_nonneg_left hn
      (by positivity : 0 ≤ 600 / π ^ 2 + 2 * (80 * σ))
    have h₃ : 600 / π ^ 2 ≤ σ := by
      dsimp only [σ, sigmaSq]
      nlinarith only [sq_nonneg R]
    nlinarith only [h₁, h₂, h₃]
  change (μw - μG) ^ 2 ≤ _
  have h₁ := mul_le_mul_of_nonneg_right hβ hVw0
  have h₂ := mul_le_mul_of_nonneg_right hρ hVG0
  have h₃ := mul_le_mul_of_nonneg_left hpass hε0
  have h₄ := mul_le_mul_of_nonneg_left href hε0
  nlinarith only [hh, h₁, h₂, h₃, h₄]

private theorem pass_quadratic_mean_shift (D : Reference n k d) (st : FilterState n d)
    (π R : ℝ) (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400)) (hp : Pass st π R)
    (A : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1) :
    let F := st.frame * (weightedCov D st - D.cov) * st.frameᵀ
    let δ := st.frame *ᵥ (st.center - D.mean)
    ((A * F).trace - qform A δ) ^ 2 ≤ 3348 * D.contamination * sigmaSq π R := by
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let M := st.frame * D.cov * st.frameᵀ
  let C := st.frame * weightedCov D st * st.frameᵀ
  let δ := st.frame *ᵥ (st.center - D.mean)
  let a := fun ij : Fin d × Fin d ↦ A ij.1 ij.2
  let E := FilterAux.average D.reference
  let z := fun l ↦ st.frame *ᵥ (D.clean l - D.mean)
  let f := fun l ↦ qform A (z l)
  let t := fun l ↦ (A *ᵥ δ) ⬝ᵥ z l
  let g := fun l ↦ qform A (st.frame *ᵥ (D.clean l - st.center))
  have hdot (v : Vec d) : a ⬝ᵥ feature v = qform A v := by
    simp only [qform, dotProduct, mulVec, Finset.mul_sum,
      feature, Fintype.sum_prod_type, a]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnorm : a ⬝ᵥ a ≤ 1 := by
    simpa only [a, frobSq, dotProduct, Fintype.sum_prod_type, pow_two] using hn
  have hh := pass_feature_mean_shift D st π R hi hf he hp a hnorm
  dsimp only at hh
  simp_rw [hdot] at hh
  have hC : W⁻¹ * (∑ l ∈ D.block, st.weights l *
      qform A (st.frame *ᵥ (D.observed l - st.center))) = (A * C).trace :=
    (FilterAux.trace_quadratic_average D.block st.weights
      (fun l ↦ D.observed l - st.center) W st.frame A).symm
  have hM : E f = (A * M).trace := by
    have hx := FilterAux.trace_quadratic_average D.reference (fun _ ↦ 1)
      (fun l ↦ D.clean l - D.mean) N st.frame A
    dsimp only [E, FilterAux.average, f, z, M, Reference.cov]
    simpa only [N, one_smul, one_mul, LinearMap.coe_mk, AddHom.coe_mk] using hx.symm
  have ht : E t = 0 := by
    have hx (l : Fin n) : t l =
        (st.frameᵀ *ᵥ (A *ᵥ δ)) ⬝ᵥ (D.clean l - D.mean) := by
      dsimp only [t, z]
      rw [dotProduct_mulVec, ← mulVec_transpose]
    change N⁻¹ * ∑ l ∈ D.reference, t l = 0
    simp_rw [hx]
    rw [reference_centered_sum D π hi.1, mul_zero]
  have hg : g = f - (2 : ℝ) • t + qform A δ • (1 : Fin n → ℝ) := by
    ext l
    have hz : st.frame *ᵥ (D.clean l - st.center) = z l - δ := by
      dsimp only [z, δ]
      rw [← mulVec_sub]
      congr 1
      abel
    change qform A (st.frame *ᵥ (D.clean l - st.center)) =
      f l - 2 * t l + qform A δ * 1
    rw [hz, FilterAux.qform_sub_symmetric A hA]
    dsimp only [f, t]
    ring
  have hG : E g = (A * M).trace + qform A δ := by
    rw [hg, E.map_add, E.map_sub, E.map_smul, E.map_smul, ht, hM,
      FilterAux.average_one D.reference hi.1.2.2.2.2.1]
    simp only [smul_eq_mul, mul_zero, mul_one, sub_zero]
  change (W⁻¹ * (∑ l ∈ D.block, st.weights l *
      qform A (st.frame *ᵥ (D.observed l - st.center))) - E g) ^ 2 ≤ _ at hh
  rw [hC, hG] at hh
  have hF : st.frame * (weightedCov D st - D.cov) * st.frameᵀ = C - M := by
    dsimp only [C, M]
    rw [mul_sub, sub_mul]
  dsimp only
  rw [hF, mul_sub, trace_sub]
  nlinarith only [hh]

/-- A clean pass yields spectral, Frobenius and mean accuracy. -/
theorem pass_accuracy
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hp : Pass st π R) :
    LE ((0.68 : ℝ) • D.cov) (weightedCov D st) ∧
    LE (weightedCov D st) ((8.2 : ℝ) • D.cov) ∧
    frobSq (st.frame * (weightedCov D st - D.cov) * st.frameᵀ) ≤
      (64 : ℝ) ^ 2 * sigmaSq π R * D.contamination ∧
    sqNormIn D.cov (st.center - D.mean) ≤ 370 * D.contamination := by
  classical
  let C := st.frame * weightedCov D st * st.frameᵀ
  let M := st.frame * D.cov * st.frameᵀ
  let F := st.frame * (weightedCov D st - D.cov) * st.frameᵀ
  let δ := st.frame *ᵥ (st.center - D.mean)
  let ε := D.contamination
  let σ := sigmaSq π R
  have hε : 0 ≤ ε := by dsimp only [ε, Reference.contamination]; positivity
  have hεsmall : ε ≤ 1 / 64000 := contamination_le_small D π R hi.1 he
  have hσ : 600 ≤ σ := sigmaSq_ge600 π R hi.1.1.1 (reference_pi_le_one D π hi.1)
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hbudget : ε * σ ≤ 1 / 64000 := by
    have hh := he.trans (min_le_left _ _)
    change ε ≤ 1 / (64000 * σ) at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 64000 * σ)).mp hh
    nlinarith only [hh']
  have hF : F = C - M := by
    dsimp only [F, C, M]
    rw [mul_sub, sub_mul]
  have hCs : Cᵀ = C := by
    obtain ⟨q, _, hq⟩ := hf.1
    change C = diagonal q at hq
    rw [hq, diagonal_transpose]
  have hMs : Mᵀ = M := by
    have hh := hi.1.2.2.2.2.2.1.posSemidef.mul_mul_conjTranspose_same st.frame
    simpa only [conjTranspose_eq_transpose_of_trivial] using hh.1.eq
  have hFs : Fᵀ = F := by rw [hF, transpose_sub, hCs, hMs]
  obtain ⟨A, hA, hnA, hdual⟩ := FilterAux.frob_dual_witness F hFs
  have hmean := pass_quadratic_mean_shift D st π R hi hf he hp A hA hnA
  change ((A * F).trace - qform A δ) ^ 2 ≤ 3348 * ε * σ at hmean
  have hq : qform A δ ^ 2 ≤ sqnorm δ ^ 2 := by
    have hh := Rounding.DetRoundAux.abs_qform_le A 1 (by norm_num)
      (by simpa using hnA) δ
    have hh' := pow_le_pow_left₀ (abs_nonneg _) hh 2
    simpa only [one_mul, sq_abs] using hh'
  have hδ := frame_mean_shift D st π R hi hf he
  change sqnorm δ ≤ 180 * ε at hδ
  have hδsq : sqnorm δ ^ 2 ≤ (81 / 160 : ℝ) * ε * σ := by
    have h₁ := pow_le_pow_left₀ (Rounding.DetRoundAux.sqnorm_nonneg δ) hδ 2
    have h₂ := mul_le_mul_of_nonneg_right hεsmall hε
    have h₃ := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ σ by linarith only [hσ]) hε
    nlinarith only [h₁, h₂, h₃]
  have hdist : frobSq F ≤ 4096 * ε * σ := by
    have hh : (A * F).trace ^ 2 ≤
        (11 / 10 : ℝ) * ((A * F).trace - qform A δ) ^ 2 + 11 * qform A δ ^ 2 := by
      nlinarith only [sq_nonneg ((A * F).trace - 11 * qform A δ)]
    nlinarith only [hh, hmean, hdual, hq, hδsq, mul_nonneg hε hσ0.le]
  have hdistSmall : frobSq F ≤ (3 / 10 : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 4096)
    nlinarith only [hdist, hh]
  have hMlower (v : Vec d) : (7 / 10 : ℝ) * sqnorm v ≤ qform M v := by
    have hC : sqnorm v ≤ qform C v := by
      obtain ⟨q, hq, hframe⟩ := hf.1
      change C = diagonal q at hframe
      rw [hframe]
      simp only [qform, mulVec_diagonal, sqnorm, dotProduct]
      apply Finset.sum_le_sum
      intro i _
      nlinarith only [mul_le_mul_of_nonneg_right (hq i).1 (sq_nonneg (v i))]
    have hh := (abs_le.mp
      (Rounding.DetRoundAux.abs_qform_le F (3 / 10) (by norm_num) hdistSmall v)).2
    have heq : qform F v = qform C v - qform M v := by
      rw [hF]
      simp only [qform, sub_mulVec, dotProduct_sub]
    linarith only [hC, hh, heq]
  have hupperFrame : LE C ((8.2 : ℝ) • M) := by
    intro v
    have h₁ := (frame_covariance_bounds D st π R hi hf he v).2
    have h₂ := hMlower v
    change qform C v ≤ qform ((8.2 : ℝ) • M) v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
    change qform C v ≤ (8.2 : ℝ) * qform M v
    change qform C v ≤ 4 * sqnorm v at h₁
    nlinarith only [h₁, h₂, Rounding.DetRoundAux.sqnorm_nonneg v]
  have hlower : LE ((0.68 : ℝ) • D.cov) (weightedCov D st) := by
    apply FilterAux.le_of_congruence st.frame _ _ hi.2.2.2.2.1
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using covariance_lower D st π R hi hf he
  have hupper : LE (weightedCov D st) ((8.2 : ℝ) • D.cov) := by
    apply FilterAux.le_of_congruence st.frame _ _ hi.2.2.2.2.1
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hupperFrame
  have hmahal : sqNormIn D.cov (st.center - D.mean) ≤ 370 * ε := by
    let y := st.center - D.mean
    let u := D.cov⁻¹ *ᵥ y
    let m := sqNormIn D.cov y
    let β := (D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)
    let ρ := (D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good)
    have hβ : β ≤ 2 * ε := hi.2.2.2.2.2.2.2.2.2.1
    have hρ : ρ ≤ 4 * ε := hi.2.2.2.2.2.2.2.2.2.2.1
    have hβ0 : 0 ≤ β := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun l _ ↦ (hi.2.2.1 l).1
    have hm0 : 0 ≤ m := by
      simpa only [m, sqNormIn, star_trivial] using
        hi.1.2.2.2.2.2.1.inv.posSemidef.dotProduct_mulVec_nonneg y
    have hu : D.cov *ᵥ u = y := by
      dsimp only [u]
      rw [mulVec_mulVec, mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr hi.1.2.2.2.2.2.1.det_pos.ne'), one_mulVec]
    have hdot : u ⬝ᵥ y = m := dotProduct_comm _ _
    have hq : qform D.cov u = m := by rw [qform, hu, hdot]
    have h₁ := point_mean_shift D st π hi (show ε ≤ 1 / 400 by
      linarith only [hεsmall]) u
    change (u ⬝ᵥ y) ^ 2 ≤ 4 * β * qform (weightedCov D st) u + 5 * ρ * qform D.cov u at h₁
    rw [hdot, hq] at h₁
    have h₂ := hupper u
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at h₂
    change qform (weightedCov D st) u ≤ (8.2 : ℝ) * qform D.cov u at h₂
    rw [hq] at h₂
    have h₃ := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 4 * β)
    have h₄ := mul_le_mul_of_nonneg_right hβ hm0
    have h₅ := mul_le_mul_of_nonneg_right hρ hm0
    have hm : m ^ 2 ≤ (86 * ε) * m := by nlinarith only [h₁, h₃, h₄, h₅, mul_nonneg hε hm0]
    change m ≤ _
    by_cases hz : m = 0
    · rw [hz]
      positivity
    · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hz)
      have hh : m ≤ 86 * ε := (mul_le_mul_iff_right₀ hmpos).mp (by
        nlinarith only [hm])
      linarith only [hh, hε]
  refine ⟨hlower, hupper, ?_, hmahal⟩
  change frobSq F ≤ (64 : ℝ) ^ 2 * σ * ε
  nlinarith only [hdist]

/-- Exact update followed by reset to the fixed rational weight grid. -/
def updateWeight (p : ℕ) (w score maximum : ℚ) : ℚ :=
  roundRat p (w * (1 - score / maximum))


end

end ABBKS26.Robust
