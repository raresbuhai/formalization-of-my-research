module

public import ABBKS26.Robust.Filter

/-! Scalar bounds for the Gaussian moment certificates. -/

@[expose] public section

namespace ABBKS26.Robust.MomentAux

open Common MvPolynomial
open scoped BigOperators Nat

theorem lin_smul {d : ℕ} (c : ℝ) (v : Vec d) : lin (c • v) = C c * lin v := by
  simp [lin, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]

theorem quad_smul {d : ℕ} (c : ℝ) (S : Mat d) : quad (c • S) = C c * quad S := by
  simp [quad, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]

theorem hmom_scale {K : Type} [CommRing K] (r : ℕ) (c a v : K) :
    IdCov.hmom r (c * a) (c ^ 2 * v) = c ^ r * IdCov.hmom r a v := by
  unfold IdCov.hmom
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : r - 2 * i + 2 * i = r := by
    simp only [Finset.mem_range] at hi
    omega
  simp only [mul_pow, ← pow_mul]
  calc
    (IdCov.hermCoeff r i : K) * (c ^ (r - 2 * i) * a ^ (r - 2 * i)) *
        (c ^ (2 * i) * v ^ i) =
        (c ^ (r - 2 * i) * c ^ (2 * i)) *
          ((IdCov.hermCoeff r i : K) * a ^ (r - 2 * i) * v ^ i) := by ring
    _ = _ := by rw [← pow_add, he]

theorem scaled_norms {d : ℕ} (w c : ℝ) (μ : Vec d) (S : Mat d)
    (hw : 0 < w) (hc : c ^ 2 = w / 2) (hμ : sqnorm μ ≤ 2 / w)
    (hS : S.PosSemidef) (hup : LE S ((1.1 / w) • (1 : Mat d))) :
    SoS.coeffNorm1 (lin (c • μ)) ≤ d ∧
      SoS.coeffNorm1 (quad (c ^ 2 • S)) ≤ (d : ℝ) ^ 2 := by
  have hcancel : c ^ 2 * (2 / w) = 1 := by rw [hc]; field_simp
  have hμi (i : Fin d) : |c * μ i| ≤ 1 := by
    have hi : μ i ^ 2 ≤ sqnorm μ := by
      simpa only [sqnorm, dotProduct, ← pow_two] using
        Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (μ j))
          (Finset.mem_univ i)
    have hh := mul_le_mul_of_nonneg_left (hi.trans hμ) (sq_nonneg c)
    rw [hcancel] at hh
    rw [abs_le]
    constructor <;> nlinarith only [hh]
  have hSi (i j : Fin d) : |c ^ 2 * S i j| ≤ 1 := by
    have hi := FilterAux.entries_le_of_qform_le S hS (1.1 / w) (fun u ↦ by
      simpa only [qform, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
        smul_eq_mul, sqnorm] using hup u) i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
    calc
      _ ≤ c ^ 2 * (1.1 / w) := mul_le_mul_of_nonneg_left hi (sq_nonneg c)
      _ ≤ 1 := by rw [hc]; field_simp; linarith only [hw]
  constructor
  · calc
      _ ≤ ∑ i, SoS.coeffNorm1 (C (c * μ i) * (X i : RPoly d)) :=
        SoS.coeffNorm1_sum_le _ _
      _ = ∑ i, |c * μ i| := by simp only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X,
        mul_one]
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hμi i
      _ = d := by simp
  · have hi (i j : Fin d) :
        SoS.coeffNorm1 (C (c ^ 2 * S i j) * (X i : RPoly d) * X j) ≤ 1 := by
      have hh := SoS.coeffNorm1_mul_le (C (c ^ 2 * S i j) * (X i : RPoly d)) (X j)
      simp only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, mul_one] at hh
      exact hh.trans (hSi i j)
    calc
      _ ≤ ∑ i, SoS.coeffNorm1 (∑ j, C (c ^ 2 * S i j) * (X i : RPoly d) * X j) :=
        SoS.coeffNorm1_sum_le _ _
      _ ≤ ∑ i, ∑ j, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦
        (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hi i j)
      _ = (d : ℝ) ^ 2 := by simp [pow_two]

private theorem doubleFactorial_le (t : ℕ) : (2 * t - 1)‼ ≤ (2 * t) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, Nat.doubleFactorial_add_one]
    calc
      (2 * t + 1) * (2 * t - 1)‼ ≤ (2 * (t + 1)) * (2 * t) ^ t :=
        Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (t + 1)) * (2 * (t + 1)) ^ t :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (2 * (t + 1)) ^ (t + 1) := by ring

theorem even_moment_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1),
      (IdCov.hermCoeff (2 * r) i : ℝ) * A ^ (r - i) * B ^ i) ≤
      (2 * A + 4 * r * B) ^ r := by
  let a := Real.sqrt A
  let b := Real.sqrt (2 * r * B)
  have ha : a ^ 2 = A := Real.sq_sqrt hA
  have hb : b ^ 2 = 2 * r * B := Real.sq_sqrt (by positivity)
  let f : ℕ → ℝ := fun j ↦ b ^ j * a ^ (2 * r - j) * ((2 * r).choose j : ℝ)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (r + 1)) :
      (IdCov.hermCoeff (2 * r) i : ℝ) * A ^ (r - i) * B ^ i ≤ f (2 * i) := by
    have hi' : i ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hd : ((2 * i - 1)‼ : ℝ) ≤ (2 * r : ℝ) ^ i := by
      exact_mod_cast (doubleFactorial_le i).trans (Nat.pow_le_pow_left (by omega) i)
    have he : f (2 * i) = ((2 * r).choose (2 * i) : ℝ) *
        A ^ (r - i) * ((2 * r : ℝ) ^ i * B ^ i) := by
      dsimp only [f]
      rw [show 2 * r - 2 * i = 2 * (r - i) by omega,
        pow_mul, pow_mul, ha, hb, mul_pow]
      ring
    rw [he, IdCov.hermCoeff, Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd (pow_nonneg hB i))
      (show 0 ≤ ((2 * r).choose (2 * i) : ℝ) * A ^ (r - i) by positivity)
    nlinarith only [hh]
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), f (2 * i) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ (Finset.range (r + 1)).image (fun i ↦ 2 * i), f j := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      dsimp only at hij
      omega
    _ ≤ ∑ j ∈ Finset.range (2 * r + 1), f j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        simp only [Finset.mem_range] at hi ⊢
        omega
      · intro j _ _
        dsimp only [f, a, b]
        positivity
    _ = (b + a) ^ (2 * r) := (add_pow b a (2 * r)).symm
    _ = ((b + a) ^ 2) ^ r := by rw [pow_mul]
    _ ≤ (2 * A + 4 * r * B) ^ r := by
      apply pow_le_pow_left₀ (sq_nonneg _)
      nlinarith only [ha, hb, sq_nonneg (a - b)]

end ABBKS26.Robust.MomentAux
