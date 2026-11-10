module

public import ABBKS26.Rounding.RC2
public import ABBKS26.Centered.PolyAuxCoeff

/-!
# The centered constraint system

The polynomials of [ABBKS26, Lemma 5.8] and the constraint system of [ABBKS26, Definition 5.9]:
the fourth-moment excess of a centered mixture is a weighted sum of squares of covariance
deviations, and polarizing it gives the Hessian constraint ([ABBKS26, Lemma 5.10]).
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial Matrix
open scoped BigOperators
variable {k d : ℕ}

def averageCov (F : FrameModel k d) : Mat d := ∑ i, F.weight i • F.cov i

def deviation (F : FrameModel k d) (i : Fin k) : Mat d := F.cov i - averageCov F

def phi4 (F : FrameModel k d) : RPoly d := ∑ i, C (3 * F.weight i) * quad (F.cov i) ^ 2

def psi (F : FrameModel k d) : RPoly d := phi4 F - 3 * quad (averageCov F) ^ 2

def polarize (p : RPoly d) : BiPoly d :=
  C (1 / 12) * (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p +
    aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p - 2 * liftV p - 2 * liftU p)

def qConstraint (p : RPoly d) (εq : ℝ) : RPoly d :=
  C (εq ^ 2) * nsq ^ 4 - (C (1 / 3) * p) ^ 2

def hConstraint (p : RPoly d) (εh : ℝ) : BiPoly d :=
  C εh * (liftV nsq ^ 4 + liftU nsq ^ 4) - (4 * polarize p) ^ 2

def system (p : RPoly d) (εq εh : ℝ) : Rounding.FamilySystem d :=
  ⟨[1 - nsq, qConstraint p εq], [hConstraint p εh], [⟨0, by simp⟩]⟩

def DataValid (F : FrameModel k d) (w γ rF : ℝ) : Prop :=
  F.Valid w ∧ (∀ i, F.mean i = 0) ∧ F.Isotropic γ ∧ γ ≤ 1 / 10 ∧
    ∀ i, frobSq (F.cov i - 1) ≤ rF

private theorem qform_average (F : FrameModel k d) (v : Vec d) :
    qform (averageCov F) v = ∑ i, F.weight i * qform (F.cov i) v := by
  simp only [averageCov, qform, sum_mulVec, dotProduct_sum, smul_mulVec,
    dotProduct_smul, smul_eq_mul]

private theorem centered_second (F : FrameModel k d) (h : ∀ i, F.mean i = 0) :
    F.second = averageCov F := by
  simp only [FrameModel.second, h, vecMulVec_zero, add_zero, averageCov]

private theorem covariance_bounds (F : FrameModel k d) (w γ rF : ℝ)
    (h : DataValid F w γ rF) (i : Fin k) (v : Vec d) :
    0 ≤ qform (F.cov i) v ∧
      qform (averageCov F) v ≤ 1.1 * sqnorm v ∧
      F.weight i * qform (F.cov i) v ≤ qform (averageCov F) v := by
  have hn : ∀ j, 0 ≤ qform (F.cov j) v := fun j ↦ by
    simpa only [qform, star_trivial] using
      (h.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v
  have hw : ∀ j, 0 ≤ F.weight j := fun j ↦ h.1.1.le.trans (h.1.2.1 j)
  refine ⟨hn i, ?_, ?_⟩
  · have hu := h.2.2.1.2.2 v
    rw [centered_second F h.2.1] at hu
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hu
    exact hu.trans (mul_le_mul_of_nonneg_right (by linarith [h.2.2.2.1])
      (Rounding.DetRoundAux.sqnorm_nonneg v))
  · rw [qform_average]
    exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j) (hn j)) (Finset.mem_univ i)

/-- Each centered covariance deviation has an operator bound. -/
theorem deviation_bound
    (F : FrameModel k d) (w γ rF : ℝ) (h : DataValid F w γ rF) :
    (∑ i, F.weight i • deviation F i) = 0 ∧
    ∀ i v, |qform (deviation F i) v| ≤ (1.1 / w) * sqnorm v := by
  constructor
  · simp only [deviation, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      h.1.2.2.1, one_smul, averageCov, sub_self]
  · intro i v
    obtain ⟨hn, hu, hi⟩ := covariance_bounds F w γ rF h i v
    have hs := Rounding.DetRoundAux.sqnorm_nonneg v
    have hw1 : w ≤ 1 := (h.1.2.1 i).trans (by
      rw [← h.1.2.2.1]
      exact Finset.single_le_sum (fun j _ ↦ h.1.1.le.trans (h.1.2.1 j))
        (Finset.mem_univ i))
    have hav : 0 ≤ qform (averageCov F) v := (mul_nonneg
      (h.1.1.le.trans (h.1.2.1 i)) hn).trans hi
    have hcov : qform (F.cov i) v ≤ (1.1 / w) * sqnorm v := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ h.1.1).2
      nlinarith [mul_le_mul_of_nonneg_right (h.1.2.1 i) hn]
    have hscale : 1.1 * sqnorm v ≤ (1.1 / w) * sqnorm v := by
      apply mul_le_mul_of_nonneg_right _ hs
      exact (le_div_iff₀ h.1.1).2 (by linarith)
    change |qform (F.cov i - averageCov F) v| ≤ _
    rw [show qform (F.cov i - averageCov F) v =
      qform (F.cov i) v - qform (averageCov F) v by
        simp only [qform, sub_mulVec, dotProduct_sub]]
    exact abs_le.2 ⟨by linarith, by linarith⟩

private def quadLinear : Mat d →ₗ[ℝ] RPoly d where
  toFun := quad
  map_add' A B := by
    simp [quad, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [quad, Matrix.smul_apply, smul_eq_C_mul, Finset.mul_sum, mul_assoc]

private theorem quad_average (F : FrameModel k d) :
    quad (averageCov F) = ∑ i, C (F.weight i) * quad (F.cov i) := by
  change quadLinear (∑ i, F.weight i • F.cov i) = _
  simp only [map_sum, map_smul, smul_eq_C_mul]
  rfl

/-- The centered fourth-moment excess is a weighted sum of squares. -/
theorem quartic_identity
    (F : FrameModel k d) (hsum : ∑ i, F.weight i = 1) :
    psi F = 3 * ∑ i, C (F.weight i) * quad (deviation F i) ^ 2 := by
  have hdev (i : Fin k) : quad (deviation F i) = quad (F.cov i) -
      quad (averageCov F) := (quadLinear (d := d)).map_sub _ _
  have hsumC : ∑ i, (C (F.weight i) : RPoly d) = 1 := by
    rw [← map_sum, hsum, map_one]
  simp only [psi, phi4, hdev, map_mul, map_ofNat]
  simp_rw [show ∀ a b c : RPoly d, c * (a - b) ^ 2 =
      c * a ^ 2 - 2 * b * (c * a) + b ^ 2 * c by intros; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← quad_average, hsumC]
  simp_rw [mul_assoc (3 : RPoly d), ← Finset.mul_sum]
  ring

private theorem quad_aeval_add_smul (A : Mat d) (hA : A.IsHermitian)
    (c : BiPoly d) :
    aeval (fun i ↦ X (Sum.inr i) + c * X (Sum.inl i)) (quad A) =
      liftV (quad A) + c ^ 2 * liftU (quad A) +
        2 * c * ∑ a, ∑ b, C (A a b) * X (Sum.inl a) * X (Sum.inr b) := by
  have hcross : (∑ a, ∑ b, C (A a b) * X (Sum.inr a) * X (Sum.inl b)) =
      (∑ a, ∑ b, C (A a b) * X (Sum.inl a) * X (Sum.inr b) : BiPoly d) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [show A b a = A a b by simpa only [star_trivial] using hA.apply a b]
    ring
  simp only [quad, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    liftV, liftU, rename_C, rename_X]
  simp_rw [show ∀ r x y z w : BiPoly d,
    r * (x + c * y) * (z + c * w) = r * x * z + c ^ 2 * (r * y * w) +
      c * (r * x * w) + c * (r * y * z) by intros; ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hcross]
  ring

/-- Polarization gives the centered Hessian identity. -/
theorem hessian_identity
    (F : FrameModel k d) (hsum : ∑ i, F.weight i = 1)
    (hsymm : ∀ i, (F.cov i).IsHermitian) :
    4 * polarize (psi F) =
      8 * (∑ i, C (F.weight i) *
        (∑ a, ∑ b, C (deviation F i a b) * X (Sum.inl a) * X (Sum.inr b)) ^ 2) +
      4 * ∑ i, C (F.weight i) * liftV (quad (deviation F i)) *
        liftU (quad (deviation F i)) := by
  have hdev (i : Fin k) : (deviation F i).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro a b
    have hentry (j : Fin k) : F.cov j b a = F.cov j a b := by
      simpa only [star_trivial] using (hsymm j).apply a b
    simp only [deviation, averageCov, Matrix.sub_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, star_trivial, hentry]
  have hadd (i : Fin k) := quad_aeval_add_smul (deviation F i) (hdev i) 1
  have hsub (i : Fin k) := quad_aeval_add_smul (deviation F i) (hdev i) (-1)
  simp only [one_mul, one_pow, mul_one] at hadd
  simp only [neg_mul, one_mul, neg_one_sq, ← sub_eq_add_neg] at hsub
  rw [quartic_identity F hsum]
  simp only [polarize, liftV, liftU, map_mul, map_ofNat, map_sum, map_pow,
    aeval_C, algebraMap_eq, rename_C, hadd, hsub]
  have hc : (C (1 / 12) : BiPoly d) * 12 = 1 := by
    rw [← map_ofNat C 12, ← C_mul]
    norm_num
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination
    (8 * C (F.weight i) *
        (∑ a, ∑ b, C (deviation F i a b) * (X (Sum.inl a) * X (Sum.inr b))) ^ 2 +
      4 * C (F.weight i) * rename Sum.inr (quad (deviation F i)) *
        rename Sum.inl (quad (deviation F i))) * hc


private theorem eval_nsq (v : Vec d) : eval v (nsq : RPoly d) = sqnorm v := by
  simp [nsq, sqnorm, dotProduct, pow_two]

private theorem eval_quad (A : Mat d) (v : Vec d) : eval v (quad A) = qform A v := by
  simp only [quad, map_sum, map_mul, eval_C, eval_X, qform, mulVec, dotProduct,
    Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring

private theorem eval_phi4_bounds (F : FrameModel k d) (w γ rF : ℝ)
    (h : DataValid F w γ rF) (v : Vec d) :
    0 ≤ eval v (phi4 F) ∧ eval v (phi4 F) ≤ (3.63 / w) * sqnorm v ^ 2 := by
  have hs := Rounding.DetRoundAux.sqnorm_nonneg v
  have hw := h.1.1
  have hn (i : Fin k) : 0 ≤ qform (F.cov i) v :=
    (covariance_bounds F w γ rF h i v).1
  have hw' (i : Fin k) : 0 ≤ F.weight i := hw.le.trans (h.1.2.1 i)
  have hu (i : Fin k) : qform (F.cov i) v ≤ (1.1 / w) * sqnorm v := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hw).2
    obtain ⟨_, hav, hi⟩ := covariance_bounds F w γ rF h i v
    nlinarith [mul_le_mul_of_nonneg_right (h.1.2.1 i) (hn i)]
  have he : eval v (phi4 F) = 3 * ∑ i, F.weight i * qform (F.cov i) v ^ 2 := by
    simp only [phi4, map_sum, map_mul, eval_C, map_pow, eval_quad, Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [he]
  refine ⟨mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw' i) (sq_nonneg _)), ?_⟩
  have hav : qform (averageCov F) v ≤ 1.1 * sqnorm v := by
    by_cases hk : Nonempty (Fin k)
    · exact (covariance_bounds F w γ rF h hk.some v).2.1
    · have hz : k = 0 := by simpa using hk
      subst k
      have he := h.1.2.2.1
      simp at he
  calc
    3 * ∑ i, F.weight i * qform (F.cov i) v ^ 2 ≤
        3 * ∑ i, F.weight i * ((1.1 / w) * sqnorm v * qform (F.cov i) v) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw' i)
      nlinarith [mul_le_mul_of_nonneg_right (hu i) (hn i)]
    _ = 3 * ((1.1 / w) * sqnorm v) * qform (averageCov F) v := by
      simp only [qform_average, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 3 * ((1.1 / w) * sqnorm v) * (1.1 * sqnorm v) := by
      gcongr
    _ = (3.63 / w) * sqnorm v ^ 2 := by ring

private theorem nsq_homogeneous : (nsq : RPoly d).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℝ i).pow 2

private theorem coefficient_constant (w : ℝ) (hw : 0 < w) (hw' : w ≤ 1 / 2) :
    8 * (2 + 3.63 / w) + 2 ≤ 20 / w ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hw)).2
  have he : (8 * (2 + 3.63 / w) + 2) * w ^ 2 = 18 * w ^ 2 + 29.04 * w := by
    field_simp
    ring
  rw [he]
  nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hw')]

/-- An injective fourth-moment certificate bounds all coefficients. -/
theorem coefficient_bound
    (F : FrameModel k d) (w γ rF η : ℝ) (p : RPoly d)
    (hF : DataValid F w γ rF) (hw : w ≤ 1 / 2) (hη : 0 ≤ η ∧ η ≤ 1)
    (hp : p.IsHomogeneous 4) (h : IsSumSq (C η * nsq ^ 4 - (p - phi4 F) ^ 2)) :
    ∀ α, |p.coeff α| ≤ 20 / w ^ 2 := by
  have hwpos : 0 < w := hF.1.1
  have hq : (p + nsq ^ 2).IsHomogeneous 4 := by
    exact hp.add (by simpa using (nsq_homogeneous (d := d)).pow 2)
  have hB : 0 ≤ 2 + 3.63 / w := by positivity
  have hb (v : Vec d) : 0 ≤ eval v (p + nsq ^ 2) ∧
      eval v (p + nsq ^ 2) ≤ (2 + 3.63 / w) * sqnorm v ^ 2 := by
    have hc := SoS.Correct.eval_nonneg_of_isSumSq h v
    simp only [map_sub, map_mul, map_pow, eval_C, eval_nsq] at hc
    have hs := Rounding.DetRoundAux.sqnorm_nonneg v
    have hdiff : |eval v p - eval v (phi4 F)| ≤ sqnorm v ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) (sq_nonneg _)).mp
      rw [sq_abs]
      nlinarith [mul_le_mul_of_nonneg_right hη.2 (by positivity : 0 ≤ sqnorm v ^ 4)]
    obtain ⟨hl, hu⟩ := eval_phi4_bounds F w γ rF hF v
    simp only [map_add, map_pow, eval_nsq]
    obtain ⟨hdlo, hdhi⟩ := abs_le.mp hdiff
    constructor <;> nlinarith
  intro α
  have hc := PolyAux.nonneg_coeff (p + nsq ^ 2) hq (2 + 3.63 / w) hB hb α
  have hn := PolyAux.nsq_sq_coeff α
  have he : p.coeff α = (p + nsq ^ 2).coeff α - (nsq ^ 2).coeff α := by
    simp
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hc hn).trans
    (coefficient_constant w hF.1.1 hw))

end

end ABBKS26.Centered
