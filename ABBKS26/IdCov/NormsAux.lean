module

public import ABBKS26.IdCov.Params
public import ABBKS26.IdCov.ApproxAux
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Coefficient extraction by finite differences, and elementary parameter estimates. -/

@[expose] public section

namespace ABBKS26.IdCov.NormsAux

noncomputable section

open Common MvPolynomial Finset
open scoped BigOperators

def diffWeight (a : ℕ) (i : Fin (a + 1)) : ℝ :=
  (-1) ^ (a - i.val) * (a.choose i.val : ℝ)

theorem diffWeight_moment (a b : ℕ) (hb : b ≤ a) :
    (∑ i : Fin (a + 1), diffWeight a i * (i.val : ℝ) ^ b) =
      if a = b then (a.factorial : ℝ) else 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℝ) (fun x : ℝ ↦ x ^ b) a 0
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at h
  simp only [diffWeight]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
    (-1 : ℝ) ^ (a - i) * (a.choose i : ℝ) * (i : ℝ) ^ b)]
  change (∑ i ∈ range (a + 1), (-1 : ℝ) ^ (a - i) * (a.choose i : ℝ) *
    (i : ℝ) ^ b) = _
  rw [← h]
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [fwdDiff_iter_eq_factorial]
  · rw [fwdDiff_iter_pow_eq_zero_of_lt hb]
    simp [hb.ne']

theorem diffWeight_abs_sum (a : ℕ) :
    (∑ i : Fin (a + 1), |diffWeight a i|) = (2 : ℝ) ^ a := by
  simp only [diffWeight, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (a.choose i : ℝ)),
    ← Nat.cast_sum, Nat.sum_range_choose]
  simp

/-- The highest-degree coefficient is a weighted sum of values on its integer box. -/
theorem coeff_box {d r : ℕ} (p : RPoly d) (hp : p.IsHomogeneous r)
    (a : Fin d →₀ ℕ) (ha : a.degree = r) :
    p.coeff a * ∏ i, ((a i).factorial : ℝ) =
      ∑ x : (i : Fin d) → Fin (a i + 1),
        (∏ i, diffWeight (a i) (x i)) * eval (fun i ↦ ((x i).val : ℝ)) p := by
  classical
  simp_rw [eval_eq', mul_sum]
  rw [sum_comm]
  have hterm (b : Fin d →₀ ℕ) (hb : b ∈ p.support) :
      (∑ x : (i : Fin d) → Fin (a i + 1),
        (∏ i, diffWeight (a i) (x i)) * (p.coeff b * ∏ i, ((x i).val : ℝ) ^ b i)) =
      if a = b then p.coeff a * ∏ i, ((a i).factorial : ℝ) else 0 := by
    have hbdeg : b.degree = r := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (mem_support_iff.mp hb)
    calc
      _ = p.coeff b * ∏ i, ∑ x : Fin (a i + 1),
          diffWeight (a i) x * (x.val : ℝ) ^ b i := by
        rw [Fintype.prod_sum, mul_sum]
        apply sum_congr rfl
        intro x _
        rw [prod_mul_distrib]
        ring
      _ = _ := by
        by_cases hab : a = b
        · subst b
          simp only [diffWeight_moment _ _ le_rfl, ite_true]
        · have hlt : ∃ i, b i < a i := by
            by_contra! h
            have heq : a = b := Finsupp.ext fun i ↦ by
              have hs : ∑ j : Fin d, a j = ∑ j : Fin d, b j := by
                simpa only [← Finsupp.degree_eq_sum] using ha.trans hbdeg.symm
              exact (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ h j)).mp hs i (mem_univ i)
            exact hab heq
          obtain ⟨i, hi⟩ := hlt
          rw [prod_eq_zero (mem_univ i) (by
            rw [diffWeight_moment _ _ hi.le, ite_eq_right hi.ne']), mul_zero, ite_eq_right hab]
  rw [sum_congr rfl hterm, sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [notMem_support_iff.mp h, zero_mul]

/-- A homogeneous polynomial controlled on its integer coefficient boxes has small coefficients. -/
theorem coeff_bound {d r : ℕ} (p : RPoly d) (hp : p.IsHomogeneous r) (B : ℝ)
    (hB : 0 ≤ B)
    (hv : ∀ a : Fin d →₀ ℕ, a.degree = r →
      ∀ x : (i : Fin d) → Fin (a i + 1), |eval (fun i ↦ ((x i).val : ℝ)) p| ≤ B) :
    ∀ a, |p.coeff a| ≤ 2 ^ r * B := by
  classical
  intro a
  by_cases h : p.coeff a = 0
  · simpa [h] using mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ r) hB
  have ha : a.degree = r := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp h
  have hf : (1 : ℝ) ≤ ∏ i : Fin d, ((a i).factorial : ℝ) :=
    one_le_prod₀ fun i _ ↦ by exact_mod_cast Nat.factorial_pos (a i)
  calc
    |p.coeff a| ≤ |p.coeff a| * ∏ i, ((a i).factorial : ℝ) :=
      le_mul_of_one_le_right (abs_nonneg _) hf
    _ = |p.coeff a * ∏ i, ((a i).factorial : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ∏ i, ((a i).factorial : ℝ))]
    _ ≤ ∑ x : (i : Fin d) → Fin (a i + 1),
        (∏ i, |diffWeight (a i) (x i)|) * B := by
      rw [coeff_box p hp a ha]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
      rw [abs_mul, abs_prod]
      exact mul_le_mul_of_nonneg_left (hv a ha x) (by positivity)
    _ = 2 ^ r * B := by
      rw [← sum_mul, ← Fintype.prod_sum (fun i (x : Fin (a i + 1)) ↦
        |diffWeight (a i) x|)]
      simp_rw [diffWeight_abs_sum]
      rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, ha]

/-- The integer box for a degree `r` coefficient lies in the radius `r` ball. -/
theorem box_sqnorm {d r : ℕ} (a : Fin d →₀ ℕ) (ha : a.degree = r)
    (x : (i : Fin d) → Fin (a i + 1)) :
    sqnorm (fun i ↦ ((x i).val : ℝ)) ≤ (r : ℝ) ^ 2 := by
  have hs : (∑ i : Fin d, ((x i).val : ℝ)) ≤ r := by
    calc _ ≤ ∑ i : Fin d, (a i : ℝ) := sum_le_sum fun i _ ↦ by
          exact_mod_cast Nat.le_of_lt_succ (x i).isLt
      _ = r := by exact_mod_cast (Finsupp.degree_eq_sum a).symm.trans ha
  change (∑ i, ((x i).val : ℝ) * (x i).val) ≤ _
  simp only [← pow_two]
  exact (sum_sq_le_sq_sum_of_nonneg (fun i _ ↦ Nat.cast_nonneg _)).trans
    (pow_le_pow_left₀ (by positivity) hs 2)

theorem norm_of_coeff {d r : ℕ} (p : RPoly d) (hp : p.IsHomogeneous r)
    (B : ℝ) (hB : 0 ≤ B) (hc : ∀ a, |p.coeff a| ≤ B) :
    SoS.coeffNorm1 p ≤ (d + 1 : ℝ) ^ r * B := by
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ r := by
    have h := SoS.card_support_le p
    rw [Fintype.card_fin] at h
    exact_mod_cast h.trans (Nat.pow_le_pow_right (Nat.succ_pos d) hp.totalDegree_le)
  exact (SoS.coeffNorm1_le hc).trans (mul_le_mul_of_nonneg_right hcard hB)

/-- Dimension-polynomial norm bound for a certified homogeneous moment error. -/
theorem error_norm {k d t s : ℕ} (D : Data k d) (M : ℕ → RPoly d)
    (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) (hs : 1 ≤ s ∧ s ≤ 2 * t)
    (hM : momentCertificate D M t η) :
    SoS.coeffNorm1 (M (2 * s) - moment D (2 * s)) ≤
      (4 * s * (d + 1 : ℝ)) ^ (2 * s) := by
  let E := M (2 * s) - moment D (2 * s)
  have hh : E.IsHomogeneous (2 * s) :=
    (hM.1 s hs.1 hs.2).sub (homogeneity D (2 * s) 0).1
  have hc : ∀ a, |E.coeff a| ≤ (4 * s : ℝ) ^ (2 * s) := by
    have hb := coeff_bound E hh ((2 * s : ℝ) ^ (2 * s)) (by positivity) ?_
    · simpa only [← mul_pow, mul_assoc, show (2 : ℝ) * (2 * s) = 4 * s by ring] using hb
    intro a ha x
    have hn : 0 ≤ sqnorm (fun i ↦ ((x i).val : ℝ)) := by
      change 0 ≤ ∑ i, ((x i).val : ℝ) * (x i).val
      exact sum_nonneg fun i _ ↦ mul_self_nonneg _
    have he := (SoS.isSumSq_map (eval (fun i ↦ ((x i).val : ℝ)))
      (hM.2 s hs.1 hs.2)).nonneg
    simp only [map_sub, map_mul, eval_C, map_pow, ApproxAux.eval_nsq] at he
    have heval : eval (fun i ↦ ((x i).val : ℝ)) E =
        eval (fun i ↦ ((x i).val : ℝ)) (M (2 * s)) -
          eval (fun i ↦ ((x i).val : ℝ)) (moment D (2 * s)) := map_sub _ _ _
    rw [← heval] at he
    change 0 ≤ η * sqnorm (fun i ↦ ((x i).val : ℝ)) ^ (2 * s) -
      eval (fun i ↦ ((x i).val : ℝ)) E ^ 2 at he
    have hpow := pow_le_pow_left₀ hn (box_sqnorm a ha x) (2 * s)
    have hbase : (sqnorm (fun i ↦ ((x i).val : ℝ))) ^ (2 * s) ≤
        ((2 * s : ℝ) ^ (2 * s)) ^ 2 := by
      simpa only [← pow_mul, mul_comm 2 (2 * s), Nat.cast_mul, Nat.cast_ofNat] using hpow
    have hmul := mul_le_mul_of_nonneg_right hη.2
      (pow_nonneg hn (2 * s))
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith
  calc _ ≤ (d + 1 : ℝ) ^ (2 * s) * (4 * s : ℝ) ^ (2 * s) :=
        norm_of_coeff E hh _ (by positivity) hc
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem parameter_bounds (w β : ℚ) (hβ : 0 < β ∧ β ≤ 1 / 4) :
    0 < epsilonSys w β ∧ epsilonSys w β ≤ 1 ∧
      0 < etaStar w β ∧ etaStar w β / 4 ≤ 1 := by
  have hβ0 := hβ.1
  have ht : (3 : ℚ) ≤ tDegree w := by
    exact_mod_cast (show 3 ≤ tDegree w by unfold tDegree; omega)
  have he : 0 < epsilonR β ∧ epsilonR β ≤ 1 := by
    constructor
    · unfold epsilonR; positivity
    · exact pow_le_one₀ (by positivity : 0 ≤ β / 25)
        (by linarith : β / 25 ≤ 1)
  have he0 := he.1
  have hc : 0 < cStar β ∧ cStar β ≤ 1 := by
    dsimp [cStar]
    constructor
    · positivity
    · have := pow_le_one₀ he.1.le he.2 (n := 2); linarith
  have hc0 := hc.1
  have hb : 0 < cStar β / (64 * tDegree w) ∧ cStar β / (64 * tDegree w) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr; linarith
  have hid : 0 < epsilonId w β ∧ epsilonId w β ≤ 1 :=
    ⟨pow_pos hb.1 _, pow_le_one₀ hb.1.le hb.2⟩
  have hs : 0 < epsilonSys w β ∧ epsilonSys w β ≤ 1 := by
    dsimp [epsilonSys]; constructor <;> linarith
  have hg : (1 : ℚ) ≤ (8 * tDegree w : ℚ) ^ (4 * tDegree w + 2) :=
    one_le_pow₀ (by linarith)
  refine ⟨hs.1, hs.2, div_pos hs.1 (by positivity), ?_⟩
  have heta : etaStar w β ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact hs.2.trans hg
  linarith

/-- A rough bound for the sum of all nonnegative Gaussian moment coefficients. -/
theorem hermCoeff_sum_bound {r : ℕ} (hr : 1 ≤ r) :
    (∑ j ∈ range (r / 2 + 1), (hermCoeff r j : ℝ)) ≤ (2 * r : ℝ) ^ r := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hchoose : ∑ j ∈ range (r / 2 + 1), r.choose (2 * j) ≤ 2 ^ r := by
    calc _ = ∑ j ∈ (range (r / 2 + 1)).image (fun j ↦ 2 * j), r.choose j := by
          rw [sum_image]
          intro i _ j _ h
          dsimp at h
          omega
      _ ≤ ∑ j ∈ range (r + 1), r.choose j := by
          apply sum_le_sum_of_subset
          intro j hj
          rcases mem_image.mp hj with ⟨i, hi, rfl⟩
          have := mem_range.mp hi
          apply mem_range.mpr
          omega
      _ = 2 ^ r := Nat.sum_range_choose r
  have hcoef (j : ℕ) (hj : j ∈ range (r / 2 + 1)) :
      (hermCoeff r j : ℝ) ≤ (r.choose (2 * j) : ℝ) * (r : ℝ) ^ r := by
    have hj' : 2 * j ≤ r := by have := mem_range.mp hj; omega
    have hdf : (Nat.doubleFactorial (2 * j - 1) : ℝ) ≤ (r : ℝ) ^ r := by
      calc _ ≤ (2 * j : ℝ) ^ j := IdentAux.alpha_bound j
        _ ≤ (r : ℝ) ^ j := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hj') _
        _ ≤ (r : ℝ) ^ r := pow_le_pow_right₀ hrR (by omega)
    simpa only [hermCoeff, Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hdf (Nat.cast_nonneg (r.choose (2 * j)))
  calc _ ≤ ∑ j ∈ range (r / 2 + 1), (r.choose (2 * j) : ℝ) * (r : ℝ) ^ r :=
        sum_le_sum hcoef
    _ = (∑ j ∈ range (r / 2 + 1), (r.choose (2 * j) : ℝ)) * (r : ℝ) ^ r :=
        (sum_mul ..).symm
    _ ≤ (2 : ℝ) ^ r * (r : ℝ) ^ r := by
        gcongr
        exact_mod_cast hchoose
    _ = _ := (mul_pow ..).symm

/-- Moment norms from bounds on the linear means and the covariance polynomial. -/
theorem moment_norm {k d t : ℕ} (D : Data k d) (π γ A : ℝ)
    (hD : D.Valid π γ) (hA : 1 ≤ A)
    (hlin : ∀ i, SoS.coeffNorm1 (lin (D.mean i)) ≤ A)
    (hS : SoS.coeffNorm1 (S D) ≤ A ^ 2) (r : ℕ) (hr : r ≤ 4 * t) :
    SoS.coeffNorm1 (moment D r) ≤ (8 * t * A) ^ r := by
  have hw (i : Fin k) : 0 ≤ D.weight i := hD.1.1.le.trans (hD.1.2.1 i)
  have hs : ∑ i, D.weight i = 1 := hD.1.2.2.1
  by_cases hz : r = 0
  · subst r
    have hm : moment D 0 = 1 := by
      simp [moment, hmom, hermCoeff, ← map_sum, hs]
    rw [hm, SoS.coeffNorm1_one, pow_zero]
  have hr1 : 1 ≤ r := by omega
  have ht (i : Fin k) : SoS.coeffNorm1 (hmom r (lin (D.mean i)) (S D)) ≤
      (2 * r * A) ^ r := by
    calc _ ≤ ∑ j ∈ range (r / 2 + 1),
          (hermCoeff r j : ℝ) * A ^ r := by
          apply (SoS.coeffNorm1_sum_le _ _).trans
          apply sum_le_sum
          intro j hj
          have hj' : 2 * j ≤ r := by have := mem_range.mp hj; omega
          rw [show (hermCoeff r j : RPoly d) = C (hermCoeff r j : ℝ) by simp,
            mul_assoc, SoS.coeffNorm1_C_mul, Nat.abs_cast]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc _ ≤ A ^ (r - 2 * j) * (A ^ 2) ^ j :=
                IdentAux.norm_mul (IdentAux.norm_pow (hlin i) _) (IdentAux.norm_pow hS _)
            _ = A ^ r := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ (2 * r : ℝ) ^ r * A ^ r := by
          rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (hermCoeff_sum_bound hr1) (by positivity)
      _ = _ := (mul_pow ..).symm
  calc _ ≤ ∑ i, D.weight i * (2 * r * A) ^ r := by
        apply (SoS.coeffNorm1_sum_le _ _).trans
        exact sum_le_sum fun i _ ↦ by
          rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (hw i)]
          exact mul_le_mul_of_nonneg_left (ht i) (hw i)
    _ = (2 * r * A) ^ r := by rw [← sum_mul, hs, one_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by
          have hrR : (r : ℝ) ≤ 4 * t := by exact_mod_cast hr
          nlinarith) _

/-- The weight floor and isotropy bound every coordinate of a component mean. -/
theorem mean_entry {k d : ℕ} (D : Data k d) (w : ℚ) (γ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hD : D.Valid (w / 2) γ) (i : Fin k) (j : Fin d) :
    |D.mean i j| ≤ (⌈8 / w⌉₊ : ℝ) := by
  let v : Vec d := Pi.single j 1
  have hn : sqnorm v = 1 := by simp [v, sqnorm, dotProduct_single]
  have hq : eval v (Q D) = ∑ l, D.weight l * D.mean l j ^ 2 := by
    rw [Q, ApproxAux.eval_quad]
    simp [qform, between, v, pow_two, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply]
  have hup := (SoS.isSumSq_map (eval v) (sos_bounds D (w / 2) γ hD).2.2.2).nonneg
  simp only [map_sub, map_mul, eval_C, ApproxAux.eval_nsq, hn, mul_one, hq] at hup
  have hweight (l : Fin k) : 0 ≤ D.weight l := hD.1.1.le.trans (hD.1.2.1 l)
  have hterm : D.weight i * D.mean i j ^ 2 ≤ 2 := by
    have hsingle := single_le_sum (s := univ) (f := fun l ↦ D.weight l * D.mean l j ^ 2)
      (fun l _ ↦ mul_nonneg (hweight l) (sq_nonneg _)) (mem_univ i)
    linarith [hD.2.2]
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR' : (w : ℝ) ≤ 1 / 2 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr hw.2
    norm_num at h ⊢
    exact h
  have hsq : D.mean i j ^ 2 ≤ 4 / (w : ℝ) := by
    apply (le_div_iff₀ hwR).mpr
    have hi : (w : ℝ) / 2 ≤ D.weight i := hD.1.2.1 i
    have := mul_le_mul_of_nonneg_right hi (sq_nonneg (D.mean i j))
    nlinarith
  have habs : |D.mean i j| ≤ 1 + 4 / (w : ℝ) := by
    have := sq_nonneg (|D.mean i j| - 1)
    nlinarith [sq_abs (D.mean i j)]
  have hdiv : 1 + 4 / (w : ℝ) ≤ 8 / (w : ℝ) := by
    apply (le_div_iff₀ hwR).mpr
    field_simp
    nlinarith
  exact habs.trans (hdiv.trans (by exact_mod_cast (Nat.le_ceil (8 / w))))

end

end ABBKS26.IdCov.NormsAux
