module

public import ABBKS26.Rounding.RC2

/-!
# The identical-covariance moment system

Generalized Hermite polynomials ([ABBKS26, Lemma 6.6]) and the moment constraint system of
[ABBKS26, Definition 6.7]. As a simplification, the projected moments are compared with
those of a Gaussian with the same second moment.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial Matrix
open scoped BigOperators
variable {k d : ℕ}

def hermCoeff (m i : ℕ) : ℕ := m.choose (2 * i) * Nat.doubleFactorial (2 * i - 1)

def hmom {K : Type} [CommRing K] (r : ℕ) (a v : K) : K :=
  ∑ i ∈ Finset.range (r / 2 + 1), (hermCoeff r i : K) * a ^ (r - 2 * i) * v ^ i


structure Data (k d : ℕ) where
  weight : Fin k → ℝ
  mean : Fin k → Vec d
  cov : Mat d

def Data.frame (D : Data k d) : FrameModel k d := ⟨D.weight, D.mean, fun _ ↦ D.cov⟩

def Data.Valid (D : Data k d) (w γ : ℝ) : Prop :=
  D.frame.Valid w ∧ D.frame.Isotropic γ ∧ γ ≤ 1 / 4

def between (D : Data k d) : Mat d :=
  ∑ i, D.weight i • vecMulVec (D.mean i) (D.mean i)

def Q (D : Data k d) : RPoly d := quad (between D)
def S (D : Data k d) : RPoly d := quad D.cov

def powerMoment (D : Data k d) (r : ℕ) : RPoly d :=
  ∑ i, C (D.weight i) * lin (D.mean i) ^ r

def moment (D : Data k d) (r : ℕ) : RPoly d :=
  ∑ i, C (D.weight i) * hmom r (lin (D.mean i)) (S D)

def alpha (s : ℕ) : ℝ := Nat.doubleFactorial (2 * s - 1)

def dev (M : ℕ → RPoly d) (s : ℕ) : RPoly d := M (2 * s) - C (alpha s) * M 2 ^ s

def constraint (M : ℕ → RPoly d) (ε : ℝ) (s : ℕ) : RPoly d :=
  C ε * nsq ^ (2 * s) - dev M s ^ 2

/-- Zero constraints are omitted; this preserves the nonconstant-constraint solver contract. -/
def system (M : ℕ → RPoly d) (t : ℕ) (ε : ℝ) : List (RPoly d) :=
  [1 - nsq] ++ ((List.range (2 * t - 1)).map (fun j ↦ constraint M ε (j + 2))).filter
    (fun p ↦ p ≠ 0)

def K (s : ℕ) : ℝ := ∑ j ∈ Finset.range (s - 1), (hermCoeff (2 * s) j : ℝ)

def momentCertificate (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (η : ℝ) : Prop :=
  (∀ s, 1 ≤ s → s ≤ 2 * t → (M (2 * s)).IsHomogeneous (2 * s)) ∧
  ∀ s, 1 ≤ s → s ≤ 2 * t →
    IsSumSq (C η * nsq ^ (2 * s) - (M (2 * s) - moment D (2 * s)) ^ 2)

-- The coefficient and variance-addition arguments below are local adaptations of
-- BS23/Common/HermiteFacts.lean; no other paper is imported.
open Finset
open scoped Nat

private theorem hermCoeff_eq_zero {m i : ℕ} (h : m < 2 * i) : hermCoeff m i = 0 := by
  simp [hermCoeff, Nat.choose_eq_zero_of_lt h]

private theorem hermCoeff_zero_right (m : ℕ) : hermCoeff m 0 = 1 := by simp [hermCoeff]


private theorem doubleFactorial_two_mul_sub_one_mul (i : ℕ) :
    (2 * i - 1)‼ * (2 ^ i * i !) = (2 * i)! := by
  cases i with
  | zero => rfl
  | succ i =>
    have h1 := Nat.doubleFactorial_two_mul (i + 1)
    have h2 := Nat.factorial_eq_mul_doubleFactorial (2 * i + 1)
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, ← h1, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
      h2, mul_comm]

/-- `c_{m,i} · 2^i · i! · (m-2i)! = m!`. -/
private theorem hermCoeff_mul_factorial {m i : ℕ} (h : 2 * i ≤ m) :
    hermCoeff m i * (2 ^ i * i ! * (m - 2 * i)!) = m ! := by
  rw [hermCoeff]
  calc m.choose (2 * i) * (2 * i - 1)‼ * (2 ^ i * i ! * (m - 2 * i)!)
      = m.choose (2 * i) * ((2 * i - 1)‼ * (2 ^ i * i !)) * (m - 2 * i)! := by ring
    _ = m ! := by rw [doubleFactorial_two_mul_sub_one_mul, Nat.choose_mul_factorial_mul_factorial h]

/-- The coefficient identity behind `hmom_add_var`. -/
private theorem hermCoeff_add_mul_choose (m l j : ℕ) :
    hermCoeff m (l + j) * (l + j).choose j = hermCoeff m l * hermCoeff (m - 2 * l) j := by
  rcases lt_or_ge m (2 * (l + j)) with h | h
  · rw [hermCoeff_eq_zero h, zero_mul]
    rcases lt_or_ge m (2 * l) with h' | h'
    · rw [hermCoeff_eq_zero h', zero_mul]
    · rw [hermCoeff_eq_zero (show m - 2 * l < 2 * j by omega), mul_zero]
  · have hF : 0 < 2 ^ (l + j) * l ! * j ! * (m - 2 * (l + j))! := by positivity
    refine Nat.eq_of_mul_eq_mul_right hF ?_
    have e1 : hermCoeff m (l + j) * (l + j).choose j * (2 ^ (l + j) * l ! * j ! *
        (m - 2 * (l + j))!) = hermCoeff m (l + j) * (2 ^ (l + j) * ((l + j).choose j * l ! * j !)
        * (m - 2 * (l + j))!) := by ring
    have e2 : hermCoeff m l * hermCoeff (m - 2 * l) j * (2 ^ (l + j) * l ! * j ! *
        (m - 2 * (l + j))!) = hermCoeff m l * (hermCoeff (m - 2 * l) j * (2 ^ j * j ! *
        (m - 2 * l - 2 * j)!)) * (2 ^ l * l !) := by
      rw [show m - 2 * l - 2 * j = m - 2 * (l + j) by omega]; ring
    rw [e1, e2, Nat.add_choose_mul_factorial_mul_factorial, hermCoeff_mul_factorial h,
      hermCoeff_mul_factorial (by omega), mul_assoc, mul_comm ((m - 2 * l)!),
      hermCoeff_mul_factorial (by omega)]

private theorem hmom_zero {K : Type} [CommRing K] (a v : K) :
    hmom 0 a v = 1 := by
  simp [hmom, hermCoeff]

private theorem hmom_two {K : Type} [CommRing K] (a v : K) :
    hmom 2 a v = a ^ 2 + v := by
  simp [hmom, sum_range_succ, hermCoeff]

private theorem hmom_zero_var {K : Type} [CommRing K] (r : ℕ) (a : K) :
    hmom r a 0 = a ^ r := by
  rw [hmom, Finset.sum_eq_single 0]
  · simp [hermCoeff_zero_right]
  · intro i _ hi
    simp [hi]
  · simp

private theorem hmom_even_zero {K : Type} [CommRing K] (s : ℕ) (v : K) :
    hmom (2 * s) 0 v = (Nat.doubleFactorial (2 * s - 1) : K) * v ^ s := by
  rw [hmom, Finset.sum_eq_single s]
  · simp [hermCoeff]
  · intro i hi hne
    have hi' : i < s := by simp only [mem_range] at hi; omega
    simp [zero_pow (show 2 * s - 2 * i ≠ 0 by omega)]
  · simp

private theorem hmom_add_var {K : Type} [CommRing K] (m : ℕ) (a u v : K) :
    hmom m a (u + v) =
      ∑ l ∈ range (m / 2 + 1), (hermCoeff m l : K) * v ^ l * hmom (m - 2 * l) a u := by
  simp only [hmom, add_pow, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine Finset.sum_nbij' (fun x ↦ ⟨x.1 - x.2, x.2⟩) (fun y ↦ ⟨y.1 + y.2, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · rintro ⟨l, j⟩ hy
    simp only [mem_sigma, mem_range] at hy ⊢
    omega
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨l, j⟩ _
    simp
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx
    obtain ⟨l, rfl⟩ : ∃ l, i = l + j := ⟨i - j, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hc := congrArg (Nat.cast : ℕ → K) (hermCoeff_add_mul_choose m l j)
    push_cast at hc
    rw [show m - 2 * l - 2 * j = m - 2 * (l + j) by omega]
    linear_combination (a ^ (m - 2 * (l + j)) * u ^ j * v ^ l) * hc

private theorem heat_hmom {K : Type} [CommRing K] (m : ℕ) (a q v : K) :
    (∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : K) * q ^ i *
      hmom (m - 2 * i) a v) = hmom m a (v - q) := by
  rw [sub_eq_add_neg, hmom_add_var]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [neg_pow]
  ring

private def quadLinear : Mat d →ₗ[ℝ] RPoly d where
  toFun := quad
  map_add' A B := by
    simp [quad, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [quad, Matrix.smul_apply, smul_eq_C_mul, Finset.mul_sum, mul_assoc]

private theorem quad_vecMulVec (a : Vec d) : quad (vecMulVec a a) = lin a ^ 2 := by
  simp only [quad, lin, pow_two, Finset.sum_mul_sum, vecMulVec_apply, C_mul]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

private theorem quad_between (D : Data k d) : Q D = powerMoment D 2 := by
  change quadLinear (∑ i, D.weight i • vecMulVec (D.mean i) (D.mean i)) = _
  simp only [map_sum, map_smul, smul_eq_C_mul]
  change (∑ i, C (D.weight i) * quad (vecMulVec (D.mean i) (D.mean i))) = _
  simp only [quad_vecMulVec, powerMoment]

/-- The second moment is common covariance plus the between-means matrix. -/
theorem second_moment
    (D : Data k d) (hs : ∑ i, D.weight i = 1) : moment D 2 = Q D + S D := by
  have hw : ∑ i, (C (D.weight i) : RPoly d) = 1 := by
    rw [← map_sum, hs, map_one]
  simp only [moment, hmom_two, mul_add, sum_add_distrib, ← sum_mul, hw, one_mul]
  rw [quad_between, powerMoment]

/-- The Hermite heat identity isolates the discrete mean moments. -/
theorem heat_identity
    (D : Data k d) (s : ℕ) :
    (∑ j ∈ Finset.range (s + 1), C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) *
      S D ^ j * moment D (2 * s - 2 * j)) = powerMoment D (2 * s) := by
  have hc (a : RPoly d) :
      (∑ j ∈ range (s + 1), C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) *
        S D ^ j * hmom (2 * s - 2 * j) a (S D)) = a ^ (2 * s) := by
    simpa only [show 2 * s / 2 = s by omega, map_mul, map_pow, map_neg, map_one,
      map_natCast, sub_self, hmom_zero_var] using heat_hmom (2 * s) a (S D) (S D)
  simp only [moment, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← hc (lin (D.mean i)), mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

/-- Applying the heat operator to the Gaussian reference leaves its excess variance. -/
theorem gaussian_reference
    (D : Data k d) (hs : ∑ i, D.weight i = 1) (s : ℕ) :
    (∑ j ∈ Finset.range (s + 1), C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) *
      S D ^ j * hmom (2 * s - 2 * j) 0 (moment D 2)) = C (alpha s) * Q D ^ s := by
  have h := heat_hmom (2 * s) (0 : RPoly d) (S D) (moment D 2)
  have he : moment D 2 - S D = Q D := by rw [second_moment D hs]; ring
  rw [he, hmom_even_zero] at h
  simpa only [show 2 * s / 2 = s by omega, map_mul, map_pow, map_neg, map_one,
    map_natCast, alpha] using h

/-- Moment mismatch equals a finite sum of system deviations. -/
theorem deviation_identity
    (D : Data k d) (hs : ∑ i, D.weight i = 1) (s : ℕ) :
    powerMoment D (2 * s) - C (alpha s) * Q D ^ s =
      ∑ j ∈ Finset.range (s - 1), C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) *
        S D ^ j * dev (moment D) (s - j) := by
  have h := congrArg₂ (fun a b : RPoly d ↦ a - b)
    (heat_identity D s) (gaussian_reference D hs s)
  rw [← sum_sub_distrib] at h
  rw [← h]
  have href (j : ℕ) : hmom (2 * s - 2 * j) (0 : RPoly d) (moment D 2) =
      C (alpha (s - j)) * moment D 2 ^ (s - j) := by
    rw [show 2 * s - 2 * j = 2 * (s - j) by omega, hmom_even_zero]
    simp only [alpha, map_natCast]
  have hlow (n : ℕ) (hn : n ≤ 1) : dev (moment D) n = 0 := by
    interval_cases n
    · simp [dev, alpha, moment, hmom_zero, ← map_sum, hs]
    · simp [dev, alpha]
  calc
    _ = ∑ j ∈ range (s + 1), C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) *
        S D ^ j * dev (moment D) (s - j) := by
      refine sum_congr rfl fun j _ ↦ ?_
      rw [href, dev, show 2 * (s - j) = 2 * s - 2 * j by omega]
      ring
    _ = _ := by
      symm
      apply sum_subset
      · intro j hj
        simp only [mem_range] at hj ⊢
        omega
      · intro j hj hj'
        simp only [mem_range, not_lt] at hj hj'
        rw [hlow (s - j) (by omega), mul_zero]

/-- Population moments and deviations have their expected homogeneous degrees. -/
theorem homogeneity
    (D : Data k d) (r s : ℕ) :
    (moment D r).IsHomogeneous r ∧ (dev (moment D) s).IsHomogeneous (2 * s) := by
  have hlin (a : Vec d) : (lin a).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ ↦ (isHomogeneous_X ℝ i).C_mul (a i)
  have hcov : (S D).IsHomogeneous 2 := by
    refine IsHomogeneous.sum _ _ _ fun i _ ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
    rw [mul_assoc]
    exact ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j)).C_mul _
  have hm (n : ℕ) : (moment D n).IsHomogeneous n := by
    refine IsHomogeneous.sum _ _ _ fun i _ ↦ IsHomogeneous.C_mul ?_ (D.weight i)
    unfold hmom
    refine IsHomogeneous.sum _ _ _ fun j hj ↦ ?_
    have hj' : 2 * j ≤ n := by simp only [mem_range] at hj; omega
    rw [← map_natCast (C : ℝ →+* RPoly d), mul_assoc]
    convert (((hlin (D.mean i)).pow (n - 2 * j)).mul (hcov.pow j)).C_mul
      (hermCoeff n j : ℝ) using 1
    omega
  refine ⟨hm r, (hm (2 * s)).sub ?_⟩
  convert ((hm 2).pow s).C_mul (alpha s) using 1

/-- Isotropy gives SoS bounds on the covariance and mean quadratic forms. -/
theorem sos_bounds
    (D : Data k d) (w γ : ℝ) (h : D.Valid w γ) :
    IsSumSq (S D) ∧ IsSumSq (Q D) ∧
      IsSumSq (C (1 + γ) * nsq - S D) ∧
      IsSumSq (C (1 + γ) * nsq - Q D) := by
  have hs : ∑ i, D.weight i = 1 := h.1.2.2.1
  have hk : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    subst k
    simp at hs
  have hcov : D.cov.PosSemidef := (h.1.2.2.2 ⟨0, hk⟩).posSemidef
  have hw (i : Fin k) : 0 ≤ D.weight i := h.1.1.le.trans (h.1.2.1 i)
  have hbet : (between D).PosSemidef := by
    apply posSemidef_sum
    intro i _
    have hi : (vecMulVec (D.mean i) (D.mean i)).PosSemidef := by
      simpa only [star_trivial] using posSemidef_vecMulVec_self_star (D.mean i)
    exact hi.smul (hw i)
  have hsecond : D.frame.second = D.cov + between D := by
    simp only [FrameModel.second, Data.frame, smul_add, sum_add_distrib,
      ← sum_smul, hs, one_smul, between]
  have hI : ((1 + γ) • (1 : Mat d)).IsHermitian :=
    (PosSemidef.one.smul (show 0 ≤ 1 + γ by linarith [h.2.1.1])).1
  have hup : ((1 + γ) • (1 : Mat d) - D.frame.second).PosSemidef := by
    have hsym : D.frame.second.IsHermitian := by
      rw [hsecond]
      exact hcov.1.add hbet.1
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hI.sub hsym) fun v ↦ ?_
    have hv := h.2.1.2.2 v
    simpa only [qform, sub_mulVec, dotProduct_sub, star_trivial, sub_nonneg] using hv
  have hgapS : ((1 + γ) • (1 : Mat d) - D.cov).PosSemidef := by
    have he : (1 + γ) • (1 : Mat d) - D.frame.second + between D =
        (1 + γ) • (1 : Mat d) - D.cov := by rw [hsecond]; abel
    rw [← he]
    exact hup.add hbet
  have hgapQ : ((1 + γ) • (1 : Mat d) - between D).PosSemidef := by
    have he : (1 + γ) • (1 : Mat d) - D.frame.second + D.cov =
        (1 + γ) • (1 : Mat d) - between D := by rw [hsecond]; abel
    rw [← he]
    exact hup.add hcov
  have hshift (A : Mat d) : quad ((1 + γ) • (1 : Mat d) - A) =
      C (1 + γ) * nsq - quad A := by
    change quadLinear ((1 + γ) • (1 : Mat d) - A) = _
    rw [map_sub, map_smul, smul_eq_C_mul]
    change C (1 + γ) * quad (1 : Mat d) - quad A = _
    have he : quad (1 : Mat d) = nsq := by
      simp [quad, nsq, Matrix.one_apply, pow_two, apply_ite, ite_mul]
    rw [he]
  refine ⟨SoSKit.psd_quad _ hcov, SoSKit.psd_quad _ hbet, ?_, ?_⟩
  · simpa only [hshift, S] using SoSKit.psd_quad _ hgapS
  · simpa only [hshift, Q] using SoSKit.psd_quad _ hgapQ

end

end ABBKS26.IdCov
