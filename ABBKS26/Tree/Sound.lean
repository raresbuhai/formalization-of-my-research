module

public import ABBKS26.Tree.SoundAux
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Population windows and arbitrary-split soundness

Gaussian population windows and the deterministic leakage argument for verified splits.
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section


open Matrix

open Common MeasureTheory
open scoped NNReal
variable {n k d : ℕ}

def ScaleValid (M : Mixture k d) (I : Finset (Fin k)) (p : StepParams)
    (e : Edge n d) : Prop :=
  e.lower ≤ e.threshold ∧ e.threshold ≤ e.upper ∧
  match e.kind with
  | .spectral => (p.windowMass : ℝ) ≤ 1 / 2 ∧
      32 / p.straddle ≤ p.K ∧ M.IsCentered ∧ 0 < e.threshold ∧
      e.lower = e.threshold / p.K ^ 2 ∧ e.upper = e.threshold * p.K ^ 2 ∧
      ∃ v : Fin d → ℚ, ∀ x, e.statistic.evalQ x = (v ⬝ᵥ x) ^ 2
  | .frobenius => (p.windowMass : ℝ) ≤ 1 / 2 ∧
      e.lower = e.threshold - p.WF ∧ e.upper = e.threshold + p.WF ∧
      ∀ j ∈ I, ProbabilityTheory.variance
        (fun y : EuclideanSpace ℝ (Fin d) ↦ e.statistic.eval y.ofLp)
        (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
          (40 / (p.w : ℝ)) ^ 2
  | .mean => (p.windowMass : ℝ) ≤
      (1 / (16 * k : ℝ)) * (p.straddle / 2) ^ 9 / 16 ∧ e.lower = e.threshold - 1 / (16 * k) ∧
      e.upper = e.threshold + 1 / (16 * k) ∧ e.statistic.A = 0 ∧
      ∀ j ∈ I, qform (M.S j) (fun i ↦ (e.statistic.b i : ℝ)) ≤ 4

def SoundConditions (p : StepParams) (ε η Φ : ℝ) : Prop :=
  0 < p.w ∧ 0 < p.straddle ∧ p.straddle ≤ Real.exp (-2) ∧
    Φ ≤ p.windowMass / 100 ∧ ε + η ≤ p.w * p.windowMass / 100 ∧
    η ≤ p.windowMass / 100 ∧ Φ + p.straddle + 8 * η + ε + η < p.w / 4 ∧
    p.verifyMass = p.w * p.windowMass / 8 ∧
    η ≤ (p.straddle : ℝ) ^ 2 / (1000 * (p.K : ℝ) ^ 2) ∧
    8 * (40 / (p.w : ℝ)) / Real.sqrt p.straddle ≤ p.WF

private theorem scale_mass_le_half (M : Mixture k d) (I : Finset (Fin k)) (p : StepParams)
    (e : Edge n d) (hI : I.Nonempty) (hφ : 0 < (p.straddle : ℝ) ∧ (p.straddle : ℝ) ≤ 1)
    (hscale : ScaleValid M I p e) : (p.windowMass : ℝ) ≤ 1 / 2 := by
  obtain ⟨j, _⟩ := hI
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr j.pos)
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hh := hscale.2.2
  cases he : e.kind with
  | spectral => simp only [he] at hh; exact hh.1
  | frobenius => simp only [he] at hh; exact hh.1
  | mean =>
    simp only [he] at hh
    have hp : ((p.straddle : ℝ) / 2) ^ 9 ≤ 1 := pow_le_one₀
      (by linarith only [hφ.1]) (by linarith only [hφ.2])
    calc (p.windowMass : ℝ) ≤ (1 / (16 * k : ℝ)) * (p.straddle / 2) ^ 9 / 16 := hh.1
      _ ≤ (1 / (16 * k : ℝ)) * 1 / 16 := by gcongr
      _ ≤ (1 / 16 : ℝ) * 1 / 16 := by
        gcongr
        exact_mod_cast (by nlinarith only [hk] : (16 : ℝ) ≤ 16 * (k : ℝ))
      _ ≤ 1 / 2 := by norm_num

/-- Expanded straddling forces mass in the shrunken logarithmic Gaussian window. -/
theorem gaussian_square_window
    (φ η K t : ℝ) (hφ : 0 < φ ∧ φ ≤ Real.exp (-2)) (hη : 0 ≤ η)
    (hK : 32 / φ ≤ K) (hsmall : η ≤ φ ^ 2 / (1000 * K ^ 2))
    (hleft : φ + η ≤ (ProbabilityTheory.gaussianReal 0 1).real {z | z ^ 2 ≤ t + 3 * η})
    (hright : φ + η ≤ (ProbabilityTheory.gaussianReal 0 1).real {z | t - 3 * η < z ^ 2}) :
    1 / 2 ≤ (ProbabilityTheory.gaussianReal 0 1).real
      {z | t / K ^ 2 + 3 * η ≤ z ^ 2 ∧ z ^ 2 ≤ t * K ^ 2 - 3 * η} := by
  have hφ1 : φ ≤ 1 := hφ.2.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hφ0 := hφ.1
  have hKφ : 32 ≤ K * φ := (div_le_iff₀ hφ.1).mp hK
  have hK0 : 0 < K := (by positivity : 0 < 32 / φ).trans_le hK
  have hK32 : 32 ≤ K := by nlinarith
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hηK : 1000 * η * K ^ 2 ≤ φ ^ 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 1000 * K ^ 2)).mp hsmall
    nlinarith only [this]
  have hηφ : 1000 * η ≤ φ ^ 2 := by
    nlinarith only [hηK, mul_nonneg hη (sub_nonneg.mpr hKsq)]
  have hφsq : φ ^ 2 ≤ 1 := by nlinarith only [hφ0, hφ1]
  have hη1 : η ≤ 1 / 1000 := by linarith only [hηφ, hφsq]
  have ha := Population.gaussianReal_zero_abs_le_le (v := 1) one_ne_zero
    (Real.sqrt_nonneg (t + 3 * η))
  have hsub : {z : ℝ | z ^ 2 ≤ t + 3 * η} ⊆
      {z | |z| ≤ Real.sqrt (t + 3 * η)} := by
    intro z hz
    exact Real.abs_le_sqrt hz
  have haφ : φ ≤ Real.sqrt (t + 3 * η) := by
    have := hleft.trans ((measureReal_mono hsub).trans ha)
    norm_num at this
    linarith
  have htη : φ ^ 2 ≤ t + 3 * η := by
    have hs := Real.sq_sqrt ((Real.sqrt_pos.mp (hφ.1.trans_le haφ)).le)
    nlinarith only [hs, haφ, hφ0]
  have htlo : φ ^ 2 / 2 ≤ t := by nlinarith only [htη, hηφ, sq_nonneg φ]
  have htη0 : 0 < t - 3 * η := by
    nlinarith only [htη, hηφ, sq_pos_of_pos hφ0]
  have hb := Population.gaussianReal_zero_abs_ge_le (v := 1)
    (Real.sqrt_pos.mpr htη0)
  have hsub' : {z : ℝ | t - 3 * η < z ^ 2} ⊆
      {z | Real.sqrt (t - 3 * η) ≤ |z|} := by
    intro z hz
    apply (Real.sqrt_le_left (abs_nonneg z)).mpr
    simpa only [sq_abs] using le_of_lt hz
  have hbφ : φ ≤ 1 / (t - 3 * η) := by
    have := hright.trans ((measureReal_mono hsub').trans hb)
    rw [Real.sq_sqrt htη0.le] at this
    norm_num only [NNReal.coe_one, one_div] at this ⊢
    linarith only [this, hη]
  have htup : φ * t ≤ 2 := by
    have := (le_div_iff₀ htη0).mp hbφ
    have hh : η * φ ≤ 1 / 1000 := by nlinarith only [hη1, hφ1, hη]
    nlinarith only [this, hh]
  have hlow : t / K ^ 2 + 3 * η ≤ (1 / 8 : ℝ) ^ 2 := by
    rw [div_add' _ _ _ (by positivity : K ^ 2 ≠ 0),
      div_le_iff₀ (by positivity : 0 < K ^ 2)]
    have hKφ' : 32 * K ≤ φ * K ^ 2 := by
      nlinarith only [mul_nonneg hK0.le (sub_nonneg.mpr hKφ)]
    have htK : t ≤ K ^ 2 / 512 := by
      nlinarith only [hKφ', hK32, htup, hφ0]
    nlinarith only [htK, hηK, hφsq, hK32]
  have hhigh : 4 ^ 2 ≤ t * K ^ 2 - 3 * η := by
    have hprod : 1024 ≤ φ ^ 2 * K ^ 2 := by
      nlinarith only [hKφ, sq_nonneg (K * φ - 32)]
    have htK : φ ^ 2 * K ^ 2 / 2 ≤ t * K ^ 2 := by
      nlinarith only [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr htlo)]
    linarith only [hprod, htK, hη1]
  have hlo := Population.gaussianReal_zero_abs_le_le (v := 1) one_ne_zero
    (t := 1 / 8) (by norm_num)
  have hhi := Population.gaussianReal_zero_abs_ge_le (v := 1) (t := 4) (by norm_num)
  have hcover := Population.one_le_measureReal_add (P := ProbabilityTheory.gaussianReal 0 1)
    (s := {z | t / K ^ 2 + 3 * η ≤ z ^ 2 ∧ z ^ 2 ≤ t * K ^ 2 - 3 * η})
    (t := {z | |z| ≤ 1 / 8} ∪ {z | 4 ≤ |z|}) (fun z ↦ by
      by_cases hz : t / K ^ 2 + 3 * η ≤ z ^ 2 ∧ z ^ 2 ≤ t * K ^ 2 - 3 * η
      · exact Or.inl hz
      · right
        by_cases hlz : t / K ^ 2 + 3 * η ≤ z ^ 2
        · right
          have hh : t * K ^ 2 - 3 * η < z ^ 2 :=
            lt_of_not_ge (fun h ↦ hz ⟨hlz, h⟩)
          change 4 ≤ |z|
          nlinarith only [hh, hhigh, sq_abs z, abs_nonneg z]
        · left
          have : z ^ 2 < t / K ^ 2 + 3 * η := lt_of_not_ge hlz
          change |z| ≤ 1 / 8
          nlinarith only [this, hlow, sq_abs z, abs_nonneg z])
  have hu := measureReal_union_le (μ := ProbabilityTheory.gaussianReal 0 1)
    {z : ℝ | |z| ≤ 1 / 8} {z | 4 ≤ |z|}
  norm_num at hlo hhi
  linarith only [hcover, hu, hlo, hhi]

private theorem gaussian_threshold_bound (m σ φ τ : ℝ) (hσ : 0 < σ) (hφ : 0 < φ)
    (hl : φ ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real {z | z ≤ τ})
    (hr : φ ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real {z | τ < z}) :
    (τ - m) ^ 2 ≤ 2 * σ ^ 2 * Real.log (1 / φ) := by
  let v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hvcoe : (v : ℝ) = σ ^ 2 := rfl
  change φ ≤ (ProbabilityTheory.gaussianReal m v).real {z | z ≤ τ} at hl
  change φ ≤ (ProbabilityTheory.gaussianReal m v).real {z | τ < z} at hr
  have he : φ ≤ Real.exp (-((τ - m) ^ 2 / (2 * σ ^ 2))) := by
    by_cases ht : m ≤ τ
    · have h := ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := ProbabilityTheory.gaussianReal m v) (X := fun z : ℝ ↦ z) τ
        (t := (τ - m) / σ ^ 2) (by positivity)
        (ProbabilityTheory.integrable_exp_mul_gaussianReal _)
      rw [ProbabilityTheory.mgf_fun_id_gaussianReal, ← Real.exp_add] at h
      have heq : -((τ - m) / σ ^ 2) * τ +
          (m * ((τ - m) / σ ^ 2) + σ ^ 2 * ((τ - m) / σ ^ 2) ^ 2 / 2) =
          -((τ - m) ^ 2 / (2 * σ ^ 2)) := by
        field_simp
        ring
      rw [hvcoe] at h
      rw [heq] at h
      have hsub : {z : ℝ | τ < z} ⊆ {z | τ ≤ z} := by
        intro z hz
        change τ < z at hz
        exact hz.le
      exact hr.trans ((measureReal_mono hsub).trans h)
    · have h := ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := ProbabilityTheory.gaussianReal m v) (X := fun z : ℝ ↦ z) τ
        (t := (τ - m) / σ ^ 2) (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg σ))
        (ProbabilityTheory.integrable_exp_mul_gaussianReal _)
      rw [ProbabilityTheory.mgf_fun_id_gaussianReal, ← Real.exp_add] at h
      have heq : -((τ - m) / σ ^ 2) * τ +
          (m * ((τ - m) / σ ^ 2) + σ ^ 2 * ((τ - m) / σ ^ 2) ^ 2 / 2) =
          -((τ - m) ^ 2 / (2 * σ ^ 2)) := by
        field_simp
        ring
      rw [hvcoe] at h
      rw [heq] at h
      exact hl.trans h
  have hh := Real.log_le_log hφ he
  rw [Real.log_exp] at hh
  have hh' : (τ - m) ^ 2 / (2 * σ ^ 2) ≤ -Real.log φ := by linarith only [hh]
  rw [div_le_iff₀ (by positivity : 0 < 2 * σ ^ 2)] at hh'
  rw [one_div, Real.log_inv]
  nlinarith only [hh']

/-- A Gaussian straddling a threshold has polynomially bounded local window mass. -/
theorem gaussian_linear_window
    (m σ W φ : ℝ) (hσ : 0 < σ) (hW : 0 < W)
    (hφ : 0 < φ ∧ φ ≤ Real.exp (-2)) (τ : ℝ)
    (hl : φ ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real {z | z ≤ τ})
    (hr : φ ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real {z | τ < z}) :
    min (1 / 2) (0.7 * W * φ ^ 9 / σ) ≤
      (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real {z | |z - τ| ≤ W} := by
  let v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hvcoe : (v : ℝ) = σ ^ 2 := rfl
  let ℓ := Real.sqrt (2 * Real.log (1 / φ))
  have hφ0 := hφ.1
  have hlog : 2 ≤ Real.log (1 / φ) := by
    have hh := Real.log_le_log hφ0 hφ.2
    rw [Real.log_exp] at hh
    rw [one_div, Real.log_inv]
    linarith only [hh]
  have hℓsq : ℓ ^ 2 = 2 * Real.log (1 / φ) := Real.sq_sqrt (by linarith)
  have hℓ0 : 0 ≤ ℓ := Real.sqrt_nonneg _
  have hℓ2 : 2 ≤ ℓ := by nlinarith only [hℓsq, hℓ0, hlog]
  have hdist : |τ - m| ≤ σ * ℓ := by
    have hh := gaussian_threshold_bound m σ φ τ hσ hφ0 hl hr
    have hs : 0 ≤ σ * ℓ := mul_nonneg hσ.le hℓ0
    nlinarith only [hh, hℓsq, hs, sq_abs (τ - m), abs_nonneg (τ - m)]
  by_cases hlarge : σ * ℓ ≤ W / 2
  · apply (min_le_left _ _).trans
    have htwo : 2 * σ + |τ - m| ≤ W := by
      nlinarith only [hlarge, hdist, hℓ2, hσ]
    have hc := Population.gaussianReal_abs_ge_le m v (t := 2 * σ) (by positivity)
    have hcover := Population.one_le_measureReal_add (P := ProbabilityTheory.gaussianReal m v)
      (s := {z | |z - τ| ≤ W}) (t := {z | 2 * σ ≤ |z - m|}) (fun z ↦ by
        by_cases hz : |z - τ| ≤ W
        · exact Or.inl hz
        · right
          have hh := abs_sub_le z m τ
          rw [abs_sub_comm m τ] at hh
          change 2 * σ ≤ |z - m|
          linarith only [hz, hh, htwo])
    have hc' : (ProbabilityTheory.gaussianReal m v).real {z | 2 * σ ≤ |z - m|} ≤
        1 / 4 := by
      refine hc.trans_eq ?_
      rw [hvcoe]
      field_simp
      norm_num
    linarith only [hc', hcover]
  · apply (min_le_right _ _).trans
    have hsmall : W < 2 * σ * ℓ := by linarith only [hlarge]
    have hpdf (z : ℝ) (hz : z ∈ Set.Icc (τ - W) (τ + W)) :
        φ ^ 9 / (Real.sqrt (2 * Real.pi) * σ) ≤ ProbabilityTheory.gaussianPDFReal m v z := by
      have hzt : |z - τ| ≤ W := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
      have hzm : |z - m| ≤ 3 * σ * ℓ := by
        have hh := abs_sub_le z τ m
        linarith only [hh, hdist, hzt, hsmall]
      have he : 9 * Real.log φ ≤ -(z - m) ^ 2 / (2 * σ ^ 2) := by
        have hh : (z - m) ^ 2 ≤ 9 * σ ^ 2 * ℓ ^ 2 := by
          nlinarith only [hzm, abs_nonneg (z - m), hσ, hℓ0, sq_abs (z - m)]
        rw [le_div_iff₀ (by positivity : 0 < 2 * σ ^ 2)]
        have hℓ' : ℓ ^ 2 = -(2 * Real.log φ) := by
          simpa only [one_div, Real.log_inv, mul_neg] using hℓsq
        nlinarith only [hh, hℓ']
      have he' : φ ^ 9 ≤ Real.exp (-(z - m) ^ 2 / (2 * σ ^ 2)) := by
        calc φ ^ 9 = Real.exp (9 * Real.log φ) := by
              simpa only [Nat.cast_ofNat, Real.exp_log hφ0] using
                (Real.exp_nat_mul (Real.log φ) 9).symm
          _ ≤ _ := Real.exp_le_exp.mpr he
      have hden : Real.sqrt (2 * Real.pi * (v : ℝ)) = Real.sqrt (2 * Real.pi) * σ := by
        rw [Real.sqrt_mul (by positivity), show (v : ℝ) = σ ^ 2 from rfl,
          Real.sqrt_sq hσ.le]
      rw [ProbabilityTheory.gaussianPDFReal, hden, hvcoe, div_eq_mul_inv,
        mul_comm ((Real.sqrt (2 * Real.pi) * σ)⁻¹)]
      exact mul_le_mul_of_nonneg_right he' (by positivity)
    have hS : {z : ℝ | |z - τ| ≤ W} = Set.Icc (τ - W) (τ + W) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    have hv : v ≠ 0 := by
      apply NNReal.coe_ne_zero.mp
      exact pow_ne_zero _ hσ.ne'
    have hi : 2 * W * (φ ^ 9 / (Real.sqrt (2 * Real.pi) * σ)) ≤
        (ProbabilityTheory.gaussianReal m v).real {z | |z - τ| ≤ W} := by
      rw [hS, measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral _ hv,
        ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
          fun z _ ↦ ProbabilityTheory.gaussianPDFReal_nonneg m v z)]
      calc 2 * W * (φ ^ 9 / (Real.sqrt (2 * Real.pi) * σ)) =
          ∫ _z in Set.Icc (τ - W) (τ + W), φ ^ 9 / (Real.sqrt (2 * Real.pi) * σ) := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
        _ ≤ _ := setIntegral_mono_on (integrableOn_const (by simp))
          (ProbabilityTheory.integrable_gaussianPDFReal m v).integrableOn measurableSet_Icc
          hpdf
    refine le_trans ?_ hi
    have hpi : 0.7 * Real.sqrt (2 * Real.pi) ≤ 2 := by
      have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith only [hs, Real.pi_lt_four, Real.sqrt_nonneg (2 * Real.pi)]
    rw [div_le_iff₀ hσ]
    have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have heq : 2 * W * (φ ^ 9 / (Real.sqrt (2 * Real.pi) * σ)) * σ =
        2 * W * φ ^ 9 / Real.sqrt (2 * Real.pi) := by field_simp
    rw [heq, le_div_iff₀ hs]
    nlinarith only [mul_nonneg (by positivity : 0 ≤ W * φ ^ 9)
      (sub_nonneg.mpr hpi)]

private theorem gaussian_expanded_linear_window
    (m σ φ W τ r η : ℝ) (hσ : 0 < σ) (hW : 0 < W)
    (hφ : 0 < φ ∧ φ ≤ Real.exp (-2)) (hr : 0 ≤ r ∧ r ≤ 2 * η * σ)
    (hηφ : η ≤ φ / 2) (hrW : r ≤ W / 2)
    (hl : φ + η ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real
      {z | z ≤ τ + r})
    (hu : φ + η ≤ (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real
      {z | τ - r < z}) :
    min (1 / 2) (0.7 * (W / 2) * (φ / 2) ^ 9 / σ) ≤
      (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, by positivity⟩).real
        {z | τ - W + r ≤ z ∧ z ≤ τ + W - r} := by
  let v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hv : v ≠ 0 := NNReal.coe_ne_zero.mp (pow_ne_zero _ hσ.ne')
  have hc := Population.gaussianReal_abs_sub_le_le m τ hv hr.1
  have hroot : Real.sqrt (v : ℝ) = σ := Real.sqrt_sq hσ.le
  rw [hroot] at hc
  have hc' : (ProbabilityTheory.gaussianReal m v).real {z | |z - τ| ≤ r} ≤ 2 * η :=
    hc.trans ((div_le_iff₀ hσ).mpr hr.2)
  have hleft : φ / 2 ≤ (ProbabilityTheory.gaussianReal m v).real {z | z ≤ τ} := by
    have hsub : {z : ℝ | z ≤ τ + r} ⊆ {z | z ≤ τ} ∪ {z | |z - τ| ≤ r} := by
      intro z hz
      change z ≤ τ + r at hz
      by_cases ht : z ≤ τ
      · exact Or.inl ht
      · right
        change |z - τ| ≤ r
        rw [abs_of_nonneg (by linarith only [ht])]
        linarith only [hz]
    have hh := (measureReal_mono (μ := ProbabilityTheory.gaussianReal m v) hsub).trans
      (measureReal_union_le _ _)
    linarith only [hh, hc', hl, hηφ]
  have hright : φ / 2 ≤ (ProbabilityTheory.gaussianReal m v).real {z | τ < z} := by
    have hsub : {z : ℝ | τ - r < z} ⊆ {z | τ < z} ∪ {z | |z - τ| ≤ r} := by
      intro z hz
      change τ - r < z at hz
      by_cases ht : τ < z
      · exact Or.inl ht
      · right
        change |z - τ| ≤ r
        rw [abs_of_nonpos (by linarith only [ht])]
        linarith only [hz]
    have hh := (measureReal_mono (μ := ProbabilityTheory.gaussianReal m v) hsub).trans
      (measureReal_union_le _ _)
    linarith only [hh, hc', hu, hηφ]
  have hh := gaussian_linear_window m σ (W / 2) (φ / 2) hσ (by positivity)
    ⟨by linarith only [hφ.1], by linarith only [hφ.1, hφ.2]⟩ τ hleft hright
  refine hh.trans (measureReal_mono (μ := ProbabilityTheory.gaussianReal m v) ?_)
  intro z hz
  change |z - τ| ≤ W / 2 at hz
  have ha := abs_le.mp hz
  constructor <;> linarith only [ha.1, ha.2, hrW]

/-- Any passing split of the required type preserves component leakage. -/
theorem split_sound
    (M : Mixture k d) (ε η Φ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (p : StepParams) (e : Edge n d) (I : Finset (Fin k))
    (hM : M.Valid) (hg : Good M ε p.w η D ω) (hr : IsRounding M (1 / n) r)
    (hI : I.Nonempty) (hl : leakage ω e.parent I ≤ Φ)
    (hw : ∀ j, (p.w : ℝ) ≤ M.w j) (hscale : ScaleValid M I p e)
    (hcond : SoundConditions p ε η Φ)
    (hn : (2 * radius d η + 2) / η ≤ n)
    (hv : Verify p (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e) :
    ∃ L R : Finset (Fin k), L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L ∪ R = I ∧
      leakage ω (e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) L ≤
        Φ + p.straddle + 8 * η ∧
      leakage ω (e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) R ≤
        Φ + p.straddle + 8 * η := by
  classical
  obtain ⟨j, hjI⟩ := hI
  rcases hcond with ⟨hwp, hφp, hφmax, hΦm, hξm, hηm, hsmall, hverify, hηK, hWF⟩
  have hφ0 : (0 : ℝ) < p.straddle := by exact_mod_cast hφp
  have hφ1 : (p.straddle : ℝ) ≤ 1 :=
    hφmax.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hη0 := SoundAux.good_eta_pos M ε p.w η D ω hg j
  have hmass := scale_mass_le_half M I p e ⟨j, hjI⟩ ⟨hφ0, hφ1⟩ hscale
  have hη : 0 < η ∧ η ≤ 1 / 100 := ⟨hη0, by linarith only [hηm, hmass]⟩
  have hn0 : (0 : ℝ) < n := by
    have hcp := SoundAux.good_cluster_pos M ε p.w η D ω hg j
    have hcn := (Finset.card_le_card (Finset.subset_univ (cluster (labels ω) j))).trans_eq
      (Finset.card_fin n)
    exact Nat.cast_pos.mpr (hcp.trans_le hcn)
  apply (show (∃ L R : Finset (Fin k),
    L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L ∪ R = I ∧
    leakage ω (e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) L ≤
      Φ + (p.straddle + 8 * η) ∧
    leakage ω (e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) R ≤
      Φ + (p.straddle + 8 * η)) → _
    from by intro h; simpa only [add_assoc] using h)
  apply SoundAux.partition_leakage ω e.parent _ _ I Φ (p.straddle + 8 * η) (ε + η) p.w
    hl (by positivity) (split_partition _ _).2 hg.2.1 (by exact_mod_cast hv.2.1)
    (by exact_mod_cast hv.2.2) hn0 (by simpa only [add_assoc] using hsmall)
  apply SoundAux.component_small M ε η Φ D ω r p e I hM hg hr hη hn hl hwp hw hφp
    hΦm hηm hξm hverify hv
  intro a ha C hs hleft hright
  cases he : e.kind with
  | spectral =>
    have hh := hscale.2.2
    simp only [he] at hh
    obtain ⟨hwm, hKQ, hcenter, _, hlow, hhigh, v, hf⟩ := hh
    let V := qform (M.S a) (fun i ↦ (v i : ℝ))
    have hV : 0 ≤ V := (hM.posDef a).posSemidef.dotProduct_mulVec_nonneg _
    have hsv := C.variance
    rw [SoundAux.spectral_variance M hM hcenter a e.statistic v hf] at hsv
    have hV0 : 0 < V := by
      change C.s ^ 2 ≤ 2 * V ^ 2 at hsv
      nlinarith only [hsv, hs, hV]
    have hss : C.s ≤ 3 / 2 * V := by
      apply (pow_le_pow_iff_left₀ C.nonneg (by positivity) two_ne_zero).mp
      change C.s ^ 2 ≤ 2 * V ^ 2 at hsv
      nlinarith only [hsv, sq_nonneg V]
    have hmargin : 2 * η * C.s ≤ 3 * η * V := by nlinarith only [hss, hη0]
    have hmap := SoundAux.spectral_standard_map M hM hcenter a e.statistic v hf
    have hprob (q : ℝ → Prop) (hq : MeasurableSet {z | q z}) :
        (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ a)) (M.S a)).real
          {y | q (e.statistic.eval y.ofLp)} =
            (ProbabilityTheory.gaussianReal 0 1).real {z | q (V * z ^ 2)} := by
      rw [SoundAux.statistic_probability _ _ _ hmap q hq,
        map_measureReal_apply (by fun_prop) hq]
      rfl
    rw [hprob (fun z ↦ z ≤ (e.threshold : ℝ) + 2 * η * C.s)
      (measurableSet_le measurable_id measurable_const)] at hleft
    rw [hprob (fun z ↦ (e.threshold : ℝ) - 2 * η * C.s < z)
      (measurableSet_lt measurable_const measurable_id)] at hright
    have hτ : ((e.threshold : ℝ) / V) * V = e.threshold := div_mul_cancel₀ _ hV0.ne'
    have hl : (p.straddle : ℝ) + η ≤ (ProbabilityTheory.gaussianReal 0 1).real
        {z | z ^ 2 ≤ (e.threshold : ℝ) / V + 3 * η} := by
      refine hleft.trans (measureReal_mono ?_)
      intro z hz
      change V * z ^ 2 ≤ (e.threshold : ℝ) + 2 * η * C.s at hz
      change z ^ 2 ≤ (e.threshold : ℝ) / V + 3 * η
      nlinarith only [hz, hmargin, hτ, hV0]
    have hr' : (p.straddle : ℝ) + η ≤ (ProbabilityTheory.gaussianReal 0 1).real
        {z | (e.threshold : ℝ) / V - 3 * η < z ^ 2} := by
      refine hright.trans (measureReal_mono ?_)
      intro z hz
      change (e.threshold : ℝ) - 2 * η * C.s < V * z ^ 2 at hz
      change (e.threshold : ℝ) / V - 3 * η < z ^ 2
      nlinarith only [hz, hmargin, hτ, hV0]
    have hK : 32 / (p.straddle : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKQ
    have hK0 : (0 : ℝ) < p.K := (div_pos (by norm_num) hφ0).trans_le hK
    have hlowR : (e.lower : ℝ) = (e.threshold : ℝ) / (p.K : ℝ) ^ 2 := by
      exact_mod_cast hlow
    have hhighR : (e.upper : ℝ) = (e.threshold : ℝ) * (p.K : ℝ) ^ 2 := by
      exact_mod_cast hhigh
    have hlowid : V * (((e.threshold : ℝ) / V) / (p.K : ℝ) ^ 2) = e.lower := by
      rw [hlowR]
      field_simp
    have hhighid : V * (((e.threshold : ℝ) / V) * (p.K : ℝ) ^ 2) = e.upper := by
      rw [hhighR]
      field_simp
    rw [hprob (fun z ↦ (e.lower : ℝ) + 2 * η * C.s ≤ z ∧
      z ≤ (e.upper : ℝ) - 2 * η * C.s) ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const))]
    refine hwm.trans ((gaussian_square_window p.straddle η p.K ((e.threshold : ℝ) / V)
      ⟨hφ0, hφmax⟩ hη0.le hK hηK hl hr').trans (measureReal_mono ?_))
    intro z hz
    have hlo := mul_le_mul_of_nonneg_left hz.1 hV0.le
    have hhi := mul_le_mul_of_nonneg_left hz.2 hV0.le
    change (e.lower : ℝ) + 2 * η * C.s ≤ V * z ^ 2 ∧
      V * z ^ 2 ≤ (e.upper : ℝ) - 2 * η * C.s
    constructor <;> nlinarith only [hlo, hhi, hlowid, hhighid, hmargin]
  | frobenius =>
    have hh := hscale.2.2
    simp only [he] at hh
    obtain ⟨hwm, hlow, hhigh, hvar⟩ := hh
    have hwpR : (0 : ℝ) < p.w := by exact_mod_cast hwp
    have h40 : 0 < 40 / (p.w : ℝ) := by positivity
    have hss : C.s ≤ 40 / (p.w : ℝ) := by
      nlinarith only [C.variance, hvar a ha, C.nonneg, h40]
    have hlowR : (e.lower : ℝ) = (e.threshold : ℝ) - p.WF := by exact_mod_cast hlow
    have hhighR : (e.upper : ℝ) = (e.threshold : ℝ) + p.WF := by exact_mod_cast hhigh
    rw [hlowR, hhighR]
    apply hwm.trans
    exact SoundAux.expanded_variance_window _ _ (SoundAux.statistic_memLp M hM a e.statistic)
      p.straddle η (40 / (p.w : ℝ)) (2 * η * C.s) e.threshold p.WF ⟨hφ0, hφ1⟩ h40
      ⟨hη0.le, hη.2⟩ ⟨by positivity, by nlinarith only [hss, hη0]⟩ (hvar a ha) hWF
      (by linarith only [hleft, hη0]) (by linarith only [hright, hη0])
  | mean =>
    have hh := hscale.2.2
    simp only [he] at hh
    obtain ⟨hwm, hlow, hhigh, hA, hvar⟩ := hh
    let V := qform (M.S a) (fun i ↦ (e.statistic.b i : ℝ))
    let σ := Real.sqrt V
    let m := (fun i ↦ (e.statistic.b i : ℝ)) ⬝ᵥ M.μ a + e.statistic.c
    let W : ℝ := 1 / (16 * k)
    have hV : 0 ≤ V := (hM.posDef a).posSemidef.dotProduct_mulVec_nonneg _
    have hsv := C.variance
    rw [SoundAux.mean_variance M hM a e.statistic hA] at hsv
    have hV0 : 0 < V := by nlinarith only [hsv, hs]
    have hσ : 0 < σ := Real.sqrt_pos.mpr hV0
    have hσsq : σ ^ 2 = V := Real.sq_sqrt hV
    have hσ2 : σ ≤ 2 := by nlinarith only [hσsq, hvar a ha, hσ]
    have hss : C.s ≤ σ := by nlinarith only [hsv, hσsq, hs, hσ]
    have hss2 : C.s ≤ 2 := hss.trans hσ2
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr a.pos)
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
    have hW : 0 < W := by dsimp only [W]; positivity
    have hW1 : W ≤ 1 := by
      dsimp only [W]
      rw [div_le_one (by positivity)]
      nlinarith only [hk]
    have hp0 : 0 ≤ (p.straddle : ℝ) / 2 := by positivity
    have hp1 : (p.straddle : ℝ) / 2 ≤ 1 := by linarith only [hφ1]
    have hp : ((p.straddle : ℝ) / 2) ^ 9 ≤ 1 := pow_le_one₀ hp0 hp1
    have hp' : ((p.straddle : ℝ) / 2) ^ 9 ≤ (p.straddle : ℝ) / 2 :=
      pow_le_of_le_one hp0 hp1 (by norm_num)
    have hmassW : (p.windowMass : ℝ) ≤ W / 16 := by
      calc (p.windowMass : ℝ) ≤ W * (p.straddle / 2) ^ 9 / 16 := hwm
        _ ≤ W * 1 / 16 := by gcongr
        _ = W / 16 := by ring
    have hmassφ : (p.windowMass : ℝ) ≤ ((p.straddle : ℝ) / 2) / 16 := by
      calc (p.windowMass : ℝ) ≤ W * (p.straddle / 2) ^ 9 / 16 := hwm
        _ ≤ 1 * (p.straddle / 2) ^ 9 / 16 := by gcongr
        _ ≤ ((p.straddle : ℝ) / 2) / 16 :=
          div_le_div_of_nonneg_right (by simpa only [one_mul] using hp') (by norm_num)
    have hηφ : η ≤ (p.straddle : ℝ) / 2 := by
      linarith only [hηm, hmassφ, hφ0]
    have hrW : 2 * η * C.s ≤ W / 2 := by
      nlinarith only [hηm, hmassW, hss2, hη0]
    have hmap : (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ a)) (M.S a)).map
        (fun y ↦ e.statistic.eval y.ofLp) =
          ProbabilityTheory.gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ := by
      rw [SoundAux.mean_map M hM a e.statistic hA]
      change ProbabilityTheory.gaussianReal m V.toNNReal = _
      congr 1
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ hV]
      exact hσsq.symm
    have hprob (q : ℝ → Prop) (hq : MeasurableSet {z | q z}) :
        (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ a)) (M.S a)).real
          {y | q (e.statistic.eval y.ofLp)} =
            (ProbabilityTheory.gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩).real {z | q z} :=
      SoundAux.statistic_probability _ _ _ hmap q hq
    rw [hprob (fun z ↦ z ≤ (e.threshold : ℝ) + 2 * η * C.s)
      (measurableSet_le measurable_id measurable_const)] at hleft
    rw [hprob (fun z ↦ (e.threshold : ℝ) - 2 * η * C.s < z)
      (measurableSet_lt measurable_const measurable_id)] at hright
    have hlowR : (e.lower : ℝ) = (e.threshold : ℝ) - W := by
      dsimp only [W]
      have h := congrArg (fun q : ℚ ↦ (q : ℝ)) hlow
      push_cast at h
      exact h
    have hhighR : (e.upper : ℝ) = (e.threshold : ℝ) + W := by
      dsimp only [W]
      have h := congrArg (fun q : ℚ ↦ (q : ℝ)) hhigh
      push_cast at h
      exact h
    rw [hlowR, hhighR, hprob (fun z ↦ (e.threshold : ℝ) - W + 2 * η * C.s ≤ z ∧
      z ≤ (e.threshold : ℝ) + W - 2 * η * C.s)
        ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const))]
    have hmin : (p.windowMass : ℝ) ≤
        min (1 / 2) (0.7 * (W / 2) * ((p.straddle : ℝ) / 2) ^ 9 / σ) := by
      apply le_min hmass
      rw [le_div_iff₀ hσ]
      have hm := mul_le_mul_of_nonneg_right hwm hσ.le
      have hn' := mul_le_mul_of_nonneg_left hσ2
        (by positivity : 0 ≤ W * ((p.straddle : ℝ) / 2) ^ 9 / 16)
      have hprod : 0 ≤ W * ((p.straddle : ℝ) / 2) ^ 9 := by positivity
      change (p.windowMass : ℝ) * σ ≤ W * ((p.straddle : ℝ) / 2) ^ 9 / 16 * σ at hm
      nlinarith only [hm, hn', hprod]
    apply hmin.trans
    exact gaussian_expanded_linear_window m σ p.straddle W e.threshold (2 * η * C.s) η
      hσ hW ⟨hφ0, hφmax⟩ ⟨by positivity, by nlinarith only [hss, hη0]⟩ hηφ hrW
      hleft hright

end

end ABBKS26.Tree
