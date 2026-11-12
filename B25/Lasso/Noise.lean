module

public import B25.Model
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Gaussian noise

For `w ~ N(0, σ² Iₙ)` (`B25.noiseLaw`):

* `B25.noise_max_tail`: for a matrix whose columns have norm `√n`, each `⟨Xⱼ, w⟩` is
  `N(0, σ² n)`, so `P(⟨Xⱼ, w⟩² > 2 (1 + τ) σ² n log d) ≤ 2 d^(-(1+τ))` (the Gaussian tail
  `P(|Z| ≥ r) ≤ 2 e^(-r²/(2v))`, for instance from Mathlib's sub-Gaussian bounds for
  `gaussianReal`), and a union bound over the `d` columns gives `2 d^(-τ)`.
* `B25.noise_norm_tail`: `P(‖w‖₂² > 4 σ² n) ≤ e^(-n/4)`, the Chernoff bound for a chi-square
  variable: `E e^(λ g²) = (1 - 2λ)^(-1/2)` for `g ~ N(0, 1)` and `λ < 1/2`; at `λ = 3/8`,
  `P(∑ gᵢ² > 4n) ≤ e^(-3n/2) 2^n ≤ e^(-n/4)`.

`σ = 0` (the noise is `0`), `n = 0` and `d ≤ 1` are degenerate cases.
-/

@[expose] public section

namespace B25

open MeasureTheory ProbabilityTheory

namespace NZ

open scoped NNReal

/-- The identity is sub-Gaussian with parameter `v` under `N(0, v)`. -/
theorem subG_id_gaussZ (v : ℝ≥0) : HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by simp [mgf_id_gaussianReal]

/-- Under `n` independent copies of `N(0, v)`, a coordinate is sub-Gaussian with parameter
`v`. -/
theorem subG_coord_gaussZ {n : ℕ} (v : ℝ≥0) (i : Fin n) :
    HasSubgaussianMGF (fun w : Fin n → ℝ ↦ w i) v (Measure.pi fun _ ↦ gaussianReal 0 v) := by
  have hm : (Measure.pi fun _ : Fin n ↦ gaussianReal 0 v).map (fun w ↦ w i) =
      gaussianReal 0 v :=
    (measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 v) i).map_eq
  have hid : HasSubgaussianMGF id v
      ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 v).map (fun w ↦ w i)) := by
    rw [hm]
    exact subG_id_gaussZ v
  have hY : AEMeasurable (fun w : Fin n → ℝ ↦ w i) (Measure.pi fun _ ↦ gaussianReal 0 v) :=
    (measurable_pi_apply i).aemeasurable
  exact HasSubgaussianMGF.of_map hY hid

/-- Under `n` independent copies of `N(0, v)`, `∑ᵢ aᵢ wᵢ` is sub-Gaussian with parameter
`c = ∑ᵢ aᵢ² v`. -/
theorem subG_lin_gaussZ {n : ℕ} (v : ℝ≥0) (a : Fin n → ℝ) {c : ℝ≥0}
    (hc : (c : ℝ) = (∑ i, a i ^ 2) * v) :
    HasSubgaussianMGF (fun w : Fin n → ℝ ↦ ∑ i, a i * w i) c
      (Measure.pi fun _ ↦ gaussianReal 0 v) := by
  have hind : iIndepFun (fun i (w : Fin n → ℝ) ↦ a i * w i)
      (Measure.pi fun _ ↦ gaussianReal 0 v) :=
    iIndepFun_pi (X := fun i (x : ℝ) ↦ a i * x) fun i ↦ (measurable_const_mul (a i)).aemeasurable
  convert HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ)
    (fun i _ ↦ (subG_coord_gaussZ v i).const_mul (a i)) using 1
  apply NNReal.eq
  rw [hc, NNReal.coe_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ (NNReal.coe_mul ⟨a i ^ 2, sq_nonneg _⟩ v).symm

/-- Two-sided sub-Gaussian tail: `P(|Y| > ε) ≤ 2 e^(-ε²/(2c))`. -/
theorem abs_tail_subGZ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {c : ℝ≥0} (hY : HasSubgaussianMGF Y c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {w | ε < |Y w|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hsub : {w | ε < |Y w|} ⊆ {w | ε ≤ Y w} ∪ {w | ε ≤ (-Y) w} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply] at hw ⊢
    rcases le_or_gt 0 (Y w) with h | h
    · left
      rw [abs_of_nonneg h] at hw
      exact hw.le
    · right
      rw [abs_of_neg h] at hw
      exact hw.le
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith [hY.measure_ge_le hε, hY.neg.measure_ge_le hε]

/-- A finite measure is at most `ofReal r` when its real value is at most `r`. -/
theorem le_ofReal_of_realZ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Set Ω} {r : ℝ} (h : μ.real s ≤ r) : μ s ≤ ENNReal.ofReal r := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- `d e^(-(1+τ) log d) = d^(-τ)` for `d > 0`. -/
theorem card_exp_rpowZ {d τ : ℝ} (hd : 0 < d) :
    d * Real.exp (-((1 + τ) * Real.log d)) = d ^ (-τ) := by
  rw [Real.rpow_def_of_pos hd]
  nth_rw 1 [← Real.exp_log hd]
  rw [← Real.exp_add]
  congr 1
  ring

/-- `E exp(t X²) = (1 - 2 t v)^(-1/2)` for `X ~ N(0, v)` with `v > 0` and `t v < 1/2`
(copied from `BDT24.Prob.T.mgf_sq_gaussianReal`). -/
theorem mgf_sq_gaussZ {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t * v < 1 / 2) :
    mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) t = (√(1 - 2 * t * v))⁻¹ := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  rw [mgf, integral_gaussianReal_eq_integral_smul hv]
  have h : ∀ x : ℝ, gaussianPDFReal 0 v x • Real.exp (t * x ^ 2) =
      (√(2 * Real.pi * v))⁻¹ * Real.exp (-(1 / (2 * v) - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have hb : 0 < 1 - 2 * t * v := by linarith
  have h2 : Real.pi / (1 / (2 * v) - t) = 2 * Real.pi * v / (1 - 2 * t * v) := by
    have : (1 / (2 * v) - t : ℝ) = (1 - 2 * t * v) / (2 * v) := by field_simp
    rw [this]
    field_simp
  have hs : 0 < √(2 * Real.pi * v) := Real.sqrt_pos.2 (by positivity)
  rw [h2, Real.sqrt_div (by positivity)]
  field_simp

/-- The moment-generating function of `∑ xᵢ²` under `n` independent copies is the `n`-th power
of that of `x²` (copied from `BDT24.Prob.T.mgf_sum_sq_pi`). -/
theorem mgf_sumsq_piZ (n : ℕ) (v : ℝ≥0) (t : ℝ) :
    mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2) (Measure.pi fun _ ↦ gaussianReal 0 v) t =
      mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) t ^ n := by
  simp only [mgf, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (fun u : ℝ ↦ Real.exp (t * u ^ 2)), Fintype.card_fin]

/-- The Chernoff factor per coordinate at `λ v = 3/8`: `e^(-3/2) · 2 ≤ e^(-1/4)`. -/
theorem chi_factorZ : Real.exp (-(3 / 2)) * 2 ≤ Real.exp (-(1 / 4)) := by
  have h := Real.add_one_le_exp (5 / 4 : ℝ)
  calc Real.exp (-(3 / 2)) * 2 ≤ Real.exp (-(3 / 2)) * Real.exp (5 / 4) := by
        gcongr
        linarith
    _ = Real.exp (-(1 / 4)) := by
        rw [← Real.exp_add]
        norm_num

end NZ

open NZ in
/-- The largest squared correlation of the noise with a column of norm `√n` exceeds
`2 (1 + τ) σ² n log d` with probability at most `2 d^(-τ)`. -/
theorem noise_max_tail {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (hX : HasNormalizedColumns X)
    (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    noiseLaw n σ {w | ∃ j, 2 * (1 + τ) * σ ^ 2 * n * Real.log d < (∑ i, X i j * w i) ^ 2} ≤
      ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · simp
  set v : NNReal := (σ ^ 2).toNNReal with hv
  have hvσ : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  have hμ : noiseLaw n σ = Measure.pi fun _ ↦ gaussianReal 0 v := rfl
  set c : NNReal := (σ ^ 2 * n).toNNReal with hc
  have hcR : (c : ℝ) = σ ^ 2 * n := Real.coe_toNNReal _ (by positivity)
  have hY : ∀ j, HasSubgaussianMGF (fun w : Fin n → ℝ ↦ ∑ i, X i j * w i) c
      (Measure.pi fun _ ↦ gaussianReal 0 v) := fun j ↦
    subG_lin_gaussZ v (fun i ↦ X i j) (by rw [hcR, hX j, hvσ]; ring)
  rw [hμ]
  by_cases hc0 : σ ^ 2 * n = 0
  · have hc0' : c = 0 := NNReal.coe_eq_zero.1 (hcR.trans hc0)
    refine (measure_mono_null (t := ⋃ j, {w : Fin n → ℝ |
      ¬ (fun w : Fin n → ℝ ↦ ∑ i, X i j * w i) w = (0 : (Fin n → ℝ) → ℝ) w}) ?_ ?_).trans_le
      zero_le
    · intro w hw
      obtain ⟨j, hj⟩ := hw
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Pi.zero_apply]
      refine ⟨j, fun h0 ↦ ?_⟩
      rw [h0] at hj
      have : 2 * (1 + τ) * σ ^ 2 * n * Real.log d = 2 * (1 + τ) * (σ ^ 2 * n) * Real.log d := by
        ring
      rw [this, hc0] at hj
      simp at hj
    · refine measure_iUnion_null fun j ↦ ?_
      have h := hY j
      rw [hc0'] at h
      exact ae_iff.1 h.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hcpos : (0 : ℝ) < σ ^ 2 * n := lt_of_le_of_ne (by positivity) (Ne.symm hc0)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  set T : ℝ := 2 * (1 + τ) * σ ^ 2 * n * Real.log d with hT
  have hT0 : 0 ≤ T := by positivity
  set ε : ℝ := √T with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hsub : {w : Fin n → ℝ | ∃ j, T < (∑ i, X i j * w i) ^ 2} ⊆
      ⋃ j, {w : Fin n → ℝ | ε < |∑ i, X i j * w i|} := by
    intro w hw
    obtain ⟨j, hj⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨j, ?_⟩
    rw [hε, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt hT0 hj
  have hexp : Real.exp (-ε ^ 2 / (2 * c)) = Real.exp (-((1 + τ) * Real.log d)) := by
    congr 1
    rw [hε, Real.sq_sqrt hT0, hT, hcR, eq_comm, eq_div_iff (mul_pos two_pos hcpos).ne']
    ring
  refine le_ofReal_of_realZ ?_
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin d, 2 * Real.exp (-((1 + τ) * Real.log d)) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [← hexp]
        exact abs_tail_subGZ (hY j) hε0
    _ = 2 * (d : ℝ) ^ (-τ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← card_exp_rpowZ hdR]
        ring

open NZ in
/-- The squared norm of the noise exceeds `4 σ² n` with probability at most `e^(-n/4)`. -/
theorem noise_norm_tail (n : ℕ) (σ : ℝ) :
    noiseLaw n σ {w | 4 * σ ^ 2 * n < w ⬝ᵥ w} ≤ ENNReal.ofReal (Real.exp (-(n / 4 : ℝ))) := by
  set v : NNReal := (σ ^ 2).toNNReal with hv
  have hvσ : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  have hμ : noiseLaw n σ = Measure.pi fun _ ↦ gaussianReal 0 v := rfl
  have hdot : ∀ w : Fin n → ℝ, w ⬝ᵥ w = ∑ i, w i ^ 2 := fun w ↦ by simp [dotProduct, sq]
  rw [hμ]
  rcases eq_or_ne σ 0 with rfl | hσ
  · have hv0 : v = 0 := by simp [hv]
    refine (measure_mono_null (t := ⋃ i, {w : Fin n → ℝ |
      ¬ (fun w : Fin n → ℝ ↦ w i) w = (0 : (Fin n → ℝ) → ℝ) w}) ?_ ?_).trans_le zero_le
    · intro w hw
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Pi.zero_apply]
      by_contra h
      simp only [not_exists, not_not] at h
      have h0 : w = 0 := funext h
      subst h0
      simp at hw
    · refine measure_iUnion_null fun i ↦ ?_
      have h : HasSubgaussianMGF (fun w : Fin n → ℝ ↦ w i) 0
          (Measure.pi fun _ ↦ gaussianReal 0 v) := by
        simpa [hv0] using subG_coord_gaussZ (n := n) v i
      exact ae_iff.1 h.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hvσ
    exact hσ (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hvσ.symm)
  have hvpos : (0 : ℝ) < v := by rw [hvσ]; positivity
  set t : ℝ := 3 / (8 * v) with ht
  have htv : t * v = 3 / 8 := by rw [ht]; field_simp
  have hM : mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) t = 2 := by
    rw [mgf_sq_gaussZ hv0 (by rw [htv]; norm_num),
      show 1 - 2 * t * v = (1 / 2) ^ 2 by linear_combination -2 * htv,
      Real.sqrt_sq (by norm_num)]
    norm_num
  have hpos : 0 < mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
      (Measure.pi fun _ ↦ gaussianReal 0 v) t := by
    rw [mgf_sumsq_piZ, hM]
    positivity
  refine le_ofReal_of_realZ ?_
  calc _ ≤ (Measure.pi fun _ : Fin n ↦ gaussianReal 0 v).real
          {x | 4 * (v : ℝ) * n ≤ ∑ i, x i ^ 2} := by
        refine measureReal_mono fun w hw ↦ ?_
        simp only [Set.mem_ofPred_eq] at hw ⊢
        rw [← hdot, hvσ]
        exact hw.le
    _ ≤ Real.exp (-t * (4 * v * n)) * mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
          (Measure.pi fun _ ↦ gaussianReal 0 v) t :=
        measure_ge_le_exp_mul_mgf _ (by positivity) (mgf_pos_iff.1 hpos)
    _ = (Real.exp (-(3 / 2)) * 2) ^ n := by
        rw [mgf_sumsq_piZ, hM, mul_pow, ← Real.exp_nat_mul]
        congr 2
        linear_combination (-4 * (n : ℝ)) * htv
    _ ≤ Real.exp (-(1 / 4)) ^ n := pow_le_pow_left₀ (by positivity) chi_factorZ n
    _ = Real.exp (-(n / 4 : ℝ)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

end B25
