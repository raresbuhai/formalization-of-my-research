module

public import BGHKLMM26.RobustMIS.Quantile
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# One-dimensional static Gaussian lemmas

On `(ℝ, γ₁)`, for a measurable `m₁ : ℝ → [0, 1]`:

* the **bathtub** principle (Lemma 4.2 of `eldan-proof.tex`, Eldan's Lemma 14 and Claim 12):
  `|∫ s m₁(s) dγ₁| ≤ q(∫ m₁ dγ₁)`, with the exact identities for `w = 𝟙_{[L, ∞)} - m₁`,
  `L = -Ψ(a)`, that measure the gap;
* the **longitudinal entry** (Lemma 4.6, Eldan's Lemma 23 adapted): `b₁₁ = ∫ (s² - 1) m₁` is
  close to `ξ = -Ψ(S) q(S)` in terms of the bathtub gap `δ' = q(S) - ∫ s m₁`.

All statements are proved. The integrals of `𝟙_{[L, ∞)}` against `1, s, s², s² - 1` come from
the standard integrals (S6) of `Normal.lean` (`Static1D.integral_ind`, `integral_mul_ind`,
`integral_sq_mul_ind`, `integral_sq_sub_one_mul_ind`); the lower half of the bathtub bound
applies the upper half to `s ↦ m₁(-s)` (symmetry of `γ₁`, `Static1D.integral_comp_neg`); for
`b11_bound` we use `P = 2(|L| + 1 + √(2 log(1/δ')))` in place of [E]'s `2 max(|L|, 1, ·)`, and the
pointwise bound `(s - L)² |w| ≤ P (s - L) w + 4 s² (𝟙_{[P/2, ∞)}(s) + 𝟙_{[P/2, ∞)}(-s))`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set

namespace Static1D

theorem integrable_id : Integrable (fun s : ℝ ↦ s) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable le_rfl

theorem integrable_sq : Integrable (fun s : ℝ ↦ s ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq

theorem integrable_of_bdd {m : ℝ → ℝ} (hm : Measurable m) {C : ℝ} (hC : ∀ s, |m s| ≤ C) :
    Integrable m (gaussianReal 0 1) :=
  (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun s ↦ by
    rw [Real.norm_eq_abs]; exact hC s)

theorem integrable_mul_of_bdd {p m : ℝ → ℝ} (hp : Integrable p (gaussianReal 0 1))
    (hm : Measurable m) {C : ℝ} (hC : ∀ s, |m s| ≤ C) :
    Integrable (fun s ↦ p s * m s) (gaussianReal 0 1) :=
  hp.mul_bdd hm.aestronglyMeasurable (ae_of_all _ fun s ↦ by rw [Real.norm_eq_abs]; exact hC s)

theorem integrable_add_sq (c : ℝ) : Integrable (fun s : ℝ ↦ (s + c) ^ 2) (gaussianReal 0 1) := by
  have : (fun s : ℝ ↦ (s + c) ^ 2) = fun s ↦ s ^ 2 + 2 * c * s + c ^ 2 := by
    funext s; ring
  rw [this]
  exact (integrable_sq.add (integrable_id.const_mul _)).add (integrable_const _)

theorem integrable_add (c : ℝ) : Integrable (fun s : ℝ ↦ s + c) (gaussianReal 0 1) :=
  integrable_id.add (integrable_const _)

theorem abs_le_one {m : ℝ → ℝ} (h01 : ∀ s, 0 ≤ m s ∧ m s ≤ 1) (s : ℝ) : |m s| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [h01 s]

theorem measurable_ind (L : ℝ) : Measurable ((Ici L).indicator (1 : ℝ → ℝ)) :=
  measurable_one.indicator measurableSet_Ici

theorem ind_mem (L s : ℝ) :
    0 ≤ (Ici L).indicator (1 : ℝ → ℝ) s ∧ (Ici L).indicator (1 : ℝ → ℝ) s ≤ 1 := by
  by_cases h : s ∈ Ici L <;> simp [h]

theorem abs_ind_sub_le {m : ℝ → ℝ} (h01 : ∀ s, 0 ≤ m s ∧ m s ≤ 1) (L s : ℝ) :
    |(Ici L).indicator (1 : ℝ → ℝ) s - m s| ≤ 1 := by
  have := ind_mem L s
  rw [abs_le]; constructor <;> linarith [h01 s]

/-- `γ₁([L, ∞)) = 1 - Φ(L)`. -/
theorem integral_ind (L : ℝ) :
    ∫ s, (Ici L).indicator 1 s ∂gaussianReal 0 1 = 1 - Gaussian.Phi L := by
  rw [integral_indicator_one measurableSet_Ici, ← compl_Iio,
    probReal_compl_eq_one_sub measurableSet_Iio]
  have h0 : (gaussianReal 0 1) {L} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  rw [measureReal_congr (Iio_ae_eq_Iic' h0), Gaussian.Phi, cdf_eq_real]

/-- `∫ s 1_{[L, ∞)} dγ₁ = φ(L)`. -/
theorem integral_mul_ind (L : ℝ) :
    ∫ s, s * (Ici L).indicator 1 s ∂gaussianReal 0 1 = npdf L := by
  rw [integral_gaussianReal_eq, ← integral_Ici_mul_npdf L, ← integral_indicator measurableSet_Ici]
  congr 1; funext s
  by_cases h : s ∈ Ici L <;> simp [h, mul_comm]

theorem integral_sq_sub_one_mul_ind (L : ℝ) :
    ∫ s, (s ^ 2 - 1) * (Ici L).indicator 1 s ∂gaussianReal 0 1 = L * npdf L := by
  rw [integral_gaussianReal_eq, ← integral_Ici_sq_sub_one_mul_npdf L,
    ← integral_indicator measurableSet_Ici]
  congr 1; funext s
  by_cases h : s ∈ Ici L <;> simp [h, mul_comm]

theorem integral_sq_mul_ind (L : ℝ) :
    ∫ s, s ^ 2 * (Ici L).indicator 1 s ∂gaussianReal 0 1 = L * npdf L + (1 - Gaussian.Phi L) := by
  rw [integral_gaussianReal_eq, ← integral_Ici_sq_mul_npdf L,
    ← integral_indicator measurableSet_Ici]
  congr 1; funext s
  by_cases h : s ∈ Ici L <;> simp [h, mul_comm]

/-- Symmetry: `∫ F(-s) dγ₁ = ∫ F dγ₁`. -/
theorem integral_comp_neg {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ s, F (-s) ∂gaussianReal 0 1 = ∫ s, F s ∂gaussianReal 0 1 := by
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun x ↦ -x) (f := F) (by fun_prop)
    hF.aestronglyMeasurable
  rw [gaussianReal_map_neg, neg_zero] at h
  exact h.symm

theorem integral_mem {m : ℝ → ℝ} (hm : Measurable m) (h01 : ∀ s, 0 ≤ m s ∧ m s ≤ 1) :
    ∫ s, m s ∂gaussianReal 0 1 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun s ↦ (h01 s).1, ?_⟩
  calc ∫ s, m s ∂gaussianReal 0 1 ≤ ∫ _s, (1 : ℝ) ∂gaussianReal 0 1 :=
        integral_mono (integrable_of_bdd hm (abs_le_one h01)) (integrable_const _)
          fun s ↦ (h01 s).2
    _ = 1 := by simp

theorem qf_eq_npdf {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : qf a = npdf (Psi a) := by
  simp only [qf, ha, ↓reduceIte]

end Static1D

open Static1D

/-- **Bathtub gap** (Lemma 4.2, second part): for `a = ∫ m₁ ∈ (0, 1)`, `L = -Ψ(a)` and
`w = 𝟙_{[L, ∞)} - m₁`: `(s - L) w(s) ≥ 0`, `∫ w = 0` and `∫ (s - L) w = q(a) - ∫ s m₁`. -/
theorem bathtub1d_gap (m₁ : ℝ → ℝ) (hm : Measurable m₁) (h01 : ∀ s, 0 ≤ m₁ s ∧ m₁ s ≤ 1)
    {a : ℝ} (ha : ∫ s, m₁ s ∂gaussianReal 0 1 = a) (ha01 : a ∈ Ioo (0 : ℝ) 1) :
    (∀ s, 0 ≤ (s + Psi a) * ((Ici (-Psi a)).indicator 1 s - m₁ s)) ∧
      ∫ s, ((Ici (-Psi a)).indicator 1 s - m₁ s) ∂gaussianReal 0 1 = 0 ∧
      ∫ s, (s + Psi a) * ((Ici (-Psi a)).indicator 1 s - m₁ s) ∂gaussianReal 0 1 =
        qf a - ∫ s, s * m₁ s ∂gaussianReal 0 1 := by
  have hind : ∫ s, (Ici (-Psi a)).indicator 1 s ∂gaussianReal 0 1 = a := by
    rw [integral_ind, Phi_neg, Phi_Psi ha01]; ring
  have hi1 : Integrable ((Ici (-Psi a)).indicator (1 : ℝ → ℝ)) (gaussianReal 0 1) :=
    integrable_of_bdd (measurable_ind _) (fun s ↦ abs_le_one (ind_mem _) s)
  have hi2 : Integrable m₁ (gaussianReal 0 1) := integrable_of_bdd hm (abs_le_one h01)
  have hw : ∫ s, ((Ici (-Psi a)).indicator 1 s - m₁ s) ∂gaussianReal 0 1 = 0 := by
    rw [integral_sub hi1 hi2, hind, ha, sub_self]
  refine ⟨fun s ↦ ?_, hw, ?_⟩
  · by_cases h : s ∈ Ici (-Psi a)
    · rw [indicator_of_mem h]
      simp only [mem_Ici] at h
      exact mul_nonneg (by linarith) (by simp only [Pi.one_apply]; linarith [h01 s])
    · rw [indicator_of_notMem h]
      simp only [mem_Ici, not_le] at h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [h01 s])
  · have hexp : ∀ s, (s + Psi a) * ((Ici (-Psi a)).indicator 1 s - m₁ s) =
        (s * (Ici (-Psi a)).indicator 1 s - s * m₁ s) +
          Psi a * ((Ici (-Psi a)).indicator 1 s - m₁ s) := fun s ↦ by ring
    simp_rw [hexp]
    have hj1 : Integrable (fun s ↦ s * (Ici (-Psi a)).indicator 1 s) (gaussianReal 0 1) :=
      integrable_mul_of_bdd integrable_id (measurable_ind _) (fun s ↦ abs_le_one (ind_mem _) s)
    have hj2 : Integrable (fun s ↦ s * m₁ s) (gaussianReal 0 1) :=
      integrable_mul_of_bdd integrable_id hm (abs_le_one h01)
    have hj3 : Integrable (fun s ↦ s * (Ici (-Psi a)).indicator 1 s - s * m₁ s)
        (gaussianReal 0 1) := hj1.sub hj2
    have hj4 : Integrable (fun s ↦ Psi a * ((Ici (-Psi a)).indicator 1 s - m₁ s))
        (gaussianReal 0 1) := (hi1.sub hi2).const_mul _
    rw [integral_add hj3 hj4, integral_sub hj1 hj2,
      integral_const_mul, hw, integral_mul_ind, npdf_neg, qf_eq_npdf ha01]
    ring

theorem Static1D.integral_mul_le (m₁ : ℝ → ℝ) (hm : Measurable m₁)
    (h01 : ∀ s, 0 ≤ m₁ s ∧ m₁ s ≤ 1) (ha01 : ∫ s, m₁ s ∂gaussianReal 0 1 ∈ Ioo (0 : ℝ) 1) :
    ∫ s, s * m₁ s ∂gaussianReal 0 1 ≤ qf (∫ s, m₁ s ∂gaussianReal 0 1) := by
  obtain ⟨a, ha⟩ : ∃ a, ∫ s, m₁ s ∂gaussianReal 0 1 = a := ⟨_, rfl⟩
  rw [ha] at ha01 ⊢
  obtain ⟨h1, -, h3⟩ := bathtub1d_gap m₁ hm h01 ha ha01
  have := integral_nonneg (μ := gaussianReal 0 1)
    (f := fun s ↦ (s + Psi a) * ((Ici (-Psi a)).indicator 1 s - m₁ s)) h1
  linarith

/-- **Bathtub** (Lemma 4.2, first part): `|∫ s m₁(s) dγ₁(s)| ≤ q(∫ m₁ dγ₁)` for measurable
`m₁ : ℝ → [0, 1]`. -/
theorem bathtub1d (m₁ : ℝ → ℝ) (hm : Measurable m₁) (h01 : ∀ s, 0 ≤ m₁ s ∧ m₁ s ≤ 1) :
    |∫ s, s * m₁ s ∂gaussianReal 0 1| ≤ qf (∫ s, m₁ s ∂gaussianReal 0 1) := by
  have hmem := integral_mem hm h01
  by_cases ha01 : ∫ s, m₁ s ∂gaussianReal 0 1 ∈ Ioo (0 : ℝ) 1
  · have hup := Static1D.integral_mul_le m₁ hm h01 ha01
    -- the reflected function
    have hm' : Measurable (fun s ↦ m₁ (-s)) := hm.comp measurable_neg
    have h01' : ∀ s, 0 ≤ m₁ (-s) ∧ m₁ (-s) ≤ 1 := fun s ↦ h01 (-s)
    have hint : ∫ s, m₁ (-s) ∂gaussianReal 0 1 = ∫ s, m₁ s ∂gaussianReal 0 1 :=
      integral_comp_neg hm
    have hfirst : ∫ s, s * m₁ (-s) ∂gaussianReal 0 1 = -∫ s, s * m₁ s ∂gaussianReal 0 1 := by
      have := integral_comp_neg (F := fun s ↦ -s * m₁ s) (by fun_prop)
      simp only [neg_neg] at this
      rw [this, ← integral_neg]
      congr 1; funext s; ring
    have hlow := Static1D.integral_mul_le (fun s ↦ m₁ (-s)) hm' h01' (by rw [hint]; exact ha01)
    rw [hint, hfirst] at hlow
    rw [abs_le]
    constructor <;> linarith
  · rw [qf_of_not_mem ha01]
    have h01' : ∫ s, m₁ s ∂gaussianReal 0 1 = 0 ∨ ∫ s, m₁ s ∂gaussianReal 0 1 = 1 := by
      simp only [mem_Ioo, not_and_or, not_lt] at ha01
      rcases ha01 with h | h
      · left; linarith [hmem.1]
      · right; linarith [hmem.2]
    have hi : Integrable m₁ (gaussianReal 0 1) := integrable_of_bdd hm (abs_le_one h01)
    rcases h01' with h0 | h1
    · have hae : m₁ =ᵐ[gaussianReal 0 1] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun s ↦ (h01 s).1) hi).1 h0
      have : ∫ s, s * m₁ s ∂gaussianReal 0 1 = 0 := by
        rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (hae.mono fun s hs ↦ by simp [hs])]
        simp
      rw [this, abs_zero]
    · have h1' : ∫ s, (1 - m₁ s) ∂gaussianReal 0 1 = 0 := by
        rw [integral_sub (integrable_const _) hi, h1]; simp
      have hae : (fun s ↦ 1 - m₁ s) =ᵐ[gaussianReal 0 1] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun s ↦ by
          change (0 : ℝ) ≤ 1 - m₁ s; linarith [h01 s])
          ((integrable_const _).sub hi)).1 h1'
      have : ∫ s, s * m₁ s ∂gaussianReal 0 1 = 0 := by
        rw [integral_congr_ae (g := fun s ↦ s) (hae.mono fun s hs ↦ by
          simp only [Pi.zero_apply] at hs
          have : m₁ s = 1 := by linarith
          simp [this])]
        exact integral_id_gaussianReal
      rw [this, abs_zero]


theorem Static1D.npdf_le_of {δ a : ℝ} (hδ : 0 < δ) (ha : √(2 * Real.log (1 / δ)) ≤ a) :
    npdf a ≤ (√(2 * π))⁻¹ * δ := by
  have hr0 : 0 ≤ √(2 * Real.log (1 / δ)) := Real.sqrt_nonneg _
  have hsq : 2 * Real.log (1 / δ) ≤ a ^ 2 := by
    rcases le_or_gt 0 (2 * Real.log (1 / δ)) with h | h
    · have := pow_le_pow_left₀ hr0 ha 2
      rwa [Real.sq_sqrt h] at this
    · nlinarith [sq_nonneg a]
  have hexp : rexp (-a ^ 2 / 2) ≤ δ := by
    calc rexp (-a ^ 2 / 2) ≤ rexp (-Real.log (1 / δ)) := Real.exp_le_exp.2 (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

theorem Static1D.inv_sqrt_two_pi_le : (√(2 * π))⁻¹ ≤ 0.4 := by
  have h : (2.5 : ℝ) ≤ √(2 * π) := by
    rw [show (2.5 : ℝ) = √(2.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_d2])
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  norm_num at h ⊢
  linarith

/-- **Longitudinal entry** (Lemma 4.6): with `S = ∫ f₁ ∈ (0, 1)`, `δ' = q(S) - ∫ s f₁`,
`ξ = -Ψ(S) q(S)` and `b₁₁ = ∫ (s² - 1) f₁`: if `δ' = 0` then `b₁₁ = ξ`, and if `δ' > 0` then
`|ξ - b₁₁| ≤ δ' (7.2 |Ψ(S)| + 7.2 √(2 log(1/δ')) + 10.4)`. -/
theorem b11_bound (f₁ : ℝ → ℝ) (hm : Measurable f₁) (h01 : ∀ s, 0 ≤ f₁ s ∧ f₁ s ≤ 1)
    {S δ' : ℝ} (hS : ∫ s, f₁ s ∂gaussianReal 0 1 = S) (hS01 : S ∈ Ioo (0 : ℝ) 1)
    (hδ : δ' = qf S - ∫ s, s * f₁ s ∂gaussianReal 0 1) :
    (δ' = 0 → ∫ s, (s ^ 2 - 1) * f₁ s ∂gaussianReal 0 1 = -Psi S * qf S) ∧
      (0 < δ' → |-Psi S * qf S - ∫ s, (s ^ 2 - 1) * f₁ s ∂gaussianReal 0 1| ≤
        δ' * (7.2 * |Psi S| + 7.2 * √(2 * Real.log (1 / δ')) + 10.4)) := by
  obtain ⟨h1, h2, h3⟩ := bathtub1d_gap f₁ hm h01 hS hS01
  rw [← hδ] at h3
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Psi S = Ψ := ⟨_, rfl⟩
  rw [hΨ] at h1 h2 h3 ⊢
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, w = fun s ↦ (Ici (-Ψ)).indicator 1 s - f₁ s := ⟨_, rfl⟩
  have hwm : Measurable w := by rw [hw]; exact (measurable_ind _).sub hm
  have hwb : ∀ s, |w s| ≤ 1 := fun s ↦ by rw [hw]; exact abs_ind_sub_le h01 _ s
  have hw1 : ∀ s, 0 ≤ (s + Ψ) * w s := fun s ↦ by rw [hw]; exact h1 s
  have hw2 : ∫ s, w s ∂gaussianReal 0 1 = 0 := by rw [hw]; exact h2
  have hw3 : ∫ s, (s + Ψ) * w s ∂gaussianReal 0 1 = δ' := by rw [hw]; exact h3
  have Ia : Integrable (fun s : ℝ ↦ (s ^ 2 - 1) * (Ici (-Ψ)).indicator 1 s) (gaussianReal 0 1) :=
    integrable_mul_of_bdd (integrable_sq.sub (integrable_const 1)) (measurable_ind _)
      (fun s ↦ abs_le_one (ind_mem _) s)
  have Ib : Integrable (fun s : ℝ ↦ (s ^ 2 - 1) * f₁ s) (gaussianReal 0 1) :=
    integrable_mul_of_bdd (integrable_sq.sub (integrable_const 1)) hm (abs_le_one h01)
  have Ic : Integrable (fun s : ℝ ↦ (s + Ψ) ^ 2 * w s) (gaussianReal 0 1) :=
    integrable_mul_of_bdd (integrable_add_sq Ψ) hwm hwb
  have Id : Integrable (fun s : ℝ ↦ (s + Ψ) * w s) (gaussianReal 0 1) :=
    integrable_mul_of_bdd (integrable_add Ψ) hwm hwb
  have Ie : Integrable w (gaussianReal 0 1) := integrable_of_bdd hwm hwb
  have e1 : ∫ s, (s ^ 2 - 1) * (Ici (-Ψ)).indicator 1 s ∂gaussianReal 0 1 = -Ψ * qf S := by
    rw [integral_sq_sub_one_mul_ind, npdf_neg, qf_eq_npdf hS01, hΨ]
  have e2 : ∫ s, (s ^ 2 - 1) * w s ∂gaussianReal 0 1 =
      ∫ s, (s ^ 2 - 1) * (Ici (-Ψ)).indicator 1 s ∂gaussianReal 0 1 -
        ∫ s, (s ^ 2 - 1) * f₁ s ∂gaussianReal 0 1 := by
    rw [← integral_sub Ia Ib, hw]
    congr 1; funext s; ring
  have e3 : ∫ s, (s ^ 2 - 1) * w s ∂gaussianReal 0 1 =
      ∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1 - 2 * Ψ * δ' := by
    have hexp : ∀ s, (s ^ 2 - 1) * w s =
        ((s + Ψ) ^ 2 * w s - 2 * Ψ * ((s + Ψ) * w s)) + (Ψ ^ 2 - 1) * w s := fun s ↦ by ring
    simp_rw [hexp]
    have I1 : Integrable (fun s ↦ (s + Ψ) ^ 2 * w s - 2 * Ψ * ((s + Ψ) * w s))
        (gaussianReal 0 1) := Ic.sub (Id.const_mul _)
    have I2 : Integrable (fun s ↦ (Ψ ^ 2 - 1) * w s) (gaussianReal 0 1) := Ie.const_mul _
    have I3 : Integrable (fun s ↦ 2 * Ψ * ((s + Ψ) * w s)) (gaussianReal 0 1) := Id.const_mul _
    rw [integral_add I1 I2, integral_sub Ic I3, integral_const_mul, integral_const_mul, hw2, hw3]
    ring
  have key : -Ψ * qf S - ∫ s, (s ^ 2 - 1) * f₁ s ∂gaussianReal 0 1 =
      ∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1 - 2 * Ψ * δ' := by
    rw [← e3, e2, e1]
  refine ⟨fun h0 ↦ ?_, fun hpos ↦ ?_⟩
  · -- `δ' = 0`: `(s - L) w = 0` a.e.
    rw [h0] at hw3 key
    have hae : (fun s ↦ (s + Ψ) * w s) =ᵐ[gaussianReal 0 1] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun s ↦ hw1 s) Id).1 hw3
    have : ∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1 = 0 := by
      rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (hae.mono fun s hs ↦ by
        simp only [Pi.zero_apply] at hs
        change (s + Ψ) ^ 2 * w s = 0
        rw [sq, mul_assoc, hs, mul_zero])]
      simp
    rw [this] at key
    linarith
  · -- `δ' > 0`
    obtain ⟨r, hr⟩ : ∃ r, √(2 * Real.log (1 / δ')) = r := ⟨_, rfl⟩
    rw [hr]
    have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
    obtain ⟨a, ha⟩ : ∃ a, a = |Ψ| + 1 + r := ⟨_, rfl⟩
    have ha1 : 1 ≤ a := by rw [ha]; linarith [abs_nonneg Ψ]
    have haΨ : |Ψ| ≤ a := by rw [ha]; linarith
    obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, T = fun s ↦ s ^ 2 * (Ici a).indicator 1 s := ⟨_, rfl⟩
    have hTm : Measurable T := by rw [hT]; exact (measurable_id.pow_const 2).mul (measurable_ind _)
    have hT0 : ∀ s, 0 ≤ T s := fun s ↦ by
      rw [hT]; exact mul_nonneg (sq_nonneg _) (ind_mem _ _).1
    have IT : Integrable T (gaussianReal 0 1) := by
      rw [hT]; exact integrable_mul_of_bdd integrable_sq (measurable_ind _)
        (fun s ↦ abs_le_one (ind_mem _) s)
    have IT' : Integrable (fun s ↦ T (-s)) (gaussianReal 0 1) := by
      rw [hT]
      have : Integrable (fun s : ℝ ↦ (-s) ^ 2) (gaussianReal 0 1) := by
        simpa only [neg_sq] using integrable_sq
      exact integrable_mul_of_bdd this ((measurable_ind _).comp measurable_neg)
        (fun s ↦ abs_le_one (ind_mem _) (-s))
    -- the pointwise bound
    have hpt : ∀ s, (s + Ψ) ^ 2 * |w s| ≤ 2 * a * ((s + Ψ) * w s) + 4 * (T s + T (-s)) := by
      intro s
      have hws := hwb s
      have hp := hw1 s
      have hT1 := hT0 s
      have hT2 := hT0 (-s)
      by_cases hd : |s + Ψ| ≤ 2 * a
      · have heq : (s + Ψ) ^ 2 * |w s| = |s + Ψ| * ((s + Ψ) * w s) := by
          rw [← abs_of_nonneg hp, abs_mul, ← mul_assoc, ← sq, sq_abs]
        rw [heq]
        have := mul_le_mul_of_nonneg_right hd hp
        linarith
      · push Not at hd
        have hs : a ≤ |s| := by linarith [abs_add_le s Ψ]
        have hsq : (s + Ψ) ^ 2 ≤ 4 * s ^ 2 := by
          have h2 : |s + Ψ| ≤ 2 * |s| := by linarith [abs_add_le s Ψ]
          have := pow_le_pow_left₀ (abs_nonneg _) h2 2
          rw [sq_abs, mul_pow, sq_abs] at this
          linarith
        have hTs : s ^ 2 ≤ T s + T (-s) := by
          rcases le_or_gt 0 s with h | h
          · have hm : s ∈ Ici a := by rw [abs_of_nonneg h] at hs; exact hs
            have : T s = s ^ 2 := by rw [hT]; simp [hm]
            linarith
          · have hm : -s ∈ Ici a := by rw [abs_of_neg h] at hs; exact hs
            have : T (-s) = s ^ 2 := by rw [hT]; simp [hm]
            linarith
        have h3 : (s + Ψ) ^ 2 * |w s| ≤ (s + Ψ) ^ 2 :=
          mul_le_of_le_one_right (sq_nonneg _) hws
        have h4 : 0 ≤ 2 * a * ((s + Ψ) * w s) := mul_nonneg (by linarith) hp
        linarith
    have Ilhs : Integrable (fun s ↦ (s + Ψ) ^ 2 * |w s|) (gaussianReal 0 1) :=
      integrable_mul_of_bdd (integrable_add_sq Ψ) (continuous_abs.measurable.comp hwm)
        (fun s ↦ by rw [abs_abs]; exact hwb s)
    have Irhs : Integrable (fun s ↦ 2 * a * ((s + Ψ) * w s) + 4 * (T s + T (-s)))
        (gaussianReal 0 1) := (Id.const_mul _).add ((IT.add IT').const_mul _)
    have hint := integral_mono Ilhs Irhs hpt
    have IT2 : Integrable (fun s ↦ T s + T (-s)) (gaussianReal 0 1) := IT.add IT'
    rw [integral_add (Id.const_mul _) (IT2.const_mul _), integral_const_mul, integral_const_mul,
      integral_add IT IT', integral_comp_neg hTm, hw3] at hint
    have hTint : ∫ s, T s ∂gaussianReal 0 1 ≤ (a + 1) * npdf a := by
      rw [hT, integral_sq_mul_ind]
      have h1 := one_sub_Phi_le (show 0 < a by linarith)
      have h2 : npdf a / a ≤ npdf a := div_le_self (npdf_pos a).le ha1
      linarith
    have hnp : npdf a ≤ (√(2 * π))⁻¹ * δ' :=
      npdf_le_of hpos (by rw [hr, ha]; linarith [abs_nonneg Ψ])
    have hc := inv_sqrt_two_pi_le
    have hnp' : npdf a ≤ 0.4 * δ' := hnp.trans (mul_le_mul_of_nonneg_right hc hpos.le)
    have hTint' : ∫ s, T s ∂gaussianReal 0 1 ≤ (a + 1) * (0.4 * δ') :=
      hTint.trans (mul_le_mul_of_nonneg_left hnp' (by linarith))
    have habs : |∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1| ≤
        ∫ s, (s + Ψ) ^ 2 * |w s| ∂gaussianReal 0 1 := by
      calc _ ≤ ∫ s, |(s + Ψ) ^ 2 * w s| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
        _ = _ := by
          congr 1; funext s
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [key]
    calc |∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1 - 2 * Ψ * δ'|
        ≤ |∫ s, (s + Ψ) ^ 2 * w s ∂gaussianReal 0 1| + |2 * Ψ * δ'| := abs_sub _ _
      _ ≤ (2 * a * δ' + 4 * (2 * ((a + 1) * (0.4 * δ')))) + 2 * |Ψ| * δ' := by
          have : |2 * Ψ * δ'| = 2 * |Ψ| * δ' := by
            rw [abs_mul, abs_mul, abs_of_pos hpos]; norm_num
          rw [this]
          linarith
      _ ≤ δ' * (7.2 * |Ψ| + 7.2 * r + 10.4) := by
          rw [ha]
          nlinarith [abs_nonneg Ψ]

end BGHKLMM26.RobustMIS
