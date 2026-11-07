module

public import BGHKLMM26.RobustMIS.Static

/-!
# The quantitative bathtub

Lemma 4.8 of `eldan-proof.tex` (Eldan, proof of Corollary 4): the `L¹` distance `δ₁` from `f` to
the halfspace `H_ν = {⟨ν, x⟩ ≥ -Ψ(m)}` of measure `m` whose normal `ν` is the direction of the
first Hermite vector satisfies `q(m) - |F̂| ≥ (√(2π)/8) δ₁²`, hence `ε(f) ≥ (λ(m)/4) δ₁²`.

Proof sketch: marginal `f₁` along `ν` (`exists_marginal`), `δ₁ = ∫ |w|` for `w = 𝟙_{[L,∞)} - f₁`
by Fubini (the fibers of `H_ν` are all or nothing), `∫ |s - L| |w| = q(m) - |F̂|`
(`bathtub1d_gap`), and Markov on the strip `|s - L| ≤ √(2π) δ₁ / 4` (`gaussianReal_Icc_le`).
Proved.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

namespace QBath

theorem inner_hermite1 (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (u : Gs n) : ⟪u, hermite1 g⟫ = ∫ x, ⟪u, x⟫ * g x ∂gm n := by
  have hint : Integrable (fun x : Gs n ↦ g x • x) (gm n) := by
    refine Integrable.mono' (IsGaussian.integrable_id.norm)
      (hg.smul measurable_id).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have := Static.abs_le_one h01 x
    simp only [id]
    nlinarith [norm_nonneg x]
  rw [hermite1, ← integral_inner hint u]
  congr 1; funext x
  rw [real_inner_smul_right, mul_comm]

theorem abs_sub_ind (L s a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    |a - (Ici L).indicator 1 s| =
      (Ici L).indicator 1 s + (1 - 2 * (Ici L).indicator 1 s) * a := by
  by_cases h : s ∈ Ici L
  · rw [indicator_of_mem h, Pi.one_apply, abs_of_nonpos (by linarith [ha.2])]
    ring
  · rw [indicator_of_notMem h, abs_of_nonneg (by linarith [ha.1])]
    ring

theorem halfInd_eq (ν : Gs n) (L : ℝ) (x : Gs n) :
    halfInd ν L x = (Ici L).indicator 1 ⟪ν, x⟫ := by
  by_cases h : L ≤ ⟪ν, x⟫
  · rw [halfInd, indicator_of_mem (show x ∈ {x | L ≤ ⟪ν, x⟫} from h),
      indicator_of_mem (show ⟪ν, x⟫ ∈ Ici L from h), Pi.one_apply, Pi.one_apply]
  · rw [halfInd, indicator_of_notMem (show x ∉ {x | L ≤ ⟪ν, x⟫} from h),
      indicator_of_notMem (show ⟪ν, x⟫ ∉ Ici L from h)]

end QBath

open QBath Static1D

/-- **Quantitative bathtub** (Lemma 4.8). -/
theorem qbath (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) (ν : Gs n) (hν : ‖ν‖ = 1)
    (hF : hermite1 f = ‖hermite1 f‖ • ν) :
    √(2 * π) / 8 * (∫ x, |f x - halfInd ν (-Psi (gMean f)) x| ∂gm n) ^ 2 ≤
        qf (gMean f) - ‖hermite1 f‖ ∧
      lam (gMean f) / 4 * (∫ x, |f x - halfInd ν (-Psi (gMean f)) x| ∂gm n) ^ 2 ≤ epsF f := by
  obtain ⟨m, hmdef⟩ : ∃ m, gMean f = m := ⟨_, rfl⟩
  rw [hmdef] at hm ⊢
  obtain ⟨f₁, hf₁, hf01, hφ⟩ := exists_marginal f hf h01 ν hν
  -- the mean and the first moment of the marginal
  have hS : ∫ s, f₁ s ∂gaussianReal 0 1 = m := by
    have := hφ (fun _ ↦ 1) measurable_const ⟨1, fun s ↦ by rw [abs_one]; nlinarith [sq_nonneg s]⟩
    simp only [one_mul] at this
    rw [← this, ← hmdef, gMean]
  have hU : ‖hermite1 f‖ = ∫ s, s * f₁ s ∂gaussianReal 0 1 := by
    have h1 : ⟪ν, hermite1 f⟫ = ‖hermite1 f‖ := by
      conv_lhs => rw [hF]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hν]; ring
    rw [← h1, inner_hermite1 f hf h01 ν]
    exact hφ id measurable_id ⟨1, fun s ↦ by simp only [id]; nlinarith [abs_nonneg s, sq_abs s]⟩
  -- `δ₁ = ∫ |w|`
  obtain ⟨L, hL⟩ : ∃ L, L = -Psi m := ⟨_, rfl⟩
  rw [← hL]
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : ℝ → ℝ, ψ₀ = (Ici L).indicator 1 := ⟨_, rfl⟩
  have hψ₀m : Measurable ψ₀ := hψ₀ ▸ measurable_ind L
  have hψ₀b : ∀ s, 0 ≤ ψ₀ s ∧ ψ₀ s ≤ 1 := fun s ↦ hψ₀ ▸ ind_mem L s
  have hψ₁m : Measurable fun s ↦ 1 - 2 * ψ₀ s := measurable_const.sub (hψ₀m.const_mul 2)
  have hψ₁b : ∀ s, |1 - 2 * ψ₀ s| ≤ 1 := fun s ↦ by
    have := hψ₀b s; rw [abs_le]; constructor <;> linarith
  have hδ : ∫ x, |f x - halfInd ν L x| ∂gm n = ∫ s, |f₁ s - ψ₀ s| ∂gaussianReal 0 1 := by
    have e1 : ∀ x, |f x - halfInd ν L x| = ψ₀ ⟪ν, x⟫ + (1 - 2 * ψ₀ ⟪ν, x⟫) * f x := fun x ↦ by
      rw [halfInd_eq, hψ₀]; exact abs_sub_ind L _ _ (h01 x)
    have e2 : ∀ s, |f₁ s - ψ₀ s| = ψ₀ s + (1 - 2 * ψ₀ s) * f₁ s := fun s ↦ by
      rw [hψ₀]; exact abs_sub_ind L _ _ (hf01 s)
    simp_rw [e1, e2]
    have I1 : Integrable (fun x : Gs n ↦ ψ₀ ⟪ν, x⟫) (gm n) :=
      Static.integrable_of_bdd (hψ₀m.comp (by fun_prop)) (C := 1) fun x ↦ by
        have := hψ₀b ⟪ν, x⟫; rw [abs_le]; constructor <;> linarith
    have I2 : Integrable (fun x : Gs n ↦ (1 - 2 * ψ₀ ⟪ν, x⟫) * f x) (gm n) :=
      Static.integrable_comp_inner_mul hf h01 ν hψ₁m (C := 1) fun s ↦ by
        have := hψ₁b s; nlinarith [sq_nonneg s]
    have J1 : Integrable ψ₀ (gaussianReal 0 1) := integrable_of_bdd hψ₀m (abs_le_one hψ₀b)
    have J2 : Integrable (fun s ↦ (1 - 2 * ψ₀ s) * f₁ s) (gaussianReal 0 1) :=
      integrable_mul_of_bdd (integrable_of_bdd hψ₁m hψ₁b) hf₁ (abs_le_one hf01)
    rw [integral_add I1 I2, integral_add J1 J2,
      hφ _ hψ₁m ⟨1, fun s ↦ by have := hψ₁b s; nlinarith [sq_nonneg s]⟩]
    congr 1
    rw [← Gaussian.map_inner_stdGaussian hν, integral_map (by fun_prop) hψ₀m.aestronglyMeasurable]
  rw [hδ]
  obtain ⟨δ, hδdef⟩ : ∃ δ, ∫ s, |f₁ s - ψ₀ s| ∂gaussianReal 0 1 = δ := ⟨_, rfl⟩
  rw [hδdef]
  have hδ0 : 0 ≤ δ := hδdef ▸ integral_nonneg fun s ↦ abs_nonneg _
  -- the bathtub identities
  obtain ⟨g1, -, g3⟩ := bathtub1d_gap f₁ hf₁ hf01 hS hm
  rw [← hL, ← hψ₀] at g1 g3
  rw [← hU] at g3
  -- Markov on the strip `|s - L| ≤ θ`
  obtain ⟨c, hc⟩ : ∃ c, c = √(2 * π) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = c * δ / 4 := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hpt : ∀ s, θ * (|f₁ s - ψ₀ s| - (Icc (L - θ) (L + θ)).indicator 1 s) ≤
      (s + Psi m) * (ψ₀ s - f₁ s) := by
    intro s
    have hp := g1 s
    have hw1 : |f₁ s - ψ₀ s| ≤ 1 := by
      have := hψ₀b s; have := hf01 s; rw [abs_le]; constructor <;> linarith
    by_cases hs : s ∈ Icc (L - θ) (L + θ)
    · rw [indicator_of_mem hs, Pi.one_apply]
      have : θ * (|f₁ s - ψ₀ s| - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθ0 (by linarith)
      linarith
    · rw [indicator_of_notMem hs, sub_zero]
      have hfar : θ ≤ |s + Psi m| := by
        simp only [mem_Icc, not_and_or, not_le] at hs
        rw [hL] at hs
        rcases hs with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have heq : (s + Psi m) * (ψ₀ s - f₁ s) = |s + Psi m| * |f₁ s - ψ₀ s| := by
        rw [abs_sub_comm, ← abs_mul, abs_of_nonneg hp]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hfar (abs_nonneg _)
  have Iabs : Integrable (fun s ↦ |f₁ s - ψ₀ s|) (gaussianReal 0 1) :=
    integrable_of_bdd (continuous_abs.measurable.comp (hf₁.sub hψ₀m)) (C := 1) fun s ↦ by
      rw [abs_abs]; have := hψ₀b s; have := hf01 s; rw [abs_le]; constructor <;> linarith
  have Iind : Integrable ((Icc (L - θ) (L + θ)).indicator (1 : ℝ → ℝ)) (gaussianReal 0 1) :=
    integrable_of_bdd (measurable_one.indicator measurableSet_Icc) (C := 1) fun s ↦ by
      by_cases h : s ∈ Icc (L - θ) (L + θ) <;> simp [h]
  have Irhs : Integrable (fun s ↦ (s + Psi m) * (ψ₀ s - f₁ s)) (gaussianReal 0 1) :=
    integrable_mul_of_bdd (integrable_add _) (hψ₀m.sub hf₁) (C := 1) fun s ↦ by
      have := hψ₀b s; have := hf01 s; rw [abs_le]; constructor <;> linarith
  have Isub : Integrable (fun s ↦ θ * (|f₁ s - ψ₀ s| - (Icc (L - θ) (L + θ)).indicator 1 s))
      (gaussianReal 0 1) := (Iabs.sub Iind).const_mul θ
  have hmono := integral_mono Isub Irhs hpt
  rw [integral_const_mul, integral_sub Iabs Iind, hδdef, g3,
    integral_indicator_one measurableSet_Icc] at hmono
  have hstrip := gaussianReal_Icc_le (show L - θ ≤ L + θ by linarith)
  rw [← hc] at hstrip
  have hstrip' : (gaussianReal 0 1).real (Icc (L - θ) (L + θ)) ≤ δ / 2 := by
    calc _ ≤ (L + θ - (L - θ)) / c := hstrip
      _ = δ / 2 := by rw [hθ]; field_simp; ring
  have hfirst : c / 8 * δ ^ 2 ≤ qf m - ‖hermite1 f‖ := by
    have := mul_le_mul_of_nonneg_left hstrip' hθ0
    have e : c / 8 * δ ^ 2 = θ * (δ - δ / 2) := by rw [hθ]; ring
    rw [e]
    nlinarith
  refine ⟨hc ▸ hfirst, ?_⟩
  -- `ε ≥ q(m) (q(m) - |F̂|) ≥ √(2/π) λ (√(2π)/8) δ²`
  have hqU := norm_hermite1_le f hf h01
  rw [hmdef] at hqU
  have hU0 := norm_nonneg (hermite1 f)
  have hq := qf_ge_lam (Ioo_subset_Icc_self hm)
  have hlam0 : 0 ≤ lam m := by unfold lam; nlinarith [hm.1, hm.2]
  have heps : epsF f = (qf m - ‖hermite1 f‖) * (qf m + ‖hermite1 f‖) := by
    rw [epsF, hmdef]; ring
  have hcc : √(2 / π) * c = 2 := by
    rw [hc, ← Real.sqrt_mul (by positivity)]
    rw [show 2 / π * (2 * π) = 2 ^ 2 by field_simp]
    exact Real.sqrt_sq (by norm_num)
  have hsq0 : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
  calc lam m / 4 * δ ^ 2 = (√(2 / π) * lam m) * (c / 8 * δ ^ 2) := by
        rw [show (√(2 / π) * lam m) * (c / 8 * δ ^ 2) = (√(2 / π) * c) * lam m / 8 * δ ^ 2 by
          ring, hcc]
        ring
    _ ≤ qf m * (qf m - ‖hermite1 f‖) :=
        mul_le_mul hq hfirst (by positivity) (qf_nonneg _)
    _ ≤ (qf m - ‖hermite1 f‖) * (qf m + ‖hermite1 f‖) := by nlinarith
    _ = epsF f := heps.symm

end BGHKLMM26.RobustMIS
