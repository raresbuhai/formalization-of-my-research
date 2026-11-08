module

public import BHJK25.Spectral.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Projections on one coordinate of a product measure

For `φ` on `(Fin m → ℝ) × Ω` under `(μ^m) ⊗ ν`, the projection on coordinate `i` is
`Gᵢ(x) = E[φ(λ with λᵢ := x, ω)]` (`BHJK25.Spectral.proj`). Its mean is that of `φ`, its variances
add up to at most the variance of `φ` (the projections on different coordinates are orthogonal),
and replacing `μ` by a point mass `δ_s` at coordinate `i` turns the mean of `φ` into `Gᵢ(s)`.
When `x ↦ φ(λ with λᵢ := x, ω)` is a polynomial of degree at most `d` for every `(λ, ω)`, so is
`Gᵢ` (Lagrange interpolation).
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Polynomial

variable {m : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The projection of `φ` on coordinate `i`: `Gᵢ(x) = E[φ(λ with λᵢ := x, ω)]`. -/
noncomputable def proj (μ : Measure ℝ) (ν : Measure Ω) (φ : (Fin m → ℝ) × Ω → ℝ) (i : Fin m)
    (x : ℝ) : ℝ :=
  ∫ p, φ (Function.update p.1 i x, p.2) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν)

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]

namespace ProjAux

/-- The map `(x, (λ, ω)) ↦ (λ with λᵢ := x, ω)`. -/
def updateProd (i : Fin m) (q : ℝ × ((Fin m → ℝ) × Ω)) : (Fin m → ℝ) × Ω :=
  (Function.update q.2.1 i q.1, q.2.2)

theorem measurable_updateProd (i : Fin m) : Measurable (updateProd (Ω := Ω) i) := by
  unfold updateProd
  fun_prop

/-- Drawing `x ∼ ρ` and `λ ∼ μ^m` independently and setting `λᵢ := x` gives `μ^m` with the
`i`-th factor replaced by `ρ`. -/
theorem pi_update_eq_map (i : Fin m) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Measure.pi (Function.update (fun _ : Fin m ↦ μ) i ρ) =
      (ρ.prod (Measure.pi fun _ : Fin m ↦ μ)).map fun q ↦ Function.update q.2 i q.1 := by
  have : ∀ j, IsProbabilityMeasure (Function.update (fun _ : Fin m ↦ μ) i ρ j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; infer_instance
    · rw [Function.update_of_ne hj]; infer_instance
  refine Measure.pi_eq fun t ht ↦ ?_
  have hpre : (fun q : ℝ × (Fin m → ℝ) ↦ Function.update q.2 i q.1) ⁻¹' Set.univ.pi t =
      t i ×ˢ Set.univ.pi (Function.update t i Set.univ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j ↦ ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨hx, hl⟩ j
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [Function.update_of_ne hj] using hl j
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi ht), hpre, Measure.prod_prod,
    Measure.pi_pi,
    ← Finset.mul_prod_erase (M := ENNReal) Finset.univ
      (fun j ↦ μ (Function.update t i Set.univ j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase (M := ENNReal) Finset.univ
      (fun j ↦ Function.update (fun _ : Fin m ↦ μ) i ρ j (t j)) (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  refine congrArg _ (Finset.prod_congr rfl fun j hj ↦ ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
    Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Resampling coordinate `i` of an i.i.d. vector does not change its law. -/
theorem measurePreserving_update (i : Fin m) :
    MeasurePreserving (fun q : ℝ × (Fin m → ℝ) ↦ Function.update q.2 i q.1)
      (μ.prod (Measure.pi fun _ : Fin m ↦ μ)) (Measure.pi fun _ : Fin m ↦ μ) where
  measurable := by fun_prop
  map_eq := by rw [← pi_update_eq_map μ i μ, Function.update_eq_self]

theorem measurePreserving_updateProd (i : Fin m) :
    MeasurePreserving (updateProd (Ω := Ω) i) (μ.prod ((Measure.pi fun _ : Fin m ↦ μ).prod ν))
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν) :=
  ((measurePreserving_update μ i).prod (MeasurePreserving.id ν)).comp
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc μ (Measure.pi fun _ : Fin m ↦ μ) ν))

theorem measurePreserving_evalFst (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → ℝ) × Ω ↦ p.1 i) ((Measure.pi fun _ : Fin m ↦ μ).prod ν)
      μ :=
  (measurePreserving_eval (fun _ : Fin m ↦ μ) i).comp measurePreserving_fst

/-- Integrating first over coordinate `i` separately: `E ψ = E_x E_{λ, ω} ψ(λ with λᵢ := x, ω)`. -/
theorem integral_eq_integral_update {ψ : (Fin m → ℝ) × Ω → ℝ}
    (hψ : Integrable ψ ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) (i : Fin m) :
    ∫ p, ψ p ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) =
      ∫ x, ∫ p, ψ (Function.update p.1 i x, p.2) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) ∂μ := by
  have hT := measurePreserving_updateProd μ ν i
  calc ∫ p, ψ p ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν)
      = ∫ p, ψ p ∂((μ.prod ((Measure.pi fun _ : Fin m ↦ μ).prod ν)).map (updateProd i)) := by
        rw [hT.map_eq]
    _ = ∫ q, ψ (updateProd i q) ∂(μ.prod ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) :=
        integral_map hT.aemeasurable (by rw [hT.map_eq]; exact hψ.1)
    _ = _ := integral_prod _ (hT.integrable_comp_of_integrable hψ)

theorem integral_comp_eval {g : ℝ → ℝ} (hg : AEStronglyMeasurable g μ) (i : Fin m) :
    ∫ p, g (p.1 i) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) = ∫ x, g x ∂μ := by
  have hE := measurePreserving_evalFst μ ν i
  calc ∫ p, g (p.1 i) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν)
      = ∫ x, g x ∂(((Measure.pi fun _ : Fin m ↦ μ).prod ν).map fun p ↦ p.1 i) :=
        (integral_map hE.aemeasurable (by rw [hE.map_eq]; exact hg)).symm
    _ = _ := by rw [hE.map_eq]

/-- Different coordinates are independent. -/
theorem integral_mul_comp_eval {g g' : ℝ → ℝ} (hg : MemLp g 2 μ) (hg' : MemLp g' 2 μ)
    {i j : Fin m} (hij : i ≠ j) :
    ∫ p, g (p.1 i) * g' (p.1 j) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) =
      (∫ x, g x ∂μ) * ∫ x, g' x ∂μ := by
  have hint : Integrable (fun p : (Fin m → ℝ) × Ω ↦ g (p.1 i) * g' (p.1 j))
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν) :=
    (hg.comp_measurePreserving (measurePreserving_evalFst μ ν i)).integrable_mul
      (hg'.comp_measurePreserving (measurePreserving_evalFst μ ν j))
  rw [integral_eq_integral_update μ ν hint i]
  calc _ = ∫ x, g x * ∫ y, g' y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [Function.update_self, Function.update_of_ne hij.symm]
        rw [integral_const_mul, integral_comp_eval μ ν hg'.aestronglyMeasurable j]
    _ = _ := integral_mul_const _ _

theorem measurable_proj {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ) (i : Fin m) :
    Measurable (proj μ ν φ i) :=
  ((hmeas.comp (measurable_updateProd i)).stronglyMeasurable.integral_prod_right'
    (ν := (Measure.pi fun _ : Fin m ↦ μ).prod ν)).measurable

/-- `Gᵢ ∈ L²(μ)` (Jensen: `Gᵢ(x)² ≤ E φ(λ with λᵢ := x, ω)²`). -/
theorem memLp_proj {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ)
    (hφ : MemLp φ 2 ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) (i : Fin m) :
    MemLp (proj μ ν φ i) 2 μ := by
  have hT := measurePreserving_updateProd μ ν i
  have hFm : Measurable (φ ∘ updateProd i) := hmeas.comp (measurable_updateProd i)
  have hF2 : Integrable (fun q ↦ (φ ∘ updateProd i) q ^ 2)
      (μ.prod ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) :=
    (hφ.comp_measurePreserving hT).integrable_sq
  have hpm := measurable_proj μ ν hmeas i
  refine (memLp_two_iff_integrable_sq hpm.aestronglyMeasurable).2 ?_
  refine hF2.integral_prod_left.mono' (hpm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hF2.prod_right_ae] with x hx
  have hxL : MemLp (fun p ↦ (φ ∘ updateProd i) (x, p)) 2
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν) :=
    (memLp_two_iff_integrable_sq (hFm.comp measurable_prodMk_left).aestronglyMeasurable).2 hx
  have hvar := variance_nonneg (fun p ↦ (φ ∘ updateProd i) (x, p))
    ((Measure.pi fun _ : Fin m ↦ μ).prod ν)
  rw [variance_eq_sub hxL] at hvar
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (∫ p, (φ ∘ updateProd i) (x, p) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν)) ^ 2 ≤ _
  simpa only [Pi.pow_apply, sub_nonneg] using hvar

theorem integral_mul_proj {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ)
    (hφ : MemLp φ 2 ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) (i : Fin m) :
    ∫ p, φ p * proj μ ν φ i (p.1 i) ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) =
      ∫ x, proj μ ν φ i x * proj μ ν φ i x ∂μ := by
  have hint : Integrable (fun p : (Fin m → ℝ) × Ω ↦ φ p * proj μ ν φ i (p.1 i))
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν) :=
    hφ.integrable_mul
      ((memLp_proj μ ν hmeas hφ i).comp_measurePreserving (measurePreserving_evalFst μ ν i))
  rw [integral_eq_integral_update μ ν hint i]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [Function.update_self]
  exact integral_mul_const _ _

end ProjAux

/-- The mean of `Gᵢ` under `μ` is the mean of `φ`. -/
theorem integral_proj {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ)
    (hφ : Integrable φ ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) (i : Fin m) :
    ∫ x, proj μ ν φ i x ∂μ = ∫ p, φ p ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) :=
  (ProjAux.integral_eq_integral_update μ ν ⟨hmeas.aestronglyMeasurable, hφ.2⟩ i).symm

/-- The variances of the projections add up to at most the variance of `φ`: the centered lifts
`Gᵢ(λᵢ) - E φ` are orthogonal, and each is the orthogonal projection of `φ - E φ` onto the
functions of `λᵢ` alone. -/
theorem sum_variance_proj_le {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ)
    (hφ : MemLp φ 2 ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) :
    ∑ i, variance (proj μ ν φ i) μ ≤ variance φ ((Measure.pi fun _ : Fin m ↦ μ).prod ν) := by
  have hφ1 := hφ.integrable one_le_two
  have hpm := ProjAux.measurable_proj μ ν hmeas
  have hpL := ProjAux.memLp_proj μ ν hmeas hφ
  -- the projections, lifted back to functions of `(λ, ω)`
  obtain ⟨X, hX⟩ : ∃ X : Fin m → (Fin m → ℝ) × Ω → ℝ, X = fun i p ↦ proj μ ν φ i (p.1 i) :=
    ⟨_, rfl⟩
  have hXL : ∀ i, MemLp (X i) 2 ((Measure.pi fun _ : Fin m ↦ μ).prod ν) := fun i ↦ by
    subst hX; exact (hpL i).comp_measurePreserving (ProjAux.measurePreserving_evalFst μ ν i)
  have hXmean : ∀ i, ∫ p, X i p ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) =
      ∫ p, φ p ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) := fun i ↦ by
    subst hX
    rw [ProjAux.integral_comp_eval μ ν (hpm i).aestronglyMeasurable, integral_proj μ ν hmeas hφ1]
  have hcovφ : ∀ i, cov[φ, X i; (Measure.pi fun _ : Fin m ↦ μ).prod ν] =
      variance (proj μ ν φ i) μ := fun i ↦ by
    rw [covariance_eq_sub hφ (hXL i), variance_eq_sub (hpL i), integral_proj μ ν hmeas hφ1,
      hXmean]
    subst hX
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [ProjAux.integral_mul_proj μ ν hmeas hφ i]
    simp only [sq]
  have hcov : ∀ i j, i ≠ j → cov[X i, X j; (Measure.pi fun _ : Fin m ↦ μ).prod ν] = 0 := by
    intro i j hij
    rw [covariance_eq_sub (hXL i) (hXL j), hXmean, hXmean]
    subst hX
    simp only [Pi.mul_apply]
    rw [ProjAux.integral_mul_comp_eval μ ν (hpL i) (hpL j) hij, integral_proj μ ν hmeas hφ1,
      integral_proj μ ν hmeas hφ1, sub_self]
  have hdiag : ∀ i, ∑ j, cov[X i, X j; (Measure.pi fun _ : Fin m ↦ μ).prod ν] =
      variance (proj μ ν φ i) μ := fun i ↦ by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ hcov i j (Ne.symm hj)) (by simp),
      covariance_self (hXL i).aemeasurable]
    subst hX
    exact (ProjAux.measurePreserving_evalFst μ ν i).variance_fun_comp (hpm i).aemeasurable
  have key := variance_nonneg (φ - ∑ i, X i) ((Measure.pi fun _ : Fin m ↦ μ).prod ν)
  rw [variance_sub hφ (memLp_finsetSum' _ fun i _ ↦ hXL i), covariance_sum_right hXL hφ,
    variance_sum hXL] at key
  simp only [hcovφ, hdiag] at key
  linarith

/-- Replacing the `i`-th factor `μ` by the point mass `δ_s` turns the mean of `φ` into `Gᵢ(s)`. -/
theorem integral_update_dirac {φ : (Fin m → ℝ) × Ω → ℝ} (hmeas : Measurable φ) (i : Fin m)
    (s : ℝ) :
    ∫ p, φ p ∂((Measure.pi (Function.update (fun _ : Fin m ↦ μ) i (Measure.dirac s))).prod ν) =
      proj μ ν φ i s := by
  have hf : Measurable fun l : Fin m → ℝ ↦ Function.update l i s := by fun_prop
  have h1 : Measure.pi (Function.update (fun _ : Fin m ↦ μ) i (Measure.dirac s)) =
      (Measure.pi fun _ : Fin m ↦ μ).map fun l ↦ Function.update l i s := by
    rw [ProjAux.pi_update_eq_map μ i (Measure.dirac s), Measure.dirac_prod,
      Measure.map_map (by fun_prop) measurable_prodMk_left]
    rfl
  have h2 : ((Measure.pi fun _ : Fin m ↦ μ).map fun l ↦ Function.update l i s).prod ν =
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν).map
        (Prod.map (fun l ↦ Function.update l i s) id) := by
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  rw [h1, h2, integral_map (by fun_prop) hmeas.aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- If every slice `x ↦ φ(λ with λᵢ := x, ω)` is a polynomial of degree at most `d`, so is `Gᵢ`:
each slice is the Lagrange interpolation of its values at `0, 1, …, d`, and so is their mean. -/
theorem proj_polynomial {φ : (Fin m → ℝ) × Ω → ℝ} (d : ℕ)
    (hpoly : ∀ (p : (Fin m → ℝ) × Ω) (i : Fin m), ∃ P : ℝ[X], P.natDegree ≤ d ∧
      ∀ x, φ (Function.update p.1 i x, p.2) = P.eval x)
    (hint : ∀ (i : Fin m) (x : ℝ), Integrable (fun p ↦ φ (Function.update p.1 i x, p.2))
      ((Measure.pi fun _ : Fin m ↦ μ).prod ν)) (i : Fin m) :
    ∃ P : ℝ[X], P.natDegree ≤ d ∧ ∀ x, proj μ ν φ i x = P.eval x := by
  -- interpolation nodes `0, 1, …, d`
  set v : Fin (d + 1) → ℝ := fun k ↦ ((k : ℕ) : ℝ)
  have hv : Set.InjOn v (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ hab ↦ Fin.ext (Nat.cast_injective hab)
  have hcard :
      ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) = ((d + 1 : ℕ) : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  refine ⟨Lagrange.interpolate Finset.univ v fun k ↦ proj μ ν φ i (v k), ?_, fun x ↦ ?_⟩
  · have hlt := Lagrange.degree_interpolate_lt (r := fun k ↦ proj μ ν φ i (v k)) hv
    rw [hcard] at hlt
    by_cases h0 : Lagrange.interpolate Finset.univ v (fun k ↦ proj μ ν φ i (v k)) = 0
    · rw [h0, natDegree_zero]
      exact Nat.zero_le _
    · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h0).mpr hlt)
  -- every slice is the interpolation of its values at the nodes
  have hslice : ∀ p : (Fin m → ℝ) × Ω, φ (Function.update p.1 i x, p.2) =
      ∑ k, φ (Function.update p.1 i (v k), p.2) * (Lagrange.basis Finset.univ v k).eval x := by
    intro p
    obtain ⟨Q, hQd, hQ⟩ := hpoly p i
    have hQlt : Q.degree < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
      rw [hcard]
      exact (degree_le_of_natDegree_le hQd).trans_lt (by exact_mod_cast Nat.lt_succ_self d)
    simp only [hQ]
    conv_lhs => rw [Lagrange.eq_interpolate hv hQlt]
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    simp only [eval_mul, eval_C]
  calc proj μ ν φ i x
      = ∫ p, ∑ k, φ (Function.update p.1 i (v k), p.2) * (Lagrange.basis Finset.univ v k).eval x
          ∂((Measure.pi fun _ : Fin m ↦ μ).prod ν) := integral_congr_ae (ae_of_all _ hslice)
    _ = ∑ k, proj μ ν φ i (v k) * (Lagrange.basis Finset.univ v k).eval x := by
        rw [integral_finsetSum _ fun k _ ↦ (hint i (v k)).mul_const _]
        exact Finset.sum_congr rfl fun k _ ↦ integral_mul_const _ _
    _ = _ := by
        rw [Lagrange.interpolate_apply, eval_finsetSum]
        simp only [eval_mul, eval_C]

end BHJK25.Spectral
