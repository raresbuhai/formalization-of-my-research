module

public import BDT24.LowDeg.Defs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality

/-!
# The low-degree advantage from Hermite coefficients

`BDT24.LowDeg.advantage_le_of_hermite`: if the coordinates `x` of the points have independent
standard Gaussian law under `Q`, every polynomial `f` of total degree at most `D` is a combination
`∑_{|α| ≤ D} c_α H_α` of multivariate Hermite polynomials (each power `Xᵢ^k` is a combination of
the `He_j(Xᵢ)` with `j ≤ k`, as `He_n` is monic of degree `n`, and a monomial `X^β` is a product of
such powers, so it expands into the `H_γ` with `γ ≤ β`). Under `Q` they are orthogonal with
`E H_α² = α!` (the product of the one-dimensional orthogonality of `He_n`, e.g. TauCeti's
`integral_hermite_mul_hermite_gaussianReal`), so `E_Q f = c_0` and `Var_Q f = ∑_{α ≠ 0} c_α² α!`.
Then `E_P f - E_Q f = ∑_{0 < |α| ≤ D} c_α E_P H_α` (as `E_P H_0 = 1`), which by Cauchy–Schwarz is
at most `√(∑_{0 < |α| ≤ D} (E_P H_α)² / α!) · √(Var_Q f)`. This is the norm of the low-degree
likelihood ratio, without the likelihood ratio.
-/

@[expose] public section

namespace BDT24.LowDeg.HM

open MeasureTheory ProbabilityTheory Polynomial

/-- The real Hermite polynomial `He_j`. -/
noncomputable abbrev hermR (j : ℕ) : ℝ[X] := (hermite j).map (algebraMap ℤ ℝ)

/-- Every real polynomial of degree at most `k` is a combination of `He_0, …, He_k`. -/
theorem exists_hermR_comb_of_natDegree_le (k : ℕ) : ∀ p : ℝ[X], p.natDegree ≤ k →
    ∃ c : ℕ → ℝ, p = ∑ j ∈ Finset.range (k + 1), c j • hermR j := by
  induction k with
  | zero =>
    intro p hp
    refine ⟨fun _ ↦ p.coeff 0, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]
    simp [hermR, Polynomial.smul_eq_C_mul]
  | succ k ih =>
    intro p hp
    set a := p.coeff (k + 1)
    obtain ⟨c, hc⟩ := ih (p - a • hermR (k + 1)) <| by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
      rw [Polynomial.coeff_sub, Polynomial.coeff_smul, Polynomial.coeff_map, smul_eq_mul]
      rcases (Nat.succ_le_of_lt hN).eq_or_lt with h | h
      · rw [← h, Polynomial.coeff_hermite_self]
        simp [a]
      · rw [Polynomial.coeff_hermite_of_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt
          (hp.trans_lt h)]
        simp
    refine ⟨fun j ↦ if j = k + 1 then a else c j, ?_⟩
    have hs : ∑ j ∈ Finset.range (k + 1), (if j = k + 1 then a else c j) • hermR j =
        ∑ j ∈ Finset.range (k + 1), c j • hermR j :=
      Finset.sum_congr rfl fun j hj ↦ by
        simp [(Finset.mem_range.mp hj).ne]
    rw [Finset.sum_range_succ (n := k + 1)]
    simp only [↓reduceIte]
    rw [hs, ← hc]
    abel

/-- `t^k = ∑_{j ≤ k} c_{k,j} He_j(t)` in every real algebra. -/
theorem exists_pow_eq_hermite_comb (k : ℕ) : ∃ c : ℕ → ℝ, ∀ {A : Type*} [CommRing A]
    [Algebra ℝ A] (t : A),
      t ^ k = ∑ j ∈ Finset.range (k + 1), algebraMap ℝ A (c j) * aeval t (hermite j) := by
  obtain ⟨c, hc⟩ := exists_hermR_comb_of_natDegree_le k (X ^ k) (by simp)
  refine ⟨c, fun {A} _ _ t ↦ ?_⟩
  have := congrArg (aeval t) hc
  simpa [map_sum, map_smul, Polynomial.aeval_map_algebraMap, Algebra.smul_def] using this

variable {ι : Type} [Fintype ι]

/-- **Every polynomial of total degree at most `D` is a combination of the `H_α` with
`|α| ≤ D`.** Each monomial `∏ᵢ Xᵢ^{βᵢ}` expands, coordinate by coordinate, into the `He_j(Xᵢ)`
with `j ≤ βᵢ`. -/
theorem exists_hermiteMv_comb [DecidableEq ι] (D : ℕ) (f : MvPolynomial ι ℝ)
    (hf : f.totalDegree ≤ D) :
    ∃ c : (ι → ℕ) → ℝ, f = ∑ α ∈ degSet ι D, c α • hermiteMv α := by
  choose c hc using exists_pow_eq_hermite_comb
  suffices h : f ∈ Submodule.span ℝ (hermiteMv '' (degSet ι D : Set (ι → ℕ))) by
    obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp h
    exact ⟨a, ha.symm⟩
  rw [MvPolynomial.as_sum f]
  refine Submodule.sum_mem _ fun v hv ↦ ?_
  have hdeg : ∑ i, v i ≤ D := by
    have := MvPolynomial.le_totalDegree hv
    rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl] at this
    omega
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_mul', Finsupp.prod_pow]
  refine Submodule.smul_mem _ _ ?_
  rw [Finset.prod_congr rfl fun i _ ↦ hc (v i) (MvPolynomial.X i : MvPolynomial ι ℝ),
    Finset.prod_univ_sum]
  refine Submodule.sum_mem _ fun γ hγ ↦ ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, ?_, rfl⟩)
  simp only [Fintype.mem_piFinset, Finset.mem_range] at hγ
  have hsum : ∑ i, γ i ≤ D :=
    (Finset.sum_le_sum fun i _ ↦ Nat.lt_succ_iff.mp (hγ i)).trans hdeg
  simp only [degSet, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨fun i ↦ Nat.lt_succ_iff.mpr ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (γ j))
    (Finset.mem_univ i)).trans hsum), hsum⟩

/-- `H_α(y) = ∏ᵢ He_{αᵢ}(yᵢ)`. -/
theorem eval_hermiteMv (α : ι → ℕ) (y : ι → ℝ) :
    MvPolynomial.eval y (hermiteMv α) = ∏ i, aeval (y i) (hermite (α i)) := by
  simp only [hermiteMv, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.eval y).toIntAlgHom
    (MvPolynomial.X i : MvPolynomial ι ℝ) (hermite (α i))
  simpa using h.symm

/-- Every polynomial is integrable under independent standard Gaussians. -/
theorem integrable_eval (p : MvPolynomial ι ℝ) :
    Integrable (fun y ↦ MvPolynomial.eval y p) (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
    exact (Integrable.fintype_prod (f := fun i t ↦ t ^ u i)
      fun i ↦ TauCeti.integrable_pow_gaussianReal 0 1 (u i)).const_mul a
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq

/-- `α! > 0`. -/
theorem multiFact_pos (α : ι → ℕ) : 0 < multiFact α :=
  Finset.prod_pos fun i _ ↦ by positivity

/-- **Orthogonality**: `E H_α H_β = if α = β then α! else 0` under independent standard
Gaussians. -/
theorem integral_hermiteMv_mul (α β : ι → ℕ) :
    ∫ y, MvPolynomial.eval y (hermiteMv α) * MvPolynomial.eval y (hermiteMv β)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = if α = β then multiFact α else 0 := by
  simp_rw [eval_hermiteMv, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (f := fun i t ↦ aeval t (hermite (α i)) * aeval t (hermite (β i)))]
  simp_rw [TauCeti.integral_hermite_mul_hermite_gaussianReal]
  split_ifs with h
  · subst h
    simp [multiFact]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- `H_0 = 1`. -/
theorem hermiteMv_zero : hermiteMv (0 : ι → ℕ) = 1 := by
  simp [hermiteMv]

/-- `E H_α = if α = 0 then 1 else 0` under independent standard Gaussians. -/
theorem integral_hermiteMv (α : ι → ℕ) :
    ∫ y, MvPolynomial.eval y (hermiteMv α) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) =
      if α = 0 then 1 else 0 := by
  have h := integral_hermiteMv_mul α 0
  simp only [hermiteMv_zero, map_one, mul_one] at h
  rw [h]
  split_ifs with h0
  · subst h0
    simp [multiFact]
  · rfl


/-- `E ∑_{α ∈ S} a_α H_α = a_0` under independent standard Gaussians, when `0 ∈ S`. -/
theorem integral_sum_hermiteMv (S : Finset (ι → ℕ)) (h0 : 0 ∈ S) (a : (ι → ℕ) → ℝ) :
    ∫ y, ∑ α ∈ S, a α * MvPolynomial.eval y (hermiteMv α)
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = a 0 := by
  rw [integral_finsetSum _ fun α _ ↦ (integrable_eval _).const_mul _]
  simp_rw [integral_const_mul, integral_hermiteMv, mul_ite, mul_one, mul_zero]
  simp [h0]

/-- `E (∑_{α ∈ S} a_α H_α)(∑_{β ∈ S} b_β H_β) = ∑_{α ∈ S} a_α b_α α!` under independent standard
Gaussians. -/
theorem integral_sum_mul_sum_hermiteMv (S : Finset (ι → ℕ)) (a b : (ι → ℕ) → ℝ) :
    ∫ y, (∑ α ∈ S, a α * MvPolynomial.eval y (hermiteMv α)) *
        (∑ β ∈ S, b β * MvPolynomial.eval y (hermiteMv β))
      ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = ∑ α ∈ S, a α * b α * multiFact α := by
  have hfun : ∀ α β, (fun y : ι → ℝ ↦ a α * MvPolynomial.eval y (hermiteMv α) *
      (b β * MvPolynomial.eval y (hermiteMv β))) = fun y ↦ (a α * b β) *
        (MvPolynomial.eval y (hermiteMv α) * MvPolynomial.eval y (hermiteMv β)) := fun α β ↦ by
    ext y
    ring
  have hint : ∀ α β, Integrable (fun y : ι → ℝ ↦ a α * MvPolynomial.eval y (hermiteMv α) *
      (b β * MvPolynomial.eval y (hermiteMv β))) (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    fun α β ↦ by
      rw [hfun]
      simpa only [map_mul] using (integrable_eval (hermiteMv α * hermiteMv β)).const_mul _
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun α _ ↦ integrable_finsetSum _ fun β _ ↦ hint α β]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  rw [integral_finsetSum _ fun β _ ↦ hint α β]
  simp_rw [hfun, integral_const_mul, integral_hermiteMv_mul, mul_ite, mul_zero]
  simp [hα]

end BDT24.LowDeg.HM

namespace BDT24.LowDeg

open MeasureTheory ProbabilityTheory

/-- **The advantage is at most the norm of the Hermite coefficients.** -/
theorem advantage_le_of_hermite {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (x : Ω → ι → ℝ) (hx : Measurable x) (P Q : Measure Ω) [IsProbabilityMeasure P]
    (hQ : Q.map x = Measure.pi fun _ : ι ↦ gaussianReal 0 1)
    (hP : ∀ f : MvPolynomial ι ℝ, Integrable (fun ω ↦ MvPolynomial.eval (x ω) f) P)
    (D : ℕ) {B : ℝ}
    (hB : ∑ α ∈ (degSet ι D).filter (· ≠ 0),
      (∫ ω, MvPolynomial.eval (x ω) (hermiteMv α) ∂P) ^ 2 / multiFact α ≤ B) :
    AdvantageAtMost x D P Q (√B) := by
  intro f hf
  have hfD : f.totalDegree ≤ D := by exact_mod_cast hf
  have : IsProbabilityMeasure Q := by
    constructor
    have h := congrArg (fun m : Measure (ι → ℝ) ↦ m Set.univ) hQ
    simpa only [Measure.map_apply hx MeasurableSet.univ, Set.preimage_univ, measure_univ]
      using h
  have hxa : AEMeasurable x Q := hx.aemeasurable
  have hcont : Continuous fun y : ι → ℝ ↦ MvPolynomial.eval y f := MvPolynomial.continuous_eval f
  have hmemμ : MemLp (fun y ↦ MvPolynomial.eval y f) 2
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).mpr ?_
    exact (HM.integrable_eval (f ^ 2)).congr (ae_of_all _ fun y ↦ MvPolynomial.eval_pow _)
  have hmemQ : MemLp (fun ω ↦ MvPolynomial.eval (x ω) f) 2 Q := by
    rw [← hQ] at hmemμ
    exact (memLp_map_measure_iff hcont.aestronglyMeasurable hxa).mp hmemμ
  refine ⟨hP f, hmemQ, ?_⟩
  obtain ⟨c, hc⟩ := HM.exists_hermiteMv_comb D f hfD
  set S := degSet ι D with hS
  have h0 : (0 : ι → ℕ) ∈ S := by simp [hS, degSet]
  have hev : ∀ y, MvPolynomial.eval y f = ∑ α ∈ S, c α * MvPolynomial.eval y (hermiteMv α) :=
    fun y ↦ by
      rw [hc]
      simp [map_sum, MvPolynomial.smul_eval]
  have hEμ : ∫ y, MvPolynomial.eval y f ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = c 0 := by
    simp_rw [hev]
    exact HM.integral_sum_hermiteMv S h0 c
  have hEQ : ∫ ω, MvPolynomial.eval (x ω) f ∂Q = c 0 := by
    have h := integral_map hxa (f := fun y : ι → ℝ ↦ MvPolynomial.eval y f)
      (hQ ▸ hcont.aestronglyMeasurable)
    rw [hQ, hEμ] at h
    exact h.symm
  have hVar : variance (fun ω ↦ MvPolynomial.eval (x ω) f) Q =
      ∑ α ∈ S.erase 0, c α ^ 2 * multiFact α := by
    have h := variance_map (X := fun y : ι → ℝ ↦ MvPolynomial.eval y f) (μ := Q) (Y := x)
      (hQ ▸ hcont.measurable.aemeasurable) hxa
    rw [hQ] at h
    rw [show (fun ω ↦ MvPolynomial.eval (x ω) f) = (fun y ↦ MvPolynomial.eval y f) ∘ x from rfl,
      ← h, variance_eq_sub hmemμ, hEμ]
    have e1 : ∫ y, ((fun y ↦ MvPolynomial.eval y f) ^ 2) y
        ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = ∑ α ∈ S, c α * c α * multiFact α := by
      simp only [Pi.pow_apply, sq, hev]
      exact HM.integral_sum_mul_sum_hermiteMv S c c
    rw [e1, ← Finset.add_sum_erase S _ h0]
    simp [multiFact, sq]
  set e : (ι → ℕ) → ℝ := fun α ↦ ∫ ω, MvPolynomial.eval (x ω) (hermiteMv α) ∂P with he
  have hEP : ∫ ω, MvPolynomial.eval (x ω) f ∂P = ∑ α ∈ S, c α * e α := by
    simp_rw [hev]
    rw [integral_finsetSum _ fun α _ ↦ (hP _).const_mul _]
    simp_rw [integral_const_mul]
    rfl
  have he0 : e 0 = 1 := by simp [he, HM.hermiteMv_zero]
  have hdiff : (∫ ω, MvPolynomial.eval (x ω) f ∂P) - ∫ ω, MvPolynomial.eval (x ω) f ∂Q =
      ∑ α ∈ S.erase 0, c α * e α := by
    rw [hEP, hEQ, ← Finset.add_sum_erase S _ h0, he0]
    ring
  rw [hdiff, hVar]
  rw [Finset.filter_ne'] at hB
  set S' := S.erase 0
  have hm : ∀ α : ι → ℕ, 0 < multiFact α := HM.multiFact_pos
  have hCS : (∑ α ∈ S', c α * e α) ^ 2 ≤
      (∑ α ∈ S', c α ^ 2 * multiFact α) * ∑ α ∈ S', e α ^ 2 / multiFact α := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S' (fun α ↦ c α * √(multiFact α))
      (fun α ↦ e α / √(multiFact α))
    have h1 : ∀ α, c α * √(multiFact α) * (e α / √(multiFact α)) = c α * e α := fun α ↦ by
      have := (Real.sqrt_pos.mpr (hm α)).ne'
      field_simp
    have h2 : ∀ α, (c α * √(multiFact α)) ^ 2 = c α ^ 2 * multiFact α := fun α ↦ by
      rw [mul_pow, Real.sq_sqrt (hm α).le]
    have h3 : ∀ α, (e α / √(multiFact α)) ^ 2 = e α ^ 2 / multiFact α := fun α ↦ by
      rw [div_pow, Real.sq_sqrt (hm α).le]
    simpa only [h1, h2, h3] using h
  have hV : 0 ≤ ∑ α ∈ S', c α ^ 2 * multiFact α :=
    Finset.sum_nonneg fun α _ ↦ mul_nonneg (sq_nonneg _) (hm α).le
  have hB' : ∑ α ∈ S', e α ^ 2 / multiFact α ≤ B := hB
  calc ∑ α ∈ S', c α * e α ≤ |∑ α ∈ S', c α * e α| := le_abs_self _
    _ ≤ √((∑ α ∈ S', c α ^ 2 * multiFact α) * B) :=
      Real.abs_le_sqrt (hCS.trans (mul_le_mul_of_nonneg_left hB' hV))
    _ = √B * √(∑ α ∈ S', c α ^ 2 * multiFact α) := by rw [Real.sqrt_mul hV, mul_comm]

end BDT24.LowDeg
