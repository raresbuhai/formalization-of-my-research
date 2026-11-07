module

public import BGHKLMM26.RobustMIS.Flow
public import BGHKLMM26.RobustMIS.Ito
public import BGHKLMM26.RobustMIS.Bessel

/-!
# Calculus toolkit for the generator computations (Deficit, Drift, Concentration)

Helper module of `Drift.lean`, `Deficit.lean`, `Concentration.lean` (§§6–8 of `eldan-proof.tex`):

* second derivatives and Laplacians of compositions `φ ∘ u` with `u` real-valued
  (`fderiv_fderiv_comp`, `laplacian_comp`, `norm_iteratedFDeriv_two_comp_le`): the identity
  `Δ(φ ∘ u) = φ''(u) |∇u|² + φ'(u) Δu` of (S8);
* the space slices `u(s, ·)` of the heat flow: smoothness, `∇u = (1-s)^{-1/2} U`, the static bounds
  `|∇u|² ≤ q(u)²/(1-s)`, `‖∇²u‖ ≤ n²/(1-s)`, `|Δu| ≤ n³/(1-s)` (dimension-dependent bounds suffice
  for `gauss_ito`), and `e = q(u)² - (1-s)|∇u|²` (`eFlow_eq`), `0 ≤ e ≤ q(u)²`;
* linearity of `iteratedFDeriv` and `Δ` on `F₁ - c Σₖ Gₖ` (`iteratedFDeriv_decomp`,
  `laplacian_decomp`);
* the derivatives of a space slice `u(s, ·)` are bounded by the joint derivatives of `u`
  (`norm_iteratedFDeriv_slice_le`), hence the third space derivatives of `u` are bounded on
  `[0, s₁] × ℝⁿ` (`bounded_iteratedFDeriv_three`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Drift

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace ContDiff

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_two_eq (F : E → ℝ) (x : E) :
    ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem norm_iteratedFDeriv_two_le_of {F : E → ℝ} {x : E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, |fderiv ℝ (fderiv ℝ F) x v w| ≤ C * ‖v‖ * ‖w‖) :
    ‖iteratedFDeriv ℝ 2 F x‖ ≤ C := by
  rw [norm_iteratedFDeriv_two_eq]
  exact ContinuousLinearMap.opNorm_le_bound₂ _ hC h

theorem abs_fderiv_fderiv_le (F : E → ℝ) (x v w : E) :
    |fderiv ℝ (fderiv ℝ F) x v w| ≤ ‖iteratedFDeriv ℝ 2 F x‖ * ‖v‖ * ‖w‖ := by
  rw [norm_iteratedFDeriv_two_eq]
  exact (fderiv ℝ (fderiv ℝ F) x).le_opNorm₂ v w

/-- The chain rule for `φ ∘ u` with `u` real-valued: the first derivative. -/
theorem fderiv_comp_eventually {u : E → ℝ} {φ φ' : ℝ → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ∀ᶠ a in 𝓝 (u x), HasDerivAt φ (φ' a) a) :
    fderiv ℝ (fun y ↦ φ (u y)) =ᶠ[𝓝 x] fun y ↦ φ' (u y) • fderiv ℝ u y := by
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hφy : ∀ᶠ y in 𝓝 x, HasDerivAt φ (φ' (u y)) (u y) := hu.continuousAt.eventually hφ
  filter_upwards [hdiff, hφy] with y h1 h2
  exact (h2.comp_hasFDerivAt y h1.hasFDerivAt).fderiv

theorem fderiv_comp_apply {u : E → ℝ} {φ φ' : ℝ → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ∀ᶠ a in 𝓝 (u x), HasDerivAt φ (φ' a) a) :
    fderiv ℝ (fun y ↦ φ (u y)) x = φ' (u x) • fderiv ℝ u x :=
  (fderiv_comp_eventually hu hφ).eq_of_nhds

/-- The chain rule for `φ ∘ u`: the second derivative. -/
theorem fderiv_fderiv_comp {u : E → ℝ} {φ φ' : ℝ → ℝ} {φ'' : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ∀ᶠ a in 𝓝 (u x), HasDerivAt φ (φ' a) a)
    (hφ' : HasDerivAt φ' φ'' (u x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ φ (u y))) x v w =
      φ'' * (fderiv ℝ u x v * fderiv ℝ u x w) + φ' (u x) * fderiv ℝ (fderiv ℝ u) x v w := by
  rw [(fderiv_comp_eventually hu hφ).fderiv_eq]
  have h1 : HasFDerivAt (fun y ↦ φ' (u y)) (φ'' • fderiv ℝ u x) x :=
    hφ'.comp_hasFDerivAt x (hu.differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have h3 := h1.smul h2
  rw [show (fun y ↦ φ' (u y) • fderiv ℝ u y) = (fun y ↦ φ' (u y)) • fderiv ℝ u from rfl,
    h3.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem norm_iteratedFDeriv_two_comp_le {u : E → ℝ} {φ φ' : ℝ → ℝ} {φ'' : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ∀ᶠ a in 𝓝 (u x), HasDerivAt φ (φ' a) a)
    (hφ' : HasDerivAt φ' φ'' (u x)) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ φ (u y)) x‖ ≤
      |φ''| * ‖fderiv ℝ u x‖ ^ 2 + |φ' (u x)| * ‖iteratedFDeriv ℝ 2 u x‖ := by
  apply norm_iteratedFDeriv_two_le_of (by positivity)
  intro v w
  rw [fderiv_fderiv_comp hu hφ hφ' v w]
  have e1 := (fderiv ℝ u x).le_opNorm v
  have e2 := (fderiv ℝ u x).le_opNorm w
  have e3 := abs_fderiv_fderiv_le u x v w
  rw [Real.norm_eq_abs] at e1 e2
  calc |φ'' * (fderiv ℝ u x v * fderiv ℝ u x w) + φ' (u x) * fderiv ℝ (fderiv ℝ u) x v w|
      ≤ |φ''| * (|fderiv ℝ u x v| * |fderiv ℝ u x w|) +
          |φ' (u x)| * |fderiv ℝ (fderiv ℝ u) x v w| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |φ''| * ((‖fderiv ℝ u x‖ * ‖v‖) * (‖fderiv ℝ u x‖ * ‖w‖)) +
          |φ' (u x)| * (‖iteratedFDeriv ℝ 2 u x‖ * ‖v‖ * ‖w‖) := by
        gcongr
    _ = _ := by ring

end Calculus

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem laplacian_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (F : E → ℝ) (x : E) :
    Laplacian.laplacian F x = ∑ i, fderiv ℝ (fderiv ℝ F) x (b i) (b i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F b]
  simp [iteratedFDeriv_two_apply]

theorem laplacian_comp {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {u : E → ℝ} {φ φ' : ℝ → ℝ} {φ'' : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ∀ᶠ a in 𝓝 (u x), HasDerivAt φ (φ' a) a)
    (hφ' : HasDerivAt φ' φ'' (u x)) :
    Laplacian.laplacian (fun y ↦ φ (u y)) x =
      φ'' * ∑ i, (fderiv ℝ u x (b i)) ^ 2 + φ' (u x) * Laplacian.laplacian u x := by
  rw [laplacian_eq_sum b, laplacian_eq_sum b u, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_fderiv_comp hu hφ hφ']
  ring

theorem abs_laplacian_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (F : E → ℝ) (x : E) :
    |Laplacian.laplacian F x| ≤ Fintype.card ι * ‖iteratedFDeriv ℝ 2 F x‖ := by
  rw [laplacian_eq_sum b]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i, |fderiv ℝ (fderiv ℝ F) x (b i) (b i)| ≤ ‖iteratedFDeriv ℝ 2 F x‖ := by
    intro i
    simpa [b.orthonormal.1 i] using abs_fderiv_fderiv_le F x (b i) (b i)
  refine (Finset.sum_le_sum fun i _ ↦ this i).trans ?_
  simp

omit [FiniteDimensional ℝ E] in
theorem sum_sq_fderiv_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (v : E) (c : ℝ) :
    ∑ i, ((c • innerSL ℝ v) (b i)) ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  have h := b.sum_inner_mul_inner v v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (b i) v]
  ring

end Laplacian

section Decomp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

theorem iteratedFDeriv_decomp {F₁ : E → ℝ} {G : ι → E → ℝ} (c : ℝ) {i : ℕ} {x : E}
    (h₁ : ContDiffAt ℝ i F₁ x) (h₂ : ∀ k, ContDiffAt ℝ i (G k) x) :
    iteratedFDeriv ℝ i (fun y ↦ F₁ y - c * ∑ k, G k y) x =
      iteratedFDeriv ℝ i F₁ x - c • ∑ k, iteratedFDeriv ℝ i (G k) x := by
  have hs : ContDiffAt ℝ i (fun y ↦ ∑ k, G k y) x :=
    ContDiffAt.sum fun k _ ↦ h₂ k
  have e : (fun y ↦ F₁ y - c * ∑ k, G k y) = F₁ - c • (fun y ↦ ∑ k, G k y) := by
    funext y; simp [smul_eq_mul]
  rw [e, iteratedFDeriv_sub_apply (g := c • fun y ↦ ∑ k, G k y) h₁ (hs.const_smul c),
    iteratedFDeriv_const_smul_apply hs,
    iteratedFDeriv_fun_sum_apply fun k _ ↦ h₂ k]

theorem norm_iteratedFDeriv_decomp_le {F₁ : E → ℝ} {G : ι → E → ℝ} (c : ℝ) {i : ℕ} {x : E}
    (h₁ : ContDiffAt ℝ i F₁ x) (h₂ : ∀ k, ContDiffAt ℝ i (G k) x) :
    ‖iteratedFDeriv ℝ i (fun y ↦ F₁ y - c * ∑ k, G k y) x‖ ≤
      ‖iteratedFDeriv ℝ i F₁ x‖ + |c| * ∑ k, ‖iteratedFDeriv ℝ i (G k) x‖ := by
  rw [iteratedFDeriv_decomp c h₁ h₂]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  gcongr
  exact norm_sum_le _ _

end Decomp

section DecompLap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem laplacian_decomp {F₁ : E → ℝ} {G : ι → E → ℝ} (c : ℝ) {x : E}
    (h₁ : ContDiffAt ℝ 2 F₁ x) (h₂ : ∀ k, ContDiffAt ℝ 2 (G k) x) :
    Laplacian.laplacian (fun y ↦ F₁ y - c * ∑ k, G k y) x =
      Laplacian.laplacian F₁ x - c * ∑ k, Laplacian.laplacian (G k) x := by
  let b := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only
  rw [iteratedFDeriv_decomp c (i := 2) h₁ h₂]
  simp only [sub_apply, smul_apply, sum_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  congr 1
  funext k
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [Finset.mul_sum]

end DecompLap

variable {n : ℕ}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem abs_bMat_le (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (i j : Fin n) : |bMat g i j| ≤ 1 := by
  have h1 : bMat g i j ^ 2 ≤ hs2 g := by
    unfold hs2
    have e1 := Finset.single_le_sum (f := fun j ↦ bMat g i j ^ 2) (fun j _ ↦ sq_nonneg _)
      (Finset.mem_univ j)
    have e2 := Finset.single_le_sum (f := fun i ↦ ∑ j, bMat g i j ^ 2)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    linarith
  have h2 := hs2_le g hg h01
  have h3 : lam (gMean g) ≤ 1 / 4 := by unfold lam; nlinarith [sq_nonneg (gMean g - 1 / 2)]
  have : bMat g i j ^ 2 ≤ 1 := by linarith
  rw [← sq_le_one_iff_abs_le_one]
  exact this

theorem abs_bForm_le (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (v w : Gs n) : |bForm g v w| ≤ n ^ 2 * ‖v‖ * ‖w‖ := by
  rw [bForm_eq_sum g hg h01]
  calc |∑ i, ∑ j, v i * w j * bMat g i j| ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ * ‖w‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [abs_mul, abs_mul]
        have hv : |v i| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v i
        have hw : |w j| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w j
        calc |v i| * |w j| * |bMat g i j| ≤ ‖v‖ * ‖w‖ * 1 := by
              gcongr
              exact abs_bMat_le g hg h01 i j
          _ = ‖v‖ * ‖w‖ := mul_one _
    _ = n ^ 2 * ‖v‖ * ‖w‖ := by simp; ring

section Flow

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

theorem contDiff_heatU {s : ℝ} (hs : s < 1) : ContDiff ℝ ∞ (heatU f s) := by
  have h := contDiffOn_heatU f hf h01
  have e : heatU f s = (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) ∘ (fun x ↦ (s, x)) := rfl
  rw [e]
  exact h.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ ↦ hs)

theorem contDiffAt_heatU {s : ℝ} (hs : s < 1) (x : Gs n) : ContDiffAt ℝ 2 (heatU f s) x :=
  ((contDiff_heatU hf h01 hs).of_le two_le_infty).contDiffAt

theorem fderiv_heatU {s : ℝ} (hs : s < 1) (x : Gs n) :
    fderiv ℝ (heatU f s) x = (√(1 - s))⁻¹ • innerSL ℝ (hermite1 (flowFun f s x)) :=
  (hasFDerivAt_heatU f hf h01 hs x).fderiv

theorem norm_fderiv_heatU_le {s : ℝ} (hs : s < 1) (x : Gs n) :
    ‖fderiv ℝ (heatU f s) x‖ ≤ (√(1 - s))⁻¹ * qf (heatU f s x) := by
  rw [fderiv_heatU hf h01 hs, norm_smul, innerSL_apply_norm, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _)]
  gcongr
  exact norm_hermite1_le _ (measurable_flowFun f hf s x) (flowFun_mem f h01 s x)

theorem sq_norm_fderiv_heatU_le {s : ℝ} (hs : s < 1) (x : Gs n) :
    ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ qf (heatU f s x) ^ 2 / (1 - s) := by
  have h := norm_fderiv_heatU_le hf h01 hs x
  have h1 : 0 < 1 - s := by linarith
  calc ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ ((√(1 - s))⁻¹ * qf (heatU f s x)) ^ 2 := by
        gcongr
    _ = qf (heatU f s x) ^ 2 / (1 - s) := by
        rw [mul_pow, inv_pow, sq_sqrt h1.le]; ring

theorem sq_norm_fderiv_heatU_le' {s : ℝ} (hs : s < 1) (x : Gs n) :
    ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ 1 / (1 - s) := by
  have h1 : 0 < 1 - s := by linarith
  refine (sq_norm_fderiv_heatU_le hf h01 hs x).trans ?_
  gcongr
  refine (qf_sq_le _).trans ?_
  rw [div_le_one (by positivity)]
  nlinarith [pi_gt_three]

theorem sum_sq_fderiv_heatU {s : ℝ} (hs : s < 1) (x : Gs n) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Gs n)) :
    ∑ i, (fderiv ℝ (heatU f s) x (b i)) ^ 2 = ‖hermite1 (flowFun f s x)‖ ^ 2 / (1 - s) := by
  have h1 : 0 < 1 - s := by linarith
  have h := b.sum_inner_mul_inner (hermite1 (flowFun f s x)) (hermite1 (flowFun f s x))
  rw [real_inner_self_eq_norm_sq] at h
  rw [fderiv_heatU hf h01 hs, ← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (b i), mul_pow, inv_pow, sq_sqrt h1.le]
  ring

theorem fderiv_fderiv_heatU {s : ℝ} (hs : s < 1) (x v w : Gs n) :
    fderiv ℝ (fderiv ℝ (heatU f s)) x v w = (1 - s)⁻¹ * bForm (flowFun f s x) v w := by
  rw [← iteratedFDeriv_two_heatU f hf h01 hs x v w, iteratedFDeriv_two_apply]
  rfl

theorem norm_iteratedFDeriv_two_heatU_le {s : ℝ} (hs : s < 1) (x : Gs n) :
    ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ ≤ n ^ 2 / (1 - s) := by
  have h1 : 0 < 1 - s := by linarith
  apply norm_iteratedFDeriv_two_le_of (by positivity)
  intro v w
  rw [fderiv_fderiv_heatU hf h01 hs, abs_mul, abs_of_pos (inv_pos.2 h1)]
  calc (1 - s)⁻¹ * |bForm (flowFun f s x) v w| ≤ (1 - s)⁻¹ * (n ^ 2 * ‖v‖ * ‖w‖) := by
        gcongr
        exact abs_bForm_le _ (measurable_flowFun f hf s x) (flowFun_mem f h01 s x) v w
    _ = n ^ 2 / (1 - s) * ‖v‖ * ‖w‖ := by ring

theorem abs_laplacian_heatU_le {s : ℝ} (hs : s < 1) (x : Gs n) :
    |Laplacian.laplacian (heatU f s) x| ≤ n ^ 3 / (1 - s) := by
  have h1 : 0 < 1 - s := by linarith
  refine (abs_laplacian_le (EuclideanSpace.basisFun (Fin n) ℝ) _ x).trans ?_
  simp only [Fintype.card_fin]
  calc (n : ℝ) * ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ ≤ n * (n ^ 2 / (1 - s)) := by
        gcongr
        exact norm_iteratedFDeriv_two_heatU_le hf h01 hs x
    _ = n ^ 3 / (1 - s) := by ring

end Flow

section Flow2

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

theorem norm_hermite1_eq {s : ℝ} (hs : s < 1) (x : Gs n) :
    ‖hermite1 (flowFun f s x)‖ = √(1 - s) * ‖fderiv ℝ (heatU f s) x‖ := by
  have h1 : 0 < 1 - s := by linarith
  rw [fderiv_heatU hf h01 hs, norm_smul, innerSL_apply_norm, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _), ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 h1).ne',
    one_mul]

/-- `e = q(u)² - (1 - s) |∇u|²`. -/
theorem eFlow_eq {s : ℝ} (hs : s < 1) (x : Gs n) :
    eFlow f s x = qf (heatU f s x) ^ 2 - (1 - s) * ‖fderiv ℝ (heatU f s) x‖ ^ 2 := by
  have h1 : 0 < 1 - s := by linarith
  simp only [eFlow, epsF]
  rw [norm_hermite1_eq hf h01 hs, mul_pow, sq_sqrt h1.le]
  rfl

theorem continuous_eFlow (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s < 1) :
    Continuous (eFlow f s) := by
  have e : eFlow f s = fun x ↦ qf (heatU f s x) ^ 2 - (1 - s) * ‖fderiv ℝ (heatU f s) x‖ ^ 2 :=
    funext (eFlow_eq hf h01 hs)
  rw [e]
  have hu := (contDiff_heatU hf h01 hs).continuous
  have hd := (contDiff_heatU hf h01 hs).continuous_fderiv (by simp)
  have hq : Continuous fun x ↦ qf (heatU f s x) :=
    contDiffOn_qf.continuousOn.comp_continuous hu (fun x ↦ heatU_mem f hf h01 hm hs x)
  fun_prop

theorem eFlow_nonneg (s : ℝ) (x : Gs n) : 0 ≤ eFlow f s x :=
  epsF_nonneg _ (measurable_flowFun f hf s x) (flowFun_mem f h01 s x)

omit hf in
theorem eFlow_le (s : ℝ) (x : Gs n) : eFlow f s x ≤ qf (heatU f s x) ^ 2 :=
  (epsF_le _ (flowFun_mem f h01 s x)).1

end Flow2

section Slice

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

/-- The derivatives of a space slice `u(s, ·)` are bounded by the joint derivatives of `u`. -/
theorem norm_iteratedFDeriv_slice_le (k : ℕ) {s : ℝ} (hs : s < 1) (y : Gs n) :
    ‖iteratedFDeriv ℝ k (heatU f s) y‖ ≤
      ‖iteratedFDeriv ℝ k (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) (s, y)‖ := by
  set U := fun p : ℝ × Gs n ↦ heatU f p.1 p.2
  set V := fun q : ℝ × Gs n ↦ U (q + (s, 0))
  set O' := {q : ℝ × Gs n | q.1 < 1 - s}
  have hO' : IsOpen O' := isOpen_lt continuous_fst continuous_const
  have hV : ContDiffOn ℝ ∞ V O' := by
    have h := (contDiffOn_heatU f hf h01).comp
      (contDiffOn_id.add (contDiffOn_const (c := ((s, 0) : ℝ × Gs n))))
      (s := O') (t := {p : ℝ × Gs n | p.1 < 1}) (fun q hq ↦ by
        simp only [O', mem_ofPred_eq] at hq
        simp only [mem_ofPred_eq, id, Prod.fst_add]
        linarith)
    exact h
  let L := ContinuousLinearMap.inr ℝ ℝ (Gs n)
  have hpre : L ⁻¹' O' = univ := by
    ext z
    simp only [O', L, mem_preimage, mem_ofPred_eq, ContinuousLinearMap.inr_apply, mem_univ,
      iff_true]
    linarith
  have hLy : L y ∈ O' := by
    simp only [O', L, mem_ofPred_eq, ContinuousLinearMap.inr_apply]
    linarith
  have h1 : heatU f s = V ∘ L := by
    funext z
    simp [V, U, L]
  have h2 := L.iteratedFDerivWithin_comp_right hV hO'.uniqueDiffOn
    (by rw [hpre]; exact uniqueDiffOn_univ) hLy (i := k) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_univ, ← h1, iteratedFDerivWithin_of_isOpen k hO' hLy] at h2
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hV' : iteratedFDeriv ℝ k V (L y) = iteratedFDeriv ℝ k U (s, y) := by
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    simp [L]
  rw [hV']
  have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Gs n)
  calc ‖iteratedFDeriv ℝ k U (s, y)‖ * ∏ _i : Fin k, ‖L‖
      ≤ ‖iteratedFDeriv ℝ k U (s, y)‖ * ∏ _i : Fin k, (1 : ℝ) := by
        gcongr with i
    _ = _ := by simp

/-- The third space derivatives of `u` are bounded on `[0, s₁] × ℝⁿ`. -/
theorem bounded_iteratedFDeriv_three {s₁ : ℝ} (hs₁ : s₁ < 1) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc 0 s₁, ∀ y, ‖iteratedFDeriv ℝ 3 (heatU f s) y‖ ≤ M := by
  obtain ⟨M, hM⟩ := bounded_iteratedFDeriv_heatU f hf h01 hs₁ 3
  refine ⟨max M 0, le_max_right _ _, fun s hs y ↦ ?_⟩
  refine (norm_iteratedFDeriv_slice_le hf h01 3 (by linarith [hs.2]) y).trans ?_
  exact (hM (s, y) ⟨by linarith [hs.1], hs.2⟩).trans (le_max_left _ _)

end Slice

end BGHKLMM26.RobustMIS.Drift
