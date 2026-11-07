module

public import BGHKLMM26.RobustMIS.Bessel
public import BGHKLMM26.RobustMIS.StaticFiberAux

/-!
# The off-axis part of `‖B‖²_HS`

Lemmas 4.3 (ii), (iii), 4.4 and 4.5 of `eldan-proof.tex`. In the basis `(u, v₂, …, vₙ)` with
`U = |U| u`, `‖B‖²_HS = b₁₁² + 2|b₁|² + ‖B_⊥‖²_HS` with `b₁₁ = ⟨B u, u⟩`. The transverse block
(Lemma 4.4, replacing Eldan's Lemma 24 and Talagrand's inequality) and the off-diagonal block
(Lemma 4.5, replacing Eldan's Lemma 27) are both bounded by the bathtub gap `δ' = q(S) - |U|`:
`‖B_⊥‖² ≤ 2√(2/π) δ'` and `|b₁|² ≤ 2(√(2/π) + √(π/2) λ⁻²) δ'`.

Proof (namespace `StaticFiber`): instead of coordinates on `ℝ × ℝⁿ⁻¹`, the fibers are
parametrized by `y ∈ ℝⁿ`, `x = s u + (y - ⟨u, y⟩ u)` (`fpt`, `integral_fiber` in
`StaticFiberAux.lean`); `g̃(y) = ∫ g(s u + P y) dγ₁(s)` (`gfib`) and
`Q(y) = ∫ s g(s u + P y) dγ₁(s)` (`Qfib`), with `|Q| ≤ q(g̃)` (`bathtub1d` on each fiber,
`abs_Qfib_le`) and `∫ ⟨v, y⟩ g̃ = ⟨v, U⟩ = 0` for `v ⊥ u`. Integrating the Taylor bound
`taylor_qf` at `h = S`, `s = g̃(y)` gives at once Jensen's `∫ q(g̃) ≤ q(S)` and
`√(π/2) ∫ (g̃ - S)² ≤ q(S) - ∫ q(g̃) ≤ δ'` (`fiber_jensen`). Then, in an orthonormal basis `b`
with `b i₀ = u` (`exists_basis_of_unit`, `hs2_eq_orthonormalBasis`): for `i, j ≠ i₀`,
`⟨B bᵢ, bⱼ⟩ = ⟨B(g̃) bᵢ, bⱼ⟩` and `‖B(g̃)‖²_HS ≤ 2 ∫ (g̃ - S)²` (`sum_perp_le`, `hs_integral_le`);
for `j ≠ i₀`, `⟨B u, bⱼ⟩ = ∫ ⟨bⱼ, y⟩ H` with `H = Q - q(S) + Ψ(S)(g̃ - S)` and
`∫ H² ≤ 2(√(2/π) + √(π/2)/λ²) δ'` (`sum_bForm_u_sq_le`, `integral_H_sq_le`,
`norm_integral_smul_le`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.StaticFiber

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

theorem abs_le_one_of {a : ℝ} (h : 0 ≤ a ∧ a ≤ 1) : |a| ≤ 1 := abs_le.2 ⟨by linarith [h.1], h.2⟩

theorem measurable_qf : Measurable qf := by
  classical
  have h : qf = (Icc (0 : ℝ) 1).piecewise qf (fun _ ↦ 0) := by
    funext a
    by_cases ha : a ∈ Icc (0 : ℝ) 1
    · simp [Set.piecewise, ha]
    · simp only [Set.piecewise, ha, ite_false]
      exact qf_of_not_mem fun h ↦ ha (Ioo_subset_Icc_self h)
  rw [h]
  exact continuousOn_qf.measurable_piecewise continuousOn_const measurableSet_Icc

/-! ### The fiber functions -/

/-- `g̃(y) = ∫ g(s u + P y) dγ₁(s)`. -/
noncomputable def gfib (g : Gs n → ℝ) (u y : Gs n) : ℝ := ∫ s, g (fpt u y s) ∂gaussianReal 0 1

/-- `Q(y) = ∫ s g(s u + P y) dγ₁(s)`. -/
noncomputable def Qfib (g : Gs n → ℝ) (u y : Gs n) : ℝ :=
  ∫ s, s * g (fpt u y s) ∂gaussianReal 0 1

section Fiber

variable {g : Gs n → ℝ} {u : Gs n}

theorem measurable_fpt_left (u y : Gs n) : Measurable (fun s : ℝ ↦ fpt u y s) := by
  unfold fpt; fun_prop

theorem measurable_gfib (hg : Measurable g) : Measurable (gfib g u) :=
  measurable_fiberInt (F := fun y s ↦ g (fpt u y s)) (hg.comp (continuous_fpt u).measurable)

theorem measurable_Qfib (hg : Measurable g) : Measurable (Qfib g u) :=
  measurable_fiberInt (F := fun y s ↦ s * g (fpt u y s))
    (measurable_snd.mul (hg.comp (continuous_fpt u).measurable))

theorem gfib_mem (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (y : Gs n) :
    0 ≤ gfib g u y ∧ gfib g u y ≤ 1 := by
  have hi : Integrable (fun s ↦ g (fpt u y s)) (gaussianReal 0 1) :=
    Gaussian.integrable_of_abs_le (hg.comp (measurable_fpt_left u y)) (C := 1)
      fun s ↦ abs_le_one_of (h01 _)
  refine ⟨integral_nonneg fun s ↦ (h01 _).1, ?_⟩
  calc gfib g u y ≤ ∫ _s, (1 : ℝ) ∂gaussianReal 0 1 :=
        integral_mono hi (integrable_const 1) fun _ ↦ (h01 _).2
    _ = 1 := by simp

/-- The bathtub bound on each fiber: `|Q| ≤ q(g̃)`. -/
theorem abs_Qfib_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (y : Gs n) :
    |Qfib g u y| ≤ qf (gfib g u y) :=
  bathtub1d (fun s ↦ g (fpt u y s)) (hg.comp (measurable_fpt_left u y)) fun _ ↦ h01 _

theorem abs_Qfib_le_one (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (y : Gs n) :
    |Qfib g u y| ≤ 1 := by
  have h1 := qf_le (gfib g u y)
  have h2 : (√(2 * π))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith [pi_gt_three])
  linarith [abs_Qfib_le (u := u) hg h01 y]

theorem integral_gfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1) :
    ∫ y, gfib g u y ∂gm n = gMean g := by
  rw [gMean, integral_fiber hu (Gaussian.integrable_of_abs_le hg fun x ↦ abs_le_one_of (h01 x))]
  rfl

theorem integral_Qfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1) :
    ∫ y, Qfib g u y ∂gm n = ⟪u, hermite1 g⟫ := by
  rw [hermite1, inner_integral_smul hg (fun x ↦ abs_le_one_of (h01 x)) u,
    integral_fiber hu (integrable_inner_mul hg fun x ↦ abs_le_one_of (h01 x))]
  congr 1
  funext y
  unfold Qfib
  congr 1
  funext s
  rw [inner_fpt_self hu]

theorem integral_inner_mul_gfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    {v : Gs n} (hv : ⟪v, u⟫ = 0) :
    ∫ y, ⟪v, y⟫ * gfib g u y ∂gm n = ⟪v, hermite1 g⟫ := by
  rw [hermite1, inner_integral_smul hg (fun x ↦ abs_le_one_of (h01 x)) v,
    integral_fiber hu (integrable_inner_mul hg fun x ↦ abs_le_one_of (h01 x))]
  congr 1
  funext y
  unfold gfib
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [inner_fpt_of_orth hv]

theorem bForm_eq_gfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    {v w : Gs n} (hv : ⟪v, u⟫ = 0) (hw : ⟪w, u⟫ = 0) :
    bForm g v w = bForm (gfib g u) v w := by
  unfold bForm
  rw [integral_fiber hu (integrable_quad_mul _ hg fun x ↦ abs_le_one_of (h01 x))]
  congr 1
  funext y
  unfold gfib
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [inner_fpt_of_orth hv, inner_fpt_of_orth hw]

theorem bForm_u_eq_Qfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    {v : Gs n} (hv : ⟪v, u⟫ = 0) :
    bForm g u v = ∫ y, ⟪v, y⟫ * Qfib g u y ∂gm n := by
  have huv : ⟪u, v⟫ = 0 := by rw [real_inner_comm]; exact hv
  unfold bForm
  rw [integral_fiber hu (integrable_quad_mul _ hg fun x ↦ abs_le_one_of (h01 x))]
  congr 1
  funext y
  unfold Qfib
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [inner_fpt_self hu, inner_fpt_of_orth hv, huv]
  ring

end Fiber

/-! ### Constants -/

theorem sqrt_two_div_pi_mul : √(2 / π) * √(π / 2) = 1 := by
  rw [← Real.sqrt_mul (by positivity)]
  have : 2 / π * (π / 2) = 1 := by field_simp
  rw [this, Real.sqrt_one]

theorem two_mul_qf_le (a : ℝ) : 2 * qf a ≤ √(2 / π) := by
  have h : √(2 / π) = 2 * (√(2 * π))⁻¹ := by
    rw [show 2 / π = (2 * (√(2 * π))⁻¹) ^ 2 by
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [h]
  linarith [qf_le a]

theorem qf_le_one (a : ℝ) : qf a ≤ 1 := by
  have h1 := two_mul_qf_le a
  have h2 : √(2 / π) ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by rw [div_le_one pi_pos]; linarith [pi_gt_three])
  linarith [qf_nonneg a]

theorem abs_qf_le_one (a : ℝ) : |qf a| ≤ 1 := abs_le_one_of ⟨qf_nonneg a, qf_le_one a⟩

/-! ### Coordinates -/

theorem coord_eq_inner (i : Fin n) (x : Gs n) : x i = ⟪EuclideanSpace.single i 1, x⟫ := by
  simp [EuclideanSpace.inner_single_left]

theorem integral_coord_quad (i j : Fin n) :
    ∫ x, (x i * x j - if i = j then 1 else 0) ∂gm n = 0 := by
  have h := integral_quad_gm (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
  have h2 : ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1⟫ =
      if i = j then 1 else 0 := by
    rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  rw [h2] at h
  simp_rw [← coord_eq_inner] at h
  exact h

theorem integrable_coord_quad (i j : Fin n) :
    Integrable (fun x : Gs n ↦ x i * x j - if i = j then 1 else 0) (gm n) := by
  have := (integrable_inner_mul_inner (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j 1)).sub (integrable_const (if i = j then (1 : ℝ) else 0))
  simp_rw [← coord_eq_inner] at this
  exact this

theorem integrable_coord_quad_mul (i j : Fin n) {c : Gs n → ℝ} (hc : Measurable c) {C : ℝ}
    (hC : ∀ x, |c x| ≤ C) :
    Integrable (fun x : Gs n ↦ (x i * x j - if i = j then 1 else 0) * c x) (gm n) := by
  have := integrable_quad_mul (v := EuclideanSpace.single i (1 : ℝ))
    (w := EuclideanSpace.single j 1) (if i = j then 1 else 0) hc hC
  simp_rw [← coord_eq_inner] at this
  exact this

theorem bForm_comm (g : Gs n → ℝ) (v w : Gs n) : bForm g v w = bForm g w v := by
  unfold bForm
  congr 1
  funext x
  rw [real_inner_comm v w, mul_comm ⟪v, x⟫]

/-! ### The bounds -/

section Bounds

variable {g : Gs n → ℝ} {u : Gs n}

theorem integrable_gfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (gfib g u) (gm n) :=
  Gaussian.integrable_of_abs_le (measurable_gfib hg) fun y ↦ abs_le_one_of (gfib_mem hg h01 y)

theorem integrable_Qfib (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (Qfib g u) (gm n) :=
  Gaussian.integrable_of_abs_le (measurable_Qfib hg) (abs_Qfib_le_one hg h01)

theorem integrable_qf_gfib (hg : Measurable g) :
    Integrable (fun y ↦ qf (gfib g u y)) (gm n) :=
  Gaussian.integrable_of_abs_le (measurable_qf.comp (measurable_gfib hg)) fun _ ↦ abs_qf_le_one _

theorem abs_gfib_sub_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) {S : ℝ}
    (hS : S ∈ Icc (0 : ℝ) 1) (y : Gs n) : |gfib g u y - S| ≤ 1 := by
  have := gfib_mem (u := u) hg h01 y
  rw [abs_le]; constructor <;> linarith [hS.1, hS.2]

theorem integrable_gfib_sub_sq (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) {S : ℝ}
    (hS : S ∈ Icc (0 : ℝ) 1) :
    Integrable (fun y ↦ (gfib g u y - S) ^ 2) (gm n) := by
  refine Gaussian.integrable_of_abs_le (((measurable_gfib hg).sub_const _).pow_const 2) (C := 1)
    fun y ↦ ?_
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have := abs_gfib_sub_le (u := u) hg h01 hS y
  nlinarith [abs_nonneg (gfib g u y - S)]

/-- **Jensen and the Taylor bound on fibers** (Lemma 4.3 (iii)): `|U| ≤ ∫ q(g̃)` and
`√(π/2) ∫ (g̃ - S)² ≤ q(S) - ∫ q(g̃)`. -/
theorem fiber_jensen (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (hUu : ⟪u, hermite1 g⟫ = ‖hermite1 g‖) :
    ‖hermite1 g‖ ≤ ∫ y, qf (gfib g u y) ∂gm n ∧
      √(π / 2) * ∫ y, (gfib g u y - gMean g) ^ 2 ∂gm n ≤
        qf (gMean g) - ∫ y, qf (gfib g u y) ∂gm n := by
  have hqi := integrable_qf_gfib (u := u) hg
  have hgi := integrable_gfib (u := u) hg h01
  have hsqi := integrable_gfib_sub_sq (u := u) hg h01 (Ioo_subset_Icc_self hS)
  constructor
  · rw [← hUu, ← integral_Qfib hg h01 hu]
    exact integral_mono (integrable_Qfib hg h01) hqi
      fun y ↦ (le_abs_self _).trans (abs_Qfib_le hg h01 y)
  · have hT : ∀ y, qf (gfib g u y) - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g) ≤
        -(√(π / 2) * (gfib g u y - gMean g) ^ 2) :=
      fun y ↦ (taylor_qf hS (gfib_mem hg h01 y)).2
    have h1 : Integrable (fun y ↦ qf (gfib g u y) - qf (gMean g)) (gm n) :=
      hqi.sub (integrable_const _)
    have h2 : Integrable (fun y ↦ Psi (gMean g) * (gfib g u y - gMean g)) (gm n) :=
      (hgi.sub (integrable_const _)).const_mul _
    have hint :
        ∫ y, (qf (gfib g u y) - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) ∂gm n ≤
        ∫ y, -(√(π / 2) * (gfib g u y - gMean g) ^ 2) ∂gm n :=
      integral_mono (h1.add h2) (hsqi.const_mul _).neg hT
    rw [integral_add h1 h2, integral_sub hqi (integrable_const _), integral_const_mul,
      integral_sub hgi (integrable_const _), integral_neg, integral_const_mul,
      integral_gfib hg h01 hu] at hint
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, mul_zero,
      add_zero] at hint
    linarith

theorem integral_gfib_sub_sq_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (hUu : ⟪u, hermite1 g⟫ = ‖hermite1 g‖) :
    ∫ y, (gfib g u y - gMean g) ^ 2 ∂gm n ≤ √(2 / π) * (qf (gMean g) - ‖hermite1 g‖) := by
  obtain ⟨h1, h2⟩ := fiber_jensen hg h01 hu hS hUu
  have h3 : √(π / 2) * ∫ y, (gfib g u y - gMean g) ^ 2 ∂gm n ≤ qf (gMean g) - ‖hermite1 g‖ := by
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (2 / π))
  rwa [← mul_assoc, sqrt_two_div_pi_mul, one_mul] at h4

theorem integral_qf_gfib_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (hUu : ⟪u, hermite1 g⟫ = ‖hermite1 g‖) :
    ∫ y, qf (gfib g u y) ∂gm n ≤ qf (gMean g) := by
  obtain ⟨_, h2⟩ := fiber_jensen hg h01 hu hS hUu
  have : 0 ≤ √(π / 2) * ∫ y, (gfib g u y - gMean g) ^ 2 ∂gm n :=
    mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  linarith

/-- `‖B(g̃)‖²_HS ≤ 2 ∫ (g̃ - S)²` (Bessel, as `∫ (x xᵀ - I) dγ = 0`). -/
theorem hs2_gfib_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) {S : ℝ}
    (hS : S ∈ Icc (0 : ℝ) 1) : hs2 (gfib g u) ≤ 2 * ∫ y, (gfib g u y - S) ^ 2 ∂gm n := by
  have hgm := measurable_gfib (u := u) hg
  have hb : ∀ y, |gfib g u y - S| ≤ 1 := abs_gfib_sub_le hg h01 hS
  have hmem : MemLp (fun y ↦ gfib g u y - S) 2 (gm n) :=
    Gaussian.memLp_two_of_abs_le (hgm.sub_const _) hb
  have key := hs_integral_le (fun y ↦ gfib g u y - S) hmem
  have he : ∀ i j, bMat (gfib g u) i j =
      ∫ x, (x i * x j - if i = j then 1 else 0) * (gfib g u x - S) ∂gm n := by
    intro i j
    have hfun : (fun x : Gs n ↦ (x i * x j - if i = j then 1 else 0) * (gfib g u x - S)) =
        fun x ↦ (x i * x j - if i = j then 1 else 0) * gfib g u x -
          S * (x i * x j - if i = j then 1 else 0) := by
      funext x; ring
    rw [hfun, integral_sub (integrable_coord_quad_mul i j hgm
        (fun y ↦ abs_le_one_of (gfib_mem hg h01 y))) ((integrable_coord_quad i j).const_mul S),
      integral_const_mul, integral_coord_quad, mul_zero, sub_zero]
    rfl
  unfold hs2
  simp_rw [he]
  exact key

/-- For `v ⊥ u`, `⟨B u, v⟩ = ∫ ⟨v, y⟩ (Q(y) - a + c (g̃(y) - S))` for all constants `a, c, S`
(as `∫ y = 0` and `∫ y g̃ = 0`). -/
theorem bForm_u_eq_H (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hU : hermite1 g = ‖hermite1 g‖ • u) {v : Gs n} (hv : ⟪v, u⟫ = 0) (S a c : ℝ) :
    bForm g u v = ∫ y, ⟪v, y⟫ * (Qfib g u y - a + c * (gfib g u y - S)) ∂gm n := by
  have hvU : ⟪v, hermite1 g⟫ = 0 := by rw [hU, inner_smul_right, hv, mul_zero]
  have e : (fun y ↦ ⟪v, y⟫ * (Qfib g u y - a + c * (gfib g u y - S))) = fun y ↦
      ⟪v, y⟫ * Qfib g u y + (c * (⟪v, y⟫ * gfib g u y) - (a + c * S) * ⟪v, y⟫) := by
    funext y; ring
  have I1 : Integrable (fun y ↦ ⟪v, y⟫ * Qfib g u y) (gm n) :=
    integrable_inner_mul (measurable_Qfib hg) (abs_Qfib_le_one hg h01)
  have I2 : Integrable (fun y ↦ c * (⟪v, y⟫ * gfib g u y)) (gm n) :=
    (integrable_inner_mul (measurable_gfib hg)
      fun y ↦ abs_le_one_of (gfib_mem hg h01 y)).const_mul c
  have I3 : Integrable (fun y ↦ (a + c * S) * ⟪v, y⟫) (gm n) :=
    (integrable_inner v).const_mul _
  have I23 : Integrable (fun y ↦ c * (⟪v, y⟫ * gfib g u y) - (a + c * S) * ⟪v, y⟫) (gm n) :=
    I2.sub I3
  rw [e, integral_add I1 I23, integral_sub I2 I3, integral_const_mul, integral_const_mul,
    integral_inner_mul_gfib hg h01 hu hv, hvU, integral_inner_gm, bForm_u_eq_Qfib hg h01 hu hv]
  ring

/-- The off-diagonal block through Bessel: `∑_{j ≠ i₀} ⟨B u, b_j⟩² ≤ ∫ H²`. -/
theorem sum_bForm_u_sq_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hU : hermite1 g = ‖hermite1 g‖ • u) (b : OrthonormalBasis (Fin n) ℝ (Gs n)) (i₀ : Fin n)
    (hb : b i₀ = u) {S : ℝ} (hS : S ∈ Icc (0 : ℝ) 1) (a c : ℝ) :
    ∑ j ∈ Finset.univ.erase i₀, bForm g u (b j) ^ 2 ≤
      ∫ y, (Qfib g u y - a + c * (gfib g u y - S)) ^ 2 ∂gm n := by
  have hHm : Measurable (fun y ↦ Qfib g u y - a + c * (gfib g u y - S)) :=
    ((measurable_Qfib hg).sub_const _).add (((measurable_gfib hg).sub_const _).const_mul _)
  have hHb : ∀ y, |Qfib g u y - a + c * (gfib g u y - S)| ≤ 1 + |a| + |c| := by
    intro y
    have h1 := abs_le.1 (abs_Qfib_le_one (u := u) hg h01 y)
    have h3 : |c * (gfib g u y - S)| ≤ |c| := by
      rw [abs_mul]
      calc |c| * |gfib g u y - S| ≤ |c| * 1 :=
            mul_le_mul_of_nonneg_left (abs_gfib_sub_le hg h01 hS y) (abs_nonneg c)
        _ = |c| := mul_one _
    have h3' := abs_le.1 h3
    rw [abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self a]
  have hmem : MemLp (fun y ↦ Qfib g u y - a + c * (gfib g u y - S)) 2 (gm n) :=
    Gaussian.memLp_two_of_abs_le hHm hHb
  set w := ∫ y, (Qfib g u y - a + c * (gfib g u y - S)) • y ∂gm n with hw
  have hj : ∀ j ∈ Finset.univ.erase i₀, bForm g u (b j) = ⟪b j, w⟫ := by
    intro j hj
    have hju : ⟪b j, u⟫ = 0 := by
      rw [← hb]
      exact b.orthonormal.2 (Finset.ne_of_mem_erase hj)
    rw [bForm_u_eq_H hg h01 hu hU hju S a c, hw, inner_integral_smul hHm hHb]
  have hsum : ∑ j ∈ Finset.univ.erase i₀, bForm g u (b j) ^ 2 =
      ∑ j ∈ Finset.univ.erase i₀, ⟪b j, w⟫ ^ 2 :=
    Finset.sum_congr rfl fun j hj' ↦ by rw [hj j hj']
  rw [hsum]
  have hn := norm_integral_smul_le _ hmem
  rw [← hw] at hn
  have hI : 0 ≤ ∫ y, (Qfib g u y - a + c * (gfib g u y - S)) ^ 2 ∂gm n :=
    integral_nonneg fun _ ↦ sq_nonneg _
  calc ∑ j ∈ Finset.univ.erase i₀, ⟪b j, w⟫ ^ 2 ≤ ∑ j, ⟪b j, w⟫ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun _ _ _ ↦ sq_nonneg _
    _ = ‖w‖ ^ 2 := b.sum_sq_inner_right w
    _ ≤ (√(∫ y, (Qfib g u y - a + c * (gfib g u y - S)) ^ 2 ∂gm n)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := Real.sq_sqrt hI

/-- Pointwise bound behind Lemma 4.5: with `a = q(g̃) - Q ∈ [0, √(2/π)]` and the Taylor remainder
`R = q(g̃) - q(S) + Ψ(S)(g̃ - S)`, `(R - a)² ≤ 2√(2/π) a + 2 (π/2)/λ² (g̃ - S)²`. -/
theorem H_sq_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (y : Gs n) :
    (Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) ^ 2 ≤
      2 * √(2 / π) * (qf (gfib g u y) - Qfib g u y) +
        2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) * (gfib g u y - gMean g) ^ 2 := by
  have hm := gfib_mem (u := u) hg h01 y
  obtain ⟨hT1, hT2⟩ := taylor_qf hS hm
  have hQ := abs_le.1 (abs_Qfib_le (u := u) hg h01 y)
  have h2q := two_mul_qf_le (gfib g u y)
  have hL : 0 < lam (gMean g) := by unfold lam; nlinarith [hS.1, hS.2]
  obtain ⟨a, ha⟩ : ∃ a, a = qf (gfib g u y) - Qfib g u y := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R,
      R = qf (gfib g u y) - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = gfib g u y - gMean g := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = √(π / 2) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = √(2 / π) := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = lam (gMean g) := ⟨_, rfl⟩
  have hH : Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g) = R - a := by
    rw [hR, ha]; ring
  rw [hH, ← ha, ← hd, ← hc, ← hc', ← hLd]
  rw [← hR, ← hd, ← hc] at hT1 hT2
  rw [← hLd] at hT1
  rw [← hc'] at h2q
  rw [← hLd] at hL
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ c' := by rw [ha]; linarith
  have ha2 : a ^ 2 ≤ c' * a := by
    rw [sq]; exact mul_le_mul_of_nonneg_right ha1 ha0
  have hc0 : 0 ≤ c := by rw [hc]; exact Real.sqrt_nonneg _
  have hd1 : d ^ 2 ≤ 1 := by
    rw [hd]
    have : |gfib g u y - gMean g| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hS.1, hS.2, hm.1, hm.2]
    rw [← sq_abs]
    nlinarith [abs_nonneg (gfib g u y - gMean g)]
  have hR0 : R ≤ 0 := by
    have : 0 ≤ c * d ^ 2 := mul_nonneg hc0 (sq_nonneg d)
    linarith
  have hRb : -R ≤ c * d ^ 2 / L := by linarith
  have hR2 : R ^ 2 ≤ c ^ 2 / L ^ 2 * d ^ 2 := by
    have h1 : R ^ 2 ≤ (c * d ^ 2 / L) ^ 2 := by
      rw [← neg_sq R]
      exact pow_le_pow_left₀ (by linarith) hRb 2
    have h2 : (c * d ^ 2 / L) ^ 2 = c ^ 2 / L ^ 2 * d ^ 2 * d ^ 2 := by
      field_simp
    have h3 : c ^ 2 / L ^ 2 * d ^ 2 * d ^ 2 ≤ c ^ 2 / L ^ 2 * d ^ 2 := by
      have : 0 ≤ c ^ 2 / L ^ 2 * d ^ 2 := by positivity
      calc c ^ 2 / L ^ 2 * d ^ 2 * d ^ 2 ≤ c ^ 2 / L ^ 2 * d ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hd1 this
        _ = _ := mul_one _
    linarith
  nlinarith [sq_nonneg (R + a)]

/-- **Off-diagonal block** (Lemma 4.5): `∫ H² ≤ 2(√(2/π) + √(π/2)/λ²) δ'` for
`H = Q - q(S) + Ψ(S)(g̃ - S)`. -/
theorem integral_H_sq_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (hUu : ⟪u, hermite1 g⟫ = ‖hermite1 g‖) :
    ∫ y, (Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) ^ 2 ∂gm n ≤
      2 * (√(2 / π) + √(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖) := by
  have hSc := Ioo_subset_Icc_self hS
  have hqi := integrable_qf_gfib (u := u) hg
  have hQi := integrable_Qfib (u := u) hg h01
  have hsqi := integrable_gfib_sub_sq (u := u) hg h01 hSc
  have hA := integral_gfib_sub_sq_le hg h01 hu hS hUu
  have hJ := integral_qf_gfib_le hg h01 hu hS hUu
  have hHm : Measurable
      (fun y ↦ Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) :=
    ((measurable_Qfib hg).sub_const _).add (((measurable_gfib hg).sub_const _).const_mul _)
  have hHi : Integrable
      (fun y ↦ (Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) ^ 2)
      (gm n) := by
    have hb : ∀ y, |Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)| ≤
        1 + |qf (gMean g)| + |Psi (gMean g)| := by
      intro y
      have h1 := abs_le.1 (abs_Qfib_le_one (u := u) hg h01 y)
      have h3 : |Psi (gMean g) * (gfib g u y - gMean g)| ≤ |Psi (gMean g)| := by
        rw [abs_mul]
        calc |Psi (gMean g)| * |gfib g u y - gMean g| ≤ |Psi (gMean g)| * 1 :=
              mul_le_mul_of_nonneg_left (abs_gfib_sub_le hg h01 hSc y) (abs_nonneg _)
          _ = _ := mul_one _
      have h3' := abs_le.1 h3
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (qf (gMean g)), le_abs_self (qf (gMean g))]
    exact (Gaussian.memLp_two_of_abs_le hHm hb).integrable_sq
  have i3 : Integrable (fun y ↦ qf (gfib g u y) - Qfib g u y) (gm n) := hqi.sub hQi
  have i1 : Integrable (fun y ↦ 2 * √(2 / π) * (qf (gfib g u y) - Qfib g u y)) (gm n) :=
    i3.const_mul _
  have i2 : Integrable (fun y ↦ 2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) *
      (gfib g u y - gMean g) ^ 2) (gm n) := hsqi.const_mul _
  have hmono : ∫ y, (Qfib g u y - qf (gMean g) + Psi (gMean g) * (gfib g u y - gMean g)) ^ 2 ∂gm n ≤
      ∫ y, (2 * √(2 / π) * (qf (gfib g u y) - Qfib g u y) +
        2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) * (gfib g u y - gMean g) ^ 2) ∂gm n :=
    integral_mono hHi (i1.add i2) (H_sq_le hg h01 hS)
  rw [integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_sub hqi hQi, integral_Qfib hg h01 hu, hUu] at hmono
  have hL : 0 < lam (gMean g) := by unfold lam; nlinarith [hS.1, hS.2]
  have hk : 0 ≤ √(π / 2) ^ 2 / lam (gMean g) ^ 2 := by positivity
  have e1 : √(π / 2) ^ 2 / lam (gMean g) ^ 2 * √(2 / π) = √(π / 2) / lam (gMean g) ^ 2 := by
    rw [div_mul_eq_mul_div, sq, mul_assoc, mul_comm (√(π / 2)) (√(2 / π)), sqrt_two_div_pi_mul,
      mul_one]
  have h1 : 2 * √(2 / π) * (∫ y, qf (gfib g u y) ∂gm n - ‖hermite1 g‖) ≤
      2 * √(2 / π) * (qf (gMean g) - ‖hermite1 g‖) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) * ∫ y, (gfib g u y - gMean g) ^ 2 ∂gm n ≤
      2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) * (√(2 / π) * (qf (gMean g) - ‖hermite1 g‖)) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h3 : 2 * (√(π / 2) ^ 2 / lam (gMean g) ^ 2) * (√(2 / π) * (qf (gMean g) - ‖hermite1 g‖)) =
      2 * (√(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖) := by
    rw [← e1]; ring
  linarith

/-- **Transverse block** (Lemma 4.4): `∑_{i, j ≠ i₀} ⟨B b_i, b_j⟩² ≤ 2 ∫ (g̃ - S)²`. -/
theorem sum_perp_le (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hu : ‖u‖ = 1)
    (b : OrthonormalBasis (Fin n) ℝ (Gs n)) (i₀ : Fin n) (hb : b i₀ = u) {S : ℝ}
    (hS : S ∈ Icc (0 : ℝ) 1) :
    ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase i₀, bForm g (b i) (b j) ^ 2 ≤
      2 * ∫ y, (gfib g u y - S) ^ 2 ∂gm n := by
  have horth : ∀ i ∈ Finset.univ.erase i₀, ⟪b i, u⟫ = 0 := fun i hi ↦ by
    rw [← hb]; exact b.orthonormal.2 (Finset.ne_of_mem_erase hi)
  calc ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase i₀, bForm g (b i) (b j) ^ 2
      = ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase i₀,
          bForm (gfib g u) (b i) (b j) ^ 2 :=
        Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by
          rw [bForm_eq_gfib hg h01 hu (horth i hi) (horth j hj)]
    _ ≤ ∑ i, ∑ j, bForm (gfib g u) (b i) (b j) ^ 2 := by
        refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) fun _ _ _ ↦ sq_nonneg _).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun _ _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    _ = hs2 (gfib g u) := (hs2_eq_orthonormalBasis _ (measurable_gfib hg) (gfib_mem hg h01) b).symm
    _ ≤ _ := hs2_gfib_le hg h01 hS

end Bounds

theorem sum_sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) (i₀ : ι) :
    ∑ i, ∑ j, F i j = F i₀ i₀ + ∑ j ∈ Finset.univ.erase i₀, F i₀ j +
      ∑ i ∈ Finset.univ.erase i₀, F i i₀ +
        ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase i₀, F i j := by
  have h : ∀ i, ∑ j, F i j = F i i₀ + ∑ j ∈ Finset.univ.erase i₀, F i j :=
    fun i ↦ (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  simp_rw [h]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), Finset.sum_add_distrib]
  ring

/-- An orthonormal basis of `ℝⁿ` containing a given unit vector. -/
theorem exists_basis_of_unit {u : Gs n} (hu : ‖u‖ = 1) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (Gs n)) (i₀ : Fin n), b i₀ = u := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exfalso
      have : u = 0 := Subsingleton.elim u 0
      rw [this, norm_zero] at hu
      exact zero_ne_one hu
    · exact h
  let i₀ : Fin n := ⟨0, hn⟩
  have horth : Orthonormal ℝ (({i₀} : Set (Fin n)).domRestrict fun _ ↦ u) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim i j
    subst this
    simp [Set.domRestrict, hu]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := Gs n) (ι := Fin n) finrank_euclideanSpace horth
  exact ⟨b, i₀, hb i₀ rfl⟩

/-- **Off-axis bound**, the proof (Lemmas 4.3–4.5). -/
theorem offaxis (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (u : Gs n) (hu : ‖u‖ = 1)
    (hU : hermite1 g = ‖hermite1 g‖ • u) :
    hs2 g - bForm g u u ^ 2 ≤
      (6 * √(2 / π) + 4 * √(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖) := by
  have hUu : ⟪u, hermite1 g⟫ = ‖hermite1 g‖ := by
    conv_lhs => rw [hU]
    rw [inner_smul_right, inner_self_of_norm hu, mul_one]
  obtain ⟨b, i₀, hb⟩ := exists_basis_of_unit hu
  have hSc := Ioo_subset_Icc_self hS
  rw [hs2_eq_orthonormalBasis g hg h01 b, sum_sum_split _ i₀, hb]
  have hsym : ∑ i ∈ Finset.univ.erase i₀, bForm g (b i) u ^ 2 =
      ∑ j ∈ Finset.univ.erase i₀, bForm g u (b j) ^ 2 :=
    Finset.sum_congr rfl fun i _ ↦ by rw [bForm_comm]
  rw [hsym]
  have h1 := sum_bForm_u_sq_le hg h01 hu hU b i₀ hb hSc (qf (gMean g)) (Psi (gMean g))
  have h2 := integral_H_sq_le hg h01 hu hS hUu
  have h3 := sum_perp_le hg h01 hu b i₀ hb hSc
  have h4 := integral_gfib_sub_sq_le hg h01 hu hS hUu
  have e : (6 * √(2 / π) + 4 * √(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖) =
      2 * (2 * (√(2 / π) + √(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖)) +
        2 * (√(2 / π) * (qf (gMean g) - ‖hermite1 g‖)) := by ring
  rw [e]
  linarith

end BGHKLMM26.RobustMIS.StaticFiber

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- **Off-axis bound** (Lemmas 4.3–4.5): `‖B‖²_HS - ⟨B u, u⟩² = 2|b₁|² + ‖B_⊥‖²_HS ≤
(6√(2/π) + 4√(π/2)/λ(S)²) (q(S) - |U|)` for a unit vector `u` with `U = |U| u`. -/
theorem offaxis_bound (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) (u : Gs n) (hu : ‖u‖ = 1)
    (hU : hermite1 g = ‖hermite1 g‖ • u) :
    hs2 g - bForm g u u ^ 2 ≤
      (6 * √(2 / π) + 4 * √(π / 2) / lam (gMean g) ^ 2) * (qf (gMean g) - ‖hermite1 g‖) :=
  StaticFiber.offaxis g hg h01 hS u hu hU

end BGHKLMM26.RobustMIS
