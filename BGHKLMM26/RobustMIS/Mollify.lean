module

public import BGHKLMM26.RobustMIS.Defs
public import Background.Gaussian

/-!
# Smoothing a Lipschitz test function

A `K`-Lipschitz `Ψ : ℝ² → ℝ` (for the `ℓ¹` distance) is uniformly `2Kη`-close to a `K`-Lipschitz
`Φ` that is `C³` along lines with third derivative `≤ 100 K η⁻² (|a'| + |b'|)³` (`mollify`).

Proof: `Φ(a, b) = E Ψ(a + η Z₀, b + η Z₁)` for a standard Gaussian `Z` on `ℝ²` (`Mollify.moll`).
Lipschitz and closeness are immediate (`E|Zᵢ| ≤ 1`). Along the line `x ↦ (a + x a', b + x b')`,
rotate `Z` so that its first coordinate is along `u = (a', b')/ρ`, `ρ = |(a', b')|₂`
(`Gaussian.map_inner_pair_stdGaussian`): the line function is `x ↦ h(ρ x / η)` with
`h(y) = E G(y + Z)` a one-dimensional Gaussian smoothing of a `Kη |u|₁`-Lipschitz `G`
(`Mollify.moll_line_eq`). In one dimension (`Mollify.smooth1d`), write
`h(y) = ∫ G(t) φ(t - y) dt` and differentiate three times under the integral sign
(`Mollify.hasDerivAt_conv`): `h⁽³⁾(y) = ∫ G(t) He₃(t - y) φ(t - y) dt` with `He₃(z) = z³ - 3z`.
Since `∫ He₃ φ = 0` (the same differentiation applied to `G = 1`, which also gives the moments
`E Z² = 1`, `E Z⁴ = 3`), this is `∫ (G(t) - G(y)) He₃(t - y) φ(t - y) dt`, of absolute value
`≤ L E|Z| |Z³ - 3Z| ≤ L E[Z⁴ + 3Z²] = 6L`. Hence the third derivative along the line is
`≤ (ρ/η)³ · 6 K η |u|₁ = 6 K ρ² (|a'| + |b'|) / η² ≤ 6 K η⁻² (|a'| + |b'|)³`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Mollify

open MeasureTheory ProbabilityTheory Real Set Filter Topology

lemma npdf_eq (z : ℝ) : npdf z = (√(2 * π))⁻¹ * rexp (-z ^ 2 / 2) := by
  simp [npdf, gaussianPDFReal_def]

lemma npdf_nonneg (z : ℝ) : 0 ≤ npdf z := gaussianPDFReal_nonneg _ _ _

lemma hasDerivAt_npdf (z : ℝ) : HasDerivAt npdf (-z * npdf z) z := by
  have h0 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-z) z := by
    have := ((hasDerivAt_pow 2 z).neg).div_const 2
    convert this using 1; ring
  have h : HasDerivAt (fun z => (√(2 * π))⁻¹ * rexp (-z ^ 2 / 2))
      ((√(2 * π))⁻¹ * (rexp (-z ^ 2 / 2) * (-z))) z := (h0.exp).const_mul _
  have e : npdf = fun z => (√(2 * π))⁻¹ * rexp (-z ^ 2 / 2) := funext npdf_eq
  rw [e]; convert h using 1; ring

lemma continuous_npdf : Continuous npdf :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_npdf z).continuousAt

lemma one_add_abs_pow_le (M : ℕ) (s : ℝ) : (1 + |s|) ^ M ≤ rexp (M * |s|) := by
  calc (1 + |s|) ^ M ≤ (rexp |s|) ^ M := by
        gcongr; linarith [Real.add_one_le_exp |s|]
    _ = rexp (M * |s|) := by rw [← Real.exp_nat_mul]

lemma poly_exp_le (M : ℕ) (s : ℝ) :
    (1 + |s|) ^ M * rexp (-s ^ 2 / 4) ≤ rexp (2 * M ^ 2) * rexp (-(1/8) * s ^ 2) := by
  rw [← Real.exp_add]
  calc (1 + |s|) ^ M * rexp (-s ^ 2 / 4) ≤ rexp (M * |s|) * rexp (-s ^ 2 / 4) := by
        gcongr; exact one_add_abs_pow_le M s
    _ = rexp (M * |s| + -s ^ 2 / 4) := by rw [Real.exp_add]
    _ ≤ rexp (2 * M ^ 2 + -(1/8) * s ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith [sq_nonneg (|s| - 4 * M), sq_abs s, abs_nonneg s]

lemma integrable_poly_exp (M : ℕ) :
    Integrable (fun s : ℝ => (1 + |s|) ^ M * rexp (-s ^ 2 / 4)) := by
  refine ((integrable_exp_neg_mul_sq (b := 1/8) (by norm_num)).const_mul
    (rexp (2 * M ^ 2))).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ =>
      (1 + |s|) ^ M * rexp (-s ^ 2 / 4)).aestronglyMeasurable
  · refine ae_of_all _ fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact poly_exp_le M s

lemma npdf_sub_le {t y y₀ : ℝ} (hy : |y - y₀| ≤ 1) :
    npdf (t - y) ≤ (√(2 * π))⁻¹ * rexp (1/2) * rexp (-(t - y₀) ^ 2 / 4) := by
  rw [npdf_eq, mul_assoc, ← Real.exp_add]
  gcongr
  have : (t - y₀) ^ 2 ≤ 2 * (t - y) ^ 2 + 2 * (y - y₀) ^ 2 := by
    nlinarith [sq_nonneg (t - y - (y - y₀))]
  have h2 : (y - y₀) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (y - y₀), sq_abs (y - y₀)]
  linarith

/-- The pointwise domination used for differentiating under the integral. -/
lemma dom_bound {G : ℝ → ℝ} {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hG : ∀ t, |G t| ≤ A + L * |t|) {R : ℝ → ℝ} {C : ℝ} {N : ℕ}
    (hR : ∀ z, |R z| ≤ C * (1 + |z|) ^ N) {t y y₀ : ℝ} (hy : |y - y₀| ≤ 1) :
    |G t * (R (t - y) * npdf (t - y))| ≤
      ((A + L * |y₀| + L) * (C * 2 ^ N) * ((√(2 * π))⁻¹ * rexp (1/2))) *
        ((1 + |t - y₀|) ^ (N + 1) * rexp (-(t - y₀) ^ 2 / 4)) := by
  have hC : 0 ≤ C := by
    have := hR 0
    rw [abs_zero, add_zero, one_pow, mul_one] at this
    exact (abs_nonneg _).trans this
  have h1 : |G t| ≤ (A + L * |y₀| + L) * (1 + |t - y₀|) := by
    have : |t| ≤ |y₀| + |t - y₀| := by
      calc |t| = |y₀ + (t - y₀)| := by ring_nf
        _ ≤ |y₀| + |t - y₀| := abs_add_le _ _
    have h0 : 0 ≤ |t - y₀| := abs_nonneg _
    have h0' : 0 ≤ A + L * |y₀| := by positivity
    calc |G t| ≤ A + L * |t| := hG t
      _ ≤ A + L * (|y₀| + |t - y₀|) := by gcongr
      _ ≤ (A + L * |y₀| + L) * (1 + |t - y₀|) := by nlinarith
  have h2 : |R (t - y)| ≤ C * 2 ^ N * (1 + |t - y₀|) ^ N := by
    have : 1 + |t - y| ≤ 2 * (1 + |t - y₀|) := by
      have : |t - y| ≤ |t - y₀| + |y - y₀| := by
        calc |t - y| = |(t - y₀) - (y - y₀)| := by ring_nf
          _ ≤ |t - y₀| + |y - y₀| := abs_sub _ _
      linarith [abs_nonneg (t - y₀)]
    calc |R (t - y)| ≤ C * (1 + |t - y|) ^ N := hR _
      _ ≤ C * (2 * (1 + |t - y₀|)) ^ N := by gcongr
      _ = C * 2 ^ N * (1 + |t - y₀|) ^ N := by rw [mul_pow]; ring
  have h3 := npdf_sub_le (t := t) hy
  rw [abs_mul, abs_mul, abs_of_nonneg (npdf_nonneg _)]
  have hX : 0 ≤ (A + L * |y₀| + L) * (1 + |t - y₀|) :=
    mul_nonneg (by nlinarith [abs_nonneg y₀]) (by positivity)
  calc |G t| * (|R (t - y)| * npdf (t - y)) ≤ ((A + L * |y₀| + L) * (1 + |t - y₀|)) *
      ((C * 2 ^ N * (1 + |t - y₀|) ^ N) *
        ((√(2 * π))⁻¹ * rexp (1/2) * rexp (-(t - y₀) ^ 2 / 4))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (npdf_nonneg _) (by positivity))
          (mul_nonneg (abs_nonneg _) (npdf_nonneg _)) hX
    _ = _ := by ring

lemma integrable_dom (D : ℝ) (N : ℕ) (y₀ : ℝ) :
    Integrable (fun t : ℝ => D * ((1 + |t - y₀|) ^ (N + 1) * rexp (-(t - y₀) ^ 2 / 4))) :=
  ((integrable_poly_exp (N + 1)).comp_sub_right y₀).const_mul D

/-- **Differentiation under the integral** against a Gaussian kernel with a polynomial factor:
`∂_y ∫ G(t) P(t - y) φ(t - y) dt = ∫ G(t) ((t - y) P(t - y) - P'(t - y)) φ(t - y) dt`. -/
lemma hasDerivAt_conv {G : ℝ → ℝ} (hGc : Continuous G) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hG : ∀ t, |G t| ≤ A + L * |t|)
    {P P' : ℝ → ℝ} (hPc : Continuous P) (hP'c : Continuous P') (hP : ∀ z, HasDerivAt P (P' z) z)
    {C : ℝ} {N : ℕ} (hPb : ∀ z, |P z| ≤ C * (1 + |z|) ^ N)
    (hQb : ∀ z, |z * P z - P' z| ≤ C * (1 + |z|) ^ N) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ t, G t * (P (t - y) * npdf (t - y)))
      (∫ t, G t * (((t - y₀) * P (t - y₀) - P' (t - y₀)) * npdf (t - y₀))) y₀ := by
  have hball : Metric.ball y₀ 1 ∈ 𝓝 y₀ := Metric.ball_mem_nhds _ one_pos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y t => G t * (P (t - y) * npdf (t - y)))
    (F' := fun y t => G t * (((t - y) * P (t - y) - P' (t - y)) * npdf (t - y)))
    (bound := fun t => ((A + L * |y₀| + L) * (C * 2 ^ N) * ((√(2 * π))⁻¹ * rexp (1/2))) *
        ((1 + |t - y₀|) ^ (N + 1) * rexp (-(t - y₀) ^ 2 / 4))) hball
    (Eventually.of_forall fun y => (by
      have := continuous_npdf
      fun_prop : Continuous fun t => G t * (P (t - y) * npdf (t - y))).aestronglyMeasurable)
    ((integrable_dom _ N y₀).mono'
      (by have := continuous_npdf; fun_prop : Continuous fun t =>
        G t * (P (t - y₀) * npdf (t - y₀))).aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs]; exact dom_bound hA hL hG hPb (by simp)))
    ((by have := continuous_npdf; fun_prop : Continuous fun t =>
      G t * (((t - y₀) * P (t - y₀) - P' (t - y₀)) * npdf (t - y₀))).aestronglyMeasurable)
    (ae_of_all _ fun t y hy => by
      rw [Real.norm_eq_abs]
      exact dom_bound (R := fun z => z * P z - P' z) hA hL hG hQb
        (by rw [Metric.mem_ball, Real.dist_eq] at hy; exact hy.le))
    (integrable_dom _ N y₀)
    (ae_of_all _ fun t y _ => by
      have h1 : HasDerivAt (fun y => P (t - y)) (P' (t - y) * (-1)) y :=
        (hP (t - y)).comp y ((hasDerivAt_id y).const_sub t)
      have h2 : HasDerivAt (fun y => npdf (t - y)) (-(t - y) * npdf (t - y) * (-1)) y :=
        (hasDerivAt_npdf (t - y)).comp y ((hasDerivAt_id y).const_sub t)
      convert (h1.mul h2).const_mul (G t) using 1
      ring)
  exact key.2


/-- `H_P G (y) = ∫ G(t) P(t - y) φ(t - y) dt`. -/
noncomputable def convH (G P : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, G t * (P (t - y) * npdf (t - y))

lemma hasDerivAt_convH {G : ℝ → ℝ} (hGc : Continuous G) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hG : ∀ t, |G t| ≤ A + L * |t|)
    {P P' Q : ℝ → ℝ} (hPc : Continuous P) (hP'c : Continuous P') (hP : ∀ z, HasDerivAt P (P' z) z)
    (hQ : ∀ z, z * P z - P' z = Q z)
    {C : ℝ} {N : ℕ} (hPb : ∀ z, |P z| ≤ C * (1 + |z|) ^ N)
    (hQb : ∀ z, |Q z| ≤ C * (1 + |z|) ^ N) (y : ℝ) :
    HasDerivAt (convH G P) (convH G Q y) y := by
  have := hasDerivAt_conv hGc hA hL hG hPc hP'c hP hPb (fun z => (hQ z).symm ▸ hQb z) y
  refine this.congr_deriv ?_
  unfold convH
  congr 1; funext t; rw [hQ]

lemma integrable_convH_integrand {G : ℝ → ℝ} (hGc : Continuous G) {A L : ℝ} (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hG : ∀ t, |G t| ≤ A + L * |t|) {P : ℝ → ℝ} (hPc : Continuous P)
    {C : ℝ} {N : ℕ} (hPb : ∀ z, |P z| ≤ C * (1 + |z|) ^ N) (y : ℝ) :
    Integrable (fun t => G t * (P (t - y) * npdf (t - y))) :=
  (integrable_dom _ N y).mono'
    (by have := continuous_npdf; fun_prop : Continuous fun t =>
      G t * (P (t - y) * npdf (t - y))).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact dom_bound hA hL hG hPb (by simp))

lemma integrable_poly_npdf {P : ℝ → ℝ} (hPc : Continuous P)
    {C : ℝ} {N : ℕ} (hPb : ∀ z, |P z| ≤ C * (1 + |z|) ^ N) :
    Integrable (fun t => P t * npdf t) := by
  have := integrable_convH_integrand (G := fun _ => 1) continuous_const zero_le_one le_rfl
    (fun t => by simp) hPc hPb 0
  simpa using this

lemma abs_pow_le_one_add (z : ℝ) {k : ℕ} (hk : k ≤ 4) : |z| ^ k ≤ (1 + |z|) ^ 4 :=
  (pow_le_pow_left₀ (abs_nonneg z) (by linarith [abs_nonneg z]) k).trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg z]) hk)

/-- The Hermite-type polynomials `1, z, z² - 1, z³ - 3z, z⁴ - 6z² + 3`. -/
noncomputable def hP : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun z => z
  | 2 => fun z => z ^ 2 - 1
  | 3 => fun z => z ^ 3 - 3 * z
  | _ => fun z => z ^ 4 - 6 * z ^ 2 + 3

noncomputable def hP' : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 1
  | 2 => fun z => 2 * z
  | _ => fun z => 3 * z ^ 2 - 3

lemma continuous_hP (m : ℕ) : Continuous (hP m) := by
  match m with
  | 0 => exact continuous_const
  | 1 => exact continuous_id
  | 2 => change Continuous fun z : ℝ => z ^ 2 - 1; fun_prop
  | 3 => change Continuous fun z : ℝ => z ^ 3 - 3 * z; fun_prop
  | m + 4 => change Continuous fun z : ℝ => z ^ 4 - 6 * z ^ 2 + 3; fun_prop

lemma continuous_hP' (m : ℕ) : Continuous (hP' m) := by
  match m with
  | 0 => exact continuous_const
  | 1 => exact continuous_const
  | 2 => change Continuous fun z : ℝ => 2 * z; fun_prop
  | m + 3 => change Continuous fun z : ℝ => 3 * z ^ 2 - 3; fun_prop

lemma hasDerivAt_hP (m : ℕ) (hm : m ≤ 3) (z : ℝ) : HasDerivAt (hP m) (hP' m z) z := by
  match m with
  | 0 => exact hasDerivAt_const _ _
  | 1 => exact hasDerivAt_id z
  | 2 =>
    change HasDerivAt (fun z : ℝ => z ^ 2 - 1) (2 * z) z
    simpa using (hasDerivAt_pow 2 z).sub_const 1
  | 3 =>
    change HasDerivAt (fun z : ℝ => z ^ 3 - 3 * z) (3 * z ^ 2 - 3) z
    have h1 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
    have h2 : HasDerivAt (fun z : ℝ => 3 * z) 3 z := by simpa using (hasDerivAt_id z).const_mul 3
    exact h1.sub h2

lemma hP_succ (m : ℕ) (hm : m ≤ 3) (z : ℝ) : z * hP m z - hP' m z = hP (m + 1) z := by
  match m with
  | 0 => simp [hP, hP']
  | 1 => simp [hP, hP']; ring
  | 2 => simp [hP, hP']; ring
  | 3 => simp [hP, hP']; ring

lemma abs_hP_le (m : ℕ) (z : ℝ) : |hP m z| ≤ 10 * (1 + |z|) ^ 4 := by
  have e0 : (1 : ℝ) ≤ (1 + |z|) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg z])
  have e1 := abs_pow_le_one_add z (k := 1) (by norm_num)
  have e2 := abs_pow_le_one_add z (k := 2) (by norm_num)
  have e3 := abs_pow_le_one_add z (k := 3) (by norm_num)
  have e4 := abs_pow_le_one_add z (k := 4) (by norm_num)
  rw [pow_one] at e1
  match m with
  | 0 => simp [hP]; linarith
  | 1 => simp only [hP]; linarith
  | 2 =>
    simp only [hP]
    have : |z ^ 2 - 1| ≤ |z| ^ 2 + 1 := by
      calc _ ≤ |z ^ 2| + |(1:ℝ)| := abs_sub _ _
        _ = _ := by rw [abs_pow]; norm_num
    linarith
  | 3 =>
    simp only [hP]
    have : |z ^ 3 - 3 * z| ≤ |z| ^ 3 + 3 * |z| := by
      calc _ ≤ |z ^ 3| + |3 * z| := abs_sub _ _
        _ = _ := by rw [abs_pow, abs_mul]; norm_num
    linarith
  | m + 4 =>
    simp only [hP]
    have : |z ^ 4 - 6 * z ^ 2 + 3| ≤ |z| ^ 4 + 6 * |z| ^ 2 + 3 := by
      calc _ ≤ |z ^ 4 - 6 * z ^ 2| + |(3:ℝ)| := abs_add_le _ _
        _ ≤ |z ^ 4| + |6 * z ^ 2| + |(3:ℝ)| := by gcongr; exact abs_sub _ _
        _ = _ := by rw [abs_pow, abs_mul, abs_pow]; norm_num
    linarith

lemma hasDerivAt_convH_hP {G : ℝ → ℝ} (hGc : Continuous G) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hG : ∀ t, |G t| ≤ A + L * |t|) (m : ℕ) (hm : m ≤ 3) (y : ℝ) :
    HasDerivAt (convH G (hP m)) (convH G (hP (m + 1)) y) y :=
  hasDerivAt_convH hGc hA hL hG (continuous_hP m) (continuous_hP' m) (hasDerivAt_hP m hm)
    (hP_succ m hm) (abs_hP_le m) (abs_hP_le (m + 1)) y

lemma convH_one_zero (y : ℝ) : convH (fun _ => 1) (hP 0) y = 1 := by
  simp only [convH, hP, one_mul]
  rw [integral_sub_right_eq_self (fun t => npdf t) y]
  exact integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma convH_one_eq_zero (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 4) (y : ℝ) :
    convH (fun _ => 1) (hP m) y = 0 := by
  have hd : ∀ k ≤ 3, ∀ y, HasDerivAt (convH (fun _ => (1:ℝ)) (hP k))
      (convH (fun _ => 1) (hP (k + 1)) y) y := fun k hk y =>
    hasDerivAt_convH_hP continuous_const zero_le_one le_rfl (fun t => by simp) k hk y
  have h1 : ∀ y, convH (fun _ => (1:ℝ)) (hP 1) y = 0 := fun y => by
    have e : convH (fun _ => (1:ℝ)) (hP 0) = fun _ => 1 := funext convH_one_zero
    have := hd 0 (by norm_num) y
    rw [e] at this
    exact this.unique (hasDerivAt_const y 1)
  have step : ∀ k ≤ 3, (∀ y, convH (fun _ => (1:ℝ)) (hP k) y = 0) →
      ∀ y, convH (fun _ => (1:ℝ)) (hP (k + 1)) y = 0 := fun k hk hz y => by
    have e : convH (fun _ => (1:ℝ)) (hP k) = fun _ => 0 := funext hz
    have := hd k hk y
    rw [e] at this
    exact this.unique (hasDerivAt_const y 0)
  have h2 := step 1 (by norm_num) h1
  have h3 := step 2 (by norm_num) h2
  have h4 := step 3 (by norm_num) h3
  interval_cases m
  · exact h1 y
  · exact h2 y
  · exact h3 y
  · exact h4 y

lemma integrable_pow_npdf (k : ℕ) (hk : k ≤ 4) : Integrable (fun t : ℝ => t ^ k * npdf t) :=
  integrable_poly_npdf (by fun_prop) (C := 1) (N := 4) fun z => by
    rw [abs_pow, one_mul]; exact abs_pow_le_one_add z hk

lemma integral_npdf : ∫ t, npdf t = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma integrable_npdf : Integrable npdf := integrable_gaussianPDFReal 0 1

lemma moment2 : ∫ t, t ^ 2 * npdf t = 1 := by
  have h := convH_one_eq_zero 2 (by norm_num) (by norm_num) 0
  have e : convH (fun _ => 1) (hP 2) 0 = ∫ t, (t ^ 2 * npdf t - npdf t) := by
    simp only [convH, hP, sub_zero, one_mul]; congr 1; funext t; ring
  rw [e, integral_sub (integrable_pow_npdf 2 (by norm_num)) integrable_npdf, integral_npdf] at h
  linarith

lemma moment4 : ∫ t, t ^ 4 * npdf t = 3 := by
  have h := convH_one_eq_zero 4 (by norm_num) (by norm_num) 0
  have e : convH (fun _ => 1) (hP 4) 0 =
      ∫ t, (t ^ 4 * npdf t - 6 * (t ^ 2 * npdf t) + 3 * npdf t) := by
    simp only [convH, hP, sub_zero, one_mul]; congr 1; funext t; ring
  have h4 := integrable_pow_npdf 4 (by norm_num)
  have h2 := (integrable_pow_npdf 2 (by norm_num)).const_mul 6
  have h42 : Integrable (fun t => t ^ 4 * npdf t - 6 * (t ^ 2 * npdf t)) := h4.sub h2
  have h0 : Integrable (fun t => 3 * npdf t) := integrable_npdf.const_mul 3
  rw [e, integral_add h42 h0, integral_sub h4 h2,
    integral_const_mul, integral_const_mul, moment2, integral_npdf] at h
  linarith


lemma lip_continuous {G : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hG : ∀ x y, |G x - G y| ≤ L * |x - y|) :
    Continuous G :=
  (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hG x y).continuous

lemma lip_growth {G : ℝ → ℝ} {L : ℝ} (hG : ∀ x y, |G x - G y| ≤ L * |x - y|) (t : ℝ) :
    |G t| ≤ |G 0| + L * |t| := by
  have := hG t 0
  rw [sub_zero] at this
  linarith [abs_sub_abs_le_abs_sub (G t) (G 0)]

lemma convH_hP3_bound {G : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hG : ∀ x y, |G x - G y| ≤ L * |x - y|) (y : ℝ) : |convH G (hP 3) y| ≤ 6 * L := by
  have hGc := lip_continuous hL hG
  have hGb := lip_growth hG
  have hI : Integrable (fun t => G t * (hP 3 (t - y) * npdf (t - y))) :=
    integrable_convH_integrand hGc (abs_nonneg _) hL hGb (continuous_hP 3) (abs_hP_le 3) y
  have hJ : Integrable (fun t => hP 3 (t - y) * npdf (t - y)) := by
    simpa using integrable_convH_integrand (G := fun _ => 1) continuous_const zero_le_one le_rfl
      (fun t => by simp) (continuous_hP 3) (abs_hP_le 3) y
  have h0 : ∫ t, hP 3 (t - y) * npdf (t - y) = 0 := by
    have := convH_one_eq_zero 3 (by norm_num) (by norm_num) y
    simpa [convH] using this
  have hIJ : Integrable (fun t => (G t - G y) * (hP 3 (t - y) * npdf (t - y))) := by
    refine (hI.sub (hJ.const_mul (G y))).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.sub_apply]; ring
  have e : convH G (hP 3) y = ∫ t, (G t - G y) * (hP 3 (t - y) * npdf (t - y)) := by
    have : ∫ t, (G t - G y) * (hP 3 (t - y) * npdf (t - y)) =
        ∫ t, (G t * (hP 3 (t - y) * npdf (t - y)) - G y * (hP 3 (t - y) * npdf (t - y))) := by
      congr 1; funext t; ring
    rw [this, integral_sub hI (hJ.const_mul _), integral_const_mul, h0, mul_zero, sub_zero]; rfl
  have hK : Integrable (fun t => L * ((|t| * |hP 3 t|) * npdf t)) := by
    refine (integrable_poly_npdf (C := 10) (N := 5)
      (by have := continuous_hP 3; fun_prop) ?_).const_mul L
    intro z
    rw [abs_mul, abs_abs, abs_abs]
    have h1 : |z| ≤ 1 + |z| := by linarith
    calc |z| * |hP 3 z| ≤ (1 + |z|) * (10 * (1 + |z|) ^ 4) :=
          mul_le_mul h1 (abs_hP_le 3 z) (abs_nonneg _) (by positivity)
      _ = 10 * (1 + |z|) ^ 5 := by ring
  have h4 := integrable_pow_npdf 4 (by norm_num)
  have h2 := (integrable_pow_npdf 2 (by norm_num)).const_mul 3
  have h42 : Integrable (fun t => t ^ 4 * npdf t + 3 * (t ^ 2 * npdf t)) := h4.add h2
  rw [e]
  calc |∫ t, (G t - G y) * (hP 3 (t - y) * npdf (t - y))|
      ≤ ∫ t, |(G t - G y) * (hP 3 (t - y) * npdf (t - y))| := abs_integral_le_integral_abs
    _ ≤ ∫ t, L * ((|t - y| * |hP 3 (t - y)|) * npdf (t - y)) := by
        refine integral_mono hIJ.abs (hK.comp_sub_right y) fun t => ?_
        simp only
        rw [abs_mul, abs_mul, abs_of_nonneg (npdf_nonneg _)]
        calc |G t - G y| * (|hP 3 (t - y)| * npdf (t - y)) ≤
            (L * |t - y|) * (|hP 3 (t - y)| * npdf (t - y)) :=
              mul_le_mul_of_nonneg_right (hG t y) (mul_nonneg (abs_nonneg _) (npdf_nonneg _))
          _ = _ := by ring
    _ = ∫ t, L * ((|t| * |hP 3 t|) * npdf t) :=
        integral_sub_right_eq_self (fun t => L * ((|t| * |hP 3 t|) * npdf t)) y
    _ ≤ ∫ t, L * (t ^ 4 * npdf t + 3 * (t ^ 2 * npdf t)) := by
        refine integral_mono hK (h42.const_mul L) fun t => ?_
        simp only
        apply mul_le_mul_of_nonneg_left _ hL
        have : |t| * |hP 3 t| ≤ t ^ 4 + 3 * t ^ 2 := by
          simp only [hP]
          rw [← abs_mul]
          have : t * (t ^ 3 - 3 * t) = t ^ 4 - 3 * t ^ 2 := by ring
          rw [this]
          calc |t ^ 4 - 3 * t ^ 2| ≤ |t ^ 4| + |3 * t ^ 2| := abs_sub _ _
            _ = t ^ 4 + 3 * t ^ 2 := by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        calc |t| * |hP 3 t| * npdf t ≤ (t ^ 4 + 3 * t ^ 2) * npdf t :=
              mul_le_mul_of_nonneg_right this (npdf_nonneg _)
          _ = _ := by ring
    _ = 6 * L := by
        rw [integral_const_mul, integral_add h4 h2, integral_const_mul, moment4, moment2]; ring

/-- **Gaussian smoothing in one dimension**: for an `L`-Lipschitz `G`, `y ↦ E G(y + Z)` is `C³` with
third derivative at most `6 L`. -/
theorem smooth1d {G : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hG : ∀ x y, |G x - G y| ≤ L * |x - y|) :
    ContDiff ℝ 3 (fun y => ∫ s, G (y + s) ∂gaussianReal 0 1) ∧
    ∀ y, |iteratedDeriv 3 (fun y => ∫ s, G (y + s) ∂gaussianReal 0 1) y| ≤ 6 * L := by
  have hGc := lip_continuous hL hG
  have hGb := lip_growth hG
  have hA : 0 ≤ |G 0| := abs_nonneg _
  have e0 : (fun y => ∫ s, G (y + s) ∂gaussianReal 0 1) = convH G (hP 0) := by
    funext y
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc ∫ s, gaussianPDFReal 0 1 s • G (y + s) = ∫ s, npdf s * G (y + s) := rfl
      _ = ∫ t, npdf (t - y) * G (y + (t - y)) :=
          (integral_sub_right_eq_self (fun s => npdf s * G (y + s)) y).symm
      _ = convH G (hP 0) y := by
          simp only [convH, hP]; congr 1; funext t
          have : y + (t - y) = t := by ring
          rw [this]; ring
  have d : ∀ m ≤ 3, ∀ y, HasDerivAt (convH G (hP m)) (convH G (hP (m + 1)) y) y :=
    fun m hm y => hasDerivAt_convH_hP hGc hA hL hGb m hm y
  have D : ∀ m ≤ 3, deriv (convH G (hP m)) = convH G (hP (m + 1)) :=
    fun m hm => funext fun y => (d m hm y).deriv
  rw [e0]
  constructor
  · have c3 : ContDiff ℝ 0 (convH G (hP 3)) :=
      contDiff_zero.2 (continuous_iff_continuousAt.2 fun y => (d 3 le_rfl y).continuousAt)
    have c2 : ContDiff ℝ 1 (convH G (hP 2)) := by
      have : ContDiff ℝ (0 + 1) (convH G (hP 2)) := contDiff_succ_iff_deriv.2
        ⟨fun y => (d 2 (by norm_num) y).differentiableAt, by simp,
          by rw [D 2 (by norm_num)]; exact c3⟩
      simpa using this
    have c1 : ContDiff ℝ 2 (convH G (hP 1)) := by
      have : ContDiff ℝ (1 + 1) (convH G (hP 1)) := contDiff_succ_iff_deriv.2
        ⟨fun y => (d 1 (by norm_num) y).differentiableAt, by simp,
          by rw [D 1 (by norm_num)]; exact c2⟩
      exact this
    have : ContDiff ℝ (2 + 1) (convH G (hP 0)) := contDiff_succ_iff_deriv.2
      ⟨fun y => (d 0 (by norm_num) y).differentiableAt, by simp,
        by rw [D 0 (by norm_num)]; exact c1⟩
    exact this
  · intro y
    rw [iteratedDeriv_eq_iterate]
    change |deriv (deriv (deriv (convH G (hP 0)))) y| ≤ 6 * L
    rw [D 0 (by norm_num), D 1 (by norm_num), D 2 (by norm_num)]
    exact convH_hP3_bound hL hG y


/-! ### Two dimensions -/

open scoped RealInnerProductSpace

lemma lipPair_nonneg {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) : 0 ≤ K := by
  have := hΨ 1 0 0 0
  norm_num at this
  exact (abs_nonneg _).trans this

lemma continuous_uncurry_of_lipPair {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) :
    Continuous (Function.uncurry Ψ) := by
  have hK := lipPair_nonneg hΨ
  refine (LipschitzWith.of_dist_le_mul (K := ⟨2 * K, by positivity⟩) fun p q => ?_).continuous
  rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h := hΨ p.1 p.2 q.1 q.2
  have h1 := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h2 := le_max_right |p.1 - q.1| |p.2 - q.2|
  change |Ψ p.1 p.2 - Ψ q.1 q.2| ≤ 2 * K * max _ _
  nlinarith

lemma map_coord_gm (i : Fin 2) : (gm 2).map (fun z : Gs 2 => z i) = gaussianReal 0 1 := by
  have := Gaussian.map_inner_stdGaussian (E := Gs 2) (u := EuclideanSpace.single i 1) (by simp)
  convert this using 2
  funext z; simp [EuclideanSpace.inner_single_left]

lemma integrable_coord (i : Fin 2) : Integrable (fun z : Gs 2 => z i) (gm 2) := by
  have h : Integrable (fun s : ℝ => s) ((gm 2).map (fun z : Gs 2 => z i)) := by
    rw [map_coord_gm]; exact IsGaussian.integrable_fun_id
  exact (integrable_map_measure h.aestronglyMeasurable
    (by fun_prop : Continuous fun z : Gs 2 => z i).measurable.aemeasurable).1 h

lemma integral_sq_gauss : ∫ s, s ^ 2 ∂gaussianReal 0 1 = 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← moment2]
  congr 1; funext s; simp only [smul_eq_mul]; ring

lemma integral_abs_gauss_le : ∫ s, |s| ∂gaussianReal 0 1 ≤ 1 := by
  have hi1 : Integrable (fun s : ℝ => |s|) (gaussianReal 0 1) := IsGaussian.integrable_fun_id.abs
  have hi2 : Integrable (fun s : ℝ => s ^ 2) (gaussianReal 0 1) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hi3 : Integrable (fun s : ℝ => 1 / 2 + s ^ 2 / 2) (gaussianReal 0 1) :=
    (integrable_const _).add (hi2.div_const 2)
  calc ∫ s, |s| ∂gaussianReal 0 1 ≤ ∫ s, (1 / 2 + s ^ 2 / 2) ∂gaussianReal 0 1 :=
        integral_mono hi1 hi3 (fun s => by nlinarith [sq_abs s, abs_nonneg s, sq_nonneg (|s| - 1)])
    _ = 1 := by
        rw [integral_add (integrable_const _) (hi2.div_const 2), integral_const, integral_div,
          integral_sq_gauss]
        simp; norm_num

lemma integral_abs_coord_le (i : Fin 2) : ∫ z, |z i| ∂gm 2 ≤ 1 := by
  have : ∫ z, |z i| ∂gm 2 = ∫ s, |s| ∂gaussianReal 0 1 := by
    rw [← map_coord_gm i, integral_map
      (by fun_prop : Continuous fun z : Gs 2 => z i).measurable.aemeasurable
      continuous_abs.aestronglyMeasurable]
  rw [this]; exact integral_abs_gauss_le

lemma integrable_moll_integrand {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) (α β η : ℝ) :
    Integrable (fun z : Gs 2 => Ψ (α + η * z 0) (β + η * z 1)) (gm 2) := by
  have hc := continuous_uncurry_of_lipPair hΨ
  have hb : Integrable (fun z : Gs 2 => |Ψ α β| + K * |η| * (|z 0| + |z 1|)) (gm 2) :=
    (integrable_const _).add (((integrable_coord 0).abs.add (integrable_coord 1).abs).const_mul _)
  refine hb.mono' (hc.comp (by fun_prop : Continuous fun z : Gs 2 =>
    (α + η * z 0, β + η * z 1))).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h := hΨ (α + η * z 0) (β + η * z 1) α β
  have e1 : α + η * z 0 - α = η * z 0 := by ring
  have e2 : β + η * z 1 - β = η * z 1 := by ring
  rw [e1, e2, abs_mul, abs_mul] at h
  have := abs_sub_abs_le_abs_sub (Ψ (α + η * z 0) (β + η * z 1)) (Ψ α β)
  have e3 : K * (|η| * |z 0| + |η| * |z 1|) = K * |η| * (|z 0| + |z 1|) := by ring
  linarith

lemma integrable_line {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) (α β α' β' : ℝ) :
    Integrable (fun t => Ψ (α + β * t) (α' + β' * t)) (gaussianReal 0 1) := by
  have hc := continuous_uncurry_of_lipPair hΨ
  have hb : Integrable (fun t : ℝ => |Ψ α α'| + K * (|β| + |β'|) * |t|) (gaussianReal 0 1) :=
    (integrable_const _).add (IsGaussian.integrable_fun_id.abs.const_mul _)
  refine hb.mono' (hc.comp (by fun_prop : Continuous fun t : ℝ =>
    (α + β * t, α' + β' * t))).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs]
  have h := hΨ (α + β * t) (α' + β' * t) α α'
  have e1 : α + β * t - α = β * t := by ring
  have e2 : α' + β' * t - α' = β' * t := by ring
  rw [e1, e2, abs_mul, abs_mul] at h
  have := abs_sub_abs_le_abs_sub (Ψ (α + β * t) (α' + β' * t)) (Ψ α α')
  have e3 : K * (|β| * |t| + |β'| * |t|) = K * (|β| + |β'|) * |t| := by ring
  linarith

/-- The Gaussian mollification `Φ(a, b) = E Ψ(a + η Z₀, b + η Z₁)`. -/
noncomputable def moll (Ψ : ℝ → ℝ → ℝ) (η : ℝ) (a b : ℝ) : ℝ :=
  ∫ z, Ψ (a + η * z 0) (b + η * z 1) ∂gm 2

lemma lipPair_moll {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) (η : ℝ) :
    LipPair (moll Ψ η) K := by
  intro a b a' b'
  unfold moll
  rw [← integral_sub (integrable_moll_integrand hΨ a b η) (integrable_moll_integrand hΨ a' b' η)]
  have := norm_integral_le_of_norm_le_const (μ := gm 2) (C := K * (|a - a'| + |b - b'|))
    (f := fun z => Ψ (a + η * z 0) (b + η * z 1) - Ψ (a' + η * z 0) (b' + η * z 1))
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      have := hΨ (a + η * z 0) (b + η * z 1) (a' + η * z 0) (b' + η * z 1)
      have e1 : a + η * z 0 - (a' + η * z 0) = a - a' := by ring
      have e2 : b + η * z 1 - (b' + η * z 1) = b - b' := by ring
      rwa [e1, e2] at this)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma abs_moll_sub_le {Ψ : ℝ → ℝ → ℝ} {K η : ℝ} (hη : 0 < η) (hΨ : LipPair Ψ K) (a b : ℝ) :
    |moll Ψ η a b - Ψ a b| ≤ 2 * K * η := by
  have hK := lipPair_nonneg hΨ
  unfold moll
  have hint := integrable_moll_integrand hΨ a b η
  have e : (∫ z, Ψ (a + η * z 0) (b + η * z 1) ∂gm 2) - Ψ a b =
      ∫ z, (Ψ (a + η * z 0) (b + η * z 1) - Ψ a b) ∂gm 2 := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp
  rw [e]
  have h01 : Integrable (fun z : Gs 2 => |z 0| + |z 1|) (gm 2) :=
    (integrable_coord 0).abs.add (integrable_coord 1).abs
  have hb : Integrable (fun z : Gs 2 => K * η * (|z 0| + |z 1|)) (gm 2) := h01.const_mul _
  have hd : Integrable (fun z : Gs 2 => Ψ (a + η * z 0) (b + η * z 1) - Ψ a b) (gm 2) :=
    hint.sub (integrable_const _)
  calc |∫ z, (Ψ (a + η * z 0) (b + η * z 1) - Ψ a b) ∂gm 2|
      ≤ ∫ z, |Ψ (a + η * z 0) (b + η * z 1) - Ψ a b| ∂gm 2 := abs_integral_le_integral_abs
    _ ≤ ∫ z, K * η * (|z 0| + |z 1|) ∂gm 2 := by
        refine integral_mono hd.abs hb fun z => ?_
        have h := hΨ (a + η * z 0) (b + η * z 1) a b
        have e1 : a + η * z 0 - a = η * z 0 := by ring
        have e2 : b + η * z 1 - b = η * z 1 := by ring
        rw [e1, e2, abs_mul, abs_mul, abs_of_pos hη] at h
        calc _ ≤ _ := h
          _ = K * η * (|z 0| + |z 1|) := by ring
    _ = K * η * ((∫ z, |z 0| ∂gm 2) + ∫ z, |z 1| ∂gm 2) := by
        rw [integral_const_mul, integral_add (integrable_coord 0).abs (integrable_coord 1).abs]
    _ ≤ K * η * (1 + 1) := by
        have := integral_abs_coord_le 0
        have := integral_abs_coord_le 1
        gcongr
    _ = 2 * K * η := by ring


/-- Along a line with direction `(a', b') ≠ 0`, the mollification is a one-dimensional Gaussian
smoothing (rotate the Gaussian so that its first coordinate is along `(a', b')`). -/
lemma moll_line_eq {Ψ : ℝ → ℝ → ℝ} {K η : ℝ} (hη : 0 < η) (hΨ : LipPair Ψ K)
    (a b a' b' ρ u₀ u₁ : ℝ) (ha' : a' = ρ * u₀) (hb' : b' = ρ * u₁)
    (hu : u₀ ^ 2 + u₁ ^ 2 = 1) (x : ℝ) :
    moll Ψ η (a + x * a') (b + x * b') =
      ∫ s, (fun y => ∫ t, Ψ ((a + η * u₀ * y) + (-(η * u₁)) * t)
        ((b + η * u₁ * y) + (η * u₀) * t) ∂gaussianReal 0 1) ((ρ / η) * x + s)
        ∂gaussianReal 0 1 := by
  have hc := continuous_uncurry_of_lipPair hΨ
  let u : Gs 2 := !₂[u₀, u₁]
  let v : Gs 2 := !₂[-u₁, u₀]
  have hu1 : ‖u‖ = 1 := by
    simp [u, EuclideanSpace.norm_eq, Fin.sum_univ_two, hu]
  have hv1 : ‖v‖ = 1 := by
    simp [v, EuclideanSpace.norm_eq, Fin.sum_univ_two, add_comm, hu]
  have huv : ⟪u, v⟫ = 0 := by
    simp [u, v, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hiu : ∀ z : Gs 2, ⟪u, z⟫ = u₀ * z 0 + u₁ * z 1 := fun z => by
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hiv : ∀ z : Gs 2, ⟪v, z⟫ = -u₁ * z 0 + u₀ * z 1 := fun z => by
    simp [v, PiLp.inner_apply, Fin.sum_univ_two]; ring
  let F : ℝ × ℝ → ℝ := fun p => Ψ (a + x * a' + η * (u₀ * p.1 - u₁ * p.2))
    (b + x * b' + η * (u₁ * p.1 + u₀ * p.2))
  have hFc : Continuous F := hc.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
    (a + x * a' + η * (u₀ * p.1 - u₁ * p.2), b + x * b' + η * (u₁ * p.1 + u₀ * p.2)))
  have hpair : Continuous fun z : Gs 2 => (⟪u, z⟫, ⟪v, z⟫) := by fun_prop
  have hcomp : (fun z : Gs 2 => F (⟪u, z⟫, ⟪v, z⟫)) =
      fun z => Ψ (a + x * a' + η * z 0) (b + x * b' + η * z 1) := by
    funext z
    simp only [F, hiu, hiv]
    have h0 : u₀ * (u₀ * z 0 + u₁ * z 1) - u₁ * (-u₁ * z 0 + u₀ * z 1) = z 0 := by
      linear_combination (z 0) * hu
    have h1 : u₁ * (u₀ * z 0 + u₁ * z 1) + u₀ * (-u₁ * z 0 + u₀ * z 1) = z 1 := by
      linear_combination (z 1) * hu
    rw [h0, h1]
  have hmap := Gaussian.map_inner_pair_stdGaussian hu1 hv1 huv
  have hFint : Integrable F ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [← hmap, integrable_map_measure hFc.aestronglyMeasurable hpair.measurable.aemeasurable]
    change Integrable (fun z : Gs 2 => F (⟪u, z⟫, ⟪v, z⟫)) (gm 2)
    rw [hcomp]
    exact integrable_moll_integrand hΨ _ _ η
  calc moll Ψ η (a + x * a') (b + x * b')
      = ∫ z, F (⟪u, z⟫, ⟪v, z⟫) ∂gm 2 := by rw [hcomp]; rfl
    _ = ∫ p, F p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        rw [← hmap, integral_map hpair.measurable.aemeasurable hFc.aestronglyMeasurable]
    _ = ∫ s, ∫ t, F (s, t) ∂gaussianReal 0 1 ∂gaussianReal 0 1 := integral_prod F hFint
    _ = _ := by
        congr 1; funext s; congr 1; funext t
        simp only [F]
        congr 1
        · rw [ha']; field_simp; ring
        · rw [hb']; field_simp; ring

lemma lineC3_moll {Ψ : ℝ → ℝ → ℝ} {K η : ℝ} (hη : 0 < η) (hΨ : LipPair Ψ K) :
    LineC3 (moll Ψ η) (100 * K / η ^ 2) := by
  have hK := lipPair_nonneg hΨ
  intro a b a' b'
  by_cases hw : a' = 0 ∧ b' = 0
  · obtain ⟨rfl, rfl⟩ := hw
    simp only [mul_zero, add_zero]
    refine ⟨contDiff_const, fun x => ?_⟩
    rw [iteratedDeriv_const]; simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = √(a' ^ 2 + b' ^ 2) := ⟨_, rfl⟩
  have hpos : 0 < a' ^ 2 + b' ^ 2 := by
    rcases not_and_or.1 hw with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  have hρ0 : 0 < ρ := hρ ▸ Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = a' ^ 2 + b' ^ 2 := by rw [hρ, Real.sq_sqrt hpos.le]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = a' / ρ := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = b' / ρ := ⟨_, rfl⟩
  have ha' : a' = ρ * u₀ := by rw [hu₀]; field_simp
  have hb' : b' = ρ * u₁ := by rw [hu₁]; field_simp
  have hu : u₀ ^ 2 + u₁ ^ 2 = 1 := by
    rw [hu₀, hu₁, div_pow, div_pow, ← add_div, ← hρ2]; field_simp
  let Gf : ℝ → ℝ := fun y => ∫ t, Ψ ((a + η * u₀ * y) + (-(η * u₁)) * t)
    ((b + η * u₁ * y) + (η * u₀) * t) ∂gaussianReal 0 1
  have hGf : ∀ y y', |Gf y - Gf y'| ≤ (K * η * (|u₀| + |u₁|)) * |y - y'| := fun y y' => by
    simp only [Gf]
    rw [← integral_sub (integrable_line hΨ _ _ _ _) (integrable_line hΨ _ _ _ _)]
    have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (C := K * η * (|u₀| + |u₁|) * |y - y'|)
      (f := fun t => Ψ ((a + η * u₀ * y) + (-(η * u₁)) * t) ((b + η * u₁ * y) + (η * u₀) * t) -
        Ψ ((a + η * u₀ * y') + (-(η * u₁)) * t) ((b + η * u₁ * y') + (η * u₀) * t))
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs]
        have h := hΨ ((a + η * u₀ * y) + (-(η * u₁)) * t) ((b + η * u₁ * y) + (η * u₀) * t)
          ((a + η * u₀ * y') + (-(η * u₁)) * t) ((b + η * u₁ * y') + (η * u₀) * t)
        have e1 : (a + η * u₀ * y) + (-(η * u₁)) * t - ((a + η * u₀ * y') + (-(η * u₁)) * t) =
          η * u₀ * (y - y') := by ring
        have e2 : (b + η * u₁ * y) + (η * u₀) * t - ((b + η * u₁ * y') + (η * u₀) * t) =
          η * u₁ * (y - y') := by ring
        rw [e1, e2, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hη] at h
        calc _ ≤ _ := h
          _ = _ := by ring)
    rw [Real.norm_eq_abs] at this
    simpa using this
  have hL : 0 ≤ K * η * (|u₀| + |u₁|) := by positivity
  obtain ⟨hh, hh3⟩ := smooth1d hL hGf
  have hline : (fun x : ℝ => moll Ψ η (a + x * a') (b + x * b')) =
      fun x => (fun y => ∫ s, Gf (y + s) ∂gaussianReal 0 1) ((ρ / η) * x) := by
    funext x
    exact moll_line_eq hη hΨ a b a' b' ρ u₀ u₁ ha' hb' hu x
  rw [hline]
  have hh' : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => ∫ s, Gf (y + s) ∂gaussianReal 0 1) := hh
  refine ⟨hh.comp (contDiff_const.mul contDiff_id), fun x => ?_⟩
  rw [iteratedDeriv_comp_const_mul hh' (ρ / η)]
  have hS : |u₀| + |u₁| = (|a'| + |b'|) / ρ := by
    rw [hu₀, hu₁, abs_div, abs_div, abs_of_pos hρ0, add_div]
  have hρS : ρ ^ 2 ≤ (|a'| + |b'|) ^ 2 := by
    rw [hρ2]; nlinarith [abs_nonneg a', abs_nonneg b', sq_abs a', sq_abs b',
      mul_nonneg (abs_nonneg a') (abs_nonneg b')]
  have hS0 : 0 ≤ |a'| + |b'| := by positivity
  calc |(ρ / η) ^ 3 * iteratedDeriv 3 (fun y => ∫ s, Gf (y + s) ∂gaussianReal 0 1) (ρ / η * x)|
      = (ρ / η) ^ 3 * |iteratedDeriv 3 (fun y => ∫ s, Gf (y + s) ∂gaussianReal 0 1)
          (ρ / η * x)| := by rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (ρ / η) ^ 3 * (6 * (K * η * (|u₀| + |u₁|))) := by gcongr; exact hh3 _
    _ = 6 * K * ρ ^ 2 * (|a'| + |b'|) / η ^ 2 := by
        rw [hS]; field_simp
    _ ≤ 6 * K * (|a'| + |b'|) ^ 2 * (|a'| + |b'|) / η ^ 2 := by gcongr
    _ ≤ 100 * K / η ^ 2 * (|a'| + |b'|) ^ 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        have := mul_nonneg hK (pow_nonneg hS0 3)
        nlinarith

end BGHKLMM26.RobustMIS.Mollify

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set

/-- **Mollification** of a Lipschitz test function of two variables. -/
theorem mollify {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) (Ψ : ℝ → ℝ → ℝ) (hΨ : LipPair Ψ K) :
    ∃ Φ : ℝ → ℝ → ℝ, LipPair Φ K ∧ LineC3 Φ (100 * K / η ^ 2) ∧
      ∀ a b, |Φ a b - Ψ a b| ≤ 2 * K * η :=
  have _h := hK
  ⟨Mollify.moll Ψ η, Mollify.lipPair_moll hΨ η, Mollify.lineC3_moll hη hΨ,
    Mollify.abs_moll_sub_le hη hΨ⟩

end BGHKLMM26.RobustMIS
