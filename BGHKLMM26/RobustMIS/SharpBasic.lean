module

public import BGHKLMM26.RobustMIS.SharpDefs
public import BGHKLMM26.RobustMIS.Gaussian
public import BGHKLMM26.RobustMIS.GaussL2

/-!
# The sharp Gaussian lemma: the noise form

The algebra of the noise form `nBil t F G = ⟨F, T_t G⟩` on bounded measurable functions: symmetry,
the expansion of `nBil t (F + G) (F + G)`, positivity and Young's inequality for `0 ≤ t ≤ 1`, the
bounds `nBil t F F ≤ nBil t |F| |F| ≤ E F²`, and the small-mass bound `nBil t v v = o(E|v|)`,
which replaces Gaussian hypercontractivity: `nBil t v v ≤ nBil t |v| |v| ≤ Γ_t(E|v|)` by Borell's
inequality, and `Γ_t(m) = o(m)` as `m → 0`.

All statements are proved. Proofs:
* symmetry: the rotation `(x, z) ↦ (t x + √(1-t²) z, √(1-t²) x - t z)` of `γ ⊗ γ`
  (`Deficit.integral_rot`) exchanges `X` and `Y`;
* positivity: `nBil t F F = E[(E F(√t W + √(1-t) V))²]` over `W` (`SharpB.nBil_eq_heat`, as
  `Deficit.gStab_eq_heat'`, by the same rotation and `Deficit.integral_rescale`);
* `E F²`: Cauchy–Schwarz, `X` and `Y` being both standard Gaussian;
* `Γ_t(m) ≤ ε m` for small `m` (`SharpB.Gam_le_mul`): `Γ_t(m) = 2 ∫_{-∞}^{Ψ(m)} φ(x) Φ(κ_t x) dx`
  (`GammaCalc.Gam_eq_two_mul`) and `Φ(κ_t x) ≤ ε/2` there.

Helpers (namespace `SharpB`): `nBil_eq_prod` (the noise form as one integral over `γ ⊗ γ`),
`integrable_integrand`, the bilinearity lemmas `nBil_add_left`, `nBil_add_right`,
`nBil_const_mul_left`, `nBil_const_mul_right`, `nBil_lin_self` (expansion of
`nBil t (a F + b G) (a F + b G)`), the heat representation `nBil_eq_heat`, `nBil_le_mean`
(`nBil t f f ≤ E|f|` for `|f| ≤ 1`), and `Gam_le_mul`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace
open Gaussian

variable {n : ℕ}

namespace SharpB

theorem nonneg_of_abs_le {F : Gs n → ℝ} {C : ℝ} (hFC : ∀ x, |F x| ≤ C) : 0 ≤ C :=
  (abs_nonneg _).trans (hFC 0)

theorem measurable_integrand (t : ℝ) {F G : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun p : Gs n × Gs n ↦ F p.1 * G (t • p.1 + √(1 - t ^ 2) • p.2)) :=
  (hF.comp measurable_fst).mul (hG.comp (GaussL2.measurable_rot t))

theorem integrable_integrand (t : ℝ) {F G : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGD : ∀ x, |G x| ≤ D) :
    Integrable (fun p : Gs n × Gs n ↦ F p.1 * G (t • p.1 + √(1 - t ^ 2) • p.2))
      ((gm n).prod (gm n)) :=
  Gaussian.integrable_of_abs_le (measurable_integrand t hF hG) (C := C * D) fun p ↦ by
    rw [abs_mul]
    exact mul_le_mul (hFC _) (hGD _) (abs_nonneg _) (nonneg_of_abs_le hFC)

/-- The noise form as one integral over `γ ⊗ γ`. -/
theorem nBil_eq_prod (t : ℝ) {F G : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGD : ∀ x, |G x| ≤ D) :
    nBil t F G = ∫ p, F p.1 * G (t • p.1 + √(1 - t ^ 2) • p.2) ∂(gm n).prod (gm n) := by
  rw [integral_prod _ (integrable_integrand t hF hG hFC hGD)]
  rfl

theorem abs_add_le_of_le {F G : Gs n → ℝ} {C D : ℝ} (hFC : ∀ x, |F x| ≤ C)
    (hGD : ∀ x, |G x| ≤ D) : ∀ x, |F x + G x| ≤ C + D :=
  fun x ↦ (abs_add_le _ _).trans (add_le_add (hFC x) (hGD x))

theorem measurable_add {F G : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun x ↦ F x + G x :=
  hF.add hG

theorem measurable_abs {F : Gs n → ℝ} (hF : Measurable F) : Measurable fun x ↦ |F x| :=
  continuous_abs.measurable.comp hF

theorem abs_const_mul_le_of_le {F : Gs n → ℝ} {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (a : ℝ) :
    ∀ x, |a * F x| ≤ |a| * C :=
  fun x ↦ by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFC x) (abs_nonneg a)

theorem nBil_add_left (t : ℝ) {F G H : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hH : Measurable H) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGC : ∀ x, |G x| ≤ C)
    (hHC : ∀ x, |H x| ≤ C) :
    nBil t (fun x ↦ F x + G x) H = nBil t F H + nBil t G H := by
  rw [nBil_eq_prod t (measurable_add hF hG) hH (abs_add_le_of_le hFC hGC) hHC,
    nBil_eq_prod t hF hH hFC hHC, nBil_eq_prod t hG hH hGC hHC,
    ← integral_add (integrable_integrand t hF hH hFC hHC) (integrable_integrand t hG hH hGC hHC)]
  congr 1
  funext p
  ring

theorem nBil_add_right (t : ℝ) {F G H : Gs n → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hH : Measurable H) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGC : ∀ x, |G x| ≤ C)
    (hHC : ∀ x, |H x| ≤ C) :
    nBil t H (fun x ↦ F x + G x) = nBil t H F + nBil t H G := by
  rw [nBil_eq_prod t hH (measurable_add hF hG) hHC (abs_add_le_of_le hFC hGC),
    nBil_eq_prod t hH hF hHC hFC, nBil_eq_prod t hH hG hHC hGC,
    ← integral_add (integrable_integrand t hH hF hHC hFC) (integrable_integrand t hH hG hHC hGC)]
  congr 1
  funext p
  ring

theorem nBil_const_mul_left (t a : ℝ) (F G : Gs n → ℝ) :
    nBil t (fun x ↦ a * F x) G = a * nBil t F G := by
  unfold nBil
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

theorem nBil_const_mul_right (t a : ℝ) (F G : Gs n → ℝ) :
    nBil t F (fun x ↦ a * G x) = a * nBil t F G := by
  unfold nBil
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-! ### The heat representation -/

/-- `x ↦ E F(x + b Z)`. -/
noncomputable def heat (F : Gs n → ℝ) (b : ℝ) (x : Gs n) : ℝ := ∫ v, F (x + b • v) ∂gm n

theorem measurable_heat {F : Gs n → ℝ} (hF : Measurable F) (b : ℝ) : Measurable (heat F b) := by
  have h : StronglyMeasurable (fun p : Gs n × Gs n ↦ F (p.1 + b • p.2)) :=
    (hF.comp (by fun_prop)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem abs_heat_le {F : Gs n → ℝ} {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (b : ℝ) (x : Gs n) :
    |heat F b x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := gm n) (f := fun v ↦ F (x + b • v)) (C := C)
    (ae_of_all _ fun v ↦ by rw [Real.norm_eq_abs]; exact hFC _)
  simpa [heat] using h

/-- `nBil t F F = E[(E F(√t W + √(1 - t) V))²]` over `W`, for `0 ≤ t < 1`. -/
theorem nBil_eq_heat {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {F : Gs n → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ x, |F x| ≤ C) :
    nBil t F F = ∫ z, heat F (√(1 - t)) (√t • z) ^ 2 ∂gm n := by
  have ha2 : √t ^ 2 = t := sq_sqrt ht0
  have hb2 : √(1 - t) ^ 2 = 1 - t := sq_sqrt (by linarith)
  have hab : √t ^ 2 + √(1 - t) ^ 2 = 1 := by rw [ha2, hb2]; ring
  have hc : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hc2 : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := sq_sqrt (by nlinarith)
  have hC0 : 0 ≤ C := nonneg_of_abs_le hFC
  have hhm := measurable_heat hF (√(1 - t))
  have hhC := abs_heat_le hFC (√(1 - t))
  have key : ∀ x, ∫ w, heat F (√(1 - t)) (√t • (√t • x + √(1 - t) • w)) ∂gm n =
      ∫ v, F (t • x + √(1 - t ^ 2) • v) ∂gm n := by
    intro x
    have hg : Measurable fun v : Gs n ↦ F (t • x + v) := hF.comp (by fun_prop)
    rw [Deficit.integral_rescale (fun v ↦ F (t • x + v)) hg (fun v ↦ hFC _)
      (c₁ := √t * √(1 - t)) (c₂ := √(1 - t)) hc (by rw [mul_pow, ha2, hb2, hc2]; ring)]
    congr 1
    funext w
    simp only [heat]
    congr 1
    funext y
    congr 1
    rw [smul_add, smul_smul, ← sq, ha2, add_assoc, mul_smul]
  have hL : nBil t F F = ∫ x, F x * ∫ v, F (t • x + √(1 - t ^ 2) • v) ∂gm n ∂gm n := by
    unfold nBil
    congr 1
    funext x
    rw [integral_const_mul]
  let Φ : Gs n × Gs n → ℝ := fun p ↦
    F (√t • p.1 + √(1 - t) • p.2) * heat F (√(1 - t)) (√t • p.1)
  have hΦm : Measurable Φ := (hF.comp (by fun_prop)).mul (hhm.comp (by fun_prop))
  have hΦb : ∀ p, |Φ p| ≤ C * C := fun p ↦ by
    simp only [Φ, abs_mul]
    exact mul_le_mul (hFC _) (hhC _) (abs_nonneg _) hC0
  have hR1 : ∫ z, heat F (√(1 - t)) (√t • z) ^ 2 ∂gm n = ∫ z, ∫ y, Φ (z, y) ∂gm n ∂gm n := by
    congr 1
    funext z
    simp only [Φ]
    rw [integral_mul_const, sq]
    rfl
  rw [hL, hR1, Deficit.integral_rot Φ hΦm hΦb hab]
  congr 1
  funext x
  simp only [Φ]
  simp_rw [Deficit.rot_vec hab]
  rw [← key x, integral_const_mul]

end SharpB

open SharpB

/-- The noise form is symmetric: the pair `(X, Y)` is exchangeable. -/
theorem nBil_comm {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F G : Gs n → ℝ} (hF : Measurable F)
    (hG : Measurable G) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGC : ∀ x, |G x| ≤ C) :
    nBil t F G = nBil t G F := by
  have hab : t ^ 2 + √(1 - t ^ 2) ^ 2 = 1 := by
    rw [sq_sqrt (by nlinarith [ht.1, ht.2])]
    ring
  let Φ : Gs n × Gs n → ℝ := fun p ↦ G p.1 * F (t • p.1 + √(1 - t ^ 2) • p.2)
  have hΦm : Measurable Φ := measurable_integrand t hG hF
  have hΦb : ∀ p, |Φ p| ≤ C * C := fun p ↦ by
    simp only [Φ, abs_mul]
    exact mul_le_mul (hGC _) (hFC _) (abs_nonneg _) (nonneg_of_abs_le hFC)
  have h := Deficit.integral_rot Φ hΦm hΦb hab
  have e : nBil t G F = ∫ z, ∫ y, Φ (z, y) ∂gm n ∂gm n := rfl
  rw [e, h]
  unfold nBil
  congr 1
  funext x
  congr 1
  funext w
  simp only [Φ]
  rw [Deficit.rot_vec hab, mul_comm]

namespace SharpB

/-- The expansion of `nBil t (a F + b G) (a F + b G)`. -/
theorem nBil_lin_self {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F G : Gs n → ℝ} (hF : Measurable F)
    (hG : Measurable G) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGC : ∀ x, |G x| ≤ C) (a b : ℝ) :
    nBil t (fun x ↦ a * F x + b * G x) (fun x ↦ a * F x + b * G x) =
      a ^ 2 * nBil t F F + 2 * (a * b) * nBil t F G + b ^ 2 * nBil t G G := by
  obtain ⟨D, hD⟩ : ∃ D, D = |a| * C + |b| * C := ⟨_, rfl⟩
  have haF : ∀ x, |a * F x| ≤ D := fun x ↦ (abs_const_mul_le_of_le hFC a x).trans
    (by rw [hD]; nlinarith [abs_nonneg b, nonneg_of_abs_le hFC])
  have hbG : ∀ x, |b * G x| ≤ D := fun x ↦ (abs_const_mul_le_of_le hGC b x).trans
    (by rw [hD]; nlinarith [abs_nonneg a, nonneg_of_abs_le hFC])
  have hHC : ∀ x, |a * F x + b * G x| ≤ D + D := abs_add_le_of_le haF hbG
  have hD2 : ∀ x, |a * F x| ≤ D + D := fun x ↦ (haF x).trans
    (by linarith [(abs_nonneg _).trans (haF x)])
  have hE2 : ∀ x, |b * G x| ≤ D + D := fun x ↦ (hbG x).trans
    (by linarith [(abs_nonneg _).trans (hbG x)])
  have hmF := hF.const_mul a
  have hmG := hG.const_mul b
  rw [nBil_add_left t hmF hmG (measurable_add hmF hmG) hD2 hE2 hHC,
    nBil_add_right t hmF hmG hmF hD2 hE2 hD2, nBil_add_right t hmF hmG hmG hD2 hE2 hE2,
    nBil_const_mul_left, nBil_const_mul_left, nBil_const_mul_left, nBil_const_mul_left,
    nBil_const_mul_right, nBil_const_mul_right, nBil_const_mul_right, nBil_const_mul_right,
    nBil_comm ht hG hF hGC hFC]
  ring

end SharpB

/-- The expansion of the noise form of a sum. -/
theorem nBil_add_self {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F G : Gs n → ℝ} (hF : Measurable F)
    (hG : Measurable G) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) (hGC : ∀ x, |G x| ≤ C) :
    nBil t (fun x ↦ F x + G x) (fun x ↦ F x + G x) =
      nBil t F F + 2 * nBil t F G + nBil t G G := by
  have h := nBil_lin_self ht hF hG hFC hGC 1 1
  simp only [one_mul, one_pow, mul_one] at h
  exact h

/-- Positivity: `nBil t F F = E[(T_{√t} F)²] ≥ 0` for `0 ≤ t ≤ 1`. -/
theorem nBil_self_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {F : Gs n → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ x, |F x| ≤ C) : 0 ≤ nBil t F F := by
  rcases ht1.lt_or_eq with h | rfl
  · rw [nBil_eq_heat ht0 h hF hFC]
    exact integral_nonneg fun z ↦ sq_nonneg _
  · refine integral_nonneg fun x ↦ integral_nonneg fun z ↦ ?_
    simp only [one_pow, sub_self, Real.sqrt_zero, zero_smul, one_smul, add_zero]
    exact mul_self_nonneg _

/-- Young's inequality for the noise form: for `l > 0`,
`Q(F + G) ≤ (1 + l) Q(F) + (1 + l⁻¹) Q(G)`. -/
theorem nBil_young {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {l : ℝ} (hl : 0 < l) {F G : Gs n → ℝ}
    (hF : Measurable F) (hG : Measurable G) {C : ℝ} (hFC : ∀ x, |F x| ≤ C)
    (hGC : ∀ x, |G x| ≤ C) :
    nBil t (fun x ↦ F x + G x) (fun x ↦ F x + G x) ≤
      (1 + l) * nBil t F F + (1 + l⁻¹) * nBil t G G := by
  have ht : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hmeas : Measurable fun x ↦ l * F x + -1 * G x := (hF.const_mul l).add (hG.const_mul (-1))
  have hbd : ∀ x, |l * F x + -1 * G x| ≤ |l| * C + |-1| * C :=
    abs_add_le_of_le (abs_const_mul_le_of_le hFC l) (abs_const_mul_le_of_le hGC (-1))
  have h0 := nBil_self_nonneg ht0 ht1 hmeas hbd
  rw [nBil_lin_self ht hF hG hFC hGC l (-1)] at h0
  rw [nBil_add_self ht hF hG hFC hGC]
  obtain ⟨A, hA⟩ : ∃ A, A = nBil t F F := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = nBil t F G := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = nBil t G G := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hD] at h0 ⊢
  have h1 : 0 ≤ l⁻¹ * (l ^ 2 * A + 2 * (l * -1) * B + (-1) ^ 2 * D) :=
    mul_nonneg (inv_nonneg.2 hl.le) h0
  have e : l⁻¹ * (l ^ 2 * A + 2 * (l * -1) * B + (-1) ^ 2 * D) = l * A - 2 * B + l⁻¹ * D := by
    field_simp
    ring
  rw [e] at h1
  nlinarith

/-- `Q(F) ≤ Q(|F|)`. -/
theorem nBil_self_le_abs {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F : Gs n → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ x, |F x| ≤ C) :
    nBil t F F ≤ nBil t (fun x ↦ |F x|) (fun x ↦ |F x|) := by
  have hA : Measurable fun x ↦ |F x| := measurable_abs hF
  have hAC : ∀ x, |(|F x|)| ≤ C := fun x ↦ by rw [abs_abs]; exact hFC x
  rw [← gStab_eq_nBil, ← gStab_eq_nBil, GaussL2.gStab_eq_prod ht (memLp_two_of_abs_le hF hFC),
    GaussL2.gStab_eq_prod ht (memLp_two_of_abs_le hA hAC)]
  refine integral_mono (integrable_integrand t hF hF hFC hFC)
    (integrable_integrand t hA hA hAC hAC) fun p ↦ ?_
  rw [← abs_mul]
  exact le_abs_self _

/-- `Q(F) ≤ E F²`: `T_t` is a contraction of `L²(γ)`. -/
theorem nBil_self_le_sq {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F : Gs n → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ x, |F x| ≤ C) : nBil t F F ≤ ∫ x, F x ^ 2 ∂gm n := by
  have hL2 : MemLp F 2 (gm n) := Gaussian.memLp_two_of_abs_le hF hFC
  have hL := GaussL2.measurable_rot (n := n) t
  have hmap := GaussL2.map_rot_gm (n := n) ht
  rw [← gStab_eq_nBil, GaussL2.gStab_eq_prod ht hL2]
  have h := GaussL2.abs_integral_mul_le
    (GaussL2.memLp_comp_of_map measurable_fst GaussL2.map_fst_gm hL2)
    (GaussL2.memLp_comp_of_map hL hmap hL2)
  rw [GaussL2.integral_comp_of_map (Φ := fun x ↦ F x ^ 2) measurable_fst GaussL2.map_fst_gm
      (hL2.aestronglyMeasurable.pow 2),
    GaussL2.integral_comp_of_map (Φ := fun x ↦ F x ^ 2) hL hmap (hL2.aestronglyMeasurable.pow 2),
    Real.mul_self_sqrt (integral_nonneg fun x ↦ sq_nonneg _)] at h
  exact (le_abs_self _).trans h

namespace SharpB

/-- `Γ_r(a) = o(a)` as `a → 0`: for `ε > 0` there is `τ₀ ∈ (0, 1)` with `Γ_r(a) ≤ ε a` on
`(0, τ₀]`. -/
theorem Gam_le_mul {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ ∈ Ioo (0 : ℝ) 1, ∀ a ∈ Ioc (0 : ℝ) τ₀, Gam r a ≤ ε * a := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, ∀ s ≤ s₀, Phi s ≤ ε / 2 := by
    have h : Tendsto Phi atBot (𝓝 0) := tendsto_cdf_atBot _
    exact Filter.eventually_atBot.1 (h.eventually (eventually_le_nhds (half_pos hε)))
  have hκ : 0 < kap r := kap_pos hr
  refine ⟨Phi (s₀ / kap r), ⟨Phi_pos _, Phi_lt_one _⟩, fun a ha ↦ ?_⟩
  have ha1 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, ha.2.trans_lt (Phi_lt_one _)⟩
  have hPsi : Psi a ≤ s₀ / kap r := by
    rw [← strictMono_Phi.le_iff_le, Phi_Psi ha1]
    exact ha.2
  rw [GammaCalc.Gam_eq_two_mul hr ha1]
  have hm : Measurable fun x : ℝ ↦ npdf x * Phi (kap r * x) := by fun_prop
  have hi1 : Integrable (fun x : ℝ ↦ npdf x * Phi (kap r * x)) :=
    Normal.integrable_npdf.mono' hm.aestronglyMeasurable (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Normal.npdf_nonneg x),
        abs_of_nonneg (Phi_pos _).le]
      exact mul_le_of_le_one_right (Normal.npdf_nonneg x) (Phi_lt_one _).le)
  have hi2 : Integrable (fun x : ℝ ↦ npdf x * (ε / 2)) := Normal.integrable_npdf.mul_const _
  have hle : ∫ x in Iic (Psi a), npdf x * Phi (kap r * x) ≤
      ∫ x in Iic (Psi a), npdf x * (ε / 2) := by
    refine setIntegral_mono_on hi1.integrableOn hi2.integrableOn measurableSet_Iic fun x hx ↦ ?_
    refine mul_le_mul_of_nonneg_left (hs₀ _ ?_) (Normal.npdf_nonneg x)
    calc kap r * x ≤ kap r * (s₀ / kap r) :=
          mul_le_mul_of_nonneg_left ((mem_Iic.1 hx).trans hPsi) hκ.le
      _ = s₀ := by field_simp
  rw [integral_mul_const, ← Phi_eq_integral, Phi_Psi ha1] at hle
  linarith

/-- `nBil t f f ≤ E|f|` for `|f| ≤ 1`. -/
theorem nBil_le_mean {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {f : Gs n → ℝ} (hf : Measurable f)
    (hf1 : ∀ x, |f x| ≤ 1) : nBil t f f ≤ ∫ x, |f x| ∂gm n := by
  refine (nBil_self_le_sq ht hf hf1).trans (integral_mono ?_ ?_ fun x ↦ ?_)
  · exact Gaussian.integrable_of_abs_le (hf.pow_const 2) (C := 1) fun x ↦ by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hf1 x)
  · exact Gaussian.integrable_of_abs_le (measurable_abs hf) (C := 1) fun x ↦ by
      rw [abs_abs]
      exact hf1 x
  · rw [← sq_abs]
    nlinarith [abs_nonneg (f x), hf1 x]

end SharpB

/-- **The small-mass bound** (in place of hypercontractivity): `Q(v) = o(E|v|)` as `E|v| → 0`,
uniformly in the dimension, for `|v| ≤ 1`. -/
theorem nBil_small {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ > 0, ∀ (n : ℕ) (v : Gs n → ℝ), Measurable v → (∀ x, |v x| ≤ 1) →
      ∫ x, |v x| ∂gm n ≤ τ₀ → nBil t v v ≤ ε * ∫ x, |v x| ∂gm n := by
  obtain ⟨τ₀, hτ, hG⟩ := Gam_le_mul (r := t) ⟨by linarith, ht1⟩ hε
  refine ⟨τ₀, hτ.1, fun n v hv hv1 hτv ↦ ?_⟩
  have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, ht1.le⟩
  have hm0 : 0 ≤ ∫ x, |v x| ∂gm n := integral_nonneg fun x ↦ abs_nonneg _
  rcases hm0.lt_or_eq with hm | hm
  · have hmI : gMean (fun x ↦ |v x|) ∈ Ioo (0 : ℝ) 1 := ⟨hm, hτv.trans_lt hτ.2⟩
    have hB := (gDef_nonneg ⟨ht0, ht1⟩ (fun x ↦ |v x|) (measurable_abs hv)
      (fun x ↦ ⟨abs_nonneg _, hv1 x⟩) hmI).1
    rw [gDef, gStab_eq_nBil] at hB
    have h1 := nBil_self_le_abs htI hv hv1
    have h2 := hG _ ⟨hm, hτv⟩
    unfold gMean at hB
    linarith
  · rw [← hm, mul_zero]
    have h := nBil_le_mean htI hv hv1
    linarith

end BGHKLMM26.RobustMIS
