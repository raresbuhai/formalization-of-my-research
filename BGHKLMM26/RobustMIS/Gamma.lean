module

public import BGHKLMM26.RobustMIS.Quantile

/-!
# The quadrant function `Γ_r`: elementary facts

`Γ_r(a) = P(G ≤ Φ⁻¹(a), H ≤ Φ⁻¹(a))` for a standard bivariate Gaussian pair with correlation `r`.
Facts used in §7 of the paper (Lemma `gaussian-facts` (c)): boundary values, `Γ_0(a) = a²`,
`Γ_r(a) ≤ a`, the Lipschitz bound `|Γ_r(a) - Γ_r(b)| ≤ 2|a - b|` (the marginals `Φ(G)`, `Φ(H)` are
uniform: `Gaussian.measureReal_Phi_lt`), Sheppard's formula `Γ_r(1/2) = 1/4 + arcsin r/(2π)`
(`Gaussian.corrPair_quadrant`), and facts on `κ_r` and the path `r(s) = (t-s)/(1-s)`.
The calculus of `Γ` (Lemma 3.3 of `eldan-proof.tex`) is in `GammaCalc.lean`.

All statements are proved. Auxiliary facts (namespace `BGHKLMM26.RobustMIS.Gamma`): the
bivariate Gaussian `corrPair r` is exchangeable for `r ∈ [-1, 1]` (`corrPair_map_swap`, by
characteristic functions: `Measure.ext_of_charFunDual`), so both marginals are standard
(`corrPair_map_fst`, `corrPair_map_snd`); `P(Φ(G) ≤ c) = clamp01 c` (`measureReal_Phi_le`), which
gives `Γ_r ≤ clamp01` and the Lipschitz bound.

Material: `Gaussian.corrPair`, `Gaussian.corrPair_quadrant` (`Background/Gaussian.lean`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Gamma

open MeasureTheory ProbabilityTheory Real Set
open Gaussian

/-! ### The bivariate Gaussian: exchangeability and marginals -/

/-- The linear map `(x, z) ↦ (x, r x + s z)`. -/
noncomputable def pairCLM (r s : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (r • ContinuousLinearMap.fst ℝ ℝ ℝ + s • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem coe_pairCLM (r s : ℝ) : ⇑(pairCLM r s) = fun p ↦ (p.1, r * p.1 + s * p.2) := by
  funext p
  simp [pairCLM]

theorem corrPair_eq_map (r : ℝ) :
    corrPair r = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (pairCLM r √(1 - r ^ 2)) := by
  rw [coe_pairCLM]
  rfl

theorem strongDual_prod_apply (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem charFunDual_gaussianReal (ℓ : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) ℓ = Complex.exp (-((ℓ 1 : ℝ) : ℂ) ^ 2 / 2) := by
  have h : ∀ x : ℝ, ℓ x = ℓ 1 * x := by
    intro x
    rw [mul_comm, ← smul_eq_mul, ← ℓ.map_smul, smul_eq_mul, mul_one]
  rw [charFunDual_apply]
  have e : (fun x : ℝ ↦ Complex.exp ((ℓ x : ℂ) * Complex.I)) =
      fun x : ℝ ↦ Complex.exp ((ℓ 1 : ℂ) * (x : ℂ) * Complex.I) := by
    funext x
    rw [h x]
    push_cast
    ring_nf
  rw [e, ← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  ring

theorem charFunDual_pair (r s : ℝ) (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (pairCLM r s)) L =
      Complex.exp
        (-(((L (1, 0) + r * L (0, 1) : ℝ) : ℂ) ^ 2 + ((s * L (0, 1) : ℝ) : ℂ) ^ 2) / 2) := by
  rw [charFunDual_map, charFunDual_prod, charFunDual_gaussianReal, charFunDual_gaussianReal,
    ← Complex.exp_add]
  congr 1
  have h1 : ((L.comp (pairCLM r s)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1 =
      L (1, 0) + r * L (0, 1) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, coe_pairCLM]
    rw [strongDual_prod_apply]
    ring
  have h2 : ((L.comp (pairCLM r s)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 = s * L (0, 1) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, coe_pairCLM]
    rw [strongDual_prod_apply]
    ring
  rw [h1, h2]
  ring

/-- **Exchangeability**: the bivariate Gaussian with correlation `r ∈ [-1, 1]` is invariant under
swapping the coordinates. -/
theorem corrPair_map_swap {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (corrPair r).map Prod.swap = corrPair r := by
  have hσ : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith [hr.1, hr.2])
  apply Measure.ext_of_charFunDual
  funext L
  have hs : (Prod.swap : ℝ × ℝ → ℝ × ℝ) =
      ⇑(ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap := rfl
  rw [hs, corrPair_eq_map, charFunDual_map, charFunDual_pair, charFunDual_pair]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]
  rw [strongDual_prod_apply L 0 1, strongDual_prod_apply L 1 0]
  have hσc : ((√(1 - r ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (r : ℂ) ^ 2 := by exact_mod_cast hσ
  push_cast
  linear_combination (-((((L (1, 0) : ℝ) : ℂ)) ^ 2 - ((L (0, 1) : ℝ) : ℂ) ^ 2) / 2) * hσc

theorem corrPair_map_fst (r : ℝ) : (corrPair r).map Prod.fst = gaussianReal 0 1 := by
  rw [corrPair, Measure.map_map measurable_fst (measurable_corrPairMap r)]
  have : (Prod.fst ∘ fun p : ℝ × ℝ ↦ (p.1, r * p.1 + √(1 - r ^ 2) * p.2)) = Prod.fst := rfl
  rw [this, Measure.map_fst_prod]
  simp

theorem corrPair_map_snd {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (corrPair r).map Prod.snd = gaussianReal 0 1 := by
  rw [← corrPair_map_swap hr, Measure.map_map measurable_snd measurable_swap]
  exact corrPair_map_fst r

theorem corrPair_real_fst (r : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (corrPair r).real {p | p.1 ∈ S} = (gaussianReal 0 1).real S := by
  rw [← corrPair_map_fst r, map_measureReal_apply measurable_fst hS]
  rfl

theorem corrPair_real_snd {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {S : Set ℝ} (hS : MeasurableSet S) :
    (corrPair r).real {p | p.2 ∈ S} = (gaussianReal 0 1).real S := by
  rw [← corrPair_map_snd hr, map_measureReal_apply measurable_snd hS]
  rfl

/-- `P(Φ(G) ≤ c) = clamp01 c`. -/
theorem measureReal_Phi_le (c : ℝ) : (gaussianReal 0 1).real {x | Phi x ≤ c} = clamp01 c := by
  by_cases h0 : c ≤ 0
  · have : {x | Phi x ≤ c} = (∅ : Set ℝ) := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [Phi_pos x]
    rw [this, clamp01]
    simp [max_eq_left (min_le_of_right_le h0)]
  by_cases h1 : 1 ≤ c
  · have : {x | Phi x ≤ c} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      linarith [Phi_lt_one x]
    rw [this, clamp01, min_eq_left h1]
    simp
  push Not at h0 h1
  have hc : c ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have : {x | Phi x ≤ c} = Iic (Psi c) := by
    ext x
    rw [mem_ofPred_eq, mem_Iic, Psi_le_iff hc]
  rw [this, ← cdf_eq_real, clamp01, min_eq_right h1.le, max_eq_right h0.le]
  exact Phi_Psi hc

theorem measurableSet_Phi_le (c : ℝ) : MeasurableSet {x : ℝ | Phi x ≤ c} :=
  measurableSet_le measurable_Phi measurable_const

theorem clamp01_le_self {a : ℝ} (ha : 0 ≤ a) : clamp01 a ≤ a := by
  unfold clamp01
  exact max_le ha (min_le_right _ _)

theorem clamp01_sub_le {a b : ℝ} (hab : a ≤ b) : clamp01 b - clamp01 a ≤ b - a := by
  unfold clamp01
  rcases le_total b 0 with hb | hb <;> rcases le_total a 0 with ha | ha <;>
    rcases le_total 1 b with hb1 | hb1 <;> rcases le_total 1 a with ha1 | ha1 <;>
    simp [*] <;> linarith

theorem clamp01_mono {a b : ℝ} (hab : a ≤ b) : clamp01 a ≤ clamp01 b := by
  unfold clamp01
  exact max_le_max le_rfl (min_le_min le_rfl hab)

theorem corrPair_zero : corrPair 0 = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [corrPair]
  have : (fun p : ℝ × ℝ ↦ (p.1, 0 * p.1 + √(1 - (0 : ℝ) ^ 2) * p.2)) = id := by
    funext p
    simp
  rw [this, Measure.map_id]

theorem measurableSet_Gam (c : ℝ) : MeasurableSet {p : ℝ × ℝ | Phi p.1 ≤ c ∧ Phi p.2 ≤ c} :=
  ((measurableSet_Phi_le c).preimage measurable_fst).inter
    ((measurableSet_Phi_le c).preimage measurable_snd)

theorem Gam_le_clamp (r a : ℝ) : Gam r a ≤ clamp01 a := by
  calc Gam r a ≤ (corrPair r).real {p | p.1 ∈ {x | Phi x ≤ a}} :=
        measureReal_mono (fun p hp ↦ hp.1)
    _ = clamp01 a := by rw [corrPair_real_fst r (measurableSet_Phi_le a), measureReal_Phi_le]

theorem Gam_mono (r : ℝ) {a b : ℝ} (hab : a ≤ b) : Gam r a ≤ Gam r b :=
  measureReal_mono (fun p hp ↦ ⟨hp.1.trans hab, hp.2.trans hab⟩)

theorem Gam_sub_le {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {a b : ℝ} (hab : a ≤ b) :
    Gam r b - Gam r a ≤ 2 * (b - a) := by
  have hsub : {p : ℝ × ℝ | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} ⊆ {p | Phi p.1 ≤ b ∧ Phi p.2 ≤ b} :=
    fun p hp ↦ ⟨hp.1.trans hab, hp.2.trans hab⟩
  have hD : MeasurableSet ({x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}) :=
    (measurableSet_Phi_le b).diff (measurableSet_Phi_le a)
  have hDm : (gaussianReal 0 1).real ({x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}) =
      clamp01 b - clamp01 a := by
    rw [measureReal_sdiff (fun x hx ↦ (hx : Phi x ≤ a).trans hab) (measurableSet_Phi_le a),
      measureReal_Phi_le, measureReal_Phi_le]
  have hcover : {p : ℝ × ℝ | Phi p.1 ≤ b ∧ Phi p.2 ≤ b} \ {p | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} ⊆
      {p | p.1 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}} ∪
        {p | p.2 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}} := by
    rintro p ⟨⟨h1, h2⟩, hn⟩
    by_cases h : Phi p.1 ≤ a
    · right
      exact ⟨h2, fun h' ↦ hn ⟨h, h'⟩⟩
    · left
      exact ⟨h1, h⟩
  calc Gam r b - Gam r a = (corrPair r).real
        ({p : ℝ × ℝ | Phi p.1 ≤ b ∧ Phi p.2 ≤ b} \ {p | Phi p.1 ≤ a ∧ Phi p.2 ≤ a}) :=
        (measureReal_sdiff hsub (measurableSet_Gam a)).symm
    _ ≤ (corrPair r).real ({p | p.1 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}} ∪
        {p | p.2 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}}) := measureReal_mono hcover
    _ ≤ (corrPair r).real {p | p.1 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}} +
        (corrPair r).real {p | p.2 ∈ {x : ℝ | Phi x ≤ b} \ {x | Phi x ≤ a}} :=
        measureReal_union_le _ _
    _ = 2 * (clamp01 b - clamp01 a) := by
        rw [corrPair_real_fst r hD, corrPair_real_snd hr hD, hDm]
        ring
    _ ≤ 2 * (b - a) := by linarith [clamp01_sub_le hab]

end BGHKLMM26.RobustMIS.Gamma

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open Gaussian

/-! ### Elementary facts -/

theorem Gam_nonneg (r a : ℝ) : 0 ≤ Gam r a := measureReal_nonneg

theorem Gam_of_nonpos (r : ℝ) {a : ℝ} (ha : a ≤ 0) : Gam r a = 0 := by
  have e : {p : ℝ × ℝ | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} = ∅ := by
    ext p
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro h
    linarith [Phi_pos p.1]
  rw [Gam, e]
  simp

theorem Gam_of_one_le {r : ℝ} {a : ℝ} (ha : 1 ≤ a) : Gam r a = 1 := by
  have e : {p : ℝ × ℝ | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} = univ := by
    ext p
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨(Phi_lt_one _).le.trans ha, (Phi_lt_one _).le.trans ha⟩
  rw [Gam, e]
  simp

/-- `Γ_0(a) = a²`. -/
theorem Gam_zero_corr {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : Gam 0 a = a ^ 2 := by
  have e : {p : ℝ × ℝ | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} = {x | Phi x ≤ a} ×ˢ {x | Phi x ≤ a} := rfl
  rw [Gam, Gamma.corrPair_zero, e, measureReal_prod_prod, Gamma.measureReal_Phi_le, clamp01,
    min_eq_right ha.2, max_eq_right ha.1]
  ring

/-- `Γ_r(a) ≤ P(G ≤ Φ⁻¹(a)) = a`. -/
theorem Gam_le_self {r : ℝ} (_hr : r ∈ Icc (-1 : ℝ) 1) {a : ℝ} (ha : 0 ≤ a) : Gam r a ≤ a :=
  (Gamma.Gam_le_clamp r a).trans (Gamma.clamp01_le_self ha)

/-- `Γ_r` is `2`-Lipschitz (the marginals `Φ(G)`, `Φ(H)` are uniform on `(0,1)`). -/
theorem abs_Gam_sub_le {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (a b : ℝ) :
    |Gam r a - Gam r b| ≤ 2 * |a - b| := by
  rcases le_total a b with hab | hab
  · rw [abs_sub_comm (Gam r a), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.2 (Gamma.Gam_mono r hab)), abs_of_nonneg (sub_nonneg.2 hab)]
    exact Gamma.Gam_sub_le hr hab
  · rw [abs_of_nonneg (sub_nonneg.2 (Gamma.Gam_mono r hab)), abs_of_nonneg (sub_nonneg.2 hab)]
    exact Gamma.Gam_sub_le hr hab

/-- **Sheppard's formula**: `Γ_r(1/2) = 1/4 + arcsin r / (2π)`. -/
theorem Gam_half {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    Gam r (1 / 2) = 1 / 4 + Real.arcsin r / (2 * π) := by
  have h : ∀ x : ℝ, Phi x ≤ 1 / 2 ↔ x ≤ 0 := by
    intro x
    rw [← Phi_zero]
    exact strictMono_Phi.le_iff_le
  have e : {p : ℝ × ℝ | Phi p.1 ≤ 1 / 2 ∧ Phi p.2 ≤ 1 / 2} = {q | q.1 ≤ 0 ∧ q.2 ≤ 0} := by
    ext p
    simp only [mem_ofPred_eq]
    rw [h, h]
  rw [Gam, e, corrPair_quadrant hr.1 hr.2]

/-- `r ↦ κ_r` is antitone on `(-1, 1)`; `κ_r ∈ (0, 1]` for `r ∈ [0, 1)`. -/
theorem antitoneOn_kap : AntitoneOn kap (Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  unfold kap
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by linarith [hy.1]) (by linarith [hx.1])]
  nlinarith

theorem kap_pos {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) : 0 < kap r :=
  Real.sqrt_pos.2 (div_pos (by linarith [hr.2]) (by linarith [hr.1]))

theorem kap_le_one {r : ℝ} (hr : 0 ≤ r) : kap r ≤ 1 := by
  unfold kap
  apply Real.sqrt_le_one.2
  rw [div_le_one (by linarith)]
  linarith

/-- The path `r(s) = (t - s)/(1 - s)` stays in `[0, t]` for `s ∈ [0, t]`. -/
theorem Gam_path_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) :
    (t - s) / (1 - s) ∈ Icc 0 t := by
  have h1 : 0 < 1 - s := by linarith [hs.2, ht.2]
  refine ⟨div_nonneg (by linarith [hs.2]) h1.le, ?_⟩
  rw [div_le_iff₀ h1]
  nlinarith [hs.1, ht.1, ht.2]

end BGHKLMM26.RobustMIS
