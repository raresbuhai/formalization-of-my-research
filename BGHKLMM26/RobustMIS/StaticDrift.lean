module

public import BGHKLMM26.RobustMIS.StaticFiber
public import BGHKLMM26.RobustMIS.Rates

/-!
# The static drift bound

Proposition 4.7 of `eldan-proof.tex` (Eldan's Proposition 18(ii), with the factor `2` on the
off-diagonal block): for measurable `g : ℝⁿ → [0, 1]` with `S = E g ∈ (0, 1)`,
`|Ψ(S)² |U|² - ‖B‖²_HS| ≤ 10 λ(S)⁻³ ψ(ε(g))`.

Proof (namespace `StaticDrift`): `D = (ξ² - b₁₁²) - Ψ(S)² ε - (‖B‖²_HS - b₁₁²)` with
`ξ = -Ψ(S) q(S)`, `b₁₁ = ⟨B u, u⟩ = ∫ (s² - 1) f₁` for the marginal `f₁` along `u = U/|U|`
(`exists_marginal`, `marginal_moments`; any unit vector if `U = 0`, `exists_unit`; `n = 0` is
trivial); `0 ≤ ‖B‖²_HS - b₁₁²` (`sq_bForm_le_hs2`) and `offaxis_bound` bound the last term,
`b11_bound` the first (with `|ξ + b₁₁| ≤ 1/4 + 3/4`, as `b₁₁² ≤ ‖B‖²_HS ≤ 2λ ≤ 1/2`), and
`Ψ² ε ≤ 2 q Ψ² δ' ≤ 0.588 δ'` the second (`D_le`). If `ε = 0` then `δ' = 0` and `D = 0`.
Otherwise `ε ≤ δ' ≤ √(π/2) ε/λ`, `|Ψ| ≤ √(2 log(1/λ))`, `λ ≤ 1/4` give the bracket bound
`≤ 7.92 √(log(1/ε))/λ²` (`bracket_le`) and `√(π/2) · 7.92 ≤ 10` (`final_le`); the numerical
constants are those of the audit (§2, Prop. 4.7).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.StaticDrift

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### Numerical constants -/

theorem sqrt_two_div_pi_le : √(2 / π) ≤ 0.798 := by
  rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ pi_pos]
  nlinarith [pi_gt_d4]

theorem sqrt_pi_div_two_le : √(π / 2) ≤ 1.2534 := by
  rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [pi_lt_d4]

theorem sqrt_two_le : √2 ≤ 1.4143 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The bracket of Prop. 4.7: `7.2|Ψ| + 7.2√(2 log(1/δ')) + 10.4 + 0.588 + 6√(2/π) + 4√(π/2)/λ²
≤ 7.92 √(log(1/ε))/λ²`, using `|Ψ| ≤ √(2 log(1/λ))`, `λ ≤ 1/4`, `ε ≤ δ'`, `ε ≤ 1/(2π)`. -/
theorem bracket_le {P δ ε l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1 / 4) (hεδ : ε ≤ δ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / (2 * π)) (hP : |P| ≤ √(2 * Real.log (1 / l))) :
    7.2 * |P| + 7.2 * √(2 * Real.log (1 / δ)) + 10.4 + 0.588 + 6 * √(2 / π) +
        4 * √(π / 2) / l ^ 2 ≤ 7.92 * √(Real.log (1 / ε)) / l ^ 2 := by
  obtain ⟨W, hW⟩ : ∃ W, W = 1 / l ^ 2 := ⟨_, rfl⟩
  obtain ⟨Le, hLe⟩ : ∃ Le, Le = √(Real.log (1 / ε)) := ⟨_, rfl⟩
  have hl2 : 0 < l ^ 2 := by positivity
  have hW16 : 16 ≤ W := by
    rw [hW, le_div_iff₀ hl2]; nlinarith
  have hlW : l ^ 2 * W = 1 := by rw [hW]; field_simp
  -- `log(1/ε) ≥ 1`
  have hlogε : 1 ≤ Real.log (1 / ε) := by
    have h1 : exp 1 ≤ 1 / ε := by
      rw [le_div_iff₀ hε0]
      have := exp_one_lt_d9
      have h2 : ε * (2 * π) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hε1
      nlinarith [pi_gt_d4]
    calc (1 : ℝ) = Real.log (exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (1 / ε) := Real.log_le_log (exp_pos 1) h1
  have hLe1 : 1 ≤ Le := by rw [hLe]; exact Real.one_le_sqrt.2 hlogε
  -- `|Ψ| ≤ 0.177/λ²`
  have hPW : |P| ≤ 0.177 * W := by
    have hlog0 : 0 ≤ Real.log (1 / l) := Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
    have hP2 : P ^ 2 ≤ 2 * Real.log (1 / l) := by
      rw [← sq_abs]
      calc |P| ^ 2 ≤ (√(2 * Real.log (1 / l))) ^ 2 := pow_le_pow_left₀ (abs_nonneg P) hP 2
        _ = _ := Real.sq_sqrt (by positivity)
    have hlog : Real.log (1 / l) ≤ 1 / l := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / l); linarith
    have hP2' : P ^ 2 * l ≤ 2 := by
      have h2 : 2 * Real.log (1 / l) ≤ 2 * (1 / l) := by linarith
      have := mul_le_mul_of_nonneg_right (hP2.trans h2) hl0.le
      rwa [mul_assoc, one_div_mul_cancel hl0.ne', mul_one] at this
    have hsq : (|P| * l ^ 2) ^ 2 ≤ 1 / 32 := by
      have h3 : (|P| * l ^ 2) ^ 2 = (P ^ 2 * l) * l ^ 3 := by rw [mul_pow, sq_abs]; ring
      have h4 : l ^ 3 ≤ 1 / 64 := by
        calc l ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ hl0.le hl1 3
          _ = 1 / 64 := by norm_num
      rw [h3]
      calc P ^ 2 * l * l ^ 3 ≤ 2 * (1 / 64) :=
            mul_le_mul hP2' h4 (by positivity) (by norm_num)
        _ = 1 / 32 := by norm_num
    have h5 : |P| * l ^ 2 ≤ 0.177 := by
      by_contra h
      have h' := not_le.1 h
      nlinarith
    calc |P| = |P| * l ^ 2 * W := by rw [mul_assoc, hlW, mul_one]
      _ ≤ 0.177 * W := mul_le_mul_of_nonneg_right h5 (by linarith)
  -- `√(2 log(1/δ)) ≤ √2 √(log(1/ε))`
  have hδ0 : 0 < δ := lt_of_lt_of_le hε0 hεδ
  have hs2 : √(2 * Real.log (1 / δ)) ≤ 1.4143 * Le := by
    have h1 : Real.log (1 / δ) ≤ Real.log (1 / ε) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hε0 hεδ)
    rw [Real.sqrt_mul (by norm_num), hLe]
    exact mul_le_mul sqrt_two_le (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) (by norm_num)
  have f2 : W ≤ W * Le := by nlinarith
  have f4 : 16 * Le ≤ W * Le := mul_le_mul_of_nonneg_right hW16 (by linarith)
  have f6 := sqrt_two_div_pi_le
  have f7 : √(π / 2) * W ≤ 1.2534 * W := mul_le_mul_of_nonneg_right sqrt_pi_div_two_le (by linarith)
  have e1 : 4 * √(π / 2) / l ^ 2 = 4 * (√(π / 2) * W) := by rw [hW]; ring
  have e2 : 7.92 * √(Real.log (1 / ε)) / l ^ 2 = 7.92 * (W * Le) := by rw [hW, hLe]; ring
  rw [e1, e2]
  linarith

/-- The last step of Prop. 4.7: `δ' X ≤ 10 ψ(ε)/λ³` from `X ≤ 7.92 √(log(1/ε))/λ²` and
`δ' ≤ √(π/2) ε/λ`. -/
theorem final_le {D δ ε l X : ℝ} (hl0 : 0 < l) (hD : |D| ≤ δ * X)
    (hX : X ≤ 7.92 * √(Real.log (1 / ε)) / l ^ 2) (hδ0 : 0 ≤ δ) (hδ : δ ≤ √(π / 2) * ε / l)
    (hε0 : 0 ≤ ε) : |D| ≤ 10 * psiL ε / l ^ 3 := by
  obtain ⟨Le, hLe⟩ : ∃ Le, Le = √(Real.log (1 / ε)) := ⟨_, rfl⟩
  have hLe0 : 0 ≤ Le := by rw [hLe]; exact Real.sqrt_nonneg _
  rw [← hLe] at hX
  have hpsi : psiL ε = ε * Le := by rw [psiL, hLe]
  have h1 : δ * X ≤ δ * (7.92 * Le / l ^ 2) := mul_le_mul_of_nonneg_left hX hδ0
  have h2 : δ * (7.92 * Le / l ^ 2) ≤ √(π / 2) * ε / l * (7.92 * Le / l ^ 2) :=
    mul_le_mul_of_nonneg_right hδ (by positivity)
  have h3 : √(π / 2) * ε / l * (7.92 * Le / l ^ 2) = (7.92 * √(π / 2)) * (ε * Le) / l ^ 3 := by
    field_simp
  have h4 : (7.92 * √(π / 2)) * (ε * Le) / l ^ 3 ≤ 10 * (ε * Le) / l ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by nlinarith [sqrt_pi_div_two_le]) (by positivity)
  rw [hpsi]
  linarith

/-- The assembly of Prop. 4.7: `D = (ξ² - b₁₁²) - Ψ² ε - (‖B‖² - b₁₁²)` with `ξ = -Ψ q`. -/
theorem D_le {P q Un ε δ b H Y K : ℝ} (hε : ε = q ^ 2 - Un ^ 2) (hδ : δ = q - Un)
    (hUn : 0 ≤ Un) (hUq : Un ≤ q) (hb : b ^ 2 ≤ 1 / 2) (hξ : q * |P| ≤ 1 / 4)
    (hqP2 : q * P ^ 2 ≤ 0.294) (hb11 : |-P * q - b| ≤ δ * Y) (hHb : b ^ 2 ≤ H)
    (hoff : H - b ^ 2 ≤ K * δ) :
    |P ^ 2 * Un ^ 2 - H| ≤ δ * (Y + 0.588 + K) := by
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hb34 : |b| ≤ 3 / 4 := by
    rw [← sq_le_sq₀ (abs_nonneg b) (by norm_num), sq_abs]; linarith
  have hξb : |-P * q + b| ≤ 1 := by
    have : |-P * q| ≤ 1 / 4 := by
      rw [abs_mul, abs_neg, mul_comm, abs_of_nonneg (hUn.trans hUq)]; exact hξ
    calc |-P * q + b| ≤ |-P * q| + |b| := abs_add_le _ _
      _ ≤ 1 := by linarith
  have e2 : |(-P * q) ^ 2 - b ^ 2| ≤ δ * Y := by
    rw [show (-P * q) ^ 2 - b ^ 2 = (-P * q - b) * (-P * q + b) by ring, abs_mul]
    calc |-P * q - b| * |-P * q + b| ≤ |-P * q - b| * 1 :=
          mul_le_mul_of_nonneg_left hξb (abs_nonneg _)
      _ ≤ δ * Y := by rw [mul_one]; exact hb11
  have e3 : P ^ 2 * ε ≤ 0.588 * δ := by
    have : P ^ 2 * ε = (P ^ 2 * δ) * (q + Un) := by rw [hε, hδ]; ring
    rw [this]
    calc P ^ 2 * δ * (q + Un) ≤ P ^ 2 * δ * (2 * q) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * (q * P ^ 2) * δ := by ring
      _ ≤ 2 * 0.294 * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
      _ = 0.588 * δ := by norm_num
  have e3' : 0 ≤ P ^ 2 * ε := by
    rw [hε]; exact mul_nonneg (sq_nonneg _) (by nlinarith)
  have e1 : P ^ 2 * Un ^ 2 - H = ((-P * q) ^ 2 - b ^ 2) - P ^ 2 * ε - (H - b ^ 2) := by
    rw [hε]; ring
  rw [e1]
  have e2' := abs_le.1 e2
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The marginal along `u` -/

open StaticFiber in
/-- The three moments of the marginal `f₁` along a unit vector `u` with `U = |U| u`:
`∫ f₁ = S`, `∫ s f₁ = |U|`, `∫ (s² - 1) f₁ = ⟨B u, u⟩`. -/
theorem marginal_moments (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {u : Gs n} (hu : ‖u‖ = 1) (hU : hermite1 g = ‖hermite1 g‖ • u) :
    ∃ f₁ : ℝ → ℝ, Measurable f₁ ∧ (∀ s, 0 ≤ f₁ s ∧ f₁ s ≤ 1) ∧
      ∫ s, f₁ s ∂gaussianReal 0 1 = gMean g ∧
      ∫ s, s * f₁ s ∂gaussianReal 0 1 = ‖hermite1 g‖ ∧
      ∫ s, (s ^ 2 - 1) * f₁ s ∂gaussianReal 0 1 = bForm g u u := by
  obtain ⟨f₁, hm, h01', hf⟩ := exists_marginal g hg h01 u hu
  refine ⟨f₁, hm, h01', ?_, ?_, ?_⟩
  · have := hf (fun _ ↦ 1) measurable_const ⟨1, fun s ↦ by
      rw [abs_one, one_mul]; nlinarith [sq_nonneg s]⟩
    simp only [one_mul] at this
    rw [← this]; rfl
  · have := hf id measurable_id ⟨1, fun s ↦ by
      rw [one_mul, id]; nlinarith [sq_nonneg (|s| - 1 / 2), sq_abs s]⟩
    simp only [id] at this
    rw [← this, ← inner_integral_smul hg (fun x ↦ abs_le_one_of (h01 x)) u]
    change ⟪u, hermite1 g⟫ = _
    conv_lhs => rw [hU]
    rw [inner_smul_right, inner_self_of_norm hu, mul_one]
  · have := hf (fun s ↦ s ^ 2 - 1) (by fun_prop) ⟨1, fun s ↦ by
      rw [one_mul, abs_le]; constructor <;> nlinarith [sq_nonneg s]⟩
    rw [← this]
    unfold bForm
    congr 1
    funext x
    rw [inner_self_of_norm hu, sq]

theorem exists_unit (g : Gs n → ℝ) (hn : 0 < n) :
    ∃ u : Gs n, ‖u‖ = 1 ∧ hermite1 g = ‖hermite1 g‖ • u := by
  by_cases hU : hermite1 g = 0
  · refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp, ?_⟩
    rw [hU, norm_zero, zero_smul]
  · refine ⟨‖hermite1 g‖⁻¹ • hermite1 g, norm_smul_inv_norm hU, ?_⟩
    rw [smul_inv_smul₀ (norm_ne_zero_iff.2 hU)]

theorem sq_bForm_le_hs2 (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {u : Gs n} (hu : ‖u‖ = 1) : bForm g u u ^ 2 ≤ hs2 g := by
  obtain ⟨b, i₀, hb⟩ := StaticFiber.exists_basis_of_unit hu
  rw [hs2_eq_orthonormalBasis g hg h01 b]
  calc bForm g u u ^ 2 = bForm g (b i₀) (b i₀) ^ 2 := by rw [hb]
    _ ≤ ∑ j, bForm g (b i₀) (b j) ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ bForm g (b i₀) (b j) ^ 2) (fun _ _ ↦ sq_nonneg _)
          (Finset.mem_univ i₀)
    _ ≤ ∑ i, ∑ j, bForm g (b i) (b j) ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ ∑ j, bForm g (b i) (b j) ^ 2)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i₀)

/-- **Drift bound**, the proof (Proposition 4.7). -/
theorem drift (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) :
    |driftD g| ≤ 10 * psiL (epsF g) / lam (gMean g) ^ 3 := by
  have hl0 : 0 < lam (gMean g) := by unfold lam; nlinarith [hS.1, hS.2]
  have hl1 : lam (gMean g) ≤ 1 / 4 := by unfold lam; nlinarith [sq_nonneg (gMean g - 1 / 2)]
  have hq0 : 0 < qf (gMean g) := qf_pos hS
  have hqlam := qf_ge_lam (Ioo_subset_Icc_self hS)
  have hUq := norm_hermite1_le g hg h01
  have hUn0 : 0 ≤ ‖hermite1 g‖ := norm_nonneg _
  have hε0 := epsF_nonneg g hg h01
  have hε1 := (epsF_le g h01).2
  have hε : epsF g = qf (gMean g) ^ 2 - ‖hermite1 g‖ ^ 2 := rfl
  have hεI : epsF g ∈ Icc (0 : ℝ) 1 :=
    ⟨hε0, hε1.trans (by rw [div_le_one (by positivity)]; nlinarith [pi_gt_three])⟩
  have hRHS0 : 0 ≤ 10 * psiL (epsF g) / lam (gMean g) ^ 3 :=
    div_nonneg (mul_nonneg (by norm_num) (psiL_nonneg hεI)) (by positivity)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hU0 : hermite1 g = 0 := Subsingleton.elim _ _
    have hH0 : hs2 g = 0 := by simp [hs2]
    have : driftD g = 0 := by simp [driftD, hU0, hH0]
    rw [this, abs_zero]
    exact hRHS0
  obtain ⟨u, hu, hU⟩ := exists_unit g hn
  obtain ⟨f₁, hf₁m, hf₁01, hS1, hU1, hb1⟩ := marginal_moments g hg h01 hu hU
  obtain ⟨hb0, hbpos⟩ := b11_bound f₁ hf₁m hf₁01 hS1 hS (δ' := qf (gMean g) - ‖hermite1 g‖)
    (by rw [hU1])
  rw [hb1] at hb0 hbpos
  have hoff := offaxis_bound g hg h01 hS u hu hU
  have hHb := sq_bForm_le_hs2 g hg h01 hu
  have hH2 := hs2_le g hg h01
  have hξ := qf_mul_abs_Psi_le (gMean g)
  have hqP2 := qf_mul_Psi_sq_le (gMean g)
  have hδ0 : 0 ≤ qf (gMean g) - ‖hermite1 g‖ := by linarith
  have hεδ : epsF g = (qf (gMean g) - ‖hermite1 g‖) * (qf (gMean g) + ‖hermite1 g‖) := by
    rw [hε]; ring
  rcases eq_or_lt_of_le hε0 with hεz | hεpos
  · -- `ε = 0`: then `δ' = 0` and `D = 0`.
    have hδz : qf (gMean g) - ‖hermite1 g‖ = 0 := by
      rcases eq_or_lt_of_le hδ0 with h | h
      · exact h.symm
      · exfalso
        have : 0 < (qf (gMean g) - ‖hermite1 g‖) * (qf (gMean g) + ‖hermite1 g‖) :=
          mul_pos h (by linarith)
        linarith
    have hb := hb0 hδz
    rw [hδz, mul_zero] at hoff
    have hD : driftD g = 0 := by
      have hUn : ‖hermite1 g‖ = qf (gMean g) := by linarith
      have hH : hs2 g = bForm g u u ^ 2 := le_antisymm (by linarith) hHb
      rw [driftD, hH, hb, hUn]
      ring
    rw [hD, abs_zero]
    exact hRHS0
  · -- `ε > 0`
    have hδpos : 0 < qf (gMean g) - ‖hermite1 g‖ := by
      by_contra h
      have h' : qf (gMean g) - ‖hermite1 g‖ = 0 := le_antisymm (not_lt.1 h) hδ0
      rw [h', zero_mul] at hεδ
      linarith
    have hb := hbpos hδpos
    have hbb : bForm g u u ^ 2 ≤ 1 / 2 := by linarith
    have hD := D_le (P := Psi (gMean g)) hε rfl hUn0 hUq hbb hξ hqP2 hb hHb hoff
    have h2q := StaticFiber.two_mul_qf_le (gMean g)
    have hc' := sqrt_two_div_pi_le
    have hεle : epsF g ≤ qf (gMean g) - ‖hermite1 g‖ := by
      rw [hεδ]
      calc (qf (gMean g) - ‖hermite1 g‖) * (qf (gMean g) + ‖hermite1 g‖) ≤
            (qf (gMean g) - ‖hermite1 g‖) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hδ0
        _ = _ := mul_one _
    have hX := bracket_le (P := Psi (gMean g)) hl0 hl1 hεle hεpos hε1 (abs_Psi_le_lam hS)
    have hδc : qf (gMean g) - ‖hermite1 g‖ ≤ √(π / 2) * epsF g / lam (gMean g) := by
      rw [le_div_iff₀ hl0]
      have h1 : (qf (gMean g) - ‖hermite1 g‖) * (√(2 / π) * lam (gMean g)) ≤ epsF g := by
        rw [hεδ]
        exact mul_le_mul_of_nonneg_left (by linarith) hδ0
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (π / 2))
      have e : √(π / 2) * ((qf (gMean g) - ‖hermite1 g‖) * (√(2 / π) * lam (gMean g))) =
          (√(2 / π) * √(π / 2)) * ((qf (gMean g) - ‖hermite1 g‖) * lam (gMean g)) := by ring
      rw [e, StaticFiber.sqrt_two_div_pi_mul, one_mul] at h2
      exact h2
    refine final_le hl0 hD ?_ hδ0 hδc hε0
    linarith

end BGHKLMM26.RobustMIS.StaticDrift

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set

variable {n : ℕ}

/-- **Drift bound** (Proposition 4.7). -/
theorem drift_bound (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hS : gMean g ∈ Ioo (0 : ℝ) 1) :
    |driftD g| ≤ 10 * psiL (epsF g) / lam (gMean g) ^ 3 :=
  StaticDrift.drift g hg h01 hS

end BGHKLMM26.RobustMIS
