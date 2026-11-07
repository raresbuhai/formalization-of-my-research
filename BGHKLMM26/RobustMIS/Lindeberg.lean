module

public import BGHKLMM26.RobustMIS.Bonami

/-!
# The Lindeberg replacement for pairs of low-degree polynomials

The invariance principle of Mossel–O'Donnell–Oleszkiewicz [MOO10] (O'Donnell, Thm 11.66, in the
quantitative `C³` form) for a *pair* `(p, q)` of multilinear polynomials of degree `≤ d` and a
test function `Φ : ℝ² → ℝ` that is Lipschitz and `C³` along lines with
`|∂³_x Φ(a + x a', b + x b')| ≤ B (|a'| + |b'|)³`:
`|E Φ(p(X), q(X)) - E Φ(p(G), q(G))| ≤ 10 B 9^d ∑ᵢ (Infᵢ(p)^{3/2} + Infᵢ(q)^{3/2})`, `X` uniform on
`{±1}^R`, `G` standard Gaussian (`lindeberg`).

Proof: hybrids `H_k = (G₁, …, G_k, X_{k+1}, …, X_R)` (`Measure.pi` of `gaussianReal 0 1` and
`signLaw`); the endpoints are the cube average (`Lindeberg.expect_eq_integral_sign`, via the
uniform law on `Bool`) and `gm R` (`Lindeberg.integral_gm_eq_pi`, `map_pi_eq_stdGaussian`).
Replacing coordinate `i` (`Lindeberg.replace_one`): split `Measure.pi` at `i`
(`measurePreserving_piFinSuccAbove`, `Lindeberg.integral_pi_split`); `p = A + xᵢ ∂ᵢp`,
`q = A' + xᵢ ∂ᵢq` with `A, ∂ᵢp, A', ∂ᵢq` independent of `xᵢ` (`Lindeberg.mlEval_update`);
Taylor of `x ↦ Φ(A + x ∂ᵢp, A' + x ∂ᵢq)` to order 2 with remainder
`≤ (B/6)(|∂ᵢp| + |∂ᵢq|)³ |x|³` (`Lindeberg.taylor3`); the first two moments of `Xᵢ` and `Gᵢ`
agree and `E|Xᵢ|³, E|Gᵢ|³ ≤ 5` (`Lindeberg.one_coord`: error `≤ (5/3) B (|∂ᵢp| + |∂ᵢq|)³`);
then `(u + v)³ ≤ 4(u³ + v³)` and `E|∂ᵢp|³ ≤ 3^d Infᵢ(p)^{3/2}` (`Lindeberg.moment3_le`, from
`bonami` for the hybrid law, `E (∂ᵢp)² = Infᵢ(p)` and `|y|³ ≤ (λ y² + y⁴/λ)/2`). Each step costs
`(20/3) B 3^d (Infᵢ(p)^{3/2} + Infᵢ(q)^{3/2})`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Lindeberg

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

/-- The part of `c` not containing `i`. -/
noncomputable def restC (c : Cube (Fin R) → ℝ) (i : Fin R) : Cube (Fin R) → ℝ :=
  fun s => if s i then 0 else c s

/-- The derivative `∂ᵢ`: `S ↦ c_{S ∪ {i}}` for `i ∉ S`. -/
noncomputable def derC (c : Cube (Fin R) → ℝ) (i : Fin R) : Cube (Fin R) → ℝ :=
  fun s => if s i then 0 else c (Function.update s i true)

lemma prod_update_of_false (s : Cube (Fin R)) {i : Fin R} (hs : s i = false) (x : Fin R → ℝ)
    (t : ℝ) :
    (∏ j, if s j then Function.update x i t j else 1) = ∏ j, if s j then x j else 1 := by
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp [hs]
  · simp [Function.update_of_ne hj]

lemma prod_update_of_true (s : Cube (Fin R)) {i : Fin R} (hs : s i = true) (x : Fin R → ℝ)
    (t : ℝ) :
    (∏ j, if s j then Function.update x i t j else 1) =
      t * ∏ j, if Function.update s i false j then x j else 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => if Function.update s i false j then x j else 1)
      (Finset.mem_univ i)]
  simp only [hs, Function.update_self, ite_true, Bool.false_eq_true, ite_false, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j ≠ i := Finset.ne_of_mem_erase hj
  simp [Function.update_of_ne hj']

lemma update_update_self {i : Fin R} {s : Cube (Fin R)} {b : Bool} (hs : s i = b) (b' : Bool) :
    Function.update (Function.update s i b') i b = s := by
  rw [Function.update_idem, ← hs, Function.update_eq_self]

lemma sum_true_eq (i : Fin R) (f : Cube (Fin R) → ℝ) :
    ∑ s ∈ univ.filter (fun s : Cube (Fin R) => s i = true), f s =
      ∑ s ∈ univ.filter (fun s : Cube (Fin R) => ¬ s i = true), f (Function.update s i true) := by
  refine Finset.sum_nbij' (fun s => Function.update s i false) (fun s => Function.update s i true)
    ?_ ?_ ?_ ?_ ?_
  · intro s _; simp
  · intro s _; simp
  · intro s hs
    exact update_update_self (by simpa using hs) _
  · intro s hs
    exact update_update_self (by simpa using hs) _
  · intro s hs
    rw [update_update_self (by simpa using hs) _]

lemma mlEval_update (c : Cube (Fin R) → ℝ) (i : Fin R) (x : Fin R → ℝ) (t : ℝ) :
    mlEval c (Function.update x i t) = mlEval (restC c i) x + t * mlEval (derC c i) x := by
  unfold mlEval restC derC
  rw [Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Cube (Fin R) => s i = true),
    add_comm]
  congr 1
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s i = true
    · simp [hs]
    · have hs' : s i = false := by simpa using hs
      simp [hs', prod_update_of_false s hs']
  · rw [sum_true_eq i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s i = true
    · simp [hs]
    · have hs' : s i = false := by simpa using hs
      rw [prod_update_of_true _ (by simp), update_update_self hs' _]
      simp [hs']
      ring

lemma sdeg_update_true (s : Cube (Fin R)) {i : Fin R} (hs : s i = false) :
    sdeg (Function.update s i true) = sdeg s + 1 := by
  unfold sdeg OAI.OptimalMaxCut.Analytic.degree
  have : Finset.univ.filter (fun j => Function.update s i true j = true) =
      insert i (Finset.univ.filter fun j => s j = true) := by
    ext j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [this, Finset.card_insert_of_notMem (by simp [hs])]

lemma derC_deg {d : ℕ} {c : Cube (Fin R) → ℝ} (hc : ∀ s, d < sdeg s → c s = 0) (i : Fin R) :
    ∀ s, d < sdeg s → derC c i s = 0 := by
  intro s hs
  unfold derC
  by_cases h : s i = true
  · simp [h]
  · simp only [h]
    exact hc _ (by rw [sdeg_update_true s (by simpa using h)]; omega)

lemma sum_derC_sq (c : Cube (Fin R) → ℝ) (i : Fin R) : ∑ s, derC c i s ^ 2 = inflC c i := by
  unfold inflC derC
  rw [sum_true_eq i, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s i = true <;> simp [hs]

lemma restC_restC (c : Cube (Fin R) → ℝ) (i : Fin R) : restC (restC c i) i = restC c i := by
  funext s; unfold restC; by_cases hs : s i = true <;> simp [hs]

lemma derC_restC (c : Cube (Fin R) → ℝ) (i : Fin R) : derC (restC c i) i = 0 := by
  funext s; unfold restC derC; by_cases hs : s i = true <;> simp [hs]

lemma restC_derC (c : Cube (Fin R) → ℝ) (i : Fin R) : restC (derC c i) i = derC c i := by
  funext s; unfold restC derC; by_cases hs : s i = true <;> simp [hs]

lemma derC_derC (c : Cube (Fin R) → ℝ) (i : Fin R) : derC (derC c i) i = 0 := by
  funext s; unfold derC; by_cases hs : s i = true <;> simp [hs]

lemma mlEval_zero (x : Fin R → ℝ) : mlEval (0 : Cube (Fin R) → ℝ) x = 0 := by
  simp [mlEval]

/-- `mlEval (restC c i)` and `mlEval (derC c i)` do not depend on `xᵢ`. -/
lemma mlEval_restC_update (c : Cube (Fin R) → ℝ) (i : Fin R) (x : Fin R → ℝ) (t : ℝ) :
    mlEval (restC c i) (Function.update x i t) = mlEval (restC c i) x := by
  rw [mlEval_update, restC_restC, derC_restC, mlEval_zero, mul_zero, add_zero]

lemma mlEval_derC_update (c : Cube (Fin R) → ℝ) (i : Fin R) (x : Fin R → ℝ) (t : ℝ) :
    mlEval (derC c i) (Function.update x i t) = mlEval (derC c i) x := by
  rw [mlEval_update, restC_derC, derC_derC, mlEval_zero, mul_zero, add_zero]

lemma continuous_mlEval' (c : Cube (Fin R) → ℝ) : Continuous (fun x : Fin R → ℝ => mlEval c x) := by
  unfold mlEval
  refine continuous_finsetSum _ fun s _ => continuous_const.mul
    (continuous_finsetProd _ fun j _ => ?_)
  by_cases h : s j = true
  · simp only [h, ite_true]; exact continuous_apply j
  · simp only [h]; exact continuous_const


/-! ### Taylor expansion along a line and one replacement -/

lemma taylor3 {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) {M : ℝ} (hM : ∀ x, |iteratedDeriv 3 g x| ≤ M)
    (t : ℝ) :
    |g t - (g 0 + deriv g 0 * t + iteratedDeriv 2 g 0 / 2 * t ^ 2)| ≤ M / 6 * |t| ^ 3 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hcd : ContDiffOn ℝ ((2 : ℕ) + 1) g (uIcc 0 t) := hg.contDiffOn
  obtain ⟨x', -, hx'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm ht) hcd
  have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_uIcc (Ne.symm ht)
  have hw : ∀ k : ℕ, k ≤ 3 → iteratedDerivWithin k g (uIcc 0 t) 0 = iteratedDeriv k g 0 :=
    fun k hk => iteratedDerivWithin_eq_iteratedDeriv hu
      ((hg.of_le (by exact_mod_cast hk)).contDiffAt) left_mem_uIcc
  have key : taylorWithinEval g 2 (uIcc 0 t) 0 t =
      g 0 + deriv g 0 * t + iteratedDeriv 2 g 0 / 2 * t ^ 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, smul_eq_mul]
    rw [hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num), iteratedDeriv_zero,
      iteratedDeriv_one]
    simp [Nat.factorial]
    ring
  rw [← key, hx', sub_zero]
  have e : iteratedDeriv (2 + 1) g x' * t ^ (2 + 1) / ((2 + 1).factorial : ℝ) =
      iteratedDeriv 3 g x' * t ^ 3 / 6 := by norm_num [Nat.factorial]
  rw [e, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 6)]
  have := hM x'
  calc |iteratedDeriv 3 g x'| * |t| ^ 3 / 6 ≤ M * |t| ^ 3 / 6 := by gcongr
    _ = M / 6 * |t| ^ 3 := by ring

lemma abs_pow_le_one_add_pow4 (t : ℝ) {k : ℕ} (hk : k ≤ 4) : |t| ^ k ≤ 1 + t ^ 4 := by
  have h4 : |t| ^ 4 = t ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rcases le_total |t| 1 with h | h
  · have : |t| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg t) h
    have : 0 ≤ t ^ 4 := by positivity
    linarith
  · have : |t| ^ k ≤ |t| ^ 4 := pow_le_pow_right₀ h hk
    linarith

lemma goodLaw_integrable_abs_pow {ν : Measure ℝ} (hν : GoodLaw ν) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun t => |t| ^ k) ν := by
  have := hν.prob
  refine ((integrable_const 1).add hν.int4).mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact abs_pow_le_one_add_pow4 t hk

lemma goodLaw_integrable_pow {ν : Measure ℝ} (hν : GoodLaw ν) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun t => t ^ k) ν :=
  (goodLaw_integrable_abs_pow hν hk).mono' (by fun_prop) (ae_of_all _ fun t => by
    rw [Real.norm_eq_abs, abs_pow])

lemma goodLaw_integral_abs_cube_le {ν : Measure ℝ} (hν : GoodLaw ν) : ∫ t, |t| ^ 3 ∂ν ≤ 5 := by
  have h2 := goodLaw_integrable_pow hν (k := 2) (by norm_num)
  have h4 := hν.int4
  have hb : Integrable (fun t : ℝ => (t ^ 2 + t ^ 4) / 2) ν := (h2.add h4).div_const 2
  calc ∫ t, |t| ^ 3 ∂ν ≤ ∫ t, (t ^ 2 + t ^ 4) / 2 ∂ν := by
        refine integral_mono (goodLaw_integrable_abs_pow hν (by norm_num)) hb fun t => ?_
        have e2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        have e4 : t ^ 4 = |t| ^ 4 := by rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm
        simp only
        rw [e2, e4]
        nlinarith [mul_nonneg (sq_nonneg |t|) (sq_nonneg (|t| - 1))]
    _ = (1 + ∫ t, t ^ 4 ∂ν) / 2 := by
        rw [integral_div, integral_add h2 h4, hν.m2]
    _ ≤ 5 := by linarith [hν.m4]

lemma lipPair_nonneg' {Φ : ℝ → ℝ → ℝ} {K : ℝ} (hK : LipPair Φ K) : 0 ≤ K := by
  have := hK 1 0 0 0
  norm_num at this
  exact (abs_nonneg _).trans this

lemma lineC3_nonneg {Φ : ℝ → ℝ → ℝ} {B : ℝ} (hB : LineC3 Φ B) : 0 ≤ B := by
  have := (hB 0 0 1 0).2 0
  norm_num at this
  exact (abs_nonneg _).trans this

lemma integrable_line_goodLaw {Φ : ℝ → ℝ → ℝ} {K B : ℝ} (hK : LipPair Φ K) (hB : LineC3 Φ B)
    {ν : Measure ℝ} (hν : GoodLaw ν) (α β α' β' : ℝ) :
    Integrable (fun t => Φ (α + t * β) (α' + t * β')) ν := by
  have := hν.prob
  have hc := (hB α α' β β').1.continuous
  have h1 := goodLaw_integrable_abs_pow hν (k := 1) (by norm_num)
  refine ((integrable_const |Φ α α'|).add (h1.const_mul (K * (|β| + |β'|)))).mono'
    hc.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs]
  have h := hK (α + t * β) (α' + t * β') α α'
  have e1 : α + t * β - α = t * β := by ring
  have e2 : α' + t * β' - α' = t * β' := by ring
  rw [e1, e2, abs_mul, abs_mul] at h
  have := abs_sub_abs_le_abs_sub (Φ (α + t * β) (α' + t * β')) (Φ α α')
  change |Φ (α + t * β) (α' + t * β')| ≤ |Φ α α'| + K * (|β| + |β'|) * |t| ^ 1
  have e3 : K * (|t| * |β| + |t| * |β'|) = K * (|β| + |β'|) * |t| ^ 1 := by ring
  linarith

/-- **One replacement**: two laws with the same first two moments give the same expectation of
`Φ(α + tβ, α' + tβ')` up to the third-order Taylor remainder. -/
lemma one_coord {Φ : ℝ → ℝ → ℝ} {K B : ℝ} (hK : LipPair Φ K) (hB : LineC3 Φ B)
    {ν₁ ν₂ : Measure ℝ} (h₁ : GoodLaw ν₁) (h₂ : GoodLaw ν₂) (α β α' β' : ℝ) :
    |∫ t, Φ (α + t * β) (α' + t * β') ∂ν₁ - ∫ t, Φ (α + t * β) (α' + t * β') ∂ν₂| ≤
      5 / 3 * (B * (|β| + |β'|) ^ 3) := by
  obtain ⟨hcd, hd3⟩ := hB α α' β β'
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => Φ (α + t * β) (α' + t * β') := ⟨_, rfl⟩
  rw [← hg] at hcd hd3 ⊢
  obtain ⟨M, hM⟩ : ∃ M, M = B * (|β| + |β'|) ^ 3 := ⟨_, rfl⟩
  rw [← hM] at hd3 ⊢
  have hM0 : 0 ≤ M := hM ▸ mul_nonneg (lineC3_nonneg hB) (by positivity)
  have gint : ∀ ν, GoodLaw ν → Integrable g ν := fun ν hν => by
    rw [hg]; exact integrable_line_goodLaw hK hB hν α β α' β'
  obtain ⟨c1, hc1⟩ : ∃ c1, c1 = deriv g 0 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = iteratedDeriv 2 g 0 / 2 := ⟨_, rfl⟩
  have rb : ∀ t, |g t - (g 0 + c1 * t + c2 * t ^ 2)| ≤ M / 6 * |t| ^ 3 := fun t => by
    rw [hc1, hc2]; exact taylor3 hcd hd3 t
  have key : ∀ ν, GoodLaw ν → |∫ t, g t ∂ν - (g 0 + c2)| ≤ M / 6 * 5 := fun ν hν => by
    have := hν.prob
    have i1 := goodLaw_integrable_pow hν (k := 1) (by norm_num)
    have i2 := goodLaw_integrable_pow hν (k := 2) (by norm_num)
    have j0 : Integrable (fun _ : ℝ => g 0) ν := integrable_const _
    have j1 : Integrable (fun t : ℝ => c1 * t) ν :=
      (i1.const_mul c1).congr (ae_of_all _ fun t => by simp)
    have j2 : Integrable (fun t : ℝ => c2 * t ^ 2) ν := i2.const_mul c2
    have j01 : Integrable (fun t : ℝ => g 0 + c1 * t) ν := j0.add j1
    have hP : Integrable (fun t : ℝ => g 0 + c1 * t + c2 * t ^ 2) ν := j01.add j2
    have hPi : ∫ t, (g 0 + c1 * t + c2 * t ^ 2) ∂ν = g 0 + c2 := by
      rw [integral_add j01 j2, integral_add j0 j1, integral_const, integral_const_mul,
        integral_const_mul, hν.m1, hν.m2]
      simp
    have hr := (gint ν hν).sub hP
    have e : ∫ t, g t ∂ν - (g 0 + c2) = ∫ t, (g t - (g 0 + c1 * t + c2 * t ^ 2)) ∂ν := by
      rw [integral_sub (gint ν hν) hP, hPi]
    rw [e]
    calc |∫ t, (g t - (g 0 + c1 * t + c2 * t ^ 2)) ∂ν|
        ≤ ∫ t, |g t - (g 0 + c1 * t + c2 * t ^ 2)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ t, M / 6 * |t| ^ 3 ∂ν :=
          integral_mono hr.abs ((goodLaw_integrable_abs_pow hν (by norm_num)).const_mul _) rb
      _ = M / 6 * ∫ t, |t| ^ 3 ∂ν := integral_const_mul _ _
      _ ≤ M / 6 * 5 := by gcongr; exact goodLaw_integral_abs_cube_le hν
  have k1 := key ν₁ h₁
  have k2 := key ν₂ h₂
  have : |∫ t, g t ∂ν₁ - ∫ t, g t ∂ν₂| ≤
      |∫ t, g t ∂ν₁ - (g 0 + c2)| + |∫ t, g t ∂ν₂ - (g 0 + c2)| := by
    calc _ = |(∫ t, g t ∂ν₁ - (g 0 + c2)) - (∫ t, g t ∂ν₂ - (g 0 + c2))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith


/-! ### Moments of multilinear polynomials under product laws -/

lemma integrable_abs_mlEval_pow (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    (b : Cube (Fin R) → ℝ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun x => |mlEval b x| ^ k) (Measure.pi ν) := by
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).prob
  have h4 : Integrable (fun x => ‖mlEval b x‖ ^ 4) (Measure.pi ν) :=
    (memLp_mlEval_pi ν hν b).integrable_norm_pow (by norm_num)
  refine ((integrable_const 1).add h4).mono'
    ((continuous_mlEval' b).abs.pow k).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change |mlEval b x| ^ k ≤ 1 + ‖mlEval b x‖ ^ 4
  rw [Real.norm_eq_abs]
  have := abs_pow_le_one_add_pow4 (mlEval b x) hk
  have h4' : |mlEval b x| ^ 4 = (mlEval b x) ^ 4 := by
    rw [pow_abs]; exact abs_of_nonneg (by positivity)
  linarith

/-- `E|p|³ ≤ 3^d (E p²)^{3/2}` for `deg p ≤ d` (Bonami and `|p|³ ≤ (λ p² + p⁴/λ)/2`). -/
lemma moment3_le (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i)) {d : ℕ}
    (b : Cube (Fin R) → ℝ) (hb : ∀ s, d < sdeg s → b s = 0) :
    ∫ x, |mlEval b x| ^ 3 ∂Measure.pi ν ≤ 3 ^ d * (∑ s, b s ^ 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ s, b s ^ 2 := ⟨_, rfl⟩
  rw [← hS]
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun s _ => sq_nonneg _
  have i2 := integrable_abs_mlEval_pow ν hν b (k := 2) (by norm_num)
  have i3 := integrable_abs_mlEval_pow ν hν b (k := 3) (by norm_num)
  have i4 := integrable_abs_mlEval_pow ν hν b (k := 4) (by norm_num)
  have m2 : ∫ x, |mlEval b x| ^ 2 ∂Measure.pi ν = S := by
    have := integral_mlEval_mul_pi ν hν b b
    rw [hS, show ∑ s, b s ^ 2 = ∑ s, b s * b s from Finset.sum_congr rfl fun s _ => by ring,
      ← this]
    congr 1; funext x; rw [sq_abs]; ring
  have m4 : ∫ x, |mlEval b x| ^ 4 ∂Measure.pi ν ≤ 9 ^ d * S ^ 2 := by
    have := bonami ν hν b hb
    rw [← hS] at this
    calc _ = ∫ x, mlEval b x ^ 4 ∂Measure.pi ν := by
          congr 1; funext x; rw [pow_abs]; exact abs_of_nonneg (by positivity)
      _ ≤ _ := this
  have amgm : ∀ lam : ℝ, 0 < lam →
      ∫ x, |mlEval b x| ^ 3 ∂Measure.pi ν ≤ (lam * S + 9 ^ d * S ^ 2 / lam) / 2 := by
    intro lam hlam
    have hb2 : Integrable (fun x => (lam * |mlEval b x| ^ 2 + |mlEval b x| ^ 4 / lam) / 2)
        (Measure.pi ν) := ((i2.const_mul lam).add (i4.div_const lam)).div_const 2
    calc ∫ x, |mlEval b x| ^ 3 ∂Measure.pi ν
        ≤ ∫ x, (lam * |mlEval b x| ^ 2 + |mlEval b x| ^ 4 / lam) / 2 ∂Measure.pi ν := by
          refine integral_mono i3 hb2 fun x => ?_
          obtain ⟨a, ha⟩ : ∃ a, a = |mlEval b x| := ⟨_, rfl⟩
          have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
          simp only
          rw [← ha]
          have key : 2 * lam * a ^ 3 ≤ lam ^ 2 * a ^ 2 + a ^ 4 := by
            nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (lam - a))]
          rw [show (lam * a ^ 2 + a ^ 4 / lam) / 2 = (lam ^ 2 * a ^ 2 + a ^ 4) / (2 * lam) by
            field_simp, le_div_iff₀ (by positivity)]
          linarith
      _ = (lam * S + (∫ x, |mlEval b x| ^ 4 ∂Measure.pi ν) / lam) / 2 := by
          rw [integral_div, integral_add (i2.const_mul lam) (i4.div_const lam),
            integral_const_mul, integral_div, m2]
      _ ≤ (lam * S + 9 ^ d * S ^ 2 / lam) / 2 := by gcongr
  rcases hS0.eq_or_lt with h0 | hpos
  · have := amgm 1 one_pos
    rw [← h0] at this ⊢
    rw [Real.zero_rpow (by norm_num), mul_zero]
    simpa using this
  · obtain ⟨r, hr⟩ : ∃ r, r = √S := ⟨_, rfl⟩
    have hr0 : 0 < r := hr ▸ Real.sqrt_pos.2 hpos
    have hSr : S = r ^ 2 := by rw [hr, Real.sq_sqrt hS0]
    have h32 : S ^ (3 / 2 : ℝ) = r ^ 2 * r := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow, ← hr, hSr]
    have := amgm (3 ^ d * r) (by positivity)
    have h9 : (9 : ℝ) ^ d = (3 ^ d) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h32]
    rw [h9, hSr] at this
    have e : ((3 : ℝ) ^ d * r * r ^ 2 + (3 ^ d) ^ 2 * (r ^ 2) ^ 2 / (3 ^ d * r)) / 2 =
        3 ^ d * (r ^ 2 * r) := by
      field_simp; ring
    linarith


/-! ### Splitting off one coordinate of a product measure -/

section Split

variable {n : ℕ}

lemma insertNth_eq_update (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i t y =
      Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 y) i t := by
  rw [Fin.update_insertNth]

lemma integral_pi_split (ν : Fin (n + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    ∫ x, F x ∂Measure.pi ν =
      ∫ y, ∫ t, F (i.insertNth t y) ∂ν i ∂Measure.pi (fun j => ν (i.succAbove j)) := by
  have hmp := (measurePreserving_piFinSuccAbove ν i).symm
  rw [← hmp.integral_comp' F, integral_prod_symm]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF

lemma integrable_split (ν : Fin (n + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    Integrable (fun y => ∫ t, F (i.insertNth t y) ∂ν i)
      (Measure.pi (fun j => ν (i.succAbove j))) := by
  have hmp := (measurePreserving_piFinSuccAbove ν i).symm
  have h := ((hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
    hF).integral_prod_right
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using h

lemma integral_pi_indep (ν : Fin (n + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (i : Fin (n + 1)) {H : (Fin (n + 1) → ℝ) → ℝ} (hH : Integrable H (Measure.pi ν))
    (hind : ∀ t y, H (i.insertNth t y) = H (i.insertNth 0 y)) :
    ∫ x, H x ∂Measure.pi ν =
        ∫ y, H (i.insertNth 0 y) ∂Measure.pi (fun j => ν (i.succAbove j)) ∧
      Integrable (fun y => H (i.insertNth 0 y)) (Measure.pi (fun j => ν (i.succAbove j))) := by
  have e : ∀ y, ∫ t, H (i.insertNth t y) ∂ν i = H (i.insertNth 0 y) := fun y => by
    simp [hind]
  refine ⟨?_, ?_⟩
  · rw [integral_pi_split ν i hH]
    congr 1; funext y; exact e y
  · have := integrable_split ν i hH
    simpa [e] using this

end Split

lemma continuous_uncurry' {Φ : ℝ → ℝ → ℝ} {K : ℝ} (hΦ : LipPair Φ K) :
    Continuous (Function.uncurry Φ) := by
  have hK := lipPair_nonneg' hΦ
  refine (LipschitzWith.of_dist_le_mul (K := ⟨2 * K, by positivity⟩) fun p q => ?_).continuous
  rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h := hΦ p.1 p.2 q.1 q.2
  have h1 := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h2 := le_max_right |p.1 - q.1| |p.2 - q.2|
  change |Φ p.1 p.2 - Φ q.1 q.2| ≤ 2 * K * max _ _
  nlinarith

lemma continuous_F {Φ : ℝ → ℝ → ℝ} {K : ℝ} (hΦ : LipPair Φ K) (c e : Cube (Fin R) → ℝ) :
    Continuous (fun x : Fin R → ℝ => Φ (mlEval c x) (mlEval e x)) :=
  (continuous_uncurry' hΦ).comp ((continuous_mlEval' c).prodMk (continuous_mlEval' e))

lemma integrable_F (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i)) {Φ : ℝ → ℝ → ℝ} {K : ℝ}
    (hΦ : LipPair Φ K) (c e : Cube (Fin R) → ℝ) :
    Integrable (fun x : Fin R → ℝ => Φ (mlEval c x) (mlEval e x)) (Measure.pi ν) := by
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).prob
  have h1 := integrable_abs_mlEval_pow ν hν c (k := 1) (by norm_num)
  have h2 := integrable_abs_mlEval_pow ν hν e (k := 1) (by norm_num)
  refine ((integrable_const |Φ 0 0|).add ((h1.add h2).const_mul K)).mono'
    (continuous_F hΦ c e).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  change |Φ (mlEval c x) (mlEval e x)| ≤ |Φ 0 0| + K * (|mlEval c x| ^ 1 + |mlEval e x| ^ 1)
  have h := hΦ (mlEval c x) (mlEval e x) 0 0
  rw [sub_zero, sub_zero] at h
  have := abs_sub_abs_le_abs_sub (Φ (mlEval c x) (mlEval e x)) (Φ 0 0)
  simp only [pow_one]
  linarith

lemma add_cube_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : (u + v) ^ 3 ≤ 4 * (u ^ 3 + v ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hu hv) (sq_nonneg (u - v))]

/-- **One replacement step** of the hybrid argument: replacing the law of coordinate `i` by
another good law changes `E Φ(p, q)` by at most `(20/3) B 3^d (Infᵢ(p)^{3/2} + Infᵢ(q)^{3/2})`. -/
lemma replace_one {d : ℕ} (c e : Cube (Fin R) → ℝ) (hc : ∀ s, d < sdeg s → c s = 0)
    (he : ∀ s, d < sdeg s → e s = 0) (Φ : ℝ → ℝ → ℝ) {K B : ℝ} (hK : LipPair Φ K)
    (hB : LineC3 Φ B) (ν : Fin R → Measure ℝ) (hν : ∀ j, GoodLaw (ν j)) (i : Fin R)
    (ν' : Measure ℝ) (hν' : GoodLaw ν') :
    |∫ x, Φ (mlEval c x) (mlEval e x) ∂Measure.pi ν -
        ∫ x, Φ (mlEval c x) (mlEval e x) ∂Measure.pi (Function.update ν i ν')| ≤
      20 / 3 * B * 3 ^ d * (inflC c i ^ (3 / 2 : ℝ) + inflC e i ^ (3 / 2 : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by have := i.pos; omega⟩
  have hB0 := lineC3_nonneg hB
  have hν2 : ∀ j, GoodLaw (Function.update ν i ν' j) := fun j => by
    by_cases hj : j = i
    · subst hj; simpa using hν'
    · rw [Function.update_of_ne hj]; exact hν j
  have : ∀ j, IsProbabilityMeasure (ν j) := fun j => (hν j).prob
  have : ∀ j, IsProbabilityMeasure (Function.update ν i ν' j) := fun j => (hν2 j).prob
  have : IsProbabilityMeasure ν' := hν'.prob
  have hF1 := integrable_F ν hν hK c e
  have hF2 := integrable_F _ hν2 hK c e
  have hρ : (fun j => Function.update ν i ν' (i.succAbove j)) = fun j => ν (i.succAbove j) :=
    funext fun j => Function.update_of_ne (i.succAbove_ne j) _ _
  have hi : Function.update ν i ν' i = ν' := Function.update_self _ _ _
  have int1 := integrable_split ν i hF1
  have int2 := integrable_split _ i hF2
  rw [hρ, hi] at int2
  rw [integral_pi_split ν i hF1, integral_pi_split _ i hF2, hρ, hi, ← integral_sub int1 int2]
  -- the derivative polynomials
  have hHc := integral_pi_indep ν i (integrable_abs_mlEval_pow ν hν (derC c i) (k := 3)
    (by norm_num)) (fun t y => by
      rw [insertNth_eq_update i t y, mlEval_derC_update])
  have hHe := integral_pi_indep ν i (integrable_abs_mlEval_pow ν hν (derC e i) (k := 3)
    (by norm_num)) (fun t y => by
      rw [insertNth_eq_update i t y, mlEval_derC_update])
  have hb : Integrable (fun y => 20 / 3 * B * (|mlEval (derC c i) (i.insertNth 0 y)| ^ 3 +
      |mlEval (derC e i) (i.insertNth 0 y)| ^ 3)) (Measure.pi (fun j => ν (i.succAbove j))) :=
    (hHc.2.add hHe.2).const_mul _
  have pt : ∀ y, ‖∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν i -
      ∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν'‖ ≤
      20 / 3 * B * (|mlEval (derC c i) (i.insertNth 0 y)| ^ 3 +
        |mlEval (derC e i) (i.insertNth 0 y)| ^ 3) := fun y => by
    have hfun : (fun t => Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y))) =
        fun t => Φ (mlEval (restC c i) (i.insertNth 0 y) + t * mlEval (derC c i) (i.insertNth 0 y))
          (mlEval (restC e i) (i.insertNth 0 y) + t * mlEval (derC e i) (i.insertNth 0 y)) := by
      funext t
      rw [insertNth_eq_update i t y, mlEval_update, mlEval_update]
    rw [Real.norm_eq_abs]
    rw [show (∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν i) =
      ∫ t, Φ (mlEval (restC c i) (i.insertNth 0 y) + t * mlEval (derC c i) (i.insertNth 0 y))
          (mlEval (restC e i) (i.insertNth 0 y) + t * mlEval (derC e i) (i.insertNth 0 y)) ∂ν i
      from congrArg (fun f => ∫ t, f t ∂ν i) hfun]
    rw [show (∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν') =
      ∫ t, Φ (mlEval (restC c i) (i.insertNth 0 y) + t * mlEval (derC c i) (i.insertNth 0 y))
          (mlEval (restC e i) (i.insertNth 0 y) + t * mlEval (derC e i) (i.insertNth 0 y)) ∂ν'
      from congrArg (fun f => ∫ t, f t ∂ν') hfun]
    refine (one_coord hK hB (hν i) hν' _ _ _ _).trans ?_
    have := add_cube_le (abs_nonneg (mlEval (derC c i) (i.insertNth 0 y)))
      (abs_nonneg (mlEval (derC e i) (i.insertNth 0 y)))
    have hB' : 0 ≤ 5 / 3 * B := by positivity
    calc 5 / 3 * (B * (|mlEval (derC c i) (i.insertNth 0 y)| +
          |mlEval (derC e i) (i.insertNth 0 y)|) ^ 3) =
        5 / 3 * B * (|mlEval (derC c i) (i.insertNth 0 y)| +
          |mlEval (derC e i) (i.insertNth 0 y)|) ^ 3 := by ring
      _ ≤ 5 / 3 * B * (4 * (|mlEval (derC c i) (i.insertNth 0 y)| ^ 3 +
          |mlEval (derC e i) (i.insertNth 0 y)| ^ 3)) := mul_le_mul_of_nonneg_left this hB'
      _ = _ := by ring
  have m3c := moment3_le ν hν (derC c i) (derC_deg hc i)
  have m3e := moment3_le ν hν (derC e i) (derC_deg he i)
  rw [sum_derC_sq] at m3c m3e
  rw [hHc.1] at m3c
  rw [hHe.1] at m3e
  calc ‖∫ y, ((∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν i) -
        ∫ t, Φ (mlEval c (i.insertNth t y)) (mlEval e (i.insertNth t y)) ∂ν')
        ∂Measure.pi (fun j => ν (i.succAbove j))‖
      ≤ ∫ y, 20 / 3 * B * (|mlEval (derC c i) (i.insertNth 0 y)| ^ 3 +
          |mlEval (derC e i) (i.insertNth 0 y)| ^ 3)
          ∂Measure.pi (fun j => ν (i.succAbove j)) :=
        norm_integral_le_of_norm_le hb (ae_of_all _ pt)
    _ = 20 / 3 * B * ((∫ y, |mlEval (derC c i) (i.insertNth 0 y)| ^ 3
          ∂Measure.pi (fun j => ν (i.succAbove j))) +
        ∫ y, |mlEval (derC e i) (i.insertNth 0 y)| ^ 3
          ∂Measure.pi (fun j => ν (i.succAbove j))) := by
        rw [integral_const_mul, integral_add hHc.2 hHe.2]
    _ ≤ 20 / 3 * B * (3 ^ d * inflC c i ^ (3 / 2 : ℝ) + 3 ^ d * inflC e i ^ (3 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring


/-! ### The endpoints of the hybrid argument -/

/-- The uniform law on `Bool`. -/
noncomputable def unifB : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)

lemma unifB_singleton (b : Bool) : unifB {b} = 1 / 2 := by
  cases b <;> simp [unifB]

instance : IsProbabilityMeasure unifB := by
  constructor
  simp [unifB, ENNReal.inv_two_add_inv_two]

lemma signLaw_eq_map : signLaw = unifB.map bitSign := by
  have hm : Measurable bitSign := measurable_of_countable _
  rw [unifB, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm]
  · simp [signLaw, bitSign, add_comm]
  · exact hm.aemeasurable

lemma expect_eq_integral_sign (f : (Fin R → ℝ) → ℝ) (hf : Continuous f) :
    (𝔼 x, f (bitVec x)) = ∫ y, f y ∂Measure.pi (fun _ : Fin R => signLaw) := by
  have hm : Measurable bitSign := measurable_of_countable _
  have hmap : Measure.pi (fun _ : Fin R => signLaw) =
      (Measure.pi fun _ : Fin R => unifB).map (fun b j => bitSign (b j)) := by
    rw [Measure.pi_map_pi (fun _ => hm.aemeasurable), signLaw_eq_map]
  rw [hmap, integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp only [Measure.real, Measure.pi_singleton, unifB_singleton, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.expect_eq_sum_div_card, Finset.sum_div, Finset.card_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ENNReal.toReal_pow]
  have h2 : (1 / 2 : ENNReal).toReal = 1 / 2 := by simp
  rw [h2, Nat.cast_pow, Nat.cast_ofNat, div_eq_inv_mul, one_div, inv_pow]
  rfl

lemma integral_gm_eq_pi (f : (Fin R → ℝ) → ℝ) (hf : Continuous f) :
    ∫ G, f G ∂gm R = ∫ y, f y ∂Measure.pi (fun _ : Fin R => gaussianReal 0 1) := by
  change ∫ G, f G.ofLp ∂stdGaussian (EuclideanSpace ℝ (Fin R)) = _
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (by fun_prop : Continuous fun G : EuclideanSpace ℝ (Fin R) => f G.ofLp).aestronglyMeasurable]

end BGHKLMM26.RobustMIS.Lindeberg

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

/-- **Lindeberg replacement** for pairs of polynomials of degree `≤ d`. -/
theorem lindeberg {d : ℕ} (c e : Cube (Fin R) → ℝ) (hc : ∀ s, d < sdeg s → c s = 0)
    (he : ∀ s, d < sdeg s → e s = 0) (Φ : ℝ → ℝ → ℝ) {K B : ℝ} (hK : LipPair Φ K)
    (hB : LineC3 Φ B) :
    |(𝔼 x, Φ (mlEval c (bitVec x)) (mlEval e (bitVec x))) -
        ∫ G, Φ (mlEval c G) (mlEval e G) ∂gm R| ≤
      10 * B * 9 ^ d * ∑ i, (inflC c i ^ (3 / 2 : ℝ) + inflC e i ^ (3 / 2 : ℝ)) := by
  obtain ⟨F, hF⟩ : ∃ F : (Fin R → ℝ) → ℝ, F = fun x => Φ (mlEval c x) (mlEval e x) := ⟨_, rfl⟩
  have hFc : Continuous F := hF ▸ Lindeberg.continuous_F hK c e
  have hB0 := Lindeberg.lineC3_nonneg hB
  have e1 : (𝔼 x, Φ (mlEval c (bitVec x)) (mlEval e (bitVec x))) = 𝔼 x, F (bitVec x) := by
    rw [hF]
  have e2 : ∫ G, Φ (mlEval c G) (mlEval e G) ∂gm R = ∫ G, F G ∂gm R := by rw [hF]
  rw [e1, e2, Lindeberg.expect_eq_integral_sign F hFc, Lindeberg.integral_gm_eq_pi F hFc]
  let hyb : ℕ → Fin R → Measure ℝ := fun k j => if (j : ℕ) < k then gaussianReal 0 1 else signLaw
  have h0 : (fun _ : Fin R => signLaw) = hyb 0 := by funext j; simp [hyb]
  have hR : (fun _ : Fin R => gaussianReal 0 1) = hyb R := by funext j; simp [hyb, j.isLt]
  have hgood : ∀ k j, GoodLaw (hyb k j) := fun k j => by
    simp only [hyb]; split_ifs
    · exact goodLaw_gaussianReal
    · exact goodLaw_signLaw
  have hsucc : ∀ i : Fin R, hyb ((i : ℕ) + 1) = Function.update (hyb i) i (gaussianReal 0 1) := by
    intro i; funext j
    by_cases hj : j = i
    · subst hj; simp [hyb]
    · rw [Function.update_of_ne hj]
      have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      simp only [hyb]
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
  rw [h0, hR]
  have tele : ∫ y, F y ∂Measure.pi (hyb 0) - ∫ y, F y ∂Measure.pi (hyb R) =
      ∑ i : Fin R, (∫ y, F y ∂Measure.pi (hyb i) - ∫ y, F y ∂Measure.pi (hyb ((i : ℕ) + 1))) := by
    rw [← Finset.sum_range_sub' (fun k => ∫ y, F y ∂Measure.pi (hyb k)) R, Finset.sum_range]
  rw [tele]
  calc |∑ i : Fin R, (∫ y, F y ∂Measure.pi (hyb i) - ∫ y, F y ∂Measure.pi (hyb ((i : ℕ) + 1)))|
      ≤ ∑ i : Fin R,
          |∫ y, F y ∂Measure.pi (hyb i) - ∫ y, F y ∂Measure.pi (hyb ((i : ℕ) + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin R, 20 / 3 * B * 3 ^ d * (inflC c i ^ (3 / 2 : ℝ) + inflC e i ^ (3 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hsucc i, hF]
        exact Lindeberg.replace_one c e hc he Φ hK hB (hyb i) (hgood i) i _ goodLaw_gaussianReal
    _ ≤ ∑ i : Fin R, 10 * B * 9 ^ d * (inflC c i ^ (3 / 2 : ℝ) + inflC e i ^ (3 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hI : 0 ≤ inflC c i ^ (3 / 2 : ℝ) + inflC e i ^ (3 / 2 : ℝ) := by
          have h1 : 0 ≤ inflC c i := Finset.sum_nonneg fun s _ => sq_nonneg _
          have h2 : 0 ≤ inflC e i := Finset.sum_nonneg fun s _ => sq_nonneg _
          positivity
        have h39 : (3 : ℝ) ^ d ≤ 9 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
        apply mul_le_mul_of_nonneg_right _ hI
        have : 20 / 3 * B * 3 ^ d ≤ 10 * B * 3 ^ d := by
          have : 0 ≤ B * 3 ^ d := by positivity
          nlinarith
        calc 20 / 3 * B * 3 ^ d ≤ 10 * B * 3 ^ d := this
          _ ≤ 10 * B * 9 ^ d := by gcongr
    _ = _ := by rw [Finset.mul_sum]

end BGHKLMM26.RobustMIS
