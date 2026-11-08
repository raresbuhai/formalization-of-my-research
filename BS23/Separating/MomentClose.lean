module

public import BS23.Common.UniformProof
public import Background.SumOfSquares.Normed
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Moment closeness on the good event

Per-cluster moments of the (perturbed) standardized noise, as polynomials in `d` variables, for
the analysis of the separating-bipartition algorithm [BS23, Theorem 1.1]. With `‖·‖₁` the sum of
the absolute values of the coefficients (`SoS.coeffNorm1`):

* `BS23.Separating.lin a = ∑ᵢ aᵢ Xᵢ`, `BS23.Separating.empMom S a r = |S|⁻¹ ∑_{j ∈ S} (lin aⱼ)^r`
  (the empirical `r`-th moment polynomial) and `BS23.Separating.gaussPoly r =
  gaussMom r · (∑ᵢ Xᵢ²)^(r/2)` (the Gaussian one, `E ⟨G, X⟩^r`; it is `0` for odd `r`).
* **Moment closeness** (`BS23.Separating.coeffNorm1_empMom_sub_gaussPoly_le`): on the good event
  `GoodNoise w η D ℓ g`, if `0 < w_c`, `2η ≤ w_c`, `2η ≤ 1`, `d ≤ n` and `r ≤ D`, then for every
  perturbation with `‖ε_j‖₂² ≤ 1/n²`,
  `‖empMom S_c (g + ε) r - gaussPoly r‖₁ ≤ (2η/w_c + 1/n) (4 (d + 1) (r + 1))^(r + 1)`.
  *Noise part* (`BS23.Separating.coeffNorm1_empMom_sub_gaussPoly_le_of_goodNoise`, error
  `(2η/w_c) d^r`): by the multinomial theorem, `empMom S_c g r - gaussPoly r` is
  `∑_{|α| = r} (r; α) (n_c⁻¹ ∑_{j ∈ S_c} g_j^α - m_α) X^α`
  (`BS23.Separating.empMom_sub_gaussPoly_eq`, from `BS23.sum_multinomial_gaussMomMulti` and
  `MvPolynomial.funext`); every coefficient is within `η n / n_c ≤ 2η/w_c`, and
  `∑_α (r; α) = d^r`. *Rounding part*
  (`BS23.Separating.coeffNorm1_empMom_add_sub_le_of_goodNoise`): `‖(A + E)^r - A^r‖₁ ≤
  r e (a + e)^(r-1)` for `‖A‖₁ ≤ a`, `‖E‖₁ ≤ e`, here with `a = ‖g_j‖₁` and
  `e = √d / n ≤ 1`; then `(a + 1)^(r-1) ≤ 2^(r-1) (1 + a^(2m))` for `m = ⌊r/2⌋`, and on the good
  event `n_c⁻¹ ∑_{j ∈ S_c} ‖g_j‖₁^(2m) ≤ d^(2m) ((2m-1)‼ + 1)` (Jensen and the moments
  `g_{ji}^(2m)`).
* **Substitutions.** `‖p(φ)‖₁ ≤ ‖p‖₁ β^r` for `p` homogeneous of degree `r` and every
  `‖φᵢ‖₁ ≤ β` (`BS23.Separating.coeffNorm1_aeval_le_of_isHomogeneous`; for `deg p ≤ r` and
  `β ≥ 1`, `BS23.Separating.coeffNorm1_aeval_le_of_totalDegree_le`). Hence moment closeness
  after `X ↦ φ` with error multiplied by `β^r`
  (`BS23.Separating.coeffNorm1_aeval_empMom_sub_le`), and
  `‖gaussPoly r‖₁ ≤ gaussMom r · d^(r/2)` (`BS23.Separating.coeffNorm1_gaussPoly_le`,
  `BS23.Separating.coeffNorm1_aeval_gaussPoly_le`).
* **Pointwise.** `|p(b)| ≤ ‖p‖₁ ‖b‖₂^r` for `p` homogeneous of degree `r`
  (`BS23.Separating.abs_eval_le_coeffNorm1_mul`), hence
  `|n_c⁻¹ ∑_{j ∈ S_c} ⟨g_j + ε_j, b⟩^r - gaussMom r ‖b‖₂^r| ≤ δ_r ‖b‖₂^r`
  (`BS23.Separating.abs_eval_empMom_sub_le`; for even degree with `‖b‖₂^(2s) = (∑ bᵢ²)^s`,
  `BS23.Separating.abs_eval_empMom_sub_le_even`, also after a substitution,
  `BS23.Separating.abs_eval_aeval_empMom_sub_le_even`).
-/

@[expose] public section

namespace BS23.Separating

open MvPolynomial Finset SoS

variable {k d n : ℕ}

/-! ### Linear forms, empirical moment polynomials and Gaussian moment polynomials -/

/-- The linear form `∑ᵢ aᵢ Xᵢ`. -/
noncomputable def lin (a : Fin d → ℝ) : MvPolynomial (Fin d) ℝ := ∑ i, C (a i) * X i

/-- The empirical `r`-th moment polynomial `|S|⁻¹ ∑_{j ∈ S} ⟨aⱼ, X⟩^r` of the points `aⱼ`,
`j ∈ S`. -/
noncomputable def empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    MvPolynomial (Fin d) ℝ :=
  (S.card : ℝ)⁻¹ • ∑ j ∈ S, lin (a j) ^ r

/-- The Gaussian `r`-th moment polynomial `E ⟨G, X⟩^r = E Z^r ‖X‖^r`, that is
`gaussMom r · (∑ᵢ Xᵢ²)^(r/2)` (`gaussMom r = 0` for odd `r`). -/
noncomputable def gaussPoly (r : ℕ) : MvPolynomial (Fin d) ℝ :=
  (gaussMom r : ℝ) • (∑ i, X i ^ 2) ^ (r / 2)

@[simp] lemma eval_lin (a b : Fin d → ℝ) : eval b (lin a) = ∑ i, a i * b i := by
  simp [lin]

lemma eval_empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) (b : Fin d → ℝ) :
    eval b (empMom S a r) = (S.card : ℝ)⁻¹ * ∑ j ∈ S, (∑ i, a j i * b i) ^ r := by
  simp [empMom, smul_eval]

lemma eval_gaussPoly (r : ℕ) (b : Fin d → ℝ) :
    eval b (gaussPoly r) = (gaussMom r : ℝ) * (∑ i, b i ^ 2) ^ (r / 2) := by
  simp [gaussPoly, smul_eval]

lemma gaussMom_eq_zero_of_not_even {r : ℕ} (hr : ¬ Even r) : gaussMom r = 0 := by
  simp [gaussMom, hr]

/-- `gaussMom r · (∑ bᵢ²)^(r/2) = gaussMom r · ‖b‖^r`: both vanish for odd `r`. -/
lemma gaussMom_mul_pow_div_two (r : ℕ) (b : Fin d → ℝ) :
    (gaussMom r : ℝ) * (∑ i, b i ^ 2) ^ (r / 2) =
      (gaussMom r : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ r := by
  by_cases hr : Even r
  · obtain ⟨s, rfl⟩ := hr
    rw [← two_mul, Nat.mul_div_cancel_left _ two_pos, pow_mul,
      Real.sq_sqrt (by positivity)]
  · simp [gaussMom_eq_zero_of_not_even hr]

lemma eval_gaussPoly' (r : ℕ) (b : Fin d → ℝ) :
    eval b (gaussPoly r) = (gaussMom r : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ r := by
  rw [eval_gaussPoly, gaussMom_mul_pow_div_two]

/-! ### The multinomial expansion -/

/-- The empirical moments minus the Gaussian ones, monomial by monomial:
`∑_{|α| = r} (r; α) (|S|⁻¹ ∑_{j ∈ S} aⱼ^α - m_α) X^α`. -/
lemma empMom_sub_gaussPoly_eq (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    empMom S a r - gaussPoly r = ∑ α ∈ (univ : Finset (Fin d)).piAntidiag r,
      ((Nat.multinomial univ α : ℝ) *
        ((S.card : ℝ)⁻¹ * ∑ j ∈ S, ∏ i, a j i ^ α i - (gaussMomMulti α : ℝ))) •
        ∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i := by
  apply MvPolynomial.funext
  intro b
  rw [map_sub, eval_empMom, eval_gaussPoly', ← sum_multinomial_gaussMomMulti, map_sum]
  simp only [smul_eval, map_prod, map_pow, eval_X]
  simp_rw [sum_pow_eq_sum_piAntidiag, mul_pow, prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have h : ∑ j ∈ S, (Nat.multinomial univ α : ℝ) * ((∏ i, a j i ^ α i) * ∏ i, b i ^ α i) =
      (Nat.multinomial univ α : ℝ) * (∏ i, b i ^ α i) * ∑ j ∈ S, ∏ i, a j i ^ α i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h]
  ring

/-! ### Coefficient norms -/

lemma coeffNorm1_prod_X_pow_le (α : Fin d → ℕ) :
    coeffNorm1 (∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i) ≤ 1 :=
  (coeffNorm1_prod_le _ _).trans (Finset.prod_le_one₀ (fun _ _ ↦ coeffNorm1_nonneg _)
    fun i _ ↦ (coeffNorm1_pow_le _ _).trans (by rw [coeffNorm1_X, one_pow]))

lemma coeffNorm1_lin_le (a : Fin d → ℝ) : coeffNorm1 (lin a) ≤ ∑ i, |a i| :=
  (coeffNorm1_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ by rw [coeffNorm1_C_mul, coeffNorm1_X, mul_one])

/-- Cauchy–Schwarz: `‖b‖₁ ≤ √d ‖b‖₂`. -/
lemma sum_abs_le_sqrt_mul_sqrt (b : Fin d → ℝ) :
    ∑ i, |b i| ≤ Real.sqrt d * Real.sqrt (∑ i, b i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ ↦ (1 : ℝ)) (fun i ↦ |b i|)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sq_abs] at h
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

@[simp] lemma lin_zero : lin (0 : Fin d → ℝ) = 0 := by simp [lin]

lemma lin_add (a b : Fin d → ℝ) : lin (a + b) = lin a + lin b := by
  simp [lin, add_mul, Finset.sum_add_distrib]

lemma lin_neg (a : Fin d → ℝ) : lin (-a) = -lin a := by
  simp [lin, Finset.sum_neg_distrib]

lemma lin_sub (a b : Fin d → ℝ) : lin (a - b) = lin a - lin b := by
  simp [lin, sub_mul, Finset.sum_sub_distrib]

lemma lin_smul (t : ℝ) (a : Fin d → ℝ) : lin (t • a) = C t * lin a := by
  simp [lin, Finset.mul_sum, mul_assoc]

lemma lin_sum {ι : Type*} (s : Finset ι) (a : ι → Fin d → ℝ) :
    lin (∑ l ∈ s, a l) = ∑ l ∈ s, lin (a l) := by
  simp only [lin, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- `‖(A + E)^(r+1) - A^(r+1)‖₁ ≤ (r + 1) e (a + e)^r` if `‖A‖₁ ≤ a` and `‖E‖₁ ≤ e`. -/
lemma coeffNorm1_add_pow_succ_sub_le {σ : Type*} (A E : MvPolynomial σ ℝ) {a e : ℝ}
    (ha : coeffNorm1 A ≤ a) (he : coeffNorm1 E ≤ e) (r : ℕ) :
    coeffNorm1 ((A + E) ^ (r + 1) - A ^ (r + 1)) ≤ (r + 1) * e * (a + e) ^ r := by
  have ha0 : 0 ≤ a := (coeffNorm1_nonneg A).trans ha
  have he0 : 0 ≤ e := (coeffNorm1_nonneg E).trans he
  have hAE : coeffNorm1 (A + E) ≤ a + e := (coeffNorm1_add_le _ _).trans (add_le_add ha he)
  induction r with
  | zero => simpa using he
  | succ r ih =>
    have heq : (A + E) ^ (r + 1 + 1) - A ^ (r + 1 + 1) =
        (A + E) * ((A + E) ^ (r + 1) - A ^ (r + 1)) + E * A ^ (r + 1) := by ring
    have hApow : coeffNorm1 (A ^ (r + 1)) ≤ (a + e) ^ (r + 1) :=
      (coeffNorm1_pow_le _ _).trans
        (pow_le_pow_left₀ (coeffNorm1_nonneg _) (ha.trans (by linarith)) _)
    rw [heq]
    calc coeffNorm1 ((A + E) * ((A + E) ^ (r + 1) - A ^ (r + 1)) + E * A ^ (r + 1))
        ≤ coeffNorm1 (A + E) * coeffNorm1 ((A + E) ^ (r + 1) - A ^ (r + 1)) +
            coeffNorm1 E * coeffNorm1 (A ^ (r + 1)) :=
          (coeffNorm1_add_le _ _).trans (add_le_add (coeffNorm1_mul_le _ _) (coeffNorm1_mul_le _ _))
      _ ≤ (a + e) * ((r + 1) * e * (a + e) ^ r) + e * (a + e) ^ (r + 1) :=
          add_le_add (mul_le_mul hAE ih (coeffNorm1_nonneg _) (by positivity))
            (mul_le_mul he hApow (coeffNorm1_nonneg _) he0)
      _ = ((r + 1 : ℕ) + 1 : ℝ) * e * (a + e) ^ (r + 1) := by push_cast; ring

/-- `‖(A + E)^r - A^r‖₁ ≤ r e (a + e)^(r-1)` if `‖A‖₁ ≤ a` and `‖E‖₁ ≤ e`. -/
lemma coeffNorm1_add_pow_sub_le {σ : Type*} (A E : MvPolynomial σ ℝ) {a e : ℝ}
    (ha : coeffNorm1 A ≤ a) (he : coeffNorm1 E ≤ e) (r : ℕ) :
    coeffNorm1 ((A + E) ^ r - A ^ r) ≤ r * e * (a + e) ^ (r - 1) := by
  rcases r with _ | r
  · simp
  · simpa using coeffNorm1_add_pow_succ_sub_le A E ha he r

/-- `(G + 1)^p ≤ 2^p (1 + G^q)` for `G ≥ 0` and `p ≤ q`. -/
lemma add_one_pow_le_two_pow_mul {G : ℝ} (hG : 0 ≤ G) {p q : ℕ} (hpq : p ≤ q) :
    (G + 1) ^ p ≤ 2 ^ p * (1 + G ^ q) := by
  have hM : 1 ≤ max G 1 := le_max_right _ _
  calc (G + 1) ^ p ≤ (2 * max G 1) ^ p :=
        pow_le_pow_left₀ (by positivity) (by linarith [le_max_left G 1, le_max_right G 1]) p
    _ = 2 ^ p * max G 1 ^ p := mul_pow _ _ _
    _ ≤ 2 ^ p * max G 1 ^ q := by gcongr
    _ ≤ 2 ^ p * (1 + G ^ q) := by
        gcongr
        rcases le_total G 1 with hG1 | hG1
        · rw [max_eq_right hG1, one_pow]; linarith [pow_nonneg hG q]
        · rw [max_eq_left hG1]; linarith

/-! ### Homogeneity -/

lemma isHomogeneous_lin (a : Fin d → ℝ) : (lin a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

lemma isHomogeneous_empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    (empMom S a r).IsHomogeneous r := by
  rw [empMom, smul_eq_C_mul]
  refine IsHomogeneous.C_mul (IsHomogeneous.sum _ _ _ fun j _ ↦ ?_) _
  simpa using (isHomogeneous_lin (a j)).pow r

lemma isHomogeneous_gaussPoly (r : ℕ) : (gaussPoly (d := d) r).IsHomogeneous r := by
  by_cases hr : Even r
  · obtain ⟨s, rfl⟩ := hr
    rw [gaussPoly, smul_eq_C_mul]
    refine IsHomogeneous.C_mul ?_ _
    have h2 : (∑ i, (X i : MvPolynomial (Fin d) ℝ) ^ 2).IsHomogeneous 2 :=
      IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow _ _
    have := h2.pow ((s + s) / 2)
    rwa [show 2 * ((s + s) / 2) = s + s by omega] at this
  · simp only [gaussPoly, gaussMom_eq_zero_of_not_even hr, Nat.cast_zero, zero_smul]
    exact isHomogeneous_zero _ _ _

/-! ### Pointwise bounds and substitutions -/

/-- `|p(b)| ≤ ‖p‖₁ ‖b‖₂^r` for `p` homogeneous of degree `r`. -/
lemma abs_eval_le_coeffNorm1_mul {p : MvPolynomial (Fin d) ℝ} {r : ℕ} (hp : p.IsHomogeneous r)
    (b : Fin d → ℝ) : |eval b p| ≤ coeffNorm1 p * Real.sqrt (∑ i, b i ^ 2) ^ r := by
  set R := Real.sqrt (∑ i, b i ^ 2)
  have hb : ∀ i, |b i| ≤ R := fun i ↦ Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun i ↦ b i ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i))
  rw [eval_eq', coeffNorm1, Finset.sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_prod]
  calc ∏ i, |b i ^ m i| ≤ ∏ i, R ^ m i :=
        Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i) _
    _ = R ^ r := by
        rw [Finset.prod_pow_eq_pow_sum, hp.degree_eq_sum_deg_support hm, ← Finsupp.degree_apply,
          Finsupp.degree_eq_sum]

/-- Substitution: `‖p(φ)‖₁ ≤ ∑_m |p_m| β^|m|` if every `‖φᵢ‖₁ ≤ β`. -/
lemma coeffNorm1_aeval_le_sum {σ τ : Type*} [Finite σ] (φ : σ → MvPolynomial τ ℝ) {β : ℝ}
    (hφ : ∀ i, coeffNorm1 (φ i) ≤ β) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (aeval φ p) ≤ ∑ m ∈ p.support, |p.coeff m| * β ^ m.degree := by
  have := Fintype.ofFinite σ
  rw [aeval_def, eval₂_eq']
  refine (coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [algebraMap_eq, coeffNorm1_C_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc coeffNorm1 (∏ i, φ i ^ m i) ≤ ∏ i, coeffNorm1 (φ i ^ m i) := coeffNorm1_prod_le _ _
    _ ≤ ∏ i, β ^ m i :=
        Finset.prod_le_prod₀ (fun _ _ ↦ coeffNorm1_nonneg _) fun i _ ↦
          (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hφ i) _)
    _ = β ^ m.degree := by rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]

/-- Substitution into a homogeneous polynomial of degree `r`: `‖p(φ)‖₁ ≤ ‖p‖₁ β^r` if every
`‖φᵢ‖₁ ≤ β`. -/
lemma coeffNorm1_aeval_le_of_isHomogeneous {σ τ : Type*} [Finite σ] (φ : σ → MvPolynomial τ ℝ)
    {β : ℝ} (hφ : ∀ i, coeffNorm1 (φ i) ≤ β) {p : MvPolynomial σ ℝ} {r : ℕ}
    (hp : p.IsHomogeneous r) : coeffNorm1 (aeval φ p) ≤ coeffNorm1 p * β ^ r := by
  refine (coeffNorm1_aeval_le_sum φ hφ p).trans_eq ?_
  rw [coeffNorm1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [hp.degree_eq_sum_deg_support hm, ← Finsupp.degree_apply]

/-- Substitution into a polynomial of degree at most `r`: `‖p(φ)‖₁ ≤ ‖p‖₁ β^r` if every
`‖φᵢ‖₁ ≤ β` and `β ≥ 1`. -/
lemma coeffNorm1_aeval_le_of_totalDegree_le {σ τ : Type*} [Finite σ]
    (φ : σ → MvPolynomial τ ℝ) {β : ℝ} (hβ : 1 ≤ β) (hφ : ∀ i, coeffNorm1 (φ i) ≤ β)
    {p : MvPolynomial σ ℝ} {r : ℕ} (hp : p.totalDegree ≤ r) :
    coeffNorm1 (aeval φ p) ≤ coeffNorm1 p * β ^ r := by
  refine (coeffNorm1_aeval_le_sum φ hφ p).trans ?_
  rw [coeffNorm1, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm ↦
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hβ ?_) (abs_nonneg _)
  exact (le_totalDegree hm).trans hp

lemma eval_aeval_eq {σ τ : Type*} (φ : σ → MvPolynomial τ ℝ) (v : τ → ℝ)
    (p : MvPolynomial σ ℝ) : eval v (aeval φ p) = eval (fun i ↦ eval v (φ i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma aeval_lin {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) (a : Fin d → ℝ) :
    aeval φ (lin a) = ∑ i, C (a i) * φ i := by
  simp [lin, algebraMap_eq]

lemma aeval_empMom {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) (S : Finset (Fin n))
    (a : Fin n → Fin d → ℝ) (r : ℕ) :
    aeval φ (empMom S a r) = (S.card : ℝ)⁻¹ • ∑ j ∈ S, (∑ i, C (a j i) * φ i) ^ r := by
  simp [empMom, aeval_lin, map_smul]

lemma aeval_gaussPoly {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) (r : ℕ) :
    aeval φ (gaussPoly r) = (gaussMom r : ℝ) • (∑ i, φ i ^ 2) ^ (r / 2) := by
  simp [gaussPoly, map_smul]

/-- `‖gaussPoly r‖₁ ≤ gaussMom r · d^(r/2)`. -/
lemma coeffNorm1_gaussPoly_le (r : ℕ) :
    coeffNorm1 (gaussPoly (d := d) r) ≤ gaussMom r * (d : ℝ) ^ (r / 2) := by
  rw [gaussPoly, coeffNorm1_smul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ((coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (coeffNorm1_nonneg _) ?_ _)) (Nat.cast_nonneg _)
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ i, coeffNorm1 ((X i : MvPolynomial (Fin d) ℝ) ^ 2) ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ (coeffNorm1_pow_le _ _).trans (by rw [coeffNorm1_X, one_pow])
    _ = d := by simp

/-- `‖gaussPoly r (φ)‖₁ ≤ gaussMom r · d^(r/2) β^r` if every `‖φᵢ‖₁ ≤ β`. -/
lemma coeffNorm1_aeval_gaussPoly_le {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (hφ : ∀ i, coeffNorm1 (φ i) ≤ β) (r : ℕ) :
    coeffNorm1 (aeval φ (gaussPoly r)) ≤ gaussMom r * (d : ℝ) ^ (r / 2) * β ^ r :=
  (coeffNorm1_aeval_le_of_isHomogeneous φ hφ (isHomogeneous_gaussPoly r)).trans
    (mul_le_mul_of_nonneg_right (coeffNorm1_gaussPoly_le r) (pow_nonneg hβ _))

/-! ### The constant -/

lemma doubleFactorial_two_mul_sub_one_le {m r : ℕ} (h : 2 * m ≤ r) :
    (2 * m - 1).doubleFactorial ≤ r ^ r :=
  (Nat.doubleFactorial_le_factorial _).trans
    ((Nat.factorial_le (by omega)).trans (Nat.factorial_le_pow r))

lemma pow_le_momCloseConst (d r : ℕ) : d ^ r ≤ (4 * (d + 1) * (r + 1)) ^ (r + 1) :=
  (Nat.pow_le_pow_left (by nlinarith) r).trans
    (Nat.pow_le_pow_right (by positivity) (Nat.le_succ r))

lemma rounding_le_momCloseConst (d r : ℕ) :
    (d + 1) * (r * 2 ^ (r - 1) *
        (1 + d ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1))) ≤
      (4 * (d + 1) * (r + 1)) ^ (r + 1) := by
  have h2m : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
  have hdf : (2 * (r / 2) - 1).doubleFactorial + 1 ≤ 2 * (r + 1) ^ r := by
    have h1 := doubleFactorial_two_mul_sub_one_le h2m
    have h2 : r ^ r ≤ (r + 1) ^ r := Nat.pow_le_pow_left (by omega) r
    have h3 : 1 ≤ (r + 1) ^ r := Nat.one_le_pow _ _ (by omega)
    omega
  have hdp : d ^ (2 * (r / 2)) ≤ (d + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) h2m)
  have hX : 1 ≤ (d + 1) ^ r * (r + 1) ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hin : 1 + d ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1) ≤
      3 * ((d + 1) ^ r * (r + 1) ^ r) := by
    calc 1 + d ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1)
        ≤ 1 + (d + 1) ^ r * (2 * (r + 1) ^ r) := by gcongr
      _ ≤ 3 * ((d + 1) ^ r * (r + 1) ^ r) := by nlinarith
  have h2 : 2 ^ (r - 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h34 : 3 * 2 ^ r ≤ 4 ^ (r + 1) :=
    calc 3 * 2 ^ r ≤ 4 * 4 ^ r := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) r)
      _ = 4 ^ (r + 1) := by ring
  calc (d + 1) * (r * 2 ^ (r - 1) *
        (1 + d ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1)))
      ≤ (d + 1) * ((r + 1) * 2 ^ r * (3 * ((d + 1) ^ r * (r + 1) ^ r))) := by
        gcongr
        omega
    _ = 3 * 2 ^ r * ((d + 1) ^ (r + 1) * (r + 1) ^ (r + 1)) := by ring
    _ ≤ 4 ^ (r + 1) * ((d + 1) ^ (r + 1) * (r + 1) ^ (r + 1)) := by gcongr
    _ = (4 * (d + 1) * (r + 1)) ^ (r + 1) := by rw [mul_pow, mul_pow]; ring

/-! ### Consequences of the good event -/

section Good

variable {w : Fin k → ℝ} {η : ℝ} {D : ℕ} {ℓ : Fin n → Fin k} {g : Fin n → Fin d → ℝ}

lemma eta_nonneg_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k) : 0 ≤ η :=
  (abs_nonneg _).trans (h.2 c 0 (by simp))

/-- On the good event with `η ≤ 1/2`, cluster `c` has at least a `w_c / 2` fraction of the
points. -/
lemma half_le_frac_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k) (hw : 0 < w c)
    (hη1 : 2 * η ≤ 1) : w c / 2 ≤ ((cluster ℓ c).card : ℝ) / n := by
  have h' := (abs_le.1 (h.1 c)).1
  nlinarith

lemma card_pos_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k) (hw : 0 < w c)
    (hη1 : 2 * η ≤ 1) : 0 < (cluster ℓ c).card ∧ 0 < n := by
  have hf : 0 < ((cluster ℓ c).card : ℝ) / n :=
    (half_pos hw).trans_le (half_le_frac_of_goodNoise h c hw hη1)
  rcases div_pos_iff.1 hf with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · exact absurd h1 (not_lt.2 (Nat.cast_nonneg _))

/-- Monomial by monomial: `|n_c⁻¹ ∑_{j ∈ S_c} g_j^α - m_α| ≤ 2η / w_c`. -/
lemma abs_avg_sub_gaussMomMulti_le (h : GoodNoise w η D ℓ g) (c : Fin k) (hw : 0 < w c)
    (hη1 : 2 * η ≤ 1) (α : Fin d → ℕ) (hα : ∑ i, α i ≤ D) :
    |((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i - gaussMomMulti α| ≤
      2 * η / w c := by
  obtain ⟨hN, hn⟩ := card_pos_of_goodNoise h c hw hη1
  have hfrac := half_le_frac_of_goodNoise h c hw hη1
  have hη0 := eta_nonneg_of_goodNoise h c
  set N := (cluster ℓ c).card
  set Y := ∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (N : ℝ)⁻¹ * Y - gaussMomMulti α =
      (n / N) * (Y / n - (N : ℝ) / n * gaussMomMulti α) := by
    field_simp
  rw [key, abs_mul, abs_of_pos (by positivity)]
  have hnN : (n : ℝ) / N ≤ 2 / w c := by
    rw [div_le_div_iff₀ hN' hw]
    rw [le_div_iff₀ hn'] at hfrac
    linarith
  calc (n : ℝ) / N * |Y / n - (N : ℝ) / n * gaussMomMulti α| ≤ (n / N) * η :=
        mul_le_mul_of_nonneg_left (h.2 c α hα) (by positivity)
    _ ≤ (2 / w c) * η := mul_le_mul_of_nonneg_right hnN hη0
    _ = 2 * η / w c := by ring

/-- **The noise part of moment closeness**: `‖empMom S_c g r - gaussPoly r‖₁ ≤ (2η / w_c) d^r`. -/
theorem coeffNorm1_empMom_sub_gaussPoly_le_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) {r : ℕ} (hr : r ≤ D) :
    coeffNorm1 (empMom (cluster ℓ c) g r - gaussPoly r) ≤ 2 * η / w c * (d : ℝ) ^ r := by
  have hη0 := eta_nonneg_of_goodNoise h c
  rw [empMom_sub_gaussPoly_eq]
  refine (coeffNorm1_sum_le _ _).trans ?_
  have hsum : ∑ α ∈ (univ : Finset (Fin d)).piAntidiag r, (Nat.multinomial univ α : ℝ) =
      (d : ℝ) ^ r := by
    have := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin d)) (fun _ ↦ (1 : ℝ)) r
    simpa using this.symm
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα ↦ ?_
  have hαD : ∑ i, α i ≤ D := (le_of_eq (mem_piAntidiag.1 hα).1).trans hr
  rw [coeffNorm1_smul, abs_mul, Nat.abs_cast]
  calc (Nat.multinomial univ α : ℝ) *
        |((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i - gaussMomMulti α| *
          coeffNorm1 (∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i)
      ≤ (Nat.multinomial univ α : ℝ) * (2 * η / w c) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (abs_avg_sub_gaussMomMulti_le h c hw hη1 α hαD) (Nat.cast_nonneg _))
          (coeffNorm1_prod_X_pow_le α) (coeffNorm1_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) hw.le))
    _ = 2 * η / w c * (Nat.multinomial univ α : ℝ) := by ring

/-- Even moments of one coordinate: `n_c⁻¹ ∑_{j ∈ S_c} g_{ji}^{2m} ≤ (2m-1)‼ + 1`. -/
lemma avg_pow_le_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k) (hw : 0 < w c)
    (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) {m : ℕ} (hm : 2 * m ≤ D) (i : Fin d) :
    ((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c, g j i ^ (2 * m) ≤
      (2 * m - 1).doubleFactorial + 1 := by
  have hα : ∑ i', (Pi.single i (2 * m) : Fin d → ℕ) i' = 2 * m := by simp
  have hb := abs_avg_sub_gaussMomMulti_le h c hw hη1 (Pi.single i (2 * m)) ((le_of_eq hα).trans hm)
  have hprod : ∀ j, ∏ i', g j i' ^ (Pi.single i (2 * m) : Fin d → ℕ) i' = g j i ^ (2 * m) := by
    intro j
    rw [Fintype.prod_eq_single i (fun i' hi' ↦ by simp [hi'])]
    simp
  have hm' : gaussMomMulti (Pi.single i (2 * m) : Fin d → ℕ) = (2 * m - 1).doubleFactorial := by
    rw [gaussMomMulti, Fintype.prod_eq_single i
      (fun i' hi' ↦ by simp [hi', gaussMom])]
    simp [gaussMom_two_mul]
  simp only [hprod, hm'] at hb
  have h2 : 2 * η / w c ≤ 1 := by rw [div_le_one hw]; exact hη
  linarith [(abs_le.1 hb).2]

/-- Even moments of the `ℓ₁` norm: `n_c⁻¹ ∑_{j ∈ S_c} ‖g_j‖₁^{2m} ≤ d^{2m} ((2m-1)‼ + 1)`. -/
lemma avg_sum_abs_pow_le_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k) (hw : 0 < w c)
    (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) {m : ℕ} (hm : 2 * m ≤ D) :
    ((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c, (∑ i, |g j i|) ^ (2 * m) ≤
      (d : ℝ) ^ (2 * m) * ((2 * m - 1).doubleFactorial + 1) := by
  obtain ⟨hN, -⟩ := card_pos_of_goodNoise h c hw hη1
  have hN' : ((cluster ℓ c).card : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rcases m with _ | m
  · simp [hN']
  · have hj : ∀ j, (∑ i, |g j i|) ^ (2 * (m + 1)) ≤
        (d : ℝ) ^ (2 * m + 1) * ∑ i, g j i ^ (2 * (m + 1)) := by
      intro j
      have := pow_sum_le_card_mul_sum_pow (s := univ) (f := fun i ↦ |g j i|)
        (fun _ _ ↦ abs_nonneg _) (2 * m + 1)
      have he : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
      simp only [card_univ, Fintype.card_fin, he.pow_abs] at this
      rwa [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    calc ((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c, (∑ i, |g j i|) ^ (2 * (m + 1))
        ≤ ((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c,
            (d : ℝ) ^ (2 * m + 1) * ∑ i, g j i ^ (2 * (m + 1)) := by
          gcongr with j
          exact hj j
      _ = (d : ℝ) ^ (2 * m + 1) * ∑ i, (((cluster ℓ c).card : ℝ)⁻¹ *
            ∑ j ∈ cluster ℓ c, g j i ^ (2 * (m + 1))) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ (d : ℝ) ^ (2 * m + 1) * ∑ _i : Fin d, (((2 * (m + 1) - 1).doubleFactorial : ℝ) + 1) := by
          gcongr with i
          exact avg_pow_le_of_goodNoise h c hw hη1 hη hm i
      _ = (d : ℝ) ^ (2 * (m + 1)) * (((2 * (m + 1) - 1).doubleFactorial : ℝ) + 1) := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
            show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ]
          ring

/-- **The rounding part of moment closeness**: perturbing each point by `ε_j` with
`‖ε_j‖₂ ≤ 1/n` moves the empirical moment polynomial by at most
`(√d / n) r 2^(r-1) (1 + d^(2m) ((2m-1)‼ + 1))` in `‖·‖₁`, `m = ⌊r/2⌋`. -/
theorem coeffNorm1_empMom_add_sub_le_of_goodNoise (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {r : ℕ} (hr : r ≤ D) :
    coeffNorm1 (empMom (cluster ℓ c) (g + ε) r - empMom (cluster ℓ c) g r) ≤
      Real.sqrt d / n * (r * 2 ^ (r - 1) *
        (1 + (d : ℝ) ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1))) := by
  obtain ⟨hN, hn⟩ := card_pos_of_goodNoise h c hw hη1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < (cluster ℓ c).card := by exact_mod_cast hN
  set e := Real.sqrt d / n with he_def
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [div_le_one hn']
    calc Real.sqrt d ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
          have : (d : ℝ) ≤ n := by exact_mod_cast hd
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith)
      _ = n := Real.sqrt_sq hn'.le
  have hej : ∀ j, coeffNorm1 (lin (ε j)) ≤ e := by
    intro j
    refine (coeffNorm1_lin_le _).trans ((sum_abs_le_sqrt_mul_sqrt _).trans ?_)
    have hs : Real.sqrt (∑ i, ε j i ^ 2) ≤ 1 / n :=
      calc Real.sqrt (∑ i, ε j i ^ 2) ≤ Real.sqrt ((1 / (n : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact hε j)
        _ = 1 / n := Real.sqrt_sq (by positivity)
    calc Real.sqrt d * Real.sqrt (∑ i, ε j i ^ 2) ≤ Real.sqrt d * (1 / n) :=
          mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = e := by rw [he_def]; ring
  have hdiff : empMom (cluster ℓ c) (g + ε) r - empMom (cluster ℓ c) g r =
      ((cluster ℓ c).card : ℝ)⁻¹ •
        ∑ j ∈ cluster ℓ c, ((lin (g j) + lin (ε j)) ^ r - lin (g j) ^ r) := by
    simp only [empMom, ← smul_sub, ← Finset.sum_sub_distrib, Pi.add_apply, lin_add]
  have hterm : ∀ j, coeffNorm1 ((lin (g j) + lin (ε j)) ^ r - lin (g j) ^ r) ≤
      r * e * 2 ^ (r - 1) * (1 + (∑ i, |g j i|) ^ (2 * (r / 2))) := by
    intro j
    have hG0 : 0 ≤ ∑ i, |g j i| := by positivity
    refine (coeffNorm1_add_pow_sub_le _ _ (coeffNorm1_lin_le _) (hej j) r).trans ?_
    calc (r : ℝ) * e * (∑ i, |g j i| + e) ^ (r - 1) ≤
          r * e * (∑ i, |g j i| + 1) ^ (r - 1) := by gcongr
      _ ≤ r * e * (2 ^ (r - 1) * (1 + (∑ i, |g j i|) ^ (2 * (r / 2)))) := by
          gcongr
          exact add_one_pow_le_two_pow_mul hG0 (by omega)
      _ = _ := by ring
  rw [hdiff, coeffNorm1_smul, abs_of_pos (inv_pos.2 hN')]
  calc ((cluster ℓ c).card : ℝ)⁻¹ *
        coeffNorm1 (∑ j ∈ cluster ℓ c, ((lin (g j) + lin (ε j)) ^ r - lin (g j) ^ r))
      ≤ ((cluster ℓ c).card : ℝ)⁻¹ * ∑ j ∈ cluster ℓ c,
          r * e * 2 ^ (r - 1) * (1 + (∑ i, |g j i|) ^ (2 * (r / 2))) := by
        gcongr
        exact (coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hterm j)
    _ = r * e * 2 ^ (r - 1) * (1 + ((cluster ℓ c).card : ℝ)⁻¹ *
          ∑ j ∈ cluster ℓ c, (∑ i, |g j i|) ^ (2 * (r / 2))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        field_simp
    _ ≤ r * e * 2 ^ (r - 1) * (1 + (d : ℝ) ^ (2 * (r / 2)) *
          ((2 * (r / 2) - 1).doubleFactorial + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right
          (avg_sum_abs_pow_le_of_goodNoise h c hw hη1 hη (m := r / 2) (by omega)) 1)
          (by positivity)
    _ = e * (r * 2 ^ (r - 1) * (1 + (d : ℝ) ^ (2 * (r / 2)) *
          ((2 * (r / 2) - 1).doubleFactorial + 1))) := by ring

/-! ### Moment closeness -/

/-- **Moment closeness.** On the good event, for every perturbation `ε` of the standardized noise
with `‖ε_j‖₂ ≤ 1/n`, the empirical `r`-th moment polynomial of cluster `c` is close to the
Gaussian one in coefficient norm `‖·‖₁`:
`‖empMom S_c (g + ε) r - gaussPoly r‖₁ ≤ (2η/w_c + 1/n) (4 (d + 1) (r + 1))^(r + 1)`. -/
theorem coeffNorm1_empMom_sub_gaussPoly_le (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {r : ℕ} (hr : r ≤ D) :
    coeffNorm1 (empMom (cluster ℓ c) (g + ε) r - gaussPoly r) ≤
      (2 * η / w c + 1 / n) * (4 * (d + 1) * (r + 1)) ^ (r + 1) := by
  have hA := coeffNorm1_empMom_sub_gaussPoly_le_of_goodNoise h c hw hη1 hr
  have hB := coeffNorm1_empMom_add_sub_le_of_goodNoise h c hw hη1 hη hd hε hr
  have hT1 : (d : ℝ) ^ r ≤ (4 * (d + 1) * (r + 1)) ^ (r + 1) := by
    exact_mod_cast pow_le_momCloseConst d r
  have hT2 : ((d : ℝ) + 1) * (r * 2 ^ (r - 1) *
      (1 + (d : ℝ) ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1))) ≤
        (4 * (d + 1) * (r + 1)) ^ (r + 1) := by
    exact_mod_cast rounding_le_momCloseConst d r
  have hsd : Real.sqrt d ≤ d + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hη0 := eta_nonneg_of_goodNoise h c
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsplit : empMom (cluster ℓ c) (g + ε) r - gaussPoly r =
      (empMom (cluster ℓ c) (g + ε) r - empMom (cluster ℓ c) g r) +
        (empMom (cluster ℓ c) g r - gaussPoly r) := by ring
  rw [hsplit]
  refine (coeffNorm1_add_le _ _).trans ?_
  set K := (r : ℝ) * 2 ^ (r - 1) *
      (1 + (d : ℝ) ^ (2 * (r / 2)) * ((2 * (r / 2) - 1).doubleFactorial + 1))
  set T := (4 * ((d : ℝ) + 1) * (r + 1)) ^ (r + 1)
  have hK : 0 ≤ K := by positivity
  calc coeffNorm1 (empMom (cluster ℓ c) (g + ε) r - empMom (cluster ℓ c) g r) +
        coeffNorm1 (empMom (cluster ℓ c) g r - gaussPoly r)
      ≤ Real.sqrt d / n * K + 2 * η / w c * (d : ℝ) ^ r := add_le_add hB hA
    _ ≤ 1 / n * ((d + 1) * K) + 2 * η / w c * T := by
        rw [div_eq_mul_one_div (Real.sqrt d), mul_comm (Real.sqrt d), mul_assoc]
        gcongr
    _ ≤ 1 / n * T + 2 * η / w c * T := by gcongr
    _ = (2 * η / w c + 1 / n) * T := by ring

/-! ### Corollaries -/

/-- **Moment closeness after a substitution** `X ↦ φ` with every `‖φᵢ‖₁ ≤ β`: the error is
multiplied by `β^r`. -/
theorem coeffNorm1_aeval_empMom_sub_le (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {r : ℕ} (hr : r ≤ D)
    {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hφ : ∀ i, coeffNorm1 (φ i) ≤ β) :
    coeffNorm1 (aeval φ (empMom (cluster ℓ c) (g + ε) r) - aeval φ (gaussPoly r)) ≤
      (2 * η / w c + 1 / n) * (4 * (d + 1) * (r + 1)) ^ (r + 1) * β ^ r := by
  rw [← map_sub]
  exact (coeffNorm1_aeval_le_of_isHomogeneous φ hφ
    ((isHomogeneous_empMom _ _ _).sub (isHomogeneous_gaussPoly _))).trans
    (mul_le_mul_of_nonneg_right
      (coeffNorm1_empMom_sub_gaussPoly_le h c hw hη1 hη hd hε hr) (pow_nonneg hβ _))

/-- **Moment closeness, pointwise**: for every `b`,
`|n_c⁻¹ ∑_{j ∈ S_c} ⟨g_j + ε_j, b⟩^r - gaussMom r ‖b‖^r| ≤ δ_r ‖b‖^r`. -/
theorem abs_eval_empMom_sub_le (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {r : ℕ} (hr : r ≤ D)
    (b : Fin d → ℝ) :
    |eval b (empMom (cluster ℓ c) (g + ε) r) - gaussMom r * Real.sqrt (∑ i, b i ^ 2) ^ r| ≤
      (2 * η / w c + 1 / n) * (4 * (d + 1) * (r + 1)) ^ (r + 1) *
        Real.sqrt (∑ i, b i ^ 2) ^ r := by
  rw [← eval_gaussPoly', ← map_sub]
  exact (abs_eval_le_coeffNorm1_mul
    ((isHomogeneous_empMom _ _ _).sub (isHomogeneous_gaussPoly _)) b).trans
    (mul_le_mul_of_nonneg_right
      (coeffNorm1_empMom_sub_gaussPoly_le h c hw hη1 hη hd hε hr) (by positivity))

/-- **Moment closeness, pointwise, even degree** `2s`: for every `b`,
`|n_c⁻¹ ∑_{j ∈ S_c} ⟨g_j + ε_j, b⟩^(2s) - (2s-1)‼ ‖b‖^(2s)| ≤ δ_{2s} ‖b‖^(2s)`. -/
theorem abs_eval_empMom_sub_le_even (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {s : ℕ}
    (hs : 2 * s ≤ D) (b : Fin d → ℝ) :
    |eval b (empMom (cluster ℓ c) (g + ε) (2 * s)) - gaussMom (2 * s) * (∑ i, b i ^ 2) ^ s| ≤
      (2 * η / w c + 1 / n) * (4 * (d + 1) * (2 * s + 1)) ^ (2 * s + 1) *
        (∑ i, b i ^ 2) ^ s := by
  have key := abs_eval_empMom_sub_le h c hw hη1 hη hd hε hs b
  rwa [pow_mul, Real.sq_sqrt (by positivity), Nat.cast_mul, Nat.cast_ofNat] at key


/-- **Moment closeness, pointwise, after a substitution** `X ↦ φ`, even degree `2s`: with
`N = ∑ᵢ φᵢ²`, `|M(v) - (2s-1)‼ N(v)^s| ≤ δ_{2s} N(v)^s` for the substituted empirical moment
polynomial `M = empMom S_c (g + ε) (2s) (φ)`. -/
theorem abs_eval_aeval_empMom_sub_le_even (h : GoodNoise w η D ℓ g) (c : Fin k)
    (hw : 0 < w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ w c) (hd : d ≤ n)
    {ε : Fin n → Fin d → ℝ} (hε : ∀ j, ∑ i, ε j i ^ 2 ≤ 1 / (n : ℝ) ^ 2) {s : ℕ}
    (hs : 2 * s ≤ D) {τ : Type*} (φ : Fin d → MvPolynomial τ ℝ) (v : τ → ℝ) :
    |eval v (aeval φ (empMom (cluster ℓ c) (g + ε) (2 * s))) -
        gaussMom (2 * s) * eval v (∑ i, φ i ^ 2) ^ s| ≤
      (2 * η / w c + 1 / n) * (4 * (d + 1) * (2 * s + 1)) ^ (2 * s + 1) *
        eval v (∑ i, φ i ^ 2) ^ s := by
  have key := abs_eval_empMom_sub_le_even h c hw hη1 hη hd hε hs (fun i ↦ eval v (φ i))
  rw [eval_aeval_eq]
  simp only [map_sum, map_pow]
  exact key

end Good

end BS23.Separating
