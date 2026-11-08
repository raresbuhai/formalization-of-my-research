module

public import BS23.ColinearSoS.Poly
public import BS23.ColinearSoS.Frame
public import BS23.Separating.Setup
public import Background.SumOfSquares.PseudoBounds

/-!
# Finite-sample transfer of the directional moment polynomials

The finite-sample step of the analysis of the sum-of-squares algorithm for [BS23, Theorem 1.2]:
on the good event, the empirical moment polynomial `Φ̂_{2m}(v) = (1/n) ∑ⱼ ⟨Xⱼ, v⟩^(2m)` of the
whitened rounded sample `Xⱼ = W (ỹⱼ - ȳ)` (`BS23.ColinearSoS.empPoly`) is close, in the
coefficient norm `‖·‖₁` (`SoS.coeffNorm1`), to the moment polynomial
`Φ_{2m}(v) = ∑_c w_c hmom (2m) (a_c ⟨ŭ, v⟩) (vᵀ Σ_W v)` of the whitened mixture
`∑_c w_c N(a_c ŭ, Σ_W)` (`BS23.ColinearSoS.popPoly`; `a_c`, `ŭ`, `Σ_W = W Σ Wᵀ` as in
`BS23/ColinearSoS/Frame.lean`).

**Main result** (`BS23.ColinearSoS.coeffNorm1_empPoly_sub_popPoly_le`). Let the mixture be valid
with means `μ_c = base + t_c u₀` and weights at least `wmin > 0`, and the sample of size `n ≥ d`
rounded within `1/n`, on the good event of degree `D ≥ 2m` and accuracy `η` with `2η ≤ wmin`, and
let the empirical covariance `Ĉ` of the rounded points satisfy `(wmin/4) Σ ⪯ Ĉ` (CV1) and
`cov ⪯ 2 Ĉ`. Then
`‖Φ̂_{2m} - Φ_{2m}‖₁ ≤ (2η/wmin + 1/n) Q^(4m+2)`, `Q = 10⁶ (d + 1)⁶ (m + 1) / wmin`
(`BS23.ColinearSoS.errMP`, `BS23.ColinearSoS.mpBase`); pointwise,
`|Φ̂_{2m}(v) - Φ_{2m}(v)| ≤ errMP · (∑ᵢ |vᵢ|)^(2m)`
(`BS23.ColinearSoS.abs_eval_empPoly_sub_popPoly_le`).

**Proof.**
* *Expansion.* The whitened points are `Xⱼ = m_{ℓⱼ} + ζⱼ` with `m_c = W (μ_c - ȳ)` and
  `ζⱼ = B ĝⱼ`, `B = W Σ^{1/2}` (`BS23.Separating.whiten_yt`). Binomially,
  `Φ̂_{2m} = ∑_c (n_c/n) ∑_q C(2m, q) ⟨m_c, v⟩^(2m-q) M_c^q` with the empirical moment
  polynomials `M_c^q` of the `ζⱼ` on cluster `c` (`BS23.ColinearSoS.MP.empPoly_eq_sum_cluster`),
  and `Φ_{2m} = ∑_c w_c ∑_q C(2m, q) ⟨W (μ_c - μ̄), v⟩^(2m-q) G_q` with the Gaussian moment
  polynomials `G_q = E Z^q · N^(q/2)`, `N(v) = vᵀ Σ_W v = ∑ᵢ φᵢ(v)²` for the columns `φᵢ` of `B`
  (`BS23.ColinearSoS.MP.hmom_eq_sum_choose`, `BS23.ColinearSoS.MP.quadPoly_SW_eq`), since
  `W (μ_c - μ̄) = a_c ŭ`.
* *Noise.* `‖M_c^q - G_q‖₁` is bounded by the moment closeness of
  `BS23/Separating/MomentClose.lean` after the substitution `X ↦ φ`, with `‖φᵢ‖₁ ≤ β =
  3 (d + 1) / √wmin` by CV1 (`BS23.ColinearSoS.MP.Hyp.coeffNorm1_empMom_sub_le`), and
  `‖G_q‖₁ ≤ E Z^q d^(q/2) β^q`.
* *Shift.* `m_c = W (μ_c - μ̄) + δ` with `δ = W (μ̄ - ȳ)`. The whitened points sum to zero, so
  `n δ = -∑_c (n_c - n w_c) W (μ_c - μ̄) - ∑_c n_c M_c^1`, and
  `‖⟨δ, ·⟩‖₁ ≤ η β + max_c ‖M_c^1‖₁` (`BS23.ColinearSoS.MP.coeffNorm1_shift_le`); here
  `‖⟨W (μ_c - μ̄), ·⟩‖₁ ≤ β` because `w_c ((W (μ_c - μ̄))ᵢ)² ≤ eᵢᵀ W cov Wᵀ eᵢ ≤
  2 eᵢᵀ W Ĉ Wᵀ eᵢ ≤ 4` (`BS23.ColinearSoS.MP.coeffNorm1_lin_W_center_le`).
* *Assembly.* In each cluster, `‖(A + Δ)^p - A^p‖₁ ≤ p ‖Δ‖₁ (‖A‖₁ + ‖Δ‖₁)^(p-1)`
  (`BS23.ColinearSoS.MP.coeffNorm1_sum_choose_sub_le`); then the cluster fractions
  `|n_c/n - w_c| ≤ η w_c` (`BS23.ColinearSoS.MP.coeffNorm1_mix_sub_le`,
  `BS23.ColinearSoS.MP.assemble`) and the numerics (`BS23.ColinearSoS.MP.mpBase_facts`,
  `BS23.ColinearSoS.MP.numerics`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open MvPolynomial Finset SoS Matrix

variable {k d n : ℕ}

/-! ### The error -/

/-- The base `Q = 10⁶ (d + 1)⁶ (m + 1) / wmin` of the error of the finite-sample transfer. -/
noncomputable def mpBase (d m : ℕ) (wmin : ℝ) : ℝ :=
  10 ^ 6 * ((d : ℝ) + 1) ^ 6 * ((m : ℝ) + 1) / wmin

/-- The error `(2η/wmin + 1/n) Q^(4m+2)` of the finite-sample transfer at degree `2m`, with
`Q = mpBase d m wmin = 10⁶ (d + 1)⁶ (m + 1) / wmin`. -/
noncomputable def errMP (d m : ℕ) (wmin η : ℝ) (n : ℕ) : ℝ :=
  (2 * η / wmin + 1 / n) * mpBase d m wmin ^ (4 * m + 2)

/-- `Q > 0`. -/
theorem mpBase_pos {d m : ℕ} {wmin : ℝ} (hw : 0 < wmin) : 0 < mpBase d m wmin := by
  unfold mpBase
  positivity

/-- The error is nonnegative. -/
theorem errMP_nonneg {d m : ℕ} {wmin η : ℝ} {n : ℕ} (hw : 0 < wmin) (hη : 0 ≤ η) :
    0 ≤ errMP d m wmin η n := by
  have := mpBase_pos (d := d) (m := m) hw
  unfold errMP
  positivity

namespace MP

variable {σ : Type*} {K : Type*} [CommRing K]

/-- `hmom r a v = ∑_q C(r, q) a^(r-q) E Z^q v^(q/2)`: the binomial expansion of
`E (a + √v Z)^r`, written without the square root. -/
theorem hmom_eq_sum_choose (r : ℕ) (a v : K) :
    hmom r a v = ∑ q ∈ range (r + 1),
      (r.choose q : K) * a ^ (r - q) * (gaussMom q : K) * v ^ (q / 2) := by
  have hsub : (range (r / 2 + 1)).image (fun i ↦ 2 * i) ⊆ range (r + 1) := by
    intro p hp
    simp only [mem_image, mem_range] at hp ⊢
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · rw [hmom]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hermCoeff, gaussMom, even_two_mul, ite_true, Nat.cast_mul,
      Nat.mul_div_cancel_left _ two_pos]
    ring
  · intro i _ j _ h
    simpa using h
  · intro p hp hp'
    have hodd : ¬ Even p := by
      rintro ⟨i, rfl⟩
      apply hp'
      simp only [mem_image, mem_range] at hp ⊢
      exact ⟨i, by omega, by omega⟩
    simp [gaussMom, hodd]

/-- `‖c p‖₁ = c ‖p‖₁` for a natural number `c`. -/
theorem coeffNorm1_natCast_mul (c : ℕ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 ((c : MvPolynomial σ ℝ) * p) = c * coeffNorm1 p := by
  rw [← map_natCast (C : ℝ →+* MvPolynomial σ ℝ) c, coeffNorm1_C_mul, Nat.abs_cast]

/-- `∑_{j ∈ s} (A + Z_j)^r = ∑_q C(r, q) A^(r-q) ∑_{j ∈ s} Z_j^q`. -/
theorem sum_add_pow_eq {ι : Type*} (s : Finset ι) (A : MvPolynomial σ ℝ)
    (Z : ι → MvPolynomial σ ℝ) (r : ℕ) :
    ∑ j ∈ s, (A + Z j) ^ r =
      ∑ q ∈ range (r + 1), (r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * ∑ j ∈ s, Z j ^ q) := by
  simp_rw [add_comm A, add_pow]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

/-- The coefficient norm of `∑_q C(r, q) A^(r-q) G_q` is at most `2^r a^r Gb` if `‖A‖₁ ≤ a`,
`a ≥ 1` and every `‖G_q‖₁ ≤ Gb`. -/
theorem coeffNorm1_sum_choose_le {A : MvPolynomial σ ℝ} {G : ℕ → MvPolynomial σ ℝ} {a Gb : ℝ}
    (r : ℕ) (hA : coeffNorm1 A ≤ a) (ha : 1 ≤ a) (hG : ∀ q ≤ r, coeffNorm1 (G q) ≤ Gb) :
    coeffNorm1 (∑ q ∈ range (r + 1), (r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * G q)) ≤
      2 ^ r * a ^ r * Gb := by
  have hGb : 0 ≤ Gb := (coeffNorm1_nonneg _).trans (hG 0 (Nat.zero_le _))
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ q ∈ range (r + 1),
        coeffNorm1 ((r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * G q))
      ≤ ∑ q ∈ range (r + 1), (r.choose q : ℝ) * (a ^ r * Gb) := by
        refine sum_le_sum fun q hq ↦ ?_
        have hq' : q ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hq)
        rw [coeffNorm1_natCast_mul]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine (coeffNorm1_mul_le _ _).trans (mul_le_mul ?_ (hG q hq') (coeffNorm1_nonneg _)
          (by positivity))
        exact (coeffNorm1_pow_le _ _).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) hA _).trans
          (pow_le_pow_right₀ ha (Nat.sub_le r q)))
    _ = 2 ^ r * a ^ r * Gb := by
        rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- **One cluster.** With `‖A‖₁ ≤ a`, `‖A' - A‖₁ ≤ e`, `a + e ≤ L`, `L ≥ 1`, and, for `q ≤ r`,
`‖K_q - G_q‖₁ ≤ e₁` and `‖G_q‖₁ ≤ Gb`:
`‖∑_q C(r, q) A'^(r-q) K_q - ∑_q C(r, q) A^(r-q) G_q‖₁ ≤ 2^r L^r (e₁ + r e Gb)`. -/
theorem coeffNorm1_sum_choose_sub_le {A A' : MvPolynomial σ ℝ} {Kq G : ℕ → MvPolynomial σ ℝ}
    {a e L e1 Gb : ℝ} (r : ℕ) (hA : coeffNorm1 A ≤ a) (hE : coeffNorm1 (A' - A) ≤ e)
    (hL : a + e ≤ L) (hL1 : 1 ≤ L) (hK : ∀ q ≤ r, coeffNorm1 (Kq q - G q) ≤ e1)
    (hG : ∀ q ≤ r, coeffNorm1 (G q) ≤ Gb) :
    coeffNorm1 (∑ q ∈ range (r + 1), (r.choose q : MvPolynomial σ ℝ) * (A' ^ (r - q) * Kq q) -
        ∑ q ∈ range (r + 1), (r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * G q)) ≤
      2 ^ r * L ^ r * (e1 + r * e * Gb) := by
  have hGb : 0 ≤ Gb := (coeffNorm1_nonneg _).trans (hG 0 (Nat.zero_le _))
  have he1 : 0 ≤ e1 := (coeffNorm1_nonneg _).trans (hK 0 (Nat.zero_le _))
  have he : 0 ≤ e := (coeffNorm1_nonneg _).trans hE
  have ha : 0 ≤ a := (coeffNorm1_nonneg _).trans hA
  have hA' : coeffNorm1 A' ≤ a + e := by
    have h := coeffNorm1_add_le A (A' - A)
    rw [add_sub_cancel] at h
    linarith
  rw [← sum_sub_distrib]
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ q ∈ range (r + 1), coeffNorm1 ((r.choose q : MvPolynomial σ ℝ) * (A' ^ (r - q) * Kq q) -
        (r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * G q))
      ≤ ∑ q ∈ range (r + 1), (r.choose q : ℝ) * (L ^ r * (e1 + r * e * Gb)) := by
        refine sum_le_sum fun q hq ↦ ?_
        have hq' : q ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hq)
        rw [← mul_sub, coeffNorm1_natCast_mul]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hsplit : A' ^ (r - q) * Kq q - A ^ (r - q) * G q =
            A' ^ (r - q) * (Kq q - G q) + (A' ^ (r - q) - A ^ (r - q)) * G q := by ring
        have hpow : coeffNorm1 (A' ^ (r - q)) ≤ L ^ r :=
          (coeffNorm1_pow_le _ _).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _)
            (hA'.trans hL) _).trans (pow_le_pow_right₀ hL1 (Nat.sub_le r q)))
        have hdiff : coeffNorm1 (A' ^ (r - q) - A ^ (r - q)) ≤ r * e * L ^ r := by
          have h := Separating.coeffNorm1_add_pow_sub_le A (A' - A) hA hE (r - q)
          rw [add_sub_cancel] at h
          refine h.trans ?_
          have h1 : ((r - q : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r q
          have h2 : (a + e) ^ (r - q - 1) ≤ L ^ r :=
            (pow_le_pow_left₀ (by linarith) hL _).trans
              (pow_le_pow_right₀ hL1 (by omega))
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 he) h2 (by positivity)
            (by positivity)
        rw [hsplit]
        refine (coeffNorm1_add_le _ _).trans ?_
        calc coeffNorm1 (A' ^ (r - q) * (Kq q - G q)) +
              coeffNorm1 ((A' ^ (r - q) - A ^ (r - q)) * G q)
            ≤ L ^ r * e1 + r * e * L ^ r * Gb :=
              add_le_add ((coeffNorm1_mul_le _ _).trans (mul_le_mul hpow (hK q hq')
                (coeffNorm1_nonneg _) (by positivity)))
                ((coeffNorm1_mul_le _ _).trans (mul_le_mul hdiff (hG q hq')
                (coeffNorm1_nonneg _) (by positivity)))
          _ = L ^ r * (e1 + r * e * Gb) := by ring
    _ = 2 ^ r * L ^ r * (e1 + r * e * Gb) := by
        rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- **Mixing the clusters.** `‖∑_c p_c F_c - ∑_c w_c H_c‖₁ ≤
∑_c p_c ‖F_c - H_c‖₁ + ∑_c |p_c - w_c| ‖H_c‖₁` for `p_c ≥ 0`. -/
theorem coeffNorm1_mix_sub_le {ι : Type*} (s : Finset ι) (p w : ι → ℝ) (hp : ∀ c, 0 ≤ p c)
    (F H : ι → MvPolynomial σ ℝ) :
    coeffNorm1 (∑ c ∈ s, p c • F c - ∑ c ∈ s, C (w c) * H c) ≤
      ∑ c ∈ s, p c * coeffNorm1 (F c - H c) + ∑ c ∈ s, |p c - w c| * coeffNorm1 (H c) := by
  have h : ∑ c ∈ s, p c • F c - ∑ c ∈ s, C (w c) * H c =
      ∑ c ∈ s, (p c • (F c - H c) + (p c - w c) • H c) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [← smul_eq_C_mul, smul_sub, sub_smul]
    abel
  rw [h, ← sum_add_distrib]
  refine (coeffNorm1_sum_le _ _).trans (sum_le_sum fun c _ ↦ ?_)
  refine (coeffNorm1_add_le _ _).trans ?_
  rw [coeffNorm1_smul, coeffNorm1_smul, abs_of_nonneg (hp c)]

/-! ### The sample in the whitened frame -/

/-- `⟨A g, v⟩ = ∑ᵢ gᵢ ⟨A eᵢ, v⟩`, as linear forms. -/
theorem lin_mulVec (A : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    Separating.lin (A *ᵥ g) = ∑ i, C (g i) * Separating.lin (fun l ↦ A l i) := by
  simp only [Separating.lin, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- The empirical moment polynomials of the points `A gⱼ` are those of the `gⱼ` after the
substitution `X ↦ φ`, `φᵢ = ⟨A eᵢ, X⟩`. -/
theorem empMom_mulVec (S : Finset (Fin n)) (A : Matrix (Fin d) (Fin d) ℝ)
    (g : Fin n → Fin d → ℝ) (q : ℕ) :
    Separating.empMom S (fun j ↦ A *ᵥ g j) q =
      aeval (fun i ↦ Separating.lin (fun l ↦ A l i)) (Separating.empMom S g q) := by
  rw [Separating.aeval_empMom]
  simp only [Separating.empMom, lin_mulVec]

/-- `vᵀ (W Σ Wᵀ) v = ∑ᵢ φᵢ(v)²` for the columns `φᵢ = ⟨B eᵢ, v⟩` of `B = W Σ^{1/2}`. -/
theorem quadPoly_SW_eq (M : Mixture k d) (hS : M.S.PosSemidef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    quadPoly (SW M (Separating.Wr r ω)) =
      ∑ i, Separating.lin (fun l ↦ Separating.Bm M r ω l i) ^ 2 := by
  apply MvPolynomial.funext
  intro v
  have h := Separating.Nform_eq_sum_sq M hS r ω v
  rw [Separating.Nform] at h
  rw [eval_quadPoly, SW, Fr.quad_conj, h]
  simp only [map_sum, map_pow, Separating.eval_lin, mulVec, dotProduct, transpose_apply]

variable {M : Mixture k d} {r : Rounding k d} {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)}

/-- The coordinates of the whitened centered means: `w_c ((W (μ_c - μ̄))ᵢ)² ≤ 4` when
`cov ⪯ 2 Ĉ`. -/
theorem w_mul_sq_W_center_le (hM : M.Valid)
    (hcov : ∀ v, Colinear.quad M.cov v ≤ 2 * Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    (c : Fin k) (i : Fin d) :
    M.w c * (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) i ^ 2 ≤ 4 := by
  set v : Fin d → ℝ := (Separating.Wr r ω)ᵀ *ᵥ Pi.single i 1 with hv
  have h1 : (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) i = (M.μ c - M.mean) ⬝ᵥ v := by
    rw [hv, Fr.dotProduct_transpose_mulVec, dotProduct_single, mul_one]
  have h2 := Colinear.w_mul_sq_center_le hM hM.nonneg_w v c
  have h3 := hcov v
  have h4 : Colinear.quad (Colinear.empCov (Separating.yt r ω)) v =
      (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ
        (diagonal (Separating.kappa (Colinear.empCov (Separating.yt r ω))) *ᵥ Pi.single i 1) :=
    Separating.quad_transpose_W_mulVec (Colinear.empCov_transpose _) _
  have h5 := Separating.dotProduct_diagonal_le_two_mul
    (Separating.kappa_le_two (Colinear.empCov (Separating.yt r ω))) (Pi.single i (1 : ℝ))
  have h6 : ∑ l, (Pi.single i (1 : ℝ) : Fin d → ℝ) l ^ 2 = 1 := by
    rw [sum_eq_single i (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp
  rw [h1]
  have h7 : v ⬝ᵥ (M.cov *ᵥ v) = Colinear.quad M.cov v := rfl
  linarith

/-- `‖⟨W (μ_c - μ̄), X⟩‖₁ ≤ 3 (d + 1) / √wmin` when `cov ⪯ 2 Ĉ`. -/
theorem coeffNorm1_lin_W_center_le (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c)
    (hcov : ∀ v, Colinear.quad M.cov v ≤ 2 * Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    (c : Fin k) :
    coeffNorm1 (Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean))) ≤
      3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
  have hs0 := Real.sqrt_pos.mpr hwmin
  have hs := Real.sq_sqrt hwmin.le
  have hcoord : ∀ i, |(Separating.Wr r ω *ᵥ (M.μ c - M.mean)) i| ≤ 2 / Real.sqrt wmin := by
    intro i
    set x := (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) i
    have h := w_mul_sq_W_center_le hM hcov c i
    have hwx : wmin * x ^ 2 ≤ 4 :=
      (mul_le_mul_of_nonneg_right (hw c) (sq_nonneg x)).trans h
    rw [le_div_iff₀ hs0]
    have ht : (|x| * Real.sqrt wmin) ^ 2 ≤ 2 ^ 2 := by
      rw [mul_pow, sq_abs, hs]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp ht
  refine (Separating.coeffNorm1_lin_le _).trans ?_
  calc ∑ i, |(Separating.Wr r ω *ᵥ (M.μ c - M.mean)) i| ≤ ∑ _i : Fin d, 2 / Real.sqrt wmin :=
        sum_le_sum fun i _ ↦ hcoord i
    _ = (d : ℝ) * (2 / Real.sqrt wmin) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hs0]
        linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- **The empirical moment polynomial, cluster by cluster.** If `Y j = m_{ℓ j} + ζ j` and every
cluster is nonempty, then `empPoly Y p = ∑_c (n_c/n) ∑_q C(p, q) ⟨m_c, X⟩^(p-q) M_c^q`, where
`M_c^q = empMom S_c ζ q` is the empirical `q`-th moment polynomial of `ζ` on cluster `c`. -/
theorem empPoly_eq_sum_cluster {ℓ : Fin n → Fin k} {Y ζ : Fin n → Fin d → ℝ}
    {mv : Fin k → Fin d → ℝ} (hY : ∀ j, Y j = mv (ℓ j) + ζ j)
    (hcard : ∀ c, 0 < (cluster ℓ c).card) (p : ℕ) :
    empPoly Y p = ∑ c, (((cluster ℓ c).card : ℝ) / n) •
      ∑ q ∈ range (p + 1), (p.choose q : MvPolynomial (Fin d) ℝ) *
        (Separating.lin (mv c) ^ (p - q) * Separating.empMom (cluster ℓ c) ζ q) := by
  have hc : ∀ c, ∑ j ∈ cluster ℓ c, Separating.lin (Y j) ^ p =
      ((cluster ℓ c).card : ℝ) • ∑ q ∈ range (p + 1), (p.choose q : MvPolynomial (Fin d) ℝ) *
        (Separating.lin (mv c) ^ (p - q) * Separating.empMom (cluster ℓ c) ζ q) := by
    intro c
    have hN : ((cluster ℓ c).card : ℝ) ≠ 0 := by exact_mod_cast (hcard c).ne'
    have h1 : ∑ j ∈ cluster ℓ c, Separating.lin (Y j) ^ p =
        ∑ j ∈ cluster ℓ c, (Separating.lin (mv c) + Separating.lin (ζ j)) ^ p :=
      sum_congr rfl fun j hj ↦ by
        rw [hY j, (mem_filter.mp hj).2, Separating.lin_add]
    rw [h1, sum_add_pow_eq, smul_sum]
    refine sum_congr rfl fun q _ ↦ ?_
    rw [← mul_smul_comm, ← mul_smul_comm, Separating.empMom, smul_inv_smul₀ hN]
  have hfib : ∑ j, Separating.lin (Y j) ^ p =
      ∑ c, ∑ j ∈ cluster ℓ c, Separating.lin (Y j) ^ p :=
    (sum_fiberwise univ ℓ fun j ↦ Separating.lin (Y j) ^ p).symm
  rw [empPoly, hfib, smul_sum]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [hc c, smul_smul, div_eq_inv_mul]

/-- `hmom p A (∑ᵢ φᵢ²) = ∑_q C(p, q) A^(p-q) G_q` with `G_q = gaussPoly q (φ)`. -/
theorem hmom_eq_sum_aeval_gaussPoly (A : MvPolynomial (Fin d) ℝ)
    (φ : Fin d → MvPolynomial (Fin d) ℝ) (p : ℕ) :
    hmom p A (∑ i, φ i ^ 2) = ∑ q ∈ range (p + 1), (p.choose q : MvPolynomial (Fin d) ℝ) *
      (A ^ (p - q) * aeval φ (Separating.gaussPoly q)) := by
  rw [hmom_eq_sum_choose]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Separating.aeval_gaussPoly, smul_eq_C_mul, map_natCast]
  ring

/-- **The shift.** If `∑_c n_c A_c + n Δ + ∑_c n_c K_c = 0`, `∑_c w_c A_c = 0`, the cluster
fractions are within `1 ± η` of the weights, `‖A_c‖₁ ≤ a` and `‖K_c‖₁ ≤ b`, then
`‖Δ‖₁ ≤ η a + b`. -/
theorem coeffNorm1_shift_le {ℓ : Fin n → Fin k} (hn : 0 < n) {w : Fin k → ℝ} {η a b : ℝ}
    (hsize : ∀ c, |((cluster ℓ c).card : ℝ) / n - w c| ≤ η * w c)
    {A0 Kc : Fin k → MvPolynomial σ ℝ} {Δ : MvPolynomial σ ℝ}
    (h : ∑ c, ((cluster ℓ c).card : ℝ) • A0 c + (n : ℝ) • Δ +
      ∑ c, ((cluster ℓ c).card : ℝ) • Kc c = 0)
    (hw : ∑ c, w c • A0 c = 0) (hsum : ∑ c, w c = 1) (hA : ∀ c, coeffNorm1 (A0 c) ≤ a)
    (hK : ∀ c, coeffNorm1 (Kc c) ≤ b) :
    coeffNorm1 Δ ≤ η * a + b := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : ∑ c, ((cluster ℓ c).card : ℝ) = n := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := ℓ)
      (fun _ _ ↦ mem_univ _)
    rw [card_univ, Fintype.card_fin] at h
    exact_mod_cast h.symm
  have hA' : ∑ c, ((cluster ℓ c).card : ℝ) • A0 c =
      ∑ c, (((cluster ℓ c).card : ℝ) - n * w c) • A0 c := by
    simp only [sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hw, smul_zero, sub_zero]
  have hΔ : (n : ℝ) • Δ = -(∑ c, (((cluster ℓ c).card : ℝ) - n * w c) • A0 c) -
      ∑ c, ((cluster ℓ c).card : ℝ) • Kc c := by
    rw [← hA', ← sub_eq_zero, ← h]
    abel
  have hηw : ∀ c, 0 ≤ η * w c := fun c ↦ (abs_nonneg _).trans (hsize c)
  have h1 : ∀ c, |((cluster ℓ c).card : ℝ) - n * w c| ≤ n * (η * w c) := by
    intro c
    have h := hsize c
    rw [show ((cluster ℓ c).card : ℝ) / n - w c = (((cluster ℓ c).card : ℝ) - n * w c) / n by
      field_simp, abs_div, abs_of_pos hN, div_le_iff₀ hN] at h
    linarith
  have hnorm : (n : ℝ) * coeffNorm1 Δ ≤ n * (η * a) + n * b := by
    have hl : coeffNorm1 ((n : ℝ) • Δ) = n * coeffNorm1 Δ := by
      rw [coeffNorm1_smul, abs_of_pos hN]
    rw [← hl, hΔ]
    refine (coeffNorm1_sub_le _ _).trans ?_
    rw [coeffNorm1_neg]
    refine add_le_add ((coeffNorm1_sum_le _ _).trans ?_) ((coeffNorm1_sum_le _ _).trans ?_)
    · calc ∑ c, coeffNorm1 ((((cluster ℓ c).card : ℝ) - n * w c) • A0 c)
          ≤ ∑ c, n * (η * w c) * a := by
            refine sum_le_sum fun c _ ↦ ?_
            rw [coeffNorm1_smul]
            exact mul_le_mul (h1 c) (hA c) (coeffNorm1_nonneg _) (mul_nonneg hN.le (hηw c))
        _ = n * (η * a) := by
            rw [← sum_mul, ← mul_sum, ← mul_sum, hsum]
            ring
    · calc ∑ c, coeffNorm1 (((cluster ℓ c).card : ℝ) • Kc c)
          ≤ ∑ c, ((cluster ℓ c).card : ℝ) * b := by
            refine sum_le_sum fun c _ ↦ ?_
            rw [coeffNorm1_smul, Nat.abs_cast]
            exact mul_le_mul_of_nonneg_left (hK c) (Nat.cast_nonneg _)
        _ = n * b := by rw [← sum_mul, hcard]
  exact le_of_mul_le_mul_left (hnorm.trans_eq (mul_add _ _ _).symm) hN

/-! ### Numerics -/

/-- `c (d + 1)^a (m + 1) / wmin ≤ Q` for `c ≤ 10⁶` and `a ≤ 6`. -/
theorem le_mpBase {d m : ℕ} {wmin : ℝ} (hw0 : 0 < wmin) {c : ℝ} (hc : c ≤ 10 ^ 6) {a : ℕ}
    (ha : a ≤ 6) :
    c * ((d : ℝ) + 1) ^ a * ((m : ℝ) + 1) / wmin ≤ mpBase d m wmin := by
  unfold mpBase
  have hx : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  gcongr

/-- `z ≤ z / w` for `z ≥ 0` and `0 < w ≤ 1`. -/
theorem le_div_of_le_one {z w : ℝ} (hz : 0 ≤ z) (hw0 : 0 < w) (hw1 : w ≤ 1) : z ≤ z / w := by
  rw [le_div_iff₀ hw0]
  nlinarith

/-- The elementary bounds on the base `Q`, with `β = 3 (d + 1) / √wmin`. -/
theorem mpBase_facts {d m : ℕ} {wmin : ℝ} (hw0 : 0 < wmin) (hw1 : wmin ≤ 1) :
    3 ≤ mpBase d m wmin ∧ 2 * (m : ℝ) ≤ mpBase d m wmin ∧
      4 * ((d : ℝ) + 1) * (2 * m + 1) ≤ mpBase d m wmin ∧
      (3 * ((d : ℝ) + 1) / Real.sqrt wmin) ^ 2 ≤ mpBase d m wmin ∧
      2 * m * ((d : ℝ) + 1) * (3 * ((d : ℝ) + 1) / Real.sqrt wmin) ≤ mpBase d m wmin ∧
      (2 * (131 * ((d : ℝ) + 1) ^ 2 * (3 * ((d : ℝ) + 1) / Real.sqrt wmin))) ^ 2 ≤
        mpBase d m wmin ∧
      65 * ((d : ℝ) + 1) ^ 2 * (3 * ((d : ℝ) + 1) / Real.sqrt wmin) ≤ mpBase d m wmin := by
  set x : ℝ := (d : ℝ) + 1 with hx
  set y : ℝ := (m : ℝ) + 1 with hy
  have hx1 : 1 ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hy1 : 1 ≤ y := by rw [hy]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hs0 := Real.sqrt_pos.mpr hw0
  set β := 3 * x / Real.sqrt wmin with hβ
  have hβsq : β ^ 2 = 9 * x ^ 2 / wmin := by
    rw [hβ, div_pow, Real.sq_sqrt hw0.le]
    ring
  have hβ1 : 1 ≤ β := by
    have hs1 : Real.sqrt wmin ≤ 1 := by
      have := Real.sqrt_le_sqrt hw1
      rwa [Real.sqrt_one] at this
    rw [hβ, le_div_iff₀ hs0]
    nlinarith
  have hββ : β ≤ β ^ 2 := by nlinarith
  have hxy : ∀ (c : ℝ) (a : ℕ), c ≤ 10 ^ 6 → a ≤ 6 →
      c * x ^ a * y / wmin ≤ mpBase d m wmin := fun c a hc ha ↦ le_mpBase hw0 hc ha
  have hdiv : ∀ z : ℝ, 0 ≤ z → z ≤ z / wmin := fun z hz ↦ le_div_of_le_one hz hw0 hw1
  have hxa : ∀ a : ℕ, 0 ≤ x ^ a := fun a ↦ pow_nonneg (by linarith) a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ (hxy 3 0 (by norm_num) (by norm_num))
    refine le_trans ?_ (hdiv _ (by positivity))
    rw [pow_zero]
    nlinarith
  · refine le_trans ?_ (hxy 2 0 (by norm_num) (by norm_num))
    refine le_trans ?_ (hdiv _ (by positivity))
    rw [pow_zero]
    linarith
  · refine le_trans ?_ (hxy 8 1 (by norm_num) (by norm_num))
    refine le_trans ?_ (hdiv _ (by positivity))
    rw [pow_one]
    nlinarith
  · rw [hβsq]
    refine le_trans ?_ (hxy 9 2 (by norm_num) (by norm_num))
    rw [div_le_div_iff_of_pos_right hw0]
    nlinarith [hxa 2]
  · calc 2 * (m : ℝ) * x * β ≤ 2 * y * x * β ^ 2 := by
          have h1 : 2 * (m : ℝ) * x ≤ 2 * y * x := by nlinarith
          exact mul_le_mul h1 hββ (by linarith) (by nlinarith)
      _ = 18 * x ^ 3 * y / wmin := by rw [hβsq]; ring
      _ ≤ mpBase d m wmin := hxy 18 3 (by norm_num) (by norm_num)
  · calc (2 * (131 * x ^ 2 * β)) ^ 2 = 617796 * x ^ 6 / wmin := by
          rw [mul_pow, mul_pow, mul_pow, hβsq]
          ring
      _ ≤ 617796 * x ^ 6 * y / wmin := by
          rw [div_le_div_iff_of_pos_right hw0]
          nlinarith [hxa 6]
      _ ≤ mpBase d m wmin := hxy 617796 6 (by norm_num) (by norm_num)
  · calc 65 * x ^ 2 * β ≤ 65 * x ^ 2 * β ^ 2 :=
          mul_le_mul_of_nonneg_left hββ (by nlinarith [hxa 2])
      _ = 585 * x ^ 4 / wmin := by rw [hβsq]; ring
      _ ≤ 585 * x ^ 4 * y / wmin := by
          rw [div_le_div_iff_of_pos_right hw0]
          nlinarith [hxa 4]
      _ ≤ mpBase d m wmin := hxy 585 4 (by norm_num) (by norm_num)

/-- The final arithmetic of the error bound. -/
theorem numerics {ε0 η Q L e : ℝ} {m : ℕ} (hm : 1 ≤ m) (hQ : 3 ≤ Q) (hε0 : 0 ≤ ε0)
    (hη : 0 ≤ η) (hηε : η ≤ ε0) (hL : 0 ≤ L) (h2L : (2 * L) ^ 2 ≤ Q) (he0 : 0 ≤ e)
    (he : e ≤ ε0 * Q) (hmQ : 2 * (m : ℝ) ≤ Q) :
    2 ^ (2 * m) * L ^ (2 * m) * (ε0 * Q ^ (3 * m + 1) + ((2 * m : ℕ) : ℝ) * e * Q ^ (2 * m)) +
        η * (2 ^ (2 * m) * L ^ (2 * m) * Q ^ (2 * m)) ≤ ε0 * Q ^ (4 * m + 2) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hP : 2 ^ (2 * m) * L ^ (2 * m) ≤ Q ^ m := by
    rw [← mul_pow, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2L m
  have hP0 : 0 ≤ 2 ^ (2 * m) * L ^ (2 * m) := by positivity
  have h1 : ((2 * m : ℕ) : ℝ) * e * Q ^ (2 * m) ≤ ε0 * Q ^ (3 * m + 1) := by
    push_cast
    calc 2 * (m : ℝ) * e * Q ^ (2 * m) ≤ Q * (ε0 * Q) * Q ^ (2 * m) := by
          gcongr
      _ = ε0 * Q ^ (2 * m + 2) := by ring
      _ ≤ ε0 * Q ^ (3 * m + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ1 (by omega)) hε0
  have h2 : η * Q ^ (2 * m) ≤ ε0 * Q ^ (3 * m + 1) :=
    mul_le_mul hηε (pow_le_pow_right₀ hQ1 (by omega)) (by positivity) hε0
  calc 2 ^ (2 * m) * L ^ (2 * m) * (ε0 * Q ^ (3 * m + 1) + ((2 * m : ℕ) : ℝ) * e * Q ^ (2 * m)) +
        η * (2 ^ (2 * m) * L ^ (2 * m) * Q ^ (2 * m))
      = 2 ^ (2 * m) * L ^ (2 * m) * (ε0 * Q ^ (3 * m + 1) +
          ((2 * m : ℕ) : ℝ) * e * Q ^ (2 * m) + η * Q ^ (2 * m)) := by ring
    _ ≤ Q ^ m * (3 * (ε0 * Q ^ (3 * m + 1))) := by
        refine mul_le_mul hP (by linarith) (by positivity) (by positivity)
    _ = 3 * (ε0 * Q ^ (4 * m + 1)) := by ring
    _ ≤ Q * (ε0 * Q ^ (4 * m + 1)) := by
        gcongr
    _ = ε0 * Q ^ (4 * m + 2) := by ring

/-! ### The shift of the means -/

/-- `⟨m_c, X⟩ = ⟨W (μ_c - μ̄), X⟩ + ⟨W (μ̄ - ȳ), X⟩`. -/
theorem lin_mc_eq (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (c : Fin k) :
    Separating.lin (Separating.mc M r ω c) =
      Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) +
        Separating.lin (Separating.Wr r ω *ᵥ (M.mean - Colinear.mean (Separating.yt r ω))) := by
  rw [← Separating.lin_add, ← mulVec_add, sub_add_sub_cancel, Separating.mc]

/-- `∑_c w_c ⟨W (μ_c - μ̄), X⟩ = 0`. -/
theorem sum_w_smul_lin_W_center (hM : M.Valid) (W : Matrix (Fin d) (Fin d) ℝ) :
    ∑ c, M.w c • Separating.lin (W *ᵥ (M.μ c - M.mean)) = 0 := by
  have h := congrArg (fun v ↦ Separating.lin (W *ᵥ v)) (Colinear.sum_w_smul_center M hM)
  simp only [mulVec_sum, mulVec_smul, Separating.lin_sum, Separating.lin_smul, mulVec_zero,
    Separating.lin_zero] at h
  simpa [smul_eq_C_mul] using h

/-- **The whitened points sum to zero**, written cluster by cluster:
`∑_c n_c ⟨W (μ_c - μ̄), X⟩ + n ⟨W (μ̄ - ȳ), X⟩ + ∑_c n_c M_c^1 = 0`, where `M_c^1` is the
empirical mean of `⟨ζⱼ, X⟩` on cluster `c`. -/
theorem sum_lin_whiten_eq_zero (hS : M.S.PosDef)
    (hcard : ∀ c, 0 < (cluster (labels ω) c).card) :
    ∑ c, ((cluster (labels ω) c).card : ℝ) •
        Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) +
      (n : ℝ) • Separating.lin (Separating.Wr r ω *ᵥ (M.mean - Colinear.mean (Separating.yt r ω))) +
      ∑ c, ((cluster (labels ω) c).card : ℝ) •
        Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) 1 = 0 := by
  set A0 : Fin k → MvPolynomial (Fin d) ℝ :=
    fun c ↦ Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean))
  set Δ := Separating.lin (Separating.Wr r ω *ᵥ (M.mean - Colinear.mean (Separating.yt r ω)))
  have h0 : ∑ j, Separating.lin (Separating.whiten (Separating.yt r ω) j) = 0 := by
    rw [← Separating.lin_sum]
    simp only [Separating.whiten_eq_mulVec]
    rw [← mulVec_sum, Separating.sum_sub_mean, mulVec_zero, Separating.lin_zero]
  have h1 : ∀ j, Separating.lin (Separating.whiten (Separating.yt r ω) j) =
      A0 (labels ω j) + Δ + Separating.lin (Separating.zeta M r ω j) := by
    intro j
    rw [Separating.whiten_yt M hS, Separating.lin_add, lin_mc_eq]
  rw [sum_congr rfl fun j _ ↦ h1 j, sum_add_distrib, sum_add_distrib] at h0
  have h2 : ∑ j, A0 (labels ω j) = ∑ c, ((cluster (labels ω) c).card : ℝ) • A0 c := by
    rw [← sum_fiberwise' univ (labels ω) A0]
    exact sum_congr rfl fun c _ ↦ (sum_const _).trans (Nat.cast_smul_eq_nsmul ℝ _ _).symm
  have h3 : ∑ _j : Fin n, Δ = (n : ℝ) • Δ := by
    rw [sum_const, card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have h4 : ∑ j, Separating.lin (Separating.zeta M r ω j) = ∑ c, ((cluster (labels ω) c).card : ℝ) •
      Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) 1 := by
    rw [← sum_fiberwise univ (labels ω)]
    refine sum_congr rfl fun c _ ↦ ?_
    have hN : ((cluster (labels ω) c).card : ℝ) ≠ 0 := by exact_mod_cast (hcard c).ne'
    rw [Separating.empMom, smul_inv_smul₀ hN]
    simp only [pow_one]
    rfl
  rw [h2, h3, h4] at h0
  exact h0

/-! ### Homogeneity -/

/-- `vᵀ S v` is homogeneous of degree `2`. -/
theorem isHomogeneous_quadPoly (S : Matrix (Fin d) (Fin d) ℝ) : (quadPoly S).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun a _ ↦ IsHomogeneous.sum _ _ _ fun b _ ↦ by
    rw [mul_assoc]
    exact ((isHomogeneous_X ℝ a).mul (isHomogeneous_X ℝ b)).C_mul _

/-- `hmom p A N` is homogeneous of degree `p` for `A` of degree `1` and `N` of degree `2`. -/
theorem isHomogeneous_hmom {A N : MvPolynomial σ ℝ} (hA : A.IsHomogeneous 1)
    (hN : N.IsHomogeneous 2) (p : ℕ) : (hmom p A N).IsHomogeneous p := by
  unfold hmom
  refine IsHomogeneous.sum _ _ _ fun i hi ↦ ?_
  have hi' : 2 * i ≤ p := by
    have := mem_range.mp hi
    omega
  rw [← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), mul_assoc]
  have h := ((hA.pow (p - 2 * i)).mul (hN.pow i)).C_mul ((hermCoeff p i : ℕ) : ℝ)
  convert h using 1
  omega

/-- `empPoly Y p` is homogeneous of degree `p`. -/
theorem isHomogeneous_empPoly (Y : Fin n → Fin d → ℝ) (p : ℕ) :
    (empPoly Y p).IsHomogeneous p := by
  rw [empPoly, smul_eq_C_mul]
  refine IsHomogeneous.C_mul (IsHomogeneous.sum _ _ _ fun j _ ↦ ?_) _
  simpa using (Separating.isHomogeneous_lin (Y j)).pow p

/-- `popPoly w a u S p` is homogeneous of degree `p`. -/
theorem isHomogeneous_popPoly (w a : Fin k → ℝ) (u : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (p : ℕ) : (popPoly w a u S p).IsHomogeneous p :=
  IsHomogeneous.sum _ _ _ fun c _ ↦ (isHomogeneous_hmom ((Separating.isHomogeneous_lin u).C_mul
    (a c)) (isHomogeneous_quadPoly S) p).C_mul (w c)

/-- `empPoly Y 0 = 1` for `n > 0`. -/
theorem empPoly_zero (Y : Fin n → Fin d → ℝ) (hn : 0 < n) : empPoly Y 0 = 1 := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [empPoly]
  simp only [pow_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [smul_eq_C_mul, ← map_natCast (C : ℝ →+* MvPolynomial (Fin d) ℝ), ← C_mul,
    inv_mul_cancel₀ hN, C_1]

/-- `popPoly w a u S 0 = 1` for weights summing to `1`. -/
theorem popPoly_zero {w a : Fin k → ℝ} (hw : ∑ c, w c = 1) (u : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) : popPoly w a u S 0 = 1 := by
  simp only [popPoly, hmom_zero, mul_one]
  rw [← map_sum, hw, C_1]

/-! ### Assembly -/

/-- `E Z^q ≤ q^q`. -/
theorem gaussMom_le_self_pow (q : ℕ) : gaussMom q ≤ q ^ q := by
  unfold gaussMom
  split_ifs
  · exact (Nat.doubleFactorial_le_factorial _).trans
      ((Nat.factorial_le (by omega)).trans (Nat.factorial_le_pow q))
  · exact Nat.zero_le _

/-- **Assembly.** The bound of `coeffNorm1_sum_choose_sub_le` in every cluster, mixed with
`coeffNorm1_mix_sub_le`, with cluster fractions `p_c` within `1 ± η` of the weights `w_c`. -/
theorem assemble {ι : Type*} (s : Finset ι) {p w : ι → ℝ} {η : ℝ} (hp : ∀ c, 0 ≤ p c)
    (hps : ∑ c ∈ s, p c = 1) (hws : ∑ c ∈ s, w c = 1) (hpw : ∀ c, |p c - w c| ≤ η * w c)
    {A A' : ι → MvPolynomial σ ℝ} {Kc : ι → ℕ → MvPolynomial σ ℝ} {G : ℕ → MvPolynomial σ ℝ}
    (r : ℕ) {a e L e1 Gb : ℝ} (hA : ∀ c, coeffNorm1 (A c) ≤ a)
    (hE : ∀ c, coeffNorm1 (A' c - A c) ≤ e) (hL : a + e ≤ L) (haL : a ≤ L) (hL1 : 1 ≤ L)
    (hK : ∀ c q, q ≤ r → coeffNorm1 (Kc c q - G q) ≤ e1)
    (hG : ∀ q ≤ r, coeffNorm1 (G q) ≤ Gb) :
    coeffNorm1 (∑ c ∈ s, p c • ∑ q ∈ range (r + 1),
          (r.choose q : MvPolynomial σ ℝ) * (A' c ^ (r - q) * Kc c q) -
        ∑ c ∈ s, C (w c) * ∑ q ∈ range (r + 1),
          (r.choose q : MvPolynomial σ ℝ) * (A c ^ (r - q) * G q)) ≤
      2 ^ r * L ^ r * (e1 + r * e * Gb) + η * (2 ^ r * L ^ r * Gb) := by
  refine (coeffNorm1_mix_sub_le s p w hp _ _).trans (add_le_add ?_ ?_)
  · refine (sum_le_sum fun c _ ↦ mul_le_mul_of_nonneg_left
      (coeffNorm1_sum_choose_sub_le r (hA c) (hE c) hL hL1 (hK c) hG) (hp c)).trans_eq ?_
    rw [← sum_mul, hps, one_mul]
  · refine (sum_le_sum fun c _ ↦ mul_le_mul (hpw c)
      (coeffNorm1_sum_choose_le r ((hA c).trans haL) hL1 hG) (coeffNorm1_nonneg _)
      ((abs_nonneg _).trans (hpw c))).trans_eq ?_
    rw [← sum_mul, ← mul_sum, hws, mul_one]

/-! ### The hypotheses -/

/-- The columns `φᵢ = ⟨B eᵢ, X⟩` of `B = W Σ^{1/2}`: `⟨ζⱼ, X⟩ = ∑ᵢ ĝⱼᵢ φᵢ`. -/
noncomputable def phi (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Fin d → MvPolynomial (Fin d) ℝ :=
  fun i ↦ Separating.lin fun l ↦ Separating.Bm M r ω l i

/-- The hypotheses of the finite-sample transfer: a valid mixture with weights at least
`wmin > 0`; `n ≥ d`, `n > 0` sample points rounded within `1/n`; the good event with
`2η ≤ wmin`; the covariance comparisons `(wmin/4) Σ ⪯ Ĉ` (CV1) and `cov ⪯ 2 Ĉ`. -/
structure Hyp (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (wmin η : ℝ) (D : ℕ) : Prop where
  valid : M.Valid
  wmin_pos : 0 < wmin
  w_ge : ∀ c, wmin ≤ M.w c
  n_pos : 0 < n
  d_le : d ≤ n
  round : IsRounding M.S (1 / n) r
  good : GoodNoise M.w η D (labels ω) (stdNoise M ω)
  eta_le : 2 * η ≤ wmin
  cv1 : ∀ v, wmin / 4 * Colinear.quad M.S v ≤
    Colinear.quad (Colinear.empCov (Separating.yt r ω)) v
  cov : ∀ v, Colinear.quad M.cov v ≤ 2 * Colinear.quad (Colinear.empCov (Separating.yt r ω)) v

namespace Hyp

variable {wmin η : ℝ} {D : ℕ}

theorem wmin_le_one (H : Hyp M r ω wmin η D) : wmin ≤ 1 :=
  Colinear.wmin_le_one H.valid H.wmin_pos H.w_ge

theorem w_pos (H : Hyp M r ω wmin η D) (c : Fin k) : 0 < M.w c :=
  H.wmin_pos.trans_le (H.w_ge c)

theorem two_eta_le_one (H : Hyp M r ω wmin η D) : 2 * η ≤ 1 :=
  H.eta_le.trans H.wmin_le_one

theorem eta_nonneg (H : Hyp M r ω wmin η D) : 0 ≤ η := by
  have h := (abs_nonneg _).trans (H.good.1 (labels ω ⟨0, H.n_pos⟩))
  exact nonneg_of_mul_nonneg_left h (H.w_pos _)

/-- Every cluster is nonempty on the good event. -/
theorem card_pos (H : Hyp M r ω wmin η D) (c : Fin k) : 0 < (cluster (labels ω) c).card :=
  (Separating.card_pos_of_goodNoise H.good c (H.w_pos c) H.two_eta_le_one).1

theorem eps_nonneg (H : Hyp M r ω wmin η D) : 0 ≤ 2 * η / wmin + 1 / n := by
  have := H.eta_nonneg
  have := H.wmin_pos
  positivity

/-- `η ≤ 2η/wmin + 1/n`. -/
theorem eta_le_eps (H : Hyp M r ω wmin η D) : η ≤ 2 * η / wmin + 1 / n := by
  have h1 : η ≤ 2 * η / wmin := by
    rw [le_div_iff₀ H.wmin_pos]
    nlinarith [H.wmin_le_one, H.eta_nonneg]
  have : 0 ≤ 1 / (n : ℝ) := by positivity
  linarith

/-- `2η/wmin + 1/n ≤ 2`. -/
theorem eps_le_two (H : Hyp M r ω wmin η D) : 2 * η / wmin + 1 / n ≤ 2 := by
  have h1 : 2 * η / wmin ≤ 1 := by rw [div_le_one H.wmin_pos]; exact H.eta_le
  have h2 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast H.n_pos)]
    exact_mod_cast H.n_pos
  linarith

/-- `2η/w_c + 1/n ≤ 2η/wmin + 1/n`. -/
theorem eps_c_le (H : Hyp M r ω wmin η D) (c : Fin k) :
    2 * η / M.w c + 1 / n ≤ 2 * η / wmin + 1 / n := by
  have : 2 * η / M.w c ≤ 2 * η / wmin :=
    div_le_div_of_nonneg_left (by linarith [H.eta_nonneg]) H.wmin_pos (H.w_ge c)
  linarith

/-- `β = 3 (d + 1) / √wmin ≥ 1`. -/
theorem one_le_beta (H : Hyp M r ω wmin η D) : 1 ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
  have hs0 := Real.sqrt_pos.mpr H.wmin_pos
  have hs1 : Real.sqrt wmin ≤ 1 := by
    have := Real.sqrt_le_sqrt H.wmin_le_one
    rwa [Real.sqrt_one] at this
  rw [le_div_iff₀ hs0]
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- The columns of `B` have `‖φᵢ‖₁ ≤ β` (CV1). -/
theorem coeffNorm1_phi_le (H : Hyp M r ω wmin η D) (i : Fin d) :
    coeffNorm1 (phi M r ω i) ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin :=
  (Separating.coeffNorm1_lin_le _).trans
    (Separating.sum_abs_Bm_col_le H.valid.posDef.posSemidef H.wmin_pos H.cv1 i)

/-- **Moment closeness of the whitened noise** on cluster `c`, after the substitution `X ↦ φ`:
`‖M_c^q - gaussPoly q (φ)‖₁ ≤ (2η/w_c + 1/n) (4 (d + 1) (q + 1))^(q + 1) β^q`. -/
theorem coeffNorm1_empMom_sub_le (H : Hyp M r ω wmin η D) (c : Fin k) {q : ℕ} (hq : q ≤ D) :
    coeffNorm1 (Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) q -
        aeval (phi M r ω) (Separating.gaussPoly q)) ≤
      (2 * η / M.w c + 1 / n) * (4 * (d + 1) * (q + 1)) ^ (q + 1) *
        (3 * ((d : ℝ) + 1) / Real.sqrt wmin) ^ q := by
  have hghat : Separating.ghat M r ω = stdNoise M ω + Separating.roundErr M r ω :=
    funext (Separating.ghat_eq M r ω)
  have hK : Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) q =
      aeval (phi M r ω) (Separating.empMom (cluster (labels ω) c)
        (stdNoise M ω + Separating.roundErr M r ω) q) := by
    rw [← hghat]
    exact empMom_mulVec _ _ _ q
  rw [hK]
  exact Separating.coeffNorm1_aeval_empMom_sub_le H.good c (H.w_pos c) H.two_eta_le_one
    (H.eta_le.trans (H.w_ge c)) H.d_le (Separating.sum_sq_roundErr_le M H.valid.posDef H.round ω)
    hq (phi M r ω) (by linarith [H.one_le_beta]) H.coeffNorm1_phi_le

/-- `‖M_c^q - gaussPoly q (φ)‖₁ ≤ (2η/wmin + 1/n) Q^(3m+1)` for `q ≤ 2m ≤ D`. -/
theorem coeffNorm1_empMom_sub_le_pow (H : Hyp M r ω wmin η D) {m : ℕ} (hm : 2 * m ≤ D)
    (c : Fin k) {q : ℕ} (hq : q ≤ 2 * m) :
    coeffNorm1 (Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) q -
        aeval (phi M r ω) (Separating.gaussPoly q)) ≤
      (2 * η / wmin + 1 / n) * mpBase d m wmin ^ (3 * m + 1) := by
  obtain ⟨hQ3, -, hQb1, hQβ, -, -, -⟩ := mpBase_facts (d := d) (m := m) H.wmin_pos H.wmin_le_one
  have hβ1 := H.one_le_beta
  set β := 3 * ((d : ℝ) + 1) / Real.sqrt wmin
  set Q := mpBase d m wmin
  refine (H.coeffNorm1_empMom_sub_le c (hq.trans hm)).trans ?_
  have hq' : (q : ℝ) ≤ 2 * m := by exact_mod_cast hq
  have h1 : (4 * ((d : ℝ) + 1) * (q + 1)) ^ (q + 1) ≤ Q ^ (2 * m + 1) := by
    refine (pow_le_pow_left₀ (by positivity) ?_ _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
    refine le_trans ?_ hQb1
    have : (0 : ℝ) ≤ 4 * ((d : ℝ) + 1) := by positivity
    nlinarith
  have h2 : β ^ q ≤ Q ^ m := by
    calc β ^ q ≤ β ^ (2 * m) := pow_le_pow_right₀ hβ1 hq
      _ = (β ^ 2) ^ m := by rw [pow_mul]
      _ ≤ Q ^ m := pow_le_pow_left₀ (by positivity) hQβ m
  calc (2 * η / M.w c + 1 / n) * (4 * (d + 1) * (q + 1)) ^ (q + 1) * β ^ q
      ≤ (2 * η / wmin + 1 / n) * Q ^ (2 * m + 1) * Q ^ m :=
        mul_le_mul (mul_le_mul (H.eps_c_le c) h1 (by positivity) H.eps_nonneg) h2
          (by positivity) (by have := H.eps_nonneg; positivity)
    _ = (2 * η / wmin + 1 / n) * Q ^ (3 * m + 1) := by ring

/-- The empirical mean of the whitened noise on cluster `c` is small:
`‖M_c^1‖₁ ≤ (2η/wmin + 1/n) · 64 (d + 1)² β`. -/
theorem coeffNorm1_empMom_one_le (H : Hyp M r ω wmin η D) (hD : 1 ≤ D) (c : Fin k) :
    coeffNorm1 (Separating.empMom (cluster (labels ω) c) (Separating.zeta M r ω) 1) ≤
      (2 * η / wmin + 1 / n) * (64 * ((d : ℝ) + 1) ^ 2 * (3 * ((d : ℝ) + 1) / Real.sqrt wmin)) := by
  have hG1 : aeval (phi M r ω) (Separating.gaussPoly 1) = 0 := by
    simp [Separating.gaussPoly, gaussMom]
  have h := H.coeffNorm1_empMom_sub_le c hD
  rw [hG1, sub_zero] at h
  refine h.trans ?_
  have hβ1 := H.one_le_beta
  have e1 : (4 * ((d : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1)) ^ (1 + 1) *
      (3 * ((d : ℝ) + 1) / Real.sqrt wmin) ^ 1 =
      64 * ((d : ℝ) + 1) ^ 2 * (3 * ((d : ℝ) + 1) / Real.sqrt wmin) := by
    push_cast
    ring
  rw [mul_assoc, e1]
  exact mul_le_mul_of_nonneg_right (H.eps_c_le c) (by positivity)

/-- The Gaussian moment polynomials: `‖gaussPoly q (φ)‖₁ ≤ Q^(2m)` for `q ≤ 2m`, `m ≥ 1`. -/
theorem coeffNorm1_gauss_le (H : Hyp M r ω wmin η D) {m : ℕ} (hm1 : 1 ≤ m) {q : ℕ}
    (hq : q ≤ 2 * m) :
    coeffNorm1 (aeval (phi M r ω) (Separating.gaussPoly q)) ≤ mpBase d m wmin ^ (2 * m) := by
  obtain ⟨-, -, -, -, hQb3, -, -⟩ := mpBase_facts (d := d) (m := m) H.wmin_pos H.wmin_le_one
  have hβ1 := H.one_le_beta
  set β := 3 * ((d : ℝ) + 1) / Real.sqrt wmin
  refine (Separating.coeffNorm1_aeval_gaussPoly_le (phi M r ω) (by linarith)
    H.coeffNorm1_phi_le q).trans ?_
  have hgm : (gaussMom q : ℝ) ≤ (2 * m : ℝ) ^ q := by
    have h := gaussMom_le_self_pow q
    have h' : q ^ q ≤ (2 * m) ^ q := Nat.pow_le_pow_left hq q
    exact_mod_cast h.trans h'
  have hx1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hdq : (d : ℝ) ^ (q / 2) ≤ ((d : ℝ) + 1) ^ q :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _).trans
      (pow_le_pow_right₀ hx1 (Nat.div_le_self q 2))
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hb3 : 1 ≤ 2 * (m : ℝ) * ((d : ℝ) + 1) * β := by
    have h2 : (1 : ℝ) ≤ 2 * (m : ℝ) * ((d : ℝ) + 1) := by nlinarith
    nlinarith
  calc (gaussMom q : ℝ) * (d : ℝ) ^ (q / 2) * β ^ q
      ≤ (2 * m : ℝ) ^ q * ((d : ℝ) + 1) ^ q * β ^ q := by gcongr
    _ = (2 * m * ((d : ℝ) + 1) * β) ^ q := by simp only [mul_pow]
    _ ≤ (2 * m * ((d : ℝ) + 1) * β) ^ (2 * m) := pow_le_pow_right₀ hb3 hq
    _ ≤ mpBase d m wmin ^ (2 * m) := pow_le_pow_left₀ (by linarith) hQb3 _

/-- **The shift** `δ = W (μ̄ - ȳ)` is small: `‖⟨δ, X⟩‖₁ ≤ (2η/wmin + 1/n) · 65 (d + 1)² β`. -/
theorem coeffNorm1_shift_le' (H : Hyp M r ω wmin η D) (hD : 1 ≤ D) :
    coeffNorm1 (Separating.lin
        (Separating.Wr r ω *ᵥ (M.mean - Colinear.mean (Separating.yt r ω)))) ≤
      (2 * η / wmin + 1 / n) * (65 * ((d : ℝ) + 1) ^ 2 * (3 * ((d : ℝ) + 1) / Real.sqrt wmin)) := by
  have hβ1 := H.one_le_beta
  set β := 3 * ((d : ℝ) + 1) / Real.sqrt wmin
  have h := coeffNorm1_shift_le H.n_pos H.good.1 (sum_lin_whiten_eq_zero H.valid.posDef H.card_pos)
    (sum_w_smul_lin_W_center H.valid (Separating.Wr r ω)) H.valid.sum_w
    (coeffNorm1_lin_W_center_le H.valid H.wmin_pos H.w_ge H.cov) (H.coeffNorm1_empMom_one_le hD)
  refine h.trans ?_
  have hx1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have : η * β ≤ (2 * η / wmin + 1 / n) * (((d : ℝ) + 1) ^ 2 * β) :=
    mul_le_mul H.eta_le_eps (le_mul_of_one_le_left (by linarith) hx1) (by linarith)
      H.eps_nonneg
  nlinarith

end Hyp

/-- **The finite-sample transfer** for `m ≥ 1` (see
`BS23.ColinearSoS.coeffNorm1_empPoly_sub_popPoly_le`). -/
theorem coeffNorm1_empPoly_sub_popPoly_le_of_pos {wmin η : ℝ} {D : ℕ}
    (H : Hyp M r ω wmin η D) {base u0 : Fin d → ℝ} {t : Fin k → ℝ} (hu0 : u0 ≠ 0)
    (hμ : ∀ c, M.μ c = base + t c • u0) {m : ℕ} (hm1 : 1 ≤ m) (hm : 2 * m ≤ D) :
    coeffNorm1 (empPoly (Separating.whiten (Separating.yt r ω)) (2 * m) -
        popPoly M.w (acoef M u0 t) (uhat M (Separating.Wr r ω) u0) (SW M (Separating.Wr r ω))
          (2 * m)) ≤ errMP d m wmin η n := by
  have hS := H.valid.posDef
  have hN : (0 : ℝ) < n := by exact_mod_cast H.n_pos
  have hβ1 := H.one_le_beta
  obtain ⟨hQ3, hQm, -, -, -, hQL, hQe⟩ := mpBase_facts (d := d) (m := m) H.wmin_pos H.wmin_le_one
  have hx1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set β := 3 * ((d : ℝ) + 1) / Real.sqrt wmin with hβ
  set ε0 := 2 * η / wmin + 1 / n with hε0
  have hε0_0 : 0 ≤ ε0 := H.eps_nonneg
  set e := ε0 * (65 * ((d : ℝ) + 1) ^ 2 * β) with he_def
  set L := 131 * ((d : ℝ) + 1) ^ 2 * β with hL_def
  have hL1 : 1 ≤ L := by nlinarith
  have hβL : β ≤ L := by nlinarith
  have haeL : β + e ≤ L := by
    have h1 : e ≤ 2 * (65 * ((d : ℝ) + 1) ^ 2 * β) :=
      mul_le_mul_of_nonneg_right H.eps_le_two (by positivity)
    have h2 : β ≤ ((d : ℝ) + 1) ^ 2 * β := le_mul_of_one_le_left (by linarith) hx1
    rw [hL_def]
    linarith
  have hE : ∀ c, coeffNorm1 (Separating.lin (Separating.mc M r ω c) -
      Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean))) ≤ e := fun c ↦ by
    rw [lin_mc_eq, add_sub_cancel_left]
    exact H.coeffNorm1_shift_le' (by omega)
  have hpop : popPoly M.w (acoef M u0 t) (uhat M (Separating.Wr r ω) u0)
      (SW M (Separating.Wr r ω)) (2 * m) =
      ∑ c, C (M.w c) * ∑ q ∈ range (2 * m + 1), ((2 * m).choose q : MvPolynomial (Fin d) ℝ) *
        (Separating.lin (Separating.Wr r ω *ᵥ (M.μ c - M.mean)) ^ (2 * m - q) *
          aeval (phi M r ω) (Separating.gaussPoly q)) := by
    unfold popPoly
    refine sum_congr rfl fun c _ ↦ ?_
    rw [quadPoly_SW_eq M hS.posSemidef r ω, hmom_eq_sum_aeval_gaussPoly,
      W_mulVec_center H.valid hu0 hμ, Separating.lin_smul]
    rfl
  have hcs : ∑ c, ((cluster (labels ω) c).card : ℝ) / n = 1 := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ)
      (f := labels ω) (fun _ _ ↦ mem_univ _)
    rw [card_univ, Fintype.card_fin] at h
    have h' : ∑ c, ((cluster (labels ω) c).card : ℝ) = n := by exact_mod_cast h.symm
    rw [← sum_div, h', div_self hN.ne']
  rw [empPoly_eq_sum_cluster (Separating.whiten_yt M hS r ω) H.card_pos (2 * m), hpop]
  have hA := assemble univ (p := fun c ↦ ((cluster (labels ω) c).card : ℝ) / n)
    (fun c ↦ by positivity) hcs H.valid.sum_w H.good.1 (2 * m)
    (coeffNorm1_lin_W_center_le H.valid H.wmin_pos H.w_ge H.cov) hE haeL hβL hL1
    (fun c q hq ↦ H.coeffNorm1_empMom_sub_le_pow hm c (q := q) hq)
    (fun q hq ↦ H.coeffNorm1_gauss_le hm1 (q := q) hq)
  refine hA.trans ?_
  have hL0 : 0 ≤ L := by linarith
  have he0 : 0 ≤ e := by positivity
  exact numerics hm1 hQ3 hε0_0 H.eta_nonneg H.eta_le_eps hL0 hQL he0
    (mul_le_mul_of_nonneg_left hQe hε0_0) hQm

end MP

/-- **Finite-sample transfer** [BS23, §5]. Let `M` be a valid mixture with means
`μ_c = base + t_c u₀` (`u₀ ≠ 0`) and weights at least `wmin > 0`, and let `ω` be a sample of size
`n ≥ d`, `n > 0`, rounded within `1/n` by `r`, on the good event of degree `D` and accuracy `η` with
`2η ≤ wmin`, such that `(wmin/4) Σ ⪯ Ĉ` (CV1) and `cov ⪯ 2 Ĉ` for the empirical covariance `Ĉ`
of the rounded points. Then for `2m ≤ D` the empirical moment polynomial of degree `2m` of the
whitened rounded points is close to the moment polynomial of the whitened mixture
`∑_c w_c N(a_c ŭ, Σ_W)` in coefficient norm:
`‖empPoly X (2m) - popPoly w a ŭ Σ_W (2m)‖₁ ≤ (2η/wmin + 1/n) Q^(4m+2)`,
`Q = 10⁶ (d + 1)⁶ (m + 1) / wmin` (`BS23.ColinearSoS.errMP`). -/
theorem coeffNorm1_empPoly_sub_popPoly_le {M : Mixture k d} (hM : M.Valid) {base u0 : Fin d → ℝ}
    {t : Fin k → ℝ} (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0) {wmin : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hn : 0 < n) (hd : d ≤ n) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {η : ℝ}
    {D : ℕ} (hG : GoodNoise M.w η D (labels ω) (stdNoise M ω)) (hηw : 2 * η ≤ wmin)
    (hcv : ∀ v, wmin / 4 * Colinear.quad M.S v ≤
      Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    (hcov : ∀ v, Colinear.quad M.cov v ≤
      2 * Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    {m : ℕ} (hm : 2 * m ≤ D) :
    coeffNorm1 (empPoly (Separating.whiten (Separating.yt r ω)) (2 * m) -
        popPoly M.w (acoef M u0 t) (uhat M (Separating.Wr r ω) u0) (SW M (Separating.Wr r ω))
          (2 * m)) ≤ errMP d m wmin η n := by
  have H : MP.Hyp M r ω wmin η D := ⟨hM, hwmin, hw, hn, hd, hr, hG, hηw, hcv, hcov⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · rw [Nat.mul_zero, MP.empPoly_zero _ hn, MP.popPoly_zero hM.sum_w, sub_self, coeffNorm1_zero]
    exact errMP_nonneg hwmin H.eta_nonneg
  · exact MP.coeffNorm1_empPoly_sub_popPoly_le_of_pos H hu0 hμ hm1 hm

/-- **Finite-sample transfer, pointwise**: under the hypotheses of
`BS23.ColinearSoS.coeffNorm1_empPoly_sub_popPoly_le`, for every `v`,
`|(1/n) ∑ⱼ ⟨Xⱼ, v⟩^(2m) - ∑_c w_c hmom (2m) (a_c ⟨ŭ, v⟩) (vᵀ Σ_W v)| ≤
errMP · (∑ᵢ |vᵢ|)^(2m)`. -/
theorem abs_eval_empPoly_sub_popPoly_le {M : Mixture k d} (hM : M.Valid)
    {base u0 : Fin d → ℝ} {t : Fin k → ℝ} (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    {wmin : ℝ} (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hn : 0 < n) (hd : d ≤ n)
    {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {η : ℝ} {D : ℕ}
    (hG : GoodNoise M.w η D (labels ω) (stdNoise M ω)) (hηw : 2 * η ≤ wmin)
    (hcv : ∀ v, wmin / 4 * Colinear.quad M.S v ≤
      Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    (hcov : ∀ v, Colinear.quad M.cov v ≤
      2 * Colinear.quad (Colinear.empCov (Separating.yt r ω)) v)
    {m : ℕ} (hm : 2 * m ≤ D) (v : Fin d → ℝ) :
    |(n : ℝ)⁻¹ * ∑ j, (Separating.whiten (Separating.yt r ω) j ⬝ᵥ v) ^ (2 * m) -
        ∑ c, M.w c * hmom (2 * m) (acoef M u0 t c * (uhat M (Separating.Wr r ω) u0 ⬝ᵥ v))
          (Colinear.quad (SW M (Separating.Wr r ω)) v)| ≤
      errMP d m wmin η n * (∑ i, |v i|) ^ (2 * m) := by
  rw [← eval_empPoly, ← eval_popPoly, ← map_sub]
  exact (SoS.abs_eval_le_of_isHomogeneous_sum_abs ((MP.isHomogeneous_empPoly _ _).sub
    (MP.isHomogeneous_popPoly _ _ _ _ _)) v).trans (mul_le_mul_of_nonneg_right
      (coeffNorm1_empPoly_sub_popPoly_le hM hu0 hμ hwmin hw hn hd hr hG hηw hcv hcov hm)
      (by positivity))

end BS23.ColinearSoS
