module

public import BS23.Common.Uniform
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.Matrix.Order

/-!
# The good event implies its uniform form

* `BS23.sum_multinomial_gaussMomMulti`: the Gaussian moments of a linear form, written out with the
  multinomial theorem: `∑_{|α| = p} (p; α) b^α m_α = (p-1)‼ ‖b‖^p` (`0` for odd `p`), where
  `m_α = gaussMomMulti α`. This is `E ⟨b, G⟩^p = E Z^p ‖b‖^p` for a standard Gaussian vector `G`,
  proved combinatorially: only even `α = 2β` contribute, and
  `(2r; 2β) ∏ (2βᵢ-1)‼ = (2r-1)‼ (r; β)` (`BS23.multinomial_two_mul_mul_prod`), so the sum is
  `(2r-1)‼ (∑ bᵢ²)^r` by the multinomial theorem again.
* `BS23.uniformNoise_of_goodNoise`: if `ν_j = B g_j` and `S = B Bᵀ`, then `GoodNoise` for `g` with
  error `η` gives `UniformNoise` for `ν` with error `η (d + 1)^D`. For a direction `v`, with
  `b = Bᵀ v`: `⟨ν_j, v⟩ = ⟨g_j, b⟩`, `vᵀ S v = ‖b‖²`; expand `⟨g_j, b⟩^p` by the multinomial
  theorem and use `GoodNoise` termwise, for a total error of at most
  `η (∑ |bᵢ|)^p ≤ η (√d ‖b‖)^p ≤ η (d + 1)^D ‖b‖^p`.
* `BS23.uniformNoise_of_goodNoise_stdNoise`: the case of a sample, with `B = Σ^{1/2}` (Mathlib's
  `CFC.sqrt`), `g = stdNoise` and `ν_j = y_j - μ_{ℓ_j}`.
-/

@[expose] public section

namespace BS23

open Matrix Finset
open scoped MatrixOrder

variable {k d : ℕ}

/-! ### Multinomial coefficients of even multi-indices -/

/-- `(2n)! = 2^n n! (2n-1)‼`. -/
lemma factorial_two_mul_eq (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * (2 * n - 1).doubleFactorial := by
  rcases n with _ | n
  · simp
  · have h : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h, Nat.factorial_eq_mul_doubleFactorial, ← h, Nat.doubleFactorial_two_mul,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

/-- `(2r; 2β) ∏ᵢ (2βᵢ-1)‼ = (2r-1)‼ (r; β)` for `r = ∑ᵢ βᵢ`. -/
lemma multinomial_two_mul_mul_prod {ι : Type*} (s : Finset ι) (β : ι → ℕ) :
    Nat.multinomial s (fun i ↦ 2 * β i) * ∏ i ∈ s, (2 * β i - 1).doubleFactorial =
      (2 * ∑ i ∈ s, β i - 1).doubleFactorial * Nat.multinomial s β := by
  have h1 := Nat.multinomial_spec s (fun i ↦ 2 * β i)
  have h2 := Nat.multinomial_spec s β
  have hP : ∏ i ∈ s, (2 * β i).factorial =
      2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
        ∏ i ∈ s, (2 * β i - 1).doubleFactorial := by
    simp_rw [factorial_two_mul_eq, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpos : 0 < 2 ^ (∑ i ∈ s, β i) * ∏ i ∈ s, (β i).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc 2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
          (Nat.multinomial s (fun i ↦ 2 * β i) * ∏ i ∈ s, (2 * β i - 1).doubleFactorial)
        = (∏ i ∈ s, (2 * β i).factorial) * Nat.multinomial s (fun i ↦ 2 * β i) := by
          rw [hP]; ring
      _ = (2 * ∑ i ∈ s, β i).factorial := by rw [h1, Finset.mul_sum]
      _ = 2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
            ((2 * ∑ i ∈ s, β i - 1).doubleFactorial * Nat.multinomial s β) := by
          rw [factorial_two_mul_eq, ← h2]; ring

/-! ### Gaussian moments of a linear form -/

lemma gaussMom_two_mul (r : ℕ) : gaussMom (2 * r) = (2 * r - 1).doubleFactorial := by
  simp [gaussMom]

lemma gaussMomMulti_eq_zero {α : Fin d → ℕ} (h : ∃ i, ¬ Even (α i)) : gaussMomMulti α = 0 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])

/-- **Gaussian moments of a linear form**, written out with the multinomial theorem:
`∑_{|α| = p} (p; α) b^α E[G^α] = E[Z^p] ‖b‖^p`, i.e. `E ⟨b, G⟩^p = E Z^p ‖b‖^p` for a standard
Gaussian vector `G` (proved combinatorially). -/
theorem sum_multinomial_gaussMomMulti (b : Fin d → ℝ) (p : ℕ) :
    ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
        (Nat.multinomial univ α : ℝ) * (∏ i, b i ^ α i) * (gaussMomMulti α : ℝ) =
      (gaussMom p : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ p := by
  by_cases hp : Even p
  · obtain ⟨r, rfl⟩ := hp
    rw [← two_mul]
    have hq : 0 ≤ ∑ i, b i ^ 2 := by positivity
    rw [pow_mul, Real.sq_sqrt hq, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    symm
    refine Finset.sum_of_injOn (fun β i ↦ 2 * β i) ?_ ?_ ?_ ?_
    · intro β _ β' _ h
      funext i
      have := congrFun h i
      simp only at this
      omega
    · intro β hβ
      simp only [mem_univ, implies_true, and_true,
        Finset.mem_coe, mem_piAntidiag] at hβ ⊢
      rw [← Finset.mul_sum, hβ]
    · intro α hα hnot
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hα
      have : ∃ i, ¬ Even (α i) := by
        by_contra hall
        push Not at hall
        apply hnot
        refine ⟨fun i ↦ α i / 2, ?_, ?_⟩
        · simp only [Finset.mem_coe, mem_piAntidiag, mem_univ, implies_true, and_true]
          have hα2 : ∀ i, α i = 2 * (α i / 2) := fun i ↦ (Nat.two_mul_div_two_of_even (hall i)).symm
          have : ∑ i, α i = 2 * ∑ i, α i / 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ hα2 i
          have hα' : ∑ i, α i = 2 * r := hα
          omega
        · funext i
          exact Nat.two_mul_div_two_of_even (hall i)
      simp [gaussMomMulti_eq_zero this]
    · intro β hβ
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hβ
      have hm := multinomial_two_mul_mul_prod univ β
      rw [hβ] at hm
      simp only [gaussMomMulti, gaussMom_two_mul]
      have hm' : ((Nat.multinomial univ fun i ↦ 2 * β i : ℕ) : ℝ) *
          ∏ i, ((2 * β i - 1).doubleFactorial : ℝ) =
          ((2 * r - 1).doubleFactorial : ℝ) * (Nat.multinomial univ β : ℝ) := by
        exact_mod_cast hm
      push_cast
      simp_rw [pow_mul]
      linear_combination (∏ i, (b i ^ 2) ^ β i) * hm'.symm
  · rw [show gaussMom p = 0 by simp [gaussMom, hp]]
    simp only [Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hα
    have : ∃ i, ¬ Even (α i) := by
      by_contra hall
      push Not at hall
      exact hp (hα ▸ Finset.even_sum _ fun i _ ↦ hall i)
    simp [gaussMomMulti_eq_zero this]

/-! ### From `GoodNoise` to `UniformNoise` -/

/-- `⟨B g, v⟩ = ⟨g, Bᵀ v⟩`. -/
lemma mulVec_dotProduct_eq_sum (B : Matrix (Fin d) (Fin d) ℝ) (g v : Fin d → ℝ) :
    (B *ᵥ g) ⬝ᵥ v = ∑ i, g i * (Bᵀ *ᵥ v) i := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  rfl

/-- `vᵀ (B Bᵀ) v = ‖Bᵀ v‖²`. -/
lemma dotProduct_mul_transpose_mulVec (B : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ ((B * Bᵀ) *ᵥ v) = ∑ i, (Bᵀ *ᵥ v) i ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp [dotProduct, sq]

/-- `(∑ᵢ |bᵢ|)^p ≤ (√d ‖b‖)^p ≤ (d + 1)^D ‖b‖^p` for `p ≤ D`. -/
lemma sum_abs_pow_le (b : Fin d → ℝ) {p D : ℕ} (hp : p ≤ D) :
    (∑ i, |b i|) ^ p ≤ ((d : ℝ) + 1) ^ D * Real.sqrt (∑ i, b i ^ 2) ^ p := by
  have hcs : ∑ i, |b i| ≤ Real.sqrt d * Real.sqrt (∑ i, b i ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ ↦ (1 : ℝ)) (fun i ↦ |b i|)
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      sq_abs] at h
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)
  have hd : Real.sqrt d ≤ (d : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  calc (∑ i, |b i|) ^ p ≤ (Real.sqrt d * Real.sqrt (∑ i, b i ^ 2)) ^ p :=
        pow_le_pow_left₀ (by positivity) hcs p
    _ = Real.sqrt d ^ p * Real.sqrt (∑ i, b i ^ 2) ^ p := mul_pow _ _ _
    _ ≤ ((d : ℝ) + 1) ^ D * Real.sqrt (∑ i, b i ^ 2) ^ p := by
        gcongr
        calc Real.sqrt d ^ p ≤ ((d : ℝ) + 1) ^ p := pow_le_pow_left₀ (by positivity) hd p
          _ ≤ ((d : ℝ) + 1) ^ D := pow_le_pow_right₀ (by linarith) hp

/-- **The good event in uniform form.** If `ν_j = B g_j` for all `j` and `S = B Bᵀ`, then the good
event for `g` with error `η` gives the uniform moment bounds for `ν` with error `η (d + 1)^D`. -/
theorem uniformNoise_of_goodNoise {n : ℕ} {w : Fin k → ℝ} {η : ℝ} {D : ℕ} {ℓ : Fin n → Fin k}
    {g ν : Fin n → Fin d → ℝ} {S : Matrix (Fin d) (Fin d) ℝ} (B : Matrix (Fin d) (Fin d) ℝ)
    (hS : S = B * Bᵀ) (hν : ∀ j, ν j = B *ᵥ g j) (h : GoodNoise w η D ℓ g) :
    UniformNoise S (η * ((d : ℝ) + 1) ^ D) D ℓ ν := by
  intro c p hp v
  subst hS
  have hη : 0 ≤ η := (abs_nonneg _).trans (h.2 c 0 (by simp))
  have hexp : ∀ j, (ν j ⬝ᵥ v) ^ p = ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
      (Nat.multinomial univ α : ℝ) * (∏ i, (Bᵀ *ᵥ v) i ^ α i) * ∏ i, g j i ^ α i := by
    intro j
    rw [hν j, mulVec_dotProduct_eq_sum, sum_pow_eq_sum_piAntidiag]
    refine sum_congr rfl fun α _ ↦ ?_
    simp_rw [mul_pow, prod_mul_distrib]
    ring
  have key : (∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ p) / n -
      ((cluster ℓ c).card : ℝ) / n * (gaussMom p : ℝ) *
        Real.sqrt (v ⬝ᵥ ((B * Bᵀ) *ᵥ v)) ^ p =
      ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
        ((Nat.multinomial univ α : ℝ) * ∏ i, (Bᵀ *ᵥ v) i ^ α i) *
          ((∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i) / n -
            ((cluster ℓ c).card : ℝ) / n * (gaussMomMulti α : ℝ)) := by
    rw [dotProduct_mul_transpose_mulVec, mul_assoc, ← sum_multinomial_gaussMomMulti]
    simp_rw [hexp]
    rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun α _ ↦ ?_
    rw [← Finset.mul_sum]
    ring
  rw [key]
  calc |∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
        ((Nat.multinomial univ α : ℝ) * ∏ i, (Bᵀ *ᵥ v) i ^ α i) *
          ((∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i) / n -
            ((cluster ℓ c).card : ℝ) / n * (gaussMomMulti α : ℝ))|
      ≤ ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
          ((Nat.multinomial univ α : ℝ) * ∏ i, |(Bᵀ *ᵥ v) i| ^ α i) * η := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun α hα ↦ ?_)
        have hαD : ∑ i, α i ≤ D := by
          have := (mem_piAntidiag.1 hα).1
          exact (le_of_eq this).trans hp
        rw [abs_mul, abs_mul, Nat.abs_cast, abs_prod]
        simp_rw [abs_pow]
        exact mul_le_mul_of_nonneg_left (h.2 c α hαD) (by positivity)
    _ = η * (∑ i, |(Bᵀ *ᵥ v) i|) ^ p := by
        rw [sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
        exact sum_congr rfl fun α _ ↦ by ring
    _ ≤ η * (((d : ℝ) + 1) ^ D * Real.sqrt (∑ i, (Bᵀ *ᵥ v) i ^ 2) ^ p) :=
        mul_le_mul_of_nonneg_left (sum_abs_pow_le _ hp) hη
    _ = η * ((d : ℝ) + 1) ^ D * Real.sqrt (v ⬝ᵥ ((B * Bᵀ) *ᵥ v)) ^ p := by
        rw [dotProduct_mul_transpose_mulVec]; ring

/-! ### The case of a sample -/

/-- Mathlib's square root of a matrix is symmetric. -/
lemma transpose_sqrt (S : Matrix (Fin d) (Fin d) ℝ) : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  have h := (CFC.sqrt_nonneg S).isSelfAdjoint
  rwa [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- `S = S^{1/2} (S^{1/2})ᵀ` for a positive semidefinite `S`. -/
lemma eq_sqrt_mul_transpose_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) :
    S = CFC.sqrt S * (CFC.sqrt S)ᵀ := by
  rw [transpose_sqrt, CFC.sqrt_mul_sqrt_self S hS.nonneg]

/-- The square root of a positive definite matrix is invertible. -/
lemma isUnit_sqrt_of_posDef {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsUnit (CFC.sqrt S) :=
  (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).2 hS.isUnit

/-- The noise `y_j - μ_{ℓ_j}` of a sample point is `Σ^{1/2}` times its standardized noise. -/
lemma sqrt_mulVec_stdNoise (M : Mixture k d) (hS : M.S.PosDef) {n : ℕ}
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    CFC.sqrt M.S *ᵥ stdNoise M ω j = fun i ↦ (ω j).2 i - M.μ (ω j).1 i := by
  rw [stdNoise, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_sqrt_of_posDef hS)), one_mulVec]

/-- **The good event of a sample in uniform form**: the good event for the standardized noise
with error `η` gives the uniform moment bounds for the noise `y_j - μ_{ℓ_j}` with covariance `Σ`
and error `η (d + 1)^D`. -/
theorem uniformNoise_of_goodNoise_stdNoise (M : Mixture k d) (hS : M.S.PosDef) {n : ℕ}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {η : ℝ} {D : ℕ}
    (h : GoodNoise M.w η D (labels ω) (stdNoise M ω)) :
    UniformNoise M.S (η * ((d : ℝ) + 1) ^ D) D (labels ω)
      (fun j i ↦ (ω j).2 i - M.μ (ω j).1 i) :=
  uniformNoise_of_goodNoise (CFC.sqrt M.S) (eq_sqrt_mul_transpose_sqrt hS.posSemidef)
    (fun j ↦ (sqrt_mulVec_stdNoise M hS ω j).symm) h

end BS23
