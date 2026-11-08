module

public import BS23.ColinearSoS.Defs
public import BS23.Common.HermiteFacts
public import Background.SumOfSquares.PseudoBounds

/-!
# The directional moments in the Bernstein basis

In the whitened frame of a mixture with colinear means, the `2m`-th directional moment of the
mixture in direction `v` is `Φ_{2m}(v) = ∑_c w_c hmom (2m) (a_c x) (y + σ² x²)`, where
`x = ⟨ŭ, v⟩` and `y = vᵀGv ≥ 0` is the part of the variance orthogonal to the line of means. It
is a combination of the "Bernstein monomials" `x^{2l} y^{m-l}`:

* **Moment equality** (`BS23.ColinearSoS.sum_hmom_eq_bernstein`, and over any commutative ring
  receiving `ℝ`, `BS23.ColinearSoS.sum_hmom_eq_bernstein_hom`):
  `Φ_{2m} = ∑_{l ≤ m} c_{2m, m-l} M_{2l} x^{2l} y^{m-l}`, with `M_{2l} = lineMom w a σ² l` the
  moments of the one-dimensional mixture `∑_c w_c N(a_c, σ²)` and `c_{2m,i} = hermCoeff (2m) i`.
  It follows from adding the variances `σ² x²` and `y` (`BS23.hmom_add_var`) and homogeneity
  (`BS23.hmom_mul`). Only even powers of `x` occur.
* **Coefficients** (`BS23.ColinearSoS.hermCoeff_two_mul_sub_eq`):
  `c_{2m, m-l} = C(m, l) (2m-1)‼ / (2l-1)‼`, so `c_{2m, m-l} M_{2l} = C(m, l) β_l` with the
  normalized coefficients `β_l = nbeta w a σ² m l` (`BS23.ColinearSoS.hermCoeff_mul_lineMom_eq`);
  `β_m = M_{2m}` (`BS23.ColinearSoS.nbeta_self`).
* **The induced distribution.** For a pseudo-expectation `Ẽ` of degree at least `2m`, `x` of
  degree at most `1` and `y` a sum of squares of degree at most `2`, the numbers
  `λ_l = Ẽ[x^{2l} y^{m-l}]` are nonnegative (`BS23.ColinearSoS.lam_nonneg`), and
  * `Ẽ[(x² + y)^m] = ∑_l C(m, l) λ_l` (`BS23.ColinearSoS.apply_add_sq_pow`);
  * `Ẽ[y (x² + y)^{m-1}] = ∑_{l < m} C(m-1, l) λ_l ≤ ∑_{l < m} C(m, l) λ_l`
    (`BS23.ColinearSoS.apply_mul_add_sq_pow`, `BS23.ColinearSoS.apply_mul_add_sq_pow_le`);
  * `Ẽ[Φ_{2m}] = ∑_l C(m, l) β_l λ_l` (`BS23.ColinearSoS.apply_sum_hmom`, and with the factors
    reordered `BS23.ColinearSoS.apply_sum_hmom'`).

  So with `N = ∑_l C(m, l) λ_l`, the weights `π_l = C(m, l) λ_l / N` form a probability vector and
  `Ẽ[Φ_{2m}] = N ∑_l π_l β_l`.
* **Selection lemmas** (real arithmetic). If `β_l ≤ β_m / 2` for `l < m` and
  `∑_l π_l β_l ≥ (1 - ε) β_m`, then `1 - π_m ≤ 2ε` (`BS23.ColinearSoS.select_max`); if
  `β_l ≥ 2 β_m` for `l < m` and `∑_l π_l β_l ≤ (1 + ε) β_m`, then `1 - π_m ≤ ε`
  (`BS23.ColinearSoS.select_min`). Both are stated with the unnormalized `C(m, l) λ_l`.
-/

@[expose] public section

namespace BS23.ColinearSoS

open Finset MvPolynomial
open scoped Nat

namespace Bern

/-- A ring hom commutes with `hmom`. -/
theorem map_hmom {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (r : ℕ) (a v : K) :
    f (hmom r a v) = hmom r (f a) (f v) := by
  simp [hmom, map_sum, map_mul, map_pow, map_natCast]

/-- One atom of the moment equality, before regrouping:
`hmom (2m) (α x) (y + s x²) = ∑_{i ≤ m} c_{2m,i} y^i x^{2(m-i)} hmom (2(m-i)) α s`. -/
theorem hmom_atom {K : Type*} [CommRing K] (f : ℝ →+* K) (α s : ℝ) (m : ℕ) (x y : K) :
    hmom (2 * m) (f α * x) (y + f s * x ^ 2) =
      ∑ i ∈ range (m + 1), (hermCoeff (2 * m) i : K) * y ^ i *
        (x ^ (2 * (m - i)) * f (hmom (2 * (m - i)) α s)) := by
  rw [add_comm y, hmom_add_var, show 2 * m / 2 + 1 = m + 1 by omega]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [show 2 * m - 2 * i = 2 * (m - i) by omega, mul_comm (f α) x, mul_comm (f s) (x ^ 2),
    hmom_mul, map_hmom]

/-- `(2l-1)‼ · 2^l · l! = (2l)!`, as used below. -/
private theorem dfac_mul (l : ℕ) : (2 * l - 1)‼ * 2 ^ l * l ! = (2 * l)! := by
  rw [mul_assoc, doubleFactorial_two_mul_sub_one_mul]

/-- The coefficient identity in `ℕ`: `c_{2m, m-l} (2l-1)‼ = C(m, l) (2m-1)‼`. -/
theorem hermCoeff_two_mul_sub_mul {m l : ℕ} (hl : l ≤ m) :
    hermCoeff (2 * m) (m - l) * (2 * l - 1)‼ = m.choose l * (2 * m - 1)‼ := by
  have hF : 0 < 2 ^ m * l ! * (m - l)! := by positivity
  refine Nat.eq_of_mul_eq_mul_right hF ?_
  have h1 : hermCoeff (2 * m) (m - l) * (2 * l - 1)‼ * (2 ^ m * l ! * (m - l)!) =
      hermCoeff (2 * m) (m - l) * (2 ^ (m - l) * (m - l)! * (2 * m - 2 * (m - l))!) := by
    rw [show 2 * m - 2 * (m - l) = 2 * l by omega, ← dfac_mul,
      show 2 ^ m = 2 ^ (m - l) * 2 ^ l by rw [← pow_add, Nat.sub_add_cancel hl]]
    ring
  have h2 : m.choose l * (2 * m - 1)‼ * (2 ^ m * l ! * (m - l)!) =
      (2 * m - 1)‼ * 2 ^ m * (m.choose l * l ! * (m - l)!) := by ring
  rw [h1, h2, hermCoeff_mul_factorial (by omega), Nat.choose_mul_factorial_mul_factorial hl,
    dfac_mul]

end Bern

/-! ### The moment equality -/

/-- **Moment equality** over any commutative ring `K` receiving `ℝ` by `f`:
`∑_c w_c hmom (2m) (a_c x) (y + σ² x²) = ∑_{l ≤ m} c_{2m, m-l} M_{2l} x^{2l} y^{m-l}`. -/
theorem sum_hmom_eq_bernstein_hom {K : Type*} [CommRing K] (f : ℝ →+* K) {k : ℕ}
    (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ) (x y : K) :
    ∑ c, f (w c) * hmom (2 * m) (f (a c) * x) (y + f σ2 * x ^ 2) =
      ∑ l ∈ range (m + 1),
        f ((hermCoeff (2 * m) (m - l) : ℝ) * lineMom w a σ2 l) * x ^ (2 * l) * y ^ (m - l) := by
  simp_rw [Bern.hmom_atom f, mul_sum]
  rw [sum_comm]
  set F : ℕ → K := fun l ↦
    f ((hermCoeff (2 * m) (m - l) : ℝ) * lineMom w a σ2 l) * x ^ (2 * l) * y ^ (m - l) with hF
  rw [← sum_range_reflect F (m + 1)]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
  simp only [hF]
  rw [show m + 1 - 1 - i = m - i by omega, Nat.sub_sub_self hi, map_mul, map_natCast,
    lineMom, map_sum, mul_sum, sum_mul, sum_mul]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [map_mul]
  ring

/-- **Moment equality** for polynomials:
`∑_c w_c hmom (2m) (a_c x) (y + σ² x²) = ∑_{l ≤ m} c_{2m, m-l} M_{2l} x^{2l} y^{m-l}`. -/
theorem sum_hmom_eq_bernstein {σ : Type*} {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ)
    (x y : MvPolynomial σ ℝ) :
    ∑ c, C (w c) * hmom (2 * m) (C (a c) * x) (y + C σ2 * x ^ 2) =
      ∑ l ∈ range (m + 1),
        C ((hermCoeff (2 * m) (m - l) : ℝ) * lineMom w a σ2 l) * x ^ (2 * l) * y ^ (m - l) :=
  sum_hmom_eq_bernstein_hom C w a σ2 m x y

/-! ### The coefficients -/

/-- `c_{2m, m-l} = C(m, l) (2m-1)‼ / (2l-1)‼`. -/
theorem hermCoeff_two_mul_sub_eq {m l : ℕ} (hl : l ≤ m) :
    (hermCoeff (2 * m) (m - l) : ℝ) =
      (m.choose l : ℝ) * (Nat.doubleFactorial (2 * m - 1) : ℝ) /
        (Nat.doubleFactorial (2 * l - 1) : ℝ) := by
  have hpos : (0 : ℝ) < (Nat.doubleFactorial (2 * l - 1) : ℝ) :=
    Nat.cast_pos.2 (Nat.doubleFactorial_pos _)
  rw [eq_div_iff hpos.ne']
  exact_mod_cast Bern.hermCoeff_two_mul_sub_mul hl

/-- `c_{2m, m-l} M_{2l} = C(m, l) β_l`. -/
theorem hermCoeff_mul_lineMom_eq {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) {m l : ℕ} (hl : l ≤ m) :
    (hermCoeff (2 * m) (m - l) : ℝ) * lineMom w a σ2 l = (m.choose l : ℝ) * nbeta w a σ2 m l := by
  rw [hermCoeff_two_mul_sub_eq hl, nbeta]
  ring

/-- `β_m = M_{2m}`: the top normalized coefficient is the moment along the line of means. -/
theorem nbeta_self {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ) :
    nbeta w a σ2 m m = lineMom w a σ2 m := by
  have hpos : (0 : ℝ) < (Nat.doubleFactorial (2 * m - 1) : ℝ) :=
    Nat.cast_pos.2 (Nat.doubleFactorial_pos _)
  rw [nbeta, mul_div_cancel_left₀ _ hpos.ne']

/-! ### The induced distribution -/

section Pseudo

variable {σ : Type*} {ℓ : ℕ} (E : SoS.PseudoExpectation σ ℓ)

/-- `λ_l = Ẽ[x^{2l} y^{m-l}] ≥ 0` for `l ≤ m`, `deg x ≤ 1`, `y` a sum of squares of degree at
most `2`, and `2m ≤ ℓ`. -/
theorem lam_nonneg {x y : MvPolynomial σ ℝ} (hx : x.totalDegree ≤ 1) (hy : IsSumSq y)
    (hy2 : y.totalDegree ≤ 2) {m l : ℕ} (hm : 2 * m ≤ ℓ) (hl : l ≤ m) :
    0 ≤ E (x ^ (2 * l) * y ^ (m - l)) := by
  have hsq : IsSumSq (x ^ (2 * l) * y ^ (m - l)) := by
    rw [pow_mul', sq]
    exact (IsSumSq.mul_self _).mul (SoS.isSumSq_pow hy _)
  refine E.nonneg_of_isSumSq hsq ?_
  have h1 : (x ^ (2 * l)).totalDegree ≤ 2 * l :=
    (totalDegree_pow x _).trans (by simpa using Nat.mul_le_mul_left (2 * l) hx)
  have h2 : (y ^ (m - l)).totalDegree ≤ (m - l) * 2 :=
    (totalDegree_pow y _).trans (Nat.mul_le_mul_left _ hy2)
  exact (totalDegree_mul _ _).trans ((add_le_add h1 h2).trans (by omega))

/-- `Ẽ[(x² + y)^m] = ∑_{l ≤ m} C(m, l) Ẽ[x^{2l} y^{m-l}]`. -/
theorem apply_add_sq_pow (x y : MvPolynomial σ ℝ) (m : ℕ) :
    E ((x ^ 2 + y) ^ m) =
      ∑ l ∈ range (m + 1), (m.choose l : ℝ) * E (x ^ (2 * l) * y ^ (m - l)) := by
  rw [add_pow, E.map_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  rw [← pow_mul, ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), mul_comm, E.map_C_mul]

/-- `Ẽ[y (x² + y)^{m-1}] = ∑_{l < m} C(m-1, l) Ẽ[x^{2l} y^{m-l}]` for `m ≥ 1`. -/
theorem apply_mul_add_sq_pow (x y : MvPolynomial σ ℝ) {m : ℕ} (hm : 1 ≤ m) :
    E (y * (x ^ 2 + y) ^ (m - 1)) =
      ∑ l ∈ range m, ((m - 1).choose l : ℝ) * E (x ^ (2 * l) * y ^ (m - l)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, add_pow, mul_sum, E.map_sum]
  refine sum_congr rfl fun l hl ↦ ?_
  have hl : l ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hl)
  rw [← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← E.map_C_mul]
  congr 1
  rw [← pow_mul, show n + 1 - l = n - l + 1 by omega, pow_succ]
  ring

/-- `Ẽ[y (x² + y)^{m-1}] ≤ ∑_{l < m} C(m, l) Ẽ[x^{2l} y^{m-l}]` for `m ≥ 1`, under the
hypotheses of `lam_nonneg`. -/
theorem apply_mul_add_sq_pow_le {x y : MvPolynomial σ ℝ} (hx : x.totalDegree ≤ 1)
    (hy : IsSumSq y) (hy2 : y.totalDegree ≤ 2) {m : ℕ} (hm1 : 1 ≤ m) (hm : 2 * m ≤ ℓ) :
    E (y * (x ^ 2 + y) ^ (m - 1)) ≤
      ∑ l ∈ range m, (m.choose l : ℝ) * E (x ^ (2 * l) * y ^ (m - l)) := by
  rw [apply_mul_add_sq_pow E x y hm1]
  refine sum_le_sum fun l hl ↦ ?_
  refine mul_le_mul_of_nonneg_right ?_ (lam_nonneg E hx hy hy2 hm (mem_range.1 hl).le)
  exact_mod_cast Nat.choose_le_choose l (Nat.sub_le m 1)

/-- `Ẽ[Φ_{2m}] = ∑_{l ≤ m} C(m, l) β_l Ẽ[x^{2l} y^{m-l}]`, where
`Φ_{2m} = ∑_c w_c hmom (2m) (a_c x) (y + σ² x²)`. -/
theorem apply_sum_hmom {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ) (x y : MvPolynomial σ ℝ) :
    E (∑ c, C (w c) * hmom (2 * m) (C (a c) * x) (y + C σ2 * x ^ 2)) =
      ∑ l ∈ range (m + 1),
        (m.choose l : ℝ) * nbeta w a σ2 m l * E (x ^ (2 * l) * y ^ (m - l)) := by
  rw [sum_hmom_eq_bernstein, E.map_sum]
  refine sum_congr rfl fun l hl ↦ ?_
  rw [mul_assoc, E.map_C_mul, hermCoeff_mul_lineMom_eq w a σ2 (Nat.lt_succ_iff.1 (mem_range.1 hl))]

/-- `apply_sum_hmom` with the factors in the order of `select_max` and `select_min`:
`Ẽ[Φ_{2m}] = ∑_{l ≤ m} C(m, l) Ẽ[x^{2l} y^{m-l}] β_l`. -/
theorem apply_sum_hmom' {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ) (x y : MvPolynomial σ ℝ) :
    E (∑ c, C (w c) * hmom (2 * m) (C (a c) * x) (y + C σ2 * x ^ 2)) =
      ∑ l ∈ range (m + 1),
        (m.choose l : ℝ) * E (x ^ (2 * l) * y ^ (m - l)) * nbeta w a σ2 m l := by
  rw [apply_sum_hmom]
  exact sum_congr rfl fun l _ ↦ by ring

end Pseudo

/-! ### Selection lemmas -/

/-- **Selection at the top.** If `β_l ≤ β_m / 2` for `l < m` and
`∑_l C(m, l) λ_l β_l ≥ (1 - ε) N β_m` with `N = ∑_l C(m, l) λ_l`, then the mass
`∑_{l < m} C(m, l) λ_l` away from `l = m` is at most `2 ε N`. -/
theorem select_max {m : ℕ} {lam β : ℕ → ℝ} (hlam : ∀ l < m, 0 ≤ lam l) (hβm : 0 < β m)
    (hβ : ∀ l < m, β l ≤ β m / 2) {ε : ℝ}
    (h : (1 - ε) * (∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l) * β m ≤
      ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l * β l) :
    ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤
      2 * ε * ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l := by
  have hS : ∑ l ∈ range m, (m.choose l : ℝ) * lam l * β l ≤
      β m / 2 * ∑ l ∈ range m, (m.choose l : ℝ) * lam l := by
    rw [mul_sum]
    refine sum_le_sum fun l hl ↦ ?_
    have hl := mem_range.1 hl
    rw [mul_comm (β m / 2)]
    exact mul_le_mul_of_nonneg_left (hβ l hl) (mul_nonneg (Nat.cast_nonneg _) (hlam l hl))
  simp only [sum_range_succ _ m, Nat.choose_self, Nat.cast_one, one_mul] at h ⊢
  set P := ∑ l ∈ range m, (m.choose l : ℝ) * lam l
  refine le_of_mul_le_mul_left ?_ hβm
  linarith

/-- **Selection at the bottom.** If `β_l ≥ 2 β_m` for `l < m` and
`∑_l C(m, l) λ_l β_l ≤ (1 + ε) N β_m` with `N = ∑_l C(m, l) λ_l`, then the mass
`∑_{l < m} C(m, l) λ_l` away from `l = m` is at most `ε N`. -/
theorem select_min {m : ℕ} {lam β : ℕ → ℝ} (hlam : ∀ l < m, 0 ≤ lam l) (hβm : 0 < β m)
    (hβ : ∀ l < m, 2 * β m ≤ β l) {ε : ℝ}
    (h : ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l * β l ≤
      (1 + ε) * (∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l) * β m) :
    ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤
      ε * ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l := by
  have hS : 2 * β m * ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤
      ∑ l ∈ range m, (m.choose l : ℝ) * lam l * β l := by
    rw [mul_sum]
    refine sum_le_sum fun l hl ↦ ?_
    have hl := mem_range.1 hl
    rw [mul_comm (2 * β m)]
    exact mul_le_mul_of_nonneg_left (hβ l hl) (mul_nonneg (Nat.cast_nonneg _) (hlam l hl))
  simp only [sum_range_succ _ m, Nat.choose_self, Nat.cast_one, one_mul] at h ⊢
  set P := ∑ l ∈ range m, (m.choose l : ℝ) * lam l
  refine le_of_mul_le_mul_left ?_ hβm
  linarith

/-- `∑_{l < m} C(m-1, l) λ_l ≤ ∑_{l < m} C(m, l) λ_l` for `λ_l ≥ 0`. -/
theorem sum_choose_pred_le {m : ℕ} {lam : ℕ → ℝ} (hlam : ∀ l < m, 0 ≤ lam l) :
    ∑ l ∈ range m, ((m - 1).choose l : ℝ) * lam l ≤ ∑ l ∈ range m, (m.choose l : ℝ) * lam l := by
  refine sum_le_sum fun l hl ↦ mul_le_mul_of_nonneg_right ?_ (hlam l (mem_range.1 hl))
  exact_mod_cast Nat.choose_le_choose l (Nat.sub_le m 1)

end BS23.ColinearSoS
