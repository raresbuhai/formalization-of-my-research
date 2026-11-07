module

public import Background.SumOfSquares.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Degrees of sums of squares

Over `ℝ`, the leading terms of squares cannot cancel: if `h = ∑ qᵢ²`, then `2 deg qᵢ ≤ deg h` for
every `i`. So a sum of squares of degree at most `ℓ` is a sum of squares of polynomials of degree
at most `ℓ / 2`, which is what makes a degree-`ℓ` pseudo-expectation nonnegative on it.

* `SoS.IsSumSq.exists_list`: a sum of squares is `∑ q ∈ L, q * q` for a list `L`.
* `SoS.two_mul_totalDegree_le`: for real polynomials, `2 deg q ≤ deg (∑ q ∈ L, q * q)` for every
  `q ∈ L`.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ : Type*}

/-- A sum of squares is the sum of the squares of the elements of a list. -/
theorem IsSumSq.exists_list {R : Type*} [CommSemiring R] {h : R} (hh : IsSumSq h) :
    ∃ L : List R, h = (L.map fun q ↦ q * q).sum := by
  induction hh with
  | zero => exact ⟨[], by simp⟩
  | sq_add a _ ih =>
    obtain ⟨L, rfl⟩ := ih
    exact ⟨a :: L, by simp⟩

/-- The sum of the squares of the elements of a list is a sum of squares. -/
theorem isSumSq_sum_mul_self {R : Type*} [CommSemiring R] (L : List R) :
    IsSumSq (L.map fun q ↦ q * q).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simpa using IsSumSq.sq_add a ih

/-- A polynomial of total degree at most `D` is the sum of its homogeneous components of degrees
`0, …, D`. -/
theorem sum_homogeneousComponent_of_totalDegree_le {R : Type*} [CommSemiring R]
    {q : MvPolynomial σ R} {D : ℕ} (hq : q.totalDegree ≤ D) :
    ∑ i ∈ Finset.range (D + 1), homogeneousComponent i q = q := by
  conv_rhs => rw [← sum_homogeneousComponent q]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range, not_lt] at hi hi'
    exact homogeneousComponent_eq_zero _ _ (by omega)

/-- If `deg q ≤ D`, the degree-`2D` part of `q²` is the square of the degree-`D` part of `q`. -/
theorem homogeneousComponent_mul_self {R : Type*} [CommSemiring R] {q : MvPolynomial σ R}
    {D : ℕ} (hq : q.totalDegree ≤ D) :
    homogeneousComponent (2 * D) (q * q) =
      homogeneousComponent D q * homogeneousComponent D q := by
  have hcomp : ∀ i j, homogeneousComponent (2 * D)
      (homogeneousComponent i q * homogeneousComponent j q) =
        if 2 * D = i + j then homogeneousComponent i q * homogeneousComponent j q else 0 :=
    fun i j ↦ homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      ((homogeneousComponent_isHomogeneous i q).mul (homogeneousComponent_isHomogeneous j q)))
  conv_lhs => rw [← sum_homogeneousComponent_of_totalDegree_le hq, Finset.sum_mul_sum, map_sum]
  rw [Finset.sum_eq_single D]
  · rw [map_sum, Finset.sum_eq_single D]
    · rw [hcomp, ite_eq_left (two_mul D)]
    · intro j hj hjD
      rw [hcomp, ite_eq_right]
      simp only [Finset.mem_range] at hj
      omega
    · simp
  · intro i hi hiD
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [hcomp, ite_eq_right]
    simp only [Finset.mem_range] at hi hj
    omega
  · simp

/-- If a sum of squares of real numbers vanishes, every term vanishes. -/
theorem eq_zero_of_sum_sq_eq_zero {L : List ℝ} (h : (L.map fun a ↦ a * a).sum = 0) :
    ∀ a ∈ L, a = 0 := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons] at h
    have hL : 0 ≤ (L.map fun a ↦ a * a).sum :=
      List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact mul_self_nonneg a)
    have hb := (add_eq_zero_iff_of_nonneg (mul_self_nonneg b) hL).1 h
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact mul_self_eq_zero.1 hb.1
    · exact ih hb.2 a ha

/-- If a sum of squares of real polynomials vanishes, every term vanishes. -/
theorem eq_zero_of_sum_mul_self_eq_zero {L : List (MvPolynomial σ ℝ)}
    (h : (L.map fun q ↦ q * q).sum = 0) : ∀ q ∈ L, q = 0 := by
  intro q hq
  have : Infinite ℝ := Infinite.of_injective ((↑) : ℕ → ℝ) Nat.cast_injective
  refine MvPolynomial.funext fun x ↦ ?_
  have hx : ((L.map (eval x)).map fun a ↦ a * a).sum = 0 := by
    have := congrArg (eval x) h
    simpa [map_list_sum, List.map_map, Function.comp_def] using this
  rw [map_zero]
  exact eq_zero_of_sum_sq_eq_zero hx _ (List.mem_map.2 ⟨q, hq, rfl⟩)

/-- A nonzero polynomial has a nonzero homogeneous component in its total degree. -/
theorem homogeneousComponent_totalDegree_ne_zero {R : Type*} [CommSemiring R]
    {q : MvPolynomial σ R} (hq : q ≠ 0) : homogeneousComponent q.totalDegree q ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.2 hq)
    fun s ↦ s.sum fun _ e ↦ e
  intro h0
  have hdeg' : d.degree = q.totalDegree := by
    rw [totalDegree, hdeg]
    rfl
  have hcoeff := congrArg (fun p : MvPolynomial σ R ↦ p.coeff d) h0
  simp only [coeff_homogeneousComponent, hdeg', ite_true] at hcoeff
  exact mem_support_iff.1 hd (by simpa using hcoeff)

/-- **No cancellation of leading terms.** For real polynomials,
`2 deg q ≤ deg (∑ q ∈ L, q * q)` for every `q ∈ L`. -/
theorem two_mul_totalDegree_le {L : List (MvPolynomial σ ℝ)} :
    ∀ q ∈ L, 2 * q.totalDegree ≤ ((L.map fun q ↦ q * q).sum).totalDegree := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q₁, hq₁, hlt⟩ := hcon
  obtain ⟨q₀, hq₀, hmax⟩ := L.toFinset.exists_max_image totalDegree ⟨q₁, List.mem_toFinset.2 hq₁⟩
  rw [List.mem_toFinset] at hq₀
  set D := q₀.totalDegree with hD
  have hle : ∀ q ∈ L, q.totalDegree ≤ D := fun q hq ↦ hmax q (List.mem_toFinset.2 hq)
  have hlt' : ((L.map fun q ↦ q * q).sum).totalDegree < 2 * D :=
    lt_of_lt_of_le hlt (Nat.mul_le_mul_left 2 (hle q₁ hq₁))
  -- The degree-`2D` part of the sum vanishes, and it is the sum of the squares of the
  -- degree-`D` parts.
  have hzero := homogeneousComponent_eq_zero (2 * D) _ hlt'
  rw [map_list_sum, List.map_map] at hzero
  have hsq : ((L.map fun q ↦ q * q).map (homogeneousComponent (2 * D))) =
      ((L.map (homogeneousComponent D)).map fun p ↦ p * p) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun q hq ↦ homogeneousComponent_mul_self (hle q hq)
  rw [← List.map_map, hsq] at hzero
  have h₀ := eq_zero_of_sum_mul_self_eq_zero hzero _ (List.mem_map.2 ⟨q₀, hq₀, rfl⟩)
  have hq₀ne : q₀ ≠ 0 := by
    rintro rfl
    simp [hD] at hlt'
  exact homogeneousComponent_totalDegree_ne_zero hq₀ne h₀

/-- A real sum of squares of degree at most `ℓ` is the sum of the squares of a list of polynomials
of degree at most `ℓ / 2`. -/
theorem IsSumSq.exists_list_of_totalDegree_le {h : MvPolynomial σ ℝ} (hh : IsSumSq h) {ℓ : ℕ}
    (hdeg : h.totalDegree ≤ ℓ) :
    ∃ L : List (MvPolynomial σ ℝ), h = (L.map fun q ↦ q * q).sum ∧
      ∀ q ∈ L, 2 * q.totalDegree ≤ ℓ := by
  obtain ⟨L, rfl⟩ := IsSumSq.exists_list hh
  exact ⟨L, rfl, fun q hq ↦ (two_mul_totalDegree_le q hq).trans hdeg⟩

end SoS
