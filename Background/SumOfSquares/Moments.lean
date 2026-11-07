module

public import Background.SumOfSquares.Approximate
public import Mathlib.Analysis.Convex.Cone.InnerDual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Moments

The moment formulation of pseudo-expectations and of approximate satisfaction, which the
sum-of-squares algorithm (`Background/SumOfSquares/Solver.lean`) optimizes over.

* **Moments.** A linear functional `Λ` on polynomials is determined by its *moments* `Λ (xᵐ)`
  (`SoS.apply_eq_sum_coeff_mul`), and every sequence `y` indexed by monomials is the moments of
  a functional, its Riesz functional `SoS.riesz y`. A degree-`ℓ` pseudo-expectation is a
  functional that maps `1` to `1` and is positive semidefinite in degree `ℓ` (`SoS.IsPSD`): its
  moment matrix `(y (α + β))_{α, β}`, indexed by the monomials of degree at most `ℓ / 2`, is
  positive semidefinite. `SoS.PseudoExpectation.ofMoments` builds one from its moments.
  `SoS.MinEigGE Λ D κ` says the moment matrix has smallest eigenvalue at least `κ`, which also
  covers approximate positive semidefiniteness (`κ < 0`) and definiteness with a margin
  (`κ > 0`).
* **Approximate satisfaction as a distance.** For one set `S` of constraints, approximate
  satisfaction [BKS23, Definition 3.1] says that the localized functional
  `h ↦ Ẽ (h * ∏ i ∈ S, fᵢ)` is nonnegative on sums of squares `h` of degree at most `D`, up to
  `t ‖h‖₂` (`SoS.ApproxNonneg`). By `SoS.approxNonneg_iff`, this holds exactly when the moments
  of degree at most `D` of the localized functional are within Euclidean distance `t` of those of
  a functional that is positive semidefinite in degree `D`. So approximate satisfaction is a
  semidefinite condition, with one auxiliary moment sequence for each set of constraints
  (`SoS.PseudoExpectation.approxSatisfies_iff`), and an algorithm can optimize over it. The proof
  is cone duality: the moment sequences of positive semidefinite functionals form the dual of
  the cone of sums of squares.
* **Constant constraints.** `SoS.PseudoExpectation.approxSatisfies_iff_of_nonneg_const`: when the
  constant constraints are nonnegative, approximate satisfaction only needs checking on sets of
  nonconstant constraints, which have at most `ℓ` elements.
* **Bounded moments.** `SoS.PseudoExpectation.abs_apply_monomial_le`: if `ℓ` is even and `Ẽ`
  satisfies an explicit bound `f = B - ∑ i, xᵢ² ≥ 0` up to `η`, every moment of degree at most
  `ℓ` is at most `(1 + |B| + η ‖f‖₂)^(ℓ / 2)` in absolute value. This bounds the region the
  algorithm searches.
-/

@[expose] public section

namespace SoS

open MvPolynomial
open scoped RealInnerProductSpace

variable {σ : Type*}

/-! ### Monomials of bounded degree -/

/-- The monomials of degree at most `D` in finitely many variables. -/
noncomputable def monomialsLE (σ : Type*) [Finite σ] (D : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le D).toFinset

@[simp] theorem mem_monomialsLE [Finite σ] {D : ℕ} {m : σ →₀ ℕ} :
    m ∈ monomialsLE σ D ↔ m.degree ≤ D := by
  simp [monomialsLE]

/-- In `n` variables there are at most `(n + 1)^D` monomials of degree at most `D`. -/
theorem card_monomialsLE_le [Fintype σ] (D : ℕ) :
    (monomialsLE σ D).card ≤ (Fintype.card σ + 1) ^ D :=
  card_le_of_degree_le _ fun _ hm ↦ mem_monomialsLE.1 hm

theorem support_subset_monomialsLE [Finite σ] {R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {D : ℕ} (h : p.totalDegree ≤ D) : p.support ⊆ monomialsLE σ D :=
  fun _ hm ↦ mem_monomialsLE.2 ((le_totalDegree hm).trans h)

/-! ### Linear functionals and their moments -/

/-- A linear functional on polynomials is determined by its moments, its values on monomials. -/
theorem apply_eq_sum_coeff_mul (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (f : MvPolynomial σ ℝ) :
    Λ f = ∑ m ∈ f.support, f.coeff m * Λ (monomial m 1) := by
  conv_lhs => rw [f.as_sum]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [show monomial m (f.coeff m) = f.coeff m • monomial m (1 : ℝ) by
    rw [smul_monomial, smul_eq_mul, mul_one], _root_.map_smul, smul_eq_mul]

/-- The Riesz functional of a sequence `y` indexed by monomials: the linear functional with
moments `y`. -/
noncomputable def riesz (y : (σ →₀ ℕ) → ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials σ ℝ).constr ℝ y

@[simp] theorem riesz_monomial (y : (σ →₀ ℕ) → ℝ) (m : σ →₀ ℕ) (c : ℝ) :
    riesz y (monomial m c) = c * y m := by
  have h := (basisMonomials σ ℝ).constr_basis ℝ y m
  simp only [coe_basisMonomials] at h
  rw [show monomial m c = c • monomial m (1 : ℝ) by rw [smul_monomial, smul_eq_mul, mul_one],
    _root_.map_smul, smul_eq_mul, riesz, h]

theorem riesz_apply (y : (σ →₀ ℕ) → ℝ) (f : MvPolynomial σ ℝ) :
    riesz y f = ∑ m ∈ f.support, f.coeff m * y m := by
  rw [apply_eq_sum_coeff_mul]
  simp

/-- Every linear functional is the Riesz functional of its moments. -/
@[simp] theorem riesz_moments (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) :
    riesz (fun m ↦ Λ (monomial m 1)) = Λ :=
  (basisMonomials σ ℝ).ext fun m ↦ by simp

theorem riesz_add (y z : (σ →₀ ℕ) → ℝ) : riesz (y + z) = riesz y + riesz z :=
  map_add ((basisMonomials σ ℝ).constr ℝ) y z

theorem riesz_smul (c : ℝ) (y : (σ →₀ ℕ) → ℝ) : riesz (c • y) = c • riesz y :=
  map_smul ((basisMonomials σ ℝ).constr ℝ) c y

/-- The moments of a localized functional: `L (xᵅ * f) = ∑ m, f_m y (α + m)`. -/
theorem riesz_monomial_mul (y : (σ →₀ ℕ) → ℝ) (α : σ →₀ ℕ) (f : MvPolynomial σ ℝ) :
    riesz y (monomial α 1 * f) = ∑ m ∈ f.support, f.coeff m * y (α + m) := by
  conv_lhs => rw [f.as_sum, Finset.mul_sum]
  simp [monomial_mul_monomial]

/-- The Riesz functional only reads the moments on the support. -/
theorem riesz_congr {y y' : (σ →₀ ℕ) → ℝ} {h : MvPolynomial σ ℝ}
    (hy : ∀ m ∈ h.support, y m = y' m) : riesz y h = riesz y' h := by
  rw [riesz_apply, riesz_apply]
  exact Finset.sum_congr rfl fun m hm ↦ by rw [hy m hm]

/-- `|L_y h - L_y' h| ≤ ρ ‖h‖₁` when the moments differ by at most `ρ` on the support. -/
theorem abs_riesz_sub_le {y y' : (σ →₀ ℕ) → ℝ} {h : MvPolynomial σ ℝ} {ρ : ℝ}
    (hy : ∀ m ∈ h.support, |y m - y' m| ≤ ρ) : |riesz y h - riesz y' h| ≤ ρ * coeffNorm1 h := by
  rw [riesz_apply, riesz_apply, ← Finset.sum_sub_distrib, coeffNorm1, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [← mul_sub, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hy m hm) (abs_nonneg _)

/-- `|L_y h| ≤ B ‖h‖₁` when the moments are at most `B` on the support. -/
theorem abs_riesz_le {y : (σ →₀ ℕ) → ℝ} {h : MvPolynomial σ ℝ} {B : ℝ}
    (hy : ∀ m ∈ h.support, |y m| ≤ B) : |riesz y h| ≤ B * coeffNorm1 h := by
  have := abs_riesz_sub_le (y' := 0) (h := h) (ρ := B) fun m hm ↦ by simpa using hy m hm
  simpa [riesz_apply] using this

/-! ### Positive semidefinite functionals -/

/-- `Λ` is positive semidefinite in degree `D`: `Λ (g * g) ≥ 0` for every polynomial `g` of degree
at most `D / 2`. For `Λ = riesz y`, this says that the moment matrix `(y (α + β))_{α, β}`, indexed
by the monomials of degree at most `D / 2`, is positive semidefinite. A degree-`ℓ`
pseudo-expectation is a functional that maps `1` to `1` and is positive semidefinite in
degree `ℓ`. -/
def IsPSD (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (D : ℕ) : Prop :=
  ∀ g : MvPolynomial σ ℝ, 2 * g.totalDegree ≤ D → 0 ≤ Λ (g * g)

namespace IsPSD

variable {Λ Λ' : MvPolynomial σ ℝ →ₗ[ℝ] ℝ} {D : ℕ}

/-- A functional that is positive semidefinite in degree `D` is nonnegative on sums of squares of
degree at most `D`. -/
theorem nonneg_of_isSumSq (hΛ : IsPSD Λ D) {h : MvPolynomial σ ℝ} (hh : IsSumSq h)
    (hdeg : h.totalDegree ≤ D) : 0 ≤ Λ h := by
  obtain ⟨L, rfl, hL⟩ := IsSumSq.exists_list_of_totalDegree_le hh hdeg
  rw [_root_.map_list_sum, List.map_map]
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact hΛ q (hL q hq)

theorem mono (hΛ : IsPSD Λ D) {D' : ℕ} (h : D' ≤ D) : IsPSD Λ D' :=
  fun g hg ↦ hΛ g (hg.trans h)

theorem add (hΛ : IsPSD Λ D) (hΛ' : IsPSD Λ' D) : IsPSD (Λ + Λ') D :=
  fun g hg ↦ add_nonneg (hΛ g hg) (hΛ' g hg)

theorem smul (hΛ : IsPSD Λ D) {c : ℝ} (hc : 0 ≤ c) : IsPSD (c • Λ) D :=
  fun g hg ↦ mul_nonneg hc (hΛ g hg)

end IsPSD

/-- `Λ (g * g) ≥ κ ‖g‖₂²` for every polynomial `g` of degree at most `D / 2`: the moment matrix of
`Λ` in degree `D` has smallest eigenvalue at least `κ`. For `κ = 0` this is `SoS.IsPSD`. For
`κ < 0` it is approximate positive semidefiniteness, which an algorithm can check exactly; for
`κ > 0`, positive definiteness with an explicit margin. -/
def MinEigGE (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (D : ℕ) (κ : ℝ) : Prop :=
  ∀ g : MvPolynomial σ ℝ, 2 * g.totalDegree ≤ D → κ * coeffNorm g ^ 2 ≤ Λ (g * g)

namespace MinEigGE

variable {Λ Λ' : MvPolynomial σ ℝ →ₗ[ℝ] ℝ} {D : ℕ} {κ κ' : ℝ}

theorem isPSD (h : MinEigGE Λ D κ) (hκ : 0 ≤ κ) : IsPSD Λ D :=
  fun g hg ↦ (mul_nonneg hκ (sq_nonneg _)).trans (h g hg)

theorem of_isPSD (h : IsPSD Λ D) : MinEigGE Λ D 0 :=
  fun g hg ↦ by simpa using h g hg

theorem mono (h : MinEigGE Λ D κ) {D' : ℕ} (hD : D' ≤ D) (hκ : κ' ≤ κ) : MinEigGE Λ D' κ' :=
  fun g hg ↦ (mul_le_mul_of_nonneg_right hκ (sq_nonneg _)).trans (h g (hg.trans hD))

theorem add (h : MinEigGE Λ D κ) (h' : MinEigGE Λ' D κ') : MinEigGE (Λ + Λ') D (κ + κ') :=
  fun g hg ↦ by
    rw [LinearMap.add_apply, add_mul]
    exact add_le_add (h g hg) (h' g hg)

theorem smul (h : MinEigGE Λ D κ) {c : ℝ} (hc : 0 ≤ c) : MinEigGE (c • Λ) D (c * κ) :=
  fun g hg ↦ by
    rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h g hg) hc

/-- Adding `τ / κ` times a functional whose moment matrix is at least `κ > 0` to one whose moment
matrix is at least `-τ` gives a positive semidefinite functional. -/
theorem isPSD_add_smul {τ : ℝ} (h : MinEigGE Λ D (-τ)) (h' : MinEigGE Λ' D κ) (hκ : 0 < κ)
    (hτ : 0 ≤ τ) : IsPSD (Λ + (τ / κ) • Λ') D :=
  (h.add (h'.smul (div_nonneg hτ hκ.le))).isPSD (by rw [div_mul_cancel₀ _ hκ.ne']; simp)

end MinEigGE

namespace PseudoExpectation

variable {ℓ : ℕ}

theorem isPSD (E : PseudoExpectation σ ℓ) : IsPSD E.toLinearMap ℓ :=
  E.map_mul_self_nonneg'

/-- The degree-`ℓ` pseudo-expectation with moments `y`: `Ẽ (xᵐ) = y m`. It needs `y 0 = 1` and a
positive semidefinite moment matrix. -/
noncomputable def ofMoments (y : (σ →₀ ℕ) → ℝ) (h0 : y 0 = 1) (hy : IsPSD (riesz y) ℓ) :
    PseudoExpectation σ ℓ where
  toLinearMap := riesz y
  map_one' := by rw [← C_1, C_apply, riesz_monomial, h0, one_mul]
  map_mul_self_nonneg' := hy

@[simp] theorem ofMoments_apply (y : (σ →₀ ℕ) → ℝ) (h0 : y 0 = 1) (hy : IsPSD (riesz y) ℓ)
    (f : MvPolynomial σ ℝ) : ofMoments y h0 hy f = riesz y f := rfl

theorem ofMoments_apply_monomial (y : (σ →₀ ℕ) → ℝ) (h0 : y 0 = 1) (hy : IsPSD (riesz y) ℓ)
    (m : σ →₀ ℕ) : ofMoments y h0 hy (monomial m 1) = y m := by
  simp

end PseudoExpectation

/-! ### Moment vectors -/

section Vectors

variable [Finite σ]

/-- The values of `y` on the monomials of degree at most `D`, as a vector in the Euclidean space
indexed by them. -/
noncomputable def vecLE (D : ℕ) (y : (σ →₀ ℕ) → ℝ) : EuclideanSpace ℝ (monomialsLE σ D) :=
  WithLp.toLp 2 fun m ↦ y m

@[simp] theorem vecLE_apply (D : ℕ) (y : (σ →₀ ℕ) → ℝ) (m : monomialsLE σ D) :
    vecLE D y m = y m := rfl

theorem inner_vecLE (D : ℕ) (y z : (σ →₀ ℕ) → ℝ) :
    ⟪vecLE D y, vecLE D z⟫ = ∑ m ∈ monomialsLE σ D, y m * z m := by
  rw [PiLp.inner_apply, ← Finset.sum_coe_sort (monomialsLE σ D)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp [mul_comm]

theorem norm_vecLE_sq (D : ℕ) (y : (σ →₀ ℕ) → ℝ) :
    ‖vecLE D y‖ ^ 2 = ∑ m ∈ monomialsLE σ D, y m ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vecLE]
  simp [sq]

/-- On polynomials of degree at most `D`, a functional is the inner product of its moments with
the coefficients. -/
theorem apply_eq_inner_vecLE (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) {D : ℕ} {h : MvPolynomial σ ℝ}
    (hh : h.totalDegree ≤ D) :
    Λ h = ⟪vecLE D fun m ↦ Λ (monomial m 1), vecLE D fun m ↦ h.coeff m⟫ := by
  rw [inner_vecLE, apply_eq_sum_coeff_mul, Finset.sum_subset (support_subset_monomialsLE hh)
    fun m _ hm ↦ by rw [notMem_support_iff.1 hm, zero_mul]]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

theorem riesz_eq_inner_vecLE (y : (σ →₀ ℕ) → ℝ) {D : ℕ} {h : MvPolynomial σ ℝ}
    (hh : h.totalDegree ≤ D) : riesz y h = ⟪vecLE D y, vecLE D fun m ↦ h.coeff m⟫ := by
  rw [apply_eq_inner_vecLE _ hh]
  simp

theorem coeffNorm_eq_norm_vecLE {D : ℕ} {h : MvPolynomial σ ℝ} (hh : h.totalDegree ≤ D) :
    coeffNorm h = ‖vecLE D fun m ↦ h.coeff m‖ := by
  rw [coeffNorm_eq_of_support_subset (support_subset_monomialsLE hh), ← norm_vecLE_sq,
    Real.sqrt_sq (norm_nonneg _)]

end Vectors

/-! ### Approximate nonnegativity on sums of squares -/

/-- `Λ` is nonnegative on sums of squares of degree at most `D` up to `t`, measured against
coefficient norms: `Λ h ≥ -t ‖h‖₂`. For a localized functional `h ↦ Ẽ (h * ∏ i ∈ S, fᵢ)`, this
is approximate satisfaction of the constraints in `S` ([BKS23, Definition 3.1];
`SoS.PseudoExpectation.approxSatisfies_iff_approxNonneg`). -/
def ApproxNonneg (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) : Prop :=
  ∀ h : MvPolynomial σ ℝ, IsSumSq h → h.totalDegree ≤ D → -(t * coeffNorm h) ≤ Λ h

/-- **Approximate nonnegativity is a distance.** For `t ≥ 0`, `Λ h ≥ -t ‖h‖₂` holds for every sum
of squares `h` of degree at most `D` if and only if the moments of `Λ` of degree at most `D` are
within Euclidean distance `t` of the moments of a functional that is positive semidefinite in
degree `D`.

One direction is the Cauchy–Schwarz inequality. For the other, let `w` be the closest point to
the moments `z` of `Λ` in the cone of moments of positive semidefinite functionals (the dual of
the cone of coefficient vectors of sums of squares). By cone duality, `w - z` is in the closure of
the cone of sums of squares, so the hypothesis applies to it, and gives `‖z - w‖² ≤ t ‖z - w‖`. -/
theorem approxNonneg_iff [Finite σ] (Λ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (D : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    ApproxNonneg Λ D t ↔ ∃ w : (σ →₀ ℕ) → ℝ, IsPSD (riesz w) D ∧
      ∑ m ∈ monomialsLE σ D, (Λ (monomial m 1) - w m) ^ 2 ≤ t ^ 2 := by
  classical
  -- Coefficient vectors and moment vectors, in the Euclidean space indexed by the monomials of
  -- degree at most `D`.
  let cv : MvPolynomial σ ℝ → EuclideanSpace ℝ (monomialsLE σ D) :=
    fun h ↦ vecLE D fun m ↦ h.coeff m
  set z := vecLE D fun m ↦ Λ (monomial m 1) with hz
  constructor
  · intro H
    -- The coefficient vectors of sums of squares of degree at most `D` form a convex cone `K`.
    let K : PointedCone ℝ (EuclideanSpace ℝ (monomialsLE σ D)) :=
      { carrier := cv '' {h | IsSumSq h ∧ h.totalDegree ≤ D}
        add_mem' := by
          rintro _ _ ⟨h₁, ⟨hh₁, hd₁⟩, rfl⟩ ⟨h₂, ⟨hh₂, hd₂⟩, rfl⟩
          exact ⟨h₁ + h₂, ⟨hh₁.add hh₂, (totalDegree_add _ _).trans (max_le hd₁ hd₂)⟩,
            by ext; simp [cv]⟩
        zero_mem' := ⟨0, ⟨IsSumSq.zero, by simp⟩, by ext; simp [cv]⟩
        smul_mem' := by
          rintro c _ ⟨h, ⟨hh, hd⟩, rfl⟩
          refine ⟨(c : ℝ) • h, ⟨?_, (totalDegree_smul_le _ _).trans hd⟩,
            by ext; simp [cv]⟩
          rw [smul_eq_C_mul, show C (c : ℝ) = C (Real.sqrt c) * C (Real.sqrt c) by
            rw [← map_mul, Real.mul_self_sqrt c.2]]
          exact (IsSumSq.mul_self _).mul hh }
    -- The hypothesis extends to the closure of `K`.
    have Hc : ∀ v ∈ (Submodule.closure K : ProperCone ℝ _), -(t * ‖v‖) ≤ ⟪z, v⟫ := by
      have hclosed :
          IsClosed {v : EuclideanSpace ℝ (monomialsLE σ D) | -(t * ‖v‖) ≤ ⟪z, v⟫} :=
        isClosed_le (by fun_prop) (by fun_prop)
      have hK : (K : Set _) ⊆ {v | -(t * ‖v‖) ≤ ⟪z, v⟫} := by
        rintro _ ⟨h, ⟨hh, hd⟩, rfl⟩
        simp only [Set.mem_ofPred_eq, cv, hz]
        rw [← coeffNorm_eq_norm_vecLE hd, ← apply_eq_inner_vecLE Λ hd]
        exact H h hh hd
      intro v hv
      exact hclosed.closure_subset_iff.2 hK hv
    -- The moments of positive semidefinite functionals form the dual cone `Kd`. Let `w` be the
    -- closest point of `Kd` to `z`.
    let Kd := ProperCone.innerDual (K : Set (EuclideanSpace ℝ (monomialsLE σ D)))
    have hconv : Convex ℝ (Kd : Set (EuclideanSpace ℝ (monomialsLE σ D))) := by
      intro y₁ hy₁ y₂ hy₂ a b ha hb _ x hx
      have h₁ : 0 ≤ ⟪x, y₁⟫ := hy₁ hx
      have h₂ : 0 ≤ ⟪x, y₂⟫ := hy₂ hx
      change 0 ≤ ⟪x, a • y₁ + b • y₂⟫
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      exact add_nonneg (mul_nonneg ha h₁) (mul_nonneg hb h₂)
    obtain ⟨w, hw, hmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex ⟨0, Kd.zero_mem⟩ Kd.isClosed.isComplete hconv z
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).1 hmin
    have h2 : ∀ y ∈ Kd, ⟪z - w, y⟫ ≤ 0 := fun y hy ↦ by
      simpa using hvar (y + w) (Kd.add_mem hy hw)
    have h1 : ⟪z - w, w⟫ = 0 := by
      have := hvar 0 Kd.zero_mem
      rw [zero_sub, inner_neg_right] at this
      linarith [h2 w hw]
    -- `w - z` is in the closure of `K`: otherwise a hyperplane would separate it from `K`, and
    -- its normal would be a point of `Kd` on the wrong side.
    have hmem : -(z - w) ∈ (Submodule.closure K : ProperCone ℝ _) := by
      by_contra hn
      obtain ⟨y, hy, hlt⟩ := ProperCone.hyperplane_separation' _ hn
      have hyd : y ∈ Kd := fun x hx ↦ hy x (subset_closure hx)
      have := h2 y hyd
      rw [inner_neg_left] at hlt
      linarith
    -- So `-(t ‖z - w‖) ≤ ⟪z, w - z⟫ = -‖z - w‖²`, and `‖z - w‖ ≤ t`.
    have key := Hc _ hmem
    have hzd : ⟪z, -(z - w)⟫ = -‖z - w‖ ^ 2 := by
      have hzw : ⟪z, z - w⟫ = ⟪z - w, z - w⟫ + ⟪w, z - w⟫ := by
        rw [← inner_add_left, sub_add_cancel]
      rw [inner_neg_right, hzw, real_inner_self_eq_norm_sq, real_inner_comm, h1, add_zero]
    rw [norm_neg, hzd] at key
    have hdt : ‖z - w‖ ≤ t := by
      by_contra hlt
      push Not at hlt
      nlinarith [mul_pos (sub_pos.2 hlt) (ht.trans_lt hlt)]
    -- The sequence of `w`.
    let w' : (σ →₀ ℕ) → ℝ := fun m ↦ if hm : m ∈ monomialsLE σ D then w ⟨m, hm⟩ else 0
    have hwv : vecLE D w' = w := by
      ext m
      change w' m = w m
      simp only [w', dite_eq_left m.2]
    refine ⟨w', fun g hg ↦ ?_, ?_⟩
    · have hd : (g * g).totalDegree ≤ D := (totalDegree_mul g g).trans (by omega)
      rw [riesz_eq_inner_vecLE w' hd, hwv, real_inner_comm]
      exact hw ⟨g * g, ⟨IsSumSq.mul_self g, hd⟩, rfl⟩
    · have hsub : z - w = vecLE D fun m ↦ Λ (monomial m 1) - w' m := by
        rw [← hwv]
        ext m
        simp [hz]
      rw [← norm_vecLE_sq, ← hsub]
      exact pow_le_pow_left₀ (norm_nonneg _) hdt 2
  · rintro ⟨w, hw, hdist⟩ h hh hd
    have hn : ‖z - vecLE D w‖ ≤ t := by
      have hsub : z - vecLE D w = vecLE D fun m ↦ Λ (monomial m 1) - w m := by
        ext m
        simp [hz]
      refine (sq_le_sq₀ (norm_nonneg _) ht).1 ?_
      rw [hsub, norm_vecLE_sq]
      exact hdist
    have hpos : 0 ≤ riesz w h := hw.nonneg_of_isSumSq hh hd
    rw [riesz_eq_inner_vecLE w hd] at hpos
    have hcs := neg_le_of_abs_le (abs_real_inner_le_norm (z - vecLE D w) (cv h))
    rw [inner_sub_left] at hcs
    have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg (cv h))
    rw [coeffNorm_eq_norm_vecLE hd, apply_eq_inner_vecLE Λ hd, ← hz]
    simp only [cv] at hcs hmul
    linarith

/-! ### Approximate satisfaction -/

namespace PseudoExpectation

variable {K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}

/-- Approximate satisfaction [BKS23, Definition 3.1], one set of constraints at a time: for each
set `S` of degree `d_S = ∑ i ∈ S, max (deg fᵢ) r ≤ ℓ`, the localized functional
`h ↦ Ẽ (h * ∏ i ∈ S, fᵢ)` is nonnegative on sums of squares of degree at most `ℓ - d_S`, up to
`η ∏ i ∈ S, ‖fᵢ‖₂`. -/
theorem approxSatisfies_iff_approxNonneg (E : PseudoExpectation σ ℓ) (A : System σ K) (η : ℝ)
    (r : ℕ) :
    E.ApproxSatisfies A η r ↔ ∀ S : Finset (Fin A.length),
      ∑ i ∈ S, max (A.get i).totalDegree r ≤ ℓ →
        ApproxNonneg (E.toLinearMap ∘ₗ LinearMap.mulRight ℝ (toReal (A.prod S)))
          (ℓ - ∑ i ∈ S, max (A.get i).totalDegree r)
          (η * ∏ i ∈ S, coeffNorm (toReal (A.get i))) := by
  constructor
  · intro hE S _ h hh hd
    exact (le_of_eq (by ring)).trans (hE S h hh (by omega))
  · intro H S h hh hd
    exact (le_of_eq (by ring)).trans (H S (by omega) h hh (by omega))

/-- **Approximate satisfaction as a semidefinite condition.** `Ẽ` satisfies `A` at degree `r` up
to `η` if and only if, for each set `S` of constraints of degree `d_S = ∑ i ∈ S, max (deg fᵢ) r`
at most `ℓ`, there is a sequence `w` that is positive semidefinite in degree `ℓ - d_S` and within
Euclidean distance `η ∏ i ∈ S, ‖fᵢ‖₂` of the moments `Ẽ (xᵐ ∏ i ∈ S, fᵢ)`, `deg m ≤ ℓ - d_S`. -/
theorem approxSatisfies_iff [Finite σ] (E : PseudoExpectation σ ℓ) (A : System σ K) {η : ℝ}
    (hη : 0 ≤ η) (r : ℕ) :
    E.ApproxSatisfies A η r ↔ ∀ S : Finset (Fin A.length),
      ∑ i ∈ S, max (A.get i).totalDegree r ≤ ℓ →
        ∃ w : (σ →₀ ℕ) → ℝ, IsPSD (riesz w) (ℓ - ∑ i ∈ S, max (A.get i).totalDegree r) ∧
          ∑ m ∈ monomialsLE σ (ℓ - ∑ i ∈ S, max (A.get i).totalDegree r),
              (E (monomial m 1 * toReal (A.prod S)) - w m) ^ 2 ≤
            (η * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ^ 2 := by
  rw [approxSatisfies_iff_approxNonneg]
  refine forall_congr' fun S ↦ forall_congr' fun _ ↦ ?_
  rw [approxNonneg_iff _ _ (mul_nonneg hη (Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _))]
  rfl

/-- **Constant constraints.** When every constraint of degree `0` (a constant) is nonnegative,
approximate satisfaction at degree `0` only needs checking on sets of nonconstant constraints:
multiplying by a constant `c ≥ 0` scales both sides of the inequality by `c`. So an algorithm
needs an auxiliary moment sequence only for each set of nonconstant constraints of degree at most
`ℓ`; such a set has at most `ℓ` elements. -/
theorem approxSatisfies_iff_of_nonneg_const (E : PseudoExpectation σ ℓ) (A : System σ K) (η : ℝ)
    (hA : ∀ i, (A.get i).totalDegree = 0 → 0 ≤ algebraMap K ℝ ((A.get i).coeff 0)) :
    E.ApproxSatisfies A η 0 ↔ ∀ S : Finset (Fin A.length), (∀ i ∈ S, (A.get i).totalDegree ≠ 0) →
      ∀ h : MvPolynomial σ ℝ, IsSumSq h → h.totalDegree + A.degree S ≤ ℓ →
        -(η * coeffNorm h * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ≤
          E (h * toReal (A.prod S)) := by
  classical
  have hmax : ∀ S : Finset (Fin A.length),
      ∑ i ∈ S, max (A.get i).totalDegree 0 = A.degree S := fun S ↦ by simp [System.degree]
  refine ⟨fun hE S _ h hh hd ↦ hE S h hh (by rwa [hmax]), fun H S h hh hd ↦ ?_⟩
  rw [hmax] at hd
  let p : Fin A.length → Prop := fun i ↦ (A.get i).totalDegree = 0
  -- The constant constraints in `S`, and their product `a ≥ 0`.
  have hC : ∀ i ∈ S.filter p, toReal (A.get i) = C (algebraMap K ℝ ((A.get i).coeff 0)) := by
    intro i hi
    conv_lhs => rw [totalDegree_eq_zero_iff_eq_C.1 (Finset.mem_filter.1 hi).2]
    simp [toReal]
  set a := ∏ i ∈ S.filter p, algebraMap K ℝ ((A.get i).coeff 0) with ha_def
  have ha : 0 ≤ a := Finset.prod_nonneg fun i hi ↦ hA i (Finset.mem_filter.1 hi).2
  have hprod : toReal (A.prod S) = C a * toReal (A.prod (S.filter fun i ↦ ¬p i)) := by
    rw [System.prod, System.prod, ← Finset.prod_filter_mul_prod_filter_not S p, toReal_mul,
      toReal_prod, Finset.prod_congr rfl hC, ← map_prod]
  have hnorm : ∏ i ∈ S, coeffNorm (toReal (A.get i)) =
      a * ∏ i ∈ S.filter (fun i ↦ ¬p i), coeffNorm (toReal (A.get i)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S p, ha_def]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hC i hi, coeffNorm_C, abs_of_nonneg (hA i (Finset.mem_filter.1 hi).2)]
  have hdeg : A.degree (S.filter fun i ↦ ¬p i) = A.degree S := by
    rw [System.degree, System.degree, ← Finset.sum_filter_add_sum_filter_not S p,
      Finset.sum_eq_zero (s := S.filter p) (f := fun i ↦ (A.get i).totalDegree)
        fun i hi ↦ (Finset.mem_filter.1 hi).2, zero_add]
  have h₁ := H (S.filter fun i ↦ ¬p i) (fun i hi ↦ (Finset.mem_filter.1 hi).2) h hh
    (by rwa [hdeg])
  rw [hprod, mul_left_comm, map_C_mul, hnorm]
  calc -(η * coeffNorm h * (a * ∏ i ∈ S.filter (fun i ↦ ¬p i), coeffNorm (toReal (A.get i))))
      = a * -(η * coeffNorm h * ∏ i ∈ S.filter (fun i ↦ ¬p i), coeffNorm (toReal (A.get i))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h₁ ha

end PseudoExpectation

/-! ### Bounded moments -/

/-- A monomial of degree at least `k` has a divisor of degree `k`. -/
theorem exists_le_degree_eq {m : σ →₀ ℕ} {k : ℕ} (hk : k ≤ m.degree) :
    ∃ α ≤ m, α.degree = k := by
  classical
  induction k with
  | zero => exact ⟨0, zero_le, by simp⟩
  | succ k ih =>
    obtain ⟨α, hαm, hα⟩ := ih (by omega)
    obtain ⟨i, hi⟩ : ∃ i, α i < m i := by
      by_contra! h
      rw [le_antisymm hαm (Finsupp.le_def.2 h)] at hα
      omega
    refine ⟨α + Finsupp.single i 1, Finsupp.le_def.2 fun j ↦ ?_, by simp [hα]⟩
    have := Finsupp.le_def.1 hαm j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, add_zero]
      omega

theorem totalDegree_monomial_one (s : σ →₀ ℕ) :
    (monomial s (1 : ℝ)).totalDegree = s.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

namespace PseudoExpectation

variable {K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}

/-- **Bounded moments.** If `ℓ` is even and `Ẽ` satisfies an explicit bound
`f = B - ∑ i, xᵢ² ≥ 0` up to `η`, then every moment of degree at most `ℓ` is at most
`c^(ℓ / 2)`, where `c = 1 + |B| + η ‖f‖₂`.

For the even moments, by induction on `α`: `x^(2α) ≤ x^(2α') ∑ j, xⱼ²` for `α = α' + eᵢ`, and
`Ẽ[x^(2α') ∑ j, xⱼ²] = B Ẽ[x^(2α')] - Ẽ[x^(2α') f] ≤ |B| c^|α'| + η ‖f‖₂`. Every other moment is
`Ẽ[xᵅ xᵝ]` with `|α|, |β| ≤ ℓ / 2`, at most `(Ẽ[x^(2α)] + Ẽ[x^(2β)]) / 2` in absolute value. -/
theorem abs_apply_monomial_le [Fintype σ] (hℓ : Even ℓ) (E : PseudoExpectation σ ℓ)
    {A : System σ K} {η : ℝ} (hη : 0 ≤ η) (hE : E.ApproxSatisfies A η 0) {B : K}
    (hB : (C B - ∑ i, X i ^ 2) ∈ A) {m : σ →₀ ℕ} (hm : m.degree ≤ ℓ) :
    |E (monomial m 1)| ≤ (1 + |algebraMap K ℝ B| +
      η * coeffNorm (toReal (C B - ∑ i, X i ^ 2 : MvPolynomial σ K))) ^ (ℓ / 2) := by
  classical
  set f : MvPolynomial σ K := C B - ∑ i, X i ^ 2 with hf
  set b := algebraMap K ℝ B with hb
  set c := 1 + |b| + η * coeffNorm (toReal f) with hc
  have hc1 : 1 ≤ c := by
    have := mul_nonneg hη (coeffNorm_nonneg (toReal f))
    have := abs_nonneg b
    linarith
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.1 hB
  have hfr : toReal f = C b - ∑ i, X i ^ 2 := by simp [hf, hb, toReal]
  have hdegf : f.totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun i _ ↦ by simp [totalDegree_X_pow])))
  -- The even moments: `Ẽ[x^(2α)] ≤ c^|α|` for `|α| ≤ ℓ / 2`.
  have heven : ∀ k : ℕ, ∀ α : σ →₀ ℕ, α.degree = k → 2 * k ≤ ℓ →
      E (monomial α 1 * monomial α 1) ≤ c ^ k := by
    intro k
    induction k with
    | zero =>
      intro α hα _
      rw [(Finsupp.degree_eq_zero_iff α).1 hα, ← C_apply, ← map_mul, mul_one, C_1, map_one,
        pow_zero]
    | succ k ih =>
      intro α hα hk
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra! h
        rw [show α = 0 from Finsupp.ext h, _root_.map_zero] at hα
        omega
      obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single i 1 :=
        ⟨α - Finsupp.single i 1,
          (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))).symm⟩
      have hα' : α'.degree = k := by
        rw [_root_.map_add, Finsupp.degree_single] at hα
        omega
      set g : MvPolynomial σ ℝ := monomial α' 1
      have hgdeg : g.totalDegree = k := by rw [totalDegree_monomial_one, hα']
      -- `x^(2α') ∑ j, xⱼ²` is the sum of the squares `(x^α' xⱼ)²`, one of which is `x^(2α)`.
      have hsum : g * g * ∑ j, X j ^ 2 = ∑ j, monomial (α' + Finsupp.single j 1) (1 : ℝ) *
          monomial (α' + Finsupp.single j 1) 1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [monomial_add_single, pow_one]
        ring
      have hle : E (monomial (α' + Finsupp.single i 1) 1 * monomial (α' + Finsupp.single i 1) 1)
          ≤ E (g * g * ∑ j, X j ^ 2) := by
        rw [hsum, map_sum]
        refine Finset.single_le_sum (f := fun j ↦ E (monomial (α' + Finsupp.single j 1) 1 *
          monomial (α' + Finsupp.single j 1) 1)) (fun j _ ↦ E.map_mul_self_nonneg ?_)
          (Finset.mem_univ i)
        rw [totalDegree_monomial_one, _root_.map_add, Finsupp.degree_single, hα']
        omega
      -- `f ≥ 0`, multiplied by `x^(2α')`.
      have happrox := hE {i₀} (g * g) (IsSumSq.mul_self g) (by
        rw [Finset.sum_singleton, Nat.max_zero, hi₀]
        have := totalDegree_mul g g
        omega)
      rw [Finset.prod_singleton, hi₀, coeffNorm_monomial_mul, coeffNorm_monomial, abs_one,
        mul_one, System.prod, Finset.prod_singleton, hi₀] at happrox
      have hsplit : E (g * g * toReal f) = b * E (g * g) - E (g * g * ∑ i, X i ^ 2) := by
        rw [hfr, mul_sub, mul_comm (g * g) (C b), map_sub, map_C_mul]
      have hgg : E (g * g) ≤ c ^ k := ih α' hα' (by omega)
      have hgg0 : 0 ≤ E (g * g) := E.map_mul_self_nonneg (by omega)
      have hbg : b * E (g * g) ≤ |b| * c ^ k :=
        (mul_le_mul_of_nonneg_right (le_abs_self b) hgg0).trans
          (mul_le_mul_of_nonneg_left hgg (abs_nonneg b))
      have hck : 1 ≤ c ^ k := one_le_pow₀ hc1
      have hη' : 0 ≤ η * coeffNorm (toReal f) := mul_nonneg hη (coeffNorm_nonneg _)
      have hcc : c ^ k * c = c ^ k + |b| * c ^ k + c ^ k * (η * coeffNorm (toReal f)) := by
        rw [hc]
        ring
      rw [pow_succ, hcc]
      linarith [mul_le_mul_of_nonneg_right hck hη']
  -- Every moment of degree at most `ℓ` is `Ẽ[xᵅ xᵝ]` with `|α|, |β| ≤ ℓ / 2`.
  obtain ⟨r, hr⟩ := hℓ
  obtain ⟨α, hαm, hα⟩ := exists_le_degree_eq (min_le_left m.degree (ℓ / 2))
  obtain ⟨β, rfl⟩ : ∃ β, m = α + β := ⟨m - α, (add_tsub_cancel_of_le hαm).symm⟩
  rw [_root_.map_add] at hm hα
  have hαd : α.degree ≤ ℓ / 2 := by omega
  have hβd : β.degree ≤ ℓ / 2 := by omega
  set u : MvPolynomial σ ℝ := monomial α 1
  set v : MvPolynomial σ ℝ := monomial β 1
  have hu := heven _ α rfl (by omega)
  have hv := heven _ β rfl (by omega)
  have hdeg : ∀ s : ℝ, 2 * (u + C s * v).totalDegree ≤ ℓ := fun s ↦ by
    have h₁ : (monomial α (1 : ℝ)).totalDegree ≤ ℓ / 2 := by
      rw [totalDegree_monomial_one]
      exact hαd
    have h₂ : (C s * monomial β (1 : ℝ)).totalDegree ≤ ℓ / 2 :=
      (totalDegree_mul _ _).trans (by
        rw [totalDegree_C, zero_add, totalDegree_monomial_one]
        exact hβd)
    have := (totalDegree_add u (C s * v)).trans (max_le h₁ h₂)
    omega
  have hp := E.map_mul_self_nonneg (hdeg 1)
  have hn := E.map_mul_self_nonneg (hdeg (-1))
  have hexp : ∀ s : ℝ, (u + C s * v) * (u + C s * v) =
      u * u + C (2 * s) * (u * v) + C (s * s) * (v * v) := fun s ↦ by
    rw [map_mul, map_mul, map_ofNat]
    ring
  rw [hexp, map_add, map_add, map_C_mul, map_C_mul] at hp hn
  have hmon : monomial (α + β) (1 : ℝ) = u * v := by
    rw [monomial_mul_monomial, mul_one]
  have hcα : c ^ α.degree ≤ c ^ (ℓ / 2) := pow_le_pow_right₀ hc1 hαd
  have hcβ : c ^ β.degree ≤ c ^ (ℓ / 2) := pow_le_pow_right₀ hc1 hβd
  rw [hmon, abs_le]
  constructor <;> nlinarith

end PseudoExpectation

end SoS
