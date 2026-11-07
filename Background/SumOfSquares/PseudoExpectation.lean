module

public import Background.SumOfSquares.Proof
public import Background.SumOfSquares.SumSq
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Pseudo-expectations and pseudo-distributions

A degree-`ℓ` *pseudo-expectation* `Ẽ` is a linear functional on real polynomials with `Ẽ 1 = 1` and
`Ẽ (f * f) ≥ 0` whenever `deg f ≤ ℓ / 2`. Only its values on polynomials of degree at most `ℓ`
carry meaning.

[BKS23, §3.1] instead defines a degree-`ℓ` *pseudo-distribution*: a finitely supported
`D : ℝⁿ → ℝ` with `∑ₓ D(x) = 1` and `∑ₓ D(x) f(x)² ≥ 0` whenever `deg f ≤ ℓ / 2`, whose
pseudo-expectation is `Ẽ_D f = ∑ₓ D(x) f(x)`. Both are defined here.
`PseudoDistribution.toPseudoExpectation` and `PseudoExpectation.exists_pseudoDistribution` show
that, for finitely many variables, they describe the same functionals on polynomials of degree at
most `ℓ`. The rest of the library uses pseudo-expectations.

* `SoS.PseudoExpectation σ ℓ`, `SoS.PseudoDistribution σ ℓ`.
* `SoS.PseudoExpectation.Satisfies`, `SoS.PseudoExpectation.ApproxSatisfies`: exact and
  `η`-approximate satisfaction of a system at degree `r` [BKS23, Definition 3.1].
-/

@[expose] public section

namespace SoS

open MvPolynomial

/-- A degree-`ℓ` pseudo-expectation on polynomials in the variables `σ`. -/
structure PseudoExpectation (σ : Type*) (ℓ : ℕ) where
  /-- The functional `f ↦ Ẽ f`. -/
  toLinearMap : MvPolynomial σ ℝ →ₗ[ℝ] ℝ
  /-- `Ẽ 1 = 1`. -/
  map_one' : toLinearMap 1 = 1
  /-- `Ẽ (f * f) ≥ 0` whenever `deg f ≤ ℓ / 2`. -/
  map_mul_self_nonneg' : ∀ f : MvPolynomial σ ℝ, 2 * f.totalDegree ≤ ℓ → 0 ≤ toLinearMap (f * f)

namespace PseudoExpectation

variable {σ : Type*} {ℓ : ℕ}

instance : CoeFun (PseudoExpectation σ ℓ) fun _ ↦ MvPolynomial σ ℝ → ℝ :=
  ⟨fun E ↦ E.toLinearMap⟩

variable (E : PseudoExpectation σ ℓ)

theorem coe_apply (f : MvPolynomial σ ℝ) : E f = E.toLinearMap f := rfl

@[simp] theorem map_one : E 1 = 1 := E.map_one'

@[simp] theorem map_add (f g : MvPolynomial σ ℝ) : E (f + g) = E f + E g :=
  E.toLinearMap.map_add f g

@[simp] theorem map_sub (f g : MvPolynomial σ ℝ) : E (f - g) = E f - E g :=
  E.toLinearMap.map_sub f g

@[simp] theorem map_neg (f : MvPolynomial σ ℝ) : E (-f) = -E f :=
  E.toLinearMap.map_neg f

@[simp] theorem map_zero : E 0 = 0 :=
  E.toLinearMap.map_zero

@[simp] theorem map_smul (c : ℝ) (f : MvPolynomial σ ℝ) : E (c • f) = c * E f :=
  E.toLinearMap.map_smul c f

@[simp] theorem map_C_mul (c : ℝ) (f : MvPolynomial σ ℝ) : E (C c * f) = c * E f := by
  rw [C_mul', map_smul]

@[simp] theorem map_C (c : ℝ) : E (C c) = c := by
  rw [← mul_one (C c), map_C_mul, map_one, mul_one]

theorem map_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    E (∑ i ∈ s, f i) = ∑ i ∈ s, E (f i) :=
  _root_.map_sum E.toLinearMap f s

theorem map_list_sum (L : List (MvPolynomial σ ℝ)) : E L.sum = (L.map E).sum :=
  _root_.map_list_sum E.toLinearMap L

theorem map_mul_self_nonneg {f : MvPolynomial σ ℝ} (hf : 2 * f.totalDegree ≤ ℓ) :
    0 ≤ E (f * f) :=
  E.map_mul_self_nonneg' f hf

/-- `Ẽ h ≥ 0` for every sum of squares `h` of degree at most `ℓ`. This holds because a sum of
squares of degree at most `ℓ` is a sum of squares of polynomials of degree at most `ℓ / 2`: over
`ℝ`, the leading terms of squares cannot cancel (`SoS.two_mul_totalDegree_le`). -/
theorem nonneg_of_isSumSq {h : MvPolynomial σ ℝ} (hh : IsSumSq h)
    (hdeg : h.totalDegree ≤ ℓ) : 0 ≤ E h := by
  obtain ⟨L, rfl, hL⟩ := IsSumSq.exists_list_of_totalDegree_le hh hdeg
  rw [map_list_sum, List.map_map]
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact E.map_mul_self_nonneg (hL q hq)

/-- A pseudo-expectation of degree `ℓ` is one of every lower degree. -/
def mono {ℓ' : ℕ} (h : ℓ' ≤ ℓ) : PseudoExpectation σ ℓ' where
  toLinearMap := E.toLinearMap
  map_one' := E.map_one'
  map_mul_self_nonneg' f hf := E.map_mul_self_nonneg' f (hf.trans h)

@[simp] theorem mono_apply {ℓ' : ℕ} (h : ℓ' ≤ ℓ) (f : MvPolynomial σ ℝ) : E.mono h f = E f := rfl

end PseudoExpectation

/-- A degree-`ℓ` pseudo-distribution as defined in [BKS23, §3.1]: a finitely supported
`D : ℝ^σ → ℝ` with `∑ₓ D(x) = 1` and `∑ₓ D(x) f(x)² ≥ 0` whenever `deg f ≤ ℓ / 2`. -/
structure PseudoDistribution (σ : Type*) (ℓ : ℕ) where
  /-- The function `D`. -/
  mass : (σ → ℝ) →₀ ℝ
  /-- `∑ₓ D(x) = 1`. -/
  sum_mass : (mass.sum fun _ w ↦ w) = 1
  /-- `∑ₓ D(x) f(x)² ≥ 0` whenever `deg f ≤ ℓ / 2`. -/
  sum_mass_mul_sq_nonneg : ∀ f : MvPolynomial σ ℝ, 2 * f.totalDegree ≤ ℓ →
    0 ≤ mass.sum fun x w ↦ w * eval x f ^ 2

namespace PseudoDistribution

variable {σ : Type*} {ℓ : ℕ}

/-- The pseudo-expectation `Ẽ_D f = ∑ₓ D(x) f(x)`. -/
noncomputable def expect (D : PseudoDistribution σ ℓ) (f : MvPolynomial σ ℝ) : ℝ :=
  D.mass.sum fun x w ↦ w * eval x f

/-- The pseudo-expectation of a pseudo-distribution. -/
noncomputable def toPseudoExpectation (D : PseudoDistribution σ ℓ) : PseudoExpectation σ ℓ where
  toLinearMap :=
    { toFun := D.expect
      map_add' f g := by
        simp [expect, Finsupp.sum, mul_add, Finset.sum_add_distrib]
      map_smul' c f := by
        simp [expect, Finsupp.sum, Finset.mul_sum, mul_left_comm] }
  map_one' := by simpa [expect] using D.sum_mass
  map_mul_self_nonneg' f hf := by
    simpa [expect, sq] using D.sum_mass_mul_sq_nonneg f hf

@[simp] theorem toPseudoExpectation_apply (D : PseudoDistribution σ ℓ) (f : MvPolynomial σ ℝ) :
    D.toPseudoExpectation f = D.expect f := rfl

end PseudoDistribution

/-- For finitely many variables, every pseudo-expectation agrees, on polynomials of degree at most
`ℓ`, with the pseudo-expectation of a pseudo-distribution. -/
theorem PseudoExpectation.exists_pseudoDistribution {σ : Type*} [Finite σ] {ℓ : ℕ}
    (E : PseudoExpectation σ ℓ) :
    ∃ D : PseudoDistribution σ ℓ, ∀ f : MvPolynomial σ ℝ, f.totalDegree ≤ ℓ → D.expect f = E f := by
  classical
  -- The monomials of degree at most `ℓ`; finitely many, since `σ` is finite.
  let T : Set (σ →₀ ℕ) := {m | m.degree ≤ ℓ}
  have : Fintype T := (Finsupp.finite_of_degree_le ℓ).fintype
  -- The moment vector of a point `x`, and the pseudo-moments of `E`.
  let v : (σ → ℝ) → (T → ℝ) := fun x m ↦ eval x (monomial (m : σ →₀ ℕ) (1 : ℝ))
  let t : T → ℝ := fun m ↦ E (monomial (m : σ →₀ ℕ) 1)
  -- The moment vectors of points span everything: a functional vanishing on all of them is a
  -- polynomial vanishing everywhere, hence zero.
  have hspan : t ∈ Submodule.span ℝ (Set.range v) := by
    by_contra hnot
    obtain ⟨φ, hφt, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hφv : ∀ x, φ (v x) = 0 := by
      intro x
      have hmem : φ (v x) ∈ (Submodule.span ℝ (Set.range v)).map φ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, rfl⟩)
      rw [hφp] at hmem
      simpa using hmem
    let a : T → ℝ := fun m ↦ φ (Pi.single m 1)
    have hφ : ∀ w : T → ℝ, φ w = ∑ m, w m * a m := by
      intro w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [_root_.map_sum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [show Pi.single m (w m) = w m • Pi.single m (1 : ℝ) by ext j; simp [Pi.single_apply],
        _root_.map_smul, smul_eq_mul]
    let P : MvPolynomial σ ℝ := ∑ m : T, C (a m) * monomial (m : σ →₀ ℕ) 1
    have hP : P = 0 := by
      have : Infinite ℝ := Infinite.of_injective ((↑) : ℕ → ℝ) Nat.cast_injective
      refine MvPolynomial.funext fun x ↦ ?_
      rw [_root_.map_zero, ← hφv x, hφ]
      simp [P, v, _root_.map_sum, mul_comm]
    have ha : ∀ m, a m = 0 := by
      intro m₀
      have hcoeff := congrArg (fun p : MvPolynomial σ ℝ ↦ p.coeff (m₀ : σ →₀ ℕ)) hP
      simp only [P] at hcoeff
      rw [coeff_sum, Finset.sum_eq_single m₀] at hcoeff
      · simpa [coeff_C_mul, coeff_monomial] using hcoeff
      · intro m _ hm
        rw [coeff_C_mul, coeff_monomial, ite_eq_right (fun h ↦ hm (Subtype.ext h)), mul_zero]
      · simp
    exact hφt (by rw [hφ]; simp [ha])
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hspan
  -- `c` has the pseudo-moments of `E`.
  have hmom : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ →
      (c.sum fun x w ↦ w * eval x (monomial m 1)) = E (monomial m 1) := by
    intro m hm
    have := congrFun hc ⟨m, hm⟩
    simpa [Finsupp.sum, Finset.sum_apply, v, t] using this
  -- So it agrees with `E` on every polynomial of degree at most `ℓ`.
  have hexp : ∀ f : MvPolynomial σ ℝ, f.totalDegree ≤ ℓ →
      (c.sum fun x w ↦ w * eval x f) = E f := by
    intro f hf
    have hmono : ∀ m ∈ f.support, monomial m (f.coeff m) = C (f.coeff m) * monomial m 1 := by
      intro m _
      rw [C_mul_monomial, mul_one]
    have hdeg : ∀ m ∈ f.support, m.degree ≤ ℓ := fun m hm ↦ (le_totalDegree hm).trans hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum, E.map_sum]
    simp only [Finsupp.sum, _root_.map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [hmono m hm, E.map_C_mul, ← hmom m (hdeg m hm), Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [map_mul, eval_C]
    ring
  refine ⟨⟨c, ?_, ?_⟩, ?_⟩
  · simpa using hexp 1 (by simp)
  · intro f hf
    have h₁ := hexp (f * f) ((totalDegree_mul f f).trans (by omega))
    have h₂ := E.map_mul_self_nonneg' f hf
    rw [← E.coe_apply, ← h₁] at h₂
    simpa [sq] using h₂
  · intro f hf
    exact hexp f hf

namespace PseudoExpectation

variable {σ K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}

/-- [BKS23, Definition 3.1]: `Ẽ` satisfies the system `A` at degree `r` if
`Ẽ (h * ∏ i ∈ S, fᵢ) ≥ 0` for every set `S` of constraints and every sum of squares `h` with
`deg h + ∑ i ∈ S, max (deg fᵢ) r ≤ ℓ`. The paper's "satisfies `A`", with no degree, is
`Satisfies E A 0`. -/
def Satisfies (E : PseudoExpectation σ ℓ) (A : System σ K) (r : ℕ) : Prop :=
  ∀ (S : Finset (Fin A.length)) (h : MvPolynomial σ ℝ), IsSumSq h →
    h.totalDegree + ∑ i ∈ S, max (A.get i).totalDegree r ≤ ℓ →
      0 ≤ E (h * toReal (A.prod S))

/-- [BKS23, Definition 3.1]: `Ẽ` satisfies the system `A` at degree `r` up to `η`, measured
against the coefficient norms: `Ẽ (h * ∏ i ∈ S, fᵢ) ≥ -η ‖h‖₂ ∏ i ∈ S, ‖fᵢ‖₂` under the same
degree condition as `Satisfies`. The paper prints `≥ η · …`; the sign must be `-η`, since
otherwise exact satisfaction would not imply approximate satisfaction. -/
def ApproxSatisfies (E : PseudoExpectation σ ℓ) (A : System σ K) (η : ℝ) (r : ℕ) : Prop :=
  ∀ (S : Finset (Fin A.length)) (h : MvPolynomial σ ℝ), IsSumSq h →
    h.totalDegree + ∑ i ∈ S, max (A.get i).totalDegree r ≤ ℓ →
      -(η * coeffNorm h * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ≤ E (h * toReal (A.prod S))

end PseudoExpectation

end SoS
