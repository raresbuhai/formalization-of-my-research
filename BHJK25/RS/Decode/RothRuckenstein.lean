module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Roth–Ruckenstein: the algebra

The roots `Y = p(X)` of a bivariate polynomial `Q ∈ F[X][Y]` are found one coefficient at a time
(Roth–Ruckenstein). Here `F[X][Y]` is `Polynomial (Polynomial F)`: the outer variable is `Y`, the
inner one `X`. A node `Q` has `Q(0, Y) = Q.map constantCoeff ≠ 0`. If `Q(X, p(X)) = 0`, then
`a = p(0)` is a root of `Q(0, Y)` (`BHJK25.RS.RR.eval_map_constantCoeff`), and `p' = (p - a) / X`
is a root of the child `Q(X, a + X Y)` (`BHJK25.RS.RR.child`, `BHJK25.RS.RR.child_eval_divX`),
which the decoder then divides by the largest power `X^v` dividing it.

The number of nodes per level is bounded by the multiplicities of the roots: after dividing the
child at `a` by `X^v`, its `Y`-degree at `X = 0` is at most the multiplicity of `a` as a root of
`Q(0, Y)` (`BHJK25.RS.RR.natDegree_map_le_rootMultiplicity`), and the multiplicities of distinct
roots sum to at most `deg Q(0, Y)` (`BHJK25.RS.RR.sum_rootMultiplicity_le`).
-/

@[expose] public section

namespace BHJK25.RS.RR

open Polynomial

variable {F : Type*} [Field F]

/-- The **child** `Q(X, a + X Y)` of `Q ∈ F[X][Y]` at `a ∈ F`: the Taylor shift `Q(X, a + Z)`,
then `Z = X Y`. -/
noncomputable def child (Q : F[X][X]) (a : F) : F[X][X] := (taylor (C a) Q).comp (C X * X)

/-- The coefficient of `Y^j` in the child is `X^j` times that of the Taylor shift. -/
theorem child_coeff (Q : F[X][X]) (a : F) (j : ℕ) :
    (child Q a).coeff j = (taylor (C a) Q).coeff j * X ^ j := by
  rw [child, comp_C_mul_X_coeff]

/-- Evaluating the child: `Q(X, a + X p)`. -/
theorem child_eval (Q : F[X][X]) (a : F) (p : F[X]) :
    (child Q a).eval p = Q.eval (X * p + C a) := by
  rw [child, eval_comp, taylor_eval, eval_mul, eval_C, eval_X]

/-- A root `p` of `Q` gives the root `(p - p(0)) / X` of the child at `p(0)`. -/
theorem child_eval_divX (Q : F[X][X]) (p : F[X]) :
    (child Q (p.coeff 0)).eval p.divX = Q.eval p := by
  rw [child_eval, mul_comm, divX_mul_X_add]

/-- `Q(0, p(0))` is the constant coefficient of `Q(X, p(X))`. -/
theorem eval_map_constantCoeff (Q : F[X][X]) (p : F[X]) :
    (Q.map constantCoeff).eval (p.coeff 0) = (Q.eval p).coeff 0 := by
  rw [eval_map, ← constantCoeff_apply, eval₂_hom, constantCoeff_apply]

/-- The child of a nonzero polynomial is nonzero. -/
theorem child_ne_zero {Q : F[X][X]} (hQ : Q ≠ 0) (a : F) : child Q a ≠ 0 := by
  rw [Ne, child, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero X_ne_zero),
    taylor_eq_zero]
  exact hQ

/-- The Taylor shift in `Y` does not raise the `X`-degrees. -/
theorem natDegree_taylor_coeff_le {Q : F[X][X]} {e : ℕ} (h : ∀ j, (Q.coeff j).natDegree ≤ e)
    (a : F) (j : ℕ) : ((taylor (C a) Q).coeff j).natDegree ≤ e := by
  rw [taylor_coeff, eval_eq_sum_range]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
  rw [← C_pow]
  refine (natDegree_mul_C_le _ _).trans ?_
  rw [hasseDeriv_coeff, ← C_eq_natCast]
  exact (natDegree_C_mul_le _ _).trans (h _)

/-- **The multiplicity bound.** If `Q(0, Y) ≠ 0` and the child of `Q` at `a` is `X^v Q₁`, then
`Q₁(0, Y)` has degree at most the multiplicity of `a` as a root of `Q(0, Y)`. -/
theorem natDegree_map_le_rootMultiplicity {Q Q₁ : F[X][X]} {a : F} {v : ℕ}
    (hQ : Q.map constantCoeff ≠ 0) (h : child Q a = C (X ^ v) * Q₁) :
    (Q₁.map constantCoeff).natDegree ≤ rootMultiplicity a (Q.map constantCoeff) := by
  have key : ∀ j, X ^ v * Q₁.coeff j = (taylor (C a) Q).coeff j * X ^ j := fun j ↦ by
    rw [← coeff_C_mul, ← h, child_coeff]
  have hmap : (taylor (C a) Q).map constantCoeff = taylor a (Q.map constantCoeff) := by
    rw [map_taylor, constantCoeff_apply, coeff_C_zero]
  set μ := rootMultiplicity a (Q.map constantCoeff) with hμdef
  have hμ : ((taylor (C a) Q).coeff μ).coeff 0 ≠ 0 := by
    have h1 : (taylor a (Q.map constantCoeff)).coeff μ
        = (taylor a (Q.map constantCoeff)).trailingCoeff := by
      rw [trailingCoeff, hμdef, rootMultiplicity_eq_natTrailingDegree, taylor_apply]
    rw [← constantCoeff_apply, ← coeff_map, hmap, h1, Ne, trailingCoeff_eq_zero, taylor_eq_zero]
    exact hQ
  have hv : v ≤ μ := by
    by_contra hlt
    apply hμ
    have := congrArg (fun p ↦ p.coeff μ) (key μ)
    simpa [coeff_X_pow_mul', coeff_mul_X_pow', hlt, eq_comm] using this
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have := congrArg (fun p ↦ p.coeff v) (key j)
  have hjv : ¬ j ≤ v := by omega
  simpa [coeff_X_pow_mul', coeff_mul_X_pow', hjv] using this

/-- The multiplicities of distinct elements as roots of `q ≠ 0` sum to at most its degree. -/
theorem sum_rootMultiplicity_le {q : F[X]} (hq : q ≠ 0) {l : List F} (hl : l.Nodup) :
    (l.map fun a ↦ rootMultiplicity a q).sum ≤ q.natDegree := by
  classical
  calc (l.map fun a ↦ rootMultiplicity a q).sum
      = ∑ a ∈ l.toFinset, q.roots.count a := by
        rw [← List.sum_toFinset _ hl]
        simp only [count_roots]
    _ ≤ ∑ a ∈ l.toFinset ∪ q.roots.toFinset, q.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = Multiset.card q.roots :=
        Multiset.sum_count_eq_card fun a ha ↦
          Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha)
    _ ≤ q.natDegree := by
        have := card_roots hq
        rwa [degree_eq_natDegree hq, Nat.cast_le] at this

end BHJK25.RS.RR
