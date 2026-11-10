module

public import ABBKS26.Assembly.ExecFrameLoop

/-! Algebraic symmetry of the rational P1 certificates, including on malformed inputs. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux.Symmetry

open Common _root_.ABBKS26.Tree Matrix FrameAux.Linear FrameAux.Features FrameProgram
open scoped BigOperators

private theorem covariance_rows_eq {d : ℕ} (pts : Points) (w : Vector)
    (a b : Fin d) (hx : ∀ i : Fin pts.length, ent pts i a = ent pts i b)
    (j : Fin d) :
    matrixOf d (covariance d pts w) a j = matrixOf d (covariance d pts w) b j := by
  let x : Fin pts.length → Fin d → ℚ := fun i j ↦ ent pts i j
  let ws : Fin pts.length → ℚ := fun i ↦ w.getD i 0
  let c := (∑ i, ws i)⁻¹ • ∑ i, ws i • x i
  have hc : c a = c b := by
    simp only [c, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show x i a = x i b from hx i]
  have hrep : RepT (covariance d pts w)
      ((∑ i, ws i)⁻¹ • ∑ i, ws i • vecMulVec (x i - c) (x i - c)) :=
    covariance_rep rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  change ent (covariance d pts w) a j = ent (covariance d pts w) b j
  rw [hrep a j, hrep b j]
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show x i a = x i b from hx i, hc]

private theorem featurePoints_swap {d : ℕ} (pts : Points) (w : Vector) (T : MatrixL)
    (i : Fin pts.length) (a b : Fin d) :
    ent (featurePoints d T pts w) i (finProdFinEquiv (a, b)) =
      ent (featurePoints d T pts w) i (finProdFinEquiv (b, a)) := by
  have hrep := featurePoints_rep (x := fun i j ↦ ent pts i j)
    (w' := fun i ↦ w.getD i 0) (T' := matrixOf d T) rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  rw [hrep i (finProdFinEquiv (a, b)), hrep i (finProdFinEquiv (b, a))]
  simp only [Equiv.symm_apply_apply]
  exact mul_comm _ _

private theorem iterationCov_rows_eq {d : ℕ} (pts : Points) (w : Vector)
    (a b : Fin d) (j : Fin (d * d)) :
    matrixOf (d * d) (iterationCov d pts w) (finProdFinEquiv (a, b)) j =
      matrixOf (d * d) (iterationCov d pts w) (finProdFinEquiv (b, a)) j := by
  apply covariance_rows_eq
  intro i
  have hi : i.val < pts.length := by
    simpa only [iterationFeatures, featurePoints_length] using i.isLt
  exact featurePoints_swap pts w _ ⟨i.val, hi⟩ a b

private theorem power_rows_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (a b : ι) (h : ∀ j, A a j = A b j)
    (p : ℕ) (hp : p ≠ 0) (j : ι) : (A ^ p) a j = (A ^ p) b j := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply]
  simp_rw [h]

private theorem columnMatrix_symmetric {d : ℕ} (pts : Points) (w : Vector)
    (j : Fin (d * d)) :
    (matrixOf d (columnMatrix d
      (power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)) j))ᵀ =
      matrixOf d (columnMatrix d
        (power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)) j) := by
  let p := Robust.RBAux.FrameLoop.power d / 2
  let A := matrixOf (d * d) (iterationCov d pts w)
  have hp : p ≠ 0 := by
    have hh := (Robust.RBAux.FrameLoop.power_spec d).2.1
    dsimp only [p]
    omega
  have hpow := power_rep (A := iterationCov d pts w) (M := A) (fun _ _ ↦ rfl) p
  have hentry (a b : Fin d) :
      ent (power (d * d) p (iterationCov d pts w)) (a * d + b) j =
        (A ^ p) (finProdFinEquiv (a, b)) j := by
    have he := hpow (finProdFinEquiv (a, b)) j
    change ent (power (d * d) p (iterationCov d pts w)) (b.val + d * a.val) j =
      (A ^ p) (finProdFinEquiv (a, b)) j at he
    simpa only [Nat.mul_comm, Nat.add_comm] using he
  ext a b
  change ent (columnMatrix d (power (d * d) p (iterationCov d pts w)) j) b a =
    ent (columnMatrix d (power (d * d) p (iterationCov d pts w)) j) a b
  unfold columnMatrix
  rw [table_rep _ b a, table_rep _ a b]
  dsimp only
  rw [hentry, hentry, power_rows_eq A _ _ (iterationCov_rows_eq pts w b a) p hp j]

private theorem matrixOf_multiply (d : ℕ) (A B : MatrixL) :
    matrixOf d (multiply d A B) = matrixOf d A * matrixOf d B := by
  ext i j
  exact (table_rep _ i j).trans
    (sum_fin_eq_list (fun r : Fin d ↦ ent A i r * ent B r j)
      (fun r ↦ ent A i r * ent B r j) (fun _ ↦ rfl)).symm

private theorem pullback_symmetric (d : ℕ) (T : MatrixL) (a : Vector) (A : MatrixL)
    (hA : (matrixOf d A)ᵀ = matrixOf d A) :
    (statisticOf d (pullback d T a A)).Aᵀ =
      (statisticOf d (pullback d T a A)).A := by
  have ht : matrixOf d (table d d fun i j ↦ ent T j i) = (matrixOf d T)ᵀ := by
    ext i j
    exact table_rep _ i j
  change (matrixOf d (pullback d T a A).1)ᵀ = matrixOf d (pullback d T a A).1
  dsimp only [pullback]
  simp only [matrixOf_multiply, ht, transpose_mul, transpose_transpose, hA, mul_assoc]

/-- Symmetry of the concrete P1 columns is algebraic, including on malformed inputs.
It needs neither eligibility nor a clean-prefix invariant. -/
theorem columns_symmetric (d : ℕ) (pts : Points) (w : Vector) (q : StatisticL)
    (hq : q ∈ columns d pts w) : (statisticOf d q).Aᵀ = (statisticOf d q).A := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have hj' : j < d * d := List.mem_range.mp hj
  exact pullback_symmetric d _ _ _ (columnMatrix_symmetric pts w ⟨j, hj'⟩)

end ABBKS26.Assembly.Exec.FrameAux.Symmetry
