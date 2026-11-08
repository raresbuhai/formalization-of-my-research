module

public import BHJK25.Spectral.Tail.Law

/-!
# The spike vector has a large Rayleigh quotient

The deterministic part of the proof of [BHJK25, Lemma 3.7] (`BHJK25.Spectral.noisy_spike`). The
noisy matrix `M = (1 - ε) M₁ + ε M₀` is symmetric, and for the spike column `u` of `M₁`,

  `uᵀ M u = (1 - ε) (λ* ‖u‖⁴ + ∑ⱼ λⱼ ⟨uⱼ, u⟩²) + ε ∑ⱼ λ'ⱼ ⟨u'ⱼ, u⟩² ≥ (1 - ε) λ* ‖u‖⁴ - S`,

where `S = ∑ⱼ |λⱼ| ⟨uⱼ, u⟩² + ∑ⱼ |λ'ⱼ| ⟨u'ⱼ, u⟩²` (`BHJK25.Spectral.TailAux.crossSum`). So if
`‖u‖² ≥ n / 2` and `S < ‖u‖² T` with `T = (1 - ε) λ* n / 4`, then
`uᵀ M u > ‖u‖² (1 - ε) λ* n / 4`, which is more than `3 ‖u‖²` once `(1 - ε) λ* n / 4 > 3`.

The event that `M` is symmetric with a vector `v` such that `vᵀ M v > 3 ‖v‖²` is measurable
(`BHJK25.Spectral.TailAux.measurableSet_goodSet`): a closed set intersected with an open one.
-/

@[expose] public section

namespace BHJK25.Spectral.TailAux

open MeasureTheory Matrix

/-- The quadratic form of `U diag(λ) Uᵀ` is `∑ⱼ λⱼ ⟨uⱼ, v⟩²`. -/
theorem quad_specMap {n m : ℕ} (q : Fin m → ℝ × (Fin n → ℝ)) (v : Fin n → ℝ) :
    v ⬝ᵥ (specMap n m (toSpec q) *ᵥ v) = ∑ j, (q j).1 * ((q j).2 ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, mulVec, specMap_apply, toSpec, Finset.mul_sum, Finset.sum_mul, sq]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i' _ ↦
    Finset.sum_congr rfl fun i _ ↦ by ring

theorem transpose_specMap {n m : ℕ} (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) :
    (specMap n m p)ᵀ = specMap n m p := by
  ext i j
  simp only [transpose_apply, specMap_apply]
  exact Finset.sum_congr rfl fun l _ ↦ by ring

theorem transpose_noisyMat {k : ℕ} (ε spike : ℝ) (ω : Sample k) :
    (noisyMat ε spike ω)ᵀ = noisyMat ε spike ω := by
  simp only [noisyMat, transpose_add, transpose_smul, transpose_specMap]

/-- The quadratic form of the noisy matrix at the spike column `u`. -/
theorem quad_noisyMat {k : ℕ} (ε spike : ℝ) (ω : Sample k) :
    ω.1.1 ⬝ᵥ (noisyMat ε spike ω *ᵥ ω.1.1) =
      (1 - ε) * (∑ j, (ω.1.2 j).1 * ((ω.1.2 j).2 ⬝ᵥ ω.1.1) ^ 2 +
        spike * (ω.1.1 ⬝ᵥ ω.1.1) ^ 2) + ε * ∑ j, (ω.2 j).1 * ((ω.2 j).2 ⬝ᵥ ω.1.1) ^ 2 := by
  simp only [noisyMat, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    quad_specMap, Fin.sum_univ_castSucc, plantCols, Fin.snoc_castSucc, Fin.snoc_last]

/-- The cross terms `S = ∑ⱼ |λⱼ| ⟨uⱼ, u⟩² + ∑ⱼ |λ'ⱼ| ⟨u'ⱼ, u⟩²` between the spike column `u` and the
other components. -/
def crossSum {k : ℕ} (ω : Sample k) : ℝ :=
  ∑ j, |(ω.1.2 j).1| * ((ω.1.2 j).2 ⬝ᵥ ω.1.1) ^ 2 + ∑ j, |(ω.2 j).1| * ((ω.2 j).2 ⬝ᵥ ω.1.1) ^ 2

theorem neg_abs_mul_le {c l a : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha : 0 ≤ a) :
    -(|l| * a) ≤ c * (l * a) := by
  have h1 : -|l| * a ≤ l * a := mul_le_mul_of_nonneg_right (neg_abs_le l) ha
  have h2 : 0 ≤ |l| * a := mul_nonneg (abs_nonneg l) ha
  nlinarith

theorem neg_sum_le {ι : Type*} [Fintype ι] {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (l a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) : -∑ j, |l j| * a j ≤ c * ∑ j, l j * a j := by
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ neg_abs_mul_le hc0 hc1 (ha j)

/-- `uᵀ M u ≥ (1 - ε) λ* ‖u‖⁴ - S`. -/
theorem quad_noisyMat_ge {k : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (spike : ℝ)
    (ω : Sample k) :
    (1 - ε) * spike * (ω.1.1 ⬝ᵥ ω.1.1) ^ 2 - crossSum ω ≤
      ω.1.1 ⬝ᵥ (noisyMat ε spike ω *ᵥ ω.1.1) := by
  rw [quad_noisyMat, crossSum]
  have h1 := neg_sum_le (sub_nonneg.2 hε1) (by linarith) (fun j ↦ (ω.1.2 j).1)
    (fun j ↦ ((ω.1.2 j).2 ⬝ᵥ ω.1.1) ^ 2) fun j ↦ sq_nonneg _
  have h2 := neg_sum_le hε0 hε1 (fun j ↦ (ω.2 j).1)
    (fun j ↦ ((ω.2 j).2 ⬝ᵥ ω.1.1) ^ 2) fun j ↦ sq_nonneg _
  linarith

/-- On the good event, the spike column `u` has `uᵀ M u > 3 ‖u‖²`. -/
theorem good_of {k : ℕ} {ε spike : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hspike : 0 ≤ spike)
    (ω : Sample k) (hs : ((k : ℝ) + 1) / 2 ≤ ω.1.1 ⬝ᵥ ω.1.1)
    (hS : crossSum ω < (ω.1.1 ⬝ᵥ ω.1.1) * ((1 - ε) * spike * ((k : ℝ) + 1) / 4))
    (hbig : 3 < (1 - ε) * spike * ((k : ℝ) + 1) / 4) :
    (noisyMat ε spike ω)ᵀ = noisyMat ε spike ω ∧
      ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (noisyMat ε spike ω *ᵥ v) := by
  refine ⟨transpose_noisyMat ε spike ω, ω.1.1, ?_⟩
  have hq := quad_noisyMat_ge hε0 hε1.le spike ω
  set s := ω.1.1 ⬝ᵥ ω.1.1
  set a := (1 - ε) * spike
  set N : ℝ := (k : ℝ) + 1
  have hN : 0 < N := by positivity
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have ha : 0 ≤ a := mul_nonneg (by linarith) hspike
  have h1 : 0 ≤ a * s * (s - N / 2) := mul_nonneg (mul_nonneg ha hs0.le) (by linarith)
  have h2 : 3 * s < a * N / 4 * s := mul_lt_mul_of_pos_right hbig hs0
  nlinarith

/-- The event that the matrix is symmetric with a vector `v` such that `vᵀ M v > 3 ‖v‖²`. -/
def goodSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | Mᵀ = M ∧ ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (M *ᵥ v)}

theorem measurableSet_goodSet (n : ℕ) : MeasurableSet (goodSet n) := by
  have h1 : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | Mᵀ = M} :=
    isClosed_eq continuous_id.matrix_transpose continuous_id
  have h2 : IsOpen {M : Matrix (Fin n) (Fin n) ℝ | ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (M *ᵥ v)} := by
    simp only [Set.ofPred_exists]
    exact isOpen_iUnion fun v ↦ isOpen_lt continuous_const (by fun_prop)
  exact h1.measurableSet.inter h2.measurableSet

end BHJK25.Spectral.TailAux
