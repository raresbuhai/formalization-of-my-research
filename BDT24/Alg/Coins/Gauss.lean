module

public import BDT24.Alg.Defs
public import Background.GaussianCoins
public import Background.Sampling

/-!
# The own sample from Gaussians

The own sample of a round (`BDT24.Alg.ownSample`) reads `n m` blocks of `cbits` coins as binary
numbers, least significant bit first. These are the chunks of `Background/Sampling.lean`
(`BDT24.Alg.CN.ownSample_eq`), which are uniform, with the law of the cells of `n m` independent
standard Gaussians (`Gaussian.sum_cells_eq_integral`). Arranged as `n` rows of `m` coordinates
(`BDT24.Alg.CN.rowsEquiv`), these Gaussians are `n` independent vectors with law `N(0, I_m)`
(`BDT24.Alg.CN.measurePreserving_rowsEquiv`). So averaging a function of the own sample over the
coins is integrating it over Gaussian rows (`BDT24.Alg.CN.sum_ownSample_eq_integral`).
-/

@[expose] public section

namespace BDT24.Alg.CN

open Finset MeasureTheory ProbabilityTheory

/-! ### Bits as numbers -/

/-- The binary number of a list of bits, as a sum over any range that covers the list. -/
theorem bitsNat_eq_sum (l : List Bool) (N : ℕ) (h : l.length ≤ N) :
    bitsNat l = ∑ t ∈ range N, if l.getD t false then 2 ^ t else 0 := by
  induction l generalizing N with
  | nil => simp [bitsNat]
  | cons b l ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; omega⟩
    rw [sum_range_succ', bitsNat, ih N (by simp at h; omega), mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun t _ ↦ ?_
    split_ifs <;> ring

/-- The binary number of the block of `b` bits after the first `o`. -/
theorem bitsNat_window (l : List Bool) (o b : ℕ) :
    bitsNat ((l.drop o).take b) = ∑ t ∈ range b, if l.getD (o + t) false then 2 ^ t else 0 := by
  rw [bitsNat_eq_sum _ b (List.length_take_le _ _)]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (mem_range.1 ht), List.getElem?_drop]

/-! ### The own sample from cells -/

/-- The own sample read from `n m` cells: coordinate `j` of point `i` from cell `i m + j`. -/
def ownFrom (n m q : ℕ) (cells : Fin (n * m) → ℕ) : Pts :=
  List.ofFn fun i : Fin n ↦ List.ofFn fun j : Fin m ↦ ownVal n m q (cells (finProdFinEquiv (i, j)))

/-- The own sample reads its coins in chunks of `cbits` bits. -/
theorem ownSample_eq (n m q : ℕ) (c : List Bool) :
    ownSample n m q c = ownFrom n m q (fun e ↦ Sampling.chunkVal (cbits n m q) c e) := by
  unfold ownSample ownFrom
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  refine List.ext_getElem (by simp) fun j h3 h4 ↦ ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  congr 1
  rw [bitsNat_window, Sampling.chunkVal, finProdFinEquiv_apply_val]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [Nat.mul_comm m i, Nat.add_comm j]

/-! ### Gaussian rows -/

/-- `n m` coordinates as `n` rows of `m` coordinates: coordinate `j` of row `i` is coordinate
`i m + j`. -/
noncomputable def rowsEquiv (n m : ℕ) : (Fin (n * m) → ℝ) ≃ᵐ (Fin n → EuclideanSpace ℝ (Fin m)) :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) finProdFinEquiv).symm.trans
    ((MeasurableEquiv.curry (Fin n) (Fin m) ℝ).trans
      (MeasurableEquiv.piCongrRight fun _ ↦ MeasurableEquiv.toLp 2 (Fin m → ℝ)))

/-- Coordinate `j` of row `i` is coordinate `i m + j`. -/
theorem rowsEquiv_apply (n m : ℕ) (g : Fin (n * m) → ℝ) (i : Fin n) (j : Fin m) :
    rowsEquiv n m g i j = g (finProdFinEquiv (i, j)) := by
  change (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) finProdFinEquiv).symm g (i, j) = _
  rw [MeasurableEquiv.piCongrLeft, MeasurableEquiv.symm_mk]
  exact Equiv.piCongrLeft_symm_apply _ _ g (i, j)

/-- A product measure on `ι × κ`, curried, is a product of product measures (as in
`BHJK25/Spectral/Basic.lean`). -/
theorem pi_map_curry {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι × κ ↦ μ).map (MeasurableEquiv.curry ι κ X) =
      Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ := by
  have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : κ) ↦ μ)
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

/-- **Gaussian rows**: `n m` independent standard Gaussians, as `n` rows, are `n` independent
vectors with law `N(0, I_m)`. -/
theorem measurePreserving_rowsEquiv (n m : ℕ) :
    MeasurePreserving (rowsEquiv n m) (Measure.pi fun _ : Fin (n * m) ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (n * m) ↦ gaussianReal 0 1)
    (finProdFinEquiv (m := n) (n := m))).symm
  have h2 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin m) ℝ)
      (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry (Fin n) (Fin m) ℝ).measurable, pi_map_curry _⟩
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin n ↦ MeasurableEquiv.toLp 2 (Fin m → ℝ))
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    refine measurePreserving_pi _ _ fun _ ↦ ⟨(MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable, ?_⟩
    rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]
  exact h3.comp (h2.comp h1)

/-- **The own sample from Gaussians**: averaging a function of the own sample over its coins is
integrating it over `n` independent Gaussian rows, read through their cells. -/
theorem sum_ownSample_eq_integral (n m q : ℕ) (G : Pts → ℝ) :
    (∑ c : Fin (n * m * cbits n m q) → Bool, G (ownSample n m q (List.ofFn c))) /
        2 ^ (n * m * cbits n m q) =
      ∫ g, G (List.ofFn fun i ↦ List.ofFn fun j ↦
          ownVal n m q (Gaussian.cellOf (cbits n m q) (g i j)))
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  simp_rw [ownSample_eq]
  rw [Sampling.sum_chunks (T := n * m * cbits n m q) (N := n * m) le_rfl
      (fun cells ↦ G (ownFrom n m q cells)), Nat.sub_self, pow_zero, one_mul,
    Gaussian.sum_cells_eq_integral (n * m) (cbits n m q) (fun cells ↦ G (ownFrom n m q cells)),
    ← (measurePreserving_rowsEquiv n m).integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp only [ownFrom, rowsEquiv_apply]

end BDT24.Alg.CN
