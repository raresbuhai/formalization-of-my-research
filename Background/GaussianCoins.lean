module

public import Background.Gaussian
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Gaussians from coin flips

A Turing machine has coin flips, not Gaussians. The coupling: for a standard Gaussian `G`, `Φ(G)`
is uniform on `(0, 1)`, so the cell `⌊2^B Φ(G)⌋` of `G` is uniform on `{0, …, 2^B - 1}`
(`Gaussian.measureReal_cellOf`). Reading `n` blocks of `B` coins as binary numbers gives `n`
independent uniform cells, with the same law as the cells of `n` independent standard Gaussians
(`Gaussian.sum_coinCells_eq_integral`). A machine that recovers `Gᵢ` approximately from its cell
then simulates Gaussian rounding.
-/

@[expose] public section

namespace Gaussian

open MeasureTheory ProbabilityTheory Real Set

/-- The standard Gaussian distribution function `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

theorem Phi_pos (x : ℝ) : 0 < Phi x :=
  TauCeti.Probability.cdf_gaussianReal_pos 0 one_ne_zero x

theorem Phi_lt_one (x : ℝ) : Phi x < 1 :=
  TauCeti.Probability.cdf_gaussianReal_lt_one 0 one_ne_zero x

theorem strictMono_Phi : StrictMono Phi :=
  TauCeti.Probability.strictMono_cdf_gaussianReal 0 one_ne_zero

theorem continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun x ↦
    (TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x).continuousAt

@[fun_prop]
theorem measurable_Phi : Measurable Phi := continuous_Phi.measurable

theorem exists_Phi_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ∃ x, Phi x = u := by
  have h : 2 * u - 1 ∈ range TauCeti.Real.erf := by
    rw [Real.range_erf]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨y, hy⟩ := h
  refine ⟨√2 * y, ?_⟩
  rw [Phi, TauCeti.Probability.cdf_gaussianReal_zero_one,
    mul_div_cancel_left₀ _ (by positivity), hy]
  ring

/-- **`Φ(G)` is uniform**: `P(Φ(G) < u) = u` for `u ∈ [0, 1]`. -/
theorem measureReal_Phi_lt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (gaussianReal 0 1).real {x | Phi x < u} = u := by
  rcases eq_or_lt_of_le hu0 with rfl | hu0'
  · have : {x | Phi x < 0} = (∅ : Set ℝ) := by
      ext x
      simp [(Phi_pos x).le]
    simp [this]
  rcases eq_or_lt_of_le hu1 with rfl | hu1'
  · have : {x | Phi x < 1} = univ := by
      ext x
      simp [Phi_lt_one x]
    simp [this]
  obtain ⟨a, ha⟩ := exists_Phi_eq ⟨hu0', hu1'⟩
  have : {x | Phi x < u} = Iio a := by
    ext x
    rw [mem_ofPred_eq, mem_Iio, ← ha]
    exact strictMono_Phi.lt_iff_lt
  rw [this, measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, ← ha]
  rfl

/-- The cell `⌊2^B Φ(x)⌋` of `x`. -/
noncomputable def cellOf (B : ℕ) (x : ℝ) : ℕ := ⌊(2 : ℝ) ^ B * Phi x⌋₊

theorem cellOf_lt (B : ℕ) (x : ℝ) : cellOf B x < 2 ^ B := by
  unfold cellOf
  rw [Nat.floor_lt (by have := Phi_pos x; positivity)]
  push_cast
  have := Phi_lt_one x
  have : (0 : ℝ) < 2 ^ B := by positivity
  nlinarith

@[fun_prop]
theorem measurable_cellOf (B : ℕ) : Measurable (cellOf B) := by
  unfold cellOf
  exact Nat.measurable_floor.comp (by fun_prop)

/-- **The cells of a standard Gaussian are uniform**: each of the `2^B` cells has probability
`2^-B`. -/
theorem measureReal_cellOf (B : ℕ) {j : ℕ} (hj : j < 2 ^ B) :
    (gaussianReal 0 1).real {x | cellOf B x = j} = 1 / 2 ^ B := by
  have h2 : (0 : ℝ) < 2 ^ B := by positivity
  have hset : {x | cellOf B x = j} =
      {x | Phi x < (j + 1) / 2 ^ B} \ {x | Phi x < j / 2 ^ B} := by
    ext x
    simp only [cellOf, mem_ofPred_eq, mem_sdiff, not_lt]
    rw [Nat.floor_eq_iff (by have := Phi_pos x; positivity), div_le_iff₀ h2, lt_div_iff₀ h2]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hj' : (j : ℝ) + 1 ≤ 2 ^ B := by exact_mod_cast hj
  rw [hset, measureReal_sdiff (fun x hx ↦ by
      simp only [mem_ofPred_eq] at hx ⊢
      exact hx.trans_le (div_le_div_of_nonneg_right (by linarith) h2.le))
    (measurableSet_lt (by fun_prop) measurable_const),
    measureReal_Phi_lt (by positivity) (by rw [div_le_one h2]; exact hj'),
    measureReal_Phi_lt (by positivity) (by rw [div_le_one h2]; linarith)]
  ring

/-! ### Reading cells from coins -/

/-- The cells read from `n` blocks of `B` coins: block `k` is the binary number whose bit `i`
(of weight `2^i`) is the coin `k B + i`. -/
def coinCells (n B : ℕ) (r : Fin (n * B) → Bool) (k : Fin n) : ℕ :=
  ∑ i : Fin B, if r (finProdFinEquiv (k, i)) then 2 ^ (i : ℕ) else 0

/-- Coin strings and tuples of cells are in bijection. -/
def coinCellsEquiv (n B : ℕ) : (Fin (n * B) → Bool) ≃ (Fin n → Fin (2 ^ B)) :=
  (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool)).symm.trans
    (Equiv.curry (Fin n) (Fin B) Bool |>.trans
      (Equiv.arrowCongr (Equiv.refl (Fin n))
        ((Equiv.arrowCongr (Equiv.refl (Fin B)) finTwoEquiv.symm).trans finFunctionFinEquiv)))

theorem coinCellsEquiv_apply (n B : ℕ) (r : Fin (n * B) → Bool) (k : Fin n) :
    (coinCellsEquiv n B r k : ℕ) = coinCells n B r k := by
  simp only [coinCellsEquiv, coinCells, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id, finFunctionFinEquiv_apply,
    Equiv.arrowCongr_symm, Equiv.curry_apply, Function.curry]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : r (finProdFinEquiv (k, i)) = true <;> simp [h] <;> rfl

/-- **The coupling of coins and Gaussians**: averaging over `n B` coins read as `n` cells is
averaging over the cells of `n` independent standard Gaussians. -/
theorem sum_coinCells_eq_integral (n B : ℕ) (F : (Fin n → ℕ) → ℝ) :
    (∑ r : Fin (n * B) → Bool, F (coinCells n B r)) / 2 ^ (n * B) =
      ∫ g, F (fun k ↦ cellOf B (g k)) ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  set μ := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  -- The coin side: a sum over tuples of cells.
  have hL : ∑ r : Fin (n * B) → Bool, F (coinCells n B r) =
      ∑ j : Fin n → Fin (2 ^ B), F (fun k ↦ (j k : ℕ)) := by
    rw [← Equiv.sum_comp (coinCellsEquiv n B).symm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    funext k
    rw [← coinCellsEquiv_apply, Equiv.apply_symm_apply]
  -- The Gaussian side: the integral of a function of finitely many cells.
  set box : (Fin n → Fin (2 ^ B)) → Set (Fin n → ℝ) := fun j ↦
    Set.pi univ fun k ↦ {x | cellOf B x = j k} with hbox
  have hboxm : ∀ j, MeasurableSet (box j) := fun j ↦
    MeasurableSet.univ_pi fun k ↦ measurableSet_eq_fun (measurable_cellOf B) measurable_const
  have hpt : ∀ g : Fin n → ℝ, F (fun k ↦ cellOf B (g k)) =
      ∑ j : Fin n → Fin (2 ^ B), (box j).indicator (fun _ ↦ F (fun k ↦ (j k : ℕ))) g := by
    intro g
    let j₀ : Fin n → Fin (2 ^ B) := fun k ↦ ⟨cellOf B (g k), cellOf_lt B (g k)⟩
    rw [Finset.sum_eq_single j₀]
    · rw [indicator_of_mem (by simp [hbox, j₀])]
    · intro j _ hj
      refine indicator_of_notMem (fun hg ↦ hj ?_) _
      funext k
      exact Fin.ext (by simpa [hbox, j₀] using (hg k (mem_univ _)).symm)
    · simp
  have hR : ∫ g, F (fun k ↦ cellOf B (g k)) ∂μ =
      ∑ j : Fin n → Fin (2 ^ B), F (fun k ↦ (j k : ℕ)) * (1 / 2 ^ B) ^ n := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ ↦ (integrable_const _).indicator (hboxm j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_indicator_const _ (hboxm j), smul_eq_mul, mul_comm]
    congr 1
    rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    simp only [← measureReal_def]
    rw [Finset.prod_congr rfl fun k _ ↦ measureReal_cellOf B (j k).2, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hL, hR, ← Finset.sum_mul, pow_mul]
  rw [div_pow, one_pow, div_eq_mul_one_div, one_div, ← pow_mul, ← pow_mul, mul_comm B n]
  simp [pow_mul]

/-- **The coupling, on tuples of cells**: the average of `F` over the tuples of `n` cells of `B`
bits is its integral over the cells of `n` independent standard Gaussians. -/
theorem sum_cells_eq_integral (n B : ℕ) (F : (Fin n → ℕ) → ℝ) :
    (∑ j : Fin n → Fin (2 ^ B), F (fun k ↦ (j k : ℕ))) / 2 ^ (n * B) =
      ∫ g, F (fun k ↦ cellOf B (g k)) ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  rw [← sum_coinCells_eq_integral]
  congr 1
  rw [← Equiv.sum_comp (coinCellsEquiv n B)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  congr 1
  funext k
  rw [coinCellsEquiv_apply]

end Gaussian
