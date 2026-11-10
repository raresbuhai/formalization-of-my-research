module

public import ABBKS26.Robust.FilterAuxEstimates
public import ABBKS26.Robust.FilterAuxWeights
public import Mathlib.Analysis.MeanInequalities

/-! Finite averages and polarization estimates for quadratic statistics. -/

@[expose] public section

namespace ABBKS26.Robust.FilterAux

open Common Matrix
open scoped BigOperators

noncomputable section

def average {ι : Type*} (s : Finset ι) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i
  map_add' f g := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

theorem average_one {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    average s 1 = 1 := by
  have hn : (s.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hs).ne'
  simp [average, hn]

theorem average_mono {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, f i ≤ g i) : average s f ≤ average s g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

theorem average_sq_center {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (a : ℝ) :
    average s (fun i ↦ (x i - average s x) ^ 2) =
      average s (fun i ↦ (x i - a) ^ 2) - (average s x - a) ^ 2 := by
  have h (c : ℝ) : average s (fun i ↦ (x i - c) ^ 2) =
      average s (fun i ↦ x i ^ 2) - 2 * c * average s x + c ^ 2 := by
    have he : (fun i ↦ (x i - c) ^ 2) =
        (fun i ↦ x i ^ 2) - (2 * c) • x + c ^ 2 • (1 : ι → ℝ) := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      ring
    rw [he, map_add, map_sub, map_smul, map_smul, average_one s hs]
    simp only [smul_eq_mul, mul_one]
  rw [h, h]
  ring

theorem sqnorm_add_le {d : ℕ} (u v : Vec d) :
    sqnorm (u + v) ≤ 2 * sqnorm u + 2 * sqnorm v := by
  have hn := Rounding.DetRoundAux.sqnorm_nonneg (u - v)
  simp only [sqnorm, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, dotProduct_comm v u] at *
  linarith only [hn]

theorem sqnorm_neg {d : ℕ} (u : Vec d) : sqnorm (-u) = sqnorm u := by
  simp [sqnorm]

theorem sqnorm_single {d : ℕ} (i : Fin d) : sqnorm (Pi.single i 1 : Vec d) = 1 := by
  classical
  simp [sqnorm]

private theorem fourth_polarization (a b c e : ℝ) :
    192 * (a * b * c * e) =
      (a + b + c + e) ^ 4 - (a + b + c - e) ^ 4 -
      (a + b - c + e) ^ 4 + (a + b - c - e) ^ 4 -
      (a - b + c + e) ^ 4 + (a - b + c - e) ^ 4 +
      (a - b - c + e) ^ 4 - (a - b - c - e) ^ 4 := by ring

private theorem fourth_polarization_map {ι : Type*}
    (E : (ι → ℝ) →ₗ[ℝ] ℝ) (a b c e : ι → ℝ) :
    192 * E (a * b * c * e) =
      E ((a + b + c + e) ^ 4) - E ((a + b + c - e) ^ 4) -
      E ((a + b - c + e) ^ 4) + E ((a + b - c - e) ^ 4) -
      E ((a - b + c + e) ^ 4) + E ((a - b + c - e) ^ 4) +
      E ((a - b - c + e) ^ 4) - E ((a - b - c - e) ^ 4) := by
  have he : (192 : ℝ) • (a * b * c * e) =
      (a + b + c + e) ^ 4 - (a + b + c - e) ^ 4 -
      (a + b - c + e) ^ 4 + (a + b - c - e) ^ 4 -
      (a - b + c + e) ^ 4 + (a - b + c - e) ^ 4 +
      (a - b - c + e) ^ 4 - (a - b - c - e) ^ 4 := by
    ext i
    exact fourth_polarization (a i) (b i) (c i) (e i)
  simpa only [map_sub, map_add, map_smul, smul_eq_mul] using congrArg E he

private theorem bilinear_comm {d : ℕ} (S : Mat d) (hS : Sᵀ = S) (u v : Vec d) :
    u ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (S *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

private theorem gaussian_polarization {d : ℕ} (S : Mat d) (hS : Sᵀ = S)
    (u v w z : Vec d) :
    192 * ((u ⬝ᵥ (S *ᵥ v)) * (w ⬝ᵥ (S *ᵥ z)) +
      (u ⬝ᵥ (S *ᵥ w)) * (v ⬝ᵥ (S *ᵥ z)) +
      (u ⬝ᵥ (S *ᵥ z)) * (v ⬝ᵥ (S *ᵥ w))) =
      3 * qform S (u + v + w + z) ^ 2 - 3 * qform S (u + v + w - z) ^ 2 -
      3 * qform S (u + v - w + z) ^ 2 + 3 * qform S (u + v - w - z) ^ 2 -
      3 * qform S (u - v + w + z) ^ 2 + 3 * qform S (u - v + w - z) ^ 2 +
      3 * qform S (u - v - w + z) ^ 2 - 3 * qform S (u - v - w - z) ^ 2 := by
  simp only [qform, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  rw [bilinear_comm S hS v u, bilinear_comm S hS w u, bilinear_comm S hS z u,
    bilinear_comm S hS w v, bilinear_comm S hS z v, bilinear_comm S hS z w]
  ring

private def projectionMap {ι : Type*} {d : ℕ} (x : ι → Vec d) :
    Vec d →ₗ[ℝ] (ι → ℝ) where
  toFun u := fun l ↦ u ⬝ᵥ x l
  map_add' u v := by ext l; exact add_dotProduct u v (x l)
  map_smul' c u := by ext l; exact smul_dotProduct c u (x l)

private theorem four_unit_norm {d : ℕ} (u v w z : Vec d)
    (hu : sqnorm u ≤ 1) (hv : sqnorm v ≤ 1)
    (hw : sqnorm w ≤ 1) (hz : sqnorm z ≤ 1) :
    sqnorm (u + v + w + z) ≤ 16 := by
  have hh := sqnorm_add_le (u + v) (w + z)
  rw [show u + v + (w + z) = u + v + w + z by abel] at hh
  linarith only [hh, sqnorm_add_le u v, sqnorm_add_le w z, hu, hv, hw, hz]

theorem mixed_fourth_error {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (x : ι → Vec d) (S : Mat d) (hS : Sᵀ = S) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ u, |E (fun l ↦ (u ⬝ᵥ x l) ^ 4) - 3 * qform S u ^ 2| ≤
      ε * sqnorm u ^ 2) (i j k l : Fin d) :
    |E (fun a ↦ x a i * x a j * x a k * x a l) -
      (S i j * S k l + S i k * S j l + S i l * S j k)| ≤ 11 * ε := by
  classical
  let u : Vec d := Pi.single i 1
  let v : Vec d := Pi.single j 1
  let w : Vec d := Pi.single k 1
  let z : Vec d := Pi.single l 1
  let L := projectionMap x
  have hn (a b c e : Vec d) (ha : sqnorm a ≤ 1) (hb : sqnorm b ≤ 1)
      (hc : sqnorm c ≤ 1) (he : sqnorm e ≤ 1) :
      |E (L (a + b + c + e) ^ 4) - 3 * qform S (a + b + c + e) ^ 2| ≤
        256 * ε := by
    have hh := four_unit_norm a b c e ha hb hc he
    have hh' := pow_le_pow_left₀
      (Rounding.DetRoundAux.sqnorm_nonneg (a + b + c + e)) hh 2
    exact (h _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hh' hε])
  have hu : sqnorm u ≤ 1 := (sqnorm_single i).le
  have hv : sqnorm v ≤ 1 := (sqnorm_single j).le
  have hw : sqnorm w ≤ 1 := (sqnorm_single k).le
  have hz : sqnorm z ≤ 1 := (sqnorm_single l).le
  have h0 := abs_le.mp (hn u v w z hu hv hw hz)
  have h1 := abs_le.mp (hn u v w (-z) hu hv hw (by simpa only [sqnorm_neg] using hz))
  have h2 := abs_le.mp (hn u v (-w) z hu hv
    (by simpa only [sqnorm_neg] using hw) hz)
  have h3 := abs_le.mp (hn u v (-w) (-z) hu hv
    (by simpa only [sqnorm_neg] using hw) (by simpa only [sqnorm_neg] using hz))
  have h4 := abs_le.mp (hn u (-v) w z hu
    (by simpa only [sqnorm_neg] using hv) hw hz)
  have h5 := abs_le.mp (hn u (-v) w (-z) hu
    (by simpa only [sqnorm_neg] using hv) hw (by simpa only [sqnorm_neg] using hz))
  have h6 := abs_le.mp (hn u (-v) (-w) z hu
    (by simpa only [sqnorm_neg] using hv) (by simpa only [sqnorm_neg] using hw) hz)
  have h7 := abs_le.mp (hn u (-v) (-w) (-z) hu
    (by simpa only [sqnorm_neg] using hv) (by simpa only [sqnorm_neg] using hw)
    (by simpa only [sqnorm_neg] using hz))
  simp only [← sub_eq_add_neg] at h1 h2 h3 h4 h5 h6 h7
  have hp := fourth_polarization_map E (L u) (L v) (L w) (L z)
  simp only [← L.map_add, ← L.map_sub] at hp
  have hg := gaussian_polarization S hS u v w z
  have he : E (L u * L v * L w * L z) =
      E (fun a ↦ x a i * x a j * x a k * x a l) := by
    congr 1
    ext a
    simp [L, projectionMap, u, v, w, z]
  have hg' : u ⬝ᵥ (S *ᵥ v) = S i j := by simp [u, v, mulVec_single]
  have hgvw : v ⬝ᵥ (S *ᵥ w) = S j k := by simp [v, w, mulVec_single]
  have hgvz : v ⬝ᵥ (S *ᵥ z) = S j l := by simp [v, z, mulVec_single]
  have hguw : u ⬝ᵥ (S *ᵥ w) = S i k := by simp [u, w, mulVec_single]
  have hguz : u ⬝ᵥ (S *ᵥ z) = S i l := by simp [u, z, mulVec_single]
  have hgwz : w ⬝ᵥ (S *ᵥ z) = S k l := by simp [w, z, mulVec_single]
  rw [he] at hp
  rw [hg', hgvw, hgvz, hguw, hguz, hgwz] at hg
  apply abs_le.mpr
  constructor <;> linarith only [hp, hg, hε, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2,
    h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

theorem mixed_second_error {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (x : ι → Vec d) (S : Mat d) (hS : Sᵀ = S) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ u, |E (fun l ↦ (u ⬝ᵥ x l) ^ 2) - qform S u| ≤ ε * sqnorm u)
    (i j : Fin d) : |E (fun a ↦ x a i * x a j) - S i j| ≤ 2 * ε := by
  classical
  let u : Vec d := Pi.single i 1
  let v : Vec d := Pi.single j 1
  let L := projectionMap x
  have hp : (4 : ℝ) • (L u * L v) = (L (u + v)) ^ 2 - (L (u - v)) ^ 2 := by
    ext l
    change 4 * ((u ⬝ᵥ x l) * (v ⬝ᵥ x l)) =
      ((u + v) ⬝ᵥ x l) ^ 2 - ((u - v) ⬝ᵥ x l) ^ 2
    rw [add_dotProduct, sub_dotProduct]
    ring
  have hp' := congrArg E hp
  rw [E.map_smul, E.map_sub] at hp'
  simp only [smul_eq_mul] at hp'
  have hg : 4 * (u ⬝ᵥ (S *ᵥ v)) = qform S (u + v) - qform S (u - v) := by
    simp only [qform, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
      dotProduct_add, dotProduct_sub]
    rw [bilinear_comm S hS v u]
    ring
  have hn : sqnorm (u + v) ≤ 4 := by
    have hh := sqnorm_add_le u v
    rw [show sqnorm u = 1 from sqnorm_single i,
      show sqnorm v = 1 from sqnorm_single j] at hh
    linarith only [hh]
  have hn' : sqnorm (u - v) ≤ 4 := by
    have hh := sqnorm_add_le u (-v)
    rw [sqnorm_neg, show sqnorm u = 1 from sqnorm_single i,
      show sqnorm v = 1 from sqnorm_single j] at hh
    rw [← sub_eq_add_neg] at hh
    linarith only [hh]
  have hbplus : ε * sqnorm (u + v) ≤ 4 * ε := by
    nlinarith only [mul_le_mul_of_nonneg_left hn hε]
  have hbminus : ε * sqnorm (u - v) ≤ 4 * ε := by
    nlinarith only [mul_le_mul_of_nonneg_left hn' hε]
  have hplus := abs_le.mp ((h (u + v)).trans hbplus)
  have hminus := abs_le.mp ((h (u - v)).trans hbminus)
  have he : E (L u * L v) = E (fun a ↦ x a i * x a j) := by
    congr 1
    ext l
    simp [L, projectionMap, u, v]
  rw [he] at hp'
  change 4 * E (fun a ↦ x a i * x a j) =
    E (fun a ↦ ((u + v) ⬝ᵥ x a) ^ 2) - E (fun a ↦ ((u - v) ⬝ᵥ x a) ^ 2) at hp'
  have hcross : u ⬝ᵥ (S *ᵥ v) = S i j := by simp [u, v, mulVec_single]
  rw [hcross] at hg
  exact abs_le.mpr ⟨by linarith only [hp', hg, hplus.1, hminus.2],
    by linarith only [hp', hg, hplus.2, hminus.1]⟩

theorem matrix_l1_le_dim {d : ℕ} (A : Mat d) (hA : frobSq A ≤ 1) :
    (∑ i, ∑ j, |A i j|) ≤ d := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d)) (fun _ ↦ (1 : ℝ))
      (fun ij ↦ |A ij.1 ij.2|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Fintype.sum_prod_type, sq_abs] at hc
  have hh := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (d : ℝ) * d)
  have hs : 0 ≤ ∑ i, ∑ j, |A i j| := by positivity
  dsimp only [frobSq] at hh
  nlinarith only [hc, hh, hs, Nat.cast_nonneg (α := ℝ) d]

def symmetricPart {d : ℕ} (A : Mat d) : Mat d := (1 / 2 : ℝ) • (A + Aᵀ)

theorem symmetricPart_symmetric {d : ℕ} (A : Mat d) :
    (symmetricPart A)ᵀ = symmetricPart A := by
  ext i j
  simp only [symmetricPart, transpose_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

theorem symmetricPart_frob_le {d : ℕ} (A : Mat d) :
    frobSq (symmetricPart A) ≤ frobSq A := by
  have ht : frobSq Aᵀ = frobSq A := by
    simp only [frobSq, transpose_apply]
    rw [Finset.sum_comm]
  calc
    _ ≤ (1 / 2 : ℝ) * (frobSq A + frobSq Aᵀ) := by
      simp only [frobSq, symmetricPart, Matrix.smul_apply, Matrix.add_apply,
        smul_eq_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith only [sq_nonneg (A i j - Aᵀ i j)]
    _ = _ := by rw [ht]; ring

theorem qform_symmetricPart {d : ℕ} (A : Mat d) (v : Vec d) :
    qform (symmetricPart A) v = qform A v := by
  have ht : qform Aᵀ v = qform A v := by
    change v ⬝ᵥ (Aᵀ *ᵥ v) = v ⬝ᵥ (A *ᵥ v)
    calc
      _ = (A *ᵥ v) ⬝ᵥ v := by
        rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose]
      _ = _ := dotProduct_comm _ _
  simp only [symmetricPart, qform, smul_mulVec, add_mulVec,
    dotProduct_smul, dotProduct_add, smul_eq_mul]
  change (1 / 2 : ℝ) * (qform A v + qform Aᵀ v) = qform A v
  rw [ht]
  ring

theorem average_quadratic {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (A : Mat d) (x : ι → Vec d) :
    E (fun l ↦ qform A (x l)) = ∑ i, ∑ j, A i j * E (fun l ↦ x l i * x l j) := by
  have he : (fun l ↦ qform A (x l)) =
      ∑ i, ∑ j, A i j • (fun l ↦ x l i * x l j) := by
    ext l
    simp only [qform, dotProduct, mulVec, Finset.mul_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem trace_inner {d : ℕ} (A S : Mat d) (hS : Sᵀ = S) :
    (A * S).trace = ∑ i, ∑ j, A i j * S i j := by
  simp only [trace, diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : S j i = S i j := congrFun (congrFun hS i) j
  rw [he]

theorem quadratic_mean_error {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (x : ι → Vec d) (A S : Mat d) (hn : frobSq A ≤ 1) (hS : Sᵀ = S)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i j, |E (fun l ↦ x l i * x l j) - S i j| ≤ ε) :
    |E (fun l ↦ qform A (x l)) - (A * S).trace| ≤ ε * d := by
  rw [average_quadratic, trace_inner A S hS, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, |A i j * (E (fun l ↦ x l i * x l j) - S i j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i j) (abs_nonneg _)
    _ = ε * ∑ i, ∑ j, |A i j| := by simp only [Finset.sum_mul, mul_comm ε]
    _ ≤ _ := mul_le_mul_of_nonneg_left (matrix_l1_le_dim A hn) hε

theorem average_quadratic_sq {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (A : Mat d) (x : ι → Vec d) :
    E (fun a ↦ qform A (x a) ^ 2) = ∑ i, ∑ j, ∑ k, ∑ l,
      (A i j * A k l) * E (fun a ↦ x a i * x a j * x a k * x a l) := by
  have hq (z : Vec d) : qform A z = ∑ i, ∑ j, A i j * z i * z j := by
    simp only [qform, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : (fun a ↦ qform A (x a) ^ 2) = ∑ i, ∑ j, ∑ k, ∑ l,
      (A i j * A k l) • (fun a ↦ x a i * x a j * x a k * x a l) := by
    ext a
    simp only [hq, pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem gaussian_quadratic_sq {d : ℕ} (A S : Mat d) (hA : Aᵀ = A) (hS : Sᵀ = S) :
    (∑ i, ∑ j, ∑ k, ∑ l, (A i j * A k l) *
      (S i j * S k l + S i k * S j l + S i l * S j k)) =
      (A * S).trace ^ 2 + 2 * (A * S * A * S).trace := by
  have h₁ : (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (S i j * S k l)) =
      (A * S).trace ^ 2 := by
    rw [trace_inner A S hS]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have h₃ : (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (S i l * S j k)) =
      (A * S * A * S).trace := by
    simp only [trace, diag, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => arg 2; ext k; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    have hs : S l i = S i l := congrFun (congrFun hS i) l
    rw [hs]
    ring
  have h₂ : (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (S i k * S j l)) =
      (A * S * A * S).trace := by
    rw [← h₃]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    have ha : A l k = A k l := congrFun (congrFun hA k) l
    rw [ha]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃]
  ring

theorem quadratic_sq_error {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (x : ι → Vec d) (A S : Mat d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1)
    (hS : Sᵀ = S) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i j k l, |E (fun a ↦ x a i * x a j * x a k * x a l) -
      (S i j * S k l + S i k * S j l + S i l * S j k)| ≤ ε) :
    |E (fun a ↦ qform A (x a) ^ 2) -
      ((A * S).trace ^ 2 + 2 * (A * S * A * S).trace)| ≤ ε * d ^ 2 := by
  rw [average_quadratic_sq, ← gaussian_quadratic_sq A S hA hS]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, |(A i j * A k l) *
        (E (fun a ↦ x a i * x a j * x a k * x a l) -
          (S i j * S k l + S i k * S j l + S i l * S j k))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦
            Finset.abs_sum_le_sum_abs _ _)))
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, |A i j| * |A k l| * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (h i j k l) (by positivity)
    _ = ε * (∑ i, ∑ j, |A i j|) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm ε]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (matrix_l1_le_dim A hn) 2) hε

theorem entries_le_of_qform_le {d : ℕ} (S : Mat d) (hS : S.PosSemidef) (c : ℝ)
    (h : ∀ u, qform S u ≤ c * sqnorm u) (i j : Fin d) : |S i j| ≤ c := by
  classical
  let u : Vec d := Pi.single i 1
  let v : Vec d := Pi.single j 1
  have hdiag (k : Fin d) : S k k ≤ c := by
    simpa [qform, sqnorm, mulVec_single] using h (Pi.single k 1)
  have hplus : 0 ≤ qform S (u + v) := by
    simpa only [qform, star_trivial] using hS.dotProduct_mulVec_nonneg (u + v)
  have hminus : 0 ≤ qform S (u - v) := by
    simpa only [qform, star_trivial] using hS.dotProduct_mulVec_nonneg (u - v)
  simp only [qform, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub] at hplus hminus
  simp only [u, v, single_dotProduct, mulVec_single, op_smul_eq_smul,
    one_smul, col_apply, one_mul] at hplus hminus
  have hji : S j i = S i j := congrFun (congrFun
    (show Sᵀ = S by simpa only [conjTranspose_eq_transpose_of_trivial] using hS.1.eq) i) j
  exact abs_le.mpr ⟨by linarith only [hplus, hji, hdiag i, hdiag j],
    by linarith only [hminus, hji, hdiag i, hdiag j]⟩

theorem linear_square_about {ι : Type*} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hE : E 1 = 1) (x : ι → ℝ) (c : ℝ) :
    E (fun i ↦ (x i - c) ^ 2) = E (x ^ 2) - 2 * c * E x + c ^ 2 := by
  have he : (fun i ↦ (x i - c) ^ 2) =
      x ^ 2 - (2 * c) • x + c ^ 2 • (1 : ι → ℝ) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      Pi.pow_apply]
    ring
  rw [he, E.map_add, E.map_sub, E.map_smul, E.map_smul, hE]
  simp only [smul_eq_mul, mul_one]

theorem average_change_center {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (a b B η : ℝ)
    (hvar : average s (fun l ↦ (x l - a) ^ 2) ≤ B)
    (hmean : (average s (fun l ↦ x l - a)) ^ 2 ≤ η) :
    average s (fun l ↦ (x l - b) ^ 2) ≤ B + (101 / 100 : ℝ) * (a - b) ^ 2 + 100 * η := by
  let f := fun l ↦ x l - a
  have hh := linear_square_about (average s) (average_one s hs) f (-(a - b))
  have he : (fun l ↦ (f l - -(a - b)) ^ 2) = (fun l ↦ (x l - b) ^ 2) := by
    ext l
    dsimp only [f]
    congr 1
    ring
  rw [he] at hh
  change average s (f ^ 2) ≤ B at hvar
  change average s f ^ 2 ≤ η at hmean
  nlinarith only [hh, hvar, hmean,
    sq_nonneg (10 * average s f - (a - b) / 10)]

theorem quadratic_center_bound {ι : Type*} {d : ℕ} (E : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hE : E 1 = 1) (x : ι → Vec d) (A S : Mat d)
    (hA : Aᵀ = A) (hn : frobSq A ≤ 1) (hS : S.PosSemidef)
    (c ε₂ ε₄ : ℝ) (hc : 0 ≤ c) (h₂ : 0 ≤ ε₂) (h₄ : 0 ≤ ε₄)
    (hupper : ∀ u, qform S u ≤ c * sqnorm u)
    (hsecond : ∀ i j, |E (fun a ↦ x a i * x a j) - S i j| ≤ ε₂)
    (hfourth : ∀ i j k l, |E (fun a ↦ x a i * x a j * x a k * x a l) -
      (S i j * S k l + S i k * S j l + S i l * S j k)| ≤ ε₄) :
    E (fun a ↦ (qform A (x a) - (A * S).trace) ^ 2) ≤
      2 * c ^ 2 + (ε₄ + 2 * c * ε₂) * d ^ 2 := by
  have hs : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.1.eq
  have hmean := quadratic_mean_error E x A S hn hs ε₂ h₂ hsecond
  have hmoment := quadratic_sq_error E x A S hA hn hs ε₄ h₄ hfourth
  have htrace : |(A * S).trace| ≤ c * d := by
    have hh := quadratic_mean_error (0 : (Unit → ℝ) →ₗ[ℝ] ℝ)
      (fun _ ↦ (0 : Vec d)) A S hn hs c hc
      (fun i j ↦ by simpa using entries_le_of_qform_le S hS c hupper i j)
    simpa only [LinearMap.zero_apply, zero_sub, abs_neg] using hh
  have hprod : |(A * S).trace *
      (E (fun a ↦ qform A (x a)) - (A * S).trace)| ≤ c * ε₂ * d ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (c * d) * (ε₂ * d) := mul_le_mul htrace hmean (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hvar := linear_square_about E hE (fun a ↦ qform A (x a)) (A * S).trace
  have hquad := (trace_quadratic_le A S hA hS c hc hupper).trans
    (mul_le_of_le_one_right (sq_nonneg c) hn)
  have hu := (abs_le.mp hmoment).2
  have hl := (abs_le.mp hprod).1
  change E (fun a ↦ (qform A (x a) - (A * S).trace) ^ 2) =
    E (fun a ↦ qform A (x a) ^ 2) -
      2 * (A * S).trace * E (fun a ↦ qform A (x a)) + (A * S).trace ^ 2 at hvar
  nlinarith only [hu, hl, hvar, hquad]

theorem qform_add_symmetric {d : ℕ} (A : Mat d) (hA : Aᵀ = A) (x y : Vec d) :
    qform A (x + y) = qform A x + 2 * ((A *ᵥ y) ⬝ᵥ x) + qform A y := by
  have hh : (A *ᵥ y) ⬝ᵥ x = x ⬝ᵥ (A *ᵥ y) := dotProduct_comm _ _
  simp only [qform, mulVec_add, add_dotProduct, dotProduct_add]
  rw [bilinear_comm A hA y x, hh]
  ring

theorem qform_sub_symmetric {d : ℕ} (A : Mat d) (hA : Aᵀ = A) (x y : Vec d) :
    qform A (x - y) = qform A x - 2 * ((A *ᵥ y) ⬝ᵥ x) + qform A y := by
  rw [sub_eq_add_neg, qform_add_symmetric A hA]
  simp only [mulVec_neg, neg_dotProduct, qform, dotProduct_neg, neg_neg]
  ring

theorem covariance_conjugate {ι : Type*} {d : ℕ} (s : Finset ι) (w : ι → ℝ)
    (z : ι → Vec d) (W : ℝ) (T : Mat d) :
    T * (W⁻¹ • ∑ l ∈ s, w l • vecMulVec (z l) (z l)) * Tᵀ =
      W⁻¹ • ∑ l ∈ s, w l • vecMulVec (T *ᵥ z l) (T *ᵥ z l) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

theorem trace_quadratic_average {ι : Type*} {d : ℕ} (s : Finset ι) (w : ι → ℝ)
    (z : ι → Vec d) (W : ℝ) (T A : Mat d) :
    (A * (T * (W⁻¹ • ∑ l ∈ s, w l • vecMulVec (z l) (z l)) * Tᵀ)).trace =
      W⁻¹ * ∑ l ∈ s, w l * qform A (T *ᵥ z l) := by
  rw [covariance_conjugate]
  simp only [Matrix.mul_smul, Finset.mul_sum, trace_smul, trace_sum, smul_eq_mul,
    mul_vecMulVec, trace_vecMulVec]
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_comm]
  rfl

theorem frob_dual_witness {d : ℕ} (F : Mat d) (hF : Fᵀ = F) :
    ∃ A : Mat d, Aᵀ = A ∧ frobSq A ≤ 1 ∧ (A * F).trace ^ 2 = frobSq F := by
  have hfn : 0 ≤ frobSq F := Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  by_cases hz : frobSq F = 0
  · exact ⟨0, by simp, by simp [frobSq], by simp [hz]⟩
  have hfpos : 0 < frobSq F := lt_of_le_of_ne hfn (Ne.symm hz)
  let r := Real.sqrt (frobSq F)
  have hr : 0 < r := Real.sqrt_pos.mpr hfpos
  have hrs : r ^ 2 = frobSq F := Real.sq_sqrt hfn
  have ht : (F * F).trace = frobSq F := by
    rw [trace_inner F F hF]
    simp only [frobSq, pow_two]
  refine ⟨r⁻¹ • F, ?_, ?_, ?_⟩
  · rw [transpose_smul, hF]
  · have he : frobSq (r⁻¹ • F) = r⁻¹ ^ 2 * frobSq F := by
      simp only [frobSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    rw [he, ← hrs, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  · rw [smul_mul, trace_smul, smul_eq_mul, ht, mul_pow, inv_pow, ← hrs]
    field_simp

theorem le_of_congruence {d : ℕ} (T A B : Mat d) (hT : T.det ≠ 0)
    (h : LE (T * A * Tᵀ) (T * B * Tᵀ)) : LE A B := by
  intro u
  let v := Tᵀ⁻¹ *ᵥ u
  have he : Tᵀ *ᵥ v = u := by
    dsimp only [v]
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (show Tᵀ.det ≠ 0 by simpa only [det_transpose] using hT)), one_mulVec]
  have hq (S : Mat d) : qform (T * S * Tᵀ) v = qform S u := by
    have hh : qform (T * S * Tᵀ) v = qform S (Tᵀ *ᵥ v) := by
      simp only [qform, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simpa only [he] using hh
  simpa only [hq] using h v

theorem component_moment_estimate {ι : Type*} {d : ℕ} (s : Finset ι)
    (hs : s.Nonempty) (x : ι → Vec d) (A S : Mat d) (ν : Vec d)
    (hA : Aᵀ = A) (hn : frobSq A ≤ 1) (hS : S.PosSemidef)
    (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hd : δ * ((d : ℝ) ^ 2 + 1) ≤ 1 / 10000)
    (hupper : ∀ u, qform S u ≤ c * sqnorm u) (hν : sqnorm ν ≤ c)
    (hfirst : ∀ u, (average s (fun l ↦ u ⬝ᵥ x l)) ^ 2 ≤ 4 * δ ^ 2 * qform S u)
    (hsecond : ∀ u, |average s (fun l ↦ (u ⬝ᵥ x l) ^ 2) - qform S u| ≤
      4 * δ * qform S u)
    (hfourth : ∀ u, |average s (fun l ↦ (u ⬝ᵥ x l) ^ 4) - 3 * qform S u ^ 2| ≤
      16 * δ * qform S u ^ 2) :
    let f := fun l ↦ qform A (x l + ν) - ((A * S).trace + qform A ν)
    average s (f ^ 2) ≤ (121 / 10 : ℝ) * c ^ 2 ∧
      (average s f) ^ 2 ≤ c ^ 2 / 100000 := by
  let E := average s
  let q := fun l ↦ qform A (x l) - (A * S).trace
  let b := A *ᵥ ν
  let t := fun l ↦ b ⬝ᵥ x l
  let f := fun l ↦ qform A (x l + ν) - ((A * S).trace + qform A ν)
  have hE : E 1 = 1 := average_one s hs
  have hδsmall : δ ≤ 1 / 10000 := by
    nlinarith only [hd, mul_nonneg hδ (sq_nonneg (d : ℝ))]
  have hδdim : δ * (d : ℝ) ^ 2 ≤ 1 / 10000 := by linarith only [hd, hδ]
  have hδlin : δ * d ≤ 1 / 10000 := by
    nlinarith only [hd, mul_nonneg hδ (sq_nonneg ((d : ℝ) - 1))]
  have hbnorm : sqnorm b ≤ c := by
    exact (sqnorm_mulVec_le A ν).trans
      ((mul_le_of_le_one_left (Rounding.DetRoundAux.sqnorm_nonneg ν) hn).trans hν)
  have hb : qform S b ≤ c ^ 2 := by
    exact (hupper b).trans (by nlinarith only [mul_le_mul_of_nonneg_left hbnorm hc])
  have hs₂ (u : Vec d) : |E (fun l ↦ (u ⬝ᵥ x l) ^ 2) - qform S u| ≤
      (4 * δ * c) * sqnorm u := by
    exact (hsecond u).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left (hupper u) (by positivity : 0 ≤ 4 * δ)])
  have hs₄ (u : Vec d) : |E (fun l ↦ (u ⬝ᵥ x l) ^ 4) - 3 * qform S u ^ 2| ≤
      (16 * δ * c ^ 2) * sqnorm u ^ 2 := by
    have hz : 0 ≤ qform S u := by
      simpa only [qform, star_trivial] using hS.dotProduct_mulVec_nonneg u
    have hh := pow_le_pow_left₀ hz (hupper u) 2
    exact (hfourth u).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 16 * δ)])
  have hsym : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.1.eq
  have h₂ := mixed_second_error E x S hsym (4 * δ * c) (by positivity) hs₂
  have h₄ := mixed_fourth_error E x S hsym (16 * δ * c ^ 2) (by positivity) hs₄
  have hq : E (q ^ 2) ≤ (101 / 50 : ℝ) * c ^ 2 := by
    have hh := quadratic_center_bound E hE x A S hA hn hS c
      (2 * (4 * δ * c)) (11 * (16 * δ * c ^ 2)) hc (by positivity) (by positivity)
      hupper h₂ h₄
    change E (q ^ 2) ≤ _ at hh
    have hh' := mul_le_mul_of_nonneg_right hδdim (sq_nonneg c)
    nlinarith only [hh, hh', sq_nonneg c]
  have ht : E (t ^ 2) ≤ (2501 / 2500 : ℝ) * c ^ 2 := by
    have hh := (abs_le.mp (hsecond b)).2
    have hh' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 + 4 * δ)
    have hh'' := mul_le_mul_of_nonneg_right hδsmall (sq_nonneg c)
    change E (t ^ 2) - qform S b ≤ _ at hh
    nlinarith only [hh, hh', hh'']
  have hf : f = q + (2 : ℝ) • t := by
    ext l
    change qform A (x l + ν) - ((A * S).trace + qform A ν) =
      qform A (x l) - (A * S).trace + 2 * ((A *ᵥ ν) ⬝ᵥ x l)
    rw [qform_add_symmetric A hA]
    ring
  have hfsq : E (f ^ 2) ≤ 2 * E (q ^ 2) + 8 * E (t ^ 2) := by
    calc
      _ ≤ E ((2 : ℝ) • q ^ 2 + (8 : ℝ) • t ^ 2) := by
        apply average_mono
        intro l _
        rw [hf]
        change (q l + 2 * t l) ^ 2 ≤ 2 * q l ^ 2 + 8 * t l ^ 2
        nlinarith only [sq_nonneg (q l - 2 * t l)]
      _ = _ := by rw [E.map_add, E.map_smul, E.map_smul]; rfl
  have hmeanq : |E q| ≤ (8 / 10000 : ℝ) * c := by
    have hh := quadratic_mean_error E x A S hn hsym (2 * (4 * δ * c))
      (by positivity) h₂
    have he : q = (fun l ↦ qform A (x l)) - (A * S).trace • (1 : ι → ℝ) := by
      ext l
      simp [q]
    rw [he, E.map_sub, E.map_smul, hE]
    simp only [smul_eq_mul, mul_one]
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hδlin hc])
  have hmeant : (E t) ^ 2 ≤ (4 / 100000000 : ℝ) * c ^ 2 := by
    have hh := hfirst b
    have h₁ := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * δ ^ 2)
    have h₂ := pow_le_pow_left₀ hδ hδsmall 2
    have h₃ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg c)
    change E t ^ 2 ≤ _ at hh
    nlinarith only [hh, h₁, h₃]
  change E (f ^ 2) ≤ _ ∧ E f ^ 2 ≤ _
  refine ⟨by linarith only [hfsq, hq, ht, sq_nonneg c], ?_⟩
  have hh := pow_le_pow_left₀ (abs_nonneg _) hmeanq 2
  rw [sq_abs, mul_pow] at hh
  rw [hf, E.map_add, E.map_smul]
  simp only [smul_eq_mul]
  nlinarith only [hh, hmeant, sq_nonneg (E q - 2 * E t), sq_nonneg c]

theorem weighted_mean_shift_general {ι : Type*} [Finite ι] [DecidableEq ι]
    (x w : ι → ℝ) (G B : Finset ι) (hdis : Disjoint G B)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hG : G.Nonempty)
    (μG μw VG Vw β ρ ω : ℝ)
    (hg : μG = (G.card : ℝ)⁻¹ * ∑ i ∈ G, x i)
    (hwmean : μw = (∑ i ∈ G ∪ B, w i)⁻¹ * ∑ i ∈ G ∪ B, w i * x i)
    (hb : β = (G.card : ℝ)⁻¹ * ∑ i ∈ B, w i)
    (hr : ρ = (G.card : ℝ)⁻¹ * ∑ i ∈ G, (1 - w i))
    (ho : ω = 1 - ρ + β) (ho0 : 0.9 ≤ ω) (hβ : β ≤ ω / 16)
    (hVG : VG = (G.card : ℝ)⁻¹ * ∑ i ∈ G, (x i - μG) ^ 2)
    (hVw : Vw = (∑ i ∈ G ∪ B, w i)⁻¹ *
      ∑ i ∈ G ∪ B, w i * (x i - μw) ^ 2) :
    (μw - μG) ^ 2 ≤ 4 * β * Vw + 5 * ρ * VG := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  apply weighted_mean_shift (x ∘ e.symm) (w ∘ e.symm)
    (G.map e.toEmbedding) (B.map e.toEmbedding)
    ((Finset.disjoint_map _).mpr hdis) (fun i ↦ hw (e.symm i))
    hG.map μG μw VG Vw β ρ ω
  · simpa using hg
  · simpa only [← Finset.map_union, Finset.sum_map, Equiv.toEmbedding_apply,
      Function.comp_apply, Equiv.symm_apply_apply] using hwmean
  · simpa using hb
  · simpa using hr
  · exact ho
  · exact ho0
  · exact hβ
  · simpa using hVG
  · simpa only [← Finset.map_union, Finset.sum_map, Equiv.toEmbedding_apply,
      Function.comp_apply, Equiv.symm_apply_apply] using hVw

theorem trace_power_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (p : ℕ) (hp : 2 ≤ p) :
    (A ^ p).trace ^ (1 + 1 / (p : ℝ)) ≤
      (Fintype.card ι : ℝ) ^ (1 / (p : ℝ)) * (A ^ (p + 1)).trace := by
  have htrace (q : ℕ) : (A ^ q).trace = ∑ i, hA.1.eigenvalues i ^ q := by
    conv_lhs => rw [hA.1.spectral_theorem, ← map_pow]
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    simp [Matrix.diagonal_pow]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [htrace, htrace]
  have hr : 1 ≤ 1 + 1 / (p : ℝ) := by linarith [one_div_pos.mpr hp0]
  have hs := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ hr
    (fun i (_ : i ∈ Finset.univ) ↦ pow_nonneg (hA.eigenvalues_nonneg i) p)
  simp only [Finset.card_univ, add_sub_cancel_left] at hs
  convert hs using 2
  congr 1
  ext i
  symm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hA.eigenvalues_nonneg i)]
  rw [show (p : ℝ) * (1 + 1 / (p : ℝ)) = p + 1 by field_simp]
  rw [← Nat.cast_add_one, Real.rpow_natCast]

theorem feature_covariance_form {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (w : ι → ℝ) (φ : ι → κ → ℝ) (W : ℝ) (a : κ → ℝ) :
    let c := W⁻¹ • ∑ i ∈ s, w i • φ i
    a ⬝ᵥ ((W⁻¹ • ∑ i ∈ s, w i • vecMulVec (φ i - c) (φ i - c)) *ᵥ a) =
      W⁻¹ * ∑ i ∈ s, w i *
        (a ⬝ᵥ φ i - W⁻¹ * ∑ j ∈ s, w j * (a ⬝ᵥ φ j)) ^ 2 := by
  dsimp only
  simp only [smul_mulVec, sum_mulVec, dotProduct_smul, dotProduct_sum,
    vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_comm (φ i - _), dotProduct_sub]
  simp only [dotProduct_smul, dotProduct_sum, smul_eq_mul]
  ring

theorem covariance_sum_form {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (w : ι → ℝ) (z : ι → κ → ℝ) (W : ℝ) (a : κ → ℝ) :
    a ⬝ᵥ ((W⁻¹ • ∑ i ∈ s, w i • vecMulVec (z i) (z i)) *ᵥ a) =
      W⁻¹ * ∑ i ∈ s, w i * (a ⬝ᵥ z i) ^ 2 := by
  simp only [smul_mulVec, sum_mulVec, dotProduct_smul, dotProduct_sum,
    vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_comm (z i), pow_two]

theorem column_norm_sum {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ) :
    (∑ j, (fun i ↦ H i j) ⬝ᵥ (fun i ↦ H i j)) = (Hᵀ * H).trace := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply, dotProduct]

theorem column_form_sum {ι : Type*} [Fintype ι] (H V : Matrix ι ι ℝ) :
    (∑ j, (fun i ↦ H i j) ⬝ᵥ (V *ᵥ fun i ↦ H i j)) = (Hᵀ * V * H).trace := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply, mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem column_square_sum {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (hH : Hᵀ = H) (z : ι → ℝ) :
    z ⬝ᵥ ((H * H) *ᵥ z) = ∑ j, ((fun i ↦ H i j) ⬝ᵥ z) ^ 2 := by
  have hc (j : ι) : (fun i ↦ H i j) = H j := by
    ext i
    exact congrFun (congrFun hH j) i
  simp_rw [hc]
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hH]
  simp only [dotProduct, mulVec, pow_two]

theorem failed_trace_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (p : ℕ) (hp : 2 ≤ p)
    (σ : ℝ) (hσ : 0 < σ)
    (hd : (Fintype.card ι : ℝ) ^ (1 / (p : ℝ)) ≤ Real.sqrt 2)
    (hf : (16 * σ) ^ p < (A ^ p).trace) :
    8 * σ * (A ^ p).trace < (A ^ (p + 1)).trace := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have ht : 0 < (A ^ p).trace := (pow_pos (by positivity) p).trans hf
  have hu : 0 ≤ (A ^ (p + 1)).trace := (hA.pow _).trace_nonneg
  have hr : 16 * σ < (A ^ p).trace ^ (1 / (p : ℝ)) := by
    have hh := Real.rpow_lt_rpow (pow_nonneg (by positivity : 0 ≤ 16 * σ) p) hf
      (one_div_pos.mpr hp0)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 16 * σ),
      mul_one_div_cancel hp0.ne', Real.rpow_one] at hh
  have hs := trace_power_mean A hA p hp
  rw [Real.rpow_add ht, Real.rpow_one] at hs
  have hd2 : (Fintype.card ι : ℝ) ^ (1 / (p : ℝ)) ≤ 2 := hd.trans (by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh, Real.sqrt_nonneg (2 : ℝ)])
  have hb := mul_le_mul_of_nonneg_right hd2 hu
  nlinarith only [hs, hb, mul_lt_mul_of_pos_left hr ht]

private theorem spectral_sum_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A = ∑ j, hA.eigenvalues j •
      vecMulVec (hA.eigenvectorBasis j) (hA.eigenvectorBasis j) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply,
    star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec_apply, transpose_apply, Function.comp_apply,
    RCLike.ofReal_real_eq_id, id, hA.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem qform_upper_of_trace_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (p : ℕ) (hp : p ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (htrace : (A ^ p).trace ≤ c ^ p) (v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
  have he (j : ι) : hA.1.eigenvalues j ≤ c := by
    have ht : (A ^ p).trace = ∑ i, hA.1.eigenvalues i ^ p := by
      conv_lhs => rw [hA.1.spectral_theorem, ← map_pow]
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
      simp [Matrix.diagonal_pow]
    apply (pow_le_pow_iff_left₀ (hA.eigenvalues_nonneg j) hc hp).mp
    rw [ht] at htrace
    exact (Finset.single_le_sum (fun i _ ↦ pow_nonneg (hA.eigenvalues_nonneg i) p)
      (Finset.mem_univ j)).trans htrace
  have hone : (1 : Matrix ι ι ℝ) =
      ∑ j, vecMulVec (hA.1.eigenvectorBasis j) (hA.1.eigenvectorBasis j) := by
    have hh := Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
    rw [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hh
    rw [← hh]
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]
  have hnorm : v ⬝ᵥ v = ∑ j, ((hA.1.eigenvectorBasis j) ⬝ᵥ v) ^ 2 := by
    calc
      _ = v ⬝ᵥ ((1 : Matrix ι ι ℝ) *ᵥ v) := by rw [one_mulVec]
      _ = _ := by
        rw [hone]
        simp only [sum_mulVec, dotProduct_sum, vecMulVec_mulVec, dotProduct_smul,
          op_smul_eq_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [dotProduct_comm v, pow_two]
  calc
    _ = ∑ j, hA.1.eigenvalues j * ((hA.1.eigenvectorBasis j) ⬝ᵥ v) ^ 2 := by
      conv_lhs => rw [spectral_sum_general A hA.1]
      simp only [sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul,
        smul_eq_mul, vecMulVec_mulVec, op_smul_eq_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [dotProduct_comm v]
      ring
    _ ≤ ∑ j, c * ((hA.1.eigenvectorBasis j) ⬝ᵥ v) ^ 2 :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (he j) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, ← hnorm]

theorem sum_filter_partition {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (label : ι → κ) (f : ι → ℝ) :
    (∑ j, ∑ l ∈ s.filter (fun l ↦ label l = j), f l) = ∑ l ∈ s, f l := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

theorem weighted_variance_min {κ : Type*} [Fintype κ]
    (w c : κ → ℝ) (hw : ∑ j, w j = 1) (a : ℝ) :
    (∑ j, w j * (c j - ∑ i, w i * c i) ^ 2) ≤ ∑ j, w j * (c j - a) ^ 2 := by
  have he (b : ℝ) : (∑ j, w j * (c j - b) ^ 2) =
      (∑ j, w j * c j ^ 2) - 2 * b * (∑ j, w j * c j) + b ^ 2 := by
    simp only [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
    congr 1
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, he]
  nlinarith only [sq_nonneg (a - ∑ j, w j * c j)]

theorem between_le_of_retained {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (label : ι → κ) (r x : ι → ℝ) (w c : κ → ℝ)
    (hr : ∀ l ∈ s, 0 ≤ r l ∧ r l ≤ 1) (hw : ∑ j, w j = 1)
    (N B V μ : ℝ) (hN : 0 < N)
    (hmass : ∀ j, N * w j / 2 ≤ ∑ l ∈ s.filter (fun l ↦ label l = j), r l)
    (hwithin : (∑ j, ∑ l ∈ s.filter (fun l ↦ label l = j), (x l - c j) ^ 2) ≤ N * B)
    (hvar : (∑ l ∈ s, r l * (x l - μ) ^ 2) ≤ N * V) :
    (∑ j, w j * (c j - ∑ i, w i * c i) ^ 2) ≤ 4 * (B + V) := by
  have hcomp (j : κ) : N * w j * (c j - μ) ^ 2 ≤
      4 * (∑ l ∈ s.filter (fun l ↦ label l = j), (x l - c j) ^ 2) +
      4 * ∑ l ∈ s.filter (fun l ↦ label l = j), r l * (x l - μ) ^ 2 := by
    have hh := Finset.sum_le_sum (s := s.filter (fun l ↦ label l = j))
      (fun l hl ↦ mul_le_mul_of_nonneg_left (show (c j - μ) ^ 2 ≤
        2 * (x l - c j) ^ 2 + 2 * (x l - μ) ^ 2 by
          nlinarith only [sq_nonneg (2 * x l - c j - μ)]) (hr l (Finset.mem_filter.mp hl).1).1)
    have hdrop : (∑ l ∈ s.filter (fun l ↦ label l = j), r l * (x l - c j) ^ 2) ≤
        ∑ l ∈ s.filter (fun l ↦ label l = j), (x l - c j) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_of_le_one_left (sq_nonneg _) (hr l (Finset.mem_filter.mp hl).1).2
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at hh
    have he (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
    simp_rw [he] at hh
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
    have hm := mul_le_mul_of_nonneg_right (hmass j) (sq_nonneg (c j - μ))
    nlinarith only [hh, hdrop, hm]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hcomp j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [sum_filter_partition] at hh
  have hh' : N * (∑ j, w j * (c j - μ) ^ 2) ≤ 4 * (N * B) + 4 * (N * V) := by
    have h₁ := mul_le_mul_of_nonneg_left hwithin (by norm_num : (0 : ℝ) ≤ 4)
    have h₂ := mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 4)
    have he : (∑ j, N * w j * (c j - μ) ^ 2) =
        N * ∑ j, w j * (c j - μ) ^ 2 := by
      simp only [Finset.mul_sum, mul_assoc]
    rw [he] at hh
    linarith only [hh, h₁, h₂]
  have hb := (mul_le_mul_iff_right₀ hN).mp (show
    N * (∑ j, w j * (c j - μ) ^ 2) ≤ N * (4 * (B + V)) by
      nlinarith only [hh'])
  exact (weighted_variance_min w c hw μ).trans hb

end

end ABBKS26.Robust.FilterAux
