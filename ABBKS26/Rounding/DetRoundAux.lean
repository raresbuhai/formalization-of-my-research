module

public import ABBKS26.Common.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Linear algebra and dyadic approximation for deterministic rounding. -/

@[expose] public section

namespace ABBKS26.Rounding.DetRoundAux

open Common Matrix
open scoped BigOperators

private theorem cell (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    ∃ a : Fin (2 * k), (a : ℝ) ≤ k * (x + 1) ∧ k * (x + 1) ≤ a + 1 := by
  let t := (k : ℝ) * (x + 1)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have ht' : t ≤ 2 * k := by dsimp [t]; nlinarith
  let a := min ⌊t⌋₊ (2 * k - 1)
  have ha : a < 2 * k := lt_of_le_of_lt (min_le_right _ _) (by omega)
  refine ⟨⟨a, ha⟩, ?_, ?_⟩
  · exact (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht)
  · change t ≤ (a : ℝ) + 1
    by_cases h : ⌊t⌋₊ ≤ 2 * k - 1
    · rw [show a = ⌊t⌋₊ from min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [show a = 2 * k - 1 from min_eq_right (by omega)]
      have he : ((2 * k - 1 : ℕ) : ℝ) + 1 = 2 * k := by
        exact_mod_cast (show 2 * k - 1 + 1 = 2 * k by omega)
      rwa [he]

theorem packing_coordinates {m n r : ℕ} (c : Fin n → Fin m → ℝ) (σ : ℝ)
    (hm : m ≤ r) (hr : 1 ≤ r) (hσ : 0 < σ)
    (hc : ∀ i a, -1 ≤ c i a ∧ c i a ≤ 1)
    (hsep : ∀ i j, i ≠ j → σ ^ 2 ≤ ∑ a, (c i a - c j a) ^ 2) :
    n ≤ (2 * ⌈2 * Real.sqrt r / σ⌉₊) ^ r := by
  classical
  let k := ⌈2 * Real.sqrt r / σ⌉₊
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have hk : 0 < k := Nat.ceil_pos.2 (div_pos (by positivity) hσ)
  have hkr : 2 * Real.sqrt r ≤ (k : ℝ) * σ := by
    exact (div_le_iff₀ hσ).1 (Nat.le_ceil _)
  choose b hb using fun i a ↦ cell k hk (c i a) (hc i a)
  have hinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    have hd : ∀ a, (k : ℝ) ^ 2 * (c i a - c j a) ^ 2 ≤ 1 := by
      intro a
      have he : b i a = b j a := congrFun hij a
      have hi := hb i a
      have hj := hb j a
      rw [← he] at hj
      have hl : -1 ≤ (k : ℝ) * (c i a - c j a) := by linarith
      have hu : (k : ℝ) * (c i a - c j a) ≤ 1 := by linarith
      have := (sq_le_one_iff_abs_le_one _).2 (abs_le.2 ⟨hl, hu⟩)
      nlinarith
    have hsum : (k : ℝ) ^ 2 * σ ^ 2 ≤ m := by
      calc
        _ ≤ (k : ℝ) ^ 2 * ∑ a, (c i a - c j a) ^ 2 :=
          mul_le_mul_of_nonneg_left (hsep i j hne) (sq_nonneg _)
        _ = ∑ a, (k : ℝ) ^ 2 * (c i a - c j a) ^ 2 := Finset.mul_sum _ _ _
        _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum fun a _ ↦ hd a
        _ = m := by simp
    have hm' : (m : ℝ) ≤ r := by exact_mod_cast hm
    have hs' : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt hr'.le
    have := mul_self_le_mul_self (by positivity : 0 ≤ 2 * Real.sqrt (r : ℝ)) hkr
    nlinarith
  have hcard := Fintype.card_le_of_injective b hinj
  simp only [Fintype.card_fin, Fintype.card_fun] at hcard
  exact hcard.trans (Nat.pow_le_pow_right (by omega) hm)

theorem sqnorm_nonneg {d : ℕ} (v : Vec d) : 0 ≤ sqnorm v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

theorem projection_contract {d : ℕ} (P : Mat d) (hP : Projection P) (v : Vec d) :
    sqnorm (P *ᵥ v) ≤ sqnorm v := by
  have hd : v ᵥ* P = P *ᵥ v := by
    conv_lhs => rw [← hP.1]
    rw [vecMul_transpose]
  have he : sqnorm (P *ᵥ v) = v ⬝ᵥ (P *ᵥ v) := by
    calc
      _ = (v ᵥ* P) ⬝ᵥ (P *ᵥ v) := by rw [hd]; rfl
      _ = v ⬝ᵥ (P *ᵥ (P *ᵥ v)) := (dotProduct_mulVec _ _ _).symm
      _ = _ := by rw [mulVec_mulVec, hP.2]
  unfold sqnorm at he
  have hn := sqnorm_nonneg (v - P *ᵥ v)
  simp only [sqnorm, sub_dotProduct, dotProduct_sub] at hn
  rw [dotProduct_comm (P *ᵥ v) v, ← he] at hn
  change (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ v
  linarith

theorem euclidean_sqnorm {d : ℕ} (v : Vec d) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = sqnorm v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [sqnorm, dotProduct, pow_two]

theorem packing {d : ℕ} (R : Mat d) (r n : ℕ) (z : Fin n → Vec d) (σ : ℝ)
    (hR : Projection R) (hr : R.rank ≤ r) (hr0 : 1 ≤ r) (hσ : 0 < σ)
    (hz : ∀ i, sqnorm (z i) ≤ 1)
    (hsep : ∀ i j, i ≠ j → σ ^ 2 ≤ sqnorm (R *ᵥ (z i - z j))) :
    n ≤ (2 * ⌈2 * Real.sqrt r / σ⌉₊) ^ r := by
  let E := EuclideanSpace ℝ (Fin d)
  let S := LinearMap.range (Matrix.toEuclideanLin R)
  let b := stdOrthonormalBasis ℝ S
  let w (i : Fin n) : S := ⟨WithLp.toLp 2 (R *ᵥ z i), ⟨WithLp.toLp 2 (z i), rfl⟩⟩
  have hm : Module.finrank ℝ S ≤ r := by
    change Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin R)) ≤ r
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [← Matrix.rank_eq_finrank_range_toLin R
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
    exact hr
  have hw : ∀ i, ‖w i‖ ^ 2 ≤ 1 := by
    intro i
    exact (euclidean_sqnorm _).trans_le ((projection_contract R hR _).trans (hz i))
  apply packing_coordinates (fun i ↦ b.repr (w i)) σ hm hr0 hσ
  · intro i a
    have hsum : ∑ a, (b.repr (w i) a) ^ 2 ≤ 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map]
      exact hw i
    have hsingle := Finset.single_le_sum (fun a _ ↦ sq_nonneg (b.repr (w i) a))
      (Finset.mem_univ a)
    exact abs_le.1 ((sq_le_one_iff_abs_le_one _).1 (hsingle.trans hsum))
  · intro i j hij
    have he : ∑ a, (b.repr (w i) a - b.repr (w j) a) ^ 2 =
        sqnorm (R *ᵥ (z i - z j)) := by
      change (∑ a, ((b.repr (w i) - b.repr (w j)) a) ^ 2) = _
      rw [← EuclideanSpace.real_norm_sq_eq]
      rw [← map_sub, b.repr.norm_map]
      change ‖(WithLp.toLp 2 (R *ᵥ z i) : E) - WithLp.toLp 2 (R *ᵥ z j)‖ ^ 2 = _
      change ‖(WithLp.toLp 2 (R *ᵥ z i - R *ᵥ z j) : E)‖ ^ 2 = _
      rw [euclidean_sqnorm, mulVec_sub]
    rw [he]
    exact hsep i j hij

end ABBKS26.Rounding.DetRoundAux

namespace ABBKS26.Rounding.DetRoundAux

open Common Matrix
open scoped BigOperators

variable {d : ℕ}

theorem projection_compl (P : Mat d) (hP : Projection P) : Projection (1 - P) := by
  constructor
  · simp [transpose_sub, hP.1]
  · noncomm_ring [hP.2]

theorem projection_dot (P : Mat d) (hP : Projection P) (v w : Vec d) :
    (P *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (P *ᵥ w) := by
  have hd : v ᵥ* P = P *ᵥ v := by
    conv_lhs => rw [← hP.1]
    rw [vecMul_transpose]
  rw [dotProduct_mulVec, hd]

theorem trace_projection_nonneg (M P : Mat d) (hM : M.PosSemidef)
    (hP : Projection P) : 0 ≤ (P * M).trace := by
  have h := (hM.mul_mul_conjTranspose_same P).trace_nonneg
  rw [conjTranspose_eq_transpose_of_trivial, hP.1, trace_mul_cycle, hP.2] at h
  exact h

theorem trace_projection_le (M P : Mat d) (hM : M.PosSemidef)
    (hP : Projection P) : (P * M).trace ≤ M.trace := by
  have h := trace_projection_nonneg M (1 - P) hM (projection_compl P hP)
  rw [sub_mul, one_mul, trace_sub] at h
  linarith


end ABBKS26.Rounding.DetRoundAux

namespace ABBKS26.Rounding.DetRoundAux

noncomputable section

open Common Matrix
open scoped BigOperators

variable {d : ℕ}

theorem projection_sqnorm (P : Mat d) (hP : Projection P) (v : Vec d) :
    sqnorm (P *ᵥ v) = qform P v := by
  rw [sqnorm, projection_dot P hP, mulVec_mulVec, hP.2]
  rfl

theorem projection_residual (P : Mat d) (hP : Projection P) (v : Vec d) :
    sqnorm ((1 - P) *ᵥ v) = sqnorm v - sqnorm (P *ᵥ v) := by
  rw [projection_sqnorm (1 - P) (projection_compl P hP),
    projection_sqnorm P hP]
  simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub, sqnorm]

theorem eigen_sqnorm (A : Mat d) (hA : A.IsHermitian) (j : Fin d) :
    sqnorm (hA.eigenvectorBasis j) = 1 := by
  rw [← euclidean_sqnorm]
  change ‖hA.eigenvectorBasis j‖ ^ 2 = 1
  rw [hA.eigenvectorBasis.norm_eq_one, one_pow]

theorem spectral_sum (A : Mat d) (hA : A.IsHermitian) :
    A = ∑ j, hA.eigenvalues j •
      vecMulVec (hA.eigenvectorBasis j) (hA.eigenvectorBasis j) := by
  classical
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply,
    star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec_apply, transpose_apply,
    Function.comp_apply, RCLike.ofReal_real_eq_id, id, hA.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spectral_one (A : Mat d) (hA : A.IsHermitian) :
    (1 : Mat d) = ∑ j, vecMulVec (hA.eigenvectorBasis j) (hA.eigenvectorBasis j) := by
  classical
  have he := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rw [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at he
  rw [← he]
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]

theorem trace_spectral (A T : Mat d) (hA : A.IsHermitian) :
    (T * A).trace = ∑ j, hA.eigenvalues j * qform T (hA.eigenvectorBasis j) := by
  conv_lhs => rw [spectral_sum A hA]
  simp only [Finset.mul_sum, mul_smul_comm, trace_sum, trace_smul,
    mul_vecMulVec, trace_vecMulVec, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [qform, dotProduct_comm]

theorem trace_basis (A T : Mat d) (hA : A.IsHermitian) :
    T.trace = ∑ j, qform T (hA.eigenvectorBasis j) := by
  have he := spectral_one A hA
  calc
    _ = (T * (1 : Mat d)).trace := by rw [mul_one]
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, trace_sum, mul_vecMulVec, trace_vecMulVec]
      apply Finset.sum_congr rfl
      intro j _
      rw [qform, dotProduct_comm]

theorem trace_projection_rank (P : Mat d) (hP : Projection P) :
    P.trace = P.rank := by
  classical
  have hH : P.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hP.1
  have he : ∀ j, hH.eigenvalues j = 0 ∨ hH.eigenvalues j = 1 := by
    intro j
    have hn := projection_sqnorm P hP (hH.eigenvectorBasis j)
    rw [hH.mulVec_eigenvectorBasis] at hn
    have hv := eigen_sqnorm P hH j
    simp only [sqnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hv hn
    simp only [qform, hH.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul] at hn
    rw [hv] at hn
    exact eq_zero_or_one_of_sq_eq_self (by nlinarith)
  rw [hH.trace_eq_sum_eigenvalues, hH.rank_eq_card_non_zero_eigs]
  simp only [RCLike.ofReal_real_eq_id, id, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j _
  rcases he j with h | h <;> simp [h]

theorem qform_spectral (A : Mat d) (hA : A.IsHermitian) (x : Vec d) :
    qform A x = ∑ j, hA.eigenvalues j * ((hA.eigenvectorBasis j) ⬝ᵥ x) ^ 2 := by
  conv_lhs => rw [spectral_sum A hA]
  simp only [qform, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul,
    smul_eq_mul, vecMulVec_mulVec, op_smul_eq_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [dotProduct_comm x]
  ring

theorem abs_qform_le (A : Mat d) (δ : ℝ) (hδ : 0 ≤ δ) (hA : frobSq A ≤ δ ^ 2)
    (v : Vec d) : |qform A v| ≤ δ * sqnorm v := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun p ↦ A p.1 p.2) (fun p ↦ v p.1 * v p.2)
  have he : ∑ p : Fin d × Fin d, A p.1 p.2 * (v p.1 * v p.2) = qform A v := by
    simp only [Fintype.sum_prod_type, qform, mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have he' : ∑ p : Fin d × Fin d, (v p.1 * v p.2) ^ 2 = sqnorm v ^ 2 := by
    rw [Fintype.sum_prod_type]
    change (∑ a, ∑ b, (v a * v b) ^ 2) = (∑ a, v a * v a) ^ 2
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he, he'] at hc
  have hf : ∑ p : Fin d × Fin d, A p.1 p.2 ^ 2 = frobSq A := by
    simp only [Fintype.sum_prod_type, frobSq]
  rw [hf] at hc
  have hb := mul_le_mul_of_nonneg_right hA (sq_nonneg (sqnorm v))
  have hn := sqnorm_nonneg v
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hδ hn)).1
  rw [sq_abs, mul_pow]
  exact hc.trans hb

theorem abs_trace_mul_le (A M : Mat d) (δ : ℝ) (hM : M.PosSemidef)
    (hδ : 0 ≤ δ) (hA : frobSq A ≤ δ ^ 2) : |(A * M).trace| ≤ δ * M.trace := by
  rw [trace_spectral M A hM.1]
  calc
    _ ≤ ∑ j, |hM.1.eigenvalues j * qform A (hM.1.eigenvectorBasis j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, hM.1.eigenvalues j * δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hM.eigenvalues_nonneg j)]
      apply mul_le_mul_of_nonneg_left _ (hM.eigenvalues_nonneg j)
      simpa only [eigen_sqnorm, mul_one] using
        abs_qform_le A δ hδ hA (hM.1.eigenvectorBasis j)
    _ = δ * M.trace := by
      rw [hM.1.trace_eq_sum_eigenvalues]
      change ∑ j, hM.1.eigenvalues j * δ = δ * ∑ j, hM.1.eigenvalues j
      rw [← Finset.sum_mul, mul_comm]

end

end ABBKS26.Rounding.DetRoundAux

namespace ABBKS26.Rounding.DetRoundAux

open Common Matrix
open scoped BigOperators

private theorem weighted_witness {ι : Type*} [Fintype ι]
    (wgt K N H : ι → ℝ) (γ ε s : ℝ) (r : ℕ)
    (hwgt : ∀ j, 0 ≤ wgt j) (hK : ∀ j, 0 ≤ K j ∧ K j ≤ 1)
    (hN : ∀ j, 0 ≤ N j) (hH : ∀ j, 0 ≤ H j) (hNH : ∀ j, N j + H j = 1)
    (hγ : 0 < γ) (hε : 0 < ε ∧ ε ≤ γ ^ 2 / 32) (hs : 0 ≤ s)
    (hr : 1 ≤ r) (htr : ∑ j, wgt j ≤ 1 + s) (hc : ∑ j, wgt j * N j ≤ ε)
    (hcont : γ ^ 2 / 8 ≤ ∑ j, wgt j * K j) (hR : ∑ j, H j ≤ r) :
    ∃ j, γ ^ 2 / (32 * r) ≤ wgt j ∧
      γ ^ 2 / (64 * (1 + s)) + γ ^ 2 / (64 * ε) * N j < K j := by
  classical
  have hεpos := hε.1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let t := γ ^ 2 / (32 * r)
  let a := γ ^ 2 / (64 * (1 + s))
  let b := γ ^ 2 / (64 * ε)
  have ht : 0 < t := by dsimp [t]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  by_contra! h
  have hpt : ∀ j, wgt j * K j ≤
      t * H j + (1 + b) * (wgt j * N j) + a * wgt j := by
    intro j
    by_cases hj : t ≤ wgt j
    · have hk := mul_le_mul_of_nonneg_left (h j hj) (hwgt j)
      have hn := mul_nonneg (hwgt j) (hN j)
      have hh := mul_nonneg ht.le (hH j)
      dsimp only [a, b] at *
      nlinarith
    · have hk := mul_le_mul_of_nonneg_left (hK j).2 (hwgt j)
      have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hj) (hH j)
      have hn := mul_nonneg hb.le (mul_nonneg (hwgt j) (hN j))
      have he := hNH j
      have hl := mul_nonneg ha.le (hwgt j)
      nlinarith
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hpt j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hsum' : γ ^ 2 / 8 ≤ t * r + (1 + b) * ε + a * (1 + s) :=
    hcont.trans (hsum.trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hR ht.le)
        (mul_le_mul_of_nonneg_left hc (by positivity)))
      (mul_le_mul_of_nonneg_left htr ha.le)))
  have ht' : t * r = γ ^ 2 / 32 := by dsimp [t]; field_simp
  have ha' : a * (1 + s) = γ ^ 2 / 64 := by
    dsimp [a]
    field_simp
  have hb' : b * ε = γ ^ 2 / 64 := by dsimp [b]; field_simp
  rw [ht', ha', add_mul, one_mul, hb'] at hsum'
  nlinarith [sq_pos_of_pos hγ]

private theorem sqrt_sqnorm_eq_norm {d : ℕ} (v : Vec d) :
    Real.sqrt (sqnorm v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [← euclidean_sqnorm, Real.sqrt_sq (norm_nonneg _)]

private theorem sqrt_sqnorm_add_le {d : ℕ} (v w : Vec d) :
    Real.sqrt (sqnorm (v + w)) ≤ Real.sqrt (sqnorm v) + Real.sqrt (sqnorm w) := by
  rw [sqrt_sqnorm_eq_norm, sqrt_sqnorm_eq_norm, sqrt_sqnorm_eq_norm]
  exact norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

private theorem residual_triangle {d : ℕ} (T : Mat d) (hT : Projection T)
    (v z : Vec d) : Real.sqrt (sqnorm (T *ᵥ v)) ≤
      Real.sqrt (sqnorm (T *ᵥ z)) + Real.sqrt (sqnorm (v - z)) := by
  calc
    _ = Real.sqrt (sqnorm (T *ᵥ z + T *ᵥ (v - z))) := by
      rw [← mulVec_add, add_sub_cancel]
    _ ≤ _ := (sqrt_sqnorm_add_le _ _).trans
      (add_le_add le_rfl (Real.sqrt_le_sqrt (projection_contract T hT (v - z))))

theorem round_progress {d : ℕ}
    (M R P Q : Mat d) (γ ε s θ : ℝ) (r : ℕ)
    (hM : M.PosSemidef) (hR : Projection R) (hP : Projection P)
    (hQ : Projection Q) (hr : R.rank ≤ r) (hr0 : 1 ≤ r)
    (hγ : 0 < γ) (hs : 0 ≤ s ∧ s ≤ 1 / 4)
    (he : 0 < ε ∧ ε ≤ γ ^ 2 / 32) (htr : M.trace ≤ 1 + s)
    (hc : ((1 - R) * M).trace ≤ ε)
    (_hpq : ∀ v, InRange P v → InRange Q v)
    (hcont : γ ^ 2 / 8 ≤ ((1 - P) * M).trace)
    (hθ : θ ≤ (γ / 200) ^ 2 * (γ ^ 2 / (32 * r)))
    (hcap : Common.LE ((1 - Q) * M * (1 - Q)) (θ • (1 : Mat d))) :
    ∃ z, InRange Q z ∧ sqnorm z ≤ 1 ∧
      γ / (8 * Real.sqrt (1 + s)) - γ / 200 ≤ Real.sqrt (sqnorm ((1 - P) *ᵥ z)) ∧
      Real.sqrt (sqnorm ((1 - R) *ᵥ z)) ≤ 8 * Real.sqrt ε / γ + γ / 200 := by
  classical
  have hεpos := he.1
  have hsnonneg := hs.1
  let v (j : Fin d) : Vec d := hM.1.eigenvectorBasis j
  let wgt := hM.1.eigenvalues
  let K (j : Fin d) := sqnorm ((1 - P) *ᵥ v j)
  let N (j : Fin d) := sqnorm ((1 - R) *ᵥ v j)
  let H (j : Fin d) := sqnorm (R *ᵥ v j)
  have hv : ∀ j, sqnorm (v j) = 1 := eigen_sqnorm M hM.1
  have hK : ∀ j, 0 ≤ K j ∧ K j ≤ 1 := fun j ↦
    ⟨sqnorm_nonneg _, (projection_contract (1 - P) (projection_compl P hP) _).trans_eq
      (hv j)⟩
  have hNH : ∀ j, N j + H j = 1 := by
    intro j
    dsimp only [N, H]
    rw [projection_residual R hR, hv]
    ring
  have hsumK : γ ^ 2 / 8 ≤ ∑ j, wgt j * K j := by
    simpa only [trace_spectral M (1 - P) hM.1,
      ← projection_sqnorm (1 - P) (projection_compl P hP)] using hcont
  have hsumN : ∑ j, wgt j * N j ≤ ε := by
    simpa only [trace_spectral M (1 - R) hM.1,
      ← projection_sqnorm (1 - R) (projection_compl R hR)] using hc
  have hsumH : ∑ j, H j ≤ r := by
    have ht := trace_basis M R hM.1
    simp only [← projection_sqnorm R hR, trace_projection_rank R hR] at ht
    rw [show (∑ j, H j) = (R.rank : ℝ) from ht.symm]
    exact_mod_cast hr
  have hsumw : ∑ j, wgt j ≤ 1 + s := by
    simpa only [hM.1.trace_eq_sum_eigenvalues, RCLike.ofReal_real_eq_id, id] using htr
  obtain ⟨j, hj, hj'⟩ := weighted_witness wgt K N H γ ε s r
    hM.eigenvalues_nonneg hK (fun _ ↦ sqnorm_nonneg _)
    (fun _ ↦ sqnorm_nonneg _) hNH hγ he hs.1 hr0 hsumw hsumN hsumK hsumH
  let x := (1 - Q) *ᵥ v j
  let z := Q *ᵥ v j
  have hx : sqnorm x ≤ (γ / 200) ^ 2 := by
    have hq := hcap x
    have hQx : (1 - Q) *ᵥ x = x := by
      dsimp only [x]
      rw [mulVec_mulVec, (projection_compl Q hQ).2]
    have hq' : qform M x ≤ θ * sqnorm x := by
      simpa only [qform, ← mulVec_mulVec,
        ← projection_dot (1 - Q) (projection_compl Q hQ), hQx,
        smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm] using hq
    have hjM : wgt j * sqnorm x ^ 2 ≤ qform M x := by
      rw [qform_spectral M hM.1]
      have ht := Finset.single_le_sum
        (fun i _ ↦ mul_nonneg (hM.eigenvalues_nonneg i) (sq_nonneg ((v i) ⬝ᵥ x)))
        (Finset.mem_univ j)
      have he : (v j) ⬝ᵥ x = sqnorm x :=
        (projection_sqnorm (1 - Q) (projection_compl Q hQ) (v j)).symm
      simpa only [he] using ht
    have hn := sqnorm_nonneg x
    by_cases hz : sqnorm x = 0
    · rw [hz]; positivity
    · have hxpos : 0 < sqnorm x := lt_of_le_of_ne hn (Ne.symm hz)
      have hw : wgt j * sqnorm x ≤ θ :=
        (mul_le_mul_iff_of_pos_right hxpos).1 (by nlinarith [hjM.trans hq'])
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
      have ht : 0 < γ ^ 2 / (32 * r) := by positivity
      have hl := mul_le_mul_of_nonneg_right hj hn
      apply (mul_le_mul_iff_of_pos_left ht).1
      nlinarith
  have hx' : Real.sqrt (sqnorm x) ≤ γ / 200 :=
    (Real.sqrt_le_left (by positivity)).2 hx
  have hzv : v j - z = x := by simp [z, x, sub_mulVec, one_mulVec]
  have hKj : γ / (8 * Real.sqrt (1 + s)) ≤ Real.sqrt (K j) := by
    have hspos : 0 < 1 + s := by linarith [hs.1]
    have hsroot : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 hspos
    have hlow : γ ^ 2 / (64 * (1 + s)) ≤ K j := by
      have hn : 0 ≤ γ ^ 2 / (64 * ε) * N j := by
        exact mul_nonneg (by positivity) (sqnorm_nonneg _)
      linarith
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (hK j).1, div_pow, mul_pow, Real.sq_sqrt hspos.le]
    convert hlow using 1
    ring
  have hNj : Real.sqrt (N j) ≤ 8 * Real.sqrt ε / γ := by
    have hhigh : N j ≤ 64 * ε / γ ^ 2 := by
      have ha : 0 ≤ γ ^ 2 / (64 * (1 + s)) := by positivity
      have hj1 := (hK j).2
      have hmul : γ ^ 2 / (64 * ε) * N j ≤ 1 := by linarith
      have hp : 0 < γ ^ 2 / (64 * ε) := by positivity
      have hb := (le_div_iff₀' hp).2 hmul
      convert hb using 1
      field_simp
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (sqnorm_nonneg _), div_pow, mul_pow, Real.sq_sqrt he.1.le]
    convert hhigh using 1
    ring
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · change Q *ᵥ (Q *ᵥ v j) = Q *ᵥ v j
    rw [mulVec_mulVec, hQ.2]
  · exact (projection_contract Q hQ _).trans_eq (hv j)
  · have ht := residual_triangle (1 - P) (projection_compl P hP) (v j) z
    rw [hzv] at ht
    dsimp only [K] at hKj
    linarith
  · have ht := residual_triangle (1 - R) (projection_compl R hR) z (v j)
    have he : sqnorm (z - v j) = sqnorm x := by
      rw [← hzv]
      simp only [sqnorm, sub_dotProduct, dotProduct_sub]
      ring
    rw [he] at ht
    dsimp only [N] at hNj
    linarith

end ABBKS26.Rounding.DetRoundAux

namespace ABBKS26.Rounding.DetRoundAux

noncomputable section

open Common Matrix Filter Topology
open scoped BigOperators

variable {d m : ℕ}

def frameProj (B : Matrix (Fin d) (Fin m) ℝ) : Mat d := B * (Bᵀ * B)⁻¹ * Bᵀ


theorem frameProj_spec (B : Matrix (Fin d) (Fin m) ℝ) (hB : (Bᵀ * B).det ≠ 0) :
    Projection (frameProj B) ∧ (frameProj B).rank = m ∧ frameProj B * B = B := by
  have hu : IsUnit (Bᵀ * B).det := isUnit_iff_ne_zero.2 hB
  have hGram : (Bᵀ * B)ᵀ = Bᵀ * B := by simp
  have hfix : frameProj B * B = B := by
    simp only [frameProj, Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hu, Matrix.mul_one]
  have hP : Projection (frameProj B) := by
    constructor
    · simp only [frameProj, transpose_mul, transpose_transpose, transpose_nonsing_inv, hGram]
      rw [Matrix.mul_assoc]
    · change frameProj B * (B * (Bᵀ * B)⁻¹ * Bᵀ) = frameProj B
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]
      rfl
  refine ⟨hP, ?_, hfix⟩
  apply Nat.le_antisymm
  · exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_le_width B))
  · have hfull : (Bᵀ * B).rank = m := by
      simpa using rank_of_det_ne_zero hB
    have hr : B.rank = m := by
      apply Nat.le_antisymm (rank_le_width B)
      exact hfull.symm.trans_le (rank_mul_le_right _ _)
    have hh := rank_mul_le_left (frameProj B) B
    rw [hfix] at hh
    exact hr.symm.trans_le hh


theorem unit_near_projection (P : Mat d) (hP : Projection P) (v : Vec d) (γ : ℝ)
    (hv : sqnorm v = 1) (hγ : 0 < γ ∧ γ ≤ 1 / 2)
    (hnear : 1 - γ ^ 2 / 2 ≤ qform P v) :
    ∃ u, sqnorm u = 1 ∧ InRange P u ∧ sqnorm (v - u) ≤ γ ^ 2 := by
  let w := P *ᵥ v
  let t := Real.sqrt (sqnorm w)
  have hw : sqnorm w = qform P v := projection_sqnorm P hP v
  have hw1 : sqnorm w ≤ 1 := (projection_contract P hP v).trans_eq hv
  have hwpos : 0 < sqnorm w := by rw [hw]; nlinarith [hγ.1, hγ.2]
  have ht : 0 < t := Real.sqrt_pos.2 hwpos
  have ht2 : t ^ 2 = sqnorm w := Real.sq_sqrt hwpos.le
  have ht1 : t ≤ 1 := by have := Real.sqrt_nonneg (sqnorm w); dsimp [t]; nlinarith
  have htl : 1 - γ ^ 2 / 2 ≤ t := by
    have ht0 : 0 ≤ t := ht.le
    nlinarith
  let u := t⁻¹ • w
  have hu : sqnorm u = 1 := by
    calc
      _ = t⁻¹ ^ 2 * sqnorm w := by
        simp only [u, sqnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        ring
      _ = 1 := by rw [inv_pow, ← ht2, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  have hPu : InRange P u := by
    change P *ᵥ (t⁻¹ • (P *ᵥ v)) = _
    rw [mulVec_smul, mulVec_mulVec, hP.2]
  refine ⟨u, hu, hPu, ?_⟩
  have hdot : v ⬝ᵥ u = t := by
    change v ⬝ᵥ (t⁻¹ • (P *ᵥ v)) = t
    rw [dotProduct_smul]
    change t⁻¹ * qform P v = t
    rw [← hw, ← ht2]
    field_simp
  have he : sqnorm (v - u) = 2 - 2 * t := by
    simp only [sqnorm, sub_dotProduct, dotProduct_sub]
    rw [show v ⬝ᵥ v = 1 from hv, show u ⬝ᵥ u = 1 from hu,
      dotProduct_comm u v, hdot]
    ring
  rw [he]
  linarith


end

end ABBKS26.Rounding.DetRoundAux
