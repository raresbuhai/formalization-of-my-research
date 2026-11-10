module

public import ABBKS26.Common.Basic
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Sum-of-squares inequalities

Normed versions of the sum-of-squares facts of [ABBKS26, §3.1] (Cauchy–Schwarz, powers,
products, quadratic forms, Lagrange identity), with explicit bounds on certificate size.
-/

@[expose] public section

namespace ABBKS26.SoSKit

noncomputable section


open Common MvPolynomial Matrix
open scoped BigOperators
variable {d : ℕ}

private def signedSqrt (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.sqrt |t| else -Real.sqrt |t|

private theorem signedSqrt_sq (t : ℝ) : signedSqrt t ^ 2 = |t| := by
  unfold signedSqrt
  split_ifs <;> simpa only [neg_sq] using Real.sq_sqrt (abs_nonneg t)

private theorem sqrt_mul_signedSqrt (t : ℝ) : Real.sqrt |t| * signedSqrt t = t := by
  unfold signedSqrt
  split_ifs with ht
  · simpa only [abs_of_nonneg ht] using Real.mul_self_sqrt ht
  · rw [mul_neg, Real.mul_self_sqrt (abs_nonneg t), abs_of_neg (lt_of_not_ge ht), neg_neg]

/-- The two-square inequality has a square certificate. -/
theorem two_squares (x y : RPoly d) :
    IsSumSq (2 * x ^ 2 + 2 * y ^ 2 - (x - y) ^ 2) := by
  convert SoS.isSumSq_sq (x + y) using 1
  ring

/-- Weighted Cauchy–Schwarz has a norm-controlled certificate. -/
theorem weighted_cs {ι : Type} [Fintype ι]
    (h : ι → ℝ) (Z : ι → RPoly d) :
    IsSumSq (C (∑ i, |h i|) * (∑ i, C |h i| * Z i ^ 2) -
      (∑ i, C (h i) * Z i) ^ 2) ∧
    SoS.coeffNorm1 (C (∑ i, |h i|) * (∑ i, C |h i| * Z i ^ 2) -
      (∑ i, C (h i) * Z i) ^ 2) ≤
      2 * (∑ i, |h i|) * ∑ i, |h i| * SoS.coeffNorm1 (Z i) ^ 2 := by
  have hu : ∀ i, (C (Real.sqrt |h i|) : RPoly d) ^ 2 = C |h i| := fun i ↦ by
    rw [← C_pow, Real.sq_sqrt (abs_nonneg _)]
  have hv : ∀ i, (C (signedSqrt (h i)) * Z i) ^ 2 = C |h i| * Z i ^ 2 := fun i ↦ by
    rw [mul_pow, ← C_pow, signedSqrt_sq]
  have huv : ∀ i, C (Real.sqrt |h i|) * (C (signedSqrt (h i)) * Z i) =
      C (h i) * Z i := fun i ↦ by
    rw [← mul_assoc, ← C_mul, sqrt_mul_signedSqrt]
  refine ⟨?_, ?_⟩
  · have hs := SoS.isSumSq_lagrange Finset.univ
      (fun i ↦ C (Real.sqrt |h i|)) (fun i ↦ C (signedSqrt (h i)) * Z i)
    simpa only [hu, hv, huv, ← map_sum] using hs
  · let K : ℝ := ∑ i, |h i|
    let S : ℝ := ∑ i, |h i| * SoS.coeffNorm1 (Z i) ^ 2
    have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ abs_nonneg (h i)
    have hS : SoS.coeffNorm1 (∑ i, C |h i| * Z i ^ 2) ≤ S := by
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [SoS.coeffNorm1_C_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left (SoS.coeffNorm1_pow_le _ _) (abs_nonneg _)
    have hL : SoS.coeffNorm1 (∑ i, C (h i) * Z i) ≤
        ∑ i, |h i| * SoS.coeffNorm1 (Z i) := by
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      exact (SoS.coeffNorm1_C_mul (h i) (Z i)).le
    have hcs : (∑ i, |h i| * SoS.coeffNorm1 (Z i)) ^ 2 ≤ K * S := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun i _ ↦ abs_nonneg (h i)) (fun i _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
      intro i _
      exact le_of_eq (by ring)
    have h₁ : SoS.coeffNorm1 (C K * (∑ i, C |h i| * Z i ^ 2)) ≤ K * S := by
      rw [SoS.coeffNorm1_C_mul, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_left hS hK
    have h₂ : SoS.coeffNorm1 ((∑ i, C (h i) * Z i) ^ 2) ≤ K * S :=
      (SoS.coeffNorm1_pow_le _ _).trans
        ((pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hL 2).trans hcs)
    exact (SoS.coeffNorm1_sub_le _ _).trans (by dsimp [K, S] at *; linarith)

/-- Products preserve certified upper bounds. -/
theorem prod (A B X Y : RPoly d)
    (hA : IsSumSq A) (hY : IsSumSq Y) (hX : IsSumSq (A - X))
    (hB : IsSumSq (B - Y)) : IsSumSq (A * B - X * Y) := by
  convert (hA.mul hB).add (hY.mul hX) using 1
  ring

/-- Powers preserve nonnegative polynomial order. -/
theorem powers (X Y : RPoly d)
    (hX : IsSumSq X) (hY : IsSumSq Y) (h : IsSumSq (Y - X)) (m : ℕ) :
    IsSumSq (Y ^ m - X ^ m) := by
  induction m with
  | zero => simp only [pow_zero, sub_self]; exact IsSumSq.zero
  | succ m ih =>
    convert (hY.mul ih).add ((SoS.isSumSq_pow hX m).mul h) using 1
    simp only [pow_succ]
    ring

/-- Mixed powers obey quadratic upper bounds. -/
theorem mixed_powers (X Y : RPoly d) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : IsSumSq X) (hY : IsSumSq Y)
    (hx : IsSumSq (C a * nsq - X)) (hy : IsSumSq (C b * nsq - Y)) (p q : ℕ) :
    IsSumSq (C (a ^ p * b ^ q) * nsq ^ (p + q) - X ^ p * Y ^ q) := by
  have hN : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  have hp := powers X (C a * nsq) hX ((SoS.isSumSq_C ha).mul hN) hx p
  have hq := powers Y (C b * nsq) hY ((SoS.isSumSq_C hb).mul hN) hy q
  have ht := prod ((C a * nsq) ^ p) ((C b * nsq) ^ q) (X ^ p) (Y ^ q)
    (SoS.isSumSq_pow ((SoS.isSumSq_C ha).mul hN) p) (SoS.isSumSq_pow hY q) hp hq
  simpa only [mul_pow, C_mul, C_pow, pow_add, mul_mul_mul_comm] using ht

/-- Telescoping controls the difference of powers. -/
theorem telescoping (X Y : RPoly d) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hX : IsSumSq X) (hY : IsSumSq Y)
    (hx : IsSumSq (C Λ * nsq - X)) (hy : IsSumSq (C Λ * nsq - Y))
    (s : ℕ) (hs : 1 ≤ s) :
    IsSumSq (C ((s : ℝ) ^ 2 * Λ ^ (2 * s - 2)) * nsq ^ (2 * s - 2) *
      (X - Y) ^ 2 - (X ^ s - Y ^ s) ^ 2) := by
  let T : ℕ → RPoly d := fun k ↦ X ^ k * Y ^ (s - 1 - k)
  let U : RPoly d := C (Λ ^ (2 * s - 2)) * nsq ^ (2 * s - 2)
  have hT : ∀ k ∈ Finset.range s, IsSumSq (U - T k ^ 2) := by
    intro k hk
    have hk' : 2 * k + 2 * (s - 1 - k) = 2 * s - 2 := by
      have := Finset.mem_range.1 hk
      omega
    have ht := mixed_powers X Y Λ Λ hΛ hΛ hX hY hx hy
      (2 * k) (2 * (s - 1 - k))
    rw [← pow_add, hk'] at ht
    simpa only [T, U, mul_pow, ← pow_mul, Nat.mul_comm] using ht
  have hsum : IsSumSq (C (s : ℝ) * U - ∑ k ∈ Finset.range s, T k ^ 2) := by
    have ht := IsSumSq.sum hT
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, map_natCast] using ht
  have hcs := SoS.isSumSq_card_mul_sum_sq_sub (Finset.range s) T
  rw [Finset.card_range] at hcs
  have hbound := (SoS.isSumSq_C_mul (Nat.cast_nonneg s) hsum).add hcs
  have hbound' : IsSumSq (C ((s : ℝ) ^ 2) * U -
      (∑ k ∈ Finset.range s, T k) ^ 2) := by
    convert hbound using 1
    rw [C_pow]
    ring
  have hfactor : (∑ k ∈ Finset.range s, T k) * (X - Y) = X ^ s - Y ^ s := by
    simpa only [T, Nat.sub_sub] using geom_sum₂_mul X Y s
  convert hbound'.mul (SoS.isSumSq_sq (X - Y)) using 1
  rw [sub_mul, ← mul_pow, hfactor]
  dsimp [U]
  simp only [C_mul, C_pow]
  ring

/-- Positive semidefinite quadratic forms are sums of squares. -/
theorem psd_quad (A : Mat d)
    (hA : A.PosSemidef) : IsSumSq (quad A) := by
  let U : Mat d := (hA.1.eigenvectorUnitary : Mat d)
  let D : Mat d := diagonal (fun i ↦ Real.sqrt (hA.1.eigenvalues i))
  have hD : D * D = diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have hP : (U * D) * (U * D)ᵀ = A := by
    conv_rhs => rw [hA.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, transpose_mul, diagonal_transpose, ← mul_assoc,
      mul_assoc U, hD, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  let P := U * D
  have hL : ∀ c, (∑ i, C (P i c) * (X i : RPoly d)) ^ 2 =
      ∑ i, ∑ j, C (P i c * P j c) * (X i * X j) := fun c ↦ by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [C_mul]
    ring
  have hR : ∀ i j, C ((P * Pᵀ) i j) * (X i * X j : RPoly d) =
      ∑ c, C (P i c * P j c) * (X i * X j) := fun i j ↦ by
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    rfl
  have hsum : ∑ c, (∑ i, C (P i c) * (X i : RPoly d)) ^ 2 = quad (P * Pᵀ) := by
    simp only [hL, quad, mul_assoc, hR]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  rw [← hP, ← hsum]
  exact IsSumSq.sum_sq _ _

private theorem quad_shift (E : Mat d) (e : ℝ) :
    quad (e • (1 : Mat d) - E) = C e * nsq - quad E ∧
      quad (e • (1 : Mat d) + E) = C e * nsq + quad E := by
  have hI : quad (e • (1 : Mat d)) = C e * nsq := by
    simp [quad, nsq, Matrix.one_apply, Finset.mul_sum, pow_two, mul_assoc,
      apply_ite, ite_mul]
  constructor
  · rw [quad, show (∑ i, ∑ j, C ((e • (1 : Mat d) - E) i j) * X i * X j) =
        quad (e • (1 : Mat d)) - quad E by
      simp [quad, C_sub, sub_mul, Finset.sum_sub_distrib]]
    rw [hI]
  · rw [quad, show (∑ i, ∑ j, C ((e • (1 : Mat d) + E) i j) * X i * X j) =
        quad (e • (1 : Mat d)) + quad E by
      simp [quad, C_add, add_mul, Finset.sum_add_distrib]]
    rw [hI]

/-- An operator bound controls the square of a quadratic form. -/
theorem quad_square (E : Mat d)
    (he : Eᵀ = E) (e : ℝ) (he0 : 0 ≤ e)
    (h : ∀ v, |qform E v| ≤ e * sqnorm v) :
    IsSumSq (C (e ^ 2) * nsq ^ 2 - quad E ^ 2) := by
  have hsym : E.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using he
  have hI : (e • (1 : Mat d)).IsHermitian :=
    (PosSemidef.one.smul he0).isHermitian
  have hminus : (e • (1 : Mat d) - E).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hI.sub hsym) fun v ↦ ?_
    have hv := (abs_le.1 (h v)).2
    simpa only [Pi.star_apply, star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
      dotProduct_sub, dotProduct_smul, sqnorm, qform, smul_eq_mul] using sub_nonneg.2 hv
  have hplus : (e • (1 : Mat d) + E).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hI.add hsym) fun v ↦ ?_
    have hv := (abs_le.1 (h v)).1
    have hv' : 0 ≤ e * sqnorm v + qform E v := by linarith
    simpa only [Pi.star_apply, star_trivial, add_mulVec, smul_mulVec, one_mulVec,
      dotProduct_add, dotProduct_smul, sqnorm, qform, smul_eq_mul] using hv'
  have hm := psd_quad _ hminus
  have hp := psd_quad _ hplus
  rw [(quad_shift E e).1] at hm
  rw [(quad_shift E e).2] at hp
  convert hm.mul hp using 1
  rw [C_pow]
  ring

/-- The coefficient norm bounds a homogeneous square in SoS. -/
theorem l1_square (E : RPoly d)
    (r : ℕ) (hE : E.IsHomogeneous r) :
    IsSumSq (C (SoS.coeffNorm1 E ^ 2) * nsq ^ r - E ^ 2) := by
  have hh : (E ^ 2).IsHomogeneous (2 * r) := by
    simpa only [mul_comm] using hE.pow 2
  have h := SoS.isSumSq_l1 hh
  have hn := SoS.coeffNorm1_pow_le E 2
  have hs := SoS.isSumSq_C_mul (sub_nonneg.2 hn)
    (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) r : IsSumSq ((nsq : RPoly d) ^ r))
  convert hs.add h using 1
  simp only [C_sub, nsq]
  ring

/-- Evaluating an SoS square bound gives a pointwise bound. -/
theorem evaluate_bound (E : RPoly d)
    (η : ℝ) (r : ℕ) (hη : 0 ≤ η) (h : IsSumSq (C η * nsq ^ r - E ^ 2))
    (v : Vec d) : |eval v E| ≤ Real.sqrt η * Real.sqrt (sqnorm v) ^ r := by
  have hn : 0 ≤ sqnorm v := by
    change 0 ≤ ∑ i, v i * v i
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
  have he : eval v (nsq : RPoly d) = sqnorm v := by
    simp [nsq, sqnorm, dotProduct, pow_two]
  have hv := (SoS.isSumSq_map (eval v) h).nonneg
  simp only [map_sub, map_mul, map_pow, eval_C, he] at hv
  have hr : (Real.sqrt η * Real.sqrt (sqnorm v) ^ r) ^ 2 = η * sqnorm v ^ r := by
    rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hn, Real.sq_sqrt hη]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ Real.sqrt η * Real.sqrt (sqnorm v) ^ r)).1
  rw [sq_abs, hr]
  linarith

/-- Weighted Lagrange Cauchy–Schwarz is a sum of squares. -/
theorem lagrange {ι : Type} [Fintype ι]
    (w : ι → ℝ) (a b : ι → RPoly d) (hw : ∀ i, 0 ≤ w i) :
    IsSumSq ((∑ i, C (w i) * a i ^ 2) * (∑ i, C (w i) * b i ^ 2) -
      (∑ i, C (w i) * a i * b i) ^ 2) := by
  have hs : ∀ i, (C (Real.sqrt (w i)) : RPoly d) ^ 2 = C (w i) := fun i ↦ by
    rw [← C_pow, Real.sq_sqrt (hw i)]
  have hm : ∀ i, (C (Real.sqrt (w i)) * a i) *
      (C (Real.sqrt (w i)) * b i) = C (w i) * a i * b i := fun i ↦ by
    rw [mul_mul_mul_comm, ← pow_two, hs, mul_assoc]
  have h := SoS.isSumSq_lagrange Finset.univ
    (fun i ↦ C (Real.sqrt (w i)) * a i) (fun i ↦ C (Real.sqrt (w i)) * b i)
  simpa only [mul_pow, hs, hm] using h

end

end ABBKS26.SoSKit
