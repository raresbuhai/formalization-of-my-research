module

public import Background.SumOfSquares.IdealSOS
public import Background.SumOfSquares.PseudoBounds

/-!
# Norm bookkeeping for sums of squares plus an ideal, in powers of a base

The identifiability argument of the small-radius analysis (`BS23/SmallRadius/Ident.lean`) builds
many certificates `SoS.SosPlusIdeal A k M g` and must bound their norms `M`. Here every norm is a
power `W^a` of one base `W ≥ 2`, and the rules of `Background/SumOfSquares/IdealSOS.lean` are
restated with exponents in `ℕ`: sums (`addW`, `sumW`), products (`mulW`, `mulSOSW`), constants
(`smulW`), powers (`powW`) and differences of powers (`pow_sub_powW`: from `0 ≤ X ≤ Y` to
`X^m ≤ Y^m`, the analogue of `SoS.isSumSq_pow_sub_pow`).

For variables `wᵢ` that are Boolean in `A` (`wᵢ² = wᵢ`, `SoS.HasEq`): `wᵢ y^(2r) ≥ 0`
(`w_mul_pow`), `(1 - wᵢ) y^(2r) ≥ 0` (`one_sub_w_mul_pow`), `∑_{i ∈ T} wᵢ ≥ 0` (`sum_wW`) and
`|T| - ∑_{i ∈ T} wᵢ ≥ 0` (`card_sub_sum_wW`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*} {A : System σ ℝ} {W : ℝ} {k k' k₁ k₂ : ℕ} {g g₁ g₂ : MvPolynomial σ ℝ}

namespace SosPlusIdeal

theorem monoW (hW : 2 ≤ W) {a a' : ℕ} (h : SosPlusIdeal A k (W ^ a) g) (hk : k ≤ k')
    (ha : a ≤ a') : SosPlusIdeal A k' (W ^ a') g :=
  h.mono hk (pow_le_pow_of_two_le hW ha)

theorem of_isSumSqW (A : System σ ℝ) {a : ℕ} (hs : IsSumSq g) (hd : g.totalDegree ≤ k)
    (hn : coeffNorm1 g ≤ W ^ a) : SosPlusIdeal A k (W ^ a) g :=
  of_isSumSq A hs hd hn

theorem addW (hW : 2 ≤ W) {a b e : ℕ} (h₁ : SosPlusIdeal A k (W ^ a) g₁)
    (h₂ : SosPlusIdeal A k (W ^ b) g₂) (ha : a ≤ e) (hb : b ≤ e) :
    SosPlusIdeal A k (W ^ (e + 1)) (g₁ + g₂) :=
  (h₁.add h₂).mono le_rfl
    (add_le_pow_succ hW (pow_le_pow_of_two_le hW ha) (pow_le_pow_of_two_le hW hb))

theorem sumW (hW : 2 ≤ W) {ι : Type*} (T : Finset ι) {g : ι → MvPolynomial σ ℝ} {a c : ℕ}
    (hT : (T.card : ℝ) ≤ W ^ c) (h : ∀ j ∈ T, SosPlusIdeal A k (W ^ a) (g j)) :
    SosPlusIdeal A k (W ^ (a + c)) (∑ j ∈ T, g j) := by
  refine (sum T (M := fun _ ↦ W ^ a) h).mono le_rfl ?_
  rw [sum_const, nsmul_eq_mul, pow_add, mul_comm (W ^ a)]
  exact mul_le_mul_of_nonneg_right hT (pow_nonneg_of_two_le hW a)

theorem mulW (hW : 2 ≤ W) {a b c e : ℕ} (h₁ : SosPlusIdeal A k₁ (W ^ a) g₁)
    (h₂ : SosPlusIdeal A k₂ (W ^ b) g₂) (hg₂ : coeffNorm1 g₂ ≤ W ^ c) (hb : b ≤ e) (hc : c ≤ e) :
    SosPlusIdeal A (k₁ + k₂) (W ^ (a + e + 1)) (g₁ * g₂) := by
  refine (h₁.mul h₂).mono le_rfl ?_
  have h := add_le_pow_succ hW (pow_le_pow_of_two_le hW hb)
    (hg₂.trans (pow_le_pow_of_two_le hW hc))
  calc W ^ a * (W ^ b + coeffNorm1 g₂) ≤ W ^ a * W ^ (e + 1) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg_of_two_le hW a)
    _ = W ^ (a + e + 1) := by rw [← pow_add, add_assoc]

theorem mulSOSW (hW : 2 ≤ W) {q : MvPolynomial σ ℝ} {a c : ℕ} (hq : IsSumSq q)
    (hqd : q.totalDegree ≤ k₁) (hqn : coeffNorm1 q ≤ W ^ c) (h : SosPlusIdeal A k₂ (W ^ a) g) :
    SosPlusIdeal A (k₁ + k₂) (W ^ (c + a)) (q * g) := by
  refine (h.mulSOS hq).mono (by omega) ?_
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right hqn (pow_nonneg_of_two_le hW a)

theorem smulW (hW : 2 ≤ W) {c : ℝ} {a e : ℕ} (hc0 : 0 ≤ c) (hc : c ≤ W ^ e)
    (h : SosPlusIdeal A k (W ^ a) g) : SosPlusIdeal A k (W ^ (e + a)) (C c * g) := by
  refine (h.smul hc0).mono le_rfl ?_
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg_of_two_le hW a)

theorem powW (hW : 2 ≤ W) {a c e : ℕ} (h : SosPlusIdeal A k (W ^ a) g)
    (hg : coeffNorm1 g ≤ W ^ c) (ha : a ≤ e) (hc : c ≤ e) (r : ℕ) :
    SosPlusIdeal A (r * k) (W ^ ((e + 1) * r)) (g ^ r) := by
  refine (h.pow r).mono le_rfl ?_
  rw [pow_mul]
  exact pow_le_pow_left₀ (add_nonneg (pow_nonneg_of_two_le hW a) (coeffNorm1_nonneg g))
    (add_le_pow_succ hW (pow_le_pow_of_two_le hW ha) (hg.trans (pow_le_pow_of_two_le hW hc))) r

/-- `‖Y^m - X^m‖₁ ≤ W^(c m + 1)` when `‖X‖₁, ‖Y‖₁ ≤ W^c`. -/
theorem coeffNorm1_pow_sub_pow_le (hW : 2 ≤ W) {X Y : MvPolynomial σ ℝ} {c : ℕ}
    (hX : coeffNorm1 X ≤ W ^ c) (hY : coeffNorm1 Y ≤ W ^ c) (m : ℕ) :
    coeffNorm1 (Y ^ m - X ^ m) ≤ W ^ (c * m + 1) := by
  have hX' : coeffNorm1 (X ^ m) ≤ W ^ (c * m) := (coeffNorm1_pow_le _ _).trans
    (by rw [pow_mul]; exact pow_le_pow_left₀ (coeffNorm1_nonneg _) hX m)
  have hY' : coeffNorm1 (Y ^ m) ≤ W ^ (c * m) := (coeffNorm1_pow_le _ _).trans
    (by rw [pow_mul]; exact pow_le_pow_left₀ (coeffNorm1_nonneg _) hY m)
  exact (coeffNorm1_sub_le _ _).trans (add_le_pow_succ hW hY' hX')

/-- **Powers of an inequality**: if `X ≥ 0` and `Y - X ≥ 0` in degree `k`, with norms `W^a` and
`W^b` and `‖X‖₁, ‖Y‖₁ ≤ W^c`, then `Y^m - X^m ≥ 0` in degree `m k`, with norm `W^(m E)`,
`E = max a b c + 4`. By induction, `Y^(m+1) - X^(m+1) = Y (Y^m - X^m) + (Y - X) X^m`. -/
theorem pow_sub_powW (hW : 2 ≤ W) {X Y : MvPolynomial σ ℝ} {a b c : ℕ}
    (hX : SosPlusIdeal A k (W ^ a) X) (hYX : SosPlusIdeal A k (W ^ b) (Y - X))
    (hXn : coeffNorm1 X ≤ W ^ c) (hYn : coeffNorm1 Y ≤ W ^ c) (m : ℕ) :
    SosPlusIdeal A (m * k) (W ^ (m * (max a (max b c) + 4))) (Y ^ m - X ^ m) := by
  set F := max a (max b c) with hF
  have haF : a ≤ F := by omega
  have hbF : b ≤ F := by omega
  have hcF : c ≤ F := by omega
  have hY : SosPlusIdeal A k (W ^ (F + 1)) Y := by
    have := addW hW hX hYX haF hbF
    rwa [add_sub_cancel] at this
  induction m with
  | zero =>
    simp only [pow_zero, sub_self, zero_mul]
    exact zero A 0 zero_le_one
  | succ m ih =>
    have e : Y ^ (m + 1) - X ^ (m + 1) = Y * (Y ^ m - X ^ m) + (Y - X) * X ^ m := by ring
    rw [e]
    have hcm : c * m ≤ m * (F + 4) := by rw [mul_comm]; exact Nat.mul_le_mul_left m (by omega)
    have hFm : (F + 1) * m ≤ m * (F + 4) := by
      rw [mul_comm]; exact Nat.mul_le_mul_left m (by omega)
    have hsucc : (m + 1) * (F + 4) = m * (F + 4) + (F + 4) := by ring
    -- `Y (Y^m - X^m)`.
    have h₁ := mulW hW (e := m * (F + 4) + 1) hY ih (coeffNorm1_pow_sub_pow_le hW hXn hYn m)
      (by omega) (by omega)
    -- `(Y - X) X^m`.
    have hXm := powW hW hX hXn haF hcF m
    have hXmn : coeffNorm1 (X ^ m) ≤ W ^ (c * m) := (coeffNorm1_pow_le _ _).trans
      (by rw [pow_mul]; exact pow_le_pow_left₀ (coeffNorm1_nonneg _) hXn m)
    have hcm' : c * m ≤ (F + 1) * m := Nat.mul_le_mul_right m (by omega)
    have h₂ := mulW hW (e := (F + 1) * m) hYX hXm hXmn le_rfl hcm'
    have h := addW hW (e := m * (F + 4) + F + 3) h₁ h₂ (by omega) (by omega)
    exact h.mono (by rw [Nat.succ_mul]; omega) (pow_le_pow_of_two_le hW (by omega))

end SosPlusIdeal

/-! ### Boolean variables -/

section Boolean

variable {ι : Type*} {wv : ι → σ} (hbool : ∀ i, HasEq A (X (wv i) ^ 2 - X (wv i)))
include hbool

/-- `wᵢ y^(2r) = (wᵢ y^r)² - y^(2r) (wᵢ² - wᵢ) ≥ 0`, for `deg y ≤ e` and `‖y‖₁ ≤ W^c`. -/
theorem w_mul_pow (i : ι) {y : MvPolynomial σ ℝ} {e c : ℕ}
    (hyd : y.totalDegree ≤ e) (hyn : coeffNorm1 y ≤ W ^ c) (r : ℕ) :
    SosPlusIdeal A (2 * (r * e) + 2) (W ^ (2 * c * r)) (X (wv i) * y ^ (2 * r)) := by
  have hyr : coeffNorm1 (y ^ r) ≤ W ^ (c * r) := (coeffNorm1_pow_le _ _).trans
    (by rw [pow_mul]; exact pow_le_pow_left₀ (coeffNorm1_nonneg _) hyn r)
  have hyrd : (y ^ r).totalDegree ≤ r * e :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left r hyd)
  refine (SosPlusIdeal.isSumSq_add_mul (isSumSq_sq (X (wv i) * y ^ r)) (hbool i)
    (-(y ^ (2 * r))) ?_ ?_ ?_ ?_).congr (by ring)
  · refine (totalDegree_pow _ 2).trans ?_
    have := (totalDegree_mul (X (wv i)) (y ^ r)).trans (add_le_add (totalDegree_X (R := ℝ)
      (wv i)).le hyrd)
    omega
  · rw [totalDegree_neg]
    have h3 : 2 * r * y.totalDegree ≤ 2 * (r * e) := by
      calc 2 * r * y.totalDegree ≤ 2 * r * e := Nat.mul_le_mul_left _ hyd
        _ = 2 * (r * e) := by ring
    have h1 := (totalDegree_pow y (2 * r)).trans h3
    have h2 := totalDegree_X_sq_sub_X_le (wv i)
    omega
  · refine (coeffNorm1_pow_le _ 2).trans ?_
    have h : coeffNorm1 (X (wv i) * y ^ r) ≤ W ^ (c * r) :=
      (coeffNorm1_mul_le (X (wv i)) (y ^ r)).trans (by rw [coeffNorm1_X, one_mul]; exact hyr)
    calc coeffNorm1 (X (wv i) * y ^ r) ^ 2 ≤ (W ^ (c * r)) ^ 2 :=
          pow_le_pow_left₀ (coeffNorm1_nonneg _) h 2
      _ = W ^ (2 * c * r) := by rw [← pow_mul]; ring_nf
  · rw [coeffNorm1_neg]
    refine (coeffNorm1_pow_le _ _).trans ?_
    calc coeffNorm1 y ^ (2 * r) ≤ (W ^ c) ^ (2 * r) :=
          pow_le_pow_left₀ (coeffNorm1_nonneg _) hyn _
      _ = W ^ (2 * c * r) := by rw [← pow_mul]; ring_nf

/-- `(1 - wᵢ) y^(2r) ≥ 0`, for `deg y ≤ e` and `‖y‖₁ ≤ W^c`. -/
theorem one_sub_w_mul_pow (hW : 2 ≤ W) (i : ι) {y : MvPolynomial σ ℝ} {e c : ℕ}
    (hyd : y.totalDegree ≤ e) (hyn : coeffNorm1 y ≤ W ^ c) (r : ℕ) :
    SosPlusIdeal A (2 * (r * e) + 2) (W ^ (2 * c * r + 2)) ((1 - X (wv i)) * y ^ (2 * r)) := by
  classical
  have hB : BooleanOn A {wv i} := fun j hj ↦ by
    rw [Finset.mem_singleton.1 hj]; exact hbool i
  have h1 := hB.one_sub_X_nonneg (Finset.mem_singleton_self _)
  have hq : IsSumSq (y ^ (2 * r)) := by rw [pow_mul']; exact isSumSq_sq _
  have hqd : (y ^ (2 * r)).totalDegree ≤ 2 * (r * e) := (totalDegree_pow _ _).trans
    (by
      calc 2 * r * y.totalDegree ≤ 2 * r * e := Nat.mul_le_mul_left _ hyd
        _ = 2 * (r * e) := by ring)
  have hqn : coeffNorm1 (y ^ (2 * r)) ≤ W ^ (2 * c * r) := (coeffNorm1_pow_le _ _).trans
    (by
      calc coeffNorm1 y ^ (2 * r) ≤ (W ^ c) ^ (2 * r) :=
            pow_le_pow_left₀ (coeffNorm1_nonneg _) hyn _
        _ = W ^ (2 * c * r) := by rw [← pow_mul]; ring_nf)
  have h4 : (4 : ℝ) ≤ W ^ 2 := by nlinarith
  have h := SosPlusIdeal.mulSOSW hW hq hqd hqn (h1.mono (M' := W ^ 2) le_rfl h4)
  exact h.congr (mul_comm _ _)

/-- `∑_{i ∈ T} wᵢ ≥ 0`, for `|T| ≤ W^c`. -/
theorem sum_wW (T : Finset ι) {c : ℕ} (hT : (T.card : ℝ) ≤ W ^ c) :
    SosPlusIdeal A 2 (W ^ c) (∑ i ∈ T, X (wv i)) := by
  classical
  have hB : BooleanOn A (T.image wv) := fun j hj ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj; exact hbool i
  exact (hB.sum_nonneg T fun i hi ↦ Finset.mem_image_of_mem _ hi).mono le_rfl hT

/-- `|T| - ∑_{i ∈ T} wᵢ ≥ 0`, for `|T| ≤ W^c`. -/
theorem card_sub_sum_wW (hW : 2 ≤ W) (T : Finset ι) {c : ℕ} (hT : (T.card : ℝ) ≤ W ^ c) :
    SosPlusIdeal A 2 (W ^ (c + 2)) (C (T.card : ℝ) - ∑ i ∈ T, X (wv i)) := by
  classical
  have hB : BooleanOn A (T.image wv) := fun j hj ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj; exact hbool i
  refine (hB.card_sub_sum_nonneg T fun i hi ↦ Finset.mem_image_of_mem _ hi).mono le_rfl ?_
  have h4 : (4 : ℝ) ≤ W ^ 2 := by nlinarith
  calc 4 * (T.card : ℝ) ≤ W ^ 2 * W ^ c :=
        mul_le_mul h4 hT (Nat.cast_nonneg _) (pow_nonneg_of_two_le hW 2)
    _ = W ^ (c + 2) := by rw [pow_add, mul_comm]

end Boolean

end SoS
