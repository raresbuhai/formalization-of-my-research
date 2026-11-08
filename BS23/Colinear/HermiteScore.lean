module

public import BS23.Colinear.Alg
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The empirical Hermite score as a polynomial in raw moments

The empirical Hermite moment `P̂_m(λ) = (1/n) ∑_j He_m(⟨λ, y_j - ȳ⟩; λᵀĈλ)`
(`BS23.Colinear.phat`) depends on the points only through the raw empirical moments
`E_r = (1/n) ∑_j ⟨y_j - c₀, λ⟩^r` (`BS23.Colinear.rawMom`) about any reference point `c₀`:
`P̂_m(λ) = F_m(E)` (`BS23.Colinear.phat_eq_Fm`) for the explicit polynomial

`F_m(z) = ∑_{i ≤ m/2} (-1)^i C(m,2i) (2i-1)‼ (z₂ - z₁²)^i ∑_{r ≤ m-2i} C(m-2i,r) z_r (-z₁)^(m-2i-r)`

(`BS23.Colinear.Fm`; the inner sum is the central moment `BS23.Colinear.cenMom` of order `m - 2i`
expressed through the raw moments, and `z₂ - z₁²` is the variance).

* `F_m` is Lipschitz on a box: if `z₀ = w₀ = 1`, `|w_r| ≤ K^r` for `r ≤ m` and
  `|z_r - w_r| ≤ δ ≤ 1` for `1 ≤ r ≤ m`, with `K ≥ 1`, then
  `|F_m(z) - F_m(w)| ≤ δ (6 (m+1) K)^(2(m+1))`
  (`BS23.Colinear.abs_Fm_sub_Fm_le`, with `BS23.Colinear.fmLip`).
* At centered moments (`w₁ = 0`, `w₂ = q`), `F_m(w) = ∑_i (-1)^i C(m, 2i) (2i-1)‼ q^i w_(m-2i)`
  (`BS23.Colinear.Fm_of_center`).
* Homogeneity: `E_r(c λ) = c^r E_r(λ)` (`BS23.Colinear.rawMom_smul`) and
  `F_m(c^r z_r) = c^m F_m(z)` (`BS23.Colinear.Fm_smul`).
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset

variable {n d : ℕ}

/-! ### The polynomial `F_m` -/

/-- The central moment of order `p` in terms of the raw moments `z`:
`∑_{r ≤ p} C(p, r) z_r (-z₁)^(p-r)`. -/
def cenMom (p : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ r ∈ range (p + 1), (p.choose r : ℝ) * z r * (-z 1) ^ (p - r)

/-- The Hermite score as a polynomial in the raw moments `z₀, …, z_m`:
`∑_{i ≤ m/2} (-1)^i C(m, 2i) (2i-1)‼ (z₂ - z₁²)^i · cenMom (m - 2i) z`. -/
def Fm (m : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) * (z 2 - z 1 ^ 2) ^ i *
    cenMom (m - 2 * i) z

theorem Fm_eq (m : ℕ) (z : ℕ → ℝ) :
    Fm m z = ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) * (z 2 - z 1 ^ 2) ^ i *
      ∑ r ∈ range (m - 2 * i + 1), ((m - 2 * i).choose r : ℝ) * z r * (-z 1) ^ (m - 2 * i - r) :=
  rfl

/-- The Lipschitz constant of `F_m` on the box of side `K`: `(6 (m+1) K)^(2(m+1))`. -/
def fmLip (m : ℕ) (K : ℝ) : ℝ := (6 * (m + 1) * K) ^ (2 * (m + 1))

/-! ### `P̂_m` in terms of the raw moments -/

/-- The raw empirical moments of the projections about `c₀`:
`E_r = (1/n) ∑_j ⟨y_j - c₀, v⟩^r`. -/
noncomputable def rawMom (Y : Fin n → Fin d → ℝ) (c₀ v : Fin d → ℝ) (r : ℕ) : ℝ :=
  (∑ j, ((Y j - c₀) ⬝ᵥ v) ^ r) / n

variable (Y : Fin n → Fin d → ℝ) (c₀ v : Fin d → ℝ)

theorem rawMom_zero (hn : 0 < n) : rawMom Y c₀ v 0 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [rawMom, this]

theorem mean_sub_dotProduct (hn : 0 < n) : (mean Y - c₀) ⬝ᵥ v = rawMom Y c₀ v 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [rawMom, pow_one, dotProduct, mean, Pi.sub_apply]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sum_pow_div_eq_cenMom (hn : 0 < n) (p : ℕ) :
    (∑ j, ((Y j - mean Y) ⬝ᵥ v) ^ p) / n = cenMom p (rawMom Y c₀ v) := by
  have hx : ∀ j, (Y j - mean Y) ⬝ᵥ v = (Y j - c₀) ⬝ᵥ v + -rawMom Y c₀ v 1 := by
    intro j
    rw [← mean_sub_dotProduct Y c₀ v hn, ← sub_eq_add_neg, ← sub_dotProduct,
      sub_sub_sub_cancel_right]
  simp_rw [hx, add_pow]
  rw [Finset.sum_comm, Finset.sum_div]
  unfold cenMom
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [rawMom]
  ring

theorem quad_empCov : quad (empCov Y) v = (∑ j, ((Y j - mean Y) ⬝ᵥ v) ^ 2) / n := by
  have h : ∀ j, ((Y j - mean Y) ⬝ᵥ v) ^ 2 =
      ∑ a, ∑ b, v a * ((Y j a - mean Y a) * (Y j b - mean Y b) * v b) := by
    intro j
    simp only [dotProduct, sq, Finset.sum_mul_sum, Pi.sub_apply]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  simp_rw [h]
  simp only [quad, empCov, dotProduct, mulVec, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]; enter [2, a]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun j _ ↦ by ring

theorem quad_empCov_eq (hn : 0 < n) :
    quad (empCov Y) v = rawMom Y c₀ v 2 - rawMom Y c₀ v 1 ^ 2 := by
  rw [quad_empCov, sum_pow_div_eq_cenMom Y c₀ v hn]
  simp [cenMom, Finset.sum_range_succ, rawMom_zero Y c₀ v hn]
  ring

/-- **`P̂_m` as a polynomial in the raw moments** about any reference point `c₀`. -/
theorem phat_eq_Fm (hn : 0 < n) (m : ℕ) : phat m Y v = Fm m (rawMom Y c₀ v) := by
  unfold phat Fm hermite
  rw [Finset.sum_comm, Finset.sum_div, ← quad_empCov_eq Y c₀ v hn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← sum_pow_div_eq_cenMom Y c₀ v hn, Finset.sum_div, Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-! ### Homogeneity -/

theorem rawMom_smul (c : ℝ) (r : ℕ) : rawMom Y c₀ (c • v) r = c ^ r * rawMom Y c₀ v r := by
  simp only [rawMom, dotProduct_smul, smul_eq_mul, mul_pow, ← Finset.mul_sum, mul_div_assoc]

theorem cenMom_smul (c : ℝ) (z : ℕ → ℝ) (p : ℕ) :
    cenMom p (fun r ↦ c ^ r * z r) = c ^ p * cenMom p z := by
  unfold cenMom
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr' : r ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [show c ^ p = c ^ r * c ^ (p - r) by rw [← pow_add, Nat.add_sub_cancel' hr'],
    show -(c ^ 1 * z 1) = c * -z 1 by ring, mul_pow]
  ring

/-- **Weighted homogeneity of `F_m`**: scaling the `r`-th input by `c^r` scales `F_m` by `c^m`. -/
theorem Fm_smul (c : ℝ) (z : ℕ → ℝ) (m : ℕ) :
    Fm m (fun r ↦ c ^ r * z r) = c ^ m * Fm m z := by
  unfold Fm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : 2 * i ≤ m := by
    have := Finset.mem_range.mp hi
    omega
  rw [cenMom_smul, show c ^ m = (c ^ 2) ^ i * c ^ (m - 2 * i) by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hi'],
    show c ^ 2 * z 2 - (c ^ 1 * z 1) ^ 2 = c ^ 2 * (z 2 - z 1 ^ 2) by ring, mul_pow]
  ring

/-! ### The population form -/

theorem cenMom_of_center (z : ℕ → ℝ) (h1 : z 1 = 0) (p : ℕ) : cenMom p z = z p := by
  unfold cenMom
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro r hr
    have : p - r ≠ 0 := by
      have := Finset.mem_range.mp hr
      omega
    simp [h1, this]

/-- **`F_m` at centered moments**: if `z₁ = 0` and `z₂ = q` then
`F_m(z) = ∑_i (-1)^i C(m, 2i) (2i-1)‼ q^i z_(m-2i)`. -/
theorem Fm_of_center (m : ℕ) (z : ℕ → ℝ) (q : ℝ) (h1 : z 1 = 0) (h2 : z 2 = q) :
    Fm m z = ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) * q ^ i * z (m - 2 * i) := by
  unfold Fm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cenMom_of_center z h1, h1, h2]
  ring

/-! ### The Lipschitz bound -/

theorem abs_mul_sub_mul_le (a b a' b' : ℝ) :
    |a * b - a' * b'| ≤ |a - a'| * |b| + |a'| * |b - b'| := by
  rw [show a * b - a' * b' = (a - a') * b + a' * (b - b') by ring, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _

/-- Powers of close numbers bounded by `M` are close. -/
theorem abs_pow_sub_pow_le_of {a b M ε : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hab : |a - b| ≤ ε)
    (k : ℕ) : |a ^ k - b ^ k| ≤ ε * k * M ^ (k - 1) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hab
  have h0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  refine (abs_pow_sub_pow_le (a := a) (b := b) (n := k)).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg k))
    (pow_le_pow_left₀ h0 (max_le ha hb) _) (by positivity) (by positivity)

/-- A sum weighted by binomial coefficients. -/
theorem abs_sum_choose_le {p : ℕ} {f : ℕ → ℝ} {B : ℝ}
    (h : ∀ r ∈ range (p + 1), |f r| ≤ p.choose r * B) :
    |∑ r ∈ range (p + 1), f r| ≤ 2 ^ p * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum h).trans_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

theorem hermCoeff_le_pow {m i : ℕ} (hi : 2 * i ≤ m) : hermCoeff m i ≤ (m + 1) ^ m := by
  unfold hermCoeff
  calc m.choose (2 * i) * Nat.doubleFactorial (2 * i - 1) ≤
        m.choose (2 * i) * Nat.factorial (2 * i) := by
        gcongr
        exact (Nat.doubleFactorial_le_factorial _).trans (Nat.factorial_le (Nat.sub_le _ _))
    _ = m.descFactorial (2 * i) := by rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
    _ ≤ m ^ (2 * i) := Nat.descFactorial_le_pow _ _
    _ ≤ (m + 1) ^ (2 * i) := Nat.pow_le_pow_left (Nat.le_succ m) _
    _ ≤ (m + 1) ^ m := Nat.pow_le_pow_right (Nat.succ_pos m) hi

section Lipschitz

variable {m : ℕ} {K δ : ℝ} {z w : ℕ → ℝ}

/-- The hypotheses of the Lipschitz bound: `z₀ = w₀ = 1`, `|w_r| ≤ K^r` and `|z_r - w_r| ≤ δ`
for `1 ≤ r ≤ m`, with `1 ≤ K` and `0 ≤ δ ≤ 1`. -/
structure LipHyp (m : ℕ) (K δ : ℝ) (z w : ℕ → ℝ) : Prop where
  one_le_K : 1 ≤ K
  nonneg : 0 ≤ δ
  le_one : δ ≤ 1
  z_zero : z 0 = 1
  w_zero : w 0 = 1
  w_le : ∀ r ≤ m, |w r| ≤ K ^ r
  sub_le : ∀ r, 1 ≤ r → r ≤ m → |z r - w r| ≤ δ

namespace LipHyp

variable (H : LipHyp m K δ z w)
include H

theorem K_nonneg : 0 ≤ K := zero_le_one.trans H.one_le_K

theorem sub_le' {r : ℕ} (hr : r ≤ m) : |z r - w r| ≤ δ := by
  rcases Nat.eq_zero_or_pos r with rfl | h
  · simp [H.z_zero, H.w_zero, H.nonneg]
  · exact H.sub_le r h hr

theorem z_le {r : ℕ} (hr : r ≤ m) : |z r| ≤ 2 * K ^ r := by
  have h1 : 1 ≤ K ^ r := one_le_pow₀ H.one_le_K
  calc |z r| = |w r + (z r - w r)| := by ring_nf
    _ ≤ |w r| + |z r - w r| := abs_add_le _ _
    _ ≤ K ^ r + 1 := add_le_add (H.w_le r hr) ((H.sub_le' hr).trans H.le_one)
    _ ≤ 2 * K ^ r := by linarith

theorem pow_K_le_two {r : ℕ} : K ^ r ≤ (2 * K) ^ r :=
  pow_le_pow_left₀ H.K_nonneg (by linarith [H.K_nonneg]) r

theorem one_le_two_K : 1 ≤ 2 * K := by linarith [H.one_le_K]

/-- Powers of `-z₁` and `-w₁`. -/
theorem neg_pow {k : ℕ} (hk : k ≤ m) :
    |(-z 1) ^ k| ≤ (2 * K) ^ k ∧ |(-w 1) ^ k| ≤ (2 * K) ^ k ∧
      |(-z 1) ^ k - (-w 1) ^ k| ≤ k * (2 * K) ^ k * δ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have h1 : 1 ≤ m := hk0.trans_le hk
  have hz1 : |-z 1| ≤ 2 * K := by simpa using H.z_le h1
  have hw1 : |-w 1| ≤ 2 * K := by
    have := H.w_le 1 h1
    rw [abs_neg]
    linarith [H.K_nonneg]
  have hzw : |-z 1 - -w 1| ≤ δ := by
    rw [show -z 1 - -w 1 = -(z 1 - w 1) by ring, abs_neg]
    exact H.sub_le' h1
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz1 k
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hw1 k
  · refine (abs_pow_sub_pow_le_of hz1 hw1 hzw k).trans ?_
    have : (2 * K) ^ (k - 1) ≤ (2 * K) ^ k := pow_le_pow_right₀ H.one_le_two_K (Nat.sub_le _ _)
    have hk : (0 : ℝ) ≤ k * δ := mul_nonneg (Nat.cast_nonneg k) H.nonneg
    calc δ * k * (2 * K) ^ (k - 1) = (k * δ) * (2 * K) ^ (k - 1) := by ring
      _ ≤ (k * δ) * (2 * K) ^ k := mul_le_mul_of_nonneg_left this hk
      _ = k * (2 * K) ^ k * δ := by ring

/-- The central moments: `|cenMom p z| ≤ 2 (4K)^p`. -/
theorem cenMom_le {p : ℕ} (hp : p ≤ m) : |cenMom p z| ≤ 2 * (4 * K) ^ p := by
  rw [show (4 * K) ^ p = 2 ^ p * (2 * K) ^ p by rw [← mul_pow]; ring_nf, mul_left_comm]
  refine abs_sum_choose_le fun r hr ↦ ?_
  have hr' : r ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hK := H.K_nonneg
  calc |z r| * |(-z 1) ^ (p - r)| ≤ (2 * K ^ r) * (2 * K) ^ (p - r) :=
        mul_le_mul (H.z_le (hr'.trans hp)) (H.neg_pow ((Nat.sub_le _ _).trans hp)).1
          (abs_nonneg _) (by positivity)
    _ ≤ (2 * (2 * K) ^ r) * (2 * K) ^ (p - r) := by
        have := H.pow_K_le_two (r := r)
        have : 0 ≤ (2 * K) ^ (p - r) := by have := H.K_nonneg; positivity
        nlinarith
    _ = 2 * (2 * K) ^ p := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hr']

/-- The central moments are close: `|cenMom p z - cenMom p w| ≤ (p+1) (4K)^p δ`. -/
theorem cenMom_sub_le {p : ℕ} (hp : p ≤ m) :
    |cenMom p z - cenMom p w| ≤ (p + 1) * (4 * K) ^ p * δ := by
  rw [show (p + 1) * (4 * K) ^ p * δ = 2 ^ p * ((p + 1) * (2 * K) ^ p * δ) by
      rw [show (4 * K) ^ p = 2 ^ p * (2 * K) ^ p by rw [← mul_pow]; ring_nf]; ring]
  unfold cenMom
  rw [← Finset.sum_sub_distrib]
  refine abs_sum_choose_le fun r hr ↦ ?_
  have hr' : r ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [show (p.choose r : ℝ) * z r * (-z 1) ^ (p - r) - p.choose r * w r * (-w 1) ^ (p - r) =
      p.choose r * (z r * (-z 1) ^ (p - r) - w r * (-w 1) ^ (p - r)) by ring, abs_mul,
    Nat.abs_cast]
  gcongr
  obtain ⟨h1, -, h3⟩ := H.neg_pow ((Nat.sub_le p r).trans hp)
  have hK := H.K_nonneg
  have e1 : (2 * K) ^ (p - r) ≤ (2 * K) ^ p := pow_le_pow_right₀ H.one_le_two_K (Nat.sub_le _ _)
  have e2 : K ^ r * (2 * K) ^ (p - r) ≤ (2 * K) ^ p :=
    calc K ^ r * (2 * K) ^ (p - r) ≤ (2 * K) ^ r * (2 * K) ^ (p - r) :=
          mul_le_mul_of_nonneg_right H.pow_K_le_two (by positivity)
      _ = (2 * K) ^ p := by rw [← pow_add, Nat.add_sub_cancel' hr']
  have hδ := H.nonneg
  have e3 : ((p - r : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p r
  have hd := H.sub_le' (hr'.trans hp)
  have hwr := H.w_le r (hr'.trans hp)
  refine (abs_mul_sub_mul_le _ _ _ _).trans ?_
  calc |z r - w r| * |(-z 1) ^ (p - r)| + |w r| * |(-z 1) ^ (p - r) - (-w 1) ^ (p - r)|
      ≤ δ * (2 * K) ^ (p - r) + K ^ r * ((p - r : ℕ) * (2 * K) ^ (p - r) * δ) := by
        gcongr
    _ = δ * (2 * K) ^ (p - r) + (p - r : ℕ) * (K ^ r * (2 * K) ^ (p - r)) * δ := by ring
    _ ≤ δ * (2 * K) ^ p + p * (2 * K) ^ p * δ := by
        have := H.nonneg
        gcongr
    _ = (p + 1) * (2 * K) ^ p * δ := by ring

/-- The variance term: `|(z₂ - z₁²)^i| ≤ (6K²)^i`, the same for `w`, and the two are close. -/
theorem var_pow {i : ℕ} (hi : 2 * i ≤ m) :
    |(z 2 - z 1 ^ 2) ^ i| ≤ (6 * K ^ 2) ^ i ∧ |(w 2 - w 1 ^ 2) ^ i| ≤ (6 * K ^ 2) ^ i ∧
      |(z 2 - z 1 ^ 2) ^ i - (w 2 - w 1 ^ 2) ^ i| ≤ i * (6 * K ^ 2) ^ i * δ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have h2 : 2 ≤ m := by omega
  have h1 : 1 ≤ m := by omega
  have hK := H.K_nonneg
  have hK1 := H.one_le_K
  have hz1 := H.z_le h1
  have hz2 := H.z_le h2
  have hw1 := H.w_le 1 h1
  have hw2 := H.w_le 2 h2
  have hd1 := H.sub_le' h1
  have hd2 := H.sub_le' h2
  have hδ := H.nonneg
  simp only [pow_one] at hz1 hw1 hd1
  have hz : |z 2 - z 1 ^ 2| ≤ 6 * K ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_pow]
    have : |z 1| ^ 2 ≤ (2 * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz1 2
    nlinarith
  have hw : |w 2 - w 1 ^ 2| ≤ 6 * K ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_pow]
    have : |w 1| ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw1 2
    nlinarith
  have hzw : |(z 2 - z 1 ^ 2) - (w 2 - w 1 ^ 2)| ≤ 6 * K ^ 2 * δ := by
    rw [show (z 2 - z 1 ^ 2) - (w 2 - w 1 ^ 2) = (z 2 - w 2) - (z 1 - w 1) * (z 1 + w 1) by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have : |z 1 + w 1| ≤ 3 * K := (abs_add_le _ _).trans (by linarith)
    have : |z 1 - w 1| * |z 1 + w 1| ≤ δ * (3 * K) :=
      mul_le_mul hd1 this (abs_nonneg _) hδ
    have hK2 : K ≤ K ^ 2 := by nlinarith
    have : δ ≤ K ^ 2 * δ := le_mul_of_one_le_left hδ (by nlinarith)
    have : K * δ ≤ K ^ 2 * δ := mul_le_mul_of_nonneg_right hK2 hδ
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz i
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hw i
  · refine (abs_pow_sub_pow_le_of hz hw hzw i).trans_eq ?_
    rw [show (6 * K ^ 2) ^ i = 6 * K ^ 2 * (6 * K ^ 2) ^ (i - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hi0]]
    ring

/-- One term of `F_m`. -/
theorem term_sub_le {i : ℕ} (hi : 2 * i ≤ m) :
    |(-1) ^ i * (hermCoeff m i : ℝ) * (z 2 - z 1 ^ 2) ^ i * cenMom (m - 2 * i) z -
        (-1) ^ i * (hermCoeff m i : ℝ) * (w 2 - w 1 ^ 2) ^ i * cenMom (m - 2 * i) w| ≤
      (hermCoeff m i : ℝ) * ((m + 1) * (6 * K) ^ m * δ) := by
  rw [show ∀ a b a' b' : ℝ, (-1) ^ i * (hermCoeff m i : ℝ) * a * b -
      (-1) ^ i * (hermCoeff m i : ℝ) * a' * b' = (-1) ^ i * (hermCoeff m i : ℝ) * (a * b - a' * b')
      from fun _ _ _ _ ↦ by ring, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]
  gcongr
  obtain ⟨-, a2, a3⟩ := H.var_pow hi
  have hp : m - 2 * i ≤ m := Nat.sub_le _ _
  have b1 := H.cenMom_le hp
  have b2 := H.cenMom_sub_le hp
  have hK := H.K_nonneg
  have hδ := H.nonneg
  have e1 : (6 * K ^ 2) ^ i * (4 * K) ^ (m - 2 * i) ≤ (6 * K) ^ m := by
    rw [← Nat.add_sub_cancel' hi, pow_add, Nat.add_sub_cancel_left, pow_mul]
    gcongr
    · nlinarith
    · linarith
  have e2 : (2 * i + ((m - 2 * i : ℕ) + 1) : ℝ) = m + 1 := by
    rw [Nat.cast_sub hi]; push_cast; ring
  refine (abs_mul_sub_mul_le _ _ _ _).trans ?_
  calc |(z 2 - z 1 ^ 2) ^ i - (w 2 - w 1 ^ 2) ^ i| * |cenMom (m - 2 * i) z| +
        |(w 2 - w 1 ^ 2) ^ i| * |cenMom (m - 2 * i) z - cenMom (m - 2 * i) w|
      ≤ (i * (6 * K ^ 2) ^ i * δ) * (2 * (4 * K) ^ (m - 2 * i)) +
        (6 * K ^ 2) ^ i * ((((m - 2 * i : ℕ) : ℝ) + 1) * (4 * K) ^ (m - 2 * i) * δ) := by
        gcongr
    _ = (2 * i + ((m - 2 * i : ℕ) + 1)) * ((6 * K ^ 2) ^ i * (4 * K) ^ (m - 2 * i)) * δ := by
        ring
    _ ≤ (m + 1) * (6 * K) ^ m * δ := by
        rw [e2]
        gcongr

end LipHyp

end Lipschitz

/-- **Lipschitz bound for `F_m`** on the box of side `K`: if `z₀ = w₀ = 1`, `|w_r| ≤ K^r` for
`r ≤ m` and `|z_r - w_r| ≤ δ` for `1 ≤ r ≤ m`, with `1 ≤ K` and `0 ≤ δ ≤ 1`, then
`|F_m(z) - F_m(w)| ≤ δ (6 (m+1) K)^(2(m+1))`. -/
theorem abs_Fm_sub_Fm_le {m : ℕ} {K δ : ℝ} {z w : ℕ → ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hz : z 0 = 1) (hw : w 0 = 1) (hwK : ∀ r ≤ m, |w r| ≤ K ^ r)
    (hzw : ∀ r, 1 ≤ r → r ≤ m → |z r - w r| ≤ δ) :
    |Fm m z - Fm m w| ≤ δ * fmLip m K := by
  have H : LipHyp m K δ z w := ⟨hK, hδ, hδ1, hz, hw, hwK, hzw⟩
  unfold Fm
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  calc ∑ i ∈ range (m / 2 + 1), |(-1) ^ i * (hermCoeff m i : ℝ) * (z 2 - z 1 ^ 2) ^ i *
          cenMom (m - 2 * i) z - (-1) ^ i * (hermCoeff m i : ℝ) * (w 2 - w 1 ^ 2) ^ i *
          cenMom (m - 2 * i) w|
      ≤ ∑ i ∈ range (m / 2 + 1), ((m + 1 : ℝ) ^ m * ((m + 1) * (6 * K) ^ m * δ)) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : 2 * i ≤ m := by
          have := Finset.mem_range.mp hi
          omega
        refine (H.term_sub_le hi').trans ?_
        gcongr
        exact_mod_cast hermCoeff_le_pow hi'
    _ = (m / 2 + 1 : ℕ) * ((m + 1 : ℝ) ^ (m + 1) * (6 * K) ^ m) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ (m + 1 : ℝ) * ((m + 1 : ℝ) ^ (m + 1) * (6 * K) ^ (m + 2)) * δ := by
        gcongr
        · push_cast
          have : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
          linarith
        · linarith
        · omega
    _ = ((m + 1 : ℝ) * (6 * K)) ^ (m + 2) * δ := by
        rw [mul_pow (m + 1 : ℝ) (6 * K) (m + 2)]
        ring
    _ ≤ δ * fmLip m K := by
        rw [mul_comm _ δ, fmLip, show (6 : ℝ) * (m + 1) * K = (m + 1) * (6 * K) by ring]
        have h1 : (1 : ℝ) ≤ (m + 1) * (6 * K) :=
          one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
            (by linarith)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) hδ

end BS23.Colinear
