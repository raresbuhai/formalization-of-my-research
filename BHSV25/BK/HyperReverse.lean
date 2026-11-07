module

public import OAI.Computability.MaxCut.Estimates.Degree

/-!
# Reverse hypercontractivity on the cube

For `f, h : {0,1}^n → [0,1]`, an integer `k ≥ 1` and `0 ≤ r ≤ 1 - 1/k`,
`E_x[f(x) T_r h(x)] ≥ (E f)^k (E h)^k` (`BHSV25.BK.Aint.rev_hc`), where `T_r` is OpenAI's noise
operator `noise r`. This is the special case `p = q = 1/k` of Borell's reverse hypercontractive
inequality `E[F(x) G(y)] ≥ ‖F‖_p ‖G‖_q` for `r`-correlated `x, y` (applied to `F = f^k`,
`G = h^k`); see Mossel, O'Donnell, Regev, Steif, Sudakov, *Non-interactive correlation
distillation, inhomogeneous Markov chains, and the reverse Bonami–Beckner inequality*, Israel J.
Math. 154 (2006), and O'Donnell, *Analysis of Boolean functions*, §10.3.

Proof: induction on `n`, splitting off the first coordinate (`BHSV25.BK.Aint.corr_succ`), from the
two-point inequality (`BHSV25.BK.Aint.two_point`)
`((1+r)(p₁ᵏq₁ᵏ + p₂ᵏq₂ᵏ) + (1-r)(p₁ᵏq₂ᵏ + p₂ᵏq₁ᵏ))/4 ≥ ((p₁+p₂)/2)ᵏ ((q₁+q₂)/2)ᵏ`. With `A, D`
(`B, E`) the half sum and half difference of `p₁ᵏ, p₂ᵏ` (of `q₁ᵏ, q₂ᵏ`) the left side is
`AB + rDE`, and Aczél's inequality `(AB - r|D||E|)² ≥ (A² - rD²)(B² - rE²)` reduces it to the
one-function form `A² - rD² ≥ ((p₁+p₂)/2)^{2k}` (`BHSV25.BK.Aint.one_fn`), i.e.
`x^{2k} + y^{2k} + (4k-2)(xy)ᵏ ≥ 4k((x+y)/2)^{2k}` (`BHSV25.BK.Aint.key_ineq`). The latter holds
with equality at `x = y` and its derivative along `x = m + t`, `y = m - t` is
`2k(x - y)(Σ_{j<2k-1} xʲ y^{2k-2-j} - (2k-1)(xy)^{k-1}) ≥ 0` (AM-GM on symmetric pairs).

Consequence (`BHSV25.BK.Aint.few_high`): if `g : {0,1}^n → [0,1]` has `E g ≤ 1/2` and `f ∈ [0,1]` is
supported where `T_r g ≥ 1 - δ`, then `(E f)^{k-1} ≤ 2ᵏ δ` (`k ≥ 2`): take `h = 1 - g`.
-/

@[expose] public section

namespace BHSV25.BK.Aint

open Finset Set
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

/-! ### The one-variable inequality -/

/-- AM-GM on symmetric pairs: `Σ_{j ≤ 2n} xʲ y^{2n-j} ≥ (2n+1)(xy)ⁿ`. -/
theorem geom_sum_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℝ) * (x * y) ^ n ≤ ∑ j ∈ range (2 * n + 1), x ^ j * y ^ (2 * n - j) := by
  have hpair : ∀ j ∈ range (2 * n + 1),
      2 * (x * y) ^ n ≤ x ^ j * y ^ (2 * n - j) + x ^ (2 * n - j) * y ^ (2 * n - (2 * n - j)) := by
    intro j hj
    have hj' : j ≤ 2 * n := by simp at hj; omega
    rw [Nat.sub_sub_self hj']
    obtain ⟨u, hu⟩ : ∃ u, u = x ^ j * y ^ (2 * n - j) := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = x ^ (2 * n - j) * y ^ j := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (x * y) ^ n := ⟨_, rfl⟩
    have huv : u * v = w ^ 2 := by
      rw [hu, hv, hw, ← pow_mul, mul_pow]
      have e1 : x ^ j * x ^ (2 * n - j) = x ^ (n * 2) := by
        rw [← pow_add]; congr 1; omega
      have e2 : y ^ (2 * n - j) * y ^ j = y ^ (n * 2) := by
        rw [← pow_add]; congr 1; omega
      calc x ^ j * y ^ (2 * n - j) * (x ^ (2 * n - j) * y ^ j)
          = (x ^ j * x ^ (2 * n - j)) * (y ^ (2 * n - j) * y ^ j) := by ring
        _ = x ^ (n * 2) * y ^ (n * 2) := by rw [e1, e2]
    have hu0 : 0 ≤ u := hu ▸ by positivity
    have hv0 : 0 ≤ v := hv ▸ by positivity
    have hw0 : 0 ≤ w := hw ▸ by positivity
    rw [← hu, ← hv, ← hw]
    nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - 2 * w)]
  have hrefl : ∑ j ∈ range (2 * n + 1), x ^ (2 * n - j) * y ^ (2 * n - (2 * n - j)) =
      ∑ j ∈ range (2 * n + 1), x ^ j * y ^ (2 * n - j) := by
    rw [← Finset.sum_range_reflect (fun j ↦ x ^ j * y ^ (2 * n - j)) (2 * n + 1)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 2
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, hrefl, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

/-- The function whose monotonicity gives `key_ineq`. -/
noncomputable def keyH (k : ℕ) (m t : ℝ) : ℝ :=
  (m + t) ^ (2 * k) + (m - t) ^ (2 * k) + (4 * k - 2) * (m ^ 2 - t ^ 2) ^ k

theorem hasDerivAt_keyH (k : ℕ) (m t : ℝ) :
    HasDerivAt (keyH k m)
      ((2 * k : ℕ) * (m + t) ^ (2 * k - 1) * 1 + (2 * k : ℕ) * (m - t) ^ (2 * k - 1) * (-1) +
        (4 * k - 2) * ((k : ℝ) * (m ^ 2 - t ^ 2) ^ (k - 1) * (-(2 * t)))) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ m + t) 1 t := (hasDerivAt_id t).const_add m
  have h2 : HasDerivAt (fun t : ℝ ↦ m - t) (-1) t := (hasDerivAt_id t).const_sub m
  have h3 : HasDerivAt (fun t : ℝ ↦ m ^ 2 - t ^ 2) (-(2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_sub (m ^ 2)
    convert this using 1
    simp
  have := ((h1.pow (2 * k)).add (h2.pow (2 * k))).add ((h3.pow k).const_mul (4 * k - 2 : ℝ))
  convert this using 1
  funext s
  simp only [keyH, Pi.add_apply, Pi.pow_apply]

theorem keyH_deriv_nonneg {k : ℕ} (hk : 1 ≤ k) {m t : ℝ} (ht : 0 ≤ t) (htm : t ≤ m) :
    0 ≤ (2 * k : ℕ) * (m + t) ^ (2 * k - 1) * 1 + (2 * k : ℕ) * (m - t) ^ (2 * k - 1) * (-1) +
        (4 * k - 2) * ((k : ℝ) * (m ^ 2 - t ^ 2) ^ (k - 1) * (-(2 * t))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨X, hX⟩ : ∃ X, X = m + t := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = m - t := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hY0 : 0 ≤ Y := by rw [hY]; linarith
  have hXY : m ^ 2 - t ^ 2 = X * Y := by rw [hX, hY]; ring
  have h2t : 2 * t = X - Y := by rw [hX, hY]; ring
  have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  rw [← hX, ← hY, hXY, e1, e2, h2t]
  have hgeom := geom_sum₂_mul X Y (2 * n + 1)
  have hge := geom_sum_ge hX0 hY0 n
  have hidx : ∀ j ∈ range (2 * n + 1), X ^ j * Y ^ (2 * n + 1 - 1 - j) =
      X ^ j * Y ^ (2 * n - j) := fun j _ ↦ by congr 2
  rw [Finset.sum_congr rfl hidx] at hgeom
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range (2 * n + 1), X ^ j * Y ^ (2 * n - j) := ⟨_, rfl⟩
  rw [← hS] at hgeom hge
  have hXY0 : 0 ≤ X - Y := by rw [← h2t]; linarith
  have key : (2 * (n + 1) : ℕ) * X ^ (2 * n + 1) * 1 + (2 * (n + 1) : ℕ) * Y ^ (2 * n + 1) * (-1) +
      (4 * ((n + 1 : ℕ) : ℝ) - 2) * (((n + 1 : ℕ) : ℝ) * (X * Y) ^ n * (-(X - Y))) =
      (2 * (n + 1 : ℕ)) * ((X - Y) * (S - ((2 * n + 1 : ℕ) : ℝ) * (X * Y) ^ n)) := by
    rw [show X ^ (2 * n + 1) = Y ^ (2 * n + 1) + S * (X - Y) by linarith only [hgeom]]
    push_cast
    ring
  rw [key]
  have : 0 ≤ S - ((2 * n + 1 : ℕ) : ℝ) * (X * Y) ^ n := by linarith
  positivity

/-- `x^{2k} + y^{2k} + (4k-2)(xy)ᵏ ≥ 4k((x+y)/2)^{2k}` for `x, y ≥ 0`, `k ≥ 1`. -/
theorem key_ineq {k : ℕ} (hk : 1 ≤ k) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * k * ((x + y) / 2) ^ (2 * k) ≤ x ^ (2 * k) + y ^ (2 * k) + (4 * k - 2) * (x * y) ^ k := by
  -- reduce to `y ≤ x`
  wlog hxy : y ≤ x generalizing x y
  · have := this hy hx (le_of_not_ge hxy)
    rw [add_comm y x, mul_comm y x] at this
    linarith
  obtain ⟨m, hm⟩ : ∃ m, m = (x + y) / 2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (x - y) / 2 := ⟨_, rfl⟩
  have hxm : x = m + t := by rw [hm, ht]; ring
  have hym : y = m - t := by rw [hm, ht]; ring
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have htm : t ≤ m := by rw [hm, ht]; linarith
  have hmono : MonotoneOn (keyH k m) (Icc 0 m) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 m) ?_ ?_ ?_
    · exact fun s _ ↦ (hasDerivAt_keyH k m s).continuousAt.continuousWithinAt
    · exact fun s _ ↦ (hasDerivAt_keyH k m s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hasDerivAt_keyH k m s).deriv]
      exact keyH_deriv_nonneg hk hs.1.le hs.2.le
  have h := hmono ⟨le_rfl, ht0.trans htm⟩ ⟨ht0, htm⟩ ht0
  have h0 : keyH k m 0 = 4 * k * m ^ (2 * k) := by
    unfold keyH
    rw [show m ^ (2 * k) = (m ^ 2) ^ k by rw [← pow_mul]]
    ring
  have ht' : keyH k m t = x ^ (2 * k) + y ^ (2 * k) + (4 * k - 2) * (x * y) ^ k := by
    unfold keyH
    rw [hxm, hym]
    ring
  rw [← hm, ← h0, ← ht']
  exact h

/-- The one-function two-point inequality: `A² - rD² ≥ ((x+y)/2)^{2k}` with `A, D` the half sum
and half difference of `xᵏ, yᵏ`. -/
theorem one_fn {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : r ≤ 1 - 1 / k) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    ((x + y) / 2) ^ (2 * k) ≤ ((x ^ k + y ^ k) / 2) ^ 2 - r * ((x ^ k - y ^ k) / 2) ^ 2 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK := key_ineq hk hx hy
  have h1 : ((x ^ k + y ^ k) / 2) ^ 2 - (1 - 1 / k) * ((x ^ k - y ^ k) / 2) ^ 2 ≤
      ((x ^ k + y ^ k) / 2) ^ 2 - r * ((x ^ k - y ^ k) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((x ^ k - y ^ k) / 2)]
  have h2 : ((x ^ k + y ^ k) / 2) ^ 2 - (1 - 1 / k) * ((x ^ k - y ^ k) / 2) ^ 2 =
      (x ^ (2 * k) + y ^ (2 * k) + (4 * k - 2) * (x * y) ^ k) / (4 * k) := by
    have ex : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    have ey : y ^ (2 * k) = (y ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [ex, ey, mul_pow]
    field_simp
    ring
  rw [h2] at h1
  have h3 : ((x + y) / 2) ^ (2 * k) ≤
      (x ^ (2 * k) + y ^ (2 * k) + (4 * k - 2) * (x * y) ^ k) / (4 * k) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **The two-point inequality.** -/
theorem two_point {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 - 1 / k)
    {p₁ p₂ q₁ q₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ((p₁ + p₂) / 2) ^ k * ((q₁ + q₂) / 2) ^ k ≤
      ((1 + r) * (p₁ ^ k * q₁ ^ k + p₂ ^ k * q₂ ^ k) +
        (1 - r) * (p₁ ^ k * q₂ ^ k + p₂ ^ k * q₁ ^ k)) / 4 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : r ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  obtain ⟨A, hA⟩ : ∃ A, A = (p₁ ^ k + p₂ ^ k) / 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (p₁ ^ k - p₂ ^ k) / 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (q₁ ^ k + q₂ ^ k) / 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (q₁ ^ k - q₂ ^ k) / 2 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = ((p₁ + p₂) / 2) ^ k := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ((q₁ + q₂) / 2) ^ k := ⟨_, rfl⟩
  have hrhs : ((1 + r) * (p₁ ^ k * q₁ ^ k + p₂ ^ k * q₂ ^ k) +
      (1 - r) * (p₁ ^ k * q₂ ^ k + p₂ ^ k * q₁ ^ k)) / 4 = A * B + r * (D * E) := by
    rw [hA, hB, hD, hE]; ring
  rw [hrhs, ← hα, ← hβ]
  have hpA := one_fn hk hr hp₁ hp₂
  have hqB := one_fn hk hr hq₁ hq₂
  have eα : ((p₁ + p₂) / 2) ^ (2 * k) = α ^ 2 := by rw [hα, ← pow_mul, mul_comm]
  have eβ : ((q₁ + q₂) / 2) ^ (2 * k) = β ^ 2 := by rw [hβ, ← pow_mul, mul_comm]
  rw [← hA, ← hD, eα] at hpA
  rw [← hB, ← hE, eβ] at hqB
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hp1k : 0 ≤ p₁ ^ k := by positivity
  have hp2k : 0 ≤ p₂ ^ k := by positivity
  have hq1k : 0 ≤ q₁ ^ k := by positivity
  have hq2k : 0 ≤ q₂ ^ k := by positivity
  have hDA : |D| ≤ A := by
    rw [abs_le, hD, hA]; constructor <;> linarith
  have hEB : |E| ≤ B := by
    rw [abs_le, hE, hB]; constructor <;> linarith
  obtain ⟨d, hd⟩ : ∃ d, d = |D| := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = |E| := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ abs_nonneg D
  have he0 : 0 ≤ e := he ▸ abs_nonneg E
  rw [← hd] at hDA
  rw [← he] at hEB
  have hDd : D ^ 2 = d ^ 2 := by rw [hd, sq_abs]
  have hEe : E ^ 2 = e ^ 2 := by rw [he, sq_abs]
  rw [hDd] at hpA
  rw [hEe] at hqB
  have hDE : -(d * e) ≤ D * E := by
    rw [hd, he, ← abs_mul]; exact neg_abs_le _
  have hlow : A * B - r * (d * e) ≤ A * B + r * (D * E) := by
    have := mul_le_mul_of_nonneg_left hDE hr0
    linarith only [this]
  have hpos : 0 ≤ A * B - r * (d * e) := by
    have h1 : d * e ≤ A * B := mul_le_mul hDA hEB he0 (hd0.trans hDA)
    have h2 : r * (d * e) ≤ d * e := mul_le_of_le_one_left (mul_nonneg hd0 he0) hr1
    linarith only [h1, h2]
  have hacz : (A ^ 2 - r * d ^ 2) * (B ^ 2 - r * e ^ 2) ≤ (A * B - r * (d * e)) ^ 2 := by
    have h1 : (A * B - r * (d * e)) ^ 2 - (A ^ 2 - r * d ^ 2) * (B ^ 2 - r * e ^ 2) =
        r * (A * e - B * d) ^ 2 := by ring
    have h2 := mul_nonneg hr0 (sq_nonneg (A * e - B * d))
    linarith only [h1, h2]
  have hsq : (α * β) ^ 2 ≤ (A * B - r * (d * e)) ^ 2 := by
    calc (α * β) ^ 2 = α ^ 2 * β ^ 2 := by ring
      _ ≤ (A ^ 2 - r * d ^ 2) * (B ^ 2 - r * e ^ 2) :=
          mul_le_mul hpA hqB (sq_nonneg _) ((sq_nonneg α).trans hpA)
      _ ≤ _ := hacz
  have := (pow_le_pow_iff_left₀ (mul_nonneg hα0 hβ0) hpos (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  linarith only [this, hlow]

/-! ### Tensorization -/

/-- The correlation `E[f(x) h(y)]` for `r`-correlated `x, y` on the cube. -/
noncomputable def corr (r : ℝ) {n : ℕ} (f h : Cube (Fin n) → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, f x * h y * ∏ i, (1 + r * bitSign (y i) * bitSign (x i))

theorem corr_eq_noise (r : ℝ) {n : ℕ} (f h : Cube (Fin n) → ℝ) :
    corr r f h = 𝔼 x, f x * noise r h x := by
  unfold corr
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  rw [noise_kernel, Finset.mul_expect]
  refine Finset.expect_congr rfl fun y _ ↦ ?_
  ring

/-- Splitting off the first coordinate of an expectation over the cube. -/
theorem expect_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    𝔼 x, F x = 𝔼 b, 𝔼 x : Cube (Fin n), F (Fin.cons b x) := by
  rw [← Fintype.expect_equiv (Fin.consEquiv (fun _ ↦ Bool)) (fun p ↦ F (Fin.cons p.1 p.2)) F
    (fun p ↦ rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_bool (F : Bool → ℝ) : 𝔼 b, F b = (F true + F false) / 2 := by
  rw [Finset.expect_eq_sum_div_card, Fintype.sum_bool]
  simp

theorem corr_succ (r : ℝ) {n : ℕ} (f h : Cube (Fin (n + 1)) → ℝ) :
    corr r f h = 𝔼 a, 𝔼 b, (1 + r * bitSign b * bitSign a) *
      corr r (fun x ↦ f (Fin.cons a x)) (fun y ↦ h (Fin.cons b y)) := by
  unfold corr
  rw [expect_cube_succ]
  refine Finset.expect_congr rfl fun a _ ↦ ?_
  simp_rw [expect_cube_succ (fun y ↦ _ * h y * _), Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun y _ ↦ ?_
  ring

theorem expect_cube_zero (F : Cube (Fin 0) → ℝ) : 𝔼 x, F x = F (fun i ↦ i.elim0) := by
  rw [Finset.expect_eq_sum_div_card, Fintype.sum_unique, Finset.card_univ,
    Fintype.card_unique]
  simp only [Nat.cast_one, div_one]
  congr 1

/-- **Reverse hypercontractivity** on the cube with `p = q = 1/k`:
`E[f(x) h(y)] ≥ (E f)ᵏ (E h)ᵏ` for `[0,1]`-valued `f, h` and `r`-correlated `x, y`,
`0 ≤ r ≤ 1 - 1/k`. -/
theorem rev_hc {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 - 1 / k) :
    ∀ (n : ℕ) (f h : Cube (Fin n) → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ h x ∧ h x ≤ 1) →
      (𝔼 x, f x) ^ k * (𝔼 x, h x) ^ k ≤ corr r f h := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : r ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  intro n
  induction n with
  | zero =>
    intro f h hf hh
    unfold corr
    rw [expect_cube_zero, expect_cube_zero, expect_cube_zero, expect_cube_zero]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    obtain ⟨f0, f1⟩ := hf (fun i ↦ i.elim0)
    obtain ⟨h0, h1⟩ := hh (fun i ↦ i.elim0)
    have a := pow_le_of_le_one f0 f1 (by omega : k ≠ 0)
    have b := pow_le_of_le_one h0 h1 (by omega : k ≠ 0)
    exact mul_le_mul a b (by positivity) f0
  | succ n ih =>
    intro f h hf hh
    rw [corr_succ]
    obtain ⟨P, hP⟩ : ∃ P : Bool → ℝ, P = fun a ↦ 𝔼 x, f (Fin.cons a x) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Bool → ℝ, Q = fun b ↦ 𝔼 y, h (Fin.cons b y) := ⟨_, rfl⟩
    have hP0 : ∀ a, 0 ≤ P a := fun a ↦ hP ▸ Finset.expect_nonneg fun x _ ↦ (hf _).1
    have hQ0 : ∀ b, 0 ≤ Q b := fun b ↦ hQ ▸ Finset.expect_nonneg fun x _ ↦ (hh _).1
    have hstep : ∀ a b, (1 + r * bitSign b * bitSign a) * (P a ^ k * Q b ^ k) ≤
        (1 + r * bitSign b * bitSign a) *
          corr r (fun x ↦ f (Fin.cons a x)) (fun y ↦ h (Fin.cons b y)) := by
      intro a b
      have hw : 0 ≤ 1 + r * bitSign b * bitSign a := by
        cases a <;> cases b <;> simp [bitSign] <;> linarith
      refine mul_le_mul_of_nonneg_left ?_ hw
      rw [hP, hQ]
      exact ih _ _ (fun x ↦ hf _) (fun y ↦ hh _)
    have hsum : 𝔼 a, 𝔼 b, (1 + r * bitSign b * bitSign a) * (P a ^ k * Q b ^ k) ≤
        𝔼 a, 𝔼 b, (1 + r * bitSign b * bitSign a) *
          corr r (fun x ↦ f (Fin.cons a x)) (fun y ↦ h (Fin.cons b y)) :=
      Finset.expect_le_expect fun a _ ↦ Finset.expect_le_expect fun b _ ↦ hstep a b
    refine le_trans ?_ hsum
    have hf' : 𝔼 x, f x = (P true + P false) / 2 := by
      rw [expect_cube_succ, expect_bool, hP]
    have hh' : 𝔼 x, h x = (Q true + Q false) / 2 := by
      rw [expect_cube_succ, expect_bool, hQ]
    rw [hf', hh']
    simp only [expect_bool, bitSign, ite_true, Bool.false_eq_true, ite_false]
    have := two_point hk hr0 hr (hP0 true) (hP0 false) (hQ0 true) (hQ0 false)
    have e : ((1 + r * -1 * -1) * (P true ^ k * Q true ^ k) +
        (1 + r * 1 * -1) * (P true ^ k * Q false ^ k)) / 2 / 2 +
      ((1 + r * -1 * 1) * (P false ^ k * Q true ^ k) +
        (1 + r * 1 * 1) * (P false ^ k * Q false ^ k)) / 2 / 2 =
      ((1 + r) * (P true ^ k * Q true ^ k + P false ^ k * Q false ^ k) +
        (1 - r) * (P true ^ k * Q false ^ k + P false ^ k * Q true ^ k)) / 4 := by ring
    linarith

/-! ### Few points where the noisy table is almost one -/

theorem noise_one_sub (r : ℝ) {n : ℕ} (g : Cube (Fin n) → ℝ) (x : Cube (Fin n)) :
    noise r (fun y ↦ 1 - g y) x = 1 - noise r g x := by
  calc noise r (fun y ↦ 1 - g y) x
      = 𝔼 y, (1 - g y) * ∏ i, (1 + r * bitSign (y i) * bitSign (x i)) := noise_kernel _ _ _
    _ = (𝔼 y : Cube (Fin n), ∏ i, (1 + r * bitSign (y i) * bitSign (x i))) -
          𝔼 y, g y * ∏ i, (1 + r * bitSign (y i) * bitSign (x i)) := by
        rw [← Finset.expect_sub_distrib]
        refine Finset.expect_congr rfl fun y _ ↦ ?_
        ring
    _ = 1 - noise r g x := by rw [noise_kernel_mass, noise_kernel]

/-- If `g ∈ [0,1]` has mean `≤ 1/2` and `f ∈ [0,1]` vanishes where `T_r g < 1 - δ`, then
`(E f)^{k-1} ≤ 2ᵏ δ`. -/
theorem few_high {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 - 1 / k) {δ : ℝ}
    (hδ : 0 ≤ δ) {n : ℕ} (g f : Cube (Fin n) → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hmean : 𝔼 x, g x ≤ 1 / 2) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hfA : ∀ x, f x ≠ 0 → 1 - δ ≤ noise r g x) :
    (𝔼 x, f x) ^ (k - 1) ≤ 2 ^ k * δ := by
  have hrev := rev_hc (by omega : 1 ≤ k) hr0 hr n f (fun y ↦ 1 - g y) hf
    (fun x ↦ ⟨by linarith [(hg x).2], by linarith [(hg x).1]⟩)
  rw [corr_eq_noise] at hrev
  simp_rw [noise_one_sub] at hrev
  have hup : 𝔼 x, f x * (1 - noise r g x) ≤ 𝔼 x, f x * δ := by
    refine Finset.expect_le_expect fun x _ ↦ ?_
    by_cases h0 : f x = 0
    · rw [h0]; simp
    · exact mul_le_mul_of_nonneg_left (by linarith [hfA x h0]) (hf x).1
  rw [← Finset.expect_mul] at hup
  have hh : 1 / 2 ≤ 𝔼 x, (1 - g x) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
    linarith
  obtain ⟨α, hα⟩ : ∃ α, α = 𝔼 x, f x := ⟨_, rfl⟩
  rw [← hα] at hrev hup ⊢
  have hα0 : 0 ≤ α := hα ▸ Finset.expect_nonneg fun x _ ↦ (hf x).1
  have hhk : (1 / 2 : ℝ) ^ k ≤ (𝔼 x, (1 - g x)) ^ k := pow_le_pow_left₀ (by norm_num) hh k
  have h1 : α ^ k * (1 / 2) ^ k ≤ α * δ := by
    calc α ^ k * (1 / 2) ^ k ≤ α ^ k * (𝔼 x, (1 - g x)) ^ k :=
          mul_le_mul_of_nonneg_left hhk (pow_nonneg hα0 k)
      _ ≤ α * δ := hrev.trans hup
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega]
  rcases hα0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow (by omega : j + 1 ≠ 0)]
    positivity
  · have h2 : α ^ (j + 2) * (1 / 2) ^ (j + 2) = α * (α ^ (j + 1) * (1 / 2) ^ (j + 2)) := by ring
    rw [h2] at h1
    have h3 : α ^ (j + 1) * (1 / 2) ^ (j + 2) ≤ δ := le_of_mul_le_mul_left h1 hpos
    have h4 : (2 : ℝ) ^ (j + 2) * (1 / 2) ^ (j + 2) = 1 := by
      rw [← mul_pow]; norm_num
    calc α ^ (j + 1) = α ^ (j + 1) * ((2 : ℝ) ^ (j + 2) * (1 / 2) ^ (j + 2)) := by rw [h4, mul_one]
      _ = 2 ^ (j + 2) * (α ^ (j + 1) * (1 / 2) ^ (j + 2)) := by ring
      _ ≤ 2 ^ (j + 2) * δ := by gcongr

end BHSV25.BK.Aint
