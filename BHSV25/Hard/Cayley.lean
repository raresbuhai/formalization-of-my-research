module

public import BHSV25.Hard.Blowup

/-!
# Explicit pseudo-random sets of every dyadic density

The reductions need dense bipartite graphs between parts of prescribed sizes, with prescribed
dyadic densities, that look random to every pair of vectors. They are Cayley sum graphs on
`Γ = Γ₀^r`, `Γ₀ = 𝔽₂ × 𝔽₂^a × 𝔽₂^a`: `x ~ y` when `x + y ∈ S`.

* **The bent function** `b(w) = w₀ + ⟨w₁, w₂⟩` on `Γ₀` (`BHSV25.Hard.Cayley.bent`) is balanced,
  and the `±1` matrix `K_xy = (-1)^{b(x+y)}` has `K² = |Γ₀| (I - P)` with `P` the translation by
  `(1, 0, 0)`, since `b(w) + b(w + u)` is affine in `w` with linear part `⟨w₁, u₂⟩ + ⟨u₁, w₂⟩`.
  So `|Xᵀ K Y| ≤ 2^a (‖X‖² + ‖Y‖²)` (`BHSV25.Hard.Cayley.abs_bil_sgn_le`).
* **Pseudo-randomness** (`BHSV25.Hard.Cayley.PR`): `S` is `(ρ, e)`-pseudo-random when
  `|∑_{x,y} X_x [x + y ∈ S] Y_y - ρ (∑ X)(∑ Y)| ≤ e (‖X‖² + ‖Y‖²)` for all `X, Y`.
* **Dyadic densities**: reading `(b(z₀), …, b(z_{r-1}))` as a binary number `hval z`, the set
  `{z : hval z < q}` has exactly `q (|Γ₀| / 2)^r` elements (`BHSV25.Hard.Cayley.card_lt`) and is
  `(q / 2^r, 4^r 2^a |Γ₀|^(r-1))`-pseudo-random for `q ≤ 2^r` (`BHSV25.Hard.Cayley.pr_lt`), by
  induction on `r`: it is the disjoint union of `{b(z₀) = 0} × {hval < ⌈q/2⌉}` and
  `{b(z₀) = 1} × {hval < ⌊q/2⌋}`, and products of pseudo-random sets are pseudo-random.
-/

@[expose] public section

namespace BHSV25.Hard.Cayley

open Finset

/-! ### Signs on `𝔽₂` -/

/-- The sign `(-1)^z` of an element of `𝔽₂`. -/
def sgn (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

theorem add_self_zmod2 (z : ZMod 2) : z + z = 0 := by
  rcases zmod2_cases z with rfl | rfl
  · simp
  · exact one_add_one_zmod2

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn]

theorem sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [sgn_zero, sgn_one, one_add_one_zmod2]

theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> simp [sgn_zero, sgn_one]

theorem sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, sgn_add, ih]

theorem sum_zmod2 (f : ZMod 2 → ℝ) : ∑ x : ZMod 2, f x = f 0 + f 1 := by
  rw [show (univ : Finset (ZMod 2)) = {0, 1} by decide, sum_pair (by decide)]

theorem sum_sgn_mul (c : ZMod 2) : ∑ x : ZMod 2, sgn (c * x) = if c = 0 then 2 else 0 := by
  rw [sum_zmod2]
  rcases zmod2_cases c with rfl | rfl
  · simp [sgn_zero]; norm_num
  · simp [sgn_zero, sgn_one]

theorem sum_sgn_dot {a : ℕ} (c : Fin a → ZMod 2) :
    ∑ w : Fin a → ZMod 2, sgn (∑ i, c i * w i) = if c = 0 then 2 ^ a else 0 := by
  classical
  simp_rw [sgn_sum]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ ↦ univ) (fun i x ↦ sgn (c i * x))]
  simp_rw [sum_sgn_mul]
  split_ifs with hc
  · simp [hc]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hc (funext h)
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-! ### The bent function -/

/-- The group `Γ₀ = 𝔽₂ × 𝔽₂^a × 𝔽₂^a`. -/
abbrev Gam0 (a : ℕ) := ZMod 2 × (Fin a → ZMod 2) × (Fin a → ZMod 2)

/-- The balanced bent function `b(w) = w₀ + ⟨w₁, w₂⟩`. -/
def bent {a : ℕ} (w : Gam0 a) : ZMod 2 := w.1 + ∑ i, w.2.1 i * w.2.2 i

theorem card_gam0 (a : ℕ) : Fintype.card (Gam0 a) = 2 * 4 ^ a := by
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_pi, prod_const, card_univ,
    Fintype.card_fin]
  rw [← mul_pow]
  norm_num

theorem sum_gam0 {a : ℕ} (f : Gam0 a → ℝ) :
    ∑ w, f w = ∑ w₀ : ZMod 2, ∑ w₁ : Fin a → ZMod 2, ∑ w₂ : Fin a → ZMod 2, f (w₀, w₁, w₂) := by
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun _ _ ↦ Fintype.sum_prod_type _

theorem bent_add_bent {a : ℕ} (w u : Gam0 a) :
    bent w + bent (w + u) = (u.1 + ∑ i, u.2.1 i * u.2.2 i) + ∑ i, u.2.2 i * w.2.1 i +
      ∑ i, u.2.1 i * w.2.2 i := by
  unfold bent
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have hs : ∑ i, (w.2.1 i + u.2.1 i) * (w.2.2 i + u.2.2 i) = ∑ i, w.2.1 i * w.2.2 i +
      ∑ i, (u.2.1 i * u.2.2 i + u.2.2 i * w.2.1 i + u.2.1 i * w.2.2 i) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun i _ ↦ by ring
  rw [hs, sum_add_distrib, sum_add_distrib]
  have h1 := add_self_zmod2 w.1
  have h2 := add_self_zmod2 (∑ i, w.2.1 i * w.2.2 i)
  linear_combination h1 + h2

/-- The autocorrelation of the signs of the bent function. -/
theorem sum_sgn_bent_mul {a : ℕ} (u : Gam0 a) :
    ∑ w, sgn (bent w) * sgn (bent (w + u)) =
      if u.2.1 = 0 ∧ u.2.2 = 0 then 2 * 4 ^ a * sgn u.1 else 0 := by
  have hpt : ∀ w : Gam0 a, sgn (bent w) * sgn (bent (w + u)) =
      sgn (u.1 + ∑ i, u.2.1 i * u.2.2 i) *
        (sgn (∑ i, u.2.2 i * w.2.1 i) * sgn (∑ i, u.2.1 i * w.2.2 i)) := by
    intro w; rw [← sgn_add, bent_add_bent, sgn_add, sgn_add, mul_assoc]
  simp_rw [hpt]
  rw [← mul_sum, sum_gam0]
  have hin : ∀ w₀ : ZMod 2, ∑ w₁ : Fin a → ZMod 2, ∑ w₂ : Fin a → ZMod 2,
      sgn (∑ i, u.2.2 i * w₁ i) * sgn (∑ i, u.2.1 i * w₂ i) =
      (if u.2.2 = 0 then (2 : ℝ) ^ a else 0) * (if u.2.1 = 0 then (2 : ℝ) ^ a else 0) := by
    intro w₀
    simp_rw [← mul_sum]
    rw [← sum_mul, sum_sgn_dot, sum_sgn_dot]
  rw [show (∑ w₀ : ZMod 2, ∑ w₁ : Fin a → ZMod 2, ∑ w₂ : Fin a → ZMod 2,
      sgn (∑ i, u.2.2 i * (w₀, w₁, w₂).2.1 i) * sgn (∑ i, u.2.1 i * (w₀, w₁, w₂).2.2 i)) =
      ∑ _w₀ : ZMod 2, (if u.2.2 = 0 then (2 : ℝ) ^ a else 0) *
        (if u.2.1 = 0 then (2 : ℝ) ^ a else 0) from sum_congr rfl fun w₀ _ ↦ hin w₀]
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have h4 : (4 : ℝ) ^ a = 2 ^ a * 2 ^ a := by rw [← mul_pow]; norm_num
  by_cases h1 : u.2.1 = 0 <;> by_cases h2 : u.2.2 = 0
  · simp only [h1, h2, Pi.zero_apply, mul_zero, sum_const_zero, add_zero, and_self, ite_true]
    rw [h4]; push_cast; ring
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- The translation by `(1, 0, 0)`. -/
def e0 (a : ℕ) : Gam0 a := (1, 0, 0)

/-- `K Y` for the sign matrix `K_xy = (-1)^{b(x+y)}`. -/
noncomputable def kmul {a : ℕ} (Y : Gam0 a → ℝ) (x : Gam0 a) : ℝ :=
  ∑ y, sgn (bent (x + y)) * Y y

theorem sum_sgn_shift {a : ℕ} (Y : Gam0 a → ℝ) (y : Gam0 a) :
    ∑ y', Y y' * (if (y' - y).2.1 = 0 ∧ (y' - y).2.2 = 0 then 2 * 4 ^ a * sgn (y' - y).1
      else 0) = 2 * 4 ^ a * (Y y - Y (y + e0 a)) := by
  rw [← Fintype.sum_equiv (Equiv.addLeft y) (fun v ↦ Y (y + v) * (if v.2.1 = 0 ∧ v.2.2 = 0 then
    2 * 4 ^ a * sgn v.1 else 0)) _ (fun v ↦ by simp)]
  rw [sum_gam0]
  simp only [mul_ite, mul_zero]
  have : ∀ v₀ : ZMod 2, (∑ v₁ : Fin a → ZMod 2, ∑ v₂ : Fin a → ZMod 2,
      if v₁ = 0 ∧ v₂ = 0 then Y (y + (v₀, v₁, v₂)) * (2 * 4 ^ a * sgn v₀) else 0) =
      Y (y + (v₀, 0, 0)) * (2 * 4 ^ a * sgn v₀) := by
    intro v₀
    rw [Fintype.sum_eq_single 0 (fun v₁ hv₁ ↦ by simp [hv₁])]
    rw [Fintype.sum_eq_single 0 (fun v₂ hv₂ ↦ by simp [hv₂])]
    simp
  simp_rw [this]
  rw [sum_zmod2, sgn_zero, sgn_one]
  simp only [e0]
  have : (y + ((0 : ZMod 2), (0 : Fin a → ZMod 2), (0 : Fin a → ZMod 2))) = y := by
    rw [show ((0 : ZMod 2), (0 : Fin a → ZMod 2), (0 : Fin a → ZMod 2)) = 0 from rfl, add_zero]
  rw [this]
  ring

theorem sum_kmul_sq_le {a : ℕ} (Y : Gam0 a → ℝ) :
    ∑ x, kmul Y x ^ 2 ≤ 4 ^ (a + 1) * ∑ y, Y y ^ 2 := by
  have hR : ∀ y y' : Gam0 a, ∑ x, sgn (bent (x + y)) * sgn (bent (x + y')) =
      if (y' - y).2.1 = 0 ∧ (y' - y).2.2 = 0 then 2 * 4 ^ a * sgn (y' - y).1 else 0 := by
    intro y y'
    rw [← sum_sgn_bent_mul]
    exact Fintype.sum_equiv (Equiv.addRight y) _ _ (fun x ↦ by
      rw [Equiv.coe_addRight, show x + y + (y' - y) = x + y' by abel])
  have hexp : ∑ x, kmul Y x ^ 2 = ∑ y, Y y * (2 * 4 ^ a * (Y y - Y (y + e0 a))) := by
    have hsq : ∀ x, kmul Y x ^ 2 = ∑ y, ∑ y', Y y * Y y' *
        (sgn (bent (x + y)) * sgn (bent (x + y'))) := by
      intro x
      rw [sq, kmul, sum_mul_sum]
      exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
    simp_rw [hsq]
    rw [sum_comm]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [sum_comm]
    simp_rw [← mul_sum, hR]
    rw [← sum_sgn_shift Y y, mul_sum]
    exact sum_congr rfl fun y' _ ↦ by ring
  rw [hexp]
  have htr : ∑ y, Y (y + e0 a) ^ 2 = ∑ y, Y y ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (e0 a)) _ _ (fun _ ↦ rfl)
  have hpt : ∀ y, Y y * (2 * 4 ^ a * (Y y - Y (y + e0 a))) ≤
      2 * 4 ^ a * (Y y ^ 2 + (Y y ^ 2 + Y (y + e0 a) ^ 2) / 2) := by
    intro y
    have h4 : (0 : ℝ) ≤ 2 * 4 ^ a := by positivity
    have : -(Y y * Y (y + e0 a)) ≤ (Y y ^ 2 + Y (y + e0 a) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Y y + Y (y + e0 a))]
    nlinarith
  calc _ ≤ ∑ y, 2 * 4 ^ a * (Y y ^ 2 + (Y y ^ 2 + Y (y + e0 a) ^ 2) / 2) :=
        sum_le_sum fun y _ ↦ hpt y
    _ = 2 * 4 ^ a * (2 * ∑ y, Y y ^ 2) := by
        rw [← mul_sum]
        congr 1
        rw [sum_add_distrib, ← sum_div, sum_add_distrib, htr]
        ring
    _ = 4 ^ (a + 1) * ∑ y, Y y ^ 2 := by rw [pow_succ]; ring

/-- **The sign matrix of the bent function is small**: `|Xᵀ K Y| ≤ 2^a (‖X‖² + ‖Y‖²)`. -/
theorem abs_bil_sgn_le {a : ℕ} (X Y : Gam0 a → ℝ) :
    |∑ x, ∑ y, X x * sgn (bent (x + y)) * Y y| ≤ 2 ^ a * (∑ x, X x ^ 2 + ∑ y, Y y ^ 2) := by
  have hrw : ∑ x, ∑ y, X x * sgn (bent (x + y)) * Y y = ∑ x, X x * kmul Y x := by
    simp only [kmul, mul_sum]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  rw [hrw]
  have ht : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  have hpt : ∀ x, |X x * kmul Y x| ≤ (2 ^ (a + 1) * X x ^ 2 + kmul Y x ^ 2 / 2 ^ (a + 1)) / 2 := by
    intro x
    rw [abs_mul]
    set t : ℝ := 2 ^ (a + 1) with ht_def
    set A := |X x|
    set B := |kmul Y x|
    have hA : X x ^ 2 = A ^ 2 := (sq_abs _).symm
    have hB : kmul Y x ^ 2 = B ^ 2 := (sq_abs _).symm
    rw [hA, hB]
    have h := sq_nonneg (t * A - B)
    rw [le_div_iff₀ two_pos]
    calc A * B * 2 = (2 * t * (A * B)) / t := by field_simp
      _ ≤ (t ^ 2 * A ^ 2 + B ^ 2) / t := by gcongr; nlinarith [h]
      _ = t * A ^ 2 + B ^ 2 / t := by field_simp
  have hK := sum_kmul_sq_le Y
  calc |∑ x, X x * kmul Y x| ≤ ∑ x, |X x * kmul Y x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (2 ^ (a + 1) * X x ^ 2 + kmul Y x ^ 2 / 2 ^ (a + 1)) / 2 := sum_le_sum fun x _ ↦ hpt x
    _ = (2 ^ (a + 1) * ∑ x, X x ^ 2 + (∑ x, kmul Y x ^ 2) / 2 ^ (a + 1)) / 2 := by
        rw [← sum_div, sum_add_distrib, ← mul_sum, ← sum_div]
    _ ≤ (2 ^ (a + 1) * ∑ x, X x ^ 2 + (4 ^ (a + 1) * ∑ y, Y y ^ 2) / 2 ^ (a + 1)) / 2 := by
        gcongr
    _ = 2 ^ a * (∑ x, X x ^ 2 + ∑ y, Y y ^ 2) := by
        have : (4 : ℝ) ^ (a + 1) = 2 ^ (a + 1) * 2 ^ (a + 1) := by rw [← mul_pow]; norm_num
        rw [this, mul_assoc, mul_div_cancel_left₀ _ ht.ne', pow_succ]
        ring

end BHSV25.Hard.Cayley
