module

public import BMW26.Spec.Defs

/-!
# Spectral concentration on low-degree functions

[BMW26, Lemmas 5.6 and 5.8], with second moments and Markov's inequality in place of the matrix
Bernstein inequality: the space of functions of degree at most `r = m / 100` has dimension
`k ≤ 17^m / 16^(m - r)` (`BMW26.LowDeg.card_lowSets_mul_le`), so `C k² mⁿ ≤ 2^m` for large `m`
(`BMW26.LowDeg.eventually_bound`). The failure probabilities are `poly(m) k² / 2^m`, so they are at
most `1/m^q` for any `q` (`BMW26.lowRel_whp_pow`, `BMW26.lowSq_whp_pow`); `BMW26.lowRel_whp` and
`BMW26.lowSq_whp` are the case `q = 3`.

Write `h = lowProj r g = ∑_{|S| ≤ r} ĝ(S) χ_S`. Then `h x - h (flip x i) = ∑_S ĝ(S) dχ_S(i, x)`
with `dχ_S(i, x) = 2 χ_S(x) [i ∈ S]`, and `energy 1 h = 2^m ∑_S 2 |S| ĝ(S)²`. Both lemmas reduce
to a matrix `b_{ST}` (vanishing when `S = ∅` or `T = ∅`) with
`(∑_{S,T} ĝ(S) ĝ(T) b_{ST})² ≤ (energy 1 h)² ∑_{S,T} b_{ST}² / (4 |S| |T| 4^m)` (Cauchy–Schwarz,
`BMW26.LowDeg.sq_sum_le_energy`): the second factor is the squared Frobenius norm of the matrix in
the basis `y_S = ĝ(S) √(2 |S| 2^m)`.

* `BMW26.lowRel_whp`: `energy w h - p energy 1 h = ∑_{S,T} ĝ(S) ĝ(T) c_{ST}` where
  `c_{ST} = ∑_{i, xᵢ = false} (w i x - p) dχ_S(i, x) dχ_T(i, x)` is a linear form in the centred
  coins with `E c_{ST}² ≤ 16 m 2^m`. So the Frobenius norm `Φ` has `E Φ ≤ 4 k² m / 2^m`, and
  `Φ ≤ γ² p²` with probability at least `1 - 1/m³` by Markov.
* `BMW26.lowSq_whp`: `∑ₓ ((L_w - pL) h)(x)² = ∑_{S,T} ĝ(S) ĝ(T) G_{ST}` with
  `G_{ST} = ∑ₓ B_S(x) B_T(x)`, `B_S(x) = ∑ᵢ dχ_S(i, x) (w i (lowPt x i) - p)`, and
  `E G_{ST} = 4 p (1 - p) |S| 2^m [S = T]`, whose part of the form is `2 p (1 - p) energy 1 h`. The
  centred summands of `G_{ST}` are bounded by `4m² + 4m`, and those at non-adjacent vertices
  depend on disjoint coins, hence are uncorrelated; so `E (G_{ST} - E G_{ST})² ≤
  2^m (m + 1) (4m² + 4m)²`, and the Frobenius norm `Ψ` of the centred matrix is at most `4p²` with
  probability at least `1 - 1/m³`. Then the form is at most `2p E + 2p E = 4p E`.
-/

@[expose] public section

namespace BMW26

open MeasureTheory Finset

namespace LowDeg

/-- The sets of size at most `r`: the characters of the low-degree space. -/
def lowSets (m r : ℕ) : Finset (Finset (Fin m)) := univ.filter fun S ↦ S.card ≤ r

theorem card_lowSets_mul_le (m r : ℕ) : 16 ^ (m - r) * (lowSets m r).card ≤ 17 ^ m := by
  have h := Finset.sum_pow_mul_eq_add_pow (1 : ℕ) 16 (univ : Finset (Fin m))
  simp only [one_pow, one_mul, Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  calc 16 ^ (m - r) * (lowSets m r).card = ∑ t ∈ lowSets m r, 16 ^ (m - r) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ t ∈ lowSets m r, 16 ^ (m - t.card) := by
        refine Finset.sum_le_sum fun t ht ↦ Nat.pow_le_pow_right (by norm_num) ?_
        have := (Finset.mem_filter.1 ht).2
        omega
    _ ≤ ∑ t : Finset (Fin m), 16 ^ (m - t.card) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 17 ^ m := by rw [h]

/-- The low-degree space is small: `C k² mⁿ ≤ 2^m` for large `m`, where `k` is the number of sets
of size at most `m / 100`. -/
theorem eventually_bound (C : ℝ) (n : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, C * ((lowSets m (m / 100)).card : ℝ) ^ 2 * (m : ℝ) ^ n ≤ 2 ^ m := by
  set D : ℝ := |C| * 200 ^ n + 1 with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 <|
    (tendsto_pow_const_div_const_pow_of_one_lt n (r := (2 : ℝ) ^ 42) (by norm_num)).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / D))
  refine ⟨100 * (R + 1), fun m hm ↦ ?_⟩
  obtain ⟨r, s, hs, rfl⟩ : ∃ r s, s < 100 ∧ m = 100 * r + s :=
    ⟨m / 100, m % 100, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 100).symm⟩
  have hr : (100 * r + s) / 100 = r := by omega
  have hr0 : R + 1 ≤ r := by omega
  rw [hr]
  set k := (lowSets (100 * r + s) r).card
  set y : ℝ := 2 ^ r with hy
  set z : ℝ := 2 ^ s with hz
  have hy0 : 0 < y := by positivity
  have hz0 : 0 < z := by positivity
  have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have h1 : (k : ℝ) * (y ^ 396 * z ^ 4) ≤ 17 ^ (100 * r + s) := by
    have h := card_lowSets_mul_le (100 * r + s) r
    rw [show 100 * r + s - r = 99 * r + s by omega] at h
    have h' : ((16 ^ (99 * r + s) * k : ℕ) : ℝ) ≤ ((17 ^ (100 * r + s) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    have e : (16 : ℝ) ^ (99 * r + s) = y ^ 396 * z ^ 4 := by
      rw [hy, hz, ← pow_mul, ← pow_mul, ← pow_add, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
      congr 1
      ring
    rw [e] at h'
    linarith
  have h2 : ((17 : ℝ) ^ (100 * r + s)) ^ 2 ≤ y ^ 850 * z ^ 9 := by
    have e : ((17 : ℝ) ^ (100 * r + s)) ^ 2 = ((17 : ℝ) ^ 4) ^ (50 * r) * ((17 : ℝ) ^ 2) ^ s := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    have e' : y ^ 850 * z ^ 9 = ((2 : ℝ) ^ 17) ^ (50 * r) * ((2 : ℝ) ^ 9) ^ s := by
      rw [hy, hz, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    rw [e, e']
    gcongr <;> norm_num
  have h3 : C * ((100 * r + s : ℕ) : ℝ) ^ n ≤ y ^ 42 := by
    have hR' : (r : ℝ) ^ n * D < 1 * ((2 : ℝ) ^ 42) ^ r := by
      have := hR r (by omega)
      rwa [div_lt_div_iff₀ (by positivity) hD0] at this
    have e : ((2 : ℝ) ^ 42) ^ r = y ^ 42 := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
    have hm : ((100 * r + s : ℕ) : ℝ) ≤ 200 * r := by
      push_cast
      have : (s : ℝ) ≤ 99 := by exact_mod_cast (by omega : s ≤ 99)
      have : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
      linarith
    have hrn : (0 : ℝ) ≤ (r : ℝ) ^ n := by positivity
    calc C * ((100 * r + s : ℕ) : ℝ) ^ n ≤ |C| * ((100 * r + s : ℕ) : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (200 * r) ^ n := by gcongr
      _ = |C| * 200 ^ n * (r : ℝ) ^ n := by ring
      _ ≤ (r : ℝ) ^ n * D := by rw [hD]; nlinarith
      _ ≤ y ^ 42 := by rw [← e]; linarith
  have h4 : ((k : ℝ) * (y ^ 396 * z ^ 4)) ^ 2 ≤ y ^ 850 * z ^ 9 :=
    le_trans (pow_le_pow_left₀ (by positivity) h1 2) h2
  have h5 : C * (k : ℝ) ^ 2 * ((100 * r + s : ℕ) : ℝ) ^ n * (y ^ 792 * z ^ 8) ≤
      y ^ 100 * z * (y ^ 792 * z ^ 8) := by
    calc C * (k : ℝ) ^ 2 * ((100 * r + s : ℕ) : ℝ) ^ n * (y ^ 792 * z ^ 8)
        = (C * ((100 * r + s : ℕ) : ℝ) ^ n) * ((k : ℝ) * (y ^ 396 * z ^ 4)) ^ 2 := by ring
      _ ≤ y ^ 42 * (y ^ 850 * z ^ 9) := mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = y ^ 100 * z * (y ^ 792 * z ^ 8) := by ring
  have e2 : (2 : ℝ) ^ (100 * r + s) = y ^ 100 * z := by
    rw [hy, hz, ← pow_mul, ← pow_add, mul_comm r]
  rw [e2]
  exact le_of_mul_le_mul_right h5 (by positivity)

/-- **Weighted Cauchy–Schwarz**: `(∑ aᵢ bᵢ)² ≤ (∑ lᵢ aᵢ²) (∑ bᵢ² / lᵢ)` for nonnegative weights
`lᵢ`, provided `bᵢ = 0` where `lᵢ = 0`. -/
theorem sq_sum_mul_le {α : Type*} (s : Finset α) (a b l : α → ℝ) (hl : ∀ i ∈ s, 0 ≤ l i)
    (hb : ∀ i ∈ s, l i = 0 → b i = 0) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, l i * a i ^ 2) * ∑ i ∈ s, b i ^ 2 / l i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ Real.sqrt (l i) * a i)
    (fun i ↦ b i / Real.sqrt (l i))
  have e1 : ∑ i ∈ s, a i * b i = ∑ i ∈ s, Real.sqrt (l i) * a i * (b i / Real.sqrt (l i)) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rcases (hl i hi).eq_or_lt with h0 | hpos
    · rw [hb i hi h0.symm]; simp
    · have : Real.sqrt (l i) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      field_simp
  have e2 : ∀ i ∈ s, (Real.sqrt (l i) * a i) ^ 2 = l i * a i ^ 2 := fun i hi ↦ by
    rw [mul_pow, Real.sq_sqrt (hl i hi)]
  have e3 : ∀ i ∈ s, (b i / Real.sqrt (l i)) ^ 2 = b i ^ 2 / l i := fun i hi ↦ by
    rw [div_pow, Real.sq_sqrt (hl i hi)]
  rw [e1, ← Finset.sum_congr rfl e2, ← Finset.sum_congr rfl e3]
  exact h

/-- Functions of finitely many coins are integrable. -/
theorem integrable_coins {ι : Type*} [Finite ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : ι → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (F : (ι → Bool) → ℝ) :
    Integrable (fun ω ↦ F (fun i ↦ a i ω)) μ := by
  have := ha.isProb
  have hmeas : Measurable (fun ω ↦ fun i ↦ a i ω) := measurable_pi_iff.2 ha.meas
  exact (Integrable.of_finite (μ := μ.map (fun ω ↦ fun i ↦ a i ω)) (f := F)).comp_measurable hmeas


theorem sum_comm3 {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (F : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, F a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm

variable {m : ℕ}

/-- `χ_S(x) - χ_S(flip x i)`: `2 χ_S(x)` if `i ∈ S`, `0` otherwise. -/
noncomputable def dchi (i : Fin m) (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  if i ∈ S then 2 * chi S x else 0

theorem abs_dchi_le (i : Fin m) (S : Finset (Fin m)) (x : Cube m) : |dchi i S x| ≤ 2 := by
  unfold dchi
  split_ifs
  · have h := chi_sq S x
    have : |chi S x| = 1 := by
      have := abs_le_of_sq_le_sq (a := chi S x) (b := 1) (by rw [h]; norm_num) (by norm_num)
      nlinarith [abs_nonneg (chi S x), sq_abs (chi S x)]
    rw [abs_mul, this]; norm_num
  · simp

theorem dchi_empty (i : Fin m) (x : Cube m) : dchi i ∅ x = 0 := by simp [dchi]

theorem lowProj_sub_flip (r : ℕ) (g : Cube m → ℝ) (x : Cube m) (i : Fin m) :
    lowProj r g x - lowProj r g (flip x i) = ∑ S ∈ lowSets m r, fourier g S * dchi i S x := by
  unfold lowProj
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [chi_flip, dchi]
  split_ifs <;> ring

theorem energy_one_lowProj (r : ℕ) (g : Cube m → ℝ) :
    energy 1 (lowProj r g) = 2 ^ m * ∑ S ∈ lowSets m r, 2 * (S.card : ℝ) * fourier g S ^ 2 := by
  rw [energy_one_eq, lowSets, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [fourier_lowProj]
  split_ifs <;> simp

/-- Cauchy–Schwarz in the basis `y_S = ĝ(S) √(2 |S| 2^m)` of the low-degree space. -/
theorem sq_sum_le_energy (r : ℕ) (g : Cube m → ℝ) (b : Finset (Fin m) → Finset (Fin m) → ℝ)
    (hb : ∀ T, b ∅ T = 0) (hb' : ∀ S, b S ∅ = 0) :
    (∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * b S T) ^ 2 ≤
      energy 1 (lowProj r g) ^ 2 *
        ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, b S T ^ 2 / (4 * S.card * T.card * 4 ^ m) := by
  have h := sq_sum_mul_le (lowSets m r ×ˢ lowSets m r) (fun q ↦ fourier g q.1 * fourier g q.2)
    (fun q ↦ b q.1 q.2) (fun q ↦ 4 * q.1.card * q.2.card * 4 ^ m) (fun q _ ↦ by positivity)
    (by
      rintro ⟨S, T⟩ _ h0
      simp only [mul_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero, pow_eq_zero_iff',
        OfNat.ofNat_ne_zero, false_or, ne_eq, false_and, or_false] at h0
      rcases h0 with rfl | rfl
      · exact hb T
      · exact hb' S)
  have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  calc (∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * b S T) ^ 2
      = (∑ q ∈ lowSets m r ×ˢ lowSets m r, fourier g q.1 * fourier g q.2 * b q.1 q.2) ^ 2 := by
        rw [Finset.sum_product]
    _ ≤ _ := h
    _ = _ := by
        rw [Finset.sum_product, Finset.sum_product]
        congr 1
        rw [energy_one_lowProj, sq, Finset.mul_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun T _ ↦ ?_
        rw [h4]
        ring

/-! ### Lemma 5.6: the quadratic form -/

/-- The coefficient of the coin `(i, x)` in `χ_Sᵀ (L_w - p L) χ_T`. -/
noncomputable def coefR (S T : Finset (Fin m)) (j : Fin m × Cube m) : ℝ :=
  if j.2 j.1 = false then dchi j.1 S j.2 * dchi j.1 T j.2 else 0

/-- `χ_Sᵀ (L_w - p L) χ_T`, a linear form in the centred weights. -/
noncomputable def cR (w : Fin m → Cube m → ℝ) (p : ℝ) (S T : Finset (Fin m)) : ℝ :=
  ∑ j, coefR S T j * (w j.1 j.2 - p)

/-- The squared Frobenius norm of the normalized matrix `N_{ST}`. -/
noncomputable def phiR (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, cR w p S T ^ 2 / (4 * S.card * T.card * 4 ^ m)

theorem energy_lowProj_eq (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) (g : Cube m → ℝ) :
    energy (fun i y ↦ w i y - p) (lowProj r g) =
      ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * cR w p S T := by
  symm
  calc ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * cR w p S T
      = ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, ∑ i, ∑ x,
          fourier g S * fourier g T * (coefR S T (i, x) * (w i x - p)) := by
        simp only [cR, Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ i, ∑ x, ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
          fourier g S * fourier g T * (coefR S T (i, x) * (w i x - p)) :=
        (Finset.sum_congr rfl fun S _ ↦ sum_comm3 _ _ _ _).trans (sum_comm3 _ _ _ _)
    _ = ∑ i, ∑ x, if x i = false then
          (w i x - p) * (∑ S ∈ lowSets m r, fourier g S * dchi i S x) ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
        split_ifs with hx
        · simp only [coefR, hx, ↓reduceIte]
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ ↦ by ring
        · simp [coefR, hx]
    _ = _ := by
        unfold energy
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [lowProj_sub_flip]

theorem lowRel_of_phiR {w : Fin m → Cube m → ℝ} {p γ : ℝ} {r : ℕ} (hγ : 0 ≤ γ) (hp : 0 ≤ p)
    (h : phiR w p r ≤ γ ^ 2 * p ^ 2) : LowRel w p γ r := by
  intro g
  rw [← energy_sub_const, energy_lowProj_eq]
  have hE : 0 ≤ energy 1 (lowProj r g) := energy_nonneg (fun _ _ ↦ zero_le_one) _
  have hcs := sq_sum_le_energy r g (cR w p) (fun T ↦ by simp [cR, coefR, dchi])
    (fun S ↦ by simp [cR, coefR, dchi])
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ ≤ _ := hcs
    _ ≤ energy 1 (lowProj r g) ^ 2 * (γ ^ 2 * p ^ 2) := by gcongr; exact h
    _ = (γ * p * energy 1 (lowProj r g)) ^ 2 := by ring

/-! ### Lemma 5.8: the squared error -/

/-- The `S`-coordinate of `(L_w - p L)` at `x`: `(L_w - pL) χ_S (x) = bS w p S x`. -/
noncomputable def bS (w : Fin m → Cube m → ℝ) (p : ℝ) (S : Finset (Fin m)) (x : Cube m) : ℝ :=
  ∑ i, dchi i S x * (w i (lowPt x i) - p)

/-- The Gram matrix `(AᵀA)_{ST}`. -/
noncomputable def gS (w : Fin m → Cube m → ℝ) (p : ℝ) (S T : Finset (Fin m)) : ℝ :=
  ∑ x, bS w p S x * bS w p T x

/-- The expectation of `gS` for coin weights. -/
noncomputable def eS (p : ℝ) (S T : Finset (Fin m)) : ℝ :=
  if S = T then 4 * p * (1 - p) * S.card * 2 ^ m else 0

/-- The squared Frobenius norm of the normalized deviation of `AᵀA`. -/
noncomputable def psiS (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
    (gS w p S T - eS p S T) ^ 2 / (4 * S.card * T.card * 4 ^ m)

theorem lap_lowProj_eq (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) (g : Cube m → ℝ) (x : Cube m) :
    lap (fun i y ↦ w i y - p) (lowProj r g) x = ∑ S ∈ lowSets m r, fourier g S * bS w p S x := by
  unfold lap bS
  simp_rw [lowProj_sub_flip, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

theorem sum_lap_sq_eq (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) (g : Cube m → ℝ) :
    ∑ x, lap (fun i y ↦ w i y - p) (lowProj r g) x ^ 2 =
      ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * gS w p S T := by
  simp_rw [lap_lowProj_eq, sq, Finset.sum_mul_sum]
  unfold gS
  simp_rw [Finset.mul_sum]
  rw [sum_comm3]
  exact Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun T _ ↦
    Finset.sum_congr rfl fun x _ ↦ by ring

theorem sum_eS (p : ℝ) (r : ℕ) (g : Cube m → ℝ) :
    ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * eS p S T =
      2 * p * (1 - p) * energy 1 (lowProj r g) := by
  rw [energy_one_lowProj]
  simp only [eS, mul_ite, mul_zero]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  rw [Finset.sum_ite_eq]
  simp only [hS, ↓reduceIte]
  ring

theorem lowSq_of_psiS {w : Fin m → Cube m → ℝ} {p : ℝ} {r : ℕ} (hp : 0 ≤ p)
    (h : psiS w p r ≤ 4 * p ^ 2) : LowSq w p r := by
  intro g
  rw [sum_lap_sq_eq]
  have hE : 0 ≤ energy 1 (lowProj r g) := energy_nonneg (fun _ _ ↦ zero_le_one) _
  have hsplit : ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * gS w p S T =
      ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, fourier g S * fourier g T * eS p S T +
      ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
        fourier g S * fourier g T * (gS w p S T - eS p S T) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T _ ↦ by ring
  have hcs := sq_sum_le_energy r g (fun S T ↦ gS w p S T - eS p S T)
    (fun T ↦ by simp [gS, bS, dchi, eS])
    (fun S ↦ by by_cases hS : S = ∅ <;> simp [gS, bS, dchi, eS, hS])
  have hdev : ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
      fourier g S * fourier g T * (gS w p S T - eS p S T) ≤ 2 * p * energy 1 (lowProj r g) := by
    refine le_trans (le_abs_self _) (abs_le_of_sq_le_sq ?_ (by positivity))
    calc _ ≤ _ := hcs
      _ ≤ energy 1 (lowProj r g) ^ 2 * (4 * p ^ 2) := by gcongr; exact h
      _ = (2 * p * energy 1 (lowProj r g)) ^ 2 := by ring
  rw [hsplit, sum_eS]
  nlinarith [mul_nonneg (mul_nonneg hp hp) hE]

/-! ### Probability -/

/-- The edge weights given by a configuration `v` of the coins. -/
def wv (v : Fin m × Cube m → Bool) (i : Fin m) (x : Cube m) : ℝ := bit (v (i, x))

theorem abs_bit_sub_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : |bit b - p| ≤ 1 := by
  cases b <;> simp only [bit, Bool.false_eq_true, ↓reduceIte] <;> rw [abs_le] <;>
    constructor <;> linarith

theorem dchi_sq_le (i : Fin m) (S : Finset (Fin m)) (x : Cube m) : dchi i S x ^ 2 ≤ 4 := by
  have := abs_dchi_le i S x
  nlinarith [sq_abs (dchi i S x), abs_nonneg (dchi i S x)]

theorem coefR_sq_le (S T : Finset (Fin m)) (j : Fin m × Cube m) : coefR S T j ^ 2 ≤ 16 := by
  unfold coefR
  split_ifs
  · rw [mul_pow]
    have h1 := dchi_sq_le j.1 S j.2
    have h2 := dchi_sq_le j.1 T j.2
    nlinarith [sq_nonneg (dchi j.1 S j.2), sq_nonneg (dchi j.1 T j.2)]
  · norm_num

theorem phiR_nonneg (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) : 0 ≤ phiR w p r :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)

theorem psiS_nonneg (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) : 0 ≤ psiS w p r :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)

theorem div_le_div_card {X : ℝ} (hX : 0 ≤ X) (S T : Finset (Fin m)) :
    X / (4 * S.card * T.card * 4 ^ m) ≤ X / (4 * 4 ^ m) := by
  rcases Nat.eq_zero_or_pos (S.card * T.card) with h | h
  · have h' : (S.card : ℝ) * T.card = 0 := by exact_mod_cast h
    have : (4 * (S.card : ℝ) * T.card * 4 ^ m) = 0 := by rw [mul_assoc 4, h']; ring
    rw [this, div_zero]
    positivity
  · apply div_le_div_of_nonneg_left hX (by positivity)
    have : (1 : ℝ) ≤ S.card * T.card := by exact_mod_cast h
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]

theorem card_cube_pairs : (Finset.univ : Finset (Fin m × Cube m)).card = m * 2 ^ m := by
  simp

theorem integral_phiR_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (r : ℕ) :
    ∫ ω, phiR (wv fun j ↦ a j ω) p r ∂μ ≤
      ((lowSets m r).card : ℝ) ^ 2 * (16 * m * 2 ^ m / (4 * 4 ^ m)) := by
  have hint : ∀ S T, ∫ ω, cR (wv fun j ↦ a j ω) p S T ^ 2 ∂μ ≤ 16 * m * 2 ^ m := by
    intro S T
    have h := ha.integral_sum_sq univ (coefR S T)
    calc ∫ ω, cR (wv fun j ↦ a j ω) p S T ^ 2 ∂μ = p * (1 - p) * ∑ j, coefR S T j ^ 2 := h
      _ ≤ 1 * ∑ _j : Fin m × Cube m, (16 : ℝ) := by
        refine mul_le_mul (by nlinarith) (Finset.sum_le_sum fun j _ ↦ coefR_sq_le S T j)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num)
      _ = 16 * m * 2 ^ m := by
        rw [Finset.sum_const, card_cube_pairs, nsmul_eq_mul]
        push_cast
        ring
  unfold phiR
  rw [integral_finsetSum _ fun S _ ↦ integrable_coins ha
    (fun v ↦ ∑ T ∈ lowSets m r, cR (wv v) p S T ^ 2 / (4 * S.card * T.card * 4 ^ m))]
  calc ∑ S ∈ lowSets m r, ∫ ω, ∑ T ∈ lowSets m r,
        cR (wv fun j ↦ a j ω) p S T ^ 2 / (4 * S.card * T.card * 4 ^ m) ∂μ
      = ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
          (∫ ω, cR (wv fun j ↦ a j ω) p S T ^ 2 ∂μ) / (4 * S.card * T.card * 4 ^ m) := by
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [integral_finsetSum _ fun T _ ↦ integrable_coins ha
          (fun v ↦ cR (wv v) p S T ^ 2 / (4 * S.card * T.card * 4 ^ m))]
        exact Finset.sum_congr rfl fun T _ ↦ integral_div _ _
    _ ≤ ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r, (16 * m * 2 ^ m / (4 * 4 ^ m) : ℝ) := by
        refine Finset.sum_le_sum fun S _ ↦ Finset.sum_le_sum fun T _ ↦ ?_
        refine (div_le_div_card (integral_nonneg fun _ ↦ sq_nonneg _) S T).trans ?_
        exact div_le_div_of_nonneg_right (hint S T) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The expectation of `bS S x * bS T x` for coin weights. -/
noncomputable def eX (p : ℝ) (S T : Finset (Fin m)) (x : Cube m) : ℝ :=
  p * (1 - p) * ∑ i, dchi i S x * dchi i T x

theorem sum_dchi_mul (i : Fin m) (S T : Finset (Fin m)) :
    ∑ x, dchi i S x * dchi i T x =
      if i ∈ S ∧ i ∈ T then 4 * (if S = T then (2 : ℝ) ^ m else 0) else 0 := by
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp only [dchi, hS, hT, ↓reduceIte, and_self, and_false, false_and, zero_mul, mul_zero,
      Finset.sum_const_zero]
  rw [← sum_chi_mul_chi, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

theorem sum_eX (p : ℝ) (S T : Finset (Fin m)) : ∑ x, eX p S T x = eS p S T := by
  unfold eX eS
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [sum_dchi_mul]
  by_cases hST : S = T
  · subst hST
    simp only [and_self, ↓reduceIte]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  · simp [hST]

/-- The centred summand of `gS` at the vertex `x`, as a function of the coins. -/
noncomputable def Yf (p : ℝ) (S T : Finset (Fin m)) (x : Cube m) (v : Fin m × Cube m → Bool) :
    ℝ :=
  bS (wv v) p S x * bS (wv v) p T x - eX p S T x

theorem gS_sub_eS (p : ℝ) (S T : Finset (Fin m)) (v : Fin m × Cube m → Bool) :
    gS (wv v) p S T - eS p S T = ∑ x, Yf p S T x v := by
  rw [← sum_eX, gS, ← Finset.sum_sub_distrib]
  rfl

theorem abs_bS_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin m × Cube m → Bool)
    (S : Finset (Fin m)) (x : Cube m) : |bS (wv v) p S x| ≤ 2 * m := by
  unfold bS
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |dchi i S x * (wv v i (lowPt x i) - p)| ≤ ∑ _i : Fin m, (2 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul]
        calc |dchi i S x| * |wv v i (lowPt x i) - p| ≤ 2 * 1 :=
              mul_le_mul (abs_dchi_le i S x) (abs_bit_sub_le hp hp1 _) (abs_nonneg _)
                (by norm_num)
          _ = 2 := by ring
    _ = 2 * m := by simp; ring

theorem abs_eX_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset (Fin m)) (x : Cube m) :
    |eX p S T x| ≤ 4 * m := by
  unfold eX
  rw [abs_mul]
  have h1 : |p * (1 - p)| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  have h2 : |∑ i, dchi i S x * dchi i T x| ≤ 4 * m := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |dchi i S x * dchi i T x| ≤ ∑ _i : Fin m, (4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          calc |dchi i S x| * |dchi i T x| ≤ 2 * 2 :=
                mul_le_mul (abs_dchi_le i S x) (abs_dchi_le i T x) (abs_nonneg _) (by norm_num)
            _ = 4 := by ring
      _ = 4 * m := by simp; ring
  calc |p * (1 - p)| * |∑ i, dchi i S x * dchi i T x| ≤ 1 * (4 * m) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 4 * m := one_mul _

theorem abs_Yf_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset (Fin m)) (x : Cube m)
    (v : Fin m × Cube m → Bool) : |Yf p S T x v| ≤ 4 * m ^ 2 + 4 * m := by
  unfold Yf
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have h1 := abs_bS_le hp hp1 v S x
  have h2 := abs_bS_le hp hp1 v T x
  have h3 := abs_eX_le hp hp1 S T x
  have : |bS (wv v) p S x| * |bS (wv v) p T x| ≤ (2 * m) * (2 * m) :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith

theorem integral_Yf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (S T : Finset (Fin m))
    (x : Cube m) : ∫ ω, Yf p S T x (fun j ↦ a j ω) ∂μ = 0 := by
  have := ha.isProb
  have hinj : Function.Injective (fun i : Fin m ↦ (i, lowPt x i)) :=
    fun i i' h ↦ congrArg Prod.fst h
  have h := (ha.precomp hinj).integral_sum_mul_sum univ (fun i ↦ dchi i S x)
    (fun i ↦ dchi i T x)
  unfold Yf
  rw [integral_sub (integrable_coins ha (fun v ↦ bS (wv v) p S x * bS (wv v) p T x))
    (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [show (∫ ω, bS (wv fun j ↦ a j ω) p S x * bS (wv fun j ↦ a j ω) p T x ∂μ) = eX p S T x
    from h]
  ring

/-- The closed neighbourhood of `x` in `Q_m`. -/
def nbhd (x : Cube m) : Finset (Cube m) := insert x (univ.image (flip x))

theorem mem_nbhd_of_lowPt_eq {x x' : Cube m} {i : Fin m} (h : lowPt x' i = lowPt x i) :
    x' ∈ nbhd x := by
  have hj : ∀ j, j ≠ i → x' j = x j := fun j hj ↦ by
    have := congrFun h j
    simpa [lowPt, Function.update_of_ne hj] using this
  unfold nbhd
  rw [Finset.mem_insert, Finset.mem_image]
  by_cases hxi : x' i = x i
  · left
    funext j
    by_cases hji : j = i
    · subst hji; exact hxi
    · exact hj j hji
  · right
    refine ⟨i, Finset.mem_univ _, ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji
      simp only [flip, Function.update_self]
      cases hx : x j <;> cases hx' : x' j <;> simp_all
    · simp only [flip, Function.update_of_ne hji]
      exact (hj j hji).symm

theorem card_nbhd_le (x : Cube m) : (nbhd x).card ≤ m + 1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_image_le.trans (by simp)) 1)

theorem integral_Yf_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset (Fin m)) (x x' : Cube m) :
    ∫ ω, Yf p S T x (fun j ↦ a j ω) * Yf p S T x' (fun j ↦ a j ω) ∂μ ≤
      if x' ∈ nbhd x then (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2 else 0 := by
  have := ha.isProb
  split_ifs with hx
  · refine (le_abs_self _).trans ?_
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun ω ↦ Yf p S T x (fun j ↦ a j ω) * Yf p S T x' (fun j ↦ a j ω))
      (C := (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, sq]
        exact mul_le_mul (abs_Yf_le hp hp1 _ _ _ _) (abs_Yf_le hp hp1 _ _ _ _) (abs_nonneg _)
          (by positivity))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  · have hdep : ∀ y : Cube m, ∀ v v' : Fin m × Cube m → Bool,
        (∀ j ∈ univ.image (fun i ↦ (i, lowPt y i)), v j = v' j) → Yf p S T y v = Yf p S T y v' := by
      intro y v v' hv
      have hb : ∀ U, bS (wv v) p U y = bS (wv v') p U y := fun U ↦
        Finset.sum_congr rfl fun i _ ↦ by
          simp only [wv]
          rw [hv _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
      simp only [Yf, hb]
    have hdisj : Disjoint (univ.image fun i ↦ (i, lowPt x i))
        (univ.image fun i ↦ (i, lowPt x' i)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj hj'
      obtain ⟨i, rfl⟩ := hj
      obtain ⟨i', h⟩ := hj'
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact hx (mem_nbhd_of_lowPt_eq h)
    rw [ha.integral_mul_of_disjoint hdisj (hdep x) (hdep x'), integral_Yf ha, zero_mul]

theorem integral_sq_sum_Yf_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset (Fin m)) :
    ∫ ω, (∑ x, Yf p S T x (fun j ↦ a j ω)) ^ 2 ∂μ ≤
      2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) := by
  have e : ∀ ω, (∑ x, Yf p S T x (fun j ↦ a j ω)) ^ 2 =
      ∑ x, ∑ x', Yf p S T x (fun j ↦ a j ω) * Yf p S T x' (fun j ↦ a j ω) :=
    fun ω ↦ by rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun x _ ↦ integrable_coins ha
    (fun v ↦ ∑ x', Yf p S T x v * Yf p S T x' v)]
  calc ∑ x, ∫ ω, ∑ x', Yf p S T x (fun j ↦ a j ω) * Yf p S T x' (fun j ↦ a j ω) ∂μ
      = ∑ x, ∑ x', ∫ ω, Yf p S T x (fun j ↦ a j ω) * Yf p S T x' (fun j ↦ a j ω) ∂μ :=
        Finset.sum_congr rfl fun x _ ↦ integral_finsetSum _ fun x' _ ↦
          integrable_coins ha (fun v ↦ Yf p S T x v * Yf p S T x' v)
    _ ≤ ∑ x : Cube m, ∑ x' : Cube m,
          if x' ∈ nbhd x then (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2 else 0 :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun x' _ ↦
          integral_Yf_mul_le ha hp hp1 S T x x'
    _ = ∑ x : Cube m, ((nbhd x).card : ℝ) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2 := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _x : Cube m, ((m : ℝ) + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2 := by
        refine Finset.sum_le_sum fun x _ ↦ ?_
        have : ((nbhd x).card : ℝ) ≤ m + 1 := by exact_mod_cast card_nbhd_le x
        gcongr
    _ = 2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp

theorem integral_psiS_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (r : ℕ) :
    ∫ ω, psiS (wv fun j ↦ a j ω) p r ∂μ ≤ ((lowSets m r).card : ℝ) ^ 2 *
      (2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) / (4 * 4 ^ m)) := by
  unfold psiS
  simp_rw [gS_sub_eS]
  rw [integral_finsetSum _ fun S _ ↦ integrable_coins ha
    (fun v ↦ ∑ T ∈ lowSets m r, (∑ x, Yf p S T x v) ^ 2 / (4 * S.card * T.card * 4 ^ m))]
  calc ∑ S ∈ lowSets m r, ∫ ω, ∑ T ∈ lowSets m r,
        (∑ x, Yf p S T x (fun j ↦ a j ω)) ^ 2 / (4 * S.card * T.card * 4 ^ m) ∂μ
      = ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
          (∫ ω, (∑ x, Yf p S T x (fun j ↦ a j ω)) ^ 2 ∂μ) / (4 * S.card * T.card * 4 ^ m) := by
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [integral_finsetSum _ fun T _ ↦ integrable_coins ha
          (fun v ↦ (∑ x, Yf p S T x v) ^ 2 / (4 * S.card * T.card * 4 ^ m))]
        exact Finset.sum_congr rfl fun T _ ↦ integral_div _ _
    _ ≤ ∑ S ∈ lowSets m r, ∑ T ∈ lowSets m r,
          (2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) / (4 * 4 ^ m) : ℝ) := by
        refine Finset.sum_le_sum fun S _ ↦ Finset.sum_le_sum fun T _ ↦ ?_
        refine (div_le_div_card (integral_nonneg fun _ ↦ sq_nonneg _) S T).trans ?_
        exact div_le_div_of_nonneg_right (integral_sq_sum_Yf_le ha hp hp1 S T) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The arithmetic after Markov's inequality. -/
theorem markov_arith {m q : ℕ} (hm : 1 ≤ m) {p I B c : ℝ} (hp : 1 / (m : ℝ) ≤ p) (hc : 0 < c)
    (hI : I * 2 ^ m ≤ B * (m : ℝ) ^ 5) (hB : B * (m : ℝ) ^ (q + 7) ≤ c * 2 ^ m) :
    I / (c * p ^ 2) ≤ 1 / (m : ℝ) ^ q := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hpm : 1 ≤ p * m := by rw [div_le_iff₀ hm0] at hp; linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h2 : (0 : ℝ) < 2 ^ m * (m : ℝ) ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ h2
  calc I * (m : ℝ) ^ q * (2 ^ m * (m : ℝ) ^ 2) = (I * 2 ^ m) * (m : ℝ) ^ (q + 2) := by ring
    _ ≤ (B * (m : ℝ) ^ 5) * (m : ℝ) ^ (q + 2) := mul_le_mul_of_nonneg_right hI (by positivity)
    _ = B * (m : ℝ) ^ (q + 7) := by ring
    _ ≤ c * 2 ^ m := hB
    _ ≤ c * 2 ^ m * (p * m) ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
    _ = c * p ^ 2 * (2 ^ m * (m : ℝ) ^ 2) := by ring

end LowDeg

/-- **Relative spectral closeness on low-degree functions**, with failure probability at most
`1/m^q` for any `q`. -/
theorem lowRel_whp_pow {γ : ℝ} (hγ : 0 < γ) (q : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 1 / (m : ℝ) ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ q ≤ μ.real {ω | LowRel (coinW a ω) p γ (m / 100)} := by
  obtain ⟨m₀, hm₀⟩ := LowDeg.eventually_bound (4 / γ ^ 2) (q + 7)
  refine ⟨max m₀ 1, fun m hm p hp hp1 Ω _ μ a ha ↦ ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have := ha.isProb
  set K : ℝ := ((LowDeg.lowSets m (m / 100)).card : ℝ) ^ 2 with hK
  set F : (Fin m × Cube m → Bool) → ℝ := fun v ↦ LowDeg.phiR (LowDeg.wv v) p (m / 100) with hF
  have hc : 0 < γ ^ 2 := by positivity
  have ht : 0 < γ ^ 2 * p ^ 2 := by positivity
  have hmark := ha.measureReal_ge_le (F := F) (fun v ↦ LowDeg.phiR_nonneg _ _ _) ht
  have hmeas := ha.measurableSet_preimage {v | γ ^ 2 * p ^ 2 ≤ F v}
  have hint : ∫ ω, F (fun j ↦ a j ω) ∂μ ≤ K * (16 * m * 2 ^ m / (4 * 4 ^ m)) :=
    LowDeg.integral_phiR_le ha hp0.le hp1 (m / 100)
  have hI : (∫ ω, F (fun j ↦ a j ω) ∂μ) * 2 ^ m ≤ (4 * K) * (m : ℝ) ^ 5 := by
    have h4 : (16 * (m : ℝ) * 2 ^ m / (4 * 4 ^ m)) * 2 ^ m = 4 * m := by
      rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp
      ring
    have hm5 : (m : ℝ) ≤ (m : ℝ) ^ 5 := le_self_pow₀ (by exact_mod_cast hm1) (by norm_num)
    calc (∫ ω, F (fun j ↦ a j ω) ∂μ) * 2 ^ m ≤ K * (16 * m * 2 ^ m / (4 * 4 ^ m)) * 2 ^ m :=
          mul_le_mul_of_nonneg_right hint (by positivity)
      _ = 4 * K * m := by rw [mul_assoc, h4]; ring
      _ ≤ 4 * K * (m : ℝ) ^ 5 := by gcongr
  have hB : 4 * K * (m : ℝ) ^ (q + 7) ≤ γ ^ 2 * 2 ^ m := by
    have h := hm₀ m (le_of_max_le_left hm)
    have e : 4 * K * (m : ℝ) ^ (q + 7) = γ ^ 2 * (4 / γ ^ 2 * K * (m : ℝ) ^ (q + 7)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h hc.le
  have hbound := LowDeg.markov_arith hm1 hp hc hI hB
  have hsub : {ω | γ ^ 2 * p ^ 2 ≤ F (fun j ↦ a j ω)}ᶜ ⊆
      {ω | LowRel (coinW a ω) p γ (m / 100)} := by
    intro ω hω
    exact LowDeg.lowRel_of_phiR hγ.le hp0.le (not_le.mp hω).le
  calc 1 - 1 / (m : ℝ) ^ q ≤ 1 - μ.real {ω | γ ^ 2 * p ^ 2 ≤ F (fun j ↦ a j ω)} := by
        linarith
    _ = μ.real {ω | γ ^ 2 * p ^ 2 ≤ F (fun j ↦ a j ω)}ᶜ := (probReal_compl_eq_one_sub hmeas).symm
    _ ≤ _ := measureReal_mono hsub

/-- **The squared error on low-degree functions**, with failure probability at most `1/m^q` for
any `q`. -/
theorem lowSq_whp_pow (q : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 1 / (m : ℝ) ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ q ≤ μ.real {ω | LowSq (coinW a ω) p (m / 100)} := by
  obtain ⟨m₀, hm₀⟩ := LowDeg.eventually_bound 8 (q + 7)
  refine ⟨max m₀ 1, fun m hm p hp hp1 Ω _ μ a ha ↦ ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have := ha.isProb
  set K : ℝ := ((LowDeg.lowSets m (m / 100)).card : ℝ) ^ 2 with hK
  set F : (Fin m × Cube m → Bool) → ℝ := fun v ↦ LowDeg.psiS (LowDeg.wv v) p (m / 100) with hF
  have hc : (0 : ℝ) < 4 := by norm_num
  have ht : 0 < 4 * p ^ 2 := by positivity
  have hmark := ha.measureReal_ge_le (F := F) (fun v ↦ LowDeg.psiS_nonneg _ _ _) ht
  have hmeas := ha.measurableSet_preimage {v | 4 * p ^ 2 ≤ F v}
  have hint : ∫ ω, F (fun j ↦ a j ω) ∂μ ≤
      K * (2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) / (4 * 4 ^ m)) :=
    LowDeg.integral_psiS_le ha hp0.le hp1 (m / 100)
  have hI : (∫ ω, F (fun j ↦ a j ω) ∂μ) * 2 ^ m ≤ (32 * K) * (m : ℝ) ^ 5 := by
    have h4 : (2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) / (4 * 4 ^ m)) * 2 ^ m =
        4 * (m : ℝ) ^ 2 * (m + 1) ^ 3 := by
      rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp
    have h2m : (m : ℝ) + 1 ≤ 2 * m := by linarith
    have h3 : ((m : ℝ) + 1) ^ 3 ≤ (2 * m) ^ 3 := by gcongr
    calc (∫ ω, F (fun j ↦ a j ω) ∂μ) * 2 ^ m ≤
          K * (2 ^ m * ((m + 1) * (4 * (m : ℝ) ^ 2 + 4 * m) ^ 2) / (4 * 4 ^ m)) * 2 ^ m :=
          mul_le_mul_of_nonneg_right hint (by positivity)
      _ = K * (4 * (m : ℝ) ^ 2 * (m + 1) ^ 3) := by rw [mul_assoc, h4]
      _ ≤ K * (4 * (m : ℝ) ^ 2 * (2 * m) ^ 3) := by gcongr
      _ = (32 * K) * (m : ℝ) ^ 5 := by ring
  have hB : 32 * K * (m : ℝ) ^ (q + 7) ≤ 4 * 2 ^ m := by
    have h := hm₀ m (le_of_max_le_left hm)
    linarith
  have hbound := LowDeg.markov_arith hm1 hp hc hI hB
  have hsub : {ω | 4 * p ^ 2 ≤ F (fun j ↦ a j ω)}ᶜ ⊆ {ω | LowSq (coinW a ω) p (m / 100)} := by
    intro ω hω
    exact LowDeg.lowSq_of_psiS hp0.le (not_le.mp hω).le
  calc 1 - 1 / (m : ℝ) ^ q ≤ 1 - μ.real {ω | 4 * p ^ 2 ≤ F (fun j ↦ a j ω)} := by
        linarith
    _ = μ.real {ω | 4 * p ^ 2 ≤ F (fun j ↦ a j ω)}ᶜ := (probReal_compl_eq_one_sub hmeas).symm
    _ ≤ _ := measureReal_mono hsub

/-- **Relative spectral closeness on low-degree functions** ([BMW26, Lemma 5.6]). -/
theorem lowRel_whp {γ : ℝ} (hγ : 0 < γ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 1 / (m : ℝ) ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 3 ≤ μ.real {ω | LowRel (coinW a ω) p γ (m / 100)} := by
  exact lowRel_whp_pow hγ 3

/-- **The squared error on low-degree functions** ([BMW26, Lemma 5.8]). -/
theorem lowSq_whp :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 1 / (m : ℝ) ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 3 ≤ μ.real {ω | LowSq (coinW a ω) p (m / 100)} := by
  exact lowSq_whp_pow 3

end BMW26
