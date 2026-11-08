module

public import BMW26.Spec.Defs

/-!
# Low-degree functions do not concentrate on the bad vertices

[BMW26, Lemma 5.9], with a second-moment bound in place of Bernstein's inequality with bounded
dependence. With `R` the bad vertices and `r = m / 100`, for `h` of degree at most `r`,
`∑_{x ∈ R} h(x)² = ∑_Z 1̂_R(Z) ∑ₓ χ_Z(x) h(x)²`, where only `|Z| ≤ 2r` contribute and
`|∑ₓ χ_Z h²| ≤ ‖h‖² ≤ ‖g‖²`; so the fraction is at most `|R|/2^m + ∑_{1 ≤ |Z| ≤ 2r} |1̂_R(Z)|`.
The indicators `1_R(x)` and `1_R(y)` are independent unless `x = y` or `x ~ y`, and all
vertices are bad with the same probability `β` (the law of independent `p`-coins depends only on
`p`), so writing `1̂_R(Z) = 2^-m ∑ₓ (1_R(x) - β) χ_Z(x)` gives `E 1̂_R(Z)² ≤ (m + 1)/2^m` for
`Z ≠ ∅`. There are at most `N = 8^(2r) (9/8)^m ≤ 2^(0.24 m)` sets `Z`, and Markov on
`∑_Z 1̂_R(Z)²` and Cauchy–Schwarz give `∑_Z |1̂_R(Z)| ≤ 2^(-m/10)` with probability at least
`1 - 1/m^q` for any `q` (`BMW26.badLow_whp_pow`), the failure probability being exponentially
small.
-/

@[expose] public section

namespace BMW26

open MeasureTheory Finset

namespace BadF

variable {m : ℕ}

/-! ### Deterministic part -/

/-- The indicator function of a set of vertices. -/
noncomputable def ind (R : Finset (Cube m)) (x : Cube m) : ℝ := by
  classical
  exact if x ∈ R then 1 else 0

theorem ind_apply (R : Finset (Cube m)) (x : Cube m) [Decidable (x ∈ R)] :
    ind R x = if x ∈ R then 1 else 0 := by
  unfold ind
  congr

theorem abs_chi (S : Finset (Fin m)) (x : Cube m) : |chi S x| = 1 := by
  unfold chi
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ ↦ by cases x i <;> simp [sgn]

theorem chi_empty (x : Cube m) : chi ∅ x = 1 := by
  simp [chi]

theorem sum_chi_eq_zero {Z : Finset (Fin m)} (hZ : Z ≠ ∅) : ∑ x, chi Z x = 0 := by
  have := sum_chi_mul_chi Z ∅
  simpa [chi_empty, hZ] using this

/-- For `Z ≠ ∅`, the Fourier coefficient does not see a constant shift. -/
theorem fourier_eq_sub (f : Cube m → ℝ) (q : ℝ) {Z : Finset (Fin m)} (hZ : Z ≠ ∅) :
    fourier f Z = (∑ x, (f x - q) * chi Z x) / 2 ^ m := by
  unfold fourier
  congr 1
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_chi_eq_zero hZ, mul_zero,
    sub_zero]

/-- Projecting on the low-degree characters does not increase the norm. -/
theorem sum_sq_lowProj_le (r : ℕ) (g : Cube m → ℝ) :
    ∑ x, lowProj r g x ^ 2 ≤ ∑ x, g x ^ 2 := by
  rw [sum_sq_eq_sum_fourier (lowProj r g), sum_sq_eq_sum_fourier g]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S _ ↦ ?_) (by positivity)
  rw [fourier_lowProj]
  split_ifs
  · exact le_rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

theorem fourier_chi_mul (Z S : Finset (Fin m)) (h : Cube m → ℝ) :
    fourier (fun x ↦ chi Z x * h x) S = fourier h (symmDiff Z S) := by
  unfold fourier
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← chi_mul_chi]
  ring

theorem card_le_card_symmDiff_add (Z S : Finset (Fin m)) :
    Z.card ≤ (symmDiff Z S).card + S.card := by
  calc Z.card = (symmDiff (symmDiff Z S) S).card := by rw [symmDiff_symmDiff_cancel_right]
    _ ≤ (symmDiff Z S ∪ S).card := card_le_card symmDiff_le_sup
    _ ≤ (symmDiff Z S).card + S.card := card_union_le _ _

/-- `h²` has degree at most `2r` when `h` has degree at most `r`. -/
theorem sum_chi_mul_sq_eq_zero (r : ℕ) (g : Cube m → ℝ) {Z : Finset (Fin m)}
    (hZ : 2 * r < Z.card) : ∑ x, chi Z x * lowProj r g x ^ 2 = 0 := by
  have h1 : ∑ x, chi Z x * lowProj r g x ^ 2 =
      ∑ x, (fun y ↦ chi Z y * lowProj r g y) x * lowProj r g x := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    ring
  rw [h1, sum_mul_eq_sum_fourier]
  simp only [fourier_chi_mul]
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  rw [fourier_lowProj, fourier_lowProj]
  split_ifs with h2 h3
  · have := card_le_card_symmDiff_add Z S
    omega
  · simp
  · simp
  · simp

theorem abs_sum_chi_mul_sq_le (r : ℕ) (g : Cube m → ℝ) (Z : Finset (Fin m)) :
    |∑ x, chi Z x * lowProj r g x ^ 2| ≤ ∑ x, g x ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ (sum_sq_lowProj_le r g))
  refine le_of_eq (Finset.sum_congr rfl fun x _ ↦ ?_)
  rw [abs_mul, abs_chi, one_mul, abs_of_nonneg (sq_nonneg _)]

theorem fourier_ind_empty (R : Finset (Cube m)) : fourier (ind R) ∅ = R.card / 2 ^ m := by
  classical
  unfold fourier
  congr 1
  simp only [chi_empty, mul_one, ind_apply]
  rw [Finset.sum_boole]
  simp

/-- The sets `Z` with `1 ≤ |Z| ≤ k`. -/
noncomputable def lowSets (m k : ℕ) : Finset (Finset (Fin m)) :=
  (univ.filter fun Z : Finset (Fin m) ↦ Z.card ≤ k).erase ∅

/-- **The deterministic bound**: the fraction of the squared norm of a function of degree at
most `r` on `R` is at most `|R|/2^m + ∑_{1 ≤ |Z| ≤ 2r} |1̂_R(Z)|`. -/
theorem sum_lowProj_sq_le (R : Finset (Cube m)) (r : ℕ) (g : Cube m → ℝ) :
    ∑ x ∈ R, lowProj r g x ^ 2 ≤
      (R.card / 2 ^ m + ∑ Z ∈ lowSets m (2 * r), |fourier (ind R) Z|) * ∑ x, g x ^ 2 := by
  classical
  set h := lowProj r g
  have e1 : ∑ x ∈ R, h x ^ 2 = ∑ x, ind R x * h x ^ 2 := by
    simp only [ind_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have e2 : ∑ x, ind R x * h x ^ 2 =
      ∑ Z, fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2 := by
    calc ∑ x, ind R x * h x ^ 2 = ∑ x, (∑ Z, fourier (ind R) Z * chi Z x) * h x ^ 2 := by
          simp only [sum_fourier_mul_chi]
      _ = ∑ x, ∑ Z, fourier (ind R) Z * (chi Z x * h x ^ 2) := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun Z _ ↦ by ring
      _ = ∑ Z, ∑ x, fourier (ind R) Z * (chi Z x * h x ^ 2) := Finset.sum_comm
      _ = ∑ Z, fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2 := by
          simp only [Finset.mul_sum]
  have e3 : ∑ Z, fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2 =
      ∑ Z ∈ univ.filter (fun Z : Finset (Fin m) ↦ Z.card ≤ 2 * r),
        fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2 := by
    refine (Finset.sum_filter_of_ne fun Z _ hZ ↦ ?_).symm
    by_contra hc
    push Not at hc
    exact hZ (by rw [sum_chi_mul_sq_eq_zero r g hc, mul_zero])
  have e4 : ∑ Z ∈ univ.filter (fun Z : Finset (Fin m) ↦ Z.card ≤ 2 * r), |fourier (ind R) Z| =
      R.card / 2 ^ m + ∑ Z ∈ lowSets m (2 * r), |fourier (ind R) Z| := by
    rw [lowSets, ← Finset.add_sum_erase _ _ (by simp : (∅ : Finset (Fin m)) ∈ _),
      fourier_ind_empty, abs_of_nonneg (by positivity)]
  rw [e1, e2, e3, ← e4, Finset.sum_mul]
  refine Finset.sum_le_sum fun Z _ ↦ ?_
  calc fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2
      ≤ |fourier (ind R) Z * ∑ x, chi Z x * h x ^ 2| := le_abs_self _
    _ = |fourier (ind R) Z| * |∑ x, chi Z x * h x ^ 2| := abs_mul _ _
    _ ≤ |fourier (ind R) Z| * ∑ x, g x ^ 2 :=
        mul_le_mul_of_nonneg_left (abs_sum_chi_mul_sq_le r g Z) (abs_nonneg _)

/-- There are at most `8^k (9/8)^m` sets of size at most `k`. -/
theorem card_filter_card_le (m k : ℕ) :
    ((univ.filter fun Z : Finset (Fin m) ↦ Z.card ≤ k).card : ℝ) ≤ 8 ^ k * (9 / 8) ^ m := by
  have hsum : ∑ Z : Finset (Fin m), (1 / 8 : ℝ) ^ Z.card = (9 / 8) ^ m := by
    have := Finset.prod_one_add (f := fun _ : Fin m ↦ (1 / 8 : ℝ)) univ
    simp only [prod_const, card_univ, Fintype.card_fin, powerset_univ] at this
    rw [← this]
    norm_num
  have h1 : (1 / 8 : ℝ) ^ k *
      ((univ.filter fun Z : Finset (Fin m) ↦ Z.card ≤ k).card : ℝ) ≤ (9 / 8) ^ m := by
    rw [← hsum, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    calc ∑ _Z ∈ univ.filter (fun Z : Finset (Fin m) ↦ Z.card ≤ k), (1 / 8 : ℝ) ^ k
        ≤ ∑ Z ∈ univ.filter (fun Z : Finset (Fin m) ↦ Z.card ≤ k), (1 / 8 : ℝ) ^ Z.card := by
          refine Finset.sum_le_sum fun Z hZ ↦ ?_
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (mem_filter.1 hZ).2
      _ ≤ ∑ Z : Finset (Fin m), (1 / 8 : ℝ) ^ Z.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ ↦ by positivity)
  have h8 : (0 : ℝ) < (1 / 8) ^ k := by positivity
  calc ((univ.filter fun Z : Finset (Fin m) ↦ Z.card ≤ k).card : ℝ)
      = 8 ^ k * ((1 / 8 : ℝ) ^ k *
          ((univ.filter fun Z : Finset (Fin m) ↦ Z.card ≤ k).card : ℝ)) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 8 ^ k * (9 / 8) ^ m := by gcongr

theorem card_lowSets_le (m k : ℕ) : ((lowSets m k).card : ℝ) ≤ 8 ^ k * (9 / 8) ^ m := by
  refine le_trans ?_ (card_filter_card_le m k)
  exact_mod_cast card_erase_le

/-! ### The numerical estimate -/

/-- For `m` large, `2 (8^(2r) (9/8)^m)² (m + 1) ≤ 2^m (2^(-m/10))² / m^q` with `r = m / 100`. -/
theorem numeric (q : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, 0 < m ∧
    2 * ((8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m) ^ 2 * (m + 1) ≤
      2 ^ m * ((2 : ℝ) ^ (-(m : ℝ) / 10)) ^ 2 / (m : ℝ) ^ q := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt (25 * (q + 1))
    (by norm_num : (1 : ℝ) < 256)
  have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4 ^ 25))
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max m₁ 1, fun m hm ↦ ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  refine ⟨hm1, ?_⟩
  have hpoly : (4 : ℝ) ^ 25 * (m : ℝ) ^ (25 * (q + 1)) ≤ 256 ^ m := by
    have := hm₁ m (le_of_max_le_left hm)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at this
    linarith
  set ρ : ℝ := (2 : ℝ) ^ ((m : ℝ) / 50) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ50 : ρ ^ 50 = 2 ^ m := by
    rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  set u : ℝ := (2 : ℝ) ^ (-(m : ℝ) / 10) with hudef
  have hu : u * ρ ^ 5 = 1 := by
    rw [hudef, hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    norm_num
    ring_nf
    simp
  have h2u : 2 ^ m * u ^ 2 = ρ ^ 40 := by
    rw [← hρ50]
    calc ρ ^ 50 * u ^ 2 = ρ ^ 40 * (u * ρ ^ 5) ^ 2 := by ring
      _ = ρ ^ 40 := by rw [hu]; ring
  have hpow : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ m = (ρ ^ k) ^ 50 := by
    intro k
    calc ((2 : ℝ) ^ k) ^ m = ((2 : ℝ) ^ m) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (ρ ^ 50) ^ k := by rw [hρ50]
      _ = (ρ ^ k) ^ 50 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h8 : (8 : ℝ) ^ (2 * (m / 100)) ≤ ρ ^ 3 := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (50 : ℕ) ≠ 0)]
    calc ((8 : ℝ) ^ (2 * (m / 100))) ^ 50 = 2 ^ (300 * (m / 100)) := by
          rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
          ring_nf
      _ ≤ 2 ^ (3 * m) := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have := Nat.div_mul_le_self m 100
          omega
      _ = ((2 : ℝ) ^ 3) ^ m := by rw [← pow_mul]
      _ = (ρ ^ 3) ^ 50 := hpow 3
  have h9 : (9 / 8 : ℝ) ^ m ≤ ρ ^ 9 := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (50 : ℕ) ≠ 0)]
    calc ((9 / 8 : ℝ) ^ m) ^ 50 = ((9 / 8 : ℝ) ^ 50) ^ m := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ 9) ^ m := by
          gcongr
          norm_num
      _ = (ρ ^ 9) ^ 50 := hpow 9
  have hB : (8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m ≤ ρ ^ 12 := by
    calc (8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m ≤ ρ ^ 3 * ρ ^ 9 :=
          mul_le_mul h8 h9 (by positivity) (by positivity)
      _ = ρ ^ 12 := by ring
  have hpoly' : 2 * ((m : ℝ) + 1) * (m : ℝ) ^ q ≤ ρ ^ 16 := by
    have h4 : 4 * (m : ℝ) ^ (q + 1) ≤ ρ ^ 16 := by
      rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (25 : ℕ) ≠ 0)]
      calc (4 * (m : ℝ) ^ (q + 1)) ^ 25 = 4 ^ 25 * (m : ℝ) ^ (25 * (q + 1)) := by ring
        _ ≤ 256 ^ m := hpoly
        _ = (ρ ^ 16) ^ 25 := by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, hpow 8]
          ring
    have : 2 * ((m : ℝ) + 1) * (m : ℝ) ^ q ≤ 4 * (m : ℝ) ^ (q + 1) := by
      have h3 : (0 : ℝ) ≤ (m : ℝ) ^ q := by positivity
      rw [pow_succ]
      nlinarith
    linarith
  rw [le_div_iff₀ (by positivity), h2u]
  have hB2 : ((8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m) ^ 2 ≤ ρ ^ 24 := by
    calc ((8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m) ^ 2 ≤ (ρ ^ 12) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hB 2
      _ = ρ ^ 24 := by ring
  calc 2 * ((8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m) ^ 2 * (m + 1) * (m : ℝ) ^ q
      = ((8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m) ^ 2 * (2 * ((m : ℝ) + 1) * (m : ℝ) ^ q) := by
        ring
    _ ≤ ρ ^ 24 * ρ ^ 16 := mul_le_mul hB2 hpoly' (by positivity) (by positivity)
    _ = ρ ^ 40 := by ring

/-! ### Probabilistic part -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A function of finitely many coins is integrable. -/
theorem integrable {ι : Type*} [Finite ι] {μ : Measure Ω} {a : ι → Ω → Bool} {p : ℝ}
    (h : IsCoins μ a p) (F : (ι → Bool) → ℝ) : Integrable (fun ω ↦ F (fun i ↦ a i ω)) μ := by
  classical
  have := Fintype.ofFinite ι
  have := h.isProb
  have hm : Measurable fun ω ↦ F (fun i ↦ a i ω) :=
    (measurable_of_countable F).comp (Measurable.of_eval h.meas)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ v, |F v|)
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun v ↦ |F v|) (fun v _ ↦ abs_nonneg _) (mem_univ _)

/-- The law of a finite family of independent `p`-coins depends only on `p`. -/
theorem integral_eq_of_coins {μ : Measure Ω} {κ : Type*} [Finite κ] {b b' : κ → Ω → Bool}
    {p : ℝ} (hb : IsCoins μ b p) (hb' : IsCoins μ b' p) (Φ : (κ → Bool) → ℝ) :
    ∫ ω, Φ (fun i ↦ b i ω) ∂μ = ∫ ω, Φ (fun i ↦ b' i ω) ∂μ := by
  classical
  have := Fintype.ofFinite κ
  have := hb.isProb
  have key : ∀ c : κ → Ω → Bool, IsCoins μ c p → ∀ i (s : Bool),
      μ.map (c i) {s} = if s then ENNReal.ofReal p else 1 - ENNReal.ofReal p := by
    intro c hc i s
    rw [Measure.map_apply (hc.meas i) (measurableSet_singleton s)]
    have ht : μ (c i ⁻¹' {true}) = ENNReal.ofReal p := by
      rw [← hc.prob_true i, ofReal_measureReal]
      rfl
    cases s
    · have hc' : c i ⁻¹' {false} = (c i ⁻¹' {true})ᶜ := by
        ext ω
        simp
      rw [hc', prob_compl_eq_one_sub (hc.meas i (measurableSet_singleton true)), ht]
      simp
    · simpa using ht
  have hmap : ∀ i, μ.map (b i) = μ.map (b' i) := by
    intro i
    rw [Measure.ext_iff_singleton]
    intro s
    rw [key b hb, key b' hb']
  have h1 := hb.indep.map_fun_eq_pi_map (fun i ↦ (hb.meas i).aemeasurable)
  have h2 := hb'.indep.map_fun_eq_pi_map (fun i ↦ (hb'.meas i).aemeasurable)
  have hm : μ.map (fun ω i ↦ b i ω) = μ.map (fun ω i ↦ b' i ω) := by
    rw [h1, h2]
    simp only [hmap]
  rw [← integral_map (Measurable.of_eval hb.meas).aemeasurable
      (measurable_of_countable Φ).aestronglyMeasurable, hm,
    integral_map (Measurable.of_eval hb'.meas).aemeasurable
      (measurable_of_countable Φ).aestronglyMeasurable]

/-- The edge weights given by a vector of coins. -/
def W (v : Fin m × Cube m → Bool) : Fin m → Cube m → ℝ := fun i y ↦ bit (v (i, y))

/-- Whether a vertex is bad, as a function of the `m` coins at it. -/
noncomputable def badLaw (m : ℕ) (p γ : ℝ) (u : Fin m → Bool) : ℝ := by
  classical
  exact if γ * p * m < |∑ i, bit (u i) - p * m| then 1 else 0

theorem mem_badSet {w : Fin m → Cube m → ℝ} {p γ : ℝ} {x : Cube m} :
    x ∈ badSet w p γ ↔ γ * p * m < |deg w x - p * m| := by
  unfold badSet
  simp

/-- Whether `x` is bad depends only on the `m` coins at `x`. -/
theorem ind_badSet_eq (p γ : ℝ) (v : Fin m × Cube m → Bool) (x : Cube m) :
    ind (badSet (W v) p γ) x = badLaw m p γ (fun i ↦ v (i, lowPt x i)) := by
  classical
  have hmem : x ∈ badSet (W v) p γ ↔ γ * p * m < |∑ i, bit (v (i, lowPt x i)) - p * m| := by
    rw [mem_badSet]
    exact Iff.rfl
  rw [ind_apply]
  unfold badLaw
  by_cases hc : γ * p * m < |∑ i, bit (v (i, lowPt x i)) - p * m|
  · simp [hmem, hc]
  · simp [hmem, hc]

/-- The coins at the `m` edges of `x`. -/
def edges (x : Cube m) : Finset (Fin m × Cube m) := univ.image fun i ↦ (i, lowPt x i)

theorem ind_badSet_congr (p γ : ℝ) {v v' : Fin m × Cube m → Bool} (x : Cube m)
    (hv : ∀ e ∈ edges x, v e = v' e) : ind (badSet (W v) p γ) x = ind (badSet (W v') p γ) x := by
  rw [ind_badSet_eq, ind_badSet_eq]
  congr 1
  funext i
  exact hv _ (mem_image_of_mem _ (mem_univ i))

theorem eq_of_lowPt_eq {x y : Cube m} {i : Fin m} (hxy : lowPt x i = lowPt y i) :
    y = x ∨ y = flip x i := by
  have hk : ∀ k, k ≠ i → y k = x k := fun k hk ↦ by
    have := congrFun hxy k
    simp only [lowPt, Function.update_of_ne hk] at this
    exact this.symm
  by_cases h : y i = x i
  · left
    funext k
    by_cases hk' : k = i
    · subst hk'
      exact h
    · exact hk k hk'
  · right
    funext k
    by_cases hk' : k = i
    · subst hk'
      simp only [flip, Function.update_self]
      revert h
      cases y k <;> cases x k <;> simp
    · simp only [flip, Function.update_of_ne hk']
      exact hk k hk'

/-- The closed neighbourhood of `x` in `Q_m`. -/
def nbhd (x : Cube m) : Finset (Cube m) := insert x (univ.image (flip x))

theorem card_nbhd_le (x : Cube m) : (nbhd x).card ≤ m + 1 := by
  unfold nbhd
  refine (card_insert_le _ _).trans ?_
  have := card_image_le (s := (univ : Finset (Fin m))) (f := flip x)
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- Non-adjacent distinct vertices have disjoint sets of edges. -/
theorem disjoint_edges {x y : Cube m} (hy : y ∉ nbhd x) : Disjoint (edges x) (edges y) := by
  rw [Finset.disjoint_left]
  intro e hex hey
  simp only [edges, mem_image, mem_univ, true_and] at hex hey
  obtain ⟨i, rfl⟩ := hex
  obtain ⟨j, hj⟩ := hey
  simp only [Prod.mk.injEq] at hj
  obtain ⟨rfl, hj⟩ := hj
  apply hy
  rcases eq_of_lowPt_eq hj.symm with h | h
  · simp [nbhd, h]
  · simp [nbhd, h]

variable {μ : Measure Ω} {a : Fin m × Cube m → Ω → Bool} {p : ℝ}

/-- All vertices are bad with the same probability. -/
theorem integral_ind_eq (h : IsCoins μ a p) (γ : ℝ) (x y : Cube m) :
    ∫ ω, ind (badSet (W fun j ↦ a j ω) p γ) x ∂μ =
      ∫ ω, ind (badSet (W fun j ↦ a j ω) p γ) y ∂μ := by
  simp only [ind_badSet_eq]
  have hx : Function.Injective fun i : Fin m ↦ ((i, lowPt x i) : Fin m × Cube m) :=
    fun i j hij ↦ congrArg Prod.fst hij
  have hy : Function.Injective fun i : Fin m ↦ ((i, lowPt y i) : Fin m × Cube m) :=
    fun i j hij ↦ congrArg Prod.fst hij
  exact integral_eq_of_coins (h.precomp hx) (h.precomp hy) (badLaw m p γ)

theorem ind_eq_zero_or_one (R : Finset (Cube m)) (x : Cube m) : ind R x = 0 ∨ ind R x = 1 := by
  classical
  rw [ind_apply]
  split_ifs <;> simp

/-- **Second moment of a Fourier coefficient of the bad set**:
`E 1̂_R(Z)² ≤ (m + 1)/2^m` for `Z ≠ ∅`. -/
theorem integral_fourier_sq_le (h : IsCoins μ a p) (γ : ℝ) {Z : Finset (Fin m)} (hZ : Z ≠ ∅) :
    ∫ ω, fourier (ind (badSet (W fun j ↦ a j ω) p γ)) Z ^ 2 ∂μ ≤ (m + 1) / 2 ^ m := by
  classical
  have := h.isProb
  set q := ∫ ω, ind (badSet (W fun j ↦ a j ω) p γ) (fun _ ↦ false) ∂μ with hqdef
  have hqx : ∀ x, ∫ ω, ind (badSet (W fun j ↦ a j ω) p γ) x ∂μ = q :=
    fun x ↦ integral_ind_eq h γ x _
  have hq0 : 0 ≤ q := integral_nonneg fun ω ↦ by
    rcases ind_eq_zero_or_one (badSet (W fun j ↦ a j ω) p γ) (fun _ ↦ false) with h0 | h0 <;>
      rw [h0] <;> norm_num
  have hq1 : q ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun ω ↦ ind (badSet (W fun j ↦ a j ω) p γ) (fun _ ↦ false))
      (Filter.Eventually.of_forall fun ω ↦ by
        rcases ind_eq_zero_or_one (badSet (W fun j ↦ a j ω) p γ) (fun _ ↦ false) with h0 | h0 <;>
          rw [h0] <;> norm_num)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  -- the centred indicators
  set D : (Fin m × Cube m → Bool) → Cube m → ℝ :=
    fun v x ↦ ind (badSet (W v) p γ) x - q with hD
  have hDabs : ∀ v x, |D v x| ≤ 1 := by
    intro v x
    simp only [hD]
    rw [abs_le]
    rcases ind_eq_zero_or_one (badSet (W v) p γ) x with h0 | h0 <;> rw [h0] <;>
      constructor <;> linarith
  have hpt : ∀ v, fourier (ind (badSet (W v) p γ)) Z ^ 2 =
      (∑ x, ∑ y, chi Z x * chi Z y * (D v x * D v y)) / (2 ^ m) ^ 2 := by
    intro v
    rw [fourier_eq_sub _ q hZ, div_pow, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [hD]
    ring
  set e : Cube m → Cube m → ℝ :=
    fun x y ↦ ∫ ω, D (fun j ↦ a j ω) x * D (fun j ↦ a j ω) y ∂μ with he
  have hint : ∫ ω, fourier (ind (badSet (W fun j ↦ a j ω) p γ)) Z ^ 2 ∂μ =
      (∑ x, ∑ y, chi Z x * chi Z y * e x y) / (2 ^ m) ^ 2 := by
    simp only [hpt]
    rw [integral_div]
    congr 1
    rw [integral_finsetSum _ (fun x _ ↦
      integrable h (fun v ↦ ∑ y, chi Z x * chi Z y * (D v x * D v y)))]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [integral_finsetSum _ (fun y _ ↦
      integrable h (fun v ↦ chi Z x * chi Z y * (D v x * D v y)))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [integral_const_mul]
  have he1 : ∀ x y, |e x y| ≤ 1 := by
    intro x y
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun ω ↦ D (fun j ↦ a j ω) x * D (fun j ↦ a j ω) y)
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul (hDabs _ x) (hDabs _ y) (abs_nonneg _) zero_le_one)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have hDint : ∀ x, ∫ ω, D (fun j ↦ a j ω) x ∂μ = 0 := by
    intro x
    simp only [hD]
    rw [integral_sub (integrable h (fun v ↦ ind (badSet (W v) p γ) x)) (integrable_const q),
      hqx x, integral_const, probReal_univ, one_smul, sub_self]
  have he0 : ∀ x y, y ∉ nbhd x → e x y = 0 := by
    intro x y hy
    simp only [he]
    rw [h.integral_mul_of_disjoint (disjoint_edges hy) (F := fun v ↦ D v x) (G := fun v ↦ D v y)
      (fun v v' hv ↦ by simp only [hD, ind_badSet_congr p γ x hv])
      (fun v v' hv ↦ by simp only [hD, ind_badSet_congr p γ y hv]), hDint x, zero_mul]
  have hrow : ∀ x, ∑ y, chi Z x * chi Z y * e x y ≤ m + 1 := by
    intro x
    calc ∑ y, chi Z x * chi Z y * e x y ≤ ∑ y, |e x y| := Finset.sum_le_sum fun y _ ↦ by
            calc chi Z x * chi Z y * e x y ≤ |chi Z x * chi Z y * e x y| := le_abs_self _
              _ = |e x y| := by rw [abs_mul, abs_mul, abs_chi, abs_chi, one_mul, one_mul]
      _ = ∑ y ∈ nbhd x, |e x y| :=
            (Finset.sum_subset (subset_univ _) fun y _ hy ↦ by rw [he0 x y hy, abs_zero]).symm
      _ ≤ ∑ _y ∈ nbhd x, (1 : ℝ) := Finset.sum_le_sum fun y _ ↦ he1 x y
      _ = (nbhd x).card := by simp
      _ ≤ m + 1 := by exact_mod_cast card_nbhd_le x
  have htot : ∑ x, ∑ y, chi Z x * chi Z y * e x y ≤ 2 ^ m * (m + 1) := by
    calc ∑ x, ∑ y, chi Z x * chi Z y * e x y ≤ ∑ _x : Cube m, ((m : ℝ) + 1) :=
          Finset.sum_le_sum fun x _ ↦ hrow x
      _ = 2 ^ m * (m + 1) := by simp; ring
  rw [hint, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ x, ∑ y, chi Z x * chi Z y * e x y) * 2 ^ m ≤ 2 ^ m * (m + 1) * 2 ^ m := by gcongr
    _ = (m + 1) * (2 ^ m) ^ 2 := by ring

/-- The expected squared Fourier mass of the bad set on `lowSets m k`. -/
theorem integral_sum_fourier_sq_le (h : IsCoins μ a p) (γ : ℝ) (k : ℕ) :
    ∫ ω, ∑ Z ∈ lowSets m k, fourier (ind (badSet (W fun j ↦ a j ω) p γ)) Z ^ 2 ∂μ ≤
      (lowSets m k).card * ((m + 1) / 2 ^ m) := by
  rw [integral_finsetSum _ (fun Z _ ↦
    integrable h (fun v ↦ fourier (ind (badSet (W v) p γ)) Z ^ 2))]
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun Z hZ ↦ integral_fourier_sq_le h γ ?_
  exact (Finset.mem_erase.1 hZ).1

end Prob

end BadF

/-- **Low-degree functions avoid the bad vertices**, with failure probability at most `1/m^q` for
any `q`. -/
theorem badLow_whp_pow (γ : ℝ) (q : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ q ≤
          μ.real {ω | BadLow (coinW a ω) p γ
            ((badSet (coinW a ω) p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100)} := by
  obtain ⟨m₀, hm₀⟩ := BadF.numeric q
  refine ⟨m₀, fun m hm p hp0 hp1 Ω _ μ a h ↦ ?_⟩
  obtain ⟨hmpos, hnum⟩ := hm₀ m hm
  classical
  have := h.isProb
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  set u : ℝ := (2 : ℝ) ^ (-(m : ℝ) / 10) with hudef
  have hu : 0 < u := by positivity
  set T := BadF.lowSets m (2 * (m / 100)) with hT
  set t : ℝ := (T.card : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  set B : ℝ := (8 : ℝ) ^ (2 * (m / 100)) * (9 / 8) ^ m with hB
  have htB : t ≤ B := BadF.card_lowSets_le m _
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (by norm_num))
  set s : ℝ := u ^ 2 / (t + 1) with hs
  have hs0 : 0 < s := by positivity
  set X : (Fin m × Cube m → Bool) → ℝ :=
    fun v ↦ ∑ Z ∈ T, fourier (BadF.ind (badSet (BadF.W v) p γ)) Z ^ 2 with hX
  have hEX : ∫ ω, X (fun j ↦ a j ω) ∂μ ≤ t * ((m + 1) / 2 ^ m) :=
    BadF.integral_sum_fourier_sq_le h γ (2 * (m / 100))
  have hM := h.measureReal_ge_le (F := X) (fun v ↦ Finset.sum_nonneg fun Z _ ↦ sq_nonneg _) hs0
  -- Markov
  have hP : μ.real {ω | s ≤ X (fun j ↦ a j ω)} ≤ 1 / (m : ℝ) ^ q := by
    refine hM.trans ?_
    refine (div_le_div_of_nonneg_right hEX hs0.le).trans ?_
    have key : t * ((m + 1) / 2 ^ m) / s = t * (t + 1) * (m + 1) / (2 ^ m * u ^ 2) := by
      rw [hs]
      field_simp
    rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 * B ^ 2 * (m + 1) * (m : ℝ) ^ q ≤ 2 ^ m * u ^ 2 := by
      rw [← le_div_iff₀ (by positivity)]
      exact hnum
    have h2 : t * (t + 1) ≤ 2 * B ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ (m + 1) * (m : ℝ) ^ q := by positivity
    have h4 : t * (t + 1) * ((m + 1) * (m : ℝ) ^ q) ≤ 2 * B ^ 2 * ((m + 1) * (m : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_right h2 h3
    nlinarith
  -- on the good event, `BadLow` holds
  have hgood : ∀ ω, X (fun j ↦ a j ω) < s → BadLow (coinW a ω) p γ
      (((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m + u) (m / 100) := by
    intro ω hω
    have hXω : ∑ Z ∈ T, fourier (BadF.ind (badSet (coinW a ω) p γ)) Z ^ 2 < s := hω
    have hsum : ∑ Z ∈ T, |fourier (BadF.ind (badSet (coinW a ω) p γ)) Z| ≤ u := by
      have hcs : (∑ Z ∈ T, |fourier (BadF.ind (badSet (coinW a ω) p γ)) Z|) ^ 2 ≤
          t * ∑ Z ∈ T, fourier (BadF.ind (badSet (coinW a ω) p γ)) Z ^ 2 := by
        have := Finset.sum_mul_sq_le_sq_mul_sq T
          (fun Z ↦ |fourier (BadF.ind (badSet (coinW a ω) p γ)) Z|) (fun _ ↦ (1 : ℝ))
        simp only [mul_one, sq_abs, one_pow, sum_const, nsmul_eq_mul] at this
        rw [ht]
        linarith
      have hsq : (∑ Z ∈ T, |fourier (BadF.ind (badSet (coinW a ω) p γ)) Z|) ^ 2 ≤ u ^ 2 := by
        refine hcs.trans ?_
        calc t * ∑ Z ∈ T, fourier (BadF.ind (badSet (coinW a ω) p γ)) Z ^ 2 ≤ t * s :=
              mul_le_mul_of_nonneg_left hXω.le ht0
          _ ≤ u ^ 2 := by
              rw [hs, mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith [sq_nonneg u]
      exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hu.le
        two_ne_zero).1 hsq
    unfold BadLow
    intro g
    refine (BadF.sum_lowProj_sq_le _ (m / 100) g).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    linarith
  -- the complement
  have hU : (Set.univ : Set Ω) ⊆ {ω | BadLow (coinW a ω) p γ
      (((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m + u) (m / 100)} ∪
      {ω | s ≤ X (fun j ↦ a j ω)} := by
    intro ω _
    by_cases hc : X (fun j ↦ a j ω) < s
    · exact Or.inl (hgood ω hc)
    · exact Or.inr (not_lt.1 hc)
  have h1 : (1 : ℝ) ≤ μ.real {ω | BadLow (coinW a ω) p γ
      (((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m + u) (m / 100)} +
      μ.real {ω | s ≤ X (fun j ↦ a j ω)} := by
    have := (measureReal_mono hU).trans (measureReal_union_le (μ := μ) _ _)
    simpa using this
  linarith

/-- **Low-degree functions avoid the bad vertices**, for every `p` and every threshold `γ`. -/
theorem badLow_whp {γ : ℝ} (hγ : 0 < γ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 3 ≤
          μ.real {ω | BadLow (coinW a ω) p γ
            ((badSet (coinW a ω) p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100)} := by
  -- the threshold `γ` plays no role: the bound holds for every set of bad vertices that is
  -- determined vertex by vertex by the coins at the vertex
  have _ := hγ
  exact badLow_whp_pow γ 3

end BMW26
