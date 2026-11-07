module

public import BGHKLMM26.Accuracy
public import BGHKLMM26.Opt
public import Background.Sampling

/-!
# The expected value of the algorithm

The coins are read as the cells of `n` independent standard Gaussians
(`BGHKLMM26.Alg.coinMean_alg`), so the algorithm's mean value is an integral over a standard
Gaussian `g` in `ℝⁿ`. Away from a bad event the algorithm follows the ideal rounding for the
vectors `v` of the solver (`BGHKLMM26.Alg.algC_eq_round0`, `BGHKLMM26.Alg.algC_eq_roundL`); the bad
event is that some `|gₖ| > R`, or some sign argument is within `1/U` of `0`, and has probability
at most `n/R² + n/U` (Chebyshev and anti-concentration). Lemmas 3.4 and 3.5 bound the ideal
roundings.
-/

@[expose] public section

namespace BGHKLMM26.Alg

open MeasureTheory ProbabilityTheory Real Factor Gaussian Finset GW
open scoped RealInnerProductSpace

variable {Q₀ : ℕ} {I : Instance}

/-! ### The algorithm reads the first `n` cells -/

theorem gHat_congr {c c' : ℕ → ℕ} {m : ℕ} (h : c m = c' m) :
    gHat Q₀ I c m = gHat Q₀ I c' m := by
  rw [gHat, gHat, h]

theorem xiNext_congr {c c' : ℕ → ℕ} (acc : List ℚ) {m : ℕ} (h : c m = c' m) :
    xiNext Q₀ I c acc m = xiNext Q₀ I c' acc m := by
  rw [xiNext, xiNext, gHat_congr h]

/-- No projections yet. Stated against `[]`: `rfl` between two `xiPre` with different cells would
make the kernel unfold the whole algorithm before reducing `List.range 0`. -/
theorem xiPre_zero (c : ℕ → ℕ) : xiPre Q₀ I c 0 = [] := rfl

theorem xiPre_congr {c c' : ℕ → ℕ} {m : ℕ} (h : ∀ k < m, c k = c' k) :
    xiPre Q₀ I c m = xiPre Q₀ I c' m := by
  induction m with
  | zero => rw [xiPre_zero, xiPre_zero]
  | succ m ih =>
    rw [xiPre_succ, xiPre_succ, ih fun k hk ↦ h k (hk.trans (Nat.lt_succ_self m)),
      xiNext_congr _ (h m (Nat.lt_succ_self m))]

theorem algC_congr {c c' : ℕ → ℕ} (h : ∀ k < I.1, c k = c' k) :
    algC Q₀ I c = algC Q₀ I c' := by
  have hx : xiHat Q₀ I c = xiHat Q₀ I c' := xiPre_congr h
  unfold algC
  rw [hx]

/-- The cells as a function on `ℕ`, `0` past `n`. -/
def extCells (n : ℕ) (u : Fin n → ℕ) (k : ℕ) : ℕ := if h : k < n then u ⟨k, h⟩ else 0

theorem cellOfCoins_eq_chunkVal (B : ℕ) (r : List Bool) (k : ℕ) :
    cellOfCoins B r k = Sampling.chunkVal B r k := by
  rw [cellOfCoins, Sampling.chunkVal, ← List.toFinset_range,
    List.sum_toFinset _ (List.nodup_range)]

/-! ### Coins and Gaussians -/

/-- The value of the algorithm's output, as a function of the cells of the Gaussians. -/
noncomputable def valC (Q₀ : ℕ) (I : Instance) (u : Fin I.1 → ℕ) : ℝ :=
  outputWeight I (algC Q₀ I (extCells I.1 u))

theorem measurable_cells (B n : ℕ) :
    Measurable fun g : EuclideanSpace ℝ (Fin n) ↦ fun k : Fin n ↦ cellOf B (g k) := by
  refine measurable_pi_iff.2 fun k ↦ (measurable_cellOf B).comp ?_
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable

theorem cellsE_eq (g : EuclideanSpace ℝ (Fin I.1)) :
    cellsE Q₀ I g = extCells I.1 (fun k ↦ cellOf (tPar Q₀ I) (g k)) := rfl

/-- **The coins are the cells of Gaussians**: with at least `n T` coins, the mean value of the
algorithm is the integral over a standard Gaussian `g` of the value for the cells of `g`. -/
theorem coinMean_alg {N : ℕ} (hN : I.1 * tPar Q₀ I ≤ N) :
    coinMean N (fun r ↦ outputWeight I (alg Q₀ (I, r))) =
      ∫ g, outputWeight I (algC Q₀ I (cellsE Q₀ I g))
        ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) := by
  set T := tPar Q₀ I
  -- The value depends on the coins through the first `n` chunks.
  have hval : ∀ r : List Bool, outputWeight I (alg Q₀ (I, r)) =
      valC Q₀ I (fun k ↦ Sampling.chunkVal T r k) := by
    intro r
    have hc : ∀ k < I.1, cellOfCoins T r k =
        extCells I.1 (fun k : Fin I.1 ↦ Sampling.chunkVal T r k) k := fun k hk ↦ by
      rw [extCells, dite_eq_left hk, cellOfCoins_eq_chunkVal]
    have halg : alg Q₀ (I, r) = algC Q₀ I (cellOfCoins T r) := rfl
    rw [halg, algC_congr hc]
    rfl
  unfold coinMean
  simp_rw [hval]
  rw [Sampling.sum_chunks hN]
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - I.1 * T) * 2 ^ (I.1 * T) := by
    rw [← pow_add, Nat.sub_add_cancel hN]
  rw [h2, mul_div_mul_left _ _ (by positivity), sum_cells_eq_integral]
  -- From the product measure to the standard Gaussian.
  have hmeas : Measurable fun g : EuclideanSpace ℝ (Fin I.1) ↦
      valC Q₀ I (fun k ↦ cellOf T (g k)) :=
    (measurable_of_countable (valC Q₀ I)).comp (measurable_cells T I.1)
  change _ = ∫ g, valC Q₀ I (fun k ↦ cellOf T (g k)) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1))
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hmeas.aestronglyMeasurable]

/-! ### The bad event -/

theorem totalWeight_nonneg (hI : Valid I) : 0 ≤ totalWeight I :=
  List.sum_nonneg fun a ha ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    exact_mod_cast (hI.1 c hc).2.2

theorem satWeight_nonneg (hI : Valid I) (x : ℕ → Bool) : 0 ≤ satWeight I x :=
  List.sum_nonneg fun a ha ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    split_ifs
    · exact_mod_cast (hI.1 c hc).2.2
    · exact le_rfl

theorem abs_satWeight_le (hI : Valid I) (x : ℕ → Bool) : |satWeight I x| ≤ totalWeight I := by
  have hnn : 0 ≤ satWeight I x := List.sum_nonneg fun a ha ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    split_ifs
    · exact_mod_cast (hI.1 c hc).2.2
    · exact le_rfl
  have hle : satWeight I x ≤ totalWeight I := by
    unfold satWeight totalWeight
    refine List.sum_le_sum fun c hc ↦ ?_
    split_ifs
    · exact le_rfl
    · exact_mod_cast (hI.1 c hc).2.2
  rw [abs_of_nonneg hnn]
  exact hle

/-- **A rounding that agrees off a bad event loses at most the total weight on it.** -/
theorem integral_ge_sub_bad (hI : Valid I) {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsProbabilityMeasure μ] (x y : E → ℕ → Bool) {ι : Type*} [Fintype ι] (B : ι → Set E)
    (hB : ∀ j, MeasurableSet (B j))
    (hagree : ∀ g, (∀ j, g ∉ B j) → ∀ i < I.1, x g i = y g i)
    (hx : Integrable (fun g ↦ satWeight I (x g)) μ)
    (hy : Integrable (fun g ↦ satWeight I (y g)) μ) :
    ∫ g, satWeight I (x g) ∂μ - totalWeight I * ∑ j, μ.real (B j) ≤ ∫ g, satWeight I (y g) ∂μ := by
  have hW := totalWeight_nonneg hI
  have hind : ∀ j, Integrable ((B j).indicator (1 : E → ℝ)) μ :=
    fun j ↦ (integrable_const 1).indicator (hB j)
  have hpt : ∀ g, satWeight I (x g) - totalWeight I * ∑ j, (B j).indicator (1 : E → ℝ) g ≤
      satWeight I (y g) := by
    intro g
    have h := Robust.satWeight_ge hI (x g) (y g)
    have hS0 : 0 ≤ ∑ j, (B j).indicator (1 : E → ℝ) g :=
      Finset.sum_nonneg fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) g
    split_ifs at h with hall
    · nlinarith
    · obtain ⟨j, hj⟩ : ∃ j, g ∈ B j := by
        by_contra hne
        push Not at hne
        exact hall (hagree g hne)
      have h1 : (1 : ℝ) ≤ ∑ j, (B j).indicator (1 : E → ℝ) g := by
        have := Finset.single_le_sum (f := fun j ↦ (B j).indicator (1 : E → ℝ) g)
          (fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) g) (Finset.mem_univ j)
        simpa [Set.indicator_of_mem hj] using this
      nlinarith
  have hint : Integrable (fun g ↦ satWeight I (x g) - totalWeight I *
      ∑ j, (B j).indicator (1 : E → ℝ) g) μ :=
    hx.sub ((integrable_finsetSum _ fun j _ ↦ hind j).const_mul _)
  have hmono := integral_mono hint hy hpt
  rw [integral_sub hx ((integrable_finsetSum _ fun j _ ↦ hind j).const_mul _), integral_const_mul,
    integral_finsetSum _ fun j _ ↦ hind j] at hmono
  simp_rw [integral_indicator_one (hB _)] at hmono
  exact hmono

/-- **Chebyshev for a coordinate**: `P(|gₖ| > R) ≤ 1/R²`. -/
theorem measureReal_coord_gt {n : ℕ} (k : Fin n) {R : ℝ} (hR : 0 < R) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {g | R < |g k|} ≤ 1 / R ^ 2 := by
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single k 1
  have he : ‖e‖ = 1 := by simp [e]
  have hcoord : ∀ g : EuclideanSpace ℝ (Fin n), ⟪e, g⟫ = g k := fun g ↦ by
    simp [e, EuclideanSpace.inner_single_left]
  have hmeas : Measurable fun g : EuclideanSpace ℝ (Fin n) ↦ ⟪e, g⟫ := by fun_prop
  have hS : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  calc (stdGaussian (EuclideanSpace ℝ (Fin n))).real {g | R < |g k|}
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))).real
          ((fun g : EuclideanSpace ℝ (Fin n) ↦ ⟪e, g⟫) ⁻¹' {x | R ≤ |x|}) := by
        refine measureReal_mono (fun g hg ↦ ?_)
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hcoord] at hg ⊢
        exact hg.le
    _ = (gaussianReal 0 1).real {x | R ≤ |x|} := by
        rw [← map_measureReal_apply hmeas hS, map_inner_stdGaussian he]
    _ ≤ 1 / R ^ 2 := Robust.measureReal_le_abs_le hR

/-! ### The parameters -/

section Params

variable (I)

theorem kR_ge : (5 : ℝ) ≤ kPar I := by exact_mod_cast five_le_kPar I

theorem kR_sq_gt : 16 * (lPar I : ℝ) + 4 < (kPar I : ℝ) ^ 2 := by
  exact_mod_cast kPar_sq_gt I

theorem kR_sq_le : (kPar I : ℝ) ^ 2 ≤ 42 * lPar I := by exact_mod_cast kPar_sq_le I

theorem LR_ge : (1 : ℝ) ≤ lPar I := by exact_mod_cast one_le_lPar I

theorem DR_ge : (2 : ℝ) ≤ dPar I := by exact_mod_cast two_le_dPar I

theorem etaR_pos : (0 : ℝ) < etaQ I := by
  have := kR_ge I
  rw [etaQ_cast]
  apply div_pos <;> nlinarith

/-- `1 - η = 2/(k² + 1) ≥ 1/k²`. -/
theorem one_sub_etaR : 1 - (etaQ I : ℝ) = 2 / ((kPar I : ℝ) ^ 2 + 1) := by
  rw [etaQ_cast]
  have := kR_ge I
  field_simp
  ring

theorem tR_le : (tQ I : ℝ) ≤ √(1 - (etaQ I : ℝ)) / 100 := by
  have hk := kR_ge I
  have h1 : 1 / (kPar I : ℝ) ≤ √(1 - (etaQ I : ℝ)) := by
    rw [one_sub_etaR, Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [tQ]
  push_cast
  rw [show (1 : ℝ) / (100 * kPar I) = 1 / kPar I / 100 by field_simp]
  linarith

theorem etaR_pow (L : ℕ) (hL : 16 * (L : ℝ) + 4 < (kPar I : ℝ) ^ 2) :
    (1 / 2 : ℝ) ≤ (etaQ I : ℝ) ^ (4 * L + 1) := by
  have hk := kR_ge I
  set a : ℝ := -(2 / ((kPar I : ℝ) ^ 2 + 1))
  have ha : (etaQ I : ℝ) = 1 + a := by have := one_sub_etaR I; simp only [a]; linarith
  have hH : 0 ≤ 2 + a := by
    simp only [a]
    have : 2 / ((kPar I : ℝ) ^ 2 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hb := one_add_mul_le_pow_of_sq_nonneg (sq_nonneg a) (sq_nonneg (1 + a)) hH (4 * L + 1)
  rw [ha]
  refine le_trans ?_ hb
  simp only [a]
  push_cast
  rw [mul_neg, ← sub_eq_add_neg, le_sub_comm, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

theorem epsR : (epsQ I : ℝ) = 1 / (10 ^ 6 * (kPar I : ℝ) ^ 2 * dPar I) := by
  simp [epsQ]

theorem epsR_pos : (0 : ℝ) < epsQ I := by
  rw [epsR]; have := kR_ge I; have := DR_ge I; positivity

theorem epsR_le_gain :
    (epsQ I : ℝ) ≤ (tQ I : ℝ) / (250 * dPar I * √(lPar I : ℝ)) / 8 := by
  have hk := kR_ge I
  have hD := DR_ge I
  have hL := LR_ge I
  have hsL : 0 < √(lPar I : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsq : √(lPar I : ℝ) ≤ 5 * kPar I := by
    rw [Real.sqrt_le_left (by positivity)]
    have := kR_sq_gt I
    nlinarith
  rw [epsR, tQ]
  push_cast
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (kPar I : ℝ) * dPar I := by positivity
  nlinarith

theorem gain_le_one : (tQ I : ℝ) / (250 * dPar I * √(lPar I : ℝ)) ≤ 1 := by
  have hk := kR_ge I
  have hD := DR_ge I
  have hL := LR_ge I
  have hsL : 1 ≤ √(lPar I : ℝ) := Real.one_le_sqrt.2 hL
  rw [div_le_one (by positivity)]
  have := tQ_le_one (I := I)
  nlinarith

theorem beta_pow : (1 / 2 : ℝ) ^ (2 * lPar I + 1) ≤ 1 / (2 * dPar I) := by
  have hD := DR_ge I
  have h1 : (dPar I : ℝ) ≤ 2 ^ lPar I := by exact_mod_cast dPar_le_pow I
  rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_succ,
    pow_mul]
  have : (2 : ℝ) ^ lPar I ≤ (2 ^ 2) ^ lPar I := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  nlinarith

end Params

/-! ### The machine against the ideal roundings -/

section Machine

/-- The machine's assignment for the Gaussian `g`. -/
noncomputable def yM (Q₀ : ℕ) (I : Instance) (g : EuclideanSpace ℝ (Fin I.1)) (i : ℕ) : Bool :=
  (algC Q₀ I (cellsE Q₀ I g)).getD i false

theorem satWeight_yM (g : EuclideanSpace ℝ (Fin I.1)) :
    satWeight I (yM Q₀ I g) = valC Q₀ I (fun k ↦ cellOf (tPar Q₀ I) (g k)) := rfl

theorem integrable_yM (hI : Valid I) :
    Integrable (fun g ↦ satWeight I (yM Q₀ I g)) (stdGaussian (EuclideanSpace ℝ (Fin I.1))) := by
  have hmeas : Measurable fun g : EuclideanSpace ℝ (Fin I.1) ↦
      valC Q₀ I (fun k ↦ cellOf (tPar Q₀ I) (g k)) :=
    (measurable_of_countable (valC Q₀ I)).comp (measurable_cells (tPar Q₀ I) I.1)
  have e : (fun g : EuclideanSpace ℝ (Fin I.1) ↦ satWeight I (yM Q₀ I g)) =
      fun g ↦ valC Q₀ I (fun k ↦ cellOf (tPar Q₀ I) (g k)) := funext satWeight_yM
  rw [e]
  exact integrable_of_abs_le hmeas fun g ↦ by rw [← satWeight_yM]; exact abs_satWeight_le hI _

theorem measurableSet_coord_gt {n : ℕ} (k : Fin n) (R : ℝ) :
    MeasurableSet {g : EuclideanSpace ℝ (Fin n) | R < |g k|} :=
  measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable)

theorem sum_bad_le {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} (B₁ B₂ : Fin n → Set _)
    {a b : ℝ} (h₁ : ∀ k, μ.real (B₁ k) ≤ a) (h₂ : ∀ i, μ.real (B₂ i) ≤ b) :
    ∑ j : Fin n ⊕ Fin n, μ.real (Sum.elim B₁ B₂ j) ≤ n * a + n * b := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have e1 : ∑ k : Fin n, μ.real (B₁ k) ≤ ∑ _k : Fin n, a := sum_le_sum fun k _ ↦ h₁ k
  have e2 : ∑ i : Fin n, μ.real (B₂ i) ≤ ∑ _i : Fin n, b := sum_le_sum fun i _ ↦ h₂ i
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at e1 e2
  linarith

/-- **The machine against hyperplane rounding.** -/
theorem machine_ge_round0 (hI : Valid I) (hQ : 10 ≤ Q₀) (hb : branch0 Q₀ I = true) :
    ∫ g, satWeight I (round0 (vAlg Q₀ I) g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) -
        totalWeight I * (I.1 * (1 / (rPar Q₀ I : ℝ) ^ 2) + I.1 * (1 / bigU Q₀ I)) ≤
      ∫ g, satWeight I (yM Q₀ I g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) := by
  set v := vAlg Q₀ I
  set μ := stdGaussian (EuclideanSpace ℝ (Fin I.1))
  set B₁ : Fin I.1 → Set (EuclideanSpace ℝ (Fin I.1)) := fun k ↦ {g | (rPar Q₀ I : ℝ) < |g k|}
  set B₂ : Fin I.1 → Set (EuclideanSpace ℝ (Fin I.1)) :=
    fun i ↦ {g | |⟪v i, g⟫ + (fun _ ↦ (0 : ℝ)) g| ≤ 1 / bigU Q₀ I}
  have hR : (0 : ℝ) < rPar Q₀ I := by have := two_le_rPar Q₀ I; positivity
  have hU : (0 : ℝ) ≤ 1 / bigU Q₀ I := by positivity
  have hunit := (vAlg_spec hI hQ).1
  have hB : ∀ j, MeasurableSet (Sum.elim B₁ B₂ j) := by
    rintro (k | i)
    · exact measurableSet_coord_gt k _
    · exact measurableSet_le (by fun_prop) measurable_const
  have hagree : ∀ g, (∀ j, g ∉ Sum.elim B₁ B₂ j) → ∀ i < I.1, round0 v g i = yM Q₀ I g i := by
    intro g hg i hi
    have hg1 : ∀ k, |g k| ≤ rPar Q₀ I := fun k ↦ by
      have := hg (Sum.inl k); simp only [Sum.elim_inl, B₁, Set.mem_ofPred_eq, not_lt] at this
      exact this
    have hg2 : 1 / bigU Q₀ I < |⟪v i, g⟫| := by
      have := hg (Sum.inr ⟨i, hi⟩)
      simp only [Sum.elim_inr, B₂, Set.mem_ofPred_eq, not_le, add_zero] at this
      exact this
    exact (algC_eq_round0 hI hQ hb g hg1 hi hg2).symm
  have hx : Integrable (fun g ↦ satWeight I (round0 v g)) μ :=
    integrable_satWeight_decide I.1 I.2 (A := fun i g ↦ ⟪v i, g⟫) fun i ↦ by fun_prop
  have h := integral_ge_sub_bad hI (μ := μ) (fun g ↦ round0 v g) (yM Q₀ I) (Sum.elim B₁ B₂) hB
    hagree hx (integrable_yM hI)
  have hsum := sum_bad_le (μ := μ) B₁ B₂ (a := 1 / (rPar Q₀ I : ℝ) ^ 2) (b := 1 / bigU Q₀ I)
    (fun k ↦ measureReal_coord_gt k hR)
    (fun i ↦ Robust.measureReal_abs_inner_add_le (hunit i i.2) measurable_const
      (fun _ _ ↦ rfl) hU)
  have hW := totalWeight_nonneg hI
  have := mul_le_mul_of_nonneg_left hsum hW
  linarith

/-- The out-edge directions are orthogonal to `vᵢ`, so the votes do not move along `vᵢ`. -/
theorem fvote_add_smul (hI : Valid I) (hQ : 10 ≤ Q₀) (i : ℕ) (g : EuclideanSpace ℝ (Fin I.1))
    (c : ℝ) :
    fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i (g + c • vAlg Q₀ I i) =
      fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g := by
  have hunit := (vAlg_spec hI hQ).1
  have hρ : ∀ c ∈ windowSet (vAlg Q₀ I) I,
      rho (vAlg Q₀ I) c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25 := by
    intro c hc
    obtain ⟨h1, h2⟩ := window_of_mem _ hc
    nlinarith
  unfold fvote vote
  refine sum_congr rfl fun k _ ↦ ?_
  obtain ⟨-, horth⟩ := outU_spec (vAlg Q₀ I) (windowSet_valid _ hI) hunit hρ i k
  rw [inner_add_right, real_inner_smul_right, horth, mul_zero, add_zero]

/-- **The machine against the shifted rounding.** -/
theorem machine_ge_roundL (hI : Valid I) (hQ : 10 ≤ Q₀) (hb : branch0 Q₀ I = false) :
    ∫ g, satWeight I (roundL (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) (tQ I) g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) -
        totalWeight I * (I.1 * (1 / (rPar Q₀ I : ℝ) ^ 2) + I.1 * (1 / bigU Q₀ I)) ≤
      ∫ g, satWeight I (yM Q₀ I g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) := by
  set v := vAlg Q₀ I
  set T := windowSet v I
  set μ := stdGaussian (EuclideanSpace ℝ (Fin I.1))
  set F : ℕ → EuclideanSpace ℝ (Fin I.1) → ℝ := fun i g ↦ (tQ I : ℝ) * fvote v T (etaQ I) i g
  set B₁ : Fin I.1 → Set (EuclideanSpace ℝ (Fin I.1)) := fun k ↦ {g | (rPar Q₀ I : ℝ) < |g k|}
  set B₂ : Fin I.1 → Set (EuclideanSpace ℝ (Fin I.1)) :=
    fun i ↦ {g | |⟪v i, g⟫ + F i g| ≤ 1 / bigU Q₀ I}
  have hR : (0 : ℝ) < rPar Q₀ I := by have := two_le_rPar Q₀ I; positivity
  have hU : (0 : ℝ) ≤ 1 / bigU Q₀ I := by positivity
  have hunit := (vAlg_spec hI hQ).1
  have hFm : ∀ i, Measurable (F i) := fun i ↦ (measurable_vote _ _ _).const_mul _
  have hB : ∀ j, MeasurableSet (Sum.elim B₁ B₂ j) := by
    rintro (k | i)
    · exact measurableSet_coord_gt k _
    · exact measurableSet_le (continuous_abs.measurable.comp
        ((by fun_prop : Measurable fun g ↦ ⟪v i, g⟫).add (hFm i))) measurable_const
  have hagree : ∀ g, (∀ j, g ∉ Sum.elim B₁ B₂ j) →
      ∀ i < I.1, roundL v T (etaQ I) (tQ I) g i = yM Q₀ I g i := by
    intro g hg i hi
    have hg1 : ∀ k, |g k| ≤ rPar Q₀ I := fun k ↦ by
      have := hg (Sum.inl k); simp only [Sum.elim_inl, B₁, Set.mem_ofPred_eq, not_lt] at this
      exact this
    have hg2 : 1 / bigU Q₀ I < |⟪v i, g⟫ + (tQ I : ℝ) * fvote v T (etaQ I) i g| := by
      have := hg (Sum.inr ⟨i, hi⟩)
      simp only [Sum.elim_inr, B₂, Set.mem_ofPred_eq, not_le, F] at this
      exact this
    exact (algC_eq_roundL hI hQ hb g hg1 hi hg2).symm
  have hx : Integrable (fun g ↦ satWeight I (roundL v T (etaQ I) (tQ I) g)) μ :=
    integrable_satWeight_decide I.1 I.2 (A := fun i g ↦ ⟪v i, g⟫ + F i g)
      fun i ↦ (by fun_prop : Measurable fun g ↦ ⟪v i, g⟫).add (hFm i)
  have h := integral_ge_sub_bad hI (μ := μ) (fun g ↦ roundL v T (etaQ I) (tQ I) g) (yM Q₀ I)
    (Sum.elim B₁ B₂) hB hagree hx (integrable_yM hI)
  have hsum := sum_bad_le (μ := μ) B₁ B₂ (a := 1 / (rPar Q₀ I : ℝ) ^ 2) (b := 1 / bigU Q₀ I)
    (fun k ↦ measureReal_coord_gt k hR)
    (fun i ↦ Robust.measureReal_abs_inner_add_le (hunit i i.2) (hFm i)
      (fun y c ↦ by simp only [F]; rw [fvote_add_smul hI hQ]) hU)
  have hW := totalWeight_nonneg hI
  have := mul_le_mul_of_nonneg_left hsum hW
  linarith

end Machine

/-! ### The mean value for one instance -/

section Mean

theorem sq_le_two_mul_two_pow (Z : ℕ) : Z ^ 2 ≤ 2 * 2 ^ Z := by
  induction Z with
  | zero => norm_num
  | succ m ih =>
    rcases Nat.lt_or_ge m 3 with h | h
    · interval_cases m <;> norm_num
    · have : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
      rw [pow_succ 2 m]
      omega

/-- The ideal roundings get `(α_GW + min(κ, 1) ε) SDP` in both branches. -/
theorem ideal_ge (hI : Valid I) (hQ : 10 ≤ Q₀) :
    (alphaGW + min kappa 1 * epsQ I) * sdp (vAlg Q₀ I) I ≤
      ∫ g, satWeight I (yM Q₀ I g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) +
        totalWeight I * (I.1 * (1 / (rPar Q₀ I : ℝ) ^ 2) + I.1 * (1 / bigU Q₀ I)) := by
  obtain ⟨hunit, -, htri, -⟩ := vAlg_spec hI hQ
  have hs0 := sdp_nonneg (vAlg Q₀ I) hI hunit
  have hε := epsR_pos I
  have hm : min kappa 1 ≤ kappa := min_le_left _ _
  have hm1 : min kappa 1 ≤ 1 := min_le_right _ _
  cases hb : branch0 Q₀ I
  · -- The shifted rounding.
    have hN : sdpOut (vAlg Q₀ I) I ≤ 2 * epsQ I * sdp (vAlg Q₀ I) I := by
      have := (branch0_iff hI hQ).not.1 (by simp [hb])
      push Not at this
      nlinarith
    set r := √(etaQ I : ℝ)
    have hrr : r * r = etaQ I := Real.mul_self_sqrt (etaR_pos I).le
    have hr0 : 0 < r := Real.sqrt_pos.2 (etaR_pos I)
    have hr1 : r < 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (etaR_pos I).le etaQ_lt_one
    have hr2 : r ^ 2 = etaQ I := by rw [sq, hrr]
    have ht : (tQ I : ℝ) ≤ √(1 - r ^ 2) / 100 := by rw [hr2]; exact tR_le I
    have hηL : (1 / 2 : ℝ) ≤ (r * r) ^ (4 * lPar I + 1) := by
      rw [hrr]; exact etaR_pow I _ (kR_sq_gt I)
    have h := roundL_branch (vAlg Q₀ I) hI (maxDegreeLE_dPar hI) hunit (le_refl _) htri hr0 hr1
      tQ_nonneg ht (one_le_lPar I) (beta_pow I) hηL hε.le (epsR_le_gain I) (gain_le_one I) hN
    rw [hrr] at h
    have hmach := machine_ge_roundL hI hQ hb
    have hg : min kappa 1 * epsQ I ≤
        (tQ I : ℝ) / (250 * dPar I * √(lPar I : ℝ)) / 2 := by
      have := epsR_le_gain I
      nlinarith
    have : (alphaGW + min kappa 1 * epsQ I) * sdp (vAlg Q₀ I) I ≤
        (alphaGW + (tQ I : ℝ) / (250 * dPar I * √(lPar I : ℝ)) / 2) * sdp (vAlg Q₀ I) I :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  · -- Hyperplane rounding.
    have hN := (branch0_iff hI hQ).1 hb
    have h := round0_branch (vAlg Q₀ I) hI hunit hN
    have hmach := machine_ge_round0 hI hQ hb
    have : (alphaGW + min kappa 1 * epsQ I) * sdp (vAlg Q₀ I) I ≤
        (alphaGW + kappa * epsQ I) * sdp (vAlg Q₀ I) I :=
      mul_le_mul_of_nonneg_right (by nlinarith) hs0
    linarith

theorem opt_le_totalWeight (hI : Valid I) : opt I ≤ totalWeight I :=
  ciSup_le fun _ ↦ (le_abs_self _).trans (abs_satWeight_le hI _)

theorem one_div_bigV_le : 1 / bigV Q₀ I ≤ 2 / ((zPar I : ℝ) ^ 2 * 2 ^ Q₀) := by
  have h1 : ((zPar I : ℝ)) ^ 2 ≤ 2 * 2 ^ zPar I := by exact_mod_cast sq_le_two_mul_two_pow (zPar I)
  have hZ : (3 : ℝ) ≤ zPar I := by exact_mod_cast three_le_zPar I
  have hV : bigV Q₀ I = 2 ^ zPar I * 2 ^ Q₀ := by rw [bigV, qPar, pow_add]
  rw [hV, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have : (0 : ℝ) < 2 ^ Q₀ := by positivity
  nlinarith

/-- The losses: `24/V + 2 (n/R² + n/U) ≤ 54/(Z² 2^Q₀)`. -/
theorem losses_le (hQ : 10 ≤ Q₀) :
    24 / bigV Q₀ I + 2 * (I.1 * (1 / (rPar Q₀ I : ℝ) ^ 2) + I.1 * (1 / bigU Q₀ I)) ≤
      54 / ((zPar I : ℝ) ^ 2 * 2 ^ Q₀) := by
  have hV1 := one_div_bigV_le (Q₀ := Q₀) (I := I)
  have hZ : (3 : ℝ) ≤ zPar I := by exact_mod_cast three_le_zPar I
  have hn : (I.1 : ℝ) ≤ zPar I := by exact_mod_cast (n_lt_zPar I).le
  have hp : (1 : ℝ) ≤ 2 ^ Q₀ := one_le_pow₀ (by norm_num)
  set Y : ℝ := (zPar I : ℝ) ^ 2 * 2 ^ Q₀ with hY
  have hY0 : 0 < Y := by positivity
  -- `n/R² ≤ 1/Y`.
  have hR : (rPar Q₀ I : ℝ) = Y := by simp [rPar, hY]
  have t1 : (I.1 : ℝ) * (1 / (rPar Q₀ I : ℝ) ^ 2) ≤ 1 / Y := by
    rw [hR, mul_one_div, div_le_div_iff₀ (by positivity) hY0, one_mul, sq]
    have : (zPar I : ℝ) ≤ Y := by
      rw [hY]; nlinarith
    nlinarith
  -- `n/U ≤ 1/V`.
  have t2 : (I.1 : ℝ) * (1 / bigU Q₀ I) ≤ 1 / bigV Q₀ I := by
    have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
    have hU := bigU_ge (Q₀ := Q₀) (I := I) hQ
    have hnV := n_le_bigV (Q₀ := Q₀) (I := I)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : bigV Q₀ I ^ 2 ≤ bigV Q₀ I ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have e24 : 24 / bigV Q₀ I = 24 * (1 / bigV Q₀ I) := by ring
  have e54 : (54 : ℝ) / Y = 24 * (2 / Y) + 2 * (1 / Y) + 2 * (2 / Y) := by ring
  rw [e24, e54]
  have h2 : 1 / bigV Q₀ I ≤ 2 / Y := hV1
  linarith

/-- The combination of the bounds, in real arithmetic: from `(α + mε) SDP ≤ E + W err`,
`SDP ≥ opt - 6W/V`, `W ≤ 2 opt` and losses `24/V + 2 err ≤ G ≤ mε/2`, `(α + G) opt ≤ E`. -/
theorem mean_combine {a me G o s W V e E : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hme0 : 0 ≤ me)
    (hme1 : me ≤ 1) (hV : 0 < V) (hW0 : 0 ≤ W) (hWo : W ≤ 2 * o) (he : 0 ≤ e)
    (hid : (a + me) * s ≤ E + W * e) (hs : o - 6 * W / V ≤ s) (hfin : 24 / V + 2 * e ≤ G)
    (hG : 2 * G ≤ me) : (a + G) * o ≤ E := by
  have ho : 0 ≤ o := by linarith
  have hs1 : (a + me) * (o - 6 * W / V) ≤ (a + me) * s :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  have hx : 6 * W / V ≤ 12 * o / V := by rw [div_le_div_iff_of_pos_right hV]; linarith
  have hx0 : 0 ≤ 6 * W / V := by positivity
  have hs2 : (a + me) * (6 * W / V) ≤ 2 * (12 * o / V) :=
    mul_le_mul (by linarith) hx hx0 (by norm_num)
  have hs3 : W * e ≤ 2 * o * e := mul_le_mul_of_nonneg_right hWo he
  have hfin' : o * (24 / V + 2 * e) ≤ o * G := mul_le_mul_of_nonneg_left hfin ho
  have e1 : 2 * (12 * o / V) + 2 * o * e = o * (24 / V + 2 * e) := by ring
  have e2 : (a + me) * (o - 6 * W / V) = (a + me) * o - (a + me) * (6 * W / V) := by ring
  have h2 := mul_le_mul_of_nonneg_right hG ho
  have e3 : (a + G) * o + o * G = a * o + (2 * G) * o := by ring
  have e4 : (a + me) * o = a * o + me * o := by ring
  linarith

theorem etaS_cast : (etaS Q₀ I : ℝ) = 1 / bigV Q₀ I := by simp [etaS, bigV]

theorem gammaS_cast_le (hW : 0 < totalWeight I) :
    (gammaS Q₀ I : ℝ) ≤ totalWeight I / bigV Q₀ I ∧ (gammaS Q₀ I : ℝ) ≤ 1 / bigV Q₀ I := by
  have hwt : wTot I ≠ 0 := by
    intro h
    have h' := wTot_cast I
    rw [h, Rat.cast_zero] at h'
    linarith
  have hg : (gammaS Q₀ I : ℝ) = ((min (wTot I) 1 : ℚ) : ℝ) / bigV Q₀ I := by
    rw [gammaS, ite_eq_right hwt, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hV : 0 ≤ bigV Q₀ I := by positivity
  rw [hg]
  refine ⟨div_le_div_of_nonneg_right ?_ hV, div_le_div_of_nonneg_right ?_ hV⟩
  · rw [← wTot_cast]; exact_mod_cast min_le_left _ _
  · exact_mod_cast min_le_right _ _

/-- The SDP value: `SDP ≥ opt - 6 W / V`. -/
theorem sdp_ge (hI : Valid I) (hQ : 10 ≤ Q₀) (hW : 0 < totalWeight I) :
    opt I - 6 * totalWeight I / bigV Q₀ I ≤ sdp (vAlg Q₀ I) I := by
  have hsdp := (vAlg_spec hI hQ).2.2.2
  obtain ⟨hγW, hγ1⟩ := gammaS_cast_le (Q₀ := Q₀) hW
  have h5 : 2 * ((etaS Q₀ I : ℝ) + gammaS Q₀ I) + tauS Q₀ I ≤ 5 / bigV Q₀ I := by
    rw [etaS_cast, tauS_cast]
    have : (5 : ℝ) / bigV Q₀ I = 2 * (1 / bigV Q₀ I + 1 / bigV Q₀ I) + 1 / bigV Q₀ I := by
      ring
    rw [this]; linarith
  have h1 := mul_le_mul_of_nonneg_right h5 (totalWeight_nonneg hI)
  have e1 : 5 / bigV Q₀ I * totalWeight I = 5 * totalWeight I / bigV Q₀ I := by ring
  have e2 : (6 : ℝ) * totalWeight I / bigV Q₀ I =
      totalWeight I / bigV Q₀ I + 5 * totalWeight I / bigV Q₀ I := by ring
  rw [e2]
  linarith

theorem epsQ_le_one : (epsQ I : ℝ) ≤ 1 := by
  rw [epsR, div_le_one (by have := kR_ge I; have := DR_ge I; positivity)]
  have hk := kR_ge I
  have hD := DR_ge I
  have h1 : (1 : ℝ) ≤ (kPar I : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (kPar I : ℝ) ^ 2 * dPar I := by
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (kPar I : ℝ) ^ 2 * dPar I := mul_le_mul h1 (by linarith) (by norm_num) (by linarith)
  have : (10 : ℝ) ^ 6 * (kPar I : ℝ) ^ 2 * dPar I = 10 ^ 6 * ((kPar I : ℝ) ^ 2 * dPar I) := by
    ring
  rw [this]
  linarith

/-- `m ε ≥ 2 m / (84 · 10⁶ L D)`. -/
theorem two_gain_le (m : ℝ) (hm : 0 ≤ m) :
    2 * (m / (84 * 10 ^ 6 * lPar I * dPar I)) ≤ m * epsQ I := by
  rw [epsR]
  have hk := kR_sq_le I
  have hk5 := kR_ge I
  have hL := LR_ge I
  have hD := DR_ge I
  rw [mul_one_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (kPar I : ℝ) ^ 2 * dPar I ≤ 42 * lPar I * dPar I :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * m * 10 ^ 6 by positivity)
  have e1 : 2 * m * (10 ^ 6 * (kPar I : ℝ) ^ 2 * dPar I) =
      2 * m * 10 ^ 6 * ((kPar I : ℝ) ^ 2 * dPar I) := by ring
  have e2 : m * (84 * 10 ^ 6 * (lPar I : ℝ) * dPar I) =
      2 * m * 10 ^ 6 * (42 * lPar I * dPar I) := by ring
  rw [e1, e2]
  exact h2

/-- The losses are at most the gain: `54/(Z² 2^Q₀) ≤ m / (84 · 10⁶ L D)`. -/
theorem losses_le_gain {m : ℝ} (hQ' : (54 * 84 * 10 ^ 6 : ℝ) ≤ m * 2 ^ Q₀) :
    54 / ((zPar I : ℝ) ^ 2 * 2 ^ Q₀) ≤ m / (84 * 10 ^ 6 * lPar I * dPar I) := by
  have hZpos : (0 : ℝ) < zPar I := by
    exact_mod_cast (show 0 < zPar I by have := three_le_zPar I; omega)
  have hL := LR_ge I
  have hD := DR_ge I
  have hZ : (lPar I : ℝ) * dPar I ≤ (zPar I : ℝ) ^ 2 := by
    have h1 : (lPar I : ℝ) ≤ zPar I := by exact_mod_cast lPar_le_zPar I
    have h2 : (dPar I : ℝ) ≤ zPar I := by exact_mod_cast dPar_le I
    rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [div_le_div_iff₀ (mul_pos (pow_pos hZpos 2) (by positivity)) (by positivity)]
  calc (54 : ℝ) * (84 * 10 ^ 6 * lPar I * dPar I) = (54 * 84 * 10 ^ 6) * (lPar I * dPar I) := by
        ring
    _ ≤ (m * 2 ^ Q₀) * (zPar I : ℝ) ^ 2 := mul_le_mul hQ' hZ (by positivity) (by positivity)
    _ = m * ((zPar I : ℝ) ^ 2 * 2 ^ Q₀) := by ring

/-- **The mean value for one instance**: for `Q₀ ≥ 10` with `54 · 84 · 10⁶ ≤ min(κ, 1) 2^Q₀`,
the machine gets `(α_GW + min(κ, 1) / (84 · 10⁶ L D)) opt` on average over the Gaussians. -/
theorem mean_ge (hI : Valid I) (hQ : 10 ≤ Q₀)
    (hQ' : (54 * 84 * 10 ^ 6 : ℝ) ≤ min kappa 1 * 2 ^ Q₀) :
    (alphaGW + min kappa 1 / (84 * 10 ^ 6 * lPar I * dPar I)) * opt I ≤
      ∫ g, satWeight I (yM Q₀ I g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) := by
  have hm0 : 0 < min kappa 1 := lt_min kappa_pos one_pos
  have hm1 : min kappa 1 ≤ 1 := min_le_right _ _
  have hW0 := totalWeight_nonneg hI
  have hopt : totalWeight I / 2 ≤ opt I := opt_ge_half hI
  have hoptW : opt I ≤ totalWeight I := opt_le_totalWeight hI
  rcases eq_or_lt_of_le hW0 with hW | hW
  · -- No weight: `opt = 0`.
    have : opt I = 0 := le_antisymm (by linarith) (by linarith)
    rw [this, mul_zero]
    exact integral_nonneg fun g ↦ satWeight_nonneg hI _
  have hε1 : min kappa 1 * epsQ I ≤ 1 := by
    have := mul_le_mul hm1 (epsQ_le_one (I := I)) (epsR_pos I).le zero_le_one
    linarith
  have hfin := (losses_le (Q₀ := Q₀) (I := I) hQ).trans (losses_le_gain hQ')
  have herr0 : (0 : ℝ) ≤ I.1 * (1 / (rPar Q₀ I : ℝ) ^ 2) + I.1 * (1 / bigU Q₀ I) := by
    positivity
  exact mean_combine alphaGW_pos.le alphaGW_lt_one
    (mul_nonneg hm0.le (epsR_pos I).le) hε1 (by positivity) hW0 (by linarith) herr0
    (ideal_ge hI hQ) (sdp_ge hI hQ hW) hfin (two_gain_le _ hm0.le)

end Mean

/-! ### In terms of the degree bound `d` -/

section Degree

theorem dPar_le_of_maxDegreeLE {d : ℕ} (hd : 2 ≤ d) (hdeg : MaxDegreeLE I d) : dPar I ≤ d :=
  max_le hd (foldr_max_le_nat fun x hx ↦ by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact hdeg v)

theorem clog_le_log {d : ℕ} (hd : 2 ≤ d) : (Nat.clog 2 d : ℝ) ≤ 3 * Real.log d := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := by positivity
  have hlog2 := Real.log_two_gt_d9
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have h1 : ((Nat.clog 2 d).pred : ℝ) * Real.log 2 < Real.log d := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by positivity) (by exact_mod_cast h)
  have h2 : (Nat.clog 2 d : ℝ) ≤ (Nat.clog 2 d).pred + 1 := by
    have : Nat.clog 2 d ≤ (Nat.clog 2 d).pred + 1 := by rw [Nat.pred_eq_sub_one]; omega
    exact_mod_cast this
  have h3 : ((Nat.clog 2 d).pred : ℝ) ≤ Real.log d / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; exact h1.le
  have h4 : Real.log d / Real.log 2 ≤ 3 / 2 * Real.log d := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 : (1 : ℝ) ≤ 3 / 2 * Real.log d := by nlinarith
  linarith

/-- **The algorithm's mean value** [BGHKLMM26, Theorem 3.1]: for `Q₀ ≥ 10` with
`54 · 84 · 10⁶ ≤ min(κ, 1) 2^Q₀` and at least `n T` coins, on instances of degree at most `d ≥ 2`
the algorithm gets `(α_GW + c / (d log d)) opt` on average, with `c = min(κ, 1) / (252 · 10⁶)`. -/
theorem alg_mean (hQ : 10 ≤ Q₀) (hQ' : (54 * 84 * 10 ^ 6 : ℝ) ≤ min kappa 1 * 2 ^ Q₀)
    {N : ℕ} (hN : I.1 * tPar Q₀ I ≤ N) (hI : Valid I) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : MaxDegreeLE I d) :
    (alphaGW + min kappa 1 / (252 * 10 ^ 6) / (d * Real.log d)) * opt I ≤
      coinMean N (fun r ↦ outputWeight I (alg Q₀ (I, r))) := by
  rw [coinMean_alg hN]
  have hmean := mean_ge hI hQ hQ'
  have e : ∫ g, outputWeight I (algC Q₀ I (cellsE Q₀ I g))
      ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) =
      ∫ g, satWeight I (yM Q₀ I g) ∂stdGaussian (EuclideanSpace ℝ (Fin I.1)) := rfl
  rw [e]
  refine le_trans ?_ hmean
  have hopt0 : 0 ≤ opt I := le_trans (by linarith [totalWeight_nonneg hI]) (opt_ge_half hI)
  refine mul_le_mul_of_nonneg_right ?_ hopt0
  have hm0 : 0 < min kappa 1 := lt_min kappa_pos one_pos
  have hL := LR_ge I
  have hD := DR_ge I
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 < Real.log d := Real.log_pos (by linarith)
  -- `L D ≤ 3 d log d`.
  have hDd : (dPar I : ℝ) ≤ d := by exact_mod_cast dPar_le_of_maxDegreeLE hd hdeg
  have hLd : (lPar I : ℝ) ≤ 3 * Real.log d := by
    have : lPar I ≤ Nat.clog 2 d := Nat.clog_mono_right _ (dPar_le_of_maxDegreeLE hd hdeg)
    exact le_trans (by exact_mod_cast this) (clog_le_log hd)
  have hLD : (lPar I : ℝ) * dPar I ≤ 3 * Real.log d * d :=
    mul_le_mul hLd hDd (by positivity) (by positivity)
  have : min kappa 1 / (252 * 10 ^ 6) / (d * Real.log d) ≤
      min kappa 1 / (84 * 10 ^ 6 * lPar I * dPar I) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 84 * 10 ^ 6 * (lPar I : ℝ) * dPar I ≤ 252 * 10 ^ 6 * (d * Real.log d) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h1 hm0.le
  linarith

end Degree

end BGHKLMM26.Alg
