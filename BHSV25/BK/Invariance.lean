module

public import BHSV25.BK.InvarianceLindeberg
public import BHSV25.BK.InvarianceMollify

/-!
# The smoothed invariance principle for Lipschitz test functions

Copied from `BGHKLMM26/RobustMIS/Invariance.lean` (papers do not import each other), with the
namespace changed to `BHSV25.BK.Aint`, the comparison made between the products of any two good
laws (instead of the cube and Gaussian space), and the influence hypothesis only on the
influences in degree `≤ n` (`invariance_laws`).

Qualitative form of O'Donnell's Corollary 11.69 / [MOO10] for a **pair** of smoothed polynomials:
for fixed `r ∈ (0, 1)`, `M`, `K` and `ε > 0` there are `n` and `τ > 0` such that for good laws
`ν₁, ν₂`, coefficient vectors `c, e` with `∑ c² ≤ M`, `∑ e² ≤ M` and all influences in degree
`≤ n` at most `τ`, and every `K`-Lipschitz `Ψ : ℝ² → ℝ`,
`|E Ψ(T_r p(X), T_r q(X)) - E Ψ(T_r p(Y), T_r q(Y))| ≤ ε` for `X ∼ ν₁^{⊗R}`, `Y ∼ ν₂^{⊗R}`.

Proof: truncate at degree `n` (`truncC`): `E|T_r p - (T_r p)^{≤n}| ≤ (δ + r^{2(n+1)} M/δ)/2`
under both laws (`Invariance.integral_abs_mlEval_le`), costing `K` times this per polynomial
(`Invariance.abs_integral_lip_sub`); mollify `Ψ` (`mollify`, cost `2Kη` per side); apply
`lindeberg_laws` to the truncations, with `Infᵢ^{3/2} ≤ √τ Infᵢ`, `∑ᵢ Infᵢ ≤ n M`
(`Invariance.sum_inflC_le`) and `Infᵢ((T_r c)^{≤n}) ≤ Infᵢ(c^{≤n})`. Choose
`η = δ = ε/(12(|K|+1))`, then `n`, then `τ`.
-/

@[expose] public section

namespace BHSV25.BK.Aint.Invariance

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

lemma truncC_deg (d : ℕ) (c : Cube (Fin R) → ℝ) : ∀ s, d < sdeg s → truncC d c s = 0 :=
  fun s hs => by unfold truncC; rw [ite_eq_right_iff.2 fun h => absurd h (by omega)]

lemma mlEval_sub (a b : Cube (Fin R) → ℝ) (x : Fin R → ℝ) :
    mlEval (a - b) x = mlEval a x - mlEval b x := by
  unfold mlEval
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.sub_apply]; ring

lemma sum_sq_smoothC_sub_truncC_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (d : ℕ)
    (c : Cube (Fin R) → ℝ) :
    ∑ s, (smoothC r c - truncC d (smoothC r c)) s ^ 2 ≤ r ^ (2 * (d + 1)) * ∑ s, c s ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  simp only [Pi.sub_apply, truncC, smoothC]
  split_ifs with h
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rw [sub_zero, mul_pow, ← pow_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_of_le_one hr0 hr1 (by omega)

lemma sum_sq_truncC_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (d : ℕ) (c : Cube (Fin R) → ℝ) :
    ∑ s, truncC d (smoothC r c) s ^ 2 ≤ ∑ s, c s ^ 2 := by
  refine Finset.sum_le_sum fun s _ => ?_
  simp only [truncC, smoothC]
  split_ifs
  · rw [mul_pow]
    calc (r ^ sdeg s) ^ 2 * c s ^ 2 ≤ 1 * c s ^ 2 := by
          gcongr; exact pow_le_one₀ (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1)
      _ = c s ^ 2 := one_mul _
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

/-- Smoothing does not increase the low-degree influences. -/
lemma inflC_truncC_smoothC_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (d : ℕ)
    (c : Cube (Fin R) → ℝ) (i : Fin R) :
    inflC (truncC d (smoothC r c)) i ≤ inflC (truncC d c) i := by
  refine Finset.sum_le_sum fun s _ => ?_
  simp only [truncC, smoothC]
  split_ifs
  · rw [mul_pow]
    calc (r ^ sdeg s) ^ 2 * c s ^ 2 ≤ 1 * c s ^ 2 := by
          gcongr; exact pow_le_one₀ (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1)
      _ = c s ^ 2 := one_mul _
  · simp

lemma inflC_nonneg (c : Cube (Fin R) → ℝ) (i : Fin R) : 0 ≤ inflC c i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `∑ᵢ Infᵢ = ∑_S |S| c_S² ≤ d ∑ c²` in degree `≤ d`. -/
lemma sum_inflC_le {d : ℕ} (c : Cube (Fin R) → ℝ) (hc : ∀ s, d < sdeg s → c s = 0) :
    ∑ i, inflC c i ≤ d * ∑ s, c s ^ 2 := by
  have e : ∑ i, inflC c i = ∑ s, (sdeg s : ℝ) * c s ^ 2 := by
    unfold inflC
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases h : d < sdeg s
  · rw [hc s h]; simp
  · gcongr
    exact_mod_cast (not_lt.1 h)

lemma rpow32_le {x σ : ℝ} (hx : 0 ≤ x) (hσ : 0 ≤ σ) (hxσ : x ≤ σ ^ 2) :
    x ^ (3 / 2 : ℝ) ≤ σ * x := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num)]; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow, mul_comm σ]
    gcongr
    calc √x ≤ √(σ ^ 2) := Real.sqrt_le_sqrt hxσ
      _ = σ := Real.sqrt_sq hσ

/-! ### Errors under a product of good laws -/

lemma integral_abs_mlEval_le (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    (t : Cube (Fin R) → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, |mlEval t x| ∂Measure.pi ν ≤ (δ + (∑ s, t s ^ 2) / δ) / 2 := by
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).prob
  have i1 := Lindeberg.integrable_abs_mlEval_pow ν hν t (k := 1) (by norm_num)
  have i2 := Lindeberg.integrable_abs_mlEval_pow ν hν t (k := 2) (by norm_num)
  have m2 : ∫ x, |mlEval t x| ^ 2 ∂Measure.pi ν = ∑ s, t s ^ 2 := by
    have := integral_mlEval_mul_pi ν hν t t
    rw [show ∑ s, t s ^ 2 = ∑ s, t s * t s from Finset.sum_congr rfl fun s _ => by ring, ← this]
    congr 1; funext x; rw [sq_abs]; ring
  have hb : Integrable (fun x => (δ + |mlEval t x| ^ 2 / δ) / 2) (Measure.pi ν) :=
    ((integrable_const δ).add (i2.div_const δ)).div_const 2
  calc ∫ x, |mlEval t x| ∂Measure.pi ν ≤ ∫ x, (δ + |mlEval t x| ^ 2 / δ) / 2 ∂Measure.pi ν := by
        refine integral_mono (by simpa using i1) hb fun x => ?_
        obtain ⟨a, ha⟩ : ∃ a, a = |mlEval t x| := ⟨_, rfl⟩
        simp only
        rw [← ha]
        rw [show (δ + a ^ 2 / δ) / 2 = (δ ^ 2 + a ^ 2) / (2 * δ) by field_simp,
          le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (a - δ)]
    _ = (δ + (∑ s, t s ^ 2) / δ) / 2 := by
        rw [integral_div, integral_add (integrable_const δ) (i2.div_const δ), integral_const,
          integral_div, m2]
        simp

lemma abs_integral_lip_sub (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    {Ψ : ℝ → ℝ → ℝ} {K : ℝ} (hΨ : LipPair Ψ K) (a b a' b' : Cube (Fin R) → ℝ) :
    |∫ x, Ψ (mlEval a x) (mlEval b x) ∂Measure.pi ν -
        ∫ x, Ψ (mlEval a' x) (mlEval b' x) ∂Measure.pi ν| ≤
      K * (∫ x, |mlEval (a - a') x| ∂Measure.pi ν + ∫ x, |mlEval (b - b') x| ∂Measure.pi ν) := by
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).prob
  have h1 := Lindeberg.integrable_F ν hν hΨ a b
  have h2 := Lindeberg.integrable_F ν hν hΨ a' b'
  have ia := Lindeberg.integrable_abs_mlEval_pow ν hν (a - a') (k := 1) (by norm_num)
  have ib := Lindeberg.integrable_abs_mlEval_pow ν hν (b - b') (k := 1) (by norm_num)
  simp only [pow_one] at ia ib
  rw [← integral_sub h1 h2, ← integral_add ia ib, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (h1.sub h2).abs
    ((ia.add ib).const_mul K) fun x => ?_)
  rw [mlEval_sub, mlEval_sub]
  exact hΨ _ _ _ _

lemma abs_integral_sub_le_const (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    {f g : (Fin R → ℝ) → ℝ} (hf : Integrable f (Measure.pi ν)) (hg : Integrable g (Measure.pi ν))
    {C : ℝ} (h : ∀ x, |f x - g x| ≤ C) :
    |∫ x, f x ∂Measure.pi ν - ∫ x, g x ∂Measure.pi ν| ≤ C := by
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => (hν i).prob
  rw [← integral_sub hf hg]
  have := norm_integral_le_of_norm_le_const (μ := Measure.pi ν) (C := C)
    (f := fun x => f x - g x) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa using this

end BHSV25.BK.Aint.Invariance

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

/-- **Smoothed invariance principle** for pairs and Lipschitz test functions, between the
products of two good laws, with the influence hypothesis only in degree `≤ n`. -/
theorem invariance_laws {r M K ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ τ > 0, ∀ ν₁ ν₂ : Measure ℝ, GoodLaw ν₁ → GoodLaw ν₂ →
      ∀ (R : ℕ) (c e : Cube (Fin R) → ℝ), ∑ s, c s ^ 2 ≤ M → ∑ s, e s ^ 2 ≤ M →
      (∀ i, inflC (truncC n c) i ≤ τ) → (∀ i, inflC (truncC n e) i ≤ τ) →
      ∀ Ψ : ℝ → ℝ → ℝ, LipPair Ψ K →
        |∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
            ∂Measure.pi (fun _ : Fin R => ν₁) -
          ∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
            ∂Measure.pi (fun _ : Fin R => ν₂)| ≤ ε := by
  obtain ⟨A, hA⟩ : ∃ A, A = |K| + 1 := ⟨_, rfl⟩
  obtain ⟨Mp, hMp⟩ : ∃ Mp, Mp = |M| + 1 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  have hMp0 : 0 < Mp := by rw [hMp]; positivity
  have hKA : |K| ≤ A := by rw [hA]; linarith
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (12 * A) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε * η / (12 * A * Mp) by positivity) hr1
  obtain ⟨B, hB⟩ : ∃ B, B = 100 * |K| / η ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨X, hX⟩ : ∃ X, X = 20 * B * 9 ^ n * n * Mp := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ε / (3 * (X + 1)) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  refine ⟨n, σ ^ 2, by positivity, ?_⟩
  intro ν₁ ν₂ h₁ h₂ R c e hc he hic hie Ψ hΨ
  have hΨ' : LipPair Ψ |K| := fun a b a' b' =>
    (hΨ a b a' b').trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  obtain ⟨Φ, hΦK, hΦB, hΦΨ⟩ := mollify (abs_nonneg K) hη0 Ψ hΨ'
  rw [← hB] at hΦB
  obtain ⟨c', hc'⟩ : ∃ c', c' = truncC n (smoothC r c) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e', e' = truncC n (smoothC r e) := ⟨_, rfl⟩
  have hr0' := hr0.le
  have hr1' := hr1.le
  have hcM : ∑ s, c s ^ 2 ≤ Mp := by rw [hMp]; linarith [le_abs_self M]
  have heM : ∑ s, e s ^ 2 ≤ Mp := by rw [hMp]; linarith [le_abs_self M]
  have hS : ∀ i : Fin R, GoodLaw ((fun _ => ν₁) i) := fun _ => h₁
  have hG : ∀ i : Fin R, GoodLaw ((fun _ => ν₂) i) := fun _ => h₂
  -- the truncation error
  have hW : r ^ (2 * (n + 1)) * Mp ≤ ε * η / (12 * A) := by
    have h1 : r ^ (2 * (n + 1)) ≤ r ^ n := pow_le_pow_of_le_one hr0' hr1' (by omega)
    calc r ^ (2 * (n + 1)) * Mp ≤ r ^ n * Mp := by gcongr
      _ ≤ ε * η / (12 * A * Mp) * Mp := by gcongr
      _ = ε * η / (12 * A) := by field_simp
  have tc : ∑ s, (smoothC r c - c') s ^ 2 ≤ r ^ (2 * (n + 1)) * Mp := by
    rw [hc']
    exact (Invariance.sum_sq_smoothC_sub_truncC_le hr0' hr1' n c).trans (by gcongr)
  have te : ∑ s, (smoothC r e - e') s ^ 2 ≤ r ^ (2 * (n + 1)) * Mp := by
    rw [he']
    exact (Invariance.sum_sq_smoothC_sub_truncC_le hr0' hr1' n e).trans (by gcongr)
  have tbound : ∀ ν : Fin R → Measure ℝ, (∀ i, GoodLaw (ν i)) →
      |K| * (∫ x, |mlEval (smoothC r c - c') x| ∂Measure.pi ν +
        ∫ x, |mlEval (smoothC r e - e') x| ∂Measure.pi ν) ≤ ε / 6 := by
    intro ν hν
    have i1 := Invariance.integral_abs_mlEval_le ν hν (smoothC r c - c') hη0
    have i2 := Invariance.integral_abs_mlEval_le ν hν (smoothC r e - e') hη0
    have j1 : (∑ s, (smoothC r c - c') s ^ 2) / η ≤ ε / (12 * A) := by
      rw [div_le_iff₀ hη0]
      calc _ ≤ r ^ (2 * (n + 1)) * Mp := tc
        _ ≤ ε * η / (12 * A) := hW
        _ = ε / (12 * A) * η := by ring
    have j2 : (∑ s, (smoothC r e - e') s ^ 2) / η ≤ ε / (12 * A) := by
      rw [div_le_iff₀ hη0]
      calc _ ≤ r ^ (2 * (n + 1)) * Mp := te
        _ ≤ ε * η / (12 * A) := hW
        _ = ε / (12 * A) * η := by ring
    have hsum : ∫ x, |mlEval (smoothC r c - c') x| ∂Measure.pi ν +
        ∫ x, |mlEval (smoothC r e - e') x| ∂Measure.pi ν ≤ η + ε / (12 * A) := by
      linarith
    have hnn : 0 ≤ ∫ x, |mlEval (smoothC r c - c') x| ∂Measure.pi ν +
        ∫ x, |mlEval (smoothC r e - e') x| ∂Measure.pi ν :=
      add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
    calc |K| * (∫ x, |mlEval (smoothC r c - c') x| ∂Measure.pi ν +
          ∫ x, |mlEval (smoothC r e - e') x| ∂Measure.pi ν) ≤ A * (η + ε / (12 * A)) :=
          mul_le_mul hKA hsum hnn hA0.le
      _ = ε / 6 := by rw [hη]; field_simp; ring
  have hmoll : 2 * |K| * η ≤ ε / 6 := by
    calc 2 * |K| * η ≤ 2 * A * η := by gcongr
      _ = ε / 6 := by rw [hη]; field_simp; ring
  have T1 : |∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
        ∂Measure.pi (fun _ : Fin R => ν₁) -
      ∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁)| ≤ ε / 6 := by
    exact (Invariance.abs_integral_lip_sub _ hS hΨ' _ _ _ _).trans (tbound _ hS)
  have T2 : |∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁) -
      ∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁)| ≤ ε / 6 := by
    refine (Invariance.abs_integral_sub_le_const _ hS (Lindeberg.integrable_F _ hS hΨ' c' e')
      (Lindeberg.integrable_F _ hS hΦK c' e') fun x => ?_).trans hmoll
    rw [abs_sub_comm]; exact hΦΨ _ _
  have T3 : |∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁) -
      ∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂)| ≤ ε / 3 := by
    refine (lindeberg_laws c' e' (hc' ▸ Invariance.truncC_deg n _)
      (he' ▸ Invariance.truncC_deg n _) Φ hΦK hΦB h₁ h₂).trans ?_
    have hc'M : ∑ s, c' s ^ 2 ≤ Mp := by
      rw [hc']; exact (Invariance.sum_sq_truncC_le hr0' hr1' n c).trans hcM
    have he'M : ∑ s, e' s ^ 2 ≤ Mp := by
      rw [he']; exact (Invariance.sum_sq_truncC_le hr0' hr1' n e).trans heM
    have ic : ∀ i, inflC c' i ≤ σ ^ 2 := fun i => by
      rw [hc']; exact (Invariance.inflC_truncC_smoothC_le hr0' hr1' n c i).trans (hic i)
    have ie : ∀ i, inflC e' i ≤ σ ^ 2 := fun i => by
      rw [he']; exact (Invariance.inflC_truncC_smoothC_le hr0' hr1' n e i).trans (hie i)
    have sc : ∑ i, inflC c' i ≤ n * Mp :=
      (Invariance.sum_inflC_le c' (hc' ▸ Invariance.truncC_deg n _)).trans (by gcongr)
    have se : ∑ i, inflC e' i ≤ n * Mp :=
      (Invariance.sum_inflC_le e' (he' ▸ Invariance.truncC_deg n _)).trans (by gcongr)
    have hsum : ∑ i, (inflC c' i ^ (3 / 2 : ℝ) + inflC e' i ^ (3 / 2 : ℝ)) ≤
        σ * (2 * (n * Mp)) := by
      calc ∑ i, (inflC c' i ^ (3 / 2 : ℝ) + inflC e' i ^ (3 / 2 : ℝ))
          ≤ ∑ i, (σ * inflC c' i + σ * inflC e' i) :=
            Finset.sum_le_sum fun i _ => add_le_add
              (Invariance.rpow32_le (Invariance.inflC_nonneg _ _) hσ0.le (ic i))
              (Invariance.rpow32_le (Invariance.inflC_nonneg _ _) hσ0.le (ie i))
        _ = σ * (∑ i, inflC c' i + ∑ i, inflC e' i) := by
            rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
        _ ≤ σ * (n * Mp + n * Mp) := by gcongr
        _ = σ * (2 * (n * Mp)) := by ring
    have hXσ : X * σ ≤ ε / 3 := by
      have e1 : X * σ = ε / 3 * (X / (X + 1)) := by rw [hσ]; field_simp
      rw [e1]
      have : X / (X + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      have : 0 ≤ ε / 3 := by positivity
      nlinarith
    calc 10 * B * 9 ^ n * ∑ i, (inflC c' i ^ (3 / 2 : ℝ) + inflC e' i ^ (3 / 2 : ℝ))
        ≤ 10 * B * 9 ^ n * (σ * (2 * (n * Mp))) := by gcongr
      _ = X * σ := by rw [hX]; ring
      _ ≤ ε / 3 := hXσ
  have T4 : |∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂) -
      ∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂)| ≤ ε / 6 := by
    exact (Invariance.abs_integral_sub_le_const _ hG (Lindeberg.integrable_F _ hG hΦK c' e')
      (Lindeberg.integrable_F _ hG hΨ' c' e') fun x => hΦΨ _ _).trans hmoll
  have T5 : |∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂) -
      ∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
        ∂Measure.pi (fun _ : Fin R => ν₂)| ≤ ε / 6 := by
    rw [abs_sub_comm]
    exact (Invariance.abs_integral_lip_sub _ hG hΨ' _ _ _ _).trans (tbound _ hG)
  set P1 := ∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
    ∂Measure.pi (fun _ : Fin R => ν₁)
  set P2 := ∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁)
  set P3 := ∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₁)
  set P4 := ∫ y, Φ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂)
  set P5 := ∫ y, Ψ (mlEval c' y) (mlEval e' y) ∂Measure.pi (fun _ : Fin R => ν₂)
  set P6 := ∫ y, Ψ (mlEval (smoothC r c) y) (mlEval (smoothC r e) y)
    ∂Measure.pi (fun _ : Fin R => ν₂)
  have a1 := abs_sub_le P1 P2 P6
  have a2 := abs_sub_le P2 P3 P6
  have a3 := abs_sub_le P3 P4 P6
  have a4 := abs_sub_le P4 P5 P6
  linarith

end BHSV25.BK.Aint
