module

public import B25.Basic

/-!
# Lemma 1.3: random rotations

`B25.partiallyRotated_of_uniform_main`: the statement of `B25.partiallyRotated_of_uniform` in
`B25/Challenge.lean`.

**Reduction to fixed unit vectors** [B25, Appendix B]. For `α` supported on `S` and `β` on `Sᶜ`,
`[X_S, R X_{Sᶜ}] α = Xα` and `[X_S, R X_{Sᶜ}] β = R (Xβ)` (`B25.rotateCols_mulVec_of_mem`,
`B25.rotateCols_mulVec_of_not_mem`). If `Xα = 0` or `Xβ = 0` the correlation is `0`. Otherwise
`u = Xα/‖Xα‖₂` and `w = Xβ/‖Xβ‖₂` are fixed unit vectors, the correlation is `corr u (R w)`
(`B25.corr_smul_left`, `B25.corr_smul_right`), and `R w` has the law `B25.uniformSphere n`, which
lives on the unit sphere, so `‖R w‖₂ = 1` almost surely and the correlation is `⟨u, R w⟩`. So
`P(|corr| > ε) ≤ σ({y : |⟨u, y⟩| > ε})` for `σ = B25.uniformSphere n` (`B25.SP.zetaKey`).
(Equality of laws makes `ω ↦ R ω w` a.e.-measurable: otherwise `Measure.map` is a Dirac measure,
which `σ` is not.)

**The cap** `{y : |⟨u, y⟩| > ε}` of the sphere. The paper writes `R w` as `g/‖g‖₂` with `g`
Gaussian and uses Gaussian tails. A shorter route uses the definition of `σ` through Mathlib's
`Measure.toSphere`: `toSphere A = n · vol((0,1) • A)` (`Measure.toSphere_apply'`), and
`toSphere univ = n · vol(ball 0 1)` (`Measure.toSphere_apply_univ`), so `σ(A)` is the fraction of
the unit ball occupied by the cone `(0,1) • A`. For the cap, every point `x` of the cone has
`‖x‖ < 1/2` or `|⟨u, x⟩| > ε/2`, and `{x ∈ ball 0 1 : ⟨u, x⟩ > t}` lies in the ball of radius
`√(1 - t²)` around `t u` (`‖x - t u‖² = ‖x‖² - 2t⟨u,x⟩ + t² < 1 - t²`). Volumes of balls scale as
`rⁿ` (`Measure.addHaar_ball_of_pos`). With the radius `1 - ε²/8 ≥ √(1 - ε²/4)` this gives
`σ(cap) ≤ 2^(-n) + 2 (1 - ε²/8)ⁿ ≤ 3 e^(-ε² n/8)` (`B25.SP.zetaCap`), which for `ε = 1/100` is at
most `e^(-c n)` with `c = ε²/16 = 1/160000` once `n ≥ n₀ = 320000` (`B25.SP.zetaNumeric`). The
same bound shows that `σ` is not a Dirac measure (`B25.SP.zetaNotDirac`): a Dirac measure at a
point `y` of the sphere puts mass `1` on the cap around `y`.
-/

@[expose] public section

namespace B25

open MeasureTheory ProbabilityTheory Matrix

namespace SP

open Metric Set
open scoped Pointwise

/-- A point of the open unit ball with `⟪u, x⟫ > t` lies in the ball of radius `1 - t²/2` around
`t u`, since `‖x - t u‖² = ‖x‖² - 2t⟪u, x⟫ + t² < 1 - t²`. -/
theorem capZetaBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u x : E} {t : ℝ}
    (hu : ‖u‖ = 1) (hx : ‖x‖ < 1) (ht : 0 < t) (ht1 : t ≤ 1) (h : t < inner ℝ u x) :
    ‖x - t • u‖ < 1 - t ^ 2 / 2 := by
  have hsq : ‖x - t • u‖ ^ 2 < (1 - t ^ 2 / 2) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hu, mul_one]
    have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
    nlinarith [mul_lt_mul_of_pos_left h ht, sq_nonneg (t ^ 2)]
  exact lt_of_pow_lt_pow_left₀ 2 (by nlinarith) hsq

/-- A point `r y` (`0 < r < 1`, `‖y‖ = 1`, `|⟪u, y⟫| > ε`) of the cone over a cap lies in the
ball of radius `1/2` around `0` (if `r < 1/2`) or in a ball of radius `1 - ε²/8` around `±(ε/2) u`
(if `r ≥ 1/2`, so that `|⟪u, r y⟫| > ε/2`). -/
theorem capZetaCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u y : E}
    {r ε : ℝ} (hu : ‖u‖ = 1) (hy : ‖y‖ = 1) (hr0 : 0 < r) (hr1 : r < 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hcap : ε < |inner ℝ u y|) :
    r • y ∈ ball 0 (1 / 2) ∪ ball ((ε / 2) • u) (1 - ε ^ 2 / 8) ∪
      ball ((ε / 2) • (-u)) (1 - ε ^ 2 / 8) := by
  have hxn : ‖r • y‖ = r := by rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  have hx1 : ‖r • y‖ < 1 := by rw [hxn]; exact hr1
  have hrad : 1 - ε ^ 2 / 8 = 1 - (ε / 2) ^ 2 / 2 := by ring
  rcases lt_or_ge r (1 / 2) with hr | hr
  · left; left
    rw [mem_ball_zero_iff, hxn]
    exact hr
  rcases lt_abs.mp hcap with h | h
  · left; right
    rw [mem_ball, dist_eq_norm, hrad]
    refine capZetaBall hu hx1 (by linarith) (by linarith) ?_
    rw [real_inner_smul_right]
    nlinarith [mul_le_mul_of_nonneg_right hr (hε0.trans h).le]
  · right
    rw [mem_ball, dist_eq_norm, hrad]
    refine capZetaBall (by rw [norm_neg, hu]) hx1 (by linarith) (by linarith) ?_
    rw [real_inner_smul_right, inner_neg_left]
    nlinarith [mul_le_mul_of_nonneg_right hr (hε0.trans h).le]

/-- The inner product of `EuclideanSpace ℝ (Fin n)` is the dot product of the coordinates. -/
theorem zetaDot {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The map from the unit sphere of `EuclideanSpace ℝ (Fin n)` to `Fin n → ℝ` is measurable. -/
theorem zetaMeasurable (n : ℕ) :
    Measurable (fun x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ x.1.ofLp) := by
  fun_prop

/-- `B25.uniformSphere n` on a measurable set: the normalized surface measure of its preimage. -/
theorem zetaApply {n : ℕ} {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    uniformSphere n s = ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹ *
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
        ((fun x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ x.1.ofLp) ⁻¹' s) := by
  rw [uniformSphere, Measure.map_apply (zetaMeasurable n) hs, Measure.smul_apply, smul_eq_mul]

/-- `B25.uniformSphere n` lives on the unit sphere `{y : y ⬝ᵥ y = 1}`. -/
theorem zetaOffSphere (n : ℕ) : uniformSphere n {y | y ⬝ᵥ y ≠ 1} = 0 := by
  rw [zetaApply (by measurability)]
  convert mul_zero _
  convert measure_empty (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
  ext x
  simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  have hx := mem_sphere_zero_iff_norm.mp x.2
  rw [← zetaDot, real_inner_self_eq_norm_sq, hx, one_pow]

/-- For `n ≥ 1`, the total surface measure is `n · vol(ball 0 1)`, nonzero and finite. -/
theorem zetaUniv {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ =
        n * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ∧
      (n : ENNReal) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 ∧
      (n : ENNReal) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ := by
  refine ⟨by rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin], ?_, ?_⟩
  · exact mul_ne_zero (by exact_mod_cast hn.ne') (measure_ball_pos _ _ one_pos).ne'
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) measure_ball_lt_top.ne

/-- **The cap bound.** For a unit vector `u` and `0 < ε ≤ 1`,
`σ({y : |⟨u, y⟩| > ε}) ≤ 2⁻ⁿ + 2 (1 - ε²/8)ⁿ`. -/
theorem zetaCap {n : ℕ} (hn : 0 < n) {u : Fin n → ℝ} (hu : u ⬝ᵥ u = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    uniformSphere n {y | ε < |u ⬝ᵥ y|} ≤
      ENNReal.ofReal ((1 / 2) ^ n + 2 * (1 - ε ^ 2 / 8) ^ n) := by
  set μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hT : MeasurableSet {y : Fin n → ℝ | ε < |u ⬝ᵥ y|} := by measurability
  set u' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  have hdot : ∀ y : EuclideanSpace ℝ (Fin n), inner ℝ u' y = u ⬝ᵥ y.ofLp := fun y ↦ by
    rw [zetaDot]
  have hu' : ‖u'‖ = 1 := by
    have h := real_inner_self_eq_norm_sq u'
    rw [hdot, WithLp.ofLp_toLp, hu] at h
    nlinarith [norm_nonneg u']
  have hs8 : 0 < 1 - ε ^ 2 / 8 := by nlinarith
  set C := Ioo (0 : ℝ) 1 • (Subtype.val ''
    ((fun x : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ x.1.ofLp) ⁻¹' {y | ε < |u ⬝ᵥ y|}))
  have hsub : C ⊆ ball 0 (1 / 2) ∪ ball ((ε / 2) • u') (1 - ε ^ 2 / 8) ∪
      ball ((ε / 2) • (-u')) (1 - ε ^ 2 / 8) := by
    intro x hx
    obtain ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_smul.mp hx
    refine capZetaCone hu' (mem_sphere_zero_iff_norm.mp y.2) hr.1 hr.2 hε0 hε1 ?_
    rw [hdot]
    exact hy
  set A := ENNReal.ofReal ((1 / 2 : ℝ) ^ n)
  set A' := ENNReal.ofReal ((1 - ε ^ 2 / 8) ^ n)
  have hball : μ C ≤ (A + A' + A') * μ (ball 0 1) := by
    calc μ C ≤ μ (ball 0 (1 / 2) ∪ ball ((ε / 2) • u') (1 - ε ^ 2 / 8) ∪
          ball ((ε / 2) • (-u')) (1 - ε ^ 2 / 8)) := measure_mono hsub
      _ ≤ μ (ball 0 (1 / 2)) + μ (ball ((ε / 2) • u') (1 - ε ^ 2 / 8)) +
          μ (ball ((ε / 2) • (-u')) (1 - ε ^ 2 / 8)) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ = _ := by
        rw [Measure.addHaar_ball_of_pos μ _ (by norm_num), Measure.addHaar_ball_of_pos μ _ hs8,
          Measure.addHaar_ball_of_pos μ _ hs8, finrank_euclideanSpace_fin, add_mul, add_mul]
  obtain ⟨hU, h0, htop⟩ := zetaUniv (n := n) hn
  rw [zetaApply hT, Measure.toSphere_apply' μ (zetaMeasurable n hT), hU,
    finrank_euclideanSpace_fin]
  calc ((n : ENNReal) * μ (ball 0 1))⁻¹ * (n * μ C)
      ≤ ((n : ENNReal) * μ (ball 0 1))⁻¹ * (n * ((A + A' + A') * μ (ball 0 1))) := by
        gcongr
    _ = A + A' + A' := by
      rw [mul_left_comm (n : ENNReal), mul_left_comm _ (A + A' + A'),
        ENNReal.inv_mul_cancel h0 htop, mul_one]
    _ = ENNReal.ofReal ((1 / 2) ^ n + 2 * (1 - ε ^ 2 / 8) ^ n) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- For `n ≥ 320000`: `2⁻ⁿ + 2 (1 - (1/100)²/8)ⁿ ≤ e^(-n/160000)`. -/
theorem zetaNumeric {n : ℕ} (hn : 320000 ≤ n) :
    (1 / 2 : ℝ) ^ n + 2 * (1 - (1 / 100 : ℝ) ^ 2 / 8) ^ n ≤ Real.exp (-(1 / 160000 * n)) := by
  have hn' : (320000 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : 1 - 1 / 80000 ≤ Real.exp (-(1 / 80000)) := by
    linarith [Real.add_one_le_exp (-(1 / 80000 : ℝ))]
  have h1 : (1 / 2 : ℝ) ^ n ≤ Real.exp (-(1 / 80000)) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by linarith) n
  have h2 : (1 - (1 / 100 : ℝ) ^ 2 / 8) ^ n ≤ Real.exp (-(1 / 80000)) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num at hexp ⊢; linarith) n
  rw [← Real.exp_nat_mul] at h1 h2
  have hsplit : Real.exp (n * -(1 / 80000)) =
      Real.exp (-(1 / 160000 * n)) * Real.exp (-(1 / 160000 * n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (3 : ℝ) ≤ Real.exp (1 / 160000 * n) := by
    linarith [Real.add_one_le_exp (1 / 160000 * (n : ℝ))]
  have hinv : Real.exp (-(1 / 160000 * n)) * Real.exp (1 / 160000 * n) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (-(1 / 160000 * n))
  nlinarith

/-- For `n ≥ 320000`, `B25.uniformSphere n` is not a Dirac measure: the Dirac measure at a point
`y` of the sphere puts mass `1` on the cap around `y`. -/
theorem zetaNotDirac {n : ℕ} (hn : 320000 ≤ n) (y : Fin n → ℝ) :
    uniformSphere n ≠ Measure.dirac y := by
  intro h
  have hy : y ⬝ᵥ y = 1 := by
    by_contra hne
    have h0 := zetaOffSphere n
    rw [h, Measure.dirac_apply_of_mem hne] at h0
    exact one_ne_zero h0
  have hcap := zetaCap (by omega) hy (ε := 1 / 100) (by norm_num) (by norm_num)
  rw [h, Measure.dirac_apply_of_mem (by simp only [mem_ofPred_eq, hy]; norm_num),
    ENNReal.one_le_ofReal] at hcap
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : Real.exp (-(1 / 160000 * n)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith [zetaNumeric hn]

/-- A nonzero vector is a positive multiple of a unit vector. -/
theorem zetaNormalize {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∃ u : Fin n → ℝ, u ⬝ᵥ u = 1 ∧ a • u = v := by
  have hpos : 0 < l2 v := by
    refine (l2_nonneg v).lt_of_ne fun h ↦ hv ?_
    have := l2_sq v
    rw [← h, zero_pow two_ne_zero, eq_comm] at this
    exact dotProduct_self_eq_zero.mp this
  refine ⟨l2 v, hpos, (l2 v)⁻¹ • v, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, ← l2_sq, smul_eq_mul, smul_eq_mul]
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- **The reduction to fixed unit vectors.** If `R v` has the law `B25.uniformSphere n` for every
unit vector `v`, then `P(|corr v (R z)| > 1/100) ≤ e^(-n/160000)` for all fixed `v` and `z`. -/
theorem zetaKey {n : ℕ} (hn : 320000 ≤ n) (v z : Fin n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hR : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 1 → P.map (fun ω ↦ R ω *ᵥ w) = uniformSphere n) :
    P {ω | (1 / 100 : ℝ) < |corr v (R ω *ᵥ z)|} ≤
      ENNReal.ofReal (Real.exp (-(1 / 160000 * n))) := by
  by_cases hv : v = 0
  · norm_num [hv, corr]
  by_cases hz : z = 0
  · norm_num [hz, corr]
  obtain ⟨a, ha, u, hu, rfl⟩ := zetaNormalize hv
  obtain ⟨b, hb, w, hw, rfl⟩ := zetaNormalize hz
  have hset : {ω | (1 / 100 : ℝ) < |corr (a • u) (R ω *ᵥ (b • w))|} =
      (fun ω ↦ R ω *ᵥ w) ⁻¹' {y | (1 / 100 : ℝ) < |corr u y|} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mulVec_smul, corr_smul_left ha, corr_smul_right hb]
  rw [hset]
  have hmeas : AEMeasurable (fun ω ↦ R ω *ᵥ w) P := by
    by_contra hnot
    have h := hR w hw
    rw [Measure.map_of_not_aemeasurable_of_ne_zero hnot (IsProbabilityMeasure.ne_zero P)] at h
    exact zetaNotDirac hn _ h.symm
  have hsub : {y : Fin n → ℝ | (1 / 100 : ℝ) < |corr u y|} ⊆
      {y | (1 / 100 : ℝ) < |u ⬝ᵥ y|} ∪ {y | y ⬝ᵥ y ≠ 1} := by
    intro y hy
    by_cases h1 : y ⬝ᵥ y = 1
    · left
      have hc : corr u y = u ⬝ᵥ y := by simp [corr, l2, hu, h1]
      simpa only [mem_ofPred_eq, hc] using hy
    · right
      exact h1
  have hT1 : MeasurableSet {y : Fin n → ℝ | (1 / 100 : ℝ) < |u ⬝ᵥ y|} := by measurability
  have hT2 : MeasurableSet {y : Fin n → ℝ | y ⬝ᵥ y ≠ 1} := by measurability
  calc P ((fun ω ↦ R ω *ᵥ w) ⁻¹' {y | (1 / 100 : ℝ) < |corr u y|})
      ≤ P ((fun ω ↦ R ω *ᵥ w) ⁻¹' {y | (1 / 100 : ℝ) < |u ⬝ᵥ y|} ∪
          (fun ω ↦ R ω *ᵥ w) ⁻¹' {y | y ⬝ᵥ y ≠ 1}) := by
        rw [← preimage_union]
        exact measure_mono (preimage_mono hsub)
    _ ≤ P ((fun ω ↦ R ω *ᵥ w) ⁻¹' {y | (1 / 100 : ℝ) < |u ⬝ᵥ y|}) +
          P ((fun ω ↦ R ω *ᵥ w) ⁻¹' {y | y ⬝ᵥ y ≠ 1}) := measure_union_le _ _
    _ = uniformSphere n {y | (1 / 100 : ℝ) < |u ⬝ᵥ y|} + uniformSphere n {y | y ⬝ᵥ y ≠ 1} := by
        rw [← Measure.map_apply_of_aemeasurable hmeas hT1,
          ← Measure.map_apply_of_aemeasurable hmeas hT2, hR w hw]
    _ ≤ ENNReal.ofReal ((1 / 2) ^ n + 2 * (1 - (1 / 100 : ℝ) ^ 2 / 8) ^ n) + 0 :=
        add_le_add (zetaCap (by omega) hu (by norm_num) (by norm_num)) (zetaOffSphere n).le
    _ ≤ _ := by
        rw [add_zero]
        exact ENNReal.ofReal_le_ofReal (zetaNumeric hn)

end SP

/-- **Lemma 1.3** of [B25]: the statement of `B25.partiallyRotated_of_uniform`. -/
theorem partiallyRotated_of_uniform_main :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ),
        (∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → P.map (fun ω ↦ R ω *ᵥ v) = uniformSphere n) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) c := by
  refine ⟨1 / 160000, by norm_num, 320000, fun n hn d X S Ω _ P _ R hR ↦ ?_⟩
  intro α β hα hβ
  simp only [rotateCols_mulVec_of_mem X S _ hα, rotateCols_mulVec_of_not_mem X S _ hβ]
  exact SP.zetaKey hn _ _ P R hR

end B25
