module

public import ABBKS26.Prob.UniformQuad
public import ABBKS26.Prob.UniformHoeffding

/-!
# Uniform window counts for a Gaussian sample

For an iid sample `g : Fin m → ℝ^d` of standard Gaussians (law `Measure.pi fun _ ↦ stdGaussian`,
with Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin d)`, which is
`multivariateGaussian 0 1`), with high probability, simultaneously for **all** quadratic
polynomials `q(g) = gᵀ A g + ⟨b, g⟩ + c` with `‖A‖_F² + ‖b‖² + c² ≤ 1` and all `a, b ∈ ℝ`, the
number of sample points with `q(g l) ∈ [a, b]` is between `(P(q(G) ∈ [a + ρ, b - ρ]) - η) m` and
`(P(q(G) ∈ [a - ρ, b + ρ]) + η) m`, and at most `η m` sample points have norm more than `R`
(`ABBKS26.Unif.UnifWin`).

* `ABBKS26.Unif.exists_bad_set`: for `0 < η`, `0 < ρ ≤ 1`, `0 < R` with `4 d ≤ η R²`, there is a
  measurable set `B` of samples with `UnifWin η ρ R g` for all `g ∉ B` and
  `P(B) ≤ (1 + 2 (2K + 1)^(d² + d + 3)) e^{-m η² / 8}`, `K = ⌈4 (dR + 1)² / ρ⌉`
  (`ABBKS26.Unif.bound`).
* `ABBKS26.Unif.exists_bad_set_of_le`: `P(B) ≤ δ` once
  `m ≥ (8 / η²) ((d² + d + 3) log(11 (dR + 1)² / ρ) + log(3 / δ))`
  (`ABBKS26.Unif.sampleSize`).
* `ABBKS26.Unif.UnifWin.winCount_le_of_near`, `ABBKS26.Unif.UnifWin.le_winCount_of_near`: the
  counts of a perturbed sample `g'` with `‖g' l - g l‖ ≤ θ` (e.g. rounded points), with the windows
  enlarged or shrunk by `θ (2R + 1) + θ²` (`ABBKS26.Unif.winCount_le_of_near`,
  `ABBKS26.Unif.le_winCount_of_near` for the deterministic comparison).

The proof: Hoeffding's inequality for each window of a finite grid of quadratics and thresholds
(`ABBKS26.Unif.net`) and for the norm, and a union bound; on the ball of radius `R` a quadratic is
within `ρ / 4` of its rounding to the grid (`ABBKS26.Unif.exists_net`), and points outside the
ball are few, in the sample and for the Gaussian (`P(‖G‖ > R) ≤ d / R² ≤ η / 4`).
-/

@[expose] public section

namespace ABBKS26.Unif

open MeasureTheory ProbabilityTheory Real Finset

variable {d m : ℕ}

/-! ### Counts and the uniform event -/

/-- The number of sample points `l` with `q(g l) ∈ [a, b]`. -/
noncomputable def winCount (q : Quad d) (a b : ℝ) (g : Fin m → EuclideanSpace ℝ (Fin d)) : ℕ :=
  (univ.filter fun l ↦ q.eval (g l) ∈ Set.Icc a b).card

/-- The number of sample points of norm more than `R`. -/
noncomputable def normCount (R : ℝ) (g : Fin m → EuclideanSpace ℝ (Fin d)) : ℕ :=
  (univ.filter fun l ↦ R < ‖g l‖).card

/-- `P(q(G) ∈ [a, b])` for a standard Gaussian vector `G` in `ℝ^d`. -/
noncomputable def winProb (q : Quad d) (a b : ℝ) : ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).real {x | q.eval x ∈ Set.Icc a b}

/-- **Uniform window counts** for a sample `g : Fin m → ℝ^d`: at most `η m` points of norm more
than `R`, and for every quadratic `q` with `‖A‖_F² + ‖b‖² + c² ≤ 1` and all `a, b`, the number
of points with `q(g l) ∈ [a, b]` is at most `(P(q(G) ∈ [a - ρ, b + ρ]) + η) m` and at least
`(P(q(G) ∈ [a + ρ, b - ρ]) - η) m`. -/
structure UnifWin (η ρ R : ℝ) (g : Fin m → EuclideanSpace ℝ (Fin d)) : Prop where
  normCount_le : (normCount R g : ℝ) ≤ η * m
  winCount_le : ∀ q : Quad d, q.normSq ≤ 1 → ∀ a b : ℝ,
    (winCount q a b g : ℝ) ≤ (winProb q (a - ρ) (b + ρ) + η) * m
  le_winCount : ∀ q : Quad d, q.normSq ≤ 1 → ∀ a b : ℝ,
    (winProb q (a + ρ) (b - ρ) - η) * m ≤ winCount q a b g

theorem winProb_nonneg (q : Quad d) (a b : ℝ) : 0 ≤ winProb q a b := measureReal_nonneg

/-! ### The grid -/

/-- The bound `(dR + 1)²` on `|q|` over the ball of radius `R`, for normalized `q`. -/
def phi (d : ℕ) (R : ℝ) : ℝ := (d * R + 1) ^ 2

theorem one_le_phi {R : ℝ} (hR : 0 ≤ R) : 1 ≤ phi d R := by
  unfold phi
  nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hR]

/-- The size `K = ⌈4 (dR + 1)² / ρ⌉` of the grid. -/
noncomputable def gridK (d : ℕ) (ρ R : ℝ) : ℕ := ⌈4 * phi d R / ρ⌉₊

/-- The mesh `ρ / (4 (dR + 1)²)` of the grid of coefficients. -/
noncomputable def meshC (d : ℕ) (ρ R : ℝ) : ℝ := ρ / (4 * phi d R)

/-- The indices of grid points: integer coefficients `(A, b, c)` and integer thresholds. -/
abbrev Idx (d : ℕ) := (Fin d → Fin d → ℤ) × (Fin d → ℤ) × ℤ × ℤ × ℤ

/-- The grid: all integers between `-K` and `K`. -/
def net (d K : ℕ) : Finset (Idx d) :=
  Fintype.piFinset (fun _ ↦ Fintype.piFinset fun _ ↦ Icc (-(K : ℤ)) K) ×ˢ
    Fintype.piFinset (fun _ ↦ Icc (-(K : ℤ)) K) ×ˢ Icc (-(K : ℤ)) K ×ˢ Icc (-(K : ℤ)) K ×ˢ
      Icc (-(K : ℤ)) K

theorem card_net (d K : ℕ) : (net d K).card = (2 * K + 1) ^ (d * d + d + 3) := by
  have h : (Icc (-(K : ℤ)) K).card = 2 * K + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [net, card_product, Fintype.card_piFinset, h, prod_const, card_univ,
    Fintype.card_fin]
  ring

/-- The quadratic with coefficients `h z`. -/
def gridQuad (h : ℝ) (z : Idx d) : Quad d :=
  ⟨fun i j ↦ h * z.1 i j, fun i ↦ h * z.2.1 i, h * z.2.2.1⟩

/-- The window of the grid point `z`: the points `x` with `q_z(x) ∈ [t z₄, t z₅]`, `q_z` the
quadratic with coefficients `h z`. -/
def netSet (h t : ℝ) (z : Idx d) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (gridQuad h z).eval x ∈ Set.Icc (t * z.2.2.2.1) (t * z.2.2.2.2)}

theorem measurableSet_netSet (h t : ℝ) (z : Idx d) : MeasurableSet (netSet h t z) :=
  (gridQuad h z).measurable_eval measurableSet_Icc

/-- **Covering by the grid.** For a normalized quadratic `q` and `-Φ ≤ α ≤ β ≤ Φ`
(`Φ = (dR + 1)²`) there is a grid window that contains every point `x` of the ball of radius `R`
with `q(x) ∈ [α, β]` and whose points `x` in the ball have `q(x) ∈ [α - ρ, β + ρ]`. -/
theorem exists_net {ρ R : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 0 ≤ R) {q : Quad d}
    (hq : q.normSq ≤ 1) {α β : ℝ} (hα : -phi d R ≤ α) (hβ : β ≤ phi d R) (hαβ : α ≤ β) :
    ∃ z ∈ net d (gridK d ρ R), ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R →
      (q.eval x ∈ Set.Icc α β → x ∈ netSet (meshC d ρ R) (ρ / 2) z) ∧
      (x ∈ netSet (meshC d ρ R) (ρ / 2) z → q.eval x ∈ Set.Icc (α - ρ) (β + ρ)) := by
  have hΦ := one_le_phi (d := d) hR
  set Φ := phi d R
  set h := meshC d ρ R with hh
  have hh0 : 0 < h := by rw [hh, meshC]; positivity
  have hhΦ : h * Φ = ρ / 4 := by
    rw [hh, meshC]
    change ρ / (4 * Φ) * Φ = ρ / 4
    field_simp
  have ht0 : 0 < ρ / 2 := by positivity
  set K := gridK d ρ R
  have hK : 4 * Φ / ρ ≤ K := Nat.le_ceil _
  have hKc : 1 / h ≤ K := by
    rw [hh, meshC, one_div_div]
    exact hK
  have hKt : (Φ + 1) / (ρ / 2) ≤ K := by
    refine le_trans ?_ hK
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hρ0]
    linarith
  set z : Idx d := (fun i j ↦ ⌊q.A i j / h⌋, fun i ↦ ⌊q.b i / h⌋, ⌊q.c / h⌋,
    ⌊(α - ρ / 4) / (ρ / 2)⌋, ⌈(β + ρ / 4) / (ρ / 2)⌉) with hz
  have hαt : |α - ρ / 4| ≤ Φ + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hβt : |β + ρ / 4| ≤ Φ + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨z, ?_, fun x hx ↦ ?_⟩
  · simp only [net, mem_product, Fintype.mem_piFinset, hz]
    exact ⟨fun i j ↦ floor_mem_Icc hh0 (q.abs_A_le_one hq i j) hKc,
      fun i ↦ floor_mem_Icc hh0 (q.abs_b_le_one hq i) hKc,
      floor_mem_Icc hh0 (q.abs_c_le_one hq) hKc, floor_mem_Icc ht0 hαt hKt,
      ceil_mem_Icc ht0 hβt hKt⟩
  -- the grid quadratic is within `ρ / 4` of `q` on the ball
  have hclose : |q.eval x - (gridQuad h z).eval x| ≤ ρ / 4 := by
    rw [← Quad.eval_sub, ← hhΦ]
    have hc : ∀ y : ℝ, |y - h * ⌊y / h⌋| ≤ h := fun y ↦
      abs_le.2 ⟨by linarith [mul_floor_le (x := y) hh0],
        by linarith [lt_mul_floor_add (x := y) hh0]⟩
    exact Quad.abs_eval_le (fun i j ↦ hc _) (fun i ↦ hc _) (hc _) hx
  have hlo : ρ / 2 * (z.2.2.2.1 : ℝ) ≤ α - ρ / 4 := mul_floor_le ht0
  have hlo' : α - ρ / 4 < ρ / 2 * (z.2.2.2.1 : ℝ) + ρ / 2 := lt_mul_floor_add ht0
  have hhi : β + ρ / 4 ≤ ρ / 2 * (z.2.2.2.2 : ℝ) := le_mul_ceil ht0
  have hhi' : ρ / 2 * (z.2.2.2.2 : ℝ) < β + ρ / 4 + ρ / 2 := mul_ceil_lt_add ht0
  rw [abs_le] at hclose
  simp only [netSet, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-! ### Counting -/

theorem card_filter_le_add {p r s : Fin m → Prop} [DecidablePred p] [DecidablePred r]
    [DecidablePred s] (h : ∀ l, p l → r l ∨ s l) :
    ((univ.filter p).card : ℝ) ≤ (univ.filter r).card + (univ.filter s).card := by
  have : (univ.filter p).card ≤ (univ.filter r).card + (univ.filter s).card := by
    refine (card_le_card fun l hl ↦ ?_).trans (card_union_le _ _)
    simp only [mem_filter, mem_univ, true_and, mem_union] at hl ⊢
    exact h l hl
  exact_mod_cast this

theorem card_filter_le_of_imp {p r : Fin m → Prop} [DecidablePred p] [DecidablePred r]
    (h : ∀ l, p l → r l) : ((univ.filter p).card : ℝ) ≤ (univ.filter r).card := by
  have : (univ.filter p).card ≤ (univ.filter r).card := by
    refine card_le_card fun l hl ↦ ?_
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact h l hl
  exact_mod_cast this

/-! ### The main theorem -/

/-- The failure probability `(1 + 2 (2K + 1)^(d² + d + 3)) e^{-m η² / 8}`,
`K = ⌈4 (dR + 1)² / ρ⌉`. -/
noncomputable def bound (d m : ℕ) (η ρ R : ℝ) : ℝ :=
  (1 + 2 * (2 * gridK d ρ R + 1 : ℝ) ^ (d * d + d + 3)) * exp (-(m * η ^ 2 / 8))

/-- The bad samples: those where some window of the grid, or the norm, has a count that deviates
by `η / 4` from its expectation. -/
noncomputable def badSet (d m : ℕ) (η ρ R : ℝ) : Set (Fin m → EuclideanSpace ℝ (Fin d)) :=
  upperBad (stdGaussian _) {x | R < ‖x‖} (η / 4) ∪
    ⋃ z ∈ net d (gridK d ρ R),
      (upperBad (stdGaussian _) (netSet (meshC d ρ R) (ρ / 2) z) (η / 4) ∪
        lowerBad (stdGaussian _) (netSet (meshC d ρ R) (ρ / 2) z) (η / 4))

theorem measurableSet_badSet (d m : ℕ) (η ρ R : ℝ) : MeasurableSet (badSet d m η ρ R) := by
  refine (measurableSet_upperBad (measurableSet_lt measurable_const measurable_norm) _).union ?_
  refine Finset.measurableSet_biUnion _ fun z _ ↦ ?_
  exact (measurableSet_upperBad (measurableSet_netSet _ _ z) _).union
    (measurableSet_lowerBad (measurableSet_netSet _ _ z) _)

theorem measureReal_badSet_le {η : ℝ} (hη : 0 ≤ η) (ρ R : ℝ) :
    (Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))).real
      (badSet d m η ρ R) ≤ bound d m η ρ R := by
  set P := Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))
  have ht : 0 ≤ η / 4 := by positivity
  have he : exp (-2 * m * (η / 4) ^ 2) = exp (-(m * η ^ 2 / 8)) := by congr 1; ring
  set e := exp (-(m * η ^ 2 / 8))
  have h1 := measureReal_upperBad_le (m := m) (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (measurableSet_lt measurable_const measurable_norm : MeasurableSet {x | R < ‖x‖}) ht
  have h2 : ∀ z, P.real (upperBad (stdGaussian _) (netSet (meshC d ρ R) (ρ / 2) z) (η / 4) ∪
      lowerBad (stdGaussian _) (netSet (meshC d ρ R) (ρ / 2) z) (η / 4)) ≤ 2 * e := by
    intro z
    refine (measureReal_union_le _ _).trans ?_
    have h3 := measureReal_upperBad_le (m := m) (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
      (measurableSet_netSet (meshC d ρ R) (ρ / 2) z) ht
    have h4 := measureReal_lowerBad_le (m := m) (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
      (measurableSet_netSet (meshC d ρ R) (ρ / 2) z) ht
    rw [he] at h3 h4
    linarith
  rw [he] at h1
  calc P.real (badSet d m η ρ R) ≤ e + ∑ z ∈ net d (gridK d ρ R), 2 * e := by
        refine (measureReal_union_le _ _).trans (add_le_add h1 ?_)
        exact (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun z _ ↦ h2 z)
    _ = bound d m η ρ R := by
        rw [sum_const, card_net, nsmul_eq_mul, bound]
        push_cast
        ring

/-- **The deterministic part.** For `0 < η`, `0 < ρ ≤ 1` and `0 < R` with `4 d ≤ η R²`, every
sample outside `badSet d m η ρ R` has uniform window counts. -/
theorem unifWin_of_notMem_badSet {η ρ R : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hR : 0 < R) (hdR : 4 * d ≤ η * R ^ 2) {g : Fin m → EuclideanSpace ℝ (Fin d)}
    (hg : g ∉ badSet d m η ρ R) : UnifWin η ρ R g := by
  classical
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set SR : Set (EuclideanSpace ℝ (Fin d)) := {x | R < ‖x‖}
  set Φ := phi d R
  set N := netSet (d := d) (meshC d ρ R) (ρ / 2)
  simp only [badSet, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hg
  obtain ⟨hgR, hgN⟩ := hg
  have hgN' : ∀ z ∈ net d (gridK d ρ R), g ∉ upperBad γ (N z) (η / 4) ∧
      g ∉ lowerBad γ (N z) (η / 4) := fun z hz ↦ hgN z hz
  -- the Gaussian norm tail
  have hpR : γ.real SR ≤ η / 4 := by
    refine (measureReal_norm_gt_le hR).trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the sample norm count
  have hnc : (normCount R g : ℝ) < (γ.real SR + η / 4) * m := by
    have := lt_of_notMem_upperBad hgR
    rwa [indCount_eq_card] at this
  have hnc' : (normCount R g : ℝ) ≤ η / 2 * m := by
    refine hnc.le.trans ?_
    gcongr
    linarith
  -- a normalized quadratic is at most `Φ` on the ball
  have hball : ∀ q : Quad d, q.normSq ≤ 1 → ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R →
      -Φ ≤ q.eval x ∧ q.eval x ≤ Φ := fun q hq x hx ↦
    abs_le.1 (Quad.abs_eval_le_of_normSq_le hq hx)
  refine ⟨hnc'.trans (by nlinarith), fun q hq a b ↦ ?_, fun q hq a b ↦ ?_⟩
  · -- the upper bound
    have hsplit : (winCount q a b g : ℝ) ≤ normCount R g +
        (univ.filter fun l ↦ ‖g l‖ ≤ R ∧ q.eval (g l) ∈ Set.Icc a b).card := by
      refine card_filter_le_add fun l hl ↦ ?_
      by_cases h : R < ‖g l‖
      · exact Or.inl h
      · exact Or.inr ⟨not_lt.1 h, hl⟩
    have hin : ((univ.filter fun l ↦ ‖g l‖ ≤ R ∧ q.eval (g l) ∈ Set.Icc a b).card : ℝ) ≤
        (γ.real SR + winProb q (a - ρ) (b + ρ) + η / 4) * m := by
      by_cases hαβ : max a (-Φ) ≤ min b Φ
      · obtain ⟨z, hz, hzx⟩ := exists_net hρ0 hρ1 hR.le hq (le_max_right a (-Φ))
          (min_le_right b Φ) hαβ
        have hcount := lt_of_notMem_upperBad (hgN' z hz).1
        rw [indCount_eq_card] at hcount
        have hsub : N z ⊆ SR ∪ {x | q.eval x ∈ Set.Icc (a - ρ) (b + ρ)} := by
          intro x hx
          by_cases h : R < ‖x‖
          · exact Or.inl h
          · obtain ⟨h1, h2⟩ := (hzx x (not_lt.1 h)).2 hx
            refine Or.inr ⟨?_, ?_⟩
            · linarith [le_max_left a (-Φ)]
            · linarith [min_le_left b Φ]
        have hmeas : γ.real (N z) ≤ γ.real SR + winProb q (a - ρ) (b + ρ) :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
        refine (card_filter_le_of_imp fun l hl ↦ ?_).trans (hcount.le.trans ?_)
        · obtain ⟨hl1, hl2⟩ := hl
          refine (hzx (g l) hl1).1 ⟨max_le hl2.1 (hball q hq _ hl1).1,
            le_min hl2.2 (hball q hq _ hl1).2⟩
        · gcongr
      · have : (univ.filter fun l ↦ ‖g l‖ ≤ R ∧ q.eval (g l) ∈ Set.Icc a b) = ∅ := by
          refine filter_eq_empty_iff.2 fun l _ hl ↦ hαβ ?_
          obtain ⟨hl1, hl2⟩ := hl
          have := hball q hq _ hl1
          exact (max_le hl2.1 this.1).trans (le_min hl2.2 this.2)
        rw [this, card_empty, Nat.cast_zero]
        have := winProb_nonneg q (a - ρ) (b + ρ)
        have : 0 ≤ γ.real SR := measureReal_nonneg
        positivity
    have := winProb_nonneg q (a - ρ) (b + ρ)
    nlinarith
  · -- the lower bound
    by_cases hαβ : max (a + ρ) (-Φ) ≤ min (b - ρ) Φ
    · obtain ⟨z, hz, hzx⟩ := exists_net hρ0 hρ1 hR.le hq (le_max_right (a + ρ) (-Φ))
        (min_le_right (b - ρ) Φ) hαβ
      have hcount := lt_of_notMem_lowerBad (hgN' z hz).2
      rw [indCount_eq_card] at hcount
      have hsub : {x | q.eval x ∈ Set.Icc (a + ρ) (b - ρ)} ⊆ SR ∪ N z := by
        intro x hx
        by_cases h : R < ‖x‖
        · exact Or.inl h
        · have hx' := hball q hq x (not_lt.1 h)
          obtain ⟨h1, h2⟩ := hx
          exact Or.inr ((hzx x (not_lt.1 h)).1 ⟨max_le h1 hx'.1, le_min h2 hx'.2⟩)
      have hmeas : winProb q (a + ρ) (b - ρ) ≤ γ.real SR + γ.real (N z) :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
      have hsplit : ((univ.filter fun l ↦ g l ∈ N z).card : ℝ) ≤ normCount R g +
          winCount q a b g := by
        refine card_filter_le_add fun l hl ↦ ?_
        by_cases h : R < ‖g l‖
        · exact Or.inl h
        · obtain ⟨h1, h2⟩ := (hzx (g l) (not_lt.1 h)).2 hl
          refine Or.inr ⟨?_, ?_⟩
          · linarith [le_max_left (a + ρ) (-Φ)]
          · linarith [min_le_left (b - ρ) Φ]
      nlinarith
    · have hsub : {x | q.eval x ∈ Set.Icc (a + ρ) (b - ρ)} ⊆ SR := by
        intro x hx
        by_contra h
        have hx' := hball q hq x (not_lt.1 h)
        obtain ⟨h1, h2⟩ := hx
        exact hαβ ((max_le h1 hx'.1).trans (le_min h2 hx'.2))
      have hmeas : winProb q (a + ρ) (b - ρ) ≤ γ.real SR := measureReal_mono hsub
      have : (0 : ℝ) ≤ winCount q a b g := Nat.cast_nonneg _
      nlinarith

/-- **Uniform window counts for a Gaussian sample.** For `0 < η`, `0 < ρ ≤ 1` and `0 < R` with
`4 d ≤ η R²`, there is a measurable set `B` of samples, of probability at most
`(1 + 2 (2K + 1)^(d² + d + 3)) e^{-m η² / 8}` with `K = ⌈4 (dR + 1)² / ρ⌉`, such that every
sample outside `B` has uniform window counts. -/
theorem exists_bad_set {η ρ R : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 0 < R)
    (hdR : 4 * d ≤ η * R ^ 2) :
    ∃ B : Set (Fin m → EuclideanSpace ℝ (Fin d)), MeasurableSet B ∧
      (∀ g ∉ B, UnifWin η ρ R g) ∧
      (Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))) B ≤
        ENNReal.ofReal (bound d m η ρ R) := by
  refine ⟨badSet d m η ρ R, measurableSet_badSet d m η ρ R,
    fun g hg ↦ unifWin_of_notMem_badSet hη hρ0 hρ1 hR hdR hg, ?_⟩
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_badSet_le hη.le ρ R)

/-! ### The sample size -/

/-- A sample size that makes the failure probability at most `δ`:
`(8 / η²) ((d² + d + 3) log(11 (dR + 1)² / ρ) + log(3 / δ))`. -/
noncomputable def sampleSize (d : ℕ) (η ρ R δ : ℝ) : ℝ :=
  8 / η ^ 2 * ((d * d + d + 3) * Real.log (11 * phi d R / ρ) + Real.log (3 / δ))

theorem bound_le {η ρ R δ : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hm : sampleSize d η ρ R δ ≤ m) : bound d m η ρ R ≤ δ := by
  have hΦ := one_le_phi (d := d) hR
  set Φ := phi d R
  set D := d * d + d + 3
  set Y := 11 * Φ / ρ with hY
  have hY0 : 0 < Y := by positivity
  have hK : (2 * gridK d ρ R + 1 : ℝ) ≤ Y := by
    have h1 : (gridK d ρ R : ℝ) < 4 * Φ / ρ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ Φ / ρ := by rw [le_div_iff₀ hρ0]; linarith
    have h3 : 4 * Φ / ρ = 4 * (Φ / ρ) := by ring
    have h4 : Y = 11 * (Φ / ρ) := by rw [hY]; ring
    rw [h4]
    linarith
  have hN : (1 + 2 * (2 * gridK d ρ R + 1 : ℝ) ^ D) ≤ 3 * Y ^ D := by
    have h1 : (2 * gridK d ρ R + 1 : ℝ) ^ D ≤ Y ^ D := by gcongr
    have h2 : (1 : ℝ) ≤ (2 * gridK d ρ R + 1 : ℝ) ^ D := one_le_pow₀ (by linarith)
    linarith
  have hlog : (D : ℝ) * Real.log Y + Real.log (3 / δ) ≤ m * η ^ 2 / 8 := by
    have := hm
    rw [sampleSize, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    have hD : ((d * d + d + 3 : ℕ) : ℝ) = (d : ℝ) * d + d + 3 := by push_cast; ring
    rw [hD]
    linarith
  calc bound d m η ρ R ≤ 3 * Y ^ D * exp (-(m * η ^ 2 / 8)) := by
        rw [bound]
        gcongr
    _ ≤ 3 * Y ^ D * exp (-((D : ℝ) * Real.log Y + Real.log (3 / δ))) := by
        gcongr
    _ = δ := by
        have e1 : Y ^ D = exp (D * Real.log Y) := by rw [Real.exp_nat_mul, Real.exp_log hY0]
        have e2 : (D : ℝ) * Real.log Y + -((D : ℝ) * Real.log Y + Real.log (3 / δ)) =
            -Real.log (3 / δ) := by ring
        rw [e1, mul_assoc, ← Real.exp_add, e2, Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- **Uniform window counts with probability `1 - δ`.** For `0 < η`, `0 < ρ ≤ 1`, `0 < R` with
`4 d ≤ η R²`, `0 < δ` and `m ≥ (8 / η²) ((d² + d + 3) log(11 (dR + 1)² / ρ) + log(3 / δ))`, there
is a measurable set `B` of samples of probability at most `δ` such that every sample outside `B`
has uniform window counts. -/
theorem exists_bad_set_of_le {η ρ R δ : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 0 < R)
    (hdR : 4 * d ≤ η * R ^ 2) (hδ : 0 < δ) (hm : sampleSize d η ρ R δ ≤ m) :
    ∃ B : Set (Fin m → EuclideanSpace ℝ (Fin d)), MeasurableSet B ∧
      (∀ g ∉ B, UnifWin η ρ R g) ∧
      (Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))) B ≤
        ENNReal.ofReal δ := by
  obtain ⟨B, hB, hgood, hP⟩ := exists_bad_set (m := m) hη hρ0 hρ1 hR hdR
  exact ⟨B, hB, hgood, hP.trans (ENNReal.ofReal_le_ofReal (bound_le hη hρ0 hρ1 hR.le hδ hm))⟩

/-! ### Perturbed samples (rounding) -/

/-- **Counts of a perturbed sample, upper bound.** If `‖g' l - g l‖ ≤ θ` for all `l`, then the
points of `g'` in `[a, b]` are at most the points of `g` in `[a - τ, b + τ]`,
`τ = θ (2R + 1) + θ²`, plus the points of `g` of norm more than `R`. -/
theorem winCount_le_of_near {q : Quad d} (hq : q.normSq ≤ 1)
    {g g' : Fin m → EuclideanSpace ℝ (Fin d)} {θ : ℝ} (hθ : ∀ l, ‖g' l - g l‖ ≤ θ) (R a b : ℝ) :
    (winCount q a b g' : ℝ) ≤ winCount q (a - (θ * (2 * R + 1) + θ ^ 2))
      (b + (θ * (2 * R + 1) + θ ^ 2)) g + normCount R g := by
  refine card_filter_le_add fun l hl ↦ ?_
  by_cases h : R < ‖g l‖
  · exact Or.inr h
  · have hθ0 : 0 ≤ θ := (norm_nonneg _).trans (hθ l)
    have h1 := abs_le.1 (Quad.abs_eval_sub_le hq (hθ l))
    have h2 : θ * (2 * ‖g l‖ + 1) ≤ θ * (2 * R + 1) := by gcongr; exact not_lt.1 h
    obtain ⟨hl1, hl2⟩ := hl
    exact Or.inl ⟨by linarith, by linarith⟩

/-- **Counts of a perturbed sample, lower bound.** If `‖g' l - g l‖ ≤ θ` for all `l`, then the
points of `g` in `[a + τ, b - τ]`, `τ = θ (2R + 1) + θ²`, are at most the points of `g'` in
`[a, b]` plus the points of `g` of norm more than `R`. -/
theorem le_winCount_of_near {q : Quad d} (hq : q.normSq ≤ 1)
    {g g' : Fin m → EuclideanSpace ℝ (Fin d)} {θ : ℝ} (hθ : ∀ l, ‖g' l - g l‖ ≤ θ) (R a b : ℝ) :
    (winCount q (a + (θ * (2 * R + 1) + θ ^ 2)) (b - (θ * (2 * R + 1) + θ ^ 2)) g : ℝ) ≤
      winCount q a b g' + normCount R g := by
  refine card_filter_le_add fun l hl ↦ ?_
  by_cases h : R < ‖g l‖
  · exact Or.inr h
  · have hθ0 : 0 ≤ θ := (norm_nonneg _).trans (hθ l)
    have h1 := abs_le.1 (Quad.abs_eval_sub_le hq (hθ l))
    have h2 : θ * (2 * ‖g l‖ + 1) ≤ θ * (2 * R + 1) := by gcongr; exact not_lt.1 h
    obtain ⟨hl1, hl2⟩ := hl
    exact Or.inl ⟨by linarith, by linarith⟩

/-- **Uniform window counts for a perturbed sample, upper bound**: with `τ = θ (2R + 1) + θ²`,
the points of `g'` in `[a, b]` are at most `(P(q(G) ∈ [a - τ - ρ, b + τ + ρ]) + 2η) m`. -/
theorem UnifWin.winCount_le_of_near {η ρ R : ℝ} {g g' : Fin m → EuclideanSpace ℝ (Fin d)}
    (hW : UnifWin η ρ R g) {θ : ℝ} (hθ : ∀ l, ‖g' l - g l‖ ≤ θ) {q : Quad d}
    (hq : q.normSq ≤ 1) (a b : ℝ) :
    (winCount q a b g' : ℝ) ≤ (winProb q (a - (θ * (2 * R + 1) + θ ^ 2) - ρ)
      (b + (θ * (2 * R + 1) + θ ^ 2) + ρ) + 2 * η) * m := by
  have h1 := Unif.winCount_le_of_near hq hθ R a b
  have h2 := hW.winCount_le q hq (a - (θ * (2 * R + 1) + θ ^ 2)) (b + (θ * (2 * R + 1) + θ ^ 2))
  have h3 := hW.normCount_le
  linarith

/-- **Uniform window counts for a perturbed sample, lower bound**: with `τ = θ (2R + 1) + θ²`,
the points of `g'` in `[a, b]` are at least `(P(q(G) ∈ [a + τ + ρ, b - τ - ρ]) - 2η) m`. -/
theorem UnifWin.le_winCount_of_near {η ρ R : ℝ} {g g' : Fin m → EuclideanSpace ℝ (Fin d)}
    (hW : UnifWin η ρ R g) {θ : ℝ} (hθ : ∀ l, ‖g' l - g l‖ ≤ θ) {q : Quad d}
    (hq : q.normSq ≤ 1) (a b : ℝ) :
    (winProb q (a + (θ * (2 * R + 1) + θ ^ 2) + ρ) (b - (θ * (2 * R + 1) + θ ^ 2) - ρ) -
      2 * η) * m ≤ winCount q a b g' := by
  have h1 := Unif.le_winCount_of_near hq hθ R a b
  have h2 := hW.le_winCount q hq (a + (θ * (2 * R + 1) + θ ^ 2)) (b - (θ * (2 * R + 1) + θ ^ 2))
  have h3 := hW.normCount_le
  linarith

end ABBKS26.Unif
