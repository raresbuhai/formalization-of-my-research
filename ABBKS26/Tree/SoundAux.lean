module

public import ABBKS26.Tree.Split
public import Mathlib.Data.Finset.Lattice.Fold

/-! Coordinate and counting lemmas for arbitrary split soundness. -/

@[expose] public section

namespace ABBKS26.Tree.SoundAux

noncomputable section

open Common Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal MatrixOrder

variable {n k d : ℕ}

theorem eval_cast (q : Statistic d) (x : Fin d → ℚ) :
    q.eval (fun i ↦ (x i : ℝ)) = (q.evalQ x : ℝ) := by
  simp only [Statistic.eval, Statistic.evalQ, qform, dotProduct, mulVec, map_apply,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  rfl

def sym (q : Statistic d) : Mat d :=
  Robust.FilterAux.symmetricPart (q.A.map (algebraMap ℚ ℝ))

theorem sym_transpose (q : Statistic d) : (sym q)ᵀ = sym q :=
  Robust.FilterAux.symmetricPart_symmetric _

theorem eval_sym (q : Statistic d) (x : Vec d) :
    q.eval x = qform (sym q) x + (fun i ↦ (q.b i : ℝ)) ⬝ᵥ x + q.c := by
  rw [sym, Robust.FilterAux.qform_symmetricPart]
  rfl

def coordinates (M : Mixture k d) (j : Fin k) (q : Statistic d) : Unif.Quad d :=
  let R := CFC.sqrt (M.S j)
  ⟨R * sym q * R, R *ᵥ ((2 : ℝ) • (sym q *ᵥ M.μ j) + fun i ↦ (q.b i : ℝ)), 0⟩

theorem coordinates_sym (M : Mixture k d) (j : Fin k) (q : Statistic d) :
    (coordinates M j q).Aᵀ = (coordinates M j q).A := by
  simp only [coordinates, transpose_mul, ProbBasic.transpose_sqrt, sym_transpose, mul_assoc]

theorem coordinates_eval (M : Mixture k d) (hM : M.Valid) (j : Fin k)
    (q : Statistic d) (y : EuclideanSpace ℝ (Fin d)) :
    q.eval y.ofLp = (coordinates M j q).eval (stdPt M j y) + q.eval (M.μ j) := by
  let R := CFC.sqrt (M.S j)
  let g := (stdPt M j y).ofLp
  have hR : R * R⁻¹ = 1 := mul_nonsing_inv _ (ProbBasic.isUnit_det_sqrt (hM.posDef j))
  have hy : y.ofLp = R *ᵥ g + M.μ j := by
    change y.ofLp = R *ᵥ (R⁻¹ *ᵥ (y.ofLp - M.μ j)) + M.μ j
    rw [mulVec_mulVec, hR, one_mulVec, sub_add_cancel]
  rw [eval_sym, Unif.Quad.eval_eq_dotProduct]
  change qform (sym q) y.ofLp + (fun i ↦ (q.b i : ℝ)) ⬝ᵥ y.ofLp + q.c =
    g ⬝ᵥ ((R * sym q * R) *ᵥ g) +
      (R *ᵥ ((2 : ℝ) • (sym q *ᵥ M.μ j) + fun i ↦ (q.b i : ℝ))) ⬝ᵥ g + 0 +
        q.eval (M.μ j)
  rw [hy, Robust.FilterAux.qform_add_symmetric _ (sym_transpose q), eval_sym]
  unfold qform
  rw [Population.mulVec_dotProduct_mulVec]
  have hRt : Rᵀ = R := ProbBasic.transpose_sqrt
  have hbil (u : Vec d) : u ⬝ᵥ (R *ᵥ g) = (R *ᵥ u) ⬝ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hRt]
  rw [hRt, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul,
    dotProduct_add, hbil, hbil]
  ring

theorem quad_variance (q : Unif.Quad d) (hq : q.Aᵀ = q.A) :
    variance q.eval (stdGaussian (EuclideanSpace ℝ (Fin d))) =
      2 * frobSq q.A + sqnorm q.b := by
  have hA : q.A.IsHermitian := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    using hq
  have h := Population.variance_quadStat_multivariateGaussian
    (S := (1 : Mat d)) (by exact Matrix.PosSemidef.one) hA q.b q.c
  rw [multivariateGaussian_zero_one] at h
  have heval : q.eval = Population.quadStat q.A q.b q.c := by
    funext y
    exact q.eval_eq_dotProduct y
  rw [heval, h, mul_one, one_mulVec]
  congr 1
  simp only [trace, diag, Matrix.mul_apply, frobSq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : q.A j i = q.A i j := congrFun (congrFun hq i) j
  rw [he, pow_two]

theorem coordinates_variance (M : Mixture k d) (hM : M.Valid) (j : Fin k)
    (q : Statistic d) :
    variance (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) =
      2 * frobSq (coordinates M j q).A + sqnorm (coordinates M j q).b := by
  let P := multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  let Q := coordinates M j q
  have hf : (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp) =
      (fun y ↦ Q.eval (stdPt M j y) + q.eval (M.μ j)) := by
    funext y
    exact coordinates_eval M hM j q y
  have hv := variance_map Q.measurable_eval.aemeasurable
    (measurable_stdPt_right M j).aemeasurable (μ := P)
  rw [map_stdPt_multivariateGaussian hM j] at hv
  rw [hf]
  change variance (fun y ↦ (Q.eval ∘ stdPt M j) y + q.eval (M.μ j)) P = _
  rw [variance_add_const
    (Q.measurable_eval.comp (measurable_stdPt_right M j)).aestronglyMeasurable, ← hv,
    quad_variance Q (coordinates_sym M j q)]

def normalize (q : Unif.Quad d) (s : ℝ) : Unif.Quad d :=
  ⟨s⁻¹ • q.A, s⁻¹ • q.b, s⁻¹ * q.c⟩

theorem normalize_eval (q : Unif.Quad d) (s : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    (normalize q s).eval y = q.eval y / s := by
  simp only [normalize, Unif.Quad.eval, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, mul_assoc]
  ring

theorem normalize_norm (q : Unif.Quad d) (s : ℝ) :
    (normalize q s).normSq = q.normSq / s ^ 2 := by
  simp only [normalize, Unif.Quad.normSq, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    mul_pow, ← Finset.mul_sum]
  ring

theorem coordinates_norm_le_variance (M : Mixture k d) (hM : M.Valid) (j : Fin k)
    (q : Statistic d) :
    (coordinates M j q).normSq ≤
      variance (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) := by
  rw [coordinates_variance M hM j q]
  have hc : (coordinates M j q).c = 0 := rfl
  simp only [Unif.Quad.normSq, hc, sqnorm, dotProduct, ← pow_two, zero_pow two_ne_zero,
    add_zero]
  have hh : 0 ≤ frobSq (coordinates M j q).A :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold frobSq at hh ⊢
  linarith only [hh]

theorem quad_norm_nonneg (q : Unif.Quad d) : 0 ≤ q.normSq := by
  exact add_nonneg
    (add_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)) (sq_nonneg _)

theorem quad_zero (q : Unif.Quad d) (hq : q.normSq = 0) (y : EuclideanSpace ℝ (Fin d)) :
    q.eval y = 0 := by
  have hA (i j : Fin d) : q.A i j = 0 := by
    have hh := q.sq_le_normSq_A i j
    rw [hq] at hh
    nlinarith only [hh, sq_nonneg (q.A i j)]
  have hb (i : Fin d) : q.b i = 0 := by
    have hh := q.sq_le_normSq_b i
    rw [hq] at hh
    nlinarith only [hh, sq_nonneg (q.b i)]
  have hc : q.c = 0 := by
    have hh := q.sq_le_normSq_c
    rw [hq] at hh
    nlinarith only [hh, sq_nonneg q.c]
  simp [Unif.Quad.eval, hA, hb, hc]

theorem reindex_count (s : Finset (Fin n)) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (q : Unif.Quad d) (a b : ℝ) :
    Unif.winCount q a b (reindex s x) =
      (s.filter fun l ↦ q.eval (x l) ∈ Set.Icc a b).card := by
  classical
  refine Finset.card_bij (fun t _ ↦ s.orderEmbOfFin rfl t) ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_filter.mpr ⟨s.orderEmbOfFin_mem rfl t, (Finset.mem_filter.mp ht).2⟩
  · intro t _ u _ htu
    exact (s.orderEmbOfFin rfl).injective htu
  · intro l hl
    obtain ⟨t, ht⟩ := (s.orderIsoOfFin rfl).surjective ⟨l, (Finset.mem_filter.mp hl).1⟩
    have ht' : s.orderEmbOfFin rfl t = l := congrArg Subtype.val ht
    refine ⟨t, ?_, ht'⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change q.eval (x (s.orderEmbOfFin rfl t)) ∈ Set.Icc a b
    rw [ht']
    exact (Finset.mem_filter.mp hl).2

def uncorrupt (ω : Fin n → Triple k d) : Fin n → Triple k d :=
  fun l ↦ ((ω l).1, (ω l).2.1, (ω l).2.1)

theorem uncorrupt_good (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (hg : Good M ε w η D ω) :
    Good M ε w η D (uncorrupt ω) := by
  refine ⟨hg.1, ?_, hg.2.2.1, hg.2.2.2⟩
  have hh := (Nat.cast_nonneg (α := ℝ) (corrupted ω).card).trans hg.2.1
  simpa [uncorrupt, corrupted] using hh

theorem clean_window_upper (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (q : Unif.Quad d) (hq : q.normSq ≤ 1) (a b : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      q.eval (stdPt M j (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))) ∈
        Set.Icc a b).card : ℝ) ≤
      (Unif.winProb q (a - 2 * η) (b + 2 * η) + η) * (cluster (labels ω) j).card := by
  have hh := rounded_windows_upper M ε w η D (uncorrupt ω) r hM
    (uncorrupt_good M ε w η D ω hg) hr hη hn j q hq a b
  dsimp only at hh
  rw [reindex_count] at hh
  have hcl : cluster (labels (uncorrupt ω)) j = cluster (labels ω) j := rfl
  have hbad : corrupted (uncorrupt ω) = ∅ := by ext l; simp [corrupted, uncorrupt]
  rw [hcl, hbad, Finset.empty_inter, Finset.card_empty, Nat.cast_zero, add_zero] at hh
  refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hh
  intro l hl
  obtain ⟨hlclean, hlwin⟩ := Finset.mem_filter.mp hl
  obtain ⟨hlj, hlbad⟩ := Finset.mem_sdiff.mp hlclean
  have hj : (ω l).1 = j := (Finset.mem_filter.mp hlj).2
  have hy : (ω l).2.1 = (ω l).2.2 := not_not.mp (mem_corrupted.not.mp hlbad)
  apply Finset.mem_filter.mpr
  refine ⟨hlj, ?_⟩
  simpa only [uncorrupt, hj, hy] using hlwin

structure CoordinateSpec (M : Mixture k d) (j : Fin k) (f : Statistic d) where
  q : Unif.Quad d
  s : ℝ
  c : ℝ
  nonneg : 0 ≤ s
  norm : q.normSq ≤ 1
  eval : ∀ y : EuclideanSpace ℝ (Fin d), f.eval y.ofLp = s * q.eval (stdPt M j y) + c
  variance : s ^ 2 ≤ variance (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp)
    (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))

theorem exists_coordinates (M : Mixture k d) (hM : M.Valid) (j : Fin k) (f : Statistic d) :
    Nonempty (CoordinateSpec M j f) := by
  let Q := coordinates M j f
  let s := Real.sqrt Q.normSq
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Q.normSq := Real.sq_sqrt (quad_norm_nonneg Q)
  by_cases hs0 : s = 0
  · have hQ : Q.normSq = 0 := by rw [← hs2, hs0]; norm_num
    refine ⟨⟨⟨0, 0, 0⟩, 0, f.eval (M.μ j), le_rfl, ?_, ?_, ?_⟩⟩
    · simp [Unif.Quad.normSq]
    · intro y
      rw [coordinates_eval M hM, quad_zero Q hQ]
      ring
    · simpa only [zero_pow two_ne_zero] using variance_nonneg
        (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp)
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
  · refine ⟨⟨normalize Q s, s, f.eval (M.μ j), hs, ?_, ?_, ?_⟩⟩
    · rw [normalize_norm, ← hs2, div_self (pow_ne_zero _ hs0)]
    · intro y
      rw [normalize_eval, mul_div_cancel₀ _ hs0, coordinates_eval M hM]
    · rw [hs2]
      exact coordinates_norm_le_variance M hM j f

theorem CoordinateSpec.prob_window (M : Mixture k d) (hM : M.Valid) (j : Fin k)
    (f : Statistic d) (C : CoordinateSpec M j f) (hs : 0 < C.s) (a b : ℝ) :
    Unif.winProb C.q a b =
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | C.s * a + C.c ≤ f.eval y.ofLp ∧ f.eval y.ofLp ≤ C.s * b + C.c} := by
  have hm : MeasurableSet {x | C.q.eval x ∈ Set.Icc a b} :=
    C.q.measurable_eval measurableSet_Icc
  rw [Unif.winProb, ← map_stdPt_multivariateGaussian hM j,
    map_measureReal_apply (measurable_stdPt_right M j) hm]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq, C.eval]
  constructor
  · rintro ⟨ha, hb⟩
    constructor <;> nlinarith only [ha, hb, hs]
  · rintro ⟨ha, hb⟩
    constructor <;> nlinarith only [ha, hb, hs]

theorem CoordinateSpec.upper_window (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : CoordinateSpec M j f) (hs : 0 < C.s) (a b : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      a ≤ (f.evalQ (r ((ω l).1, (ω l).2.2)) : ℝ) ∧
        (f.evalQ (r ((ω l).1, (ω l).2.2)) : ℝ) ≤ b).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | a - 2 * η * C.s ≤ f.eval y.ofLp ∧ f.eval y.ofLp ≤ b + 2 * η * C.s} + η) *
          (cluster (labels ω) j).card := by
  have hh := clean_window_upper M ε w η D ω r hM hg hr hη hn j C.q C.norm
    ((a - C.c) / C.s) ((b - C.c) / C.s)
  rw [C.prob_window M hM j f hs] at hh
  have ha : C.s * ((a - C.c) / C.s - 2 * η) + C.c = a - 2 * η * C.s := by
    field_simp
    ring
  have hb : C.s * ((b - C.c) / C.s + 2 * η) + C.c = b + 2 * η * C.s := by
    field_simp
    ring
  rw [ha, hb] at hh
  convert hh using 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l _
  have he := C.eval (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))
  change f.eval (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)) = _ at he
  rw [← eval_cast, he]
  simp only [Set.mem_Icc, div_le_iff₀ hs, le_div_iff₀ hs]
  constructor <;> rintro ⟨ha', hb'⟩ <;> constructor <;> linarith only [ha', hb']

def value (f : Statistic d) (ω : Fin n → Triple k d) (r : Rounding k d) (l : Fin n) : ℝ :=
  (f.evalQ (r ((ω l).1, (ω l).2.2)) : ℝ)

theorem value_abs_le_sum (f : Statistic d) (ω : Fin n → Triple k d)
    (r : Rounding k d) (l : Fin n) :
    |value f ω r l| ≤ ∑ i, |value f ω r i| :=
  Finset.single_le_sum (f := fun i ↦ |value f ω r i|)
    (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ l)

theorem CoordinateSpec.upper_left (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : CoordinateSpec M j f) (hs : 0 < C.s) (t : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦ value f ω r l ≤ t).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | f.eval y.ofLp ≤ t + 2 * η * C.s} + η) * (cluster (labels ω) j).card := by
  classical
  let a := -(∑ i, |value f ω r i|)
  have hh := C.upper_window M ε w η D ω r hM hg hr hη hn j f hs a t
  have he : ((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      a ≤ value f ω r l ∧ value f ω r l ≤ t) =
      ((cluster (labels ω) j \ corrupted ω).filter fun l ↦ value f ω r l ≤ t) := by
    apply Finset.filter_congr
    intro l _
    have ha : a ≤ value f ω r l := by
      have h := value_abs_le_sum f ω r l
      have h' := neg_abs_le (value f ω r l)
      dsimp only [a]
      linarith only [h, h']
    exact and_iff_right ha
  change (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
    a ≤ value f ω r l ∧ value f ω r l ≤ t).card : ℝ) ≤ _ at hh
  rw [he] at hh
  refine hh.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (Nat.cast_nonneg _))
  exact measureReal_mono fun _ hy ↦ hy.2

theorem CoordinateSpec.upper_right (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : CoordinateSpec M j f) (hs : 0 < C.s) (t : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦ t < value f ω r l).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | t - 2 * η * C.s < f.eval y.ofLp} + η) * (cluster (labels ω) j).card := by
  classical
  let B := (cluster (labels ω) j \ corrupted ω).filter fun l ↦ t < value f ω r l
  by_cases hB : B.Nonempty
  · let a := B.inf' hB (value f ω r)
    let b := ∑ i, |value f ω r i|
    have ha : t < a := (Finset.lt_inf'_iff hB).mpr fun l hl ↦ (Finset.mem_filter.mp hl).2
    have hsub : B ⊆ (cluster (labels ω) j \ corrupted ω).filter fun l ↦
        a ≤ value f ω r l ∧ value f ω r l ≤ b := by
      intro l hl
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_filter.mp hl).1, Finset.inf'_le _ hl, ?_⟩
      exact (le_abs_self _).trans (value_abs_le_sum f ω r l)
    have hh := C.upper_window M ε w η D ω r hM hg hr hη hn j f hs a b
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hh.trans ?_)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply add_le_add _ le_rfl
    exact measureReal_mono fun y hy ↦ by
      change t - 2 * η * C.s < f.eval y.ofLp
      linarith only [ha, hy.1]
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (add_nonneg measureReal_nonneg hη.1.le) (Nat.cast_nonneg _)

theorem CoordinateSpec.lower_window (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : CoordinateSpec M j f) (hs : 0 < C.s) (a b : ℝ) :
    ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | a + 2 * η * C.s ≤ f.eval y.ofLp ∧ f.eval y.ofLp ≤ b - 2 * η * C.s} - η) *
        (cluster (labels ω) j).card ≤
      ((cluster (labels ω) j).filter fun l ↦
        a ≤ value f ω r l ∧ value f ω r l ≤ b).card +
          (corrupted ω ∩ cluster (labels ω) j).card := by
  have hh := rounded_windows M ε w η D ω r hM hg hr hη hn j C.q C.norm
    ((a - C.c) / C.s) ((b - C.c) / C.s)
  dsimp only at hh
  rw [reindex_count, C.prob_window M hM j f hs] at hh
  have ha : C.s * ((a - C.c) / C.s + 2 * η) + C.c = a + 2 * η * C.s := by
    field_simp
    ring
  have hb : C.s * ((b - C.c) / C.s - 2 * η) + C.c = b - 2 * η * C.s := by
    field_simp
    ring
  rw [ha, hb] at hh
  convert hh using 2
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l hl
  have hj : (ω l).1 = j := (Finset.mem_filter.mp hl).2
  have he := C.eval (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))
  change f.eval (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)) = _ at he
  rw [hj] at he
  simp only [value, ← eval_cast, hj, he, Set.mem_Icc, div_le_iff₀ hs, le_div_iff₀ hs]
  constructor <;> rintro ⟨ha', hb'⟩ <;> constructor <;> linarith only [ha', hb']

theorem good_cluster_pos (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (hg : Good M ε w η D ω) (j : Fin k) :
    0 < (cluster (labels ω) j).card := by
  by_contra hc
  have hc0 : (cluster (labels ω) j).card = 0 := by omega
  apply hg.2.2.1 j
  apply Or.inl
  simp [Unif.upperBad, Unif.indCount, hc0]

theorem good_eta_pos (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (hg : Good M ε w η D ω) (j : Fin k) : 0 < η := by
  classical
  by_contra hη
  have hη0 : η ≤ 0 := le_of_not_gt hη
  let K := Unif.gridK d (η / 4) (radius d η)
  have hnet : (Unif.net d K).Nonempty := by
    rw [← Finset.card_pos, Unif.card_net]
    positivity
  obtain ⟨z, hz⟩ := hnet
  let S := Unif.netSet (Unif.meshC d (η / 4) (radius d η)) (η / 4 / 2) z
  let g := clusterPts M ω j
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hh : (η / 16) * (cluster (labels ω) j).card ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  apply hg.2.2.1 j
  right
  apply Set.mem_iUnion.mpr
  refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
  by_cases hu : (μ.real S + η / 16) * (cluster (labels ω) j).card ≤ Unif.indCount S g
  · left
    change (μ.real S + η / 4 / 4) * (cluster (labels ω) j).card ≤ _
    convert hu using 1; ring
  · right
    change Unif.indCount S g ≤ (μ.real S - η / 4 / 4) * (cluster (labels ω) j).card
    dsimp only [g] at hu
    push Not at hu
    nlinarith only [hu, hh]

theorem foldl_max_le_iff (l : List ℝ) (a b : ℝ) :
    l.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ l, x ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc, and_left_comm]

theorem leakage_component (ω : Fin n → Triple k d) (N : Finset (Fin n))
    (I : Finset (Fin k)) (Φ : ℝ) (hΦ : leakage ω N I ≤ Φ) (j : Fin k) :
    (if j ∈ I then (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ)
      else (((cluster (labels ω) j \ corrupted ω) ∩ N).card : ℝ)) ≤
        Φ * (cluster (labels ω) j).card := by
  classical
  have hh := ((foldl_max_le_iff _ 0 Φ).mp hΦ).2 _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  by_cases hc : (cluster (labels ω) j).card = 0
  · have hz := Finset.card_eq_zero.mp hc
    simp [hz]
  · have hc0 : (0 : ℝ) < (cluster (labels ω) j).card :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
    change (if j ∈ I then _ / _ else _ / _) ≤ Φ at hh
    split_ifs at hh ⊢ <;> exact (div_le_iff₀ hc0).mp hh

theorem leakage_le_of_counts (ω : Fin n → Triple k d) (N : Finset (Fin n))
    (I : Finset (Fin k)) (Φ : ℝ) (hΦ : 0 ≤ Φ)
    (hc : ∀ j, (if j ∈ I then (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ)
      else (((cluster (labels ω) j \ corrupted ω) ∩ N).card : ℝ)) ≤
        Φ * (cluster (labels ω) j).card) : leakage ω N I ≤ Φ := by
  classical
  apply (foldl_max_le_iff _ 0 Φ).mpr
  refine ⟨hΦ, ?_⟩
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  have hh := hc j
  by_cases hz : (cluster (labels ω) j).card = 0
  · have he := Finset.card_eq_zero.mp hz
    simpa [he] using hΦ
  · have hp : (0 : ℝ) < (cluster (labels ω) j).card :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    split_ifs at hh ⊢ <;> exact (div_le_iff₀ hp).mpr hh

theorem sum_cluster_card (ω : Fin n → Triple k d) (s : Finset (Fin n)) :
    ∑ j, ((s ∩ cluster (labels ω) j).card : ℝ) = s.card := by
  classical
  have he : ∀ j, s ∩ cluster (labels ω) j = s.filter (labels ω · = j) := by
    intro j
    ext l
    simp [cluster]
  simp_rw [he]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]

theorem empty_leakage_bound (ω : Fin n → Triple k d) (N : Finset (Fin n)) (Φ : ℝ)
    (hΦ : leakage ω N ∅ ≤ Φ) : (N.card : ℝ) ≤ Φ * n + (corrupted ω).card := by
  classical
  have hh : ((N \ corrupted ω).card : ℝ) ≤ Φ * n := by
    rw [← sum_cluster_card ω (N \ corrupted ω)]
    calc ∑ j, (((N \ corrupted ω) ∩ cluster (labels ω) j).card : ℝ) ≤
        ∑ j, Φ * (cluster (labels ω) j).card := by
          apply Finset.sum_le_sum
          intro j _
          have hj := leakage_component ω N ∅ Φ hΦ j
          have he : (N \ corrupted ω) ∩ cluster (labels ω) j =
              (cluster (labels ω) j \ corrupted ω) ∩ N := by ext l; simp; tauto
          simpa only [he, Finset.notMem_empty, ite_false] using hj
      _ = Φ * n := by
        rw [← Finset.mul_sum]
        have he := sum_cluster_card ω Finset.univ
        simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at he
        rw [he]
  have hsub : N ⊆ (N \ corrupted ω) ∪ corrupted ω := by intro l hl; simp; tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact (Nat.cast_le.mpr hc).trans (by push_cast; linarith only [hh])

theorem partition_leakage (ω : Fin n → Triple k d) (N A B : Finset (Fin n))
    (I : Finset (Fin k)) (Φ u ξ w : ℝ) (hΦ : leakage ω N I ≤ Φ) (hu : 0 ≤ u)
    (hpart : A ∪ B = N) (hbad : (corrupted ω).card ≤ ξ * n)
    (hsizeA : w * n / 4 ≤ A.card) (hsizeB : w * n / 4 ≤ B.card)
    (hn : 0 < (n : ℝ)) (hsmall : Φ + u + ξ < w / 4)
    (hcomp : ∀ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω) ∩ A).card : ℝ) ≤
          u * (cluster (labels ω) j).card ∨
      (((cluster (labels ω) j \ corrupted ω) ∩ B).card : ℝ) ≤
          u * (cluster (labels ω) j).card) :
    ∃ L R : Finset (Fin k), L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L ∪ R = I ∧
      leakage ω A L ≤ Φ + u ∧ leakage ω B R ≤ Φ + u := by
  classical
  let L := I.filter fun j ↦ (((cluster (labels ω) j \ corrupted ω) ∩ B).card : ℝ) ≤
    u * (cluster (labels ω) j).card
  let R := I \ L
  have hΦ0 := ((foldl_max_le_iff _ 0 Φ).mp hΦ).1
  have hΓ : 0 ≤ Φ + u := add_nonneg hΦ0 hu
  have hR (j : Fin k) (hj : j ∈ R) :
      (((cluster (labels ω) j \ corrupted ω) ∩ A).card : ℝ) ≤
        u * (cluster (labels ω) j).card := by
    obtain ⟨hjI, hjL⟩ := Finset.mem_sdiff.mp hj
    exact (hcomp j hjI).resolve_right (fun h ↦ hjL (Finset.mem_filter.mpr ⟨hjI, h⟩))
  have hL (j : Fin k) (hj : j ∈ L) :
      (((cluster (labels ω) j \ corrupted ω) ∩ B).card : ℝ) ≤
        u * (cluster (labels ω) j).card := (Finset.mem_filter.mp hj).2
  have bound (X Y : Finset (Fin n)) (J : Finset (Fin k))
      (hXY : X ∪ Y = N) (hJN : J ⊆ I)
      (hJ : ∀ j ∈ J, (((cluster (labels ω) j \ corrupted ω) ∩ Y).card : ℝ) ≤
        u * (cluster (labels ω) j).card)
      (hIJ : ∀ j ∈ I, j ∉ J →
        (((cluster (labels ω) j \ corrupted ω) ∩ X).card : ℝ) ≤
          u * (cluster (labels ω) j).card) : leakage ω X J ≤ Φ + u := by
    apply leakage_le_of_counts ω X J (Φ + u) hΓ
    intro j
    have hj := leakage_component ω N I Φ hΦ j
    by_cases hjJ : j ∈ J
    · have hjI := hJN hjJ
      simp only [hjJ, hjI, ite_true] at hj ⊢
      have hs : (cluster (labels ω) j \ corrupted ω) \ X ⊆
          ((cluster (labels ω) j \ corrupted ω) \ N) ∪
            ((cluster (labels ω) j \ corrupted ω) ∩ Y) := by
        rw [← hXY]
        intro l hl
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hl ⊢
        tauto
      have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
      have hc' : (((cluster (labels ω) j \ corrupted ω) \ X).card : ℝ) ≤
          (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ) +
            (((cluster (labels ω) j \ corrupted ω) ∩ Y).card : ℝ) := by exact_mod_cast hc
      nlinarith only [hc', hj, hJ j hjJ]
    · simp only [hjJ, ite_false]
      by_cases hjI : j ∈ I
      · have hh := hIJ j hjI hjJ
        nlinarith only [hh, mul_nonneg hΦ0 (Nat.cast_nonneg
          (cluster (labels ω) j).card)]
      · simp only [hjI, ite_false] at hj
        have hs : X ⊆ N := by rw [← hXY]; exact Finset.subset_union_left
        have hc : (((cluster (labels ω) j \ corrupted ω) ∩ X).card : ℝ) ≤
            ((cluster (labels ω) j \ corrupted ω) ∩ N).card :=
          Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter_left hs))
        nlinarith only [hc, hj, mul_nonneg hu (Nat.cast_nonneg
          (cluster (labels ω) j).card)]
  have hLA : leakage ω A L ≤ Φ + u := bound A B L hpart (Finset.filter_subset _ _)
    hL (fun j hj hjL ↦ hR j (Finset.mem_sdiff.mpr ⟨hj, hjL⟩))
  have hRB : leakage ω B R ≤ Φ + u := bound B A R (by rw [Finset.union_comm, hpart])
    Finset.sdiff_subset hR (fun j hj hjR ↦ hL j (by
      by_contra hjL
      exact hjR (Finset.mem_sdiff.mpr ⟨hj, hjL⟩)))
  have hnonempty (X : Finset (Fin n)) (J : Finset (Fin k))
      (hX : w * n / 4 ≤ X.card) (hJ : leakage ω X J ≤ Φ + u) : J.Nonempty := by
    by_contra hne
    have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he] at hJ
    have hh := empty_leakage_bound ω X (Φ + u) hJ
    nlinarith only [hh, hX, hbad, mul_pos (sub_pos.mpr hsmall) hn]
  exact ⟨L, R, hnonempty A L hsizeA hLA, hnonempty B R hsizeB hRB,
    Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.filter_subset _ _), hLA, hRB⟩

theorem component_small (M : Mixture k d) (ε η Φ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (p : StepParams) (e : Edge n d)
    (I : Finset (Fin k)) (hM : M.Valid) (hg : Good M ε p.w η D ω)
    (hr : IsRounding M (1 / n) r) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hn : (2 * radius d η + 2) / η ≤ n) (hΦ : leakage ω e.parent I ≤ Φ)
    (hw : 0 < p.w) (hwj : ∀ j, (p.w : ℝ) ≤ M.w j) (hφ : 0 < p.straddle)
    (hΦm : Φ ≤ p.windowMass / 100) (hηm : η ≤ p.windowMass / 100)
    (hξm : ε + η ≤ p.w * p.windowMass / 100)
    (hverify : p.verifyMass = p.w * p.windowMass / 8)
    (hv : Verify p (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e)
    (hpop : ∀ j ∈ I, ∀ C : CoordinateSpec M j e.statistic, 0 < C.s →
      (p.straddle : ℝ) + η ≤
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
          {y | e.statistic.eval y.ofLp ≤ e.threshold + 2 * η * C.s} →
      (p.straddle : ℝ) + η ≤
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
          {y | (e.threshold : ℝ) - 2 * η * C.s < e.statistic.eval y.ofLp} →
      (p.windowMass : ℝ) ≤
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
          {y | (e.lower : ℝ) + 2 * η * C.s ≤ e.statistic.eval y.ofLp ∧
            e.statistic.eval y.ofLp ≤ (e.upper : ℝ) - 2 * η * C.s}) :
    ∀ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω) ∩
        e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card : ℝ) ≤
          ((p.straddle : ℝ) + 8 * η) * (cluster (labels ω) j).card ∨
      (((cluster (labels ω) j \ corrupted ω) ∩
        e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card : ℝ) ≤
          ((p.straddle : ℝ) + 8 * η) * (cluster (labels ω) j).card := by
  classical
  intro j hj
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let Sj := cluster (labels ω) j
  let T := Sj \ corrupted ω
  let f := e.statistic
  let u : ℝ := p.straddle + 8 * η
  have hφ0 : (0 : ℝ) < p.straddle := by exact_mod_cast hφ
  have hη0 := hη.1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hSj : (0 : ℝ) < Sj.card := Nat.cast_pos.mpr (good_cluster_pos M ε p.w η D ω hg j)
  have hn0 : (0 : ℝ) < n := hSj.trans_le
    (Nat.cast_le.mpr ((Finset.card_le_card (Finset.subset_univ Sj)).trans_eq
      (Finset.card_fin n)))
  have hw0 : (0 : ℝ) < p.w := by exact_mod_cast hw
  have hwm : (0 : ℝ) < p.windowMass := by linarith only [hη.1, hηm]
  obtain ⟨C⟩ := exists_coordinates M hM j f
  have hleftsub : T ∩ e.left x ⊆ T.filter fun l ↦ value f ω r l ≤ e.threshold := by
    intro l hl
    obtain ⟨hlT, hlA⟩ := Finset.mem_inter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨hlT, ?_⟩
    have hh := (Finset.mem_filter.mp hlA).2
    change (f.evalQ (x l) : ℝ) ≤ (e.threshold : ℝ)
    exact_mod_cast hh
  have hrightsub : T ∩ e.right x ⊆ T.filter fun l ↦ (e.threshold : ℝ) < value f ω r l := by
    intro l hl
    obtain ⟨hlT, hlB⟩ := Finset.mem_inter.mp hl
    obtain ⟨hlN, hlA⟩ := Finset.mem_sdiff.mp hlB
    apply Finset.mem_filter.mpr
    refine ⟨hlT, ?_⟩
    have hh : e.threshold < f.evalQ (x l) := by
      exact lt_of_not_ge (fun h ↦ hlA (Finset.mem_filter.mpr ⟨hlN, h⟩))
    change (e.threshold : ℝ) < (f.evalQ (x l) : ℝ)
    exact_mod_cast hh
  by_contra hsmall
  push Not at hsmall
  obtain ⟨hbigL, hbigR⟩ := hsmall
  have hbL : u * Sj.card < ((T.filter fun l ↦ value f ω r l ≤ e.threshold).card : ℝ) :=
    hbigL.trans_le (Nat.cast_le.mpr (Finset.card_le_card hleftsub))
  have hbR : u * Sj.card < ((T.filter fun l ↦ (e.threshold : ℝ) < value f ω r l).card : ℝ) :=
    hbigR.trans_le (Nat.cast_le.mpr (Finset.card_le_card hrightsub))
  have hs : 0 < C.s := by
    by_contra hs
    have hs0 : C.s = 0 := le_antisymm (le_of_not_gt hs) C.nonneg
    have hval (l : Fin n) : value f ω r l = C.c := by
      have he := C.eval (WithLp.toLp 2 fun i ↦ (x l i : ℝ))
      change (f.evalQ (x l) : ℝ) = C.c
      simpa only [hs0, zero_mul, zero_add, WithLp.ofLp_toLp, eval_cast] using he
    by_cases ht : C.c ≤ (e.threshold : ℝ)
    · have he : (T.filter fun l ↦ (e.threshold : ℝ) < value f ω r l) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro l _
        rw [hval]
        exact not_lt_of_ge ht
      rw [he, Finset.card_empty, Nat.cast_zero] at hbR
      exact (mul_nonneg hu hSj.le).not_gt hbR
    · have he : (T.filter fun l ↦ value f ω r l ≤ e.threshold) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro l _
        rwa [hval]
      rw [he, Finset.card_empty, Nat.cast_zero] at hbL
      exact (mul_nonneg hu hSj.le).not_gt hbL
  have hUL := C.upper_left M ε p.w η D ω r hM hg hr hη hn j f hs e.threshold
  have hUR := C.upper_right M ε p.w η D ω r hM hg hr hη hn j f hs e.threshold
  have hpL : (p.straddle : ℝ) + η ≤
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | f.eval y.ofLp ≤ e.threshold + 2 * η * C.s} := by
    by_contra hpL
    have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hpL)) hSj.le
    dsimp only [u] at hbL
    nlinarith only [hbL, hUL, hm, mul_pos hη.1 hSj]
  have hpR : (p.straddle : ℝ) + η ≤
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | (e.threshold : ℝ) - 2 * η * C.s < f.eval y.ofLp} := by
    by_contra hpR
    have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hpR)) hSj.le
    dsimp only [u] at hbR
    nlinarith only [hbR, hUR, hm, mul_pos hη.1 hSj]
  have hp := hpop j hj C hs hpL hpR
  have hlo := C.lower_window M ε p.w η D ω r hM hg hr hη hn j f hs e.lower e.upper
  let W := Sj.filter fun l ↦ (e.lower : ℝ) ≤ value f ω r l ∧ value f ω r l ≤ e.upper
  let V := e.parent.filter fun l ↦ e.lower ≤ f.evalQ (x l) ∧ f.evalQ (x l) ≤ e.upper
  have hsub : W ⊆ V ∪ ((T \ e.parent) ∪ corrupted ω) := by
    intro l hl
    obtain ⟨hlS, hlW⟩ := Finset.mem_filter.mp hl
    by_cases hlN : l ∈ e.parent
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      change (e.lower : ℝ) ≤ (f.evalQ (x l) : ℝ) ∧
        (f.evalQ (x l) : ℝ) ≤ (e.upper : ℝ) at hlW
      exact ⟨hlN, by exact_mod_cast hlW⟩
    · apply Finset.mem_union_right
      by_cases hlbad : l ∈ corrupted ω
      · exact Finset.mem_union_right _ hlbad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hlS, hlbad⟩, hlN⟩)
  have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hdel := leakage_component ω e.parent I Φ hΦ j
  simp only [hj, ite_true] at hdel
  have hbad : ((corrupted ω ∩ Sj).card : ℝ) ≤ (corrupted ω).card :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
  have hcard' : (W.card : ℝ) ≤ V.card + (T \ e.parent).card + (corrupted ω).card := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using hcard)
  have hwindow : ((p.windowMass : ℝ) - η - Φ) * Sj.card ≤
      V.card + 2 * (corrupted ω).card := by
    have hm := mul_le_mul_of_nonneg_right hp hSj.le
    nlinarith only [hlo, hm, hdel, hbad, hcard']
  have hV : (V.card : ℝ) ≤ (p.w : ℝ) * p.windowMass / 8 * n := by
    have hv' : (V.card : ℝ) ≤ (p.verifyMass : ℝ) * e.parent.card := by exact_mod_cast hv.1
    have hncard : (e.parent.card : ℝ) ≤ n :=
      Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using Finset.card_le_univ e.parent)
    have he : (p.verifyMass : ℝ) = (p.w : ℝ) * p.windowMass / 8 := by
      exact_mod_cast hverify
    rw [he] at hv'
    exact hv'.trans (mul_le_mul_of_nonneg_left hncard (by positivity))
  have hΓ : (49 / 50 : ℝ) * p.windowMass ≤ (p.windowMass : ℝ) - η - Φ := by
    linarith only [hΦm, hηm]
  have hSj' : (9 / 10 : ℝ) * p.w * n ≤ Sj.card := by
    have hh := ((good_counts M ε p.w η D ω hg ⟨hη.1.le, hη.2⟩).1 j).1
    have hm := mul_le_mul_of_nonneg_right (hwj j) hn0.le
    nlinarith only [hh, hm]
  have hlower := mul_le_mul hΓ hSj' (by positivity)
    (le_trans (by positivity : 0 ≤ (49 / 50 : ℝ) * p.windowMass) hΓ)
  have hξ := mul_le_mul_of_nonneg_right hξm hn0.le
  have hbad' := hg.2.1
  have hpos : 0 < (p.w : ℝ) * p.windowMass * n := by positivity
  nlinarith only [hwindow, hV, hlower, hξ, hbad', hpos]

theorem statistic_memLp (M : Mixture k d) (hM : M.Valid) (j : Fin k) (f : Statistic d) :
    MemLp (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) 2
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) := by
  let Q := coordinates M j f
  let P := multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  have hA : Q.A.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using coordinates_sym M j f
  have hQ := Population.memLp_quadStat_multivariateGaussian
    (S := (1 : Mat d)) Matrix.PosSemidef.one hA Q.b Q.c
  rw [multivariateGaussian_zero_one] at hQ
  have heval : Q.eval = Population.quadStat Q.A Q.b Q.c := by
    funext y
    exact Q.eval_eq_dotProduct y
  rw [← heval, ← map_stdPt_multivariateGaussian hM j,
    memLp_map_measure_iff Q.measurable_eval.aestronglyMeasurable
      (measurable_stdPt_right M j).aemeasurable] at hQ
  have hh := hQ.add (memLp_const (f.eval (M.μ j)))
  convert hh using 1
  funext y
  exact coordinates_eval M hM j f y

theorem spectral_eval (f : Statistic d) (v : Fin d → ℚ)
    (hf : ∀ x, f.evalQ x = (v ⬝ᵥ x) ^ 2) :
    ∀ y : Vec d, f.eval y = ((fun i ↦ (v i : ℝ)) ⬝ᵥ y) ^ 2 := by
  have hd : DenseRange (fun x : Fin d → ℚ ↦ fun i ↦ (x i : ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  have he : f.eval = (fun y : Vec d ↦ ((fun i ↦ (v i : ℝ)) ⬝ᵥ y) ^ 2) := by
    apply hd.equalizer
    · unfold Statistic.eval qform
      fun_prop
    · fun_prop
    · funext x
      simp only [Function.comp_apply, eval_cast, hf, Rat.cast_pow, dotProduct,
        Rat.cast_sum, Rat.cast_mul]
  exact congrFun he

theorem mean_map (M : Mixture k d) (hM : M.Valid) (j : Fin k) (f : Statistic d)
    (hA : f.A = 0) :
    (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).map
      (fun y ↦ f.eval y.ofLp) =
        gaussianReal ((fun i ↦ (f.b i : ℝ)) ⬝ᵥ M.μ j + f.c)
          (qform (M.S j) (fun i ↦ (f.b i : ℝ))).toNNReal := by
  have hf : (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) =
      (fun z : ℝ ↦ z + f.c) ∘ (fun y ↦ (fun i ↦ (f.b i : ℝ)) ⬝ᵥ y.ofLp) := by
    funext y
    simp [Statistic.eval, hA, qform]
  rw [hf, ← Measure.map_map (by fun_prop) (Population.measurable_dotProduct _),
    Population.map_dotProduct_multivariateGaussian (hM.posDef j).posSemidef,
    gaussianReal_map_add_const]
  rfl

theorem mean_variance (M : Mixture k d) (hM : M.Valid) (j : Fin k) (f : Statistic d)
    (hA : f.A = 0) :
    variance (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp)
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) =
        qform (M.S j) (fun i ↦ (f.b i : ℝ)) := by
  have hf : (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) =
      (fun y ↦ (fun i ↦ (f.b i : ℝ)) ⬝ᵥ y.ofLp + f.c) := by
    funext y
    simp [Statistic.eval, hA, qform]
  rw [hf, variance_add_const (Population.measurable_dotProduct _).aestronglyMeasurable,
    Population.variance_dotProduct_multivariateGaussian (hM.posDef j).posSemidef]
  rfl

theorem square_variance (v : ℝ≥0) :
    variance (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  have hX : MemLp (fun z : ℝ ↦ z ^ 2) 2 (gaussianReal 0 v) := by
    apply (TauCeti.memLp_two_eval_gaussianReal 0 v (Polynomial.X ^ 2)).ae_eq
    exact ae_of_all _ (fun _ ↦ Polynomial.eval_X_pow 2)
  have h4 : ∫ z, z ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
    simpa [mul_comm] using TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 v 2
  rw [variance_eq_sub hX]
  change (∫ z, (z ^ 2) ^ 2 ∂gaussianReal 0 v) -
    (∫ z, z ^ 2 ∂gaussianReal 0 v) ^ 2 = _
  have h4' : ∫ z, (z ^ 2) ^ 2 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
    convert h4 using 1
    apply integral_congr_ae
    exact ae_of_all _ (fun z ↦ by ring)
  rw [h4', TauCeti.Probability.integral_sq_gaussianReal]
  norm_num
  ring

theorem spectral_map (M : Mixture k d) (hM : M.Valid) (hcenter : M.IsCentered)
    (j : Fin k) (f : Statistic d) (v : Fin d → ℚ)
    (hf : ∀ x, f.evalQ x = (v ⬝ᵥ x) ^ 2) :
    (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).map
      (fun y ↦ f.eval y.ofLp) =
        (gaussianReal 0 (qform (M.S j) (fun i ↦ (v i : ℝ))).toNNReal).map
          (fun z : ℝ ↦ z ^ 2) := by
  have he : (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) =
      (fun z : ℝ ↦ z ^ 2) ∘ (fun y ↦ (fun i ↦ (v i : ℝ)) ⬝ᵥ y.ofLp) := by
    funext y
    exact spectral_eval f v hf y.ofLp
  rw [he, ← Measure.map_map (by fun_prop) (Population.measurable_dotProduct _),
    Population.map_dotProduct_multivariateGaussian (hM.posDef j).posSemidef]
  congr 2
  simp only [hcenter j, dotProduct_zero]

theorem spectral_variance (M : Mixture k d) (hM : M.Valid) (hcenter : M.IsCentered)
    (j : Fin k) (f : Statistic d) (v : Fin d → ℚ)
    (hf : ∀ x, f.evalQ x = (v ⬝ᵥ x) ^ 2) :
    variance (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp)
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) =
        2 * qform (M.S j) (fun i ↦ (v i : ℝ)) ^ 2 := by
  let P := multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) := by
    unfold Statistic.eval qform
    fun_prop
  have hh := variance_map (μ := P) (X := id) measurable_id.aemeasurable hm.aemeasurable
  rw [spectral_map M hM hcenter j f v hf] at hh
  have hh' := variance_map (μ := gaussianReal 0
    (qform (M.S j) (fun i ↦ (v i : ℝ))).toNNReal)
    (X := id) measurable_id.aemeasurable
    (by fun_prop : Measurable fun z : ℝ ↦ z ^ 2).aemeasurable
  rw [hh'] at hh
  change variance (fun z : ℝ ↦ z ^ 2)
    (gaussianReal 0 (qform (M.S j) (fun i ↦ (v i : ℝ))).toNNReal) =
      variance (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) P at hh
  rw [square_variance] at hh
  have hq : 0 ≤ qform (M.S j) (fun i ↦ (v i : ℝ)) :=
    (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg _
  simpa only [Function.comp_def, id_eq, Real.coe_toNNReal _ hq] using hh.symm

theorem expanded_variance_window {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (φ η s r t W : ℝ) (hφ : 0 < φ ∧ φ ≤ 1) (hs : 0 < s)
    (hη : 0 ≤ η ∧ η ≤ 1 / 100) (hr : 0 ≤ r ∧ r ≤ 2 * η * s)
    (hvar : variance X P ≤ s ^ 2) (hW : 8 * s / Real.sqrt φ ≤ W)
    (hl : φ ≤ P.real {y | X y ≤ t + r}) (hu : φ ≤ P.real {y | t - r < X y}) :
    1 / 2 ≤ P.real {y | t - W + r ≤ X y ∧ X y ≤ t + W - r} := by
  let m := ∫ y, X y ∂P
  have hroot : 0 < Real.sqrt φ := Real.sqrt_pos.mpr hφ.1
  have hroot1 : Real.sqrt φ ≤ 1 := Real.sqrt_le_one.mpr hφ.2
  have hd0 : 0 < s / Real.sqrt φ := div_pos hs hroot
  have hd : s ≤ s / Real.sqrt φ := by
    rw [le_div_iff₀ hroot]
    nlinarith only [hroot1, hs]
  have hupper : m - (t + r) ≤ s / Real.sqrt φ := by
    by_cases hm : m ≤ t + r
    · linarith only [hm, hd0]
    · have hm0 : 0 < m - (t + r) := by linarith only [hm]
      have hc := Population.measureReal_le_of_subset_dev hX hm0
        (s := {y | X y ≤ t + r}) (fun y hy ↦ by
          change X y ≤ t + r at hy
          change m - (t + r) ≤ |X y - m|
          rw [abs_sub_comm, abs_of_nonneg (by linarith only [hy, hm0])]
          linarith only [hy])
      have hh := hl.trans hc
      rw [le_div_iff₀ (by positivity)] at hh
      have hsq : ((m - (t + r)) * Real.sqrt φ) ^ 2 ≤ s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hφ.1.le]
        nlinarith only [hh, hvar]
      have hp := (pow_le_pow_iff_left₀ (by positivity) hs.le two_ne_zero).mp hsq
      rwa [le_div_iff₀ hroot]
  have hlower : (t - r) - m ≤ s / Real.sqrt φ := by
    by_cases hm : t - r ≤ m
    · linarith only [hm, hd0]
    · have hm0 : 0 < t - r - m := by linarith only [hm]
      have hc := Population.measureReal_le_of_subset_dev hX hm0
        (s := {y | t - r < X y}) (fun y hy ↦ by
          change t - r < X y at hy
          change t - r - m ≤ |X y - m|
          rw [abs_of_nonneg (by linarith only [hy, hm0])]
          linarith only [hy])
      have hh := hu.trans hc
      rw [le_div_iff₀ (by positivity)] at hh
      have hsq : ((t - r - m) * Real.sqrt φ) ^ 2 ≤ s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hφ.1.le]
        nlinarith only [hh, hvar]
      have hp := (pow_le_pow_iff_left₀ (by positivity) hs.le two_ne_zero).mp hsq
      rwa [le_div_iff₀ hroot]
  have hdist : |m - t| ≤ s / Real.sqrt φ + r := by
    exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper]⟩
  have hmargin : 2 * s + s / Real.sqrt φ + 2 * r ≤ W := by
    have hηs := mul_le_mul_of_nonneg_right hη.2 hs.le
    have hW' : 8 * (s / Real.sqrt φ) ≤ W := by simpa only [mul_div_assoc] using hW
    linarith only [hW', hd, hr.2, hηs, hs]
  have hc := Population.measureReal_abs_sub_ge_le hX (c := 2 * s) (by positivity)
  have hc' : P.real {y | 2 * s ≤ |X y - m|} ≤ 1 / 4 := by
    refine hc.trans ((div_le_div_of_nonneg_right hvar (by positivity)).trans_eq ?_)
    field_simp
    ring
  have hcover := Population.one_le_measureReal_add (P := P)
    (s := {y | t - W + r ≤ X y ∧ X y ≤ t + W - r})
    (t := {y | 2 * s ≤ |X y - m|}) (fun y ↦ by
      by_cases hy : t - W + r ≤ X y ∧ X y ≤ t + W - r
      · exact Or.inl hy
      · right
        have hh := abs_sub_le (X y) m t
        change 2 * s ≤ |X y - m|
        have hnot : W - r < |X y - t| := by
          by_contra hh
          have habs := abs_le.mp (le_of_not_gt hh)
          exact hy ⟨by linarith only [habs.1], by linarith only [habs.2]⟩
        linarith only [hnot, hh, hdist, hmargin])
  linarith only [hc', hcover]

theorem statistic_measurable (f : Statistic d) :
    Measurable (fun y : EuclideanSpace ℝ (Fin d) ↦ f.eval y.ofLp) := by
  unfold Statistic.eval qform
  fun_prop

theorem statistic_probability (P : Measure (EuclideanSpace ℝ (Fin d))) (f : Statistic d)
    (G : Measure ℝ) (hG : P.map (fun y ↦ f.eval y.ofLp) = G)
    (q : ℝ → Prop) (hq : MeasurableSet {z | q z}) :
    P.real {y | q (f.eval y.ofLp)} = G.real {z | q z} := by
  rw [← hG, map_measureReal_apply (statistic_measurable f) hq]
  rfl

theorem spectral_standard_map (M : Mixture k d) (hM : M.Valid) (hcenter : M.IsCentered)
    (j : Fin k) (f : Statistic d) (v : Fin d → ℚ)
    (hf : ∀ x, f.evalQ x = (v ⬝ᵥ x) ^ 2) :
    (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).map
      (fun y ↦ f.eval y.ofLp) =
        (gaussianReal 0 1).map (fun z : ℝ ↦
          qform (M.S j) (fun i ↦ (v i : ℝ)) * z ^ 2) := by
  let a := qform (M.S j) (fun i ↦ (v i : ℝ))
  have ha : 0 ≤ a := (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg _
  have hg : (gaussianReal 0 1).map (fun z : ℝ ↦ Real.sqrt a * z) =
      gaussianReal 0 a.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, mul_one,
      Real.sq_sqrt ha, Real.coe_toNNReal _ ha]
  rw [spectral_map M hM hcenter j f v hf, ← hg, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, mul_pow, Real.sq_sqrt ha]
  rfl

end

end ABBKS26.Tree.SoundAux
