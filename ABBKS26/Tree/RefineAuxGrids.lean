module

public import ABBKS26.Tree.RefineAuxLists
public import ABBKS26.Tree.RefineAuxIsotropy
public import ABBKS26.Tree.RefineAuxCleanPass

/-! Covering and rounding estimates for the input-determined refinement lists. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix _root_.ABBKS26.Tree
open scoped BigOperators

variable {d : ℕ}

theorem frame_second_qform {k : ℕ} (F : FrameModel k d) (v : Vec d) :
    qform F.second v =
      ∑ i, F.weight i * (qform (F.cov i) v + (v ⬝ᵥ F.mean i) ^ 2) := by
  simp only [FrameModel.second, qform, sum_mulVec, dotProduct_sum, smul_mulVec,
    dotProduct_smul, smul_eq_mul, add_mulVec, dotProduct_add, vecMulVec_mulVec,
    op_smul_eq_smul, dotProduct_comm (F.mean _) v]
  congr 1
  funext i
  ring

/-- Isotropy and a component weight floor bound each projected component mean. -/
theorem projected_mean_bound {k : ℕ} (F : FrameModel k d) (w γ : ℝ)
    (hF : F.Valid w) (hiso : F.Isotropic γ) (j : Fin k) (v : Vec d) :
    w * (v ⬝ᵥ F.mean j) ^ 2 ≤ (1 + γ) * sqnorm v := by
  have hcov (i : Fin k) : 0 ≤ qform (F.cov i) v := by
    exact (hF.2.2.2 i).posSemidef.dotProduct_mulVec_nonneg v
  have hw (i : Fin k) : 0 ≤ F.weight i := hF.1.le.trans (hF.2.1 i)
  have hj : F.weight j * (qform (F.cov j) v + (v ⬝ᵥ F.mean j) ^ 2) ≤
      qform F.second v := by
    rw [frame_second_qform]
    exact Finset.single_le_sum
      (fun i _ ↦ mul_nonneg (hw i) (add_nonneg (hcov i) (sq_nonneg (v ⬝ᵥ F.mean i))))
      (Finset.mem_univ j)
  have hweight := mul_le_mul_of_nonneg_right (hF.2.1 j) (sq_nonneg (v ⬝ᵥ F.mean j))
  have hupper := hiso.2.2 v
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hupper
  change qform F.second v ≤ (1 + γ) * sqnorm v at hupper
  nlinarith only [hweight, hj, hupper, mul_nonneg (hw j) (hcov j)]

/-- Large mean separation in an isotropic frame forces a thin common-covariance direction. -/
theorem mean_thin_direction {k : ℕ} (F : FrameModel k d) (S : Mat d)
    (w γ Δ τ : ℝ) (hF : F.Valid (w / 2)) (hiso : F.Isotropic γ) (hγ : γ ≤ 1)
    (hbudget : 16 ≤ Δ ^ 2 * w * τ) (a b : Fin k)
    (hsep : MeanSeparated Δ (F.mean a) (F.mean b) S) :
    ∃ v, sqnorm v = 1 ∧ qform S v ≤ τ := by
  by_contra h
  have hl (v : Vec d) : τ * sqnorm v ≤ qform S v := by
    apply CompleteAux.lower_of_unit
    intro u hu
    exact le_of_lt (lt_of_not_ge (fun hh ↦ h ⟨u, hu, hh⟩))
  have hw : 0 < w := by linarith only [hF.1]
  obtain ⟨v, hv⟩ := hsep
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hn : 0 < sqnorm v := by
    have hnonneg := Rounding.DetRoundAux.sqnorm_nonneg v
    exact lt_of_le_of_ne hnonneg (Ne.symm
      (fun hh ↦ hv0 (dotProduct_self_eq_zero.mp hh)))
  have ha := projected_mean_bound F (w / 2) γ hF hiso a v
  have hb := projected_mean_bound F (w / 2) γ hF hiso b v
  have hγv := mul_le_mul_of_nonneg_right hγ hn.le
  have hdiff : ((F.mean a - F.mean b) ⬝ᵥ v) ^ 2 ≤
      2 * (v ⬝ᵥ F.mean a) ^ 2 + 2 * (v ⬝ᵥ F.mean b) ^ 2 := by
    rw [sub_dotProduct, dotProduct_comm (F.mean a) v, dotProduct_comm (F.mean b) v]
    nlinarith only [sq_nonneg (v ⬝ᵥ F.mean a + v ⬝ᵥ F.mean b)]
  have hdiffw := mul_le_mul_of_nonneg_left hdiff hw.le
  have hlow := mul_le_mul_of_nonneg_left (hl v) (sq_nonneg Δ)
  change 2 * Δ ^ 2 * qform S v < _ at hv
  have hvw := mul_lt_mul_of_pos_left hv hw
  have hloww := mul_le_mul_of_nonneg_left hlow hw.le
  have hbudgetv := mul_le_mul_of_nonneg_right hbudget hn.le
  nlinarith only [ha, hb, hγv, hdiffw, hloww, hvw, hbudgetv, hn]

/-- A positive semidefinite quadratic form has the usual squared triangle bound. -/
theorem qform_near_bound (S : Mat d) (hS : S.PosSemidef) (u v : Vec d) :
    qform S u ≤ 2 * qform S v + 2 * qform S (u - v) := by
  have hn := hS.dotProduct_mulVec_nonneg (u - (2 : ℝ) • v)
  have he : qform S (u - (2 : ℝ) • v) =
      2 * qform S v + 2 * qform S (u - v) - qform S u := by
    simp only [qform, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  change 0 ≤ qform S (u - (2 : ℝ) • v) at hn
  linarith only [he, hn]

theorem identical_tolerances (β : ℚ) (hβ : 0 < β ∧ β ≤ 1 / 100) :
    (IdCov.gammaStar β : ℝ) ≤ 1 / 100 ∧
      (IdCov.tauStar β : ℝ) ≤ (β : ℝ) ^ 2 / 100 := by
  have hβ0 : (0 : ℝ) ≤ β := by exact_mod_cast hβ.1.le
  have hβ1 : (β : ℝ) ≤ 1 := by
    exact_mod_cast hβ.2.trans (by norm_num : (1 / 100 : ℚ) ≤ 1)
  have hpow := pow_le_one₀ hβ0 hβ1 (n := 8)
  have hpow2 := pow_le_pow_of_le_one hβ0 hβ1 (show 2 ≤ 8 by omega)
  simp only [IdCov.gammaStar, IdCov.tauStar, IdCov.epsilonR, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat]
  constructor
  · calc
      ((β : ℝ) / 25) ^ 8 / 6 = (β : ℝ) ^ 8 / (25 ^ 8 * 6) := by ring
      _ ≤ 1 / (25 ^ 8 * 6) := by gcongr
      _ ≤ 1 / 100 := by norm_num
  · calc
      ((β : ℝ) / 25) ^ 8 / 3 = (β : ℝ) ^ 8 / (25 ^ 8 * 3) := by ring
      _ ≤ (β : ℝ) ^ 2 / (25 ^ 8 * 3) := by gcongr
      _ ≤ (β : ℝ) ^ 2 / 100 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by norm_num)


theorem sqrtUp_sq (x : ℚ) : x ≤ sqrtUp x ^ 2 := by
  have hceil := Nat.le_ceil (max 0 x)
  have hs := Nat.lt_succ_sqrt ⌈max 0 x⌉₊
  have hnat : (⌈max 0 x⌉₊ : ℚ) ≤ sqrtUp x ^ 2 := by
    unfold sqrtUp
    have hs' : ⌈max 0 x⌉₊ ≤ (Nat.sqrt ⌈max 0 x⌉₊ + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one, pow_two] using hs.le
    exact_mod_cast hs'
  exact (le_max_right 0 x).trans (hceil.trans hnat)


/-- Every center in the prescribed mean range has a nearest entry on the fixed grid. -/
theorem meanThresholds_cover (k : ℕ) (p : Tree.StepParams) (hk : 0 < k) (t : ℝ)
    (ht : |t| ≤ 4 * (sqrtUp (1 / p.w) : ℝ)) :
    ∃ q ∈ meanThresholds k p, |(q : ℝ) - t| ≤ 1 / (32 * k : ℝ) := by
  let J := meanThresholdRadius k p
  let z := round (16 * (k : ℝ) * t)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hJ : 64 * (k : ℝ) * (sqrtUp (1 / p.w) : ℝ) ≤ J := by
    have hh : (64 * k * sqrtUp (1 / p.w) : ℚ) ≤ J := Nat.le_ceil _
    exact_mod_cast hh
  have htJ : |16 * (k : ℝ) * t| ≤ J := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 * k)]
    calc
      _ ≤ 16 * k * (4 * (sqrtUp (1 / p.w) : ℝ)) := by gcongr
      _ ≤ J := by nlinarith only [hJ]
  have hz := abs_sub_round (16 * (k : ℝ) * t)
  change |16 * (k : ℝ) * t - (z : ℝ)| ≤ 1 / 2 at hz
  have hzJ : -(J : ℤ) - 1 ≤ z ∧ z ≤ (J : ℤ) + 1 := by
    obtain ⟨htlo, hthi⟩ := abs_le.mp htJ
    obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
    constructor
    · exact_mod_cast (show -(J : ℝ) - 1 ≤ (z : ℝ) by linarith only [htlo, hzhi])
    · exact_mod_cast (show (z : ℝ) ≤ (J : ℝ) + 1 by linarith only [hthi, hzlo])
  let i := (z + J + 1).toNat
  have hi : (i : ℤ) = z + J + 1 := Int.toNat_of_nonneg (by omega)
  have hiR : (i : ℝ) = z + J + 1 := by exact_mod_cast hi
  have hiJ : i < 2 * J + 3 := by omega
  let q : ℚ := ((i : ℚ) - ((J : ℚ) + 1)) / (16 * (k : ℚ))
  refine ⟨q, List.mem_map.mpr ⟨i, List.mem_range.mpr hiJ, rfl⟩, ?_⟩
  have hq : (q : ℝ) = (z : ℝ) / (16 * k) := by
    dsimp only [q]
    push_cast
    rw [hiR]
    ring
  rw [hq, div_sub' (by positivity : (16 * (k : ℝ)) ≠ 0), abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 16 * k)]
  rw [abs_sub_comm] at hz
  apply (div_le_div_of_nonneg_right hz (by positivity)).trans_eq
  field_simp [hkR.ne']
  ring

/-- A spread of component means leaves a buffered separating entry on the fixed mean grid. -/
theorem meanThresholds_separate {k : ℕ} (p : StepParams) (I : Finset (Fin k))
    (c : Fin k → ℝ) (a b : Fin k) (ha : a ∈ I) (hb : b ∈ I)
    (hspread : 9 / 10 ≤ |c a - c b|)
    (hbound : ∀ j ∈ I, |c j| ≤ 4 * (sqrtUp (1 / p.w) : ℝ)) :
    ∃ q ∈ meanThresholds k p, ∃ J : Finset (Fin k),
      J ⊆ I ∧ J.Nonempty ∧ (I \ J).Nonempty ∧
      ∀ j ∈ I, (j ∈ J → c j ≤ (q : ℝ) - 2 / (5 * k : ℝ)) ∧
        (j ∉ J → (q : ℝ) + 2 / (5 * k : ℝ) ≤ c j) := by
  classical
  have hk : 0 < k := a.pos
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let s := I.image c
  have hcard : (s.card : ℝ) ≤ k := by
    exact_mod_cast Finset.card_image_le.trans
      (show I.card ≤ k by simpa using Finset.card_le_univ I)
  have hstep : 0 < 9 / (10 * k : ℝ) := by positivity
  have hcancel : (k : ℝ) * (9 / (10 * k : ℝ)) = 9 / 10 := by
    field_simp
  have hsmall : ((s.card : ℝ) - 1) * (9 / (10 * k : ℝ)) < |c a - c b| := by
    have hh := mul_le_mul_of_nonneg_right hcard hstep.le
    nlinarith only [hh, hcancel, hstep, hspread]
  have hca : c a ∈ s := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hcb : c b ∈ s := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  obtain ⟨lo, hlo, hi, hhi, hgap, hside⟩ :
      ∃ lo ∈ s, ∃ hi ∈ s, lo + 9 / (10 * k : ℝ) < hi ∧
        ∀ x ∈ s, x ≤ lo ∨ hi ≤ x := by
    rcases le_total (c a) (c b) with h | h
    · apply CompleteAux.expectation_gap hca hcb
      rwa [abs_of_nonpos (sub_nonpos.mpr h), neg_sub] at hsmall
    · apply CompleteAux.expectation_gap hcb hca
      rwa [abs_of_nonneg (sub_nonneg.mpr h)] at hsmall
  have hbnd (x : ℝ) (hx : x ∈ s) : |x| ≤ 4 * (sqrtUp (1 / p.w) : ℝ) := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hbound j hj
  have hmid : |(lo + hi) / 2| ≤ 4 * (sqrtUp (1 / p.w) : ℝ) := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hbnd lo hlo)
    obtain ⟨hl', hu'⟩ := abs_le.mp (hbnd hi hhi)
    exact abs_le.mpr ⟨by linarith only [hl, hl'], by linarith only [hu, hu']⟩
  obtain ⟨q, hq, hnear⟩ := meanThresholds_cover k p hk ((lo + hi) / 2) hmid
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hnear
  have hconstants : 2 / (5 * k : ℝ) + 1 / (32 * k : ℝ) ≤ 9 / (20 * k : ℝ) := by
    field_simp
    nlinarith only [hkR]
  have hhalf : 2 * (9 / (20 * k : ℝ)) = 9 / (10 * k : ℝ) := by ring
  have hloq : lo ≤ (q : ℝ) - 2 / (5 * k : ℝ) := by
    linarith only [hgap, hqlo, hconstants, hhalf]
  have hhiq : (q : ℝ) + 2 / (5 * k : ℝ) ≤ hi := by
    linarith only [hgap, hqhi, hconstants, hhalf]
  let J := I.filter (fun j ↦ c j ≤ lo)
  refine ⟨q, hq, J, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hlo
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq.le⟩⟩
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hhi
    refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩⟩
    intro hjJ
    have hh := (Finset.mem_filter.mp hjJ).2
    rw [heq] at hh
    linarith only [hh, hgap, hstep]
  · intro j hj
    constructor
    · intro hjJ
      exact (Finset.mem_filter.mp hjJ).2.trans hloq
    · intro hjJ
      apply hhiq.trans
      exact (hside (c j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).resolve_left
        (fun hh ↦ hjJ (Finset.mem_filter.mpr ⟨hj, hh⟩))

/-- Pull a rational linear statistic back through the chosen affine frame. -/
def meanStatistic (T : Matrix (Fin d) (Fin d) ℚ) (a u : Fin d → ℚ) : Statistic d :=
  ⟨0, Tᵀ *ᵥ u, -((Tᵀ *ᵥ u) ⬝ᵥ a)⟩


theorem meanStatistic_b (T : Matrix (Fin d) (Fin d) ℚ) (a u : Fin d → ℚ) :
    (fun i ↦ ((meanStatistic T a u).b i : ℝ)) =
      (T.map (algebraMap ℚ ℝ))ᵀ *ᵥ (fun i ↦ (u i : ℝ)) := by
  ext i
  exact (algebraMap ℚ ℝ).map_mulVec Tᵀ u i

theorem meanStatistic_eval (T : Matrix (Fin d) (Fin d) ℚ) (a u : Fin d → ℚ)
    (x : Vec d) :
    (meanStatistic T a u).eval x = (fun i ↦ (u i : ℝ)) ⬝ᵥ
      (T.map (algebraMap ℚ ℝ) *ᵥ (x - (fun i ↦ (a i : ℝ)))) := by
  have hc : ((meanStatistic T a u).c : ℝ) =
      -((T.map (algebraMap ℚ ℝ))ᵀ *ᵥ (fun i ↦ (u i : ℝ))) ⬝ᵥ
        (fun i ↦ (a i : ℝ)) := by
    change ((-((Tᵀ *ᵥ u) ⬝ᵥ a) : ℚ) : ℝ) = _
    have hd : (((Tᵀ *ᵥ u) ⬝ᵥ a : ℚ) : ℝ) =
        (fun i ↦ ((Tᵀ *ᵥ u) i : ℝ)) ⬝ᵥ (fun i ↦ (a i : ℝ)) := by
      simp only [dotProduct, Rat.cast_sum, Rat.cast_mul]
    rw [Rat.cast_neg, hd]
    rw [show (fun i ↦ ((Tᵀ *ᵥ u) i : ℝ)) =
      (T.map (algebraMap ℚ ℝ))ᵀ *ᵥ (fun i ↦ (u i : ℝ)) from meanStatistic_b T a u]
    rw [neg_dotProduct]
  have hAz : (meanStatistic T a u).A.map (algebraMap ℚ ℝ) = 0 := by
    ext i j
    norm_num [meanStatistic]
  rw [Statistic.eval, hAz, meanStatistic_b, hc]
  simp only [qform, zero_mulVec, dotProduct_zero, zero_add]
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_sub, neg_dotProduct]
  ring


/-- An additive edge stores the exact window required by mean-split soundness. -/
def meanEdge {n : ℕ} (k h : ℕ) (N : Finset (Fin n)) (q : Statistic d) (t : ℚ) :
    Edge n d :=
  ⟨h, N, q, .mean, t, t - 1 / (16 * k), t + 1 / (16 * k)⟩

/-- A small common variance and separated means give a buffered witness on the fixed grid. -/
theorem meanGrid_complete {n k : ℕ} (M : Mixture k d) (I : Finset (Fin k))
    (p : StepParams) (N : Finset (Fin n)) (q : Statistic d) (c : Fin k → ℝ)
    (η : ℝ) (h : ℕ) (hM : M.Valid) (hA : q.A = 0)
    (hβ : 0 < p.subspaceAccuracy ∧ p.subspaceAccuracy ≤ 1 / 100)
    (hη : 0 ≤ η) (hmargin : 4 * η ≤ 1 / (16 * k : ℝ))
    (hmass : (p.windowMass : ℝ) ≤
      (1 / (16 * k : ℝ)) * (p.straddle / 2) ^ 9 / 16)
    (htail : 200 * (k : ℝ) ^ 2 * (p.subspaceAccuracy : ℝ) ^ 2 ≤ p.tail)
    (hc : ∀ j ∈ I, c j = ∫ y : EuclideanSpace ℝ (Fin d), q.eval y.ofLp
      ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hvar : ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        9 * (p.subspaceAccuracy : ℝ) ^ 2)
    (hbound : ∀ j ∈ I, |c j| ≤ 4 * (sqrtUp (1 / p.w) : ℝ))
    (hspread : ∃ a ∈ I, ∃ b ∈ I, 9 / 10 ≤ |c a - c b|) :
    ∃ t ∈ meanThresholds k p, ∃ J : Finset (Fin k),
      ScaleValid M I p (meanEdge k h N q t) ∧
        Tree.RefineAux.BufferedComplete M I J p η (meanEdge k h N q t) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hspread
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr a.pos
  have hkQ : (0 : ℚ) < k := Nat.cast_pos.mpr a.pos
  have hβ0 : (0 : ℝ) < p.subspaceAccuracy := by exact_mod_cast hβ.1
  have hβ1 : (p.subspaceAccuracy : ℝ) ≤ 1 / 100 := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hβ.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hvar4 : 9 * (p.subspaceAccuracy : ℝ) ^ 2 ≤ 4 := by
    nlinarith only [hβ0, hβ1, sq_nonneg ((p.subspaceAccuracy : ℝ) - 1 / 100)]
  obtain ⟨t, ht, J, hJI, hJ, hIJ, hside⟩ :=
    meanThresholds_separate p I c a b ha hb hab hbound
  let e := meanEdge k h N q t
  let W : ℝ := 1 / (16 * k : ℝ)
  let r : ℝ := 1 / (4 * k : ℝ)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hgap : r + 2 * W ≤ 2 / (5 * k : ℝ) := by
    dsimp only [r, W]
    field_simp
    nlinarith only [hkR]
  refine ⟨t, ht, J, ?_, hJI, hJ, hIJ, ?_⟩
  · refine ⟨?_, ?_, hmass, rfl, rfl, hA, ?_⟩
    · change t - 1 / (16 * k : ℚ) ≤ t
      have hh : (0 : ℚ) ≤ 1 / (16 * k) := by positivity
      linarith only [hh]
    · change t ≤ t + 1 / (16 * k : ℚ)
      have hh : (0 : ℚ) ≤ 1 / (16 * k) := by positivity
      linarith only [hh]
    · intro j hj
      change qform (M.S j) (fun i ↦ (q.b i : ℝ)) ≤ 4
      rw [← SoundAux.mean_variance M hM j q hA]
      exact (hvar j hj).trans hvar4
  · intro j hj C
    change SoundAux.CoordinateSpec M j q at C
    have hs : C.s ≤ 2 := by
      nlinarith only [C.variance, hvar j hj, hvar4, C.nonneg]
    have hm : 2 * η * C.s ≤ W := by
      change 4 * η ≤ W at hmargin
      nlinarith only [hmargin, mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * η)]
    have hbudget : 9 * (p.subspaceAccuracy : ℝ) ^ 2 / r ^ 2 ≤ p.tail := by
      have he : 9 * (p.subspaceAccuracy : ℝ) ^ 2 / r ^ 2 =
          144 * (k : ℝ) ^ 2 * (p.subspaceAccuracy : ℝ) ^ 2 := by
        dsimp only [r]
        field_simp
        ring
      rw [he]
      nlinarith only [htail, sq_nonneg ((k : ℝ) * (p.subspaceAccuracy : ℝ))]
    apply mean_complete M j p e (c j) r (9 * (p.subspaceAccuracy : ℝ) ^ 2)
      η C.s (j ∈ J) hM hA (hc j hj) hr (by
        change qform (M.S j) (fun i ↦ (q.b i : ℝ)) ≤ _
        rw [← SoundAux.mean_variance M hM j q hA]
        exact hvar j hj) hbudget
    constructor
    · intro z hy
      change ((t - 1 / (16 * k) : ℚ) : ℝ) - 2 * η * C.s ≤ z ∧
        z ≤ ((t + 1 / (16 * k) : ℚ) : ℝ) + 2 * η * C.s at hy
      push_cast at hy
      change (t : ℝ) - W - 2 * η * C.s ≤ z ∧
        z ≤ (t : ℝ) + W + 2 * η * C.s at hy
      by_cases hjJ : j ∈ J
      · have hh := (hside j hj).1 hjJ
        have habs := le_abs_self (z - c j)
        change r ≤ |z - c j|
        linarith only [hh, habs, hy.1, hm, hgap]
      · have hh := (hside j hj).2 hjJ
        have habs := neg_le_abs (z - c j)
        change r ≤ |z - c j|
        linarith only [hh, habs, hy.2, hm, hgap]
    · intro z hy
      by_cases hjJ : j ∈ J
      · simp only [hjJ, ite_true] at hy
        change (t : ℝ) - 2 * η * C.s < z at hy
        have hh := (hside j hj).1 hjJ
        have habs := le_abs_self (z - c j)
        linarith only [hh, habs, hy, hm, hgap, hW]
      · simp only [hjJ, ite_false] at hy
        change z ≤ (t : ℝ) + 2 * η * C.s at hy
        have hh := (hside j hj).2 hjJ
        have habs := neg_le_abs (z - c j)
        linarith only [hh, habs, hy, hm, hgap, hW]

/-- Consecutive powers of two cover every magnitude between the grid endpoints. -/
theorem dyadic_cover (H t : ℝ) (T : ℕ) (ht : 0 ≤ t) (hT : 0 < T) (hH : t ≤ H)
    (hlast : H / (2 : ℝ) ^ (T - 1) ≤ t) :
    ∃ i < T, t / 2 ≤ H / (2 : ℝ) ^ i ∧ H / (2 : ℝ) ^ i ≤ t := by
  have hex : ∃ i, H / (2 : ℝ) ^ i ≤ t := ⟨T - 1, hlast⟩
  let i := Nat.find hex
  have hi : i ≤ T - 1 := Nat.find_min' hex hlast
  refine ⟨i, by omega, ?_, Nat.find_spec hex⟩
  by_cases hi0 : i = 0
  · simp only [hi0, pow_zero, div_one]
    linarith only [hH, ht]
  · have hp : t < H / (2 : ℝ) ^ (i - 1) :=
      lt_of_not_ge (Nat.find_min hex (by omega : i - 1 < i))
    have hpow : (2 : ℝ) ^ i = 2 ^ (i - 1) * 2 := by
      conv_lhs => rw [show i = (i - 1) + 1 by omega, pow_succ]
    have he : H / (2 : ℝ) ^ (i - 1) = 2 * (H / (2 : ℝ) ^ i) := by
      rw [hpow]
      field_simp
    rw [he] at hp
    linarith only [hp]

end

end ABBKS26.RefineAux
