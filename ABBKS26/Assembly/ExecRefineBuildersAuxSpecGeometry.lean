module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecCertificate
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecDirection

/-! Thin directions and variance gaps after bounded rounding in the original frame. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecGeometry

open Common Centered Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders
open scoped BigOperators

noncomputable section

variable {m d : ℕ}

theorem frob_pair (A B : Mat d) :
    frobSq (A - B) ≤ 2 * frobSq (A - 1) + 2 * frobSq (B - 1) := by
  simp only [frobSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.sub_apply]
  nlinarith only [sq_nonneg (A i j + B i j - 2 * (1 : Mat d) i j)]

theorem thin (G : FrameModel m d) (p : StepParams) (k : ℕ) (next : StepParams)
    (hp : StepReady .centered k p next) (hm : 2 ≤ m)
    (hG : DataValid G (p.w / 2 : ℚ) p.isotropy
      ((10000 * p.sigmaSq / (p.w / 2) + 10 : ℚ) : ℝ))
    (hsep : ∀ a b, a ≠ b → CenteredSeparated p.separation (G.cov a) (G.cov b)) :
    ∃ (i : Fin m) (v : Vec d), sqnorm v = 1 ∧
      qform (G.cov i) v ≤ 3 * (p.subspaceAccuracy : ℝ) ^ 8 := by
  obtain ⟨hw, hw2, hμ, hμ100, _, _, _, _, _, _, _, _, _, _, _, _, hmode⟩ := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hΔ, hρ⟩ := hmode
  let C : ℝ := 4 / p.w
  let β : ℝ := p.subspaceAccuracy
  let rF : ℝ := ((10000 * p.sigmaSq / (p.w / 2) + 10 : ℚ) : ℝ)
  have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw
  have hwR2 : (p.w : ℝ) ≤ 1 / 2 := by
    have hb := Rat.cast_mono (K := ℝ) hw2
    norm_num at hb
    exact hb
  have hC : 8 ≤ C := by dsimp only [C]; rw [le_div_iff₀ hwR]; linarith only [hwR2]
  have hβ : 0 < β := by
    dsimp only [β]
    exact_mod_cast hμ
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    exact_mod_cast hμ100.trans (by norm_num : (1 / 100 : ℚ) ≤ 1)
  have hcov (i : Fin m) : (G.cov i).PosDef ∧ LE (G.cov i) (C • (1 : Mat d)) := by
    refine ⟨hG.1.2.2.2 i, ?_⟩
    intro v
    have hu := SpecDirection.covariance_upper G (p.w / 2 : ℚ) p.isotropy rF hG i v
    have he : 1.1 / (((p.w / 2 : ℚ) : ℝ)) ≤ C := by
      push_cast
      dsimp only [C]
      field_simp
      norm_num
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    exact hu.trans (mul_le_mul_of_nonneg_right he (DetRoundAux.sqnorm_nonneg v))
  have hrF : 0 ≤ rF := by
    let i : Fin m := ⟨0, by omega⟩
    exact (by unfold frobSq; positivity : 0 ≤ frobSq (G.cov i - 1)).trans
      (hG.2.2.2.2 i)
  have hpair (a b : Fin m) : frobSq (G.cov a - G.cov b) ≤
      (2 * Real.sqrt rF) ^ 2 := by
    have hs := Real.sq_sqrt hrF
    have hf := (frob_pair (G.cov a) (G.cov b)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hG.2.2.2.2 a) (by norm_num))
        (mul_le_mul_of_nonneg_left (hG.2.2.2.2 b) (by norm_num)))
    change frobSq (G.cov a - G.cov b) ≤ 2 * rF + 2 * rF at hf
    nlinarith only [hf, hs]
  have hthinΔ : C < (p.separation : ℝ) ^ 2 * (3 * β ^ 8) := by
    convert hΔ using 1; ring
  have hthinρ : (2 * Real.sqrt rF) * C ≤ (p.separation : ℝ) * (3 * β ^ 8) ^ 2 := by
    dsimp only [rF]
    push_cast
    convert hρ using 1; ring
  obtain ⟨j, _, v, hv, ht⟩ := thin_direction G Finset.univ C
    (2 * Real.sqrt rF) p.separation (3 * β ^ 8) (by simpa using hm)
    ⟨by positivity, by
      have he := pow_le_one₀ hβ.le hβ1 (n := 8)
      linarith only [he, hC]⟩
    (fun i _ ↦ hcov i) (fun a _ b _ ↦ hpair a b)
    (fun a _ b _ hab ↦ hsep a b hab) hthinΔ hthinρ (by positivity)
  exact ⟨j, v, hv, ht.le⟩

theorem qform_sub_comm (S : Mat d) (u v : Vec d) : qform S (u - v) =
    qform S (v - u) := by
  simp only [qform, mulVec_sub, dotProduct_sub, sub_dotProduct]
  ring

/-- Rounding in the original frame preserves the variance gap needed by the fixed grid.
Only its component covariance error is used; no inverse frame is constructed. -/
theorem deviations (G : FrameModel m d) (S : Fin m → Mat d) (p : StepParams)
    (hG : DataValid G (p.w / 2 : ℚ) p.isotropy
      ((10000 * p.sigmaSq / (p.w / 2) + 10 : ℚ) : ℝ))
    (hw : 0 < p.w ∧ p.w ≤ 1 / 2)
    (hμ : 0 < p.subspaceAccuracy ∧ p.subspaceAccuracy ≤ 1 / 100)
    (hS : ∀ j, (S j).PosDef) (u b c v : Vec d) (j : Fin m)
    (ht : qform (G.cov j) v ≤ 3 * (p.subspaceAccuracy : ℝ) ^ 8)
    (hnorm : |‖WithLp.toLp 2 u‖ - 1| ≤ (p.subspaceAccuracy : ℝ) / 4)
    (hnear : ‖WithLp.toLp 2 u - WithLp.toLp 2 v‖ ≤ 33 * (p.subspaceAccuracy : ℝ))
    (hb : ∀ i, qform (S i) b = qform (G.cov i) u)
    (hc : ∀ i, qform (S i) (c - b) ≤ (p.subspaceAccuracy : ℝ) ^ 2 / 16) :
    let σ := fun i ↦ Real.sqrt (qform (S i) c)
    (∀ i, 0 < σ i) ∧ (∀ i, σ i ≤ 2 * (sqrtUp (4 / p.w) : ℝ)) ∧
      (∃ i, σ i ≤ 64 * (4 / p.w : ℝ) * p.subspaceAccuracy) ∧
      (∃ i, 1 / 2 < σ i) := by
  let C : ℝ := 4 / p.w
  let β : ℝ := p.subspaceAccuracy
  have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw.1
  have hwR2 : (p.w : ℝ) ≤ 1 / 2 := by
    have hb := Rat.cast_mono (K := ℝ) hw.2
    norm_num at hb
    exact hb
  have hC : 8 ≤ C := by dsimp only [C]; rw [le_div_iff₀ hwR]; linarith only [hwR2]
  have hβ : 0 < β := by
    dsimp only [β]
    exact_mod_cast hμ.1
  have hβ100 : β ≤ 1 / 100 := by
    have hb := Rat.cast_mono (K := ℝ) hμ.2
    norm_num at hb
    exact hb
  have hβ1 : β ≤ 1 := by linarith only [hβ100]
  have hβsq : β ^ 2 ≤ 1 / 100 := by nlinarith only [hβ, hβ100]
  have hnormsq := CompleteAux.norm_sq u
  have hnlo : 9 / 10 ≤ sqnorm u := by
    have he := (abs_le.mp hnorm).1
    nlinarith only [he, hnormsq, norm_nonneg (WithLp.toLp 2 u), hβ100, hβ]
  have hnhi : sqnorm u ≤ 3 / 2 := by
    have he := (abs_le.mp hnorm).2
    nlinarith only [he, hnormsq, norm_nonneg (WithLp.toLp 2 u), hβ100, hβ]
  have hupper (i : Fin m) (z : Vec d) : qform (G.cov i) z ≤ C * sqnorm z := by
    have hu := SpecDirection.covariance_upper G (p.w / 2 : ℚ) p.isotropy _ hG i z
    have he : 1.1 / (((p.w / 2 : ℚ) : ℝ)) ≤ C := by
      push_cast
      dsimp only [C]
      field_simp
      norm_num
    exact hu.trans (mul_le_mul_of_nonneg_right he (DetRoundAux.sqnorm_nonneg z))
  have hcb (i : Fin m) : qform (S i) c ≤ 2 * qform (G.cov i) u + β ^ 2 / 8 := by
    have he := ABBKS26.RefineAux.qform_near_bound (S i) (hS i).posSemidef c b
    rw [hb i] at he
    linarith only [he, hc i]
  have hbc (i : Fin m) : qform (G.cov i) u ≤ 2 * qform (S i) c + β ^ 2 / 8 := by
    have he := ABBKS26.RefineAux.qform_near_bound (S i) (hS i).posSemidef b c
    rw [hb i, qform_sub_comm (S i) b c] at he
    linarith only [he, hc i]
  have hlarge : ∃ i, 1 / 4 < qform (S i) c := by
    by_contra! h
    have hiso := hG.2.2.1.2.1 u
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hiso
    have hsecond := ABBKS26.RefineAux.frame_second_qform G u
    simp only [hG.2.1, dotProduct_zero, zero_pow (by omega : 2 ≠ 0), add_zero] at hsecond
    have hsum : (∑ i, G.weight i * qform (G.cov i) u) ≤ 51 / 100 := by
      calc
        _ ≤ ∑ i, G.weight i * (51 / 100) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hG.1.1.le.trans (hG.1.2.1 i))
          linarith only [hbc i, h i, hβsq]
        _ = 51 / 100 := by rw [← Finset.sum_mul, hG.1.2.2.1]; norm_num
    have hγ := mul_le_mul_of_nonneg_right hG.2.2.2.1 (DetRoundAux.sqnorm_nonneg u)
    change (1 - (p.isotropy : ℝ)) * sqnorm u ≤ qform G.second u at hiso
    rw [hsecond] at hiso
    nlinarith only [hiso, hsum, hγ, hnlo]
  have hc0 : c ≠ 0 := by
    obtain ⟨i, hi⟩ := hlarge
    intro he
    rw [he, qform, mulVec_zero, dotProduct_zero] at hi
    norm_num at hi
  have hpos (i : Fin m) : 0 < qform (S i) c := by
    simpa only [qform, star_trivial] using (hS i).dotProduct_mulVec_pos hc0
  have hsmall : qform (S j) c ≤ (64 * C * β) ^ 2 := by
    have hn := ABBKS26.RefineAux.qform_near_bound (G.cov j)
      (hG.1.2.2.2 j).posSemidef u v
    have hu := hupper j (u - v)
    have hnear' : sqnorm (u - v) ≤ (33 * β) ^ 2 := by
      rw [← CompleteAux.norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hnear 2
    have he := mul_le_mul_of_nonneg_left hnear' (by linarith only [hC] : 0 ≤ C)
    have hβ8 : β ^ 8 ≤ β ^ 2 := pow_le_pow_of_le_one hβ.le hβ1 (by norm_num)
    have hCC : C ≤ C ^ 2 / 8 := by nlinarith only [hC]
    have hCβ := mul_le_mul_of_nonneg_right hCC (sq_nonneg β)
    have hβC := mul_le_mul_of_nonneg_right (by nlinarith only [hC, sq_nonneg (C - 1)] : 1 ≤ C ^ 2)
      (sq_nonneg β)
    nlinarith only [hcb j, hn, hu, he, ht, hβ8, hCβ, hβC]
  refine ⟨fun i ↦ Real.sqrt_pos.mpr (hpos i), ?_,
    ⟨j, (Real.sqrt_le_iff).mpr ⟨by positivity, hsmall⟩⟩, ?_⟩
  · intro i
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by unfold sqrtUp; positivity, ?_⟩
    have hu := (hupper i u).trans
      (mul_le_mul_of_nonneg_left hnhi (by linarith only [hC] : 0 ≤ C))
    have huc : qform (S i) c ≤ 4 * C := by linarith only [hcb i, hu, hC, hβsq]
    have hs : C ≤ (sqrtUp (4 / p.w) : ℝ) ^ 2 := by
      have he := Rat.cast_mono (K := ℝ) (ABBKS26.RefineAux.sqrtUp_sq (4 / p.w))
      push_cast at he
      exact he
    nlinarith only [huc, hs]
  · obtain ⟨i, hi⟩ := hlarge
    refine ⟨i, ?_⟩
    have hs := Real.sq_sqrt (hpos i).le
    nlinarith only [hs, hi, Real.sqrt_nonneg (qform (S i) c)]

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecGeometry
