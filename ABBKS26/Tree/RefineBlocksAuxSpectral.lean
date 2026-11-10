module

public import ABBKS26.Tree.RefineAuxCore

/-! Buffered spectral witnesses at a specified rational magnitude. -/

@[expose] public section

namespace ABBKS26.Tree.RefineAux

noncomputable section

open Matrix Common MeasureTheory ProbabilityTheory

variable {n k d : ℕ}

theorem buffered_spectral_recorded
    (M : Mixture k d) (I : Finset (Fin k)) (p : StepParams)
    (N : Finset (Fin n)) (η : ℝ) (h : ℕ) (u : Fin d → ℚ) (t : ℚ) (R : ℝ)
    (hM : M.Valid) (hcen : M.IsCentered) (ht : 0 < t) (hK : 1 ≤ p.K)
    (hη : 0 ≤ η ∧ η ≤ 1 / 100) (hR : 1 ≤ R)
    (htail : 1 / R + 2 * Real.sqrt η ≤ p.tail)
    (hside : ∀ j ∈ I,
      qform (M.S j) (fun i ↦ (u i : ℝ)) ≤ ((t : ℝ) / (2 * p.K * R)) ^ 2 ∨
        ((t : ℝ) * p.K * R) ^ 2 ≤ qform (M.S j) (fun i ↦ (u i : ℝ)))
    (hlo : ∃ j ∈ I,
      qform (M.S j) (fun i ↦ (u i : ℝ)) ≤ ((t : ℝ) / (2 * p.K * R)) ^ 2)
    (hhi : ∃ j ∈ I,
      ((t : ℝ) * p.K * R) ^ 2 ≤ qform (M.S j) (fun i ↦ (u i : ℝ))) :
    ∃ J : Finset (Fin k),
      BufferedComplete M I J p η
        (⟨h, N, ⟨vecMulVec u u, 0, 0⟩, .spectral,
          t ^ 2, t ^ 2 / p.K ^ 2, t ^ 2 * p.K ^ 2⟩ : Edge n d) := by
  classical
  let z : Vec d := fun i ↦ (u i : ℝ)
  let V : Fin k → ℝ := fun j ↦ qform (M.S j) z
  let q : Statistic d := ⟨vecMulVec u u, 0, 0⟩
  have hq (x : Fin d → ℚ) : q.evalQ x = (u ⬝ᵥ x) ^ 2 := by
    simp [q, Statistic.evalQ, vecMulVec_mulVec, dotProduct_smul, pow_two, dotProduct_comm]
  have heval (x : Vec d) : q.eval x = (z ⬝ᵥ x) ^ 2 :=
    SoundAux.spectral_eval q u hq x
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hKR : (1 : ℝ) ≤ p.K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < p.K := by linarith only [hKR]
  have hR0 : 0 < R := by linarith only [hR]
  have hη0 : 0 ≤ η := hη.1
  let a : ℝ := t / (2 * p.K)
  let b : ℝ := t * p.K
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := mul_pos htR hK0
  have halow : (a / R) ^ 2 ≤ a ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_self ha.le hR
  have hab : 4 * a ^ 2 ≤ b ^ 2 := by
    have hKsq : 1 ≤ (p.K : ℝ) ^ 2 := one_le_pow₀ hKR
    have he : 4 * a ^ 2 * (p.K : ℝ) ^ 2 = (t : ℝ) ^ 2 := by
      dsimp only [a]
      field_simp
      ring
    have h1 := mul_le_mul_of_nonneg_left hKsq (sq_nonneg (t : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hKsq (by positivity : 0 ≤ 4 * a ^ 2)
    dsimp only [b]
    rw [mul_pow]
    nlinarith only [he, h1, h2]
  have hhigh (j : Fin k) (hj : (b * R) ^ 2 ≤ V j) : (a / R) ^ 2 < V j := by
    have hh : b ^ 2 ≤ (b * R) ^ 2 := by
      apply pow_le_pow_left₀ hb.le
      exact le_mul_of_one_le_right hb.le hR
    nlinarith only [halow, hab, hh, hj, sq_pos_of_pos ha]
  let J := I.filter (fun j ↦ V j ≤ (a / R) ^ 2)
  let e : Edge n d := ⟨h, N, q, .spectral, t ^ 2, t ^ 2 / p.K ^ 2, t ^ 2 * p.K ^ 2⟩
  have hKsqQ : (1 : ℚ) ≤ p.K ^ 2 := one_le_pow₀ hK
  have hlow : e.lower ≤ e.threshold := by
    exact div_le_self (sq_nonneg t) hKsqQ
  have hupp : e.threshold ≤ e.upper := le_mul_of_one_le_right (sq_nonneg t) hKsqQ
  refine ⟨J, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · obtain ⟨j, hj, hv⟩ := hlo
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    simpa only [V, z, a, div_div] using hv
  · obtain ⟨j, hj, hv⟩ := hhi
    refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩⟩
    intro hjJ
    exact (not_le_of_gt (hhigh j hv)) (Finset.mem_filter.mp hjJ).2
  · intro j hj C
    change SoundAux.CoordinateSpec M j q at C
    apply spectral_complete M j p e u a b R η C.s (j ∈ J) hM hcen hq ha hb hR
      hη.1 C.nonneg _ htail (fun hjJ ↦ (Finset.mem_filter.mp hjJ).2) _ _ hlow hupp _
    · simpa only [SoundAux.spectral_variance M hM hcen j q u hq] using C.variance
    · intro hjJ
      rcases hside j hj with hv | hv
      · exact (hjJ (Finset.mem_filter.mpr ⟨hj, by
          simpa only [V, z, a, div_div] using hv⟩)).elim
      · exact hv
    · intro hjJ
      have hV : 0 ≤ V j := (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg z
      have hv : V j ≤ a ^ 2 := (Finset.mem_filter.mp hjJ).2.trans halow
      have hh := mul_le_mul_of_nonneg_right hη.2 (by positivity : 0 ≤ 4 * V j)
      have he : (e.lower : ℝ) = 4 * a ^ 2 := by
        dsimp only [e, a]
        push_cast
        field_simp
        ring
      rw [he]
      change a ^ 2 + 4 * η * V j ≤ 4 * a ^ 2
      nlinarith only [hh, hv, hV, sq_nonneg a]
    · dsimp only [e, b]
      push_cast
      nlinarith


end

end ABBKS26.Tree.RefineAux
