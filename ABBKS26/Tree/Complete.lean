module

public import ABBKS26.Tree.CompleteAuxPopulation
public import ABBKS26.Centered.ThmZ
public import ABBKS26.IdCov.Subspace

/-!
# Completeness of the splits

Some candidate split separates a node with two or more components: Frobenius splits
([ABBKS26, Lemma 5.24]), spectral splits along a net of the subspace found
([ABBKS26, Lemma 5.25]), and mean splits ([ABBKS26, Lemma 6.16]).
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section


open Matrix

open Common MeasureTheory
open scoped BigOperators
variable {n k d : ℕ}

def netBound (D : ℕ) (α : ℚ) : ℕ := (1 + ⌈64 * (D : ℚ) / α⌉₊) ^ D

def frobCap (k : ℕ) : ℕ := 2 ^ (k - 1)


/-- Frobenius-close separated centered components contain a thin direction. -/
theorem thin_direction
    (F : FrameModel k d) (I : Finset (Fin k)) (C₀ ρ Δ c : ℝ)
    (hI : 2 ≤ I.card) (hc : 0 < c ∧ c ≤ C₀)
    (hcov : ∀ j ∈ I, (F.cov j).PosDef ∧ LE (F.cov j) (C₀ • (1 : Mat d)))
    (hf : ∀ a ∈ I, ∀ b ∈ I, frobSq (F.cov a - F.cov b) ≤ ρ ^ 2)
    (hs : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → CenteredSeparated Δ (F.cov a) (F.cov b))
    (hΔ : C₀ < Δ ^ 2 * c) (hρ : ρ * C₀ ≤ Δ * c ^ 2) (hρ₀ : 0 ≤ ρ) :
    ∃ j ∈ I, ∃ v, sqnorm v = 1 ∧ qform (F.cov j) v < c := by
  classical
  by_contra h
  have hl (j) (hj : j ∈ I) (v) : c * sqnorm v ≤ qform (F.cov j) v := by
    apply CompleteAux.lower_of_unit
    intro u hu
    by_contra hh
    exact h ⟨j, hj, u, hu, lt_of_not_ge hh⟩
  have hu (j) (hj : j ∈ I) (v) : qform (F.cov j) v ≤ C₀ * sqnorm v := by
    simpa [qform, sqnorm, smul_mulVec, dotProduct_smul, smul_eq_mul]
      using (hcov j hj).2 v
  have hC : 0 < C₀ := hc.1.trans_le hc.2
  have hsq : ρ ^ 2 * C₀ ^ 2 ≤ Δ ^ 2 * c ^ 4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hρ₀ hC.le) hρ 2
    nlinarith only [hh]
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  have ht : ((F.cov a - F.cov b) * (F.cov a - F.cov b)).trace ≤ ρ ^ 2 := by
    rw [CompleteAux.trace_sq _ ((hcov a ha).1.isHermitian.sub (hcov b hb).1.isHermitian)]
    exact hf a ha b hb
  have hsep := Separation.spectrallySeparated_of_centeredSeparated
    (hcov a ha).1 (hcov b hb).1 hc.1 (hl a ha) (hl b hb)
    (hu a ha) (hu b hb) ht hsq (hs a ha b hb hab)
  have hn (v : Vec d) : 0 ≤ sqnorm v := by
    simpa [sqnorm] using dotProduct_self_star_nonneg v
  rcases hsep with ⟨v, hv⟩ | ⟨v, hv⟩
  · have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hpos : 0 < sqnorm v := lt_of_le_of_ne (hn v)
      (Ne.symm (fun hz ↦ hv0 (dotProduct_self_eq_zero.mp hz)))
    have hlow := mul_le_mul_of_nonneg_left (hl b hb v) (sq_nonneg Δ)
    have hhigh := hu a ha v
    have := mul_lt_mul_of_pos_right hΔ hpos
    dsimp only [qform] at *
    nlinarith
  · have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hpos : 0 < sqnorm v := lt_of_le_of_ne (hn v)
      (Ne.symm (fun hz ↦ hv0 (dotProduct_self_eq_zero.mp hz)))
    have hlow := mul_le_mul_of_nonneg_left (hl a ha v) (sq_nonneg Δ)
    have hhigh := hu b hb v
    have := mul_lt_mul_of_pos_right hΔ hpos
    dsimp only [qform] at *
    nlinarith


end

end ABBKS26.Tree
