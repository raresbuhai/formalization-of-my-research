module

public import ABBKS26.Tree.RefineAuxAffine
public import Mathlib.Topology.Order.Compact

/-! Uniform covariance bounds for all references compatible with one observed block. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix Robust
open scoped BigOperators Topology

variable {n k d : ℕ}

def observedCenter (x : Fin n → Vec d) (N : Finset (Fin n)) : Vec d :=
  (N.card : ℝ)⁻¹ • ∑ l ∈ N, x l

def observedCov (x : Fin n → Vec d) (N : Finset (Fin n)) : Mat d :=
  (N.card : ℝ)⁻¹ • ∑ l ∈ N,
    vecMulVec (x l - observedCenter x N) (x l - observedCenter x N)

/-- The covariance of the full observed block dominates every compatible clean reference. -/
theorem reference_cov_le_observed (R : Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ maxContamination π t) :
    LE ((0.68 : ℝ) • R.cov) (observedCov R.observed R.block) := by
  classical
  have hε := RBAux.contamination_small_pi R π t hR.1.1 hπ he
  have hε0 : 0 ≤ R.contamination := by unfold Reference.contamination; positivity
  have hε1 : R.contamination ≤ 1 / 10000 := by linarith only [hε, hπ]
  have hr : (0 : ℝ) < R.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hR.2.2.2.2.1
  have hmiss : ((R.reference \ R.good).card : ℝ) ≤
      R.contamination * R.reference.card := by
    apply (div_le_iff₀ hr).mp
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hcard : ((R.reference \ R.good).card : ℝ) + R.good.card = R.reference.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hR.2.1
  have hgood : (R.good.card : ℝ) ≤ R.block.card := by
    exact_mod_cast Finset.card_le_card hR.2.2.1
  have hb : (0 : ℝ) < R.block.card := by
    have hh := mul_le_mul_of_nonneg_right hε1 hr.le
    linarith only [hmiss, hcard, hgood, hh, hr]
  have hbad : ((R.block \ R.good).card : ℝ) ≤ R.contamination * R.block.card := by
    apply (div_le_iff₀ hb).mp
    exact le_max_left _ _
  have hcard' : ((R.block \ R.good).card : ℝ) + R.good.card = R.block.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hR.2.2.1
  let st : FilterState n d := ⟨fun _ ↦ 1, observedCenter R.observed R.block, 1, 0, 0⟩
  have hmass (S : Finset (Fin n)) : st.mass S = S.card := by
    simp only [FilterState.mass, st, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrem : R.reference.card - st.mass R.good ≤ π * R.reference.card / 100 := by
    rw [hmass]
    have hh := mul_le_mul_of_nonneg_right hε hr.le
    linarith only [hmiss, hcard, hh]
  have hupper : st.mass R.block ≤ (11 / 10 : ℝ) * R.reference.card := by
    rw [hmass]
    have hh := mul_le_mul_of_nonneg_right hε1 hb.le
    have hsub : (R.good.card : ℝ) ≤ R.reference.card := by
      exact_mod_cast Finset.card_le_card hR.2.1
    linarith only [hbad, hcard', hh, hsub]
  have hl := RBAux.retained_covariance_lower R st π hR hres
    (fun _ ↦ by constructor <;> norm_num) hrem hupper (by rwa [hmass])
  have hcov : weightedCov R st = observedCov R.observed R.block := by
    simp only [weightedCov, hmass, st, one_smul, observedCov]
  rwa [hcov] at hl

/-- The same observed covariance bounds every population component, regardless of its label. -/
theorem component_cov_le_observed (R : Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ maxContamination π t) (j : Fin k) (v : Vec d) :
    π * qform (R.model.cov j) v ≤ 2 * qform (observedCov R.observed R.block) v := by
  have hc := population_component_second_le R π (1 / 10000) hR (by norm_num) hres v j
  have hl := reference_cov_le_observed R π t hR hres hπ he v
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hl
  change (0.68 : ℝ) * qform R.cov v ≤ qform (observedCov R.observed R.block) v at hl
  have hvar : 0 ≤ qform (R.model.cov j) v :=
    (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v
  have hw := mul_le_mul_of_nonneg_right (hR.1.2.1 j) hvar
  have hw0 := hR.1.1.le.trans (hR.1.2.1 j)
  have hcov0 : 0 ≤ qform R.cov v :=
    hR.2.2.2.2.2.1.posSemidef.dotProduct_mulVec_nonneg v
  nlinarith only [hc, hl, hw, mul_nonneg hw0 (sq_nonneg (v ⬝ᵥ (R.model.mean j - R.mean))),
    hcov0]


def pureStatistic (Q : Matrix (Fin d) (Fin d) ℚ) : Tree.Statistic d := ⟨Q, 0, 0⟩

theorem pureStatistic_integral (Q : Matrix (Fin d) (Fin d) ℚ) (hQ : Qᵀ = Q)
    (S : Mat d) (hS : S.PosSemidef) :
    (∫ y : EuclideanSpace ℝ (Fin d), (pureStatistic Q).eval y.ofLp
      ∂ProbabilityTheory.multivariateGaussian 0 S) =
      (Q.map (algebraMap ℚ ℝ) * S).trace := by
  have hA : (Q.map (algebraMap ℚ ℝ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, hQ]
  have hf : (fun y : EuclideanSpace ℝ (Fin d) ↦ (pureStatistic Q).eval y.ofLp) =
      Population.quadStat (Q.map (algebraMap ℚ ℝ)) 0 0 := by
    funext y
    simp [pureStatistic, Tree.Statistic.eval, Population.quadStat, qform]
  rw [hf, Population.integral_quadStat_multivariateGaussian hS hA]
  simp


def CenteredCompatible (x : Fin n → Vec d) (N : Finset (Fin n)) (π t : ℝ)
    (R : Reference n k d) : Prop :=
  R.Valid π ∧ R.Resilient 4 (1 / 10000) ∧ R.block = N ∧ R.observed = x ∧
    (∀ j, R.model.mean j = 0) ∧ R.contamination ≤ maxContamination π t


end

end ABBKS26.RefineAux
