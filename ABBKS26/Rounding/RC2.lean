module

public import ABBKS26.Rounding.RawTransport

/-!
# Orthogonal-complement rounding

[ABBKS26, Theorem 4.2] (`roundComplement_spec`): deterministic rounding
(`ABBKS26.Rounding.detRound_spec`, [ABBKS26, Theorem 4.1]) applied to the nested system of
[ABBKS26, Lemma 4.3] returns a subspace approximately orthogonal to all solutions of the
original system.
-/

@[expose] public section

namespace ABBKS26.Rounding

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {d : ℕ}

structure ComplementInput (d : ℕ) where
  system : FamilySystem d
  degree : ℕ
  tolerance : ℚ
  radius : ℚ
  rankBound : ℕ
  M₁ : ℝ
  M₂ : ℝ
  X : ℝ

def ComplementInput.Hypotheses (I : ComplementInput d) (Ps : List (Mat d)) : Prop :=
  I.system.Valid I.degree ∧ Even I.degree ∧ 2 ≤ I.degree ∧
  0 < I.tolerance ∧ 0 < I.radius ∧ I.radius ≤ 1 / 2 ∧ 1 ≤ I.rankBound ∧
  1 ≤ I.M₁ ∧ 1 ≤ I.M₂ ∧ 1 ≤ I.X ∧
  25 * (I.tolerance : ℝ) ^ (1 / 8 : ℝ) ≤ I.radius ∧
  (∀ P ∈ Ps, Projection P ∧
    I.system.Derives I.degree I.M₁ I.X (C (I.tolerance : ℝ) - quad P)) ∧
  ∃ R : Mat d, Projection R ∧ R.rank ≤ I.rankBound ∧
    I.system.FeasibleComplement R I.M₂

/-- The full complement-rounding contract for one represented call. -/
def ComplementResultSpec (I : ComplementInput d) (Y : RoundOutput d) : Prop :=
  Y.basis.length ≤ rankCap I.radius I.rankBound ∧
    Projection Y.proj ∧ Y.proj.rank = Y.basis.length ∧
    ∀ Ps, I.Hypotheses Ps → Covers Y.proj
      {v | sqnorm v = 1 ∧ ∃ P ∈ Ps, 1 - (I.tolerance : ℝ) ≤ sqnorm (P *ᵥ v)}
      I.radius


/-- An actual rational representation, with explicit real-to-machine budget bounds.
The objective degree is separate because `RawRep` specifies only the constraints. -/
structure RCEncoding (I : ComplementInput d) where
  raw : RawInput
  problem : SoS.Solver.Problem
  normBound : ℚ
  dimension_eq : raw.family.dimension = d
  system_eq : dimension_eq ▸ raw.family.real = I.system
  degree_eq : raw.degree = I.degree
  tolerance_eq : raw.epsilon = I.tolerance
  represents : RawRep raw problem
  objective_degree : ∀ f ∈ problem.2.2.2.1 :: problem.2.2.2.2,
    (f.toPoly problem.numVars).totalDegree ≤ problem.degree
  ball_le : ballBound I.system I.degree I.tolerance I.M₁ I.X ≤ (raw.ball : ℝ)
  norm_one_le : 1 ≤ normBound
  norm_le : nestedNorm I.system I.degree I.tolerance I.M₂ ≤ (normBound : ℝ)

def RCEncoding.roundInput (I : ComplementInput d) (E : RCEncoding I) : RoundInput :=
  ⟨E.problem, d, I.radius, I.rankBound, E.normBound⟩

/-- RC2's eighth-root schedule implies DR's fourth-power concentration threshold. -/
theorem complement_round_parameters (ε γ : ℝ) (hε : 0 < ε) (hγ : γ ≤ 1 / 2)
    (hsmall : 25 * ε ^ (1 / 8 : ℝ) ≤ γ) :
    ε ≤ 1 ∧ 2 * Real.sqrt ε ≤ γ ^ 4 / 160000 := by
  let t := ε ^ (1 / 8 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg hε.le _
  have ht8 : t ^ 8 = ε := by
    simpa only [t, one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hε.le (by norm_num : 8 ≠ 0)
  have ht1 : t ≤ 1 := by change 25 * t ≤ γ at hsmall; linarith
  have hsqrt : Real.sqrt ε = t ^ 4 := by
    calc
      _ = Real.sqrt ((t ^ 4) ^ 2) := by congr 1; rw [← pow_mul]; exact ht8.symm
      _ = t ^ 4 := Real.sqrt_sq (by positivity)
  have hfour := pow_le_pow_left₀ (by positivity : 0 ≤ 25 * t) hsmall 4
  constructor
  · rw [← ht8]
    exact (pow_le_pow_left₀ ht ht1 8).trans_eq (one_pow 8)
  · rw [hsqrt]
    nlinarith only [hfour, pow_nonneg ht 4]

/-- Nested feasibility and concentration reduce each actual encoded RC2 call to specified DR.
Validity is derived from the current target; empty target sets need no feasible solver point. -/
theorem roundComplement_spec
    (round : (J : RoundInput) → RoundOutput J.ambient) (hround : RoundSpec round)
    (I : ComplementInput d) (E : RCEncoding I) :
    ComplementResultSpec I (round E.roundInput) := by
  rcases E with ⟨raw, problem, B, hd, hsys, hdeg, hεeq, hrep, hobj, hball, hB, hnorm⟩
  cases hd
  dsimp only [RCEncoding.roundInput]
  let J : RoundInput := ⟨problem, raw.family.dimension, I.radius, I.rankBound, B⟩
  refine ⟨(hround J).1, (hround J).2.1, (hround J).2.2.1, ?_⟩
  intro Ps hI v hv
  rcases hI with ⟨hA, _, _, hε, hγ, hγ1, hr1, _, _, _, hsmall, hPs,
    R, hR, hr, hcomp⟩
  have hγ1R : (I.radius : ℝ) ≤ 1 / 2 := by
    have he := Rat.cast_mono (K := ℝ) hγ1
    norm_num at he
    exact he
  obtain ⟨hε1, hsmall'⟩ := complement_round_parameters I.tolerance I.radius
    (by exact_mod_cast hε) hγ1R hsmall
  obtain ⟨P, hP, hnear⟩ := hv.2
  obtain ⟨y, hy, hs⟩ := nested_feasible I.system I.degree I.tolerance I.M₁ I.X raw.ball
    P v hA (hPs P hP).1 hv.1 (by exact_mod_cast hε) hnear hball (hPs P hP).2
  have hs' : SatisfiesNested raw.family.real raw.degree raw.epsilon raw.ball y := by
    simpa only [hsys, hdeg, hεeq] using hs
  have hvalid := RawTransport.valid_of_rep raw problem hrep hobj ⟨y, hs'⟩
  have htarget := RawTransport.target_of_satisfies raw problem hrep
    I.radius I.rankBound B v hv.1 y hy hs'
  have hconcentrated := RawTransport.concentrated_of_complement raw problem hrep
    (by simpa only [hsys, hdeg] using hA) hvalid I.radius I.rankBound B I.M₂ R hR hr
    (by simpa only [hεeq] using hε) (by rw [hεeq]; exact_mod_cast hε1)
    (by simpa only [hsys] using hcomp) hγ hγ1 hr1 hB
    (by simpa only [hεeq] using hsmall')
    (by simpa only [hsys, hdeg, hεeq] using hnorm)
  exact (hround J).2.2.2.2 hconcentrated v htarget


end

end ABBKS26.Rounding
