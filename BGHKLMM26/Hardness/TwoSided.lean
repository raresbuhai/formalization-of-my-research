module

public import Complexity.Computability.Complexity.Classes.Promise.Randomized
public import Complexity.Computability.Complexity.Classes.BPP.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform

/-!
# Randomized reductions with two-sided error

complexitylib's randomized reductions (`Cslib.Complexity.PromiseProblem.RPReducible`) err only on
no-instances. The reduction of [BGHKLMM26, Section 6] samples a sparse graph, and may fail on both
sides. `BGHKLMM26.Hard.RandReducible` allows error `1/10` on both, and `PromiseBPP` is closed under
it (`BGHKLMM26.Hard.RandReducible.mem_PromiseBPP`): run the reduction, then a solver for the target
with error `1/8`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Cslib Cslib.Complexity Cslib.Complexity.PromiseProblem Turing.MultiTapeTM Cslib.Probability

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {X : PromiseProblem α} {Y : PromiseProblem β}

/-- A **randomized polynomial-time reduction with two-sided error `1/10`**: a uniform strict PPT
program that maps yes-instances to yes-instances and no-instances to no-instances, each with
probability at least `9/10`. -/
def RandReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (X : PromiseProblem α)
    (Y : PromiseProblem β) : Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    (∀ a ∈ X.yes, 9 / 10 ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal) ∧
    ∀ a ∈ X.no, 9 / 10 ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal

/-- **`PromiseBPP` is closed under randomized reductions with two-sided error.** -/
theorem RandReducible.mem_PromiseBPP (hXY : RandReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  -- a solver for `Y` with error at most `1 / 8`
  obtain ⟨p, V, hV, hYV⟩ := mem_PromiseBPP_iff_forall_solvesWithErrorExponent.1 hY 3
  let M (b : β) : ProbComp Bool :=
    (fun w => V (b, w)) <$> BitString.sampleList (p.eval (encB b).length)
  have hMyes (b : β) (hb : b ∈ Y.yes) : 7 / 8 ≤ Pr[M b] := by
    rw [probability_sampleList_verifier, le_div_iff₀ (by positivity)]
    have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := b)
      (n := p.eval (encB b).length)
    have h := (hYV b).1 hb
    simp only [ErrorExponentAt, Bool.not_true, Polynomial.eval_ofNat] at h
    have h' : (7 : ℝ) * 2 ^ p.eval (encB b).length ≤ 8 * acceptCount V b (p.eval (encB b).length) :=
      by exact_mod_cast (by omega)
    linarith
  have hMno (b : β) (hb : b ∈ Y.no) : Pr[M b] ≤ 1 / 8 := by
    rw [probability_sampleList_verifier, div_le_iff₀ (by positivity)]
    have h := (hYV b).2 hb
    simp only [ErrorExponentAt, Bool.not_false, Polynomial.eval_ofNat] at h
    rw [← acceptCount] at h
    have h' : (8 : ℝ) * acceptCount V b (p.eval (encB b).length) ≤ 2 ^ p.eval (encB b).length :=
      by exact_mod_cast h
    linarith
  let T (a : α) : ProbComp Bool := R a >>= M
  have hT : IsPPTOn encA encBool T := hR.bind (IsPPTOn.of_seeded
    ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length encB)) hV)
  refine mem_PromiseBPP_iff_exists_isPPTOn.mpr ⟨T, hT, fun a ha => ?_, fun a ha => ?_⟩
  · have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y))
      Y.yes {true} (by norm_num : (0 : ℝ) ≤ 7 / 8) (hyesR a ha)
      fun y _ hy => by
        rw [PMF.toOuterMeasure_apply_singleton]
        exact hMyes y hy
    rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
    change 9 / 10 * (7 / 8) ≤ Pr[T a] at h
    linarith
  · have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
      (ProbComp.eval (R a)) (fun y => ProbComp.eval (M y)) Y.no {true}
      (by norm_num : (0 : ℝ) ≤ 1 / 8) fun y _ hy => by
        rw [PMF.toOuterMeasure_apply_singleton]
        exact hMno y hy
    rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at hfail
    change Pr[T a] ≤ _ at hfail
    have hadd := PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R a)) Y.no
    have hno := hnoR a ha
    rw [ProbComp.probability_not]
    linarith

/-- A deterministic reduction followed by a randomized one. -/
theorem PolyTimeReducible.trans_randReducible {γ : Type} {encC : γ ↪ List Bool}
    {Z : PromiseProblem γ} (hXY : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hYZ : RandReducible encB encC Y Z) : RandReducible encA encC X Z := by
  obtain ⟨f, hf, hyes, hno⟩ := hXY
  obtain ⟨R, hR, hRyes, hRno⟩ := hYZ
  exact ⟨fun a => R (f a), hR.preprocess hf, fun a ha => hRyes _ (hyes ha),
    fun a ha => hRno _ (hno ha)⟩

/-- **NP-hardness and a randomized reduction**: if `X` is NP-hard, reduces to `Y` with two-sided
error, and `Y ∈ PromiseBPP`, then `NP ⊆ BPP` for every encoding. -/
theorem NP_subset_BPP_of_npHard_of_randReducible (hX : PromiseProblem.NPHard encA X)
    (hXY : RandReducible encA encB X Y) (hY : Y ∈ PromiseBPP encB) :
    ∀ (γ : Type) (encC : γ ↪ List Bool), NP encC ⊆ BPP encC := by
  intro γ encC A hA
  have hXB : X ∈ PromiseBPP encA := hXY.mem_PromiseBPP hY
  exact ofSet_mem_PromiseBPP.mp ((hX encC A hA).mem_PromiseBPP hXB)

end BGHKLMM26.Hard
