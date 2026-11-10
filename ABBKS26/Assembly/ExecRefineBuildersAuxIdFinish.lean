module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAllowance
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdComplete

/-! Assembly of prepared affine bounds into identical-covariance builder geometry. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdFinish

open Common Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

/-- Bounds for the actual affine pullbacks, before the guarded dyadic rounding. -/
def Envelope (MC : MomentCode) (NC : NestedCode) (RC : RoundCode) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .identical M ε w η Δ D ω r ps →
      localBudget .identical k n d ps ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
      ∀ u ∈ IdProgram.grid MC NC RC (args k ps x h P, fuel),
        let a := (args k ps x h P, fuel)
        let q := statisticOf d (IdProgram.statistic a u)
        (∀ i, |q.b i| ≤ (2 : ℚ) ^ IdGuard.exponent a) ∧
        ∀ j ∈ I, |(IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a) q).eval
          (M.μ j) - q.eval (M.μ j)| ≤ 1 / 100

/-- Everything after the two explicit execution and affine-envelope obligations is proved:
shell validity, the thin-direction witness, rounding margins, grid membership, and verify. -/
theorem certificate (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (RC : RoundCode) (hRC : RoundSpecL RC)
    (hfuel : IdAllowance.Prepared MC NC) (hbound : Envelope MC NC RC) :
    IdGuard.Valid (IdProgram.statistics MC NC RC) ∧
      IdGuard.Complete (IdProgram.statistics MC NC RC) := by
  refine ⟨IdValidity.valid_of_magnitude MC hMC NC RC ?_, ?_⟩
  · intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP u hu
    exact (hbound k ps x fuel h P M ε w η Δ D ω r I
      hx hp hf hh hI hl hP u hu).1
  · intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP hcard
    obtain ⟨u, hu, hvar, hmean, hspread⟩ := IdDirection.prepared MC hMC NC hNC RC hRC
      ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP hcard
      (hfuel k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP)
    have hb := hbound k ps x fuel h P M ε w η Δ D ω r I
      hx hp hf hh hI hl hP u hu
    exact IdComplete.rounded_separator (IdProgram.statistics MC NC RC) ps x fuel h P
      M ε w η Δ D ω r I hI hx hp hf hh hl hP
      (IdProgram.statistic (args k ps x h P, fuel) u)
      (List.mem_map.mpr ⟨u, hu, rfl⟩) hb.1 hvar hmean hspread hb.2

end

end ABBKS26.Assembly.Exec.RefineSynth.IdFinish
