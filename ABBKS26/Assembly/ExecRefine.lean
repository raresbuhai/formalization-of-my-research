module

public import ABBKS26.Assembly.ExecRefineKernels

/-!
# The refiner's executable lists

The block kernel returns the internally verified/merged RB3 pool and all L/I pairs. The
candidate wrapper below performs no additional acceptance test. Blocks are scanned separately,
so a failed block call cannot discard the children returned by another block.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Effective RB3, guarded Z/SUB, nets and fixed thresholds supply one compatible refiner. -/
theorem exists_refine_code
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ B : RefineCode, RefineSpecL B := by
  obtain ⟨A, hA⟩ := RefineSynth.exists_frobenius_kernel F hF
  obtain ⟨S, hS⟩ := RefineSynth.exists_spectral_kernel F hF M hM N hN R hR
  obtain ⟨I, hI⟩ := RefineSynth.exists_identical_kernel F hF M hM N hN R hR
  let C := RefineSynth.centeredKernel A S
  have hC := RefineSynth.centered_kernel_spec F A S hA hS
  refine ⟨RefineSynth.jointCode C I, ⟨RefineSynth.joint_contract C I hC hI,
    ?_, RefineSynth.joint_polytime C I hC hI, ?_, ?_⟩⟩
  · intro mode
    cases mode with
    | centered => exact hC.polytime
    | identical => exact hI.polytime
  · intro mode x fuel hx hf
    exact RefineSynth.joint_agrees C I hC hI mode x fuel hx hf
  · intro mode x fuel hx hf
    exact RefineSynth.joint_levels_size C I hC hI mode x fuel hx hf


end ABBKS26.Assembly.Exec
