module

public import ABBKS26.Assembly.ExecRefineAuxWrapper
public import ABBKS26.Assembly.ExecRefineAuxSize
public import ABBKS26.Assembly.ExecRefineKernelsAuxRB3
public import ABBKS26.Assembly.ExecRefineKernelsAuxThresholds
public import ABBKS26.Assembly.ExecRefineSources

/-!
# Kernel obligations for the executable refiner

The three synthesis lemmas below are local: RB3, centered spectral pairs, and identical
covariance mean pairs. They must construct compatible typed and list kernels, rather than
assert computability of a classical choice. `KernelRepresentation` records agreement on
arbitrary parent subsets and a uniform edge-bit envelope as well as polynomial time.

The remaining assembly proofs are independent of those constructions. In particular,
`levels_storage` proves why a per-edge envelope suffices for a whole unfiltered level;
`refine_agrees` removes the three count truncations without bounding the incoming history.
No equality to the classical `Tree.refine` is required or asserted.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime

/-- P1's eligible rational pool, quantile anchors, Verify, and greedy distance merging
produce the capped RB3 list. Completeness is conditional only on the shared P1 FAR case. -/
theorem exists_frobenius_kernel (F : FrameCode) (hF : FrameSpec F) :
    ∃ K : Kernel, CenteredStageSpec F true K := by
  obtain ⟨P, hc, hg⟩ := exists_frobenius_source F hF
  exact ⟨Sources.frobKernel P,
    ⟨frob_source_representation P hc, frob_source_contract F P hg⟩⟩

/-- Degree-two certified moments followed by guarded Thm Z supply the spectral net times
its fixed threshold grid. All pairs are kept, including pairs that fail a window check. -/
theorem exists_spectral_kernel
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ K : Kernel, CenteredStageSpec F false K := by
  obtain ⟨P, hr, hc, hg⟩ := exists_spectral_source F hF M hM N hN R hR
  exact ⟨Sources.pairKernel .centered P,
    ⟨pair_source_representation .centered P hr, spectral_source_contract F P hc hg⟩⟩

/-- Rounded, magnitude-guarded moments and sparse SUB supply the mean net times its fixed
threshold grid, with an absolute sample-bit exponent and a quadratic log-degree exponent. -/
theorem exists_identical_kernel
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ K : Kernel, KernelSpec .identical K := by
  obtain ⟨P, hr, hc, hg⟩ := exists_identical_source F hF M hM N hN R hR
  exact ⟨Sources.pairKernel .identical P,
    ⟨pair_source_representation .identical P hr, identical_source_contract F P hc hg⟩⟩

/-- The complementary FAR cases combine, and the two independent hard caps add exactly. -/
theorem centered_kernel_spec (F : FrameCode) (A S : Kernel)
    (hA : CenteredStageSpec F true A) (hS : CenteredStageSpec F false S) :
    KernelSpec .centered (centeredKernel A S) := by
  have hc : BlockContract .centered (centeredKernel A S).run := by
    intro n d k ps x fuel h N
    obtain ⟨ha, hpa, hca⟩ := hA.contract k ps x fuel h N
    obtain ⟨hs, hps, hcs⟩ := hS.contract k ps x fuel h N
    refine ⟨?_, ?_, ?_⟩
    · change (A.run .centered k ps x fuel h N ++
        S.run .centered k ps x fuel h N).length ≤ _
      rw [List.length_append]
      have hcap : frobCap k ≤ stepBranchCap .centered k (ps h) := by
        unfold stepBranchCap
        exact Nat.le_add_right _ _
      simp only [centeredStageCap, ite_true, Bool.false_eq_true,
        ite_false] at ha hs
      omega
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpa e he
      · exact hps e he
    · intro M ε w η Δ D ω r I hx hp hf hh hI hl hN
      obtain ⟨hva, hfa⟩ := hca M ε w η Δ D ω r I hx hp hf hh hI hl hN
      obtain ⟨hvs, hfs⟩ := hcs M ε w η Δ D ω r I hx hp hf hh hI hl hN
      refine ⟨?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hva e he
        · exact hvs e he
      · intro hcard
        classical
        by_cases hfar : centeredFar F M ω r (ps h) fuel N I hI
        · obtain ⟨e, he, hv⟩ := hfa hcard hfar
          exact ⟨e, List.mem_append_left _ he, hv⟩
        · obtain ⟨e, he, hv⟩ := hfs hcard hfar
          exact ⟨e, List.mem_append_right _ he, hv⟩
  refine ⟨?_, hc⟩
  constructor
  · exact listAppend' hA.polytime hS.polytime
  · intro x fuel hx hf
    dsimp only
    intro h hh N
    change _ ++ _ = _
    rw [hA.agrees x fuel hx hf h hh N, hS.agrees x fuel hx hf h hh N]
    exact (List.map_append ..).symm
  · intro x fuel hx hf
    dsimp only
    intro h hh N e he
    rcases List.mem_append.mp he with he | he
    · exact (hA.edge_size x fuel hx hf h hh N e he).trans (le_max_left _ _)
    · exact (hS.edge_size x fuel hx hf h hh N e he).trans (le_max_right _ _)
  · intro x hx
    change levelBits _ _ _ (max (A.bits x) (S.bits x)) ≤ _
    rcases le_total (A.bits x) (S.bits x) with hb | hb
    · rw [max_eq_right hb]
      exact hS.storage x hx
    · rw [max_eq_left hb]
      exact hA.storage x hx

/-- Mode dispatch preserves the block contract and hence the existing extension theorem. -/
theorem joint_contract (C I : Kernel) (hC : KernelSpec .centered C)
    (hI : KernelSpec .identical I) : RefineSpec (jointCode C I).ref := by
  apply refine_spec
  intro n d mode
  cases mode with
  | centered => exact hC.contract
  | identical => exact hI.contract

/-- The generic wrapper certificate applies to both local programs on arbitrary inputs. -/
theorem joint_polytime (C I : Kernel) (hC : KernelSpec .centered C)
    (hI : KernelSpec .identical I) (mode : Mode) :
    ComputableInPolyTime (refineL (jointCode C I) mode)
      (encPair encRefineArgs encUnary) (encList encCandidate) := by
  apply refine_polytime
  cases mode with
  | centered => exact hC.polytime
  | identical => exact hI.polytime

/-- The typed refiner is the block-scan witness just constructed, with every original slot. -/
theorem joint_agrees (C I : Kernel) (hC : KernelSpec .centered C)
    (hI : KernelSpec .identical I) (mode : Mode) (x : Input) (fuel : ℕ)
    (hx : Valid x) (hf : need mode x ≤ fuel)
    (A : Candidate x.points.length (dim x.points)) :
    refineL (jointCode C I) mode ((dim x.points, x.k,
      (List.range x.k).map (fun h ↦ paramsList (Schedule.params mode x.wmin x.k h)),
      x.points, candidateList A), fuel) =
      ((jointCode C I).ref mode x.k (Schedule.params mode x.wmin x.k)
        (inputPoints x) fuel A).map candidateList := by
  apply refine_agrees (jointCode C I) (jointRun C I) (by intros; rfl)
    (joint_contract C I hC hI) mode x fuel hf
  · cases mode with
    | centered => exact hC.contract
    | identical => exact hI.contract
  · cases mode with
    | centered => exact hC.agrees x fuel hx hf
    | identical => exact hI.agrees x fuel hx hf

/-- Per-edge storage bounds pay for the whole level, including repeated path records. -/
theorem joint_levels_size (C I : Kernel) (hC : KernelSpec .centered C)
    (hI : KernelSpec .identical I) (mode : Mode) (x : Input) (fuel : ℕ)
    (hx : Valid x) (hf : need mode x ≤ fuel) (h : ℕ) (hh : h ≤ x.k - 1) :
    (encList encCandidate
      ((levels (jointCode C I).ref mode x.k (Schedule.params mode x.wmin x.k)
        (inputPoints x) fuel h).map candidateList)).length ≤ fuel := by
  have hs : RefineSpec (jointCode C I).ref := joint_contract C I hC hI
  have hk : 1 ≤ x.k := hx.2.2.2.1
  cases mode with
  | centered =>
    exact (levels_storage (jointRun C I) hs .centered x.k _ (inputPoints x) fuel
      (C.bits x) hk (hC.edge_size x fuel hx hf) h hh).trans ((hC.storage x hx).trans hf)
  | identical =>
    exact (levels_storage (jointRun C I) hs .identical x.k _ (inputPoints x) fuel
      (I.bits x) hk (hI.edge_size x fuel hx hf) h hh).trans ((hI.storage x hx).trans hf)

end ABBKS26.Assembly.Exec.RefineSynth
