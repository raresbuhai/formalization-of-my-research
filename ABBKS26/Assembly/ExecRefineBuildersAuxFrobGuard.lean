module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobPure
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobBudget

/-! Exact provenance and conditional completeness after the all-threshold size guard. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobGuard

open Common _root_.ABBKS26.Tree Sources Builders

/-- The guard preserves exactly the original flag and decoded statistic of a raw entry.
Its acceptance condition inspects every scanned edge, rather than a chosen threshold. -/
theorem retained_iff (B : Budget .centered) (f : Args → PoolL) (a : Args)
    (q : Statistic a.1.1) :
    (q, true) ∈ (frobCode B f a).map (fun p ↦ (statisticOf a.1.1 p.1, p.2)) ↔
      ∃ p : StatisticL, (p, true) ∈ f a ∧ statisticOf a.1.1 p = q ∧
        ∀ e ∈ Thresholds.rawL a.1.1 a.1.2.2.2.1 a.1.2.2.2.2.1
          a.1.2.2.2.2.2 (FramePool.canonical a.1.1 p) (field a 6),
          (encEdge e).length ≤ B.limit a := by
  constructor
  · intro hq
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
    obtain ⟨hm, hfit⟩ := List.mem_filter.mp hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    have hflag : r.2 = true := congrArg Prod.snd heq
    have hstat : statisticOf a.1.1 r.1 = q := by
      have hh := congrArg Prod.fst heq
      simpa only [FramePool.canonical_agrees, statistic_roundtrip] using hh
    exact ⟨r.1, hflag ▸ hr, hstat, (fits_iff _ _).mp hfit⟩
  · rintro ⟨p, hp, heq, hsize⟩
    apply List.mem_map.mpr
    refine ⟨(FramePool.canonical a.1.1 p, true), ?_, ?_⟩
    · apply List.mem_filter.mpr
      exact ⟨List.mem_map.mpr ⟨(p, true), hp, rfl⟩, (fits_iff _ _).mpr hsize⟩
    · exact Prod.ext (by rw [FramePool.canonical_agrees, statistic_roundtrip, heq]) rfl


end ABBKS26.Assembly.Exec.RefineSynth.FrobGuard
