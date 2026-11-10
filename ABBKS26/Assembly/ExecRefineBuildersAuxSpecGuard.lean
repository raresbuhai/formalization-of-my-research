module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecWindows

/-! Guard survival and scale validity for bounded spectral direction lists. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecGuard

open Common _root_.ABBKS26.Tree Sources Builders Matrix
open Turing.MultiTapeTM ComputableInPolyTime

def precision (a : Args) : ℕ := FrobScan.coefficientExponent a

def exponent (a : Args) : ℕ := FrobScan.coefficientExponent a

def run (g : Args → Points) (a : Args) : PairDataL :=
  ((g a).map (SpecSquare.run a.1.1 (precision a) (exponent a)), SpecWindows.run a)

theorem parameter_bound (a : Args) : precision a + exponent a + 1 ≤ FrobScan.key a ^ 4 := by
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hp : 1 ≤ z ^ 3 := one_le_pow₀ (by omega)
  change z ^ 3 + z ^ 3 + 1 ≤ z ^ 4
  calc
    _ ≤ 3 * z ^ 3 := by omega
    _ ≤ z * z ^ 3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem run_polytime (g : Args → Points)
    (hg : ComputableInPolyTime g encArgs encPoints) :
    ComputableInPolyTime (run g) encArgs encPairData := by
  apply ComputableInPolyTime.prod
  · apply mapWithInput hg
    exact SpecSquare.run_polytime_of (by fun_prop)
      (FrobScan.coefficientExponent_polytime.comp (fst _ _))
      (FrobScan.coefficientExponent_polytime.comp (fst _ _)) (by fun_prop)
  · exact SpecWindows.run_polytime

theorem square_canonical (d p b : ℕ) (v : Vector) :
    FramePool.canonical d (SpecSquare.run d p b v) = SpecSquare.run d p b v := by
  apply Prod.ext
  · change FrameAux.Features.table d d (fun i j ↦
      ((FrameAux.Features.table d d fun r c ↦
        FrobRound.entry p b 1 (v.getD r 0) * FrobRound.entry p b 1 (v.getD c 0)).getD
          i []).getD j 0) = _
    unfold FrameAux.Features.table
    apply List.map_congr_left
    intro i hi
    apply List.map_congr_left
    intro j hj
    dsimp only
    rw [FrameAux.Linear.getD_map_range _ _ (List.mem_range.mp hi),
      FrameAux.Linear.getD_map_range _ _ (List.mem_range.mp hj)]
  · apply Prod.ext
    · change (List.range d).map (fun i ↦ (List.replicate d (0 : ℚ)).getD i 0) = _
      simp [SpecSquare.run]
    · rfl

theorem normal_run (g : Args → Points) (a : Args) :
    pairNormal a.1.1 (run g a) = run g a := by
  apply Prod.ext
  · simp only [pairNormal, run, List.map_map, Function.comp_def, square_canonical]
  · rfl

/-- Every pair fits, on malformed inputs too. The bound is independent of the direction
program's output bits and of global fuel. -/
theorem all_pairs_fit (g : Args → Points) (a : Args) :
    ∀ e ∈ pairsL .centered a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (pairNormal a.1.1 (run g a)), (encEdge e).length ≤ SpecSquare.budget.limit a := by
  rw [normal_run]
  intro e he
  obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  obtain ⟨hb, hlo, hhi⟩ := SpecWindows.endpoints a t.1 t.2.1 t.2.2 ht
  exact SpecSquare.edge_envelope a (precision a) (exponent a) v t.1 t.2.1 t.2.2
    (by simpa only [Nat.add_comm] using parameter_bound a) hb hlo hhi

theorem code_run (g : Args → Points) (a : Args) :
    pairCode .centered SpecSquare.budget (run g) a = run g a := by
  have hf := (fits_iff _ _).mpr (all_pairs_fit g a)
  change (if fits _ _ then _ else _) = _
  rw [hf]
  exact normal_run g a

theorem data_run {n d : ℕ} (g : Args → Points) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) :
    (pairSource .centered SpecSquare.budget (run g)).data k ps x fuel h P =
      ((run g (args k ps x h P, fuel)).1.map (statisticOf d),
        (run g (args k ps x h P, fuel)).2) := by
  change ((pairCode .centered SpecSquare.budget (run g) _).1.map (statisticOf d),
    (pairCode .centered SpecSquare.budget (run g) _).2) = _
  rw [code_run]

theorem count {n d : ℕ} (g : Args → Points) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k)
    (hg : (g (args k ps x h P, fuel)).length ≤
      netBound (Centered.dimensionCap ((ps h).w / 2)
        (10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10) (ps h).subspaceAccuracy)
        (ps h).subspaceAccuracy) :
    (run g (args k ps x h P, fuel)).1.length *
      (run g (args k ps x h P, fuel)).2.length ≤ centeredStageCap false k (ps h) := by
  rw [show (run g (args k ps x h P, fuel)).1.length =
    (g (args k ps x h P, fuel)).length from List.length_map ..]
  have ht := congrArg List.length (SpecWindows.agrees k ps x fuel h P hh)
  simp only [List.length_map, ABBKS26.RefineAux.spectralThresholds_length] at ht
  change _ * (SpecWindows.run _).length ≤ _
  rw [ht]
  simpa only [centeredStageCap, Bool.false_eq_true, ↓reduceIte, stepBranchCap,
    Nat.add_sub_cancel_left, ABBKS26.RefineAux.spectralThresholdCount]
    using Nat.mul_le_mul_right (ABBKS26.RefineAux.spectralThresholdCount (ps h)) hg

noncomputable section

theorem validity {n k d : ℕ} (g : Args → Points)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k))
    (hp : Prepared .centered M ε w η Δ D ω r ps) (hh : h < k - 1) :
    ∀ q ∈ ((pairSource .centered SpecSquare.budget (run g)).data k ps x fuel h P).1,
      ∀ t ∈ ((pairSource .centered SpecSquare.budget (run g)).data k ps x fuel h P).2,
        ScaleValid M I (ps h) (pairEdge .centered h P q t) := by
  rw [data_run]
  intro q hq t ht
  obtain ⟨qL, hqL, rfl⟩ := List.mem_map.mp hq
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hqL
  change ScaleValid M I (ps h) (pairEdge .centered h P
    (statisticOf d (SpecSquare.run d (precision (args k ps x h P, fuel))
      (exponent (args k ps x h P, fuel)) v)) t)
  rw [SpecSquare.decoded]
  change t ∈ SpecWindows.run (args k ps x h P, fuel) at ht
  rw [SpecWindows.agrees k ps x fuel h P (by omega)] at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hs0 : 0 < s := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    unfold sqrtUp
    positivity
  exact SpecSquare.scaleValid M ε w η Δ D ω r ps hp h hh P I _ s hs0

/-- Only a complete rounded direction remains to be supplied: the window factor,
normalization, validity, and all-pairs bit guard are already fixed. -/
def Complete (F : FrameCode) (g : Args → Points) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .centered M ε w η Δ D ω r ps →
      localBudget .centered k n d ps ≤ fuel → h < k - 1 →
      ∀ (hI : I.Nonempty), leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
      2 ≤ I.card → ¬ centeredFar F M ω r (ps h) fuel P I hI →
      ∃ q ∈ (run g (args k ps x h P, fuel)).1.map (statisticOf d),
        ∃ t ∈ SpecWindows.run (args k ps x h P, fuel),
          Verify (ps h) x (pairEdge .centered h P q t)

theorem geometry_of_complete (F : FrameCode) (g : Args → Points) (hg : Complete F g) :
    PairGeometry .centered F (pairSource .centered SpecSquare.budget (run g)) := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP
  refine ⟨validity g ps x fuel h P M ε w η Δ D ω r I hp hh, ?_⟩
  intro hcard hnf
  rw [data_run]
  exact hg k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP hcard (hnf rfl)

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecGuard
