module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdLinear
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdEncoding
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecGuard

/-! Guard survival and geometry transport for bounded affine mean statistics. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdGuard

open Common _root_.ABBKS26.Tree Sources Builders Matrix
open Turing.MultiTapeTM ComputableInPolyTime

abbrev Statistics := List StatisticL
abbrev encStatistics := encList encStatistic

def precision (a : Args) : ℕ := FrobScan.coefficientExponent a

def exponent (a : Args) : ℕ := FrobScan.coefficientExponent a

noncomputable def budget : Budget .identical :=
  IdStorage.budget FrobScan.limit FrobScan.limit_polytime IdEncoding.canonical_envelope

/-- Only the depth check can empty these raw factors. No empirical verification is used. -/
def run (g : Args → Statistics) (a : Args) : PairDataL :=
  if a.1.2.2.2.2.1 < a.1.2.1 then
    ((g a).map (IdLinear.run a.1.1 (precision a) (exponent a)), IdWindows.run a)
  else ([], [])

theorem run_polytime (g : Args → Statistics)
    (hg : ComputableInPolyTime g encArgs encStatistics) :
    ComputableInPolyTime (run g) encArgs encPairData := by
  have hc : ComputableInPolyTime
      (fun a : Args ↦ decide (a.1.2.2.2.2.1 < a.1.2.1)) encArgs encBool :=
    binary_lt' (by fun_prop) (by fun_prop)
  unfold run
  apply FrameAux.Linear.ite_prop hc
  · apply ComputableInPolyTime.prod
    · apply mapWithInput hg
      exact IdLinear.run_polytime_of (by fun_prop)
        (FrobScan.coefficientExponent_polytime.comp (fst _ _))
        (FrobScan.coefficientExponent_polytime.comp (fst _ _)) (by fun_prop)
    · exact IdWindows.run_polytime
  · exact const ([], [])

theorem normal_run (g : Args → Statistics) (a : Args) :
    pairNormal a.1.1 (run g a) = run g a := by
  unfold run
  split_ifs
  · apply Prod.ext
    · simp only [pairNormal, List.map_map, Function.comp_def, IdLinear.canonical]
    · rfl
  · rfl

/-- Every raw pair fits, including on malformed inputs and at excessive global fuel. -/
theorem all_pairs_fit (g : Args → Statistics) (a : Args) :
    ∀ e ∈ pairsL .identical a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (pairNormal a.1.1 (run g a)), (encEdge e).length ≤ budget.limit a := by
  rw [normal_run]
  unfold run
  split_ifs
  · intro e he
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    obtain ⟨hb, hlo, hhi⟩ := IdWindows.endpoints a t.1 t.2.1 t.2.2 ht
    exact IdLinear.edge_envelope a (precision a) (exponent a) q' t.1 t.2.1 t.2.2
      (SpecGuard.parameter_bound a) hb hlo hhi
  · simp only [pairsL, List.flatMap_nil, List.not_mem_nil, false_implies, implies_true]

theorem code_run (g : Args → Statistics) (a : Args) :
    pairCode .identical budget (run g) a = run g a := by
  have hf := (fits_iff _ _).mpr (all_pairs_fit g a)
  change (if fits _ _ then _ else _) = _
  rw [hf]
  exact normal_run g a

theorem data_run {n d : ℕ} (g : Args → Statistics) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) :
    (pairSource .identical budget (run g)).data k ps x fuel h P =
      ((run g (args k ps x h P, fuel)).1.map (statisticOf d),
        (run g (args k ps x h P, fuel)).2) := by
  change ((pairCode .identical budget (run g) _).1.map (statisticOf d),
    (pairCode .identical budget (run g) _).2) = _
  rw [code_run]

theorem count {n d : ℕ} (g : Args → Statistics) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n))
    (hg : h < k → (g (args k ps x h P, fuel)).length ≤
      netBound (IdCov.N_pack (ps h).subspaceAccuracy k) (ps h).subspaceAccuracy) :
    (run g (args k ps x h P, fuel)).1.length *
      (run g (args k ps x h P, fuel)).2.length ≤ stepBranchCap .identical k (ps h) := by
  by_cases hh : h < k
  · have hw := IdWindows.radius_agrees k ps x fuel h P hh
    have ht := IdWindows.length_run (args k ps x h P, fuel)
    rw [hw] at ht
    change _ ≤ netBound _ _ * (2 * ABBKS26.RefineAux.meanThresholdRadius k (ps h) + 3)
    dsimp only [run, args]
    rw [ite_eq_left hh, List.length_map]
    exact Nat.mul_le_mul (hg hh) ht
  · dsimp only [run, args]
    rw [ite_eq_right hh]
    exact Nat.zero_le _

noncomputable section

/-- The bounded affine coefficients are the only population-validity obligation left. -/
def Valid (g : Args → Statistics) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .identical M ε w η Δ D ω r ps →
      localBudget .identical k n d ps ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
      ∀ q ∈ g (args k ps x h P, fuel), ∀ j ∈ I,
        qform (M.S j) (fun i ↦ (FrobRound.entry (precision (args k ps x h P, fuel))
          (exponent (args k ps x h P, fuel)) 1 (q.2.1.getD i.val 0) : ℝ)) ≤ 4

def Complete (g : Args → Statistics) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .identical M ε w η Δ D ω r ps →
      localBudget .identical k n d ps ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
      2 ≤ I.card →
      ∃ q ∈ (run g (args k ps x h P, fuel)).1.map (statisticOf d),
        ∃ t ∈ (run g (args k ps x h P, fuel)).2,
          Verify (ps h) x (pairEdge .identical h P q t)

theorem validity (g : Args → Statistics) (hg : Valid g)
    {n k d : ℕ} (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k))
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1) (hI : I.Nonempty)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    ∀ q ∈ ((pairSource .identical budget (run g)).data k ps x fuel h P).1,
      ∀ t ∈ ((pairSource .identical budget (run g)).data k ps x fuel h P).2,
        ScaleValid M I (ps h) (pairEdge .identical h P q t) := by
  rw [data_run]
  dsimp only [run, args]
  rw [ite_eq_left (show h < k by omega)]
  intro q hq t ht
  obtain ⟨qL, hqL, rfl⟩ := List.mem_map.mp hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hqL
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  have hw : (0 : ℚ) ≤ 1 / (16 * k : ℚ) := by positivity
  have hm := (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmass : ((ps h).windowMass : ℝ) =
      (1 / (16 * k : ℝ)) * ((ps h).straddle / 2) ^ 9 / 16 := by
    have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) hm
    push_cast at hc ⊢
    exact hc
  rw [IdLinear.decoded]
  dsimp only [ScaleValid, pairEdge, IdWindows.window]
  refine ⟨?_, ?_, hmass.le, rfl, rfl, rfl, ?_⟩
  · linarith only [hw]
  · linarith only [hw]
  · exact hg k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP q' hq'

theorem geometry (F : FrameCode) (g : Args → Statistics)
    (hv : Valid g) (hc : Complete g) :
    PairGeometry .identical F (pairSource .identical budget (run g)) := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP
  refine ⟨validity g hv ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP, ?_⟩
  intro hcard _
  rw [data_run]
  exact hc k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP hcard

end

end ABBKS26.Assembly.Exec.RefineSynth.IdGuard
