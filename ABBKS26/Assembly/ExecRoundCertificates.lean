module

public import ABBKS26.Assembly.ExecRoundCertificatesAuxPoly
public import ABBKS26.Assembly.ExecRoundCertificatesAuxCapture
public import ABBKS26.Assembly.ExecRoundCertificatesAuxReading

/-!
# Certificates for the concrete deterministic rounder

`RoundProgram` is a rational list program, not a choice of `Rounding.detRound`.
The original interfaces live unchanged in `ExecRoundAuxData` to avoid an import cycle.
The generic capped-loop and replay proofs in `ExecRoundAuxLoop` are independent of solver
correctness. The append-history, encoded-size, shape, and rank-cap invariants are proved
in `ExecRoundAuxFacts` on arbitrary inputs. `ExecRoundAuxPoly` certifies exact rational
projectors, the binary packing and greedy counts, both prescribed precisions, candidate
normalization, and the append guard, all with absolute polynomial degree.

`ExecRoundCertificatesAuxPoly` compiles the planner with bounds on both loops' intermediate
states. `ExecRoundCertificatesAuxGeometry` interprets the rational projectors and residual tests
and bounds the stored bases and local solver budgets. These bounds remove every fuel cap.
`ExecRoundCertificatesAuxCapture` proves acceptance, covariance progress, greedy capture, and
packing for the concrete lists. `ExecRoundCertificatesAuxReading` bounds solver concentration
and objective rounding. Together they force a covering stop. None of the proved invariants
assumes correctness on junk inputs. The given `NestedCode` is unnecessary here: `RoundArgs`
already contains the reified problem.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundCertificates

open Common Rounding RoundProgram
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped Matrix

abbrev code := RoundProgram.code

/-- List enumeration gives exactly the analytic quadratic objective and prescribed accuracy. -/
theorem objective_agrees (a : RoundArgs) (Q : MatrixL) :
    objective a Q = objectiveProblem (input a) (matrixOf a.2.1 Q) ∧
      (∀ P, accuracy a P = solverAccuracy (input a) P) := by
  constructor
  · have hrange : List.range a.2.1 = (List.finRange a.2.1).map Fin.val := by
      apply List.ext_getElem <;> simp
    simp only [objective, objectiveProblem, input, hrange, List.flatMap_map,
      List.map_map, Function.comp_def, matrixOf, FrameAux.Linear.ent]
  · intro P
    rfl

/-- Reading the rational table and then casting agrees with quadratic pseudo-moment reading. -/
theorem moments_agree (a : RoundArgs) (out : SoS.Solver.Output) :
    (matrixOf a.2.1 (moments a out)).map (algebraMap ℚ ℝ) = readMoments (input a) out := by
  ext i j
  simp [matrixOf, moments, table, input, readMoments, i.isLt, j.isLt]

/-- Capping the exponent before exponentiation implements the minimum of the true budget.
In particular no global fuel is copied into the accuracy or the high-degree problem. -/
theorem solverFuel_eq (P : SoS.Solver.Problem) (fuel : ℕ) (acc : ℚ × ℚ) :
    solverFuel P fuel = min fuel (SoS.Solver.budget (P, acc)) := by
  unfold solverFuel SoS.Solver.budget
  by_cases h : P.degree + 1 ≤ fuel
  · rw [min_eq_right h]
  · have hle : fuel ≤ P.degree + 1 := by omega
    have hp : fuel ≤ ((SoS.Solver.encProblem P).length + 2) ^ fuel :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) fuel)
    rw [min_eq_left hle, min_eq_left hp,
      min_eq_left (hp.trans (Nat.pow_le_pow_right (by omega) hle))]

/-- On every input the planner respects its encoding cap, cardinal cap, and append history. -/
theorem plan_invariants (q : RoundArgs × ℕ) :
    Safe q.1 q.2 (plan q) := plan_safe q

/-- The concrete planner is polynomial in its full input and unary fuel, including junk.
The degree of this machine certificate is absolute; correctness is not a runtime guard. -/
theorem plan_polytime : ComputableInPolyTime plan RoundAux.encArgsFuel encPoints := by
  exact Compile.plan_time

/-- Positive residual tests make the Gram matrix invertible at every append. Thus the list
has the analytic projection, rank, and common-grid conditioning required by `RoundSpec`. -/
theorem basis_geometry (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    Projection (output a B).proj ∧ (output a B).proj.rank = B.length ∧
      (output a B).WellConditioned (greedyPrecision a) := by
  exact Geometry.basis_geometry a B hB

private theorem solve_fuel_eq (I : RoundInput) (fuel : ℕ) (hf : roundFuel I ≤ fuel)
    (B : Points) (hB : GoodBasis (roundArgs I) B)
    (hn : I.problem.numVars ≤ (SoS.Solver.encProblem I.problem).length) :
    solve (roundArgs I) fuel (roundedProjection (roundArgs I) B) =
      solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B) := by
  have hb := Bounds.sufficient_solver_fuel I B hB hn (0, 0)
  unfold solve
  dsimp only
  rw [solverFuel_eq _ fuel (0, 0), solverFuel_eq _ (roundFuel I) (0, 0),
    min_eq_right (hb.trans hf), min_eq_right hb]

private theorem greedyStep_fuel_eq (I : RoundInput) (fuel : ℕ)
    (hf : roundFuel I ≤ fuel) (M : MatrixL) (s : Bool × Points)
    (hs : Safe (roundArgs I) (roundFuel I) s.2) :
    greedyStep (roundArgs I) fuel M s = greedyStep (roundArgs I) (roundFuel I) M s := by
  unfold greedyStep
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · rfl
      · rename_i y _
        by_cases hv : acceptable (roundArgs I) s.2 (candidate (roundArgs I) s.2 y)
        · have hgood := GoodBasis.snoc hs.2.2 hv (candidate_grid (roundArgs I) s.2 y)
          have hlen : (s.2 ++ [candidate (roundArgs I) s.2 y]).length ≤
              rankCap (roundArgs I).2.2.1 (roundArgs I).2.2.2.1 := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hsize := (Bounds.basis_size_bound _ _ hgood hlen).trans
            (Bounds.sufficient_basis_fuel I)
          simp only [hv, hsize, hsize.trans hf, and_self, ite_true]
        · simp only [hv, false_and, ite_false]

private theorem iterate_eq_on {α : Type} (f g : α → α) (P : α → Prop)
    (hfg : ∀ s, P s → f s = g s) (hg : ∀ s, P s → P (g s))
    (s : α) (hs : P s) (n : ℕ) : f^[n] s = g^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact hfg _ (iterate_preserves g P hg s hs n)

private theorem greedy_iterate_fuel_eq (I : RoundInput) (fuel : ℕ)
    (hf : roundFuel I ≤ fuel) (M : MatrixL) (B : Points)
    (hB : Safe (roundArgs I) (roundFuel I) B) (n : ℕ) :
    ((greedyStep (roundArgs I) fuel M)^[n]) (false, B) =
      ((greedyStep (roundArgs I) (roundFuel I) M)^[n]) (false, B) := by
  exact iterate_eq_on _ _ (fun s : Bool × Points ↦ Safe _ (roundFuel I) s.2)
    (fun s hs ↦ greedyStep_fuel_eq I fuel hf M s hs)
    (greedyStep_safe _ _ _) (false, B) hB n

private theorem greedy_fuel_eq (I : RoundInput) (fuel : ℕ)
    (hf : roundFuel I ≤ fuel) (M : MatrixL) (B : Points)
    (hB : Safe (roundArgs I) (roundFuel I) B) :
    greedy (roundArgs I) fuel M B = greedy (roundArgs I) (roundFuel I) M B := by
  have hc := (Bounds.sufficient_counts I).1
  unfold greedy
  simp only [roundArgs] at hc ⊢
  rw [min_eq_right (hc.trans hf), min_eq_right hc]
  exact congrArg Prod.snd (greedy_iterate_fuel_eq I fuel hf M B hB _)

private theorem outerStep_fuel_eq (I : RoundInput) (fuel : ℕ)
    (hf : roundFuel I ≤ fuel) (s : Bool × Points)
    (hs : Safe (roundArgs I) (roundFuel I) s.2)
    (hn : I.problem.numVars ≤ (SoS.Solver.encProblem I.problem).length) :
    outerStep (roundArgs I) fuel s = outerStep (roundArgs I) (roundFuel I) s := by
  unfold outerStep
  split
  · rfl
  · dsimp only
    rw [solve_fuel_eq I fuel hf s.2 hs.2.2 hn, greedy_fuel_eq I fuel hf _ s.2 hs]

private theorem outer_iterate_fuel_eq (I : RoundInput) (fuel : ℕ)
    (hf : roundFuel I ≤ fuel)
    (hn : I.problem.numVars ≤ (SoS.Solver.encProblem I.problem).length) (n : ℕ) :
    ((outerStep (roundArgs I) fuel)^[n]) (false, []) =
      ((outerStep (roundArgs I) (roundFuel I))^[n]) (false, []) := by
  exact iterate_eq_on _ _ (fun s : Bool × Points ↦ Safe _ (roundFuel I) s.2)
    (fun s hs ↦ outerStep_fuel_eq I fuel hf s hs hn)
    (outerStep_safe _ _) (false, []) (safe_nil _ _) n

/-- Sufficient fuel removes every cap in this fixed planner, even on nonconcentrated inputs.
This is equality of stored rational lists, not just equality of their spans. -/
theorem plan_stable (I : RoundInput) (fuel : ℕ) (hf : roundFuel I ≤ fuel) :
    plan (roundArgs I, fuel) = plan (roundArgs I, roundFuel I) := by
  unfold plan
  split
  · rename_i hn
    have hc := (Bounds.sufficient_counts I).2
    simp only [roundArgs] at hn hc ⊢
    rw [min_eq_right (hc.trans hf), min_eq_right hc]
    exact congrArg Prod.snd (outer_iterate_fuel_eq I fuel hf hn _)
  · rfl

private theorem trace_cast (d : ℕ) (M : MatrixL) :
    (trace d M : ℝ) = ((matrixOf d M).map (algebraMap ℚ ℝ)).trace := by
  rw [Capture.trace_matrix]
  simp [Matrix.trace, Matrix.diag]

private theorem trace_multiply_cast (d : ℕ) (A B : MatrixL) :
    (trace d (multiply d A B) : ℝ) =
      ((matrixOf d A).map (algebraMap ℚ ℝ) *
        (matrixOf d B).map (algebraMap ℚ ℝ)).trace := by
  rw [trace_cast, Capture.multiply_matrix, Matrix.map_mul]

private theorem solve_correct (I : RoundInput) (hI : I.Concentrated) (B : Points)
    (hB : GoodBasis (roundArgs I) B) :
    let Q := matrixOf I.ambient (roundedProjection (roundArgs I) B)
    SoS.Solver.Correct (objectiveProblem I Q) (solverAccuracy I (objectiveProblem I Q))
      (solverAccuracy I (objectiveProblem I Q))
      (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B)) := by
  let a := roundArgs I
  let Q := roundedProjection a B
  let P := objective a Q
  have he : P = objectiveProblem I (matrixOf I.ambient Q) := (objective_agrees a Q).1
  have hP : P.Valid := by rw [he]; exact Reading.objective_valid I hI _
  have hb := Bounds.sufficient_solver_fuel I B hB (SoS.Correct.numVars_le hI.2.1) (0, 0)
  change SoS.Solver.Correct (objectiveProblem I _) _ _ _
  rw [← he]
  change SoS.Solver.Correct P (accuracy a P) (accuracy a P) (solve a (roundFuel I) Q)
  unfold solve
  dsimp only
  rw [solverFuel_eq _ _ (0, 0), min_eq_right hb]
  exact SoS.Correct.core_correct P hP _ _ (by unfold accuracy; positivity)
    (by unfold accuracy; positivity)

private theorem outerStep_prefix (a : RoundArgs) (fuel : ℕ) (s : Bool × Points) :
    s.2 <+: (outerStep a fuel s).2 ∧
      (outerStep a fuel s).2.length ≤ s.2.length + greedyCap a.2.2.1 a.2.2.2.1 := by
  unfold outerStep
  split
  · exact ⟨List.prefix_refl _, by omega⟩
  · dsimp only
    split
    · exact ⟨List.prefix_refl _, by simp⟩
    · split
      · exact ⟨List.prefix_refl _, by simp⟩
      · split
        · exact ⟨List.prefix_refl _, by simp⟩
        · have h := Capture.greedy_iterate_prefix a fuel
            (moments a (solve a fuel (roundedProjection a s.2))) (false, s.2)
            (min fuel (greedyCap a.2.2.1 a.2.2.2.1))
          refine ⟨h.1, h.2.trans ?_⟩
          exact Nat.add_le_add_left (min_le_right _ _) _

private theorem outer_iterate_prefix (a : RoundArgs) (fuel : ℕ) (s : Bool × Points)
    (n : ℕ) : s.2 <+: (((outerStep a fuel)^[n]) s).2 ∧
      (((outerStep a fuel)^[n]) s).2.length ≤
        s.2.length + n * greedyCap a.2.2.1 a.2.2.2.1 := by
  induction n with
  | zero => exact ⟨List.prefix_refl _, by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := outerStep_prefix a fuel (((outerStep a fuel)^[n]) s)
    refine ⟨ih.1.trans h.1, ?_⟩
    rw [Nat.succ_mul]
    omega

private theorem outer_prefix_between (a : RoundArgs) (fuel i j : ℕ) (hij : i ≤ j) :
    (((outerStep a fuel)^[i]) (false, [])).2 <+:
      (((outerStep a fuel)^[j]) (false, [])).2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_comm i k, Function.iterate_add_apply]
  exact (outer_iterate_prefix a fuel _ k).1

private theorem outer_reading (I : RoundInput) (hI : I.Concentrated)
    (R : Mat I.ambient)
    (hconc : ∀ (Q : Matrix (Fin I.ambient) (Fin I.ambient) ℚ) (out : SoS.Solver.Output),
      SoS.Solver.Correct (objectiveProblem I Q) (solverAccuracy I (objectiveProblem I Q))
        (solverAccuracy I (objectiveProblem I Q)) out →
      ((1 - R) * readMoments I out).trace ≤ (I.radius : ℝ) ^ 4 / 150000)
    (B : Points) (hB : Safe (roundArgs I) (roundFuel I) B) :
    let a := roundArgs I
    let Q := roundedProjection a B
    let M := moments a (solve a (roundFuel I) Q)
    let P : Mat I.ambient := (output a B).proj
    let N := (matrixOf I.ambient M).map (algebraMap ℚ ℝ)
    N.PosSemidef ∧ |trace I.ambient M - 1| ≤ 1 / 4 ∧ N.trace ≤ 5 / 4 ∧
      (1 - I.radius ^ 2 / 4 ≤ trace I.ambient (multiply I.ambient Q M) →
        ∀ v, I.Target v → 1 - (I.radius : ℝ) ^ 2 / 2 ≤ qform P v) ∧
      (¬1 - I.radius ^ 2 / 4 ≤ trace I.ambient (multiply I.ambient Q M) →
        (I.radius : ℝ) ^ 2 / 8 ≤ ((1 - P) * N).trace) ∧
      ((1 - R) * N).trace ≤ (I.radius : ℝ) ^ 4 / 150000 := by
  let a := roundArgs I
  let P : Mat I.ambient := (output a B).proj
  let Q := roundedProjection a B
  let out := solve a (roundFuel I) Q
  let M := moments a out
  let N := readMoments I out
  have hP : Projection P := (basis_geometry a B hB.2.2).1
  have hc := solve_correct I hI B hB.2.2
  have hN : (matrixOf I.ambient M).map (algebraMap ℚ ℝ) = N := moments_agree a out
  have hread := solver_reading I hI P (matrixOf I.ambient Q) hP
    (Reading.rounded_projection_error a hI.2.2.1 B hB.2.2) out hc
  obtain ⟨hPSD, htr, hstop, hcont⟩ := hread
  have htrrat : |trace I.ambient M - 1| ≤ 1 / 4 := by
    apply Rat.cast_le (K := ℝ) |>.1
    norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat]
    rw [trace_cast, hN]
    exact htr
  have htrace : N.trace ≤ 5 / 4 := by linarith [(abs_le.1 htr).2]
  have htQ : (trace I.ambient (multiply I.ambient Q M) : ℝ) =
      ((matrixOf I.ambient Q).map (algebraMap ℚ ℝ) * N).trace := by
    rw [trace_multiply_cast, hN]
  refine ⟨?_, htrrat, ?_, ?_, ?_, ?_⟩
  · change ((matrixOf I.ambient M).map (algebraMap ℚ ℝ)).PosSemidef
    rw [hN]
    exact hPSD
  · change ((matrixOf I.ambient M).map (algebraMap ℚ ℝ)).trace ≤ _
    rw [hN]
    exact htrace
  · intro hs
    have hs' := Rat.cast_le (K := ℝ) |>.2 hs
    push_cast at hs'
    rw [htQ] at hs'
    exact hstop hs'
  · intro hs
    rw [hN]
    have hs' : ((matrixOf I.ambient Q).map (algebraMap ℚ ℝ) * N).trace <
        1 - (I.radius : ℝ) ^ 2 / 4 := by
      rw [← htQ]
      have h := Rat.cast_lt (K := ℝ) |>.2 (lt_of_not_ge hs)
      push_cast at h
      exact h
    exact hcont hs'
  · rw [hN]
    exact hconc _ out hc

private theorem outerStep_continue (a : RoundArgs) (fuel : ℕ) (B : Points)
    (ht : |trace a.2.1 (moments a (solve a fuel (roundedProjection a B))) - 1| ≤ 1 / 4)
    (hs : ¬1 - a.2.2.1 ^ 2 / 4 ≤ trace a.2.1 (multiply a.2.1 (roundedProjection a B)
      (moments a (solve a fuel (roundedProjection a B)))))
    (hne : (greedy a fuel (moments a (solve a fuel (roundedProjection a B))) B).length ≠
      B.length) :
    outerStep a fuel (false, B) =
      (false, greedy a fuel (moments a (solve a fuel (roundedProjection a B))) B) := by
  unfold outerStep
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ite_eq_right (not_lt.2 ht), ite_eq_right hs, ite_eq_right hne]

/-- The abstract trace is the decoded actual planner and its actual solver/capture calls. -/
noncomputable def algorithmTrace (I : RoundInput) : DRTrace I where
  output := output (roundArgs I) (plan (roundArgs I, roundFuel I))
  outer j := let s := ((outerStep (roundArgs I) (roundFuel I))^[j]) (false, [])
    (s.1, output (roundArgs I) s.2)
  moments j :=
    let B := (((outerStep (roundArgs I) (roundFuel I))^[j]) (false, [])).2
    (matrixOf I.ambient (moments (roundArgs I)
      (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B)))).map
        (algebraMap ℚ ℝ)
  stop j :=
    let B := (((outerStep (roundArgs I) (roundFuel I))^[j]) (false, [])).2
    let M := moments (roundArgs I)
      (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B))
    1 - I.radius ^ 2 / 4 ≤
      trace I.ambient (multiply I.ambient (roundedProjection (roundArgs I) B) M)
  capture j :=
    let B := (((outerStep (roundArgs I) (roundFuel I))^[j]) (false, [])).2
    Capture.captureTrace I B (moments (roundArgs I)
      (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B)))

private theorem decoded_length (a : RoundArgs) (B : Points) :
    (output a B).basis.length = B.length := by
  change (B.map (vectorOf a.2.1)).length = B.length
  exact List.length_map _

private theorem captureTrace_agrees (I : RoundInput) (B : Points) (M : MatrixL) :
    ((Capture.captureTrace I B M).state (greedyCap I.radius I.rankBound)).2 =
      output (roundArgs I) (greedy (roundArgs I) (roundFuel I) M B) := by
  change output (roundArgs I)
    (((greedyStep (roundArgs I) (roundFuel I) M)^[greedyCap I.radius I.rankBound])
      (false, B)).2 = _
  have hf := (Bounds.sufficient_counts I).1
  unfold greedy
  simp only [roundArgs] at hf ⊢
  rw [min_eq_right hf]

private theorem decoded_length_ne (a : RoundArgs) (B D : Points) (Y : RoundOutput a.2.1)
    (hY : Y = output a D) (hne : Y.basis.length ≠ (output a B).basis.length) :
    D.length ≠ B.length := by
  simpa only [hY, decoded_length] using hne

private theorem decoded_transition (a : RoundArgs) (s : Bool × Points) (D : Points)
    (Y : RoundOutput a.2.1) (hs : s = (false, D)) (hY : Y = output a D) :
    (s.1, output a s.2) = (false, Y) := by
  rw [hs]
  exact Prod.ext rfl hY.symm

private theorem outerStep_decoded (I : RoundInput) (hI : I.Concentrated) (B : Points)
    (hB : Safe (roundArgs I) (roundFuel I) B)
    (hstop : ¬1 - I.radius ^ 2 / 4 ≤ trace I.ambient
      (multiply I.ambient (roundedProjection (roundArgs I) B)
        (moments (roundArgs I) (solve (roundArgs I) (roundFuel I)
          (roundedProjection (roundArgs I) B)))))
    (hne : ((Capture.captureTrace I B (moments (roundArgs I)
      (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B)))).state
        (greedyCap I.radius I.rankBound)).2.basis.length ≠
          (output (roundArgs I) B).basis.length) :
    let s := outerStep (roundArgs I) (roundFuel I) (false, B)
    (s.1, output (roundArgs I) s.2) = (false,
      ((Capture.captureTrace I B (moments (roundArgs I)
        (solve (roundArgs I) (roundFuel I) (roundedProjection (roundArgs I) B)))).state
          (greedyCap I.radius I.rankBound)).2) := by
  let a := roundArgs I
  let fuel := roundFuel I
  let M := moments a (solve a fuel (roundedProjection a B))
  let D := greedy a fuel M B
  have hD : D.length ≠ B.length :=
    decoded_length_ne a B D _ (captureTrace_agrees I B M) hne
  obtain ⟨R, ε, hR, hr, _, hε, emb, hemb, hsp, hsm, hDer⟩ := hI.2.2.2.2.2.2
  have hconc := Reading.concentration I hI R ε emb hemb hε hsp hsm hDer
  have htr := (outer_reading I hI R hconc B hB).2.1
  have he := outerStep_continue a fuel B htr hstop hD
  exact decoded_transition a _ D _ he (captureTrace_agrees I B M)

private theorem trace_continuing (I : RoundInput) (hI : I.Concentrated) (j : ℕ)
    (hb : ((algorithmTrace I).outer j).1 = false) (hstop : ¬(algorithmTrace I).stop j)
    (hne : (((algorithmTrace I).capture j).state (greedyCap I.radius I.rankBound)).2.basis.length ≠
      ((algorithmTrace I).outer j).2.basis.length) :
    (algorithmTrace I).outer (j + 1) =
      (false, (((algorithmTrace I).capture j).state (greedyCap I.radius I.rankBound)).2) := by
  let a := roundArgs I
  let fuel := roundFuel I
  let state (t : ℕ) := ((outerStep a fuel)^[t]) (false, [])
  let decode (s : Bool × Points) := (s.1, output a s.2)
  have hsafe : Safe a fuel (state j).2 :=
    iterate_preserves _ (fun s : Bool × Points ↦ Safe a fuel s.2)
      (outerStep_safe a fuel) (false, []) (safe_nil a fuel) j
  have hb' : state j = (false, (state j).2) := Prod.ext hb rfl
  have hn : state (j + 1) = outerStep a fuel (state j) :=
    Function.iterate_succ_apply' _ _ _
  exact (congrArg decode hn).trans
    ((congrArg (fun s ↦ decode (outerStep a fuel s)) hb').trans
      (outerStep_decoded I hI (state j).2 hsafe hstop hne))

/-- All abstract local laws follow from concrete matrix, list, solver and fuel certificates. -/
theorem trace_spec (I : RoundInput) : DRTraceSpec I (algorithmTrace I) := by
  let a := roundArgs I
  let fuel := roundFuel I
  let state (j : ℕ) := ((outerStep a fuel)^[j]) (false, [])
  let M (j : ℕ) := moments a (solve a fuel (roundedProjection a (state j).2))
  have hsafe (j : ℕ) : Safe a fuel (state j).2 :=
    iterate_preserves _ (fun s : Bool × Points ↦ Safe a fuel s.2)
      (outerStep_safe a fuel) (false, []) (safe_nil a fuel) j
  have hs := plan_invariants (roundArgs I, roundFuel I)
  obtain ⟨hP, hr, hc⟩ := basis_geometry _ _ hs.2.2
  refine
    { output_length := ?_, output_projection := hP, output_rank := ?_
      output_conditioned := ⟨greedyPrecision a, hc⟩, initial := rfl
      basis_prefix := ?_, range_mono := ?_, length := ?_, projection := ?_
      agrees := ?_, reading := ?_, concentration := ?_, capture_spec := ?_
      capture_prefix := ?_, capture_range := ?_, continuing := trace_continuing I }
  · simpa only [algorithmTrace, output, List.length_map, roundArgs] using hs.1
  · change _ = (List.map (vectorOf I.ambient) _).length
    rw [List.length_map]
    exact hr
  · intro i j hij
    exact (outer_prefix_between a fuel i j hij).map (vectorOf I.ambient)
  · intro i j hij
    exact Capture.prefix_range a _ _ (hsafe j).2.2 (outer_prefix_between a fuel i j hij)
  · intro j
    have h := (outer_iterate_prefix a fuel (false, []) j).2
    change (List.map (vectorOf I.ambient) (state j).2).length ≤ _
    rw [List.length_map]
    simpa only [List.length_nil, zero_add, state, a, roundArgs] using h
  · intro j
    exact (basis_geometry a _ (hsafe j).2.2).1
  · intro hI
    change output a (plan (a, fuel)) =
      output a (((outerStep a fuel)^[packCount I.radius I.rankBound + 1]) (false, [])).2
    congr 1
    have hn : a.1.numVars ≤ (SoS.Solver.encProblem a.1).length :=
      SoS.Correct.numVars_le hI.2.1
    have hc : packCount a.2.2.1 a.2.2.2.1 + 1 ≤ fuel := (Bounds.sufficient_counts I).2
    unfold plan
    rw [ite_eq_left hn, min_eq_right hc]
    rfl
  · intro hI j
    obtain ⟨R, ε, hR, hr, _, hε, emb, hemb, hsp, hsm, hDer⟩ := hI.2.2.2.2.2.2
    have hconc := Reading.concentration I hI R ε emb hemb hε hsp hsm hDer
    obtain ⟨hPSD, _, htr, hstop, hcont, _⟩ := outer_reading I hI R hconc _ (hsafe j)
    exact ⟨hPSD, htr, hstop, hcont⟩
  · intro hI
    obtain ⟨R, ε, hR, hr, _, hε, emb, hemb, hsp, hsm, hDer⟩ := hI.2.2.2.2.2.2
    have hconc := Reading.concentration I hI R ε emb hemb hε hsp hsm hDer
    refine ⟨R, hR, hr, ?_⟩
    intro j
    exact (outer_reading I hI R hconc _ (hsafe j)).2.2.2.2.2
  · intro _ j hlen hPSD ht
    change (List.map (vectorOf I.ambient) (state j).2).length + _ ≤ _ at hlen
    rw [List.length_map] at hlen
    exact Capture.captureTrace_spec I _ _ (hsafe j) hlen hPSD ht
  · intro j
    exact ((Capture.greedy_iterate_prefix a fuel (M j) (false, (state j).2)
      (greedyCap I.radius I.rankBound)).1).map (vectorOf I.ambient)
  · intro j v hv
    have hgood := (iterate_preserves _ (fun s : Bool × Points ↦ Safe a fuel s.2)
      (greedyStep_safe a fuel (M j)) (false, (state j).2) (hsafe j)
        (greedyCap I.radius I.rankBound)).2.2
    exact Capture.prefix_range a _ _ hgood
      (Capture.greedy_iterate_prefix a fuel (M j) (false, (state j).2) _).1 v hv


/-- The public one-vector step is a polynomial-time replay of the concrete planner. -/
theorem step_polytime : ComputableInPolyTime code.step
    (encPair (encPair encRoundArgs encUnary) encPoints) (encOption encVector) := by
  unfold code RoundProgram.code
  exact .of_tidy (ComputableTidilyInPolyTime.getElem? (encL := encList encVector)
    (plan_polytime.comp (fst _ _)).tidy
    ((length_list encVector).comp (snd _ _)).tidy)

/-- The public iterate certificate follows from the proved encoded-basis invariant. -/
theorem loop_polytime : ComputableInPolyTime (roundL code)
    (encPair encRoundArgs encUnary) encPoints :=
  RoundAux.loop_polytime code step_polytime

/-- Replaying returns the planner's actual list, with no change of coordinates or span. -/
theorem replay (q : RoundArgs × ℕ) : roundL code q = plan q :=
  RoundAux.replay_eq code q (plan q) (fun _ ↦ rfl) (plan_invariants q).2.1

/-- The semantic witness is the decoded concrete plan at the existing sufficient fuel.
The original nested encoder argument is retained, although the problem is already reified. -/
theorem semantic (_N : NestedCode) (_hN : NestedSpec _N) :
    ∃ run : (I : RoundInput) → RoundOutput I.ambient, RoundSpec run ∧
      ∀ I fuel, roundFuel I ≤ fuel →
        roundL code (roundArgs I, fuel) = (run I).basis.map (fun v ↦ List.ofFn v) := by
  let run : (I : RoundInput) → RoundOutput I.ambient := fun I ↦
    output (roundArgs I) (plan (roundArgs I, roundFuel I))
  refine ⟨run, ?_, ?_⟩
  · exact detRound_spec algorithmTrace trace_spec
  · intro I fuel hf
    rw [replay, plan_stable I fuel hf]
    exact (output_roundtrip _ _ (plan_invariants _).2.2.rows).symm

end ABBKS26.Assembly.Exec.RoundCertificates
