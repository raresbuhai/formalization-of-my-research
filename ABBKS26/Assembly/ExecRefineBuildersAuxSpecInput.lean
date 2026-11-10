module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecSolver

/-! The centered family built from the shared executable moment payload. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecInput

open Common _root_.ABBKS26.Tree Sources Builders MvPolynomial
open Encoding (encRat)
open SoS.Solver (RawPoly encRawPoly)
open Turing.MultiTapeTM ComputableInPolyTime

def psi (d : ℕ) (p : RawPoly) : RawPoly :=
  p ++ NestedProgram.scale (-3) (MomentProgram.power d (MomentProgram.normSq d) 2)

def weight (a : Args) : ℚ := field a 0 / 2

def accuracy (a : Args) : ℚ := field a 10

def delta (a : Args) : ℚ := Centered.delta (weight a) (accuracy a)

def epsilonQ (a : Args) : ℚ := 8 * delta a ^ 2

def epsilonH (a : Args) : ℚ := 256 * delta a ^ 2 / weight a ^ 2

def tolerance (a : Args) : ℚ := Centered.roundTolerance (accuracy a)

def payload (F : FrameCode) (M : MomentCode) (a : Args) : RawPoly :=
  psi a.1.1 (SpecPayload.run F M a)

/-- The ball parameter is local data, separate from the external unary solver allowance. -/
def query (F : FrameCode) (M : MomentCode) (Bd : Args → ℚ) (a : Args) : NestedArgs × ℕ :=
  SpecSolver.query a.1.1 (payload F M a) (epsilonQ a) (epsilonH a) (tolerance a) (Bd a)

theorem psi_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ psi (d a) (p a)) enc encRawPoly :=
  listAppend' hp (NestedProgram.scale_polytime (const _)
    (SpecPoly.power_polytime_of 2 hd (SpecPoly.normSq_polytime_of hd)))

theorem delta_polytime : ComputableInPolyTime delta encArgs encRat := by
  unfold delta Centered.delta Centered.nu weight accuracy
  exact FrameAux.Linear.rat_pow' (rat_mul' (rat_div' (field_polytime 0) (const 2))
    (FrameAux.Linear.rat_pow' (field_polytime 10) (const 4))) (const 8)

theorem epsilonQ_polytime : ComputableInPolyTime epsilonQ encArgs encRat :=
  rat_mul' (const 8) (FrameAux.Linear.rat_pow' delta_polytime (const 2))

theorem epsilonH_polytime : ComputableInPolyTime epsilonH encArgs encRat :=
  rat_div' (rat_mul' (const 256) (FrameAux.Linear.rat_pow' delta_polytime (const 2)))
    (FrameAux.Linear.rat_pow' (rat_div' (field_polytime 0) (const 2)) (const 2))

theorem tolerance_polytime : ComputableInPolyTime tolerance encArgs encRat :=
  rat_mul' (const 7) (FrameAux.Linear.rat_pow' (field_polytime 10) (const 8))

theorem payload_polytime (F : FrameCode) (hF : FrameSpec F)
    (M : MomentCode) (hM : MomentSpec M) :
    ComputableInPolyTime (payload F M) encArgs encRawPoly :=
  psi_polytime_of (by fun_prop) (SpecPayload.run_polytime F hF M hM)

theorem query_polytime (F : FrameCode) (hF : FrameSpec F)
    (M : MomentCode) (hM : MomentSpec M) (Bd : Args → ℚ)
    (hB : ComputableInPolyTime Bd encArgs encRat) :
    ComputableInPolyTime (query F M Bd) encArgs (encPair encNestedArgs encUnary) :=
  SpecSolver.query_polytime_of (by fun_prop) (payload_polytime F hF M hM)
    epsilonQ_polytime epsilonH_polytime tolerance_polytime hB

noncomputable section

theorem psi_real (d : ℕ) (p : RawPoly) :
    SoS.toReal ((psi d p).toPoly d) = SoS.toReal (p.toPoly d) - 3 * nsq ^ 2 := by
  simp [psi, SoS.Poly.toPoly_append, NestedProgram.scale_toPoly,
    MomentProgram.power_toPoly, MomentProgram.normSq_toPoly, SoS.toReal, nsq]
  simp only [map_ofNat]
  ring

private theorem sum_addE (d : ℕ) (a b : List ℕ) :
    (SoS.Poly.expo d (SoS.Poly.addE d a b)).sum =
      (SoS.Poly.expo d a).sum + (SoS.Poly.expo d b).sum := by
  have he : SoS.Poly.expo d (SoS.Poly.addE d a b) = SoS.Poly.addE d a b := by
    apply List.ext_getElem (by simp [SoS.Poly.expo, SoS.Poly.addE])
    intro i hi hi'
    have hid : i < d := by simpa [SoS.Poly.addE] using hi'
    simp [SoS.Poly.expo, List.getD_eq_getElem?_getD, hid]
  rw [he]
  exact List.sum_map_add

private theorem normSq_raw (d : ℕ) :
    ∀ z ∈ MomentProgram.normSq d, (SoS.Poly.expo d z.1).sum = 2 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  rw [← SoS.Mono.degree_toFinsupp (SoS.Poly.length_expo d _),
    SoS.Poly.toFinsupp_expo,
    MomentProgram.unitExp_toFinsupp _ _ _ (List.mem_range.mp hi),
    Finsupp.degree_single]

private theorem normSq_square_raw (d : ℕ) :
    ∀ z ∈ MomentProgram.power d (MomentProgram.normSq d) 2,
      (SoS.Poly.expo d z.1).sum = 4 := by
  have he : MomentProgram.power d (MomentProgram.normSq d) 2 =
      SoS.Coords.mulRaw d (MomentProgram.normSq d) (MomentProgram.normSq d) := by
    unfold MomentProgram.power
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    congr 1
    unfold SoS.Coords.mulRaw MomentProgram.constant
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    conv_rhs => rw [← List.map_id (MomentProgram.normSq d)]
    apply List.map_congr_left
    intro z hz
    have hlen : z.1.length = d := by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      simp [MomentProgram.unitExp]
    congr 1
    · apply List.ext_getElem (by simp [SoS.Poly.addE, hlen])
      intro i hi hi'
      have hid : i < d := by simpa [SoS.Poly.addE] using hi
      simp only [SoS.Poly.addE, List.getElem_map, List.getElem_range,
        List.getD_nil, zero_add]
      exact List.getD_eq_getElem _ _ hi'
    · exact one_mul _
  rw [he]
  intro z hz
  obtain ⟨a, ha, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
  rw [sum_addE, normSq_raw d a ha, normSq_raw d b hb]

/-- The encoded quartic and the radial correction have raw degree at most four, even
when zero coefficients occur among the dense monomials. -/
theorem payload_raw (F : FrameCode) (M : MomentCode) (a : Args) :
    ∀ z ∈ payload F M a, (SoS.Poly.expo a.1.1 z.1).sum ≤ 4 := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hz
    have hm := SoS.Mono.mem_all.mp (SpecRound.monomials_eq a.1.1 ▸ hμ)
    have he : SoS.Poly.expo a.1.1 μ = μ := by
      apply List.ext_getElem (by simpa using hm.1.symm)
      intro i hi hi'
      simp [SoS.Poly.expo, List.getD_eq_getElem?_getD, hi']
    rw [he]
    exact hm.2
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    exact (normSq_square_raw a.1.1 t ht).le

private theorem rounded_homogeneous {d : ℕ} (p : QPoly d) (r : ℕ)
    (hp : p.IsHomogeneous 4) : (roundPoly r p).IsHomogeneous 4 := by
  apply IsHomogeneous.sum
  intro α hα
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp hα)

/-- Every compatible clean-pass payload is a homogeneous quartic. -/
theorem prepared_homogeneous {n k d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    ((payload F MC (args k ps x h P, fuel)).toPoly d).IsHomogeneous 4 := by
  have hquartic := (SpecMoments.prepared_quartic F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf).1
  have hround := SpecPayload.prepared_agrees F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  have hn : ((MomentProgram.normSq d).toPoly d).IsHomogeneous 2 := by
    rw [MomentProgram.normSq_toPoly]
    exact IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow i 2
  change ((psi d (SpecPayload.run F MC (args k ps x h P, fuel))).toPoly d).IsHomogeneous 4
  simp only [psi, SoS.Poly.toPoly_append, NestedProgram.scale_toPoly,
    MomentProgram.power_toPoly, hround]
  exact (rounded_homogeneous _ _ hquartic).add (by
    simpa only [Nat.reduceMul] using (hn.pow 2).C_mul (-3))

/-- The concrete executable centered query has the required nested representation. -/
theorem prepared_rep {n k d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (Bd : Args → ℚ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    let a := (args k ps x h P, fuel)
    Rounding.RawRep (nestedInput (query F MC Bd a))
      (SpecSolver.zeroObjective (NC.build (query F MC Bd a))) := by
  let a := (args k ps x h P, fuel)
  exact SpecSolver.build_rep NC hNC d (payload F MC a)
    (epsilonQ a) (epsilonH a) (tolerance a) (Bd a) (payload_raw F MC a)
    (prepared_homogeneous F hF MC hMC ps x fuel h P M ε w η Δ D ω r I hI
      hx hp hf hh hl hP hnf)


end

end ABBKS26.Assembly.Exec.RefineSynth.SpecInput
