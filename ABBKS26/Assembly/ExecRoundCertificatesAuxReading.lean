module

public import ABBKS26.Assembly.ExecRoundCertificatesAuxGeometry

/-! Solver interpretation and concentration for the concrete rounder. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundCertificates.Reading

open Common Rounding Matrix MvPolynomial
open scoped BigOperators

noncomputable section

private theorem pairExponent_finsupp (n : ℕ) (a b : Fin n) :
    SoS.Mono.toFinsupp n (pairExponent n a b) =
      Finsupp.single a 1 + Finsupp.single b 1 := by
  ext j
  simp [SoS.Mono.toFinsupp_apply, pairExponent, List.getD_eq_getElem?_getD,
    j.isLt, Finsupp.single_apply, Fin.ext_iff, eq_comm]

private theorem moment_pair (I : RoundInput) (h : I.ambient ≤ I.problem.numVars)
    (out : SoS.Solver.Output)
    (E : SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree)
    (hdeg : 2 ≤ I.problem.degree) (hE : SoS.Solver.HasMoments E
      (out.toPoly I.problem.numVars)) (a b : Fin I.ambient) :
    readMoments I out a b = E (X ⟨a.val, a.isLt.trans_le h⟩ *
      X ⟨b.val, b.isLt.trans_le h⟩) := by
  let a' : Fin I.problem.numVars := ⟨a.val, a.isLt.trans_le h⟩
  let b' : Fin I.problem.numVars := ⟨b.val, b.isLt.trans_le h⟩
  have hlen : (pairExponent I.problem.numVars a b).length = I.problem.numVars := by
    simp [pairExponent]
  have hm := hE (Finsupp.single a' 1 + Finsupp.single b' 1) (by
    simpa using hdeg)
  have hx : (monomial (Finsupp.single a' 1 + Finsupp.single b' 1)) (1 : ℝ) =
      X a' * X b' := by rw [X, X, monomial_mul_monomial, one_mul]
  rw [hx] at hm
  rw [← pairExponent_finsupp I.problem.numVars a' b', SoS.Poly.coeff_toPoly out hlen]
    at hm
  exact hm.symm

private theorem moment_quad (I : RoundInput) (h : I.ambient ≤ I.problem.numVars)
    (out : SoS.Solver.Output)
    (E : SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree)
    (hdeg : 2 ≤ I.problem.degree) (hE : SoS.Solver.HasMoments E
      (out.toPoly I.problem.numVars)) (emb : Fin I.ambient ↪ Fin I.problem.numVars)
    (hemb : ∀ i, (emb i).val = i.val) (A : Mat I.ambient) :
    E (rename emb (quad A)) = (A * readMoments I out).trace := by
  have hi : ∀ i, emb i = ⟨i.val, i.isLt.trans_le h⟩ :=
    fun i ↦ Fin.ext (hemb i)
  simp only [quad, map_sum, map_mul, rename_C, rename_X, E.map_sum,
    trace, diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [moment_pair I h out E hdeg hE b a, hi, hi, mul_comm (X _ :
    MvPolynomial (Fin I.problem.numVars) ℝ)]
  rw [mul_assoc, E.map_C_mul]

private theorem moment_nsq (I : RoundInput) (h : I.ambient ≤ I.problem.numVars)
    (out : SoS.Solver.Output)
    (E : SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree)
    (hdeg : 2 ≤ I.problem.degree) (hE : SoS.Solver.HasMoments E
      (out.toPoly I.problem.numVars)) (emb : Fin I.ambient ↪ Fin I.problem.numVars)
    (hemb : ∀ i, (emb i).val = i.val) :
    E (rename emb nsq) = (readMoments I out).trace := by
  simp only [nsq, map_sum, map_pow, rename_X, E.map_sum, trace, diag]
  apply Finset.sum_congr rfl
  intro a _
  rw [moment_pair I h out E hdeg hE a a, pow_two,
    show emb a = ⟨a.val, a.isLt.trans_le h⟩ from Fin.ext (hemb a)]

private theorem list_map_flatMap_sum {α β M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a ↦ ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem objective_poly (I : RoundInput) (_h : I.ambient ≤ I.problem.numVars)
    (Q : Matrix (Fin I.ambient) (Fin I.ambient) ℚ)
    (emb : Fin I.ambient ↪ Fin I.problem.numVars) (hemb : ∀ i, (emb i).val = i.val) :
    SoS.toReal (((objectiveProblem I Q).2.2.2.1).toPoly I.problem.numVars) =
      rename emb (quad (Q.map (algebraMap ℚ ℝ))) := by
  have ht (a b : Fin I.ambient) :
      (SoS.Mono.toFinsupp I.problem.numVars
        (SoS.Poly.expo I.problem.numVars (pairExponent I.problem.numVars a b))) =
        Finsupp.single (emb a) 1 + Finsupp.single (emb b) 1 := by
    ext i
    rw [SoS.Mono.toFinsupp_apply, SoS.Poly.getD_expo _ i.isLt]
    simp [
      pairExponent, List.getD_eq_getElem?_getD, i.isLt, Finsupp.single_apply,
      Fin.ext_iff, hemb, eq_comm]
  change SoS.toReal (SoS.Solver.RawPoly.toPoly I.problem.numVars
    ((List.finRange I.ambient).flatMap fun a : Fin I.ambient ↦
    (List.finRange I.ambient).map fun b : Fin I.ambient ↦
      (pairExponent I.problem.numVars a b, Q a b))) = _
  rw [SoS.Poly.toPoly_eq_sum]
  rw [list_map_flatMap_sum]
  simp only [List.map_map]
  rw [← Fin.sum_univ_def, SoS.toReal, map_sum]
  simp only [Function.comp_apply, ← Fin.sum_univ_def, map_sum, map_monomial,
    ht, quad, map_mul, rename_C, rename_X, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (monomial (Finsupp.single (emb a) 1 + Finsupp.single (emb b) 1))
    ((algebraMap ℚ ℝ) (Q a b)) =
    monomial 0 ((algebraMap ℚ ℝ) (Q a b)) * monomial (Finsupp.single (emb a) 1) 1 *
      monomial (Finsupp.single (emb b) 1) 1
  simp only [monomial_mul_monomial, zero_add, mul_one]

theorem objective_valid (I : RoundInput) (hI : I.Concentrated)
    (Q : Matrix (Fin I.ambient) (Fin I.ambient) ℚ) : (objectiveProblem I Q).Valid := by
  obtain ⟨ha, hvalid, _, _, _, _, R, ε, _, _, _, _, emb, hemb, _⟩ := hI
  refine ⟨hvalid.1, hvalid.2.1, ?_, hvalid.2.2.2.1, hvalid.2.2.2.2⟩
  intro q hq
  have hq' : q = (objectiveProblem I Q).2.2.2.1 := by simpa [objectiveProblem] using hq
  subst q
  change (((objectiveProblem I Q).2.2.2.1).toPoly I.problem.numVars).totalDegree ≤ _
  rw [← SoS.totalDegree_toReal_rat, objective_poly I ha Q emb hemb]
  apply (totalDegree_rename_le _ _).trans
  apply le_trans _ hvalid.2.1
  unfold quad
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by
    have h := totalDegree_mul (C ((Q.map (algebraMap ℚ ℝ)) i j)) (X i)
    simpa using Nat.add_le_add_right h 1)

theorem product_bound (P : SoS.Solver.Problem) :
    ∏ i : Fin (P.system.map SoS.toReal).length,
      (1 + SoS.coeffNorm ((P.system.map SoS.toReal).get i)) ≤
        (2 : ℝ) ^ (2 * (SoS.Solver.encProblem P).length) := by
  let e : Fin (P.system.map SoS.toReal).length ≃ Fin P.system.length :=
    finCongr (by simp)
  have he : ∏ i : Fin (P.system.map SoS.toReal).length,
      (1 + SoS.coeffNorm ((P.system.map SoS.toReal).get i)) =
        ∏ i : Fin P.system.length, (1 + SoS.coeffNorm (SoS.toReal (P.system.get i))) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  rw [he]
  let len (i : Fin P.system.length) := (SoS.Poly.encRaw (P.2.2.1.getD i [])).length
  have hb (i : Fin P.system.length) :
      SoS.coeffNorm (SoS.toReal (P.system.get i)) ≤ (2 : ℝ) ^ len i := by
    exact (SoS.coeffNorm_le_coeffNorm1 _).trans (SoS.Correct.coeffNorm1_get_le P i)
  calc
    _ ≤ ∏ i : Fin P.system.length, (2 : ℝ) ^ (len i + 1) := by
      apply Finset.prod_le_prod₀ (fun i _ ↦ add_nonneg zero_le_one (SoS.coeffNorm_nonneg _))
      intro i _
      rw [pow_succ]
      have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := len i)
      linarith [hb i]
    _ = (2 : ℝ) ^ (∑ i, (len i + 1)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := by
      apply pow_le_pow_right₀ (by norm_num)
      have hsum := SoS.Correct.sum_length_le P Finset.univ
      have hlen : P.system.length ≤ (SoS.Solver.encProblem P).length := by
        simpa only [SoS.Solver.Problem.system, List.length_map] using
          SoS.Correct.length_cons_le P
      change (∑ i, len i) ≤ _ at hsum
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
      change (∑ i, len i) + P.system.length ≤ _
      omega

theorem accuracy_error (I : RoundInput) (P : SoS.Solver.Problem)
    (hγ : 0 < I.radius) (_hN : 1 ≤ I.normBound) :
    (solverAccuracy I P : ℝ) * I.normBound *
      2 ^ (2 * (SoS.Solver.encProblem P).length) ≤ (I.radius : ℝ) ^ 4 / 2 ^ 24 := by
  let L := (SoS.Solver.encProblem P).length
  let b := Nat.clog 2 ⌈I.normBound⌉₊
  let c := Nat.clog 2 ⌈1 / I.radius⌉₊
  have hb : (I.normBound : ℝ) ≤ (2 : ℝ) ^ b := by
    have h : I.normBound ≤ (2 : ℚ) ^ b :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _)
    exact_mod_cast h
  have hc : (1 : ℝ) ≤ I.radius * (2 : ℝ) ^ c := by
    have h : 1 / I.radius ≤ (2 : ℚ) ^ c :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _)
    have h' := (div_le_iff₀ hγ).1 h
    have h'' := Rat.cast_le (K := ℝ) |>.2 h'
    push_cast at h''
    linarith
  have hγr : (0 : ℝ) < I.radius := Rat.cast_pos.2 hγ
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hc 4
  rw [one_pow, mul_pow] at hpow
  let k := 2 * L + b + 4 * c + Nat.clog 2 (I.ambient + 2) + 24
  have hk : (2 : ℝ) ^ (2 * L) * 2 ^ b * (2 ^ c) ^ 4 * 2 ^ 24 ≤ 2 ^ k := by
    rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp only [k]; omega)
  change ((1 / (2 : ℚ) ^ k : ℚ) : ℝ) * I.normBound * 2 ^ (2 * L) ≤ _
  push_cast
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (2 : ℝ) ^ b * 2 ^ (2 * L) * 2 ^ 24 := by gcongr
    _ ≤ (I.radius : ℝ) ^ 4 *
        (2 ^ (2 * L) * 2 ^ b * (2 ^ c) ^ 4 * 2 ^ 24) := by
      nlinarith [mul_le_mul_of_nonneg_right hpow
        (by positivity : 0 ≤ (2 : ℝ) ^ b * 2 ^ (2 * L) * 2 ^ 24)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)

theorem concentration (I : RoundInput) (hI : I.Concentrated)
    (R : Mat I.ambient) (ε : ℝ) (emb : Fin I.ambient ↪ Fin I.problem.numVars)
    (hemb : ∀ i, (emb i).val = i.val)
    (hε : ε ≤ (I.radius : ℝ) ^ 4 / 160000)
    (_hsp : rename emb (nsq - 1) ∈ I.problem.system.map SoS.toReal)
    (hsm : rename emb (1 - nsq) ∈ I.problem.system.map SoS.toReal)
    (hDer : SoS.DerivesN (I.problem.system.map SoS.toReal) I.problem.degree I.normBound
      (rename emb (quad R) - C (1 - ε)))
    (Q : Matrix (Fin I.ambient) (Fin I.ambient) ℚ) (out : SoS.Solver.Output)
    (hc : SoS.Solver.Correct (objectiveProblem I Q)
      (solverAccuracy I (objectiveProblem I Q))
      (solverAccuracy I (objectiveProblem I Q)) out) :
    ((1 - R) * readMoments I out).trace ≤ (I.radius : ℝ) ^ 4 / 150000 := by
  let P := objectiveProblem I Q
  let η : ℝ := solverAccuracy I P
  rcases hc with ⟨E, hE, hA, _⟩
  change SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree at E
  change SoS.Solver.HasMoments E (out.toPoly I.problem.numVars) at hE
  change E.ApproxSatisfies I.problem.system (η + η) 0 at hA
  have hη : 0 ≤ η := by dsimp only [η, solverAccuracy]; positivity
  have hreal := hA.map_toReal
  have hderive := hDer.approx_ge (add_nonneg hη hη) hreal le_rfl
  rw [E.map_sub, E.map_C, moment_quad I hI.1 out E hI.2.1.2.1 hE emb hemb] at hderive
  have hdeg : (rename emb (1 - nsq : RPoly I.ambient)).totalDegree ≤ I.problem.degree := by
    simp only [map_sub, map_one, nsq, map_sum, map_pow, rename_X]
    apply (totalDegree_sub _ _).trans
    apply max_le (by simp)
    apply le_trans _ hI.2.1.2.1
    apply totalDegree_finsetSum_le
    intro i _
    simp
  have ht := hreal.neg_le_apply_of_mem hsm (by simpa using hdeg)
  simp only [SoS.toReal_real, map_sub, map_one, E.map_sub, E.map_one,
    moment_nsq I hI.1 out E hI.2.1.2.1 hE emb hemb] at ht
  have hprod := product_bound P
  have hcoef : SoS.coeffNorm (rename emb (1 - nsq : RPoly I.ambient)) ≤
      2 ^ (2 * (SoS.Solver.encProblem P).length) := by
    obtain ⟨g, hg, hge⟩ := List.mem_map.1 hsm
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have h := (SoS.coeffNorm_le_coeffNorm1 (SoS.toReal (f.toPoly I.problem.numVars))).trans
      ((SoS.Correct.coeffNorm1_toReal_le I.problem.numVars f).trans
        (SoS.Correct.rawNorm1_le f))
    rw [← hge]
    apply h.trans
    apply pow_le_pow_right₀ (by norm_num)
    exact (SoS.Correct.length_encRaw_le_of_mem (P := P) hf).trans (by omega)
  have hbound := accuracy_error I P hI.2.2.1 hI.2.2.2.2.2.1
  have hN : (1 : ℝ) ≤ I.normBound := by exact_mod_cast hI.2.2.2.2.2.1
  have hderr := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (add_nonneg hη hη) (zero_le_one.trans hN))
  have hterr := mul_le_mul_of_nonneg_left hcoef (add_nonneg hη hη)
  change (η + η) * I.normBound *
      (∏ i : Fin (I.problem.system.map SoS.toReal).length,
        (1 + SoS.coeffNorm ((I.problem.system.map SoS.toReal).get i))) ≤ _ at hderr
  simp only [map_sub, map_one] at hterr
  have hscale : η * 2 ^ (2 * (SoS.Solver.encProblem P).length) ≤
      η * I.normBound * 2 ^ (2 * (SoS.Solver.encProblem P).length) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hη hN) (by positivity)
  rw [sub_mul, one_mul, trace_sub]
  change η * I.normBound * 2 ^ (2 * (SoS.Solver.encProblem P).length) ≤ _ at hbound
  norm_num only [show (2 : ℝ) ^ 24 = 16777216 by norm_num] at hbound
  have hr' : 1 - ε - (I.radius : ℝ) ^ 4 / 8388608 ≤
      (R * readMoments I out).trace := by nlinarith only [hderive, hderr, hbound]
  have ht' : (readMoments I out).trace ≤ 1 + (I.radius : ℝ) ^ 4 / 8388608 := by
    nlinarith only [ht, hterr, hscale, hbound]
  have hγ4 : 0 ≤ (I.radius : ℝ) ^ 4 := by positivity
  linarith

theorem rounded_projection_error (a : RoundArgs) (hγ : 0 < a.2.2.1) (B : Points)
    (hB : RoundProgram.GoodBasis a B) :
    frobSq ((matrixOf a.2.1 (RoundProgram.roundedProjection a B)).map
      (algebraMap ℚ ℝ) - (RoundProgram.output a B).proj) ≤
        (a.2.2.1 : ℝ) ^ 4 / 65536 := by
  let P := (RoundProgram.output a B).proj
  let p := RoundProgram.objectivePrecision a
  have hP : Projection P := (Geometry.basis_geometry a B hB).1
  have hentry (i j : Fin a.2.1) : |P i j| ≤ 1 := by
    let e : Vec a.2.1 := Pi.single j 1
    have he : sqnorm e = 1 := by simp [e, sqnorm]
    have hcol : (P *ᵥ e) i = P i j := by simp [e, mulVec_single]
    have hc := DetRoundAux.projection_contract P hP e
    have hi : (P *ᵥ e) i ^ 2 ≤ sqnorm (P *ᵥ e) := by
      simpa only [sqnorm, dotProduct, ← pow_two] using
        Finset.single_le_sum (fun k _ ↦ sq_nonneg ((P *ᵥ e) k)) (Finset.mem_univ i)
    rw [hcol] at hi
    rw [he] at hc
    nlinarith [sq_abs (P i j), abs_nonneg (P i j)]
  have hproj (i j : Fin a.2.1) :
      (FrameAux.Linear.ent (RoundProgram.projection a.2.1 B) i j : ℝ) =
        P i j := congrArg (fun A ↦ A i j) (Geometry.projection_eq a B)
  have hr (i j : Fin a.2.1) :
      |((matrixOf a.2.1 (RoundProgram.roundedProjection a B)).map
        (algebraMap ℚ ℝ) - P) i j| ≤ 1 / (2 : ℝ) ^ p := by
    have he : FrameAux.Linear.ent (RoundProgram.roundedProjection a B) i j =
        roundRat p (FrameAux.Linear.ent (RoundProgram.projection a.2.1 B) i j) := by
      unfold RoundProgram.roundedProjection FrameAux.Linear.ent
      rw [SoS.PDTestRat.getD_map_of_eq
        (fun row : List ℚ ↦ row.map (roundRat (RoundProgram.objectivePrecision a)))
        (RoundProgram.projection a.2.1 B) i.val (d := []) (d' := []) rfl]
      exact SoS.PDTestRat.getD_map_of_eq _ _ _ (d' := 0) (by simp [roundRat])
    have habs : |FrameAux.Linear.ent (RoundProgram.projection a.2.1 B) i j| ≤
        (2 : ℚ) ^ 0 := by
      apply Rat.cast_le (K := ℝ) |>.1
      simpa only [Rat.cast_abs, pow_zero, Rat.cast_one, hproj] using hentry i j
    have herr := (NestedProgram.rounded_coefficient p 0 _ habs).1
    change |((FrameAux.Linear.ent (RoundProgram.roundedProjection a B) i j : ℚ) : ℝ) -
      P i j| ≤ _
    rw [he, ← hproj]
    exact herr
  have hpow : 1024 * (a.2.1 + 1 : ℚ) / a.2.2.1 ^ 2 ≤ (2 : ℚ) ^ p :=
    (Nat.le_ceil _).trans (by
      dsimp only [p, RoundProgram.objectivePrecision]
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _)
  have hg : (0 : ℝ) < a.2.2.1 := Rat.cast_pos.2 hγ
  have hpow' : 1024 * (a.2.1 + 1 : ℝ) ≤ (2 : ℝ) ^ p * a.2.2.1 ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hγ)).1 hpow
    exact_mod_cast h
  have hδ : (a.2.1 : ℝ) / (2 : ℝ) ^ p ≤ (a.2.2.1 : ℝ) ^ 2 / 256 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc
    _ ≤ ∑ _i : Fin a.2.1, ∑ _j : Fin a.2.1, (1 / (2 : ℝ) ^ p) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hr i j) 2
    _ = ((a.2.1 : ℝ) / (2 : ℝ) ^ p) ^ 2 := by simp; ring
    _ ≤ _ := by
      have h := pow_le_pow_left₀ (by positivity) hδ 2
      convert h using 1
      ring


end

end ABBKS26.Assembly.Exec.RoundCertificates.Reading
