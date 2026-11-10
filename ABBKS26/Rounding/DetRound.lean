module

public import ABBKS26.Rounding.Nested
public import ABBKS26.Rounding.DetRoundAux
public import Background.SumOfSquares.Algorithm.Correct

/-!
# Deterministic subspace rounding

[ABBKS26, Theorem 4.1, Algorithm 1], with a deterministic step: from a solved sum-of-squares
program, repeatedly add a direction with large pseudo-variance outside the current span;
a packing bound caps the number of rounds, and the final span approximately contains every
solution.
-/

@[expose] public section

namespace ABBKS26.Rounding

noncomputable section


open Matrix

open Common Matrix MvPolynomial
open scoped BigOperators
variable {d : ℕ}

-- Integer upper rounding avoids a real square-root oracle in parameter computation.
def packCount (γ : ℚ) (r : ℕ) : ℕ :=
  (2 * ⌈40 * sqrtUp r / γ⌉₊) ^ r

def greedyThreshold (γ : ℚ) (r : ℕ) : ℚ :=
  1 / (2 : ℚ) ^ Nat.clog 2 ⌈1280000 * (r + 1 : ℚ) / γ ^ 4⌉₊

def greedyCap (γ : ℚ) (r : ℕ) : ℕ := ⌈32 / greedyThreshold γ r⌉₊ + 1

def rankCap (γ : ℚ) (r : ℕ) : ℕ := (packCount γ r + 1) * greedyCap γ r

/-- The absolute exponent furnished by the existing solver implementation. -/
def solverConstant : ℕ := Classical.choose SoS.Solver.exists_solver

structure RoundInput where
  problem : SoS.Solver.Problem
  ambient : ℕ
  radius : ℚ
  rankBound : ℕ
  normBound : ℚ

structure RoundOutput (d : ℕ) where
  basis : List (Fin d → ℚ)

def RoundOutput.proj (Y : RoundOutput d) : Mat d := projector Y.basis

def RoundInput.Target (I : RoundInput) (v : Vec I.ambient) : Prop :=
  sqnorm v = 1 ∧ ∃ y : Fin I.problem.numVars → ℝ,
    (∀ i : Fin I.ambient, ∀ h : i.val < I.problem.numVars, y ⟨i.val, h⟩ = v i) ∧
    ∀ f ∈ I.problem.system, 0 ≤ eval y (SoS.toReal f)

def RoundInput.Concentrated (I : RoundInput) : Prop :=
  I.ambient ≤ I.problem.numVars ∧ I.problem.Valid ∧ 0 < I.radius ∧ I.radius ≤ 1 / 2 ∧
    1 ≤ I.rankBound ∧ 1 ≤ I.normBound ∧
    ∃ (R : Mat I.ambient) (ε : ℝ), Projection R ∧ R.rank ≤ I.rankBound ∧
      0 ≤ ε ∧ ε ≤ (I.radius : ℝ) ^ 4 / 160000 ∧
      ∃ emb : Fin I.ambient ↪ Fin I.problem.numVars,
        (∀ i, (emb i).val = i.val) ∧
        rename emb (nsq - 1) ∈ I.problem.system.map SoS.toReal ∧
        rename emb (1 - nsq) ∈ I.problem.system.map SoS.toReal ∧
        SoS.DerivesN (I.problem.system.map SoS.toReal) I.problem.degree I.normBound
          (rename emb (quad R) - C (1 - ε))

def RoundOutput.WellConditioned (Y : RoundOutput d) (p : ℕ) : Prop :=
  ∀ j : Fin Y.basis.length,
    let v : Vec d := fun i ↦ (Y.basis[j] i : ℝ)
    let z := (1 - projector (Y.basis.take j)) *ᵥ v
    9 / 64 ≤ sqnorm z ∧ sqnorm z ≤ 81 / 64 ∧
      ∀ i, -1 ≤ Y.basis[j] i ∧ Y.basis[j] i ≤ 1 ∧
        ∃ a : ℤ, Y.basis[j] i = a / (2 : ℚ) ^ p

/-- The full deterministic-rounding contract at one input and output. -/
def RoundResultSpec (I : RoundInput) (Y : RoundOutput I.ambient) : Prop :=
  Y.basis.length ≤ rankCap I.radius I.rankBound ∧
    Projection Y.proj ∧ Y.proj.rank = Y.basis.length ∧
    (∃ p, Y.WellConditioned p) ∧
    (I.Concentrated → Covers Y.proj {v | I.Target v} I.radius)

def RoundSpec (run : (I : RoundInput) → RoundOutput I.ambient) : Prop :=
  ∀ I, RoundResultSpec I (run I)

/-- Raw exponents for the objective and for reading quadratic pseudo-moments. -/
def pairExponent (n a b : ℕ) : List ℕ :=
  (List.range n).map fun j ↦ (if j = a then 1 else 0) + (if j = b then 1 else 0)

def objectiveProblem (I : RoundInput)
    (Q : Matrix (Fin I.ambient) (Fin I.ambient) ℚ) : SoS.Solver.Problem :=
  (I.problem.numVars, I.problem.degree, I.problem.2.2.1,
    (((List.finRange I.ambient).flatMap fun a : Fin I.ambient ↦
      (List.finRange I.ambient).map fun b : Fin I.ambient ↦
        (pairExponent I.problem.numVars a.val b.val, Q a b)), []))

def readMoments (I : RoundInput) (out : SoS.Solver.Output) : Mat I.ambient :=
  fun a b ↦ (SoS.Poly.coeff I.problem.numVars out
    (pairExponent I.problem.numVars a b) : ℝ)

def solverAccuracy (I : RoundInput) (P : SoS.Solver.Problem) : ℚ :=
  1 / (2 : ℚ) ^ (2 * (SoS.Solver.encProblem P).length +
    Nat.clog 2 ⌈I.normBound⌉₊ + 4 * Nat.clog 2 ⌈1 / I.radius⌉₊ +
      Nat.clog 2 (I.ambient + 2) + 24)

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

private theorem moment_psd (I : RoundInput) (h : I.ambient ≤ I.problem.numVars)
    (out : SoS.Solver.Output)
    (E : SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree)
    (hdeg : 2 ≤ I.problem.degree) (hE : SoS.Solver.HasMoments E
      (out.toPoly I.problem.numVars)) : (readMoments I out).PosSemidef := by
  have hm := moment_pair I h out E hdeg hE
  have hsym : (readMoments I out).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext a b
    simp only [transpose_apply, hm, mul_comm]
  apply PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro v
  let f : MvPolynomial (Fin I.problem.numVars) ℝ :=
    ∑ a : Fin I.ambient, C (v a) * X ⟨a.val, a.isLt.trans_le h⟩
  have hf : f.totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro a _
    exact (totalDegree_mul _ _).trans (by simp)
  have hn := E.map_mul_self_nonneg ((Nat.mul_le_mul_left 2 hf).trans hdeg)
  have hexpand : f * f = ∑ a : Fin I.ambient, ∑ b : Fin I.ambient,
      C (v a) * X ⟨a.val, a.isLt.trans_le h⟩ *
        (C (v b) * X ⟨b.val, b.isLt.trans_le h⟩) := by
    dsimp only [f]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.mul_sum _ _ _
  have he : E (f * f) = v ⬝ᵥ (readMoments I out *ᵥ v) := by
    rw [hexpand]
    simp only [E.map_sum, mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hm]
    have hp : C (v a) * X (⟨a.val, a.isLt.trans_le h⟩ : Fin I.problem.numVars) *
        (C (v b) * X ⟨b.val, b.isLt.trans_le h⟩) =
        C (v a * v b) * (X ⟨a.val, a.isLt.trans_le h⟩ *
          X ⟨b.val, b.isLt.trans_le h⟩) := by rw [C_mul]; ring
    rw [hp, E.map_C_mul]
    ring
  simpa only [he, star_trivial] using hn

private theorem accuracy_scaled_bound (I : RoundInput) (P : SoS.Solver.Problem)
    (hγ : 0 < I.radius) (hγ1 : I.radius ≤ 1 / 2) :
    (solverAccuracy I P : ℝ) * 2 ^ (SoS.Solver.encProblem P).length ≤
      (I.radius : ℝ) ^ 2 / 1024 := by
  let L := (SoS.Solver.encProblem P).length
  let a := Nat.clog 2 ⌈1 / I.radius⌉₊
  let N := 2 * L + Nat.clog 2 ⌈I.normBound⌉₊ + 4 * a +
    Nat.clog 2 (I.ambient + 2) + 24
  have hg : (0 : ℝ) < I.radius := by exact_mod_cast hγ
  have hg1 : (I.radius : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * I.radius ≤ 1 := by
      exact_mod_cast (show 2 * I.radius ≤ 1 by linarith)
    linarith
  have ha : (1 / I.radius : ℚ) ≤ (2 : ℚ) ^ a :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by omega : 1 < 2) _)
  have ha' : 1 ≤ (I.radius : ℝ) * (2 : ℝ) ^ a := by
    have h := (div_le_iff₀ hγ).1 ha
    exact_mod_cast (by simpa [mul_comm] using h : (1 : ℚ) ≤ I.radius * 2 ^ a)
  have hf := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha' 4
  rw [one_pow, mul_pow] at hf
  have hd : (2 : ℝ) ^ L * ((2 : ℝ) ^ a) ^ 4 * 2 ^ 24 ≤ (2 : ℝ) ^ N := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [N]
    omega
  have he : (solverAccuracy I P : ℝ) * 2 ^ L * 2 ^ 24 ≤ (I.radius : ℝ) ^ 4 := by
    change ((1 / (2 : ℚ) ^ N : ℚ) : ℝ) * 2 ^ L * 2 ^ 24 ≤ _
    push_cast
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul,
      div_le_iff₀ (by positivity)]
    calc
      _ ≤ (I.radius : ℝ) ^ 4 * (2 ^ L * (2 ^ a) ^ 4 * 2 ^ 24) := by
        calc
          _ = 1 * (2 ^ L * (2 : ℝ) ^ 24) := by ring
          _ ≤ ((I.radius : ℝ) ^ 4 * (2 ^ a) ^ 4) * (2 ^ L * 2 ^ 24) :=
            mul_le_mul_of_nonneg_right hf (by positivity)
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  have hη : (0 : ℝ) < solverAccuracy I P := by unfold solverAccuracy; positivity
  have hγsq : (I.radius : ℝ) ^ 4 ≤ (I.radius : ℝ) ^ 2 := by
    have h : (I.radius : ℝ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (I.radius : ℝ)) (sub_nonneg.2 h)]
  change (solverAccuracy I P : ℝ) * 2 ^ L ≤ _
  norm_num at he
  nlinarith [mul_pos hη (by positivity : (0 : ℝ) < 2 ^ L)]

private theorem system_coeffNorm_bound (P : SoS.Solver.Problem)
    (f : MvPolynomial (Fin P.numVars) ℝ) (hf : f ∈ P.system.map SoS.toReal) :
    SoS.coeffNorm f ≤ 2 ^ (SoS.Solver.encProblem P).length := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
  exact (SoS.coeffNorm_le_coeffNorm1 _).trans
    (((SoS.Correct.coeffNorm1_toReal_le _ _).trans (SoS.Correct.rawNorm1_le _)).trans
      (pow_le_pow_right₀ (by norm_num) (SoS.Correct.length_encRaw_le_of_mem hp)))

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


/-- Reading a correct objective solve gives PSD moments and the stop/continue alternatives. -/
theorem solver_reading
    (I : RoundInput) (hI : I.Concentrated) (Q : Mat I.ambient)
    (Qrat : Matrix (Fin I.ambient) (Fin I.ambient) ℚ)
    (hQ : Projection Q)
    (hq : frobSq (Qrat.map (algebraMap ℚ ℝ) - Q) ≤ (I.radius : ℝ) ^ 4 / 65536)
    (out : SoS.Solver.Output)
    (hc : SoS.Solver.Correct (objectiveProblem I Qrat)
      (solverAccuracy I (objectiveProblem I Qrat))
      (solverAccuracy I (objectiveProblem I Qrat)) out) :
    let M := readMoments I out
    M.PosSemidef ∧ |M.trace - 1| ≤ 1 / 4 ∧
      (1 - (I.radius : ℝ) ^ 2 / 4 ≤ (Qrat.map (algebraMap ℚ ℝ) * M).trace →
        ∀ v, I.Target v → 1 - (I.radius : ℝ) ^ 2 / 2 ≤ qform Q v) ∧
      ((Qrat.map (algebraMap ℚ ℝ) * M).trace < 1 - (I.radius : ℝ) ^ 2 / 4 →
        (I.radius : ℝ) ^ 2 / 8 ≤ ((1 - Q) * M).trace) := by
  have _hQ := hQ
  rcases hI with ⟨ha, hvalid, hγ, hγ1, _, _, R, ε, _, _, _, _,
    emb, hemb, hsp, hsm, _⟩
  rcases hc with ⟨E, hE, hA, hopt⟩
  change SoS.PseudoExpectation (Fin I.problem.numVars) I.problem.degree at E
  change SoS.Solver.HasMoments E (out.toPoly I.problem.numVars) at hE
  change E.ApproxSatisfies I.problem.system
    ((solverAccuracy I (objectiveProblem I Qrat) : ℝ) +
      solverAccuracy I (objectiveProblem I Qrat)) 0 at hA
  let P := objectiveProblem I Qrat
  let η : ℝ := solverAccuracy I P
  let M := readMoments I out
  let A := Qrat.map (algebraMap ℚ ℝ)
  have hη : 0 < η := by dsimp [η, solverAccuracy]; positivity
  have hγr : (0 : ℝ) < I.radius := by exact_mod_cast hγ
  have hγr1 : (I.radius : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * I.radius ≤ 1 := by
      exact_mod_cast (show 2 * I.radius ≤ 1 by linarith)
    linarith
  have hscale := accuracy_scaled_bound I P hγ hγ1
  have hpow : (1 : ℝ) ≤ 2 ^ (SoS.Solver.encProblem P).length :=
    one_le_pow₀ (by norm_num)
  have hηle : η ≤ (I.radius : ℝ) ^ 2 / 1024 :=
    (le_mul_of_one_le_right hη.le hpow).trans hscale
  have hM : M.PosSemidef := moment_psd I ha out E hvalid.2.1 hE
  have hAre : E.ApproxSatisfies (I.problem.system.map SoS.toReal) (η + η) 0 :=
    hA.map_toReal
  have hn : (rename emb (nsq : RPoly I.ambient)).totalDegree ≤ 2 := by
    simp only [nsq, map_sum, map_pow, rename_X]
    apply totalDegree_finsetSum_le
    intro i _
    simp
  have hdp : (rename emb (nsq - 1 : RPoly I.ambient)).totalDegree ≤ I.problem.degree := by
    rw [map_sub, map_one]
    exact ((totalDegree_sub _ _).trans (max_le hn (by simp))).trans hvalid.2.1
  have hdm : (rename emb (1 - nsq : RPoly I.ambient)).totalDegree ≤ I.problem.degree := by
    rw [map_sub, map_one]
    exact ((totalDegree_sub _ _).trans (max_le (by simp) hn)).trans hvalid.2.1
  have hp := hAre.neg_le_apply_of_mem hsp (by
    rw [max_eq_left (Nat.zero_le _)]
    exact hdp)
  have hm := hAre.neg_le_apply_of_mem hsm (by
    rw [max_eq_left (Nat.zero_le _)]
    exact hdm)
  simp only [SoS.toReal_real, map_sub, map_one, E.map_sub, E.map_one,
    moment_nsq I ha out E hvalid.2.1 hE emb hemb] at hp hm
  have hnp := system_coeffNorm_bound P _ hsp
  have hnm := system_coeffNorm_bound P _ hsm
  have htr : |M.trace - 1| ≤ (I.radius : ℝ) ^ 2 / 512 := by
    have hep : 2 * η * SoS.coeffNorm (rename emb (nsq - 1 : RPoly I.ambient)) ≤
        (I.radius : ℝ) ^ 2 / 512 :=
      (mul_le_mul_of_nonneg_left hnp (by positivity)).trans (by linarith)
    have hem : 2 * η * SoS.coeffNorm (rename emb (1 - nsq : RPoly I.ambient)) ≤
        (I.radius : ℝ) ^ 2 / 512 :=
      (mul_le_mul_of_nonneg_left hnm (by positivity)).trans (by linarith)
    simp only [map_sub, map_one] at hep hem
    apply abs_le.2
    constructor <;> dsimp only [η, P, M] at * <;> linarith
  have htr4 : |M.trace - 1| ≤ 1 / 4 := htr.trans (by nlinarith)
  have hobj : P.objective E = (A * M).trace := by
    change E (SoS.toReal (((objectiveProblem I Qrat).2.2.2.1).toPoly
      I.problem.numVars)) + 0 = _
    rw [add_zero]
    rw [objective_poly I ha Qrat emb hemb, moment_quad I ha out E hvalid.2.1 hE emb hemb]
  have hpert := DetRoundAux.abs_trace_mul_le (A - Q) M ((I.radius : ℝ) ^ 2 / 256)
    hM (by positivity) (by convert hq using 1; ring)
  rw [sub_mul, trace_sub] at hpert
  have hqpert : |(A * M).trace - (Q * M).trace| ≤
      5 * (I.radius : ℝ) ^ 2 / 1024 := by
    refine hpert.trans ?_
    have ht := (abs_le.1 htr4).2
    nlinarith
  refine ⟨hM, htr4, ?_, ?_⟩
  · intro hstop v hv
    obtain ⟨hvnorm, y, hy, hyA⟩ := hv
    have hcpt := hopt (SoS.Correct.ofPoint I.problem.degree y)
      (SoS.Correct.ofPoint_approxSatisfies hyA hη.le)
    have heval : P.objective (SoS.Correct.ofPoint I.problem.degree y) = qform A v := by
      change (SoS.Correct.ofPoint I.problem.degree y)
        (SoS.toReal (((objectiveProblem I Qrat).2.2.2.1).toPoly I.problem.numVars)) + 0 = _
      rw [add_zero]
      rw [objective_poly I ha Qrat emb hemb, SoS.Correct.ofPoint_apply]
      simp only [quad, eval_rename, map_sum, eval_mul, eval_C, eval_X, Function.comp_apply,
        qform, mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [show y (emb a) = v a from by
        have he : emb a = ⟨a.val, a.isLt.trans_le ha⟩ := Fin.ext (hemb a)
        rw [he]; exact hy a _, show y (emb b) = v b from by
        have he : emb b = ⟨b.val, b.isLt.trans_le ha⟩ := Fin.ext (hemb b)
        rw [he]; exact hy b _]
      ring
    change P.objective E ≤ P.objective (SoS.Correct.ofPoint I.problem.degree y) + η at hcpt
    rw [hobj, heval] at hcpt
    have hpv := DetRoundAux.abs_qform_le (A - Q) ((I.radius : ℝ) ^ 2 / 256)
      (by positivity) (by convert hq using 1; ring) v
    rw [hvnorm, mul_one] at hpv
    have he : qform (A - Q) v = qform A v - qform Q v := by
      simp only [qform, sub_mulVec, dotProduct_sub]
    rw [he] at hpv
    have ht := (abs_le.1 hpv).2
    change 1 - (I.radius : ℝ) ^ 2 / 2 ≤ qform Q v
    dsimp only [A, M, η, P] at *
    linarith
  · intro hcont
    rw [sub_mul, one_mul, trace_sub]
    have ht := (abs_le.1 htr).1
    have hq' := (abs_le.1 hqpert).1
    dsimp only [A, M] at *
    linarith

/-- A continuing round yields a new vector near the hidden low-rank range. -/
theorem round_progress
    (M R P Q : Mat d) (γ ε s θ : ℝ) (r : ℕ)
    (hM : M.PosSemidef) (hR : Projection R) (hP : Projection P)
    (hQ : Projection Q) (hr : R.rank ≤ r) (hr0 : 1 ≤ r)
    (hγ : 0 < γ) (hs : 0 ≤ s ∧ s ≤ 1 / 4)
    (he : 0 < ε ∧ ε ≤ γ ^ 2 / 32) (htr : M.trace ≤ 1 + s)
    (hc : ((1 - R) * M).trace ≤ ε)
    (hpq : ∀ v, InRange P v → InRange Q v)
    (hcont : γ ^ 2 / 8 ≤ ((1 - P) * M).trace)
    (hθ : θ ≤ (γ / 200) ^ 2 * (γ ^ 2 / (32 * r)))
    (hcap : LE ((1 - Q) * M * (1 - Q)) (θ • (1 : Mat d))) :
    ∃ z, InRange Q z ∧ sqnorm z ≤ 1 ∧
      γ / (8 * Real.sqrt (1 + s)) - γ / 200 ≤ Real.sqrt (sqnorm ((1 - P) *ᵥ z)) ∧
      Real.sqrt (sqnorm ((1 - R) *ᵥ z)) ≤ 8 * Real.sqrt ε / γ + γ / 200 := by
  exact DetRoundAux.round_progress M R P Q γ ε s θ r hM hR hP hQ hr hr0 hγ hs he
    htr hc hpq hcont hθ hcap

/-- Separated projected points admit the finite rank-dependent packing bound. -/
theorem packing
    (R : Mat d) (r n : ℕ) (z : Fin n → Vec d) (σ : ℝ)
    (hR : Projection R) (hr : R.rank ≤ r) (hr0 : 1 ≤ r) (hσ : 0 < σ)
    (hz : ∀ i, sqnorm (z i) ≤ 1)
    (hsep : ∀ i j, i ≠ j → σ ^ 2 ≤ sqnorm (R *ᵥ (z i - z j))) :
    n ≤ (2 * ⌈2 * Real.sqrt r / σ⌉₊) ^ r := by
  exact DetRoundAux.packing R r n z σ hR hr hr0 hσ hz hsep

/-- The decoded inner loop, including its persistent stop bit. -/
structure DRCaptureTrace (d : ℕ) where
  state : ℕ → Bool × RoundOutput d

/-- Local capture guarantees: each live step either certifies the residual spectral bound
or appends a direction with the prescribed trace gain. No terminal capture is assumed. -/
structure DRCaptureSpec (I : RoundInput) (M : Mat I.ambient)
    (B : RoundOutput I.ambient) (T : DRCaptureTrace I.ambient) : Prop where
  initial : T.state 0 = (false, B)
  projection : ∀ t, Projection (T.state t).2.proj
  halted : ∀ t, (T.state t).1 = true → T.state (t + 1) = T.state t
  step : ∀ t, t < greedyCap I.radius I.rankBound → (T.state t).1 = false →
    ((T.state (t + 1)).1 = true ∧ (T.state (t + 1)).2 = (T.state t).2 ∧
      LE ((1 - (T.state t).2.proj) * M * (1 - (T.state t).2.proj))
        ((greedyThreshold I.radius I.rankBound : ℝ) • (1 : Mat I.ambient))) ∨
    ((T.state (t + 1)).1 = false ∧
      ((T.state t).2.proj * M).trace + (greedyThreshold I.radius I.rankBound : ℝ) / 16 ≤
        ((T.state (t + 1)).2.proj * M).trace)

/-- The actual bounded outer trace and the inner capture traces it invokes. The output may
also implement an input guard; agreement with the trace is required on concentrated inputs. -/
structure DRTrace (I : RoundInput) where
  output : RoundOutput I.ambient
  outer : ℕ → Bool × RoundOutput I.ambient
  moments : ℕ → Mat I.ambient
  stop : ℕ → Prop
  capture : ℕ → DRCaptureTrace I.ambient

/-- Local geometry, solver-reading, concentration and bounded-loop laws for Algorithm 1.
The stop test supplies a quadratic estimate, never target coverage. The capture spec supplies
only one-step gain; both bounded-loop arguments are proved by the DR milestone. -/
structure DRTraceSpec (I : RoundInput) (T : DRTrace I) : Prop where
  output_length : T.output.basis.length ≤ rankCap I.radius I.rankBound
  output_projection : Projection T.output.proj
  output_rank : T.output.proj.rank = T.output.basis.length
  output_conditioned : ∃ p, T.output.WellConditioned p
  initial : T.outer 0 = (false, ⟨[]⟩)
  basis_prefix : ∀ i j, i ≤ j → (T.outer i).2.basis <+: (T.outer j).2.basis
  range_mono : ∀ i j, i ≤ j → ∀ v,
    InRange (T.outer i).2.proj v → InRange (T.outer j).2.proj v
  length : ∀ j, (T.outer j).2.basis.length ≤ j * greedyCap I.radius I.rankBound
  projection : ∀ j, Projection (T.outer j).2.proj
  agrees : I.Concentrated → T.output = (T.outer (packCount I.radius I.rankBound + 1)).2
  reading : I.Concentrated → ∀ j,
    (T.moments j).PosSemidef ∧ (T.moments j).trace ≤ 5 / 4 ∧
    (T.stop j → ∀ v, I.Target v →
      1 - (I.radius : ℝ) ^ 2 / 2 ≤ qform (T.outer j).2.proj v) ∧
    (¬T.stop j → (I.radius : ℝ) ^ 2 / 8 ≤
      ((1 - (T.outer j).2.proj) * T.moments j).trace)
  concentration : I.Concentrated → ∃ R : Mat I.ambient,
    Projection R ∧ R.rank ≤ I.rankBound ∧ ∀ j,
      ((1 - R) * T.moments j).trace ≤ (I.radius : ℝ) ^ 4 / 150000
  capture_spec : I.Concentrated → ∀ j,
    (T.outer j).2.basis.length + greedyCap I.radius I.rankBound ≤
      rankCap I.radius I.rankBound →
    (T.moments j).PosSemidef → (T.moments j).trace ≤ 5 / 4 →
    DRCaptureSpec I (T.moments j) (T.outer j).2 (T.capture j)
  capture_prefix : ∀ j, (T.outer j).2.basis <+:
    ((T.capture j).state (greedyCap I.radius I.rankBound)).2.basis
  capture_range : ∀ j v, InRange (T.outer j).2.proj v →
    InRange ((T.capture j).state (greedyCap I.radius I.rankBound)).2.proj v
  continuing : I.Concentrated → ∀ j, (T.outer j).1 = false → ¬T.stop j →
    ((T.capture j).state (greedyCap I.radius I.rankBound)).2.basis.length ≠
      (T.outer j).2.basis.length →
    T.outer (j + 1) = (false, ((T.capture j).state (greedyCap I.radius I.rankBound)).2)

/-- Decode the final output of a supplied Algorithm 1 trace. -/
def drLoop (trace : (I : RoundInput) → DRTrace I) (I : RoundInput) : RoundOutput I.ambient :=
  (trace I).output

namespace DRTrace

/-- The bounded inner induction derives spectral capture from the append gain. -/
theorem capture_bound (I : RoundInput) (M : Mat I.ambient) (B : RoundOutput I.ambient)
    (T : DRCaptureTrace I.ambient) (hT : DRCaptureSpec I M B T)
    (hM : M.PosSemidef) (ht : M.trace ≤ 5 / 4) :
    LE ((1 - (T.state (greedyCap I.radius I.rankBound)).2.proj) * M *
      (1 - (T.state (greedyCap I.radius I.rankBound)).2.proj))
      ((greedyThreshold I.radius I.rankBound : ℝ) • (1 : Mat I.ambient)) := by
  let cap := greedyCap I.radius I.rankBound
  let θ : ℝ := greedyThreshold I.radius I.rankBound
  let captured (Y : RoundOutput I.ambient) :=
    LE ((1 - Y.proj) * M * (1 - Y.proj)) (θ • (1 : Mat I.ambient))
  have hinv (j : ℕ) (hj : j ≤ cap) :
      ((T.state j).1 = true ∧ captured (T.state j).2) ∨
      ((T.state j).1 = false ∧ (B.proj * M).trace + j * (θ / 16) ≤
        ((T.state j).2.proj * M).trace) := by
    induction j with
    | zero => right; rw [hT.initial]; exact ⟨rfl, by simp⟩
    | succ j ih =>
      rcases ih (by omega) with ⟨hb, hc⟩ | ⟨hb, htr⟩
      · left
        rw [hT.halted j hb]
        exact ⟨hb, hc⟩
      · rcases hT.step j (by omega) hb with ⟨hb', he, hc⟩ | ⟨hb', hgain⟩
        · left
          exact ⟨hb', he.symm ▸ hc⟩
        · right
          refine ⟨hb', ?_⟩
          push_cast
          dsimp only [θ] at *
          linarith
  rcases hinv cap le_rfl with ⟨_, hc⟩ | ⟨_, htr⟩
  · exact hc
  · exfalso
    have hP : Projection B.proj := by
      have h := hT.projection 0
      simpa only [hT.initial] using h
    have hnonneg := DetRoundAux.trace_projection_nonneg M B.proj hM hP
    have hle := (DetRoundAux.trace_projection_le M _ hM (hT.projection cap)).trans ht
    have hθ : 0 < θ := by unfold θ greedyThreshold; positivity
    have hceil := Nat.le_ceil (32 / greedyThreshold I.radius I.rankBound)
    have hceil' : 32 / θ ≤ (cap : ℝ) := by
      dsimp only [cap, greedyCap]
      push_cast
      have h := Rat.cast_le (K := ℝ) |>.2 hceil
      push_cast at h
      linarith
    have hh := (div_le_iff₀ hθ).1 hceil'
    nlinarith

theorem sqnorm_add_le {d : ℕ} (v w : Vec d) :
    Real.sqrt (sqnorm (v + w)) ≤ Real.sqrt (sqnorm v) + Real.sqrt (sqnorm w) := by
  have he (x : Vec d) : Real.sqrt (sqnorm x) =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    rw [← DetRoundAux.euclidean_sqnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [he, he, he]
  exact norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

theorem norm_sub_le {d : ℕ} (v w : Vec d) :
    Real.sqrt (sqnorm v) ≤ Real.sqrt (sqnorm w) + Real.sqrt (sqnorm (v - w)) := by
  simpa only [add_sub_cancel] using sqnorm_add_le w (v - w)

theorem sqnorm_sub_comm {d : ℕ} (v w : Vec d) : sqnorm (v - w) = sqnorm (w - v) := by
  simp only [sqnorm, sub_dotProduct, dotProduct_sub]
  ring

theorem progress_constants (γ : ℝ) (hγ : 0 < γ) :
    21 * γ / 200 ≤ γ / (8 * Real.sqrt (1 + (1 / 4 : ℝ))) - γ / 200 ∧
      8 * Real.sqrt (γ ^ 4 / 150000) / γ + γ / 200 ≤ 13 * γ / 500 := by
  have hs0 : 0 < Real.sqrt (1 + (1 / 4 : ℝ)) := by positivity
  have hs1 : Real.sqrt (1 + (1 / 4 : ℝ)) ≤ 9 / 8 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  constructor
  · have he : γ / 9 ≤ γ / (8 * Real.sqrt (1 + (1 / 4 : ℝ))) := by
      apply div_le_div_of_nonneg_left hγ.le (by positivity)
      linarith
    linarith
  · have hs : Real.sqrt (γ ^ 4 / 150000) ≤ γ ^ 2 / 384 := by
      apply (Real.sqrt_le_left (by positivity)).2
      nlinarith [sq_nonneg (γ ^ 2)]
    have hh := (div_le_div_iff_of_pos_right hγ).2 (mul_le_mul_of_nonneg_left hs
      (by norm_num : (0 : ℝ) ≤ 8))
    have he : 8 * (γ ^ 2 / 384) / γ = γ / 48 := by field_simp; ring
    rw [he] at hh
    linarith

theorem threshold_bound (γ : ℚ) (r : ℕ) (hγ : 0 < γ) (hr : 1 ≤ r) :
    (greedyThreshold γ r : ℝ) ≤ ((γ : ℝ) / 200) ^ 2 *
      ((γ : ℝ) ^ 2 / (32 * r)) := by
  have hpow : 1280000 * (r + 1 : ℚ) / γ ^ 4 ≤
      (2 : ℚ) ^ Nat.clog 2 ⌈1280000 * (r + 1 : ℚ) / γ ^ 4⌉₊ :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _)
  have hg : 0 < γ ^ 4 := by positivity
  have hmul := (div_le_iff₀ hg).1 hpow
  have ht : greedyThreshold γ r * (1280000 * (r : ℚ)) ≤ γ ^ 4 := by
    unfold greedyThreshold
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ht' := Rat.cast_le (K := ℝ) |>.2 ht
  push_cast at ht'
  rw [div_pow, mul_div, le_div_iff₀ (by positivity)]
  norm_num
  nlinarith

theorem continuing_witness {d : ℕ} (M R P Q : Mat d) (γ : ℚ) (r : ℕ)
    (hM : M.PosSemidef) (hR : Projection R) (hP : Projection P) (hQ : Projection Q)
    (hr : R.rank ≤ r) (hr0 : 1 ≤ r) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (htr : M.trace ≤ 5 / 4) (hc : ((1 - R) * M).trace ≤ (γ : ℝ) ^ 4 / 150000)
    (hpq : ∀ v, InRange P v → InRange Q v)
    (hcont : (γ : ℝ) ^ 2 / 8 ≤ ((1 - P) * M).trace)
    (hcap : Common.LE ((1 - Q) * M * (1 - Q))
      ((greedyThreshold γ r : ℝ) • (1 : Mat d))) :
    ∃ z, InRange Q z ∧ sqnorm z ≤ 1 ∧
      21 * (γ : ℝ) / 200 ≤ Real.sqrt (sqnorm ((1 - P) *ᵥ z)) ∧
      Real.sqrt (sqnorm ((1 - R) *ᵥ z)) ≤ 13 * (γ : ℝ) / 500 := by
  have hg : (0 : ℝ) < γ := Rat.cast_pos.2 hγ
  have hg1 : (γ : ℝ) ≤ 1 / 2 := by
    have h := Rat.cast_le (K := ℝ) |>.2 hγ1
    norm_num at h ⊢
    exact h
  have he : 0 < (γ : ℝ) ^ 4 / 150000 ∧
      (γ : ℝ) ^ 4 / 150000 ≤ (γ : ℝ) ^ 2 / 32 := by
    constructor
    · positivity
    · have hh : (γ : ℝ) ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (γ : ℝ)) (sub_nonneg.2 hh)]
  obtain ⟨z, hz, hznorm, hzfar, hznear⟩ := round_progress M R P Q γ
    ((γ : ℝ) ^ 4 / 150000) (1 / 4) (greedyThreshold γ r) r hM hR hP hQ hr hr0
    hg (by norm_num) he (by linarith) hc hpq hcont (threshold_bound γ r hγ hr0) hcap
  have hconst := progress_constants γ hg
  exact ⟨z, hz, hznorm, hconst.1.trans hzfar, hznear.trans hconst.2⟩

theorem sqrtUp_bound (r : ℕ) : Real.sqrt r ≤ (sqrtUp (r : ℚ) : ℝ) := by
  have he : sqrtUp (r : ℚ) = (Nat.sqrt r + 1 : ℕ) := by
    simp [sqrtUp]
  rw [he]
  apply (Real.sqrt_le_left (by positivity)).2
  have h := Nat.lt_succ_sqrt r
  exact_mod_cast (by simpa only [pow_two, Nat.succ_eq_add_one] using h.le)

theorem separated {d : ℕ} (R P : Mat d) (_hR : Projection R) (hP : Projection P)
    (v w : Vec d) (γ : ℝ) (hγ : 0 < γ) (hw : InRange P w)
    (hfar : 21 * γ / 200 ≤ Real.sqrt (sqnorm ((1 - P) *ᵥ v)))
    (hv : Real.sqrt (sqnorm ((1 - R) *ᵥ v)) ≤ 13 * γ / 500)
    (hw' : Real.sqrt (sqnorm ((1 - R) *ᵥ w)) ≤ 13 * γ / 500) :
    (γ / 20) ^ 2 ≤ sqnorm (R *ᵥ (v - w)) := by
  have hres : (1 - P) *ᵥ (v - w) = (1 - P) *ᵥ v := by
    change P *ᵥ w = w at hw
    simp only [mulVec_sub, sub_mulVec, one_mulVec, hw]
    abel
  have hdist : 21 * γ / 200 ≤ Real.sqrt (sqnorm (v - w)) := by
    have hc := DetRoundAux.projection_contract (1 - P)
      (DetRoundAux.projection_compl P hP) (v - w)
    rw [hres] at hc
    exact hfar.trans (Real.sqrt_le_sqrt hc)
  have hnear : Real.sqrt (sqnorm ((1 - R) *ᵥ (v - w))) ≤ 26 * γ / 500 := by
    rw [mulVec_sub]
    have hh := norm_sub_le ((1 - R) *ᵥ v - (1 - R) *ᵥ w) ((1 - R) *ᵥ v)
    rw [show (1 - R) *ᵥ v - (1 - R) *ᵥ w - (1 - R) *ᵥ v =
      -((1 - R) *ᵥ w) by abel] at hh
    simp only [sqnorm, neg_dotProduct, dotProduct_neg, neg_neg] at hh
    change Real.sqrt (sqnorm ((1 - R) *ᵥ v - (1 - R) *ᵥ w)) ≤
      Real.sqrt (sqnorm ((1 - R) *ᵥ v)) + Real.sqrt (sqnorm ((1 - R) *ᵥ w)) at hh
    linarith
  have hdecomp : v - w = R *ᵥ (v - w) + (1 - R) *ᵥ (v - w) := by
    simp [sub_mulVec]
  have htri := sqnorm_add_le (R *ᵥ (v - w)) ((1 - R) *ᵥ (v - w))
  rw [← hdecomp] at htri
  have hl : γ / 20 ≤ Real.sqrt (sqnorm (R *ᵥ (v - w))) := by linarith
  have hs := Real.sq_sqrt (DetRoundAux.sqnorm_nonneg (R *ᵥ (v - w)))
  nlinarith [Real.sqrt_nonneg (sqnorm (R *ᵥ (v - w)))]

theorem packing_bound {d : ℕ} (R : Mat d) (r n : ℕ) (z : Fin n → Vec d)
    (γ : ℚ) (hR : Projection R) (hr : R.rank ≤ r) (hr0 : 1 ≤ r) (hγ : 0 < γ)
    (hz : ∀ i, sqnorm (z i) ≤ 1)
    (hsep : ∀ i j, i ≠ j → ((γ : ℝ) / 20) ^ 2 ≤ sqnorm (R *ᵥ (z i - z j))) :
    n ≤ packCount γ r := by
  have hγ' : (0 : ℝ) < γ := Rat.cast_pos.2 hγ
  have hp := packing R r n z ((γ : ℝ) / 20) hR hr hr0 (by positivity) hz hsep
  apply hp.trans
  unfold packCount
  gcongr
  apply Nat.ceil_le.2
  have hs := sqrtUp_bound r
  have he : 2 * Real.sqrt r / ((γ : ℝ) / 20) = 40 * Real.sqrt r / γ := by ring
  rw [he]
  have hc : ((40 * sqrtUp (r : ℚ) / γ : ℚ) : ℝ) =
      40 * (sqrtUp (r : ℚ) : ℝ) / γ := by push_cast; rfl
  have hh := Rat.cast_le (K := ℝ) |>.2 (Nat.le_ceil (40 * sqrtUp (r : ℚ) / γ))
  rw [hc, Rat.cast_natCast] at hh
  refine le_trans ?_ hh
  gcongr
end DRTrace

/-- Algorithm 1: local solver estimates, bounded greedy capture and packing force coverage
of the actual decoded trace, with the original unconditional rank and conditioning clauses. -/
theorem detRound_spec (trace : (I : RoundInput) → DRTrace I)
    (htrace : ∀ I, DRTraceSpec I (trace I)) : RoundSpec (drLoop trace) := by
  classical
  intro I
  let T := trace I
  have hT : DRTraceSpec I T := htrace I
  refine ⟨hT.output_length, hT.output_projection, hT.output_rank,
    hT.output_conditioned, ?_⟩
  intro hI
  change Covers T.output.proj _ _
  rw [hT.agrees hI]
  let n := packCount I.radius I.rankBound + 1
  obtain ⟨R, hR, hr, hconc⟩ := hT.concentration hI
  have hg : (0 : ℝ) < I.radius := Rat.cast_pos.2 hI.2.2.1
  have hg1 : (I.radius : ℝ) ≤ 1 / 2 := by
    have h := Rat.cast_le (K := ℝ) |>.2 hI.2.2.2.1
    norm_num at h ⊢
    exact h
  by_contra hno
  have hnot (j : ℕ) (hj : j ≤ n) :
      ¬Covers (T.outer j).2.proj {v | I.Target v} I.radius := by
    intro hc
    apply hno
    intro v hv
    obtain ⟨u, hu, hur, hdist⟩ := hc v hv
    exact ⟨u, hu, hT.range_mono j n hj u hur, hdist⟩
  have hlength (j : ℕ) (hj : j < n) :
      (T.outer j).2.basis.length + greedyCap I.radius I.rankBound ≤
        rankCap I.radius I.rankBound := by
    have h := hT.length j
    have hj' : j + 1 ≤ n := by omega
    have hm := Nat.mul_le_mul_right (greedyCap I.radius I.rankBound) hj'
    unfold rankCap
    dsimp only [n] at hm
    rw [Nat.add_mul, one_mul] at hm
    omega
  have hprogress (j : ℕ) (hj : j < n) (hb : (T.outer j).1 = false) :
      (T.outer (j + 1)).1 = false ∧ ∃ z : Vec I.ambient,
        InRange (T.outer (j + 1)).2.proj z ∧ sqnorm z ≤ 1 ∧
          21 * (I.radius : ℝ) / 200 ≤
            Real.sqrt (sqnorm ((1 - (T.outer j).2.proj) *ᵥ z)) ∧
          Real.sqrt (sqnorm ((1 - R) *ᵥ z)) ≤ 13 * (I.radius : ℝ) / 500 := by
    obtain ⟨hPSD, htr, hstop, hcont⟩ := hT.reading hI j
    have hs : ¬T.stop j := by
      intro hs
      apply hnot j hj.le
      intro v hv
      exact DetRoundAux.unit_near_projection _ (hT.projection j) v I.radius hv.1
        ⟨hg, hg1⟩ (hstop hs v hv)
    have hc := hT.capture_spec hI j (hlength j hj) hPSD htr
    have hcap := DRTrace.capture_bound I (T.moments j) (T.outer j).2
      (T.capture j) hc hPSD htr
    let D := ((T.capture j).state (greedyCap I.radius I.rankBound)).2
    obtain ⟨z, hz, hznorm, hzfar, hznear⟩ := DRTrace.continuing_witness
      (T.moments j) R (T.outer j).2.proj D.proj I.radius I.rankBound hPSD hR
      (hT.projection j) (hc.projection _) hr hI.2.2.2.2.1 hI.2.2.1 hI.2.2.2.1
      htr (hconc j) (hT.capture_range j) (hcont hs) hcap
    have hne : D.basis.length ≠ (T.outer j).2.basis.length := by
      intro he
      have hBD : (T.outer j).2.basis = D.basis :=
        (hT.capture_prefix j).eq_of_length he.symm
      have hproj : (T.outer j).2.proj = D.proj := congrArg projector hBD
      rw [hproj, Matrix.sub_mulVec, Matrix.one_mulVec, hz, sub_self] at hzfar
      norm_num [sqnorm] at hzfar
      linarith
    rw [hT.continuing hI j hb hs hne]
    exact ⟨rfl, z, hz, hznorm, hzfar, hznear⟩
  have hbits (j : ℕ) (hj : j ≤ n) : (T.outer j).1 = false := by
    induction j with
    | zero => rw [hT.initial]
    | succ j ih => exact (hprogress j (by omega) (ih (by omega))).1
  choose z hz using fun j : Fin n ↦ (hprogress j j.isLt (hbits j j.isLt.le)).2
  have hsep_ordered (i j : Fin n) (hij : i < j) :
      ((I.radius : ℝ) / 20) ^ 2 ≤ sqnorm (R *ᵥ (z j - z i)) := by
    have hmem : InRange (T.outer j).2.proj (z i) :=
      hT.range_mono (i.val + 1) j.val (by omega) (z i) (hz i).1
    exact DRTrace.separated R (T.outer j).2.proj hR (hT.projection j) (z j) (z i)
      I.radius hg hmem (hz j).2.2.1 (hz j).2.2.2 (hz i).2.2.2
  have hsep (i j : Fin n) (hij : i ≠ j) :
      ((I.radius : ℝ) / 20) ^ 2 ≤ sqnorm (R *ᵥ (z i - z j)) := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hh := hsep_ordered i j h
      have he : R *ᵥ (z i - z j) = -(R *ᵥ (z j - z i)) := by
        rw [← Matrix.mulVec_neg]
        congr 1
        abel
      simpa only [he, sqnorm, neg_dotProduct, dotProduct_neg, neg_neg] using hh
    · exact hsep_ordered j i h
  have hp := DRTrace.packing_bound R I.rankBound n z I.radius hR hr hI.2.2.2.2.1
    hI.2.2.1 (fun j ↦ (hz j).2.1) hsep
  dsimp only [n] at hp
  omega


end

end ABBKS26.Rounding
