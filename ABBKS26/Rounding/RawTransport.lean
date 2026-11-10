module

public import ABBKS26.Rounding.Raw
public import ABBKS26.Rounding.DetRound

/-! Exact finite-variable transport for represented nested systems. -/

@[expose] public section

namespace ABBKS26.Rounding.RawTransport

open Common Matrix MvPolynomial
open SoS.Solver (Problem RawPoly)

noncomputable section

/-- A finite solver point is obtained by restricting the same analytic nested witness. -/
theorem target_of_satisfies (I : RawInput) (P : Problem) (hP : RawRep I P)
    (γ : ℚ) (r : ℕ) (M : ℚ) (v : Vec I.family.dimension)
    (hv : sqnorm v = 1) (y : ℕ → ℝ)
    (hy : ∀ i : Fin I.family.dimension, y i.val = v i)
    (hs : SatisfiesNested I.family.real I.degree I.epsilon I.ball y) :
    (RoundInput.mk P I.family.dimension γ r M).Target v := by
  refine ⟨hv, (fun i ↦ y i.val), ?_, ?_⟩
  · intro i _
    exact hy i
  · intro f hf
    have hm : rename Fin.val (SoS.toReal f) ∈
        nestedSystem I.family.real I.degree I.epsilon I.ball := by
      rw [← hP.2.2]
      exact List.mem_map.mpr ⟨f, hf, rfl⟩
    simpa only [eval_rename, Function.comp_def] using hs _ hm

private def restrictVars (n i : ℕ) : MvPolynomial (Fin n) ℝ :=
  if h : i < n then X ⟨i, h⟩ else 0

private theorem restrict_degree (n i : ℕ) : (restrictVars n i).totalDegree ≤ 1 := by
  unfold restrictVars
  split <;> simp

private theorem restrict_norm (n i : ℕ) : SoS.coeffNorm1 (restrictVars n i) ≤ 1 := by
  unfold restrictVars
  split <;> simp [SoS.coeffNorm1_X, SoS.coeffNorm1_zero]

private theorem restrict_rename (n : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    aeval (restrictVars n) (rename Fin.val f) = f := by
  rw [aeval_rename]
  have he : restrictVars n ∘ (Fin.val : Fin n → ℕ) = X := by
    funext i
    simp only [Function.comp_apply, restrictVars, i.isLt, dite_true]
  rw [he]
  exact aeval_X_left_apply f

private theorem restrict_prefix {n m : ℕ} (h : m ≤ n) (f : MvPolynomial (Fin m) ℝ) :
    aeval (restrictVars n) (rename Fin.val f) = rename (Fin.castLEEmb h) f := by
  rw [aeval_rename, rename_eq_aeval]
  have he : restrictVars n ∘ (Fin.val : Fin m → ℕ) = X ∘ Fin.castLEEmb h := by
    funext i
    simp only [Function.comp_apply, restrictVars, i.isLt.trans_le h, dite_true]
    rfl
  rw [he]

private theorem finite_system (I : RawInput) (P : Problem) (hP : RawRep I P) :
    (nestedSystem I.family.real I.degree I.epsilon I.ball).map
      (aeval (restrictVars P.numVars)) = P.system.map SoS.toReal := by
  rw [← hP.2.2, List.map_map]
  apply List.map_congr_left
  intro f _
  exact restrict_rename P.numVars (SoS.toReal f)

private theorem prefix_mem (I : RawInput) (P : Problem) (hP : RawRep I P)
    (f : RPoly I.family.dimension)
    (hf : rename Fin.val f ∈ nestedSystem I.family.real I.degree I.epsilon I.ball)
    (hd : I.family.dimension ≤ P.numVars) :
    rename (Fin.castLEEmb hd) f ∈ P.system.map SoS.toReal := by
  rw [← finite_system I P hP]
  exact List.mem_map.mpr ⟨rename Fin.val f, hf, restrict_prefix hd f⟩

/-- Reification transports the complement concentration certificate without increasing
its norm or degree. Feasibility of the solver problem is a separate, explicit premise. -/
theorem concentrated_of_complement (I : RawInput) (P : Problem) (hP : RawRep I P)
    (hA : I.family.real.Valid I.degree) (hv : P.Valid)
    (γ : ℚ) (r : ℕ) (B : ℚ) (M : ℝ) (R : Mat I.family.dimension)
    (hR : Projection R) (hr : R.rank ≤ r)
    (hε : 0 < I.epsilon) (hε1 : I.epsilon ≤ 1)
    (hcomp : I.family.real.FeasibleComplement R M)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hr1 : 1 ≤ r) (hB : 1 ≤ B)
    (hsmall : 2 * Real.sqrt (I.epsilon : ℝ) ≤ (γ : ℝ) ^ 4 / 160000)
    (hbound : nestedNorm I.family.real I.degree I.epsilon M ≤ B) :
    (RoundInput.mk P I.family.dimension γ r B).Concentrated := by
  have hd : I.family.dimension ≤ P.numVars := by
    rw [hP.1]
    exact RawAux.dimension_le_vars I.family.real I.degree
  let e := Fin.castLEEmb hd
  have hsphere : rename Fin.val (nsq - 1 : RPoly I.family.dimension) ∈
      nestedSystem I.family.real I.degree I.epsilon I.ball := by
    simp only [nestedSystem, nsq, map_sub, map_sum, map_pow, rename_X, map_one]
    exact List.mem_append_left _ (by simp)
  have hball : rename Fin.val (1 - nsq : RPoly I.family.dimension) ∈
      nestedSystem I.family.real I.degree I.epsilon I.ball := by
    simp only [nestedSystem, nsq, map_sub, map_sum, map_pow, rename_X, map_one]
    exact List.mem_append_left _ (by simp)
  have hc := nested_concentration I.family.real I.degree I.epsilon I.ball M R
    hA hR (by exact_mod_cast hε) (by exact_mod_cast hε1) hcomp
  have hc' := NestedAux.aevalNq hc (restrictVars P.numVars)
    (restrict_degree P.numVars) le_rfl (restrict_norm P.numVars)
  rw [finite_system I P hP] at hc'
  simp only [mul_one, one_pow, map_sub, aeval_C, restrict_prefix hd] at hc'
  rw [← hP.2.1] at hc'
  refine ⟨hd, hv, hγ, hγ1, hr1, hB, R, 2 * Real.sqrt (I.epsilon : ℝ),
    hR, hr, by positivity, hsmall, e, (fun _ ↦ rfl), ?_, ?_, ?_⟩
  · exact prefix_mem I P hP _ hsphere hd
  · exact prefix_mem I P hP _ hball hd
  · exact (hc'.derivesN.mono le_rfl hbound).congr (by
      simp only [e, algebraMap_eq, map_sub])

/-- A satisfying analytic point makes the normalized reification a valid solver problem. -/
theorem valid_of_rep (I : RawInput) (P : Problem) (hP : RawRep I P)
    (hobj : ∀ f ∈ P.2.2.2.1 :: P.2.2.2.2,
      (f.toPoly P.numVars).totalDegree ≤ P.degree)
    (hy : ∃ y : ℕ → ℝ,
      SatisfiesNested I.family.real I.degree I.epsilon I.ball y) :
    P.Valid := by
  change Even P.degree ∧ 2 ≤ P.degree ∧
    (∀ f ∈ P.2.2.2.1 :: P.2.2.2.2,
      (f.toPoly P.numVars).totalDegree ≤ P.degree) ∧
    (∃ B : ℚ, (C B : QPoly P.numVars) - ∑ i : Fin P.numVars, X i ^ 2 ∈ P.system) ∧
    ∃ y : Fin P.numVars → ℝ, ∀ f ∈ P.system, 0 ≤ eval y (SoS.toReal f)
  obtain ⟨y, hy⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hP.2.1]
    exact even_two.mul_right _
  · rw [hP.2.1]
    unfold solverDegree outerDegree
    omega
  · exact hobj
  · have hm : C (I.ball : ℝ) -
        ∑ i ∈ Finset.range (nestedVars I.family.real I.degree), X i ^ 2 ∈
          nestedSystem I.family.real I.degree I.epsilon I.ball := by
      unfold nestedSystem
      exact List.mem_append_right _ (List.mem_singleton_self _)
    rw [← hP.1, ← hP.2.2] at hm
    obtain ⟨f, hf, he⟩ := List.mem_map.mp hm
    refine ⟨I.ball, ?_⟩
    have hball : f = C I.ball - ∑ i : Fin P.numVars, X i ^ 2 := by
      apply (MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective)
      apply (MvPolynomial.rename_injective Fin.val Fin.val_injective)
      change rename Fin.val (SoS.toReal f) = _
      rw [he]
      simp only [map_sub, map_C, map_sum, map_pow, map_X, rename_C, rename_X]
      change C (I.ball : ℝ) - _ = C (I.ball : ℝ) - _
      rw [Finset.sum_range]
    exact hball ▸ hf
  · refine ⟨fun i ↦ y i.val, ?_⟩
    intro f hf
    have hm : rename Fin.val (SoS.toReal f) ∈
        nestedSystem I.family.real I.degree I.epsilon I.ball := by
      rw [← hP.2.2]
      exact List.mem_map.mpr ⟨f, hf, rfl⟩
    simpa only [eval_rename, Function.comp_def] using hy _ hm

end

end ABBKS26.Rounding.RawTransport
