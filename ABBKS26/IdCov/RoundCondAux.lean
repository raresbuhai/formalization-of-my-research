module

public import ABBKS26.IdCov.Approx

/-! Linear algebra for the rounding hypotheses. -/

@[expose] public section

namespace ABBKS26.IdCov.RoundCondAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators

variable {k d : ℕ}

theorem between_psd (D : Data k d) (π γ : ℝ) (hD : D.Valid π γ) :
    (between D).PosSemidef := by
  apply posSemidef_sum
  intro i _
  have hi : (vecMulVec (D.mean i) (D.mean i)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (D.mean i)
  exact hi.smul (hD.1.1.le.trans (hD.1.2.1 i))

theorem le_of_gap_psd {A B : Mat d} (h : (B - A).PosSemidef) : LE A B := by
  intro v
  simpa only [qform, star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] using
    h.dotProduct_mulVec_nonneg v

theorem spectral_cut (A : Mat d) (hA : A.PosSemidef) (L τ : ℝ)
    (hupper : LE A (L • (1 : Mat d))) :
    ∃ P : Mat d, Projection P ∧ LE (τ • P) A ∧
      LE A (L • P + τ • (1 - P)) := by
  classical
  let T := Unitary.conjStarAlgAut ℝ (Mat d) hA.1.eigenvectorUnitary
  let e := hA.1.eigenvalues
  let f : Fin d → ℝ := fun i ↦ if τ ≤ e i then 1 else 0
  let P := T (diagonal f)
  have hT (B : Mat d) : T B =
      (hA.1.eigenvectorUnitary : Mat d) * B *
        (hA.1.eigenvectorUnitary : Mat d)ᴴ := by
    simp only [T, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hs : T (diagonal e) = A := by
    simpa only [T, e, Function.comp_def, RCLike.ofReal_real_eq_id, id] using
      hA.1.spectral_theorem.symm
  have he (i : Fin d) : e i ≤ L := by
    have hi := hupper (hA.1.eigenvectorBasis i)
    have hn := Rounding.DetRoundAux.eigen_sqnorm A hA.1 i
    simp only [qform, hA.1.mulVec_eigenvectorBasis, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at hi
    change (hA.1.eigenvectorBasis i : Vec d) ⬝ᵥ hA.1.eigenvectorBasis i = 1 at hn
    simpa only [hn, mul_one] using hi
  have hpos (B : Mat d) (hB : B.PosSemidef) : (T B).PosSemidef := by
    rw [hT]
    exact hB.mul_mul_conjTranspose_same _
  refine ⟨P, ⟨?_, ?_⟩, ?_, ?_⟩
  · have hh : (T (diagonal f)).IsHermitian := by
      rw [hT]
      exact isHermitian_mul_mul_conjTranspose _ (isHermitian_diagonal f)
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hh
  · change T (diagonal f) * T (diagonal f) = T (diagonal f)
    rw [← map_mul]
    congr 1
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp [f]
    split_ifs <;> norm_num
  · have hh : (diagonal e - τ • diagonal f).PosSemidef := by
      rw [← diagonal_smul, diagonal_sub]
      apply PosSemidef.diagonal
      intro i
      dsimp [f]
      split_ifs with hi
      · simpa using sub_nonneg.mpr hi
      · simpa using hA.eigenvalues_nonneg i
    apply le_of_gap_psd
    simpa only [map_sub, map_smul, hs, P] using hpos _ hh
  · have hh : (L • diagonal f + τ • (1 - diagonal f) - diagonal e).PosSemidef := by
      rw [← diagonal_one, diagonal_sub, ← diagonal_smul, ← diagonal_smul,
        diagonal_add, diagonal_sub]
      apply PosSemidef.diagonal
      intro i
      dsimp [f]
      split_ifs with hi
      · simpa using sub_nonneg.mpr (he i)
      · simpa using sub_nonneg.mpr (le_of_lt (lt_of_not_ge hi))
    apply le_of_gap_psd
    simpa only [map_sub, map_add, map_smul, map_one, hs, P] using hpos _ hh

theorem mean_projection (D : Data k d) :
    ∃ R : Mat d, Projection R ∧ R.rank ≤ k ∧
      ∀ i, R *ᵥ D.mean i = D.mean i := by
  let E := EuclideanSpace ℝ (Fin d)
  let m : Fin k → E := fun i ↦ WithLp.toLp 2 (D.mean i)
  let S := Submodule.span ℝ (Set.range m)
  let R : Mat d := Matrix.toEuclideanLin.symm S.starProjection.toLinearMap
  have hR : Matrix.toEuclideanLin R = S.starProjection.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hs : R.IsHermitian := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hR]
    exact S.starProjection_isSymmetric
  refine ⟨R, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hs
  · apply Matrix.toEuclideanLin.injective
    change Matrix.toLpLin 2 2 (R * R) = Matrix.toLpLin 2 2 R
    rw [Matrix.toLpLin_mul_same]
    change Matrix.toEuclideanLin R * Matrix.toEuclideanLin R = Matrix.toEuclideanLin R
    rw [hR]
    exact congrArg (fun f : E →L[ℝ] E ↦ f.toLinearMap)
      S.isIdempotentElem_starProjection
  · rw [Matrix.rank_eq_finrank_range_toLin R
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
    change Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin R)) ≤ k
    rw [hR, S.range_starProjection]
    exact (finrank_range_le_card m).trans_eq (Fintype.card_fin k)
  · intro i
    have hi : S.starProjection (m i) = m i :=
      S.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨i, rfl⟩)
    change S.starProjection.toLinearMap (m i) = m i at hi
    rw [← hR] at hi
    exact congrArg (fun v : E ↦ (v : Fin d → ℝ)) hi

theorem lin_degree (v : Vec d) : (lin v).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem subst_degree (A : Mat d) (p : RPoly d) :
    (subst A p).totalDegree ≤ p.totalDegree := by
  simpa only [subst, Nat.mul_one] using
    SoS.totalDegree_aeval_le (fun i ↦ lin (A i)) (fun i ↦ lin_degree (A i)) p

theorem subst_one (p : RPoly d) : subst (1 : Mat d) p = p := by
  have h : (fun i ↦ lin ((1 : Mat d) i)) = X := by
    funext i
    simp [lin, Matrix.one_apply, apply_ite, ite_mul]
  simp [subst, h]

theorem projection_entry (P : Mat d) (hP : Projection P) (i j : Fin d) :
    |P i j| ≤ 1 := by
  have he : (P *ᵥ Pi.single j 1) i ^ 2 ≤ sqnorm (P *ᵥ Pi.single j 1) := by
    simpa only [sqnorm, dotProduct, pow_two] using
      Finset.single_le_sum (fun a _ ↦ mul_self_nonneg ((P *ᵥ Pi.single j 1) a))
        (Finset.mem_univ i)
  have hc := Rounding.DetRoundAux.projection_contract P hP (Pi.single j 1)
  have hn : sqnorm (Pi.single j 1 : Vec d) = 1 := by
    rw [sqnorm, dotProduct_single, Pi.single_eq_same, mul_one]
  have hx : (P *ᵥ Pi.single j 1) i = P i j := by simp [mulVec_single]
  rw [hn] at hc
  rw [hx] at he
  exact (sq_le_one_iff_abs_le_one _).1 (he.trans hc)

theorem projection_lin_norm (P : Mat d) (hP : Projection P) (i : Fin d) :
    SoS.coeffNorm1 (lin (P i)) ≤ d := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ by
      simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, mul_one] using
        projection_entry P hP i j
    _ = d := by simp

theorem subst_ball (R : Mat d) (hR : Projection R) :
    subst (1 - R) (1 - nsq) = 1 - nsq + quad R := by
  have hP := Rounding.DetRoundAux.projection_compl R hR
  have hN (A : Mat d) : subst A nsq = quad (Aᵀ * A) := by
    simp only [subst, nsq, map_sum, map_mul, aeval_X, lin, pow_two,
      Finset.sum_mul_sum, quad, Matrix.mul_apply, Matrix.transpose_apply, map_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hn : subst (1 - R) nsq = nsq - quad R := by
    rw [hN, hP.1, hP.2]
    simp [quad, nsq, C_sub, sub_mul, Finset.sum_sub_distrib,
      Matrix.one_apply, pow_two, apply_ite, ite_mul]
  change (aeval _) (1 - nsq) = _
  rw [map_sub, map_one]
  change 1 - subst (1 - R) nsq = _
  rw [hn]
  ring

theorem feasible_ball (R : Mat d) (hR : Projection R) :
    SoS.DerivesNq (ball : List (RPoly d)) (1 - nsq : RPoly d).totalDegree
      (1 + SoS.coeffNorm1 (quad R)) 1 (subst (1 - R) (1 - nsq)) := by
  have hd : (quad R).totalDegree ≤ (1 - nsq : RPoly d).totalDegree := by
    by_cases hz : d = 0
    · subst d
      simp [quad]
    · have hn : (nsq : RPoly d) ≠ 0 := by
        let i : Fin d := ⟨0, Nat.pos_of_ne_zero hz⟩
        intro h
        have he := congrArg (eval (Pi.single i (1 : ℝ))) h
        simp [nsq, Pi.single_apply] at he
      have hdeg := (ApproxAux.nsq_homogeneous (d := d)).totalDegree hn
      rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt,
        totalDegree_neg, hdeg]
      · exact IdentAux.quad_degree R
      · simp only [totalDegree_one, totalDegree_neg, hdeg]
        norm_num
  have hp : R.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hR.1, hR.2] using
      posSemidef_conjTranspose_mul_self R
  have hb : SoS.DerivesNq ball (1 - nsq : RPoly d).totalDegree 1 1 (1 - nsq) :=
    SoS.DerivesNq.of_mem (by simp [ball]) le_rfl le_rfl
  have hq := SoS.DerivesNq.ofIsSOS (q := 1) ball
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using SoSKit.psd_quad R hp) hd le_rfl
  rw [subst_ball R hR]
  exact hb.add hq

theorem constraint_subst_norm
    (D : Data k d) (M : ℕ → RPoly d) (t s : ℕ) (π ε W : ℝ) (P : Mat d)
    (ht : 1 ≤ t) (hs : 2 ≤ s ∧ s ≤ 2 * t) (he : 0 ≤ ε ∧ ε ≤ 1)
    (hW : NormLedger D M t π ε W) (hP : Projection P)
    (hd : (constraint M ε s).totalDegree ≤ 4 * s) :
    SoS.coeffNorm1 (subst P (constraint M ε s)) ≤ W ^ (20 * t) := by
  have hb := ApproxAux.size_bounds_one ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hW0 : 0 ≤ W := by linarith
  have ha : alpha s ≤ W ^ s := by
    apply (IdentAux.alpha_bound s).trans
    apply pow_le_pow_left₀ (by positivity)
    have hs' : (s : ℝ) ≤ 2 * t := by exact_mod_cast hs.2
    linarith [hb.2.2.2]
  have hm₂ : SoS.coeffNorm1 (M 2) ≤ W ^ 2 := hW.2.2.2.1 1 (by omega) (by omega)
  have hgauss : SoS.coeffNorm1 (C (alpha s) * M 2 ^ s) ≤ W ^ (3 * s) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_nonneg
      (show 0 ≤ alpha s by linarith [IdentAux.alpha_one_le s])]
    calc _ ≤ W ^ s * (W ^ 2) ^ s := mul_le_mul ha (IdentAux.norm_pow hm₂ s)
          (SoS.coeffNorm1_nonneg _) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hm : SoS.coeffNorm1 (dev M s) ≤ 2 * W ^ (3 * s) := by
    have hms := (hW.2.2.2.1 s (by omega) hs.2).trans
      (SoS.pow_le_pow_of_two_le hW2 (show 2 * s ≤ 3 * s by omega))
    exact (SoS.coeffNorm1_sub_le _ _).trans (by linarith)
  have hfirst : SoS.coeffNorm1 (C ε * nsq ^ (2 * s) : RPoly d) ≤ W ^ (6 * s) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_nonneg he.1]
    calc _ ≤ 1 * W ^ (2 * s) := mul_le_mul he.2
          (IdentAux.norm_pow (IdentAux.norm_nsq.trans hb.2.1) _)
          (SoS.coeffNorm1_nonneg _) (by norm_num)
      _ ≤ _ := by simpa using SoS.pow_le_pow_of_two_le hW2 (show 2 * s ≤ 6 * s by omega)
  have hsq : SoS.coeffNorm1 (dev M s ^ 2) ≤ 4 * W ^ (6 * s) := by
    calc _ ≤ (2 * W ^ (3 * s)) ^ 2 := IdentAux.norm_pow hm 2
      _ = _ := by rw [mul_pow, ← pow_mul]; norm_num; congr 1; omega
  have hc : SoS.coeffNorm1 (constraint M ε s) ≤ 5 * W ^ (6 * s) :=
    (SoS.coeffNorm1_sub_le _ _).trans (by linarith)
  let β : ℝ := d + 1
  have hβ : 1 ≤ β := by dsimp [β]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hβ₂ : β ^ 2 ≤ W := by
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hh := mul_le_mul_of_nonneg_left ht'
      (show 0 ≤ 64 * (d + 1 : ℝ) ^ 2 by positivity)
    dsimp [β]
    nlinarith [hW.1]
  have hpow : β ^ (4 * s) ≤ W ^ (2 * s) := by
    calc _ = (β ^ 2) ^ (2 * s) := by rw [← pow_mul]; congr 1; omega
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hβ₂ _
  have hn := SoS.coeffNorm1_aeval_le (fun i ↦ lin (P i)) hβ
    (fun i ↦ (projection_lin_norm P hP i).trans (by dsimp [β]; linarith))
    (constraint M ε s)
  calc
    _ ≤ SoS.coeffNorm1 (constraint M ε s) * β ^ (constraint M ε s).totalDegree := hn
    _ ≤ (5 * W ^ (6 * s)) * β ^ (4 * s) := mul_le_mul hc
        (pow_le_pow_right₀ hβ hd) (by positivity) (by positivity)
    _ ≤ (5 * W ^ (6 * s)) * W ^ (2 * s) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 5 * W ^ (8 * s) := by
      rw [mul_assoc, ← pow_add, show 6 * s + 2 * s = 8 * s by omega]
    _ ≤ W ^ (8 * s + 1) := by rw [pow_succ]; nlinarith [hb.1, pow_nonneg hW0 (8 * s)]
    _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)

end

end ABBKS26.IdCov.RoundCondAux
