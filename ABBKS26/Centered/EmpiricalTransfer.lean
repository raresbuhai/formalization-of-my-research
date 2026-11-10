module

public import ABBKS26.Centered.ThmZAuxProof

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalTransfer

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

theorem q_homogeneous (p : RPoly d) (ε : ℝ) (hp : p.IsHomogeneous 4) :
    (qConstraint p ε).IsHomogeneous 8 := by
  exact ((IdentAux.nsq_homogeneous.pow 4).C_mul _).sub
    (by simpa only [Nat.reduceMul] using (hp.C_mul (1 / 3)).pow 2)

theorem inst_homogeneous (p : RPoly d) (ε : ℝ) (hp : p.IsHomogeneous 4)
    (E : Mat d) : (inst (hConstraint p ε) E).IsHomogeneous 8 := by
  simpa only [inst, one_mul] using
    (IdentAux.hConstraint_homogeneous p ε hp).aeval (n := 1)
      (Sum.elim (fun i ↦ lin (E i)) X) (by
        intro i
        rcases i with i | i
        · change (lin (E i)).IsHomogeneous 1
          exact IsHomogeneous.sum _ _ _ fun j _ ↦ (isHomogeneous_X ℝ j).C_mul _
        · exact isHomogeneous_X ℝ i)

theorem derivesAt (p : RPoly d) (εq εh M : ℝ) (E : Mat d) (g : RPoly d)
    (hp : p.IsHomogeneous 4)
    (h : SoS.DerivesNq ((system p εq εh).instances (fun _ ↦ E)) 8 M 1 g) :
    (system p εq εh).DerivesAt (fun _ ↦ E) 8 M g := by
  apply IdentAux.derivesAt_of_homogeneous _ _ _ _ _ ?_ h
  intro a
  fin_cases a
  change (inst (hConstraint p εh) E).IsHomogeneous (hConstraint p εh).totalDegree
  by_cases hz : hConstraint p εh = 0
  · simp only [hz, inst, map_zero, totalDegree_zero]
    exact isHomogeneous_zero _ _ 0
  · rw [(IdentAux.hConstraint_homogeneous p εh hp).totalDegree hz]
    exact inst_homogeneous p εh hp E

theorem entry_of_frob (E : Mat d) (X : ℝ) (hX : 0 ≤ X)
    (hE : frobSq E ≤ X ^ 2) (i j : Fin d) : |E i j| ≤ X := by
  have hi : ∑ j, E i j ^ 2 ≤ frobSq E :=
    Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ sq_nonneg (E a b))
      (Finset.mem_univ i)
  have hj : E i j ^ 2 ≤ ∑ j, E i j ^ 2 :=
    Finset.single_le_sum (fun b _ ↦ sq_nonneg (E i b)) (Finset.mem_univ j)
  exact (sq_le_sq₀ (abs_nonneg _) hX).mp
    (by simpa only [sq_abs] using hj.trans (hi.trans hE))

theorem inst_norm (p : BiPoly d) (E : Mat d) (X : ℝ) (hX : 0 ≤ X)
    (hE : frobSq E ≤ X ^ 2) (hp : p.totalDegree ≤ 8) :
    SoS.coeffNorm1 (inst p E) ≤
      SoS.coeffNorm1 p * (1 + d * X) ^ 8 := by
  have hbase : 1 ≤ 1 + (d : ℝ) * X := by
    linarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hX]
  apply (SoS.coeffNorm1_aeval_le _ hbase ?_ p).trans
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hp)
      (SoS.coeffNorm1_nonneg p)
  · intro i
    rcases i with i | i
    · exact (IdentAux.norm_lin E X (entry_of_frob E X hX hE) i).trans
        (by linarith)
    · exact (SoS.coeffNorm1_X _).le.trans hbase

private theorem bridge (A : List (RPoly d)) (f g : RPoly d) (M : ℝ)
    (hf : f ∈ A) (hfd : f.totalDegree ≤ 8) (hg : g.IsHomogeneous 8)
    (hs : IsSumSq (g - 2 * f))
    (hn : SoS.coeffNorm1 g + 2 * SoS.coeffNorm1 f + 2 ≤ M) :
    SoS.DerivesNq A g.totalDegree M 1 g := by
  have hM : 0 ≤ M := by
    linarith only [hn, SoS.coeffNorm1_nonneg g, SoS.coeffNorm1_nonneg f]
  by_cases hz : g = 0
  · rw [hz]
    exact SoS.DerivesNq.zero A _ _ hM
  rw [hg.totalDegree hz]
  have hd : (g - 2 * f).totalDegree ≤ 8 := by
    apply (totalDegree_sub _ _).trans
    apply max_le hg.totalDegree_le
    exact (totalDegree_mul _ _).trans (by
      rw [show (2 : RPoly d) = C 2 from (map_ofNat C 2).symm, totalDegree_C, zero_add]
      exact hfd)
  have hnorm : SoS.coeffNorm1 (g - 2 * f) ≤
      SoS.coeffNorm1 g + 2 * SoS.coeffNorm1 f := by
    have hh := SoS.coeffNorm1_sub_le g (2 * f)
    have he : SoS.coeffNorm1 (2 * f) = 2 * SoS.coeffNorm1 f := by
      rw [show (2 : RPoly d) = C 2 from (map_ofNat C 2).symm,
        SoS.coeffNorm1_C_mul]
      norm_num
    rwa [he] at hh
  have hr := SoS.DerivesNq.ofIsSOS (q := 1) A
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using hs) hd hnorm
  have ha : SoS.DerivesNq A 8 1 1 f := SoS.DerivesNq.of_mem hf hfd le_rfl
  exact ((hr.add (ha.smul (by norm_num : (0 : ℝ) ≤ 2))).congr (by
    rw [map_ofNat]
    ring)).mono
    le_rfl (by simpa only [mul_one] using hn)

/-- Norms of the two families and their single matrix instance pay for linear
composition. The resulting certificate retains the original slot matrices. -/
theorem derives_transfer (p q : RPoly d) (εq εh εq' εh' M X B : ℝ)
    (hp : p.IsHomogeneous 4) (hq : q.IsHomogeneous 4) (hX : 0 ≤ X)
    (hB : 1 ≤ B)
    (htrq : IsSumSq (qConstraint q εq' - 2 * qConstraint p εq))
    (htrh : IsSumSq (hConstraint q εh' - 2 * hConstraint p εh))
    (hnq : SoS.coeffNorm1 (qConstraint q εq') +
      2 * SoS.coeffNorm1 (qConstraint p εq) + 2 ≤ B)
    (hnh : (SoS.coeffNorm1 (hConstraint q εh') +
      2 * SoS.coeffNorm1 (hConstraint p εh)) * (1 + d * X) ^ 8 + 2 ≤ B)
    (g : RPoly d) (hg : (system q εq' εh').Derives 8 M X g) :
    (system p εq εh).Derives 8 (M * (1 + 3 * B)) X g := by
  obtain ⟨Ξ, hΞ, hproof⟩ := hg
  let E := Ξ ⟨0, by simp [system]⟩
  have he : ∀ a, Ξ a = E := by
    intro a
    congr 1
    apply Fin.ext
    have ha : a.val < 1 := a.isLt
    change a.val = 0
    omega
  have hfrob : frobSq E ≤ X ^ 2 := hΞ _
  have hlist (t : RPoly d) (a b : ℝ) :
      (system t a b).instances (fun _ ↦ E) =
        [1 - nsq, qConstraint t a, inst (hConstraint t b) E] := by
    simp [system, FamilySystem.instances, List.ofFn_succ]
  have hproof' : SoS.DerivesNq ((system q εq' εh').instances (fun _ ↦ E)) 8 M 1 g := by
    have hfun : Ξ = fun _ ↦ E := funext he
    rw [hfun] at hproof
    exact hproof.derivesNq
  have hdq := (q_homogeneous p εq hp).totalDegree_le
  have hdh := (inst_homogeneous p εh hp E).totalDegree_le
  have hbridge : ∀ f ∈ (system q εq' εh').instances (fun _ ↦ E),
      SoS.DerivesNq ((system p εq εh).instances (fun _ ↦ E)) f.totalDegree B 1 f := by
    intro f hf
    rw [hlist] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact SoS.DerivesNq.of_mem (by rw [hlist]; simp) le_rfl hB
    rcases List.mem_cons.mp hf with rfl | hf
    · exact bridge _ _ _ B (by rw [hlist]; simp) hdq
        (q_homogeneous q εq' hq) htrq hnq
    rw [List.mem_singleton.mp hf]
    apply bridge _ _ _ B (by rw [hlist]; simp) hdh
      (inst_homogeneous q εh' hq E) (instance_sos _ _ 2 E htrh)
    have hi := inst_norm (hConstraint q εh') E X hX hfrob
      (IdentAux.hConstraint_homogeneous q εh' hq).totalDegree_le
    have hj := inst_norm (hConstraint p εh) E X hX hfrob
      (IdentAux.hConstraint_homogeneous p εh hp).totalDegree_le
    nlinarith only [hi, hj, hnh]
  have hres := SoS.DerivesNq.trans hbridge hproof'
  have hlen : ((system q εq' εh').instances (fun _ ↦ E)).length = 3 := by
    rw [hlist]
    rfl
  have hres' : SoS.DerivesNq ((system p εq εh).instances (fun _ ↦ E))
      8 (M * (1 + 3 * B)) 1 g := by
    simpa only [hlen, Nat.cast_ofNat] using hres
  exact ⟨fun _ ↦ E, fun _ ↦ hfrob, derivesAt p εq εh _ E g hp hres'⟩

end

end ABBKS26.Centered.EmpiricalTransfer
