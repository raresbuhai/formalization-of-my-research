module

public import ABBKS26.Tree.Complete

/-!
# Empirical verification of complete splits

Component window counts and two small wrong-side counts imply the refinement check.
-/

@[expose] public section

namespace ABBKS26.Tree.RefineAux

noncomputable section

open Common MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n k d : ℕ}

private theorem constant_clean_count {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (ω : Fin n → Triple k d) (j : Fin k)
    (f : Fin n → ℝ) (g : Ω → ℝ) (c η : ℝ) (hη : 0 ≤ η)
    (hf : ∀ l, f l = c) (hg : ∀ y, g y = c) (P : ℝ → Prop) [DecidablePred P] :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦ P (f l)).card : ℝ) ≤
      (ν.real {y | P (g y)} + η) * (cluster (labels ω) j).card := by
  classical
  simp_rw [hf, hg]
  by_cases hc : P c
  · simp only [hc, Finset.filter_true, Set.ofPred_true, probReal_univ]
    have hh : ((cluster (labels ω) j \ corrupted ω).card : ℝ) ≤
        (cluster (labels ω) j).card :=
      Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
    nlinarith only [hh, mul_nonneg hη (Nat.cast_nonneg (cluster (labels ω) j).card)]
  · simp only [hc, Finset.filter_false, Finset.card_empty, Nat.cast_zero,
      Set.ofPred_false, measureReal_empty, zero_add]
    positivity

/-- The population comparison also applies to statistics of zero variance. -/
theorem upper_window (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : SoundAux.CoordinateSpec M j f) (a b : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      a ≤ SoundAux.value f ω r l ∧ SoundAux.value f ω r l ≤ b).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | a - 2 * η * C.s ≤ f.eval y.ofLp ∧ f.eval y.ofLp ≤ b + 2 * η * C.s} + η) *
          (cluster (labels ω) j).card := by
  by_cases hs : C.s = 0
  · have he (y : EuclideanSpace ℝ (Fin d)) : f.eval y.ofLp = C.c := by
      simpa only [hs, zero_mul, zero_add] using C.eval y
    have hv (l : Fin n) : SoundAux.value f ω r l = C.c := by
      rw [SoundAux.value, ← SoundAux.eval_cast]
      exact he (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))
    simpa only [hs, mul_zero, sub_zero, add_zero] using
      constant_clean_count _ ω j _ _ C.c η hη.1.le hv he (fun t ↦ a ≤ t ∧ t ≤ b)
  · exact C.upper_window M ε w η D ω r hM hg hr hη hn j f
      (lt_of_le_of_ne C.nonneg (Ne.symm hs)) a b

theorem upper_left (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : SoundAux.CoordinateSpec M j f) (t : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      SoundAux.value f ω r l ≤ t).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | f.eval y.ofLp ≤ t + 2 * η * C.s} + η) * (cluster (labels ω) j).card := by
  by_cases hs : C.s = 0
  · have he (y : EuclideanSpace ℝ (Fin d)) : f.eval y.ofLp = C.c := by
      simpa only [hs, zero_mul, zero_add] using C.eval y
    have hv (l : Fin n) : SoundAux.value f ω r l = C.c := by
      rw [SoundAux.value, ← SoundAux.eval_cast]
      exact he (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))
    simpa only [hs, mul_zero, add_zero] using
      constant_clean_count _ ω j _ _ C.c η hη.1.le hv he (fun z ↦ z ≤ t)
  · exact C.upper_left M ε w η D ω r hM hg hr hη hn j f
      (lt_of_le_of_ne C.nonneg (Ne.symm hs)) t

theorem upper_right (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (f : Statistic d) (C : SoundAux.CoordinateSpec M j f) (t : ℝ) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      t < SoundAux.value f ω r l).card : ℝ) ≤
      ((multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
        {y | t - 2 * η * C.s < f.eval y.ofLp} + η) * (cluster (labels ω) j).card := by
  by_cases hs : C.s = 0
  · have he (y : EuclideanSpace ℝ (Fin d)) : f.eval y.ofLp = C.c := by
      simpa only [hs, zero_mul, zero_add] using C.eval y
    have hv (l : Fin n) : SoundAux.value f ω r l = C.c := by
      rw [SoundAux.value, ← SoundAux.eval_cast]
      exact he (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)))
    simpa only [hs, mul_zero, sub_zero] using
      constant_clean_count _ ω j _ _ C.c η hη.1.le hv he (fun z ↦ t < z)
  · exact C.upper_right M ε w η D ω r hM hg hr hη hn j f
      (lt_of_le_of_ne C.nonneg (Ne.symm hs)) t

theorem sum_reference_card (ω : Fin n → Triple k d) (I : Finset (Fin k)) :
    ∑ j ∈ I, ((cluster (labels ω) j).card : ℝ) = (referenceSet ω I).card := by
  classical
  have hf (j : Fin k) : referenceSet ω I ∩ cluster (labels ω) j =
      if j ∈ I then cluster (labels ω) j else ∅ := by
    by_cases hj : j ∈ I
    · rw [ite_eq_left hj]
      apply Finset.inter_eq_right.mpr
      intro l hl
      have he : (ω l).1 = j := (Finset.mem_filter.mp hl).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, he.symm ▸ hj⟩
    · rw [ite_eq_right hj]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      obtain ⟨hI, hcluster⟩ := Finset.mem_inter.mp hl
      have he : (ω l).1 = j := (Finset.mem_filter.mp hcluster).2
      exact hj (he ▸ (Finset.mem_filter.mp hI).2)
  have hh := SoundAux.sum_cluster_card ω (referenceSet ω I)
  have hcast (j : Fin k) :
      ((if j ∈ I then cluster (labels ω) j else ∅).card : ℝ) =
        if j ∈ I then ((cluster (labels ω) j).card : ℝ) else 0 := by
    split_ifs <;> simp
  simpa only [hf, hcast, Finset.sum_ite_mem, Finset.univ_inter] using hh

private theorem contamination_counts (ω : Fin n → Triple k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (δ : ℝ)
    (hδ : nodeContamination ω N I ≤ δ) (hhalf : δ ≤ 1 / 2) :
    let G := referenceSet ω I
    let H := G ∩ (Finset.univ \ corrupted ω) ∩ N
    ((N \ H).card : ℝ) ≤ δ * N.card ∧ (G.card : ℝ) ≤ 2 * N.card := by
  classical
  intro G H
  have hN : ((N \ H).card : ℝ) / N.card ≤ δ := (le_max_left _ _).trans hδ
  have hG : ((G \ H).card : ℝ) / G.card ≤ δ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hδ)
  constructor
  · by_cases hn : N.card = 0
    · have he := Finset.card_eq_zero.mp hn
      simp [he]
    · exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mp hN
  · by_cases hg : G.card = 0
    · simp only [hg, Nat.cast_zero]
      positivity
    · have hh := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg))).mp hG
      have hsub : H ⊆ G := (Finset.inter_subset_left).trans Finset.inter_subset_left
      have he : ((G \ H).card : ℝ) + H.card = G.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
      have hc : (H.card : ℝ) ≤ N.card :=
        Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
      nlinarith only [hh, he, hc,
        mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg G.card)]

theorem window_count_le (ω : Fin n → Triple k d) (N : Finset (Fin n))
    (I : Finset (Fin k)) (δ t : ℝ) (P : Fin n → Prop) [DecidablePred P]
    (hδ : nodeContamination ω N I ≤ δ) (hhalf : δ ≤ 1 / 2) (ht : 0 ≤ t)
    (hwin : ∀ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω).filter P).card : ℝ) ≤
        t * (cluster (labels ω) j).card) :
    ((N.filter P).card : ℝ) ≤ (δ + 2 * t) * N.card := by
  classical
  let G := referenceSet ω I
  let H := G ∩ (Finset.univ \ corrupted ω) ∩ N
  have hcover : H.filter P ⊆ I.biUnion (fun j ↦
      (cluster (labels ω) j \ corrupted ω).filter P) := by
    intro l hl
    obtain ⟨hlH, hlP⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlGbad, _⟩ := Finset.mem_inter.mp hlH
    obtain ⟨hlG, hlbad⟩ := Finset.mem_inter.mp hlGbad
    have hj : (ω l).1 ∈ I := (Finset.mem_filter.mp hlG).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(ω l).1, hj, Finset.mem_filter.mpr ⟨?_, hlP⟩⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ l, rfl⟩,
      (Finset.mem_sdiff.mp hlbad).2⟩
  have hH : ((H.filter P).card : ℝ) ≤ t * G.card := by
    calc
      _ ≤ ∑ j ∈ I, (((cluster (labels ω) j \ corrupted ω).filter P).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
      _ ≤ ∑ j ∈ I, t * (cluster (labels ω) j).card :=
        Finset.sum_le_sum hwin
      _ = t * G.card := by rw [← Finset.mul_sum, sum_reference_card]
  have hsub : N.filter P ⊆ (N \ H) ∪ H.filter P := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hl ⊢
    tauto
  obtain ⟨hbad, hsize⟩ := contamination_counts ω N I δ hδ hhalf
  have hc : ((N.filter P).card : ℝ) ≤ (N \ H).card + (H.filter P).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have htG := mul_le_mul_of_nonneg_left hsize ht
  nlinarith only [hc, hbad, hH, htG]

theorem side_large (ω : Fin n → Triple k d) (N A B : Finset (Fin n))
    (I : Finset (Fin k)) (j : Fin k) (w Φ t ξ : ℝ)
    (hj : j ∈ I) (hpart : A ∪ B = N) (hleak : leakage ω N I ≤ Φ)
    (hcounts : 0.9 * w * n ≤ (cluster (labels ω) j).card)
    (hbad : (corrupted ω).card ≤ ξ * n)
    (hwrong : (((cluster (labels ω) j \ corrupted ω) ∩ B).card : ℝ) ≤
      t * (cluster (labels ω) j).card)
    (hsmall : Φ + t ≤ 1 / 2) (hξ : ξ ≤ w / 8) : w * n / 4 ≤ A.card := by
  classical
  have hmissing := SoundAux.leakage_component ω N I Φ hleak j
  simp only [hj, ite_true] at hmissing
  have hsub : cluster (labels ω) j ⊆
      (((cluster (labels ω) j \ corrupted ω) \ N) ∪ corrupted ω) ∪
        (((cluster (labels ω) j \ corrupted ω) ∩ B) ∪ A) := by
    intro l hl
    have hN : l ∈ N ↔ l ∈ A ∨ l ∈ B := by rw [← hpart]; simp
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hc : ((cluster (labels ω) j).card : ℝ) ≤
      (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ) + (corrupted ω).card +
        (((cluster (labels ω) j \ corrupted ω) ∩ B).card : ℝ) + A.card := by
    have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h₁ := Finset.card_union_le
      ((cluster (labels ω) j \ corrupted ω) \ N) (corrupted ω)
    have h₂ := Finset.card_union_le ((cluster (labels ω) j \ corrupted ω) ∩ B) A
    exact_mod_cast hh.trans (by omega)
  have hmul := mul_le_mul_of_nonneg_right hsmall
    (Nat.cast_nonneg (α := ℝ) (cluster (labels ω) j).card)
  have hξn := mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hc, hmissing, hwrong, hcounts, hbad, hmul, hξn]

/-- Verification uses component counts only on the clean reference. -/
theorem verify_of_component_counts (ω : Fin n → Triple k d)
    (x : Fin n → Fin d → ℚ) (p : StepParams) (e : Edge n d)
    (I : Finset (Fin k)) (w Φ δ t ξ : ℝ)
    (hw : (p.w : ℝ) = w) (hleak : leakage ω e.parent I ≤ Φ)
    (hδ : nodeContamination ω e.parent I ≤ δ) (hhalf : δ ≤ 1 / 2)
    (ht : 0 ≤ t) (hverify : δ + 2 * t ≤ p.verifyMass)
    (hsmall : Φ + t ≤ 1 / 2) (hξ : ξ ≤ w / 8)
    (hcounts : ∀ j, 0.9 * w * n ≤ (cluster (labels ω) j).card)
    (hbad : (corrupted ω).card ≤ ξ * n)
    (hwin : ∀ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
        e.lower ≤ e.statistic.evalQ (x l) ∧ e.statistic.evalQ (x l) ≤ e.upper).card : ℝ) ≤
          t * (cluster (labels ω) j).card)
    (hleft : ∃ j ∈ I, (((cluster (labels ω) j \ corrupted ω) ∩ e.right x).card : ℝ) ≤
      t * (cluster (labels ω) j).card)
    (hright : ∃ j ∈ I, (((cluster (labels ω) j \ corrupted ω) ∩ e.left x).card : ℝ) ≤
      t * (cluster (labels ω) j).card) : Verify p x e := by
  classical
  have hwindow : (e.windowCount x : ℝ) ≤ (p.verifyMass : ℝ) * e.parent.card := by
    apply (window_count_le ω e.parent I δ t _ hδ hhalf ht hwin).trans
    exact mul_le_mul_of_nonneg_right hverify (Nat.cast_nonneg _)
  refine ⟨by exact_mod_cast hwindow, ?_, ?_⟩
  · obtain ⟨j, hj, hwrong⟩ := hleft
    have hh := side_large ω e.parent (e.left x) (e.right x) I j w Φ t ξ hj
      (split_partition e x).2 hleak (hcounts j) hbad hwrong hsmall hξ
    rw [← hw] at hh
    exact_mod_cast hh
  · obtain ⟨j, hj, hwrong⟩ := hright
    have hh := side_large ω e.parent (e.right x) (e.left x) I j w Φ t ξ hj
      (by rw [Finset.union_comm]; exact (split_partition e x).2)
      hleak (hcounts j) hbad hwrong hsmall hξ
    rw [← hw] at hh
    exact_mod_cast hh


end

end ABBKS26.Tree.RefineAux
