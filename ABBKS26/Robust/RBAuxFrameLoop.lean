module

public import ABBKS26.Robust.RBAuxApprox
public import ABBKS26.Prob.UniformQuad

/-! Estimates for frames selected using only the observed block. -/

@[expose] public section

namespace ABBKS26.Robust.RBAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators MatrixOrder Topology

variable {n k d : ℕ}

private theorem reference_cov_qform (D : Reference n k d) (u : Vec d) :
    qform D.cov u = (D.reference.card : ℝ)⁻¹ *
      ∑ l ∈ D.reference, (u ⬝ᵥ (D.clean l - D.mean)) ^ 2 := by
  simp only [Reference.cov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_comm u, pow_two]


private theorem retained_sum (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (w f : Fin n → ℝ) :
    (∑ l ∈ D.reference, (if l ∈ D.good then w l else 0) * f l) =
      ∑ l ∈ D.good, w l * f l := by
  classical
  calc
    _ = ∑ l ∈ D.good, (if l ∈ D.good then w l else 0) * f l :=
      (Finset.sum_subset hD.2.1 (fun l _ hl ↦ by simp [hl])).symm
    _ = _ := Finset.sum_congr rfl fun l hl ↦ by simp [hl]

private theorem reference_centered_sum (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (u : Vec d) : (∑ l ∈ D.reference, u ⬝ᵥ (D.clean l - D.mean)) = 0 := by
  have hN : (D.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hD.2.2.2.2.1).ne'
  simp only [dotProduct_sub, Finset.sum_sub_distrib, Reference.mean,
    dotProduct_smul, smul_eq_mul, ← dotProduct_sum, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

private theorem weighted_cov_qform (D : Reference n k d) (st : FilterState n d)
    (u : Vec d) :
    qform (weightedCov D st) u = (st.mass D.block)⁻¹ *
      ∑ l ∈ D.block, st.weights l * (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
  simp only [weightedCov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_comm u]
  ring


/-- The retained block controls covariance before the eligibility cutoff. -/
theorem retained_covariance_lower
    (D : Reference n k d) (st : FilterState n d) (π : ℝ) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000))
    (hw : ∀ l, 0 ≤ st.weights l ∧ st.weights l ≤ 1)
    (hrem : D.reference.card - st.mass D.good ≤ π * D.reference.card / 100)
    (hW : st.mass D.block ≤ (11 / 10 : ℝ) * D.reference.card)
    (hW0 : 0 < st.mass D.block) :
    LE ((0.68 : ℝ) • D.cov) (weightedCov D st) := by
  classical
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hπ : 0 < π := hD.1.1
  have hπ1 : π ≤ 1 := by
    obtain ⟨l, _⟩ := hD.2.2.2.2.1
    calc
      _ ≤ D.model.weight (D.label l) := hD.1.2.1 _
      _ ≤ ∑ j, D.model.weight j := Finset.single_le_sum
        (fun j _ ↦ hπ.le.trans (hD.1.2.1 j)) (Finset.mem_univ _)
      _ = 1 := hD.1.2.2.1
  intro u
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
  change (0.68 : ℝ) * qform D.cov u ≤ qform (weightedCov D st) u
  let g := qform D.cov u
  let x := fun l ↦ u ⬝ᵥ (D.clean l - D.mean)
  let a := u ⬝ᵥ (st.center - D.mean)
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  have hg : 0 ≤ g := by
    simpa only [g, qform, star_trivial] using
      hD.2.2.2.2.2.1.posSemidef.dotProduct_mulVec_nonneg u
  have hr (l : Fin n) (_ : l ∈ D.reference) : 0 ≤ r l ∧ r l ≤ 1 := by
    dsimp only [r]
    split_ifs
    · exact hw l
    · norm_num
  have hsecond : (∑ l ∈ D.reference, x l ^ 2) = N * g := by
    dsimp only [g]
    rw [reference_cov_qform]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hfourth : (∑ l ∈ D.reference, x l ^ 4) ≤ N * (4 / π) * g ^ 2 := by
    have hh := (div_le_iff₀ hN).mp (directional_fourth D π hD hres u)
    dsimp only [g, x]
    nlinarith only [hh]
  have hrmass : (∑ l ∈ D.reference, (1 - r l)) ≤ N * π / 100 := by
    have heq : (∑ l ∈ D.reference, r l) = st.mass D.good := by
      simpa only [r, mul_one, FilterState.mass] using
        retained_sum D π hD st.weights (fun _ ↦ 1)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, heq]
    change N - st.mass D.good ≤ _
    nlinarith only [hrem]
  have hret := FilterAux.retained_variance_lower D.reference r x hr N g π a hN rfl hg
    ⟨hπ, hπ1⟩ (reference_centered_sum D π hD u) hsecond hfourth hrmass
  have hsum : (∑ l ∈ D.reference, r l * (x l - a) ^ 2) ≤
      ∑ l ∈ D.block, st.weights l * (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
    rw [retained_sum D π hD]
    calc
      _ = ∑ l ∈ D.good, st.weights l *
          (u ⬝ᵥ (D.observed l - st.center)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hD.2.2.2.1 l hl]
        congr 2
        dsimp only [x, a]
        rw [← dotProduct_sub]
        congr 1
        abel
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1
        (fun l _ _ ↦ mul_nonneg (hw l).1 (sq_nonneg _))
  have hcov : (3 / 4 : ℝ) * N * g ≤ W * qform (weightedCov D st) u := by
    rw [weighted_cov_qform]
    change _ ≤ W * (W⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hW0.ne', one_mul]
    exact hret.trans hsum
  have hh := mul_le_mul_of_nonneg_right hW hg
  apply (mul_le_mul_iff_right₀ hW0).mp
  change W * ((0.68 : ℝ) * g) ≤ W * qform (weightedCov D st) u
  nlinarith only [hcov, hh, mul_nonneg hN.le hg]

theorem contamination_small_pi (D : Reference n k d) (π R : ℝ)
    (hπ : 0 < π) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ maxContamination π R) :
    D.contamination ≤ π / 10000 := by
  have hε : 0 ≤ D.contamination := by
    unfold Reference.contamination
    positivity
  have hσ : 0 < sigmaSq π R :=
    add_pos_of_pos_of_nonneg (div_pos (by norm_num) (sq_pos_of_pos hπ))
      (mul_nonneg (by norm_num) (sq_nonneg R))
  have hb : D.contamination * (64000 * sigmaSq π R) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 64000 * sigmaSq π R)).mp he
  have hσπ : 600 ≤ sigmaSq π R * π ^ 2 := by
    dsimp only [sigmaSq]
    have hh : (600 / π ^ 2 : ℝ) * π ^ 2 = 600 :=
      div_mul_cancel₀ _ (sq_pos_of_pos hπ).ne'
    nlinarith only [hh, mul_nonneg (sq_nonneg R) (sq_nonneg π)]
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg π)
  have hh' := mul_le_mul_of_nonneg_left hσπ (by positivity : 0 ≤ 64000 * D.contamination)
  have hπsq : π ^ 2 ≤ π := by nlinarith only [hπ.le, hπ1]
  linarith only [hh, hh', hπsq, hε]

/-- Mass bounds from the computable total-weight eligibility check. -/
theorem eligible_mass_bounds
    (D : Reference n k d) (st : FilterState n d) (π : ℝ) (hD : D.Valid π)
    (hπ1 : π ≤ 1) (he : D.contamination ≤ π / 10000)
    (hw : ∀ l, 0 ≤ st.weights l ∧ st.weights l ≤ 1)
    (hel : D.block.card - st.mass D.block ≤ π * D.block.card / 130) :
    D.reference.card - st.mass D.good ≤ π * D.reference.card / 100 ∧
      st.mass D.block ≤ (11 / 10 : ℝ) * D.reference.card ∧
      (9 / 10 : ℝ) * D.reference.card ≤ st.mass D.block ∧
      (D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good) ≤
        2 * D.contamination := by
  classical
  let N : ℝ := D.reference.card
  let m : ℝ := D.block.card
  let ε := D.contamination
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hε : 0 ≤ ε := by dsimp only [ε, Reference.contamination]; positivity
  have he1 : ε ≤ 1 / 10000 := by linarith only [he, hπ1]
  have hgB : (1 - ε) * m ≤ D.good.card := by
    by_cases hm : m = 0
    · rw [hm, mul_zero]
      positivity
    have hm0 : 0 < m := lt_of_le_of_ne (by positivity) (Ne.symm hm)
    have hh : ((D.block \ D.good).card : ℝ) / m ≤ ε :=
      le_max_left _ _
    have hc := Finset.card_sdiff_add_card_eq_card hD.2.2.1
    have hcR : ((D.block \ D.good).card : ℝ) + D.good.card = m := by
      dsimp only [N, m]
      exact_mod_cast hc
    have hh' := (div_le_iff₀ hm0).mp hh
    nlinarith only [hh', hcR]
  have hgR : (1 - ε) * N ≤ D.good.card := by
    have hh : ((D.reference \ D.good).card : ℝ) / N ≤ ε :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hc := Finset.card_sdiff_add_card_eq_card hD.2.1
    have hcR : ((D.reference \ D.good).card : ℝ) + D.good.card = N := by
      dsimp only [N, m]
      exact_mod_cast hc
    have hh' := (div_le_iff₀ hN).mp hh
    nlinarith only [hh', hcR]
  have hgN : (D.good.card : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast Finset.card_le_card hD.2.1
  have hmN : m ≤ (101 / 100 : ℝ) * N := by
    nlinarith only [hgB, hgN, he1, mul_nonneg (sub_nonneg.mpr he1)
      (show 0 ≤ m by positivity)]
  have hdrop : (D.good.card : ℝ) - st.mass D.good ≤
      m - st.mass D.block := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1
      (f := fun l ↦ 1 - st.weights l) (fun l _ _ ↦ sub_nonneg.mpr (hw l).2)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      FilterState.mass] using hh
  have hrem : N - st.mass D.good ≤ π * N / 100 := by
    have h₁ := mul_le_mul_of_nonneg_left hmN hD.1.1.le
    have h₂ := mul_le_mul_of_nonneg_right he hN.le
    dsimp only [ε] at hgR
    dsimp only [m] at hdrop h₁
    nlinarith only [hgR, hdrop, hel, h₁, h₂, mul_pos hD.1.1 hN]
  have hgood : st.mass D.good ≤ st.mass D.block :=
    Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1 (fun l _ _ ↦ (hw l).1)
  have hupper : st.mass D.block ≤ (11 / 10 : ℝ) * N := by
    have hh : st.mass D.block ≤ m := by
      simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_le_sum (fun l (_ : l ∈ D.block) ↦ (hw l).2)
    linarith only [hh, hmN, hN.le]
  have hlower : (9 / 10 : ℝ) * N ≤ st.mass D.block := by
    have hh := mul_le_mul_of_nonneg_right hπ1 hN.le
    linarith only [hrem, hgood, hh, hN.le]
  refine ⟨hrem, hupper, hlower, ?_⟩
  have hbad : st.mass (D.block \ D.good) ≤ ε * m := by
    have hh : st.mass (D.block \ D.good) ≤ ((D.block \ D.good).card : ℝ) := by
      simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_le_sum (fun l (_ : l ∈ D.block \ D.good) ↦ (hw l).2)
    have hc := Finset.card_sdiff_add_card_eq_card hD.2.2.1
    have hcR : ((D.block \ D.good).card : ℝ) + D.good.card = m := by
      dsimp only [N, m]
      exact_mod_cast hc
    nlinarith only [hh, hcR, hgB]
  rw [← div_eq_inv_mul, div_le_iff₀ hN]
  have hh := mul_le_mul_of_nonneg_left hmN hε
  nlinarith only [hbad, hh, mul_nonneg hε hN.le]

private theorem reference_statistic_shift (D : Reference n k d) (st : FilterState n d)
    (π : ℝ) (hD : D.Valid π)
    (hw : ∀ l, 0 ≤ st.weights l ∧ st.weights l ≤ 1)
    (hbad : (D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good) ≤
      2 * D.contamination)
    (hmass : 0.9 * D.reference.card ≤ st.mass D.block)
    (he : D.contamination ≤ 1 / 400)
    (x y : Fin n → ℝ) (hxy : ∀ l ∈ D.good, x l = y l) :
    let μG := (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, x l
    let μw := (st.mass D.block)⁻¹ * ∑ l ∈ D.block, st.weights l * y l
    let VG := (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2
    let Vw := (st.mass D.block)⁻¹ *
      ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2
    (μw - μG) ^ 2 ≤
      4 * ((D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)) * Vw +
      5 * ((D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good)) * VG := by
  classical
  let N : ℝ := D.reference.card
  let W := st.mass D.block
  let r := fun l ↦ if l ∈ D.good then st.weights l else 0
  let G : Finset (Fin n ⊕ Fin n) := D.reference.map Function.Embedding.inl
  let B : Finset (Fin n ⊕ Fin n) := (D.block \ D.good).map Function.Embedding.inr
  let z := Sum.elim x y
  let w := Sum.elim r st.weights
  let μG := N⁻¹ * ∑ l ∈ D.reference, x l
  let μw := W⁻¹ * ∑ l ∈ D.block, st.weights l * y l
  let VG := N⁻¹ * ∑ l ∈ D.reference, (x l - μG) ^ 2
  let Vw := W⁻¹ * ∑ l ∈ D.block, st.weights l * (y l - μw) ^ 2
  let β := N⁻¹ * st.mass (D.block \ D.good)
  let ρ := N⁻¹ * (N - st.mass D.good)
  let ω := N⁻¹ * W
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hω : 0.9 ≤ ω := by
    dsimp only [ω]
    rw [← div_eq_inv_mul, le_div_iff₀ hN]
    exact hmass
  have hβ : β ≤ ω / 16 := by
    change β ≤ 2 * D.contamination at hbad
    linarith only [hbad, he, hω]
  have hm : W = st.mass D.good + st.mass (D.block \ D.good) := by
    have hh := Finset.sum_sdiff hD.2.2.1 (f := st.weights)
    dsimp only [W, FilterState.mass]
    linarith only [hh]
  have hr : (∑ l ∈ D.reference, r l) = st.mass D.good := by
    simpa only [r, mul_one, FilterState.mass] using
      retained_sum D π hD st.weights (fun _ ↦ 1)
  have hsum (f g : Fin n → ℝ) (hfg : ∀ l ∈ D.good, f l = g l) :
      (∑ l ∈ D.reference, r l * f l) +
        (∑ l ∈ D.block \ D.good, st.weights l * g l) =
      ∑ l ∈ D.block, st.weights l * g l := by
    rw [retained_sum D π hD]
    have hgood : (∑ l ∈ D.good, st.weights l * f l) =
        ∑ l ∈ D.good, st.weights l * g l :=
      Finset.sum_congr rfl fun l hl ↦ by rw [hfg l hl]
    rw [hgood, add_comm, Finset.sum_sdiff hD.2.2.1]
  have hdis : Disjoint G B := Finset.disjoint_map_inl_map_inr _ _
  have hwhole (f : (Fin n ⊕ Fin n) → ℝ) :
      (∑ l ∈ G ∪ B, f l) =
        (∑ l ∈ D.reference, f (Sum.inl l)) +
          ∑ l ∈ D.block \ D.good, f (Sum.inr l) := by
    rw [Finset.sum_union hdis]
    simp only [G, B, Finset.sum_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply]
  have hweight : (∑ l ∈ G ∪ B, w l) = W := by
    rw [hwhole]
    change (∑ l ∈ D.reference, r l) + st.mass (D.block \ D.good) = W
    rw [hr, hm]
  apply FilterAux.weighted_mean_shift_general z w G B hdis
    (fun l ↦ by
      cases l with
      | inl l =>
        change 0 ≤ r l ∧ r l ≤ 1
        dsimp only [r]
        split_ifs
        · exact hw l
        · norm_num
      | inr l => exact hw l)
    hD.2.2.2.2.1.map μG μw VG Vw β ρ ω
  · simp only [G, Finset.card_map, Finset.sum_map, z, Sum.elim_inl,
      Function.Embedding.inl_apply]
    rfl
  · rw [hweight, hwhole]
    change μw = W⁻¹ * ((∑ l ∈ D.reference, r l * x l) +
      ∑ l ∈ D.block \ D.good, st.weights l * y l)
    rw [hsum x y hxy]
  · simp only [G, B, Finset.card_map, Finset.sum_map, w, Sum.elim_inr,
      Function.Embedding.inr_apply]
    rfl
  · simp only [G, Finset.card_map, Finset.sum_map, w, Sum.elim_inl,
      Function.Embedding.inl_apply, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, hr]
    rfl
  · dsimp only [ω, ρ, β]
    rw [hm]
    field_simp
    ring
  · exact hω
  · exact hβ
  · simp only [G, Finset.card_map, Finset.sum_map, z, Sum.elim_inl,
      Function.Embedding.inl_apply]
    rfl
  · rw [hweight, hwhole]
    change Vw = W⁻¹ * ((∑ l ∈ D.reference, r l * (x l - μw) ^ 2) +
      ∑ l ∈ D.block \ D.good, st.weights l * (y l - μw) ^ 2)
    rw [hsum _ _ (fun l hl ↦ by rw [hxy l hl])]


/-- Eligibility controls both the reference covariance and the reference mean in a frame. -/
theorem eligible_frame_bounds
    (D : Reference n k d) (st : FilterState n d) (π R : ℝ) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000)) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ maxContamination π R)
    (hw : ∀ l, 0 ≤ st.weights l ∧ st.weights l ≤ 1)
    (hel : D.block.card - st.mass D.block ≤ π * D.block.card / 130)
    (hf : FrameNormalized D st)
    (hcenter : st.center = (st.mass D.block)⁻¹ •
      ∑ l ∈ D.block, st.weights l • D.observed l) :
    LE (st.frame * D.cov * st.frameᵀ) (6 • (1 : Mat d)) ∧
      sqnorm (st.frame *ᵥ (st.center - D.mean)) ≤ 1 := by
  have heπ := contamination_small_pi D π R hD.1.1 hπ1 he
  obtain ⟨hrem, hupper, hlower, hbad⟩ := eligible_mass_bounds D st π hD hπ1 heπ hw hel
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hW : 0 < st.mass D.block := by linarith only [hlower, hN]
  have hcov := retained_covariance_lower D st π hD hres hw hrem hupper hW
  have hC (v : Vec d) :
      qform (st.frame * weightedCov D st * st.frameᵀ) v ≤ 4 * sqnorm v := by
    obtain ⟨q, hq, hframe⟩ := hf.1
    rw [hframe]
    simp only [qform, mulVec_diagonal, sqnorm, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_right (hq i).2.le (sq_nonneg (v i))]
  have hM (v : Vec d) : qform (st.frame * D.cov * st.frameᵀ) v ≤ 6 * sqnorm v := by
    have hh := hcov (st.frameᵀ *ᵥ v)
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    change (0.68 : ℝ) * qform D.cov (st.frameᵀ *ᵥ v) ≤
      qform (weightedCov D st) (st.frameᵀ *ᵥ v) at hh
    rw [← RBAux.qform_conjugate, ← RBAux.qform_conjugate] at hh
    linarith only [hh, hC v, Rounding.DetRoundAux.sqnorm_nonneg v]
  refine ⟨?_, ?_⟩
  · intro v
    simp only [qform, dotProduct_smul, smul_eq_mul, nsmul_eq_mul,
      Matrix.mul_one, Nat.cast_ofNat, Matrix.ofNat_mulVec]
    exact hM v
  · let δ := st.frame *ᵥ (st.center - D.mean)
    let β := (D.reference.card : ℝ)⁻¹ * st.mass (D.block \ D.good)
    let ρ := (D.reference.card : ℝ)⁻¹ * (D.reference.card - st.mass D.good)
    have hε : D.contamination ≤ 1 / 10000 := by linarith only [heπ, hπ1]
    have hβ : β ≤ 2 * D.contamination := hbad
    have hρ : ρ ≤ π / 100 := by
      dsimp only [ρ]
      rw [← div_eq_inv_mul, div_le_iff₀ hN]
      linarith only [hrem]
    have hβ0 : 0 ≤ β := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun l _ ↦ (hw l).1
    have hρ0 : 0 ≤ ρ := by
      apply mul_nonneg (by positivity)
      apply sub_nonneg.mpr
      calc
        st.mass D.good ≤ (D.good.card : ℝ) := by
          simpa only [FilterState.mass, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_le_sum (fun l (_ : l ∈ D.good) ↦ (hw l).2)
        _ ≤ _ := by exact_mod_cast Finset.card_le_card hD.2.1
    let u := st.frameᵀ *ᵥ δ
    have hh := reference_statistic_shift D st π hD hw hbad (by norm_num at hlower ⊢; exact hlower)
      (hε.trans (by norm_num)) (fun l ↦ u ⬝ᵥ D.clean l)
      (fun l ↦ u ⬝ᵥ D.observed l) (fun l hl ↦ by rw [hD.2.2.2.1 l hl])
    have hμG : (D.reference.card : ℝ)⁻¹ *
        (∑ l ∈ D.reference, u ⬝ᵥ D.clean l) = u ⬝ᵥ D.mean := by
      simp only [Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
    have hμw : (st.mass D.block)⁻¹ *
        (∑ l ∈ D.block, st.weights l * (u ⬝ᵥ D.observed l)) = u ⬝ᵥ st.center := by
      rw [hcenter]
      simp only [dotProduct_smul, dotProduct_sum, smul_eq_mul]
    dsimp only at hh
    rw [hμG, hμw] at hh
    simp only [← dotProduct_sub] at hh
    rw [← reference_cov_qform, ← weighted_cov_qform] at hh
    have hdot : u ⬝ᵥ (st.center - D.mean) = sqnorm δ := by
      dsimp only [u, sqnorm]
      rw [dotProduct_mulVec, ← mulVec_transpose]
    rw [hdot] at hh
    change sqnorm δ ^ 2 ≤ 4 * β * qform (weightedCov D st) u +
      5 * ρ * qform D.cov u at hh
    dsimp only [u] at hh
    rw [← RBAux.qform_conjugate, ← RBAux.qform_conjugate] at hh
    have h₁ := mul_le_mul_of_nonneg_left (hC δ) (by positivity : 0 ≤ 4 * β)
    have h₂ := mul_le_mul_of_nonneg_left (hM δ) (by positivity : 0 ≤ 5 * ρ)
    have h₃ := mul_le_mul_of_nonneg_right hβ
      (Rounding.DetRoundAux.sqnorm_nonneg δ)
    have h₄ := mul_le_mul_of_nonneg_right hρ
      (Rounding.DetRoundAux.sqnorm_nonneg δ)
    have h₅ := mul_le_mul_of_nonneg_right hε
      (Rounding.DetRoundAux.sqnorm_nonneg δ)
    have h₆ := mul_le_mul_of_nonneg_right hπ1
      (Rounding.DetRoundAux.sqnorm_nonneg δ)
    have hn := Rounding.DetRoundAux.sqnorm_nonneg δ
    change sqnorm δ ≤ 1
    nlinarith only [hh, h₁, h₂, h₃, h₄, h₅, h₆, hn]

private theorem projected_moment (D : Reference n k d) (θ : ℝ)
    (hres : D.Resilient 4 θ) (i : Fin d) (u a : Vec d) (j : Fin k)
    (r : ℕ) (hr : r ≤ 4) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ r -
      IdCov.hmom r (u ⬝ᵥ (D.model.mean j - a)) (qform (D.model.cov j) u)| ≤
      (θ / (d + 1 : ℝ) ^ 8) *
        (1 + |u ⬝ᵥ (D.model.mean j - a)| + |qform (D.model.cov j) u|) ^ r := by
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  have h := hres (vecMulVec (Pi.single i 1) u) a j r hr
  dsimp only at h ⊢
  simp only [FilterAux.lin_projection, FilterAux.quad_projection] at h
  have he : (C (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (C (u ⬝ᵥ (D.clean l - a)) * X i) ^ r) -
      IdCov.hmom r (C (u ⬝ᵥ (D.model.mean j - a)) * X i)
        (C (qform (D.model.cov j) u) * X i ^ 2) =
      C ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ r -
        IdCov.hmom r (u ⬝ᵥ (D.model.mean j - a)) (qform (D.model.cov j) u)) *
          (X i : RPoly d) ^ r := by
    rw [FilterAux.hmom_monomial]
    simp only [mul_pow, ← map_pow, ← Finset.sum_mul, ← map_sum]
    rw [← mul_assoc, ← C_mul, ← sub_mul, ← C_sub]
  change SoS.coeffNorm1 ((C (Cj.card : ℝ)⁻¹ *
    ∑ l ∈ Cj, (C (u ⬝ᵥ (D.clean l - a)) * X i) ^ r) - _) ≤ _ at h
  rw [he] at h
  simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, X_pow_eq_monomial,
    SoS.coeffNorm1_monomial, abs_one, mul_one] using h

private theorem qform_scale (A : Mat d) (c : ℝ) (u : Vec d) :
    qform A (c • u) = c ^ 2 * qform A u := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private theorem component_moments (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π)
    (hθ : 0 ≤ θ) (hres : D.Resilient 4 θ) (i : Fin d) (u a : Vec d)
    (hu : u ≠ 0) (j : Fin k) :
    let Cj := D.reference.filter (fun l ↦ D.label l = j)
    let m := (u ⬝ᵥ (D.model.mean j - a)) ^ 2 + qform (D.model.cov j) u
    (1 - 9 * (θ / (d + 1 : ℝ) ^ 8)) * m ≤
        (Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2 ∧
      (Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4 ≤
        (3 + 81 * (θ / (d + 1 : ℝ) ^ 8)) * m ^ 2 := by
  let Cj := D.reference.filter (fun l ↦ D.label l = j)
  let μ := u ⬝ᵥ (D.model.mean j - a)
  let S := qform (D.model.cov j) u
  have hS : 0 < S := by
    simpa only [S, qform, star_trivial] using (hD.1.2.2.2 j).dotProduct_mulVec_pos hu
  apply FilterAux.scalar_moment_bounds _ _ μ S _ hS (by positivity)
  · intro c
    have h := projected_moment D θ hres i (c • u) a j 2 (by omega)
    dsimp only at h
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      qform_scale, FilterAux.hmom_two] at h
    have he : (Cj.card : ℝ)⁻¹ * (c ^ 2 * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2) -
        ((c * μ) ^ 2 + c ^ 2 * S) =
        c ^ 2 * ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 2 -
          (μ ^ 2 + S)) := by ring
    simp only [μ, S, mul_pow] at he
    rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg c) hS.le)] at h
    exact h
  · intro c
    have h := projected_moment D θ hres i (c • u) a j 4 (by omega)
    dsimp only at h
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      qform_scale, FilterAux.hmom_four] at h
    have he : (Cj.card : ℝ)⁻¹ * (c ^ 4 * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
        ((c * μ) ^ 4 + 6 * (c * μ) ^ 2 * (c ^ 2 * S) + 3 * (c ^ 2 * S) ^ 2) =
        c ^ 4 * ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
          c ^ 4 * (μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2) := by ring
    simp only [μ, S, mul_pow] at he
    rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg c) hS.le)] at h
    dsimp only [μ, S, Cj]
    linarith only [(abs_le.mp h).2]

private theorem component_card_pos (D : Reference n k d) (π : ℝ)
    (hD : D.Valid π) (j : Fin k) :
    0 < (D.reference.filter (fun l ↦ D.label l = j)).card := by
  have hw : 0 < D.model.weight j := hD.1.1.trans_le (hD.1.2.1 j)
  rw [hD.2.2.2.2.2.2 j] at hw
  by_contra hn
  have he : (D.reference.filter (fun l ↦ D.label l = j)).card = 0 := by omega
  simp [he] at hw


private theorem reference_partition (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (f : Fin n → ℝ) :
    (∑ j, D.model.weight j *
      ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j), f l) =
      (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, f l := by
  classical
  have he (j : Fin k) : D.model.weight j *
      ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ =
      (D.reference.card : ℝ)⁻¹ := by
    rw [hD.2.2.2.2.2.2 j, div_eq_mul_inv]
    have hc : ((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (component_card_pos D π hD j).ne'
    field_simp
  simp only [he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem resilience_delta (θ : ℝ) (hθ : 0 ≤ θ) (i : Fin d) :
    0 ≤ θ / (d + 1 : ℝ) ^ 8 ∧ θ / (d + 1 : ℝ) ^ 8 ≤ θ / 256 := by
  have hd : (2 : ℝ) ≤ d + 1 := by
    have hn : 1 ≤ d := by have hi := i.isLt; omega
    exact_mod_cast (by omega : 2 ≤ d + 1)
  have hpow : (256 : ℝ) ≤ (d + 1 : ℝ) ^ 8 := by
    exact_mod_cast (show (2 : ℝ) ^ 8 ≤ (d + 1 : ℝ) ^ 8 from
      pow_le_pow_left₀ (by norm_num) hd 8)
  exact ⟨by positivity, div_le_div_of_nonneg_left hθ (by norm_num) hpow⟩

private theorem component_second_le (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (u : Vec d) (j : Fin k) :
    D.model.weight j *
      (((D.reference.filter (fun l ↦ D.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j),
          (u ⬝ᵥ (D.clean l - D.mean)) ^ 2) ≤ qform D.cov u := by
  rw [reference_cov_qform, ← reference_partition D π hD]
  rw [← mul_assoc]
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro i _
  exact mul_nonneg (mul_nonneg (hD.1.1.le.trans (hD.1.2.1 i)) (by positivity))
    (Finset.sum_nonneg fun l _ ↦ sq_nonneg _)

private theorem population_second_le (D : Reference n k d) (π θ : ℝ) (hD : D.Valid π)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : D.Resilient 4 θ) (u : Vec d) (j : Fin k) :
    D.model.weight j * ((u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 +
      qform (D.model.cov j) u) ≤ (1 + θ) * qform D.cov u := by
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := (u ⬝ᵥ (D.model.mean j - D.mean)) ^ 2 + qform (D.model.cov j) u
  have hδ := resilience_delta θ hθ.1 i
  have hw : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hm : 0 ≤ m := add_nonneg (sq_nonneg _) (by
    simpa only [qform, star_trivial] using
      (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
  have hprod : 1 ≤ (1 + θ) * (1 - 9 * δ) := by
    dsimp only [δ]
    nlinarith only [hδ.1, hδ.2, hθ.1,
      mul_nonneg (sub_nonneg.mpr hθ.2) hδ.1]
  have he := (component_moments D π θ hD hθ.1 hres i u D.mean hu j).1
  have he' : (1 - 9 * δ) * (D.model.weight j * m) ≤ qform D.cov u := by
    have hh := mul_le_mul_of_nonneg_left he hw
    have hb := component_second_le D π hD u j
    dsimp only [δ, m]
    nlinarith only [hh, hb]
  calc
    _ ≤ (1 + θ) * (1 - 9 * δ) * (D.model.weight j * m) :=
      le_mul_of_one_le_left (mul_nonneg hw hm) hprod
    _ = (1 + θ) * ((1 - 9 * δ) * (D.model.weight j * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he' (by linarith only [hθ.1])


/-- A public form of the population second-moment estimate for the wrapper. -/
theorem population_second_frame (D : Reference n k d) (π : ℝ)
    (hD : D.Valid π) (hres : D.Resilient 4 (1 / 10000)) (T : Mat d)
    (hM : LE (T * D.cov * Tᵀ) (6 • (1 : Mat d))) (j : Fin k) (v : Vec d) :
    D.model.weight j * (v ⬝ᵥ (T *ᵥ (D.model.mean j - D.mean))) ^ 2 ≤
      (601 / 100 : ℝ) * sqnorm v := by
  have hh := population_second_le D π (1 / 10000) hD (by norm_num) hres
    (Tᵀ *ᵥ v) j
  have hcov : 0 ≤ qform (D.model.cov j) (Tᵀ *ᵥ v) := by
    simpa only [qform, star_trivial] using
      (hD.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg (Tᵀ *ᵥ v)
  have hw : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hdot : (Tᵀ *ᵥ v) ⬝ᵥ (D.model.mean j - D.mean) =
      v ⬝ᵥ (T *ᵥ (D.model.mean j - D.mean)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose]
  rw [hdot, ← RBAux.qform_conjugate T D.cov] at hh
  have hm := hM v
  simp only [qform, dotProduct_smul, smul_eq_mul, nsmul_eq_mul,
    Matrix.mul_one, Nat.cast_ofNat, Matrix.ofNat_mulVec] at hm
  change qform (T * D.cov * Tᵀ) v ≤ 6 * sqnorm v at hm
  nlinarith only [hh, hm, mul_nonneg hw hcov,
    Rounding.DetRoundAux.sqnorm_nonneg v]

namespace FrameLoop

variable {m : ℕ}

def mass (w : Fin m → ℝ) : ℝ := ∑ i, w i

def center (x : Fin m → Vec d) (w : Fin m → ℝ) : Vec d :=
  (mass w)⁻¹ • ∑ i, w i • x i

def covariance (x : Fin m → Vec d) (w : Fin m → ℝ) : Mat d :=
  (mass w)⁻¹ • ∑ i, w i • vecMulVec (x i - center x w) (x i - center x w)


def power (d : ℕ) : ℕ := 2 * (d * d + 1)

theorem power_spec (d : ℕ) : Even (power d) ∧ 2 ≤ power d ∧
    (d * d : ℝ) ^ (1 / (power d : ℝ)) ≤ Real.sqrt 2 := by
  refine ⟨even_two_mul _, by unfold power; omega, ?_⟩
  have hp : power d ≠ 0 := by unfold power; omega
  have hn : (d * d : ℝ) ≤ 2 ^ (d * d + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := d * d)).le.trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ (d * d)))
  have he : Real.sqrt 2 ^ power d = (2 : ℝ) ^ (d * d + 1) := by
    rw [power, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (Real.sqrt 2 ^ power d) ^ (1 / (power d : ℝ)) := by
      apply Real.rpow_le_rpow (by positivity) (he.symm ▸ hn) (by positivity)
    _ = Real.sqrt 2 := by
      simpa only [one_div] using Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 2) hp

theorem covariance_psd {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (v : ι → Vec d) :
    ((∑ i, w i)⁻¹ • ∑ i, w i • vecMulVec (v i) (v i)).PosSemidef := by
  apply PosSemidef.smul _ (inv_nonneg.mpr (Finset.sum_nonneg fun i _ ↦ hw i))
  apply posSemidef_sum
  intro i _
  apply PosSemidef.smul _ (hw i)
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (v i)


def liftWeights (idx : Fin m → Fin n) (w : Fin m → ℝ) (l : Fin n) : ℝ :=
  ∑ i, if idx i = l then w i else 0

theorem liftWeights_apply (idx : Fin m → Fin n) (hinj : Function.Injective idx)
    (w : Fin m → ℝ) (i : Fin m) : liftWeights idx w (idx i) = w i := by
  classical
  simp only [liftWeights, hinj.eq_iff]
  simp

theorem liftWeights_zero (idx : Fin m → Fin n) (w : Fin m → ℝ) (l : Fin n)
    (hl : l ∉ Set.range idx) : liftWeights idx w l = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun he ↦ hl ⟨i, he⟩)

theorem liftWeights_bounds (idx : Fin m → Fin n) (hinj : Function.Injective idx)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    ∀ l, 0 ≤ liftWeights idx w l ∧ liftWeights idx w l ≤ 1 := by
  intro l
  by_cases hl : l ∈ Set.range idx
  · obtain ⟨i, rfl⟩ := hl
    simpa only [liftWeights_apply idx hinj] using hw i
  · simp only [liftWeights_zero idx w l hl]
    norm_num

theorem sum_index {α : Type*} [AddCommMonoid α]
    (B : Finset (Fin n)) (idx : Fin m → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ B}) (f : Fin n → α) :
    (∑ l ∈ B, f l) = ∑ i, f (idx i) := by
  classical
  symm
  apply Finset.sum_bij (fun i _ ↦ idx i)
  · intro i _
    have hh : idx i ∈ Set.range idx := ⟨i, rfl⟩
    rwa [hrange] at hh
  · intro i _ j _ he
    exact hinj he
  · intro l hl
    have hh : l ∈ Set.range idx := by rwa [hrange]
    obtain ⟨i, hi⟩ := hh
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    rfl


theorem reference_count_bounds (D : Reference n k d) (π : ℝ) (hD : D.Valid π)
    (he : D.contamination ≤ 1 / 10000) :
    (1 - D.contamination) * D.block.card ≤ D.good.card ∧
      (1 - D.contamination) * D.reference.card ≤ D.good.card ∧
      (D.block.card : ℝ) ≤ (101 / 100 : ℝ) * D.reference.card := by
  classical
  let N : ℝ := D.reference.card
  let m : ℝ := D.block.card
  let ε := D.contamination
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have he1 : ε ≤ 1 / 10000 := he
  have hgB : (1 - ε) * m ≤ D.good.card := by
    by_cases hm : m = 0
    · rw [hm, mul_zero]
      positivity
    have hm0 : 0 < m := lt_of_le_of_ne (by positivity) (Ne.symm hm)
    have hh : ((D.block \ D.good).card : ℝ) / m ≤ ε :=
      le_max_left _ _
    have hc := Finset.card_sdiff_add_card_eq_card hD.2.2.1
    have hcR : ((D.block \ D.good).card : ℝ) + D.good.card = m := by
      dsimp only [N, m]
      exact_mod_cast hc
    have hh' := (div_le_iff₀ hm0).mp hh
    nlinarith only [hh', hcR]
  have hgR : (1 - ε) * N ≤ D.good.card := by
    have hh : ((D.reference \ D.good).card : ℝ) / N ≤ ε :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hc := Finset.card_sdiff_add_card_eq_card hD.2.1
    have hcR : ((D.reference \ D.good).card : ℝ) + D.good.card = N := by
      dsimp only [N, m]
      exact_mod_cast hc
    have hh' := (div_le_iff₀ hN).mp hh
    nlinarith only [hh', hcR]
  have hgN : (D.good.card : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast Finset.card_le_card hD.2.1
  have hmN : m ≤ (101 / 100 : ℝ) * N := by
    nlinarith only [hgB, hgN, he1, mul_nonneg (sub_nonneg.mpr he1)
      (show 0 ≤ m by positivity)]
  exact ⟨hgB, hgR, hmN⟩


theorem power_column_symmetric (D : Reference n k d) (st : FilterState n d)
    (hp : 2 ≤ st.power) (hf : FrameNormalized D st)
    (j : Fin d × Fin d) :
    (fun i l ↦ (st.featureCov ^ (st.power / 2)) (i, l) j : Mat d)ᵀ =
      (fun i l ↦ (st.featureCov ^ (st.power / 2)) (i, l) j : Mat d) := by
  classical
  let φ := fun l ↦ feature (st.frame *ᵥ (D.observed l - st.center))
  let c := (st.mass D.block)⁻¹ • ∑ l ∈ D.block, st.weights l • φ l
  have hφ (l : Fin n) (i k : Fin d) : φ l (i, k) = φ l (k, i) := mul_comm _ _
  have hc (i k : Fin d) : c (i, k) = c (k, i) := by
    dsimp only [c]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hφ]
  have hrow (i k : Fin d) (a : Fin d × Fin d) :
      st.featureCov (i, k) a = st.featureCov (k, i) a := by
    rw [hf.2]
    simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
      Pi.sub_apply, smul_eq_mul]
    change (st.mass D.block)⁻¹ *
      (∑ l ∈ D.block, st.weights l * ((φ l (i, k) - c (i, k)) * (φ l a - c a))) =
      (st.mass D.block)⁻¹ *
      (∑ l ∈ D.block, st.weights l * ((φ l (k, i) - c (k, i)) * (φ l a - c a)))
    simp_rw [hφ _ i k, hc i k]
  have hp : st.power / 2 ≠ 0 := by
    omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp
  funext i k
  change (st.featureCov ^ (st.power / 2)) (k, i) j =
    (st.featureCov ^ (st.power / 2)) (i, k) j
  rw [hq, pow_succ', Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hrow k i a]


def normalizedColumn (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ)
    (p : ℕ) (j : Fin d × Fin d) : Mat d :=
  fun i l ↦ (A ^ (p / 2)) (i, l) j / Real.sqrt (∑ a, (A ^ (p / 2)) a j ^ 2)

theorem normalizedColumn_norm (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ)
    (p : ℕ) (j : Fin d × Fin d) : frobSq (normalizedColumn A p j) ≤ 1 := by
  let N := ∑ a, (A ^ (p / 2)) a j ^ 2
  have hN : 0 ≤ N := Finset.sum_nonneg fun a _ ↦ sq_nonneg _
  have he : frobSq (normalizedColumn A p j) = N / Real.sqrt N ^ 2 := by
    simp only [normalizedColumn, frobSq, div_pow, ← Finset.sum_div,
      N, Fintype.sum_prod_type]
  rw [he, Real.sq_sqrt hN]
  exact div_self_le_one N

theorem normalizedColumn_symm (D : Reference n k d) (st : FilterState n d)
    (hp : 2 ≤ st.power) (hf : FrameNormalized D st) (j : Fin d × Fin d) :
    (normalizedColumn st.featureCov st.power j)ᵀ =
      normalizedColumn st.featureCov st.power j := by
  have hh := power_column_symmetric D st hp hf j
  ext i l
  simp only [normalizedColumn, transpose_apply]
  exact congrArg (fun z : ℝ ↦ z / _) (congrFun (congrFun hh i) l)

def frameQuad (T : Mat d) (a : Vec d) (A : Mat d) : Unif.Quad d where
  A := Tᵀ * A * T
  b := -(2 : ℝ) • (Tᵀ *ᵥ (A *ᵥ (T *ᵥ a)))
  c := qform A (T *ᵥ a)

def quadCenter (F : FrameModel k d) (j : Fin k) (q : Unif.Quad d) : ℝ :=
  (q.A * F.cov j).trace + qform q.A (F.mean j) + q.b ⬝ᵥ F.mean j + q.c

def quadVariance (F : FrameModel k d) (j : Fin k) (q : Unif.Quad d) : ℝ :=
  2 * (q.A * F.cov j * q.A * F.cov j).trace +
    qform (F.cov j) (2 • (q.A *ᵥ F.mean j) + q.b)

theorem frameQuad_center (F : FrameModel k d) (j : Fin k)
    (T A : Mat d) (a : Vec d) (hA : Aᵀ = A) :
    quadCenter F j (frameQuad T a A) =
      (A * (T * F.cov j * Tᵀ)).trace + qform A (T *ᵥ (F.mean j - a)) := by
  have ht : (Tᵀ * A * T * F.cov j).trace = (A * (T * F.cov j * Tᵀ)).trace := by
    calc
      _ = (Tᵀ * (A * T * F.cov j)).trace := by simp only [mul_assoc]
      _ = ((A * T * F.cov j) * Tᵀ).trace := trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  have hq : qform (Tᵀ * A * T) (F.mean j) = qform A (T *ᵥ F.mean j) := by
    simpa only [transpose_transpose] using RBAux.qform_conjugate Tᵀ A (F.mean j)
  dsimp only [quadCenter, frameQuad]
  rw [ht, hq, mulVec_sub, FilterAux.qform_sub_symmetric A hA]
  simp only [smul_dotProduct, smul_eq_mul, dotProduct_mulVec, ← mulVec_transpose]
  ring

theorem frameQuad_variance (F : FrameModel k d) (j : Fin k)
    (T A : Mat d) (a : Vec d) (hA : Aᵀ = A) :
    quadVariance F j (frameQuad T a A) =
      2 * (A * (T * F.cov j * Tᵀ) * A * (T * F.cov j * Tᵀ)).trace +
        4 * qform (A * (T * F.cov j * Tᵀ) * A) (T *ᵥ (F.mean j - a)) := by
  let G := Tᵀ * A * T
  let S := T * F.cov j * Tᵀ
  let μ := T *ᵥ (F.mean j - a)
  have ht : (G * F.cov j * G * F.cov j).trace = (A * S * A * S).trace := by
    calc
      _ = (Tᵀ * (A * T * F.cov j * Tᵀ * A * T * F.cov j)).trace := by
        simp only [G, mul_assoc]
      _ = ((A * T * F.cov j * Tᵀ * A * T * F.cov j) * Tᵀ).trace :=
        trace_mul_comm _ _
      _ = _ := by simp only [S, mul_assoc]
  have hv : 2 • (G *ᵥ F.mean j) + (frameQuad T a A).b =
      2 • (Tᵀ *ᵥ (A *ᵥ μ)) := by
    dsimp only [G, μ, frameQuad]
    simp only [← mulVec_mulVec, mulVec_sub, neg_smul, two_smul]
    abel
  have hq : qform (F.cov j) (2 • (Tᵀ *ᵥ (A *ᵥ μ))) =
      4 * qform (A * S * A) μ := by
    have hscale : qform (F.cov j) (2 • (Tᵀ *ᵥ (A *ᵥ μ))) =
        4 * qform (F.cov j) (Tᵀ *ᵥ (A *ᵥ μ)) := by
      simp only [two_smul, qform, mulVec_add, add_dotProduct, dotProduct_add]
      ring
    rw [hscale, ← RBAux.qform_conjugate T (F.cov j)]
    have he : qform S (A *ᵥ μ) = qform (A * S * A) μ := by
      simpa only [hA] using (RBAux.qform_conjugate A S μ).symm
    change 4 * qform S (A *ᵥ μ) = _
    rw [he]
  change 2 * (G * F.cov j * G * F.cov j).trace +
    qform (F.cov j) (2 • (G *ᵥ F.mean j) + (frameQuad T a A).b) = _
  rw [ht, hv, hq]


def fnorm (A : Mat d) : ℝ := Real.sqrt (frobSq A)

theorem fnorm_nonneg (A : Mat d) : 0 ≤ fnorm A := Real.sqrt_nonneg _

theorem fnorm_sq (A : Mat d) : fnorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem fnorm_euclidean (A : Mat d) :
    fnorm A = ‖(WithLp.toLp 2 (fun ij : Fin d × Fin d ↦ A ij.1 ij.2) :
      EuclideanSpace ℝ (Fin d × Fin d))‖ := by
  simp only [fnorm, PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs,
    frobSq, Fintype.sum_prod_type]

theorem fnorm_add (A B : Mat d) : fnorm (A + B) ≤ fnorm A + fnorm B := by
  rw [fnorm_euclidean, fnorm_euclidean A, fnorm_euclidean B]
  exact norm_add_le
    (WithLp.toLp 2 (fun ij : Fin d × Fin d ↦ A ij.1 ij.2) :
      EuclideanSpace ℝ (Fin d × Fin d))
    (WithLp.toLp 2 (fun ij : Fin d × Fin d ↦ B ij.1 ij.2) :
      EuclideanSpace ℝ (Fin d × Fin d))


theorem fnorm_zero : fnorm (0 : Mat d) = 0 := by
  simp only [fnorm, frobSq, Matrix.zero_apply, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_const_zero, Real.sqrt_zero]


end FrameLoop

end

end ABBKS26.Robust.RBAux
