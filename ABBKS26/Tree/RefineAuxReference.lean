module

public import ABBKS26.Tree.RefineAuxResilience
public import ABBKS26.Tree.RefineAuxVerify

/-! The rounded clean reference attached to a refinement block. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix MvPolynomial Finset _root_.ABBKS26.Tree
open scoped BigOperators MatrixOrder

variable {n k d : ℕ}

/-- Components in a node are enumerated independently of the observed block. -/
def component (I : Finset (Fin k)) : Fin I.card → Fin k := I.orderEmbOfFin rfl

/-- Outside the reference the label is immaterial; use its first component. -/
def referenceLabel (I : Finset (Fin k)) (hI : I.Nonempty) (j : Fin k) : Fin I.card :=
  if hj : j ∈ I then (I.orderIsoOfFin rfl).symm ⟨j, hj⟩
  else ⟨0, Finset.card_pos.mpr hI⟩

/-- The full labelled component samples, with rounded clean and observed points. -/
def roundedReference (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) :
    Robust.Reference n I.card d where
  model :=
    { weight := fun j ↦ ((cluster (labels ω) (component I j)).card : ℝ) /
        (referenceSet ω I).card
      mean := fun j ↦ M.μ (component I j)
      cov := fun j ↦ M.S (component I j) }
  label := fun l ↦ referenceLabel I hI (ω l).1
  reference := referenceSet ω I
  good := referenceSet ω I ∩ (univ \ corrupted ω) ∩ N
  block := N
  clean := fun l i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ)
  observed := fun l i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)


theorem roundedReference_cluster
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) (j : Fin I.card) :
    (roundedReference M ω r N I hI).reference.filter
        (fun l ↦ (roundedReference M ω r N I hI).label l = j) =
      cluster (labels ω) (component I j) := by
  classical
  apply Finset.Subset.antisymm
  · intro l hl
    have hh := Finset.mem_filter.mp hl
    have hm : (ω l).1 ∈ I := (Finset.mem_filter.mp hh.1).2
    have he : referenceLabel I hI (ω l).1 = j := hh.2
    dsimp only [referenceLabel] at he
    rw [dite_eq_left hm] at he
    have he' := congrArg (fun a ↦ ((I.orderIsoOfFin rfl) a).val) he
    have hj : (ω l).1 = component I j := by
      simpa only [OrderIso.apply_symm_apply, component, coe_orderIsoOfFin_apply] using he'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hj⟩
  · intro l hl
    have hj : (ω l).1 = component I j := (Finset.mem_filter.mp hl).2
    have hm : (ω l).1 ∈ I := hj ▸ I.orderEmbOfFin_mem rfl j
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ l, hm⟩, ?_⟩
    change referenceLabel I hI (ω l).1 = j
    dsimp only [referenceLabel]
    rw [dite_eq_left hm]
    apply (I.orderIsoOfFin rfl).injective
    apply Subtype.ext
    simpa only [OrderIso.apply_symm_apply, coe_orderIsoOfFin_apply, component] using hj

theorem roundedReference_resilient
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) (hM : M.Valid)
    (s : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hm : ∀ j ∈ I, ∀ q ≤ s,
      SoS.coeffNorm1 (Resilience.empMom (cluster (labels ω) j)
        (standardizedRounded M ω r) q - Resilience.gaussPoly q) ≤
          θ / (d + 1 : ℝ) ^ (3 * s)) :
    (roundedReference M ω r N I hI).Resilient s θ := by
  apply Resilience.rounded_reference_resilient M ω r hM _ (component I)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (roundedReference_cluster M ω r N I hI)
    (fun _ ↦ rfl) s θ hθ
  intro j q hq
  exact hm _ (I.orderEmbOfFin_mem rfl j) q hq

private theorem projected_moment (D : Robust.Reference n k d) (θ : ℝ)
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
  simp only [Robust.FilterAux.lin_projection, Robust.FilterAux.quad_projection] at h
  have he : (C (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (C (u ⬝ᵥ (D.clean l - a)) * X i) ^ r) -
      IdCov.hmom r (C (u ⬝ᵥ (D.model.mean j - a)) * X i)
        (C (qform (D.model.cov j) u) * X i ^ 2) =
      C ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ r -
        IdCov.hmom r (u ⬝ᵥ (D.model.mean j - a)) (qform (D.model.cov j) u)) *
          (X i : RPoly d) ^ r := by
    rw [Robust.FilterAux.hmom_monomial]
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

theorem component_moments (D : Robust.Reference n k d) (θ : ℝ) (hcov : ∀ j, (D.model.cov j).PosDef)
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
    simpa only [S, qform, star_trivial] using (hcov j).dotProduct_mulVec_pos hu
  apply Robust.FilterAux.scalar_moment_bounds _ _ μ S _ hS (by positivity)
  · intro c
    have h := projected_moment D θ hres i (c • u) a j 2 (by omega)
    dsimp only at h
    simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      qform_scale, Robust.FilterAux.hmom_two] at h
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
      qform_scale, Robust.FilterAux.hmom_four] at h
    have he : (Cj.card : ℝ)⁻¹ * (c ^ 4 * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
        ((c * μ) ^ 4 + 6 * (c * μ) ^ 2 * (c ^ 2 * S) + 3 * (c ^ 2 * S) ^ 2) =
        c ^ 4 * ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (D.clean l - a)) ^ 4) -
          c ^ 4 * (μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2) := by ring
    simp only [μ, S, mul_pow] at he
    rw [he, abs_of_nonneg (mul_nonneg (sq_nonneg c) hS.le)] at h
    dsimp only [μ, S, Cj]
    linarith only [(abs_le.mp h).2]

/-- Small affine moment errors force the actual rounded reference covariance to be positive. -/
theorem reference_cov_posDef {m : ℕ} (R : Robust.Reference n m d)
    (hcov : ∀ j, (R.model.cov j).PosDef) (hne : R.reference.Nonempty)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ) :
    R.cov.PosDef := by
  have hpsd : R.cov.PosSemidef := by
    unfold Robust.Reference.cov
    apply PosSemidef.smul _ (by positivity)
    apply posSemidef_sum
    intro l _
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (R.clean l - R.mean)
  apply PosDef.of_dotProduct_mulVec_pos hpsd.1
  intro v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  let l₀ := hne.choose
  let j := R.label l₀
  let Cj := R.reference.filter (fun l ↦ R.label l = j)
  have hC := component_moments R θ hcov hθ.1 hres i v R.mean hv j
  have hvar : 0 < qform (R.model.cov j) v := by
    simpa only [qform, star_trivial] using (hcov j).dotProduct_mulVec_pos hv
  have ht : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 8 :=
    one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) d])
  have hsmall : θ / (d + 1 : ℝ) ^ 8 ≤ 1 / 10000 :=
    (div_le_self hθ.1 ht).trans hθ.2
  have hpos : 0 < (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (v ⬝ᵥ (R.clean l - R.mean)) ^ 2 := by
    apply lt_of_lt_of_le _ hC.1
    apply mul_pos
    · linarith only [hsmall]
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) hvar
  have hsum : 0 < ∑ l ∈ Cj, (v ⬝ᵥ (R.clean l - R.mean)) ^ 2 := by
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (Cj.card : ℝ)⁻¹)
      (le_of_not_gt h)
    linarith only [hpos, hh]
  have htotal : (∑ l ∈ Cj, (v ⬝ᵥ (R.clean l - R.mean)) ^ 2) ≤
      ∑ l ∈ R.reference, (v ⬝ᵥ (R.clean l - R.mean)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  have hR : (0 : ℝ) < R.reference.card := by exact_mod_cast card_pos.mpr hne
  have heq : v ⬝ᵥ (R.cov *ᵥ v) = (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, (v ⬝ᵥ (R.clean l - R.mean)) ^ 2 := by
    simp only [Robust.Reference.cov, smul_mulVec, sum_mulVec, dotProduct_smul,
      dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul, pow_two,
      dotProduct_comm]
  simp only [star_trivial]
  rw [heq]
  exact mul_pos (inv_pos.mpr hR) (hsum.trans_le htotal)

/-- The reference weights satisfy the robust floor `w/2` on every good sample. -/
theorem roundedReference_valid
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hM : M.Valid) (hg : Good M ε w η D ω) (hw : 0 < w)
    (hwj : ∀ j, w ≤ M.w j) (hη : 0 ≤ η ∧ η ≤ 1 / 100)
    (hcov : (roundedReference M ω r N I hI).cov.PosDef) :
    (roundedReference M ω r N I hI).Valid (w / 2) := by
  classical
  let G := referenceSet ω I
  have hcluster (j : Fin k) (hj : j ∈ I) : cluster (labels ω) j ⊆ G := by
    intro l hl
    have hh : (ω l).1 = j := (mem_filter.mp hl).2
    simp only [G, referenceSet, mem_filter, mem_univ, true_and, hh, hj]
  let j₀ := hI.choose
  have hj₀ := hI.choose_spec
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (SoundAux.good_cluster_pos M ε w η D ω hg j₀).trans_le
      ((card_le_card (subset_univ _)).trans_eq (card_fin n))
  have hG : G.Nonempty :=
    (card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hg j₀)).mono
      (hcluster j₀ hj₀)
  have hG0 : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr hG
  have hGn : (G.card : ℝ) ≤ n := by
    exact_mod_cast (card_le_card (subset_univ G)).trans_eq (card_fin n)
  have hcounts := (good_counts M ε w η D ω hg hη).1
  have hweight (j : Fin I.card) : w / 2 ≤
      ((cluster (labels ω) (component I j)).card : ℝ) / G.card := by
    rw [le_div_iff₀ hG0]
    have hc := (hcounts (component I j)).1
    have hm := mul_le_mul_of_nonneg_right (hwj (component I j)) hn.le
    have hnG := mul_le_mul_of_nonneg_left hGn hw.le
    nlinarith only [hc, hm, hnG]
  have hsum : ∑ j : Fin I.card,
      ((cluster (labels ω) (component I j)).card : ℝ) = G.card := by
    rw [← Tree.RefineAux.sum_reference_card ω I]
    exact (I.orderIsoOfFin rfl).toEquiv.sum_comp
      (fun j : I ↦ ((cluster (labels ω) j).card : ℝ)) |>.trans (by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach I (fun j : Fin k ↦ ((cluster (labels ω) j).card : ℝ)))
  refine ⟨⟨by positivity, hweight, ?_, fun j ↦ hM.posDef (component I j)⟩,
    inter_subset_left.trans inter_subset_left, inter_subset_right, ?_, hG, hcov, ?_⟩
  · change (∑ j, ((cluster (labels ω) (component I j)).card : ℝ) / G.card) = 1
    rw [← sum_div, hsum, div_self hG0.ne']
  · intro l hl
    have hnot : l ∉ corrupted ω := (mem_sdiff.mp (mem_inter.mp (mem_inter.mp hl).1).2).2
    have he : (ω l).2.1 = (ω l).2.2 := not_not.mp (mem_corrupted.not.mp hnot)
    change (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)) =
      (fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ))
    rw [he]
  · intro j
    rw [roundedReference_cluster]
    rfl

/-- An observed block is represented by the canonical increasing index enumeration. -/
abbrev blockInput (x : Fin n → Fin d → ℚ) (N : Finset (Fin n)) : Points :=
  List.ofFn fun l : Fin N.card ↦ List.ofFn (x (N.orderEmbOfFin rfl l))

theorem blockInput_represents
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) :
    Robust.Represents (roundedReference M ω r N I hI)
      (blockInput (fun l i ↦ r ((ω l).1, (ω l).2.2) i) N) := by
  classical
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let pts := blockInput x N
  have hlen : pts.length = N.card := by simp [pts, blockInput]
  let idx : Fin pts.length → Fin n :=
    fun l ↦ N.orderEmbOfFin rfl (Fin.cast hlen l)
  have hcast : Function.Injective (Fin.cast hlen) := by
    intro a b h
    have hh : a.val = b.val := congrArg (fun t : Fin N.card ↦ t.val) h
    exact Fin.ext hh
  refine ⟨hlen, idx, (N.orderEmbOfFin rfl).injective.comp hcast, ?_, ?_⟩
  · ext l
    constructor
    · rintro ⟨a, rfl⟩
      exact N.orderEmbOfFin_mem rfl _
    · intro hl
      let j := (N.orderIsoOfFin rfl).symm ⟨l, hl⟩
      refine ⟨Fin.cast hlen.symm j, ?_⟩
      change N.orderEmbOfFin rfl (Fin.cast hlen (Fin.cast hlen.symm j)) = l
      rw [show Fin.cast hlen (Fin.cast hlen.symm j) = j from Fin.ext rfl]
      change ((N.orderIsoOfFin rfl) ((N.orderIsoOfFin rfl).symm ⟨l, hl⟩)).val = l
      simp only [OrderIso.apply_symm_apply]
  · intro l
    have helem : (blockInput x N)[l] = List.ofFn (x (idx l)) := by
      change (List.ofFn (fun a : Fin N.card ↦ List.ofFn (x (N.orderEmbOfFin rfl a)))).get l
        = List.ofFn (x (idx l))
      rw [List.get_ofFn]
    change (blockInput x N)[l].length = d ∧ _
    rw [helem]
    refine ⟨List.length_ofFn, fun j ↦ ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rfl

end

end ABBKS26.RefineAux
