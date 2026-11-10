module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobScan
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobCap

/-! Quantitative lower bounds from rational sample Gram matrices. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobFloor

open Common Matrix _root_.ABBKS26.Tree Sources Builders
open scoped BigOperators

/-- A determinant floor and a trace ceiling bound every eigenvalue from below. -/
theorem spectral_floor {d : ℕ} (A : Mat d) (hA : A.PosDef) (a e : ℕ)
    (hdet : 1 / (2 : ℝ) ^ a ≤ A.det) (htrace : A.trace ≤ (2 : ℝ) ^ e) :
    ∀ v, (1 / (2 : ℝ) ^ (a + e * d)) * sqnorm v ≤ qform A v := by
  classical
  have hupper (i : Fin d) : hA.1.eigenvalues i ≤ (2 : ℝ) ^ e := by
    apply le_trans _ htrace
    rw [hA.1.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ ↦ (hA.eigenvalues_pos j).le)
      (Finset.mem_univ i)
  have hlower (i : Fin d) : 1 / (2 : ℝ) ^ (a + e * d) ≤ hA.1.eigenvalues i := by
    have hp : (∏ j ∈ Finset.univ.erase i, hA.1.eigenvalues j) ≤
        ((2 : ℝ) ^ e) ^ d := by
      calc
        _ ≤ ∏ _j ∈ Finset.univ.erase i, (2 : ℝ) ^ e :=
          Finset.prod_le_prod₀ (fun j _ ↦ (hA.eigenvalues_pos j).le)
            (fun j _ ↦ hupper j)
        _ = ((2 : ℝ) ^ e) ^ (d - 1) := by simp
        _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
    have heq := hA.1.det_eq_prod_eigenvalues
    change A.det = ∏ j, hA.1.eigenvalues j at heq
    have hd : A.det ≤ hA.1.eigenvalues i * (2 : ℝ) ^ (e * d) := by
      calc
        _ = (∏ j ∈ Finset.univ.erase i, hA.1.eigenvalues j) *
            hA.1.eigenvalues i := heq.trans
              (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
        _ ≤ ((2 : ℝ) ^ e) ^ d * hA.1.eigenvalues i :=
          mul_le_mul_of_nonneg_right hp (hA.eigenvalues_pos i).le
        _ = _ := by rw [pow_mul, mul_comm]
    rw [pow_add, ← div_div]
    exact (div_le_iff₀ (by positivity)).mpr (hdet.trans hd)
  intro v
  have hnorm : sqnorm v = ∑ j, ((hA.1.eigenvectorBasis j).ofLp ⬝ᵥ v) ^ 2 := by
    have he : sqnorm v = qform (1 : Mat d) v := by simp [sqnorm, qform]
    rw [he, Rounding.DetRoundAux.spectral_one A hA.1]
    simp only [qform, sum_mulVec, dotProduct_sum, vecMulVec_mulVec,
      op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [dotProduct_comm v, pow_two]
  rw [Rounding.DetRoundAux.qform_spectral A hA.1, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right (hlower j) (sq_nonneg _)

open Turing.MultiTapeTM

private theorem vector_den_bound (xs : Vector) :
    (xs.map Rat.den).prod ≤ 2 ^ (encVector xs).length := by
  induction xs with
  | nil => simp only [List.map_nil, List.prod_nil]; exact Nat.one_le_two_pow
  | cons q xs ih =>
    have hq := (FrobSize.of_encoding (le_refl (Encoding.encRat q).length)).denominator
    have he : (encVector (q :: xs)).length =
        2 * (Encoding.encRat q).length + 1 + (encVector xs).length := by
      change (frame (Encoding.encRat q) ++ encVector xs).length = _
      rw [List.length_append, length_frame]
    rw [List.map_cons, List.prod_cons, he]
    apply (Nat.mul_le_mul hq ih).trans
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- One common denominator for all sample coordinates costs at most the sample encoding. -/
def denominator (pts : Points) : ℕ := (pts.flatten.map Rat.den).prod

theorem denominator_pos (pts : Points) : 0 < denominator pts := by
  apply List.prod_pos
  intro a ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
  exact q.den_pos

theorem denominator_bound (pts : Points) : denominator pts ≤ 2 ^ (encPoints pts).length := by
  induction pts with
  | nil => simp only [denominator, List.flatten_nil, List.map_nil, List.prod_nil]
           exact Nat.one_le_two_pow
  | cons xs pts ih =>
    have hx := vector_den_bound xs
    have he : (encPoints (xs :: pts)).length =
        2 * (encVector xs).length + 1 + (encPoints pts).length := by
      change (frame (encVector xs) ++ encPoints pts).length = _
      rw [List.length_append, length_frame]
    rw [he]
    simp only [denominator, List.flatten_cons, List.map_append, List.prod_append]
    apply (Nat.mul_le_mul hx ih).trans
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem denominator_clears {n d : ℕ} (x : Fin n → Fin d → ℚ) (l : Fin n) (i : Fin d) :
    ∃ a : ℤ, (a : ℚ) = (denominator (pointsOf x) : ℚ) * x l i := by
  have hm : x l i ∈ (pointsOf x).flatten := by
    apply List.mem_flatten.mpr
    refine ⟨List.ofFn (x l), List.mem_ofFn.mpr ⟨l, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  have hd : (x l i).den ∣ denominator (pointsOf x) :=
    List.dvd_prod (List.mem_map_of_mem hm)
  obtain ⟨t, ht⟩ := hd
  refine ⟨(t : ℤ) * (x l i).num, ?_⟩
  rw [ht]
  push_cast
  rw [mul_comm ((x l i).den : ℚ), mul_assoc, mul_comm ((x l i).den : ℚ),
    Rat.mul_den_eq_num]

/-- The unnormalized second moment of a subset uses only observed rational coordinates. -/
def gram {n d : ℕ} (x : Fin n → Fin d → ℚ) (G : Finset (Fin n)) : Mat d :=
  ∑ l ∈ G, vecMulVec (fun i ↦ (x l i : ℝ)) (fun i ↦ (x l i : ℝ))

theorem gram_qform {n d : ℕ} (x : Fin n → Fin d → ℚ) (G : Finset (Fin n)) (v : Vec d) :
    qform (gram x G) v = ∑ l ∈ G, (v ⬝ᵥ fun i ↦ (x l i : ℝ)) ^ 2 := by
  simp only [gram, qform, sum_mulVec, dotProduct_sum, vecMulVec_mulVec,
    op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [dotProduct_comm v, pow_two]

/-- Clearing the sample denominators gives a nonzero integer determinant. -/
theorem gram_det_floor {n d : ℕ} (x : Fin n → Fin d → ℚ) (G : Finset (Fin n))
    (hG : (gram x G).PosDef) (z : ℕ) (hz : (encPoints (pointsOf x)).length ≤ z) :
    1 / (2 : ℝ) ^ (2 * z * d) ≤ (gram x G).det := by
  classical
  let Q := denominator (pointsOf x)
  have hQ : 0 < (Q : ℝ) := by exact_mod_cast denominator_pos (pointsOf x)
  choose a ha using denominator_clears x
  let Z : Matrix (Fin d) (Fin d) ℤ := ∑ l ∈ G, vecMulVec (a l) (a l)
  have hZ : Z.map (Int.castRingHom ℝ) = (Q : ℝ) ^ 2 • gram x G := by
    ext i j
    dsimp only [Z, gram, Matrix.map_apply, Matrix.smul_apply]
    simp only [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    change (↑(∑ l ∈ G, a l i * a l j) : ℝ) =
      (Q : ℝ) ^ 2 * ∑ l ∈ G, (x l i : ℝ) * (x l j : ℝ)
    simp only [Int.cast_sum, Int.cast_mul]
    have hc (l : Fin n) (i : Fin d) : (a l i : ℝ) = (Q : ℝ) * (x l i : ℝ) := by
      exact_mod_cast ha l i
    simp_rw [hc]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have heq : (Z.det : ℝ) = (Q : ℝ) ^ (2 * d) * (gram x G).det := by
    have he := (Int.castRingHom ℝ).map_det Z
    change (Z.det : ℝ) = (Z.map (Int.castRingHom ℝ)).det at he
    rw [hZ, det_smul, Fintype.card_fin, ← pow_mul] at he
    exact he
  have hZpos : (0 : ℝ) < Z.det := by
    rw [heq]
    exact mul_pos (pow_pos hQ _) hG.det_pos
  have hZ1 : (1 : ℝ) ≤ Z.det := by
    have hZpos' : (0 : ℤ) < Z.det := by exact_mod_cast hZpos
    exact_mod_cast (show (1 : ℤ) ≤ Z.det by omega)
  have hQbound : (Q : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast (denominator_bound (pointsOf x)).trans
      (Nat.pow_le_pow_right (by norm_num) hz)
  have hpow : (Q : ℝ) ^ (2 * d) ≤ (2 : ℝ) ^ (2 * z * d) := by
    have hh := pow_le_pow_left₀ hQ.le hQbound (2 * d)
    rw [← pow_mul] at hh
    convert hh using 1
    congr 1
    ring
  rw [div_le_iff₀ (by positivity)]
  have hh := mul_le_mul_of_nonneg_right hpow hG.det_pos.le
  nlinarith only [heq, hZ1, hh]

/-- The trace ceiling uses the original sample bits, including arbitrary rational entries. -/
theorem gram_trace_bound {n d : ℕ} (x : Fin n → Fin d → ℚ) (G : Finset (Fin n))
    (z : ℕ) (hn : n ≤ z) (hd : d ≤ z) (hx : (encPoints (pointsOf x)).length ≤ z) :
    (gram x G).trace ≤ (2 : ℝ) ^ (4 * z) := by
  have hb (l : Fin n) (i : Fin d) : |(x l i : ℝ)| ≤ (2 : ℝ) ^ z :=
    (FrobBounds.sample_entry x l i).trans (pow_le_pow_right₀ (by norm_num) hx)
  have he (l : Fin n) (i : Fin d) : (x l i : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * z) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hb l i) 2
    rw [sq_abs, ← pow_mul] at hh
    convert hh using 1
    congr 1
    ring
  have ht : (gram x G).trace ≤ d * (n * (2 : ℝ) ^ (2 * z)) := by
    simp only [Matrix.trace, Matrix.diag, gram, Matrix.sum_apply, vecMulVec_apply]
    calc
      _ ≤ ∑ _i : Fin d, ∑ _l ∈ G, (2 : ℝ) ^ (2 * z) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun l _ ↦ by simpa only [pow_two] using he l i
      _ = d * (G.card * (2 : ℝ) ^ (2 * z)) := by simp only
        [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := by
        gcongr
        exact_mod_cast (Finset.card_le_card (Finset.subset_univ G)).trans_eq
          (Finset.card_fin n)
  have hn' : (n : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast hn.trans (Nat.lt_two_pow_self (n := z)).le
  have hd' : (d : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast hd.trans (Nat.lt_two_pow_self (n := z)).le
  calc
    _ ≤ d * (n * (2 : ℝ) ^ (2 * z)) := ht
    _ ≤ (2 : ℝ) ^ z * ((2 : ℝ) ^ z * (2 : ℝ) ^ (2 * z)) := by gcongr
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- Every positive definite subset Gram matrix has a floor polynomial in input bits. -/
theorem gram_lower {n d : ℕ} (x : Fin n → Fin d → ℚ) (G : Finset (Fin n))
    (hG : (gram x G).PosDef) (z : ℕ) (hn : n ≤ z) (hd : d ≤ z)
    (hx : (encPoints (pointsOf x)).length ≤ z) (v : Vec d) :
    (1 / (2 : ℝ) ^ (6 * z * d)) * sqnorm v ≤ qform (gram x G) v := by
  have hh := spectral_floor (gram x G) hG (2 * z * d) (4 * z)
    (gram_det_floor x G hG z hx) (gram_trace_bound x G z hn hd hx) v
  convert hh using 1
  congr 2
  ring

private theorem retained_sum_pos {n : ℕ} (C G : Finset (Fin n))
    (hGC : G ⊆ C) (f : Fin n → ℝ) (S : ℝ) (hS : 0 < S)
    (hC : 0 < (C.card : ℝ)) (hmiss : ((C \ G).card : ℝ) ≤ C.card / 10000)
    (hsecond : C.card * S / 2 ≤ ∑ l ∈ C, f l ^ 2)
    (hfourth : (∑ l ∈ C, f l ^ 4) ≤ 4 * C.card * S ^ 2) :
    0 < ∑ l ∈ G, f l ^ 2 := by
  classical
  by_contra h
  have hzero : (∑ l ∈ G, f l ^ 2) = 0 :=
    le_antisymm (le_of_not_gt h) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have heq : (∑ l ∈ C \ G, f l ^ 2) = ∑ l ∈ C, f l ^ 2 := by
    have hh := Finset.sum_sdiff hGC (f := fun l ↦ f l ^ 2)
    linarith only [hh, hzero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (C \ G) (fun _ ↦ (1 : ℝ))
    (fun l ↦ f l ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hfourth' : (∑ l ∈ C \ G, (f l ^ 2) ^ 2) ≤ 4 * C.card * S ^ 2 := by
    calc
      _ = ∑ l ∈ C \ G, f l ^ 4 := by congr 1; funext l; ring
      _ ≤ ∑ l ∈ C, f l ^ 4 := Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset (fun _ _ _ ↦ by positivity)
      _ ≤ _ := hfourth
  have hbound := mul_le_mul hmiss hfourth'
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity : 0 ≤ (C.card : ℝ) / 10000)
  rw [heq] at hcs
  have hpos : 0 < (C.card * S : ℝ) := mul_pos hC hS
  have hlow := pow_le_pow_left₀ (by positivity : 0 ≤ (C.card : ℝ) * S / 2) hsecond 2
  nlinarith only [hcs, hbound, hlow, sq_pos_of_pos hpos]

/-- Retained observations from each centered component still span the ambient space. -/
theorem component_gram {n k d : ℕ} (R : Robust.Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (hcen : ∀ j, R.model.mean j = 0)
    (he : R.contamination ≤ Robust.maxContamination π t)
    (x : Fin n → Fin d → ℚ) (hx : R.observed = fun l i ↦ (x l i : ℝ)) (j : Fin k) :
    ∃ G : Finset (Fin n), (gram x G).PosDef ∧
      ∀ v, qform (gram x G) v ≤ 2 * n * qform (R.model.cov j) v := by
  classical
  let C := R.reference.filter (fun l ↦ R.label l = j)
  let G := R.good.filter (fun l ↦ R.label l = j)
  have hGC : G ⊆ C := Finset.filter_subset_filter _ hR.2.1
  have href : 0 < (R.reference.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hR.2.2.2.2.1
  have hπC : π * R.reference.card ≤ (C.card : ℝ) := by
    have hh := hR.1.2.1 j
    rw [hR.2.2.2.2.2.2 j] at hh
    exact (le_div_iff₀ href).mp hh
  have hC : 0 < (C.card : ℝ) := (mul_pos hR.1.1 href).trans_le hπC
  have hmiss : ((C \ G).card : ℝ) ≤ C.card / 10000 := by
    have hsub : C \ G ⊆ R.reference \ R.good := by
      intro l hl
      obtain ⟨hlC, hlG⟩ := Finset.mem_sdiff.mp hl
      have hl := Finset.mem_filter.mp hlC
      exact Finset.mem_sdiff.mpr ⟨hl.1, fun hgood ↦
        hlG (Finset.mem_filter.mpr ⟨hgood, hl.2⟩)⟩
    have hh : ((R.reference \ R.good).card : ℝ) ≤
        R.contamination * R.reference.card := by
      apply (div_le_iff₀ href).mp
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hε := Robust.RBAux.contamination_small_pi R π t hR.1.1 hπ he
    have hcard : ((C \ G).card : ℝ) ≤ (R.reference \ R.good).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith only [hcard, hh, hπC, mul_le_mul_of_nonneg_right hε href.le]
  have hagree (l : Fin n) (hl : l ∈ G) :
      (fun i ↦ (x l i : ℝ)) = R.clean l := by
    exact (congrFun hx l).symm.trans (hR.2.2.2.1 l (Finset.mem_filter.mp hl).1)
  have hform (v : Vec d) : qform (gram x G) v = ∑ l ∈ G, (v ⬝ᵥ R.clean l) ^ 2 := by
    rw [gram_qform]
    exact Finset.sum_congr rfl fun l hl ↦ by rw [hagree l hl]
  have hδ : (1 / 10000 : ℝ) / (d + 1 : ℝ) ^ 8 ≤ 1 / 10000 :=
    div_le_self (by norm_num) (one_le_pow₀
      (by linarith only [Nat.cast_nonneg (α := ℝ) d] : (1 : ℝ) ≤ d + 1))
  have hpsd : (gram x G).PosSemidef := by
    unfold gram
    apply Matrix.posSemidef_sum
    intro l _
    simpa only [star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (fun i ↦ (x l i : ℝ))
  refine ⟨G, PosDef.of_dotProduct_mulVec_pos hpsd.1 ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _⟩ := Function.ne_iff.mp hv
    have hS : 0 < qform (R.model.cov j) v := by
      simpa only [qform, star_trivial] using (hR.1.2.2.2 j).dotProduct_mulVec_pos hv
    have hm := ABBKS26.RefineAux.component_moments R (1 / 10000) hR.1.2.2.2
      (by norm_num) hres i v 0 hv j
    dsimp only at hm
    simp only [hcen, sub_zero, dotProduct_zero] at hm
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add] at hm
    change (1 - 9 * _) * qform (R.model.cov j) v ≤
      (C.card : ℝ)⁻¹ * ∑ l ∈ C, (v ⬝ᵥ R.clean l) ^ 2 ∧ _ at hm
    have hsecond := mul_le_mul_of_nonneg_left hm.1 hC.le
    have hfourth := mul_le_mul_of_nonneg_left hm.2 hC.le
    rw [mul_inv_cancel_left₀ hC.ne'] at hsecond hfourth
    have h2 : C.card * qform (R.model.cov j) v / 2 ≤
        ∑ l ∈ C, (v ⬝ᵥ R.clean l) ^ 2 := by
      nlinarith only [hsecond, mul_le_mul_of_nonneg_right hδ
        (mul_nonneg hC.le hS.le), mul_pos hC hS]
    have h4 : (∑ l ∈ C, (v ⬝ᵥ R.clean l) ^ 4) ≤
        4 * C.card * qform (R.model.cov j) v ^ 2 := by
      nlinarith only [hfourth, mul_le_mul_of_nonneg_right hδ
        (mul_nonneg hC.le (sq_nonneg (qform (R.model.cov j) v))),
          mul_nonneg hC.le (sq_nonneg (qform (R.model.cov j) v))]
    change 0 < qform (gram x G) v
    rw [hform]
    exact retained_sum_pos C G hGC (fun l ↦ v ⬝ᵥ R.clean l) _ hS hC hmiss h2 h4
  · intro v
    have hm := ABBKS26.RefineAux.centered_component_moments R (1 / 10000)
      hR.1.2.2.2 hcen hres v j
    have hS : 0 ≤ qform (R.model.cov j) v :=
      (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v
    have hupper := (abs_le.mp hm.2).2
    change (C.card : ℝ)⁻¹ * (∑ l ∈ C, (v ⬝ᵥ R.clean l) ^ 2) - _ ≤ _ at hupper
    have hu := mul_le_mul_of_nonneg_left hupper hC.le
    rw [mul_sub, mul_inv_cancel_left₀ hC.ne'] at hu
    have hCn : (C.card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_le_card (Finset.subset_univ C)).trans_eq (Finset.card_fin n)
    rw [hform]
    apply (Finset.sum_le_sum_of_subset_of_nonneg hGC (fun _ _ _ ↦ sq_nonneg _)).trans
    have hsum : (∑ l ∈ C, (v ⬝ᵥ R.clean l) ^ 2) ≤
        2 * C.card * qform (R.model.cov j) v := by
      nlinarith only [hu, mul_le_mul_of_nonneg_right hδ (mul_nonneg hC.le hS),
        mul_nonneg hC.le hS]
    exact hsum.trans (by gcongr)

/-- Prepared moments and rational sample size supply the cap floor without a new assumption. -/
theorem prepared_floor : FrobCap.PreparedFloor FrobScan.coefficientExponent := by
  intro n d k ps x fuel h N M ε w η Δ D ω r I hx hp _ hh hI hl hN
  classical
  let a : Args := (args k ps x h N, fuel)
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hd : d ≤ z := (FrobScan.key_bounds a).2.1
  have hxz : (encPoints (pointsOf x)).length ≤ z := (FrobScan.key_bounds a).2.2.2.1
  have hn : n ≤ z := by
    have hc := Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) (pointsOf x)
    simpa only [pointsOf, List.length_ofFn] using hc.trans hxz
  have hn0 : (0 : ℝ) < n := by
    have hsize := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
    by_contra hn0
    have hzero : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn0) (by positivity)
    rw [hzero] at hsize
    norm_num at hsize
  obtain ⟨hcompat, hπ⟩ := hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh N I hI hl hN
  obtain ⟨hR, hres, _, _, hcen, he⟩ := hcompat
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let j : Fin I.card := ⟨0, Finset.card_pos.mpr hI⟩
  have hobs' : R.observed = fun l i ↦ (x l i : ℝ) := by
    rw [hx]
    rfl
  obtain ⟨G, hG, hupper⟩ := component_gram R _ _ hR hres hπ hcen he x hobs' j
  refine ⟨ABBKS26.RefineAux.component I j, I.orderEmbOfFin_mem rfl j, ?_⟩
  intro v
  have hfloor := gram_lower x G hG z hn hd hxz v
  have hu := hupper v
  change qform (gram x G) v ≤
    2 * n * qform (M.S (ABBKS26.RefineAux.component I j)) v at hu
  have hw : (0 : ℝ) < (ps h).w := by
    exact_mod_cast (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).1
  have hscale : 40 / ((ps h).w : ℝ) ≤ (2 : ℝ) ^ (z + 6) := by
    have hfield : field a 0 = (ps h).w := by
      rw [field_args _ _ _ _ _ _ (by omega)]
      rfl
    simpa only [hfield] using FrobScan.scale_bound a
  have hn' : (n : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast hn.trans (Nat.lt_two_pow_self (n := z)).le
  have hpow : 6 * z * d + (2 * z + 7) ≤ z ^ 3 := by
    have hdim : 6 * z * d ≤ 6 * z ^ 2 := by nlinarith only [Nat.mul_le_mul_left (6 * z) hd]
    have hsmall : 2 * z + 7 ≤ z ^ 2 := by nlinarith only [hz]
    have hlarge : 7 * z ^ 2 ≤ z ^ 3 := by
      calc
        _ ≤ z * z ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    omega
  have hcoef : (2 * n : ℝ) * (40 / ((ps h).w : ℝ)) ≤ (2 : ℝ) ^ (2 * z + 7) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ z * (2 : ℝ) ^ (z + 6) := by
        gcongr
      _ = _ := by
        rw [show 2 * z + 7 = 1 + z + (z + 6) by omega]
        simp only [pow_add, pow_one]
  have hpaid : (2 * n : ℝ) * ((40 / ((ps h).w : ℝ)) / (2 : ℝ) ^ z ^ 3) ≤
      1 / (2 : ℝ) ^ (6 * z * d) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc
      _ ≤ (2 : ℝ) ^ (2 * z + 7) * (2 : ℝ) ^ (6 * z * d) := by gcongr
      _ = (2 : ℝ) ^ (6 * z * d + (2 * z + 7)) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hpow
  have hpaid' := mul_le_mul_of_nonneg_right hpaid (Rounding.DetRoundAux.sqnorm_nonneg v)
  change (40 / ((ps h).w : ℝ)) / (2 : ℝ) ^ z ^ 3 * sqnorm v ≤ _
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 * n)).mp
  nlinarith only [hpaid', hfloor, hu]

end ABBKS26.Assembly.Exec.RefineSynth.FrobFloor
