module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdFinish

/-! Rational augmented Gram matrices control affine statistics without centered means. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdFloor

open Common Matrix _root_.ABBKS26.Tree Sources Builders
open scoped BigOperators

noncomputable section

theorem retained_bounds {n : ℕ} (C G : Finset (Fin n)) (f : Fin n → ℝ) (m : ℝ)
    (hGC : G ⊆ C) (hC : 0 < (C.card : ℝ)) (hm : 0 ≤ m)
    (hmiss : ((C \ G).card : ℝ) ≤ C.card / 10000)
    (hsecond : C.card * m / 2 ≤ ∑ l ∈ C, f l ^ 2)
    (hfourth : (∑ l ∈ C, f l ^ 4) ≤ 4 * C.card * m ^ 2) :
    C.card * m / 4 ≤ ∑ l ∈ G, f l ^ 2 ∧
      (∑ l ∈ G, f l ^ 2) ≤ 2 * C.card * m := by
  classical
  have hs0 : 0 ≤ ∑ l ∈ C \ G, f l ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (C \ G) (fun _ ↦ (1 : ℝ))
    (fun l ↦ f l ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have h4 : (∑ l ∈ C \ G, (f l ^ 2) ^ 2) ≤ 4 * C.card * m ^ 2 := by
    calc
      _ = ∑ l ∈ C \ G, f l ^ 4 := by congr 1; funext l; ring
      _ ≤ ∑ l ∈ C, f l ^ 4 := Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset (fun _ _ _ ↦ by positivity)
      _ ≤ _ := hfourth
  have hp := mul_le_mul hmiss h4 (by positivity) (by positivity)
  have hsq : (∑ l ∈ C \ G, f l ^ 2) ^ 2 ≤ (C.card * m / 4) ^ 2 := by
    nlinarith only [hs, hp, sq_nonneg ((C.card : ℝ) * m)]
  have hsmall := (sq_le_sq₀ hs0 (by positivity)).mp hsq
  have he := Finset.sum_sdiff hGC (f := fun l ↦ f l ^ 2)
  have ht := Finset.sum_mul_sq_le_sq_mul_sq C (fun _ ↦ (1 : ℝ))
    (fun l ↦ f l ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at ht
  have h4' : (∑ l ∈ C, (f l ^ 2) ^ 2) ≤ 4 * C.card * m ^ 2 := by
    simpa only [← pow_mul] using hfourth
  have hp' := mul_le_mul_of_nonneg_left h4' hC.le
  have hsq' : (∑ l ∈ C, f l ^ 2) ^ 2 ≤ (2 * C.card * m) ^ 2 := by
    nlinarith only [ht, hp']
  have hlarge := (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (by positivity)).mp hsq'
  refine ⟨by linarith only [hsecond, hsmall, he], ?_⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hGC
    (fun _ _ _ ↦ sq_nonneg _)).trans hlarge

variable {n k d : ℕ}

theorem retained_component (R : Robust.Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hπ : π ≤ 1)
    (he : R.contamination ≤ Robust.maxContamination π t) (j : Fin k) :
    let C := R.reference.filter (fun l ↦ R.label l = j)
    let G := R.good.filter (fun l ↦ R.label l = j)
    G ⊆ C ∧ 0 < (C.card : ℝ) ∧
      ((C \ G).card : ℝ) ≤ C.card / 10000 := by
  classical
  let C := R.reference.filter (fun l ↦ R.label l = j)
  let G := R.good.filter (fun l ↦ R.label l = j)
  have href : 0 < (R.reference.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hR.2.2.2.2.1
  have hπC : π * R.reference.card ≤ (C.card : ℝ) := by
    have hh := hR.1.2.1 j
    rw [hR.2.2.2.2.2.2 j] at hh
    exact (le_div_iff₀ href).mp hh
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
  refine ⟨Finset.filter_subset_filter _ hR.2.1,
    (mul_pos hR.1.1 href).trans_le hπC, ?_⟩
  nlinarith only [hcard, hh, hπC, mul_le_mul_of_nonneg_right hε href.le]

theorem affine_component (R : Robust.Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ Robust.maxContamination π t)
    (j : Fin k) (v : Vec d) (c : ℝ) :
    let C := R.reference.filter (fun l ↦ R.label l = j)
    let G := R.good.filter (fun l ↦ R.label l = j)
    let m := (v ⬝ᵥ R.model.mean j + c) ^ 2 + qform (R.model.cov j) v
    C.card * m / 4 ≤ ∑ l ∈ G, (v ⬝ᵥ R.clean l + c) ^ 2 ∧
      (∑ l ∈ G, (v ⬝ᵥ R.clean l + c) ^ 2) ≤ 2 * C.card * m := by
  classical
  let C := R.reference.filter (fun l ↦ R.label l = j)
  let G := R.good.filter (fun l ↦ R.label l = j)
  obtain ⟨hGC, hC, hmiss⟩ := retained_component R π t hR hπ he j
  by_cases hv : v = 0
  · subst v
    simp only [zero_dotProduct, zero_add, qform, mulVec_zero, dotProduct_zero, add_zero]
    have hg : (C.card : ℝ) / 4 ≤ G.card := by
      have hc : ((C \ G).card : ℝ) + G.card = C.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hGC
      linarith only [hc, hmiss, hC]
    have hg' : (G.card : ℝ) ≤ 2 * C.card := by
      have hc : (G.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card hGC
      linarith only [hc, hC]
    simp only [Finset.sum_const, nsmul_eq_mul]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_right hg (sq_nonneg c),
      mul_le_mul_of_nonneg_right hg' (sq_nonneg c)]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hvi : v i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  let a : Vec d := Pi.single i (-c / v i)
  have ha : v ⬝ᵥ a = -c := by
    simp only [a, dotProduct_single]
    field_simp
  have hm := ABBKS26.RefineAux.component_moments R (1 / 10000) hR.1.2.2.2
    (by norm_num) hres i v a hv j
  simp only [dotProduct_sub, ha, sub_neg_eq_add] at hm
  have hδ : (1 / 10000 : ℝ) / (d + 1 : ℝ) ^ 8 ≤ 1 / 10000 :=
    div_le_self (by norm_num) (one_le_pow₀ (by
      linarith only [Nat.cast_nonneg (α := ℝ) d] : (1 : ℝ) ≤ d + 1))
  let m := (v ⬝ᵥ R.model.mean j + c) ^ 2 + qform (R.model.cov j) v
  have hm0 : 0 ≤ m := add_nonneg (sq_nonneg _)
    ((hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v)
  have h2 := mul_le_mul_of_nonneg_left hm.1 hC.le
  have h4 := mul_le_mul_of_nonneg_left hm.2 hC.le
  rw [mul_inv_cancel_left₀ hC.ne'] at h2 h4
  apply retained_bounds C G (fun l ↦ v ⬝ᵥ R.clean l + c) m hGC hC hm0 hmiss
  · have hh := mul_le_mul_of_nonneg_right hδ (mul_nonneg hC.le hm0)
    change (C.card : ℝ) * ((1 - 9 * _) * m) ≤ _ at h2
    nlinarith only [h2, hh, mul_nonneg hC.le hm0]
  · have hh := mul_le_mul_of_nonneg_right hδ (mul_nonneg hC.le (sq_nonneg m))
    change _ ≤ (C.card : ℝ) * ((3 + 81 * _) * m ^ 2) at h4
    nlinarith only [h4, hh, mul_nonneg hC.le (sq_nonneg m)]


/-- Clearing one common denominator bounds a rational Gram determinant. -/
theorem determinant_floor (x : Fin n → Fin d → ℚ) (G : Finset (Fin n))
    (hG : (FrobFloor.gram x G).PosDef) (Q z : ℕ) (hQpos : 0 < Q)
    (hQbound : Q ≤ 2 ^ z)
    (hclear : ∀ l i, ∃ a : ℤ, (a : ℚ) = (Q : ℚ) * x l i) :
    1 / (2 : ℝ) ^ (2 * z * d) ≤ (FrobFloor.gram x G).det := by
  classical
  have hQ : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  choose a ha using hclear
  let Z : Matrix (Fin d) (Fin d) ℤ := ∑ l ∈ G, vecMulVec (a l) (a l)
  have hZ : Z.map (Int.castRingHom ℝ) = (Q : ℝ) ^ 2 • FrobFloor.gram x G := by
    ext i j
    dsimp only [Z, FrobFloor.gram, Matrix.map_apply, Matrix.smul_apply]
    simp only [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    change (↑(∑ l ∈ G, a l i * a l j) : ℝ) =
      (Q : ℝ) ^ 2 * ∑ l ∈ G, (x l i : ℝ) * (x l j : ℝ)
    simp only [Int.cast_sum, Int.cast_mul]
    have hc (l : Fin n) (i : Fin d) : (a l i : ℝ) = (Q : ℝ) * (x l i : ℝ) := by
      exact_mod_cast ha l i
    simp_rw [hc]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have heq : (Z.det : ℝ) = (Q : ℝ) ^ (2 * d) * (FrobFloor.gram x G).det := by
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
  have hQR : (Q : ℝ) ≤ (2 : ℝ) ^ z := by exact_mod_cast hQbound
  have hpow : (Q : ℝ) ^ (2 * d) ≤ (2 : ℝ) ^ (2 * z * d) := by
    have hh := pow_le_pow_left₀ hQ.le hQR (2 * d)
    rw [← pow_mul] at hh
    convert hh using 1
    congr 1
    ring
  rw [div_le_iff₀ (by positivity)]
  have hh := mul_le_mul_of_nonneg_right hpow hG.det_pos.le
  nlinarith only [heq, hZ1, hh]


/-- An affine form is represented by one extra, constant sample coordinate. -/
def augment (x : Fin n → Fin d → ℚ) (l : Fin n) : Fin (d + 1) → ℚ :=
  Fin.cons 1 (x l)

theorem augment_dot (x : Fin n → Fin d → ℚ) (l : Fin n) (v : Vec (d + 1)) :
    v ⬝ᵥ (fun i ↦ (augment x l i : ℝ)) =
      v 0 + Fin.tail v ⬝ᵥ (fun i ↦ (x l i : ℝ)) := by
  simp [dotProduct, Fin.sum_univ_succ, augment, Fin.tail]

/-- Retained affine moments give a positive definite augmented rational Gram matrix. -/
theorem component_gram (R : Robust.Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ Robust.maxContamination π t)
    (x : Fin n → Fin d → ℚ) (hx : R.observed = fun l i ↦ (x l i : ℝ)) (j : Fin k) :
    ∃ G : Finset (Fin n), (FrobFloor.gram (augment x) G).PosDef ∧
      ∀ v : Vec (d + 1), qform (FrobFloor.gram (augment x) G) v ≤
        2 * n * ((Fin.tail v ⬝ᵥ R.model.mean j + v 0) ^ 2 +
          qform (R.model.cov j) (Fin.tail v)) := by
  classical
  let C := R.reference.filter (fun l ↦ R.label l = j)
  let G := R.good.filter (fun l ↦ R.label l = j)
  have hC : 0 < (C.card : ℝ) := (retained_component R π t hR hπ he j).2.1
  have hagree (l : Fin n) (hl : l ∈ G) :
      (fun i ↦ (x l i : ℝ)) = R.clean l := by
    exact (congrFun hx l).symm.trans (hR.2.2.2.1 l (Finset.mem_filter.mp hl).1)
  have hform (v : Vec (d + 1)) : qform (FrobFloor.gram (augment x) G) v =
      ∑ l ∈ G, (Fin.tail v ⬝ᵥ R.clean l + v 0) ^ 2 := by
    rw [FrobFloor.gram_qform]
    apply Finset.sum_congr rfl
    intro l hl
    rw [augment_dot, hagree l hl, add_comm]
  have hpsd : (FrobFloor.gram (augment x) G).PosSemidef := by
    unfold FrobFloor.gram
    apply Matrix.posSemidef_sum
    intro l _
    simpa only [star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (fun i ↦ (augment x l i : ℝ))
  refine ⟨G, PosDef.of_dotProduct_mulVec_pos hpsd.1 ?_, ?_⟩
  · intro v hv
    have hm := (affine_component R π t hR hres hπ he j (Fin.tail v) (v 0)).1
    have hmpos : 0 < (Fin.tail v ⬝ᵥ R.model.mean j + v 0) ^ 2 +
        qform (R.model.cov j) (Fin.tail v) := by
      by_cases ht : Fin.tail v = 0
      · have hzero : v 0 ≠ 0 := by
          intro hz
          apply hv
          rw [← Fin.cons_self_tail v, hz, ht]
          ext i
          refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl
        simpa only [ht, zero_dotProduct, zero_add, qform, mulVec_zero,
          dotProduct_zero, add_zero] using sq_pos_of_ne_zero hzero
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
          ((hR.1.2.2.2 j).dotProduct_mulVec_pos ht)
    change 0 < qform (FrobFloor.gram (augment x) G) v
    rw [hform]
    exact (div_pos (mul_pos hC hmpos) (by norm_num)).trans_le hm
  · intro v
    rw [hform]
    apply (affine_component R π t hR hres hπ he j (Fin.tail v) (v 0)).2.trans
    have hc : (C.card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_le_univ C).trans_eq (Fintype.card_fin n)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
      (add_nonneg (sq_nonneg _)
        ((hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg _))


/-- The augmented Gram floor uses the original sample denominator, so adjoining the
constant coordinate does not enlarge the denominator exponent. -/
theorem augmented_lower (x : Fin n → Fin d → ℚ) (G : Finset (Fin n))
    (hG : (FrobFloor.gram (augment x) G).PosDef) (z : ℕ)
    (hn : n ≤ z) (hd : d ≤ z)
    (hx : (encPoints (pointsOf x)).length ≤ z) (v : Vec (d + 1)) :
    (1 / (2 : ℝ) ^ (6 * z * (d + 1))) * sqnorm v ≤
      qform (FrobFloor.gram (augment x) G) v := by
  let Q := FrobFloor.denominator (pointsOf x)
  have hdet := determinant_floor (augment x) G hG Q z
    (FrobFloor.denominator_pos _) ((FrobFloor.denominator_bound _).trans
      (Nat.pow_le_pow_right (by norm_num) hx)) (by
        intro l i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact ⟨Q, by simp [augment]⟩
        · simpa only [augment, Fin.cons_succ] using FrobFloor.denominator_clears x l j)
  have hb (l : Fin n) (i : Fin (d + 1)) :
      |(augment x l i : ℝ)| ≤ (2 : ℝ) ^ z := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [augment, Fin.cons_zero, Rat.cast_one, abs_one] using
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ z)
    · exact (FrobBounds.sample_entry x l j).trans (pow_le_pow_right₀ (by norm_num) hx)
  have he (l : Fin n) (i : Fin (d + 1)) :
      (augment x l i : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * z) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hb l i) 2
    rw [sq_abs, ← pow_mul] at hh
    convert hh using 1; congr 1; omega
  have hn' : (n : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast hn.trans (Nat.lt_two_pow_self (n := z)).le
  have hd' : (d + 1 : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast (by omega : d + 1 ≤ z + 1).trans
      (Nat.lt_two_pow_self (n := z))
  have ht : (FrobFloor.gram (augment x) G).trace ≤ (2 : ℝ) ^ (4 * z) := by
    have hs : (FrobFloor.gram (augment x) G).trace ≤
        (d + 1) * (n * (2 : ℝ) ^ (2 * z)) := by
      simp only [Matrix.trace, Matrix.diag, FrobFloor.gram, Matrix.sum_apply,
        vecMulVec_apply]
      calc
        _ ≤ ∑ _i : Fin (d + 1), ∑ _l ∈ G, (2 : ℝ) ^ (2 * z) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_le_sum fun l _ ↦ by simpa only [pow_two] using he l i
        _ = (d + 1) * (G.card * (2 : ℝ) ^ (2 * z)) := by simp
        _ ≤ _ := by
          gcongr
          exact_mod_cast (Finset.card_le_univ G).trans_eq (Fintype.card_fin n)
    calc
      _ ≤ (d + 1) * (n * (2 : ℝ) ^ (2 * z)) := hs
      _ ≤ (2 : ℝ) ^ z * ((2 : ℝ) ^ z * (2 : ℝ) ^ (2 * z)) := by gcongr
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hf := FrobFloor.spectral_floor _ hG (2 * z * (d + 1)) (4 * z) hdet ht v
  convert hf using 1; congr 2; ring


/-- The retained second moment also bounds absolute component means by sample magnitudes. -/
theorem component_mean_bound (R : Robust.Reference n k d) (π t : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ Robust.maxContamination π t)
    (x : Fin n → Fin d → ℚ) (hx : R.observed = fun l i ↦ (x l i : ℝ))
    (X : ℝ) (hX : 0 ≤ X) (hbound : ∀ l i, |(x l i : ℝ)| ≤ X)
    (j : Fin k) (i : Fin d) : |R.model.mean j i| ≤ 2 * X := by
  classical
  let C := R.reference.filter (fun l ↦ R.label l = j)
  let G := R.good.filter (fun l ↦ R.label l = j)
  let v : Vec d := Pi.single i 1
  have hCv := retained_component R π t hR hπ he j
  have hC : 0 < (C.card : ℝ) := hCv.2.1
  have hs := (affine_component R π t hR hres hπ he j v 0).1
  have hsum : (∑ l ∈ G, (v ⬝ᵥ R.clean l + 0) ^ 2) ≤ C.card * X ^ 2 := by
    calc
      _ ≤ ∑ _l ∈ G, X ^ 2 := by
        apply Finset.sum_le_sum
        intro l hl
        have ha : R.clean l = fun i ↦ (x l i : ℝ) :=
          (hR.2.2.2.1 l (Finset.mem_filter.mp hl).1).symm.trans (congrFun hx l)
        rw [ha]
        simpa [v] using pow_le_pow_left₀ (abs_nonneg _) (hbound l i) 2
      _ = G.card * X ^ 2 := by simp
      _ ≤ C.card * X ^ 2 := by
        gcongr
        exact hCv.1
  have hv : v ⬝ᵥ R.model.mean j + 0 = R.model.mean j i := by simp [v]
  rw [hv] at hs
  have hvar : 0 ≤ qform (R.model.cov j) v :=
    (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v
  have hm : (R.model.mean j i) ^ 2 ≤ (2 * X) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hs, hsum, mul_nonneg hC.le hvar]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by rwa [sq_abs])

/-- Affine coefficient bounds follow from one compatible augmented Gram matrix. -/
theorem coefficients (R : Robust.Reference n k d) (π t w : ℝ)
    (hR : R.Valid π) (hres : R.Resilient 4 (1 / 10000)) (hπ : π ≤ 1)
    (he : R.contamination ≤ Robust.maxContamination π t)
    (x : Fin n → Fin d → ℚ) (hx : R.observed = fun l i ↦ (x l i : ℝ))
    (j : Fin k) (z : ℕ) (hz : 64 ≤ z) (hn : n ≤ z) (hd : d ≤ z)
    (hxz : (encPoints (pointsOf x)).length ≤ z) (hw : 0 < w)
    (hscale : 40 / w ≤ (2 : ℝ) ^ (z + 6)) (b : Fin d → ℚ) (c : ℚ)
    (hm : ((fun i ↦ (b i : ℝ)) ⬝ᵥ R.model.mean j + c) ^ 2 +
      qform (R.model.cov j) (fun i ↦ (b i : ℝ)) ≤ 20 / w) :
    (∀ i, |b i| ≤ (2 : ℚ) ^ z ^ 3) ∧ |c| ≤ (2 : ℚ) ^ z ^ 3 := by
  classical
  let v : Fin (d + 1) → ℚ := Fin.cons c b
  let vR : Vec (d + 1) := fun i ↦ (v i : ℝ)
  obtain ⟨G, hG, hupper⟩ := component_gram R π t hR hres hπ he x hx j
  have hu : qform (FrobFloor.gram (augment x) G) vR ≤ 40 * n / w := by
    apply (hupper vR).trans
    have ht : Fin.tail vR = fun i ↦ (b i : ℝ) := rfl
    rw [ht]
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * n)
    change 2 * (n : ℝ) * (((fun i ↦ (b i : ℝ)) ⬝ᵥ R.model.mean j + c) ^ 2 +
      qform (R.model.cov j) (fun i ↦ (b i : ℝ))) ≤ _
    exact hh.trans_eq (by ring)
  have hl := augmented_lower x G hG z hn hd hxz vR
  have hn' : (n : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast hn.trans (Nat.lt_two_pow_self (n := z)).le
  let e := 6 * z * (d + 1) + (2 * z + 6)
  have hb : sqnorm vR ≤ (2 : ℝ) ^ e := by
    have hu' : 40 * n / w ≤ (2 : ℝ) ^ (2 * z + 6) := by
      calc
        _ = n * (40 / w) := by ring
        _ ≤ (2 : ℝ) ^ z * (2 : ℝ) ^ (z + 6) :=
          mul_le_mul hn' hscale (by positivity) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega
    have hh := hl.trans (hu.trans hu')
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), one_mul] at hh
    exact hh.trans_eq (by rw [← pow_add]; congr 1; dsimp only [e]; omega)
  have he : e ≤ z ^ 3 := by
    have h1 : 6 * z * (d + 1) ≤ 12 * z ^ 2 := by
      nlinarith only [Nat.mul_le_mul_left (6 * z) hd, hz]
    have h2 : 2 * z + 6 ≤ z ^ 2 := by nlinarith only [hz]
    have h3 : 13 * z ^ 2 ≤ z ^ 3 := by
      calc
        _ ≤ z * z ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    dsimp only [e]
    omega
  have hv (i : Fin (d + 1)) : |v i| ≤ (2 : ℚ) ^ z ^ 3 := by
    have hi : (vR i) ^ 2 ≤ sqnorm vR := by
      simpa only [sqnorm, dotProduct, ← pow_two] using
        Finset.single_le_sum (fun j _ ↦ sq_nonneg (vR j)) (Finset.mem_univ i)
    have hpow : (2 : ℝ) ^ e ≤ ((2 : ℝ) ^ z ^ 3) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hs : |vR i| ≤ (2 : ℝ) ^ z ^ 3 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      (by simpa only [sq_abs] using hi.trans (hb.trans hpow))
    change |(v i : ℝ)| ≤ _ at hs
    exact_mod_cast hs
  exact ⟨fun i ↦ hv i.succ, hv 0⟩


end

end ABBKS26.Assembly.Exec.RefineSynth.IdFloor
