module

public import BHSV25.Net.GSMachine
public import BHSV25.Net.Correct

/-!
# The greedy net is correct

For a symmetric integer table `Q` whose scaled real matrix `P = c Q` acts on the eigenbasis of a
symmetric matrix by numbers `φᵢ`, with `|φᵢ| ≤ ℓ` outside a set `R` of at most `T` indices, every
vector `w` of length at most `1` whose coefficients vanish outside `R` and where `φᵢ < h` is
within `2 √T / N + √n 2^(T+1) ℓ / h` of a candidate of the greedy net
(`BHSV25.Net.exists_cand_near`):

* **the greedy bound** (`BHSV25.Net.greedy_resid_le`): the columns of `P` are their parts on the
  eigenvectors in `R`, a space of dimension at most `T`, plus a part of norm at most `ℓ`; after
  `T` rounds every column has residual at most `2^(T+1) ℓ`;
* **the target**: `w = P x` with `‖x‖ ≤ 1 / h`, so its residual is at most `√n ‖x‖` times that;
* **the grid** (`BHSV25.Net.exists_grid_near`): the projection of `w` onto the chosen columns is
  within `2 √T / N` of a candidate in the ball, in the scaled Gram–Schmidt coordinates that the
  machine computes (`BHSV25.Net.rtZ_eq`).

The two filters of the algorithms, `((I - Ã) / 2)^E` and `Ã^(2m)`, then give the nets of the
bottom eigenspace and of the eigenspace of large eigenvalues in absolute value
(`BHSV25.Net.netGS_bottom_correct`, `BHSV25.Net.netGS_abs_correct`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral
open Cslib (rowEntry)

variable {n : ℕ}

/-! ### Lengths -/

theorem sqrt_dot_add_le (a b : Fin n → ℝ) :
    Real.sqrt ((a + b) ⬝ᵥ (a + b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h := abs_dotProduct_le a b
  have ha := Real.sq_sqrt (dot_self_nonneg a)
  have hb := Real.sq_sqrt (dot_self_nonneg b)
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm b a]
  nlinarith [le_abs_self (a ⬝ᵥ b)]

theorem sqrt_dot_sum_le {κ : Type*} (s : Finset κ) (y : κ → Fin n → ℝ) :
    Real.sqrt ((∑ k ∈ s, y k) ⬝ᵥ (∑ k ∈ s, y k)) ≤ ∑ k ∈ s, Real.sqrt (y k ⬝ᵥ y k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (sqrt_dot_add_le _ _).trans (by linarith)

theorem sqrt_dot_smul (a : ℝ) (y : Fin n → ℝ) :
    Real.sqrt ((a • y) ⬝ᵥ (a • y)) = |a| * Real.sqrt (y ⬝ᵥ y) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem sum_abs_le (x : Fin n → ℝ) : ∑ v, |x v| ≤ Real.sqrt n * Real.sqrt (x ⬝ᵥ x) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine Real.le_sqrt_of_sq_le ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ ↦ (1 : ℝ)) fun v ↦ |x v|
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at h
  simpa [dotProduct, sq] using h

/-! ### The eigenbasis -/

theorem eq_sum_coeff {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (x : Fin n → ℝ) :
    x = ∑ i, coeff hA i x • ⇑(hA.eigenvectorBasis i) := by
  classical
  refine eq_of_coeff_eq hA fun l ↦ ?_
  rw [coeff_sum]
  simp only [coeff_smul, coeff_eigenvector, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-! ### The general net -/

/-- The standard basis vector `e_v` (`0` for `v ≥ n`). -/
noncomputable def evec (n : ℕ) (v : ℕ) : Fin n → ℝ :=
  if hv : v < n then Pi.single ⟨v, hv⟩ 1 else 0

theorem evec_dotProduct (a b : ℕ) :
    evec n a ⬝ᵥ evec n b = if a = b ∧ a < n then 1 else 0 := by
  classical
  unfold evec
  by_cases ha : a < n <;> by_cases hb : b < n
  · simp only [ha, hb, dite_true, single_dotProduct, Pi.single_apply, one_mul, Fin.mk.injEq]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]
  · simp only [ha, hb, dite_true, dite_false, dotProduct_zero]
    have : a ≠ b := fun h ↦ hb (h ▸ ha)
    simp [this]
  · simp [ha, hb]
  · simp [ha, hb]

/-- **The general net.** For a symmetric integer table `Q` with `c Q` acting on the eigenbasis of
`A` by `φ`, `|φᵢ| ≤ ℓ` outside `R` (`|R| ≤ T`), and a target `w` supported on `R` where `φ ≥ h`,
some candidate is within `2 √T / N + √n 2^(T+1) ℓ / h` of `w`. -/
theorem exists_cand_near {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (Q : List (List ℤ)) (hQ : Q.length ≤ n) (hsym : ∀ u v : ℕ, rowEntry Q u v = rowEntry Q v u)
    {c : ℝ} (hc : 0 < c) (φ : Fin n → ℝ)
    (hP : ∀ i x, coeff hA i ((c • Matrix.of fun u v : Fin n ↦ (rowEntry Q u v : ℝ)) *ᵥ x) =
      φ i * coeff hA i x)
    (R : Finset (Fin n)) {T : ℕ} (hR : R.card ≤ T) {ℓ h : ℝ} (hℓ : 0 ≤ ℓ) (hh : 0 < h)
    (hφl : ∀ i ∉ R, |φ i| ≤ ℓ) (w : Fin n → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : ∀ i, coeff hA i w ≠ 0 → i ∈ R ∧ h ≤ φ i) {N B : ℕ} (hN : 0 < N)
    (hB : BallBudget N T B) :
    ∃ cand ∈ candsOf N B (dataOf n Q (gramRows n Q) (selOf n T (gramRows n Q))),
      Real.sqrt ((ratVec n cand - w) ⬝ᵥ (ratVec n cand - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt n * 2 ^ (T + 1) * ℓ / h := by
  classical
  set col := colZ n Q with hcol
  set G := gramRows n Q with hGdef
  have hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b := rowEntry_gramRows Q hQ
  set S := selOf n T G with hSdef
  have hSsel : S = greedySel n T (scoreR col) := selZ_eq G col hG n T
  set P : Matrix (Fin n) (Fin n) ℝ := c • Matrix.of fun u v : Fin n ↦ (rowEntry Q u v : ℝ)
    with hPdef
  set colP : ℕ → Fin n → ℝ := fun v ↦ c • col v with hcolP
  -- the columns of `P`
  have hcolPe : ∀ v, colP v = P *ᵥ evec n v := by
    intro v
    funext u
    by_cases hv : v < n
    · simp only [hcolP, evec, hv, dite_true, mulVec_single_one, Pi.smul_apply, hPdef,
        smul_eq_mul, hcol, colZ]
      simp [hsym]
    · simp only [hcolP, evec, hv, dite_false, mulVec_zero, Pi.zero_apply, Pi.smul_apply, hcol,
        colZ]
      rw [rowEntry_of_length_le (hQ.trans (not_lt.1 hv)), Int.cast_zero, smul_zero]
  -- the selection is the greedy selection of the columns of `P`
  have hcolsP : ∀ L : List ℕ, colsL colP L = fun j ↦ c • colsL col L j := fun L ↦ rfl
  have hSselP : S = greedySel n T (scoreR colP) := by
    rw [hSsel]
    refine greedySel_congr (fun L v _ ↦ ?_) (fun L u _ v _ ↦ ?_)
    · rw [scoreR, scoreR, hcolsP, det_gramF_smul_family]
      have : (0 : ℝ) < (c * c) ^ Fintype.card (Fin (L ++ [v]).length) := by positivity
      exact (mul_pos_iff_of_pos_left this).symm
    · rw [scoreR, scoreR, scoreR, scoreR, hcolsP, hcolsP, det_gramF_smul_family,
        det_gramF_smul_family]
      have hu : (L ++ [u]).length = (L ++ [v]).length := by simp
      simp only [Fintype.card_fin, hu]
      have : (0 : ℝ) < (c * c) ^ (L ++ [v]).length := by positivity
      exact (mul_lt_mul_iff_of_pos_left this).symm
  have hgood : GoodSel col n S := by rw [hSsel]; exact goodSel_greedySeq col n T
  have hdetS : (gramF (colsL col S)).det ≠ 0 := hgood.1.ne'
  -- the decomposition of the columns
  set u : Fin n → Fin n → ℝ := fun i ↦ ⇑(hA.eigenvectorBasis i) with hu
  set noise : (Fin n → ℝ) → Fin n → ℝ := fun y ↦
    ∑ i ∈ Finset.univ.filter (· ∉ R), (φ i * coeff hA i y) • u i with hnoise
  set bb : ℕ → Fin n → ℝ := fun v ↦ noise (evec n v) with hbb
  set aa : ℕ → Fin n → ℝ := fun v ↦ colP v - bb v with haa
  set V : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range fun i : R ↦ u i) with hV
  have hcoeffP : ∀ v i, coeff hA i (colP v) = φ i * coeff hA i (evec n v) := fun v i ↦ by
    rw [hcolPe, hP]
  have haV : ∀ v, aa v ∈ V := by
    intro v
    have hexp := eq_sum_coeff hA (colP v)
    have hsplit : colP v = ∑ i ∈ Finset.univ.filter (· ∈ R), (φ i * coeff hA i (evec n v)) • u i +
        bb v := by
      conv_lhs => rw [hexp]
      simp only [hcoeffP]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ R)]
    have : aa v = ∑ i ∈ Finset.univ.filter (· ∈ R), (φ i * coeff hA i (evec n v)) • u i := by
      rw [haa]; simp only; rw [hsplit]; abel
    rw [this]
    refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨i, (Finset.mem_filter.1 hi).2⟩, rfl⟩
  have hVdim : Module.finrank ℝ V ≤ T :=
    (finrank_range_le_card (R := ℝ) fun i : R ↦ u i).trans (by simpa using hR)
  -- the noise is small
  have hnoise_coeff : ∀ y l, coeff hA l (noise y) = if l ∉ R then φ l * coeff hA l y else 0 := by
    intro y l
    rw [hnoise, coeff_sum]
    simp only [coeff_smul, hu, coeff_eigenvector, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hnoise_lin : ∀ (L : List ℕ) (cc : Fin L.length → ℝ),
      ∑ j, cc j • bb L[j] = noise (∑ j, cc j • evec n L[j]) := by
    intro L cc
    refine eq_of_coeff_eq hA fun l ↦ ?_
    rw [coeff_sum, hnoise_coeff, coeff_sum]
    simp only [coeff_smul, hbb, hnoise_coeff]
    by_cases hl : l ∈ R
    · simp [hl]
    · simp only [hl, not_false_eq_true, ite_true]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hb : ∀ L : List ℕ, L.Nodup → ∀ cc : Fin L.length → ℝ,
      (∑ j, cc j • bb L[j]) ⬝ᵥ (∑ j, cc j • bb L[j]) ≤ ℓ ^ 2 * ∑ j, cc j ^ 2 := by
    intro L hL cc
    rw [hnoise_lin]
    set z := ∑ j, cc j • evec n L[j] with hz
    have hzz : z ⬝ᵥ z ≤ ∑ j, cc j ^ 2 := by
      rw [hz, sum_dotProduct]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      rw [dotProduct_sum, Finset.sum_eq_single j]
      · rw [smul_dotProduct, dotProduct_smul, evec_dotProduct, smul_eq_mul, smul_eq_mul]
        split_ifs <;> nlinarith [sq_nonneg (cc j)]
      · intro k _ hkj
        rw [smul_dotProduct, dotProduct_smul, evec_dotProduct]
        have : ¬ (L[j] = L[k] ∧ L[j] < n) := fun h ↦ hkj (Fin.ext
          ((hL.getElem_inj_iff).1 h.1).symm)
        have h0 : (if L[j] = L[k] ∧ L[j] < n then (1 : ℝ) else 0) = 0 :=
          ite_eq_right_iff.2 fun hh ↦ absurd hh this
        rw [h0, smul_zero, smul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hzz' : ∑ l, coeff hA l z ^ 2 ≤ ∑ j, cc j ^ 2 := by rw [sum_coeff_sq]; exact hzz
    rw [← sum_coeff_sq hA (noise z)]
    calc ∑ l, coeff hA l (noise z) ^ 2 ≤ ∑ l, ℓ ^ 2 * coeff hA l z ^ 2 := by
          refine Finset.sum_le_sum fun l _ ↦ ?_
          rw [hnoise_coeff]
          by_cases hl : l ∈ R
          · simp only [hl, not_true_eq_false, ite_false, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow]
            positivity
          · simp only [hl, not_false_eq_true, ite_true]
            rw [mul_pow]
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hφl l hl) 2
      _ = ℓ ^ 2 * ∑ l, coeff hA l z ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ℓ ^ 2 * ∑ j, cc j ^ 2 := mul_le_mul_of_nonneg_left hzz' (sq_nonneg _)
  -- the greedy bound for the columns of `P`
  have hgreedy : ∀ v < n, resid (colsL colP S) (colP v) ⬝ᵥ resid (colsL colP S) (colP v) ≤
      ((2 ^ (T + 1) - 1) * ℓ) ^ 2 := by
    intro v hv
    rw [hSselP]
    exact greedy_resid_le colP aa bb (fun v ↦ (sub_add_cancel (colP v) (bb v)).symm) V hVdim
      haV hℓ hb n hv
  -- the target
  set x := preimage hA φ w with hx
  have hPx : P *ᵥ x = w := by
    refine eq_of_coeff_eq hA fun l ↦ ?_
    rw [hP, coeff_preimage]
    by_cases hl : coeff hA l w = 0
    · rw [hl]; simp
    · have hφ := (hw l hl).2
      field_simp [(hh.trans_le hφ).ne']
  have hxx : x ⬝ᵥ x ≤ 1 / h ^ 2 := by
    rw [← sum_coeff_sq hA x]
    have hw' := hw1
    rw [← sum_coeff_sq hA w] at hw'
    calc ∑ l, coeff hA l x ^ 2 ≤ ∑ l, coeff hA l w ^ 2 / h ^ 2 := by
          refine Finset.sum_le_sum fun l _ ↦ ?_
          rw [coeff_preimage]
          by_cases hc0 : coeff hA l w = 0
          · simp [hc0]
          · have hφ := (hw l hc0).2
            rw [div_pow]
            exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (pow_le_pow_left₀ hh.le hφ 2)
      _ = (∑ l, coeff hA l w ^ 2) / h ^ 2 := by rw [Finset.sum_div]
      _ ≤ 1 / h ^ 2 := div_le_div_of_nonneg_right hw' (by positivity)
  have hwsum : w = ∑ v : Fin n, x v • colP v := by
    rw [← hPx]
    funext u'
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [hcolPe v]
    simp only [evec, v.2, dite_true, mulVec_single_one]
    simp [mul_comm]
  -- the residual of the target
  have hres : ∀ y, resid (colsL colP S) y = resid (colsL col S) y := fun y ↦ by
    rw [hcolsP]; exact resid_smul_family _ hdetS hc.ne' y
  have hresid_eq : resid (colsL col S) w = ∑ v : Fin n, x v • resid (colsL colP S) (colP v) := by
    conv_lhs => rw [hwsum]
    rw [resid_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [resid_smul, hres]
  have hresid_le : Real.sqrt (resid (colsL col S) w ⬝ᵥ resid (colsL col S) w) ≤
      Real.sqrt n * 2 ^ (T + 1) * ℓ / h := by
    rw [hresid_eq]
    refine (sqrt_dot_sum_le _ _).trans ?_
    have h1 : ∀ v : Fin n, Real.sqrt ((x v • resid (colsL colP S) (colP v)) ⬝ᵥ
        (x v • resid (colsL colP S) (colP v))) ≤ |x v| * (2 ^ (T + 1) * ℓ) := by
      intro v
      rw [sqrt_dot_smul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Real.sqrt_le_iff.2 ⟨by positivity, (hgreedy v v.2).trans ?_⟩
      have : (0 : ℝ) ≤ (2 ^ (T + 1) - 1) * ℓ :=
        mul_nonneg (by have : (1 : ℝ) ≤ 2 ^ (T + 1) := one_le_pow₀ (by norm_num); linarith) hℓ
      exact pow_le_pow_left₀ this (by nlinarith) 2
    refine (Finset.sum_le_sum fun v _ ↦ h1 v).trans ?_
    rw [← Finset.sum_mul]
    have h2 := sum_abs_le x
    have h3 : Real.sqrt (x ⬝ᵥ x) ≤ 1 / h := by
      rw [show 1 / h = Real.sqrt (1 / h ^ 2) by
        rw [Real.sqrt_div' 1 (sq_nonneg h), Real.sqrt_one, Real.sqrt_sq hh.le]]
      exact Real.sqrt_le_sqrt hxx
    calc (∑ v, |x v|) * (2 ^ (T + 1) * ℓ) ≤ (Real.sqrt n * (1 / h)) * (2 ^ (T + 1) * ℓ) :=
          mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left h3
            (Real.sqrt_nonneg _))) (by positivity)
      _ = Real.sqrt n * 2 ^ (T + 1) * ℓ / h := by ring
  -- the leading determinants are positive
  set k := S.length with hk
  have hSeq : S = greedySeq n (scoreR col) T := hSsel
  have hkT : k ≤ T := by rw [hk, hSeq]; exact length_greedySeq_le n (scoreR col) T
  have hpos : ∀ l ≤ k, 0 < deltaR col S l := fun l hl ↦ by
    rw [deltaR, hSeq, take_greedySeq n (scoreR col) (by rw [← hSeq]; exact hl)]
    exact (goodSel_greedySeq col n l).1
  have hΔ : ∀ l, ((deltaZ G S l : ℤ) : ℝ) = deltaR col S l := deltaZ_eq G col hG S
  set σ : ℕ → ℕ := sigmaZ G S with hσ
  have hX : ∀ l < k, (((deltaZ G S (l + 1) * deltaZ G S l).toNat : ℕ) : ℝ) =
      deltaR col S (l + 1) * deltaR col S l := by
    intro l hl
    have h1 : (0 : ℝ) < deltaZ G S (l + 1) * deltaZ G S l := by
      rw [hΔ, hΔ]; exact mul_pos (hpos _ hl) (hpos _ hl.le)
    have h2 : 0 ≤ deltaZ G S (l + 1) * deltaZ G S l := by exact_mod_cast h1.le
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h2, Int.cast_mul, hΔ, hΔ]
  have hX1 : ∀ l < k, 1 ≤ (deltaZ G S (l + 1) * deltaZ G S l).toNat := by
    intro l hl
    have h := hX l hl
    have h1 : (0 : ℝ) < ((deltaZ G S (l + 1) * deltaZ G S l).toNat : ℝ) := by
      rw [h]; exact mul_pos (hpos _ hl) (hpos _ hl.le)
    exact_mod_cast h1
  have hσpos : ∀ l < k, 0 < σ l := fun l hl ↦ Nat.sqrt_pos.2 (hX1 l hl)
  -- the scaled Gram–Schmidt vectors
  set q : Fin k → Fin n → ℝ := fun l ↦ (deltaR col S l / σ l) • gsR col S l with hq
  have horth : ∀ i j, i ≠ j → q i ⬝ᵥ q j = 0 := by
    intro i j hij
    rw [hq]
    simp only [smul_dotProduct, dotProduct_smul]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · rw [gsR_orth col S hpos h j.2]; simp
    · rw [dotProduct_comm, gsR_orth col S hpos h i.2]; simp
  have hqq : ∀ l : Fin k, q l ⬝ᵥ q l =
      ((deltaZ G S (l + 1) * deltaZ G S l).toNat : ℝ) / (σ l : ℝ) ^ 2 := by
    intro l
    rw [hX l l.2, hq]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [gsR_dot_self col S l.2 (hpos l l.2.le)]
    have h1 := hpos l l.2.le
    have h2 : (0 : ℝ) < σ l := by exact_mod_cast hσpos l l.2
    field_simp
  have hqb : ∀ l : Fin k, 1 ≤ q l ⬝ᵥ q l ∧ q l ⬝ᵥ q l ≤ 4 := by
    intro l
    rw [hqq l]
    set X := (deltaZ G S (l + 1) * deltaZ G S l).toNat with hXdef
    have h2 : (0 : ℝ) < σ l := by exact_mod_cast hσpos l l.2
    have hs1 : σ l ^ 2 ≤ X := Nat.sqrt_le' X
    have hs2 : X < (σ l + 1) ^ 2 := Nat.lt_succ_sqrt' X
    have hs3 : 1 ≤ σ l := hσpos l l.2
    constructor
    · rw [le_div_iff₀ (by positivity), one_mul]; exact_mod_cast hs1
    · rw [div_le_iff₀ (by positivity)]
      have : X ≤ 4 * σ l ^ 2 := by nlinarith
      exact_mod_cast this
  -- the projection of the target, in these coordinates
  set a : Fin k → ℝ := fun l ↦ (gsR col S l ⬝ᵥ w / (gsR col S l ⬝ᵥ gsR col S l)) *
    (σ l / deltaR col S l) with ha
  have hproj : w - resid (colsL col S) w = ∑ l, a l • q l := by
    rw [sub_resid_eq_sum col S hpos w, Finset.sum_range]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ha, hq, smul_smul]
    congr 1
    have h1 := (hpos l l.2.le).ne'
    have h2 : (σ l : ℝ) ≠ 0 := by exact_mod_cast (hσpos l l.2).ne'
    field_simp
  have hz : (∑ l, a l • q l) ⬝ᵥ (∑ l, a l • q l) ≤ 1 := by
    rw [← hproj]
    exact (sub_resid_dot_self_le col hdetS w).trans hw1
  obtain ⟨m, hm, hmball, herr⟩ := exists_grid_near q horth hqb a hz hN
  -- the candidate
  set rts := (List.range k).map (rtZ n Q G S) with hrts
  set sig := (List.range k).map (sigmaZ G S) with hsig
  have hrtslen : rts.length = k := by simp [hrts]
  have hm' : ∀ l, 0 ≤ m l + N := fun l ↦ by have := (abs_le.1 (hm l)).1; omega
  set f : Fin k → Fin (2 * N + 1) := fun l ↦ ⟨(m l + N).toNat, by
    have := (abs_le.1 (hm l)).2; omega⟩ with hf
  set ms := List.ofFn fun l ↦ (f l : ℕ) with hms
  have hball : ∑ l, (((f l : ℕ) : ℚ) - N) ^ 2 ≤ (N : ℚ) ^ 2 := by
    have e : ∀ l, (((f l : ℕ) : ℚ) - N) = (m l : ℚ) := fun l ↦ by
      simp only [hf]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hm' l)]
      push_cast
      ring
    simp only [e]
    have h : ((∑ l, ((m l : ℚ)) ^ 2 : ℚ) : ℝ) ≤ (((N : ℚ) ^ 2 : ℚ) : ℝ) := by
      push_cast
      exact hmball
    exact_mod_cast h
  have hmem : ms ∈ ballTuples B N k := ofFn_mem_ballTuples (hB.mono hkT) f hball
  refine ⟨candGS n N rts sig ms, ?_, ?_⟩
  · rw [candsOf, dataOf, hSdef]
    exact List.mem_map.2 ⟨ms, by rwa [hrtslen], rfl⟩
  · -- the candidate is `∑ (m_l / N) q_l`
    have hcand : ratVec n (candGS n N rts sig ms) = ∑ l, ((m l : ℝ) / N) • q l := by
      rw [ratVec_candGS, hrtslen, Finset.sum_range]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hrow : (fun u : Fin n ↦ (rowEntry rts l u : ℝ)) = deltaR col S l • gsR col S l :=
        rtZ_eq Q G hG S l.2 (hpos l l.2.le).ne'
      have hmsl : ((ms.getD l 0 : ℕ) : ℝ) - N = m l := by
        rw [hms, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        simp only [hf, Fin.eta]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (hm' l)]
        push_cast
        ring
      have hsigl : sig.getD l 0 = σ l := by rw [hsig, getD_map_range k _ _ l.2]
      rw [hrow, hmsl, hsigl, hq, smul_smul, smul_smul]
      congr 1
      have h2 : (σ l : ℝ) ≠ 0 := by exact_mod_cast (hσpos l l.2).ne'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
    rw [hcand]
    have hsplit : ∑ l, ((m l : ℝ) / N) • q l - w =
        (∑ l, ((m l : ℝ) / N) • q l - ∑ l, a l • q l) + -resid (colsL col S) w := by
      rw [← hproj]; abel
    rw [hsplit]
    refine (sqrt_dot_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Real.sqrt_le_sqrt herr).trans ?_
      have h4 : Real.sqrt (4 * k) = 2 * Real.sqrt k := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity), h4]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast hkT)) (by norm_num)) (by positivity)
    · rw [neg_dotProduct, dotProduct_neg, neg_neg]
      exact hresid_le

/-! ### Graphs -/

/-- The net always contains the zero vector: the tuple of zero coefficients. -/
theorem exists_zero_mem_candsOf (N B : ℕ) (d : ℕ × List (List ℤ) × List ℕ)
    (hB : BallBudget N d.2.1.length B) :
    ∃ c ∈ candsOf N B d, ratVec d.1 c = 0 := by
  set f : Fin d.2.1.length → Fin (2 * N + 1) := fun _ ↦ ⟨N, by omega⟩
  refine ⟨candGS d.1 N d.2.1 d.2.2 (List.ofFn fun l ↦ (f l : ℕ)),
    List.mem_map.2 ⟨_, ofFn_mem_ballTuples hB f (by simp [f]), rfl⟩, ?_⟩
  rw [ratVec_candGS]
  refine Finset.sum_eq_zero fun l hl ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_ofFn]
  simp [f]

theorem length_selOf_le (n T : ℕ) (G : List (List ℤ)) : (selOf n T G).length ≤ T :=
  length_greedySeq_le n (scoreZ G) T

theorem length_mulL (N : ℕ) (X Y : List (List ℤ)) : (mulL N X Y).length = N := by simp [mulL]

theorem length_powL (N : ℕ) (M : List (List ℤ)) (e : ℕ) : (powL N M e).length = N := by
  cases e with
  | zero => simp [powL, idL]
  | succ e => rw [powL, Function.iterate_succ_apply', length_mulL]

theorem length_of_mem_powL (N : ℕ) (M : List (List ℤ)) (e : ℕ) :
    ∀ r ∈ powL N M e, r.length = N := by
  intro r hr
  cases e with
  | zero =>
    obtain ⟨u, -, rfl⟩ := (by simpa [powL, idL] using hr :
      ∃ a < N, List.map (fun v ↦ if a = v then (1 : ℤ) else 0) (List.range N) = r)
    simp
  | succ e =>
    rw [powL, Function.iterate_succ_apply', mulL] at hr
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hr
    simp

theorem rowEntry_powL_of_le (N : ℕ) (M : List (List ℤ)) (e : ℕ) {u v : ℕ} (h : N ≤ u ∨ N ≤ v) :
    rowEntry (powL N M e) u v = 0 := by
  rcases h with h | h
  · exact rowEntry_of_length_le (by rw [length_powL]; exact h) v
  · by_cases hu : u < (powL N M e).length
    · have hmem : (powL N M e).getD u [] ∈ powL N M e := by
        rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _
      rw [rowEntry, List.getD_eq_default _ _ (by rw [length_of_mem_powL N M e _ hmem]; exact h)]
    · exact rowEntry_of_length_le (not_lt.1 hu) v

/-- The data of the net on a graph. -/
theorem gsData_graph' (bottom : Bool) (E T : ℕ) (G : Graph) :
    gsData bottom E T (G.1, adjTable G) =
      dataOf G.1 (powL G.1 (baseMat bottom G.1 (deg G.1 (adjTable G)) (adjTable G)) E)
        (gramRows G.1 (powL G.1 (baseMat bottom G.1 (deg G.1 (adjTable G)) (adjTable G)) E))
        (selOf G.1 T
          (gramRows G.1
            (powL G.1 (baseMat bottom G.1 (deg G.1 (adjTable G)) (adjTable G)) E))) := by
  simp only [gsData, filtQ, numV_graph]

/-- The net always contains the zero vector, on a graph. -/
theorem exists_zero_mem_netGS (bottom : Bool) (E T N B : ℕ) (G : Graph)
    (hB : BallBudget N T B) :
    ∃ c ∈ netGS bottom E T N B (G.1, adjTable G), ratVec G.1 c = 0 := by
  rw [netGS, gsData_graph']
  refine exists_zero_mem_candsOf N B _ (hB.mono ?_)
  simp only [dataOf, List.length_map, List.length_range]
  exact length_selOf_le _ _ _

/-- The data of the net on a graph with vertices of degree `d`. -/
theorem gsData_graph (bottom : Bool) (E T : ℕ) (G : Graph) {d : ℕ}
    (hdeg : deg G.1 (adjTable G) = d) :
    gsData bottom E T (G.1, adjTable G) =
      dataOf G.1 (powL G.1 (baseMat bottom G.1 d (adjTable G)) E)
        (gramRows G.1 (powL G.1 (baseMat bottom G.1 d (adjTable G)) E))
        (selOf G.1 T (gramRows G.1 (powL G.1 (baseMat bottom G.1 d (adjTable G)) E))) := by
  simp only [gsData, filtQ, numV_graph, hdeg]

/-- The eigenspace of the filter, for the facts of `BHSV25/Net/Correct.lean`. -/
def bParams (bottom : Bool) : Params := ⟨bottom⟩

/-- The real filter: `c Q = (M / D)^E` for `c = D^(-E)`. -/
theorem filter_eq (bottom : Bool) (G : Graph) (d E : ℕ) :
    ((denBase (bParams bottom) d : ℝ)⁻¹ ^ E) • (Matrix.of fun u v : Fin G.1 ↦
      (rowEntry (powL G.1 (baseMat bottom G.1 d (adjTable G)) E) u v : ℝ)) =
    ((denBase (bParams bottom) d : ℝ)⁻¹ • (toMat G.1 (baseMat bottom G.1 d (adjTable G))).map
      (Int.castRingHom ℝ)) ^ E := by
  rw [smul_pow, ← map_castRingHom_pow, ← toMat_powL]
  rfl

theorem rowEntry_powL_symm (bottom : Bool) (G : Graph) (d E : ℕ) (u v : ℕ) :
    rowEntry (powL G.1 (baseMat bottom G.1 d (adjTable G)) E) u v =
      rowEntry (powL G.1 (baseMat bottom G.1 d (adjTable G)) E) v u := by
  by_cases h : u < G.1 ∧ v < G.1
  · have hs := toMat_baseMat_symm (bParams bottom) G d
    have hs' : (toMat G.1 (powL G.1 (baseMat bottom G.1 d (adjTable G)) E))ᵀ =
        toMat G.1 (powL G.1 (baseMat bottom G.1 d (adjTable G)) E) := by
      rw [toMat_powL, transpose_pow]
      exact congrArg (· ^ E) hs
    have := congrFun (congrFun hs' ⟨u, h.1⟩) ⟨v, h.2⟩
    rw [transpose_apply] at this
    exact this.symm
  · have h' : G.1 ≤ u ∨ G.1 ≤ v := by omega
    rw [rowEntry_powL_of_le _ _ _ h', rowEntry_powL_of_le _ _ _ h'.symm]

/-- **The bottom net.** On a regular graph with at most `T` eigenvalues at most `-θ'`, the greedy
net with filter `((I - Ã) / 2)^E` contains, for every vector `w` of length at most `1` in the
span of the eigenvectors with eigenvalues at most `-θ`, a vector within
`2 √T / N + √n 2^(T+1) ((1 + θ') / (1 + θ))^E`. -/
theorem netGS_bottom_correct (G : Graph) (hreg : G.IsRegular) {θ' θ : ℝ} (hθ' : 0 < θ')
    (hθ : θ' < θ) {T : ℕ} (hT : (Finset.univ.filter fun i ↦ G.eig i ≤ -θ').card ≤ T) (E : ℕ)
    {N B : ℕ} (hN : 0 < N) (hB : BallBudget N T B) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : G.InEigSpan (· ≤ -θ) w) :
    ∃ c ∈ netGS true E T N B (G.1, adjTable G),
      Real.sqrt ((ratVec G.1 c - w) ⬝ᵥ (ratVec G.1 c - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * ((1 + θ') / (1 + θ)) ^ E := by
  obtain ⟨d, hregd⟩ := hreg
  have hbound :
      0 ≤ 2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * ((1 + θ') / (1 + θ)) ^ E := by
    have : 0 ≤ (1 + θ') / (1 + θ) := by apply div_nonneg <;> linarith
    positivity
  -- the zero vector is a candidate
  have hzero := exists_zero_mem_netGS true E T N B G hB
  have hwzero : w = 0 → ∃ c ∈ netGS true E T N B (G.1, adjTable G),
      Real.sqrt ((ratVec G.1 c - w) ⬝ᵥ (ratVec G.1 c - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * ((1 + θ') / (1 + θ)) ^ E := by
    rintro rfl
    obtain ⟨c, hc, hc0⟩ := hzero
    refine ⟨c, hc, ?_⟩
    rw [hc0, sub_zero, dotProduct_zero, Real.sqrt_zero]
    exact hbound
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · exact hwzero (funext fun i ↦ absurd i.2 (by omega))
  have hdeg : deg G.1 (adjTable G) = d := by rw [deg_graph G hn]; exact hregd _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine hwzero (eq_zero_of_inEigSpan G hw fun i ↦ ?_)
    rw [eig_eq_zero_of_deg_zero G hregd i]
    linarith
  -- the filter
  set c : ℝ := (denBase (bParams true) d : ℝ)⁻¹ ^ E with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < denBase (bParams true) d := by
      simp only [denBase, bParams, ite_true]; positivity
    positivity
  set φ : Fin G.1 → ℝ := fun i ↦ ((1 - G.eig i) / 2) ^ E with hφ
  have hP : ∀ i x, coeff G.normAdj_isHermitian i ((c • Matrix.of fun u v : Fin G.1 ↦
      (rowEntry (powL G.1 (baseMat true G.1 d (adjTable G)) E) u v : ℝ)) *ᵥ x) =
      φ i * coeff G.normAdj_isHermitian i x := by
    intro i x
    have hbase : (denBase (bParams true) d : ℝ)⁻¹ • (toMat G.1 (baseMat true G.1 d
        (adjTable G))).map (Int.castRingHom ℝ) = (1 / 2 : ℝ) • (1 - G.normAdj) :=
      bottom_base (bParams true) rfl G hregd hd
    rw [hc, filter_eq, hbase]
    exact coeff_pow_mulVec _ (coeff_halfSub G i) E x
  have hb01 : ∀ i, 0 ≤ (1 - G.eig i) / 2 := fun i ↦ by
    have := abs_le.1 (G.abs_eig_le_one i); linarith
  obtain ⟨cand, hcand, hdist⟩ := exists_cand_near G.normAdj_isHermitian
    (powL G.1 (baseMat true G.1 d (adjTable G)) E) (by rw [length_powL])
    (rowEntry_powL_symm true G d E) hc0 φ hP (Finset.univ.filter fun i ↦ G.eig i ≤ -θ') hT
    (ℓ := ((1 + θ') / 2) ^ E) (h := ((1 + θ) / 2) ^ E) (by positivity)
    (pow_pos (by linarith) E)
    (fun i hi ↦ by
      have hi' : -θ' < G.eig i := by simpa using hi
      rw [hφ, abs_of_nonneg (pow_nonneg (hb01 i) _)]
      exact pow_le_pow_left₀ (hb01 i) (by linarith) E)
    w hw1
    (fun i hi ↦ by
      have hle : G.eig i ≤ -θ := by
        by_contra hcon
        exact hi (hw i hcon)
      refine ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith, ?_⟩
      exact pow_le_pow_left₀ (by linarith) (by linarith) E)
    hN hB
  refine ⟨cand, ?_, hdist.trans (le_of_eq ?_)⟩
  · rw [netGS, gsData_graph true E T G hdeg]; exact hcand
  · have h1 : (1 + θ : ℝ) ≠ 0 := by linarith
    congr 1
    rw [mul_div_assoc, ← div_pow,
      show (1 + θ') / 2 / ((1 + θ) / 2) = (1 + θ') / (1 + θ) by field_simp]

/-- **The absolute net.** On a regular graph with at most `T` eigenvalues at least `θ'` in absolute
value, the greedy net with filter `Ã^(2m)` contains, for every vector `w` of length at most `1`
in the span of the eigenvectors with eigenvalues at least `θ` in absolute value, a vector within
`2 √T / N + √n 2^(T+1) (θ' / θ)^(2m)`. -/
theorem netGS_abs_correct (G : Graph) (hreg : G.IsRegular) {θ' θ : ℝ} (hθ' : 0 < θ')
    (hθ : θ' < θ) {T : ℕ} (hT : (Finset.univ.filter fun i ↦ θ' ≤ |G.eig i|).card ≤ T) (m : ℕ)
    {N B : ℕ} (hN : 0 < N) (hB : BallBudget N T B) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : G.InEigSpan (fun μ ↦ θ ≤ |μ|) w) :
    ∃ c ∈ netGS false (2 * m) T N B (G.1, adjTable G),
      Real.sqrt ((ratVec G.1 c - w) ⬝ᵥ (ratVec G.1 c - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * (θ' / θ) ^ (2 * m) := by
  obtain ⟨d, hregd⟩ := hreg
  have hθ0 : 0 < θ := hθ'.trans hθ
  have hbound : 0 ≤ 2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * (θ' / θ) ^ (2 * m) := by
    have : 0 ≤ θ' / θ := div_nonneg hθ'.le hθ0.le
    positivity
  have hwzero : w = 0 → ∃ c ∈ netGS false (2 * m) T N B (G.1, adjTable G),
      Real.sqrt ((ratVec G.1 c - w) ⬝ᵥ (ratVec G.1 c - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * (θ' / θ) ^ (2 * m) := by
    rintro rfl
    obtain ⟨c, hc, hc0⟩ := exists_zero_mem_netGS false (2 * m) T N B G hB
    refine ⟨c, hc, ?_⟩
    rw [hc0, sub_zero, dotProduct_zero, Real.sqrt_zero]
    exact hbound
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · exact hwzero (funext fun i ↦ absurd i.2 (by omega))
  have hdeg : deg G.1 (adjTable G) = d := by rw [deg_graph G hn]; exact hregd _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine hwzero (eq_zero_of_inEigSpan G hw fun i ↦ ?_)
    rw [eig_eq_zero_of_deg_zero G hregd i, abs_zero, not_le]
    exact hθ0
  -- the filter
  set c : ℝ := (denBase (bParams false) d : ℝ)⁻¹ ^ (2 * m) with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < denBase (bParams false) d := by
      simp only [denBase, bParams, Bool.false_eq_true, ite_false, one_mul]; exact_mod_cast hd
    positivity
  set φ : Fin G.1 → ℝ := fun i ↦ (G.eig i ^ 2) ^ m with hφ
  have hP : ∀ i x, coeff G.normAdj_isHermitian i ((c • Matrix.of fun u v : Fin G.1 ↦
      (rowEntry (powL G.1 (baseMat false G.1 d (adjTable G)) (2 * m)) u v : ℝ)) *ᵥ x) =
      φ i * coeff G.normAdj_isHermitian i x := by
    intro i x
    have hbase : (denBase (bParams false) d : ℝ)⁻¹ • (toMat G.1 (baseMat false G.1 d
        (adjTable G))).map (Int.castRingHom ℝ) = G.normAdj :=
      abs_base (bParams false) rfl G hregd
    rw [hc, filter_eq, hbase, coeff_pow_mulVec _ (fun y ↦ coeff_mulVec _ i y) (2 * m) x]
    simp only [hφ, Graph.eig, ← pow_mul]
  have hb : ∀ i, 0 ≤ G.eig i ^ 2 := fun i ↦ sq_nonneg _
  obtain ⟨cand, hcand, hdist⟩ := exists_cand_near G.normAdj_isHermitian
    (powL G.1 (baseMat false G.1 d (adjTable G)) (2 * m)) (by rw [length_powL])
    (rowEntry_powL_symm false G d (2 * m)) hc0 φ hP
    (Finset.univ.filter fun i ↦ θ' ≤ |G.eig i|) hT
    (ℓ := (θ' ^ 2) ^ m) (h := (θ ^ 2) ^ m) (by positivity) (by positivity)
    (fun i hi ↦ by
      have hi' : |G.eig i| < θ' := by simpa using hi
      rw [hφ, abs_of_nonneg (pow_nonneg (hb i) _)]
      refine pow_le_pow_left₀ (hb i) ?_ m
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hi'.le 2)
    w hw1
    (fun i hi ↦ by
      have hle : θ ≤ |G.eig i| := by
        by_contra hcon
        exact hi (hw i hcon)
      refine ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith, ?_⟩
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [← sq_abs (G.eig i)]
      exact pow_le_pow_left₀ hθ0.le hle 2)
    hN hB
  refine ⟨cand, ?_, hdist.trans (le_of_eq ?_)⟩
  · rw [netGS, gsData_graph false (2 * m) T G hdeg]; exact hcand
  · congr 1
    rw [mul_div_assoc, ← div_pow, ← div_pow, ← pow_mul]

end Net

end BHSV25
