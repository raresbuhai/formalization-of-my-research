module

public import Background.SumOfSquares.Normed

/-!
# Boolean variables

Sum-of-squares consequences of the Boolean constraints `xᵢ² = xᵢ`, for systems that contain them
for every variable (`SoS.Boolean A`). For a set `S` of variables, `x_S = ∏ i ∈ S, xᵢ` (`SoS.xS`).

* `SoS.Boolean.sq_sub`: `x_S² = x_S`, in degree `2 |S|`.
* `SoS.Boolean.X_mul_sub`: `xᵢ x_S = x_S` for `i ∈ S`.
* `SoS.Boolean.nonneg`: `x_S ≥ 0`; `SoS.Boolean.mul_nonneg`: `x_S x_T ≥ 0`.
* `SoS.Boolean.litProd_nonneg`: a product of literals `xᵢ` and `1 - xᵢ` is nonnegative.
* `SoS.Boolean.pow_sub_esymm`: the powers of `s = ∑ i ∈ U, xᵢ` expand into the elementary
  symmetric polynomials `e_m = ∑_{S ⊆ U, |S| = m} x_S` (`SoS.esymmOn`):
  `s^t = ∑_{m ≤ t} a(t, m) e_m`, in degree `2t`. The coefficients `a(t, m) = m! S(t, m) ≥ 0`
  (`SoS.stirlingCoeff`, with `S` the Stirling numbers of the second kind) count the maps from a
  `t`-set onto an `m`-set. They follow from `s e_m = m e_m + (m + 1) e_{m+1}`.

All norms are explicit. The equalities `h = 0` of a system are pairs of constraints `h ≥ 0` and
`-h ≥ 0` (`SoS.HasEq`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*}

/-- `A` contains the equality `h = 0`: both `h ≥ 0` and `-h ≥ 0`. -/
def HasEq (A : System σ ℝ) (h : MvPolynomial σ ℝ) : Prop := h ∈ A ∧ -h ∈ A

theorem HasEq.derivesEq {A : System σ ℝ} {h : MvPolynomial σ ℝ} (hh : HasEq A h) {k : ℕ}
    {M : ℝ} (hdeg : h.totalDegree ≤ k) (hM : 1 ≤ M) : DerivesEq A k M h :=
  DerivesEq.of_mem hh.1 hh.2 hdeg hM

/-- All variables are Boolean: `A` contains `xᵢ² = xᵢ` for every `i`. -/
def Boolean (A : System σ ℝ) : Prop := ∀ i, HasEq A (X i ^ 2 - X i)

/-- The monomial `x_S = ∏ i ∈ S, xᵢ` of a set `S` of variables. -/
noncomputable def xS (S : Finset σ) : MvPolynomial σ ℝ := ∏ i ∈ S, X i

@[simp] theorem xS_empty : xS (∅ : Finset σ) = 1 := prod_empty

theorem xS_insert [DecidableEq σ] {i : σ} {S : Finset σ} (h : i ∉ S) :
    xS (insert i S) = X i * xS S :=
  prod_insert h

theorem X_mul_xS_erase [DecidableEq σ] {i : σ} {S : Finset σ} (h : i ∈ S) :
    X i * xS (S.erase i) = xS S :=
  mul_prod_erase S _ h

theorem totalDegree_xS_le (S : Finset σ) : (xS S).totalDegree ≤ S.card :=
  (totalDegree_finsetProd _ _).trans (by simp)

theorem coeffNorm1_xS_le (S : Finset σ) : coeffNorm1 (xS S) ≤ 1 :=
  coeffNorm1_prod_X_le S

theorem totalDegree_X_sq_sub_X_le (i : σ) : (X i ^ 2 - X i : MvPolynomial σ ℝ).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) (by rw [totalDegree_X]; omega))

theorem coeffNorm1_X_sq_le (i : σ) : coeffNorm1 (X i ^ 2 : MvPolynomial σ ℝ) ≤ 1 :=
  (coeffNorm1_pow_le _ 2).trans (by rw [coeffNorm1_X]; norm_num)

/-- `x_S x_T = x_{S ∩ T}² x_{S ∖ T ∪ T ∖ S}`. -/
theorem xS_mul_xS [DecidableEq σ] (S T : Finset σ) :
    xS S * xS T = xS (S ∩ T) ^ 2 * xS (S \ T ∪ T \ S) := by
  unfold xS
  rw [prod_union disjoint_sdiff_sdiff, ← prod_inter_mul_prod_sdiff S T, ←
    prod_inter_mul_prod_sdiff T S, inter_comm T S]
  ring

namespace Boolean

variable {A : System σ ℝ}

theorem eq (hB : Boolean A) (i : σ) : DerivesEq A 2 1 (X i ^ 2 - X i) :=
  (hB i).derivesEq (totalDegree_X_sq_sub_X_le i) le_rfl

/-- `x_S² = x_S`. -/
theorem sq_sub (hB : Boolean A) (S : Finset σ) :
    DerivesEq A (2 * S.card) (4 * S.card) (xS S ^ 2 - xS S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using DerivesEq.zero A 0 le_rfl
  | insert a S ha ih =>
    rw [xS_insert ha, card_insert_of_notMem ha]
    have h₁ := ih.mulSOS (IsSOS.sq (X a))
    have h₂ := (hB.eq a).mul (xS S)
    have hd₁ := totalDegree_X_pow (R := ℝ) a 2
    have hd₂ := totalDegree_xS_le S
    have hn₁ := coeffNorm1_X_sq_le (σ := σ) a
    have hn₂ := coeffNorm1_xS_le S
    refine ((h₁.mono (k' := 2 * (S.card + 1)) (by omega) (M' := 4 * S.card) ?_).add
      (h₂.mono (k' := 2 * (S.card + 1)) (by omega) (M' := 4) ?_)).mono le_rfl
      (by push_cast; linarith) |>.congr (by ring)
    · nlinarith [coeffNorm1_nonneg (X a ^ 2 : MvPolynomial σ ℝ)]
    · nlinarith [coeffNorm1_nonneg (xS S)]

/-- `xᵢ x_S = x_S` for `i ∈ S`. -/
theorem X_mul_sub (hB : Boolean A) {S : Finset σ} {i : σ} (hi : i ∈ S) :
    DerivesEq A (2 * S.card) 4 (X i * xS S - xS S) := by
  classical
  have h := (hB.eq i).mul (xS (S.erase i))
  have hd := totalDegree_xS_le (S.erase i)
  have hc := card_erase_of_mem hi
  have hpos := card_pos.2 ⟨i, hi⟩
  have hn := coeffNorm1_xS_le (S.erase i)
  refine (h.mono (by omega) ?_).congr ?_
  · nlinarith [coeffNorm1_nonneg (xS (S.erase i))]
  · rw [← X_mul_xS_erase hi]
    ring

/-- `x_S ≥ 0`, as `x_S = x_S² - (x_S² - x_S)`. -/
theorem nonneg (hB : Boolean A) (S : Finset σ) :
    DerivesN A (2 * S.card) (4 * S.card + 1) (xS S) := by
  have h₁ := DerivesN.ofIsSOS A (IsSOS.sq (xS S)) (k := 2 * S.card)
    ((totalDegree_pow _ 2).trans (by have := totalDegree_xS_le S; omega))
    ((coeffNorm1_pow_le _ 2).trans (pow_le_one₀ (coeffNorm1_nonneg _) (coeffNorm1_xS_le S)))
  refine ((h₁.add (hB.sq_sub S).2).mono le_rfl (by linarith)).congr (by ring)

/-- `x_S x_T ≥ 0`, from `x_S x_T = x_{S ∩ T}² x_{S ∖ T ∪ T ∖ S}`. -/
theorem mul_nonneg (hB : Boolean A) (S T : Finset σ) :
    DerivesN A (2 * (S.card + T.card)) (4 * (S.card + T.card) + 1) (xS S * xS T) := by
  classical
  have h := (hB.nonneg (S \ T ∪ T \ S)).mulSOS (IsSOS.sq (xS (S ∩ T)))
  have hR : (S \ T ∪ T \ S).card = (S \ T).card + (T \ S).card :=
    card_union_of_disjoint disjoint_sdiff_sdiff
  have h₁ := card_inter_add_card_sdiff S T
  have h₂ := card_inter_add_card_sdiff T S
  rw [inter_comm T S] at h₂
  have hd : (xS (S ∩ T) ^ 2).totalDegree ≤ 2 * (S ∩ T).card :=
    (totalDegree_pow _ 2).trans (by have := totalDegree_xS_le (S ∩ T); omega)
  have hn : coeffNorm1 (xS (S ∩ T) ^ 2) ≤ 1 :=
    (coeffNorm1_pow_le _ 2).trans (pow_le_one₀ (coeffNorm1_nonneg _) (coeffNorm1_xS_le _))
  refine (h.mono (by omega) ?_).congr (xS_mul_xS S T).symm
  have : ((S \ T ∪ T \ S).card : ℝ) ≤ S.card + T.card := by exact_mod_cast (by omega)
  nlinarith [coeffNorm1_nonneg (xS (S ∩ T) ^ 2)]

end Boolean

/-! ### Powers of a sum of Boolean variables -/

/-- The elementary symmetric polynomial `e_m = ∑_{S ⊆ U, |S| = m} x_S` of the variables in `U`. -/
noncomputable def esymmOn (U : Finset σ) (m : ℕ) : MvPolynomial σ ℝ :=
  ∑ S ∈ U.powersetCard m, xS S

/-- The coefficients `a(t, m) = m! S(t, m)` of `s^t = ∑_m a(t, m) e_m` for a sum `s` of Boolean
variables: `a(0, 0) = 1` and `a(t + 1, m + 1) = (m + 1) (a(t, m) + a(t, m + 1))`. -/
def stirlingCoeff : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | t + 1, m + 1 => (m + 1) * (stirlingCoeff t m + stirlingCoeff t (m + 1))

theorem stirlingCoeff_eq_zero_of_lt : ∀ {t m : ℕ}, t < m → stirlingCoeff t m = 0
  | 0, _ + 1, _ => rfl
  | t + 1, m + 1, h => by
    rw [stirlingCoeff, stirlingCoeff_eq_zero_of_lt (by omega : t < m),
      stirlingCoeff_eq_zero_of_lt (by omega : t < m + 1), Nat.mul_zero]

/-- The sum of the coefficients, the ordered Bell number, is at most `(2t + 1)^t`. -/
theorem sum_stirlingCoeff_le (t : ℕ) :
    ∑ m ∈ range (t + 1), stirlingCoeff t m ≤ (2 * t + 1) ^ t := by
  induction t with
  | zero => simp [stirlingCoeff]
  | succ t ih =>
    rw [sum_range_succ', stirlingCoeff]
    simp only [stirlingCoeff, add_zero]
    have h₁ : ∀ m ∈ range (t + 1), (m + 1) * (stirlingCoeff t m + stirlingCoeff t (m + 1)) ≤
        (t + 1) * (stirlingCoeff t m + stirlingCoeff t (m + 1)) := fun m hm ↦
      Nat.mul_le_mul_right _ (by have := mem_range.1 hm; omega)
    have h₂ : ∑ m ∈ range (t + 1), stirlingCoeff t (m + 1) ≤
        ∑ m ∈ range (t + 1), stirlingCoeff t m := by
      have e1 := sum_range_succ' (stirlingCoeff t) (t + 1)
      have e2 := sum_range_succ (stirlingCoeff t) (t + 1)
      rw [stirlingCoeff_eq_zero_of_lt (by omega : t < t + 1), add_zero] at e2
      omega
    calc ∑ m ∈ range (t + 1), (m + 1) * (stirlingCoeff t m + stirlingCoeff t (m + 1))
        ≤ ∑ m ∈ range (t + 1), (t + 1) * (stirlingCoeff t m + stirlingCoeff t (m + 1)) :=
          sum_le_sum h₁
      _ = (t + 1) * (∑ m ∈ range (t + 1), stirlingCoeff t m +
            ∑ m ∈ range (t + 1), stirlingCoeff t (m + 1)) := by
          rw [← mul_sum, sum_add_distrib]
      _ ≤ (t + 1) * (2 * (2 * t + 1) ^ t) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * (t + 1)) * (2 * t + 1) ^ t := by ring
      _ ≤ (2 * (t + 1) + 1) * (2 * (t + 1) + 1) ^ t :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) t)
      _ = (2 * (t + 1) + 1) ^ (t + 1) := by ring

section Esymm

variable [DecidableEq σ]

/-- Double counting: the pairs `(S, i)` with `|S| = m` and `i ∈ U ∖ S` are the pairs `(T, i)`
with `|T| = m + 1` and `i ∈ T`, by `T = S ∪ {i}`. -/
theorem sum_powersetCard_sdiff {R : Type*} [AddCommMonoid R] (U : Finset σ) (m : ℕ)
    (f : Finset σ → R) :
    ∑ S ∈ U.powersetCard m, ∑ i ∈ U \ S, f (insert i S) =
      ∑ T ∈ U.powersetCard (m + 1), ∑ _i ∈ T, f T := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ ↦ ⟨insert x.2 x.1, x.2⟩) (fun y _ ↦ ⟨y.1.erase y.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨S, i⟩ h
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at h ⊢
    exact ⟨⟨insert_subset h.2.1 h.1.1, by rw [card_insert_of_notMem h.2.2, h.1.2]⟩,
      mem_insert_self _ _⟩
  · rintro ⟨T, i⟩ h
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at h ⊢
    exact ⟨⟨(erase_subset _ _).trans h.1.1, by rw [card_erase_of_mem h.2, h.1.2]; rfl⟩,
      h.1.1 h.2, notMem_erase _ _⟩
  · rintro ⟨S, i⟩ h
    simp only [mem_sigma, mem_sdiff] at h
    simp [erase_insert h.2.2]
  · rintro ⟨T, i⟩ h
    simp only [mem_sigma] at h
    simp [insert_erase h.2]
  · intro _ _
    rfl

omit [DecidableEq σ] in
/-- `s e_m = ∑_{|S| = m} ∑_{i ∈ S} xᵢ x_S + (m + 1) e_{m+1}` for `s = ∑ i ∈ U, xᵢ`. -/
theorem sum_X_mul_esymmOn (U : Finset σ) (m : ℕ) :
    (∑ i ∈ U, X i) * esymmOn U m =
      ∑ S ∈ U.powersetCard m, ∑ i ∈ S, X i * xS S + C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1) := by
  classical
  have hsplit : ∀ S ∈ U.powersetCard m, ∑ i ∈ U, X i * xS S =
      ∑ i ∈ S, X i * xS S + ∑ i ∈ U \ S, xS (insert i S) := by
    intro S hS
    rw [← sum_sdiff (mem_powersetCard.1 hS).1, add_comm]
    congr 1
    exact sum_congr rfl fun i hi ↦ (xS_insert (mem_sdiff.1 hi).2).symm
  rw [esymmOn, mul_sum, sum_congr rfl fun S _ ↦ (sum_mul U (fun i ↦ X i) (xS S)),
    sum_congr rfl hsplit, sum_add_distrib, sum_powersetCard_sdiff, esymmOn, mul_sum]
  congr 1
  refine sum_congr rfl fun T hT ↦ ?_
  rw [sum_const, (mem_powersetCard.1 hT).2, nsmul_eq_mul, ← map_natCast C]

omit [DecidableEq σ] in
/-- `∑_{|S| = m} ∑_{i ∈ S} x_S = m e_m`. -/
theorem sum_sum_xS (U : Finset σ) (m : ℕ) :
    ∑ S ∈ U.powersetCard m, ∑ _i ∈ S, xS S = C (m : ℝ) * esymmOn U m := by
  rw [esymmOn, mul_sum]
  refine sum_congr rfl fun S hS ↦ ?_
  rw [sum_const, (mem_powersetCard.1 hS).2, nsmul_eq_mul, ← map_natCast C]

omit [DecidableEq σ] in
/-- The recursion of the coefficients:
`∑_{m ≤ t} a(t, m) (m e_m + (m + 1) e_{m+1}) = ∑_{m ≤ t+1} a(t + 1, m) e_m`. -/
theorem sum_stirlingCoeff_succ (U : Finset σ) (t : ℕ) :
    ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) *
        (C (m : ℝ) * esymmOn U m + C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1)) =
      ∑ m ∈ range (t + 2), C (stirlingCoeff (t + 1) m : ℝ) * esymmOn U m := by
  have hshift : ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * (C (m : ℝ) * esymmOn U m) =
      ∑ m ∈ range (t + 1), C (stirlingCoeff t (m + 1) : ℝ) *
        (C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1)) := by
    have h₁ := sum_range_succ' (fun m ↦ C (stirlingCoeff t m : ℝ) * (C (m : ℝ) * esymmOn U m))
      (t + 1)
    have h₂ := sum_range_succ (fun m ↦ C (stirlingCoeff t m : ℝ) * (C (m : ℝ) * esymmOn U m))
      (t + 1)
    rw [stirlingCoeff_eq_zero_of_lt (by omega : t < t + 1)] at h₂
    simp only [Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero] at h₁ h₂
    rw [← h₂, h₁]
  rw [sum_range_succ' _ (t + 1)]
  simp only [stirlingCoeff, Nat.cast_zero, map_zero, zero_mul, add_zero, mul_add,
    sum_add_distrib]
  rw [hshift, ← sum_add_distrib]
  refine sum_congr rfl fun m _ ↦ ?_
  push_cast
  simp only [map_add, map_mul, map_one]
  ring

end Esymm

namespace Boolean

variable {A : System σ ℝ}

/-- The norm bound of `SoS.Boolean.pow_sub_esymm`. -/
noncomputable def powNorm (n t : ℕ) : ℝ :=
  4 * t ^ 2 * ((n : ℝ) + 1) ^ (2 * t) * (2 * t + 1) ^ t

theorem powNorm_nonneg (n t : ℕ) : 0 ≤ powNorm n t := by
  unfold powNorm
  positivity

/-- The Boolean reductions in `s e_m`: `∑_{|S| = m} ∑_{i ∈ S} xᵢ x_S = m e_m`. -/
theorem sum_X_mul_xS_sub (hB : Boolean A) (U : Finset σ) {m k : ℕ} (hm : m ≤ k) :
    DerivesEq A (2 * k) (4 * m * (U.card.choose m))
      (∑ S ∈ U.powersetCard m, ∑ i ∈ S, (X i * xS S - xS S)) := by
  have h := DerivesEq.sum (k := 2 * k) (U.powersetCard m) fun S hS ↦
    DerivesEq.sum (k := 2 * k) S fun i hi ↦
      (hB.X_mul_sub hi).mono (by have := (mem_powersetCard.1 hS).2; omega) le_rfl
  refine h.mono le_rfl (le_of_eq ?_)
  have hcard : ∀ S ∈ U.powersetCard m, ∑ _i ∈ S, (4 : ℝ) = 4 * m := by
    intro S hS
    rw [sum_const, (mem_powersetCard.1 hS).2, nsmul_eq_mul]
    ring
  rw [sum_congr rfl hcard, sum_const, card_powersetCard, nsmul_eq_mul]
  ring

/-- **Powers of a sum of Boolean variables.** `s^t = ∑_{m ≤ t} a(t, m) e_m` for
`s = ∑ i ∈ U, xᵢ`, in degree `2t`. -/
theorem pow_sub_esymm (hB : Boolean A) (U : Finset σ) (t : ℕ) :
    DerivesEq A (2 * t) (powNorm U.card t)
      ((∑ i ∈ U, X i) ^ t - ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * esymmOn U m) := by
  classical
  induction t with
  | zero =>
    refine (DerivesEq.zero A 0 (powNorm_nonneg _ 0)).congr ?_
    simp [stirlingCoeff, esymmOn, powersetCard_zero]
  | succ t ih =>
    have hs : coeffNorm1 (∑ i ∈ U, X i : MvPolynomial σ ℝ) ≤ U.card :=
      (coeffNorm1_sum_le _ _).trans (by simp [coeffNorm1_X])
    have hsd : (∑ i ∈ U, X i : MvPolynomial σ ℝ).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]
    -- `s (s^t - E_t)`.
    have h₁ := ih.mul (∑ i ∈ U, X i)
    -- The Boolean reductions `xᵢ x_S = x_S` in `s e_m`.
    have h₂ := DerivesEq.sum (k := 2 * (t + 1)) (range (t + 1)) fun m hm ↦
      ((sum_X_mul_xS_sub hB U (k := t + 1) (m := m)
        (by have := mem_range.1 hm; omega)).smul (stirlingCoeff t m : ℝ))
    have hinner : ∀ m, ∑ S ∈ U.powersetCard m, ∑ i ∈ S, (X i * xS S - xS S) =
        (∑ i ∈ U, X i) * esymmOn U m - C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1) -
          C (m : ℝ) * esymmOn U m := by
      intro m
      simp only [sum_sub_distrib]
      rw [sum_sum_xS, sum_X_mul_esymmOn]
      ring
    have hid : (∑ i ∈ U, X i) ^ (t + 1) - ∑ m ∈ range (t + 2),
        C (stirlingCoeff (t + 1) m : ℝ) * esymmOn U m =
        (∑ i ∈ U, X i) * ((∑ i ∈ U, X i) ^ t -
          ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * esymmOn U m) +
        ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) *
          ∑ S ∈ U.powersetCard m, ∑ i ∈ S, (X i * xS S - xS S) := by
      rw [← sum_stirlingCoeff_succ U t]
      simp_rw [hinner]
      have e1 : (∑ i ∈ U, X i) * ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * esymmOn U m =
          ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * ((∑ i ∈ U, X i) * esymmOn U m) := by
        rw [mul_sum]
        exact sum_congr rfl fun m _ ↦ by ring
      have e2 : ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) *
          ((∑ i ∈ U, X i) * esymmOn U m - C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1) -
            C (m : ℝ) * esymmOn U m) =
          ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) * ((∑ i ∈ U, X i) * esymmOn U m) -
          ∑ m ∈ range (t + 1), C (stirlingCoeff t m : ℝ) *
            (C (m : ℝ) * esymmOn U m + C ((m + 1 : ℕ) : ℝ) * esymmOn U (m + 1)) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun m _ ↦ by ring
      rw [mul_sub, e1, e2, pow_succ]
      ring
    rw [hid]
    refine ((h₁.mono (by omega) le_rfl).add h₂).mono le_rfl ?_
    -- The norms.
    set N : ℝ := (U.card : ℝ) + 1 with hNdef
    have hN1 : 1 ≤ N := by simp [N]
    have hterm : ∀ m ∈ range (t + 1),
        |(stirlingCoeff t m : ℝ)| * (4 * m * (U.card.choose m)) ≤
        stirlingCoeff t m * (4 * t * N ^ t) := by
      intro m hm
      have hmt := mem_range.1 hm
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hc : ((U.card.choose m : ℕ) : ℝ) ≤ N ^ t := by
        calc ((U.card.choose m : ℕ) : ℝ) ≤ (U.card : ℝ) ^ m := by
              exact_mod_cast Nat.choose_le_pow U.card m
          _ ≤ N ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) (by simp [N]) m
          _ ≤ N ^ t := pow_le_pow_right₀ hN1 (by omega)
      have hm : (m : ℝ) ≤ t := by exact_mod_cast (by omega : m ≤ t)
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h1 : (0 : ℝ) ≤ (U.card.choose m : ℕ) := Nat.cast_nonneg _
      calc 4 * (m : ℝ) * (U.card.choose m : ℕ) ≤ 4 * t * (U.card.choose m : ℕ) := by gcongr
        _ ≤ 4 * t * N ^ t := by gcongr
    have hF : (∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ≤ (2 * t + 1) ^ t := by
      exact_mod_cast sum_stirlingCoeff_le t
    have h2 := (sum_le_sum hterm).trans_eq (sum_mul _ _ _).symm
    have hG : (2 * (t : ℝ) + 1) ^ t ≤ (2 * ((t : ℝ) + 1) + 1) ^ (t + 1) := by
      calc (2 * (t : ℝ) + 1) ^ t ≤ (2 * ((t : ℝ) + 1) + 1) ^ t :=
            pow_le_pow_left₀ (by positivity) (by linarith) t
        _ ≤ _ := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]) (by omega)
    have hNt : N ^ t ≤ N ^ (2 * (t + 1)) := pow_le_pow_right₀ hN1 (by omega)
    have hNt' : N ^ (2 * t) * N ^ 2 = N ^ (2 * (t + 1)) := by rw [← pow_add]; ring_nf
    have hsN : (coeffNorm1 (∑ i ∈ U, X i : MvPolynomial σ ℝ) + 1) ^ 2 ≤ N ^ 2 :=
      pow_le_pow_left₀ (by linarith [coeffNorm1_nonneg (∑ i ∈ U, X i : MvPolynomial σ ℝ)])
        (by simp only [N]; linarith) 2
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    calc (coeffNorm1 (∑ i ∈ U, X i : MvPolynomial σ ℝ) + 1) ^ 2 * powNorm U.card t +
          ∑ m ∈ range (t + 1), |(stirlingCoeff t m : ℝ)| * (4 * m * (U.card.choose m))
        ≤ N ^ 2 * powNorm U.card t + (2 * t + 1) ^ t * (4 * t * N ^ t) :=
          add_le_add (mul_le_mul_of_nonneg_right hsN (powNorm_nonneg _ _))
            (h2.trans (mul_le_mul_of_nonneg_right hF (by positivity)))
      _ = 4 * (2 * t + 1) ^ t * (t ^ 2 * (N ^ (2 * t) * N ^ 2) + t * N ^ t) := by
          unfold powNorm
          ring
      _ ≤ 4 * (2 * t + 1) ^ t * (t ^ 2 * N ^ (2 * (t + 1)) + t * N ^ (2 * (t + 1))) := by
          rw [hNt']
          gcongr
      _ = 4 * (2 * t + 1) ^ t * ((t ^ 2 + t) * N ^ (2 * (t + 1))) := by ring
      _ ≤ 4 * (2 * ((t : ℝ) + 1) + 1) ^ (t + 1) * (((t : ℝ) + 1) ^ 2 * N ^ (2 * (t + 1))) := by
          gcongr
          nlinarith
      _ = powNorm U.card (t + 1) := by
          unfold powNorm
          push_cast
          ring

end Boolean

/-! ### Products of literals -/

/-- A literal: `xᵢ` (`true`) or `1 - xᵢ` (`false`). -/
noncomputable def lit (b : Bool) (i : σ) : MvPolynomial σ ℝ := if b then X i else 1 - X i

/-- The product of a list of literals. -/
noncomputable def litProd (l : List (Bool × σ)) : MvPolynomial σ ℝ :=
  (l.map fun x ↦ lit x.1 x.2).prod

theorem litProd_cons (x : Bool × σ) (l : List (Bool × σ)) :
    litProd (x :: l) = lit x.1 x.2 * litProd l := by
  simp [litProd]

theorem totalDegree_lit_le (b : Bool) (i : σ) : (lit b i).totalDegree ≤ 1 := by
  unfold lit
  split_ifs
  · rw [totalDegree_X]
  · exact (totalDegree_sub _ _).trans (max_le (by simp) (by rw [totalDegree_X]))

theorem coeffNorm1_lit_le (b : Bool) (i : σ) : coeffNorm1 (lit b i) ≤ 2 := by
  unfold lit
  split_ifs
  · rw [coeffNorm1_X]; norm_num
  · have := coeffNorm1_sub_le (1 : MvPolynomial σ ℝ) (X i)
    rw [coeffNorm1_one, coeffNorm1_X] at this
    linarith

theorem totalDegree_litProd_le (l : List (Bool × σ)) : (litProd l).totalDegree ≤ l.length := by
  induction l with
  | nil => simp [litProd]
  | cons x l ih =>
    rw [litProd_cons, List.length_cons]
    have := totalDegree_lit_le x.1 x.2
    exact (totalDegree_mul _ _).trans (by omega)

theorem coeffNorm1_litProd_le (l : List (Bool × σ)) : coeffNorm1 (litProd l) ≤ 2 ^ l.length := by
  induction l with
  | nil => simp [litProd, coeffNorm1_one]
  | cons x l ih =>
    rw [litProd_cons, List.length_cons, pow_succ]
    refine (coeffNorm1_mul_le _ _).trans ?_
    have := coeffNorm1_lit_le x.1 x.2
    nlinarith [coeffNorm1_nonneg (lit x.1 x.2), coeffNorm1_nonneg (litProd l)]

namespace Boolean

variable {A : System σ ℝ}

/-- `ℓ² = ℓ` for a literal. -/
theorem lit_sq_sub (hB : Boolean A) (b : Bool) (i : σ) :
    DerivesEq A 2 1 (lit b i ^ 2 - lit b i) := by
  refine (hB.eq i).congr ?_
  unfold lit
  split_ifs <;> ring

/-- `p² = p` for a product `p` of literals. -/
theorem litProd_sq_sub (hB : Boolean A) (l : List (Bool × σ)) :
    DerivesEq A (2 * l.length) (10 ^ l.length) (litProd l ^ 2 - litProd l) := by
  induction l with
  | nil => simpa [litProd] using DerivesEq.zero A 0 zero_le_one
  | cons x l ih =>
    rw [litProd_cons, List.length_cons]
    set a := lit x.1 x.2
    set b := litProd l
    have hda : a.totalDegree ≤ 1 := totalDegree_lit_le x.1 x.2
    have hdb : b.totalDegree ≤ l.length := totalDegree_litProd_le l
    have hna : coeffNorm1 a ≤ 2 := coeffNorm1_lit_le x.1 x.2
    have hnb : coeffNorm1 b ≤ 2 ^ l.length := coeffNorm1_litProd_le l
    have h₁ := (hB.lit_sq_sub x.1 x.2).mulSOS (IsSOS.sq b)
    have h₂ := ih.mul a
    have hb2 : coeffNorm1 (b ^ 2) ≤ 4 ^ l.length :=
      (coeffNorm1_pow_le _ 2).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) hnb 2).trans_eq
        (by rw [← pow_mul, mul_comm, pow_mul]; norm_num))
    refine ((h₁.mono (k' := 2 * (l.length + 1)) ?_ (M' := 4 ^ l.length) ?_).add
      (h₂.mono (k' := 2 * (l.length + 1)) (by omega) (M' := 9 * 10 ^ l.length) ?_)).mono le_rfl
      ?_ |>.congr (by ring)
    · have := (totalDegree_pow b 2).trans (by omega : 2 * b.totalDegree ≤ 2 * l.length)
      omega
    · rw [mul_one]; exact hb2
    · have : (coeffNorm1 a + 1) ^ 2 ≤ 9 := by
        nlinarith [coeffNorm1_nonneg a]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · have : (4 : ℝ) ^ l.length ≤ 10 ^ l.length := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      rw [pow_succ]
      linarith

/-- **A product of literals is nonnegative**: `p = p² - (p² - p)`. -/
theorem litProd_nonneg (hB : Boolean A) (l : List (Bool × σ)) :
    DerivesN A (2 * l.length) (2 * 10 ^ l.length) (litProd l) := by
  have h₁ := DerivesN.ofIsSOS A (IsSOS.sq (litProd l)) (k := 2 * l.length) (M := 10 ^ l.length)
    ((totalDegree_pow _ 2).trans (by have := totalDegree_litProd_le l; omega))
    ((coeffNorm1_pow_le _ 2).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _)
      (coeffNorm1_litProd_le l) 2).trans (by
        rw [← pow_mul, mul_comm, pow_mul]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _)))
  exact ((h₁.add (hB.litProd_sq_sub l).2).mono le_rfl (by linarith)).congr (by ring)

end Boolean

end SoS
