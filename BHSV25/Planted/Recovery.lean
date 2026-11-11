module

public import BHSV25.Planted.Lift
public import BHSV25.Alg.GridPartition

/-!
# Recovering partitions with a grid of centers, for a symmetric matrix

[BHSV25, Theorem 5.1] with a net of constant precision `η` and the grid of centers of
[BHSV25, Lemma 5.4] (`BHSV25.Planted.exists_good_grid`), for a symmetric matrix `Q` with
`|xᵀ Q x| ≤ ‖x‖²` in place of the normalized adjacency matrix of a regular graph
(`BHSV25/Alg/GridPartition.lean`, whose proof this follows). The closeness of `Q` to its model is
a hypothesis, as in the paper's theorem: the dispersions are at most `Δ n`. Let `χ` have `m` parts
of at least `c n` points and a model whose rows are `α`-separated, let `0 < θ < τ` with
`2 τ² / c ≤ α² / 2`, and let `U` contain a vector within `η` of every vector of norm at most `1` in
the span of the eigenvectors of `Q` with `|μ| ≥ θ`. Then for some `m`-tuple of vectors of `U` and
some grid of centers the clusters of `BHSV25.Alg.clustersC` agree with `χ` on all but
`(512 m⁴ Δ / (c (τ - θ)² α²) + 512 m² η² / α²) · n` points.

* **Eigenspace approximation** (Lemma 5.2): by Lemma 7.4, the lift of every unit eigenvector `z`
  of the symmetrized model is an approximate eigenvector of `Q`
  (`BHSV25.Planted.dist_mulVec_lift_eigenvector`), so it is close to its projection on the
  eigenvectors of `Q` with `|μ| ≥ θ` when `|μ_z| ≥ τ` (`BHSV25.Planted.sum_netTarget_sub_le`).
* **Coordinate separation** (Lemma 5.3, `BHSV25.Planted.exists_sep`): the eigenvalues of the
  symmetrized model lie in `[-1, 1]` (`BHSV25.Planted.abs_eigVal_le`).
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset Spectral

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix (Fin n) (Fin n) ℝ}

/-! ### The eigenvectors of the symmetrized model -/

/-- The `r`-th unit eigenvector of the symmetrized model. -/
noncomputable def eigVec (hQ : Q.IsHermitian) (χ : Fin n → ι) (r : ι) : ι → ℝ :=
  ⇑((symModel_isHermitian hQ χ).eigenvectorBasis r)

/-- The `r`-th eigenvalue of the symmetrized model. -/
noncomputable def eigVal (hQ : Q.IsHermitian) (χ : Fin n → ι) (r : ι) : ℝ :=
  (symModel_isHermitian hQ χ).eigenvalues r

theorem eigVec_dotProduct_self (hQ : Q.IsHermitian) (χ : Fin n → ι) (r : ι) :
    eigVec hQ χ r ⬝ᵥ eigVec hQ χ r = 1 := by
  rw [eigVec, Alg.dotProduct_eigenvectorBasis, ite_eq_left rfl]

theorem symModel_mulVec_eigVec (hQ : Q.IsHermitian) (χ : Fin n → ι) (r : ι) :
    symModel Q χ *ᵥ eigVec hQ χ r = eigVal hQ χ r • eigVec hQ χ r :=
  (symModel_isHermitian hQ χ).mulVec_eigenvectorBasis r

/-- The eigenvalues of the symmetrized model lie in `[-1, 1]` when `|xᵀ Q x| ≤ ‖x‖²`. -/
theorem abs_eigVal_le (hQ : Q.IsHermitian) (hbd : ∀ x, |x ⬝ᵥ (Q *ᵥ x)| ≤ x ⬝ᵥ x)
    (χ : Fin n → ι) (hne : ∀ a, (part χ a).Nonempty) (r : ι) : |eigVal hQ χ r| ≤ 1 := by
  have h1 : eigVal hQ χ r = lift χ (eigVec hQ χ r) ⬝ᵥ (Q *ᵥ lift χ (eigVec hQ χ r)) := by
    rw [lift_dotProduct_mulVec_lift, eigVal, eigVec,
      ← Alg.eigenvalues_eq_dotProduct (symModel_isHermitian hQ χ) r]
  have h2 := hbd (lift χ (eigVec hQ χ r))
  rw [lift_dotProduct_lift χ hne, eigVec_dotProduct_self] at h2
  rw [h1]
  exact h2

/-- `Q lift e_c - lift (S e_c)`. -/
noncomputable def liftErr (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (c : ι) : Fin n → ℝ :=
  Q *ᵥ lift χ (Pi.single c 1) - lift χ (symModel Q χ *ᵥ Pi.single c 1)

/-- The lift of an eigenvector of `S` is an approximate eigenvector of `Q`:
`Q lift z - μ lift z = ∑_c z_c (Q lift e_c - lift (S e_c))`. -/
theorem mulVec_lift_eigVec_sub (hQ : Q.IsHermitian) (χ : Fin n → ι) (r : ι) :
    Q *ᵥ lift χ (eigVec hQ χ r) - eigVal hQ χ r • lift χ (eigVec hQ χ r) =
      ∑ c, eigVec hQ χ r c • liftErr Q χ c := by
  have hdec := pi_eq_sum_univ' (eigVec hQ χ r)
  have h1 : Q *ᵥ lift χ (eigVec hQ χ r) =
      ∑ c, eigVec hQ χ r c • (Q *ᵥ lift χ (Pi.single c 1)) := by
    conv_lhs => rw [hdec]
    rw [lift_sum, mulVec_sum]
    simp only [lift_smul, mulVec_smul]
  have h2 : eigVal hQ χ r • lift χ (eigVec hQ χ r) =
      ∑ c, eigVec hQ χ r c • lift χ (symModel Q χ *ᵥ Pi.single c 1) := by
    rw [← lift_smul, ← symModel_mulVec_eigVec]
    conv_lhs => rw [hdec]
    rw [mulVec_sum, lift_sum]
    simp only [mulVec_smul, lift_smul]
  rw [h1, h2, ← sum_sub_distrib]
  simp only [liftErr, smul_sub]

/-- **Lemma 7.4 with the dispersion bound**: `‖Q lift e_c - lift (S e_c)‖² ≤ m Δ / c`. -/
theorem liftErr_dotProduct_le (χ : Fin n → ι) {c Δ : ℝ} (hc : 0 < c)
    (hsize : ∀ a, c * n ≤ (part χ a).card) (hn : 0 < n) (hdisp : ∀ a b, disp Q χ a b ≤ Δ * n)
    (c' : ι) : liftErr Q χ c' ⬝ᵥ liftErr Q χ c' ≤ Fintype.card ι * Δ / c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsc : 0 < c * n := mul_pos hc hnR
  rw [liftErr, dist_lift_single]
  have hsum : ∑ a, disp Q χ a c' ≤ Fintype.card ι * (Δ * n) := by
    calc ∑ a, disp Q χ a c' ≤ ∑ _a : ι, Δ * n := sum_le_sum fun a _ ↦ hdisp a c'
      _ = Fintype.card ι * (Δ * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (part χ c').card := lt_of_lt_of_le hsc (hsize c')
  rw [div_le_div_iff₀ hpos hc]
  have hnn : 0 ≤ Fintype.card ι * (Δ * n) := le_trans
    (sum_nonneg fun a _ ↦ sum_nonneg fun x _ ↦ sq_nonneg _) hsum
  calc (∑ a, disp Q χ a c') * c ≤ Fintype.card ι * (Δ * n) * c :=
        mul_le_mul_of_nonneg_right hsum hc.le
    _ = Fintype.card ι * Δ * (c * n) := by ring
    _ ≤ Fintype.card ι * Δ * (part χ c').card := by
        refine mul_le_mul_of_nonneg_left (hsize c') ?_
        have : 0 ≤ Fintype.card ι * Δ * n := by linarith
        exact nonneg_of_mul_nonneg_left this hnR

/-- **The lift of an eigenvector of `S` is an approximate eigenvector of `Q`**:
`‖Q lift z - μ lift z‖² ≤ m² Δ / c`. -/
theorem dist_mulVec_lift_eigenvector (hQ : Q.IsHermitian) (χ : Fin n → ι) {c Δ : ℝ} (hc : 0 < c)
    (hsize : ∀ a, c * n ≤ (part χ a).card) (hn : 0 < n) (hdisp : ∀ a b, disp Q χ a b ≤ Δ * n)
    (r : ι) :
    (Q *ᵥ lift χ (eigVec hQ χ r) - eigVal hQ χ r • lift χ (eigVec hQ χ r)) ⬝ᵥ
      (Q *ᵥ lift χ (eigVec hQ χ r) - eigVal hQ χ r • lift χ (eigVec hQ χ r)) ≤
      Fintype.card ι ^ 2 * Δ / c := by
  rw [mulVec_lift_eigVec_sub]
  refine (Alg.dotProduct_sum_smul_le _ (eigVec_dotProduct_self hQ χ r) _).trans ?_
  calc ∑ c', liftErr Q χ c' ⬝ᵥ liftErr Q χ c' ≤ ∑ _c' : ι, Fintype.card ι * Δ / c :=
        sum_le_sum fun c' _ ↦ liftErr_dotProduct_le χ hc hsize hn hdisp c'
    _ = Fintype.card ι ^ 2 * Δ / c := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

omit [Fintype ι] in
/-- The entry `S_ja` of the symmetrized model: `√|V_a| M_aj / √|V_j|`. -/
theorem symModel_apply_eq (hQ : Q.IsHermitian) (χ : Fin n → ι) (hne : ∀ a, (part χ a).Nonempty)
    (j a : ι) :
    symModel Q χ j a = Real.sqrt (part χ a).card * pmodel Q χ a j / Real.sqrt (part χ j).card := by
  have ha : (0 : ℝ) < (part χ a).card := by exact_mod_cast (hne a).card_pos
  have hj : (0 : ℝ) < (part χ j).card := by exact_mod_cast (hne j).card_pos
  have hsa0 := Real.sqrt_pos.2 ha
  have hsj0 := Real.sqrt_pos.2 hj
  rw [symModel, sum_wt_comm hQ, ← card_mul_pmodel, sqrt_mul_card]
  field_simp
  rw [Real.sq_sqrt ha.le]
  ring

/-- **Coordinate separation** [BHSV25, Lemma 5.3]: for parts `a ≠ b`, some eigenvector `z` of `S`
with `|μ| ≥ τ` separates them: `(z_a / √|V_a| - z_b / √|V_b|)² ≥ α² / (4 m n)`. -/
theorem exists_sep (hQ : Q.IsHermitian) (hbd : ∀ x, |x ⬝ᵥ (Q *ᵥ x)| ≤ x ⬝ᵥ x) (χ : Fin n → ι)
    {c α τ : ℝ} (hc : 0 < c) (hsize : ∀ a, c * n ≤ (part χ a).card) (hn : 0 < n) (hα : 0 < α)
    (hsep : ∀ a b, a ≠ b → α ^ 2 ≤ ∑ j, (pmodel Q χ a j - pmodel Q χ b j) ^ 2)
    (hτ : τ ^ 2 * (2 / c) ≤ α ^ 2 / 2) {a b : ι} (hab : a ≠ b) :
    ∃ r, τ ≤ |eigVal hQ χ r| ∧ α ^ 2 / (4 * Fintype.card ι * n) ≤
      (eigVec hQ χ r a / Real.sqrt (part χ a).card -
        eigVec hQ χ r b / Real.sqrt (part χ b).card) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ a, (0 : ℝ) < (part χ a).card := fun a ↦ lt_of_lt_of_le (mul_pos hc hnR) (hsize a)
  have hne : ∀ a, (part χ a).Nonempty := fun a ↦ card_pos.1 (by exact_mod_cast hpos a)
  set Da := Real.sqrt n / Real.sqrt (part χ a).card with hDa
  set Db := Real.sqrt n / Real.sqrt (part χ b).card with hDb
  set x : ι → ℝ := Da • Pi.single a 1 - Db • Pi.single b 1 with hx
  have hsq : ∀ a', Real.sqrt (part χ a').card ^ 2 = (part χ a').card :=
    fun a' ↦ Real.sq_sqrt (hpos a').le
  have hsqn : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnR.le
  have hs0 : ∀ a', 0 < Real.sqrt (part χ a').card := fun a' ↦ Real.sqrt_pos.2 (hpos a')
  -- `‖x‖² ≤ 2 / c`
  have hD2 : ∀ a', (Real.sqrt n / Real.sqrt (part χ a').card) ^ 2 ≤ 1 / c := by
    intro a'
    rw [div_pow, hsqn, hsq, div_le_div_iff₀ (hpos a') hc, one_mul, mul_comm]
    exact hsize a'
  have hxx : x ⬝ᵥ x ≤ 2 / c := by
    have : x ⬝ᵥ x = Da ^ 2 + Db ^ 2 := by
      simp only [hx, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_eq_add (s := univ) a b hab (fun i _ hi ↦ by
        rw [Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hi.2]; ring) (by simp) (by simp)]
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hab.symm,
        Pi.single_eq_same]
      ring
    rw [this]
    have h1 := hD2 a
    have h2 := hD2 b
    rw [← hDa] at h1
    rw [← hDb] at h2
    have e : (2 : ℝ) / c = 1 / c + 1 / c := by ring
    linarith
  -- `‖S x‖² ≥ α²`
  have hSx : α ^ 2 ≤ (symModel Q χ *ᵥ x) ⬝ᵥ (symModel Q χ *ᵥ x) := by
    have hval : ∀ j, (symModel Q χ *ᵥ x) j =
        Real.sqrt n * (pmodel Q χ a j - pmodel Q χ b j) / Real.sqrt (part χ j).card := by
      intro j
      rw [hx, mulVec_sub, mulVec_smul, mulVec_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
        mulVec_single_one, mulVec_single_one, Matrix.col_apply, Matrix.col_apply,
        symModel_apply_eq hQ χ hne j a, symModel_apply_eq hQ χ hne j b, smul_eq_mul, smul_eq_mul,
        hDa, hDb]
      field_simp
    calc α ^ 2 ≤ ∑ j, (pmodel Q χ a j - pmodel Q χ b j) ^ 2 := hsep a b hab
      _ ≤ ∑ j, (symModel Q χ *ᵥ x) j * (symModel Q χ *ᵥ x) j := by
          refine sum_le_sum fun j _ ↦ ?_
          rw [hval, ← sq, div_pow, mul_pow, hsqn, hsq]
          rw [le_div_iff₀ (hpos j)]
          have hj : ((part χ j).card : ℝ) ≤ n := by
            exact_mod_cast (card_le_univ _).trans (by simp)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  obtain ⟨r, hr, hcoef⟩ := Alg.exists_coeff_sq_ge (symModel_isHermitian hQ χ)
    (fun r ↦ abs_eigVal_le hQ hbd χ hne r) hα hSx hxx hτ
  refine ⟨r, hr, ?_⟩
  have hcx : coeff (symModel_isHermitian hQ χ) r x = Real.sqrt n *
      (eigVec hQ χ r a / Real.sqrt (part χ a).card -
        eigVec hQ χ r b / Real.sqrt (part χ b).card) := by
    rw [hx, Alg.coeff_sub', Alg.coeff_smul', Alg.coeff_smul', Alg.coeff_single, Alg.coeff_single,
      hDa, hDb]
    simp only [eigVec]
    ring
  rw [hcx, mul_pow, hsqn] at hcoef
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
  rw [div_le_iff₀ (by positivity)] at hcoef ⊢
  nlinarith

/-! ### The targets of the net -/

/-- The target of the net for the eigenvector `r` of `S`: the projection of its lift on the
eigenvectors of `Q` with `|μ| ≥ θ` if `|μ_r| ≥ τ`, and `0` otherwise. -/
noncomputable def netTarget (hQ : Q.IsHermitian) (χ : Fin n → ι) (θ τ : ℝ) (r : ι) : Fin n → ℝ :=
  open Classical in
  if τ ≤ |eigVal hQ χ r| then proj hQ (fun t ↦ θ ≤ |t|) (lift χ (eigVec hQ χ r)) else 0

/-- The values of the eigenvector `r` of `S` on the parts, normalized: `z_a / √|V_a|` if
`|μ_r| ≥ τ`, and `0` otherwise. -/
noncomputable def partValue (hQ : Q.IsHermitian) (χ : Fin n → ι) (τ : ℝ) (r a : ι) : ℝ :=
  open Classical in
  if τ ≤ |eigVal hQ χ r| then eigVec hQ χ r a / Real.sqrt (part χ a).card else 0

theorem netTarget_dotProduct_le (hQ : Q.IsHermitian) (χ : Fin n → ι)
    (hne : ∀ a, (part χ a).Nonempty) (θ τ : ℝ) (r : ι) :
    netTarget hQ χ θ τ r ⬝ᵥ netTarget hQ χ θ τ r ≤ 1 := by
  rw [netTarget]
  split_ifs
  · refine (Alg.proj_dotProduct_le _ _ _).trans ?_
    rw [lift_dotProduct_lift χ hne, eigVec_dotProduct_self]
  · simp

theorem netTarget_inEigSpan (hQ : Q.IsHermitian) (χ : Fin n → ι) (θ τ : ℝ) (r : ι) :
    InEigSpan hQ (fun μ ↦ θ ≤ |μ|) (netTarget hQ χ θ τ r) := by
  rw [netTarget]
  split_ifs
  · exact inEigSpan_proj _ _ _
  · intro i _
    simp [coeff]

/-- The net targets are close to the values on the parts:
`∑_y (w_r(y) - V_r(χ y))² ≤ m² Δ / (c (τ - θ)²)`. -/
theorem sum_netTarget_sub_le (hQ : Q.IsHermitian) (χ : Fin n → ι) {c Δ θ τ : ℝ} (hc : 0 < c)
    (hsize : ∀ a, c * n ≤ (part χ a).card) (hn : 0 < n) (hdisp : ∀ a b, disp Q χ a b ≤ Δ * n)
    (hθτ : θ < τ) (r : ι) :
    ∑ y, (netTarget hQ χ θ τ r y - partValue hQ χ τ r (χ y)) ^ 2 ≤
      Fintype.card ι ^ 2 * Δ / (c * (τ - θ) ^ 2) := by
  have hη : 0 < τ - θ := sub_pos.2 hθτ
  have hbound : 0 ≤ Fintype.card ι ^ 2 * Δ / (c * (τ - θ) ^ 2) := by
    have h0 := dist_mulVec_lift_eigenvector hQ χ hc hsize hn hdisp r
    have : 0 ≤ Fintype.card ι ^ 2 * Δ / c :=
      le_trans (sum_nonneg fun x _ ↦ mul_self_nonneg _) h0
    rw [← div_div]
    positivity
  unfold netTarget partValue
  split_ifs with hbig
  · have hlift : ∀ y, eigVec hQ χ r (χ y) / Real.sqrt (part χ (χ y)).card =
        lift χ (eigVec hQ χ r) y := fun y ↦ rfl
    simp only [hlift]
    have h1 := Alg.dist_proj_le hQ hη (by linarith : θ + (τ - θ) ≤ |eigVal hQ χ r|)
      (lift χ (eigVec hQ χ r))
    have h2 := dist_mulVec_lift_eigenvector hQ χ hc hsize hn hdisp r
    have h3 : ∑ y, (proj hQ (fun t ↦ θ ≤ |t|) (lift χ (eigVec hQ χ r)) y -
        lift χ (eigVec hQ χ r) y) ^ 2 =
        (lift χ (eigVec hQ χ r) - proj hQ (fun t ↦ θ ≤ |t|) (lift χ (eigVec hQ χ r))) ⬝ᵥ
          (lift χ (eigVec hQ χ r) - proj hQ (fun t ↦ θ ≤ |t|) (lift χ (eigVec hQ χ r))) := by
      simp only [dotProduct, Pi.sub_apply]
      exact sum_congr rfl fun y _ ↦ by ring
    rw [h3, le_div_iff₀ (by positivity)]
    calc _ = (τ - θ) ^ 2 * ((lift χ (eigVec hQ χ r) - proj hQ (fun t ↦ θ ≤ |t|)
            (lift χ (eigVec hQ χ r))) ⬝ᵥ (lift χ (eigVec hQ χ r) -
            proj hQ (fun t ↦ θ ≤ |t|) (lift χ (eigVec hQ χ r)))) * c := by
          ring
      _ ≤ Fintype.card ι ^ 2 * Δ / c * c := mul_le_mul_of_nonneg_right (h1.trans h2) hc.le
      _ = Fintype.card ι ^ 2 * Δ := div_mul_cancel₀ _ hc.ne'
  · simpa using hbound

/-- The values of the eigenvectors on the parts are at most `1 / √|V_a|`. -/
theorem abs_partValue_le (hQ : Q.IsHermitian) (χ : Fin n → ι) (τ : ℝ) (r a : ι) :
    |partValue hQ χ τ r a| ≤ 1 / Real.sqrt (part χ a).card := by
  unfold partValue
  split_ifs
  · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have h1 := eigVec_dotProduct_self hQ χ r
    have h2 : eigVec hQ χ r a ^ 2 ≤ eigVec hQ χ r ⬝ᵥ eigVec hQ χ r := by
      rw [dotProduct]
      have := single_le_sum (f := fun b ↦ eigVec hQ χ r b * eigVec hQ χ r b)
        (fun b _ ↦ mul_self_nonneg _) (mem_univ a)
      simpa [sq] using this
    rw [h1] at h2
    exact (sq_le_one_iff_abs_le_one _).1 h2
  · simp only [abs_zero]
    positivity

/-! ### Theorem 5.1 with a grid of centers -/

open Classical in
/-- **Theorem 5.1 with a grid of centers.** -/
theorem exists_good_grid (hQ : Q.IsHermitian) (hbd : ∀ x, |x ⬝ᵥ (Q *ᵥ x)| ≤ x ⬝ᵥ x)
    {m : ℕ} (χ : Fin n → ι) (e : ι ≃ Fin m) {c α Δ θ τ η : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hsize : ∀ a, c * n ≤ (part χ a).card)
    (hα : 0 < α) (hsep : ∀ a b, a ≠ b → α ^ 2 ≤ ∑ j, (pmodel Q χ a j - pmodel Q χ b j) ^ 2)
    (hdisp : ∀ a b, disp Q χ a b ≤ Δ * n)
    (hθτ : θ < τ) (hτ : τ ^ 2 * (2 / c) ≤ α ^ 2 / 2) (U : List (List ℚ))
    (hnet : ∀ w : Fin n → ℝ, w ⬝ᵥ w ≤ 1 → InEigSpan hQ (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec n u - w) ⬝ᵥ (Net.ratVec n u - w) ≤ η ^ 2)
    {S K : ℕ} (hS : 128 * (m : ℝ) ^ 2 ≤ α ^ 2 * (S : ℝ) ^ 2) (hK1 : 1 ≤ K)
    (hK : (S : ℝ) ^ 2 ≤ c * ((K : ℝ) - 1) ^ 2) :
    ∃ us : Fin m → List ℚ, (∀ j, us j ∈ U) ∧ ∃ ts : Fin (m * m) → Fin (2 * K + 1),
      ((univ.filter fun y : Fin n ↦ Alg.clusterIdxC (List.ofFn us)
          (Alg.gridCenters m S K (Nat.sqrt n) (List.ofFn fun k ↦ (ts k : ℕ))) y ≠ e (χ y)).card :
          ℝ) ≤
        (512 * m ^ 4 * Δ / (c * (τ - θ) ^ 2 * α ^ 2) + 512 * m ^ 2 * η ^ 2 / α ^ 2) *
          n := by
  classical
  have hm : Fintype.card ι = m := by simpa using Fintype.card_congr e
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ a, (0 : ℝ) < (part χ a).card := fun a ↦
    lt_of_lt_of_le (by positivity) (hsize a)
  have hne : ∀ a, (part χ a).Nonempty := fun a ↦ card_pos.1 (by exact_mod_cast hpos a)
  have hη : 0 < τ - θ := sub_pos.2 hθτ
  set E := 512 * (m : ℝ) ^ 4 * Δ / (c * (τ - θ) ^ 2 * α ^ 2) with hEdef
  set F := 512 * (m : ℝ) ^ 2 * η ^ 2 / α ^ 2 with hFdef
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty (Fin n) := ⟨fun y ↦ hι.false (χ y)⟩
    have h0 : n = 0 := by simpa using this
    omega
  have hmpos : (0 : ℝ) < m := by
    rw [← hm]
    exact_mod_cast Fintype.card_pos
  -- the net vectors
  choose u hu hud using fun r ↦ hnet (netTarget hQ χ θ τ r) (netTarget_dotProduct_le hQ χ hne θ τ r)
    (netTarget_inEigSpan hQ χ θ τ r)
  set Ur : ι → Fin n → ℝ := fun r ↦ Net.ratVec n (u r) with hUr
  set W := netTarget hQ χ θ τ with hW
  set V := partValue hQ χ τ with hV
  set ρ : ℝ := α ^ 2 / (128 * m * n) with hρ
  have hρpos : 0 < ρ := by positivity
  -- vertices spoiled by the net: few
  set B1 := univ.filter fun y ↦ ρ / 4 < ∑ r, (Ur r y - W r y) ^ 2 with hB1
  have hB1c : (B1.card : ℝ) ≤ F * n := by
    have hmk := Alg.card_lt_le_sum (fun y ↦ ∑ r, (Ur r y - W r y) ^ 2)
      (fun y ↦ sum_nonneg fun r _ ↦ sq_nonneg _) (ρ / 4)
    rw [← hB1, sum_comm] at hmk
    have hsum : ∑ r, ∑ y, (Ur r y - W r y) ^ 2 ≤ m * η ^ 2 := by
      calc ∑ r, ∑ y, (Ur r y - W r y) ^ 2 ≤ ∑ _r : ι, η ^ 2 := by
            refine sum_le_sum fun r _ ↦ ?_
            have := hud r
            simp only [dotProduct, Pi.sub_apply] at this
            simpa only [sq] using this
        _ = m * η ^ 2 := by rw [sum_const, card_univ, hm, nsmul_eq_mul]
    have h1 := hmk.trans hsum
    have h2 : (m : ℝ) * η ^ 2 = F * n * (ρ / 4) := by
      rw [hFdef, hρ]
      field_simp
      ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- vertices far from the values of their parts: few
  set B2 := univ.filter fun y ↦ ρ / 4 < ∑ r, (W r y - V r (χ y)) ^ 2 with hB2
  have hB2c : (B2.card : ℝ) ≤ E * n := by
    have hmk := Alg.card_lt_le_sum (fun y ↦ ∑ r, (W r y - V r (χ y)) ^ 2)
      (fun y ↦ sum_nonneg fun r _ ↦ sq_nonneg _) (ρ / 4)
    rw [← hB2, sum_comm] at hmk
    have hsum : ∑ r, ∑ y, (W r y - V r (χ y)) ^ 2 ≤
        m * (m ^ 2 * Δ / (c * (τ - θ) ^ 2)) := by
      calc ∑ r, ∑ y, (W r y - V r (χ y)) ^ 2 ≤
            ∑ _r : ι, (m : ℝ) ^ 2 * Δ / (c * (τ - θ) ^ 2) := by
            refine sum_le_sum fun r _ ↦ ?_
            have := sum_netTarget_sub_le hQ χ hc hsize hn hdisp hθτ r
            rw [hm] at this
            exact this
        _ = m * (m ^ 2 * Δ / (c * (τ - θ) ^ 2)) := by
            rw [sum_const, card_univ, hm, nsmul_eq_mul]
    have h1 := hmk.trans hsum
    have h2 : (m : ℝ) * (m ^ 2 * Δ / (c * (τ - θ) ^ 2)) = E * n * (ρ / 4) := by
      rw [hEdef, hρ]
      field_simp
      ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- good vertices
  have hgood : ∀ y, y ∉ B1 → y ∉ B2 → ∑ r, (Ur r y - V r (χ y)) ^ 2 ≤ ρ := by
    intro y hy1 hy2
    have h1 : ¬ ρ / 4 < ∑ r, (Ur r y - W r y) ^ 2 :=
      fun hlt ↦ hy1 (mem_filter.2 ⟨mem_univ _, hlt⟩)
    have h2 : ¬ ρ / 4 < ∑ r, (W r y - V r (χ y)) ^ 2 :=
      fun hlt ↦ hy2 (mem_filter.2 ⟨mem_univ _, hlt⟩)
    push Not at h1 h2
    have h3 := Alg.sum_sq_sub_le (fun r ↦ Ur r y - W r y) (fun r ↦ V r (χ y) - W r y)
    have e3 : ∀ r, Ur r y - W r y - (V r (χ y) - W r y) = Ur r y - V r (χ y) := fun r ↦ by ring
    simp only [e3] at h3
    have e4 : ∑ r, (V r (χ y) - W r y) ^ 2 = ∑ r, (W r y - V r (χ y)) ^ 2 :=
      sum_congr rfl fun r _ ↦ by ring
    rw [e4] at h3
    linarith
  -- the grid
  set R := Nat.sqrt n with hR
  obtain ⟨hR1, hR2⟩ := Alg.sqrt_bounds hn
  have hRpos : (0 : ℝ) < R := by have := Real.sqrt_pos.2 hnR; linarith
  have hS0 : (0 : ℝ) < S := by
    have : (0 : ℝ) < α ^ 2 * (S : ℝ) ^ 2 := lt_of_lt_of_le (by positivity) hS
    have hS' : (S : ℝ) ≠ 0 := by intro h0; rw [h0] at this; simp at this
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hS')
  have hVb : ∀ r a, |V r a * S * R| ≤ (K : ℝ) - 1 := by
    intro r a
    have h1 := abs_partValue_le hQ χ τ r a
    have h2 : Real.sqrt (c * n) ≤ Real.sqrt (part χ a).card := Real.sqrt_le_sqrt (hsize a)
    have hcn : 0 < Real.sqrt (c * n) := Real.sqrt_pos.2 (by positivity)
    have h3 : |V r a| ≤ 1 / Real.sqrt (c * n) :=
      h1.trans (one_div_le_one_div_of_le hcn h2)
    rw [abs_mul, abs_mul, abs_of_pos hS0, abs_of_pos hRpos]
    have hK' : (S : ℝ) ≤ Real.sqrt c * ((K : ℝ) - 1) := by
      have hK0 : (0 : ℝ) ≤ (K : ℝ) - 1 := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
        linarith
      rw [← Real.sqrt_sq hS0.le, ← Real.sqrt_sq hK0, ← Real.sqrt_mul hc.le]
      exact Real.sqrt_le_sqrt hK
    have hsc : Real.sqrt (c * n) = Real.sqrt c * Real.sqrt n := Real.sqrt_mul hc.le _
    calc |V r a| * S * R ≤ 1 / Real.sqrt (c * n) * S * Real.sqrt n := by gcongr
      _ = S / Real.sqrt c := by
          rw [hsc]
          have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
          field_simp
      _ ≤ (K : ℝ) - 1 := by
          rw [div_le_iff₀ (Real.sqrt_pos.2 hc)]
          linarith
  choose tN htNlt htNclose using fun r a ↦ Alg.exists_grid_center hS0 hRpos (hVb r a)
  set ts : Fin (m * m) → Fin (2 * K + 1) := fun k ↦
    ⟨tN (e.symm (finProdFinEquiv.symm k).2) (e.symm (finProdFinEquiv.symm k).1),
      htNlt _ _⟩ with hts
  set C : ι → ι → ℝ := fun r a ↦ ((tN r a : ℝ) - K) / (S * R) with hC
  have hCval : ∀ a j : Fin m, (((Alg.gridCenters m S K R (List.ofFn fun k ↦ (ts k : ℕ))).getD a
      []).getD j 0 : ℝ) = C (e.symm j) (e.symm a) := by
    intro a j
    rw [Alg.getD_gridCenters _ a.2 j.2]
    have hidx : (a : ℕ) * m + j = (finProdFinEquiv (a, j) : ℕ) := by
      rw [finProdFinEquiv_apply_val]; ring
    have hlt : (a : ℕ) * m + j < (List.ofFn fun k ↦ (ts k : ℕ)).length := by
      rw [List.length_ofFn, hidx]
      exact (finProdFinEquiv (a, j)).2
    have hget : (List.ofFn fun k ↦ (ts k : ℕ)).getD (a * m + j) 0 =
        tN (e.symm j) (e.symm a) := by
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      simp only [hts, hidx, Fin.eta, Equiv.symm_apply_apply]
    rw [hget, hC]
    push_cast
    rfl
  have hCclose : ∀ a, ∑ r, (C r a - V r a) ^ 2 ≤ ρ := by
    intro a
    have hpt : ∀ r, (C r a - V r a) ^ 2 ≤ (1 : ℝ) / ((S : ℝ) ^ 2 * n) := by
      intro r
      have h1 := htNclose r a
      rw [← sq_abs]
      have h2 : |C r a - V r a| ^ 2 ≤ (1 / (2 * (S * R))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      refine h2.trans ?_
      have hRsq : (n : ℝ) / 4 ≤ (R : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hR1 2
        rw [div_pow, Real.sq_sqrt hnR.le] at this
        linarith
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_pow,
        mul_pow]
      nlinarith [sq_nonneg (S : ℝ)]
    calc ∑ r, (C r a - V r a) ^ 2 ≤ ∑ _r : ι, (1 : ℝ) / ((S : ℝ) ^ 2 * n) :=
          sum_le_sum fun r _ ↦ hpt r
      _ = (m : ℝ) / ((S : ℝ) ^ 2 * n) := by
          rw [sum_const, card_univ, hm, nsmul_eq_mul]; ring
      _ ≤ ρ := by
          rw [hρ, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 := mul_le_mul_of_nonneg_right hS hnR.le
          have e1 : (m : ℝ) * (128 * m * n) = 128 * (m : ℝ) ^ 2 * n := by ring
          have e2 : α ^ 2 * ((S : ℝ) ^ 2 * n) = α ^ 2 * (S : ℝ) ^ 2 * n := by ring
          rw [e1, e2]
          exact h1
  -- the separation of the values
  have hsepV : ∀ a b, a ≠ b → 32 * ρ ≤ ∑ r, (V r a - V r b) ^ 2 := by
    intro a b hab
    obtain ⟨r, hr, hsepr⟩ := exists_sep hQ hbd χ hc hsize hn hα hsep hτ hab
    rw [hm] at hsepr
    refine le_trans ?_ (single_le_sum (fun r _ ↦ sq_nonneg (V r a - V r b)) (mem_univ r))
    have e1 : 32 * ρ = α ^ 2 / (4 * m * n) := by rw [hρ]; field_simp; ring
    rw [e1]
    simp only [hV, partValue, ite_eq_left hr]
    exact hsepr
  -- the tuple of net vectors
  refine ⟨fun j ↦ u (e.symm j), fun j ↦ hu _, ts, ?_⟩
  have hcount : (univ.filter fun y : Fin n ↦ Alg.clusterIdxC (List.ofFn fun j ↦ u (e.symm j))
      (Alg.gridCenters m S K R (List.ofFn fun k ↦ (ts k : ℕ))) y ≠ e (χ y)) ⊆ B1 ∪ B2 := by
    intro y hy
    rw [mem_filter] at hy
    by_contra hyB
    rw [mem_union, not_or] at hyB
    exact hy.2 (Alg.clusterIdxC_good e _ _ (Alg.length_gridCenters _ _ _ _ _) Ur
      (fun r y ↦ by simp [hUr, Net.ratVec]) C V hCval hρpos hCclose hsepV (χ y) y
      (hgood y hyB.1 hyB.2))
  calc _ ≤ ((B1 ∪ B2).card : ℝ) := by exact_mod_cast card_le_card hcount
    _ ≤ (B1.card : ℝ) + B2.card := by exact_mod_cast card_union_le B1 B2
    _ ≤ F * n + E * n := add_le_add hB1c hB2c
    _ = (E + F) * n := by ring

end Planted

end BHSV25
