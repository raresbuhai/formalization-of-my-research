module

public import BHSV25.Alg.Variance
public import BHSV25.Alg.PartitionSpectral
public import BHSV25.Alg.Cluster
public import BHSV25.Net.Spec

/-!
# The spectral part of recovering partitions

The ingredients of [BHSV25, Theorem 5.1] for regular graphs, on the symmetrized model
`S = B^{1/2} M B^{-1/2}` (`BHSV25.Alg.symModel`) and the lift `z ↦ (x ↦ z_{χ x} / √|V_{χ x}|)`
(`BHSV25.Alg.lift`), for a partition `χ` of a regular graph with at most one eigenvalue above
`L ∈ (0, 1)`, parts of at least `c n` vertices, weight `I ≤ ε₀ n` inside the parts, and a model
whose rows are `α`-separated. The clustering and the assembly are in
`BHSV25/Alg/GridPartition.lean`.

* **Eigenspace approximation** (Lemma 5.2): by Lemmas 6.1 and 7.4, `Ã lift e_c` is close to
  `lift (S e_c)` for every part `c`, so the lift of every unit eigenvector `z` of `S` is an
  approximate eigenvector of `Ã` with the same eigenvalue `μ`
  (`BHSV25.Alg.dist_mulVec_lift_eigenvector`); if `|μ| ≥ τ`, it is close to its projection on the
  eigenvectors of `Ã` with `|μ| ≥ θ` (`BHSV25.Alg.netTarget`, `BHSV25.Alg.sum_netTarget_sub_le`).
* **Coordinate separation** (Lemma 5.3): for parts `a ≠ b`, some eigenvector `z` of `S` with
  `|μ| ≥ τ` has `(z_a / √|V_a| - z_b / √|V_b|)² ≥ α² / (4 m n)` (`BHSV25.Alg.exists_sep`), since the
  eigenvalues of `S` lie in `[-1, 1]`.
* **Markov's inequality** for the vertices far from the values of their part
  (`BHSV25.Alg.card_lt_le_sum`).

The net needs a bound `T` on the number of eigenvalues of absolute value at least `θ'`; for a
regular graph with at most one eigenvalue above `δ < θ'² / 2`, [BHSV25, Corollary 4.2] gives
`1 + 4 / θ'⁴` (`BHSV25.Alg.card_abs_eig_ge_le`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Matrix Finset Spectral

/-! ### Counting -/

/-- **Markov's inequality** for a finite sum: at most `(∑ f) / t` points have `f > t`. -/
theorem card_lt_le_sum {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    ((univ.filter fun x ↦ t < f x).card : ℝ) * t ≤ ∑ x, f x := by
  calc ((univ.filter fun x ↦ t < f x).card : ℝ) * t = ∑ _x ∈ univ.filter fun x ↦ t < f x, t := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ univ.filter fun x ↦ t < f x, f x := sum_le_sum fun x hx ↦ (mem_filter.1 hx).2.le
    _ ≤ ∑ x, f x := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ ↦ hf x

/-! ### Clustering with good representatives -/

theorem sum_sq_sub_le {R : Type*} [Fintype R] (p q : R → ℝ) :
    ∑ r, (p r - q r) ^ 2 ≤ 2 * ∑ r, p r ^ 2 + 2 * ∑ r, q r ^ 2 := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun r _ ↦ by nlinarith [sq_nonneg (p r + q r)]

/-! ### The eigenvectors of the symmetrized model -/

section Eigen

variable {G : Graph} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `r`-th unit eigenvector of the symmetrized model. -/
noncomputable def eigVec (χ : Fin G.1 → ι) (r : ι) : ι → ℝ :=
  ⇑((symModel_isHermitian (G := G) χ).eigenvectorBasis r)

/-- The `r`-th eigenvalue of the symmetrized model. -/
noncomputable def eigVal (χ : Fin G.1 → ι) (r : ι) : ℝ :=
  (symModel_isHermitian (G := G) χ).eigenvalues r

theorem eigVec_dotProduct_self (χ : Fin G.1 → ι) (r : ι) : eigVec χ r ⬝ᵥ eigVec χ r = 1 := by
  rw [eigVec, dotProduct_eigenvectorBasis, ite_eq_left rfl]

theorem symModel_mulVec_eigVec (χ : Fin G.1 → ι) (r : ι) :
    symModel G χ *ᵥ eigVec χ r = eigVal χ r • eigVec χ r :=
  (symModel_isHermitian χ).mulVec_eigenvectorBasis r

/-- The eigenvalues of the symmetrized model lie in `[-1, 1]`. -/
theorem abs_eigVal_le (χ : Fin G.1 → ι) (hne : ∀ a, (part G χ a).Nonempty) (r : ι) :
    |eigVal χ r| ≤ 1 := by
  have h1 : eigVal χ r = lift G χ (eigVec χ r) ⬝ᵥ (G.normAdj *ᵥ lift G χ (eigVec χ r)) := by
    rw [lift_dotProduct_mulVec_lift, eigVal, eigVec,
      ← eigenvalues_eq_dotProduct (symModel_isHermitian χ) r]
  have h2 := G.abs_quad_normAdj_le (lift G χ (eigVec χ r))
  rw [lift_dotProduct_lift χ hne, eigVec_dotProduct_self] at h2
  rw [h1]
  exact h2

/-- `Ã lift e_c - lift (S e_c)`. -/
noncomputable def liftErr (χ : Fin G.1 → ι) (c : ι) : Fin G.1 → ℝ :=
  G.normAdj *ᵥ lift G χ (Pi.single c 1) - lift G χ (symModel G χ *ᵥ Pi.single c 1)

/-- The lift of an eigenvector of `S` is an approximate eigenvector of `Ã`:
`Ã lift z - μ lift z = ∑_c z_c (Ã lift e_c - lift (S e_c))`. -/
theorem mulVec_lift_eigVec_sub (χ : Fin G.1 → ι) (r : ι) :
    G.normAdj *ᵥ lift G χ (eigVec χ r) - eigVal χ r • lift G χ (eigVec χ r) =
      ∑ c, eigVec χ r c • liftErr χ c := by
  have hdec := pi_eq_sum_univ' (eigVec χ r)
  have h1 : G.normAdj *ᵥ lift G χ (eigVec χ r) =
      ∑ c, eigVec χ r c • (G.normAdj *ᵥ lift G χ (Pi.single c 1)) := by
    conv_lhs => rw [hdec]
    rw [lift_sum, mulVec_sum]
    simp only [lift_smul, mulVec_smul]
  have h2 : eigVal χ r • lift G χ (eigVec χ r) =
      ∑ c, eigVec χ r c • lift G χ (symModel G χ *ᵥ Pi.single c 1) := by
    rw [← lift_smul, ← symModel_mulVec_eigVec]
    conv_lhs => rw [hdec]
    rw [mulVec_sum, lift_sum]
    simp only [mulVec_smul, lift_smul]
  rw [h1, h2, ← sum_sub_distrib]
  simp only [liftErr, smul_sub]

omit [DecidableEq ι] in
/-- The squared norm of `∑_c z_c w_c` for a unit vector `z`. -/
theorem dotProduct_sum_smul_le {n : ℕ} (z : ι → ℝ) (hz : z ⬝ᵥ z = 1) (w : ι → Fin n → ℝ) :
    (∑ c, z c • w c) ⬝ᵥ (∑ c, z c • w c) ≤ ∑ c, w c ⬝ᵥ w c := by
  have hpt : ∀ x, (∑ c, z c * w c x) ^ 2 ≤ ∑ c, w c x ^ 2 := by
    intro x
    have h := sum_mul_sq_le_sq_mul_sq univ z (fun c ↦ w c x)
    have hz' : ∑ c, z c ^ 2 = 1 := by
      rw [← hz]
      simp [dotProduct, sq]
    rw [hz', one_mul] at h
    exact h
  calc (∑ c, z c • w c) ⬝ᵥ (∑ c, z c • w c) = ∑ x, (∑ c, z c * w c x) ^ 2 := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sq, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ x, ∑ c, w c x ^ 2 := sum_le_sum fun x _ ↦ hpt x
    _ = ∑ c, w c ⬝ᵥ w c := by
        rw [sum_comm]
        simp only [dotProduct, sq]

open Classical in
/-- **Lemma 7.4 with Lemma 6.1**: `‖Ã lift e_c - lift (S e_c)‖² ≤ m (ε₀ / L + L) / c`. -/
theorem liftErr_dotProduct_le {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) {c L ε₀ : ℝ} (hc : 0 < c) (hsize : ∀ a, c * G.1 ≤ (part G χ a).card)
    (hn : 0 < G.1) (hL0 : 0 < L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1)
    (hint : intWt G χ ≤ ε₀ * G.1) (c' : ι) :
    liftErr χ c' ⬝ᵥ liftErr χ c' ≤ Fintype.card ι * (ε₀ / L + L) / c := by
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hsc : 0 < c * G.1 := mul_pos hc hnR
  rw [liftErr, dist_lift_single]
  have hdisp : ∀ a, disp G χ a c' ≤ (ε₀ / L + L) * G.1 := by
    intro a
    have h1 := disp_le h hd hL0 hL1 hexp χ a c'
    have h2 : intWt G χ / L ≤ ε₀ * G.1 / L := div_le_div_of_nonneg_right hint hL0.le
    calc disp G χ a c' ≤ ε₀ * G.1 / L + L * G.1 := by linarith
      _ = (ε₀ / L + L) * G.1 := by ring
  have hsum : ∑ a, disp G χ a c' ≤ Fintype.card ι * ((ε₀ / L + L) * G.1) := by
    calc ∑ a, disp G χ a c' ≤ ∑ _a : ι, (ε₀ / L + L) * G.1 := sum_le_sum fun a _ ↦ hdisp a
      _ = Fintype.card ι * ((ε₀ / L + L) * G.1) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (part G χ c').card := lt_of_lt_of_le hsc (hsize c')
  rw [div_le_div_iff₀ hpos hc]
  have hnn : 0 ≤ Fintype.card ι * ((ε₀ / L + L) * G.1) := le_trans
    (sum_nonneg fun a _ ↦ sum_nonneg fun x _ ↦ sq_nonneg _) hsum
  calc (∑ a, disp G χ a c') * c ≤ Fintype.card ι * ((ε₀ / L + L) * G.1) * c :=
        mul_le_mul_of_nonneg_right hsum hc.le
    _ = Fintype.card ι * (ε₀ / L + L) * (c * G.1) := by ring
    _ ≤ Fintype.card ι * (ε₀ / L + L) * (part G χ c').card := by
        refine mul_le_mul_of_nonneg_left (hsize c') ?_
        have : 0 ≤ Fintype.card ι * (ε₀ / L + L) * G.1 := by linarith
        exact nonneg_of_mul_nonneg_left this hnR

open Classical in
/-- **The lift of an eigenvector of `S` is an approximate eigenvector of `Ã`**:
`‖Ã lift z - μ lift z‖² ≤ m² (ε₀ / L + L) / c`. -/
theorem dist_mulVec_lift_eigenvector {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) {c L ε₀ : ℝ} (hc : 0 < c) (hsize : ∀ a, c * G.1 ≤ (part G χ a).card)
    (hn : 0 < G.1) (hL0 : 0 < L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1)
    (hint : intWt G χ ≤ ε₀ * G.1) (r : ι) :
    (G.normAdj *ᵥ lift G χ (eigVec χ r) - eigVal χ r • lift G χ (eigVec χ r)) ⬝ᵥ
      (G.normAdj *ᵥ lift G χ (eigVec χ r) - eigVal χ r • lift G χ (eigVec χ r)) ≤
      Fintype.card ι ^ 2 * (ε₀ / L + L) / c := by
  rw [mulVec_lift_eigVec_sub]
  refine (dotProduct_sum_smul_le _ (eigVec_dotProduct_self χ r) _).trans ?_
  calc ∑ c', liftErr χ c' ⬝ᵥ liftErr χ c' ≤ ∑ _c' : ι, Fintype.card ι * (ε₀ / L + L) / c :=
        sum_le_sum fun c' _ ↦ liftErr_dotProduct_le h hd χ hc hsize hn hL0 hL1 hexp hint c'
    _ = Fintype.card ι ^ 2 * (ε₀ / L + L) / c := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

omit [Fintype ι] in
/-- The entry `S_ja` of the symmetrized model: `√|V_a| M_aj / √|V_j|`. -/
theorem symModel_apply_eq (χ : Fin G.1 → ι) (hne : ∀ a, (part G χ a).Nonempty) (j a : ι) :
    symModel G χ j a = Real.sqrt (part G χ a).card * pmodel G χ a j /
      Real.sqrt (part G χ j).card := by
  have ha : (0 : ℝ) < (part G χ a).card := by exact_mod_cast (hne a).card_pos
  have hj : (0 : ℝ) < (part G χ j).card := by exact_mod_cast (hne j).card_pos
  have hsa := Real.mul_self_sqrt ha.le
  have hsa0 := Real.sqrt_pos.2 ha
  have hsj0 := Real.sqrt_pos.2 hj
  rw [symModel, sum_wt_comm, ← card_mul_pmodel, sqrt_mul_card]
  field_simp
  rw [Real.sq_sqrt ha.le]
  ring

/-- **Coordinate separation** [BHSV25, Lemma 5.3]: for parts `a ≠ b`, some eigenvector `z` of `S`
with `|μ| ≥ τ` separates them: `(z_a / √|V_a| - z_b / √|V_b|)² ≥ α² / (4 m n)`. -/
theorem exists_sep (χ : Fin G.1 → ι) {c α τ : ℝ} (hc : 0 < c)
    (hsize : ∀ a, c * G.1 ≤ (part G χ a).card) (hn : 0 < G.1) (hα : 0 < α)
    (hsep : ∀ a b, a ≠ b → α ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2)
    (hτ : τ ^ 2 * (2 / c) ≤ α ^ 2 / 2) {a b : ι} (hab : a ≠ b) :
    ∃ r, τ ≤ |eigVal χ r| ∧ α ^ 2 / (4 * Fintype.card ι * G.1) ≤
      (eigVec χ r a / Real.sqrt (part G χ a).card -
        eigVec χ r b / Real.sqrt (part G χ b).card) ^ 2 := by
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hpos : ∀ a, (0 : ℝ) < (part G χ a).card := fun a ↦ lt_of_lt_of_le (mul_pos hc hnR) (hsize a)
  have hne : ∀ a, (part G χ a).Nonempty := fun a ↦ card_pos.1 (by exact_mod_cast hpos a)
  set Da := Real.sqrt G.1 / Real.sqrt (part G χ a).card with hDa
  set Db := Real.sqrt G.1 / Real.sqrt (part G χ b).card with hDb
  set x : ι → ℝ := Da • Pi.single a 1 - Db • Pi.single b 1 with hx
  have hsq : ∀ a', Real.sqrt (part G χ a').card ^ 2 = (part G χ a').card :=
    fun a' ↦ Real.sq_sqrt (hpos a').le
  have hsqn : Real.sqrt G.1 ^ 2 = G.1 := Real.sq_sqrt hnR.le
  have hs0 : ∀ a', 0 < Real.sqrt (part G χ a').card := fun a' ↦ Real.sqrt_pos.2 (hpos a')
  -- `‖x‖² ≤ 2 / c`
  have hD2 : ∀ a', (Real.sqrt G.1 / Real.sqrt (part G χ a').card) ^ 2 ≤ 1 / c := by
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
  have hSx : α ^ 2 ≤ (symModel G χ *ᵥ x) ⬝ᵥ (symModel G χ *ᵥ x) := by
    have hval : ∀ j, (symModel G χ *ᵥ x) j =
        Real.sqrt G.1 * (pmodel G χ a j - pmodel G χ b j) / Real.sqrt (part G χ j).card := by
      intro j
      rw [hx, mulVec_sub, mulVec_smul, mulVec_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
        mulVec_single_one, mulVec_single_one, Matrix.col_apply, Matrix.col_apply,
        symModel_apply_eq χ hne j a, symModel_apply_eq χ hne j b, smul_eq_mul, smul_eq_mul,
        hDa, hDb]
      field_simp
    calc α ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 := hsep a b hab
      _ ≤ ∑ j, (symModel G χ *ᵥ x) j * (symModel G χ *ᵥ x) j := by
          refine sum_le_sum fun j _ ↦ ?_
          rw [hval, ← sq, div_pow, mul_pow, hsqn, hsq]
          rw [le_div_iff₀ (hpos j)]
          have hj : ((part G χ j).card : ℝ) ≤ G.1 := by
            exact_mod_cast (card_le_univ _).trans (by simp)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  obtain ⟨r, hr, hcoef⟩ := exists_coeff_sq_ge (symModel_isHermitian χ)
    (fun r ↦ abs_eigVal_le χ hne r) hα hSx hxx hτ
  refine ⟨r, hr, ?_⟩
  have hcx : coeff (symModel_isHermitian χ) r x = Real.sqrt G.1 *
      (eigVec χ r a / Real.sqrt (part G χ a).card -
        eigVec χ r b / Real.sqrt (part G χ b).card) := by
    rw [hx, coeff_sub', coeff_smul', coeff_smul', coeff_single, coeff_single, hDa, hDb]
    simp only [eigVec]
    ring
  rw [hcx, mul_pow, hsqn] at hcoef
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
  rw [div_le_iff₀ (by positivity)] at hcoef ⊢
  nlinarith

end Eigen

/-! ### Recovering the partition -/

section Recovery

variable {G : Graph} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The target of the net for the eigenvector `r` of `S`: the projection of its lift on the
eigenvectors of `Ã` with `|μ| ≥ θ` if `|μ_r| ≥ τ`, and `0` otherwise. -/
noncomputable def netTarget (χ : Fin G.1 → ι) (θ τ : ℝ) (r : ι) : Fin G.1 → ℝ :=
  open Classical in
  if τ ≤ |eigVal χ r| then proj G.normAdj_isHermitian (fun t ↦ θ ≤ |t|) (lift G χ (eigVec χ r))
  else 0

/-- The values of the eigenvector `r` of `S` on the parts, normalized: `z_a / √|V_a|` if
`|μ_r| ≥ τ`, and `0` otherwise. -/
noncomputable def partValue (χ : Fin G.1 → ι) (τ : ℝ) (r a : ι) : ℝ :=
  open Classical in
  if τ ≤ |eigVal χ r| then eigVec χ r a / Real.sqrt (part G χ a).card else 0

theorem netTarget_dotProduct_le (χ : Fin G.1 → ι) (hne : ∀ a, (part G χ a).Nonempty)
    (θ τ : ℝ) (r : ι) : netTarget χ θ τ r ⬝ᵥ netTarget χ θ τ r ≤ 1 := by
  rw [netTarget]
  split_ifs
  · refine (proj_dotProduct_le _ _ _).trans ?_
    rw [lift_dotProduct_lift χ hne, eigVec_dotProduct_self]
  · simp

theorem netTarget_inEigSpan (χ : Fin G.1 → ι) (θ τ : ℝ) (r : ι) :
    G.InEigSpan (fun μ ↦ θ ≤ |μ|) (netTarget χ θ τ r) := by
  rw [netTarget]
  split_ifs
  · exact inEigSpan_proj _ _ _
  · intro i _
    simp [coeff]

open Classical in
/-- The net targets are close to the values on the parts:
`∑_y (w_r(y) - V_r(χ y))² ≤ m² (ε₀ / L + L) / (c (τ - θ)²)`. -/
theorem sum_netTarget_sub_le {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) {c L ε₀ θ τ : ℝ} (hc : 0 < c) (hsize : ∀ a, c * G.1 ≤ (part G χ a).card)
    (hn : 0 < G.1) (hL0 : 0 < L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1)
    (hint : intWt G χ ≤ ε₀ * G.1) (hθτ : θ < τ) (r : ι) :
    ∑ y, (netTarget χ θ τ r y - partValue χ τ r (χ y)) ^ 2 ≤
      Fintype.card ι ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2) := by
  have hη : 0 < τ - θ := sub_pos.2 hθτ
  have hbound : 0 ≤ Fintype.card ι ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2) := by
    have h0 := dist_mulVec_lift_eigenvector h hd χ hc hsize hn hL0 hL1 hexp hint r
    have : 0 ≤ Fintype.card ι ^ 2 * (ε₀ / L + L) / c :=
      le_trans (sum_nonneg fun x _ ↦ mul_self_nonneg _) h0
    rw [← div_div]
    positivity
  unfold netTarget partValue
  split_ifs with hbig
  · have hlift : ∀ y, eigVec χ r (χ y) / Real.sqrt (part G χ (χ y)).card =
        lift G χ (eigVec χ r) y := fun y ↦ rfl
    simp only [hlift]
    have h1 := dist_proj_le G.normAdj_isHermitian hη (by linarith : θ + (τ - θ) ≤ |eigVal χ r|)
      (lift G χ (eigVec χ r))
    have h2 := dist_mulVec_lift_eigenvector h hd χ hc hsize hn hL0 hL1 hexp hint r
    have h3 : ∑ y, (proj G.normAdj_isHermitian (fun t ↦ θ ≤ |t|) (lift G χ (eigVec χ r)) y -
        lift G χ (eigVec χ r) y) ^ 2 =
        (lift G χ (eigVec χ r) - proj G.normAdj_isHermitian (fun t ↦ θ ≤ |t|)
          (lift G χ (eigVec χ r))) ⬝ᵥ (lift G χ (eigVec χ r) -
          proj G.normAdj_isHermitian (fun t ↦ θ ≤ |t|) (lift G χ (eigVec χ r))) := by
      simp only [dotProduct, Pi.sub_apply]
      exact sum_congr rfl fun y _ ↦ by ring
    rw [h3, le_div_iff₀ (by positivity)]
    calc _ = (τ - θ) ^ 2 * ((lift G χ (eigVec χ r) - proj G.normAdj_isHermitian
            (fun t ↦ θ ≤ |t|) (lift G χ (eigVec χ r))) ⬝ᵥ (lift G χ (eigVec χ r) -
            proj G.normAdj_isHermitian (fun t ↦ θ ≤ |t|) (lift G χ (eigVec χ r)))) * c := by
          ring
      _ ≤ Fintype.card ι ^ 2 * (ε₀ / L + L) / c * c :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hc.le
      _ = Fintype.card ι ^ 2 * (ε₀ / L + L) := div_mul_cancel₀ _ hc.ne'
  · simpa using hbound

end Recovery

/-! ### Few large eigenvalues -/

open Classical in
/-- **[BHSV25, Corollary 4.2]** for the net: a regular graph with at most one eigenvalue above
`δ < θ'² / 2`, `0 < θ' < 1`, has at most `1 + 4 / θ'⁴` eigenvalues of absolute value at least
`θ'`. -/
theorem card_abs_eig_ge_le (G : Graph) {δ θ' : ℝ} (hθ0 : 0 < θ') (hθ1 : θ' < 1)
    (hδ : δ < θ' ^ 2 / 2) (hexp : G.numEigGT δ ≤ 1) :
    ((univ.filter fun i ↦ θ' ≤ |G.eig i|).card : ℝ) ≤ 1 + 4 / θ' ^ 4 := by
  set σ := θ' ^ 2 / 2 with hσ
  have hσ0 : 0 < σ := by positivity
  have hθ2 : θ' ^ 2 < 1 := by nlinarith
  have hσ1 : σ < 1 := by linarith
  -- eigenvalues at least `σ`: at most one
  have hge : (univ.filter fun i ↦ σ ≤ G.eig i).card ≤ 1 := by
    refine le_trans (card_le_card fun i hi ↦ ?_) hexp
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_lt_of_le hδ hi.2⟩
  -- eigenvalues at most `-θ'`: at most `1 / σ²`
  have hneg := G.card_eig_le_neg_le hσ0.le hσ1 hσ0 hσ1
  have hsqrt : Real.sqrt (σ * (1 - σ) + σ) ≤ θ' := by
    rw [Real.sqrt_le_left hθ0.le]
    nlinarith
  have hsub : (univ.filter fun i ↦ G.eig i ≤ -θ') ⊆
      univ.filter fun i ↦ G.eig i ≤ -Real.sqrt (σ * (1 - σ) + σ) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans (by linarith)⟩
  have hneg' : σ ^ 2 * ((univ.filter fun i ↦ G.eig i ≤ -θ').card : ℝ) ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub)
      (sq_nonneg σ)) (hneg.trans ?_)
    exact_mod_cast hge
  have hpos : (univ.filter fun i ↦ θ' ≤ G.eig i).card ≤ 1 := by
    refine le_trans (card_le_card fun i hi ↦ ?_) hge
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans (by nlinarith) hi.2⟩
  have hunion : (univ.filter fun i ↦ θ' ≤ |G.eig i|) ⊆
      (univ.filter fun i ↦ θ' ≤ G.eig i) ∪ univ.filter fun i ↦ G.eig i ≤ -θ' := by
    intro i hi
    rw [mem_filter] at hi
    rw [mem_union, mem_filter, mem_filter]
    rcases le_abs'.1 hi.2 with h | h
    · exact Or.inr ⟨mem_univ _, h⟩
    · exact Or.inl ⟨mem_univ _, h⟩
  have h1 : ((univ.filter fun i ↦ θ' ≤ |G.eig i|).card : ℝ) ≤
      (univ.filter fun i ↦ θ' ≤ G.eig i).card + (univ.filter fun i ↦ G.eig i ≤ -θ').card := by
    exact_mod_cast (card_le_card hunion).trans (card_union_le _ _)
  have h2 : ((univ.filter fun i ↦ G.eig i ≤ -θ').card : ℝ) ≤ 4 / θ' ^ 4 := by
    have hσ2 : σ ^ 2 = θ' ^ 4 / 4 := by rw [hσ]; ring
    rw [hσ2] at hneg'
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h3 : ((univ.filter fun i ↦ θ' ≤ G.eig i).card : ℝ) ≤ 1 := by exact_mod_cast hpos
  linarith

end Alg

end BHSV25
