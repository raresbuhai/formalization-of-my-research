module

public import ABBKS26.Assembly.ExecMomentAuxSDP

/-! Reading degree-two constraints only needs their singleton consequences. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.MomentRead

noncomputable section

open Common Robust Rounding MvPolynomial Matrix
open _root_.ABBKS26.Assembly.Exec.MomentAux
open scoped BigOperators

variable {n d : ℕ}

theorem coeffNorm_rename {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    (p : MvPolynomial σ ℝ) : SoS.coeffNorm (rename f p) = SoS.coeffNorm p := by
  classical
  unfold SoS.coeffNorm
  rw [support_rename_of_injective hf, Finset.sum_image
    (fun _ _ _ _ h ↦ Finsupp.mapDomain_injective hf h)]
  simp only [coeff_rename_mapDomain f hf]

theorem coeffNorm1_rename {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    (p : MvPolynomial σ ℝ) : SoS.coeffNorm1 (rename f p) = SoS.coeffNorm1 p := by
  classical
  unfold SoS.coeffNorm1
  rw [support_rename_of_injective hf, Finset.sum_image
    (fun _ _ _ _ h ↦ Finsupp.mapDomain_injective hf h)]
  simp only [coeff_rename_mapDomain f hf]

theorem totalDegree_toReal (p : MvPolynomial (Fin n) ℚ) :
    (SoS.toReal p).totalDegree = p.totalDegree := by
  unfold SoS.toReal totalDegree
  rw [support_map_of_injective p Rat.cast_injective]

def indexBack (v : ℕ) (hv : 0 < v) (i : ℕ) : Fin v :=
  if hi : i < v then ⟨i, hi⟩ else ⟨0, hv⟩

theorem indexBack_val (v : ℕ) (hv : 0 < v) (i : Fin v) : indexBack v hv i.val = i := by
  simp [indexBack, i.isLt]

def lift {v : ℕ} (E : SoS.PseudoExpectation (Fin v) 2) (hv : 0 < v) :
    SoS.PseudoExpectation ℕ 2 where
  toLinearMap := E.toLinearMap.comp (rename (indexBack v hv)).toLinearMap
  map_one' := by simp
  map_mul_self_nonneg' p hp := by
    change 0 ≤ E (rename (indexBack v hv) (p * p))
    rw [map_mul]
    apply E.map_mul_self_nonneg
    have hdeg := totalDegree_rename_le (indexBack v hv) p
    omega

theorem lift_rename {v : ℕ} (E : SoS.PseudoExpectation (Fin v) 2) (hv : 0 < v)
    (p : MvPolynomial (Fin v) ℝ) : lift E hv (rename Fin.val p) = E p := by
  change E (rename (indexBack v hv) (rename Fin.val p)) = E p
  rw [rename_rename]
  have h : indexBack v hv ∘ Fin.val = id := by funext i; exact indexBack_val v hv i
  simp only [h, rename_id, AlgHom.id_apply]

theorem sample_norm_sum_le {m d A S r : ℕ} (x : Fin m → Vec d)
    (hm : m ≤ A) (hd : d ≤ A) (hr : 1 ≤ r) (hS : 4 * r ≤ S)
    (hx : ∀ i j, |x i j| ≤ 2 ^ A) :
    (∑ i, sqnorm (x i) ^ r) ≤ (2 : ℝ) ^ (S * A) := by
  have hA : (A : ℝ) ≤ 2 ^ A := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hd' : (d : ℝ) ≤ 2 ^ A := (by exact_mod_cast hd : (d : ℝ) ≤ A).trans hA
  have hm' : (m : ℝ) ≤ 2 ^ A := (by exact_mod_cast hm : (m : ℝ) ≤ A).trans hA
  have hi (i : Fin m) : sqnorm (x i) ≤ (2 : ℝ) ^ (3 * A) := by
    unfold sqnorm dotProduct
    calc
      _ ≤ ∑ _j : Fin d, ((2 : ℝ) ^ A) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [pow_le_pow_left₀ (abs_nonneg _) (hx i j) 2, sq_abs (x i j)]
      _ ≤ 2 ^ A * ((2 : ℝ) ^ A) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hd' (sq_nonneg ((2 : ℝ) ^ A))
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  calc
    _ ≤ ∑ _i : Fin m, ((2 : ℝ) ^ (3 * A)) ^ r := by
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ _ (hi i)
      change 0 ≤ ∑ j : Fin d, x i j * x i j
      exact Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _
    _ ≤ 2 ^ A * ((2 : ℝ) ^ (3 * A)) ^ r := by
      simpa using mul_le_mul_of_nonneg_right hm' (by positivity :
        0 ≤ ((2 : ℝ) ^ (3 * A)) ^ r)
    _ = (2 : ℝ) ^ ((3 * r + 1) * A) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right A (by omega))

theorem dyadic_error_bound (S A : ℕ) (C₀ V : ℝ) (hA : 1 ≤ A)
    (hC : C₀ ≤ S * (2 : ℝ) ^ S) (hV : V ≤ (2 : ℝ) ^ (S * A)) :
    (2 / (2 : ℝ) ^ ((S + A + 2) ^ 2)) * C₀ +
      (4 / (2 : ℝ) ^ ((S + A + 2) ^ 2)) * V ≤ 1 := by
  have hS : (S : ℝ) ≤ 2 ^ S := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hC' : C₀ ≤ (2 : ℝ) ^ (2 * S) := by
    calc
      _ ≤ S * (2 : ℝ) ^ S := hC
      _ ≤ 2 ^ S * (2 : ℝ) ^ S := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by rw [← pow_add, two_mul]
  have h1 : (2 : ℝ) ^ (2 * S) ≤ 2 ^ (S * A + 2 * S + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (S * A) ≤ 2 ^ (S * A + 2 * S + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow : (2 : ℝ) ^ (S * A + 2 * S + 5) ≤ 2 ^ ((S + A + 2) ^ 2) := by
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ ((S + A + 2) ^ 2))).mp
  field_simp
  calc
    2 * C₀ + 4 * V ≤ 8 * (2 : ℝ) ^ (S * A + 2 * S + 2) := by
      linarith only [hC'.trans h1, hV.trans h2,
        pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (S * A + 2 * S + 2)]
    _ = (2 : ℝ) ^ (S * A + 2 * S + 5) := by
      simp only [pow_add]
      norm_num
      ring
    _ ≤ _ := hpow

theorem single_coefficient_read_bound (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f)
    (a : Fin J.length) (μ : Fin d →₀ ℕ) (hμ : μ ∈ monos d (2 * J[a])) :
    |E ((momentTemplate x J B a).coeff μ)| ≤
      η * SoS.coeffNorm1 ((momentTemplate x J B a).coeff μ) := by
  let c := (momentTemplate x J B a).coeff μ
  obtain ⟨hp, hn⟩ := coefficient_constraints_mem x J B ε ball a μ hμ
  have hp' := hE _ hp
  have hn' := hE _ hn
  change -(η * SoS.coeffNorm c) ≤ E c at hp'
  change -(η * SoS.coeffNorm (-c)) ≤ E (-c) at hn'
  simp only [E.map_neg] at hn'
  have hnp := mul_le_mul_of_nonneg_left (SoS.coeffNorm_le_coeffNorm1 c) hη
  have hnn := mul_le_mul_of_nonneg_left (SoS.coeffNorm_le_coeffNorm1 (-c)) hη
  rw [SoS.coeffNorm1_neg] at hnn
  rw [abs_le]
  constructor <;> linarith only [hp', hn', hnp, hnn]

theorem single_residual_norm_bound (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f)
    (a : Fin J.length) :
    SoS.coeffNorm1
      (homogeneousComponent (2 * J[a]) (expectCoeffs E (momentTemplate x J B a))) ≤
      η * ∑ μ ∈ (monos d (2 * J[a])).toFinset,
        SoS.coeffNorm1 ((momentTemplate x J B a).coeff μ) := by
  classical
  let R := homogeneousComponent (2 * J[a]) (expectCoeffs E (momentTemplate x J B a))
  have hs : R.support ⊆ (monos d (2 * J[a])).toFinset := by
    intro μ hμ
    have hdeg : μ.degree = 2 * J[a] := by
      by_contra h
      have hc := mem_support_iff.mp hμ
      simp only [R, coeff_homogeneousComponent, ite_eq_right h] at hc
      exact hc rfl
    exact List.mem_toFinset.mpr (mem_monos_of_degree _ μ hdeg.le)
  rw [SoS.coeffNorm1_eq_of_support_subset hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro μ hμ
  dsimp only [R]
  rw [coeff_homogeneousComponent]
  split_ifs
  · rw [coeff_expectCoeffs]
    exact single_coefficient_read_bound E x J B ε ball η hη hE a μ
      (List.mem_toFinset.mp hμ)
  · exact (abs_zero : |(0 : ℝ)| = 0).le.trans
      (mul_nonneg hη (SoS.coeffNorm1_nonneg _))

theorem single_read_weights_bounds (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f) (i : Fin n) :
    -(2 * η) ≤ E (X i.val) ∧ E (X i.val) ≤ 1 + 2 * η := by
  obtain ⟨hl, hu⟩ := weight_constraints_mem x J B ε ball i
  have hl' := hE _ hl
  have hu' := hE _ hu
  simp only [E.map_sub, E.map_one] at hl' hu'
  have hnl : SoS.coeffNorm (X i.val : NPoly) ≤ 1 := by
    simpa only [SoS.coeffNorm1_X] using SoS.coeffNorm_le_coeffNorm1 (X i.val : NPoly)
  have hnu : SoS.coeffNorm (1 - X i.val : NPoly) ≤ 2 := by
    refine (SoS.coeffNorm_le_coeffNorm1 _).trans ((SoS.coeffNorm1_sub_le _ _).trans ?_)
    simp only [SoS.coeffNorm1_one, SoS.coeffNorm1_X]
    norm_num
  have hnl' := mul_le_mul_of_nonneg_left hnl hη
  have hnu' := mul_le_mul_of_nonneg_left hnu hη
  constructor <;> linarith only [hl', hu', hnl', hnu', hη]

theorem single_read_mass_lower (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f) :
    (1 - ε) * n - 2 * η * n ≤ ∑ i : Fin n, E (X i.val) := by
  let f : NPoly := (∑ i : Fin n, X i.val) - C ((1 - ε) * n)
  have hf : f ∈ momentConstraints x J B ε ball := by
    simp only [momentConstraints, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (Or.inr rfl)
  have hm := hE _ hf
  have hns : SoS.coeffNorm1 (∑ i : Fin n, (X i.val : NPoly)) ≤ n := by
    simpa only [SoS.coeffNorm1_X, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using
      SoS.coeffNorm1_sum_le Finset.univ (fun i : Fin n ↦ (X i.val : NPoly))
  have hconst : |(1 - ε) * (n : ℝ)| ≤ n := by
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (Nat.cast_nonneg _))]
    nlinarith only [mul_nonneg hε.1 (Nat.cast_nonneg (α := ℝ) n)]
  have hnf : SoS.coeffNorm f ≤ 2 * n := by
    refine (SoS.coeffNorm_le_coeffNorm1 f).trans ?_
    have hh := SoS.coeffNorm1_sub_le (∑ i : Fin n, (X i.val : NPoly))
      (C ((1 - ε) * n))
    rw [SoS.coeffNorm1_C] at hh
    change SoS.coeffNorm1 f ≤ _ at hh
    linarith only [hh, hns, hconst]
  have hh := mul_le_mul_of_nonneg_left hnf hη
  dsimp only [f] at hm
  rw [E.map_sub, E.map_sum, E.map_C] at hm
  linarith only [hm, hh]

theorem single_read_clipped_mass (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f) :
    (1 - ε - 4 * η) * n ≤ ∑ i : Fin n, clipped (E (X i.val)) := by
  have hm := single_read_mass_lower E x J B ε ball η hη hε hE
  have hc := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    (abs_le.mp (clipped_error (show 0 ≤ 2 * η by positivity)
      (single_read_weights_bounds E x J B ε ball η hη hE i))).1
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hc
  nlinarith only [hm, hc]

theorem single_approximate_clipped_sos (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε ball η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ f ∈ momentConstraints x J B ε ball, -(η * SoS.coeffNorm f) ≤ E f)
    (a : Fin J.length) :
    IsSumSq (C (B J[a] * n +
      η * ∑ μ ∈ (monos d (2 * J[a])).toFinset,
        SoS.coeffNorm1 ((momentTemplate x J B a).coeff μ) +
      (2 * η) * ∑ i, sqnorm (x i) ^ J[a]) * nsq ^ J[a] -
      ∑ i : Fin n, C (clipped (E (X i.val))) * lin (x i) ^ (2 * J[a])) :=
  clipped_read_sos E x J B a _ (2 * η) (by positivity)
    (single_read_weights_bounds E x J B ε ball η hη hE)
    (single_residual_norm_bound E x J B ε ball η hη hE a)

end

end ABBKS26.Assembly.Exec.MomentRead
