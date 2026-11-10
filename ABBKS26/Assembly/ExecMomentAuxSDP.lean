module

public import ABBKS26.Assembly.ExecData

/-! Algebraic facts for the degree-two weight/Gram moment program. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.MomentAux

noncomputable section

open Common Robust Rounding MvPolynomial Matrix
open scoped BigOperators

variable {n d : ℕ}

theorem embed_coeff_degree (p : RPoly d) : NestedAux.CoeffDegree (embedCoeff p) 0 := by
  intro μ
  simp [embedCoeff, coeff_map]

theorem gram_coeff_degree (start : ℕ) (L : List (Fin d →₀ ℕ)) :
    NestedAux.CoeffDegree (gram start L) 2 := by
  apply NestedAux.CoeffDegree.sum
  intro c _
  apply NestedAux.CoeffDegree.pow (n := 1) (k := 2)
  apply NestedAux.CoeffDegree.sum
  intro a _
  have hx : NestedAux.CoeffDegree (C (X (start + a * L.length + c)) : Template d) 1 := by
    simpa using NestedAux.CoeffDegree.const (σ := Fin d)
      (X (start + a * L.length + c) : NPoly)
  have hm : NestedAux.CoeffDegree (monomial L[a] (1 : NPoly)) 0 := by
    simpa using NestedAux.CoeffDegree.monomial L[a] (1 : NPoly)
  simpa using hx.mul hm

theorem template_coeff_degree (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (a : Fin J.length) : NestedAux.CoeffDegree (momentTemplate x J B a) 2 := by
  apply NestedAux.CoeffDegree.sub
  · apply NestedAux.CoeffDegree.sub
    · exact (embed_coeff_degree _).mono (by omega)
    · apply NestedAux.CoeffDegree.sum
      intro i _
      have hx : NestedAux.CoeffDegree (C (X i.val) : Template d) 1 := by
        simpa using NestedAux.CoeffDegree.const (σ := Fin d) (X i.val : NPoly)
      exact (hx.mul (embed_coeff_degree _)).mono (by omega)
  · exact gram_coeff_degree _ _

theorem constraints_degree (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (ε ball : ℝ) (f : NPoly) (hf : f ∈ momentConstraints x J B ε ball) :
    f.totalDegree ≤ 2 := by
  classical
  simp only [momentConstraints, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap] at hf
  rcases hf with ((rfl | hf) | rfl) | hf
  · refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    exact totalDegree_finsetSum_le fun i _ ↦ by simp
  · obtain ⟨i, _, rfl | rfl⟩ := hf
    · simp
    · exact (totalDegree_sub _ _).trans (by simp)
  · refine (totalDegree_sub _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
    exact totalDegree_finsetSum_le fun i _ ↦ by simp
  · obtain ⟨a, _, μ, _, rfl | rfl⟩ := hf
    · exact template_coeff_degree x J B a μ
    · simpa only [totalDegree_neg] using template_coeff_degree x J B a μ

/-- The Gram entries read from a degree-two pseudo-expectation are exactly PSD. -/
theorem expected_gram_psd {σ : Type} {m : ℕ} (E : SoS.PseudoExpectation σ 2)
    (p : Fin m → MvPolynomial σ ℝ) (hp : ∀ i, (p i).totalDegree ≤ 1) :
    Matrix.PosSemidef (fun i j : Fin m ↦ E (p i * p j)) := by
  classical
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v ↦ ?_
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, mul_comm]
  · let q : MvPolynomial σ ℝ := ∑ i, C (v i) * p i
    have hq : q.totalDegree ≤ 1 := by
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simpa using hp i)
    have he : q * q = ∑ i, ∑ j, C (v i * v j) * (p i * p j) := by
      simp only [q, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [C_mul]
      ring
    have hpos := E.map_mul_self_nonneg (show 2 * q.totalDegree ≤ 2 by omega)
    rw [he, E.map_sum] at hpos
    simp only [E.map_sum, E.map_C_mul] at hpos
    simpa only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using hpos

/-- Substituting arbitrary outer polynomials in a read Gram matrix preserves SoS. -/
theorem expected_gram_sos {σ : Type} {m : ℕ} (E : SoS.PseudoExpectation σ 2)
    (p : Fin m → MvPolynomial σ ℝ) (hp : ∀ i, (p i).totalDegree ≤ 1)
    (v : Fin m → RPoly d) :
    IsSumSq (∑ i, ∑ j, C (E (p i * p j)) * v i * v j) := by
  have h := SoSKit.psd_quad _ (expected_gram_psd E p hp)
  have hs := SoS.isSumSq_map (eval₂Hom (C : ℝ →+* RPoly d) v) h
  simpa [quad, map_sum] using hs

/-- Apply the pseudo-expectation to the inner coefficients only. -/
def expectCoeffs (E : SoS.PseudoExpectation ℕ 2) (p : Template d) : RPoly d :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange E E.map_zero p.coeff)

@[simp] theorem coeff_expectCoeffs (E : SoS.PseudoExpectation ℕ 2)
    (p : Template d) (μ : Fin d →₀ ℕ) :
    (expectCoeffs E p).coeff μ = E (p.coeff μ) := rfl


theorem expectCoeffs_sub (E : SoS.PseudoExpectation ℕ 2) (p q : Template d) :
    expectCoeffs E (p - q) = expectCoeffs E p - expectCoeffs E q := by
  ext μ
  simp

theorem expectCoeffs_sum {ι : Type} (E : SoS.PseudoExpectation ℕ 2)
    (S : Finset ι) (p : ι → Template d) :
    expectCoeffs E (∑ i ∈ S, p i) = ∑ i ∈ S, expectCoeffs E (p i) := by
  ext μ
  simp [E.map_sum]

theorem expectCoeffs_embed (E : SoS.PseudoExpectation ℕ 2) (p : RPoly d) :
    expectCoeffs E (embedCoeff p) = p := by
  ext μ
  simp [embedCoeff, coeff_map]

theorem expectCoeffs_const_mul_embed (E : SoS.PseudoExpectation ℕ 2)
    (q : NPoly) (p : RPoly d) :
    expectCoeffs E (C q * embedCoeff p) = C (E q) * p := by
  ext μ
  simp only [coeff_expectCoeffs, coeff_C_mul, embedCoeff, coeff_map]
  rw [mul_comm q, E.map_C_mul, mul_comm]

theorem expectCoeffs_monomial (E : SoS.PseudoExpectation ℕ 2)
    (μ : Fin d →₀ ℕ) (q : NPoly) :
    expectCoeffs E (monomial μ q) = monomial μ (E q) := by
  classical
  ext ν
  by_cases h : μ = ν <;> simp [coeff_monomial, h]

/-- The full read Gram polynomial, including its lower degree terms. -/
def readGram (E : SoS.PseudoExpectation ℕ 2) (start : ℕ)
    (L : List (Fin d →₀ ℕ)) : RPoly d :=
  ∑ c : Fin L.length, ∑ a : Fin L.length, ∑ b : Fin L.length,
    C (E (X (start + a * L.length + c) * X (start + b * L.length + c))) *
      monomial L[a] 1 * monomial L[b] 1

theorem expectCoeffs_gram (E : SoS.PseudoExpectation ℕ 2) (start : ℕ)
    (L : List (Fin d →₀ ℕ)) : expectCoeffs E (gram start L) = readGram E start L := by
  simp only [Rounding.gram, pow_two, Finset.sum_mul_sum]
  simp only [expectCoeffs_sum, readGram]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : (C (X (start + a * L.length + c)) * monomial L[a] 1) *
      (C (X (start + b * L.length + c)) * monomial L[b] 1) =
      monomial (L[a] + L[b])
        (X (start + a * L.length + c) * X (start + b * L.length + c) : NPoly) := by
    rw [C_mul_monomial, C_mul_monomial, monomial_mul_monomial]
    simp
  rw [he, expectCoeffs_monomial, C_mul_monomial, monomial_mul_monomial]
  simp

theorem readGram_sos (E : SoS.PseudoExpectation ℕ 2) (start : ℕ)
    (L : List (Fin d →₀ ℕ)) : IsSumSq (readGram E start L) := by
  apply IsSumSq.sum
  intro c _
  exact expected_gram_sos E (fun a ↦ X (start + a * L.length + c))
    (fun _ ↦ by simp) (fun a ↦ monomial L[a] 1)

theorem readGram_degree (E : SoS.PseudoExpectation ℕ 2) (start r : ℕ)
    (L : List (Fin d →₀ ℕ)) (hL : ∀ μ ∈ L, μ.degree ≤ r) :
    (readGram E start L).totalDegree ≤ 2 * r := by
  apply totalDegree_finsetSum_le
  intro c _
  apply totalDegree_finsetSum_le
  intro a _
  apply totalDegree_finsetSum_le
  intro b _
  have ha := hL L[a] (List.getElem_mem a.isLt)
  have hb := hL L[b] (List.getElem_mem b.isLt)
  refine (totalDegree_mul _ _).trans ?_
  have hh := totalDegree_mul
    (C (E (X (start + a * L.length + c) * X (start + b * L.length + c))))
    (monomial L[a] (1 : ℝ))
  have hma := totalDegree_monomial_le L[a] (1 : ℝ)
  have hmb := totalDegree_monomial_le L[b] (1 : ℝ)
  change (monomial L[a] (1 : ℝ)).totalDegree ≤ L[a].degree at hma
  change (monomial L[b] (1 : ℝ)).totalDegree ≤ L[b].degree at hmb
  rw [totalDegree_C, zero_add] at hh
  omega

theorem template_read (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (a : Fin J.length) :
    expectCoeffs E (momentTemplate x J B a) =
      C (B J[a] * n) * nsq ^ J[a] -
        (∑ i : Fin n, C (E (X i.val)) * lin (x i) ^ (2 * J[a])) -
        readGram E (momentGramOffset n d J a) (monos d J[a]) := by
  simp only [momentTemplate, expectCoeffs_sub, expectCoeffs_embed, expectCoeffs_sum,
    expectCoeffs_const_mul_embed, expectCoeffs_gram]

theorem top_component_sos (p : RPoly d) (r : ℕ) (hp : IsSumSq p)
    (hd : p.totalDegree ≤ 2 * r) : IsSumSq (homogeneousComponent (2 * r) p) := by
  obtain ⟨L, rfl, hL⟩ := SoS.IsSumSq.exists_list_of_totalDegree_le hp hd
  rw [map_list_sum, List.map_map]
  simp only [Function.comp_def]
  have he : (L.map fun q ↦ homogeneousComponent (2 * r) (q * q)) =
      (L.map fun q ↦ homogeneousComponent r q * homogeneousComponent r q) := by
    apply List.map_congr_left
    intro q hq
    exact SoS.homogeneousComponent_mul_self (by have := hL q hq; omega)
  rw [he]
  simpa only [List.map_map, Function.comp_def] using
    SoS.isSumSq_sum_mul_self (L.map (homogeneousComponent r))

theorem monos_degree (r : ℕ) (μ : Fin d →₀ ℕ) (hμ : μ ∈ monos d r) :
    μ.degree ≤ r := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hμ
  exact (SoS.Mono.degree_toFinsupp (SoS.Mono.mem_all.mp he).1).trans_le
    (SoS.Mono.mem_all.mp he).2

theorem mem_monos_of_degree (r : ℕ) (μ : Fin d →₀ ℕ) (hμ : μ.degree ≤ r) :
    μ ∈ monos d r := by
  let e := List.ofFn μ
  have he : SoS.Mono.toFinsupp d e = μ := SoS.Poly.toFinsupp_ofFn μ
  have hlen : e.length = d := by simp [e]
  have hsum : e.sum ≤ r := by
    rw [← SoS.Mono.degree_toFinsupp hlen, he]
    exact hμ
  exact List.mem_map.mpr ⟨e, SoS.Mono.mem_all.mpr ⟨hlen, hsum⟩, he⟩

theorem coefficient_constraints_mem (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (ε ball : ℝ) (a : Fin J.length) (μ : Fin d →₀ ℕ) (hμ : μ ∈ monos d (2 * J[a])) :
    (momentTemplate x J B a).coeff μ ∈ momentConstraints x J B ε ball ∧
      -(momentTemplate x J B a).coeff μ ∈ momentConstraints x J B ε ball := by
  simp only [momentConstraints, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap]
  constructor
  · exact Or.inr ⟨a, List.mem_finRange a, μ, hμ, Or.inl rfl⟩
  · exact Or.inr ⟨a, List.mem_finRange a, μ, hμ, Or.inr rfl⟩


/-- Only the top homogeneous component of the coefficient residual is needed. -/
theorem read_moment_sos (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (a : Fin J.length) (δ : ℝ)
    (herr : SoS.coeffNorm1
      (homogeneousComponent (2 * J[a]) (expectCoeffs E (momentTemplate x J B a))) ≤ δ) :
    IsSumSq (C (B J[a] * n + δ) * nsq ^ J[a] -
      ∑ i : Fin n, C (E (X i.val)) * lin (x i) ^ (2 * J[a])) := by
  let r := J[a]
  let P : RPoly d := C (B r * n) * nsq ^ r -
    ∑ i : Fin n, C (E (X i.val)) * lin (x i) ^ (2 * r)
  let G := readGram E (momentGramOffset n d J a) (monos d r)
  let R := homogeneousComponent (2 * r) (expectCoeffs E (momentTemplate x J B a))
  have hlin (u : Vec d) : (lin u).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ ↦ (isHomogeneous_X ℝ i).C_mul (u i)
  have hP : P.IsHomogeneous (2 * r) := by
    apply IsHomogeneous.sub
    · apply IsHomogeneous.C_mul
      simpa only [nsq, Nat.mul_comm] using
        (IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow i 2).pow r
    · apply IsHomogeneous.sum
      intro i _
      simpa only [one_mul] using ((hlin (x i)).pow (2 * r)).C_mul (E (X i.val))
  have hid : P = R + homogeneousComponent (2 * r) G := by
    have ht : expectCoeffs E (momentTemplate x J B a) = P - G := template_read E x J B a
    have h : R = P - homogeneousComponent (2 * r) G := by
      dsimp only [R]
      rw [ht, map_sub, homogeneousComponent_eq_self hP]
    linear_combination -h
  have hG : IsSumSq (homogeneousComponent (2 * r) G) :=
    top_component_sos G r (readGram_sos E _ _)
      (readGram_degree E _ r _ fun μ hμ ↦ monos_degree r μ hμ)
  have hR : R.IsHomogeneous (2 * r) := homogeneousComponent_isHomogeneous _ _
  have hE := SoS.isSumSq_l1 hR.neg
  rw [SoS.coeffNorm1_neg, sub_neg_eq_add] at hE
  change IsSumSq (C (SoS.coeffNorm1 R) * nsq ^ r + R) at hE
  have hslack : IsSumSq (C (δ - SoS.coeffNorm1 R) * (nsq : RPoly d) ^ r) :=
    SoS.isSumSq_C_mul (sub_nonneg.mpr herr)
      (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) r)
  have hs : IsSumSq (C δ * (nsq : RPoly d) ^ r + R) := by
    convert hE.add hslack using 1
    rw [C_sub]
    ring
  have hb : IsSumSq (P + C δ * nsq ^ r) := by
    rw [hid]
    convert hG.add hs using 1
    ring
  convert hb using 1
  dsimp only [P, r]
  rw [C_add]
  ring

theorem clipped_read_sos (E : SoS.PseudoExpectation ℕ 2) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (a : Fin J.length) (δ ρ : ℝ) (hρ : 0 ≤ ρ)
    (hw : ∀ i : Fin n, -ρ ≤ E (X i.val) ∧ E (X i.val) ≤ 1 + ρ)
    (herr : SoS.coeffNorm1
      (homogeneousComponent (2 * J[a]) (expectCoeffs E (momentTemplate x J B a))) ≤ δ) :
    IsSumSq (C (B J[a] * n + δ + ρ * ∑ i, sqnorm (x i) ^ J[a]) * nsq ^ J[a] -
      ∑ i : Fin n, C (clipped (E (X i.val))) * lin (x i) ^ (2 * J[a])) :=
  clipping_sos x (fun i ↦ E (X i.val)) (B J[a] * n + δ) ρ J[a] hρ hw
    (read_moment_sos E x J B a δ herr)


theorem clipped_bounds (u : ℝ) : 0 ≤ clipped u ∧ clipped u ≤ 1 := by
  exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

theorem clipped_error {u ρ : ℝ} (hρ : 0 ≤ ρ) (hu : -ρ ≤ u ∧ u ≤ 1 + ρ) :
    |clipped u - u| ≤ ρ := by
  unfold clipped
  by_cases h0 : 0 ≤ u
  · rw [max_eq_left h0]
    by_cases h1 : u ≤ 1
    · simpa [min_eq_left h1] using hρ
    · rw [min_eq_right (le_of_not_ge h1), abs_of_nonpos (by linarith)]
      linarith only [hu.2]
  · rw [max_eq_right (le_of_not_ge h0), min_eq_left zero_le_one, zero_sub, abs_neg,
      abs_of_nonpos (le_of_not_ge h0)]
    linarith only [hu.1]


theorem weight_constraints_mem (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (ε ball : ℝ) (i : Fin n) :
    (X i.val : NPoly) ∈ momentConstraints x J B ε ball ∧
      (1 - X i.val : NPoly) ∈ momentConstraints x J B ε ball := by
  simp only [momentConstraints, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap]
  constructor
  · exact Or.inl (Or.inl (Or.inr ⟨i, List.mem_finRange i, Or.inl rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨i, List.mem_finRange i, Or.inr rfl⟩))


end

end ABBKS26.Assembly.Exec.MomentAux
