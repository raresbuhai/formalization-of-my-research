module

public import BKS23.Rounding

/-!
# Rounding to a nearby set

The rounding of `BKS23/Rounding.lean` when the certificate is too weak to round to the planted
clique exactly, as for [BKS23, Theorem 5.6 (1)] (`|x| |y| ≤ ω` with `ω ≈ n p / (1 - p)`): some
`S_Q = {i | Ẽ[w_Q] ≤ 2 Ẽ[w_Q wᵢ]}` differs from the planted set `S` in at most about
`8 ω (n/k²)^T` vertices (`BKS23.Rounding.exists_round_near_eq`). This is [BKS23, Theorem 5.1]
with `δ = (1 - p)/24`, but with the threshold `1/2` instead of `1 - 2δ`, so that the algorithm
needs no `p`; the refinement of [BKS23, Claim 5.9] then recovers `S` (`BKS23/Refine.lean`).
-/

@[expose] public section

namespace BKS23.Rounding

open SoS MvPolynomial Finset

/-- **Averaging, approximately.** As `BKS23.Rounding.exists_round`, without a smallness
hypothesis: some `Q` has `a Q > 0` and `{i | a Q ≤ 2 d Q i}` differs from `S` in at most
`8 (U + 2 |𝒬| (n + 1) ε) / L` elements. -/
theorem exists_round_near {ι : Type*} {n : ℕ} (𝒬 : Finset ι) (S : Finset (Fin n)) (a : ι → ℝ)
    (d : ι → Fin n → ℝ) {L U ε : ℝ} (hL0 : 0 < L) (hε : 0 ≤ ε) (hL : L ≤ ∑ Q ∈ 𝒬, a Q)
    (hU : ∑ Q ∈ 𝒬, ∑ i ∈ Sᶜ, d Q i ≤ U) (hd0 : ∀ Q i, -ε ≤ d Q i)
    (hd1 : ∀ Q i, d Q i ≤ a Q + ε) (hsum : ∀ Q, S.card * a Q - ε ≤ ∑ i, d Q i) :
    ∃ Q ∈ 𝒬, 0 < a Q ∧
      (((univ.filter fun i ↦ a Q ≤ 2 * d Q i) \ S).card +
        (S \ univ.filter fun i ↦ a Q ≤ 2 * d Q i).card : ℝ) ≤
          8 * (U + 2 * 𝒬.card * (n + 1) * ε) / L := by
  classical
  set c := 2 * (U + 𝒬.card * n * ε) / L with hc
  set τ := L / (2 * 𝒬.card) with hτ
  have hn : (Sᶜ.card : ℝ) ≤ n := by
    have := card_le_univ Sᶜ
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hinner : ∀ Q, -(n * ε) ≤ ∑ i ∈ Sᶜ, d Q i := fun Q ↦ by
    calc -(n * ε) ≤ -(Sᶜ.card * ε) := by nlinarith
      _ = ∑ _i ∈ Sᶜ, -ε := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun i _ ↦ hd0 Q i
  have hne : 𝒬.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hL
    linarith
  have hQ0 : (0 : ℝ) < 𝒬.card := by exact_mod_cast hne.card_pos
  have hτ0 : 0 < τ := by positivity
  have hcU : 0 ≤ U + 𝒬.card * n * ε := by
    have : -(𝒬.card * (n * ε)) ≤ ∑ Q ∈ 𝒬, ∑ i ∈ Sᶜ, d Q i := by
      calc -(𝒬.card * (n * ε)) = ∑ _Q ∈ 𝒬, -(n * ε) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun Q _ ↦ hinner Q
    nlinarith
  have hc0 : 0 ≤ c := by positivity
  -- (i) Some `Q` has `a Q ≥ τ` and `∑_{i ∉ S} d Q i ≤ c a Q`.
  have hgood : ∃ Q ∈ 𝒬, τ ≤ a Q ∧ ∑ i ∈ Sᶜ, d Q i ≤ c * a Q := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    set 𝒬₁ := 𝒬.filter (fun Q ↦ τ ≤ a Q)
    set 𝒬₀ := 𝒬.filter (fun Q ↦ ¬ τ ≤ a Q)
    have hsplit : ∀ f : ι → ℝ, ∑ Q ∈ 𝒬, f Q = ∑ Q ∈ 𝒬₁, f Q + ∑ Q ∈ 𝒬₀, f Q :=
      fun f ↦ (sum_filter_add_sum_filter_not 𝒬 _ f).symm
    have h0 : ∑ Q ∈ 𝒬₀, a Q ≤ L / 2 := by
      calc ∑ Q ∈ 𝒬₀, a Q ≤ ∑ _Q ∈ 𝒬₀, τ :=
            sum_le_sum fun Q hQ ↦ (not_le.1 (mem_filter.1 hQ).2).le
        _ = 𝒬₀.card * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 𝒬.card * τ := by
            gcongr
            exact filter_subset _ _
        _ = L / 2 := by rw [hτ]; field_simp
    have h1 : L / 2 ≤ ∑ Q ∈ 𝒬₁, a Q := by
      have := hsplit a
      linarith
    have hne₁ : 𝒬₁.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at h1
      linarith
    have hlt : c * ∑ Q ∈ 𝒬₁, a Q < ∑ Q ∈ 𝒬₁, ∑ i ∈ Sᶜ, d Q i := by
      rw [mul_sum]
      exact sum_lt_sum_of_nonempty hne₁ fun Q hQ ↦
        hcon Q (mem_filter.1 hQ).1 (mem_filter.1 hQ).2
    have hge0 : -(𝒬.card * (n * ε)) ≤ ∑ Q ∈ 𝒬₀, ∑ i ∈ Sᶜ, d Q i := by
      calc -(𝒬.card * (n * ε)) ≤ -(𝒬₀.card * (n * ε)) := by
            have : (𝒬₀.card : ℝ) ≤ 𝒬.card := by exact_mod_cast card_le_card (filter_subset _ _)
            exact neg_le_neg (mul_le_mul_of_nonneg_right this (by positivity))
        _ = ∑ _Q ∈ 𝒬₀, -(n * ε) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun Q _ ↦ hinner Q
    have hcL : c * (L / 2) = U + 𝒬.card * n * ε := by rw [hc]; field_simp
    have hs := hsplit fun Q ↦ ∑ i ∈ Sᶜ, d Q i
    have hm := mul_le_mul_of_nonneg_left h1 hc0
    have hassoc : (𝒬.card : ℝ) * (n * ε) = 𝒬.card * n * ε := by ring
    linarith
  obtain ⟨Q, hQ, hτQ, hbQ⟩ := hgood
  set A := a Q with hA
  have ha : 0 < A := hτ0.trans_le hτQ
  have hkn : (S.card : ℝ) ≤ n := by
    have := card_le_univ S
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  set F := univ.filter fun i ↦ A ≤ 2 * d Q i with hF
  refine ⟨Q, hQ, ha, ?_⟩
  -- (ii) Few vertices outside `S` pass the threshold: each has `d Q i ≥ A / 2`.
  have hout : ((F \ S).card : ℝ) * (A / 2) ≤ c * A + n * ε := by
    have h1 : ∑ i ∈ F \ S, d Q i ≤ ∑ i ∈ Sᶜ, d Q i + n * ε := by
      have hsub : F \ S ⊆ Sᶜ := fun i hi ↦ mem_compl.2 (mem_sdiff.1 hi).2
      have := sum_sdiff hsub (f := d Q)
      have hrest : -((n : ℝ) * ε) ≤ ∑ i ∈ Sᶜ \ (F \ S), d Q i := by
        calc -((n : ℝ) * ε) ≤ -((Sᶜ \ (F \ S)).card * ε) := by
              have : ((Sᶜ \ (F \ S)).card : ℝ) ≤ Sᶜ.card := by
                exact_mod_cast card_le_card sdiff_subset
              nlinarith
          _ = ∑ _i ∈ Sᶜ \ (F \ S), -ε := by rw [sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := sum_le_sum fun i _ ↦ hd0 Q i
      linarith
    have h2 : ((F \ S).card : ℝ) * (A / 2) ≤ ∑ i ∈ F \ S, d Q i := by
      calc ((F \ S).card : ℝ) * (A / 2) = ∑ _i ∈ F \ S, A / 2 := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum fun i hi ↦ by
            have := (mem_filter.1 (mem_sdiff.1 hi).1).2
            linarith
    linarith
  -- (iii) Few vertices of `S` fail the threshold: each leaves `A / 2` of `∑ᵢ d Q i`.
  have hin : ((S \ F).card : ℝ) * (A / 2) ≤ c * A + (n + 1) * ε := by
    have hS : ∑ i ∈ S, d Q i ≤ S.card * (A + ε) - (S \ F).card * (A / 2) := by
      have hsplit := sum_sdiff (sdiff_subset : S \ F ⊆ S) (f := d Q)
      have hS1 : ∑ i ∈ S \ (S \ F), d Q i ≤ (S \ (S \ F)).card * (A + ε) := by
        calc ∑ i ∈ S \ (S \ F), d Q i ≤ ∑ _i ∈ S \ (S \ F), (A + ε) :=
              sum_le_sum fun i _ ↦ hd1 Q i
          _ = _ := by rw [sum_const, nsmul_eq_mul]
      have hS2 : ∑ i ∈ S \ F, d Q i ≤ (S \ F).card * (A / 2) := by
        calc ∑ i ∈ S \ F, d Q i ≤ ∑ _i ∈ S \ F, A / 2 := sum_le_sum fun i hi ↦ by
              have hiF : i ∉ F := (mem_sdiff.1 hi).2
              simp only [hF, mem_filter, mem_univ, true_and, not_le] at hiF
              linarith
          _ = _ := by rw [sum_const, nsmul_eq_mul]
      have hcard : ((S \ (S \ F)).card : ℝ) + (S \ F).card = S.card := by
        have := card_sdiff_add_card_eq_card (sdiff_subset : S \ F ⊆ S)
        exact_mod_cast this
      have hA0 : 0 ≤ A + ε := by linarith
      nlinarith
    have hall := sum_add_sum_compl S (d Q)
    have := hsum Q
    have hkε : (S.card : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right hkn hε
    nlinarith
  -- (iv) Together.
  have hτA : 1 / A ≤ 2 * 𝒬.card / L := by
    rw [div_le_div_iff₀ ha hL0]
    have : L ≤ 2 * 𝒬.card * A := by
      have := hτQ
      rw [hτ, div_le_iff₀ (by positivity)] at this
      linarith
    linarith
  have hsum2 : ((F \ S).card : ℝ) + (S \ F).card ≤ 4 * c + 4 * (n + 1) * ε / A := by
    have e1 : ((F \ S).card : ℝ) ≤ 2 * c + 2 * n * ε / A := by
      rw [show 2 * c + 2 * n * ε / A = (c * A + n * ε) / (A / 2) by field_simp,
        le_div_iff₀ (by positivity)]
      exact hout
    have e2 : ((S \ F).card : ℝ) ≤ 2 * c + 2 * (n + 1) * ε / A := by
      rw [show 2 * c + 2 * (n + 1) * ε / A = (c * A + (n + 1) * ε) / (A / 2) by field_simp,
        le_div_iff₀ (by positivity)]
      exact hin
    have e3 : 2 * (n : ℝ) * ε / A ≤ 2 * (n + 1) * ε / A := by
      gcongr; linarith
    have e4 : 4 * ((n : ℝ) + 1) * ε / A = 2 * (n + 1) * ε / A + 2 * (n + 1) * ε / A := by ring
    linarith
  have hfin : 4 * c + 4 * (n + 1) * ε / A ≤ 8 * (U + 2 * 𝒬.card * (n + 1) * ε) / L := by
    have h1 : 4 * ((n : ℝ) + 1) * ε / A ≤ 4 * (n + 1) * ε * (2 * 𝒬.card / L) := by
      rw [show 4 * ((n : ℝ) + 1) * ε / A = 4 * (n + 1) * ε * (1 / A) by ring]
      exact mul_le_mul_of_nonneg_left hτA (by positivity)
    have h2 : 4 * c = 8 * (U + 𝒬.card * n * ε) / L := by rw [hc]; ring
    have h3 : 8 * (U + 2 * 𝒬.card * (n + 1) * ε) / L =
        8 * (U + 𝒬.card * n * ε) / L + 8 * (𝒬.card * (n + 2) * ε) / L := by ring
    have h4 : 4 * ((n : ℝ) + 1) * ε * (2 * 𝒬.card / L) ≤ 8 * (𝒬.card * (n + 2) * ε) / L := by
      rw [show 4 * ((n : ℝ) + 1) * ε * (2 * 𝒬.card / L) = 8 * (𝒬.card * (n + 1) * ε) / L by ring]
      gcongr
      linarith
    linarith
  linarith

/-- **The rounding to a nearby set.** As `BKS23.Rounding.exists_round_eq`, without the smallness
hypothesis: some `T`-tuple `Q` has `S_Q = {i | Ẽ[w_Q] ≤ 2 Ẽ[w_Q wᵢ]}` differing from `S` in at
most `8 (ω + (η + γ) M Π + 2 k^T (n + 1) err) / (coverage^T - errH)` vertices. -/
theorem exists_round_near_eq {n k ℓ T D : ℕ} {L : List (ℕ × ℕ)} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} (hS : G.IsNClique k S) (hLc : Clique.ListsNonEdges G L)
    (hLs : Clique.OnlyNonEdges G L) {E : PseudoExpectation (Fin n) ℓ} {η γ : ℝ} (hη : 0 < η)
    (hγ : 0 < γ) (hγη : γ ≤ η)
    (hE : E.ApproxSatisfies (Clique.problem n k ℓ L).system (η + γ) 0)
    (hopt : ∀ E' : PseudoExpectation (Fin n) ℓ,
      E'.ApproxSatisfies (Clique.problem n k ℓ L).system η 0 →
        (Clique.problem n k ℓ L).objective E ≤ (Clique.problem n k ℓ L).objective E' + γ)
    (hℓ : 2 * T + 2 ≤ ℓ) {ω M : ℝ} (hD : D ≤ ℓ)
    (hcert : DerivesN (Clique.realSystem n k ℓ L) D M
      (C ω - (∑ u ∈ S, X u) ^ T * ∑ v ∈ Sᶜ, X v))
    (hε1 : err n k ℓ L η γ T ≤ 1) (hεk : err n k ℓ L η γ T ≤ k)
    (hcov : 0 < coverage n k η γ (err n k ℓ L η γ T))
    (hLpos : 0 < coverage n k η γ (err n k ℓ L η γ T) ^ T - errH n k ℓ L η γ T) :
    ∃ Q : Fin T → Fin n,
      (((univ.filter fun i ↦ E (wQ Q) ≤ 2 * E (wQ Q * X i)) \ S).card +
        (S \ univ.filter fun i ↦ E (wQ Q) ≤ 2 * E (wQ Q * X i)).card : ℝ) ≤
        8 * (ω + (η + γ) * M * constraintNorm n k ℓ L +
          2 * (k : ℝ) ^ T * (n + 1) * err n k ℓ L η γ T) /
          (coverage n k η γ (err n k ℓ L η γ T) ^ T - errH n k ℓ L η γ T) := by
  classical
  set A := Clique.realSystem n k ℓ L
  set PN := constraintNorm n k ℓ L with hPN
  set ε := err n k ℓ L η γ T with hεdef
  have hPN0 : 0 ≤ PN := constraintNorm_nonneg n k ℓ L
  have hηγ : 0 ≤ η + γ := by linarith
  have hε0 : 0 ≤ ε := by rw [hεdef, err]; positivity
  have hA : E.ApproxSatisfies A (η + γ) 0 := hE.map_toReal
  have hAx : Biclique.Axioms A S G.Adj k := Clique.axioms hLc fun _ _ _ _ h ↦ h
  have hB := hAx.bool
  have hcardEq : DerivesEq A 1 1 (∑ i, X i - C (k : ℝ)) :=
    hAx.card.derivesEq ((totalDegree_sub _ _).trans
      (max_le (totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X])
        (by rw [totalDegree_C]; omega))) le_rfl
  -- Approximate soundness, with the error `ε`.
  have hsound : ∀ {d : ℕ} {M' : ℝ} {g : MvPolynomial (Fin n) ℝ}, d ≤ ℓ →
      M' ≤ 2 * 10 ^ (T + 1) → DerivesN A d M' g → -ε ≤ E g := by
    intro d M' g hd hM' h
    refine le_trans ?_ (h.approx_ge hηγ hA hd)
    rw [neg_le_neg_iff, hεdef, err, ← hPN]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM' hηγ) hPN0
  have hlit : ∀ l : List (Bool × Fin n), l.length ≤ T + 1 → -ε ≤ E (litProd l) := by
    intro l hl
    refine hsound (by omega) ?_ (hB.litProd_nonneg l)
    have : (10 : ℝ) ^ l.length ≤ 10 ^ (T + 1) := pow_le_pow_right₀ (by norm_num) hl
    linarith
  -- The approximate constraints on `Ẽ[w_Q wᵢ]`.
  have hd0 : ∀ (Q : Fin T → Fin n) i, -ε ≤ E (wQ Q * X i) := by
    intro Q i
    have := hlit ((true, i) :: List.ofFn fun j ↦ (true, Q j)) (by simp)
    simp only [litProd_cons, litProd_ofFn, lit, ↓reduceIte] at this
    rwa [mul_comm] at this
  have hd1 : ∀ (Q : Fin T → Fin n) i, E (wQ Q * X i) ≤ E (wQ Q) + ε := by
    intro Q i
    have := hlit ((false, i) :: List.ofFn fun j ↦ (true, Q j)) (by simp)
    simp only [litProd_cons, litProd_ofFn, lit, Bool.false_eq_true, ↓reduceIte, sub_mul,
      one_mul, PseudoExpectation.map_sub] at this
    rw [mul_comm] at this
    linarith
  have hsum : ∀ Q : Fin T → Fin n, S.card * E (wQ Q) - ε ≤ ∑ i, E (wQ Q * X i) := by
    intro Q
    have hw : (wQ Q).totalDegree ≤ T := (totalDegree_finsetProd _ _).trans (by simp)
    have hwn : coeffNorm1 (wQ Q) ≤ 1 := coeffNorm1_prod_X_le' Q
    have := hsound (by omega) (by
      have : (coeffNorm1 (wQ Q) + 1) ^ 2 * 1 ≤ 4 := by
        nlinarith [coeffNorm1_nonneg (wQ Q)]
      have : (4 : ℝ) ≤ 2 * 10 ^ (T + 1) := by
        have : (10 : ℝ) ≤ 10 ^ (T + 1) := le_self_pow₀ (by norm_num) (by omega)
        linarith
      linarith) ((hcardEq.mul (wQ Q)).1)
    rw [hS.card_eq]
    rw [mul_sub, mul_sum, PseudoExpectation.map_sub, PseudoExpectation.map_sum,
      mul_comm (wQ Q) (C _), PseudoExpectation.map_C_mul] at this
    linarith
  -- Maximal coverage: `Ẽ[s] ≥ coverage`.
  have hm0 : ∀ i, -ε ≤ E (X i) := fun i ↦ by
    have := hlit [(true, i)] (by simp)
    simpa [litProd, lit] using this
  have hm1 : ∀ i, E (X i) ≤ 1 + ε := fun i ↦ by
    have := hlit [(false, i)] (by simp)
    simp [litProd, lit] at this
    linarith
  have hsumm : (k : ℝ) - ε ≤ ∑ i, E (X i) := by
    have := hsound (by omega) (by
      have : (10 : ℝ) ≤ 10 ^ (T + 1) := le_self_pow₀ (by norm_num) (by omega)
      linarith) hcardEq.1
    rw [PseudoExpectation.map_sub, PseudoExpectation.map_sum, PseudoExpectation.map_C] at this
    linarith
  set t := γ / (η + γ) with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by rw [htdef, div_le_iff₀ (by linarith)]; linarith
  have hmixη : (1 - t) * (η + γ) + t * 0 = η := by rw [htdef]; field_simp; ring
  set y := Clique.planted S
  have hy : ∀ f ∈ (Clique.problem n k ℓ L).system, 0 ≤ eval y (toReal f) := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
    exact (Clique.eval_planted hS hLs hr).ge
  set E' := PseudoExpectation.mix E (SoS.Correct.ofPoint ℓ y) t ht0.le (by linarith)
  have hE' : E'.ApproxSatisfies (Clique.problem n k ℓ L).system η 0 := by
    have := hE.mix (SoS.Correct.ofPoint_approxSatisfies (ℓ := ℓ) hy le_rfl) ht0.le
      (by linarith : t ≤ 1)
    rwa [hmixη] at this
  have hobj := hopt E' hE'
  rw [Clique.objective_eq, Clique.objective_eq] at hobj
  have hE'X : ∀ i, E' (X i) = (1 - t) * E (X i) + t * y i := fun i ↦ by
    rw [PseudoExpectation.mix_apply, SoS.Correct.ofPoint_apply, eval_X]
  simp_rw [hE'X] at hobj
  have hu : ∀ i, y i = 0 ∨ y i = 1 := fun i ↦ by
    simp only [y, Clique.planted]
    split_ifs <;> simp
  have hcov' := coverage_bound (fun i ↦ E (X i)) y hu
    (by rw [Clique.sum_planted, hS.card_eq]) ht0 ht1 hγ.le hobj
  have hsS : E (∑ u ∈ S, X u) = ∑ i, E (X i) * y i := by
    rw [PseudoExpectation.map_sum]
    simp only [y, Clique.planted, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter]
  have ha4 : ∑ i, E (X i) ^ 2 ≤ 4 * n := by
    calc ∑ i, E (X i) ^ 2 ≤ ∑ _i : Fin n, (4 : ℝ) := sum_le_sum fun i _ ↦ by
          nlinarith [hm0 i, hm1 i]
      _ = 4 * n := by simp; ring
  have haLow : ((k : ℝ) - ε) ^ 2 / n ≤ ∑ i, E (X i) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i : Fin n ↦ E (X i))
    simp only [card_univ, Fintype.card_fin] at hcs
    have hk0 : 0 ≤ (k : ℝ) - ε := by linarith
    nlinarith [pow_le_pow_left₀ hk0 hsumm 2]
  have hcovE : coverage n k η γ ε ≤ E (∑ u ∈ S, X u) := by
    rw [hsS]
    have hγt : γ / t = η + γ := by rw [htdef]; field_simp
    rw [hγt] at hcov'
    simp only [coverage]
    have : t * (∑ i, E (X i) ^ 2 + k) ≤ t * (4 * n + k) := by gcongr
    linarith
  -- Hölder: `Ẽ[s^T] ≥ Ẽ[s]^T - errH ≥ coverage^T - errH`.
  set s : MvPolynomial (Fin n) ℝ := ∑ u ∈ S, X u
  have hc0 : 0 ≤ E s := hcov.le.trans hcovE
  have hck : E s ≤ 2 * k := by
    simp only [s, PseudoExpectation.map_sum]
    calc ∑ u ∈ S, E (X u) ≤ ∑ _u ∈ S, (2 : ℝ) := sum_le_sum fun u _ ↦ by linarith [hm1 u]
      _ = 2 * k := by rw [sum_const, hS.card_eq, nsmul_eq_mul]; ring
  have hL : coverage n k η γ ε ^ T - errH n k ℓ L η γ T ≤ E (s ^ T) := by
    have hH : E s ^ T - errH n k ℓ L η γ T ≤ E (s ^ T) :=
      holder hB hS.card_eq hηγ hA (by omega) hc0 hck
    have hcovT : coverage n k η γ ε ^ T ≤ E s ^ T := pow_le_pow_left₀ hcov.le hcovE T
    linarith
  -- The certificate: `Ẽ[s^T |y|] ≤ ω + (η + γ) M Π`.
  have hU : E (s ^ T * ∑ v ∈ Sᶜ, X v) ≤ ω + (η + γ) * M * PN := by
    have := hcert.approx_ge hηγ hA hD
    rw [PseudoExpectation.map_sub, PseudoExpectation.map_C] at this
    have hPN' : ∏ i, (1 + coeffNorm (A.get i)) = PN := rfl
    rw [hPN'] at this
    linarith
  -- The sums over `Q ∈ S^T`.
  have hexp : s ^ T = ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, wQ Q := pow_sum_X_eq S T
  have hsumA : E (s ^ T) = ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, E (wQ Q) := by
    rw [hexp, PseudoExpectation.map_sum]
  have hsumU : E (s ^ T * ∑ v ∈ Sᶜ, X v) =
      ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, ∑ i ∈ Sᶜ, E (wQ Q * X i) := by
    rw [hexp, sum_mul, PseudoExpectation.map_sum]
    exact sum_congr rfl fun Q _ ↦ by rw [mul_sum, PseudoExpectation.map_sum]
  have hcardQ : ((Fintype.piFinset fun _ : Fin T ↦ S).card : ℝ) = (k : ℝ) ^ T := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hS.card_eq]
    push_cast
    rfl
  obtain ⟨Q, -, -, hQ⟩ := exists_round_near (Fintype.piFinset fun _ : Fin T ↦ S) S
    (fun Q ↦ E (wQ Q)) (fun Q i ↦ E (wQ Q * X i)) hLpos hε0 (hsumA ▸ hL)
    (hsumU ▸ hU) hd0 hd1 hsum
  rw [hcardQ] at hQ
  exact ⟨Q, hQ⟩

end BKS23.Rounding
