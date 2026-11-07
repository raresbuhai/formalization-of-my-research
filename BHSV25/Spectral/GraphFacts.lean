module

public import BHSV25.Spectral.Eigen

/-!
# The normalized adjacency matrix

The proofs behind the graph part of the spectral toolkit (`BHSV25/Spectral/Basic.lean`), about
the normalized adjacency matrix `Ã = D^(-1/2) A D^(-1/2)` of a graph (`BHSV25.Graph.normAdj`).

* `Ã` has nonnegative entries, and `|xᵀ Ã x| ≤ ‖x‖²`, since
  `|x_u x_v| / √(d_u d_v) ≤ (x_u² / d_u + x_v² / d_v) / 2` on every edge; so its eigenvalues lie
  in `[-1, 1]`.
* For a `d`-regular graph, `Ã = A / d` and `Ã 𝟙 = 𝟙`.
* If at most one eigenvalue of a regular graph is larger than `L ∈ [0, 1)`, that eigenvalue is `1`
  and its eigenvector is `𝟙 / √n`, so `xᵀ Ã x ≤ (∑ x)² / n + L (‖x‖² - (∑ x)² / n)`.
-/

@[expose] public section

namespace BHSV25

namespace Spectral

namespace Impl

open Matrix

variable (G : Graph)

theorem normAdj_nonneg (u v : Fin G.1) : 0 ≤ G.normAdj u v := by
  unfold Graph.normAdj
  split_ifs
  · positivity
  · exact le_rfl

open Classical in
theorem sum_adj_ite (u : Fin G.1) (c : ℝ) :
    ∑ v, (if G.2.Adj u v then c else 0) = G.2.degree u * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

open Classical in
/-- On an edge, `|x_u x_v| / √(d_u d_v) ≤ (x_u² / d_u + x_v² / d_v) / 2`. -/
theorem normAdj_mul_abs_le (x : Fin G.1 → ℝ) (u v : Fin G.1) :
    G.normAdj u v * (|x u| * |x v|) ≤
      (if G.2.Adj u v then x u ^ 2 / G.2.degree u else 0) / 2 +
        (if G.2.Adj u v then x v ^ 2 / G.2.degree v else 0) / 2 := by
  unfold Graph.normAdj
  split_ifs with h
  · have hu : (0 : ℝ) < G.2.degree u := by
      exact_mod_cast (G.2.degree_pos_iff_exists_adj u).2 ⟨v, h⟩
    have hv : (0 : ℝ) < G.2.degree v := by
      exact_mod_cast (G.2.degree_pos_iff_exists_adj v).2 ⟨u, h.symm⟩
    set a := |x u| / Real.sqrt (G.2.degree u)
    set b := |x v| / Real.sqrt (G.2.degree v)
    have hsu := Real.sq_sqrt hu.le
    have hsv := Real.sq_sqrt hv.le
    have hsu0 := Real.sqrt_pos.2 hu
    have hsv0 := Real.sqrt_pos.2 hv
    have hab : 1 / Real.sqrt (G.2.degree u * G.2.degree v) * (|x u| * |x v|) = a * b := by
      rw [Real.sqrt_mul hu.le]
      simp only [a, b]
      field_simp
    have ha : a ^ 2 = x u ^ 2 / G.2.degree u := by
      simp only [a]
      rw [div_pow, sq_abs, hsu]
    have hb : b ^ 2 = x v ^ 2 / G.2.degree v := by
      simp only [b]
      rw [div_pow, sq_abs, hsv]
    rw [hab, ← ha, ← hb]
    linarith only [two_mul_le_add_sq a b]
  · simp

open Classical in
theorem sum_sum_ite_div_le (x : Fin G.1 → ℝ) :
    ∑ u, ∑ v, (if G.2.Adj u v then x u ^ 2 / G.2.degree u else 0) ≤ x ⬝ᵥ x := by
  rw [dotProduct]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  rw [sum_adj_ite]
  rcases eq_or_ne (G.2.degree u : ℝ) 0 with h0 | h0
  · rw [h0, zero_mul]
    exact mul_self_nonneg _
  · rw [mul_div_cancel₀ _ h0, sq]

theorem abs_quad_normAdj_le (x : Fin G.1 → ℝ) : |x ⬝ᵥ (G.normAdj *ᵥ x)| ≤ x ⬝ᵥ x := by
  classical
  have hexp : x ⬝ᵥ (G.normAdj *ᵥ x) = ∑ u, ∑ v, x u * (G.normAdj u v * x v) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ u, |∑ v, x u * (G.normAdj u v * x v)| ≤
      ∑ v, ((if G.2.Adj u v then x u ^ 2 / G.2.degree u else 0) / 2 +
        (if G.2.Adj u v then x v ^ 2 / G.2.degree v else 0) / 2) := by
    intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
    refine le_trans (le_of_eq ?_) (normAdj_mul_abs_le G x u v)
    rw [abs_mul, abs_mul, abs_of_nonneg (normAdj_nonneg G u v)]
    ring
  refine (Finset.sum_le_sum fun u _ ↦ h1 u).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  have h2 : ∑ u, ∑ v, (if G.2.Adj u v then x v ^ 2 / G.2.degree v else 0) =
      ∑ u, ∑ v, (if G.2.Adj u v then x u ^ 2 / G.2.degree u else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
    simp only [G.2.adj_comm]
  rw [h2]
  have h3 := sum_sum_ite_div_le G x
  linarith

theorem abs_eig_le_one (i : Fin G.1) : |G.eig i| ≤ 1 := by
  set hA := G.normAdj_isHermitian
  set b : Fin G.1 → ℝ := ⇑(hA.eigenvectorBasis i)
  have hbb : b ⬝ᵥ b = 1 := by
    rw [← sum_coeff_sq hA, Finset.sum_eq_single i]
    · simp [b, coeff_eigenvector]
    · intro j _ hj
      simp [b, coeff_eigenvector, hj]
    · simp
  have hq : b ⬝ᵥ (G.normAdj *ᵥ b) = G.eig i := by
    rw [quad_eq hA, Finset.sum_eq_single i]
    · simp [b, coeff_eigenvector]
      rfl
    · intro j _ hj
      simp [b, coeff_eigenvector, hj]
    · simp
  have := abs_quad_normAdj_le G b
  rwa [hq, hbb] at this

open Classical in
theorem normAdj_of_isRegularOfDegree {d : ℕ} (h : G.2.IsRegularOfDegree d) (u v : Fin G.1) :
    G.normAdj u v = if G.2.Adj u v then (d : ℝ)⁻¹ else 0 := by
  unfold Graph.normAdj
  split_ifs
  · rw [h u, h v, Real.sqrt_mul_self (Nat.cast_nonneg d), one_div]
  · rfl

open Classical in
theorem normAdj_mulVec_one {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) :
    G.normAdj *ᵥ (fun _ ↦ (1 : ℝ)) = fun _ ↦ 1 := by
  funext u
  simp only [mulVec, dotProduct, mul_one, normAdj_of_isRegularOfDegree G h]
  rw [sum_adj_ite, h u]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hd)

open Classical in
/-- In a regular graph with at most one eigenvalue above `L ∈ [0, 1)`, the quadratic form of the
normalized adjacency matrix is at most `L` on the vectors orthogonal to the all-ones vector. -/
theorem quad_le_of_numEigGT_le_one {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) {L : ℝ}
    (_hL0 : 0 ≤ L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1) (x : Fin G.1 → ℝ) :
    x ⬝ᵥ (G.normAdj *ᵥ x) ≤
      (∑ v, x v) ^ 2 / G.1 + L * (x ⬝ᵥ x - (∑ v, x v) ^ 2 / G.1) := by
  set hA := G.normAdj_isHermitian
  set one : Fin G.1 → ℝ := fun _ ↦ 1 with hone
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · have hx : x = 0 := funext fun i ↦ absurd i.2 (by omega)
    simp [hx]
  have h1 : G.normAdj *ᵥ one = one := normAdj_mulVec_one G h hd
  have hc1 : ∀ i, hA.eigenvalues i ≠ 1 → coeff hA i one = 0 := by
    intro i hi
    have h2 := coeff_mulVec hA i one
    rw [h1] at h2
    have h3 : (1 - hA.eigenvalues i) * coeff hA i one = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h' | h'
    · exact absurd (by linarith) hi
    · exact h'
  have hone_ne : one ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [one] at this
  obtain ⟨i₀, hi₀⟩ := exists_coeff_ne_zero hA hone_ne
  have hμ₀ : hA.eigenvalues i₀ = 1 := by
    by_contra hne
    exact hi₀ (hc1 i₀ hne)
  have huniq : ∀ i, L < hA.eigenvalues i → i = i₀ := by
    intro i hi
    have hmem : i ∈ Finset.univ.filter fun i ↦ L < G.eig i :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    have hmem0 : i₀ ∈ Finset.univ.filter fun i ↦ L < G.eig i := by
      have : L < hA.eigenvalues i₀ := by rw [hμ₀]; exact hL1
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    exact Finset.card_le_one.1 hexp i hmem i₀ hmem0
  have hc1' : ∀ i, i ≠ i₀ → coeff hA i one = 0 := by
    intro i hi
    refine hc1 i fun hμ ↦ hi (huniq i ?_)
    rw [hμ]
    exact hL1
  set c := coeff hA i₀ one
  set a := coeff hA i₀ x
  have hcsq : c ^ 2 = G.1 := by
    have h2 := sum_coeff_sq hA one
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by rw [hc1' i hi]; ring) (by simp)] at h2
    rw [h2]
    simp [one, dotProduct]
  have hs : ∑ v, x v = c * a := by
    have h2 := dotProduct_eq_sum_coeff hA one x
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by rw [hc1' i hi]; ring) (by simp)] at h2
    rw [← h2]
    simp [one, dotProduct]
  have hsn : (∑ v, x v) ^ 2 / G.1 = a ^ 2 := by
    have hc0 : c ^ 2 ≠ 0 := pow_ne_zero 2 hi₀
    rw [hs, ← hcsq, mul_pow]
    field_simp
  have hterm : ∀ i, hA.eigenvalues i * coeff hA i x ^ 2 ≤
      L * coeff hA i x ^ 2 + (if i = i₀ then (1 - L) * coeff hA i x ^ 2 else 0) := by
    intro i
    split_ifs with hi
    · rw [hi, hμ₀]
      linarith
    · have : hA.eigenvalues i ≤ L := by
        by_contra hlt
        exact hi (huniq i (lt_of_not_ge hlt))
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (coeff hA i x))
      linarith
  rw [quad_eq hA, hsn]
  refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
    sum_coeff_sq hA]
  ring

end Impl

end Spectral

end BHSV25
