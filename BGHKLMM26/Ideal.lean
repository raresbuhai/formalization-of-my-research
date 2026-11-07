module

public import BGHKLMM26.Gain

/-!
# The rounding with ideal vectors

[BGHKLMM26, Lemmas 3.4 and 3.5]. For unit vectors `vᵢ` satisfying the triangle inequalities up
to `θ ≤ 1/20`, let `T` be the constraints in the window `1/2 < ρ < 4/5` (`BGHKLMM26.window`).

* Hyperplane rounding has expected value at least `α_GW SDP + κ SDP_N`, where `SDP_N` is the SDP
  value outside the window (`BGHKLMM26.round0_ge`).
* The shifted rounding has expected value at least `α_GW SDP_T + λ W_T / (250 d √L)`
  (`BGHKLMM26.roundL_ge`), by Theorem 3.2 (`BGHKLMM26.gain`), whose hypotheses hold in the window:
  out-edges of a vertex go to distinct neighbours, so the triangle inequalities give
  `⟨u_{i→j}, u_{i→k}⟩ ≥ -1/2` (`BGHKLMM26.outU_inner_ge`).
-/

@[expose] public section

namespace BGHKLMM26

open MeasureTheory ProbabilityTheory Real Gaussian Set GW
open scoped RealInnerProductSpace

/-! ### Out-edges -/

section OutEdges

theorem outEdges_cons (c : Constraint) (T : List Constraint) (i : ℕ) :
    outEdges (c :: T) i = (if c.1.1 = i then [(c.1.2, c.2.1, c.2.2)]
      else if c.1.2 = i then [(c.1.1, c.2.1, c.2.2)] else []) ++ outEdges T i := by
  simp only [outEdges, List.filterMap_cons]
  split_ifs <;> rfl

theorem length_outEdges (T : List Constraint) (i : ℕ) :
    (outEdges T i).length = (T.filter fun c ↦ c.1.1 = i ∨ c.1.2 = i).length := by
  induction T with
  | nil => rfl
  | cons c T ih =>
    rw [outEdges_cons, List.length_append, ih, List.filter_cons]
    by_cases h1 : c.1.1 = i <;> by_cases h2 : c.1.2 = i <;> simp [h1, h2] <;> omega

/-- The out-edges of a vertex in a sublist of the constraints are at most its degree. -/
theorem length_outEdges_le {I : Instance} {T : List Constraint} (hT : T.Sublist I.2) (i : ℕ) :
    (outEdges T i).length ≤ degree I i := by
  rw [length_outEdges, degree]
  exact (hT.filter _).length_le

/-- On distinct pairs, the out-edges of a vertex go to distinct neighbours. -/
theorem nodup_outEdges {T : List Constraint} (hT : ∀ c ∈ T, c.1.1 < c.1.2)
    (hnd : (T.map Prod.fst).Nodup) (i : ℕ) : ((outEdges T i).map Prod.fst).Nodup := by
  induction T with
  | nil => simp [outEdges]
  | cons c T ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih' := ih (fun c' h ↦ hT c' (List.mem_cons_of_mem _ h)) hnd.2
    have hc := hT c List.mem_cons_self
    have hnot : ∀ j, (c.1.1 = i ∧ c.1.2 = j ∨ c.1.2 = i ∧ c.1.1 = j) →
        j ∉ (outEdges T i).map Prod.fst := by
      intro j hj hmem
      obtain ⟨e, he, hej⟩ := List.mem_map.1 hmem
      obtain ⟨c', hc', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := mem_outEdges he
      all_goals
        have hc'' := hT c' (List.mem_cons_of_mem _ hc')
        rw [h2] at hej
        simp only at hej
        have : c'.1 = c.1 := by
          rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ <;> ext <;> omega
        exact hnd.1 (this ▸ List.mem_map_of_mem hc')
    rw [outEdges_cons, List.map_append]
    by_cases h1 : c.1.1 = i
    · simp only [h1, ite_true, List.map_cons, List.map_nil, List.singleton_append,
        List.nodup_cons]
      exact ⟨hnot _ (Or.inl ⟨h1, rfl⟩), ih'⟩
    · by_cases h2 : c.1.2 = i
      · simp only [h1, h2, ite_true, ite_false, List.map_cons, List.map_nil,
          List.singleton_append, List.nodup_cons]
        exact ⟨hnot _ (Or.inr ⟨h2, rfl⟩), ih'⟩
      · simpa [h1, h2] using ih'

end OutEdges

/-! ### The window and the triangle inequalities -/

section Window

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E)

/-- The window [BGHKLMM26, Algorithm 1, line 3]: `1/2 < ρ < 4/5`, around `-ρ* ≈ 0.689`. -/
def window (c : Constraint) : Prop :=
  1 / 2 < rho v c.1.1 c.1.2 c.2.1 ∧ rho v c.1.1 c.1.2 c.2.1 < 4 / 5

/-- The triangle inequalities of the SDP [BGHKLMM26, Section 3], in the form used here and up to
`θ`: `bⱼ bₖ ⟨vⱼ, vₖ⟩ ≥ bⱼ ⟨vᵢ, vⱼ⟩ + bₖ ⟨vᵢ, vₖ⟩ - 1 - θ` for distinct `i, j, k < n`. -/
def Triangle (n : ℕ) (θ : ℝ) : Prop :=
  ∀ i j k : ℕ, i < n → j < n → k < n → i ≠ j → i ≠ k → j ≠ k → ∀ b b' : Bool,
    bsign b * ⟪v i, v j⟫ + bsign b' * ⟪v i, v k⟫ - 1 - θ ≤ bsign b * bsign b' * ⟪v j, v k⟫

theorem inner_dirVec {i j j' : ℕ} (b b' : Bool) (hi : ‖v i‖ = 1) :
    ⟪dirVec v i j b, dirVec v i j' b'⟫ = (√(1 - rho v i j b ^ 2))⁻¹ *
      (√(1 - rho v i j' b' ^ 2))⁻¹ *
        (bsign b * bsign b' * ⟪v j, v j'⟫ - rho v i j b * rho v i j' b') := by
  have hii : ⟪v i, v i⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hi, one_pow]
  simp only [dirVec, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    conj_trivial, hii, rho, real_inner_comm (v i) (v j)]
  ring

/-- **The vectors `h` of a vertex are not too anti-correlated** [BGHKLMM26, proof of Lemma 3.5]:
in the window, with the triangle inequalities up to `θ ≤ 1/20`,
`⟨u_{i→j}, u_{i→k}⟩ ≥ -1/2` for distinct neighbours `j ≠ k`. -/
theorem dirVec_inner_ge {n : ℕ} {θ : ℝ} (hθ : θ ≤ 1 / 20) (htri : Triangle v n θ)
    (hv : ∀ i < n, ‖v i‖ = 1) {i j j' : ℕ} (hi : i < n) (hj : j < n) (hj' : j' < n)
    (hij : i ≠ j) (hij' : i ≠ j') (hjj' : j ≠ j') {b b' : Bool}
    (hw : 1 / 2 < rho v i j b ∧ rho v i j b < 4 / 5)
    (hw' : 1 / 2 < rho v i j' b' ∧ rho v i j' b' < 4 / 5) :
    -(1 / 2) ≤ ⟪dirVec v i j b, dirVec v i j' b'⟫ := by
  rw [inner_dirVec v b b' (hv i hi)]
  set ρ := rho v i j b with hρdef
  set ρ' := rho v i j' b' with hρ'def
  have htr := htri i j j' hi hj hj' hij hij' hjj' b b'
  rw [show bsign b * ⟪v i, v j⟫ = ρ from rfl, show bsign b' * ⟪v i, v j'⟫ = ρ' from rfl] at htr
  set σ := √(1 - ρ ^ 2) with hσdef
  set σ' := √(1 - ρ' ^ 2) with hσ'def
  have hσ : 3 / 5 ≤ σ := by
    rw [hσdef, show (3 / 5 : ℝ) = √((3 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hσ' : 3 / 5 ≤ σ' := by
    rw [hσ'def, show (3 / 5 : ℝ) = √((3 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hσ2 : σ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hσ'2 : σ' ^ 2 = 1 - ρ' ^ 2 := Real.sq_sqrt (by nlinarith)
  -- `(1 - ρ)(1 - ρ') ≤ σ σ' / 3`, by squaring.
  have hprod : 3 * ((1 - ρ) * (1 - ρ')) ≤ σ * σ' := by
    have h0 : 0 ≤ 3 * ((1 - ρ) * (1 - ρ')) := by nlinarith
    rw [← Real.sqrt_sq h0, ← Real.sqrt_sq (by positivity : 0 ≤ σ * σ')]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow σ σ', hσ2, hσ'2]
    have h1 : 3 * (1 - ρ) ≤ 1 + ρ := by linarith
    have h2 : 3 * (1 - ρ') ≤ 1 + ρ' := by linarith
    have h3 : 0 ≤ 1 - ρ := by linarith
    have h4 : 0 ≤ 1 - ρ' := by linarith
    have : (3 * (1 - ρ)) * (3 * (1 - ρ')) ≤ (1 + ρ) * (1 + ρ') :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    have : (3 * ((1 - ρ) * (1 - ρ'))) ^ 2 ≤ ((1 - ρ) * (1 - ρ')) * ((1 + ρ) * (1 + ρ')) := by
      have h5 : 0 ≤ (1 - ρ) * (1 - ρ') := mul_nonneg h3 h4
      nlinarith
    nlinarith
  have hss : 9 / 25 ≤ σ * σ' := by nlinarith
  have hpos : 0 < σ * σ' := by linarith
  rw [← mul_inv, ← div_eq_inv_mul, le_div_iff₀ hpos]
  nlinarith

open Classical in
/-- The constraints in the window. -/
noncomputable def windowSet (I : Instance) : List Constraint :=
  I.2.filter fun c ↦ decide (window v c)

theorem windowSet_sublist (I : Instance) : (windowSet v I).Sublist I.2 := List.filter_sublist

theorem window_of_mem {I : Instance} {c : Constraint} (hc : c ∈ windowSet v I) : window v c := by
  classical
  simpa [windowSet] using (List.mem_filter.1 hc).2

theorem windowSet_valid {I : Instance} (hI : Valid I) :
    ∀ c ∈ windowSet v I, c.1.1 < c.1.2 ∧ c.1.2 < I.1 ∧ 0 ≤ c.2.2 :=
  fun c hc ↦ hI.1 c ((windowSet_sublist v I).subset hc)

theorem windowSet_nodup {I : Instance} (hI : Valid I) : ((windowSet v I).map Prod.fst).Nodup :=
  hI.2.sublist ((windowSet_sublist v I).map _)

/-- An out-edge `(j, b, w)` of `i` in the window: `i ≠ j` are vertices and `ρᵢⱼ` is in the
window. -/
theorem outEdge_window {I : Instance} (hI : Valid I) {i : ℕ} {e : ℕ × Bool × ℚ}
    (he : e ∈ outEdges (windowSet v I) i) :
    i < I.1 ∧ e.1 < I.1 ∧ i ≠ e.1 ∧ 1 / 2 < rho v i e.1 e.2.1 ∧ rho v i e.1 e.2.1 < 4 / 5 := by
  obtain ⟨c, hc, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := mem_outEdges he
  · obtain ⟨hij, hjn, -⟩ := windowSet_valid v hI c hc
    have hw := window_of_mem v hc
    rw [h2, ← h1]
    exact ⟨hij.trans hjn, hjn, hij.ne, hw⟩
  · obtain ⟨hij, hjn, -⟩ := windowSet_valid v hI c hc
    have hw := window_of_mem v hc
    rw [h2, ← h1, ← rho_comm]
    exact ⟨hjn, hij.trans hjn, hij.ne', hw⟩

/-- **The hypothesis `⟨hᵢⱼ, hᵢₖ⟩ ≥ -β` of Theorem 3.2** holds in the window with `β = 1/2`
[BGHKLMM26, proof of Lemma 3.5]. -/
theorem outU_inner_ge {I : Instance} (hI : Valid I) {θ : ℝ} (hθ : θ ≤ 1 / 20)
    (htri : Triangle v I.1 θ) (hv : ∀ i < I.1, ‖v i‖ = 1) (i : ℕ)
    (k k' : Fin (outEdges (windowSet v I) i).length) (hkk' : k ≠ k') :
    -(1 / 2) ≤ ⟪outU v (windowSet v I) i k, outU v (windowSet v I) i k'⟫ := by
  obtain ⟨hi, hj, hij, hw⟩ :=
    outEdge_window v hI (List.getElem_mem (l := outEdges (windowSet v I) i) k.2)
  obtain ⟨-, hj', hij', hw'⟩ :=
    outEdge_window v hI (List.getElem_mem (l := outEdges (windowSet v I) i) k'.2)
  have hnd := nodup_outEdges (fun c hc ↦ (windowSet_valid v hI c hc).1)
    (windowSet_nodup v hI) i
  have hjj' : (outEdges (windowSet v I) i)[k.1].1 ≠ (outEdges (windowSet v I) i)[k'.1].1 := by
    intro h
    have := (hnd.getElem_inj_iff (i := k.1) (j := k'.1) (hi := by simp)
      (hj := by simp)).1 (by simpa using h)
    exact hkk' (Fin.ext this)
  exact dirVec_inner_ge v hθ htri hv hi hj hj' hij hij' hjj' hw hw'

end Window

/-! ### The two roundings -/

section Values

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (v : ℕ → E)

/-- The SDP contribution `w (1 + ρ) / 2` of a constraint. -/
noncomputable def sdpTerm (c : Constraint) : ℝ := (c.2.2 : ℝ) * ((1 + rho v c.1.1 c.1.2 c.2.1) / 2)

/-- The SDP value `∑ w (1 + ρ) / 2` of the vectors. -/
noncomputable def sdp (I : Instance) : ℝ := (I.2.map (sdpTerm v)).sum

open Classical in
/-- The SDP value `SDP_N` outside the window. -/
noncomputable def sdpOut (I : Instance) : ℝ :=
  (I.2.map fun c ↦ if window v c then 0 else sdpTerm v c).sum

/-- The SDP value `SDP_T` in the window. -/
noncomputable def sdpIn (I : Instance) : ℝ := ((windowSet v I).map (sdpTerm v)).sum

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sdp_eq_add (I : Instance) : sdp v I = sdpIn v I + sdpOut v I := by
  classical
  unfold sdp sdpIn sdpOut windowSet
  induction I.2 with
  | nil => simp
  | cons c l ih =>
    by_cases h : window v c
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, decide_true, ite_true, ih]
      ring
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, decide_false, ite_false,
        Bool.false_eq_true, ih]
      ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_rho_le {i j : ℕ} (b : Bool) (hi : ‖v i‖ = 1) (hj : ‖v j‖ = 1) :
    |rho v i j b| ≤ 1 := by
  rw [rho, abs_mul]
  have : |bsign b| = 1 := by rcases bsign_cases b with h | h <;> rw [h] <;> norm_num
  rw [this, one_mul]
  exact abs_inner_le_one hi hj

/-- **Hyperplane rounding, constraint by constraint**: on constraints between unit vectors, its
expected value is `∑ w (1/2 + arcsin ρ / π)`. -/
theorem integral_satWeight_round0 (n : ℕ) (L : List Constraint)
    (hv : ∀ c ∈ L, ‖v c.1.1‖ = 1 ∧ ‖v c.1.2‖ = 1) :
    ∫ g, satWeight (n, L) (round0 v g) ∂stdGaussian E =
      (L.map fun c ↦ (c.2.2 : ℝ) * (1 / 2 + arcsin (rho v c.1.1 c.1.2 c.2.1) / π)).sum := by
  have h0 : ∀ g, satWeight (n, L) (round0 v g) = (L.map fun c ↦ (c.2.2 : ℝ) / 2 *
      (1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫)).sum :=
    fun g ↦ satWeight_decide n L (fun i ↦ ⟪v i, g⟫)
  simp_rw [h0]
  have hint : ∀ c ∈ L, Integrable (fun g ↦ (c.2.2 : ℝ) / 2 *
      (1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫)) (stdGaussian E) := by
    intro c _
    refine integrable_of_abs_le (C := |(c.2.2 : ℝ)|) (by fun_prop) fun g ↦ ?_
    rw [abs_mul, abs_div, abs_two]
    have : |1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_sgn, abs_sgn]
      rcases bsign_cases c.2.1 with h | h <;> rw [h] <;> norm_num
    nlinarith [abs_nonneg (c.2.2 : ℝ)]
  rw [integral_list_sum _ _ hint]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  obtain ⟨hi, hj⟩ := hv c hc
  have hs : Integrable (fun g ↦ sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫) (stdGaussian E) :=
    integrable_of_abs_le (C := 1) (by fun_prop) fun g ↦ by rw [abs_mul, abs_sgn, abs_sgn, mul_one]
  have : ∀ g, (c.2.2 : ℝ) / 2 * (1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫) =
      (c.2.2 : ℝ) / 2 + (c.2.2 : ℝ) / 2 * bsign c.2.1 *
        (sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫) := fun g ↦ by ring
  simp_rw [this]
  rw [integral_add (integrable_const _) (hs.const_mul _), integral_const, integral_const_mul,
    integral_sgn_mul_sgn hi hj, probReal_univ, one_smul, rho]
  have harc : bsign c.2.1 * arcsin ⟪v c.1.1, v c.1.2⟫ =
      arcsin (bsign c.2.1 * ⟪v c.1.1, v c.1.2⟫) := by
    rcases bsign_cases c.2.1 with h | h <;> rw [h] <;> simp [arcsin_neg]
  rw [← harc]
  have := pi_pos
  field_simp

/-- The gap constant `κ` outside the window (`BGHKLMM26.GW.exists_gap_mul`). -/
noncomputable def kappa : ℝ := Classical.choose exists_gap_mul

theorem kappa_pos : 0 < kappa := (Classical.choose_spec exists_gap_mul).1

theorem kappa_spec {ρ : ℝ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) (hout : ρ ≤ 1 / 2 ∨ 4 / 5 ≤ ρ) :
    (alphaGW + kappa) * ((1 + ρ) / 2) ≤ 1 / 2 + arcsin ρ / π :=
  (Classical.choose_spec exists_gap_mul).2 ρ h1 h2 hout

/-- **Hyperplane rounding** [BGHKLMM26, Lemma 3.4 and the Goemans–Williamson analysis]: its
expected value is at least `α_GW SDP + κ SDP_N`. -/
theorem round0_ge {I : Instance} (hI : Valid I) (hv : ∀ i < I.1, ‖v i‖ = 1) :
    alphaGW * sdp v I + kappa * sdpOut v I ≤ ∫ g, satWeight I (round0 v g) ∂stdGaussian E := by
  classical
  have hv' : ∀ c ∈ I.2, ‖v c.1.1‖ = 1 ∧ ‖v c.1.2‖ = 1 := fun c hc ↦
    ⟨hv _ ((hI.1 c hc).1.trans (hI.1 c hc).2.1), hv _ (hI.1 c hc).2.1⟩
  have h := integral_satWeight_round0 v I.1 I.2 hv'
  rw [show ((I.1, I.2) : Instance) = I from rfl] at h
  rw [h, sdp, sdpOut, ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add]
  refine List.sum_le_sum fun c hc ↦ ?_
  obtain ⟨hi, hj⟩ := hv' c hc
  have hw : (0 : ℝ) ≤ c.2.2 := by exact_mod_cast (hI.1 c hc).2.2
  have hρ := abs_le.1 (abs_rho_le v c.2.1 hi hj)
  simp only [sdpTerm]
  by_cases hwin : window v c
  · rw [ite_eq_left hwin, mul_zero, add_zero]
    have := alphaGW_mul_le hρ.1 hρ.2
    nlinarith
  · rw [ite_eq_right hwin]
    have hout : rho v c.1.1 c.1.2 c.2.1 ≤ 1 / 2 ∨ 4 / 5 ≤ rho v c.1.1 c.1.2 c.2.1 := by
      by_contra h'
      push Not at h'
      exact hwin ⟨h'.1, h'.2⟩
    have := kappa_spec hρ.1 hρ.2 hout
    nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem integrable_list_sum {α : Type*} {μ : Measure E} (l : List α) (F : α → E → ℝ)
    (hF : ∀ c ∈ l, Integrable (F c) μ) : Integrable (fun g ↦ (l.map fun c ↦ F c g).sum) μ := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF c List.mem_cons_self).add (ih fun c' hc' ↦ hF c' (List.mem_cons_of_mem _ hc'))

omit [BorelSpace E] in
/-- A rounding by signs of measurable functions has integrable value. -/
theorem integrable_satWeight_decide (n : ℕ) (L : List Constraint) {A : ℕ → E → ℝ}
    (hA : ∀ i, Measurable (A i)) :
    Integrable (fun g ↦ satWeight (n, L) (fun i ↦ decide (0 ≤ A i g))) (stdGaussian E) := by
  simp_rw [satWeight_decide]
  refine integrable_list_sum _ _ fun c _ ↦ ?_
  have h1 := hA c.1.1
  have h2 := hA c.1.2
  refine integrable_of_abs_le (C := |(c.2.2 : ℝ)|) (by fun_prop) fun g ↦ ?_
  rw [abs_mul, abs_div, abs_two]
  have : |1 + bsign c.2.1 * sgn (A c.1.1 g) * sgn (A c.1.2 g)| ≤ 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_sgn, abs_sgn]
    rcases bsign_cases c.2.1 with h | h <;> rw [h] <;> norm_num
  nlinarith [abs_nonneg (c.2.2 : ℝ)]

/-- Dropping constraints lowers the satisfied weight. -/
theorem satWeight_le_of_sublist {I : Instance} (hI : Valid I) {L : List Constraint}
    (hL : L.Sublist I.2) (x : ℕ → Bool) : satWeight (I.1, L) x ≤ satWeight I x := by
  unfold satWeight
  refine (hL.map _).sum_le_sum fun a ha ↦ ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
  split_ifs
  · exact_mod_cast (hI.1 c hc).2.2
  · exact le_rfl

/-- **The shifted rounding** [BGHKLMM26, Lemma 3.5, with Theorem 3.2]: with the triangle
inequalities up to `θ ≤ 1/20`, its expected value is at least `α_GW SDP_T + λ W_T / (250 d √L)`. -/
theorem roundL_ge {I : Instance} (hI : Valid I) {d : ℕ} (hd : MaxDegreeLE I d)
    (hv : ∀ i < I.1, ‖v i‖ = 1) {θ : ℝ} (hθ : θ ≤ 1 / 20) (htri : Triangle v I.1 θ)
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100)
    {L : ℕ} (hL : 1 ≤ L) (hβL : (1 / 2 : ℝ) ^ (2 * L + 1) ≤ 1 / (2 * d))
    (hηL : 1 / 2 ≤ (r * r) ^ (4 * L + 1)) :
    alphaGW * sdpIn v I +
        t * ((windowSet v I).map fun c ↦ (c.2.2 : ℝ)).sum / (250 * d * √L) ≤
      ∫ g, satWeight I (roundL v (windowSet v I) (r * r) t g) ∂stdGaussian E := by
  set T := windowSet v I with hTdef
  have hTv := windowSet_valid v hI
  have hρ : ∀ c ∈ T, rho v c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25 := by
    intro c hc
    have := window_of_mem v hc
    nlinarith [this.1, this.2]
  have hdeg : ∀ i, (outEdges T i).length ≤ d :=
    fun i ↦ (length_outEdges_le (windowSet_sublist v I) i).trans (hd i)
  have hgain := gain v hTv hv hρ hdeg (outU_inner_ge v hI hθ htri hv) hr0 hr1 ht0 ht hL hβL hηL
  have hv' : ∀ c ∈ T, ‖v c.1.1‖ = 1 ∧ ‖v c.1.2‖ = 1 := fun c hc ↦
    ⟨hv _ ((hTv c hc).1.trans (hTv c hc).2.1), hv _ (hTv c hc).2.1⟩
  rw [integral_satWeight_round0 v I.1 T hv'] at hgain
  have hbase : alphaGW * sdpIn v I ≤
      (T.map fun c ↦ (c.2.2 : ℝ) * (1 / 2 + arcsin (rho v c.1.1 c.1.2 c.2.1) / π)).sum := by
    rw [sdpIn, ← hTdef, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun c hc ↦ ?_
    obtain ⟨hi, hj⟩ := hv' c hc
    have hw : (0 : ℝ) ≤ c.2.2 := by exact_mod_cast (hTv c hc).2.2
    have hρ' := abs_le.1 (abs_rho_le v c.2.1 hi hj)
    have := alphaGW_mul_le hρ'.1 hρ'.2
    simp only [sdpTerm]
    nlinarith
  have hfm : ∀ i, Measurable fun g ↦ ⟪v i, g⟫ + t * fvote v T (r * r) i g := fun i ↦ by
    have : Measurable (fvote v T (r * r) i) := measurable_vote _ _ _
    fun_prop
  have hmono : ∫ g, satWeight (I.1, T) (roundL v T (r * r) t g) ∂stdGaussian E ≤
      ∫ g, satWeight I (roundL v T (r * r) t g) ∂stdGaussian E :=
    integral_mono (integrable_satWeight_decide I.1 T hfm)
      (integrable_satWeight_decide I.1 I.2 hfm)
      fun g ↦ satWeight_le_of_sublist hI (windowSet_sublist v I) _
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sdpTerm_nonneg {I : Instance} (hI : Valid I) (hv : ∀ i < I.1, ‖v i‖ = 1) {c : Constraint}
    (hc : c ∈ I.2) : 0 ≤ sdpTerm v c := by
  have hw : (0 : ℝ) ≤ c.2.2 := by exact_mod_cast (hI.1 c hc).2.2
  have := abs_le.1 (abs_rho_le v c.2.1 (hv _ ((hI.1 c hc).1.trans (hI.1 c hc).2.1))
    (hv _ (hI.1 c hc).2.1))
  unfold sdpTerm
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sdp_nonneg {I : Instance} (hI : Valid I) (hv : ∀ i < I.1, ‖v i‖ = 1) : 0 ≤ sdp v I :=
  List.sum_nonneg fun x hx ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact sdpTerm_nonneg v hI hv hc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The window's weight bounds its SDP value: `W_T ≥ SDP_T`. -/
theorem sdpIn_le {I : Instance} (hI : Valid I) (hv : ∀ i < I.1, ‖v i‖ = 1) :
    sdpIn v I ≤ ((windowSet v I).map fun c ↦ (c.2.2 : ℝ)).sum := by
  refine List.sum_le_sum fun c hc ↦ ?_
  have hc' := (windowSet_sublist v I).subset hc
  have hw : (0 : ℝ) ≤ c.2.2 := by exact_mod_cast (hI.1 c hc').2.2
  have := abs_le.1 (abs_rho_le v c.2.1 (hv _ ((hI.1 c hc').1.trans (hI.1 c hc').2.1))
    (hv _ (hI.1 c hc').2.1))
  unfold sdpTerm
  nlinarith

/-- **Lemma 3.4** [BGHKLMM26]: if `SDP_N ≥ ε SDP`, hyperplane rounding gets `(α_GW + κ ε) SDP`. -/
theorem round0_branch {I : Instance} (hI : Valid I) (hv : ∀ i < I.1, ‖v i‖ = 1) {ε : ℝ}
    (hN : ε * sdp v I ≤ sdpOut v I) :
    (alphaGW + kappa * ε) * sdp v I ≤ ∫ g, satWeight I (round0 v g) ∂stdGaussian E := by
  have := round0_ge v hI hv
  have := kappa_pos
  nlinarith

/-- **Lemma 3.5** [BGHKLMM26]: if `SDP_N ≤ 2ε SDP` with `ε ≤ Γ/8` for the gain rate
`Γ = λ / (250 d √L) ≤ 1`, the shifted rounding gets `(α_GW + Γ/2) SDP`. -/
theorem roundL_branch {I : Instance} (hI : Valid I) {d : ℕ} (hd : MaxDegreeLE I d)
    (hv : ∀ i < I.1, ‖v i‖ = 1) {θ : ℝ} (hθ : θ ≤ 1 / 20) (htri : Triangle v I.1 θ)
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100)
    {L : ℕ} (hL : 1 ≤ L) (hβL : (1 / 2 : ℝ) ^ (2 * L + 1) ≤ 1 / (2 * d))
    (hηL : 1 / 2 ≤ (r * r) ^ (4 * L + 1)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ t / (250 * d * √L) / 8) (hΓ : t / (250 * d * √L) ≤ 1)
    (hN : sdpOut v I ≤ 2 * ε * sdp v I) :
    (alphaGW + t / (250 * d * √L) / 2) * sdp v I ≤
      ∫ g, satWeight I (roundL v (windowSet v I) (r * r) t g) ∂stdGaussian E := by
  set Γ := t / (250 * d * √L) with hΓdef
  have hmain := roundL_ge v hI hd hv hθ htri hr0 hr1 ht0 ht hL hβL hηL
  have hW := sdpIn_le v hI hv
  have hsplit := sdp_eq_add v I
  have hs0 := sdp_nonneg v hI hv
  have hΓ0 : 0 ≤ Γ := by positivity
  have hα0 := alphaGW_pos
  have hα1 := alphaGW_lt_one
  have h1 : t * ((windowSet v I).map fun c ↦ (c.2.2 : ℝ)).sum / (250 * d * √L) =
      Γ * ((windowSet v I).map fun c ↦ (c.2.2 : ℝ)).sum := by rw [hΓdef]; ring
  rw [h1] at hmain
  have hin : (1 - 2 * ε) * sdp v I ≤ sdpIn v I := by linarith
  have h2 : (alphaGW + Γ) * sdpIn v I ≤ ∫ g, satWeight I (roundL v (windowSet v I) (r * r) t g)
      ∂stdGaussian E := by nlinarith
  have h3 : (alphaGW + Γ / 2) * sdp v I ≤ (alphaGW + Γ) * ((1 - 2 * ε) * sdp v I) := by
    have : alphaGW + Γ / 2 ≤ (alphaGW + Γ) * (1 - 2 * ε) := by nlinarith
    nlinarith
  have h4 : (alphaGW + Γ) * ((1 - 2 * ε) * sdp v I) ≤ (alphaGW + Γ) * sdpIn v I :=
    mul_le_mul_of_nonneg_left hin (by positivity)
  linarith

end Values

end BGHKLMM26
