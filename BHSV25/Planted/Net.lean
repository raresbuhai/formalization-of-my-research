module

public import BHSV25.Alg.ExpanderFull
public import BHSV25.Planted.Recovery

/-!
# The net and the rounding on a planted graph

The greedy net of Theorem 7.1 (`BHSV25.Alg.expNet`) and the grid clustering
(`BHSV25.Alg.gridAlg`) on any graph `G`, analysed with the matrix `A_G / d`
(`BHSV25.Planted.adjDiv`) for a scale `d > 0` that the algorithm does not know, in place of the
normalized adjacency matrix of a regular graph.

* `|xᵀ (A_G / d) x| ≤ ‖x‖²` when every degree is at most `d` (`BHSV25.Planted.abs_quad_adjDiv_le`).
* **The net** (`BHSV25.Planted.expNet_cover_adjDiv`): the filter of the net, a power of the
  integer adjacency matrix, acts on the eigenvectors of `A_G / d` by the same power of their
  eigenvalues up to the factor `d^(-2 a n)`, so the net covers the eigenvectors of `A_G / d` with
  eigenvalues at least `θ` in absolute value, at precision `4 / K`, when at most `T` eigenvalues
  of `A_G / d` are at least `θ / 2` in absolute value.
* **The rounding** (`BHSV25.Planted.numColored_gridAlg_ge`): if `χ` is a proper `k`-coloring of
  `G`, the grid clustering colors at least `n - 2 E` vertices, where `E` is the number of vertices
  that some candidate clusters differently from `χ`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset Spectral

/-! ### The matrix `A_G / d` -/

open Classical in
/-- The adjacency matrix of `G` divided by `d`. -/
noncomputable def adjDiv (G : Graph) (d : ℝ) : Matrix (Fin G.1) (Fin G.1) ℝ :=
  fun u v ↦ if G.2.Adj u v then d⁻¹ else 0

theorem adjDiv_isHermitian (G : Graph) (d : ℝ) : (adjDiv G d).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u v ↦ ?_
  simp only [adjDiv, star_trivial]
  by_cases h : G.2.Adj u v
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h h'.symm]

open Classical in
theorem sum_adj_ite (G : Graph) (u : Fin G.1) (c : ℝ) :
    ∑ v, (if G.2.Adj u v then c else 0) = G.2.degree u * c := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul,
    ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

open Classical in
/-- `|xᵀ (A_G / d) x| ≤ ‖x‖²` when every degree is at most `d`. -/
theorem abs_quad_adjDiv_le (G : Graph) {d : ℝ} (hd : 0 < d)
    (hdeg : ∀ u, (G.2.degree u : ℝ) ≤ d) (x : Fin G.1 → ℝ) :
    |x ⬝ᵥ (adjDiv G d *ᵥ x)| ≤ x ⬝ᵥ x := by
  classical
  have hexp : x ⬝ᵥ (adjDiv G d *ᵥ x) = ∑ u, ∑ v, x u * (adjDiv G d u v * x v) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [hexp]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ u, |∑ v, x u * (adjDiv G d u v * x v)| ≤
      ∑ v, ((if G.2.Adj u v then x u ^ 2 else 0) / (2 * d) +
        (if G.2.Adj u v then x v ^ 2 else 0) / (2 * d)) := by
    intro u
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ ↦ ?_)
    simp only [adjDiv]
    by_cases h : G.2.Adj u v
    · simp only [h, ite_true]
      rw [← add_div, le_div_iff₀ (by positivity), abs_mul, abs_mul, abs_inv, abs_of_pos hd]
      have : |x u| * |x v| * 2 ≤ x u ^ 2 + x v ^ 2 := by
        nlinarith [sq_nonneg (|x u| - |x v|), sq_abs (x u), sq_abs (x v)]
      calc |x u| * (d⁻¹ * |x v|) * (2 * d) = |x u| * |x v| * 2 * (d⁻¹ * d) := by ring
        _ = |x u| * |x v| * 2 := by rw [inv_mul_cancel₀ hd.ne', mul_one]
        _ ≤ x u ^ 2 + x v ^ 2 := this
    · simp [h]
  refine (sum_le_sum fun u _ ↦ h1 u).trans ?_
  simp only [sum_add_distrib, ← sum_div]
  have h2 : ∑ u, ∑ v, (if G.2.Adj u v then x v ^ 2 else 0) =
      ∑ u, ∑ v, (if G.2.Adj u v then x u ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ ?_
    simp only [G.2.adj_comm]
  rw [h2]
  simp only [sum_adj_ite]
  have h3 : ∑ u, (G.2.degree u : ℝ) * x u ^ 2 ≤ d * (x ⬝ᵥ x) := by
    rw [dotProduct, mul_sum]
    exact sum_le_sum fun u _ ↦ by
      rw [← sq]
      exact mul_le_mul_of_nonneg_right (hdeg u) (sq_nonneg _)
  rw [← add_div, div_le_iff₀ (by positivity)]
  linarith

/-! ### The net -/

/-- The integer adjacency matrix of the net is `d` times `A_G / d`. -/
theorem adjDiv_base (G : Graph) (d' : ℕ) {d : ℝ} :
    d⁻¹ • (Net.toMat G.1 (Net.baseMat false G.1 d' (adjTable G))).map (Int.castRingHom ℝ) =
      adjDiv G d := by
  classical
  ext u v
  rw [Matrix.smul_apply, Matrix.map_apply, Net.toMat_baseMat, adjDiv]
  simp only [Net.entry, Bool.false_eq_true, ite_false, Net.adjB_graph, smul_eq_mul,
    Int.coe_castRingHom]
  by_cases ha : G.2.Adj u v
  · simp [ha]
  · simp [ha]

/-- The real filter: `s^E Q = (s M)^E` for the integer table `Q = M^E`. -/
theorem filter_eq_smul (G : Graph) (d' E : ℕ) (s : ℝ) :
    (s ^ E) • (Matrix.of fun u v : Fin G.1 ↦
      (Cslib.rowEntry (Net.powL G.1 (Net.baseMat false G.1 d' (adjTable G)) E) u v : ℝ)) =
    (s • (Net.toMat G.1 (Net.baseMat false G.1 d' (adjTable G))).map (Int.castRingHom ℝ)) ^ E := by
  rw [smul_pow, ← Net.map_castRingHom_pow, ← Net.toMat_powL]
  rfl

/-- **The absolute net for `A_G / d`.** If at most `T` eigenvalues of `A_G / d` are at least `θ'`
in absolute value, the greedy net with filter `A_G^(2m)` contains, for every vector `w` of length
at most `1` in the span of the eigenvectors of `A_G / d` with eigenvalues at least `θ` in absolute
value, a vector within `2 √T / N + √n 2^(T+1) (θ' / θ)^(2m)`. -/
theorem netGS_adjDiv_correct (G : Graph) {d : ℝ} (hd : 0 < d) {θ' θ : ℝ} (hθ' : 0 < θ')
    (hθ : θ' < θ) {T : ℕ}
    (hT : (univ.filter fun i ↦ θ' ≤ |(adjDiv_isHermitian G d).eigenvalues i|).card ≤ T) (m : ℕ)
    {N B : ℕ} (hN : 0 < N) (hB : Net.BallBudget N T B) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : InEigSpan (adjDiv_isHermitian G d) (fun μ ↦ θ ≤ |μ|) w) :
    ∃ c ∈ Net.netGS false (2 * m) T N B (G.1, adjTable G),
      Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ≤
        2 * Real.sqrt T / N + Real.sqrt G.1 * 2 ^ (T + 1) * (θ' / θ) ^ (2 * m) := by
  set hA := adjDiv_isHermitian G d
  have hθ0 : 0 < θ := hθ'.trans hθ
  set d' := Net.deg G.1 (adjTable G)
  set c : ℝ := (d⁻¹) ^ (2 * m) with hc
  have hc0 : 0 < c := by positivity
  set φ : Fin G.1 → ℝ := fun i ↦ (hA.eigenvalues i ^ 2) ^ m with hφ
  have hP : ∀ i x, coeff hA i ((c • Matrix.of fun u v : Fin G.1 ↦
      (Cslib.rowEntry (Net.powL G.1 (Net.baseMat false G.1 d' (adjTable G)) (2 * m)) u v : ℝ)) *ᵥ
        x) = φ i * coeff hA i x := by
    intro i x
    rw [hc, filter_eq_smul, adjDiv_base, Net.coeff_pow_mulVec _ (fun y ↦ coeff_mulVec _ i y)
      (2 * m) x]
    simp only [hφ, ← pow_mul]
  have hb : ∀ i, 0 ≤ hA.eigenvalues i ^ 2 := fun i ↦ sq_nonneg _
  obtain ⟨cand, hcand, hdist⟩ := Net.exists_cand_near hA
    (Net.powL G.1 (Net.baseMat false G.1 d' (adjTable G)) (2 * m)) (by rw [Net.length_powL])
    (Net.rowEntry_powL_symm false G d' (2 * m)) hc0 φ hP
    (univ.filter fun i ↦ θ' ≤ |hA.eigenvalues i|) hT
    (ℓ := (θ' ^ 2) ^ m) (h := (θ ^ 2) ^ m) (by positivity) (by positivity)
    (fun i hi ↦ by
      have hi' : |hA.eigenvalues i| < θ' := by simpa using hi
      rw [hφ, abs_of_nonneg (pow_nonneg (hb i) _)]
      refine pow_le_pow_left₀ (hb i) ?_ m
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hi'.le 2)
    w hw1
    (fun i hi ↦ by
      have hle : θ ≤ |hA.eigenvalues i| := by
        by_contra hcon
        exact hi (hw i hcon)
      refine ⟨by simp only [mem_filter, mem_univ, true_and]; linarith, ?_⟩
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [← sq_abs (hA.eigenvalues i)]
      exact pow_le_pow_left₀ hθ0.le hle 2)
    hN hB
  refine ⟨cand, ?_, hdist.trans (le_of_eq ?_)⟩
  · rw [Net.netGS, Net.gsData_graph']; exact hcand
  · congr 1
    rw [mul_div_assoc, ← div_pow, ← div_pow, ← pow_mul]

/-- **The net covers the eigenvectors of `A_G / d` with eigenvalues at least `θ` in absolute
value**, at precision `4 / K`, when at most `T` eigenvalues of `A_G / d` are at least `θ / 2` in
absolute value. -/
theorem expNet_cover_adjDiv (G : Graph) {d : ℝ} (hd : 0 < d) {θ : ℝ} (hθ0 : 0 < θ) {T : ℕ}
    (hcard : (univ.filter fun i ↦ θ / 2 ≤ |(adjDiv_isHermitian G d).eigenvalues i|).card ≤ T)
    {K a : ℕ} (hK : 0 < K) (ha : T + 2 + K ≤ a) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : InEigSpan (adjDiv_isHermitian G d) (fun μ ↦ θ ≤ |μ|) w) :
    ∃ u ∈ Alg.expNet (a, T, (Nat.sqrt T + 1) * K, (3 + 12 * K) ^ T) (G.1, adjTable G),
      (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ (4 / K) ^ 2 := by
  set N := (Nat.sqrt T + 1) * K with hN
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos _) hK
  rw [Alg.expNet, Alg.numV_graph]
  simp only
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · -- no vertices
    obtain ⟨c, hc, -⟩ := Net.exists_zero_mem_netGS false (2 * (a * G.1)) T N ((3 + 12 * K) ^ T) G
      (Net.ballBudget_sqrt T K)
    refine ⟨c, hc, ?_⟩
    have : (Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w) = 0 := by
      simp only [dotProduct]
      exact Finset.sum_eq_zero fun i _ ↦ absurd i.2 (by omega)
    rw [this]
    positivity
  obtain ⟨c, hc, hcw⟩ := netGS_adjDiv_correct G hd (by positivity : 0 < θ / 2)
    (by linarith : θ / 2 < θ) hcard (a * G.1) hNpos (Net.ballBudget_sqrt T K) w hw1 hw
  refine ⟨c, hc, ?_⟩
  have hgrid : 2 * Real.sqrt T / N ≤ 2 / K := by
    have hs : Real.sqrt T ≤ (Nat.sqrt T + 1 : ℕ) := by
      push_cast
      exact (Real.real_sqrt_lt_nat_sqrt_succ).le
    rw [hN, Nat.cast_mul, div_le_div_iff₀ (by positivity) hK']
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * K)
    nlinarith
  have hfilt := Alg.abs_filter_error_le (T := T) hn hK ha hθ0
  have h1 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ≤ 4 / K := by
    refine hcw.trans ?_
    have : (4 : ℝ) / K = 2 / K + 2 / K := by ring
    rw [this]
    exact add_le_add hgrid hfilt
  have h2 := Real.sq_sqrt (Net.dot_self_nonneg (Net.ratVec G.1 c - w))
  have h3 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ^ 2 ≤ (4 / K) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [h2] at h3
  exact h3

/-! ### The rounding -/

open Classical in
/-- **The rounding of a candidate close to a proper coloring**: if `χ` is a proper `k`-coloring
of `G`, the grid clustering colors at least `n - 2 E` vertices, where `E` is the number of
vertices that the clusters of some candidate place outside their color class. -/
theorem numColored_gridAlg_ge (G : Graph) {k : ℕ} (hk : 0 < k) (χ : Fin G.1 → Fin k)
    (hχ : ∀ u v, G.2.Adj u v → χ u ≠ χ v) (Sg Kg Bg : ℕ) (U : List (List ℚ))
    (hB1 : U.length ^ k ≤ Bg) (hB2 : (2 * Kg + 1) ^ (k * k) ≤ Bg) (us : Fin k → List ℚ)
    (hus : ∀ j, us j ∈ U) (ts : Fin (k * k) → Fin (2 * Kg + 1)) :
    (G.1 : ℝ) - 2 * ((univ.filter fun y : Fin G.1 ↦ Alg.clusterIdxC (List.ofFn us)
        (Alg.gridCenters k Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y ≠
          (χ y : ℕ)).card : ℝ) ≤
      G.numColored k (Alg.gridAlg k k Sg Kg Bg U (G.1, adjTable G)) := by
  set cs := Alg.gridCenters k Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ)) with hcs
  set q : Fin G.1 → ℕ := fun y ↦ Alg.clusterIdxC (List.ofFn us) cs y with hq
  set I : ℕ → Finset (Fin G.1) := fun j ↦ univ.filter fun y ↦ (χ y : ℕ) = j with hI
  have hIind : ∀ j, G.2.IsIndepSet (I j : Set (Fin G.1)) := by
    intro j u hu v hv _ huv
    rw [mem_coe, hI, mem_filter] at hu hv
    exact hχ u v huv (Fin.ext (hu.2.trans hv.2.symm))
  have hspec := (Alg.gridAlg_spec G hk le_rfl Sg Kg Bg U hB1 hB2).2 us hus ts I hIind
  rw [← hcs] at hspec
  have hR : ∀ j, Alg.classSet G k (Alg.clustersC G.1 (List.ofFn us) cs) j =
      univ.filter fun y ↦ q y = j := by
    intro j
    ext y
    rw [Alg.classSet, mem_filter, mem_filter, Alg.getD_clustersC _ _ y.2]
  -- each term as a sum over the vertices
  have hterm : ∀ j, ((univ.filter fun y ↦ q y = j) ∩ I j).card -
      (((univ.filter fun y ↦ q y = j) \ I j).card : ℝ) =
      ∑ y, (if q y = j then (if (χ y : ℕ) = j then 1 else -1) else 0) := by
    intro j
    have h1 : (((univ.filter fun y ↦ q y = j) ∩ I j).card : ℝ) =
        ∑ y, (if q y = j then (if (χ y : ℕ) = j then 1 else 0) else 0) := by
      have e : (univ.filter fun y ↦ q y = j) ∩ I j =
          univ.filter fun y ↦ q y = j ∧ (χ y : ℕ) = j := by
        ext y; simp [hI]
      rw [e, card_filter]
      push_cast
      refine sum_congr rfl fun y _ ↦ ?_
      by_cases h1 : q y = j <;> by_cases h2 : (χ y : ℕ) = j <;> simp [h1, h2]
    have h2 : (((univ.filter fun y ↦ q y = j) \ I j).card : ℝ) =
        ∑ y, (if q y = j then (if (χ y : ℕ) = j then 0 else 1) else 0) := by
      have e : (univ.filter fun y ↦ q y = j) \ I j =
          univ.filter fun y ↦ q y = j ∧ ¬ (χ y : ℕ) = j := by
        ext y; simp [hI]
      rw [e, card_filter]
      push_cast
      refine sum_congr rfl fun y _ ↦ ?_
      by_cases h1 : q y = j <;> by_cases h2 : (χ y : ℕ) = j <;> simp [h1, h2]
    rw [h1, h2, ← sum_sub_distrib]
    refine sum_congr rfl fun y _ ↦ ?_
    by_cases h1 : q y = j <;> by_cases h2 : (χ y : ℕ) = j <;> simp [h1, h2]
  -- the sum over the clusters, vertex by vertex
  have hpt : ∀ y, (if q y = χ y then (1 : ℝ) else -1) ≤
      ∑ j ∈ range k, (if q y = j then (if (χ y : ℕ) = j then 1 else -1) else 0) := by
    intro y
    by_cases hyk : q y < k
    · rw [sum_eq_single_of_mem (q y) (mem_range.2 hyk) (fun j _ hj ↦ by simp [Ne.symm hj])]
      simp only [ite_true]
      by_cases h : q y = χ y
      · simp [h]
      · simp [h, Ne.symm h]
    · have hne : q y ≠ χ y := fun h ↦ hyk (h ▸ (χ y).2)
      rw [sum_eq_zero fun j hj ↦ by
        rw [mem_range] at hj
        simp [show q y ≠ j by omega]]
      simp [hne]
  have hall : ∑ y, (if q y = χ y then (1 : ℝ) else -1) =
      G.1 - 2 * ((univ.filter fun y : Fin G.1 ↦ q y ≠ (χ y : ℕ)).card : ℝ) := by
    have e : ∀ y, (if q y = χ y then (1 : ℝ) else -1) =
        1 - 2 * (if q y ≠ (χ y : ℕ) then 1 else 0) := fun y ↦ by
      by_cases h : q y = χ y <;> simp [h]; norm_num
    rw [sum_congr rfl fun y _ ↦ e y, sum_sub_distrib, ← mul_sum, card_filter]
    simp
  have hlow : (G.1 : ℝ) - 2 * ((univ.filter fun y : Fin G.1 ↦ q y ≠ (χ y : ℕ)).card : ℝ) ≤
      ∑ j ∈ range k, max 0 (((Alg.classSet G k (Alg.clustersC G.1 (List.ofFn us) cs) j ∩
        I j).card : ℝ) - (Alg.classSet G k (Alg.clustersC G.1 (List.ofFn us) cs) j \
          I j).card) := by
    rw [← hall]
    calc ∑ y, (if q y = χ y then (1 : ℝ) else -1)
        ≤ ∑ y, ∑ j ∈ range k, (if q y = j then (if (χ y : ℕ) = j then 1 else -1) else 0) :=
          sum_le_sum fun y _ ↦ hpt y
      _ = ∑ j ∈ range k, ∑ y, (if q y = j then (if (χ y : ℕ) = j then 1 else -1) else 0) :=
          Finset.sum_comm
      _ ≤ _ := by
          refine sum_le_sum fun j _ ↦ ?_
          rw [hR, ← hterm]
          exact le_max_right _ _
  exact hlow.trans hspec

end Planted

end BHSV25
