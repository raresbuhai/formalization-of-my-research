module

public import BHSV25.Net.Approx
public import BHSV25.Net.Machine
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The nets are correct

On the input of a regular graph, the candidate list `BHSV25.Net.netList` contains a vector close to
every target vector (`BHSV25.Net.bottomNet_correct`, `BHSV25.Net.absNet_correct`).

* **The input of a graph** (`BHSV25.Net.adjB_graph`, `BHSV25.Net.deg_graph`): the table gives the
  adjacency relation, and the degree of vertex `0` is the degree of the graph. (The first proof is
  adapted from `BHSV25.Alg.adjBit_adjTable` in `BHSV25/Alg/GraphMachine.lean`.)
* **The filter** (`BHSV25.Net.filt`): the real matrix `Q / D^e` that the machine computes; it is
  symmetric and equals `(M / D)^e`. A candidate is `P (∑ⱼ βⱼ e_{vⱼ})` with `βⱼ = (zⱼ - Z) / S`
  (`BHSV25.Net.realVec_cand_eq`).
* **Rounding** (`BHSV25.Net.near_of_filter`): the coefficients of `BHSV25.Net.exists_near`,
  multiplied by `S` and rounded, lie in `[-Z, Z]` and move by at most `1 / S`.
* **The two filters**: `((I - Ã)/2)^m` and `Ã^(2m)`, and the constants of `BHSV25.Net.Params`
  (`BHSV25.Net.exists_consts`): with `m = c (a + 2 ⌈log₂ (n + 1)⌉)`, the ratio `(ℓ₀/h₀)^m` of
  the filter outside and on the target eigenspace is at most `2^(-a) / n²`, and the coefficients
  are at most `n / h₀^m = n^O(1)`.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral

/-- A list of rationals read as a real vector of length `n` (missing entries are `0`); the same
as `BHSV25.Net.vecOf` of `BHSV25/Net/Spec.lean`. -/
def realVec (n : ℕ) (c : List ℚ) : Fin n → ℝ := fun i ↦ ((c.getD i 0 : ℚ) : ℝ)

/-! ### The input of a graph -/

theorem numV_graph (G : Graph) : numV (G.1, adjTable G) = G.1 := by
  have h : (adjTable G).length = G.1 * G.1 := by rw [adjTable, List.length_ofFn]
  rw [numV, h]
  refine min_eq_right ?_
  rcases Nat.eq_zero_or_pos G.1 with h0 | h0
  · omega
  · exact Nat.le_mul_of_pos_left _ h0

open Classical in
theorem adjB_graph (G : Graph) (u v : Fin G.1) :
    adjB G.1 (adjTable G) u v = decide (G.2.Adj u v) := by
  have hlt : (u : ℕ) * G.1 + v < G.1 * G.1 := by
    have := u.2
    have := v.2
    nlinarith
  have hlen : (adjTable G).length = G.1 * G.1 := by rw [adjTable, List.length_ofFn]
  have hk : (⟨(u : ℕ) * G.1 + v, hlt⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) :=
    Fin.ext (by rw [finProdFinEquiv_apply_val]; ring)
  rw [adjB, List.getD_eq_getElem _ _ (by rw [hlen]; exact hlt)]
  simp only [adjTable, List.getElem_ofFn]
  rw [show (⟨(u : ℕ) * G.1 + v, _⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) from hk,
    Equiv.symm_apply_apply]

theorem countP_range (n : ℕ) (q : ℕ → Bool) :
    (List.range n).countP q = ∑ v : Fin n, if q v then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Fin.sum_univ_castSucc]
    simp [List.countP_cons]

open Classical in
theorem deg_graph (G : Graph) (h0 : 0 < G.1) : deg G.1 (adjTable G) = G.2.degree ⟨0, h0⟩ := by
  rw [deg, countP_range, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have h : (adjTable G).getD v false = adjB G.1 (adjTable G) (⟨0, h0⟩ : Fin G.1) v := by
    simp [adjB]
  rw [h, adjB_graph]
  simp

/-! ### The filter -/

/-- The real filter `P = Q / D^e` that the machine computes on a graph, for the degree `d`. -/
noncomputable def filt (p : Params) (G : Graph) (d : ℕ) : Matrix (Fin G.1) (Fin G.1) ℝ :=
  ((denBase p d : ℝ)⁻¹ ^ expo p G.1) •
    (toMat G.1 (powL G.1 (baseMat p.bottom G.1 d (adjTable G)) (expo p G.1))).map
      (Int.castRingHom ℝ)

theorem map_castRingHom_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (e : ℕ) :
    (M ^ e).map (Int.castRingHom ℝ) = (M.map (Int.castRingHom ℝ)) ^ e := by
  induction e with
  | zero => simp [Matrix.map_one]
  | succ e ih => rw [pow_succ, pow_succ, Matrix.map_mul, ih]

theorem filt_eq (p : Params) (G : Graph) (d : ℕ) :
    filt p G d = ((denBase p d : ℝ)⁻¹ •
      (toMat G.1 (baseMat p.bottom G.1 d (adjTable G))).map (Int.castRingHom ℝ)) ^ expo p G.1 := by
  rw [filt, toMat_powL, map_castRingHom_pow, smul_pow]

theorem toMat_baseMat_symm (p : Params) (G : Graph) (d : ℕ) :
    (toMat G.1 (baseMat p.bottom G.1 d (adjTable G)))ᵀ =
      toMat G.1 (baseMat p.bottom G.1 d (adjTable G)) := by
  classical
  ext u v
  rw [transpose_apply, toMat_baseMat]
  simp only [entry, adjB_graph, G.2.adj_comm u v]
  by_cases h : u = v
  · subst h; rfl
  · have h1 : (v : ℕ) ≠ u := fun h' ↦ h (Fin.ext h'.symm)
    have h2 : (u : ℕ) ≠ v := fun h' ↦ h (Fin.ext h')
    simp [h1, h2]

theorem filt_symm (p : Params) (G : Graph) (d : ℕ) (u v : Fin G.1) :
    filt p G d u v = filt p G d v u := by
  have h := toMat_baseMat_symm p G d
  have h' : (toMat G.1 (powL G.1 (baseMat p.bottom G.1 d (adjTable G)) (expo p G.1)))ᵀ =
      toMat G.1 (powL G.1 (baseMat p.bottom G.1 d (adjTable G)) (expo p G.1)) := by
    rw [toMat_powL, transpose_pow, h]
  unfold filt
  simp only [Matrix.smul_apply, Matrix.map_apply]
  rw [← transpose_apply (toMat G.1 _) v u, h']

/-! ### Candidates -/

theorem realVec_cand (T n Z : ℕ) (q : ℚ) (Q : List (List ℤ)) (f : Fin T → Fin n)
    (zz : Fin T → ℕ) (u : Fin n) :
    realVec n (cand T n Z q Q (List.ofFn fun j ↦ (f j : ℕ)) (List.ofFn zz)) u =
      (∑ j : Fin T, ((zz j : ℝ) - Z) * (toMat n Q (f j) u : ℝ)) / (q : ℝ) := by
  rw [realVec, cand, getD_map_range n _ _ u.2, sum_map_range]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h1 : (List.ofFn zz).getD j 0 = zz j := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have h2 : (List.ofFn fun j ↦ (f j : ℕ)).getD j 0 = f j := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [h1, h2]
  rfl

/-- **A candidate is the filter applied to a sparse vector**, with coefficients
`(zⱼ - Z) / S`. -/
theorem realVec_cand_eq (p : Params) (G : Graph) {d : ℕ} (hd : 0 < d) (hK : 0 < p.K)
    (hn : 0 < G.1) (f : Fin p.T → Fin G.1) (zz : Fin p.T → ℕ) :
    realVec G.1 (cand p.T G.1 (zMax p G.1) ((p.K * G.1 * denBase p d ^ expo p G.1 : ℕ) : ℚ)
      (powL G.1 (baseMat p.bottom G.1 d (adjTable G)) (expo p G.1))
      (List.ofFn fun j ↦ (f j : ℕ)) (List.ofFn zz)) =
    filt p G d *ᵥ ∑ j, (((zz j : ℝ) - zMax p G.1) / (p.K * G.1)) • Pi.single (f j) 1 := by
  funext u
  rw [realVec_cand, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Finset.sum_apply, Pi.smul_apply,
    Matrix.col_apply, smul_eq_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [filt_symm p G d u (f j)]
  unfold filt
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.coe_castRingHom]
  have hD : (0 : ℝ) < denBase p d := by
    unfold denBase
    split_ifs <;> positivity
  have hK' : (0 : ℝ) < p.K := by exact_mod_cast hK
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  push_cast
  field_simp
  rw [mul_assoc _ ((denBase p d : ℝ) ^ _), ← mul_pow, mul_one_div_cancel hD.ne', one_pow, mul_one]

/-- **Rounding**: the net contains a candidate within the error of `BHSV25.Net.exists_near`, for
the scale `S = K n`, when the range `Z` covers the coefficients. -/
theorem near_of_filter (p : Params) (G : Graph) {d : ℕ} (hdeg : deg G.1 (adjTable G) = d)
    (hd : 0 < d) (hK : 0 < p.K) (hn : 0 < G.1) (φ : Fin G.1 → ℝ)
    (hP : ∀ i x, coeff G.normAdj_isHermitian i (filt p G d *ᵥ x) =
      φ i * coeff G.normAdj_isHermitian i x)
    (R : Finset (Fin G.1)) (hR : R.card ≤ p.T) {ℓ h : ℝ} (hh : 0 < h) (hφ1 : ∀ i, |φ i| ≤ 1)
    (hφl : ∀ i ∉ R, |φ i| ≤ ℓ) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : ∀ i, coeff G.normAdj_isHermitian i w ≠ 0 → i ∈ R ∧ h ≤ φ i)
    (hZ : (p.K * G.1 : ℝ) * (G.1 / h) + 1 ≤ zMax p G.1) :
    ∃ c ∈ netList p (G.1, adjTable G), (realVec G.1 c - w) ⬝ᵥ (realVec G.1 c - w) ≤
      2 * (p.T * (1 / (p.K * G.1 : ℝ))) ^ 2 + 2 * (ℓ * (p.T * (G.1 / h))) ^ 2 := by
  obtain ⟨f, β, hβ, hnear⟩ :=
    exists_near G.normAdj_isHermitian (filt p G d) φ hP R hR hn hh hφ1 hφl w hw1 hw
  set S : ℝ := p.K * G.1 with hS
  have hS0 : 0 < S := by
    have hK' : (0 : ℝ) < p.K := by exact_mod_cast hK
    have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
    positivity
  set Z := zMax p G.1 with hZdef
  set r : Fin p.T → ℤ := fun j ↦ round (β j * S) with hrdef
  have hr : ∀ j, |(r j : ℝ) - β j * S| ≤ 1 / 2 := fun j ↦ by
    rw [abs_sub_comm]
    exact abs_sub_round _
  have hrZ : ∀ j, |r j| ≤ Z := by
    intro j
    have h1 : |β j * S| ≤ S * (G.1 / h) := by
      rw [abs_mul, abs_of_pos hS0, mul_comm]
      exact mul_le_mul_of_nonneg_left (hβ j) hS0.le
    have h2 : |(r j : ℝ)| ≤ Z := by
      calc |(r j : ℝ)| = |((r j : ℝ) - β j * S) + β j * S| := by ring_nf
        _ ≤ |(r j : ℝ) - β j * S| + |β j * S| := abs_add_le _ _
        _ ≤ 1 / 2 + S * (G.1 / h) := add_le_add (hr j) h1
        _ ≤ Z := by linarith
    have h3 : ((|r j| : ℤ) : ℝ) ≤ ((Z : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      exact_mod_cast h2
    exact_mod_cast h3
  set zz : Fin p.T → ℕ := fun j ↦ (r j + Z).toNat with hzzdef
  have hzz : ∀ j, ((zz j : ℕ) : ℤ) = r j + Z := fun j ↦ by
    have := hrZ j
    rw [abs_le] at this
    exact Int.toNat_of_nonneg (by omega)
  have hzzlt : ∀ j, zz j < 2 * Z + 1 := fun j ↦ by
    have h1 := hzz j
    have h2 := hrZ j
    rw [abs_le] at h2
    omega
  have hzzR : ∀ j, (zz j : ℝ) - Z = r j := fun j ↦ by
    have h1 : ((zz j : ℤ) : ℝ) = ((r j + Z : ℤ) : ℝ) := by rw [hzz j]
    push_cast at h1
    linarith
  set vs := List.ofFn fun j ↦ (f j : ℕ)
  set zs := List.ofFn zz
  refine ⟨cand p.T G.1 Z ((p.K * G.1 * denBase p d ^ expo p G.1 : ℕ) : ℚ)
    (powL G.1 (baseMat p.bottom G.1 d (adjTable G)) (expo p G.1)) vs zs, ?_, ?_⟩
  · rw [netList, ctx, numV_graph, hdeg]
    refine List.mem_cons_of_mem _ ?_
    rw [body, List.mem_flatMap]
    have hL1 : G.1 ^ p.T ≤ budget p G.1 := Nat.pow_le_pow_left (by omega) _
    have hL2 : (2 * Z + 1) ^ p.T ≤ budget p G.1 := Nat.pow_le_pow_left (by omega) _
    refine ⟨vs, Tuples.ofFn_mem_tuples hL1 f, ?_⟩
    rw [List.mem_map]
    refine ⟨zs, ?_, rfl⟩
    exact Tuples.ofFn_mem_tuples hL2 (fun j ↦ (⟨zz j, hzzlt j⟩ : Fin (2 * Z + 1)))
  · rw [realVec_cand_eq p G hd hK hn f zz]
    refine hnear _ (1 / S) fun j ↦ ?_
    rw [hzzR j]
    have h1 : (r j : ℝ) / S - β j = ((r j : ℝ) - β j * S) / S := by field_simp
    rw [h1, abs_div, abs_of_pos hS0]
    exact div_le_div_of_nonneg_right ((hr j).trans (by norm_num)) hS0.le

/-! ### The constants -/

theorem two_pow_size_le {n : ℕ} (hn : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  have h1 : 0 < n.size := Nat.size_pos.2 hn
  have h2 : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.1 (by omega)
  calc 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
        rw [← pow_succ']
        congr 1
        omega
    _ ≤ 2 * n := by omega

/-- The range `Z` covers the coefficients: `K n · n / h₀^m + 1 ≤ Z_c (n + 1)^{Z_e}`. -/
theorem range_ok {h₀ : ℝ} (hh0 : 0 < h₀) {c a K H : ℕ} (hH : 1 / h₀ ≤ H) {n : ℕ} (hn : 0 < n) :
    (K * n : ℝ) * (n / h₀ ^ (c * (a + 2 * n.size))) + 1 ≤
      (((K * H ^ (c * a) * 2 ^ (2 * c * H) + 1) * (n + 1) ^ (2 * c * H + 2) : ℕ) : ℝ) := by
  set m := c * (a + 2 * n.size) with hm
  have hHm : 1 / h₀ ^ m ≤ (H : ℝ) ^ m := by
    rw [← _root_.one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hH m
  have e1 : H ^ m = H ^ (c * a) * H ^ (2 * c * n.size) := by
    rw [← pow_add]
    congr 1
    rw [hm]
    ring
  have e2 : H ^ (2 * c * n.size) ≤ 2 ^ (2 * c * H) * n ^ (2 * c * H) := by
    calc H ^ (2 * c * n.size) ≤ (2 ^ H) ^ (2 * c * n.size) :=
          Nat.pow_le_pow_left H.lt_two_pow_self.le _
      _ = (2 ^ n.size) ^ (2 * c * H) := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (2 * n) ^ (2 * c * H) := Nat.pow_le_pow_left (two_pow_size_le hn) _
      _ = 2 ^ (2 * c * H) * n ^ (2 * c * H) := mul_pow _ _ _
  have hnat : K * n * n * H ^ m ≤ K * H ^ (c * a) * 2 ^ (2 * c * H) * n ^ (2 * c * H + 2) := by
    rw [e1]
    calc K * n * n * (H ^ (c * a) * H ^ (2 * c * n.size)) ≤
          K * n * n * (H ^ (c * a) * (2 ^ (2 * c * H) * n ^ (2 * c * H))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ = K * H ^ (c * a) * 2 ^ (2 * c * H) * n ^ (2 * c * H + 2) := by ring
  have hnat2 : K * n * n * H ^ m + 1 ≤
      (K * H ^ (c * a) * 2 ^ (2 * c * H) + 1) * (n + 1) ^ (2 * c * H + 2) := by
    have h1 : n ^ (2 * c * H + 2) ≤ (n + 1) ^ (2 * c * H + 2) := Nat.pow_le_pow_left (by omega) _
    have h2 : 1 ≤ (n + 1) ^ (2 * c * H + 2) := Nat.one_le_pow _ _ (by omega)
    calc K * n * n * H ^ m + 1 ≤ K * H ^ (c * a) * 2 ^ (2 * c * H) * n ^ (2 * c * H + 2) + 1 :=
          by omega
      _ ≤ K * H ^ (c * a) * 2 ^ (2 * c * H) * (n + 1) ^ (2 * c * H + 2) +
          (n + 1) ^ (2 * c * H + 2) := Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
      _ = _ := by ring
  have hreal : (K * n : ℝ) * (n / h₀ ^ m) ≤ (K * n : ℝ) * (n * (H : ℝ) ^ m) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hHm (by positivity)
  calc (K * n : ℝ) * (n / h₀ ^ m) + 1 ≤ (K * n : ℝ) * (n * (H : ℝ) ^ m) + 1 := by linarith
    _ = ((K * n * n * H ^ m + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast hnat2

/-- The error: `2 (T / (K n))² + 2 (ℓ₀^m T n / h₀^m)² ≤ (κ / n)²`. -/
theorem error_ok {h₀ ℓ₀ : ℝ} (hℓ0 : 0 < ℓ₀) (hh0 : 0 < h₀) {c a K T : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hc : (ℓ₀ / h₀) ^ c < 1 / 2) (ha : 2 * (T : ℝ) / κ < 2 ^ a) (hK : 2 * (T : ℝ) / κ < K)
    {n : ℕ} (hn : 0 < n) :
    2 * (T * (1 / (K * n : ℝ))) ^ 2 +
      2 * (ℓ₀ ^ (c * (a + 2 * n.size)) * (T * (n / h₀ ^ (c * (a + 2 * n.size))))) ^ 2 ≤
        (κ / n) ^ 2 := by
  set m := c * (a + 2 * n.size) with hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK0 : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
  have hK2 : 2 * (T : ℝ) < K * κ := (div_lt_iff₀ hκ).1 hK
  have ha2 : 2 * (T : ℝ) < 2 ^ a * κ := (div_lt_iff₀ hκ).1 ha
  have h1 : (T : ℝ) * (1 / (K * n)) ≤ κ / (2 * n) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hρ0 : 0 ≤ ℓ₀ / h₀ := by positivity
  have hρm : (ℓ₀ / h₀) ^ m ≤ (1 / 2) ^ (a + 2 * n.size) := by
    rw [hm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hc.le _
  have hsz : (n : ℝ) < 2 ^ n.size := by exact_mod_cast Nat.lt_size_self n
  have hk : (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n.size) ^ 2 := pow_le_pow_left₀ hn'.le hsz.le 2
  have e4 : (2 : ℝ) ^ a * ((2 : ℝ) ^ n.size) ^ 2 = 2 ^ (a + 2 * n.size) := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  have key : (T : ℝ) * n * (2 * n) ≤ κ * (2 ^ a * ((2 : ℝ) ^ n.size) ^ 2) := by
    calc (T : ℝ) * n * (2 * n) = (2 * T) * n ^ 2 := by ring
      _ ≤ (2 ^ a * κ) * n ^ 2 := mul_le_mul_of_nonneg_right ha2.le (by positivity)
      _ ≤ (2 ^ a * κ) * ((2 : ℝ) ^ n.size) ^ 2 := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = κ * (2 ^ a * ((2 : ℝ) ^ n.size) ^ 2) := by ring
  have h2 : ℓ₀ ^ m * (T * (n / h₀ ^ m)) ≤ κ / (2 * n) := by
    have e : ℓ₀ ^ m * (T * (n / h₀ ^ m)) = (ℓ₀ / h₀) ^ m * (T * n) := by
      rw [div_pow]
      field_simp
    rw [e]
    calc (ℓ₀ / h₀) ^ m * (T * n) ≤ (1 / 2) ^ (a + 2 * n.size) * (T * n) :=
          mul_le_mul_of_nonneg_right hρm (by positivity)
      _ = (T * n) / (2 ^ a * ((2 : ℝ) ^ n.size) ^ 2) := by
          rw [e4, _root_.one_div_pow]
          ring
      _ ≤ κ / (2 * n) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith [key]
  have h1' := pow_le_pow_left₀ (by positivity) h1 2
  have h2' := pow_le_pow_left₀ (by positivity) h2 2
  calc _ ≤ 2 * (κ / (2 * n)) ^ 2 + 2 * (κ / (2 * n)) ^ 2 := by linarith
    _ = (κ / n) ^ 2 := by
        field_simp
        ring

/-! ### Degenerate inputs -/

theorem realVec_nil (n : ℕ) : realVec n [] = 0 := by
  funext i
  simp [realVec]

open Classical in
/-- A regular graph of degree `0` has only the eigenvalue `0`. -/
theorem eig_eq_zero_of_deg_zero (G : Graph) (h : G.2.IsRegularOfDegree 0) (i : Fin G.1) :
    G.eig i = 0 := by
  classical
  have h0 : ∀ u v, G.normAdj u v = 0 := fun u v ↦ by
    rw [G.normAdj_of_isRegularOfDegree h]
    simp
  have h1 := coeff_mulVec G.normAdj_isHermitian i ⇑(G.normAdj_isHermitian.eigenvectorBasis i)
  rw [coeff_eigenvector] at h1
  have h2 : G.normAdj *ᵥ ⇑(G.normAdj_isHermitian.eigenvectorBasis i) = 0 := by
    ext u
    simp only [mulVec, dotProduct, h0, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  rw [h2] at h1
  simp only [coeff, dotProduct_zero] at h1
  simp only [ite_true, mul_one] at h1
  exact h1.symm

theorem eq_zero_of_inEigSpan (G : Graph) {S : ℝ → Prop} {w : Fin G.1 → ℝ}
    (hw : G.InEigSpan S w) (hS : ∀ i, ¬ S (G.eig i)) : w = 0 :=
  eq_of_coeff_eq G.normAdj_isHermitian fun i ↦ by
    rw [hw i (hS i)]
    simp [coeff]

theorem dist_zero_le (n : ℕ) (κ : ℝ) :
    (realVec n [] - 0) ⬝ᵥ (realVec n [] - 0) ≤ (κ / n) ^ 2 := by
  rw [realVec_nil, sub_zero, dotProduct_zero]
  positivity

theorem dist_empty_le (G : Graph) (hn : G.1 = 0) (w : Fin G.1 → ℝ) (κ : ℝ) :
    (realVec G.1 [] - w) ⬝ᵥ (realVec G.1 [] - w) ≤ (κ / G.1) ^ 2 := by
  have h : (realVec G.1 [] - w) ⬝ᵥ (realVec G.1 [] - w) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ absurd i.2 (by omega)
  rw [h]
  positivity

/-! ### The two filters -/

theorem coeff_halfSub (G : Graph) (i : Fin G.1) (x : Fin G.1 → ℝ) :
    coeff G.normAdj_isHermitian i (((1 / 2 : ℝ) • (1 - G.normAdj)) *ᵥ x) =
      ((1 - G.eig i) / 2) * coeff G.normAdj_isHermitian i x := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, coeff_smul, coeff_sub,
    coeff_mulVec]
  unfold Graph.eig
  ring

open Classical in
/-- For the bottom eigenspace, `M / D = (I - Ã) / 2`. -/
theorem bottom_base (p : Params) (hp : p.bottom = true) (G : Graph) {d : ℕ}
    (hreg : G.2.IsRegularOfDegree d) (hd : 0 < d) :
    (denBase p d : ℝ)⁻¹ • (toMat G.1 (baseMat p.bottom G.1 d (adjTable G))).map
      (Int.castRingHom ℝ) = (1 / 2 : ℝ) • (1 - G.normAdj) := by
  classical
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext u v
  rw [Matrix.smul_apply, Matrix.map_apply, toMat_baseMat, Matrix.smul_apply, Matrix.sub_apply,
    G.normAdj_of_isRegularOfDegree hreg u v, Matrix.one_apply]
  simp only [entry, hp, ite_true, adjB_graph, denBase, smul_eq_mul, Int.coe_castRingHom]
  by_cases huv : u = v
  · subst huv
    simp only [ite_true, G.2.irrefl, decide_false, Bool.false_eq_true, ite_false]
    push_cast
    field_simp
    ring
  · have h' : (u : ℕ) ≠ v := fun h ↦ huv (Fin.ext h)
    by_cases ha : G.2.Adj u v
    · simp only [h', huv, ha, ite_false, ite_true, decide_true]
      push_cast
      field_simp
      ring
    · simp only [h', huv, ha, ite_false, decide_false, Bool.false_eq_true]
      simp

open Classical in
/-- For the absolute eigenspace, `M / D = Ã`. -/
theorem abs_base (p : Params) (hp : p.bottom = false) (G : Graph) {d : ℕ}
    (hreg : G.2.IsRegularOfDegree d) :
    (denBase p d : ℝ)⁻¹ • (toMat G.1 (baseMat p.bottom G.1 d (adjTable G))).map
      (Int.castRingHom ℝ) = G.normAdj := by
  classical
  ext u v
  rw [Matrix.smul_apply, Matrix.map_apply, toMat_baseMat, G.normAdj_of_isRegularOfDegree hreg u v]
  simp only [entry, hp, Bool.false_eq_true, ite_false, adjB_graph, denBase, smul_eq_mul,
    Int.coe_castRingHom, one_mul]
  by_cases ha : G.2.Adj u v
  · simp [ha]
  · simp [ha]

/-! ### The two nets -/

/-- The parameters for filter values `ℓ₀^m` outside and `h₀^m` on the target eigenspace: the
exponent, scale and range of `BHSV25.Net.range_ok` and `BHSV25.Net.error_ok`. -/
theorem exists_params {h₀ ℓ₀ : ℝ} (hℓ0 : 0 < ℓ₀) (hℓh : ℓ₀ < h₀) {κ : ℝ} (hκ : 0 < κ)
    (bottom : Bool) (T : ℕ) :
    ∃ p : Params, p.bottom = bottom ∧ p.T = T ∧ 0 < p.K ∧ ∀ n : ℕ, 0 < n →
      (p.K * n : ℝ) * (n / h₀ ^ (p.c * (p.a + 2 * n.size))) + 1 ≤ zMax p n ∧
      2 * (T * (1 / (p.K * n : ℝ))) ^ 2 +
        2 * (ℓ₀ ^ (p.c * (p.a + 2 * n.size)) * (T * (n / h₀ ^ (p.c * (p.a + 2 * n.size))))) ^ 2
          ≤ (κ / n) ^ 2 := by
  have hh0 : 0 < h₀ := hℓ0.trans hℓh
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
    ((div_lt_one hh0).2 hℓh)
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (2 * (T : ℝ) / κ) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (T : ℝ) / κ)
  obtain ⟨H, hH⟩ := exists_nat_ge (1 / h₀)
  have hK0 : 0 < K := by
    have : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
    exact_mod_cast this
  refine ⟨⟨bottom, T, c, a, K, K * H ^ (c * a) * 2 ^ (2 * c * H) + 1, 2 * c * H + 2⟩, rfl, rfl,
    hK0, fun n hn ↦ ⟨?_, error_ok hℓ0 hh0 hκ hc ha hK hn⟩⟩
  have h := range_ok hh0 (c := c) (a := a) (K := K) hH hn
  simpa [zMax] using h

/-- **The bottom net is correct**: on every regular graph with at most `T` eigenvalues at most
`-θ'`, it contains a vector within `κ / n` of every vector of norm at most `1` in the span of the
eigenvectors with eigenvalues at most `-θ`. -/
theorem bottomNet_correct (θ' θ κ : ℚ) (hθ' : 0 < θ') (hθ : θ' < θ) (_hθ1 : θ < 1) (hκ : 0 < κ)
    (T : ℕ) :
    ∃ p : Params, ∀ G : Graph, G.IsRegular →
      (Finset.univ.filter fun i ↦ G.eig i ≤ -θ').card ≤ T →
        ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (· ≤ -θ) w →
          ∃ c ∈ netList p (G.1, adjTable G),
            (realVec G.1 c - w) ⬝ᵥ (realVec G.1 c - w) ≤ (κ / G.1) ^ 2 := by
  have hθ'r : (0 : ℝ) < θ' := by exact_mod_cast hθ'
  have hθr : (θ' : ℝ) < θ := by exact_mod_cast hθ
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  set h₀ : ℝ := (1 + θ) / 2 with hh₀
  set ℓ₀ : ℝ := (1 + θ') / 2 with hℓ₀
  have hℓ0 : 0 < ℓ₀ := by rw [hℓ₀]; linarith
  have hℓh : ℓ₀ < h₀ := by rw [hℓ₀, hh₀]; linarith
  obtain ⟨p, hpb, hpT, hK0, hp⟩ := exists_params hℓ0 hℓh hκr true T
  refine ⟨p, ?_⟩
  rintro G ⟨d, hreg⟩ hcount w hw1 hw
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · exact ⟨[], List.mem_cons_self, dist_empty_le G hn w κ⟩
  have hdeg : deg G.1 (adjTable G) = d := by
    rw [deg_graph G hn]
    exact hreg _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hw0 : w = 0 := eq_zero_of_inEigSpan G hw fun i ↦ by
      rw [eig_eq_zero_of_deg_zero G hreg i]
      linarith
    subst hw0
    exact ⟨[], List.mem_cons_self, dist_zero_le G.1 κ⟩
  set m := p.c * (p.a + 2 * G.1.size) with hm
  have hexpo : expo p G.1 = m := by simp [expo, hpb, hm]
  set φ : Fin G.1 → ℝ := fun i ↦ ((1 - G.eig i) / 2) ^ m with hφ
  have hP : ∀ i x, coeff G.normAdj_isHermitian i (filt p G d *ᵥ x) =
      φ i * coeff G.normAdj_isHermitian i x := by
    intro i x
    rw [filt_eq, bottom_base p hpb G hreg hd, hexpo]
    exact coeff_pow_mulVec _ (coeff_halfSub G i) m x
  have hb : ∀ i, 0 ≤ (1 - G.eig i) / 2 ∧ (1 - G.eig i) / 2 ≤ 1 := fun i ↦ by
    have := abs_le.1 (G.abs_eig_le_one i)
    constructor <;> linarith
  obtain ⟨c, hc, hdist⟩ := near_of_filter p G hdeg hd hK0 hn φ hP
    (Finset.univ.filter fun i ↦ G.eig i ≤ -θ') (hpT ▸ hcount) (ℓ := ℓ₀ ^ m) (h := h₀ ^ m)
    (pow_pos (by rw [hh₀]; linarith) m)
    (fun i ↦ by
      rw [abs_of_nonneg (pow_nonneg (hb i).1 _)]
      exact pow_le_one₀ (hb i).1 (hb i).2)
    (fun i hi ↦ by
      have hi' : -(θ' : ℝ) < G.eig i := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
        exact hi
      rw [abs_of_nonneg (pow_nonneg (hb i).1 _)]
      exact pow_le_pow_left₀ (hb i).1 (by rw [hℓ₀]; linarith) m)
    w hw1
    (fun i hi ↦ by
      have hle : G.eig i ≤ -(θ : ℝ) := by
        by_contra hcon
        exact hi (hw i hcon)
      refine ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith, ?_⟩
      exact pow_le_pow_left₀ (by rw [hh₀]; linarith) (by rw [hh₀]; linarith) m)
    (hp G.1 hn).1
  refine ⟨c, hc, hdist.trans ?_⟩
  rw [hpT]
  exact (hp G.1 hn).2

/-- **The absolute net is correct**: on every regular graph with at most `T` eigenvalues at least
`θ'` in absolute value, it contains a vector within `κ / n` of every vector of norm at most `1` in
the span of the eigenvectors with eigenvalues at least `θ` in absolute value. -/
theorem absNet_correct (θ' θ κ : ℚ) (hθ' : 0 < θ') (hθ : θ' < θ) (_hθ1 : θ ≤ 1) (hκ : 0 < κ)
    (T : ℕ) :
    ∃ p : Params, ∀ G : Graph, G.IsRegular →
      (Finset.univ.filter fun i ↦ θ' ≤ |G.eig i|).card ≤ T →
        ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
          ∃ c ∈ netList p (G.1, adjTable G),
            (realVec G.1 c - w) ⬝ᵥ (realVec G.1 c - w) ≤ (κ / G.1) ^ 2 := by
  have hθ'r : (0 : ℝ) < θ' := by exact_mod_cast hθ'
  have hθr : (θ' : ℝ) < θ := by exact_mod_cast hθ
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  set h₀ : ℝ := (θ : ℝ) ^ 2 with hh₀
  set ℓ₀ : ℝ := (θ' : ℝ) ^ 2 with hℓ₀
  have hℓ0 : 0 < ℓ₀ := by positivity
  have hℓh : ℓ₀ < h₀ := pow_lt_pow_left₀ hθr hθ'r.le (by norm_num)
  obtain ⟨p, hpb, hpT, hK0, hp⟩ := exists_params hℓ0 hℓh hκr false T
  refine ⟨p, ?_⟩
  rintro G ⟨d, hreg⟩ hcount w hw1 hw
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · exact ⟨[], List.mem_cons_self, dist_empty_le G hn w κ⟩
  have hdeg : deg G.1 (adjTable G) = d := by
    rw [deg_graph G hn]
    exact hreg _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hw0 : w = 0 := eq_zero_of_inEigSpan G hw fun i ↦ by
      rw [eig_eq_zero_of_deg_zero G hreg i, abs_zero, not_le]
      linarith
    subst hw0
    exact ⟨[], List.mem_cons_self, dist_zero_le G.1 κ⟩
  set m := p.c * (p.a + 2 * G.1.size) with hm
  have hexpo : expo p G.1 = 2 * m := by simp [expo, hpb, hm]
  set φ : Fin G.1 → ℝ := fun i ↦ (G.eig i ^ 2) ^ m with hφ
  have hP : ∀ i x, coeff G.normAdj_isHermitian i (filt p G d *ᵥ x) =
      φ i * coeff G.normAdj_isHermitian i x := by
    intro i x
    rw [filt_eq, abs_base p hpb G hreg, hexpo]
    rw [coeff_pow_mulVec _ (fun y ↦ coeff_mulVec _ i y) (2 * m) x]
    simp only [φ, Graph.eig, ← pow_mul]
  have hb : ∀ i, 0 ≤ G.eig i ^ 2 ∧ G.eig i ^ 2 ≤ 1 := fun i ↦
    ⟨sq_nonneg _, by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (G.abs_eig_le_one i)⟩
  obtain ⟨c, hc, hdist⟩ := near_of_filter p G hdeg hd hK0 hn φ hP
    (Finset.univ.filter fun i ↦ θ' ≤ |G.eig i|) (hpT ▸ hcount) (ℓ := ℓ₀ ^ m) (h := h₀ ^ m)
    (pow_pos (pow_pos (hθ'r.trans hθr) 2) m)
    (fun i ↦ by
      rw [abs_of_nonneg (pow_nonneg (hb i).1 _)]
      exact pow_le_one₀ (hb i).1 (hb i).2)
    (fun i hi ↦ by
      have hi' : |G.eig i| < θ' := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
        exact hi
      rw [abs_of_nonneg (pow_nonneg (hb i).1 _)]
      refine pow_le_pow_left₀ (hb i).1 ?_ m
      rw [hℓ₀, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hi'.le 2)
    w hw1
    (fun i hi ↦ by
      have hle : (θ : ℝ) ≤ |G.eig i| := by
        by_contra hcon
        exact hi (hw i hcon)
      refine ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; linarith, ?_⟩
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [hh₀, ← sq_abs (G.eig i)]
      exact pow_le_pow_left₀ (hθ'r.trans hθr).le hle 2)
    (hp G.1 hn).1
  refine ⟨c, hc, hdist.trans ?_⟩
  rw [hpT]
  exact (hp G.1 hn).2

end Net

end BHSV25
