module

public import BHSV25.Planted.Stop
public import BHSV25.Net.StopCorrect

/-!
# Theorem 7.12: the analysis of the algorithm that finds the number of rounds

The guarantee of `BHSV25.Planted.planAlgU` on one good coloring (`BHSV25.Planted.planted_good`),
with `a = 2 K + 8`, `θ = 1 / (16 k²)` and the threshold `ψ = 4 θ / 5` at the scale of the average
degree `S / n` of the planted graph:

* **the scale**: the average degree is at most `d` (`BHSV25.Planted.count_true_plant_le`) and, on a
  good coloring of a host with at least `(k (4k + 1))⁴` vertices, at least `d / 2`, as the classes
  carry at most `1/k + 2/(4k + 1) < 1/2` of the weight of the host
  (`BHSV25.Planted.count_true_plant_ge`). So the threshold at the scale `d` is between
  `(2 θ / 5)^E` and `(4 θ / 5)^E`;
* **the noise**: at most `numT k t` eigenvalues of `A_G / d` are at least `θ / 3` in absolute value
  (`BHSV25.Planted.card_abs_ge_numT_third`, Lemma 7.16 as for `θ / 2`), and
  `2^(n+1) (θ/3)^E ≤ (2θ/5)^E`;
* **the target**: the eigenvectors with eigenvalues at least `θ` in absolute value, where the
  filter is at least `θ^E`, and `√n (4/5)^E ≤ 2 / K`.

So the stopping round is at most `numT k t`, and the net at the stopping round covers the target
at precision `4 / K` (`BHSV25.Planted.roundsP_le_and_cover`, through
`BHSV25.Net.exists_cand_near_stop`), and Theorem 7.12 on one good coloring holds for any net that
covers the target (`BHSV25.Planted.isColoring_planted_of_net`).
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset Spectral

variable {k : ℕ}

/-! ### The scale -/

/-- The number of ones of a list of bits given by a function is the number of its ones. -/
theorem stopP_count_ofFn {m : ℕ} (f : Fin m → Bool) :
    (List.ofFn f).count true = (univ.filter fun i ↦ f i = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.univ_succ, Finset.filter_cons]
    by_cases h : f 0 = true
    · simp [h, Finset.card_map, Finset.filter_map]
    · simp [h, Finset.card_map, Finset.filter_map]

open Classical in
/-- The number of ones of the adjacency table is the sum of the degrees. -/
theorem count_true_adjTable (G : Graph) : (adjTable G).count true = ∑ x, G.2.degree x := by
  rw [adjTable, stopP_count_ofFn, card_filter]
  rw [← Fintype.sum_equiv finProdFinEquiv
    (fun p : Fin G.1 × Fin G.1 ↦ if G.2.Adj p.1 p.2 then 1 else 0) _ (fun p ↦ by simp)]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← card_filter, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]

open Classical in
/-- The planted graph has average degree at most the degree `d` of the host. -/
theorem count_true_plant_le (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (χ : Fin H.1 → Fin k) : (adjTable (H.plant χ)).count true ≤ d * H.1 := by
  rw [count_true_adjTable]
  calc ∑ x, (H.plant χ).2.degree x ≤ ∑ _x : Fin (H.plant χ).1, d :=
        sum_le_sum fun x _ ↦
          (degree_le_of_adj (G := (H.plant χ).2) (G' := H.2) (fun _ _ h ↦ h.1) x).trans
            (hreg x).le
    _ = d * H.1 := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        exact Nat.mul_comm _ _

/-- `n^(1/4) ≥ k (4 k + 1)` for `n ≥ (k (4 k + 1))⁴`. -/
theorem stopP_qr_ge {n : ℕ} (hn : minN k ≤ n) : (k : ℝ) * (4 * k + 1) ≤ qr n := by
  have h1 : ((k : ℝ) * (4 * k + 1)) ^ 4 ≤ (n : ℝ) := by
    have : ((k * (4 * k + 1)) ^ 4 : ℕ) ≤ n := hn
    exact_mod_cast this
  have h2 : qr n ^ 4 = n := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, qr_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← h2] at h1
  exact le_of_pow_le_pow_left₀ (by norm_num) (Real.sqrt_nonneg _) h1

/-- The weight inside the classes: `∑_a edg(a, a) = ∑_{χ x = χ y} X_xy`. -/
theorem stopP_sum_edg_self {n : ℕ} (X : Fin n → Fin n → ℝ) (χ : Fin n → Fin k) :
    ∑ a, edg X χ a a = ∑ x, ∑ y, (if χ x = χ y then X x y else 0) := by
  have hsum : ∀ x y : Fin n, ∑ a : Fin k, (if χ x = a ∧ χ y = a then X x y else 0) =
      if χ x = χ y then X x y else 0 := by
    intro x y
    rw [Finset.sum_eq_single (χ x)]
    · by_cases h : χ x = χ y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb
      exact ite_eq_right fun h ↦ hb h.1.symm
    · simp
  simp only [edg]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun y _ ↦ hsum x y

/-- `1 / k + 2 / (4 k + 1) ≤ 1 / 2` for `k ≥ 3`. -/
theorem stopP_frac_le (hk : 3 ≤ k) {n q : ℝ} (hn : 0 ≤ n) (hq : (k : ℝ) * (4 * k + 1) ≤ q) :
    (k : ℝ) * (n / (k : ℝ) ^ 2 + 2 * n / q) ≤ n / 2 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have e : (k : ℝ) * (n / (k : ℝ) ^ 2 + 2 * n / q) = n / k + 2 * k * n / q := by
    field_simp
  rw [e]
  have h1 : 2 * (k : ℝ) * n / q ≤ 2 * n / (4 * k + 1) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * n)]
  have h2 : (n : ℝ) / k + 2 * n / (4 * k + 1) ≤ n / 2 := by
    rw [div_add_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ 4 * k ^ 2 - 11 * k - 2 := by nlinarith
    nlinarith [mul_nonneg hn this]
  linarith

open Classical in
/-- **The scale**: on a good coloring of a host with at least `(k (4k + 1))⁴` vertices, the
planted graph has average degree at least `d / 2`. -/
theorem count_true_plant_ge (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (hd : 1 ≤ d) (χ : Fin H.1 → Fin k) (hn : minN k ≤ H.1)
    (hgood : Good (fun x y ↦ H.normAdj x y) χ) :
    (d : ℝ) * H.1 / 2 ≤ (adjTable (H.plant χ)).count true := by
  have hk0 : 0 < k := by omega
  have hd0 : d ≠ 0 := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set X : Fin H.1 → Fin H.1 → ℝ := fun x y ↦ H.normAdj x y with hXdef
  have hrow : ∀ x, ∑ y, X x y = 1 := fun x ↦ Alg.sum_normAdj hreg hd0 x
  -- the number of ones as the weight of `A_G / d`
  have hS : (((adjTable (H.plant χ)).count true : ℕ) : ℝ) =
      d * ∑ x : Fin (H.plant χ).1, ∑ y, adjDiv (H.plant χ) d x y := by
    rw [count_true_adjTable]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [adjDiv]
    rw [sum_adj_ite]
    field_simp
  have hplant : ∑ x : Fin (H.plant χ).1, ∑ y, adjDiv (H.plant χ) d x y =
      ∑ x : Fin H.1, ∑ y : Fin H.1, (X x y - if χ x = χ y then X x y else 0) :=
    sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by
      rw [adjDiv_plant H hreg χ x y]
      by_cases h : χ x = χ y <;> simp [h, hXdef]
  have hsplit : ∑ x : Fin H.1, ∑ y : Fin H.1, (X x y - if χ x = χ y then X x y else 0) =
      H.1 - ∑ a, edg X χ a a := by
    rw [stopP_sum_edg_self]
    simp only [sum_sub_distrib, hrow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  -- the weight inside the classes
  obtain ⟨-, hg2, -⟩ := hgood
  have hq := stopP_qr_ge hn
  have hin : ∑ a, edg X χ a a ≤ (k : ℝ) * (H.1 / (k : ℝ) ^ 2 + 2 * H.1 / qr H.1) := by
    calc ∑ a, edg X χ a a ≤ ∑ _a : Fin k, ((H.1 : ℝ) / (k : ℝ) ^ 2 + 2 * H.1 / qr H.1) :=
          sum_le_sum fun a _ ↦ by linarith [(abs_lt.1 (hg2 a a)).2]
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfrac := stopP_frac_le hk (Nat.cast_nonneg H.1) hq
  rw [hS, hplant, hsplit]
  have h1 : (H.1 : ℝ) / 2 ≤ H.1 - ∑ a, edg X χ a a := by linarith
  calc (d : ℝ) * H.1 / 2 = d * (H.1 / 2) := by ring
    _ ≤ d * (H.1 - ∑ a, edg X χ a a) := mul_le_mul_of_nonneg_left h1 hdR.le

/-! ### The noise -/

open Classical in
/-- **The eigenvalues above the noise** (Lemma 7.16 with Corollary 4.2): at most `numT k t`
eigenvalues of `A_G / d` are at least `θ / 3 = 1 / (48 k²)` in absolute value. -/
theorem card_abs_ge_numT_third (hk : 0 < k) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) {t : ℕ}
    (hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ t) (χ : Fin H.1 → Fin k) :
    (univ.filter fun i ↦ 1 / (16 * (k : ℝ) ^ 2) / 3 ≤
        |(adjDiv_isHermitian (H.plant χ) d).eigenvalues i|).card ≤ numT k t := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set l := lamP k with hl
  have hl0 : 0 < l := lamP_pos hk
  have hl1 : l < 1 := by
    rw [hl, lamP, div_lt_one (by positivity)]
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 4]
  -- the bottom of the host's spectrum
  set r₂ : ℝ := 1 / (64 * (k : ℝ) ^ 2) with hr₂
  have hneg := H.card_eig_le_neg_le hl0.le hl1 hl0 hl1
  have hsqrt : Real.sqrt (l * (1 - l) + l) ≤ r₂ := by
    rw [Real.sqrt_le_left (by positivity)]
    have : l * (1 - l) ≤ l := by nlinarith
    have e : r₂ ^ 2 = 2 * l := by rw [hr₂, hl, lamP]; field_simp; ring
    rw [e]
    linarith
  have hsub : (univ.filter fun i ↦ H.eig i ≤ -r₂) ⊆
      univ.filter fun i ↦ H.eig i ≤ -Real.sqrt (l * (1 - l) + l) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans (by linarith)⟩
  have ht₂ : (univ.filter fun i ↦ H.eig i ≤ -r₂).card ≤ t * (2 ^ 26 * k ^ 8) := by
    have h1 : l ^ 2 * ((univ.filter fun i ↦ H.eig i ≤ -r₂).card : ℝ) ≤ t := by
      refine le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hsub)
        (sq_nonneg l)) (hneg.trans ?_)
      exact_mod_cast hrank
    have e : l ^ 2 = 1 / (2 ^ 26 * (k : ℝ) ^ 8) := by rw [hl, lamP]; field_simp; ring
    rw [e, one_div, inv_mul_le_iff₀ (by positivity)] at h1
    have : ((univ.filter fun i ↦ H.eig i ≤ -r₂).card : ℝ) ≤ t * (2 ^ 26 * k ^ 8) := by
      linarith
    exact_mod_cast this
  have hmain := card_abs_ge_plant_le H hreg χ (r₁ := l) (r₂ := r₂) hrank ht₂
  refine le_trans (card_le_card fun i hi ↦ ?_) hmain
  rw [mem_filter] at hi ⊢
  refine ⟨hi.1, le_trans ?_ hi.2⟩
  have e : 1 / (16 * (k : ℝ) ^ 2) / 3 = 1 / (64 * (k : ℝ) ^ 2) + 1 / (192 * (k : ℝ) ^ 2) := by
    field_simp; ring
  rw [e, hr₂]
  have : l ≤ 1 / (192 * (k : ℝ) ^ 2) := by
    rw [hl, lamP, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 2]
  linarith

/-! ### The number of rounds on a graph -/

/-- The number of rounds on a graph: the stopping round of the greedy selection on the powers of
the adjacency matrix. -/
theorem stopP_roundsP_graph (k K a : ℕ) (G : Graph) :
    roundsP (k, K, a) (G.1, adjTable G) =
      Net.stopZ G.1 (Net.gramRows G.1 (Net.powL G.1
        (Net.baseMat false G.1 (Net.deg G.1 (adjTable G)) (adjTable G)) (2 * (a * G.1))))
        (((20 * k ^ 2 * G.1) ^ (2 * (2 * (a * G.1))) : ℕ) : ℤ)
        ((((adjTable G).count true) ^ (2 * (2 * (a * G.1))) : ℕ) : ℤ) := by
  simp only [roundsP, Net.filtQ, Alg.numV_graph, Net.numV_graph]

/-- The number of rounds on a graph without vertices is `0`. -/
theorem stopP_roundsP_zero (k K a : ℕ) (G : Graph) (hn : G.1 = 0) :
    roundsP (k, K, a) (G.1, adjTable G) = 0 := by
  rw [stopP_roundsP_graph, Net.stopZ, hn, List.range_zero, List.countP_nil]

/-- The stopping round of a table of zeros, for `Y = 0`, is `0`. -/
theorem stopP_stopZ_zero {n : ℕ} (Q : List (List ℤ)) (hQ : Q.length ≤ n)
    (hQ0 : ∀ a u, Cslib.rowEntry Q a u = 0) {X : ℤ} (hX : 0 ≤ X) :
    Net.stopZ n (Net.gramRows n Q) X 0 = 0 := by
  have hcol : ∀ v, Net.colZ n Q v = 0 := fun v ↦ funext fun u ↦ by simp [Net.colZ, hQ0]
  have hok : ∀ s, Net.okZ n (Net.gramRows n Q) X 0 (Net.selOf n s (Net.gramRows n Q)) = true := by
    intro s
    rcases hX.lt_or_eq with hX | hX
    · rw [Net.okZ_iff _ (Net.colZ n Q) (Net.rowEntry_gramRows Q hQ) hX]
      intro v _
      have h0 : Net.resid (Net.colsL (Net.colZ n Q) (Net.selOf n s (Net.gramRows n Q)))
          (Net.colZ n Q v) = 0 := by
        rw [hcol v]
        simpa using Net.resid_smul
          (f := Net.colsL (Net.colZ n Q) (Net.selOf n s (Net.gramRows n Q))) 0 0
      rw [h0]
      simp
    · subst hX
      simp [Net.okZ]
  simp [Net.stopZ, hok]

/-! ### The net at the stopping round -/

/-- The filter `d^(-2m) A^(2m)` multiplies the `i`-th coefficient in the eigenbasis of `A_G / d`
by `(μᵢ²)^m`. -/
theorem stopP_hP (G : Graph) (d : ℝ) (m : ℕ) (i : Fin G.1) (x : Fin G.1 → ℝ) :
    coeff (adjDiv_isHermitian G d) i ((((d⁻¹) ^ (2 * m)) • Matrix.of fun u v : Fin G.1 ↦
      (Cslib.rowEntry (Net.powL G.1 (Net.baseMat false G.1 (Net.deg G.1 (adjTable G))
        (adjTable G)) (2 * m)) u v : ℝ)) *ᵥ x) =
      ((adjDiv_isHermitian G d).eigenvalues i ^ 2) ^ m * coeff (adjDiv_isHermitian G d) i x := by
  rw [filter_eq_smul, adjDiv_base, Net.coeff_pow_mulVec _ (fun y ↦ coeff_mulVec _ i y)
    (2 * m) x]
  simp only [← pow_mul]

/-- **The noise is below the threshold**: `((2^(r+1) - 1) (θ₃²)^m)² D^(4m) ≤ d^(-4m) S^(4m)`
when `S / d ≥ (6/5) θ₃ D` and `m ≥ 2 (r + 1)`. -/
theorem stopP_noise {r m : ℕ} (hrm : 2 * (r + 1) ≤ m) {θ₃ D S d : ℝ} (hθ₃ : 0 ≤ θ₃)
    (hD : 0 ≤ D) (hd : 0 < d) (hS : 6 / 5 * (θ₃ * D) * d ≤ S) :
    ((2 ^ (r + 1) - 1) * (θ₃ ^ 2) ^ m) ^ 2 * D ^ (2 * (2 * m)) ≤
      ((d⁻¹) ^ (2 * m)) ^ 2 * S ^ (2 * (2 * m)) := by
  have hb : 0 ≤ θ₃ * D := mul_nonneg hθ₃ hD
  have hs : 6 / 5 * (θ₃ * D) ≤ S / d := by rw [le_div_iff₀ hd]; linarith
  have h65 : (2 : ℝ) ^ (r + 1) ≤ (6 / 5) ^ (2 * m) := by
    calc (2 : ℝ) ^ (r + 1) ≤ ((6 / 5) ^ 4) ^ (r + 1) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (6 / 5) ^ (4 * (r + 1)) := by rw [← pow_mul]
      _ ≤ (6 / 5) ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hx1 : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hx : (0 : ℝ) ≤ 2 ^ (r + 1) - 1 := by linarith
  have key : (2 ^ (r + 1) - 1) * (θ₃ * D) ^ (2 * m) ≤ (S / d) ^ (2 * m) := by
    calc (2 ^ (r + 1) - 1) * (θ₃ * D) ^ (2 * m) ≤ (6 / 5) ^ (2 * m) * (θ₃ * D) ^ (2 * m) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb _)
      _ = (6 / 5 * (θ₃ * D)) ^ (2 * m) := by ring
      _ ≤ (S / d) ^ (2 * m) := pow_le_pow_left₀ (by positivity) hs _
  have e1 : ((2 ^ (r + 1) - 1) * (θ₃ ^ 2) ^ m) ^ 2 * D ^ (2 * (2 * m)) =
      ((2 ^ (r + 1) - 1) * (θ₃ * D) ^ (2 * m)) ^ 2 := by ring
  have e2 : ((d⁻¹) ^ (2 * m)) ^ 2 * S ^ (2 * (2 * m)) = ((S / d) ^ (2 * m)) ^ 2 := by
    rw [div_eq_mul_inv]; ring
  rw [e1, e2]
  exact pow_le_pow_left₀ (mul_nonneg hx (pow_nonneg hb _)) key 2

/-- **The threshold is below the target's filter**: `d^(-4m) S^(4m) ≤ (ψ^(2m))² D^(4m)` when
`S ≤ d ψ D`. -/
theorem stopP_target {m : ℕ} {ψ D S d : ℝ} (hd : 0 < d) (hS0 : 0 ≤ S) (hS : S ≤ d * (ψ * D)) :
    ((d⁻¹) ^ (2 * m)) ^ 2 * S ^ (2 * (2 * m)) ≤ (ψ ^ (2 * m)) ^ 2 * D ^ (2 * (2 * m)) := by
  have hs : S / d ≤ ψ * D := by rw [div_le_iff₀ hd]; linarith
  have e1 : ((d⁻¹) ^ (2 * m)) ^ 2 * S ^ (2 * (2 * m)) = ((S / d) ^ (2 * m)) ^ 2 := by
    rw [div_eq_mul_inv]; ring
  have e2 : (ψ ^ (2 * m)) ^ 2 * D ^ (2 * (2 * m)) = ((ψ * D) ^ (2 * m)) ^ 2 := by ring
  rw [e1, e2]
  exact pow_le_pow_left₀ (pow_nonneg (by positivity) _)
    (pow_le_pow_left₀ (by positivity) hs _) 2

/-- **The error of the filter**: `√n (4/5)^(2 (2K + 8) n) ≤ 2 / K`. -/
theorem stopP_err {n K : ℕ} (hn : 0 < n) (hK : 0 < K) :
    Real.sqrt n * (4 / 5 : ℝ) ^ (2 * ((2 * K + 8) * n)) ≤ 2 / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (4 / 5 : ℝ) ^ (2 * ((2 * K + 8) * n)) ≤ (1 / 2) ^ (n + K + 3) := by
    calc (4 / 5 : ℝ) ^ (2 * ((2 * K + 8) * n)) = ((4 / 5) ^ 4) ^ ((K + 4) * n) := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ (1 / 2) ^ ((K + 4) * n) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (1 / 2) ^ (n + K + 3) := pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (by nlinarith)
  have h2 : Real.sqrt n ≤ 2 ^ n := by
    have h3 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have h4 : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have h4 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
  calc Real.sqrt n * (4 / 5 : ℝ) ^ (2 * ((2 * K + 8) * n)) ≤ 2 ^ n * (1 / 2) ^ (n + K + 3) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = 1 / (8 * 2 ^ K) := by
        rw [_root_.one_div_pow, pow_add, pow_add]
        field_simp
        ring
    _ ≤ 2 / K := by
        rw [div_le_div_iff₀ (by positivity) hK']
        nlinarith

/-- The grid's error: `2 √T / N ≤ 2 / K` for `N = (⌊√T⌋ + 1) K`. -/
theorem stopP_grid (T : ℕ) {K : ℕ} (hK : 0 < K) :
    2 * Real.sqrt T / ((Nat.sqrt T + 1) * K : ℕ) ≤ 2 / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : Real.sqrt T ≤ (Nat.sqrt T + 1 : ℕ) := by
    push_cast
    exact (Real.real_sqrt_lt_nat_sqrt_succ).le
  rw [Nat.cast_mul, div_le_div_iff₀ (by positivity) hK']
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * K)
  nlinarith

/-- **The net at the stopping round**, on a graph `G` with average degree between `d / 2` and
`d` and at most `T₀` eigenvalues of `A_G / d` at least `θ / 3` in absolute value: the stopping
round is at most `T₀`, and with a budget `B ≥ (3 + 12 K)^T` the net covers the eigenvectors of
`A_G / d` with eigenvalues at least `θ` in absolute value at precision `4 / K`. -/
theorem roundsP_le_and_cover (G : Graph) {d : ℝ} (hd : 0 < d) (hk : 0 < k) {K : ℕ} (hK : 0 < K)
    (hlo : d * G.1 / 2 ≤ (adjTable G).count true) (hhi : ((adjTable G).count true : ℝ) ≤ d * G.1)
    {T₀ : ℕ} (hcard : (univ.filter fun i ↦ 1 / (16 * (k : ℝ) ^ 2) / 3 ≤
      |(adjDiv_isHermitian G d).eigenvalues i|).card ≤ T₀) :
    roundsP (k, K, 2 * K + 8) (G.1, adjTable G) ≤ T₀ ∧
    ∀ B : ℕ, (3 + 12 * K) ^ roundsP (k, K, 2 * K + 8) (G.1, adjTable G) ≤ B →
      ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 →
        InEigSpan (adjDiv_isHermitian G d) (fun μ ↦ 1 / (16 * (k : ℝ) ^ 2) ≤ |μ|) w →
        ∃ u ∈ Alg.expNet (2 * K + 8, roundsP (k, K, 2 * K + 8) (G.1, adjTable G),
            (Nat.sqrt (roundsP (k, K, 2 * K + 8) (G.1, adjTable G)) + 1) * K, B)
            (G.1, adjTable G),
          (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ (4 / K) ^ 2 := by
  have hBB : ∀ T B : ℕ, (3 + 12 * K) ^ T ≤ B → Net.BallBudget ((Nat.sqrt T + 1) * K) T B :=
    fun T B hB i hi ↦ (Net.ballBudget_sqrt T K i hi).trans hB
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · -- no vertices
    refine ⟨by rw [stopP_roundsP_zero k K _ G hn0]; omega, fun B hB w _ _ ↦ ?_⟩
    rw [Alg.expNet, Alg.numV_graph]
    obtain ⟨c, hc, -⟩ := Net.exists_zero_mem_netGS false (2 * ((2 * K + 8) * G.1)) _ _ B G
      (hBB _ B hB)
    refine ⟨c, hc, ?_⟩
    have : (Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w) = 0 := by
      simp only [dotProduct]
      exact Finset.sum_eq_zero fun i _ ↦ absurd i.2 (by omega)
    rw [this]
    positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [stopP_roundsP_graph]
  set hA := adjDiv_isHermitian G d with hAdef
  set m := (2 * K + 8) * G.1 with hm
  have hm10 : 10 * G.1 ≤ m := by rw [hm]; nlinarith
  set Q := Net.powL G.1 (Net.baseMat false G.1 (Net.deg G.1 (adjTable G)) (adjTable G))
    (2 * m) with hQdef
  set S : ℕ := (adjTable G).count true with hSdef
  have hQ : Q.length ≤ G.1 := (Net.length_powL _ _ _).le
  have hsym := Net.rowEntry_powL_symm false G (Net.deg G.1 (adjTable G)) (2 * m)
  have hc : 0 < (d⁻¹) ^ (2 * m) := by positivity
  set φ : Fin G.1 → ℝ := fun i ↦ (hA.eigenvalues i ^ 2) ^ m with hφ
  have hP := stopP_hP G d m
  set θ : ℝ := 1 / (16 * (k : ℝ) ^ 2) with hθ
  have hθ0 : 0 < θ := by positivity
  set R := univ.filter fun i ↦ θ / 3 ≤ |hA.eigenvalues i| with hR
  have hRn : R.card ≤ G.1 := (card_le_univ R).trans (by simp)
  have hφl : ∀ i ∉ R, |φ i| ≤ ((θ / 3) ^ 2) ^ m := by
    intro i hi
    have hi' : |hA.eigenvalues i| < θ / 3 := by
      rw [hR, mem_filter] at hi
      push Not at hi
      exact hi (mem_univ _)
    rw [hφ, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
    refine pow_le_pow_left₀ (sq_nonneg _) ?_ m
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hi'.le 2
  have hX : (0 : ℤ) < (((20 * k ^ 2 * G.1) ^ (2 * (2 * m)) : ℕ) : ℤ) := by positivity
  -- the noise is below the threshold
  have hτ : ((2 ^ (R.card + 1) - 1) * ((θ / 3) ^ 2) ^ m) ^ 2 *
      ((((20 * k ^ 2 * G.1) ^ (2 * (2 * m)) : ℕ) : ℤ) : ℝ) ≤
      ((d⁻¹) ^ (2 * m)) ^ 2 * (((S ^ (2 * (2 * m)) : ℕ) : ℤ) : ℝ) := by
    push_cast
    refine stopP_noise (by omega) (by positivity) (by positivity) hd ?_
    have e : 6 / 5 * (θ / 3 * (20 * (k : ℝ) ^ 2 * G.1)) * d = d * G.1 / 2 := by
      rw [hθ]; field_simp; ring
    rw [e]
    exact hlo
  obtain ⟨hle, -⟩ := Net.stopZ_le_and_resid hA Q hQ hsym hc φ hP R (by positivity) hφl hX hτ
  refine ⟨hle.trans hcard, fun B hB w hw1 hw ↦ ?_⟩
  -- the threshold is below the target's filter
  set ψ : ℝ := 1 / (20 * (k : ℝ) ^ 2) with hψ
  have hρY : ((d⁻¹) ^ (2 * m)) ^ 2 * (((S ^ (2 * (2 * m)) : ℕ) : ℤ) : ℝ) ≤
      (ψ ^ (2 * m)) ^ 2 * ((((20 * k ^ 2 * G.1) ^ (2 * (2 * m)) : ℕ) : ℤ) : ℝ) := by
    push_cast
    refine stopP_target hd (Nat.cast_nonneg _) ?_
    have e : ψ * (20 * (k : ℝ) ^ 2 * G.1) = G.1 := by rw [hψ]; field_simp
    rw [e]
    exact hhi
  have hw' : ∀ i, coeff hA i w ≠ 0 → (θ ^ 2) ^ m ≤ φ i := by
    intro i hi
    have hle : θ ≤ |hA.eigenvalues i| := by
      by_contra hcon
      exact hi (hw i hcon)
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [← sq_abs (hA.eigenvalues i)]
    exact pow_le_pow_left₀ hθ0.le hle 2
  set T := Net.stopZ G.1 (Net.gramRows G.1 Q) (((20 * k ^ 2 * G.1) ^ (2 * (2 * m)) : ℕ) : ℤ)
    ((S ^ (2 * (2 * m)) : ℕ) : ℤ) with hT
  have hN : 0 < (Nat.sqrt T + 1) * K := Nat.mul_pos (Nat.succ_pos _) hK
  obtain ⟨-, cand, hcand, hdist⟩ := Net.exists_cand_near_stop hA Q hQ hsym hc φ hP R
    (by positivity) hφl hX hτ (ρ := ψ ^ (2 * m)) (by positivity) hρY (h := (θ ^ 2) ^ m)
    (by positivity) w hw1 hw' hN (hBB _ B hB)
  rw [Alg.expNet, Alg.numV_graph, Net.netGS, Net.gsData_graph']
  refine ⟨cand, hcand, ?_⟩
  -- the error
  have herr : Real.sqrt G.1 * ψ ^ (2 * m) / (θ ^ 2) ^ m ≤ 2 / K := by
    have hr : ψ / θ = 4 / 5 := by rw [hψ, hθ]; field_simp; norm_num
    rw [← pow_mul, mul_div_assoc, ← div_pow, hr, hm]
    exact stopP_err hn hK
  have h1 : Real.sqrt ((Net.ratVec G.1 cand - w) ⬝ᵥ (Net.ratVec G.1 cand - w)) ≤ 4 / K := by
    refine hdist.trans ?_
    have : (4 : ℝ) / K = 2 / K + 2 / K := by ring
    rw [this]
    exact add_le_add (stopP_grid T hK) herr
  have h2 := Real.sq_sqrt (Net.dot_self_nonneg (Net.ratVec G.1 cand - w))
  have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [h2] at h3
  exact h3

/-! ### One good coloring -/

open Classical in
/-- **The algorithm on one good coloring**: for `k ≥ 3`, a `d`-regular host with `d ≥ 1`, at
least `(k (4k + 1))⁴` vertices and at most `t` eigenvalues at least `λ₀`, and a good coloring,
the stopping round is at most `numT k t`, and with budgets `B₁ ≥ (3 + 12 K)^T` and
`B₂ ≥ (B₁ + 1)^k, (2 K' + 1)^(k²)` the output is a
`(k, B / (d + 1)^(1/4) + 65536 k⁴ / K²)`-coloring. -/
theorem planted_good (hk : 3 ≤ k) {K : ℕ} (hK : 0 < K) (t : ℕ) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) (hd : 1 ≤ d)
    (hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ t) (χ : Fin H.1 → Fin k)
    (hn : minN k ≤ H.1) (hgood : Good (fun x y ↦ H.normAdj x y) χ) :
    roundsP (k, K, 2 * K + 8) ((H.plant χ).1, adjTable (H.plant χ)) ≤ numT k t ∧
    ∀ B₁ B₂ : ℕ,
      (3 + 12 * K) ^ roundsP (k, K, 2 * K + 8) ((H.plant χ).1, adjTable (H.plant χ)) ≤ B₁ →
      (B₁ + 1) ^ k ≤ B₂ → (2 * gridK k + 1) ^ (k * k) ≤ B₂ →
      (H.plant χ).IsColoring k
        (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2)
        (planAlgU (k, K, 2 * K + 8) ((B₁, B₂), ((H.plant χ).1, adjTable (H.plant χ)))) := by
  have hk0 : 0 < k := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlo : (d : ℝ) * (H.plant χ).1 / 2 ≤ (adjTable (H.plant χ)).count true :=
    count_true_plant_ge hk H hreg hd χ hn hgood
  have hhi : ((adjTable (H.plant χ)).count true : ℝ) ≤ d * (H.plant χ).1 := by
    have := count_true_plant_le H hreg χ
    exact_mod_cast this
  obtain ⟨hle, hcov⟩ := roundsP_le_and_cover (H.plant χ) hdR hk0 hK hlo hhi
    (card_abs_ge_numT_third hk0 H hreg hrank χ)
  refine ⟨hle, fun B₁ B₂ hB₁ hB₂ hB₃ ↦ ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = roundsP (k, K, 2 * K + 8) ((H.plant χ).1, adjTable (H.plant χ)) :=
    ⟨_, rfl⟩
  have hU := (Nat.pow_le_pow_left (Alg.length_expNet_le (2 * K + 8, T, (Nat.sqrt T + 1) * K, B₁)
    ((H.plant χ).1, adjTable (H.plant χ))) k).trans hB₂
  rw [hT] at hU
  exact isColoring_planted_of_net hk hK H hreg hd χ hn hgood _ (hcov B₁ hB₁) hU hB₃

/-! ### Graphs without edges, and the output -/

/-- On a graph without edges, the number of rounds is `0`. -/
theorem roundsP_eq_zero (p : PPar) (hp : 0 < p.2.2) (G : Graph)
    (hG : (adjTable G).count true = 0) : roundsP p (G.1, adjTable G) = 0 := by
  obtain ⟨k, K, a⟩ := p
  rw [stopP_roundsP_graph]
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · rw [Net.stopZ, hn, List.range_zero, List.countP_nil]
  have ha : 0 < a := hp
  have hE : 0 < 2 * (2 * (a * G.1)) := by positivity
  rw [hG, zero_pow hE.ne', Nat.cast_zero]
  refine stopP_stopZ_zero _ (by rw [Net.length_powL]) (fun i u ↦ ?_) (by positivity)
  -- the table has no ones
  have hnot : true ∉ adjTable G := List.count_eq_zero.1 hG
  have hfalse : ∀ j, (adjTable G).getD j false = false := by
    intro j
    by_cases hj : j < (adjTable G).length
    · rw [List.getD_eq_getElem _ _ hj]
      have hmem := List.getElem_mem hj
      cases h : (adjTable G)[j] with
      | true => exact absurd (h ▸ hmem) hnot
      | false => rfl
    · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
  have hM : Net.toMat G.1 (Net.baseMat false G.1 (Net.deg G.1 (adjTable G)) (adjTable G)) = 0 := by
    rw [Net.toMat_baseMat]
    funext u v
    simp only [Net.entry, Net.adjB, hfalse]
    simp
  by_cases h : i < G.1 ∧ u < G.1
  · have := congrFun (congrFun (Net.toMat_powL G.1
      (Net.baseMat false G.1 (Net.deg G.1 (adjTable G)) (adjTable G)) (2 * (a * G.1)))
      ⟨i, h.1⟩) ⟨u, h.2⟩
    rw [hM, zero_pow (by positivity), Matrix.zero_apply] at this
    exact this
  · exact Net.rowEntry_powL_of_le _ _ _ (by omega)

/-- **The output is always a partial coloring**, for budgets `B₂ ≥ (B₁ + 1)^k, (2 K' + 1)^(k²)`. -/
theorem isPartialColoring_planAlgU (hk : 0 < k) (K a B₁ B₂ : ℕ) (h1 : (B₁ + 1) ^ k ≤ B₂)
    (h2 : (2 * gridK k + 1) ^ (k * k) ≤ B₂) (G : Graph) :
    G.IsPartialColoring k (planAlgU (k, K, a) ((B₁, B₂), (G.1, adjTable G))) := by
  have hU := Nat.pow_le_pow_left (Alg.length_expNet_le (a, roundsP (k, K, a) (G.1, adjTable G),
    (Nat.sqrt (roundsP (k, K, a) (G.1, adjTable G)) + 1) * K, B₁) (G.1, adjTable G)) k
  exact (Alg.gridAlg_spec G hk le_rfl _ _ _ _ (hU.trans h1) h2).1

end Planted

end BHSV25
