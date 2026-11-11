module

public import BHSV25.Planted.Rank
public import BHSV25.Planted.Conc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 7.12 on one good coloring

The deterministic part of [BHSV25, Theorem 7.12] (`BHSV25.Planted.isColoring_planted_of_net`):
for `k ≥ 3`, a `d`-regular host `H` with `d ≥ 1`, and a good coloring `χ`
(`BHSV25.Planted.Good`) of `n ≥ (k (4k + 1))⁴` vertices, the grid clustering of Theorem 7.1
(`BHSV25.Alg.gridAlg`) of any list `U` that covers the eigenvectors of `A_G / d` with eigenvalues
at least `1 / (16 k²)` in absolute value at precision `4 / K` outputs a
`(k, B / (d + 1)^(1/4) + 65536 k⁴ / K²)`-coloring of the planted graph `G`, with
`B = 5 · 2²¹ k¹¹`. The net of Theorem 7.1 with the parameters `BHSV25.Planted.planParams k K t`
covers them when the host has at most `t` eigenvalues at least `λ₀ = 1 / (8192 k⁴)`
(`BHSV25.Planted.exists_good_candidate`, for Theorem 7.17).

The proof is the paper's: Theorem 5.1 for `Q = A_G / d` (`BHSV25.Planted.exists_good_grid`), with
* the parts of at least `n / (2k)` vertices (Lemma 7.13);
* the rows of the model separated by `α = 1 / (2k)`: `M_aa = 0` and `M_ab ≥ 1 / (2k)` for `a ≠ b`
  (Lemma 7.14);
* the dispersions at most `(1 / (k² d) + 3 / n^(1/4)) n` (Lemma 7.15), at most
  `5 n / (d + 1)^(1/4)` as `n ≥ d + 1`;
* at most `T = (k + 1) (t + 2²⁶ k⁸ t)` eigenvalues of `Q` at least `1 / (32 k²)` in absolute value
  (Lemma 7.16, with `r₁ = λ₀` and `r₂ = 1 / (64 k²)`, and Corollary 4.2 for the bottom of the
  host's spectrum);
* a net at precision `4 / K` for `θ = 1 / (16 k²)`, `τ = 2 θ`;

and the rounding of `BHSV25.Planted.numColored_gridAlg_ge`, as the planted coloring is proper.
The paper normalizes by `d' = (k - 1) d / k`, the expected degree; normalizing by `d` keeps
`|xᵀ Q x| ≤ ‖x‖²` exact and changes the model by the factor `(k - 1) / k`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset Spectral

/-! ### The constants -/

/-- The threshold `λ₀ = 1 / (8192 k⁴)` of Theorem 7.12. -/
noncomputable def lamP (k : ℕ) : ℝ := 1 / (8192 * (k : ℝ) ^ 4)

/-- The number of eigenvalues the net covers: `T = (k + 1) (t + 2²⁶ k⁸ t)`. -/
def numT (k t : ℕ) : ℕ := (k + 1) * (t + t * (2 ^ 26 * k ^ 8))

/-- The scale of the grid of centers, `32 k²`. -/
def gridS (k : ℕ) : ℕ := 32 * k ^ 2

/-- The range of the grid of centers, `64 k³ + 1`. -/
def gridK (k : ℕ) : ℕ := 64 * k ^ 3 + 1

/-- The parameters of the algorithm for `k` colors, the precision `4 / K` and `t` eigenvalues. -/
def planParams (k K t : ℕ) : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
  ((k, k, gridS k, gridK k,
      ((3 + 12 * K) ^ numT k t + 1) ^ k + (2 * gridK k + 1) ^ (k * k)),
    (numT k t + 2 + K, numT k t, (Nat.sqrt (numT k t) + 1) * K, (3 + 12 * K) ^ numT k t))

/-- The minimal number of vertices, `(k (4 k + 1))⁴`. -/
def minN (k : ℕ) : ℕ := (k * (4 * k + 1)) ^ 4

/-- The constant `B = 5 · 2²¹ k¹¹` of the error. -/
noncomputable def errB (k : ℕ) : ℝ := 5 * 2 ^ 21 * (k : ℝ) ^ 11

/-! ### The host and the planted graph -/

open Classical in
theorem isWeight_normAdj (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) :
    IsWeight (fun x y ↦ H.normAdj x y) (1 / d) where
  nonneg := H.normAdj_nonneg
  symm := Alg.normAdj_symm (G := H)
  diag x := by rw [H.normAdj_of_isRegularOfDegree hreg]; simp
  rowSum := Alg.sum_normAdj hreg hd
  sqSum x := by
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    simp only [H.normAdj_of_isRegularOfDegree hreg, apply_ite (· ^ 2), zero_pow two_ne_zero,
      sum_adj_ite, hreg x]
    field_simp
    exact le_rfl

variable {k : ℕ}

theorem degree_le_of_adj {V : Type*} [Fintype V] {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : ∀ u v, G.Adj u v → G'.Adj u v) (u : V) :
    G.degree u ≤ G'.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_le_card fun v hv ↦ ?_
  simp only [SimpleGraph.mem_neighborFinset] at hv ⊢
  exact h u v hv

open Classical in
theorem degree_plant_le (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (χ : Fin H.1 → Fin k)
    (u : Fin (H.plant χ).1) : (((H.plant χ).2.degree u : ℕ) : ℝ) ≤ d := by
  have h := degree_le_of_adj (G := (H.plant χ).2) (G' := H.2) (fun _ _ h ↦ h.1) u
  have h2 : H.2.degree u = d := hreg u
  exact_mod_cast h.trans h2.le

section Bridge

variable {n : ℕ} (X : Fin n → Fin n → ℝ) {Q : Matrix (Fin n) (Fin n) ℝ} (χ : Fin n → Fin k)
  (hQ : ∀ u v, Q u v = if χ u = χ v then 0 else X u v)
include hQ

theorem wt_eq_dwt (x : Fin n) (b : Fin k) (hb : χ x ≠ b) : wt Q χ x b = dwt X χ x b := by
  rw [wt, ← sum_ite_part, dwt]
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases hy : χ y = b
  · rw [ite_eq_left hy, ite_eq_left hy, hQ, ite_eq_right]
    rw [hy]; exact hb
  · rw [ite_eq_right hy, ite_eq_right hy]

theorem wt_self (x : Fin n) : wt Q χ x (χ x) = 0 := by
  rw [wt]
  exact sum_eq_zero fun y hy ↦ by rw [hQ, ite_eq_left (mem_part.1 hy).symm]

theorem pmodel_self (a : Fin k) : pmodel Q χ a a = 0 := by
  rw [pmodel, sum_eq_zero fun x hx ↦ by rw [← mem_part.1 hx]; exact wt_self X χ hQ x, zero_div]

theorem disp_self (a : Fin k) : disp Q χ a a = 0 := by
  rw [disp, pmodel_self X χ hQ]
  exact sum_eq_zero fun x hx ↦ by rw [← mem_part.1 hx, wt_self X χ hQ x]; simp

omit hQ in
theorem card_part_eq_cnt (a : Fin k) : ((part χ a).card : ℝ) = cnt χ a := by
  rw [part, card_filter, cnt]
  push_cast
  rfl

theorem sum_wt_eq_edg {a b : Fin k} (hab : a ≠ b) :
    ∑ x ∈ part χ a, wt Q χ x b = edg X χ a b := by
  rw [← sum_ite_part, edg]
  refine sum_congr rfl fun x _ ↦ ?_
  by_cases hx : χ x = a
  · rw [ite_eq_left hx, wt_eq_dwt X χ hQ x b (by rw [hx]; exact hab), dwt]
    exact sum_congr rfl fun y _ ↦ by simp [hx]
  · rw [ite_eq_right hx]
    exact (sum_eq_zero fun y _ ↦ by simp [hx]).symm

theorem pmodel_eq {a b : Fin k} (hab : a ≠ b) : pmodel Q χ a b = edg X χ a b / cnt χ a := by
  rw [pmodel, sum_wt_eq_edg X χ hQ hab, card_part_eq_cnt]

theorem disp_le_dev {a b : Fin k} (hab : a ≠ b) : disp Q χ a b ≤ dev X χ a b := by
  refine (disp_le_sum_sq _ χ a b (1 / k)).trans (le_of_eq ?_)
  rw [← sum_ite_part, dev]
  refine sum_congr rfl fun x _ ↦ ?_
  by_cases hx : χ x = a
  · rw [ite_eq_left hx, ite_eq_left hx, wt_eq_dwt X χ hQ x b (by rw [hx]; exact hab)]
  · rw [ite_eq_right hx, ite_eq_right hx]

end Bridge

/-! ### The spectrum -/

theorem lamP_pos (hk : 0 < k) : 0 < lamP k := by unfold lamP; positivity

open Classical in
/-- **The eigenvalues the net covers** (Lemma 7.16 with Corollary 4.2): at most `numT k t`
eigenvalues of `A_G / d` are at least `1 / (32 k²)` in absolute value. -/
theorem card_abs_ge_numT (hk : 0 < k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    {t : ℕ} (hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ t) (χ : Fin H.1 → Fin k) :
    (univ.filter fun i ↦ 1 / (16 * (k : ℝ) ^ 2) / 2 ≤
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
  have e : 1 / (16 * (k : ℝ) ^ 2) / 2 = 1 / (64 * (k : ℝ) ^ 2) + 1 / (64 * (k : ℝ) ^ 2) := by
    field_simp; ring
  rw [e, hr₂]
  have : l ≤ 1 / (64 * (k : ℝ) ^ 2) := by
    rw [hl, lamP, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 2]
  linarith

/-! ### The arithmetic -/

theorem qr_eq_rpow (n : ℕ) : qr n = (n : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [qr, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- `1 / (k² d) + 3 / n^(1/4) ≤ 5 / (d + 1)^(1/4)` for `n ≥ d + 1 ≥ 2`. -/
theorem disp_const_le (hk : 0 < k) {n d : ℕ} (hd : 1 ≤ d) (hnd : d + 1 ≤ n) :
    1 / ((k : ℝ) ^ 2 * d) + 3 / qr n ≤ 5 / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set r := ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) with hr
  have hr0 : 0 < r := by positivity
  have hrq : r ≤ qr n := by
    rw [qr_eq_rpow, hr]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnd) (by norm_num)
  have hrd : r ≤ (d : ℝ) + 1 := by
    rw [hr]
    calc ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ ((d : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (d : ℝ) + 1 := Real.rpow_one _
  have h1 : 1 / ((k : ℝ) ^ 2 * d) ≤ 2 / r := by
    rw [div_le_div_iff₀ (by positivity) hr0]
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 2]
  have h2 : 3 / qr n ≤ 3 / r := div_le_div_of_nonneg_left (by norm_num) hr0 hrq
  have e : (5 : ℝ) / r = 2 / r + 3 / r := by ring
  rw [e]
  linarith

/-! ### One good coloring -/

open Classical in
/-- **The good candidate** (Theorem B.1, the list version of Theorem 7.12), for any list `U`
that covers the eigenvectors of `A_G / d` with eigenvalues at least `1 / (16 k²)` in absolute
value at precision `4 / K`: some tuple of vectors of `U` and some grid of centers cluster all but
`(B / (d + 1)^(1/4) + 65536 k⁴ / K²) n / 2` vertices as the planted coloring. -/
theorem exists_good_candidate_of_net (hk : 3 ≤ k) {K : ℕ} (hK : 0 < K) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) (hd : 1 ≤ d) (χ : Fin H.1 → Fin k) (hn : minN k ≤ H.1)
    (hgood : Good (fun x y ↦ H.normAdj x y) χ) (U : List (List ℚ))
    (hnet : ∀ w : Fin (H.plant χ).1 → ℝ, w ⬝ᵥ w ≤ 1 →
      InEigSpan (adjDiv_isHermitian (H.plant χ) d) (fun μ ↦ 1 / (16 * (k : ℝ) ^ 2) ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec (H.plant χ).1 u - w) ⬝ᵥ (Net.ratVec (H.plant χ).1 u - w) ≤
        (4 / K) ^ 2) :
    ∃ us : Fin k → List ℚ, (∀ j, us j ∈ U) ∧
      ∃ ts : Fin (k * k) → Fin (2 * gridK k + 1),
        2 * ((univ.filter fun y : Fin (H.plant χ).1 ↦ Alg.clusterIdxC (List.ofFn us)
          (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt (H.plant χ).1)
            (List.ofFn fun j ↦ (ts j : ℕ))) y ≠ (χ y : ℕ)).card : ℝ) ≤
          (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2) * H.1 := by
  have hk0 : 0 < k := by omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set G := H.plant χ with hG
  set n := G.1 with hn_def
  have hnH : n = H.1 := rfl
  have hmin : 1 ≤ minN k := Nat.one_le_pow _ _ (by positivity)
  have hn' : minN k ≤ n := hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hd0 : d ≠ 0 := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnd : d + 1 ≤ n := by
    have := H.2.degree_lt_card_verts ⟨0, by rw [← hnH]; exact hn0⟩
    rw [hreg, Fintype.card_fin] at this
    rw [hnH]
    omega
  set χ' : Fin n → Fin k := χ with hχ'
  set X : Fin n → Fin n → ℝ := fun x y ↦ H.normAdj x y with hXdef
  have hX : IsWeight X (1 / d) := isWeight_normAdj H hreg hd0
  set Q := adjDiv G d with hQdef
  have hQh : Q.IsHermitian := adjDiv_isHermitian G d
  have hQ : ∀ u v, Q u v = if χ' u = χ' v then 0 else X u v := fun u v ↦ adjDiv_plant H hreg χ u v
  have hgood' : Good X χ' := hgood
  have hbd : ∀ x, |x ⬝ᵥ (Q *ᵥ x)| ≤ x ⬝ᵥ x :=
    abs_quad_adjDiv_le G hdR (degree_plant_le H hreg χ)
  -- `n^(1/4) ≥ k (4k + 1)`
  set q := qr n with hqdef
  have hq0 : 0 < q := qr_pos hn0
  have hq : (k : ℝ) * (4 * k + 1) ≤ q := by
    have h1 : ((k : ℝ) * (4 * k + 1)) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hn'
    have h2 : q ^ 4 = n := by
      rw [hqdef, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, qr_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [← h2] at h1
    exact le_of_pow_le_pow_left₀ (by norm_num) hq0.le h1
  obtain ⟨hg1, hg2, hg3⟩ := hgood'
  -- the sizes of the parts
  have hcnt : ∀ a, (n : ℝ) / (2 * k) ≤ cnt χ' a := by
    intro a
    have h := (abs_lt.1 (hg1 a)).1
    have h2k : 2 * (k : ℝ) ≤ q := by nlinarith
    have h2 : (n : ℝ) / q ≤ n / (2 * k) := by
      rw [div_le_div_iff₀ hq0 (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h2k hnR.le]
    have e : (n : ℝ) / k = n / (2 * k) + n / (2 * k) := by field_simp; ring
    linarith
  have hsize : ∀ a, 1 / (2 * (k : ℝ)) * n ≤ (part χ' a).card := by
    intro a
    rw [card_part_eq_cnt χ' a]
    have := hcnt a
    calc 1 / (2 * (k : ℝ)) * n = n / (2 * k) := by ring
      _ ≤ _ := this
  -- the model
  have hmodel : ∀ a b, a ≠ b → 1 / (2 * (k : ℝ)) ≤ pmodel Q χ' a b := by
    intro a b hab
    rw [pmodel_eq X χ' hQ hab]
    have hc0 : 0 < cnt χ' a := lt_of_lt_of_le (by positivity) (hcnt a)
    have hc1 : cnt χ' a ≤ n / k + n / q := by linarith [(abs_lt.1 (hg1 a)).2]
    have he1 : (n : ℝ) / (k : ℝ) ^ 2 - 2 * n / q ≤ edg X χ' a b := by
      linarith [(abs_lt.1 (hg2 a b)).1]
    rw [le_div_iff₀ hc0]
    have key : (n : ℝ) / k + n / q ≤ 2 * k * ((n : ℝ) / (k : ℝ) ^ 2 - 2 * n / q) := by
      have e1 : 2 * (k : ℝ) * ((n : ℝ) / (k : ℝ) ^ 2 - 2 * n / q) = 2 * n / k - 4 * k * n / q := by
        field_simp
        ring
      rw [e1]
      have h3 : (4 * (k : ℝ) + 1) * n / q ≤ n / k := by
        rw [div_le_div_iff₀ hq0 hk']
        nlinarith
      have e2 : (4 * (k : ℝ) + 1) * n / q = 4 * k * n / q + n / q := by ring
      have e3 : 2 * (n : ℝ) / k = n / k + n / k := by ring
      linarith
    calc 1 / (2 * (k : ℝ)) * cnt χ' a ≤ 1 / (2 * k) * (n / k + n / q) :=
          mul_le_mul_of_nonneg_left hc1 (by positivity)
      _ ≤ 1 / (2 * k) * (2 * k * ((n : ℝ) / (k : ℝ) ^ 2 - 2 * n / q)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (n : ℝ) / (k : ℝ) ^ 2 - 2 * n / q := by field_simp
      _ ≤ edg X χ' a b := he1
  have hsep : ∀ a b, a ≠ b → (1 / (2 * (k : ℝ))) ^ 2 ≤
      ∑ j, (pmodel Q χ' a j - pmodel Q χ' b j) ^ 2 := by
    intro a b hab
    have h1 := hmodel a b hab
    have h2 : pmodel Q χ' b b = 0 := pmodel_self X χ' hQ b
    refine le_trans ?_ (single_le_sum (fun j _ ↦ sq_nonneg (pmodel Q χ' a j - pmodel Q χ' b j))
      (mem_univ b))
    rw [h2, sub_zero]
    exact pow_le_pow_left₀ (by positivity) h1 2
  -- the dispersions
  set Δ := 1 / ((k : ℝ) ^ 2 * d) + 3 / q with hΔ
  have hdisp : ∀ a b, disp Q χ' a b ≤ Δ * n := by
    intro a b
    have hΔ0 : 0 ≤ Δ := by positivity
    by_cases hab : a = b
    · subst hab
      rw [disp_self X χ' hQ]
      positivity
    · refine (disp_le_dev X χ' hQ hab).trans ?_
      have h1 := (abs_lt.1 (hg3 a b)).2
      have h2 : (∑ ψ, dev X ψ a b) / (k : ℝ) ^ n ≤ n * (1 / d) / (k : ℝ) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have := sum_dev_le hk0 hX a b
        calc ∑ ψ, dev X ψ a b ≤ n * (1 / d) * ((k : ℝ) ^ n / k / k) := this
          _ = n * (1 / d) / (k : ℝ) ^ 2 * (k : ℝ) ^ n := by field_simp
      have e : Δ * n = n * (1 / d) / (k : ℝ) ^ 2 + 3 * n / q := by
        rw [hΔ]; field_simp
      rw [e]
      linarith
  -- the net
  set θ : ℝ := 1 / (16 * (k : ℝ) ^ 2) with hθ
  have hθ0 : 0 < θ := by positivity
  -- the grid
  have hS : 128 * (k : ℝ) ^ 2 ≤ (1 / (2 * (k : ℝ))) ^ 2 * (gridS k : ℝ) ^ 2 := by
    simp only [gridS]
    push_cast
    field_simp
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 2]
  have hKg : ((gridS k : ℕ) : ℝ) ^ 2 ≤ 1 / (2 * (k : ℝ)) * (((gridK k : ℕ) : ℝ) - 1) ^ 2 := by
    simp only [gridS, gridK]
    push_cast
    rw [add_sub_cancel_right]
    field_simp
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 5, pow_le_pow_left₀ zero_le_one hk1 4]
  have hτ : (2 * θ) ^ 2 * (2 / (1 / (2 * (k : ℝ)))) ≤ (1 / (2 * (k : ℝ))) ^ 2 / 2 := by
    rw [hθ]
    field_simp
    nlinarith [pow_le_pow_left₀ zero_le_one hk1 3, pow_le_pow_left₀ zero_le_one hk1 4,
      pow_le_pow_left₀ zero_le_one hk1 5]
  obtain ⟨us, hus, ts, hcount⟩ := exists_good_grid hQh hbd χ' (Equiv.refl (Fin k)) hn0
    (by positivity : (0 : ℝ) < 1 / (2 * k)) hsize (by positivity) hsep hdisp
    (by linarith : θ < 2 * θ) hτ U hnet hS (by simp [gridK]) hKg
  -- the count
  set E := ((univ.filter fun y : Fin n ↦ Alg.clusterIdxC (List.ofFn us)
      (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt n) (List.ofFn fun j ↦ (ts j : ℕ))) y ≠
        (χ' y : ℕ)).card : ℝ) with hE
  have hcount' : E ≤ (512 * (k : ℝ) ^ 4 * Δ / (1 / (2 * k) * (2 * θ - θ) ^ 2 *
      (1 / (2 * k)) ^ 2) + 512 * (k : ℝ) ^ 2 * (4 / K) ^ 2 / (1 / (2 * k)) ^ 2) * n := by
    have h := hcount
    simp only [Equiv.refl_apply] at h
    exact h
  have hc1 : 2 * (512 * (k : ℝ) ^ 4 * Δ / (1 / (2 * k) * (2 * θ - θ) ^ 2 *
      (1 / (2 * k)) ^ 2)) = 2 ^ 21 * (k : ℝ) ^ 11 * Δ := by
    rw [hθ]; field_simp; ring
  have hc2 : 2 * (512 * (k : ℝ) ^ 2 * (4 / K) ^ 2 / (1 / (2 * k)) ^ 2) =
      65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2 := by
    field_simp; ring
  have hΔle := disp_const_le hk0 hd hnd
  rw [← hΔ] at hΔle
  have hB : 2 ^ 21 * (k : ℝ) ^ 11 * Δ ≤ errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    have e : errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) =
        2 ^ 21 * (k : ℝ) ^ 11 * (5 / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4)) := by
      rw [errB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hΔle (by positivity)
  have h2E : 2 * E ≤ (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) +
      65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2) * n := by
    have := mul_le_mul_of_nonneg_left hcount' (by norm_num : (0 : ℝ) ≤ 2)
    rw [← mul_assoc, mul_add, hc1, hc2] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hnR.le)
    linarith
  exact ⟨us, hus, ts, h2E⟩


open Classical in
/-- **The good candidate** for the net of the algorithm of Theorem 7.1 with the parameters
`BHSV25.Planted.planParams k K t`, when the host has at most `t` eigenvalues at least `λ₀`: the net
covers the eigenvectors with eigenvalues at least `1 / (16 k²)` in absolute value
(`BHSV25.Planted.expNet_cover_adjDiv`, `BHSV25.Planted.card_abs_ge_numT`). -/
theorem exists_good_candidate (hk : 3 ≤ k) {K : ℕ} (hK : 0 < K) (t : ℕ) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) (hd : 1 ≤ d)
    (hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ t) (χ : Fin H.1 → Fin k)
    (hn : minN k ≤ H.1) (hgood : Good (fun x y ↦ H.normAdj x y) χ) :
    ∃ us : Fin k → List ℚ,
      (∀ j, us j ∈ Alg.expNet (planParams k K t).2 ((H.plant χ).1, adjTable (H.plant χ))) ∧
      ∃ ts : Fin (k * k) → Fin (2 * gridK k + 1),
        2 * ((univ.filter fun y : Fin (H.plant χ).1 ↦ Alg.clusterIdxC (List.ofFn us)
          (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt (H.plant χ).1)
            (List.ofFn fun j ↦ (ts j : ℕ))) y ≠ (χ y : ℕ)).card : ℝ) ≤
          (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2) * H.1 :=
  exists_good_candidate_of_net hk hK H hreg hd χ hn hgood _ fun w hw1 hw ↦
    expNet_cover_adjDiv (H.plant χ) (by exact_mod_cast hd : (0 : ℝ) < d) (by positivity)
      (card_abs_ge_numT (by omega) H hreg hrank χ) hK le_rfl w hw1 hw

open Classical in
/-- **Theorem 7.12 on one good coloring**: the grid clustering of any list `U` that covers the
eigenvectors of `A_G / d` with eigenvalues at least `1 / (16 k²)` in absolute value at precision
`4 / K` is a `(k, B / (d + 1)^(1/4) + 65536 k⁴ / K²)`-coloring. -/
theorem isColoring_planted_of_net (hk : 3 ≤ k) {K : ℕ} (hK : 0 < K) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) (hd : 1 ≤ d) (χ : Fin H.1 → Fin k) (hn : minN k ≤ H.1)
    (hgood : Good (fun x y ↦ H.normAdj x y) χ) (U : List (List ℚ))
    (hnet : ∀ w : Fin (H.plant χ).1 → ℝ, w ⬝ᵥ w ≤ 1 →
      InEigSpan (adjDiv_isHermitian (H.plant χ) d) (fun μ ↦ 1 / (16 * (k : ℝ) ^ 2) ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec (H.plant χ).1 u - w) ⬝ᵥ (Net.ratVec (H.plant χ).1 u - w) ≤
        (4 / K) ^ 2)
    {B : ℕ} (hB1 : U.length ^ k ≤ B) (hB2 : (2 * gridK k + 1) ^ (k * k) ≤ B) :
    (H.plant χ).IsColoring k
      (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2)
      (Alg.gridAlg k k (gridS k) (gridK k) B U ((H.plant χ).1, adjTable (H.plant χ))) := by
  have hk0 : 0 < k := by omega
  set G := H.plant χ with hG
  set χ' : Fin G.1 → Fin k := χ with hχ'
  obtain ⟨us, hus, ts, h2E⟩ := exists_good_candidate_of_net hk hK H hreg hd χ hn hgood U hnet
  have hround := numColored_gridAlg_ge G hk0 χ' (fun u v h ↦ h.2) (gridS k) (gridK k) B U hB1
    hB2 us hus ts
  have hpart : G.IsPartialColoring k
      (Alg.gridAlg k k (gridS k) (gridK k) B U (G.1, adjTable G)) :=
    (Alg.gridAlg_spec G hk0 le_rfl _ _ _ U hB1 hB2).1
  refine ⟨hpart, ?_⟩
  have hround' : (G.1 : ℝ) - 2 * ((univ.filter fun y : Fin G.1 ↦ Alg.clusterIdxC (List.ofFn us)
      (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y ≠
        (χ' y : ℕ)).card : ℝ) ≤
      G.numColored k (Alg.gridAlg k k (gridS k) (gridK k) B U (G.1, adjTable G)) := hround
  have h2E' : 2 * ((univ.filter fun y : Fin G.1 ↦ Alg.clusterIdxC (List.ofFn us)
      (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y ≠
        (χ' y : ℕ)).card : ℝ) ≤
      (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2) * G.1 := h2E
  have e : (1 - (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2)) *
      (G.1 : ℝ) = G.1 - (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) +
        65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2) * G.1 := by ring
  rw [e]
  linarith

end Planted

end BHSV25
