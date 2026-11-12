module

public import BDT24.Analysis.Exact

/-!
# The paired test decides correctly [BDT24, proof of Theorem 3.1]

On a planted sample `z` and a null sample `g` (rows in `ℝ^{d+1}`), with the regression sample
`S = pairMap(z, g)` of secret `x* = (v/√6, 0)`, so that `S x* = √(2/3) ⟨v/2, z_{2..}⟩`:

* if the estimate predicts within `0.1 √n` (`PredictsWell`), the residual of the planted sample
  `z₁ - ⟨v/2, z_{2..}⟩` has squared norm at most `0.51 n`, and `⟨v/2, z_{2..}⟩ - g₁` has squared
  norm at least `0.98 n`, then the predictions are within `(0.1 + √(2/3) √0.51 + 0.005) √n ≤
  0.689 √n` of `√(2/3) z₁` and at least `(√(2/3) √0.98 - 0.105) √n ≥ 0.703 √n` from `√(2/3) g₁`
  (`BDT24.Analysis.test_fwd`); the predictions use the `q`-bit design and the test uses `√(2/3)`
  to `q` bits, which costs at most `0.005 √n` when `2^q` exceeds `2` to the length of the
  estimate times `1024 (d + 1)(R + 1)`, as every coordinate of the estimate is at most `2` to its
  length;
* symmetrically, with the null sample first and secret `(0, v/√6)`, the test says the null
  sample is not planted (`BDT24.Analysis.test_bwd`), for `n ≥ 1`.
-/

@[expose] public section

namespace BDT24.Analysis.TS

open BDT24.Alg BDT24.Prob

/-- `zipWith` of two `ofFn`s. -/
theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn fun i ↦ f (a i) (b i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The sum of `f` over `List.range m`. -/
theorem sum_map_range {m : ℕ} (f : ℕ → ℚ) :
    ((List.range m).map f).sum = ∑ j : Fin m, f j := by
  have : (List.range m).map f = List.ofFn fun j : Fin m ↦ f j := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [this, List.sum_ofFn]

/-- The design row of a pair of quantized points. -/
theorem getD_row {d q : ℕ} (x y : EuclideanSpace ℝ (Fin (d + 1))) (j : Fin (2 * d)) :
    ((List.ofFn fun i ↦ quantize q (x i)).tail ++ (List.ofFn fun i ↦ quantize q (y i)).tail).getD
      j 0 = quantize q ((pairMap d (x, y)).1 j) := by
  rw [List.ofFn_succ, List.ofFn_succ]
  simp only [List.tail_cons, pairMap]
  by_cases h : (j : ℕ) < d
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left]
  · have hj := j.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    rw [dite_eq_left (by omega)]
    simp only [Option.getD_some, h, dite_false]
    rfl

/-- The prediction on point `i`, from the `q`-bit design of the regression sample of `(x, y)`. -/
noncomputable def prd (q : ℕ) {n d : ℕ} (x y : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (xh : Estimate) (i : Fin n) : ℝ :=
  ∑ j : Fin (2 * d), (quantize q ((pairMap d (x i, y i)).1 j) : ℝ) / 2 ^ q * (xh.getD j 0 : ℝ)

/-- The prediction of a pair of quantized points. -/
theorem dotQ_row (q : ℕ) {d : ℕ} (x y : EuclideanSpace ℝ (Fin (d + 1))) (xh : Estimate) :
    ((dotQ q ((List.ofFn fun i ↦ quantize q (x i)).tail ++
      (List.ofFn fun i ↦ quantize q (y i)).tail) xh : ℚ) : ℝ) =
    ∑ j : Fin (2 * d), (quantize q ((pairMap d (x, y)).1 j) : ℝ) / 2 ^ q * (xh.getD j 0 : ℝ) := by
  have hl : ((List.ofFn fun i ↦ quantize q (x i)).tail ++
      (List.ofFn fun i ↦ quantize q (y i)).tail).length = 2 * d := by simp; ring
  unfold dotQ
  rw [hl, sum_map_range]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [getD_row]

/-- The residual of the predictions on a pair of quantized samples, against the quantized first
coordinates of `w`. -/
theorem resid_eq (q : ℕ) {n d : ℕ} (x y w : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (xh : Estimate) :
    ((resid q (predict q (qz q x) (qz q y) xh) (qz q w) : ℚ) : ℝ) =
      ∑ i, (prd q x y xh i - (sQ q : ℝ) * ((quantize q (w i 0) : ℝ) / 2 ^ q)) ^ 2 := by
  unfold resid predict qz
  rw [zipWith_ofFn, zipWith_ofFn, List.sum_ofFn]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotQ_row, List.ofFn_succ]
  rfl

/-! ### Rounding errors -/

/-- A quantized number is within `2^(-q)` of the number. -/
theorem abs_quantize_sub_le (q : ℕ) (t : ℝ) : |(quantize q t : ℝ) / 2 ^ q - t| ≤ 1 / 2 ^ q := by
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have h1 := Int.floor_le ((2 : ℝ) ^ q * t)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ q * t)
  unfold quantize
  rw [show (⌊(2 : ℝ) ^ q * t⌋ : ℝ) / 2 ^ q - t = (⌊(2 : ℝ) ^ q * t⌋ - 2 ^ q * t) / 2 ^ q by
    field_simp, abs_div, abs_of_pos hp, div_le_div_iff_of_pos_right hp, abs_le]
  constructor <;> linarith

/-- `sQ q` is within `2^(-q)` of `√(2/3)`. -/
theorem abs_sQ_sub_le (q : ℕ) : |(sQ q : ℝ) - √(2 / 3)| ≤ 1 / 2 ^ q := by
  have h := SoS.Loop.abs_sqrtP_sub_le q (r := 2 / 3) (by norm_num)
  have h23 : (((2 / 3 : ℚ)) : ℝ) = 2 / 3 := by push_cast; ring
  rw [h23] at h
  exact h

/-- The target `sQ q · (u₁ / 2^q)` of the test is within `(R + 2) 2^(-q)` of `√(2/3) t`. -/
theorem abs_target_le (q : ℕ) {R t : ℝ} (ht : |t| ≤ R) :
    |√(2 / 3) * t - (sQ q : ℝ) * ((quantize q t : ℝ) / 2 ^ q)| ≤ (R + 2) / 2 ^ q := by
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hp1 : 1 / (2 : ℝ) ^ q ≤ 1 := by
    rw [div_le_one hp]; exact one_le_pow₀ (by norm_num)
  have hc : √(2 / 3 : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; norm_num
  have hc0 : 0 ≤ √(2 / 3 : ℝ) := Real.sqrt_nonneg _
  set t' := (quantize q t : ℝ) / 2 ^ q
  have h1 := abs_quantize_sub_le q t
  have h2 := abs_sQ_sub_le q
  have ht' : |t'| ≤ R + 1 := by
    have : |t'| ≤ |t' - t| + |t| := by
      have := abs_add_le (t' - t) t
      simpa using this
    linarith
  have heq : √(2 / 3) * t - (sQ q : ℝ) * t' = √(2 / 3) * (t - t') + (√(2 / 3) - sQ q) * t' := by
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_sub_comm t, abs_sub_comm (√(2 / 3))]
  have h3 : |√(2 / 3 : ℝ)| * |t' - t| ≤ 1 * (1 / 2 ^ q) :=
    mul_le_mul (by rw [abs_of_nonneg hc0]; exact hc) h1 (abs_nonneg _) zero_le_one
  have h4 : |(sQ q : ℝ) - √(2 / 3)| * |t'| ≤ 1 / 2 ^ q * (R + 1) :=
    mul_le_mul h2 ht' (abs_nonneg _) (by positivity)
  have : (R + 2) / 2 ^ q = 1 * (1 / 2 ^ q) + 1 / 2 ^ q * (R + 1) := by ring
  rw [this]
  linarith

/-- The prediction on the `q`-bit design is within `2d 2^H 2^(-q)` of that on the real design,
for `H` the length of the estimate. -/
theorem abs_prd_sub_le (q : ℕ) {n d : ℕ} (x y : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (xh : Estimate) (i : Fin n) :
    |prd q x y xh i - ∑ j, (pairMap d (x i, y i)).1 j * (xh.getD j 0 : ℝ)| ≤
      2 * d * (2 ^ (encEstimate xh).length / 2 ^ q) := by
  unfold prd
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j : Fin (2 * d), |(quantize q ((pairMap d (x i, y i)).1 j) : ℝ) / 2 ^ q *
      (xh.getD j 0 : ℝ) - (pairMap d (x i, y i)).1 j * (xh.getD j 0 : ℝ)| ≤
      2 ^ (encEstimate xh).length / 2 ^ q := by
    intro j
    rw [← sub_mul, abs_mul]
    have h1 := abs_quantize_sub_le q ((pairMap d (x i, y i)).1 j)
    have h2 := abs_getD_le xh j
    calc _ ≤ 1 / 2 ^ q * 2 ^ (encEstimate xh).length :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun j _ ↦ hterm j).trans ?_
  simp

/-! ### The secret's predictions -/

/-- A sum over `Fin (2d)` as the sums over the two halves. -/
theorem sum_two_mul {d : ℕ} (f : Fin (2 * d) → ℝ) :
    ∑ j, f j = ∑ i : Fin d, f ⟨i, by omega⟩ + ∑ i : Fin d, f ⟨d + i, by omega⟩ := by
  rw [← (finCongr (two_mul d)).symm.sum_comp, Fin.sum_univ_add]
  rfl

/-- `1/√6 = √(2/3)/2`. -/
theorem inv_sqrt_six (a : ℝ) : a / √6 = √(2 / 3) * (a / 2) := by
  have h : √(2 / 3 : ℝ) * √6 = 2 := by
    rw [← Real.sqrt_mul (by norm_num), show (2 / 3 * 6 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h6 : (0 : ℝ) < √6 := by positivity
  rw [div_eq_iff h6.ne']
  linear_combination (-(a / 2)) * h

/-- The secret `xsF` predicts `√(2/3) ⟨v/2, x_{2..}⟩` on the regression point of `(x, y)`. -/
theorem sum_xsF {d : ℕ} (v : Fin d → SignType) (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    ∑ j, (pairMap d (x, y)).1 j * xsF d v j = √(2 / 3) * ∑ j : Fin d, (v j : ℝ) / 2 * x j.succ := by
  rw [sum_two_mul, Finset.mul_sum]
  simp only [pairMap, xsF, PiLp.toLp_apply]
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, add_lt_iff_neg_left, not_lt_zero,
    mul_zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change x j.succ * _ = _
  rw [inv_sqrt_six]
  ring

/-- The secret `xsB` predicts `√(2/3) ⟨v/2, y_{2..}⟩` on the regression point of `(x, y)`. -/
theorem sum_xsB {d : ℕ} (v : Fin d → SignType) (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    ∑ j, (pairMap d (x, y)).1 j * xsB d v j = √(2 / 3) * ∑ j : Fin d, (v j : ℝ) / 2 * y j.succ := by
  rw [sum_two_mul, Finset.mul_sum]
  have h1 : ∀ i : Fin d, ¬ d ≤ (i : ℕ) := fun i ↦ not_le.2 i.isLt
  simp only [pairMap, xsB, PiLp.toLp_apply]
  simp only [h1, ↓reduceDIte, mul_zero, Finset.sum_const_zero, zero_add, add_lt_iff_neg_left,
    not_lt_zero, Nat.le_add_right, add_tsub_cancel_left, Fin.eta]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change y j.succ * _ = _
  rw [inv_sqrt_six]
  ring

/-- The rounding errors are at most `1/512` when `2^q ≥ 2^H · 1024 (d + 1)(R + 1)`. -/
theorem errors_le {d H q : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hq : (2 : ℝ) ^ H * (1024 * (d + 1) * (R + 1)) ≤ 2 ^ q) :
    2 * (d : ℝ) * ((2 : ℝ) ^ H / 2 ^ q) ≤ 1 / 512 ∧ (R + 2) / (2 : ℝ) ^ q ≤ 1 / 512 := by
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hH : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
  set δ : ℝ := 2 ^ H / 2 ^ q with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h1 : δ * (1024 * (d + 1) * (R + 1)) ≤ 1 := by
    rw [hδ, div_mul_eq_mul_div, div_le_one hp]
    exact hq
  have h2 : 1 / (2 : ℝ) ^ q ≤ δ := div_le_div_of_nonneg_right hH hp.le
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  constructor
  · nlinarith [mul_nonneg hδ0 hd, mul_nonneg (mul_nonneg hδ0 hd) (by linarith : (0 : ℝ) ≤ R - 1)]
  · rw [div_eq_mul_one_div]
    nlinarith [mul_nonneg hδ0 hd, mul_nonneg (mul_nonneg hδ0 hd) (by linarith : (0 : ℝ) ≤ R + 1),
      mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ R + 2)]

/-! ### The inequality chain -/

/-- The Euclidean norm of a vector given by its coordinates. -/
theorem norm_toLp {n : ℕ} (f : Fin n → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n))‖ = √(∑ i, f i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp

/-- An upper bound on a norm from one on the sum of squares. -/
theorem norm_toLp_le {n : ℕ} (f : Fin n → ℝ) {b : ℝ} (hb : 0 ≤ b) (h : ∑ i, f i ^ 2 ≤ b ^ 2) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n))‖ ≤ b := by
  rw [norm_toLp, Real.sqrt_le_left hb]
  exact h

/-- A lower bound on a norm from one on the sum of squares. -/
theorem le_norm_toLp {n : ℕ} (f : Fin n → ℝ) {b : ℝ} (h : b ^ 2 ≤ ∑ i, f i ^ 2) :
    b ≤ ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n))‖ := by
  rw [norm_toLp]
  exact Real.le_sqrt_of_sq_le h

/-- A vector with coordinates at most `ε` has norm at most `ε √n`. -/
theorem norm_toLp_le_of_abs {n : ℕ} (f : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, |f i| ≤ ε) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n))‖ ≤ ε * √n := by
  refine norm_toLp_le f (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  calc ∑ i, f i ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = ε ^ 2 * n := by simp [mul_comm]

/-- `0.8164 ≤ √(2/3) ≤ 0.8166`. -/
theorem sqrt_two_thirds_mem : 8164 / 10000 ≤ √(2 / 3 : ℝ) ∧ √(2 / 3 : ℝ) ≤ 8166 / 10000 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

/-- **The inequality chain.** Predictions `P` within `1/512` of predictions `A` that are within
`0.1 √n` of `√(2/3) L` (the secret's), targets `T, T'` within `1/512` of `√(2/3) z₀, √(2/3) g₀`,
`‖z₀ - L‖² ≤ 0.51 n` and `‖L - g₀‖² ≥ 0.98 n`: then `P` is at most `0.6872 √n` from `T` and at
least `0.7042 √n` from `T'`. -/
theorem chain {n : ℕ} (P A L z0 g0 T T' : Fin n → ℝ)
    (hA : ∑ i, (A i - √(2 / 3) * L i) ^ 2 ≤ n / 100) (hP : ∀ i, |P i - A i| ≤ 1 / 512)
    (hw : ∑ i, (z0 i - L i) ^ 2 ≤ 51 / 100 * n) (ho : 98 / 100 * n ≤ ∑ i, (L i - g0 i) ^ 2)
    (hT : ∀ i, |√(2 / 3) * z0 i - T i| ≤ 1 / 512)
    (hT' : ∀ i, |√(2 / 3) * g0 i - T' i| ≤ 1 / 512) :
    ‖(WithLp.toLp 2 (fun i ↦ P i - T i) : EuclideanSpace ℝ (Fin n))‖ ≤ 6872 / 10000 * √n ∧
      7042 / 10000 * √n ≤
        ‖(WithLp.toLp 2 (fun i ↦ P i - T' i) : EuclideanSpace ℝ (Fin n))‖ := by
  set c := √(2 / 3 : ℝ)
  obtain ⟨hc1, hc2⟩ := sqrt_two_thirds_mem
  set s := √(n : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  let V : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
  set a : Fin n → ℝ := fun i ↦ A i - c * L i
  set e : Fin n → ℝ := fun i ↦ P i - A i + (c * z0 i - T i)
  set e' : Fin n → ℝ := fun i ↦ P i - A i + (c * g0 i - T' i)
  set w : Fin n → ℝ := fun i ↦ z0 i - L i
  set o : Fin n → ℝ := fun i ↦ L i - g0 i
  have ha : ‖V a‖ ≤ s / 10 :=
    norm_toLp_le a (by positivity) (by rw [div_pow, hs2]; linarith)
  have he : ‖V e‖ ≤ 1 / 256 * s := by
    refine norm_toLp_le_of_abs e (by norm_num) fun i ↦ ?_
    have := abs_add_le (P i - A i) (c * z0 i - T i)
    linarith [hP i, hT i]
  have he' : ‖V e'‖ ≤ 1 / 256 * s := by
    refine norm_toLp_le_of_abs e' (by norm_num) fun i ↦ ?_
    have := abs_add_le (P i - A i) (c * g0 i - T' i)
    linarith [hP i, hT' i]
  have hwn : ‖V w‖ ≤ 7142 / 10000 * s :=
    norm_toLp_le w (by positivity) (by rw [mul_pow, hs2]; linarith)
  have hon : 9899 / 10000 * s ≤ ‖V o‖ :=
    le_norm_toLp o (by rw [mul_pow, hs2]; linarith)
  have hX : V (fun i ↦ P i - T i) = V a + V e - c • V w := by
    ext i
    simp only [V, a, e, w, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hY : c • V o = V (fun i ↦ P i - T' i) - V a - V e' := by
    ext i
    simp only [V, a, e', o, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  constructor
  · change ‖V (fun i ↦ P i - T i)‖ ≤ _
    rw [hX]
    have h1 := norm_sub_le (V a + V e) (c • V w)
    have h2 := norm_add_le (V a) (V e)
    rw [norm_smul, Real.norm_of_nonneg hc0] at h1
    have h3 : c * ‖V w‖ ≤ 8166 / 10000 * (7142 / 10000 * s) :=
      mul_le_mul hc2 hwn (norm_nonneg _) (by norm_num)
    nlinarith
  · change _ ≤ ‖V (fun i ↦ P i - T' i)‖
    have h1 := norm_sub_le (V (fun i ↦ P i - T' i) - V a) (V e')
    have h2 := norm_sub_le (V (fun i ↦ P i - T' i)) (V a)
    rw [← hY, norm_smul, Real.norm_of_nonneg hc0] at h1
    have h3 : 8164 / 10000 * (9899 / 10000 * s) ≤ c * ‖V o‖ :=
      mul_le_mul hc1 hon (by positivity) hc0
    nlinarith

/-- **The comparison of the residuals**, from the inequality chain: `‖P - T‖² ≤ ‖P - T'‖²`, and
strictly when `n ≥ 1`. -/
theorem chain_sq {n : ℕ} (P A L z0 g0 T T' : Fin n → ℝ)
    (hA : ∑ i, (A i - √(2 / 3) * L i) ^ 2 ≤ n / 100) (hP : ∀ i, |P i - A i| ≤ 1 / 512)
    (hw : ∑ i, (z0 i - L i) ^ 2 ≤ 51 / 100 * n) (ho : 98 / 100 * n ≤ ∑ i, (L i - g0 i) ^ 2)
    (hT : ∀ i, |√(2 / 3) * z0 i - T i| ≤ 1 / 512)
    (hT' : ∀ i, |√(2 / 3) * g0 i - T' i| ≤ 1 / 512) :
    ∑ i, (P i - T i) ^ 2 ≤ ∑ i, (P i - T' i) ^ 2 ∧
      (0 < n → ∑ i, (P i - T i) ^ 2 < ∑ i, (P i - T' i) ^ 2) := by
  obtain ⟨h1, h2⟩ := chain P A L z0 g0 T T' hA hP hw ho hT hT'
  rw [norm_toLp] at h1 h2
  have hX0 : 0 ≤ ∑ i, (P i - T i) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hY0 : 0 ≤ ∑ i, (P i - T' i) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hs0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  constructor
  · rw [← Real.sqrt_le_sqrt_iff hY0]
    linarith
  · intro hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [← Real.sqrt_lt_sqrt_iff hX0]
    linarith

end BDT24.Analysis.TS

namespace BDT24.Analysis

open BDT24.Alg BDT24.Prob

/-- **The test on (planted, null).** -/
theorem test_fwd {n d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k)
    (z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (xh : Estimate) (q : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hz : ∀ i j, |z i j| ≤ R) (hg : ∀ i j, |g i j| ≤ R)
    (hc1 : ∑ i, noiseStat d v (z i) ^ 2 ≤ 51 / 100 * n)
    (hc2 : 98 / 100 * n ≤ ∑ i, otherStat d v (z i, g i) ^ 2)
    (hpw : PredictsWell (fun i ↦ pairMap d (z i, g i)) (xsF d v) xh)
    (hq : (2 : ℝ) ^ (encEstimate xh).length * (1024 * (d + 1) * (R + 1)) ≤ 2 ^ q) :
    resid q (predict q (qz q z) (qz q g) xh) (qz q z) ≤
      resid q (predict q (qz q z) (qz q g) xh) (qz q g) := by
  -- the sparsity of `v` plays no role: the chain holds for every sign pattern
  have _ := hv
  obtain ⟨hP, hT⟩ := TS.errors_le hR hq
  rw [← Rat.cast_le (K := ℝ), TS.resid_eq, TS.resid_eq]
  refine (TS.chain_sq (TS.prd q z g xh)
    (fun i ↦ ∑ j, (pairMap d (z i, g i)).1 j * (xh.getD j 0 : ℝ))
    (fun i ↦ ∑ j : Fin d, (v j : ℝ) / 2 * z i j.succ) (fun i ↦ z i 0) (fun i ↦ g i 0)
    (fun i ↦ (sQ q : ℝ) * ((quantize q (z i 0) : ℝ) / 2 ^ q))
    (fun i ↦ (sQ q : ℝ) * ((quantize q (g i 0) : ℝ) / 2 ^ q)) ?_ ?_ hc1 hc2 ?_ ?_).1
  · refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ ↦ ?_) hpw
    rw [← TS.sum_xsF v (z i) (g i), ← Finset.sum_sub_distrib]
    simp_rw [mul_sub]
  · exact fun i ↦ (TS.abs_prd_sub_le q z g xh i).trans hP
  · exact fun i ↦ (TS.abs_target_le q (hz i 0)).trans hT
  · exact fun i ↦ (TS.abs_target_le q (hg i 0)).trans hT

/-- **The test on (null, planted).** -/
theorem test_bwd {n d k : ℕ} (hn : 0 < n) {v : Fin d → SignType} (hv : v ∈ spikeSigns d k)
    (z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (xh : Estimate) (q : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hz : ∀ i j, |z i j| ≤ R) (hg : ∀ i j, |g i j| ≤ R)
    (hc1 : ∑ i, noiseStat d v (z i) ^ 2 ≤ 51 / 100 * n)
    (hc2 : 98 / 100 * n ≤ ∑ i, otherStat d v (z i, g i) ^ 2)
    (hpw : PredictsWell (fun i ↦ pairMap d (g i, z i)) (xsB d v) xh)
    (hq : (2 : ℝ) ^ (encEstimate xh).length * (1024 * (d + 1) * (R + 1)) ≤ 2 ^ q) :
    ¬ resid q (predict q (qz q g) (qz q z) xh) (qz q g) ≤
      resid q (predict q (qz q g) (qz q z) xh) (qz q z) := by
  -- the sparsity of `v` plays no role: the chain holds for every sign pattern
  have _ := hv
  obtain ⟨hP, hT⟩ := TS.errors_le hR hq
  rw [not_le, ← Rat.cast_lt (K := ℝ), TS.resid_eq, TS.resid_eq]
  refine (TS.chain_sq (TS.prd q g z xh)
    (fun i ↦ ∑ j, (pairMap d (g i, z i)).1 j * (xh.getD j 0 : ℝ))
    (fun i ↦ ∑ j : Fin d, (v j : ℝ) / 2 * z i j.succ) (fun i ↦ z i 0) (fun i ↦ g i 0)
    (fun i ↦ (sQ q : ℝ) * ((quantize q (z i 0) : ℝ) / 2 ^ q))
    (fun i ↦ (sQ q : ℝ) * ((quantize q (g i 0) : ℝ) / 2 ^ q)) ?_ ?_ hc1 hc2 ?_ ?_).2 hn
  · refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ ↦ ?_) hpw
    rw [← TS.sum_xsB v (g i) (z i), ← Finset.sum_sub_distrib]
    simp_rw [mul_sub]
  · exact fun i ↦ (TS.abs_prd_sub_le q g z xh i).trans hP
  · exact fun i ↦ (TS.abs_target_le q (hz i 0)).trans hT
  · exact fun i ↦ (TS.abs_target_le q (hg i 0)).trans hT

end BDT24.Analysis
