module

public import BHSV25.Hard.ModelCount

/-!
# The design for Theorem 1.9 (2): estimates

Real estimates on the data of `BHSV25/Hard/ModelDesign.lean`, for `π_i ≥ π_min > 0`:

* **The planted matrix** of the design is `κ D w_ij / (s_i s_j)`, `κ = P² / (D 2^r)`
  (`BHSV25.Hard.ModelRed.Data.chat_eq`), and `D w_ij / (s_i s_j)` is within
  `δ₀ = 8k / (D π_min³)` of `M_ij / π_j` (`BHSV25.Hard.ModelRed.Data.abs_chat_sub_le`).
* `M_ij / π_j` depends only on the classes of `i` and `j`
  (`BHSV25.Hard.ModelRed.Data.ratio_congr`).
* The fraction `V_b = ∑_j s_j ℓ_jb / (2HD)` of color `b` is within `k² / D + k / (2H)` of `π_b`
  (`BHSV25.Hard.ModelRed.Data.abs_V_sub_le`).
* `∑_i π_i κ_i = 1 - α` for `κ_i = ∑_b max(0, 2 ρ⁽ⁱ⁾_b - 1)`
  (`BHSV25.Hard.ModelRed.Data.sum_π_κ`), and `e_i ≤ 2H κ_i + 2k`
  (`BHSV25.Hard.ModelRed.Data.e_le`).
-/

@[expose] public section

namespace BHSV25.Hard.ModelRed

open Finset LowRank Cayley

namespace Data

variable (X : Data)

theorem one_le_k : 1 ≤ X.k := by
  rcases Nat.eq_zero_or_pos X.k with h | h
  · have := X.hπ.2.1
    have hk : X.k = 0 := h
    revert this
    generalize X.π = π
    revert π
    rw [hk]
    simp
  · exact h

/-! ### The planted matrix -/

/-- The scale of the planted matrix. -/
noncomputable def κ : ℝ := (X.P : ℝ) ^ 2 / (X.D * 2 ^ X.r)

theorem κ_nonneg : 0 ≤ X.κ := by unfold κ; positivity

theorem s_pos (i : Fin X.k) : (0 : ℝ) < X.s i := by exact_mod_cast X.one_le_s i

theorem chat_eq (i j : Fin X.k) :
    X.design.Chat i j = X.κ * (X.D * X.w i j / (X.s i * X.s j)) := by
  have hD : (0 : ℝ) < X.D := by
    have := X.hD i
    have := X.π_le_one i
    have hk : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
    by_contra h
    have : (X.D : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    nlinarith
  unfold Design.Chat
  split_ifs with h
  · change i = j at h
    subst h
    rw [X.w_diag]; simp
  · change (X.q i j : ℝ) / 2 ^ X.r = _
    unfold q κ
    have hp : ∀ c, (X.p c : ℝ) = X.P / X.s c := fun c ↦ by
      rw [eq_div_iff (X.s_pos c).ne']; exact_mod_cast X.p_mul_s c
    push_cast
    rw [hp i, hp j]
    have := X.s_pos i
    have := X.s_pos j
    field_simp

/-- **The planted matrix is close to `M_ij / π_j`.** -/
theorem abs_chat_sub_le {pm : ℝ} (hpm : 0 < pm) (hπ : ∀ i, pm ≤ X.π i) (i j : Fin X.k) :
    |X.D * X.w i j / (X.s i * X.s j) - X.M i j / X.π j| ≤ 8 * X.k / (X.D * pm ^ 3) := by
  set A : ℝ := (X.D : ℝ)
  have hk : (1 : ℝ) ≤ X.k := by exact_mod_cast X.one_le_k
  have hπi := X.π_pos i
  have hπj := X.π_pos j
  have hAi := X.hD i
  have hAj := X.hD j
  have hA : 0 < A := by
    by_contra h
    have : A ≤ 0 := not_lt.1 h
    nlinarith [X.π_le_one i]
  have hsi := X.s_pos i
  have hsj := X.s_pos j
  have hsi1 := X.s_le i
  have hsi2 := X.le_s i
  have hsj1 := X.s_le j
  have hsj2 := X.le_s j
  have hw1 := X.w_le i j
  have hw2 := X.lt_w i j
  have hM0 := X.M_nonneg i j
  have hM1 := X.M_le_one i j
  have hπi1 := X.π_le_one i
  have hπj1 := X.π_le_one j
  set N : ℝ := A * X.w i j * X.π j - X.M i j * (X.s i * X.s j)
  have hrw : A * X.w i j / (X.s i * X.s j) - X.M i j / X.π j = N / (X.s i * X.s j * X.π j) := by
    simp only [N]; field_simp
  have hden0 : (0 : ℝ) < X.s i * X.s j * X.π j := mul_pos (mul_pos hsi hsj) hπj
  rw [hrw, abs_div, abs_of_pos hden0]
  have hN : |N| ≤ 2 * X.k * A := by
    refine abs_le.2 ⟨?_, ?_⟩
    · -- lower bound
      have h1 : A * (A * X.π i * X.M i j - 1) * X.π j ≤ A * X.w i j * X.π j := by
        have : A * X.π i * X.M i j - 1 ≤ X.w i j := by linarith
        have := mul_le_mul_of_nonneg_left this hA.le
        exact mul_le_mul_of_nonneg_right this hπj.le
      have h2 : X.M i j * (X.s i * X.s j) ≤ X.M i j * ((A * X.π i) * (A * X.π j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsi1 hsj1 hsj.le (by positivity)) hM0
      simp only [N]
      nlinarith
    · -- upper bound
      have h1 : A * X.w i j * X.π j ≤ A * (A * X.π i * X.M i j) * X.π j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw1 hA.le) hπj.le
      have hai : 0 ≤ A * X.π i - X.k := by linarith
      have haj : 0 ≤ A * X.π j - X.k := by linarith
      have h2 : X.M i j * ((A * X.π i - X.k) * (A * X.π j - X.k)) ≤
          X.M i j * (X.s i * X.s j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsi2 hsj2 haj hsi.le) hM0
      have h3 : X.M i j * (X.k * A * (X.π i + X.π j)) ≤ 2 * X.k * A := by
        have : X.k * A * (X.π i + X.π j) ≤ 2 * X.k * A := by
          have : (0 : ℝ) ≤ X.k * A := by positivity
          nlinarith
        calc X.M i j * (X.k * A * (X.π i + X.π j)) ≤ 1 * (X.k * A * (X.π i + X.π j)) :=
              mul_le_mul_of_nonneg_right hM1 (by positivity)
          _ ≤ _ := by linarith
      simp only [N]
      have hkk : (0 : ℝ) ≤ X.M i j * X.k ^ 2 := by positivity
      nlinarith
  have hden : A ^ 2 * pm ^ 3 / 4 ≤ X.s i * X.s j * X.π j := by
    have h1 := X.half_le_s i
    have h2 := X.half_le_s j
    have hpi := hπ i
    have hpj := hπ j
    have e1 : A * pm / 2 ≤ X.s i := le_trans (by nlinarith) h1
    have e2 : A * pm / 2 ≤ X.s j := le_trans (by nlinarith) h2
    have : (A * pm / 2) * (A * pm / 2) ≤ X.s i * X.s j :=
      mul_le_mul e1 e2 (by positivity) hsi.le
    calc A ^ 2 * pm ^ 3 / 4 = (A * pm / 2) * (A * pm / 2) * pm := by ring
      _ ≤ X.s i * X.s j * X.π j := mul_le_mul this hpj hpm.le (by positivity)
  rw [div_le_div_iff₀ hden0 (by positivity)]
  calc |N| * (A * pm ^ 3) ≤ 2 * X.k * A * (A * pm ^ 3) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 8 * X.k * (A ^ 2 * pm ^ 3 / 4) := by ring
    _ ≤ 8 * X.k * (X.s i * X.s j * X.π j) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- **`M_ij / π_j` depends only on the classes.** -/
theorem ratio_congr {i j c e : Fin X.k} (hi : X.M i = X.M c) (hj : X.M j = X.M e) :
    X.M i j / X.π j = X.M c e / X.π e := by
  rw [congrFun hi j]
  have hjc : X.M j c = X.M e c := congrFun hj c
  have h1 := X.hπ.2.2 c j
  have h2 := X.hπ.2.2 e c
  rw [div_eq_div_iff (X.π_pos j).ne' (X.π_pos e).ne']
  apply mul_left_cancel₀ (X.π_pos c).ne'
  linear_combination X.π e * h1 + X.π j * h2 + (X.π j * X.π e) * hjc

/-! ### Color fractions -/

theorem sum_π_ρ (b : Fin X.k) : ∑ j, X.π j * X.ρ j b = X.π b := by
  have hpt : ∀ j, X.π j * X.ρ j b =
      if j ∈ Alg.rowGroup X.M b then X.π j * (X.π b / X.Pi b) else 0 := by
    intro j
    unfold ρ
    by_cases hj : j ∈ Alg.rowGroup X.M b
    · have hrow : X.M j = X.M b := Alg.mem_rowGroup.1 hj
      rw [ite_eq_left (Alg.mem_rowGroup.2 hrow.symm), ite_eq_left hj, X.Pi_congr hrow]
    · have hrow : ¬ X.M b = X.M j := fun h ↦ hj (Alg.mem_rowGroup.2 h.symm)
      rw [ite_eq_right (fun h ↦ hrow (Alg.mem_rowGroup.1 h)), ite_eq_right hj, mul_zero]
  simp_rw [hpt]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_mul]
  change X.Pi b * (X.π b / X.Pi b) = X.π b
  field_simp [(X.Pi_pos b).ne']

theorem abs_ℓ_sub_le (j b : Fin X.k) : |(X.ℓ j b : ℝ) - 2 * X.H * X.ρ j b| ≤ X.k := by
  have := Units.abs_card_col_sub_le (X.ρ_nonneg j) (X.ρ_sum j) j (2 * X.H) b
  push_cast at this
  exact this

theorem ℓ_le (j b : Fin X.k) : (X.ℓ j b : ℝ) ≤ 2 * X.H := by
  have : X.ℓ j b ≤ 2 * X.H := (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- **The color fractions are close to `π`.** -/
theorem abs_V_sub_le (b : Fin X.k) :
    |(∑ j, (X.s j : ℝ) * X.ℓ j b) / (2 * X.H * X.D) - X.π b| ≤
      (X.k : ℝ) ^ 2 / X.D + X.k / (2 * X.H) := by
  have hH : (0 : ℝ) < X.H := by exact_mod_cast X.hH
  have hD : (0 : ℝ) < X.D := by
    have h1 := X.hD b
    by_contra h
    have : (X.D : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, zero_mul] at h1
    have : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
    linarith
  have hsum : ∑ j, (X.s j : ℝ) * X.ℓ j b - 2 * X.H * X.D * X.π b =
      ∑ j, (((X.s j : ℝ) - X.D * X.π j) * X.ℓ j b +
        X.D * X.π j * ((X.ℓ j b : ℝ) - 2 * X.H * X.ρ j b)) := by
    rw [← X.sum_π_ρ b, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have hbound : |∑ j, (X.s j : ℝ) * X.ℓ j b - 2 * X.H * X.D * X.π b| ≤
      2 * X.H * X.k ^ 2 + X.D * X.k := by
    rw [hsum]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |((X.s j : ℝ) - X.D * X.π j) * X.ℓ j b +
          X.D * X.π j * ((X.ℓ j b : ℝ) - 2 * X.H * X.ρ j b)|
        ≤ ∑ j, (X.k * (2 * X.H) + X.D * X.π j * X.k) := by
          refine sum_le_sum fun j _ ↦ (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            have h1 : |(X.s j : ℝ) - X.D * X.π j| ≤ X.k := by
              rw [abs_le]; constructor <;> linarith [X.s_le j, X.le_s j]
            have h2 : |(X.ℓ j b : ℝ)| ≤ 2 * X.H := by
              rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact X.ℓ_le j b
            exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
          · rw [abs_mul, abs_of_nonneg (by have := X.π_pos j; positivity)]
            exact mul_le_mul_of_nonneg_left (X.abs_ℓ_sub_le j b)
              (by have := X.π_pos j; positivity)
      _ = 2 * X.H * X.k ^ 2 + X.D * X.k := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul,
            ← mul_sum, X.hπ.2.1]
          ring
  have hrw : (∑ j, (X.s j : ℝ) * X.ℓ j b) / (2 * X.H * X.D) - X.π b =
      (∑ j, (X.s j : ℝ) * X.ℓ j b - 2 * X.H * X.D * X.π b) / (2 * X.H * X.D) := by
    field_simp
  have hHD : (0 : ℝ) < 2 * X.H * X.D := by positivity
  rw [hrw, abs_div, abs_of_pos hHD, div_le_iff₀ hHD]
  calc _ ≤ (2 * X.H * X.k ^ 2 + X.D * X.k : ℝ) := hbound
    _ = ((X.k : ℝ) ^ 2 / X.D + X.k / (2 * X.H)) * (2 * X.H * X.D) := by field_simp

theorem V_le_one (b : Fin X.k) : (∑ j, (X.s j : ℝ) * X.ℓ j b) / (2 * X.H * X.D) ≤ 1 := by
  have hH : (0 : ℝ) < X.H := by exact_mod_cast X.hH
  have hD : (0 : ℝ) < X.D := by
    have h1 := X.hD b
    by_contra h
    have : (X.D : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, zero_mul] at h1
    have : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
    linarith
  have hHD : (0 : ℝ) < 2 * X.H * X.D := by positivity
  rw [div_le_one hHD]
  calc ∑ j, (X.s j : ℝ) * X.ℓ j b ≤ ∑ j, X.D * X.π j * (2 * X.H) :=
        sum_le_sum fun j _ ↦ mul_le_mul (X.s_le j) (X.ℓ_le j b) (Nat.cast_nonneg _)
          (by have := X.π_pos j; positivity)
    _ = 2 * X.H * X.D := by rw [← sum_mul, ← mul_sum, X.hπ.2.1]; ring

/-! ### The uncovered fraction -/

/-- The excess of the largest color of the class of `i`. -/
noncomputable def κc (i : Fin X.k) : ℝ := ∑ b, max 0 (2 * X.ρ i b - 1)

theorem κc_nonneg (i : Fin X.k) : 0 ≤ X.κc i := sum_nonneg fun _ _ ↦ le_max_left _ _

theorem e_le (i : Fin X.k) : (X.e i : ℝ) ≤ 2 * X.H * X.κc i + 2 * X.k :=
  Units.card_col_sh_le (X.ρ_sum i) i X.H

/-- **`∑_i π_i κ_i = 1 - α`.** -/
theorem sum_π_κ : ∑ i, X.π i * X.κc i = 1 - alpha X.M X.π := by
  rw [Alg.alpha_eq_sum_rowGroup]
  have hmin : ∀ b, min (X.π b) ((∑ c ∈ Alg.rowGroup X.M b, X.π c) - X.π b) =
      X.π b - max 0 (2 * X.π b - X.Pi b) := by
    intro b
    change min (X.π b) (X.Pi b - X.π b) = _
    rcases le_total (X.π b) (X.Pi b - X.π b) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  simp_rw [hmin]
  rw [sum_sub_distrib, X.hπ.2.1, sub_sub_cancel]
  unfold κc
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ ↦ ?_
  have hpt : ∀ i, X.π i * max 0 (2 * X.ρ i b - 1) =
      if i ∈ Alg.rowGroup X.M b then X.π i * max 0 (2 * (X.π b / X.Pi b) - 1) else 0 := by
    intro i
    unfold ρ
    by_cases hi : i ∈ Alg.rowGroup X.M b
    · have hrow : X.M i = X.M b := Alg.mem_rowGroup.1 hi
      rw [ite_eq_left (Alg.mem_rowGroup.2 hrow.symm), ite_eq_left hi, X.Pi_congr hrow]
    · have hrow : ¬ X.M b = X.M i := fun h ↦ hi (Alg.mem_rowGroup.2 h.symm)
      rw [ite_eq_right (fun h ↦ hrow (Alg.mem_rowGroup.1 h)), ite_eq_right hi]
      norm_num
  simp_rw [hpt]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_mul]
  change X.Pi b * max 0 (2 * (X.π b / X.Pi b) - 1) = max 0 (2 * X.π b - X.Pi b)
  have hP := X.Pi_pos b
  rw [mul_max_of_nonneg _ _ hP.le, mul_zero]
  congr 1
  field_simp

/-! ### The error of the pseudo-random sets -/

theorem err_mul_le (a r : ℕ) : err a r * 2 ^ a ≤ 8 ^ r * ((4 : ℝ) ^ a) ^ r := by
  unfold err
  have h4 : (4 : ℝ) ^ a = 2 ^ a * 2 ^ a := by rw [← mul_pow]; norm_num
  have h8 : (8 : ℝ) ^ r = 4 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
  have hpos : (0 : ℝ) < 2 ^ a := by positivity
  rw [mul_pow, h8, div_mul_eq_mul_div, div_le_iff₀ (by positivity), h4]
  have : (0 : ℝ) ≤ 4 ^ r * 2 ^ a * (2 ^ r * (2 ^ a * 2 ^ a) ^ r) * 2 ^ a := by positivity
  nlinarith

end Data

end BHSV25.Hard.ModelRed
