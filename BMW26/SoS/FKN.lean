module

public import BMW26.SoS.Basic

/-!
# The sum-of-squares FKN theorem

[BMW26, Theorem 4.1]: the Boolean constraints `X x² = 1` prove, in degree `4`,
`∑ᵢ f̂(i)⁴ ≥ 1 - O(1 - ∑ᵢ f̂(i)²)` (`BMW26.fkn`, with the constant `10`; the proof gives `6`).

The proof follows the paper with `W = 1 - ∑ᵢ f̂(i)²` in place of `δ`. Write `E` for the average over
the cube, `ℓ(x) = ∑ᵢ f̂(i) χᵢ(x)`, `g = f - ℓ`, `D = ℓ² - 1`, `Z = ∑_{|U| ≥ 2} f̂(U)²`, and `P_S`,
`Q_S` for the Fourier coefficients of `D` and of `(g - f̂(∅)) ℓ`. Modulo the Boolean constraints:

* `E g² = W` (Parseval), and `E g² = f̂(∅)² + Z`;
* `D + g ℓ + g f = f² - 1`, `E [D ℓ] = 0`, and `D` has no Fourier mass above level `2`, so
  `E D² / 2 ≤ ∑_{|S| ≤ 2} Q_S² + E (g f)²` (the paper's triangle inequality; the constant term
  `f̂(∅) ℓ` of `g ℓ` drops out since `E [D ℓ] = 0`);
* `Q_S = ∑ⱼ f̂(j) b(S ∆ {j})` with `b(U) = f̂(U)` for `|U| ≥ 2` and `0` otherwise; by
  Cauchy–Schwarz (Lagrange's identity), and since a set `U` with `|U| ≥ 2` is `S ∆ {j}` with
  `|S| ≤ 2` for at most `3` indices `j`, `∑_{|S| ≤ 2} Q_S² ≤ 3 (∑ᵢ f̂(i)²) Z ≤ 3 Z`;
* `E D² = W² + 2 ((∑ᵢ f̂(i)²)² - ∑ᵢ f̂(i)⁴)` (the fourth moment of `ℓ`).

The argument is one certificate (`BMW26.FKN.key_identity`): the goal is a sum of squares minus
`E [σ (f² - 1)]`, for a sum of squares `σ` of degree `2`. This identity between polynomials is
checked at every real point (`MvPolynomial.funext`), where it follows from the Fourier identities
of `BMW26/Cube/Basic.lean` (`BMW26.FKN.real_identity`).
-/

@[expose] public section

namespace BMW26

open Finset MvPolynomial SoS

namespace FKN

variable {m : ℕ}

/-! ### Fourier identities for real functions -/

/-- A linear combination `∑ᵢ cᵢ χᵢ` of the characters of level one. -/
def lin (c : Fin m → ℝ) (x : Cube m) : ℝ := ∑ i, c i * chi {i} x

theorem symmDiff_singleton_eq_empty {i j : Fin m} :
    symmDiff ({i} : Finset (Fin m)) {j} = ∅ ↔ i = j := by
  rw [← Finset.bot_eq_empty, symmDiff_eq_bot, Finset.singleton_inj]

theorem card_symmDiff_singleton_le (i j : Fin m) :
    (symmDiff ({i} : Finset (Fin m)) {j}).card ≤ 2 :=
  (Finset.card_le_card (symmDiff_le_sup (a := ({i} : Finset (Fin m))) (b := {j}))).trans
    ((Finset.card_union_le _ _).trans (by simp))

theorem symmDiff_singleton_ne_singleton (i j k : Fin m) :
    symmDiff ({j} : Finset (Fin m)) {k} ≠ {i} := by
  intro h
  by_cases hjk : j = k
  · subst hjk
    rw [symmDiff_self] at h
    exact Finset.singleton_ne_empty i h.symm
  · have hj : j ∈ symmDiff ({j} : Finset (Fin m)) {k} := by
      simp [Finset.mem_symmDiff, hjk]
    have hk : k ∈ symmDiff ({j} : Finset (Fin m)) {k} := by
      simp [Finset.mem_symmDiff, Ne.symm hjk]
    rw [h, Finset.mem_singleton] at hj hk
    exact hjk (hj.trans hk.symm)

theorem symmDiff_singleton_eq_iff {i j k l : Fin m} (hij : i ≠ j) :
    symmDiff ({k} : Finset (Fin m)) {l} = symmDiff {i} {j} ↔
      (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  constructor
  · intro h
    have hi : i ∈ symmDiff ({k} : Finset (Fin m)) {l} := by
      rw [h]; simp [Finset.mem_symmDiff, hij]
    have hj : j ∈ symmDiff ({k} : Finset (Fin m)) {l} := by
      rw [h]; simp [Finset.mem_symmDiff, Ne.symm hij]
    simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hi hj
    rcases hi with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rcases hj with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact symmDiff_comm _ _

theorem lin_sq (c : Fin m → ℝ) (x : Cube m) :
    lin c x ^ 2 = ∑ i, ∑ j, c i * c j * chi (symmDiff {i} {j}) x := by
  rw [lin, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← chi_mul_chi]; ring

/-- The Fourier coefficients of `ℓ²`. -/
theorem sum_lin_sq_mul_chi (c : Fin m → ℝ) (T : Finset (Fin m)) :
    ∑ x, lin c x ^ 2 * chi T x =
      2 ^ m * ∑ i, ∑ j, if symmDiff {i} {j} = T then c i * c j else 0 := by
  simp_rw [lin_sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : ∀ x, c i * c j * chi (symmDiff {i} {j}) x * chi T x =
      c i * c j * (chi (symmDiff {i} {j}) x * chi T x) := fun x ↦ by ring
  simp_rw [this, ← Finset.mul_sum, sum_chi_mul_chi]
  split_ifs <;> ring

theorem sum_lin_sq (c : Fin m → ℝ) : ∑ x, lin c x ^ 2 = 2 ^ m * ∑ i, c i ^ 2 := by
  have h := sum_lin_sq_mul_chi c ∅
  simp only [chi, Finset.prod_empty, mul_one, symmDiff_singleton_eq_empty] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp [sq]

theorem sum_chi_eq (U : Finset (Fin m)) :
    ∑ x : Cube m, chi U x = if U = ∅ then (2 : ℝ) ^ m else 0 := by
  have h := sum_chi_mul_chi ∅ U
  simp only [chi, Finset.prod_empty, one_mul] at h
  simp only [chi]
  rw [h]
  simp only [eq_comm]

/-- `ℓ² - 1` has no Fourier mass on a nonempty `S` that is not `{i} ∆ {j}`. -/
theorem sum_D_mul_chi_eq_zero (c : Fin m → ℝ) {S : Finset (Fin m)} (hS : S ≠ ∅)
    (h : ∀ i j, symmDiff ({i} : Finset (Fin m)) {j} ≠ S) :
    ∑ x, (lin c x ^ 2 - 1) * chi S x = 0 := by
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, sum_lin_sq_mul_chi, sum_chi_eq]
  simp [h, hS]

theorem sum_D_mul_chi_of_two_lt (c : Fin m → ℝ) {S : Finset (Fin m)} (hS : 2 < S.card) :
    ∑ x, (lin c x ^ 2 - 1) * chi S x = 0 := by
  refine sum_D_mul_chi_eq_zero c ?_ fun i j h ↦ ?_
  · rintro rfl; simp at hS
  · have := card_symmDiff_singleton_le i j
    rw [h] at this
    omega

theorem sum_D_mul_lin (c : Fin m → ℝ) : ∑ x, (lin c x ^ 2 - 1) * lin c x = 0 := by
  simp_rw [lin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : ∀ x, (lin c x ^ 2 - 1) * (c i * chi {i} x) = c i * ((lin c x ^ 2 - 1) * chi {i} x) :=
    fun x ↦ by ring
  simp_rw [lin] at this
  simp_rw [this, ← Finset.mul_sum]
  have h := sum_D_mul_chi_eq_zero c (S := {i}) (Finset.singleton_ne_empty i)
    (fun j k ↦ symmDiff_singleton_ne_singleton i j k)
  simp only [lin] at h
  rw [h, mul_zero]

/-- The inner sum in the fourth moment. -/
theorem sum_sum_ite_symmDiff (c : Fin m → ℝ) (i j : Fin m) :
    (∑ k, ∑ l, if symmDiff {k} {l} = symmDiff ({i} : Finset (Fin m)) {j} then c k * c l
      else 0) = if i = j then ∑ k, c k ^ 2 else 2 * (c i * c j) := by
  split_ifs with hij
  · subst hij
    simp only [symmDiff_self, Finset.bot_eq_empty, symmDiff_singleton_eq_empty]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  · simp_rw [symmDiff_singleton_eq_iff hij]
    have : ∀ k l : Fin m, (if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then c k * c l else 0) =
        (if k = i then (if l = j then c k * c l else 0) else 0) +
          (if k = j then (if l = i then c k * c l else 0) else 0) := by
      intro k l
      by_cases hki : k = i <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
        by_cases hlj : l = j <;> simp_all
    simp_rw [this, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
    ring

/-- **The fourth moment**: `E (ℓ² - 1)² = (1 - ∑ cᵢ²)² + 2 ((∑ cᵢ²)² - ∑ cᵢ⁴)`. -/
theorem sum_D_sq (c : Fin m → ℝ) :
    ∑ x, (lin c x ^ 2 - 1) ^ 2 =
      2 ^ m * ((1 - ∑ i, c i ^ 2) ^ 2 + 2 * ((∑ i, c i ^ 2) ^ 2 - ∑ i, c i ^ 4)) := by
  have h4 : ∑ x, lin c x ^ 2 * lin c x ^ 2 =
      2 ^ m * (3 * (∑ i, c i ^ 2) ^ 2 - 2 * ∑ i, c i ^ 4) := by
    conv_lhs => enter [2, x, 2]; rw [lin_sq]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ x, ∑ j, lin c x ^ 2 * (c i * c j * chi (symmDiff {i} {j}) x) =
        ∑ j, c i * c j * ∑ x, lin c x ^ 2 * chi (symmDiff {i} {j}) x := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      ring
    simp_rw [this, sum_lin_sq_mul_chi, sum_sum_ite_symmDiff]
    have : ∀ i j : Fin m, c i * c j * (2 ^ m * if i = j then ∑ k, c k ^ 2 else 2 * (c i * c j)) =
        2 ^ m * (2 * (c i ^ 2 * c j ^ 2) +
          if i = j then c i ^ 2 * ∑ k, c k ^ 2 - 2 * c i ^ 4 else 0) := by
      intro i j
      split_ifs with h
      · subst h; ring
      · ring
    simp_rw [this, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    have e1 : ∑ x, ∑ y, 2 * (c x ^ 2 * c y ^ 2) = 2 * (∑ k, c k ^ 2) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    have e2 : ∑ x, (c x ^ 2 * ∑ k, c k ^ 2 - 2 * c x ^ 4) =
        (∑ k, c k ^ 2) ^ 2 - 2 * ∑ i, c i ^ 4 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sq]
    rw [e1, e2]
    ring
  have hexp : ∀ x, (lin c x ^ 2 - 1) ^ 2 = lin c x ^ 2 * lin c x ^ 2 - 2 * lin c x ^ 2 + 1 :=
    fun x ↦ by ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h4, sum_lin_sq]
  simp
  ring

/-! ### The Fourier coefficients of `v` at level one, and the rest -/

/-- The Fourier coefficients `v̂({i})` of level one. -/
noncomputable def cf (v : Cube m → ℝ) (i : Fin m) : ℝ := fourier v {i}

/-- `v̂(U)` for `|U| ≥ 2` and `0` otherwise: the Fourier coefficients of `v - ℓ - v̂(∅)`. -/
noncomputable def bb (v : Cube m → ℝ) (U : Finset (Fin m)) : ℝ :=
  if 2 ≤ U.card then fourier v U else 0

/-- The Fourier coefficient at `S` of `(v - ℓ - v̂(∅)) ℓ`: `∑ⱼ v̂({j}) b(S ∆ {j})`. -/
noncomputable def qq (v : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ j, cf v j * bb v (symmDiff S {j})

/-- The Fourier coefficient at `S` of `ℓ² - 1`. -/
noncomputable def pp (v : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  1 / 2 ^ m * ∑ x, chi S x * (lin (cf v) x ^ 2 - 1)

/-- The sets of size at most `2`. -/
noncomputable def F2 : Finset (Finset (Fin m)) := univ.filter fun S ↦ S.card ≤ 2

theorem sum_mul_chi_eq (g : Cube m → ℝ) (S : Finset (Fin m)) :
    ∑ x, g x * chi S x = 2 ^ m * fourier g S := by
  unfold fourier
  field_simp

theorem sum_lin_mul_chi (c : Fin m → ℝ) (U : Finset (Fin m)) :
    ∑ x, lin c x * chi U x = 2 ^ m * ∑ i, if {i} = U then c i else 0 := by
  simp_rw [lin, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_chi_mul_chi]
  split_ifs <;> ring

/-- The Fourier coefficients of `v - ℓ - v̂(∅)`. -/
theorem sum_rest_mul_chi (v : Cube m → ℝ) (U : Finset (Fin m)) :
    ∑ x, (v x - lin (cf v) x - fourier v ∅) * chi U x = 2 ^ m * bb v U := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_mul_chi_eq, sum_lin_mul_chi,
    ← Finset.mul_sum, sum_chi_eq, bb]
  by_cases h2 : 2 ≤ U.card
  · have hU : U ≠ ∅ := by rintro rfl; simp at h2
    have hi : ∀ i : Fin m, ({i} : Finset (Fin m)) ≠ U := by
      rintro i rfl; simp at h2
    simp [hU, hi, h2]
  · simp only [h2, ↓reduceIte]
    rcases Nat.lt_or_ge U.card 1 with h1 | h1
    · have hU : U = ∅ := Finset.card_eq_zero.1 (by omega)
      subst hU
      simp
      ring
    · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 (show U.card = 1 by omega)
      simp [Finset.singleton_inj, cf]

/-- The Fourier coefficients of `(v - ℓ - v̂(∅)) ℓ`. -/
theorem sum_rest_mul_lin_mul_chi (v : Cube m → ℝ) (S : Finset (Fin m)) :
    ∑ x, ((v x - lin (cf v) x - fourier v ∅) * lin (cf v) x) * chi S x = 2 ^ m * qq v S := by
  have : ∀ x, ((v x - lin (cf v) x - fourier v ∅) * lin (cf v) x) * chi S x =
      ∑ j, cf v j * ((v x - lin (cf v) x - fourier v ∅) * chi (symmDiff S {j}) x) := by
    intro x
    conv_lhs => enter [1, 2]; rw [lin]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← chi_mul_chi]
    ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_rest_mul_chi, qq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem bb_empty (v : Cube m → ℝ) : bb v ∅ = 0 := by simp [bb]

/-- **Parseval for `v - ℓ`**: `E (v - ℓ)² = v̂(∅)² + ∑_U b(U)²`. -/
theorem sum_sub_lin_sq (v : Cube m → ℝ) :
    ∑ x, (v x - lin (cf v) x) ^ 2 = 2 ^ m * (fourier v ∅ ^ 2 + ∑ U, bb v U ^ 2) := by
  set h : Cube m → ℝ := fun x ↦ v x - lin (cf v) x - fourier v ∅ with hh
  have hf : ∀ U, fourier h U = bb v U := by
    intro U
    have h1 := sum_rest_mul_chi v U
    rw [sum_mul_chi_eq (g := h)] at h1
    have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
    exact mul_left_cancel₀ h2m h1
  have hP := sum_sq_eq_sum_fourier h
  simp_rw [hf] at hP
  have h0 : ∑ x, h x = 0 := by
    have := sum_rest_mul_chi v ∅
    simp only [chi, Finset.prod_empty, mul_one, bb_empty, mul_zero] at this
    exact this
  have : ∀ x, (v x - lin (cf v) x) ^ 2 = h x ^ 2 + 2 * fourier v ∅ * h x + fourier v ∅ ^ 2 := by
    intro x; simp only [hh]; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0, hP]
  simp
  ring

/-- `E (v - ℓ)² = E v² - ∑ᵢ v̂({i})²`. -/
theorem sum_sub_lin_sq' (v : Cube m → ℝ) :
    ∑ x, (v x - lin (cf v) x) ^ 2 = ∑ x, v x ^ 2 - 2 ^ m * ∑ i, cf v i ^ 2 := by
  have hvl : ∑ x, v x * lin (cf v) x = 2 ^ m * ∑ i, cf v i ^ 2 := by
    simp_rw [lin, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : ∀ x, v x * (cf v i * chi {i} x) = cf v i * (v x * chi {i} x) := fun x ↦ by ring
    simp_rw [this, ← Finset.mul_sum, sum_mul_chi_eq, cf]
    ring
  have : ∀ x, (v x - lin (cf v) x) ^ 2 = v x ^ 2 - 2 * (v x * lin (cf v) x) + lin (cf v) x ^ 2 :=
    fun x ↦ by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hvl, sum_lin_sq]
  ring

theorem fourier_D (v : Cube m → ℝ) (S : Finset (Fin m)) :
    fourier (fun x ↦ lin (cf v) x ^ 2 - 1) S = pp v S := by
  unfold fourier pp
  rw [div_eq_inv_mul, one_div]
  congr 1
  exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _

theorem pp_eq_zero (v : Cube m → ℝ) {S : Finset (Fin m)} (hS : S ∉ (F2 : Finset (Finset (Fin m)))) :
    pp v S = 0 := by
  have h : 2 < S.card := by simpa [F2] using hS
  rw [← fourier_D]
  unfold fourier
  rw [sum_D_mul_chi_of_two_lt _ h, zero_div]

/-- **Parseval for `ℓ² - 1`**, whose Fourier coefficients vanish above level `2`. -/
theorem sum_pp_sq (v : Cube m → ℝ) :
    ∑ S ∈ F2, pp v S ^ 2 = 1 / 2 ^ m * ∑ x, (lin (cf v) x ^ 2 - 1) ^ 2 := by
  have hP := sum_sq_eq_sum_fourier (fun x ↦ lin (cf v) x ^ 2 - 1)
  simp_rw [fourier_D] at hP
  rw [hP, Finset.sum_subset (Finset.subset_univ _) fun S _ hS ↦ by rw [pp_eq_zero v hS]; ring]
  field_simp

/-- **Plancherel for `ℓ² - 1` and `(v - ℓ - v̂(∅)) ℓ`.** -/
theorem sum_pp_mul_qq (v : Cube m → ℝ) :
    ∑ S ∈ F2, pp v S * qq v S = 1 / 2 ^ m *
      ∑ x, (lin (cf v) x ^ 2 - 1) * ((v x - lin (cf v) x - fourier v ∅) * lin (cf v) x) := by
  have hP := sum_mul_eq_sum_fourier (fun x ↦ lin (cf v) x ^ 2 - 1)
    (fun x ↦ (v x - lin (cf v) x - fourier v ∅) * lin (cf v) x)
  have hq : ∀ S, fourier (fun x ↦ (v x - lin (cf v) x - fourier v ∅) * lin (cf v) x) S =
      qq v S := by
    intro S
    have h1 := sum_rest_mul_lin_mul_chi v S
    rw [sum_mul_chi_eq (g := fun x ↦ (v x - lin (cf v) x - fourier v ∅) * lin (cf v) x)] at h1
    have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
    exact mul_left_cancel₀ h2m h1
  simp_rw [fourier_D, hq] at hP
  rw [hP, Finset.sum_subset (Finset.subset_univ _) fun S _ hS ↦ by rw [pp_eq_zero v hS]; ring]
  field_simp

/-! ### Counting and Cauchy–Schwarz -/

/-- The number of `j` with `|U ∆ {j}| ≤ 2`. -/
noncomputable def cnt (U : Finset (Fin m)) : ℕ :=
  (univ.filter fun j ↦ (symmDiff U {j}).card ≤ 2).card

theorem cnt_le_three {U : Finset (Fin m)} (hU : 2 ≤ U.card) : cnt U ≤ 3 := by
  have key : ∀ j, (symmDiff U {j}).card ≤ 2 → j ∈ U ∧ U.card ≤ 3 := by
    intro j hj
    by_cases hjU : j ∈ U
    · have e : symmDiff U {j} = U.erase j := by
        ext k
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
          · exact ⟨h2, h1⟩
          · exact absurd hjU h2
        · rintro ⟨h1, h2⟩
          exact Or.inl ⟨h2, h1⟩
      rw [e, Finset.card_erase_of_mem hjU] at hj
      exact ⟨hjU, by omega⟩
    · have e : symmDiff U {j} = insert j U := by
        ext k
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro (⟨h1, _⟩ | ⟨rfl, _⟩)
          · exact Or.inr h1
          · exact Or.inl rfl
        · rintro (rfl | h1)
          · exact Or.inr ⟨rfl, hjU⟩
          · exact Or.inl ⟨h1, fun h ↦ hjU (h ▸ h1)⟩
      rw [e, Finset.card_insert_of_notMem hjU] at hj
      omega
  unfold cnt
  by_cases h : ∃ j, (symmDiff U {j}).card ≤ 2
  · obtain ⟨j, hj⟩ := h
    calc _ ≤ U.card := Finset.card_le_card fun k hk ↦ (key k (Finset.mem_filter.1 hk).2).1
      _ ≤ 3 := (key j hj).2
  · push Not at h
    rw [Finset.filter_false_of_mem fun j _ ↦ not_le.2 (h j)]
    simp

/-- Each `U` is `S ∆ {j}` for `cnt U` pairs `(S, j)` with `|S| ≤ 2`. -/
theorem sum_F2_sum_symmDiff (β : Finset (Fin m) → ℝ) :
    ∑ S ∈ F2, ∑ j, β (symmDiff S {j}) = ∑ U, (cnt U : ℝ) * β U := by
  rw [Finset.sum_comm]
  have : ∀ j : Fin m, ∑ S ∈ F2, β (symmDiff S {j}) =
      ∑ U, if (symmDiff U {j}).card ≤ 2 then β U else 0 := by
    intro j
    rw [F2, Finset.sum_filter]
    let e : Finset (Fin m) ≃ Finset (Fin m) :=
      ⟨fun S ↦ symmDiff S {j}, fun S ↦ symmDiff S {j},
        fun S ↦ symmDiff_symmDiff_cancel_right {j} S,
        fun S ↦ symmDiff_symmDiff_cancel_right {j} S⟩
    refine Fintype.sum_equiv e _ _ fun S ↦ ?_
    simp only [e, Equiv.coe_fn_mk, symmDiff_symmDiff_cancel_right]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt]

/-- **Lagrange's identity**, the sum-of-squares form of Cauchy–Schwarz. -/
theorem lagrange {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, x i ^ 2) * (∑ j ∈ s, y j ^ 2) - (∑ i ∈ s, x i * y i) ^ 2 =
      1 / 2 * ∑ i ∈ s, ∑ j ∈ s, (x i * y j - x j * y i) ^ 2 := by
  have e : ∑ i ∈ s, ∑ j ∈ s, (x i * y j - x j * y i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, x i ^ 2 * y j ^ 2 + ∑ i ∈ s, ∑ j ∈ s, x j ^ 2 * y i ^ 2 -
        2 * ∑ i ∈ s, ∑ j ∈ s, (x i * y i) * (x j * y j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h1 : ∑ i ∈ s, ∑ j ∈ s, x i ^ 2 * y j ^ 2 = (∑ i ∈ s, x i ^ 2) * ∑ j ∈ s, y j ^ 2 :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, x j ^ 2 * y i ^ 2 = (∑ i ∈ s, x i ^ 2) * ∑ j ∈ s, y j ^ 2 := by
    rw [Finset.sum_comm]; exact (Finset.sum_mul_sum _ _ _ _).symm
  have h3 : ∑ i ∈ s, ∑ j ∈ s, (x i * y i) * (x j * y j) = (∑ i ∈ s, x i * y i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [e, h1, h2, h3]
  ring

/-! ### The polynomials of the proof -/

/-- `ℓ(x) = ∑ᵢ f̂(i) χᵢ(x)`. -/
noncomputable def ellP (x : Cube m) : MvPolynomial (Cube m) ℝ := ∑ i, aP {i} * C (chi {i} x)

/-- `g(x) = f(x) - ℓ(x)`. -/
noncomputable def gP (x : Cube m) : MvPolynomial (Cube m) ℝ := X x - ellP x

/-- `D(x) = ℓ(x)² - 1`. -/
noncomputable def DP (x : Cube m) : MvPolynomial (Cube m) ℝ := ellP x ^ 2 - 1

/-- The Fourier coefficient of `D` at `S`. -/
noncomputable def PP (S : Finset (Fin m)) : MvPolynomial (Cube m) ℝ :=
  C (1 / 2 ^ m) * ∑ x, C (chi S x) * DP x

/-- `f̂(U)` for `|U| ≥ 2`, `0` otherwise. -/
noncomputable def bP (U : Finset (Fin m)) : MvPolynomial (Cube m) ℝ :=
  if 2 ≤ U.card then aP U else 0

/-- The Fourier coefficient of `(g - f̂(∅)) ℓ` at `S`. -/
noncomputable def QP (S : Finset (Fin m)) : MvPolynomial (Cube m) ℝ :=
  ∑ j, aP {j} * bP (symmDiff S {j})

/-- `∑_{|U| ≥ 2} f̂(U)²`. -/
noncomputable def ZP : MvPolynomial (Cube m) ℝ := ∑ U, bP U ^ 2

/-- `E g²`. -/
noncomputable def EgP : MvPolynomial (Cube m) ℝ := C (1 / 2 ^ m) * ∑ x, gP x ^ 2

/-- `∑ᵢ f̂(i)²`. -/
noncomputable def sP : MvPolynomial (Cube m) ℝ := ∑ i, aP {i} ^ 2

theorem eval_aP (v : Cube m → ℝ) (S : Finset (Fin m)) : eval v (aP S) = fourier v S := by
  simp only [aP, fcP, map_mul, map_sum, eval_C, eval_X, fourier, div_eq_inv_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

theorem eval_ellP (v : Cube m → ℝ) (x : Cube m) : eval v (ellP x) = lin (cf v) x := by
  simp [ellP, lin, cf, eval_aP]

theorem eval_gP (v : Cube m → ℝ) (x : Cube m) : eval v (gP x) = v x - lin (cf v) x := by
  simp [gP, eval_ellP]

theorem eval_DP (v : Cube m → ℝ) (x : Cube m) : eval v (DP x) = lin (cf v) x ^ 2 - 1 := by
  simp [DP, eval_ellP]

theorem eval_PP (v : Cube m → ℝ) (S : Finset (Fin m)) : eval v (PP S) = pp v S := by
  simp [PP, pp, eval_DP]

theorem eval_bP (v : Cube m → ℝ) (U : Finset (Fin m)) : eval v (bP U) = bb v U := by
  unfold bP bb
  split_ifs <;> simp [eval_aP]

theorem eval_QP (v : Cube m → ℝ) (S : Finset (Fin m)) : eval v (QP S) = qq v S := by
  simp [QP, qq, eval_bP, eval_aP, cf]

theorem eval_ZP (v : Cube m → ℝ) : eval v ZP = ∑ U, bb v U ^ 2 := by
  simp [ZP, eval_bP]

theorem eval_EgP (v : Cube m → ℝ) :
    eval v EgP = 1 / 2 ^ m * ∑ x, (v x - lin (cf v) x) ^ 2 := by
  simp [EgP, eval_gP]

theorem eval_sP (v : Cube m → ℝ) : eval v sP = ∑ i, fourier v {i} ^ 2 := by
  simp [sP, eval_aP]

/-! ### The certificate -/

/-- `∑_{|S| ≤ 2} (Q_S + P_S / 2)²`. -/
noncomputable def sos1 : MvPolynomial (Cube m) ℝ := ∑ S ∈ F2, (QP S + C (1 / 2) * PP S) ^ 2

/-- `E (g f + D / 2)²`. -/
noncomputable def sos2 : MvPolynomial (Cube m) ℝ :=
  C (1 / 2 ^ m) * ∑ x, (gP x * X x + C (1 / 2) * DP x) ^ 2

/-- Lagrange's identity for each `Q_S`. -/
noncomputable def sos3 : MvPolynomial (Cube m) ℝ :=
  C (1 / 2) * ∑ S ∈ F2, ∑ j, ∑ k,
    (aP {j} * bP (symmDiff S {k}) - aP {k} * bP (symmDiff S {j})) ^ 2

/-- The counting: `∑ᵢ f̂(i)² · ∑_U (3 - cnt U) b(U)²`. -/
noncomputable def sos4 : MvPolynomial (Cube m) ℝ :=
  sP * ∑ U, C (3 - (cnt U : ℝ)) * bP U ^ 2

/-- The multiplier of the ideal: `ℓ² + g² + 3 Z + 7`. -/
noncomputable def sig (x : Cube m) : MvPolynomial (Cube m) ℝ :=
  ellP x ^ 2 + gP x ^ 2 + C 3 * ZP + C 7



/-- Expanding `E[σ (f² - 1)]`, using `D + g ℓ + g f = f² - 1`. -/
theorem sum_ideal_expand (v L : Cube m → ℝ) (a Z : ℝ) (hDL : ∑ x, (L x ^ 2 - 1) * L x = 0) :
    1 / 2 ^ m * ∑ x, (L x ^ 2 + (v x - L x) ^ 2 + 3 * Z + 7) * (v x ^ 2 - 1) =
      1 / 2 ^ m * ∑ x, (L x ^ 2 - 1) ^ 2 +
        1 / 2 ^ m * ∑ x, (L x ^ 2 - 1) * ((v x - L x - a) * L x) +
        1 / 2 ^ m * ∑ x, (L x ^ 2 - 1) * (v x - L x) * v x +
        (8 + 3 * Z) * (1 / 2 ^ m * ∑ x, v x ^ 2 - 1) +
        1 / 2 ^ m * ∑ x, (v x - L x) ^ 2 * v x ^ 2 - 1 / 2 ^ m * ∑ x, (v x - L x) ^ 2 := by
  have hpt : ∀ x, (L x ^ 2 + (v x - L x) ^ 2 + 3 * Z + 7) * (v x ^ 2 - 1) =
      (L x ^ 2 - 1) ^ 2 + (L x ^ 2 - 1) * ((v x - L x - a) * L x) +
        (L x ^ 2 - 1) * (v x - L x) * v x + (8 + 3 * Z) * v x ^ 2 +
        (v x - L x) ^ 2 * v x ^ 2 - (v x - L x) ^ 2 + a * ((L x ^ 2 - 1) * L x) -
        (8 + 3 * Z) := fun x ↦ by ring
  rw [Finset.sum_congr rfl fun x _ ↦ hpt x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hDL,
    Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

/-- The certificate at a real point `v`. -/
theorem real_identity (v : Cube m → ℝ) :
    ∑ x, fourier v {x} ^ 4 - 1 + 10 * (1 - ∑ x, fourier v {x} ^ 2) =
      ∑ x ∈ F2, (qq v x + 1 / 2 * pp v x) ^ 2 +
        1 / 2 ^ m * ∑ x, ((v x - lin (cf v) x) * v x + 1 / 2 * (lin (cf v) x ^ 2 - 1)) ^ 2 +
        1 / 2 * ∑ x ∈ F2, ∑ x_1, ∑ x_2,
          (fourier v {x_1} * bb v (symmDiff x {x_2}) - fourier v {x_2} * bb v (symmDiff x {x_1}))
            ^ 2 +
        (∑ x, fourier v {x} ^ 2) * ∑ x, (3 - (cnt x : ℝ)) * bb v x ^ 2 +
        3 * ((1 / 2 ^ m * ∑ x, (v x - lin (cf v) x) ^ 2) * ∑ U, bb v U ^ 2) +
        3 * fourier v ∅ ^ 2 +
        3 / 2 * (1 - ∑ x, fourier v {x} ^ 2) ^ 2 +
        4 * (1 / 2 ^ m * ∑ x, (v x - lin (cf v) x) ^ 2) -
        1 / 2 ^ m * ∑ x, (lin (cf v) x ^ 2 + (v x - lin (cf v) x) ^ 2 + 3 * ∑ U, bb v U ^ 2 + 7) *
          (v x ^ 2 - 1) := by
  have f10 := sum_ideal_expand v (lin (cf v)) (fourier v ∅) (∑ U, bb v U ^ 2)
    (sum_D_mul_lin _)
  have f3 := sum_pp_sq v
  have f4 := sum_pp_mul_qq v
  have f7 : 1 / 2 ^ m * ∑ x, (v x - lin (cf v) x) ^ 2 = fourier v ∅ ^ 2 + ∑ U, bb v U ^ 2 := by
    rw [sum_sub_lin_sq]
    field_simp
  have f8 : 1 / 2 ^ m * ∑ x, v x ^ 2 - ∑ x, fourier v {x} ^ 2 =
      1 / 2 ^ m * ∑ x, (v x - lin (cf v) x) ^ 2 := by
    rw [sum_sub_lin_sq']
    simp only [cf]
    field_simp
  have f9 : 1 / 2 ^ m * ∑ x, (lin (cf v) x ^ 2 - 1) ^ 2 =
      (1 - ∑ x, fourier v {x} ^ 2) ^ 2 +
        2 * ((∑ x, fourier v {x} ^ 2) ^ 2 - ∑ x, fourier v {x} ^ 4) := by
    rw [sum_D_sq]
    simp only [cf]
    field_simp
  have f5 : 1 / 2 * ∑ S ∈ F2, ∑ j, ∑ k,
      (fourier v {j} * bb v (symmDiff S {k}) - fourier v {k} * bb v (symmDiff S {j})) ^ 2 =
      (∑ x, fourier v {x} ^ 2) * (∑ S ∈ F2, ∑ j, bb v (symmDiff S {j}) ^ 2) -
        ∑ S ∈ F2, qq v S ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← lagrange]
    rfl
  have f6 : ∑ U, (3 - (cnt U : ℝ)) * bb v U ^ 2 =
      3 * ∑ U, bb v U ^ 2 - ∑ S ∈ F2, ∑ j, bb v (symmDiff S {j}) ^ 2 := by
    rw [sum_F2_sum_symmDiff (fun U ↦ bb v U ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun U _ ↦ by ring
  set L := lin (cf v) with hL
  set a := fourier v ∅ with ha
  set Z := ∑ U, bb v U ^ 2 with hZ
  set s := ∑ x, fourier v {x} ^ 2 with hs
  set q := ∑ x, fourier v {x} ^ 4 with hq
  set Y := ∑ S ∈ F2, ∑ j, bb v (symmDiff S {j}) ^ 2 with hY
  have f1 : ∑ S ∈ F2, (qq v S + 1 / 2 * pp v S) ^ 2 = ∑ S ∈ F2, qq v S ^ 2 +
      ∑ S ∈ F2, pp v S * qq v S + 1 / 4 * ∑ S ∈ F2, pp v S ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ ↦ by ring
  have f2 : 1 / 2 ^ m * ∑ x, ((v x - L x) * v x + 1 / 2 * (L x ^ 2 - 1)) ^ 2 =
      1 / 2 ^ m * ∑ x, (v x - L x) ^ 2 * v x ^ 2 +
        1 / 2 ^ m * ∑ x, (L x ^ 2 - 1) * (v x - L x) * v x +
        1 / 4 * (1 / 2 ^ m * ∑ x, (L x ^ 2 - 1) ^ 2) := by
    have : ∑ x, ((v x - L x) * v x + 1 / 2 * (L x ^ 2 - 1)) ^ 2 =
        ∑ x, (v x - L x) ^ 2 * v x ^ 2 + ∑ x, (L x ^ 2 - 1) * (v x - L x) * v x +
          1 / 4 * ∑ x, (L x ^ 2 - 1) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [this]
    ring
  linear_combination (-1 : ℝ) * f1 + (-1 : ℝ) * f2 + (-1 / 4 : ℝ) * f3 + (-1 : ℝ) * f4 +
    (-1 : ℝ) * f5 + (-s) * f6 + 3 * f7 + (8 + 3 * Z) * f8 + (1 / 2 : ℝ) * f9 + f10

/-- The certificate: `goal = SOS - E[σ (f² - 1)]`. -/
theorem key_identity :
    (∑ i, aP {i} ^ 4 - 1 + 10 * (1 - ∑ i, aP {i} ^ 2) : MvPolynomial (Cube m) ℝ) =
      sos1 + sos2 + sos3 + sos4 + C 3 * (EgP * ZP) + C 3 * aP ∅ ^ 2 +
        C (3 / 2) * (1 - sP) ^ 2 + C 4 * EgP -
        C (1 / 2 ^ m) * ∑ x, sig x * (X x ^ 2 - 1) := by
  apply MvPolynomial.funext
  intro v
  simp only [sos1, sos2, sos3, sos4, sig, map_add, map_sub, map_mul, map_sum, map_pow, eval_C,
    eval_X, map_one, map_ofNat, eval_aP, eval_ellP, eval_gP, eval_DP, eval_PP, eval_bP, eval_QP,
    eval_ZP, eval_EgP, eval_sP]
  exact real_identity v

/-! ### Degrees and norms -/

section Bounds

variable {σ : Type*}

theorem deg_add {p q : MvPolynomial σ ℝ} {d : ℕ} (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d) : (p + q).totalDegree ≤ d :=
  (totalDegree_add p q).trans (max_le hp hq)

theorem deg_sub {p q : MvPolynomial σ ℝ} {d : ℕ} (hp : p.totalDegree ≤ d)
    (hq : q.totalDegree ≤ d) : (p - q).totalDegree ≤ d :=
  (totalDegree_sub p q).trans (max_le hp hq)

theorem deg_mul {p q : MvPolynomial σ ℝ} {a b : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)

theorem deg_C_mul (c : ℝ) {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.totalDegree ≤ d) :
    (C c * p).totalDegree ≤ d := by
  simpa using deg_mul (totalDegree_C c).le hp

theorem deg_mul_C (c : ℝ) {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.totalDegree ≤ d) :
    (p * C c).totalDegree ≤ d := by
  simpa using deg_mul hp (totalDegree_C c).le

theorem deg_sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ ℝ} {d : ℕ}
    (h : ∀ i ∈ s, (f i).totalDegree ≤ d) : (∑ i ∈ s, f i).totalDegree ≤ d :=
  totalDegree_finsetSum_le h

theorem deg_sq {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.totalDegree ≤ d) :
    (p ^ 2).totalDegree ≤ 2 * d :=
  (totalDegree_pow p 2).trans (Nat.mul_le_mul_left 2 hp)

theorem deg_one {d : ℕ} : (1 : MvPolynomial σ ℝ).totalDegree ≤ d := by simp

theorem deg_C {c : ℝ} {d : ℕ} : (C c : MvPolynomial σ ℝ).totalDegree ≤ d := by simp

theorem nm_add {p q : MvPolynomial σ ℝ} {a b : ℝ} (hp : coeffNorm1 p ≤ a)
    (hq : coeffNorm1 q ≤ b) : coeffNorm1 (p + q) ≤ a + b :=
  (coeffNorm1_add_le p q).trans (add_le_add hp hq)

theorem nm_sub {p q : MvPolynomial σ ℝ} {a b : ℝ} (hp : coeffNorm1 p ≤ a)
    (hq : coeffNorm1 q ≤ b) : coeffNorm1 (p - q) ≤ a + b :=
  (coeffNorm1_sub_le p q).trans (add_le_add hp hq)

theorem nm_mul {p q : MvPolynomial σ ℝ} {a b : ℝ} (hp : coeffNorm1 p ≤ a)
    (hq : coeffNorm1 q ≤ b) : coeffNorm1 (p * q) ≤ a * b :=
  (coeffNorm1_mul_le p q).trans
    (mul_le_mul hp hq (coeffNorm1_nonneg q) ((coeffNorm1_nonneg p).trans hp))

theorem nm_C_mul (c : ℝ) {p : MvPolynomial σ ℝ} {a : ℝ} (hp : coeffNorm1 p ≤ a) :
    coeffNorm1 (C c * p) ≤ |c| * a := by
  rw [coeffNorm1_C_mul]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg c)

theorem nm_sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ ℝ} {a : ℝ}
    (h : ∀ i ∈ s, coeffNorm1 (f i) ≤ a) : coeffNorm1 (∑ i ∈ s, f i) ≤ s.card * a :=
  (coeffNorm1_sum_le s f).trans ((Finset.sum_le_sum h).trans (by simp))

theorem nm_sq {p : MvPolynomial σ ℝ} {a : ℝ} (hp : coeffNorm1 p ≤ a) :
    coeffNorm1 (p ^ 2) ≤ a ^ 2 := by
  rw [sq, sq]
  exact nm_mul hp hp

theorem nm_C (c : ℝ) : coeffNorm1 (C c : MvPolynomial σ ℝ) ≤ |c| := (coeffNorm1_C c).le

end Bounds

theorem abs_chi_le (S : Finset (Fin m)) (x : Cube m) : |chi S x| ≤ 1 := by
  have h : |chi S x| ^ 2 = 1 := by rw [sq_abs]; exact chi_sq S x
  nlinarith [abs_nonneg (chi S x)]

theorem card_cube : ((univ : Finset (Cube m)).card : ℝ) = 2 ^ m := by simp

theorem card_sets : ((univ : Finset (Finset (Fin m))).card : ℝ) = 2 ^ m := by simp

theorem card_F2_le : ((F2 : Finset (Finset (Fin m))).card : ℝ) ≤ 2 ^ m := by
  rw [← card_sets]
  exact_mod_cast Finset.card_filter_le _ _

theorem card_fin_le : ((univ : Finset (Fin m)).card : ℝ) ≤ 2 ^ m := by
  rw [Finset.card_univ, Fintype.card_fin]
  exact_mod_cast (Nat.lt_two_pow_self).le

theorem one_le_two_pow : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)

theorem deg_aP (S : Finset (Fin m)) : (aP S).totalDegree ≤ 1 :=
  deg_C_mul _ (deg_sum _ fun x _ ↦ deg_C_mul _ (totalDegree_X x).le)

theorem nm_aP (S : Finset (Fin m)) : coeffNorm1 (aP S) ≤ 1 := by
  have h1 : coeffNorm1 (∑ x, C (chi S x) * X x : MvPolynomial (Cube m) ℝ) ≤
      (univ : Finset (Cube m)).card * 1 :=
    nm_sum _ fun x _ ↦ by rw [coeffNorm1_C_mul, coeffNorm1_X, mul_one]; exact abs_chi_le S x
  refine (nm_C_mul _ h1).trans (le_of_eq ?_)
  rw [card_cube, abs_of_pos (by positivity)]
  field_simp

theorem deg_ellP (x : Cube m) : (ellP x).totalDegree ≤ 1 :=
  deg_sum _ fun _ _ ↦ deg_mul_C _ (deg_aP _)

theorem nm_ellP (x : Cube m) : coeffNorm1 (ellP x) ≤ 2 ^ m := by
  refine (nm_sum (a := 1) _ fun i _ ↦ (nm_mul (nm_aP {i}) (nm_C (chi {i} x))).trans
    (by rw [one_mul]; exact abs_chi_le _ x)).trans ?_
  rw [mul_one]
  exact card_fin_le

theorem deg_gP (x : Cube m) : (gP x).totalDegree ≤ 1 :=
  deg_sub (totalDegree_X x).le (deg_ellP x)

theorem deg_DP (x : Cube m) : (DP x).totalDegree ≤ 2 :=
  deg_sub (deg_sq (deg_ellP x)) deg_one

theorem deg_PP (S : Finset (Fin m)) : (PP S).totalDegree ≤ 2 :=
  deg_C_mul _ (deg_sum _ fun x _ ↦ deg_C_mul _ (deg_DP x))

theorem deg_bP (U : Finset (Fin m)) : (bP U).totalDegree ≤ 1 := by
  unfold bP
  split_ifs
  · exact deg_aP U
  · simp

theorem nm_bP (U : Finset (Fin m)) : coeffNorm1 (bP U) ≤ 1 := by
  unfold bP
  split_ifs
  · exact nm_aP U
  · simp

theorem deg_QP (S : Finset (Fin m)) : (QP S).totalDegree ≤ 2 :=
  deg_sum _ fun _ _ ↦ deg_mul (deg_aP _) (deg_bP _)

theorem deg_ZP : (ZP : MvPolynomial (Cube m) ℝ).totalDegree ≤ 2 :=
  deg_sum _ fun U _ ↦ deg_sq (deg_bP U)

theorem deg_EgP : (EgP : MvPolynomial (Cube m) ℝ).totalDegree ≤ 2 :=
  deg_C_mul _ (deg_sum _ fun x _ ↦ deg_sq (deg_gP x))

theorem deg_sP : (sP : MvPolynomial (Cube m) ℝ).totalDegree ≤ 2 :=
  deg_sum _ fun _ _ ↦ deg_sq (deg_aP _)

theorem nm_gP (x : Cube m) : coeffNorm1 (gP x) ≤ 2 * 2 ^ m := by
  refine (nm_sub (coeffNorm1_X x).le (nm_ellP x)).trans ?_
  linarith [one_le_two_pow (m := m)]

theorem nm_DP (x : Cube m) : coeffNorm1 (DP x) ≤ 2 * (2 ^ m) ^ 2 := by
  refine (nm_sub (nm_sq (nm_ellP x)) coeffNorm1_one.le).trans ?_
  nlinarith [one_le_two_pow (m := m)]

theorem nm_PP (S : Finset (Fin m)) : coeffNorm1 (PP S) ≤ 2 * (2 ^ m) ^ 2 := by
  have h1 : coeffNorm1 (∑ x, C (chi S x) * DP x) ≤
      (univ : Finset (Cube m)).card * (2 * (2 ^ m) ^ 2) :=
    nm_sum _ fun x _ ↦ (nm_C_mul _ (nm_DP x)).trans (by
      have := abs_chi_le S x
      have : (0 : ℝ) ≤ 2 * (2 ^ m) ^ 2 := by positivity
      nlinarith)
  refine (nm_C_mul _ h1).trans (le_of_eq ?_)
  rw [card_cube, abs_of_pos (by positivity)]
  field_simp

theorem nm_QP (S : Finset (Fin m)) : coeffNorm1 (QP S) ≤ 2 ^ m := by
  refine (nm_sum (a := 1) _ fun j _ ↦ (nm_mul (nm_aP {j}) (nm_bP _)).trans
    (by norm_num)).trans ?_
  rw [mul_one]
  exact card_fin_le

theorem nm_ZP : coeffNorm1 (ZP : MvPolynomial (Cube m) ℝ) ≤ 2 ^ m := by
  refine (nm_sum (a := 1) _ fun U _ ↦ (nm_sq (nm_bP U)).trans (by norm_num)).trans ?_
  rw [mul_one, card_sets]

theorem nm_EgP : coeffNorm1 (EgP : MvPolynomial (Cube m) ℝ) ≤ 4 * (2 ^ m) ^ 2 := by
  have h1 : coeffNorm1 (∑ x, gP x ^ 2) ≤ (univ : Finset (Cube m)).card * (2 * 2 ^ m) ^ 2 :=
    nm_sum _ fun x _ ↦ nm_sq (nm_gP x)
  refine (nm_C_mul _ h1).trans (le_of_eq ?_)
  rw [card_cube, abs_of_pos (by positivity)]
  field_simp
  ring

theorem nm_sP : coeffNorm1 (sP : MvPolynomial (Cube m) ℝ) ≤ 2 ^ m := by
  refine (nm_sum (a := 1) _ fun i _ ↦ (nm_sq (nm_aP {i})).trans (by norm_num)).trans ?_
  rw [mul_one]
  exact card_fin_le

/-! ### The pieces of the proof -/

theorem isSOS_ZP : IsSOS (ZP : MvPolynomial (Cube m) ℝ) := IsSOS.sum _ fun _ _ ↦ IsSOS.sq _

theorem isSOS_EgP : IsSOS (EgP : MvPolynomial (Cube m) ℝ) :=
  (IsSOS.const (by positivity)).mul (IsSOS.sum _ fun _ _ ↦ IsSOS.sq _)

theorem isSOS_sig (x : Cube m) : IsSOS (sig x) :=
  (((IsSOS.sq _).add (IsSOS.sq _)).add ((IsSOS.const (by norm_num)).mul isSOS_ZP)).add
    (IsSOS.const (by norm_num))

theorem deg_sig (x : Cube m) : (sig x).totalDegree ≤ 2 :=
  deg_add (deg_add (deg_add ((deg_sq (deg_ellP x)).trans le_rfl)
    ((deg_sq (deg_gP x)).trans le_rfl)) (deg_C_mul _ deg_ZP)) deg_C

theorem nm_sig (x : Cube m) : coeffNorm1 (sig x) ≤ 15 * (2 ^ m) ^ 2 := by
  refine (nm_add (nm_add (nm_add (nm_sq (nm_ellP x)) (nm_sq (nm_gP x)))
    (nm_C_mul _ nm_ZP)) (nm_C 7)).trans ?_
  have h1 := one_le_two_pow (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by norm_num : (0 : ℝ) < 7)]
  nlinarith

variable (A : System (Cube m) ℝ)

/-- The Boolean constraint `X x² = 1`. -/
theorem boolEq (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A) (x : Cube m) :
    DerivesEq A 2 1 (X x ^ 2 - 1 : MvPolynomial (Cube m) ℝ) :=
  DerivesEq.of_mem (hbool x).1 (by rw [neg_sub]; exact (hbool x).2)
    (deg_sub ((deg_sq (totalDegree_X x).le).trans le_rfl) deg_one) le_rfl

/-- The multiple `E[σ (f² - 1)]` of the Boolean constraints. -/
theorem d_ideal (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A) :
    DerivesEq A 4 (15 * ((2 : ℝ) ^ m) ^ 5) (C (1 / 2 ^ m) * ∑ x, sig x * (X x ^ 2 - 1)) := by
  have hx : ∀ x ∈ (univ : Finset (Cube m)),
      DerivesEq A 4 (15 * (2 ^ m) ^ 2) (sig x * (X x ^ 2 - 1)) := by
    intro x _
    refine ((boolEq A hbool x).mulSOS (isSOS_sig x)).mono ?_ ?_
    · have := deg_sig x
      omega
    · rw [mul_one]
      exact nm_sig x
  refine ((DerivesEq.sum univ hx).smul (1 / 2 ^ m)).mono le_rfl ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_cube, abs_of_pos (by positivity)]
  have h1 := one_le_two_pow (m := m)
  have : (1 / 2 ^ m * (2 ^ m * (15 * (2 ^ m) ^ 2)) : ℝ) = 15 * (2 ^ m) ^ 2 := by
    field_simp
  rw [this]
  have h2 : ((2 : ℝ) ^ m) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  linarith

theorem d_sos1 : DerivesN A 4 (4 * ((2 : ℝ) ^ m) ^ 5) sos1 := by
  refine DerivesN.ofIsSOS A (IsSOS.sum _ fun _ _ ↦ IsSOS.sq _)
    (deg_sum _ fun S _ ↦ (deg_sq (deg_add (deg_QP S) (deg_C_mul _ (deg_PP S)))).trans le_rfl) ?_
  refine (nm_sum (a := (2 ^ m + |1 / 2| * (2 * (2 ^ m) ^ 2)) ^ 2) _ fun S _ ↦
    nm_sq (nm_add (nm_QP S) (nm_C_mul _ (nm_PP S)))).trans ?_
  have hc := card_F2_le (m := m)
  have h1 := one_le_two_pow (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  set t : ℝ := 2 ^ m
  have e1 : t + 1 / 2 * (2 * t ^ 2) ≤ 2 * t ^ 2 := by nlinarith
  have e2 : (t + 1 / 2 * (2 * t ^ 2)) ^ 2 ≤ (2 * t ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e1 2
  calc _ ≤ t * (2 * t ^ 2) ^ 2 := mul_le_mul hc e2 (by positivity) (by positivity)
    _ = 4 * t ^ 5 := by ring

theorem d_sos2 : DerivesN A 4 (9 * ((2 : ℝ) ^ m) ^ 5) sos2 := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by positivity)).mul
    (IsSOS.sum _ fun _ _ ↦ IsSOS.sq _)) (deg_C_mul _ (deg_sum _ fun x _ ↦
      (deg_sq (deg_add (deg_mul (deg_gP x) (totalDegree_X x).le)
        ((deg_C_mul _ (deg_DP x)).trans (by norm_num)))).trans le_rfl)) ?_
  have h0 : coeffNorm1 (∑ x, (gP x * X x + C (1 / 2) * DP x) ^ 2) ≤
      (univ : Finset (Cube m)).card * (2 * 2 ^ m * 1 + |1 / 2| * (2 * (2 ^ m) ^ 2)) ^ 2 :=
    nm_sum _ fun x _ ↦ nm_sq (nm_add (nm_mul (nm_gP x) (coeffNorm1_X x).le)
      (nm_C_mul _ (nm_DP x)))
  refine (nm_C_mul _ h0).trans ?_
  have h1 := one_le_two_pow (m := m)
  rw [card_cube, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (by positivity)]
  set t : ℝ := 2 ^ m
  have e1 : 2 * t * 1 + 1 / 2 * (2 * t ^ 2) ≤ 3 * t ^ 2 := by nlinarith
  have e2 : (2 * t * 1 + 1 / 2 * (2 * t ^ 2)) ^ 2 ≤ (3 * t ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e1 2
  have e3 : t ^ 4 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  have ht : t ≠ 0 := by positivity
  calc 1 / t * (t * (2 * t * 1 + 1 / 2 * (2 * t ^ 2)) ^ 2)
      = (2 * t * 1 + 1 / 2 * (2 * t ^ 2)) ^ 2 := by field_simp
    _ ≤ (3 * t ^ 2) ^ 2 := e2
    _ ≤ 9 * t ^ 5 := by nlinarith

theorem d_sos3 : DerivesN A 4 (2 * ((2 : ℝ) ^ m) ^ 5) sos3 := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by norm_num)).mul (IsSOS.sum _ fun _ _ ↦
    IsSOS.sum _ fun _ _ ↦ IsSOS.sum _ fun _ _ ↦ IsSOS.sq _))
    (deg_C_mul _ (deg_sum _ fun S _ ↦ deg_sum _ fun j _ ↦ deg_sum _ fun k _ ↦
      (deg_sq (deg_sub (deg_mul (deg_aP _) (deg_bP _)) (deg_mul (deg_aP _) (deg_bP _)))).trans
        le_rfl)) ?_
  have h0 : coeffNorm1 (∑ S ∈ F2, ∑ j, ∑ k,
      (aP {j} * bP (symmDiff S {k}) - aP {k} * bP (symmDiff S {j})) ^ 2) ≤
      (F2 : Finset (Finset (Fin m))).card * ((univ : Finset (Fin m)).card *
        ((univ : Finset (Fin m)).card * (1 * 1 + 1 * 1) ^ 2)) :=
    nm_sum _ fun S _ ↦ nm_sum _ fun j _ ↦ nm_sum _ fun k _ ↦
      nm_sq (nm_sub (nm_mul (nm_aP _) (nm_bP _)) (nm_mul (nm_aP _) (nm_bP _)))
  refine (nm_C_mul _ h0).trans ?_
  have h1 := one_le_two_pow (m := m)
  have hc := card_F2_le (m := m)
  have hf := card_fin_le (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  set t : ℝ := 2 ^ m
  have e3 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  have hf0 : (0 : ℝ) ≤ (univ : Finset (Fin m)).card := by positivity
  have hc0 : (0 : ℝ) ≤ (F2 : Finset (Finset (Fin m))).card := by positivity
  calc 1 / 2 * ((F2 : Finset (Finset (Fin m))).card * ((univ : Finset (Fin m)).card *
        ((univ : Finset (Fin m)).card * (1 * 1 + 1 * 1) ^ 2)))
      ≤ 1 / 2 * (t * (t * (t * (1 * 1 + 1 * 1) ^ 2))) := by gcongr
    _ = 2 * t ^ 3 := by ring
    _ ≤ 2 * t ^ 5 := by linarith

theorem d_sos4 : DerivesN A 4 (4 * ((2 : ℝ) ^ m) ^ 5) sos4 := by
  have hsos : ∀ U ∈ (univ : Finset (Finset (Fin m))),
      IsSOS (C (3 - (cnt U : ℝ)) * bP U ^ 2) := by
    intro U _
    by_cases h : 2 ≤ U.card
    · refine (IsSOS.const ?_).mul (IsSOS.sq _)
      have := cnt_le_three h
      have : (cnt U : ℝ) ≤ 3 := by exact_mod_cast this
      linarith
    · simp [bP, h, IsSOS.zero]
  refine DerivesN.ofIsSOS A ((IsSOS.sum _ fun _ _ ↦ IsSOS.sq _).mul (IsSOS.sum _ hsos))
    ((deg_mul deg_sP (deg_sum _ fun U _ ↦ deg_C_mul _ ((deg_sq (deg_bP U)).trans le_rfl))).trans
      le_rfl) ?_
  have h1 := one_le_two_pow (m := m)
  have hcnt : ∀ U : Finset (Fin m), |3 - (cnt U : ℝ)| ≤ 3 + 2 ^ m := by
    intro U
    have : (cnt U : ℝ) ≤ 2 ^ m := by
      refine le_trans ?_ (card_fin_le (m := m))
      exact_mod_cast Finset.card_filter_le _ _
    have h0 : (0 : ℝ) ≤ cnt U := by positivity
    rw [abs_le]
    constructor <;> linarith
  have h0 : coeffNorm1 (∑ U, C (3 - (cnt U : ℝ)) * bP U ^ 2) ≤
      (univ : Finset (Finset (Fin m))).card * (3 + 2 ^ m) :=
    nm_sum _ fun U _ ↦ (nm_C_mul _ (nm_sq (nm_bP U))).trans (by
      have := hcnt U
      nlinarith [abs_nonneg (3 - (cnt U : ℝ))])
  refine (nm_mul nm_sP h0).trans ?_
  rw [card_sets]
  set t : ℝ := 2 ^ m
  have e3 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  nlinarith

theorem d_sos5 : DerivesN A 4 (12 * ((2 : ℝ) ^ m) ^ 5) (C 3 * (EgP * ZP)) := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by norm_num)).mul (isSOS_EgP.mul isSOS_ZP))
    (deg_C_mul _ ((deg_mul deg_EgP deg_ZP).trans le_rfl)) ?_
  refine (nm_C_mul _ (nm_mul nm_EgP nm_ZP)).trans ?_
  have h1 := one_le_two_pow (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  set t : ℝ := 2 ^ m
  have e3 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  nlinarith

theorem d_sos6 : DerivesN A 4 (3 * ((2 : ℝ) ^ m) ^ 5) (C 3 * aP ∅ ^ 2) := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by norm_num)).mul (IsSOS.sq _))
    (deg_C_mul _ ((deg_sq (deg_aP _)).trans (by norm_num))) ?_
  refine (nm_C_mul _ (nm_sq (nm_aP _))).trans ?_
  have h1 := one_le_two_pow (m := m)
  have e3 : (1 : ℝ) ≤ ((2 : ℝ) ^ m) ^ 5 := one_le_pow₀ h1
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

theorem d_sos7 : DerivesN A 4 (6 * ((2 : ℝ) ^ m) ^ 5) (C (3 / 2) * (1 - sP) ^ 2) := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by norm_num)).mul (IsSOS.sq _))
    (deg_C_mul _ ((deg_sq (deg_sub deg_one deg_sP)).trans le_rfl)) ?_
  refine (nm_C_mul _ (nm_sq (nm_sub coeffNorm1_one.le nm_sP))).trans ?_
  have h1 := one_le_two_pow (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  set t : ℝ := 2 ^ m
  have e3 : t ^ 2 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  nlinarith

theorem d_sos8 : DerivesN A 4 (16 * ((2 : ℝ) ^ m) ^ 5) (C 4 * EgP) := by
  refine DerivesN.ofIsSOS A ((IsSOS.const (by norm_num)).mul isSOS_EgP)
    (deg_C_mul _ (deg_EgP.trans (by norm_num))) ?_
  refine (nm_C_mul _ nm_EgP).trans ?_
  have h1 := one_le_two_pow (m := m)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  set t : ℝ := 2 ^ m
  have e3 : t ^ 2 ≤ t ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  nlinarith

end FKN

/-- **The sum-of-squares FKN theorem**: from the Boolean constraints,
`∑ᵢ f̂(i)⁴ - 1 + 10 (1 - ∑ᵢ f̂(i)²) ≥ 0` in degree `4`. -/
theorem fkn {m : ℕ} (A : System (Cube m) ℝ) (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A) :
    DerivesN A 4 ((2 : ℝ) ^ (40 * (m + 4)))
      (∑ i, aP {i} ^ 4 - 1 + 10 * (1 - ∑ i, aP {i} ^ 2)) := by
  open FKN in
  have hsos := ((((((((d_sos1 A).add (d_sos2 A)).add (d_sos3 A)).add (d_sos4 A)).add
    (d_sos5 A)).add (d_sos6 A)).add (d_sos7 A)).add (d_sos8 A))
  have he := (d_ideal A hbool).neg.congr (q' := ∑ i, aP {i} ^ 4 - 1 +
    10 * (1 - ∑ i, aP {i} ^ 2) - (sos1 + sos2 + sos3 + sos4 + C 3 * (EgP * ZP) +
      C 3 * aP ∅ ^ 2 + C (3 / 2) * (1 - sP) ^ 2 + C 4 * EgP)) (by rw [key_identity]; ring)
  refine (hsos.of_eq he).mono le_rfl ?_
  have h1 : (1 : ℝ) ≤ 2 ^ m := FKN.one_le_two_pow
  have h2 : ((2 : ℝ) ^ m) ^ 5 * 2 ^ 7 ≤ 2 ^ (40 * (m + 4)) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (0 : ℝ) ≤ ((2 : ℝ) ^ m) ^ 5 := by positivity
  norm_num at h2
  linarith

end BMW26
