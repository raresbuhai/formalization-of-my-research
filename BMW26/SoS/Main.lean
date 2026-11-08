module

public import BMW26.SoS.FKN
public import Mathlib.Analysis.Matrix.Order

/-!
# The sum-of-squares certificate: level-one mass

[BMW26, Lemma 6.3 and Lemma 6.8], for a good sample `H` (`BMW26.Good`): the program proves, in
degree `4`, that its solutions have Fourier mass at least `1 - O(δ + τ₀ + ξ)` on the dictators
(`BMW26.level_one_mass`). This is what the rounding needs; it implies the quartic proxy of
[BMW26, Claim 6.10] through `BMW26.fkn`.

With `Λ = E_Q(f)/2^m`, `Λ' = E_H(f)/(p 2^m)`, `cᵢ = f̂(i)` and `g = f ∘ χᵢ`:

* (Lemma 6.4) `Λ - 2 = (E_{Q(i)}(g) - E_{Mᵢ}(g)) / 2^m` modulo the Boolean constraints, and the
  same for `H`;
* (Lemma 6.5) by the spectral closeness of `H` and of its half-cubes (`Good.full`, `Good.half`),
  `Λ - 2 ≤ Λ' - E_H(χᵢ)/(p 2^m) + 3 ε E_Q(g)/2^m + 3ξ`; the diagonal errors are constants on
  `±1`-valued `g`;
* (Lemma 6.7) `E_Q(g)/2^m ≤ (Λ - 2) + 4 (1 - cᵢ²)`;
* (Lemma 6.6) with `E_H(χᵢ) ≥ 2(1 - τ₀) p 2^m` (`Good.count`):
  `A ≤ 12 ε (1 - cᵢ²)` for `A = (1 - 3ε)(Λ - 2) - (Λ' - 2) - 2τ₀ - 3ξ`;
* (Lemma 6.9) multiplying by `cᵢ²` and summing, `A ≤ 12 ε (1 - ∑ᵢ cᵢ⁴)`; the product with
  `1 - ∑ᵢ cᵢ² = ∑_{|S| ≠ 1} f̂(S)²` (modulo the constraints) is a sum of squares times a derived
  inequality, so no product of two derived inequalities is needed;
* (FKN, `BMW26.fkn`) `1 - ∑ᵢ cᵢ⁴ ≤ 10 (1 - ∑ᵢ cᵢ²) ≤ 5 (Λ - 2)` (Lemma 6.8);
* the cut constraint gives `Λ' - 2 ≤ δ + 3τ₀`, so `(1 - 63 ε)(Λ - 2) ≤ δ + 5τ₀ + 3ξ`, and
  `∑ᵢ cᵢ² ≥ 1 - (Λ - 2)/2`.

In the proof (namespace `BMW26.Cert`), a quadratic form `∑_{u,v} Q_uv X_u X_v` that is
nonnegative at every real point is a sum of squares (`BMW26.Cert.IsQuadN.isSOS`, by the
factorization `Q = Bᵀ B` of positive semidefinite matrices); this gives the spectral bounds of
Lemma 6.5 and Jensen's inequality of Lemma 6.7 (`BMW26.Cert.dirSOS`). Polynomial identities are
checked at every real point (`MvPolynomial.funext`). The bound of one direction is
`BMW26.Cert.dir_bound`, Lemma 6.8 is `BMW26.Cert.energy_bound`, and the assembly is
`BMW26.Cert.level_one_mass_of_le`, for `ξ ≤ 1`.
-/

@[expose] public section

namespace BMW26.Cert

open Finset MvPolynomial SoS

/-! ### Quadratic forms -/

section Quad

variable {ι : Type*} [Fintype ι]

/-- A linear form `P = ∑ᵤ aᵤ Xᵤ` with `∑ᵤ |aᵤ| ≤ c`. -/
def IsLinN (P : MvPolynomial ι ℝ) (c : ℝ) : Prop :=
  ∃ a : ι → ℝ, P = ∑ u, C (a u) * X u ∧ ∑ u, |a u| ≤ c

/-- A quadratic form `P = ∑_{u,v} Q_{uv} Xᵤ X_v` with `∑_{u,v} |Q_{uv}| ≤ c`. -/
def IsQuadN (P : MvPolynomial ι ℝ) (c : ℝ) : Prop :=
  ∃ Q : ι → ι → ℝ, P = ∑ u, ∑ v, C (Q u v) * (X u * X v) ∧ ∑ u, ∑ v, |Q u v| ≤ c

namespace IsLinN

variable {P P' : MvPolynomial ι ℝ} {c c' : ℝ}

theorem nonneg (h : IsLinN P c) : 0 ≤ c := by
  obtain ⟨a, -, ha⟩ := h
  exact (sum_nonneg fun _ _ ↦ abs_nonneg _).trans ha

theorem mono (h : IsLinN P c) (hc : c ≤ c') : IsLinN P c' := by
  obtain ⟨a, rfl, ha⟩ := h
  exact ⟨a, rfl, ha.trans hc⟩

theorem X' (u : ι) : IsLinN (X u : MvPolynomial ι ℝ) 1 := by
  classical
  refine ⟨fun v ↦ if v = u then 1 else 0, ?_, ?_⟩
  · simp [apply_ite C]
  · simp only [apply_ite abs, abs_one, abs_zero, sum_ite_eq', mem_univ, ite_true, le_refl]

theorem add (h : IsLinN P c) (h' : IsLinN P' c') : IsLinN (P + P') (c + c') := by
  obtain ⟨a, rfl, ha⟩ := h
  obtain ⟨b, rfl, hb⟩ := h'
  refine ⟨fun u ↦ a u + b u, ?_, ?_⟩
  · rw [← sum_add_distrib]
    exact sum_congr rfl fun u _ ↦ by rw [C_add, add_mul]
  · calc ∑ u, |a u + b u| ≤ ∑ u, (|a u| + |b u|) := sum_le_sum fun u _ ↦ abs_add_le _ _
      _ ≤ c + c' := by rw [sum_add_distrib]; linarith

theorem smul (a : ℝ) (h : IsLinN P c) : IsLinN (C a * P) (|a| * c) := by
  obtain ⟨b, rfl, hb⟩ := h
  refine ⟨fun u ↦ a * b u, ?_, ?_⟩
  · rw [mul_sum]
    exact sum_congr rfl fun u _ ↦ by rw [C_mul, mul_assoc]
  · simp only [abs_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg a)

theorem neg (h : IsLinN P c) : IsLinN (-P) c := by
  have := h.smul (-1)
  simpa using this

theorem sub (h : IsLinN P c) (h' : IsLinN P' c') : IsLinN (P - P') (c + c') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

theorem sum {κ : Type*} (s : Finset κ) {P : κ → MvPolynomial ι ℝ} {c : κ → ℝ}
    (h : ∀ k ∈ s, IsLinN (P k) (c k)) : IsLinN (∑ k ∈ s, P k) (∑ k ∈ s, c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun k hk ↦ h k (mem_insert_of_mem hk))

theorem coeffNorm1_le (h : IsLinN P c) : coeffNorm1 P ≤ c := by
  obtain ⟨a, rfl, ha⟩ := h
  refine (coeffNorm1_sum_le _ _).trans (le_trans (sum_le_sum fun u _ ↦ ?_) ha)
  rw [coeffNorm1_C_mul, coeffNorm1_X, mul_one]

theorem totalDegree_le (h : IsLinN P c) : P.totalDegree ≤ 1 := by
  obtain ⟨a, rfl, -⟩ := h
  refine totalDegree_finsetSum_le fun u _ ↦ (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

end IsLinN

namespace IsQuadN

variable {P P' : MvPolynomial ι ℝ} {c c' : ℝ}

theorem nonneg (h : IsQuadN P c) : 0 ≤ c := by
  obtain ⟨Q, -, hQ⟩ := h
  exact (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _).trans hQ

theorem mono (h : IsQuadN P c) (hc : c ≤ c') : IsQuadN P c' := by
  obtain ⟨Q, rfl, hQ⟩ := h
  exact ⟨Q, rfl, hQ.trans hc⟩

theorem zero : IsQuadN (0 : MvPolynomial ι ℝ) 0 := ⟨0, by simp, by simp⟩

theorem add (h : IsQuadN P c) (h' : IsQuadN P' c') : IsQuadN (P + P') (c + c') := by
  obtain ⟨Q, rfl, hQ⟩ := h
  obtain ⟨R, rfl, hR⟩ := h'
  refine ⟨fun u v ↦ Q u v + R u v, ?_, ?_⟩
  · rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ ↦ by rw [C_add, add_mul]
  · calc ∑ u, ∑ v, |Q u v + R u v| ≤ ∑ u, ∑ v, (|Q u v| + |R u v|) :=
          sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ abs_add_le _ _
      _ ≤ c + c' := by simp only [sum_add_distrib]; linarith

theorem smul (a : ℝ) (h : IsQuadN P c) : IsQuadN (C a * P) (|a| * c) := by
  obtain ⟨Q, rfl, hQ⟩ := h
  refine ⟨fun u v ↦ a * Q u v, ?_, ?_⟩
  · simp only [mul_sum]
    exact sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ by rw [C_mul, mul_assoc]
  · simp only [abs_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left hQ (abs_nonneg a)

theorem neg (h : IsQuadN P c) : IsQuadN (-P) c := by
  simpa using h.smul (-1)

theorem sub (h : IsQuadN P c) (h' : IsQuadN P' c') : IsQuadN (P - P') (c + c') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

theorem sum {κ : Type*} (s : Finset κ) {P : κ → MvPolynomial ι ℝ} {c : κ → ℝ}
    (h : ∀ k ∈ s, IsQuadN (P k) (c k)) : IsQuadN (∑ k ∈ s, P k) (∑ k ∈ s, c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun k hk ↦ h k (mem_insert_of_mem hk))

/-- The product of two linear forms. -/
theorem mul {L L' : MvPolynomial ι ℝ} (h : IsLinN L c) (h' : IsLinN L' c') :
    IsQuadN (L * L') (c * c') := by
  have hc := h.nonneg
  obtain ⟨a, rfl, ha⟩ := h
  obtain ⟨b, rfl, hb⟩ := h'
  refine ⟨fun u v ↦ a u * b v, ?_, ?_⟩
  · rw [sum_mul_sum]
    exact sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ by rw [C_mul]; ring
  · simp only [abs_mul, ← mul_sum, ← sum_mul]
    exact mul_le_mul ha hb (sum_nonneg fun _ _ ↦ abs_nonneg _) hc

theorem sq {L : MvPolynomial ι ℝ} (h : IsLinN L c) : IsQuadN (L ^ 2) (c ^ 2) := by
  rw [pow_two, pow_two]
  exact IsQuadN.mul h h

theorem _root_.BMW26.Cert.IsLinN.sq {L : MvPolynomial ι ℝ} (h : IsLinN L c) :
    IsQuadN (L ^ 2) (c ^ 2) :=
  IsQuadN.sq h

theorem coeffNorm1_le (h : IsQuadN P c) : coeffNorm1 P ≤ c := by
  obtain ⟨Q, rfl, hQ⟩ := h
  refine (coeffNorm1_sum_le _ _).trans (le_trans (sum_le_sum fun u _ ↦ ?_) hQ)
  refine (coeffNorm1_sum_le _ _).trans (sum_le_sum fun v _ ↦ ?_)
  rw [coeffNorm1_C_mul]
  refine (mul_le_mul_of_nonneg_left (coeffNorm1_mul_le _ _) (abs_nonneg _)).trans ?_
  rw [coeffNorm1_X, coeffNorm1_X, mul_one, mul_one]

theorem totalDegree_le (h : IsQuadN P c) : P.totalDegree ≤ 2 := by
  obtain ⟨Q, rfl, -⟩ := h
  refine totalDegree_finsetSum_le fun u _ ↦ totalDegree_finsetSum_le fun v _ ↦ ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X, totalDegree_X]

theorem eval_eq {Q : ι → ι → ℝ} (y : ι → ℝ) :
    eval y (∑ u, ∑ v, C (Q u v) * (X u * X v)) = ∑ u, ∑ v, Q u v * (y u * y v) := by
  simp [map_sum]

end IsQuadN

/-- A Gram form: `∑_{v, w} (∑_{u ∈ s} K_uv K_uw) p_v p_w = ∑_{u ∈ s} (∑_v K_uv p_v)²`.
(From `BKS23.Spectral.sum_sum_gram`, `BKS23/SpectralCertificate.lean`.) -/
theorem sum_sum_gram {R κ : Type*} [CommRing R] (f : ℝ →+* R) (s : Finset κ) (K : κ → ι → ℝ)
    (p : ι → R) :
    ∑ v, ∑ w, f (∑ u ∈ s, K u v * K u w) * (p v * p w) =
      ∑ u ∈ s, (∑ v, f (K u v) * p v) ^ 2 := by
  calc _ = ∑ v, ∑ u ∈ s, ∑ w, f (K u v * K u w) * (p v * p w) :=
        sum_congr rfl fun v _ ↦ by simp_rw [map_sum, sum_mul]; exact sum_comm
    _ = ∑ u ∈ s, ∑ v, ∑ w, f (K u v * K u w) * (p v * p w) := sum_comm
    _ = _ := sum_congr rfl fun u _ ↦ by
        rw [sq, sum_mul_sum]
        exact sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ by rw [map_mul]; ring

/-- Symmetrizing the coefficients does not change a quadratic form. -/
theorem sum_sum_symm {R : Type*} [CommRing R] (f : ℝ →+* R) (Q : ι → ι → ℝ) (p : ι → R) :
    ∑ u, ∑ v, f ((Q u v + Q v u) / 2) * (p u * p v) = ∑ u, ∑ v, f (Q u v) * (p u * p v) := by
  have h2 : ∑ u, ∑ v, f (Q v u) * (p u * p v) = ∑ u, ∑ v, f (Q u v) * (p u * p v) := by
    rw [sum_comm]
    exact sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ by ring
  have h1 : ∑ u, ∑ v, f ((Q u v + Q v u) / 2) * (p u * p v) =
      f (1 / 2) * (∑ u, ∑ v, f (Q u v) * (p u * p v) +
        ∑ u, ∑ v, f (Q v u) * (p u * p v)) := by
    rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun v _ ↦ ?_
    rw [show (Q u v + Q v u) / 2 = 1 / 2 * Q u v + 1 / 2 * Q v u by ring, map_add, map_mul,
      map_mul]
    ring
  rw [h1, h2, ← two_mul, ← mul_assoc, ← map_ofNat f 2, ← map_mul]
  norm_num

open scoped MatrixOrder in
/-- **A nonnegative quadratic form is a sum of squares** (adapted from
`BKS23.Spectral.isSOS_of_sum_sq_le`, `BKS23/SpectralCertificate.lean`): the symmetrized
coefficient matrix is positive semidefinite, hence `Bᵀ B` (Mathlib). -/
theorem IsQuadN.isSOS {P : MvPolynomial ι ℝ} {c : ℝ} (h : IsQuadN P c)
    (hP : ∀ y, 0 ≤ eval y P) : IsSOS P := by
  classical
  obtain ⟨Q, rfl, -⟩ := h
  set Q' : Matrix ι ι ℝ := Matrix.of fun u v ↦ (Q u v + Q v u) / 2 with hQ'
  have hpsd : Q'.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun v w ↦ ?_)
      fun y ↦ ?_
    · simp only [hQ', Matrix.of_apply, star_trivial]
      ring
    · have : dotProduct (star y) (Q'.mulVec y) = ∑ u, ∑ v, Q' u v * (y u * y v) := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, mul_sum]
        exact sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ by ring
      rw [this]
      have e := sum_sum_symm (RingHom.id ℝ) Q y
      simp only [RingHom.id_apply] at e
      simp only [hQ', Matrix.of_apply]
      rw [e, ← IsQuadN.eval_eq]
      exact hP y
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  have hQB : ∀ u v, Q' u v = ∑ l, B l u * B l v := fun u v ↦ by
    have := congrFun (congrFun hB u) v
    simpa [Matrix.mul_apply, Matrix.star_apply] using this
  have e := sum_sum_symm C Q X
  rw [← e]
  have hQB' : ∀ u v, (Q u v + Q v u) / 2 = ∑ l, B l u * B l v := hQB
  simp_rw [hQB']
  rw [sum_sum_gram C univ B X]
  exact IsSOS.sum _ fun l _ ↦ IsSOS.sq _

end Quad

variable {m : ℕ}

/-! ### Sums over the hypercube -/

/-- A sum over the cube as a sum over the edges of direction `i`, at their lower endpoints. -/
theorem sum_pairs {M : Type*} [AddCommMonoid M] (i : Fin m) (F : Cube m → M) :
    ∑ x, F x = ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (F x + F (flip x i)) := by
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not univ (fun x : Cube m ↦ x i = false)]
  congr 1
  refine sum_nbij' (fun x ↦ flip x i) (fun x ↦ flip x i) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [flip_apply_self]
    simpa using hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [flip_apply_self, hx]
    simp
  · intro x _; exact flip_flip x i
  · intro x _; exact flip_flip x i
  · intro x _; rw [flip_flip]

theorem card_cube : (Fintype.card (Cube m) : ℝ) = 2 ^ m := by
  simp [Cube]

/-- Half of the vertices are lower endpoints of the edges of direction `i`. -/
theorem card_low (i : Fin m) :
    ((univ.filter (fun x : Cube m ↦ x i = false)).card : ℝ) = 2 ^ m / 2 := by
  have h := sum_pairs i (fun _ ↦ (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [card_cube] at h
  linarith

theorem chi_abs (S : Finset (Fin m)) (x : Cube m) : |chi S x| = 1 := by
  have h := chi_sq S x
  have h0 := abs_nonneg (chi S x)
  have h1 : |chi S x| ^ 2 = 1 := by rw [sq_abs]; exact h
  nlinarith

/-! ### Polynomials -/

/-- The energy of the edges of direction `i`: `∑_{xᵢ = false} w i x (X x - X (flip x i))²`. -/
noncomputable def mMinus (w : Fin m → Cube m → ℝ) (i : Fin m) : MvPolynomial (Cube m) ℝ :=
  ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), C (w i x) * (X x - X (flip x i)) ^ 2

/-- The energy of the edges of direction `i` for `f ∘ χᵢ`: `∑_{xᵢ = false} w i x (X x + X (flip
x i))²`. -/
noncomputable def mPlus (w : Fin m → Cube m → ℝ) (i : Fin m) : MvPolynomial (Cube m) ℝ :=
  ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), C (w i x) * (X x + X (flip x i)) ^ 2

/-- The diagonal form `∑ₓ D x X x²`. -/
noncomputable def sqSum (D : Cube m → ℝ) : MvPolynomial (Cube m) ℝ := ∑ x, C (D x) * X x ^ 2

theorem energyP_eq (w : Fin m → Cube m → ℝ) (i : Fin m) :
    energyP w = energyP (halfW i w) + mMinus w i := by
  simp only [energyP, mMinus]
  rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have h1 : ∀ j ∈ univ.erase i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x j = false),
      C (halfW i w j x) * (X x - X (flip x j)) ^ 2 =
      ∑ x ∈ univ.filter (fun x : Cube m ↦ x j = false), C (w j x) * (X x - X (flip x j)) ^ 2 :=
    fun j hj ↦ sum_congr rfl fun x _ ↦ by simp [halfW, ne_of_mem_erase hj]
  rw [sum_congr rfl h1]
  simp [halfW, add_comm]

theorem fcP_singleton (i : Fin m) :
    fcP {i} = ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (X x - X (flip x i)) := by
  rw [fcP, sum_pairs i]
  refine sum_congr rfl fun x hx ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hx
  rw [chi_singleton, chi_singleton, flip_apply_self, hx]
  simp [sgn]
  ring

theorem eval_energyP (w : Fin m → Cube m → ℝ) (y : Cube m → ℝ) :
    eval y (energyP w) = energy w y := by
  simp [energyP, energy, map_sum]

theorem eval_sqSum (D : Cube m → ℝ) (y : Cube m → ℝ) :
    eval y (sqSum D) = ∑ x, D x * y x ^ 2 := by
  simp [sqSum, map_sum]

theorem eval_aP (S : Finset (Fin m)) (y : Cube m → ℝ) : eval y (aP S) = fourier y S := by
  simp only [aP, fcP, fourier, map_mul, eval_C, map_sum, eval_X]
  rw [sum_congr rfl fun x _ ↦ mul_comm (chi S x) (y x)]
  ring

/-- The energy of `f ∘ χᵢ`. -/
theorem eval_energyP_sgn (w : Fin m → Cube m → ℝ) (i : Fin m) (y : Cube m → ℝ) :
    eval y (energyP (halfW i w) + mPlus w i) = energy w (fun x ↦ sgn (x i) * y x) := by
  simp only [map_add, eval_energyP, mPlus, map_sum, map_mul, eval_C, map_pow, eval_X, energy]
  rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have h1 : ∀ j ∈ univ.erase i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x j = false),
      halfW i w j x * (y x - y (flip x j)) ^ 2 =
      ∑ x ∈ univ.filter (fun x : Cube m ↦ x j = false),
        w j x * (sgn (x i) * y x - sgn (flip x j i) * y (flip x j)) ^ 2 := by
    intro j hj
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [halfW, ne_of_mem_erase hj, ite_false]
    rw [flip_apply_ne _ (Ne.symm (ne_of_mem_erase hj))]
    have := sgn_sq (x i)
    linear_combination (w j x * (y x - y (flip x j)) ^ 2) * (-this)
  have h2 : ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), w i x * (y x + y (flip x i)) ^ 2 =
      ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false),
        w i x * (sgn (x i) * y x - sgn (flip x i i) * y (flip x i)) ^ 2 := by
    refine sum_congr rfl fun x hx ↦ ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [flip_apply_self, hx]
    simp [sgn]
  rw [sum_congr rfl h1, ← h2]
  simp [halfW]
  ring


theorem sum_graphW_low (H : SimpleGraph (Cube m)) (i : Fin m) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), graphW H i x = (dirCount H i : ℝ) := by
  classical
  simp only [graphW, dirCount]
  rw [sum_boole, filter_filter]

theorem sum_one_low (i : Fin m) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (1 : Fin m → Cube m → ℝ) i x =
      2 ^ m / 2 := by
  simp only [Pi.one_apply, sum_const, nsmul_eq_mul, mul_one, card_low]

/-! ### The polynomials of the argument -/

/-- `Λ - 2`, with `Λ = E_Q(f) / 2^m`. -/
noncomputable def lamP (m : ℕ) : MvPolynomial (Cube m) ℝ := C (1 / 2 ^ m) * energyP 1 - 2

/-- `Λ' - 2`, with `Λ' = E_H(f) / (p 2^m)`. -/
noncomputable def lamP' (H : SimpleGraph (Cube m)) (p : ℝ) : MvPolynomial (Cube m) ℝ :=
  C (1 / (p * 2 ^ m)) * energyP (graphW H) - 2

/-- `(1 - 3ε)(Λ - 2) - (Λ' - 2) - 2τ₀ - 3ξ`. -/
noncomputable def aPoly (H : SimpleGraph (Cube m)) (p ε ξ τ₀ : ℝ) : MvPolynomial (Cube m) ℝ :=
  C (1 - 3 * ε) * lamP m - lamP' H p - C (2 * τ₀ + 3 * ξ)

/-- The Boolean defect of the edges of direction `i`: `0` on `±1` points. -/
noncomputable def boolDir (w : Fin m → Cube m → ℝ) (i : Fin m) : MvPolynomial (Cube m) ℝ :=
  mPlus w i + mMinus w i - C (4 * ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), w i x)

/-- The Boolean defect of a diagonal form: `0` on `±1` points. -/
noncomputable def boolDiag (D : Cube m → ℝ) : MvPolynomial (Cube m) ℝ :=
  sqSum D - C (∑ x, D x)

/-- The spectral bound of the half-cubes (Lemma 6.5): nonnegative when `H` is good. -/
noncomputable def specHalf (H : SimpleGraph (Cube m)) (p ε : ℝ) (D : Cube m → ℝ) (i : Fin m) :
    MvPolynomial (Cube m) ℝ :=
  C (ε * p) * energyP (halfW i 1) + sqSum D +
    (energyP (halfW i (graphW H)) - C p * energyP (halfW i 1))

/-- The spectral bound of the whole cube for `f ∘ χᵢ` (Lemma 6.5): nonnegative when `H` is
good. -/
noncomputable def specFull (H : SimpleGraph (Cube m)) (p ε : ℝ) (D : Cube m → ℝ) (i : Fin m) :
    MvPolynomial (Cube m) ℝ :=
  C (ε * p) * (energyP (halfW i 1) + mPlus 1 i) + sqSum D -
    ((energyP (halfW i (graphW H)) + mPlus (graphW H) i) - C p * (energyP (halfW i 1) + mPlus 1 i))

/-- Jensen's inequality on the matching of direction `i` (Lemma 6.7). -/
noncomputable def jensenP (i : Fin m) : MvPolynomial (Cube m) ℝ :=
  mMinus 1 i - C (2 / 2 ^ m) * fcP {i} ^ 2

/-- The sum of squares of the bound of direction `i`. -/
noncomputable def dirSOS (H : SimpleGraph (Cube m)) (p ε : ℝ) (D D' : Cube m → ℝ) (i : Fin m) :
    MvPolynomial (Cube m) ℝ :=
  C 2 * specHalf H p ε D' i + specFull H p ε D i + C (2 * ε * p) * mPlus 1 i +
    C (6 * ε * p) * jensenP i

theorem dir_identity {H : SimpleGraph (Cube m)} {p ε ξ τ₀ : ℝ} (hp : p ≠ 0)
    (D D' : Cube m → ℝ) (i : Fin m) :
    C (12 * ε) * (1 - aP {i} ^ 2) - aPoly H p ε ξ τ₀ =
      C (1 / (p * 2 ^ m)) * (dirSOS H p ε D D' i + C (4 * (dirCount H i : ℝ) - 2 * (p * 2 ^ m) +
        2 * τ₀ * (p * 2 ^ m) + 3 * ξ * (p * 2 ^ m) - 2 * ∑ x, D' x - ∑ x, D x)) -
      C (1 / (p * 2 ^ m)) * (C ((1 + 3 * ε) * p) * boolDir 1 i + C 2 * boolDiag D' +
        boolDiag D - boolDir (graphW H) i) := by
  refine MvPolynomial.funext fun y ↦ ?_
  have e1 := congrArg (eval y) (energyP_eq (1 : Fin m → Cube m → ℝ) i)
  have e2 := congrArg (eval y) (energyP_eq (graphW H) i)
  simp only [map_add] at e1 e2
  have ha : eval y (aP {i}) = 1 / 2 ^ m * eval y (fcP {i}) := by simp [aP]
  simp only [aPoly, lamP, lamP', dirSOS, specHalf, specFull, jensenP, boolDir, boolDiag,
    map_add, map_sub, map_mul, eval_C, map_one, map_pow, map_ofNat, sum_graphW_low,
    sum_one_low, ha, e1, e2]
  have hn : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-! ### Norms of the polynomials -/

theorem sum_low_le (i : Fin m) {f : Cube m → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), f x ≤ c * (2 ^ m / 2) := by
  calc _ ≤ ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), c := sum_le_sum fun x _ ↦ hf x
    _ = c * (2 ^ m / 2) := by rw [sum_const, nsmul_eq_mul, card_low, mul_comm]

theorem isLinN_X_sub (a b : Cube m) : IsLinN (X a - X b : MvPolynomial (Cube m) ℝ) 2 := by
  classical
  exact ((IsLinN.X' a).sub (IsLinN.X' b)).mono (by norm_num)

theorem isLinN_X_add (a b : Cube m) : IsLinN (X a + X b : MvPolynomial (Cube m) ℝ) 2 := by
  classical
  exact ((IsLinN.X' a).add (IsLinN.X' b)).mono (by norm_num)

theorem isQuadN_mMinus {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) (i : Fin m) :
    IsQuadN (mMinus w i) (2 * 2 ^ m) := by
  refine (IsQuadN.sum _ fun x _ ↦ ((isLinN_X_sub x (flip x i)).sq.smul (w i x))).mono ?_
  refine (sum_low_le i (c := 4) fun x ↦ ?_).trans (le_of_eq (by ring))
  nlinarith [hw i x, abs_nonneg (w i x)]

theorem isQuadN_mPlus {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) (i : Fin m) :
    IsQuadN (mPlus w i) (2 * 2 ^ m) := by
  refine (IsQuadN.sum _ fun x _ ↦ ((isLinN_X_add x (flip x i)).sq.smul (w i x))).mono ?_
  refine (sum_low_le i (c := 4) fun x ↦ ?_).trans (le_of_eq (by ring))
  nlinarith [hw i x, abs_nonneg (w i x)]

theorem energyP_eq_sum (w : Fin m → Cube m → ℝ) : energyP w = ∑ i, mMinus w i := rfl

theorem isQuadN_energyP {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) :
    IsQuadN (energyP w) (2 * m * 2 ^ m) := by
  rw [energyP_eq_sum]
  refine (IsQuadN.sum univ fun i _ ↦ isQuadN_mMinus hw i).mono (le_of_eq ?_)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem isQuadN_sqSum (D : Cube m → ℝ) : IsQuadN (sqSum D) (∑ x, |D x|) := by
  classical
  refine (IsQuadN.sum univ fun x _ ↦ ((IsLinN.X' x).sq.smul (D x))).mono (le_of_eq ?_)
  simp

theorem isLinN_fcP (S : Finset (Fin m)) : IsLinN (fcP S) (2 ^ m) := by
  classical
  refine (IsLinN.sum univ fun x _ ↦ (IsLinN.X' x).smul (chi S x)).mono (le_of_eq ?_)
  simp [chi_abs]

theorem isLinN_aP (S : Finset (Fin m)) : IsLinN (aP S) 1 := by
  refine ((isLinN_fcP S).smul (1 / 2 ^ m)).mono (le_of_eq ?_)
  rw [abs_of_pos (by positivity)]
  field_simp

theorem abs_one_le (i : Fin m) (x : Cube m) : |(1 : Fin m → Cube m → ℝ) i x| ≤ 1 := by simp

theorem abs_graphW_le (H : SimpleGraph (Cube m)) (i : Fin m) (x : Cube m) :
    |graphW H i x| ≤ 1 := by
  unfold graphW; split_ifs <;> simp

theorem abs_halfW_le {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) (i j : Fin m)
    (x : Cube m) : |halfW i w j x| ≤ 1 := by
  unfold halfW; split_ifs
  · simp
  · exact hw j x

theorem isQuadN_specHalf {H : SimpleGraph (Cube m)} {p ε : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {D : Cube m → ℝ} (hD : ∑ x, |D x| ≤ 2 ^ m) (hm : 1 ≤ m)
    (i : Fin m) : IsQuadN (specHalf H p ε D i) (8 * m * 2 ^ m) := by
  have h1 := isQuadN_energyP (abs_halfW_le abs_one_le i)
  have hH := isQuadN_energyP (abs_halfW_le (abs_graphW_le H) i)
  refine (((h1.smul (ε * p)).add (isQuadN_sqSum D)).add (hH.sub (h1.smul p))).mono ?_
  rw [abs_of_nonneg (mul_nonneg hε hp), abs_of_nonneg hp]
  have hK : (0 : ℝ) ≤ m * 2 ^ m := by positivity
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ^ m ≤ m * 2 ^ m := le_mul_of_one_le_left (by positivity) hm'
  have hεp : ε * p ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hεp hK, mul_le_mul_of_nonneg_right hp1 hK]

theorem isQuadN_specFull {H : SimpleGraph (Cube m)} {p ε : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {D : Cube m → ℝ} (hD : ∑ x, |D x| ≤ 2 ^ m) (hm : 1 ≤ m)
    (i : Fin m) : IsQuadN (specFull H p ε D i) (16 * m * 2 ^ m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ^ m ≤ m * 2 ^ m := le_mul_of_one_le_left (by positivity) hm'
  have hG1 : IsQuadN (energyP (halfW i 1) + mPlus 1 i) (4 * m * 2 ^ m) :=
    ((isQuadN_energyP (abs_halfW_le abs_one_le i)).add (isQuadN_mPlus abs_one_le i)).mono
      (by nlinarith)
  have hGH : IsQuadN (energyP (halfW i (graphW H)) + mPlus (graphW H) i) (4 * m * 2 ^ m) :=
    ((isQuadN_energyP (abs_halfW_le (abs_graphW_le H) i)).add
      (isQuadN_mPlus (abs_graphW_le H) i)).mono (by nlinarith)
  refine (((hG1.smul (ε * p)).add (isQuadN_sqSum D)).sub (hGH.sub (hG1.smul p))).mono ?_
  rw [abs_of_nonneg (mul_nonneg hε hp), abs_of_nonneg hp]
  have hK : (0 : ℝ) ≤ m * 2 ^ m := by positivity
  have hεp : ε * p ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hεp hK, mul_le_mul_of_nonneg_right hp1 hK]

theorem isQuadN_jensenP (i : Fin m) : IsQuadN (jensenP i) (4 * 2 ^ m) := by
  refine ((isQuadN_mMinus abs_one_le i).sub ((isLinN_fcP {i}).sq.smul (2 / 2 ^ m))).mono
    (le_of_eq ?_)
  rw [abs_of_pos (by positivity)]
  field_simp
  ring

theorem isQuadN_dirSOS {H : SimpleGraph (Cube m)} {p ε : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {D D' : Cube m → ℝ} (hD : ∑ x, |D x| ≤ 2 ^ m)
    (hD' : ∑ x, |D' x| ≤ 2 ^ m) (hm : 1 ≤ m) (i : Fin m) :
    IsQuadN (dirSOS H p ε D D' i) (64 * m * 2 ^ m) := by
  refine (((((isQuadN_specHalf hp hp1 hε hε1 hD' hm i).smul 2).add
    (isQuadN_specFull hp hp1 hε hε1 hD hm i)).add ((isQuadN_mPlus abs_one_le i).smul _)).add
    ((isQuadN_jensenP i).smul _)).mono ?_
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε * p),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * ε * p), abs_two]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ^ m ≤ m * 2 ^ m := le_mul_of_one_le_left (by positivity) hm'
  have hn : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hεp : ε * p ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hεp hn]

/-! ### Nonnegativity of the spectral bounds -/

theorem eval_specFull_nonneg {H : SimpleGraph (Cube m)} {p ε : ℝ} {D : Cube m → ℝ}
    (hD : SpecClose (graphW H) 1 p ε D) (i : Fin m) (y : Cube m → ℝ) :
    0 ≤ eval y (specFull H p ε D i) := by
  have h1 := eval_energyP_sgn (1 : Fin m → Cube m → ℝ) i y
  have hH := eval_energyP_sgn (graphW H) i y
  have hs := hD (fun x ↦ sgn (x i) * y x)
  have hsq : ∑ x, D x * (sgn (x i) * y x) ^ 2 = ∑ x, D x * y x ^ 2 :=
    sum_congr rfl fun x _ ↦ by rw [mul_pow, sgn_sq, one_mul]
  rw [hsq] at hs
  simp only [specFull, map_add, map_sub, map_mul, eval_C, eval_sqSum] at h1 hH ⊢
  rw [h1, hH]
  linarith [le_abs_self (energy (graphW H) (fun x ↦ sgn (x i) * y x) -
    p * energy 1 (fun x ↦ sgn (x i) * y x))]

theorem eval_specHalf_nonneg {H : SimpleGraph (Cube m)} {p ε : ℝ} {D : Cube m → ℝ} {i : Fin m}
    (hD : SpecClose (halfW i (graphW H)) (halfW i 1) p ε D) (y : Cube m → ℝ) :
    0 ≤ eval y (specHalf H p ε D i) := by
  have hs := hD y
  simp only [specHalf, map_add, map_sub, map_mul, eval_C, eval_sqSum, eval_energyP]
  linarith [neg_abs_le (energy (halfW i (graphW H)) y - p * energy (halfW i 1) y)]

theorem eval_jensenP_nonneg (i : Fin m) (y : Cube m → ℝ) : 0 ≤ eval y (jensenP i) := by
  have h := sq_sum_le_card_mul_sum_sq (s := univ.filter (fun x : Cube m ↦ x i = false))
    (f := fun x ↦ y x - y (flip x i))
  rw [card_low] at h
  simp only [jensenP, mMinus, fcP_singleton, map_sub, map_mul, map_sum, map_pow, eval_C, eval_X,
    Pi.one_apply, one_mul]
  have hn : (0 : ℝ) < 2 ^ m := by positivity
  rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hn]
  nlinarith

theorem eval_mPlus_nonneg (i : Fin m) (y : Cube m → ℝ) : 0 ≤ eval y (mPlus 1 i) := by
  simp only [mPlus, map_sum, map_mul, map_pow, map_add, eval_C, eval_X, Pi.one_apply, one_mul]
  exact sum_nonneg fun _ _ ↦ sq_nonneg _

theorem isSOS_dirSOS {H : SimpleGraph (Cube m)} {p ε : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {D D' : Cube m → ℝ} (hD : ∑ x, |D x| ≤ 2 ^ m)
    (hD' : ∑ x, |D' x| ≤ 2 ^ m) (hm : 1 ≤ m) (i : Fin m)
    (hfull : SpecClose (graphW H) 1 p ε D)
    (hhalf : SpecClose (halfW i (graphW H)) (halfW i 1) p ε D') :
    IsSOS (dirSOS H p ε D D' i) := by
  refine (isQuadN_dirSOS hp hp1 hε hε1 hD hD' hm i).isSOS fun y ↦ ?_
  simp only [dirSOS, map_add, map_mul, eval_C]
  have := eval_specHalf_nonneg hhalf y
  have := eval_specFull_nonneg hfull i y
  have := eval_mPlus_nonneg i y
  have := eval_jensenP_nonneg i y
  have : 0 ≤ ε * p := mul_nonneg hε hp
  positivity

/-! ### Booleanity -/

theorem totalDegree_bool (x : Cube m) : (X x ^ 2 - 1 : MvPolynomial (Cube m) ℝ).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (by simp))
    (by simp))

theorem boolDir_eq (w : Fin m → Cube m → ℝ) (i : Fin m) :
    boolDir w i = ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false),
        C (2 * w i x) * (X x ^ 2 - 1) +
      ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false),
        C (2 * w i x) * (X (flip x i) ^ 2 - 1) := by
  rw [boolDir, mPlus, mMinus, mul_sum, map_sum, ← sum_add_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  simp only [map_mul, map_ofNat]
  ring

section Bool

variable {A : System (Cube m) ℝ} (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A)
include hbool

/-- The Boolean constraints, with coefficients. -/
theorem derivesEq_bool {κ : Type*} (s : Finset κ) (φ : κ → Cube m) (a : κ → ℝ) :
    DerivesEq A 2 (∑ k ∈ s, |a k|) (∑ k ∈ s, C (a k) * (X (φ k) ^ 2 - 1)) := by
  refine DerivesEq.sum s fun k _ ↦ ?_
  have h := DerivesEq.of_mem (hbool (φ k)).1 (by rw [neg_sub]; exact (hbool (φ k)).2)
    (totalDegree_bool (φ k)) le_rfl
  simpa using h.smul (a k)

theorem derivesEq_boolDir {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) (i : Fin m) :
    DerivesEq A 2 (2 * 2 ^ m) (boolDir w i) := by
  rw [boolDir_eq]
  refine ((derivesEq_bool hbool _ id _).add (derivesEq_bool hbool _ (fun x ↦ flip x i) _)).mono
    le_rfl ?_
  have h : ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), |2 * w i x| ≤ 2 * (2 ^ m / 2) :=
    sum_low_le i fun x ↦ by rw [abs_mul, abs_two]; linarith [hw i x]
  linarith

theorem derivesEq_boolDiag (D : Cube m → ℝ) : DerivesEq A 2 (∑ x, |D x|) (boolDiag D) := by
  have h := derivesEq_bool hbool univ id D
  refine h.congr ?_
  simp only [boolDiag, sqSum, map_sum, id, mul_sub, mul_one, sum_sub_distrib]

end Bool

/-! ### The bound of one direction (Lemmas 6.4–6.7) -/

theorem count_facts {H : SimpleGraph (Cube m)} {p ε ξ τ₀ : ℝ} (hp : 0 < p) (hτ₀1 : τ₀ ≤ 1 / 4)
    (good : Good H p ε ξ τ₀) (i : Fin m) :
    1 ≤ p * 2 ^ m ∧ (dirCount H i : ℝ) ≤ (1 + τ₀) * (p * 2 ^ m / 2) ∧
      (1 - τ₀) * (p * 2 ^ m / 2) ≤ dirCount H i := by
  have h := abs_le.1 (good.count i)
  have hpn : 0 < p * 2 ^ m := by positivity
  have hlo : (1 - τ₀) * (p * 2 ^ m / 2) ≤ dirCount H i := by linarith [h.1]
  have hhi : (dirCount H i : ℝ) ≤ (1 + τ₀) * (p * 2 ^ m / 2) := by linarith [h.2]
  have hpos : (0 : ℝ) < dirCount H i := lt_of_lt_of_le (by nlinarith) hlo
  have h1 : (1 : ℝ) ≤ dirCount H i := Nat.one_le_cast.2 (Nat.cast_pos.1 hpos)
  refine ⟨?_, hhi, hlo⟩
  nlinarith

theorem dir_bound {H : SimpleGraph (Cube m)} {p ε ξ τ₀ : ℝ} (hm : 1 ≤ m) (hp : 0 < p)
    (hp1 : p ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hξ1 : ξ ≤ 1) (hτ₀1 : τ₀ ≤ 1 / 4)
    (good : Good H p ε ξ τ₀) {A : System (Cube m) ℝ}
    (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A) (i : Fin m) :
    DerivesN A 2 (128 * m * 2 ^ m) (C (12 * ε) * (1 - aP {i} ^ 2) - aPoly H p ε ξ τ₀) := by
  obtain ⟨D, hD0, hDs, hDc⟩ := good.full
  obtain ⟨D', hD0', hDs', hDc'⟩ := good.half i
  obtain ⟨hpn, hcnt1, hcnt2⟩ := count_facts hp hτ₀1 good i
  have hn : (0 : ℝ) < 2 ^ m := by positivity
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (2 : ℝ) ^ m ≤ m * 2 ^ m := le_mul_of_one_le_left hn.le hm'
  have hξp : ξ * p * 2 ^ m ≤ 2 ^ m := by
    have : ξ * p ≤ 1 := by nlinarith
    nlinarith
  have hDa : ∑ x, |D x| ≤ 2 ^ m := by
    simp only [abs_of_nonneg (hD0 _)]; linarith
  have hDa' : ∑ x, |D' x| ≤ 2 ^ m := by
    simp only [abs_of_nonneg (hD0' _)]; linarith
  have hDp : 0 ≤ ∑ x, D x := sum_nonneg fun x _ ↦ hD0 x
  have hDp' : 0 ≤ ∑ x, D' x := sum_nonneg fun x _ ↦ hD0' x
  set c : ℝ := 4 * (dirCount H i : ℝ) - 2 * (p * 2 ^ m) + 2 * τ₀ * (p * 2 ^ m) +
    3 * ξ * (p * 2 ^ m) - 2 * ∑ x, D' x - ∑ x, D x with hc
  have hc0 : 0 ≤ c := by nlinarith
  have hc1 : c ≤ 6 * 2 ^ m := by nlinarith
  have hq0 : 0 < 1 / (p * 2 ^ m) := by positivity
  have hq1 : 1 / (p * 2 ^ m) ≤ 1 := by rw [div_le_one (by positivity)]; exact hpn
  have hQ := isQuadN_dirSOS (H := H) hp.le hp1 hε hε1 hDa hDa' hm i
  have hsos := isSOS_dirSOS hp.le hp1 hε hε1 hDa hDa' hm i hDc hDc'
  -- the sum of squares
  have h1 : DerivesN A 2 (1 / (p * 2 ^ m) * (64 * m * 2 ^ m + c))
      (C (1 / (p * 2 ^ m)) * (dirSOS H p ε D D' i + C c)) := by
    refine DerivesN.ofIsSOS A ((IsSOS.const hq0.le).mul (hsos.add (IsSOS.const hc0))) ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_add _ _).trans (max_le hQ.totalDegree_le (by simp))
    · rw [coeffNorm1_C_mul, abs_of_pos hq0]
      refine mul_le_mul_of_nonneg_left ((coeffNorm1_add_le _ _).trans ?_) hq0.le
      rw [coeffNorm1_C, abs_of_nonneg hc0]
      linarith [hQ.coeffNorm1_le]
  -- the Boolean constraints
  have h2 := (((((derivesEq_boolDir hbool abs_one_le i).smul ((1 + 3 * ε) * p)).add
    ((derivesEq_boolDiag hbool D').smul 2)).add (derivesEq_boolDiag hbool D)).sub
    (derivesEq_boolDir hbool (abs_graphW_le H) i)).smul (1 / (p * 2 ^ m))
  have h3 : DerivesN A 2 _ (C (12 * ε) * (1 - aP {i} ^ 2) - aPoly H p ε ξ τ₀) :=
    h1.of_eq (h2.neg.congr (by rw [dir_identity hp.ne' D D' i, hc]; ring))
  refine h3.mono le_rfl ?_
  rw [abs_of_pos hq0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + 3 * ε) * p), abs_two]
  have e1 : (1 + 3 * ε) * p ≤ 4 := by nlinarith
  have e2 : 1 / (p * 2 ^ m) * (64 * m * 2 ^ m + c) ≤ 64 * m * 2 ^ m + c := by
    have : 0 ≤ 64 * m * 2 ^ m + c := by positivity
    nlinarith
  have e3 : (1 + 3 * ε) * p * (2 * 2 ^ m) ≤ 4 * (2 * 2 ^ m) :=
    mul_le_mul_of_nonneg_right e1 (by positivity)
  have e4 : 1 / (p * 2 ^ m) * ((1 + 3 * ε) * p * (2 * 2 ^ m) + 2 * ∑ x, |D' x| +
      ∑ x, |D x| + 2 * 2 ^ m) ≤ (1 + 3 * ε) * p * (2 * 2 ^ m) + 2 * ∑ x, |D' x| +
      ∑ x, |D x| + 2 * 2 ^ m := by
    have : 0 ≤ (1 + 3 * ε) * p * (2 * 2 ^ m) + 2 * ∑ x, |D' x| + ∑ x, |D x| + 2 * 2 ^ m := by
      positivity
    nlinarith
  nlinarith

/-! ### The cut constraint -/

theorem totalDegree_energyP_le {w : Fin m → Cube m → ℝ} (hw : ∀ i x, |w i x| ≤ 1) :
    (energyP w).totalDegree ≤ 2 :=
  (isQuadN_energyP hw).totalDegree_le

theorem isSOS_energyP {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) : IsSOS (energyP w) :=
  IsSOS.sum _ fun i _ ↦ IsSOS.sum _ fun x _ ↦ (IsSOS.const (hw i x)).mul (IsSOS.sq _)

/-- The cut constraint gives `Λ' - 2 ≤ δ + 3τ₀`. -/
theorem cut_bound {H : SimpleGraph (Cube m)} {p ε ξ τ₀ δ : ℝ} (hm : 1 ≤ m) (hp : 0 < p)
    (hτ₀ : 0 ≤ τ₀) (hτ₀1 : τ₀ ≤ 1 / 4) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (good : Good H p ε ξ τ₀)
    {A : System (Cube m) ℝ} (hcut : cutPolyCube H δ ∈ A) :
    DerivesN A 2 5 (C (δ + 3 * τ₀) - lamP' H p) := by
  have hcount : ∀ i, (dirCount H i : ℝ) ≤ (1 + τ₀) * (p * 2 ^ m / 2) :=
    fun i ↦ (count_facts hp hτ₀1 good i).2.1
  have hpn := (count_facts hp hτ₀1 good ⟨0, hm⟩).1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hE : ∑ i, (dirCount H i : ℝ) ≤ m * ((1 + τ₀) * (p * 2 ^ m / 2)) := by
    calc ∑ i, (dirCount H i : ℝ) ≤ ∑ _i : Fin m, (1 + τ₀) * (p * 2 ^ m / 2) :=
          sum_le_sum fun i _ ↦ hcount i
      _ = _ := by simp
  have hmpn : 0 < (m : ℝ) * (p * 2 ^ m) := by positivity
  set E := ∑ i, (dirCount H i : ℝ) with hEdef
  set c₂ := δ + 3 * τ₀ + 2 - (2 + δ) * 2 * E / (m * (p * 2 ^ m)) with hc₂
  have key : (2 + δ) * 2 * E ≤ (δ + 3 * τ₀ + 2) * (m * (p * 2 ^ m)) := by
    have h1 := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ (2 + δ) * 2)
    have h2 : (2 + δ) * (1 + τ₀) ≤ δ + 3 * τ₀ + 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hmpn.le]
  have hc₀ : 0 ≤ c₂ := by
    rw [hc₂, sub_nonneg, div_le_iff₀ hmpn]
    exact key
  have hE0 : 0 ≤ E := sum_nonneg fun i _ ↦ Nat.cast_nonneg _
  have hc₁ : c₂ ≤ 4 := by
    have : 0 ≤ (2 + δ) * 2 * E / (m * (p * 2 ^ m)) := by positivity
    linarith
  have hdeg : (cutPolyCube H δ).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega)
      ((totalDegree_mul _ _).trans ?_))
    rw [totalDegree_C, zero_add]
    exact totalDegree_energyP_le (abs_graphW_le H)
  have hq0 : 0 ≤ 1 / (m * (p * 2 ^ m)) := by positivity
  have hq1 : 1 / (m * (p * 2 ^ m)) ≤ 1 := by
    rw [div_le_one hmpn]; nlinarith
  have h := ((DerivesN.of_mem hcut hdeg le_rfl).smul hq0).add
    (DerivesN.ofIsSOS A (IsSOS.const hc₀) (by simp) (by rw [coeffNorm1_C, abs_of_nonneg hc₀]))
  refine (h.congr ?_).mono le_rfl (by linarith)
  refine MvPolynomial.funext fun y ↦ ?_
  simp only [cutPolyCube, lamP', hc₂, hEdef, map_add, map_sub, map_mul, eval_C, map_ofNat]
  have hn : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Fourier analysis (Lemma 6.8) -/

theorem sum_card_one {M : Type*} [AddCommMonoid M] (g : Finset (Fin m) → M) :
    ∑ S, (if S.card = 1 then g S else 0) = ∑ i, g {i} := by
  rw [← sum_filter, ← powerset_univ, ← powersetCard_eq_filter, powersetCard_one, sum_map]
  rfl

/-- **Parseval** for the program's variables. -/
theorem sum_aP_sq : ∑ S, aP S ^ 2 = C (1 / 2 ^ m) * ∑ x : Cube m, X x ^ 2 := by
  refine MvPolynomial.funext fun y ↦ ?_
  simp only [map_sum, map_pow, eval_aP, map_mul, eval_C, eval_X]
  rw [sum_sq_eq_sum_fourier y]
  field_simp

theorem aP_empty : aP (∅ : Finset (Fin m)) = C (1 / 2 ^ m) * ∑ x : Cube m, X x := by
  simp [aP, fcP, chi]

/-- The Fourier weights `2|S| - 4 + 2·𝟙[|S| = 1] + 4·𝟙[S = ∅] ≥ 0`. -/
noncomputable def cS (S : Finset (Fin m)) : ℝ :=
  2 * S.card - 4 + (if S.card = 1 then 2 else 0) + (if S = ∅ then 4 else 0)

theorem cS_nonneg (S : Finset (Fin m)) : 0 ≤ cS S := by
  unfold cS
  by_cases h0 : S = ∅
  · subst h0; simp
  · have h1 : 1 ≤ S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
    by_cases h2 : S.card = 1
    · simp [h0, h2]; norm_num
    · have h3 : (2 : ℝ) ≤ S.card := by exact_mod_cast (by omega : 2 ≤ S.card)
      simp only [h0, h2, ite_false]
      linarith

theorem cS_le (S : Finset (Fin m)) : cS S ≤ 2 * m + 2 := by
  unfold cS
  have : (S.card : ℝ) ≤ m := by exact_mod_cast (card_le_univ S).trans (by simp)
  split_ifs <;> linarith

/-- The polynomial identity of Lemma 6.8: `Λ - 2 - 2 (1 - ∑ᵢ cᵢ²)` is a nonnegative combination of
the `f̂(S)²`, modulo `f̂(∅) = 0` and Parseval. -/
theorem fourier_identity :
    lamP m - 2 * (1 - ∑ i, aP {i} ^ 2) =
      ∑ S, C (cS S) * aP S ^ 2 - C 4 * aP ∅ ^ 2 + C 4 * (∑ S, aP S ^ 2 - 1) := by
  refine MvPolynomial.funext fun y ↦ ?_
  simp only [lamP, map_sub, map_add, map_mul, map_sum, map_pow, eval_C, map_one, map_ofNat,
    eval_aP, eval_energyP, energy_one_eq]
  have h1 : ∑ S, cS S * fourier y S ^ 2 = ∑ S, 2 * (S.card : ℝ) * fourier y S ^ 2 -
      4 * ∑ S, fourier y S ^ 2 + 2 * ∑ i, fourier y {i} ^ 2 + 4 * fourier y ∅ ^ 2 := by
    have e1 := sum_card_one (fun S ↦ fourier y S ^ 2)
    have e2 : ∑ S : Finset (Fin m), (if S = ∅ then fourier y S ^ 2 else 0) = fourier y ∅ ^ 2 := by
      simp
    have e3 : ∑ S, cS S * fourier y S ^ 2 = ∑ S, (2 * (S.card : ℝ) * fourier y S ^ 2 -
        4 * fourier y S ^ 2 + 2 * (if S.card = 1 then fourier y S ^ 2 else 0) +
        4 * (if S = ∅ then fourier y S ^ 2 else 0)) :=
      sum_congr rfl fun S _ ↦ by unfold cS; split_ifs <;> ring
    rw [e3, sum_add_distrib, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
      e1, e2]
  rw [h1]
  have hn : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-! ### The Boolean and balance constraints in degree `4` -/

/-- The sum of the Boolean defects, `∑ₓ (X x² - 1)`. -/
noncomputable def boolSum (m : ℕ) : MvPolynomial (Cube m) ℝ := ∑ x : Cube m, (X x ^ 2 - 1)

/-- The Fourier mass off level `1`: `∑_{|S| ≠ 1} f̂(S)²`. -/
noncomputable def highP (m : ℕ) : MvPolynomial (Cube m) ℝ :=
  ∑ S : Finset (Fin m), C (if S.card = 1 then (0 : ℝ) else 1) * aP S ^ 2

theorem isQuadN_highP : IsQuadN (highP m) (2 ^ m) := by
  refine (IsQuadN.sum univ fun S _ ↦ (isLinN_aP S).sq.smul _).mono ?_
  calc ∑ S : Finset (Fin m), |if S.card = 1 then (0 : ℝ) else 1| * 1 ^ 2
      ≤ ∑ _S : Finset (Fin m), (1 : ℝ) := sum_le_sum fun S _ ↦ by split_ifs <;> simp
    _ = 2 ^ m := by simp

theorem isSOS_highP : IsSOS (highP m) :=
  IsSOS.sum _ fun S _ ↦ (IsSOS.const (by split_ifs <;> norm_num)).mul (IsSOS.sq _)

theorem sum_aP_sq_split : ∑ S, aP S ^ 2 = ∑ i, aP {i} ^ 2 + highP m := by
  rw [← sum_card_one (fun S ↦ aP S ^ 2), highP, ← sum_add_distrib]
  refine sum_congr rfl fun S _ ↦ ?_
  split_ifs <;> simp

theorem low_sub_highP : (1 - ∑ i, aP {i} ^ 2) - highP m = -(C (1 / 2 ^ m) * boolSum m) := by
  have h := sum_aP_sq_split (m := m)
  rw [sum_aP_sq] at h
  have e : (1 - ∑ i, aP {i} ^ 2) - highP m = 1 - C (1 / 2 ^ m) * ∑ x : Cube m, X x ^ 2 := by
    rw [h]; ring
  rw [e]
  refine MvPolynomial.funext fun y ↦ ?_
  simp only [boolSum, map_sub, map_neg, map_mul, map_sum, map_pow, eval_C, eval_X, map_one,
    sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, map_natCast, card_cube]
  field_simp
  ring

theorem parseval_sub_one : ∑ S, aP S ^ 2 - 1 = C (1 / 2 ^ m) * boolSum m := by
  have h := low_sub_highP (m := m)
  rw [sum_aP_sq_split]
  linear_combination -h

section Bool2

variable {A : System (Cube m) ℝ} (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A)
include hbool

theorem derivesEq_boolSum : DerivesEq A 2 (2 ^ m) (boolSum m) := by
  refine (derivesEq_bool hbool univ id (fun _ ↦ 1)).congr (by simp [boolSum]) |>.mono le_rfl ?_
  simp

theorem derivesEq_parseval : DerivesEq A 2 1 (∑ S, aP S ^ 2 - 1) := by
  rw [parseval_sub_one]
  refine ((derivesEq_boolSum hbool).smul (1 / 2 ^ m)).mono le_rfl (le_of_eq ?_)
  rw [abs_of_pos (by positivity)]
  field_simp

omit hbool in
theorem derivesEq_aP_empty (hbal : ∑ x, X x ∈ A ∧ -∑ x, X x ∈ A) :
    DerivesEq A 3 4 (aP ∅ ^ 2) := by
  have hlin : IsLinN (∑ x : Cube m, (X x : MvPolynomial (Cube m) ℝ)) (2 ^ m) := by
    classical
    refine (IsLinN.sum univ fun x _ ↦ IsLinN.X' x).mono (le_of_eq ?_)
    simp
  have hb := DerivesEq.of_mem hbal.1 hbal.2 hlin.totalDegree_le le_rfl
  have hr : IsLinN (C (1 / 2 ^ m) * aP (∅ : Finset (Fin m))) (1 / 2 ^ m) := by
    have := (isLinN_aP (∅ : Finset (Fin m))).smul (1 / 2 ^ m)
    rwa [abs_of_pos (by positivity), mul_one] at this
  refine ((hb.mul (C (1 / 2 ^ m) * aP ∅)).congr ?_).mono ?_ ?_
  · rw [aP_empty]; ring
  · have := hr.totalDegree_le
    omega
  · have h1 := hr.coeffNorm1_le
    have h2 : (1 : ℝ) / 2 ^ m ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h0 := coeffNorm1_nonneg (C (1 / 2 ^ m) * aP (∅ : Finset (Fin m)))
    nlinarith

/-- The level-`≥ 2` Fourier mass bound (Lemma 6.8): `Λ - 2 ≥ 2 (1 - ∑ᵢ cᵢ²)`. -/
theorem energy_bound (hm : 1 ≤ m) (hbal : ∑ x, X x ∈ A ∧ -∑ x, X x ∈ A) :
    DerivesN A 4 (24 * m * 2 ^ m) (lamP m - 2 * (1 - ∑ i, aP {i} ^ 2)) := by
  have hQ : IsQuadN (∑ S : Finset (Fin m), C (cS S) * aP S ^ 2) (2 ^ m * (2 * m + 2)) := by
    refine (IsQuadN.sum univ fun S _ ↦ (isLinN_aP S).sq.smul _).mono ?_
    calc ∑ S : Finset (Fin m), |cS S| * 1 ^ 2 ≤ ∑ _S : Finset (Fin m), (2 * m + 2 : ℝ) :=
          sum_le_sum fun S _ ↦ by rw [abs_of_nonneg (cS_nonneg S), one_pow, mul_one]; exact cS_le S
      _ = 2 ^ m * (2 * m + 2) := by simp; ring
  have hsos : IsSOS (∑ S : Finset (Fin m), C (cS S) * aP S ^ 2) :=
    IsSOS.sum _ fun S _ ↦ (IsSOS.const (cS_nonneg S)).mul (IsSOS.sq _)
  have h := DerivesN.ofIsSOS (k := 4) A hsos (hQ.totalDegree_le.trans (by norm_num))
    hQ.coeffNorm1_le
  have he := (((derivesEq_aP_empty hbal).smul (-4)).mono (k' := 4) (by norm_num) le_rfl).add
    (((derivesEq_parseval hbool).smul 4).mono (k' := 4) (by norm_num) le_rfl)
  refine (h.of_eq (he.congr ?_)).mono le_rfl ?_
  · rw [fourier_identity, C_neg]; ring
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    norm_num
    nlinarith

/-- The product of `12ε - A ≥ 0` with `∑_{|S| ≠ 1} f̂(S)² = 1 - ∑ᵢ cᵢ²` (modulo Booleanity). -/
theorem prod_bound {H : SimpleGraph (Cube m)} {p ε ξ τ₀ : ℝ} (hm : 1 ≤ m) (hp : 0 < p)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ₀1 : τ₀ ≤ 1 / 4) (good : Good H p ε ξ τ₀) :
    DerivesEq A 4 (8 * m * 2 ^ m)
      ((C (12 * ε) - aPoly H p ε ξ τ₀) * ((1 - ∑ i, aP {i} ^ 2) - highP m)) := by
  have hpn := (count_facts hp hτ₀1 good ⟨0, hm⟩).1
  have hn : (0 : ℝ) < 2 ^ m := by positivity
  set a₀ := 6 * ε + 2 * τ₀ + 3 * ξ with ha₀
  set a₁ := -((1 - 3 * ε) / 2 ^ m) with ha₁
  set a₂ := 1 / (p * 2 ^ m) with ha₂
  have hid : C (12 * ε) - aPoly H p ε ξ τ₀ =
      C a₀ + C a₁ * energyP 1 + C a₂ * energyP (graphW H) := by
    refine MvPolynomial.funext fun y ↦ ?_
    simp only [aPoly, lamP, lamP', ha₀, ha₁, ha₂, map_add, map_sub, map_mul, eval_C, map_ofNat,
      map_neg]
    field_simp
    ring
  have hb := derivesEq_boolSum hbool (m := m)
  have hbE := ((hb.mulSOS (isSOS_energyP (w := (1 : Fin m → Cube m → ℝ))
    (fun _ _ ↦ zero_le_one))).mono (k' := 4)
    (by have := totalDegree_energyP_le (abs_one_le (m := m)); omega) le_rfl)
  have hbH := ((hb.mulSOS (isSOS_energyP (fun i x ↦ (by unfold graphW; split_ifs <;> norm_num :
    (0 : ℝ) ≤ graphW H i x)))).mono (k' := 4)
    (by have := totalDegree_energyP_le (abs_graphW_le H); omega) le_rfl)
  have h := ((((hb.mono (k' := 4) (by norm_num) le_rfl).smul (-(1 / 2 ^ m))).smul a₀).add
    ((hbE.smul (-(1 / 2 ^ m))).smul a₁)).add ((hbH.smul (-(1 / 2 ^ m))).smul a₂)
  refine (h.congr ?_).mono le_rfl ?_
  · rw [low_sub_highP, hid, C_neg]; ring
  · have e1 := (isQuadN_energyP (abs_one_le (m := m))).coeffNorm1_le
    have e2 := (isQuadN_energyP (abs_graphW_le H)).coeffNorm1_le
    have hq : |-(1 / (2 : ℝ) ^ m)| = 1 / 2 ^ m := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [hq, abs_of_nonneg (by positivity : 0 ≤ a₀), abs_of_pos (by positivity : 0 < a₂),
      abs_of_nonpos (by rw [ha₁, neg_nonpos]; apply div_nonneg <;> [linarith; positivity])]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn : (2 : ℝ) ^ m ≤ m * 2 ^ m := le_mul_of_one_le_left hn.le hm'
    have f1 : 1 / 2 ^ m * 2 ^ m = (1 : ℝ) := by field_simp
    have f2 : 1 / 2 ^ m * (coeffNorm1 (energyP 1 : MvPolynomial (Cube m) ℝ) * 2 ^ m) =
        coeffNorm1 (energyP 1 : MvPolynomial (Cube m) ℝ) := by field_simp
    have f3 : 1 / 2 ^ m * (coeffNorm1 (energyP (graphW H)) * 2 ^ m) =
        coeffNorm1 (energyP (graphW H)) := by field_simp
    rw [f1, f2, f3]
    have g1 : -a₁ ≤ 1 := by
      rw [ha₁, neg_neg, div_le_one hn]; nlinarith [one_le_pow₀ (M₀ := ℝ) (n := m) one_le_two]
    have g2 : a₂ ≤ 1 := by rw [ha₂, div_le_one (by positivity)]; exact hpn
    have g0 : 0 ≤ -a₁ := by linarith [g1, show -a₁ = (1 - 3 * ε) / 2 ^ m by rw [ha₁, neg_neg],
      show 0 ≤ (1 - 3 * ε) / 2 ^ m by apply div_nonneg <;> [linarith; positivity]]
    have hE1 := coeffNorm1_nonneg (energyP 1 : MvPolynomial (Cube m) ℝ)
    have hE2 := coeffNorm1_nonneg (energyP (graphW H))
    have ha₀4 : a₀ ≤ 4 := by rw [ha₀]; linarith
    have h1mn : (1 : ℝ) ≤ m * 2 ^ m := hm'.trans (le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ (by norm_num)))
    nlinarith [mul_le_mul g1 e1 hE1 zero_le_one, mul_le_mul g2 e2 hE2 zero_le_one]

end Bool2

/-! ### Assembly (Lemma 6.9 and the end of the proof of Lemma 6.3) -/

theorem sum_mul_dir (ε : ℝ) (Ap : MvPolynomial (Cube m) ℝ) :
    ∑ i, aP {i} ^ 2 * (C (12 * ε) * (1 - aP {i} ^ 2) - Ap) =
      C (12 * ε) * (∑ i, aP {i} ^ 2 - ∑ i, aP {i} ^ 4) - Ap * ∑ i, aP {i} ^ 2 := by
  calc ∑ i, aP {i} ^ 2 * (C (12 * ε) * (1 - aP {i} ^ 2) - Ap) =
        ∑ i, (C (12 * ε) * aP {i} ^ 2 - C (12 * ε) * aP {i} ^ 4 - Ap * aP {i} ^ 2) :=
        sum_congr rfl fun i _ ↦ by ring
    _ = _ := by rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]; ring

theorem final_bound {c₁ ε K : ℝ} (hm : 1 ≤ m) (hc0 : 0 ≤ c₁) (hc2 : c₁ ≤ 2) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 100) (hK0 : 0 ≤ K) (hK : K ≤ 6) :
    c₁ * (m * (128 * m * 2 ^ m) + 2 ^ m * (128 * m * 2 ^ m + 12 * ε) + 8 * m * 2 ^ m +
        12 * ε * 2 ^ (40 * (m + 4)) + 60 * ε * (24 * m * 2 ^ m) + 5) +
      1 / 2 * (24 * m * 2 ^ m) + (4 - c₁) * K ≤ (2 : ℝ) ^ (200 * (m + 4)) := by
  have hmn : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hn1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn3 : ((2 : ℝ) ^ m) ^ 3 ≤ 2 ^ (40 * (m + 4)) := by
    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hB1 : (1 : ℝ) ≤ 2 ^ (40 * (m + 4)) := one_le_pow₀ (by norm_num)
  have hBB : (2 : ℝ) ^ (40 * (m + 4)) * 2 ^ 10 ≤ 2 ^ (200 * (m + 4)) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  set n : ℝ := 2 ^ m
  set B : ℝ := 2 ^ (40 * (m + 4))
  have hmm : (m : ℝ) * m ≤ n * n := mul_le_mul hmn hmn (by positivity) (by positivity)
  have hmn2 : (m : ℝ) * n ≤ n * n := mul_le_mul_of_nonneg_right hmn (by positivity)
  have hnn : n * n ≤ n ^ 3 := by nlinarith
  have e1 : (m : ℝ) * (128 * m * n) ≤ 128 * n ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hmm (by positivity : (0 : ℝ) ≤ n)]
  have e2 : n * (128 * m * n + 12 * ε) ≤ 129 * n ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn2 (by positivity : (0 : ℝ) ≤ n)]
  have e3 : 8 * m * n ≤ 8 * n ^ 3 := by nlinarith
  have e4 : 12 * ε * B ≤ B := by nlinarith
  have e5 : 60 * ε * (24 * m * n) ≤ 15 * n ^ 3 := by nlinarith
  have hin : m * (128 * m * n) + n * (128 * m * n + 12 * ε) + 8 * m * n + 12 * ε * B +
      60 * ε * (24 * m * n) + 5 ≤ 286 * B := by nlinarith
  have hin0 : 0 ≤ m * (128 * m * n) + n * (128 * m * n + 12 * ε) + 8 * m * n + 12 * ε * B +
      60 * ε * (24 * m * n) + 5 := by positivity
  have f1 := mul_le_mul hc2 hin hin0 (by norm_num)
  have f2 : (4 - c₁) * K ≤ 24 * B := by nlinarith
  have f3 : 1 / 2 * (24 * m * n) ≤ 12 * B := by nlinarith
  have f4 : 2 * (286 * B) + 12 * B + 24 * B ≤ B * 2 ^ 10 := by norm_num; linarith
  clear_value n B
  generalize (2 : ℝ) ^ (200 * (m + 4)) = T at hBB ⊢
  linarith

theorem level_one_mass_of_le {m : ℕ} (hm : 2 ≤ m) {H : SimpleGraph (Cube m)} {p ε ξ τ₀ δ : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hτ₀ : 0 ≤ τ₀) (hτ₀1 : τ₀ ≤ 1 / 4) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (good : Good H p ε ξ τ₀)
    (A : System (Cube m) ℝ) (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A)
    (hbal : ∑ x, X x ∈ A ∧ -∑ x, X x ∈ A) (hcut : cutPolyCube H δ ∈ A) :
    DerivesN A 4 ((2 : ℝ) ^ (200 * (m + 4)))
      (∑ i, aP {i} ^ 2 - C (1 - 4 * (δ + 5 * τ₀ + 3 * ξ))) := by
  have hm1 : 1 ≤ m := by omega
  set Ap := aPoly H p ε ξ τ₀ with hAp
  have hsq : ∀ i : Fin m, IsQuadN (aP {i} ^ 2) 1 := fun i ↦ by simpa using (isLinN_aP {i}).sq
  have hM0 : (0 : ℝ) ≤ 128 * m * 2 ^ m := by positivity
  have hF1 : ∀ i, DerivesN A 2 (128 * m * 2 ^ m) (C (12 * ε) * (1 - aP {i} ^ 2) - Ap) :=
    fun i ↦ dir_bound hm1 hp hp1 hε.le (by linarith) hξ1 hτ₀1 good hbool i
  -- Lemma 6.9: multiply by `cᵢ²` and sum
  have hS1 : DerivesN A 4 (m * (128 * m * 2 ^ m))
      (∑ i, aP {i} ^ 2 * (C (12 * ε) * (1 - aP {i} ^ 2) - Ap)) := by
    have := DerivesN.sum univ fun i _ ↦ ((hF1 i).mulSOS (IsSOS.sq (aP {i}))).mono (k' := 4)
      (M' := 128 * m * 2 ^ m) (by have := (hsq i).totalDegree_le; omega)
      (mul_le_of_le_one_left hM0 (hsq i).coeffNorm1_le)
    rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  -- `12ε - A ≥ 0`, times `∑_{|S| ≠ 1} f̂(S)²`
  have hF1' : DerivesN A 2 (128 * m * 2 ^ m + 12 * ε) (C (12 * ε) - Ap) := by
    have hc : (0 : ℝ) ≤ 12 * ε := by positivity
    refine ((hF1 ⟨0, by omega⟩).add (DerivesN.ofIsSOS A ((IsSOS.const hc).mul
      (IsSOS.sq (aP {⟨0, by omega⟩}))) ?_ ?_)).congr (by ring)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (hsq _).totalDegree_le
    · rw [coeffNorm1_C_mul, abs_of_nonneg hc]
      exact mul_le_of_le_one_right hc (hsq _).coeffNorm1_le
  have hS2 : DerivesN A 4 (2 ^ m * (128 * m * 2 ^ m + 12 * ε)) (highP m * (C (12 * ε) - Ap)) :=
    (hF1'.mulSOS isSOS_highP).mono (by have := (isQuadN_highP (m := m)).totalDegree_le; omega)
      (mul_le_mul_of_nonneg_right isQuadN_highP.coeffNorm1_le (by positivity))
  have hS3 := (prod_bound hbool hm1 hp hε.le hε1 hξ hξ1 hτ₀ hτ₀1 good).1
  have hF := fkn A hbool
  have hF3 := energy_bound hbool hm1 hbal
  have hF2 := (cut_bound hm1 hp hτ₀ hτ₀1 hδ hδ1 good hcut).mono (k' := 4) (by norm_num) le_rfl
  have hX := ((((hS1.add hS2).add hS3).add (hF.smul (c := 12 * ε) (by positivity))).add
    (hF3.smul (c := 60 * ε) (by positivity))).add hF2
  -- the end of the proof of Lemma 6.3
  have h63 : 0 < 1 - 63 * ε := by linarith
  set c₁ := 1 / (2 * (1 - 63 * ε)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hc₁2 : c₁ ≤ 2 := by
    rw [hc₁, div_le_iff₀ (by positivity)]; linarith
  set K := δ + 5 * τ₀ + 3 * ξ with hK
  have hK0 : 0 ≤ (4 - c₁) * K := mul_nonneg (by linarith) (by positivity)
  have hfin := ((hX.smul hc₁0.le).add (hF3.smul (c := 1 / 2) (by norm_num))).add
    (DerivesN.ofIsSOS (k := 4) A (IsSOS.const hK0) (by rw [totalDegree_C]; omega)
      (le_of_eq (by rw [coeffNorm1_C, abs_of_nonneg hK0])))
  refine (hfin.congr ?_).mono le_rfl
    (final_bound hm1 hc₁0.le hc₁2 hε.le hε1 (by positivity) (by linarith))
  rw [sum_mul_dir]
  refine MvPolynomial.funext fun y ↦ ?_
  simp only [hAp, aPoly, map_add, map_sub, map_mul, eval_C, map_one, map_ofNat]
  rw [hc₁]
  field_simp
  ring

/-- When `4 (δ + 5τ₀ + 3ξ) ≥ 1` the bound is trivial: `∑ᵢ cᵢ² + (4 (δ + 5τ₀ + 3ξ) - 1)` is a sum of
squares. Its norm is small only while `δ + 5τ₀ + 3ξ` is. -/
theorem level_one_mass_trivial {m : ℕ} {K : ℝ} (hK : 1 ≤ 4 * K)
    (hK' : 4 * K ≤ (2 : ℝ) ^ (199 * (m + 4))) (A : System (Cube m) ℝ) :
    DerivesN A 4 ((2 : ℝ) ^ (200 * (m + 4))) (∑ i, aP {i} ^ 2 - C (1 - 4 * K)) := by
  have hc : 0 ≤ 4 * K - 1 := by linarith
  have hsos : IsSOS (∑ i : Fin m, aP {i} ^ 2 + C (4 * K - 1)) :=
    (IsSOS.sum _ fun i _ ↦ IsSOS.sq _).add (IsSOS.const hc)
  have hQ : IsQuadN (∑ i : Fin m, aP {i} ^ 2) m := by
    refine (IsQuadN.sum univ fun i _ ↦ (isLinN_aP {i}).sq).mono (le_of_eq ?_)
    simp
  refine (DerivesN.ofIsSOS A hsos ?_ ?_).congr ?_
  · exact (totalDegree_add _ _).trans (max_le (hQ.totalDegree_le.trans (by norm_num))
      (by rw [totalDegree_C]; omega))
  · refine (coeffNorm1_add_le _ _).trans ?_
    rw [coeffNorm1_C, abs_of_nonneg hc]
    have hmn : (m : ℝ) ≤ 2 ^ (199 * (m + 4)) := by
      have : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self).le
      exact this.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hp : (2 : ℝ) ^ (199 * (m + 4)) * 2 ≤ 2 ^ (200 * (m + 4)) := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    generalize (2 : ℝ) ^ (200 * (m + 4)) = T at hp ⊢
    generalize (2 : ℝ) ^ (199 * (m + 4)) = T' at hp hmn hK'
    linarith [hQ.coeffNorm1_le]
  · rw [show 4 * K - 1 = -(1 - 4 * K) by ring, C_neg]
    ring

end BMW26.Cert

namespace BMW26

open Finset MvPolynomial SoS

/-- **The level-one mass of the program's solutions**: for a good sample `H`, every system
containing the Boolean, balance and cut constraints proves `∑ᵢ f̂(i)² ≥ 1 - 4 (δ + 5τ₀ + 3ξ)` in
degree `4`. -/
theorem level_one_mass {m : ℕ} (hm : 2 ≤ m) {H : SimpleGraph (Cube m)} {p ε ξ τ₀ δ : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hτ₀ : 0 ≤ τ₀) (hτ₀1 : τ₀ ≤ 1 / 4) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (good : Good H p ε ξ τ₀)
    (A : System (Cube m) ℝ) (hbool : ∀ x, X x ^ 2 - 1 ∈ A ∧ 1 - X x ^ 2 ∈ A)
    (hbal : ∑ x, X x ∈ A ∧ -∑ x, X x ∈ A) (hcut : cutPolyCube H δ ∈ A) :
    DerivesN A 4 ((2 : ℝ) ^ (200 * (m + 4)))
      (∑ i, aP {i} ^ 2 - C (1 - 4 * (δ + 5 * τ₀ + 3 * ξ))) :=
  Cert.level_one_mass_of_le hm hp hp1 hε hε1 hξ hξ1 hτ₀ hτ₀1 hδ hδ1 good A hbool hbal hcut

end BMW26
