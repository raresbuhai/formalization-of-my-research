module

public import Background.SumOfSquares.Lifted
public import Background.SumOfSquares.PDTest

/-!
# The separation oracle

The separation oracle for the set the algorithm searches (`SoS.Lifted.InSet`), and the objective
cut. Each constraint of the set is tested exactly, with rational arithmetic, and each failed test
gives a cut.

* **Moment matrices** (`SoS.momentMatrix`). With the monomials of degree at most `D / 2` listed as
  `ms`, the matrix `M = (y (msᵢ + msⱼ))ᵢⱼ` has `vᵀ (M + τ I) v = L_y(g²) + τ ‖g‖₂²` for
  `g = ∑ vᵢ x^msᵢ` (`SoS.quad_momentMatrix`). So "the moment matrix is at least `-τ`"
  (`SoS.MinEigGE`) says exactly that `M + τ I` is positive semidefinite
  (`SoS.minEigGE_iff_momentMatrix`), which `SoS.PDTest.test` checks.
* **Cuts.** The moments and auxiliary moments are affine functions of the point, so every
  functional `x ↦ L_{y(x)}(h)` has a gradient (`SoS.Lifted.gradY`, `SoS.Lifted.gradW`). A failed
  positive definiteness test gives `v` with `vᵀ (M(c) + τ I) v ≤ 0`, and the gradient of
  `L_{y(x)}(g²)` cuts `c` off from every point whose moment matrix is at least `-τ/2`
  (`SoS.Lifted.validAnswer_of_psd`). A violated distance constraint is cut by its gradient
  (`SoS.Lifted.validAnswer_of_dist`), a coordinate out of the box by a coordinate vector
  (`SoS.Lifted.validAnswer_of_box`), and the objective by its gradient
  (`SoS.Lifted.obj_ge_add_gradObj`).
* **Answers** (`SoS.Lifted.ValidAnswer`). The oracle declares a point feasible only if it is in
  `InSet A ℓ η τ R` (`SoS.Lifted.validAnswer_none`), and its cuts keep `InSet A ℓ η (τ/2) R`. The
  slack `τ/2` makes the positive semidefiniteness cuts strict, and a cut that would be `0` can be
  replaced by any vector (`SoS.Lifted.ValidAnswer.orDefault`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Matrix

/-! ### Moment matrices -/

section MomentMatrix

variable {σ : Type*} {N : ℕ}

/-- The polynomial `∑ i, vᵢ x^(msᵢ)`. -/
noncomputable def polyOf (ms : Fin N → σ →₀ ℕ) (v : Fin N → ℝ) : MvPolynomial σ ℝ :=
  ∑ i, monomial (ms i) (v i)

/-- The moment matrix of `y` on the monomials `ms`, shifted by `τ`:
`(y (msᵢ + msⱼ) + τ [i = j])ᵢⱼ`. -/
noncomputable def momentMatrix (y : (σ →₀ ℕ) → ℝ) (τ : ℝ) (ms : Fin N → σ →₀ ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ y (ms i + ms j) + if i = j then τ else 0

theorem momentMatrix_transpose (y : (σ →₀ ℕ) → ℝ) (τ : ℝ) (ms : Fin N → σ →₀ ℕ) :
    (momentMatrix y τ ms)ᵀ = momentMatrix y τ ms := by
  ext i j
  simp [momentMatrix, add_comm (ms j), eq_comm]

theorem coeff_polyOf {ms : Fin N → σ →₀ ℕ} (hms : Function.Injective ms) (v : Fin N → ℝ)
    (i : Fin N) : (polyOf ms v).coeff (ms i) = v i := by
  classical
  rw [polyOf, coeff_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [coeff_monomial, ite_eq_right fun h ↦ absurd (hms h) hj]
  · simp

theorem coeffNorm_polyOf_sq {ms : Fin N → σ →₀ ℕ} (hms : Function.Injective ms)
    (v : Fin N → ℝ) : coeffNorm (polyOf ms v) ^ 2 = ∑ i, v i ^ 2 := by
  classical
  have hsupp : (polyOf ms v).support ⊆ Finset.univ.image ms := by
    intro m hm
    by_contra h
    apply mem_support_iff.1 hm
    rw [polyOf, coeff_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [coeff_monomial, ite_eq_right fun hj ↦ absurd (Finset.mem_image.2 ⟨j, by simp, hj⟩) h]
  rw [coeffNorm_eq_of_support_subset hsupp, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Finset.sum_image fun i _ j _ h ↦ hms h]
  simp [coeff_polyOf hms]

theorem riesz_polyOf_mul_self (y : (σ →₀ ℕ) → ℝ) (ms : Fin N → σ →₀ ℕ) (v : Fin N → ℝ) :
    riesz y (polyOf ms v * polyOf ms v) = ∑ i, ∑ j, v i * v j * y (ms i + ms j) := by
  simp only [polyOf, Finset.sum_mul_sum, monomial_mul_monomial, map_sum, riesz_monomial]

/-- `vᵀ (M + τ I) v = L_y(g²) + τ ‖g‖₂²` for `g = ∑ vᵢ x^(msᵢ)`. -/
theorem quad_momentMatrix (y : (σ →₀ ℕ) → ℝ) (τ : ℝ) {ms : Fin N → σ →₀ ℕ}
    (hms : Function.Injective ms) (v : Fin N → ℝ) :
    v ⬝ᵥ momentMatrix y τ ms *ᵥ v =
      riesz y (polyOf ms v * polyOf ms v) + τ * coeffNorm (polyOf ms v) ^ 2 := by
  have hM : momentMatrix y τ ms = Matrix.of (fun i j ↦ y (ms i + ms j)) + τ • 1 := by
    ext i j
    simp [momentMatrix, Matrix.one_apply]
  rw [riesz_polyOf_mul_self, coeffNorm_polyOf_sq hms, hM, add_mulVec, dotProduct_add,
    smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  · simp only [dotProduct, mulVec, of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  · simp [dotProduct, sq]

theorem totalDegree_polyOf_le {ms : Fin N → σ →₀ ℕ} {e : ℕ} (hms : ∀ i, (ms i).degree ≤ e)
    (v : Fin N → ℝ) : (polyOf ms v).totalDegree ≤ e :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦
    (totalDegree_monomial_le _ _).trans (hms i))

/-- **Moment matrices.** If `ms` lists the monomials of degree at most `D / 2` without repetition,
the moment matrix of `y` is at least `-τ` exactly when `M + τ I` is positive semidefinite. -/
theorem minEigGE_iff_momentMatrix {y : (σ →₀ ℕ) → ℝ} {τ : ℝ} {D : ℕ} {ms : Fin N → σ →₀ ℕ}
    (hms : Function.Injective ms) (hrange : ∀ m, m ∈ Set.range ms ↔ m.degree ≤ D / 2) :
    MinEigGE (riesz y) D (-τ) ↔ ∀ v, 0 ≤ v ⬝ᵥ momentMatrix y τ ms *ᵥ v := by
  classical
  constructor
  · intro h v
    have hdeg := totalDegree_polyOf_le (fun i ↦ (hrange (ms i)).1 ⟨i, rfl⟩) v
    have := h (polyOf ms v) (by omega)
    rw [quad_momentMatrix y τ hms]
    linarith
  · intro h g hg
    -- `g` is `polyOf ms v` for its coefficients `v` on `ms`.
    set v : Fin N → ℝ := fun i ↦ g.coeff (ms i)
    have hgv : polyOf ms v = g := by
      ext m
      by_cases hm : m ∈ Set.range ms
      · obtain ⟨i, rfl⟩ := hm
        rw [coeff_polyOf hms]
      · rw [polyOf, coeff_sum, Finset.sum_eq_zero fun j _ ↦ by
          rw [coeff_monomial, ite_eq_right fun hj ↦ absurd ⟨j, hj⟩ hm]]
        by_contra hne
        exact hm ((hrange m).2 ((le_totalDegree (mem_support_iff.2 (Ne.symm hne))).trans
          (by omega)))
    have := h v
    rw [quad_momentMatrix y τ hms, hgv] at this
    linarith

/-- **A positive semidefiniteness cut.** If `vᵀ (M_c + τ I) v ≤ 0` for the moment matrix of
`y_c`, with `v ≠ 0` and `τ > 0`, then every `y` whose moment matrix is at least `-τ/2` has
`L_y(g²) > L_{y_c}(g²)` for `g = ∑ vᵢ x^(msᵢ)`. -/
theorem riesz_lt_of_witness {yc y : (σ →₀ ℕ) → ℝ} {τ : ℝ} {D : ℕ} {ms : Fin N → σ →₀ ℕ}
    (hms : Function.Injective ms) (hrange : ∀ m, m ∈ Set.range ms ↔ m.degree ≤ D / 2)
    (hτ : 0 < τ) {v : Fin N → ℝ} (hv : v ≠ 0) (hwit : v ⬝ᵥ momentMatrix yc τ ms *ᵥ v ≤ 0)
    (hy : MinEigGE (riesz y) D (-(τ / 2))) :
    riesz yc (polyOf ms v * polyOf ms v) < riesz y (polyOf ms v * polyOf ms v) := by
  have hdeg := totalDegree_polyOf_le (fun i ↦ (hrange (ms i)).1 ⟨i, rfl⟩) v
  have h1 := hy (polyOf ms v) (by omega)
  rw [quad_momentMatrix yc τ hms] at hwit
  have hpos : 0 < coeffNorm (polyOf ms v) ^ 2 := by
    rw [coeffNorm_polyOf_sq hms]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi) (Finset.single_le_sum (f := fun i ↦ v i ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i))
  nlinarith

end MomentMatrix

/-! ### Gradients -/

namespace Lifted

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [Algebra K ℝ]
  {A : System σ K} {ℓ : ℕ}

/-- The coefficients of `h` on the moment coordinates: the gradient of `x ↦ L_{y(x)}(h)`. -/
noncomputable def gradY (h : MvPolynomial σ ℝ) : Coord A ℓ → ℝ :=
  Sum.elim (fun m ↦ h.coeff m.1) 0

/-- The coefficients of `h` on the auxiliary coordinates of `S`: the gradient of
`x ↦ L_{w_S(x)}(h)`. -/
noncomputable def gradW (S : sets A ℓ) (h : MvPolynomial σ ℝ) : Coord A ℓ → ℝ :=
  Sum.elim 0 fun p ↦ if p.1 = S then h.coeff p.2.1 else 0

omit [Algebra K ℝ] in
/-- `L_{y(x)}(h) - L_{y(c)}(h) = ∇ ⬝ (x - c)` for `deg h ≤ ℓ`. -/
theorem riesz_ys_sub {h : MvPolynomial σ ℝ} (hh : h.totalDegree ≤ ℓ) (x c : Coord A ℓ → ℝ) :
    riesz (ys x) h - riesz (ys c) h = gradY h ⬝ᵥ (x - c) := by
  classical
  rw [riesz_apply, riesz_apply, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  rw [Finset.sum_subset (support_subset_monomialsLE hh) fun m _ hm ↦ by
    rw [notMem_support_iff.1 hm, zero_mul]]
  rw [← Finset.add_sum_erase _ _ (mem_monomialsLE.2 (by simp : (0 : σ →₀ ℕ).degree ≤ ℓ)),
    ys_zero, ys_zero, sub_self, mul_zero, zero_add, ← Finset.sum_coe_sort]
  simp only [dotProduct, Fintype.sum_sum_type, gradY, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, Pi.sub_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp [ys, m.2]

omit [Algebra K ℝ] in
/-- `L_{w_S(x)}(h) - L_{w_S(c)}(h) = ∇ ⬝ (x - c)` for `deg h ≤ ℓ - deg S`. -/
theorem riesz_ws_sub (S : sets A ℓ) {h : MvPolynomial σ ℝ}
    (hh : h.totalDegree ≤ ℓ - A.degree S.1) (x c : Coord A ℓ → ℝ) :
    riesz (ws x S) h - riesz (ws c S) h = gradW S h ⬝ᵥ (x - c) := by
  classical
  rw [riesz_apply, riesz_apply, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  rw [Finset.sum_subset (support_subset_monomialsLE hh) fun m _ hm ↦ by
    rw [notMem_support_iff.1 hm, zero_mul], ← Finset.sum_coe_sort]
  simp only [dotProduct, Fintype.sum_sum_type, gradW, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add, Pi.sub_apply, Fintype.sum_sigma, ite_mul]
  rw [Finset.sum_eq_single S (fun S' _ hS' ↦ by simp [hS']) (by simp)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp [ws, m.2]

/-! ### Valid answers -/

/-- A valid answer of the separation oracle at `c`: `none` only for points of
`InSet A ℓ η τ R`, and otherwise a nonzero cut with every point of `InSet A ℓ η (τ / 2) R` on its
nonpositive side. -/
def ValidAnswer (η τ R : ℝ) (c : Coord A ℓ → ℝ) : Option (Coord A ℓ → ℝ) → Prop
  | none => InSet A ℓ η τ R c
  | some a => a ≠ 0 ∧ ∀ x, InSet A ℓ η (τ / 2) R x → a ⬝ᵥ (x - c) ≤ 0

/-- A vector, or a fixed coordinate vector in its place if it is `0`. -/
noncomputable def orDefault (i₀ : Coord A ℓ) (a : Coord A ℓ → ℝ) : Coord A ℓ → ℝ :=
  if a = 0 then Pi.single i₀ 1 else a

omit [Algebra K ℝ] in
theorem orDefault_ne_zero (i₀ : Coord A ℓ) (a : Coord A ℓ → ℝ) : orDefault i₀ a ≠ 0 := by
  unfold orDefault
  split_ifs with h
  · exact fun h' ↦ (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using congrFun h' i₀)
  · exact h

/-- A strict cut that would be `0` cuts off every point, so any vector does. -/
theorem ValidAnswer.orDefault {η τ R : ℝ} {c a : Coord A ℓ → ℝ} (i₀ : Coord A ℓ)
    (h : ∀ x, InSet A ℓ η (τ / 2) R x → a ⬝ᵥ (x - c) < 0) :
    ValidAnswer η τ R c (some (Lifted.orDefault i₀ a)) := by
  refine ⟨orDefault_ne_zero i₀ a, fun x hx ↦ ?_⟩
  unfold Lifted.orDefault
  split_ifs with ha
  · have := h x hx
    simp [ha] at this
  · exact (h x hx).le

/-- **The box cut.** A coordinate beyond `R` is cut by its coordinate vector. -/
theorem validAnswer_of_box {η τ R : ℝ} {c : Coord A ℓ → ℝ} {i : Coord A ℓ} (hi : R < |c i|) :
    ValidAnswer η τ R c (some (Pi.single i (if 0 < c i then 1 else -1))) := by
  classical
  refine ⟨fun h ↦ ?_, fun x hx ↦ ?_⟩
  · have := congrFun h i
    split_ifs at this <;> simp at this
  · have hxi := abs_le.1 (hx.box i)
    rw [single_dotProduct, Pi.sub_apply]
    split_ifs with hc
    · rw [abs_of_pos hc] at hi
      linarith
    · rw [abs_of_nonpos (not_lt.1 hc)] at hi
      linarith

/-- **The positive semidefiniteness cut for the moments.** If the test of `M(y(c)) + τ I` gives a
witness `v`, the gradient of `-L_{y(x)}(g²)` is a valid cut. -/
theorem validAnswer_of_psd {η τ R : ℝ} {c : Coord A ℓ → ℝ} {N : ℕ} {ms : Fin N → σ →₀ ℕ}
    (hms : Function.Injective ms) (hrange : ∀ m, m ∈ Set.range ms ↔ m.degree ≤ ℓ / 2)
    (hτ : 0 < τ) {v : Fin N → ℝ} (hv : v ≠ 0)
    (hwit : v ⬝ᵥ momentMatrix (ys c) τ ms *ᵥ v ≤ 0) (i₀ : Coord A ℓ) :
    ValidAnswer η τ R c
      (some (orDefault i₀ (-gradY (polyOf ms v * polyOf ms v)))) := by
  refine ValidAnswer.orDefault i₀ fun x hx ↦ ?_
  have hdeg : (polyOf ms v * polyOf ms v).totalDegree ≤ ℓ := by
    have := totalDegree_polyOf_le (fun i ↦ (hrange (ms i)).1 ⟨i, rfl⟩) v
    exact (totalDegree_mul _ _).trans (by omega)
  have hlt := riesz_lt_of_witness hms hrange hτ hv hwit hx.psd
  rw [neg_dotProduct, ← riesz_ys_sub hdeg]
  linarith

/-- **The positive semidefiniteness cut for an auxiliary sequence.** -/
theorem validAnswer_of_psd_aux {η τ R : ℝ} {c : Coord A ℓ → ℝ} (S : sets A ℓ) {N : ℕ}
    {ms : Fin N → σ →₀ ℕ} (hms : Function.Injective ms)
    (hrange : ∀ m, m ∈ Set.range ms ↔ m.degree ≤ (ℓ - A.degree S.1) / 2)
    (hτ : 0 < τ) {v : Fin N → ℝ} (hv : v ≠ 0)
    (hwit : v ⬝ᵥ momentMatrix (ws c S) τ ms *ᵥ v ≤ 0) (i₀ : Coord A ℓ) :
    ValidAnswer η τ R c
      (some (orDefault i₀ (-gradW S (polyOf ms v * polyOf ms v)))) := by
  refine ValidAnswer.orDefault i₀ fun x hx ↦ ?_
  have hdeg : (polyOf ms v * polyOf ms v).totalDegree ≤ ℓ - A.degree S.1 := by
    have := totalDegree_polyOf_le (fun i ↦ (hrange (ms i)).1 ⟨i, rfl⟩) v
    exact (totalDegree_mul _ _).trans (by omega)
  have hlt := riesz_lt_of_witness hms hrange hτ hv hwit (hx.psd_aux S)
  rw [neg_dotProduct, ← riesz_ws_sub S hdeg]
  linarith

/-- The residual of the distance constraint of `S` at the monomial `m`. -/
noncomputable def resid (x : Coord A ℓ → ℝ) (S : sets A ℓ) (m : σ →₀ ℕ) : ℝ :=
  loc A (ys x) S m - ws x S m

/-- The gradient of the residual. -/
noncomputable def gradResid (S : sets A ℓ) (m : σ →₀ ℕ) : Coord A ℓ → ℝ :=
  gradY (monomial m 1 * toReal (A.prod S.1)) - gradW S (monomial m 1)

theorem resid_sub (S : sets A ℓ) {m : σ →₀ ℕ} (hm : m ∈ monomialsLE σ (ℓ - A.degree S.1))
    (x c : Coord A ℓ → ℝ) : resid x S m - resid c S m = gradResid S m ⬝ᵥ (x - c) := by
  have h1 := riesz_ys_sub (totalDegree_monomial_mul_prod_le (degree_le_of_mem_sets S.2)
    (mem_monomialsLE.1 hm)) x c
  have h2 := riesz_ws_sub S (h := monomial m 1)
    (by rw [totalDegree_monomial_one]; exact mem_monomialsLE.1 hm) x c
  simp only [riesz_monomial, one_mul] at h2
  rw [gradResid, sub_dotProduct, ← h1, ← h2, resid, resid, loc, loc]
  ring

/-- **The distance cut.** If the distance constraint of `S` fails at `c`, its gradient
`2 ∑ₘ rₘ(c) ∇rₘ` is a valid cut: the sum of squares of affine functions lies above its tangent. -/
theorem validAnswer_of_dist {η τ R : ℝ} {c : Coord A ℓ → ℝ} (S : sets A ℓ)
    (hS : (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2 <
      ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), resid c S m ^ 2) (i₀ : Coord A ℓ) :
    ValidAnswer η τ R c (some (orDefault i₀
      (∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), (2 * resid c S m) • gradResid S m))) := by
  refine ValidAnswer.orDefault i₀ fun x hx ↦ ?_
  have hx' := hx.dist S
  -- `∑ rₘ(x)² ≥ ∑ rₘ(c)² + 2 ∑ rₘ(c) (rₘ(x) - rₘ(c))`.
  have htan : ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), resid c S m ^ 2 +
      (∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), (2 * resid c S m) • gradResid S m) ⬝ᵥ (x - c) ≤
      ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), resid x S m ^ 2 := by
    rw [sum_dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m hm ↦ ?_
    rw [smul_dotProduct, smul_eq_mul, ← resid_sub S hm]
    nlinarith [sq_nonneg (resid x S m - resid c S m)]
  have : ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), resid x S m ^ 2 ≤
      (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2 := hx'
  linarith

/-- **Feasibility.** A point that passes every test is in the set: every coordinate is at most
`R`, the moment matrices pass the positive definiteness test, and the distance constraints
hold. -/
theorem validAnswer_none {η τ R : ℝ} {c : Coord A ℓ → ℝ} (hbox : ∀ i, |c i| ≤ R)
    {N : ℕ} {ms : Fin N → σ →₀ ℕ} (hms : Function.Injective ms)
    (hrange : ∀ m, m ∈ Set.range ms ↔ m.degree ≤ ℓ / 2)
    (hpsd : ∀ v, v ≠ 0 → 0 < v ⬝ᵥ momentMatrix (ys c) τ ms *ᵥ v)
    (msS : sets A ℓ → Σ N, Fin N → σ →₀ ℕ)
    (hmsS : ∀ S, Function.Injective (msS S).2)
    (hrangeS : ∀ S m, m ∈ Set.range (msS S).2 ↔ m.degree ≤ (ℓ - A.degree S.1) / 2)
    (hpsdS : ∀ S v, v ≠ 0 → 0 < v ⬝ᵥ momentMatrix (ws c S) τ (msS S).2 *ᵥ v)
    (hdist : ∀ S : sets A ℓ, ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), resid c S m ^ 2 ≤
      (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2) :
    ValidAnswer η τ R c none := by
  have hnn : ∀ {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}, (∀ v, v ≠ 0 → 0 < v ⬝ᵥ M *ᵥ v) →
      ∀ v, 0 ≤ v ⬝ᵥ M *ᵥ v := fun h v ↦ by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (h v hv).le
  exact ⟨(minEigGE_iff_momentMatrix hms hrange).2 (hnn hpsd),
    fun S ↦ (minEigGE_iff_momentMatrix (hmsS S) (hrangeS S)).2 (hnn (hpsdS S)),
    hdist, hbox⟩

/-! ### The objective cut -/

/-- The gradient of the objective at `c`: `∇L(q₀) + ∑ⱼ 2 L_{y(c)}(qⱼ) ∇L(qⱼ)`. -/
noncomputable def gradObj (q₀ : MvPolynomial σ ℝ) (qs : List (MvPolynomial σ ℝ))
    (c : Coord A ℓ → ℝ) : Coord A ℓ → ℝ :=
  gradY q₀ + (qs.map fun q ↦ (2 * riesz (ys c) q) • gradY (A := A) (ℓ := ℓ) q).sum

omit [Algebra K ℝ] in
/-- **The objective lies above its tangent**: `obj(x) ≥ obj(c) + ∇obj(c) ⬝ (x - c)`. So every
point with a smaller objective is on the negative side of the gradient. -/
theorem obj_ge_add_gradObj {q₀ : MvPolynomial σ ℝ} {qs : List (MvPolynomial σ ℝ)}
    (hq : ∀ q ∈ q₀ :: qs, q.totalDegree ≤ ℓ) (x c : Coord A ℓ → ℝ) :
    obj q₀ qs (ys c) + gradObj q₀ qs c ⬝ᵥ (x - c) ≤ obj q₀ qs (ys x) := by
  have h0 := riesz_ys_sub (hq q₀ List.mem_cons_self) x c
  -- Each square lies above its tangent.
  have hlist : ∀ l : List (MvPolynomial σ ℝ), (∀ q ∈ l, q.totalDegree ≤ ℓ) →
      (l.map fun q ↦ riesz (ys c) q ^ 2).sum +
        (l.map fun q ↦ (2 * riesz (ys c) q) • gradY (A := A) (ℓ := ℓ) q).sum ⬝ᵥ (x - c) ≤
        (l.map fun q ↦ riesz (ys x) q ^ 2).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons q l ih =>
      simp only [List.map_cons, List.sum_cons, add_dotProduct]
      have h1 := ih fun q' hq' ↦ hl q' (List.mem_cons_of_mem _ hq')
      have h2 := riesz_ys_sub (hl q List.mem_cons_self) x c
      rw [smul_dotProduct, smul_eq_mul, ← h2]
      nlinarith [sq_nonneg (riesz (ys x) q - riesz (ys c) q)]
  have := hlist qs fun q hq' ↦ hq q (List.mem_cons_of_mem _ hq')
  rw [obj, obj, gradObj, add_dotProduct, ← h0]
  linarith

omit [Algebra K ℝ] in
/-- **The objective cut**: if `obj(x) < obj(c)`, the gradient at `c` (or any vector, when it is
`0`) has `x` on its negative side. -/
theorem objective_cut {q₀ : MvPolynomial σ ℝ} {qs : List (MvPolynomial σ ℝ)}
    (hq : ∀ q ∈ q₀ :: qs, q.totalDegree ≤ ℓ) (c : Coord A ℓ → ℝ) (i₀ : Coord A ℓ)
    (x : Coord A ℓ → ℝ) (hx : obj q₀ qs (ys x) < obj q₀ qs (ys c)) :
    orDefault i₀ (gradObj q₀ qs c) ⬝ᵥ (x - c) ≤ 0 := by
  have h := obj_ge_add_gradObj hq x c
  unfold orDefault
  split_ifs with ha
  · rw [ha, zero_dotProduct] at h
    linarith
  · linarith

end Lifted

end SoS
