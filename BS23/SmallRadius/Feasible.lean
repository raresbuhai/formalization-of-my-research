module

public import BS23.SmallRadius.Program
public import BS23.SmallRadius.MomentSoS
public import Background.SumOfSquares.GridMoments
public import Background.SumOfSquares.SumSq
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Feasibility of the program of a round

The sum-of-squares solver needs a **valid** program (`SoS.Solver.Problem.Valid`): among other
things, the program must have a real feasible point inside its ball. This file shows that the
program of each round of the algorithm of [BS23, Theorem 1.3] (`BS23.SmallRadius.problem`, with its
two-degree moment constraint) has one, on a good frame (`BS23.SmallRadius.SRFrame.Good`), as long as
some cluster `c` keeps at least half of its points among the remaining ones.

**`BS23.SmallRadius.SRFrame.Good.valid_problem`.** For remaining points `idx : Fin n' ↪ Fin n`, a
cluster `c` with `|S_c| ≤ 2 |T|`, `T = {i : ℓ_{idx i} = c}`, the coefficients `b = bOf z t Lb` of
`B̃` on all the data, `m = t / s`, `K = (256 s)^t`, `Bd = 2^(4n²)` and a budget `Lb` that cuts
nothing (`BS23.SmallRadius.Fits`), the program on the data `z_{idx i}` is valid.
`BS23.SmallRadius.SRFrame.Good.valid_problem_list` is the same for the points of a list `Rem`
without repetitions, with `T = S_c ∩ Rem`.

The feasible point is the cluster itself: `wᵢ = 1_T(i)`, `μ = G m_c`, `σ = |T|`, `C_α` the
coefficients of `H(v) = ∑_{i ∈ T} ⟨z_i - μ, v⟩^(2s)`, and `P` a Gram factor of
`K |T|^m B̃(v) - H(v)^m`. The Boolean, size and coefficient equalities hold by construction, and
the moment equalities `Mom_γ = 0` say exactly that `∑_c (∑_β P_{βc} v^β)² = K |T|^m B̃(v) - H(v)^m`.

* **The Gram factor exists** because `K |T|^m B̃ - H^m` is a sum of squares. In the standard frame
  (`BS23.SmallRadius.SRFrame.Good.isSumSq_feas`): with `X_T = ∑_{j ∈ T} lin(g_j + e_j)^(2s)`,
  `X_T ≼ ∑_{j ∈ S_c} lin(g_j + e_j)^(2s) ≼ |S_c| (8s)^s nsq^s` (subsets and (E2)), so
  `X_T^m ≼ |S_c|^m (8s)^t nsq^t ≼ 16^t |S_c|^m (8s)^t B_std ≼ (256 s)^t |T|^m B_std` by powers,
  (E4) and `|S_c|^m ≤ 2^m |T|^m ≤ 2^t |T|^m` (`BS23.SmallRadius.feas_arith`). The substitution
  `v ↦ Gᵀ v` (`BS23.SmallRadius.substT`) turns `B_std` into `B̃` and `lin(g_j + e_j)` into
  `⟨z_j - μ, v⟩` for `j ∈ S_c`, since `z_j = G (m_c + g_j + e_j)`.
* **From squares to a Gram factor** (`BS23.SmallRadius.exists_gram`): the squares `h_k²` have
  degree at most `2t`, so `deg h_k ≤ t`; with `u_k` the coefficient vector of `h_k` on the
  exponent vectors of degree at most `t`, `Q = ∑_k u_k u_kᵀ` is positive semidefinite, and the
  spectral theorem gives `Q = P Pᵀ` (`BS23.SmallRadius.exists_mul_transpose_eq`), with
  `∑ P_{βc}² = tr Q ≤ ∑_k ‖h_k‖₂²`.
* **The ball.** By interpolation on the grid `{0, …, t}^d`
  (`BS23.SmallRadius.sum_coeffNorm_sq_le_grid`, from `SoS.coeffNorm_sq_le_sum_grid`),
  `∑_k ‖h_k‖₂² ≤ gridConst d t · ∑_x (K |T|^m B̃ - H^m)(x)`, and on the grid the polynomial is at
  most `K n^m (d n² t)^(2t)` (`BS23.SmallRadius.SRFrame.Good.eval_feas_le`, using `|z_{ja}| ≤ n²`).
  The coefficients satisfy `∑ C_α² ≤ ‖H‖₁² ≤ (n (2n³)^(2s))²`
  (`BS23.SmallRadius.SRFrame.Good.coeffNorm1_sum_lin_pow_le`), and `w`, `μ`, `σ` contribute at
  most `n`, `20 n` and `n²`. Under the guard (`(d+1)^(4t) ≤ n`, so `16 (d+1)(t+1)² ≤ n`), each
  part is at most `n^n ≤ 2^(n²)`, and the total is at most `2^(4n²)`
  (`BS23.SmallRadius.ball_arith`).
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial Finset SoS Matrix
open BS23.Separating (lin lin_add isHomogeneous_lin coeffNorm1_lin_le eval_lin)

/-! ### Polynomials from their coefficients on a list of exponent vectors -/

section Coeffs

variable {d : ℕ}

/-- The exponent vectors of a duplicate-free list, as monomials, are distinct. -/
theorem injOn_toFinsupp {Γ : List (List ℕ)} (hlen : ∀ e ∈ Γ, e.length = d) :
    ∀ e ∈ Γ.toFinset, ∀ e' ∈ Γ.toFinset, Mono.toFinsupp d e = Mono.toFinsupp d e' → e = e' :=
  fun e he e' he' h => Mono.toFinsupp_inj (hlen e (List.mem_toFinset.1 he))
    (hlen e' (List.mem_toFinset.1 he')) h

/-- A sum over the positions of a duplicate-free list of exponent vectors is a sum over the
corresponding monomials. -/
theorem sum_get_eq_sum_image {M : Type*} [AddCommMonoid M] {Γ : List (List ℕ)} (hΓ : Γ.Nodup)
    (hlen : ∀ e ∈ Γ, e.length = d) (f : (Fin d →₀ ℕ) → M) :
    ∑ j : Fin Γ.length, f (Mono.toFinsupp d (Γ.get j)) =
      ∑ m ∈ Γ.toFinset.image (Mono.toFinsupp d), f m := by
  classical
  rw [Finset.sum_image (injOn_toFinsupp hlen), List.sum_toFinset _ hΓ]
  simp only [List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem Γ (fun e => f (Mono.toFinsupp d e))

/-- The monomials of degree at most `D` are those of a list of all exponent vectors of degree at
most `D`. -/
theorem mem_image_toFinsupp {D : ℕ} {Γ : List (List ℕ)}
    (memΓ : ∀ e, e ∈ Γ ↔ e.length = d ∧ e.sum ≤ D) {m : Fin d →₀ ℕ} (hm : m.degree ≤ D) :
    m ∈ Γ.toFinset.image (Mono.toFinsupp d) := by
  classical
  refine Finset.mem_image.2 ⟨List.ofFn m, List.mem_toFinset.2 ((memΓ _).2 ⟨List.length_ofFn, ?_⟩),
    SoS.Poly.toFinsupp_ofFn m⟩
  rwa [List.sum_ofFn, ← Finsupp.degree_eq_sum]

/-- **A polynomial from its coefficients**: `∑_{e ∈ Γ} p_e X^e = p` for `p` of degree at most `D`,
when `Γ` lists every exponent vector of degree at most `D` once. -/
theorem sum_coeff_mul_powE_X {D : ℕ} {Γ : List (List ℕ)} (hΓ : Γ.Nodup)
    (memΓ : ∀ e, e ∈ Γ ↔ e.length = d ∧ e.sum ≤ D) {p : MvPolynomial (Fin d) ℝ}
    (hp : p.totalDegree ≤ D) :
    ∑ j : Fin Γ.length, C (p.coeff (Mono.toFinsupp d (Γ.get j))) *
      RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) (Γ.get j) = p := by
  classical
  have h1 : ∀ e : List ℕ, C (p.coeff (Mono.toFinsupp d e)) *
      RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) e =
        monomial (Mono.toFinsupp d e) (p.coeff (Mono.toFinsupp d e)) := fun e => by
    rw [RawAlg.powE_X_eq_monomial, C_mul_monomial, mul_one]
  simp only [h1]
  rw [sum_get_eq_sum_image hΓ (fun e he => ((memΓ e).1 he).1)
    (fun m => monomial m (p.coeff m))]
  conv_rhs => rw [p.as_sum]
  symm
  refine Finset.sum_subset (fun m hm => mem_image_toFinsupp memΓ
    ((le_totalDegree hm).trans hp)) fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, monomial_zero]

/-- **The squared coefficients on a list** are at most `‖p‖₂²`. -/
theorem sum_coeff_sq_le {Γ : List (List ℕ)} (hΓ : Γ.Nodup) (hlen : ∀ e ∈ Γ, e.length = d)
    (p : MvPolynomial (Fin d) ℝ) :
    ∑ j : Fin Γ.length, p.coeff (Mono.toFinsupp d (Γ.get j)) ^ 2 ≤ coeffNorm p ^ 2 := by
  classical
  rw [sum_get_eq_sum_image hΓ hlen (fun m => p.coeff m ^ 2),
    coeffNorm_eq_of_support_subset (Finset.subset_union_right (s₁ := Γ.toFinset.image
      (Mono.toFinsupp d))), Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun _ _ _ => sq_nonneg _

end Coeffs

/-! ### Gram factors -/

section Gram

/-- **A positive semidefinite real matrix has a square factor**: `Q = P Pᵀ`. -/
theorem exists_mul_transpose_eq {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) : ∃ P : Matrix ι ι ℝ, P * Pᵀ = Q := by
  classical
  set U : Matrix ι ι ℝ := (hQ.1.eigenvectorUnitary : Matrix ι ι ℝ)
  refine ⟨U * diagonal (fun i => Real.sqrt (hQ.1.eigenvalues i)), ?_⟩
  have hD : diagonal (fun i => Real.sqrt (hQ.1.eigenvalues i)) *
      diagonal (fun i => Real.sqrt (hQ.1.eigenvalues i)) =
        diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    exact Real.mul_self_sqrt (hQ.eigenvalues_nonneg i)
  conv_rhs => rw [hQ.1.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, transpose_mul, diagonal_transpose, ← mul_assoc,
    mul_assoc U, hD, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

variable {σ : Type*}

theorem sum_sq_eq_quad {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (e : ι → MvPolynomial σ ℝ) :
    ∑ c, (∑ β, C (P β c) * e β) ^ 2 = ∑ β, ∑ β', C ((P * Pᵀ) β β') * (e β * e β') := by
  have hL : ∀ c, (∑ β, C (P β c) * e β) ^ 2 =
      ∑ β, ∑ β', C (P β c * P β' c) * (e β * e β') := fun c => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
    rw [C_mul]
    ring
  have hR : ∀ β β', C ((P * Pᵀ) β β') * (e β * e β') =
      ∑ c, C (P β c * P β' c) * (e β * e β') := fun β β' => by
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    rfl
  simp only [hL, hR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_comm

theorem quad_vecMulVec {ι : Type*} [Fintype ι] (u : ι → ℝ) (e : ι → MvPolynomial σ ℝ) :
    ∑ β, ∑ β', C (vecMulVec u u β β') * (e β * e β') = (∑ β, C (u β) * e β) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
  rw [vecMulVec_apply, C_mul]
  ring

theorem quad_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (Q : κ → Matrix ι ι ℝ)
    (e : ι → MvPolynomial σ ℝ) :
    ∑ β, ∑ β', C ((∑ k ∈ s, Q k) β β') * (e β * e β') =
      ∑ k ∈ s, ∑ β, ∑ β', C (Q k β β') * (e β * e β') := by
  simp only [Matrix.sum_apply, map_sum, Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

variable {d : ℕ}

/-- **The Gram factor**: a sum of squares of polynomials of degree at most `t` is
`∑_c (∑_β P_{βc} X^β)²` over a list `Γ` of all exponent vectors of degree at most `t`, with
`∑ P_{βc}² ≤ ∑_h ‖h‖₂²`. -/
theorem exists_gram {t : ℕ} {Γ : List (List ℕ)} (hΓ : Γ.Nodup)
    (memΓ : ∀ e, e ∈ Γ ↔ e.length = d ∧ e.sum ≤ t) (L : List (MvPolynomial (Fin d) ℝ))
    (hL : ∀ h ∈ L, h.totalDegree ≤ t) :
    ∃ P : Fin Γ.length → Fin Γ.length → ℝ,
      ∑ c, (∑ β, C (P β c) * RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) (Γ.get β)) ^ 2 =
        (L.map fun h => h * h).sum ∧
      ∑ β, ∑ c, P β c ^ 2 ≤ (L.map fun h => coeffNorm h ^ 2).sum := by
  classical
  set e : Fin Γ.length → MvPolynomial (Fin d) ℝ := fun β => RawAlg.powE X (Γ.get β)
  set u : Fin L.length → Fin Γ.length → ℝ :=
    fun k β => (L.get k).coeff (Mono.toFinsupp d (Γ.get β))
  set Q : Matrix (Fin Γ.length) (Fin Γ.length) ℝ := ∑ k, vecMulVec (u k) (u k)
  have hQ : Q.PosSemidef := posSemidef_sum _ fun k _ => by
    simpa using posSemidef_vecMulVec_self_star (u k)
  obtain ⟨P, hP⟩ := exists_mul_transpose_eq hQ
  have hlen : ∀ e ∈ Γ, e.length = d := fun e he => ((memΓ e).1 he).1
  refine ⟨P, ?_, ?_⟩
  · change ∑ c, (∑ β, C (P β c) * e β) ^ 2 = _
    rw [sum_sq_eq_quad, hP, quad_sum]
    simp only [quad_vecMulVec, u, e]
    have : ∀ k : Fin L.length, (∑ β : Fin Γ.length, C ((L.get k).coeff
        (Mono.toFinsupp d (Γ.get β))) * RawAlg.powE X (Γ.get β)) ^ 2 = L.get k * L.get k :=
      fun k => by
        rw [sum_coeff_mul_powE_X hΓ memΓ (hL _ (List.get_mem _ _)), sq]
    simp only [this]
    simp only [List.get_eq_getElem]
    exact Fin.sum_univ_fun_getElem L (fun h => h * h)
  · have htr : ∑ β, ∑ c, P β c ^ 2 = ∑ k, ∑ β, u k β ^ 2 := by
      have h1 : ∀ β, ∑ c, P β c ^ 2 = (P * Pᵀ) β β := fun β => by
        simp [Matrix.mul_apply, sq]
      simp only [h1, hP, Q, Matrix.sum_apply, vecMulVec_apply]
      simp only [← sq]
      exact Finset.sum_comm
    rw [htr]
    calc ∑ k, ∑ β, u k β ^ 2 ≤ ∑ k : Fin L.length, coeffNorm (L.get k) ^ 2 :=
          Finset.sum_le_sum fun k _ => sum_coeff_sq_le hΓ hlen _
      _ = (L.map fun h => coeffNorm h ^ 2).sum := by
          simp only [List.get_eq_getElem]
          exact Fin.sum_univ_fun_getElem L (fun h => coeffNorm h ^ 2)

end Gram

/-! ### The grid bound on the coefficients -/

section Grid

variable {d : ℕ}

/-- The constant of the grid bound in `d` variables and degree `t`. -/
def gridConst (d t : ℕ) : ℕ := (d + 1) ^ t * interpBound t ^ (2 * d) * (t + 1) ^ d

/-- **The coefficients of a sum of squares, by the grid**: for polynomials `h` of degree at most
`t`, `∑_h ‖h‖₂² ≤ gridConst d t · ∑_{x ∈ {0,…,t}^d} (∑_h h²)(x)`. -/
theorem sum_coeffNorm_sq_le_grid {t : ℕ} (L : List (MvPolynomial (Fin d) ℝ))
    (hL : ∀ h ∈ L, h.totalDegree ≤ t) :
    (L.map fun h => coeffNorm h ^ 2).sum ≤
      gridConst d t * ∑ x : Fin d → Fin (t + 1), eval (gridPoint x) (L.map fun h => h * h).sum := by
  induction L with
  | nil => simp
  | cons h L ih =>
    simp only [List.map_cons, List.sum_cons, map_add, Finset.sum_add_distrib, mul_add]
    refine add_le_add ?_ (ih fun h' hh' => hL h' (List.mem_cons_of_mem _ hh'))
    have := coeffNorm_sq_le_sum_grid (σ := Fin d) (hL h List.mem_cons_self)
    simpa [gridConst, eval_mul, sq] using this

end Grid

/-! ### The polynomial of the feasible point, in the standard frame -/

section Frame

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

/-- `16^t |S|^m (8s)^t ≤ (256 s)^t |T|^m` for `|S| ≤ 2 |T|` and `m = t / s`. -/
theorem feas_arith {S T : ℕ} (hST : S ≤ 2 * T) :
    (16 : ℝ) ^ t * ((S : ℝ) ^ (t / s) * (8 * s) ^ t) ≤ (256 * s) ^ t * (T : ℝ) ^ (t / s) := by
  have hm : t / s ≤ t := Nat.div_le_self _ _
  have h1 : (S : ℝ) ^ (t / s) ≤ 2 ^ t * (T : ℝ) ^ (t / s) := by
    calc (S : ℝ) ^ (t / s) ≤ (2 * T) ^ (t / s) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hST) _
      _ = 2 ^ (t / s) * (T : ℝ) ^ (t / s) := mul_pow _ _ _
      _ ≤ 2 ^ t * (T : ℝ) ^ (t / s) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (by positivity)
  calc (16 : ℝ) ^ t * ((S : ℝ) ^ (t / s) * (8 * s) ^ t)
      ≤ 16 ^ t * (2 ^ t * (T : ℝ) ^ (t / s) * (8 * s) ^ t) := by gcongr
    _ = (256 * s) ^ t * (T : ℝ) ^ (t / s) := by
        have e : (256 * (s : ℝ)) ^ t = 16 ^ t * (2 ^ t * (8 * s) ^ t) := by
          rw [← mul_pow, ← mul_pow]
          ring_nf
        rw [e]
        ring

theorem isSumSq_Bstd (F : SRFrame n d k) (t : ℕ) : IsSumSq (F.Bstd t) := by
  refine isSumSq_C_mul (by positivity) (IsSumSq.sum fun j _ => ?_)
  rw [pow_mul']
  exact isSumSq_sq _

namespace SRFrame.Good

/-- **The polynomial of the feasible point is a sum of squares** (in the standard frame): for
`T ⊆ S_c` with `|S_c| ≤ 2 |T|` and `m = t / s`,
`(∑_{j ∈ T} lin(g_j + e_j)^(2s))^m ≼ (256 s)^t |T|^m B_std`. -/
theorem isSumSq_feas (hF : F.Good w R Csep s t) (c : Fin k) {T : Finset (Fin n)}
    (hT : T ⊆ cluster F.ℓ c) (hcard : (cluster F.ℓ c).card ≤ 2 * T.card) :
    IsSumSq (C ((256 * (s : ℝ)) ^ t * (T.card : ℝ) ^ (t / s)) * F.Bstd t -
      (∑ j ∈ T, lin (F.g j + F.e j) ^ (2 * s)) ^ (t / s)) := by
  have hms : s * (t / s) = t := by rw [mul_comm]; exact hF.params.div_mul_s
  set XT := ∑ j ∈ T, lin (F.g j + F.e j) ^ (2 * s) with hXT
  set Y : MvPolynomial (Fin d) ℝ := C (((cluster F.ℓ c).card : ℝ) * (8 * s) ^ s) * nsq d ^ s
  have hX : IsSumSq XT := IsSumSq.sum fun j _ => by rw [pow_mul']; exact isSumSq_sq _
  have hYX : IsSumSq (Y - XT) :=
    isSumSq_sub_trans (isSumSq_sum_lin_pow_sub_of_subset hT (fun j => F.g j + F.e j) s)
      (hF.cluster_moment_sos c)
  have h1 := isSumSq_pow_sub_pow hX hYX (t / s)
  set a : ℝ := ((cluster F.ℓ c).card : ℝ) ^ (t / s) * (8 * s) ^ t with ha
  have hYm : Y ^ (t / s) = C a * nsq d ^ t := by
    rw [mul_pow, ← C_pow, mul_pow, ← pow_mul, ← pow_mul, hms, ha]
  rw [hYm] at h1
  have h2 : IsSumSq (C (16 ^ t * a) * F.Bstd t - C a * nsq d ^ t) := by
    have := isSumSq_C_mul_sub (c := 16 ^ t * a) (by positivity) hF.covEst_lower
    convert this using 2
    rw [← mul_assoc, ← C_mul]
    congr 2
    rw [mul_comm, ← mul_assoc, ← mul_pow]
    norm_num
  have h3 := isSumSq_C_mul_sub_C_mul (feas_arith (s := s) (t := t) hcard) (isSumSq_Bstd F t)
  exact isSumSq_sub_trans (isSumSq_sub_trans h1 h2) h3

end SRFrame.Good

/-- The substitution `v ↦ Gᵀ v`: `(Gᵀ v)_a = ∑_b G_{ba} v_b`. -/
noncomputable def substT (G : Matrix (Fin d) (Fin d) ℝ) : Fin d → MvPolynomial (Fin d) ℝ :=
  fun a => ∑ b, C (G b a) * X b

/-- `lin(u)(Gᵀ v) = lin(G u)(v)`. -/
theorem aeval_substT_lin (G : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    aeval (substT G) (lin u) = lin (G *ᵥ u) := by
  simp only [lin, map_sum, map_mul, aeval_C, aeval_X, substT, Finset.mul_sum, mulVec,
    dotProduct, MvPolynomial.algebraMap_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

namespace SRFrame.Good

/-- `B_std(Gᵀ v) = (n t^t)⁻¹ ∑_j ⟨z_j, v⟩^(2t)`. -/
theorem aeval_substT_Bstd (hF : F.Good w R Csep s t) (t' : ℕ) :
    aeval (substT F.G) (F.Bstd t') =
      C (1 / ((n : ℝ) * (t' : ℝ) ^ t')) * ∑ j, lin (F.zR j) ^ (2 * t') := by
  simp only [SRFrame.Bstd, map_mul, aeval_C, MvPolynomial.algebraMap_eq, map_sum, map_pow,
    aeval_substT_lin, hF.z_eq]

/-- For `j ∈ S_c`: `lin(g_j + e_j)(Gᵀ v) = ⟨z_j - G m_c, v⟩`. -/
theorem aeval_substT_noise (hF : F.Good w R Csep s t) {c : Fin k} {j : Fin n}
    (hj : F.ℓ j = c) :
    aeval (substT F.G) (lin (F.g j + F.e j)) = lin (F.zR j - F.G *ᵥ F.m c) := by
  rw [aeval_substT_lin, hF.z_eq j, SRFrame.ζ, hj, mulVec_add, mulVec_add, mulVec_add]
  congr 1
  abel

end SRFrame.Good

end Frame

/-! ### The size of the feasible point -/

section Arith

/-- `16 (d+1) (t+1)² ≤ n` from `(d+1)^(4t) ≤ n`, for `d ≥ 1` and `t ≥ 3`. -/
theorem sixteen_mul_le {d t n : ℕ} (hd : 1 ≤ d) (ht : 3 ≤ t) (h : (d + 1) ^ (4 * t) ≤ n) :
    16 * (d + 1) * (t + 1) ^ 2 ≤ n := by
  have h1 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  have h2 : (t + 1) ^ 2 ≤ 2 ^ (2 * t) := by
    calc (t + 1) ^ 2 ≤ (2 ^ t) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 2 ^ (2 * t) := by rw [← pow_mul, mul_comm]
  have h3 : 16 ≤ 2 ^ (2 * t - 1) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (4 * t - 1) ≤ (d + 1) ^ (4 * t - 1) := Nat.pow_le_pow_left (by omega) _
  have h5 : (d + 1) ^ (4 * t) = (d + 1) * (d + 1) ^ (4 * t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h6 : 2 ^ (4 * t - 1) = 2 ^ (2 * t - 1) * 2 ^ (2 * t) := by
    rw [← pow_add]
    congr 1
    omega
  calc 16 * (d + 1) * (t + 1) ^ 2 = (d + 1) * (16 * (t + 1) ^ 2) := by ring
    _ ≤ (d + 1) * (2 ^ (2 * t - 1) * 2 ^ (2 * t)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 h2)
    _ = (d + 1) * 2 ^ (4 * t - 1) := by rw [h6]
    _ ≤ (d + 1) * (d + 1) ^ (4 * t - 1) := Nat.mul_le_mul_left _ h4
    _ = (d + 1) ^ (4 * t) := h5.symm
    _ ≤ n := h

/-- `interpBound t ≤ (t+1)^((t+1)²)`. -/
theorem interpBound_le (t : ℕ) : interpBound t ≤ (t + 1) ^ ((t + 1) ^ 2) := by
  unfold interpBound
  calc (t + 1).factorial * ((t + 1) ^ t) ^ (t + 1) ≤ (t + 1) ^ (t + 1) * ((t + 1) ^ t) ^ (t + 1) :=
        Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ = (t + 1) ^ ((t + 1) ^ 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

/-- **The arithmetic of the ball**: the bounds on the blocks of the feasible point add up to at
most `Bd = 2^(4n²)`. -/
theorem ball_arith {k d n : ℕ} {w R : ℝ} {s t : ℕ} (h : SRParams k d n w R s t) :
    21 * n + n ^ 2 + (n * (2 * n ^ 3) ^ (2 * s)) ^ 2 +
      gridConst d t * ((t + 1) ^ d * ((256 * s) ^ t * n ^ (t / s) * (d * n ^ 2 * t) ^ (2 * t)))
      ≤ ballBd n := by
  have hn : 2 ^ 20 ≤ n := h.n_ge
  have hd : 1 ≤ d := h.one_le_d
  have ht : 8 ≤ t := h.eight_le_t
  have hst : s ≤ t := h.s_le_t
  have hm : t / s ≤ t := Nat.div_le_self _ _
  have key := sixteen_mul_le hd (by omega) h.dpow_le
  set Q := (t + 1) ^ 2 with hQ
  have hQ1 : t + 1 ≤ Q := by rw [hQ]; nlinarith
  have hkey : 16 * (d * Q) + 16 * Q ≤ n := by nlinarith
  have hdQ : d ≤ d * Q := Nat.le_mul_of_pos_right _ (by omega)
  have hdn : d + 1 ≤ n := by nlinarith
  have htn : t + 1 ≤ n := by nlinarith
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  -- the Gram block
  have e1 : (d + 1) ^ t ≤ n ^ t := Nat.pow_le_pow_left hdn t
  have e2 : interpBound t ^ (2 * d) ≤ n ^ (2 * d * Q) := by
    calc interpBound t ^ (2 * d) ≤ ((t + 1) ^ Q) ^ (2 * d) :=
          Nat.pow_le_pow_left (interpBound_le t) _
      _ ≤ (n ^ Q) ^ (2 * d) := Nat.pow_le_pow_left (Nat.pow_le_pow_left htn _) _
      _ = n ^ (2 * d * Q) := by rw [← pow_mul, mul_comm]
  have e3 : (t + 1) ^ d ≤ n ^ d := Nat.pow_le_pow_left htn d
  have e4 : (256 * s) ^ t ≤ n ^ t := Nat.pow_le_pow_left (by nlinarith) t
  have e5 : n ^ (t / s) ≤ n ^ t := Nat.pow_le_pow_right hn1 hm
  have e6 : (d * n ^ 2 * t) ^ (2 * t) ≤ n ^ (8 * t) := by
    have : d * n ^ 2 * t ≤ n ^ 4 := by
      calc d * n ^ 2 * t ≤ n * n ^ 2 * n := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega))
            (by omega)
        _ = n ^ 4 := by ring
    calc (d * n ^ 2 * t) ^ (2 * t) ≤ (n ^ 4) ^ (2 * t) := Nat.pow_le_pow_left this _
      _ = n ^ (8 * t) := by rw [← pow_mul]; ring_nf
  have hE : gridConst d t * ((t + 1) ^ d * ((256 * s) ^ t * n ^ (t / s) *
      (d * n ^ 2 * t) ^ (2 * t))) ≤ n ^ n := by
    calc gridConst d t * ((t + 1) ^ d * ((256 * s) ^ t * n ^ (t / s) *
          (d * n ^ 2 * t) ^ (2 * t)))
        ≤ n ^ t * n ^ (2 * d * Q) * n ^ d * (n ^ d * (n ^ t * n ^ t * n ^ (8 * t))) := by
          unfold gridConst
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3)
            (Nat.mul_le_mul e3 (Nat.mul_le_mul (Nat.mul_le_mul e4 e5) e6))
      _ = n ^ (t + 2 * d * Q + d + (d + (t + t + 8 * t))) := by simp only [pow_add]
      _ ≤ n ^ n := Nat.pow_le_pow_right hn1 (by nlinarith)
  -- the coefficient block
  have hC : (n * (2 * n ^ 3) ^ (2 * s)) ^ 2 ≤ n ^ n := by
    have h1 : 2 * n ^ 3 ≤ n ^ 4 := by
      calc 2 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn2
        _ = n ^ 4 := by ring
    calc (n * (2 * n ^ 3) ^ (2 * s)) ^ 2 ≤ (n * (n ^ 4) ^ (2 * s)) ^ 2 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)) _
      _ = n ^ (2 + 16 * s) := by
          rw [← pow_mul, ← pow_succ', ← pow_mul]
          ring_nf
      _ ≤ n ^ n := Nat.pow_le_pow_right hn1 (by nlinarith)
  -- the small blocks
  have hS : 21 * n + n ^ 2 ≤ n ^ n := by
    have h1 : n ^ 3 ≤ n ^ n := Nat.pow_le_pow_right hn1 (by omega)
    have h2 : 22 * n ^ 2 ≤ n ^ 3 := by
      calc 22 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = n ^ 3 := by ring
    nlinarith
  have hnn : n ^ n ≤ 2 ^ (n ^ 2) := by
    calc n ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ (n ^ 2) := by rw [← pow_mul, sq]
  have hfin : 4 * 2 ^ (n ^ 2) ≤ 2 ^ (4 * n ^ 2) := by
    calc 4 * 2 ^ (n ^ 2) = 2 ^ (n ^ 2 + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (4 * n ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  unfold ballBd
  omega

end Arith

/-! ### Feasibility -/

section Feasible

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

namespace SRFrame.Good

/-- The coefficients of `∑_{i ∈ T'} ⟨z_i - μ, v⟩^(2s)`: `‖·‖₁ ≤ n (2n³)^(2s)` when `|T'| ≤ n` and
`|μ_a| ≤ n`. -/
theorem coeffNorm1_sum_lin_pow_le (hF : F.Good w R Csep s t) {n' : ℕ} (idx : Fin n' → Fin n)
    (T' : Finset (Fin n')) (hT' : T'.card ≤ n) {μv : Fin d → ℝ} (hμ : ∀ a, |μv a| ≤ n) :
    coeffNorm1 (∑ i ∈ T', lin (F.zR (idx i) - μv) ^ (2 * s)) ≤
      n * (2 * (n : ℝ) ^ 3) ^ (2 * s) := by
  have hn := hF.n_pos_real
  have hd : (d : ℝ) ≤ n := by exact_mod_cast hF.params.d_lt_n.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hF.n_pos
  have hlin : ∀ i, coeffNorm1 (lin (F.zR (idx i) - μv)) ≤ 2 * (n : ℝ) ^ 3 := fun i => by
    refine (coeffNorm1_lin_le _).trans ?_
    calc ∑ a, |(F.zR (idx i) - μv) a| ≤ ∑ _a : Fin d, 2 * (n : ℝ) ^ 2 :=
          Finset.sum_le_sum fun a _ => by
            have h1 := hF.abs_z_le (idx i) a
            have h2 := hμ a
            calc |(F.zR (idx i) - μv) a| ≤ |(F.z (idx i) a : ℝ)| + |μv a| := by
                  simpa [SRFrame.zR] using abs_sub _ _
              _ ≤ (n : ℝ) ^ 2 + n := add_le_add h1 h2
              _ ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
      _ = d * (2 * (n : ℝ) ^ 2) := by simp
      _ ≤ n * (2 * (n : ℝ) ^ 2) := by gcongr
      _ = 2 * (n : ℝ) ^ 3 := by ring
  calc coeffNorm1 (∑ i ∈ T', lin (F.zR (idx i) - μv) ^ (2 * s))
      ≤ ∑ i ∈ T', coeffNorm1 (lin (F.zR (idx i) - μv) ^ (2 * s)) := coeffNorm1_sum_le _ _
    _ ≤ ∑ _i ∈ T', (2 * (n : ℝ) ^ 3) ^ (2 * s) := Finset.sum_le_sum fun i _ =>
        (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hlin i) _)
    _ = T'.card * (2 * (n : ℝ) ^ 3) ^ (2 * s) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (2 * (n : ℝ) ^ 3) ^ (2 * s) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hT') (by positivity)

/-- **The polynomial of the feasible point on the grid**: for `0 ≤ x_a ≤ t`, `K ≥ 0` and
`H(x) ≥ 0`, `(K B̃ - H^m)(x) ≤ K (d n² t)^(2t)`. -/
theorem eval_feas_le (hF : F.Good w R Csep s t) {x : Fin d → ℝ}
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ t) {K : ℝ} (hK : 0 ≤ K) {H : MvPolynomial (Fin d) ℝ}
    (hH : 0 ≤ eval x H) (m : ℕ) :
    eval x (C K * (C (1 / ((n : ℝ) * (t : ℝ) ^ t)) * ∑ j, lin (F.zR j) ^ (2 * t)) - H ^ m) ≤
      K * ((d : ℝ) * n ^ 2 * t) ^ (2 * t) := by
  have hn := hF.n_pos_real
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast hF.params.t_pos
  have htt : (1 : ℝ) ≤ (t : ℝ) ^ t := one_le_pow₀ ht
  set B : ℝ := (d : ℝ) * n ^ 2 * t
  have hB : 0 ≤ B := by positivity
  have hj : ∀ j, (∑ a, F.zR j a * x a) ^ (2 * t) ≤ B ^ (2 * t) := fun j => by
    have h1 : |∑ a, F.zR j a * x a| ≤ B := by
      calc |∑ a, F.zR j a * x a| ≤ ∑ a, |F.zR j a * x a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin d, (n : ℝ) ^ 2 * t := Finset.sum_le_sum fun a _ => by
            rw [abs_mul, abs_of_nonneg (hx a).1]
            exact mul_le_mul (hF.abs_z_le j a) (hx a).2 (hx a).1 (by positivity)
        _ = B := by simp [B]; ring
    rw [← Even.pow_abs ⟨t, two_mul t⟩]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 _
  have hsum : ∑ j, (∑ a, F.zR j a * x a) ^ (2 * t) ≤ n * B ^ (2 * t) := by
    calc ∑ j, (∑ a, F.zR j a * x a) ^ (2 * t) ≤ ∑ _j : Fin n, B ^ (2 * t) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = n * B ^ (2 * t) := by simp
  have hsum0 : 0 ≤ ∑ j, (∑ a, F.zR j a * x a) ^ (2 * t) :=
    Finset.sum_nonneg fun j _ => by rw [pow_mul']; exact sq_nonneg _
  simp only [map_sub, map_mul, eval_C, map_sum, map_pow, eval_lin]
  have hHm : 0 ≤ eval x H ^ m := pow_nonneg hH m
  have h2 : 1 / ((n : ℝ) * t ^ t) * ∑ j, (∑ a, F.zR j a * x a) ^ (2 * t) ≤ B ^ (2 * t) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    calc ∑ j, (∑ a, F.zR j a * x a) ^ (2 * t) ≤ n * B ^ (2 * t) := hsum
      _ ≤ B ^ (2 * t) * (n * t ^ t) := by nlinarith [pow_nonneg hB (2 * t)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hK]

/-- **The program of a round is feasible**. Let the frame be good, let the
remaining points be `idx : Fin n' ↪ Fin n` (the program sees the data `z_{idx i}`), and let `c` be
a cluster with `|S_c| ≤ 2 |T|`, where `T = {i : ℓ_{idx i} = c}` is its remaining part. Then the
program with the coefficients `b = bOf z t Lb` of `B̃` on all the data, `m = t / s`,
`K = (256 s)^t` and `Bd = 2^(4n²)` is valid, as long as nothing is cut (`Fits`).

The feasible point: `w = 1_T`, `μ = G m_c`, `σ = |T|`, `C_α` the coefficients of
`H(v) = ∑_{i ∈ T} ⟨z_i - μ, v⟩^(2s)`, and `P` a Gram factor of the sum of squares
`K |T|^m B̃(v) - H(v)^m` (`isSumSq_feas` after the substitution `v ↦ Gᵀ v`, since
`z_i - μ = G (g_i + e_i)` on `T`). Its size is bounded through the grid
(`sum_coeffNorm_sq_le_grid`) and `ball_arith`. -/
theorem valid_problem (hF : F.Good w R Csep s t) {Lb : ℕ} (hfit : Fits d s t (t / s) Lb)
    {n' : ℕ} (idx : Fin n' → Fin n) (hidx : Function.Injective idx) (c : Fin k)
    (hT : (cluster F.ℓ c).card ≤ 2 * (univ.filter fun i => F.ℓ (idx i) = c).card) :
    (problem (fun i => F.z (idx i)) (bOf F.z t Lb) s t (t / s) (((256 * s) ^ t : ℕ) : ℚ)
      ((ballBd n : ℕ) : ℚ) Lb).Valid := by
  classical
  have hp := hF.params
  have hms : s * (t / s) = t := by rw [mul_comm]; exact hp.div_mul_s
  have hn'n : n' ≤ n := by simpa using Fintype.card_le_of_injective idx hidx
  have hnR := hF.n_pos_real
  set T' : Finset (Fin n') := univ.filter fun i => F.ℓ (idx i) = c with hT'
  set Tm : Finset (Fin n) := T'.map ⟨idx, hidx⟩ with hTm
  have hTmS : Tm ⊆ cluster F.ℓ c := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa [cluster] using hi
  have hTmcard : Tm.card = T'.card := Finset.card_map _
  have hT'n : T'.card ≤ n := (Finset.card_le_univ _).trans (by simpa using hn'n)
  -- the mean
  set μv : Fin d → ℝ := F.G *ᵥ F.m c with hμv
  have hμ2 : μv ⬝ᵥ μv ≤ 20 * n := by
    have h1 := hF.G_mulVec_le (F.m c)
    have h2 := hF.radius c
    have h3 := hF.three_R_sq_le_n
    nlinarith [sq_nonneg R]
  have hμ : ∀ a, |μv a| ≤ n := fun a => by
    have h1 : μv a ^ 2 ≤ μv ⬝ᵥ μv := by
      rw [dotProduct, sq]
      exact Finset.single_le_sum (f := fun b => μv b * μv b) (fun b _ => mul_self_nonneg _)
        (Finset.mem_univ a)
    have h20 : (20 : ℝ) ≤ n := by
      have : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hp.n_ge
      push_cast at this
      linarith
    exact abs_le_of_sq_le_sq (by nlinarith) hnR.le
  -- the polynomials `H`, `B̃` and `F = K |T|^m B̃ - H^m`
  set H : MvPolynomial (Fin d) ℝ := ∑ i ∈ T', lin (F.zR (idx i) - μv) ^ (2 * s) with hH
  have hHhom : H.IsHomogeneous (2 * s) := isHomogeneous_sum_lin_pow _ _ _
  set Btil : MvPolynomial (Fin d) ℝ :=
    C (1 / ((n : ℝ) * (t : ℝ) ^ t)) * ∑ j, lin (F.zR j) ^ (2 * t) with hBtil
  have hBhom : Btil.IsHomogeneous (2 * t) := (isHomogeneous_sum_lin_pow _ _ _).C_mul _
  set Kr : ℝ := (256 * (s : ℝ)) ^ t * (T'.card : ℝ) ^ (t / s) with hKr
  set Fp : MvPolynomial (Fin d) ℝ := C Kr * Btil - H ^ (t / s) with hFp
  have hFpS : IsSumSq Fp := by
    have h := isSumSq_aeval (substT F.G) (hF.isSumSq_feas c hTmS (by rw [hTmcard]; exact hT))
    have hX : aeval (substT F.G) (∑ j ∈ Tm, lin (F.g j + F.e j) ^ (2 * s)) = H := by
      rw [map_sum, hTm, Finset.sum_map]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [map_pow, Function.Embedding.coeFn_mk, hF.aeval_substT_noise hi]
    rwa [map_sub, map_mul, aeval_C, MvPolynomial.algebraMap_eq, hF.aeval_substT_Bstd, map_pow,
      hX, hTmcard] at h
  have hFpdeg : Fp.totalDegree ≤ 2 * t := by
    have h1 : (H ^ (t / s)).IsHomogeneous (2 * t) := by
      have := hHhom.pow (t / s)
      rwa [mul_assoc, hms] at this
    exact ((hBhom.C_mul Kr).sub h1).totalDegree_le
  obtain ⟨Lh, hLh, hLdeg⟩ := hFpS.exists_list_of_totalDegree_le hFpdeg
  have hL := good_lay (n := n') hfit
  obtain ⟨P, hPeq, hPtr⟩ := exists_gram (d := d) hL.nodupB hL.memB Lh fun h hh =>
    Nat.le_of_mul_le_mul_left (hLdeg h hh) (by norm_num)
  have hCsum := sum_coeff_mul_powE_X (d := d) hL.nodupA hL.memA (p := H) hHhom.totalDegree_le
  have hBsum : ((gams d t Lb).map fun γ' => C ((bOf F.z t Lb γ' : ℚ) : ℝ) *
      RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) γ').sum = Btil := by
    have h := sum_bOf_mul_powE_of_fits (S := MvPolynomial (Fin d) ℝ) F.z hfit X
    simp only [MvPolynomial.algebraMap_apply, eq_ratCast] at h
    rw [h, hBtil]
    push_cast
    rw [one_div]
    rfl
  set yw : Fin (lay n' d s t Lb).n → ℝ := fun i => if F.ℓ (idx i) = c then 1 else 0 with hyw
  set yμ : Fin (lay n' d s t Lb).d → ℝ := μv with hyμ
  set yC : Fin (lay n' d s t Lb).A → ℝ := fun j =>
    H.coeff (Mono.toFinsupp d ((lay n' d s t Lb).As.get j)) with hyC
  have hHw : (∑ i : Fin (lay n' d s t Lb).n, C (yw i) *
      (∑ a : Fin d, (C ((F.z (idx i) a : ℚ) : ℝ) - C (yμ a) : MvPolynomial (Fin d) ℝ) *
          X a) ^ (2 * s)) = H := by
    rw [hH, hT', Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [yw]
    split_ifs
    · rw [map_one, one_mul]
      simp only [lin, Pi.sub_apply, SRFrame.zR, map_sub, yμ]
    · rw [map_zero, zero_mul]
  have hKcast : ((((256 * s) ^ t : ℕ) : ℚ) : ℝ) * (T'.card : ℝ) ^ (t / s) = Kr := by
    rw [hKr]
    push_cast
    ring
  refine valid_of_eval (by have := hp.t_pos; omega)
    ((lay n' d s t Lb).point yw yμ (T'.card : ℝ) yC P) ?_ ?_ ?_ ?_ ?_
  · rw [Lay.sum_point_sq]
    have hw : ∑ i, yw i ^ 2 ≤ n := by
      calc ∑ i, yw i ^ 2 ≤ ∑ _i : Fin (lay n' d s t Lb).n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by simp only [yw]; split_ifs <;> norm_num
        _ = n' := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            rfl
        _ ≤ n := by exact_mod_cast hn'n
    have hm' : ∑ a, yμ a ^ 2 ≤ 20 * n := by
      have : ∑ a, yμ a ^ 2 = yμ ⬝ᵥ yμ := by simp [dotProduct, sq]
      rw [this]
      exact hμ2
    have hs : (T'.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hT'n) 2
    have hc : ∑ j, yC j ^ 2 ≤ ((n : ℝ) * (2 * (n : ℝ) ^ 3) ^ (2 * s)) ^ 2 := by
      calc ∑ j, yC j ^ 2 ≤ coeffNorm H ^ 2 :=
            sum_coeff_sq_le (d := d) hL.nodupA (fun e he => ((hL.memA e).1 he).1) H
        _ ≤ coeffNorm1 H ^ 2 :=
            pow_le_pow_left₀ (coeffNorm_nonneg _) (coeffNorm_le_coeffNorm1 H) 2
        _ ≤ _ := pow_le_pow_left₀ (coeffNorm1_nonneg _)
            (hF.coeffNorm1_sum_lin_pow_le idx T' hT'n hμ) 2
    have hKr0 : 0 ≤ Kr := by positivity
    have hKrle : Kr ≤ (256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) := by
      rw [hKr]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast hT'n) _) (by positivity)
    have hg : ∑ β, ∑ c', P β c' ^ 2 ≤ (gridConst d t : ℝ) * (((t : ℝ) + 1) ^ d *
        ((256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t))) := by
      have hLd : ∀ h ∈ Lh, h.totalDegree ≤ t := fun h hh =>
        Nat.le_of_mul_le_mul_left (hLdeg h hh) (by norm_num)
      refine hPtr.trans ((sum_coeffNorm_sq_le_grid Lh hLd).trans ?_)
      rw [← hLh]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      calc ∑ x : Fin d → Fin (t + 1), eval (gridPoint x) Fp
          ≤ ∑ _x : Fin d → Fin (t + 1),
              (256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t) := by
            refine Finset.sum_le_sum fun x _ => ?_
            have hx : ∀ a, 0 ≤ gridPoint x a ∧ gridPoint x a ≤ t := fun a =>
              ⟨Nat.cast_nonneg _, show ((x a : ℕ) : ℝ) ≤ t by
                exact_mod_cast Nat.lt_succ_iff.1 (x a).2⟩
            have hH0 : 0 ≤ eval (gridPoint x) H := by
              rw [hH, map_sum]
              exact Finset.sum_nonneg fun i _ => by
                rw [map_pow]
                exact (even_two_mul s).pow_nonneg _
            refine (hF.eval_feas_le hx hKr0 hH0 (t / s)).trans ?_
            exact mul_le_mul_of_nonneg_right hKrle (by positivity)
        _ = ((t : ℝ) + 1) ^ d *
              ((256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hcast : ((21 * n + n ^ 2 + (n * (2 * n ^ 3) ^ (2 * s)) ^ 2 + gridConst d t *
        ((t + 1) ^ d * ((256 * s) ^ t * n ^ (t / s) * (d * n ^ 2 * t) ^ (2 * t))) : ℕ) : ℝ) ≤
        (ballBd n : ℝ) := by exact_mod_cast ball_arith hp
    push_cast at hcast
    have hBd : ((((ballBd n : ℕ) : ℚ)) : ℝ) = (ballBd n : ℝ) := Rat.cast_natCast _
    rw [hBd]
    linarith
  · intro i
    simp only [Lay.point_wv, yw]
    split_ifs <;> norm_num
  · simp only [Lay.point_sv, Lay.point_wv, yw]
    rw [Finset.sum_boole]
    rfl
  · intro α hα
    refine (Lay.eval_coefRaw hL _ _ hα).trans ?_
    simp only [Lay.point_cv, Lay.point_wv, Lay.point_mv]
    have key : (∑ j : Fin (lay n' d s t Lb).A, (C (yC j) : MvPolynomial (Fin d) ℝ) *
        RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).As.get j) -
      ∑ i : Fin (lay n' d s t Lb).n, (C (yw i) : MvPolynomial (Fin d) ℝ) *
        (∑ a : Fin d, (C ((F.z (idx i) a : ℚ) : ℝ) - C (yμ a) : MvPolynomial (Fin d) ℝ) *
          X a) ^ (2 * s)).coeff
          (Mono.toFinsupp d α) = 0 := by
      rw [hCsum, hHw, sub_self]
      rfl
    exact key
  · intro γ hγ
    refine (Lay.eval_momRaw hL _ _ _ hγ).trans ?_
    simp only [Lay.point_sv, Lay.point_cv, Lay.point_pv]
    have key : ((C ((((256 * s) ^ t : ℕ) : ℚ) * (T'.card : ℝ) ^ (t / s)) :
          MvPolynomial (Fin d) ℝ) * ((gams d t Lb).map fun γ' =>
          (C ((bOf F.z t Lb γ' : ℚ) : ℝ) : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) γ').sum -
        (∑ j : Fin (lay n' d s t Lb).A, (C (yC j) : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).As.get j)) ^ (t / s) -
        ∑ c' : Fin (lay n' d s t Lb).B, (∑ β : Fin (lay n' d s t Lb).B,
          (C (P β c') : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).Bs.get β)) ^ 2).coeff
          (Mono.toFinsupp d γ) = 0 := by
      rw [hBsum, hCsum, hPeq, ← hLh, hFp, hKcast, sub_self]
      rfl
    exact key

/-- The remaining part of a cluster, for the remaining points listed by `Rem`:
`|{i : ℓ_{Rem[i]} = c}| = |S_c ∩ Rem|`. -/
theorem card_filter_get_eq {Rem : List (Fin n)} (hRem : Rem.Nodup) (ℓ : Fin n → Fin k)
    (c : Fin k) :
    (univ.filter fun i : Fin Rem.length => ℓ (Rem.get i) = c).card =
      (cluster ℓ c ∩ Rem.toFinset).card := by
  classical
  rw [← Finset.card_map ⟨Rem.get, List.nodup_iff_injective_get.1 hRem⟩]
  congr 1
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_inter, cluster, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, List.get_mem _ _⟩
  · rintro ⟨hj, hjR⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hjR
    exact ⟨i, hj, rfl⟩

/-- **`valid_problem` for a list of remaining points**: the program on the data `z_j`, `j ∈ Rem`
(in the order of `Rem`, without repetitions), is valid when some cluster keeps at least half of
its points in `Rem`, `|S_c| ≤ 2 |S_c ∩ Rem|`. -/
theorem valid_problem_list (hF : F.Good w R Csep s t) {Lb : ℕ} (hfit : Fits d s t (t / s) Lb)
    {Rem : List (Fin n)} (hRem : Rem.Nodup) (c : Fin k)
    (hT : (cluster F.ℓ c).card ≤ 2 * (cluster F.ℓ c ∩ Rem.toFinset).card) :
    (problem (fun i : Fin Rem.length => F.z (Rem.get i)) (bOf F.z t Lb) s t (t / s)
      (((256 * s) ^ t : ℕ) : ℚ) ((ballBd n : ℕ) : ℚ) Lb).Valid :=
  hF.valid_problem hfit Rem.get (List.nodup_iff_injective_get.1 hRem) c
    (by rwa [card_filter_get_eq hRem])

end SRFrame.Good

end Feasible

end BS23.SmallRadius
