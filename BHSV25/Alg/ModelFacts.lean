module

public import BHSV25.Model
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Facts about models

Facts about a model `M` (`BHSV25.IsModel`) and a stationary distribution `π` of it
(`BHSV25.IsStationary`), used by the algorithm of [BHSV25, Theorem 7.1].

* **Normalization** (`BHSV25.Alg.exists_isStationary_of_ne_zero`): a model with `k ≥ 1` colors
  has a stationary distribution (`IsModel` gives a positive `π` in detailed balance; dividing by
  its sum normalizes it).
* **[BHSV25, Lemma 7.3]**, in the form used here (`BHSV25.Alg.exists_stationary_stable`): if a
  probability vector `p` is stationary for `M` up to `ε` (`|∑_a p_a M_ab - p_b| ≤ ε` for all `b`),
  then `|p_a - π_a| ≤ C ε` for all `a`, with `C` depending only on `M` and `π`. The proof: the
  matrix `S = D M D⁻¹`, `D = diag(√π)`, is symmetric with the characteristic polynomial of `M`, so
  at most one of its eigenvalues is positive (`IsModel.secondEig`); the eigenvalue `1` is then
  simple, so `q ↦ (qᵀ (M - I), ∑ q)` is injective, and an injective linear map on a
  finite-dimensional space is bounded below.
* **Groups of equal rows** (`BHSV25.Alg.rowGroup`, `BHSV25.Alg.rowRep`): the colors whose rows equal
  the row of `a`, and the one of them with the largest `π` (the paper's `a_i^*`).
* **Equal rows** of a model have a `0` between them (`BHSV25.Alg.eq_zero_of_row_eq`), since the
  diagonal is `0`.
* **The contracted model has distinct rows** (`BHSV25.Alg.row_eq_of_sum_rowGroup_eq`): by detailed
  balance, the entries of a row within a group are proportional to `π`, so a row is determined by
  its sums over the groups.
* **`α` by groups** (`BHSV25.Alg.alpha_eq_sum_rowRep`):
  `α = ∑_i (π(S_i) - max(0, 2 π_{a_i^*} - π(S_i)))` over the groups `S_i`, and `α = 0` for distinct
  rows (`BHSV25.Alg.alpha_eq_zero`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix

variable {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)

/-! ### Stationary distributions -/

/-- A model with at least one color has a stationary distribution. -/
theorem exists_isStationary_of_ne_zero (hM : IsModel M) (hk : k ≠ 0) :
    ∃ π : Fin k → ℝ, IsStationary M π := by
  obtain ⟨π, hpos, hdb⟩ := hM.reversible
  have hs : 0 < ∑ a, π a :=
    Finset.sum_pos (fun a _ ↦ hpos a) ⟨⟨0, Nat.pos_of_ne_zero hk⟩, mem_univ _⟩
  refine ⟨fun a ↦ π a / ∑ b, π b, fun a ↦ div_pos (hpos a) hs, ?_, fun a b ↦ ?_⟩
  · rw [← Finset.sum_div, div_self hs.ne']
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hdb a b]

/-- `π` is fixed by `M`: `∑_a π_a M_ab = π_b`. -/
theorem sum_mul_eq_of_isStationary (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π)
    (b : Fin k) : ∑ a, π a * M a b = π b := by
  rw [Finset.sum_congr rfl fun a _ ↦ hπ.2.2 a b, ← Finset.mul_sum, hM.rowSum b, mul_one]

/-! ### Stability of the stationary distribution -/

/-- The symmetrization `D M D⁻¹`, `D = diag(√π)`, of a matrix in detailed balance with `π`. -/
noncomputable def symmetrize (π : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ √(π a) * M a b / √(π b)

theorem symmetrize_eq (π : Fin k → ℝ) :
    symmetrize M π = diagonal (fun a ↦ √(π a)) * M * diagonal (fun b ↦ (√(π b))⁻¹) := by
  ext a b
  rw [mul_diagonal, diagonal_mul, symmetrize, div_eq_mul_inv]

theorem charpoly_symmetrize {π : Fin k → ℝ} (hπ : ∀ a, 0 < π a) :
    (symmetrize M π).charpoly = M.charpoly := by
  rw [symmetrize_eq, charpoly_mul_comm, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  have h : (fun b ↦ (√(π b))⁻¹ * √(π b)) = fun _ ↦ (1 : ℝ) :=
    funext fun b ↦ inv_mul_cancel₀ (Real.sqrt_pos.2 (hπ b)).ne'
  rw [h, diagonal_one, Matrix.one_mul]

variable {M}

theorem symmetrize_isHermitian {π : Fin k → ℝ} (hπ : IsStationary M π) :
    (symmetrize M π).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b ↦ ?_
  simp only [symmetrize, star_trivial]
  have ha := Real.mul_self_sqrt (hπ.1 a).le
  have hb := Real.mul_self_sqrt (hπ.1 b).le
  rw [div_eq_div_iff (Real.sqrt_pos.2 (hπ.1 a)).ne' (Real.sqrt_pos.2 (hπ.1 b)).ne']
  calc √(π b) * M b a * √(π b) = (√(π b) * √(π b)) * M b a := by ring
    _ = (√(π a) * √(π a)) * M a b := by rw [ha, hb, hπ.2.2 a b]
    _ = √(π a) * M a b * √(π a) := by ring

/-- If `qᵀ M = qᵀ`, then `q / √π` is fixed by the symmetrization. -/
theorem symmetrize_mulVec {π : Fin k → ℝ} (hπ : IsStationary M π) {q : Fin k → ℝ}
    (hq : ∀ b, ∑ a, q a * M a b = q b) :
    symmetrize M π *ᵥ (fun a ↦ q a / √(π a)) = fun a ↦ q a / √(π a) := by
  funext b
  have hb := Real.mul_self_sqrt (hπ.1 b).le
  have hb' := (Real.sqrt_pos.2 (hπ.1 b)).ne'
  have hterm : ∀ a, symmetrize M π b a * (q a / √(π a)) = q a * M a b / √(π b) := by
    intro a
    have ha := Real.mul_self_sqrt (hπ.1 a).le
    have ha' := (Real.sqrt_pos.2 (hπ.1 a)).ne'
    rw [symmetrize, div_mul_div_comm, div_eq_div_iff (mul_ne_zero ha' ha') hb']
    calc √(π b) * M b a * q a * √(π b) = q a * ((√(π b) * √(π b)) * M b a) := by ring
      _ = q a * ((√(π a) * √(π a)) * M a b) := by rw [ha, hb, hπ.2.2 a b]
      _ = q a * M a b * (√(π a) * √(π a)) := by ring
  simp only [mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a, ← Finset.sum_div, hq b]

/-- The coefficient of `A x` on an eigenvector of a symmetric `A`. -/
theorem eigenvector_dotProduct_mulVec {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian)
    (i : Fin k) (x : Fin k → ℝ) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ x) = hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) := by
  have hs : Aᵀ = A := hA.isSymm
  rw [dotProduct_mulVec, ← mulVec_transpose, hs, hA.mulVec_eigenvectorBasis i, smul_dotProduct,
    smul_eq_mul]

/-- A vector orthogonal to all the eigenvectors of a symmetric matrix is `0`. -/
theorem eq_zero_of_eigenvector_dotProduct_eq_zero {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) {x : Fin k → ℝ} (h : ∀ i, ⇑(hA.eigenvectorBasis i) ⬝ᵥ x = 0) :
    x = 0 := by
  have h' := congrArg WithLp.ofLp ((hA.eigenvectorBasis).sum_repr' (WithLp.toLp 2 x))
  have hin : ∀ i, inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) = 0 := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using h i
  simp only [hin, zero_smul, Finset.sum_const_zero] at h'
  simpa using h'.symm

/-- At most one eigenvalue of the symmetrization of a model is positive. -/
theorem card_eigenvalues_symmetrize_pos_le (hM : IsModel M) {π : Fin k → ℝ}
    (hπ : IsStationary M π) :
    (univ.filter fun i ↦ 0 < (symmetrize_isHermitian hπ).eigenvalues i).card ≤ 1 := by
  have h := hM.secondEig
  rw [← charpoly_symmetrize M hπ.1, (symmetrize_isHermitian hπ).roots_charpoly_eq_eigenvalues,
    Multiset.filter_map, Multiset.card_map, RCLike.ofReal_real_eq_id] at h
  exact h

/-- **Simplicity of the eigenvalue `1`**: if `qᵀ M = qᵀ` and `∑ q = 0`, then `q = 0`. -/
theorem eq_zero_of_sum_mul_eq (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π)
    {q : Fin k → ℝ} (hq : ∀ b, ∑ a, q a * M a b = q b) (hs : ∑ a, q a = 0) : q = 0 := by
  funext a0
  have hS := symmetrize_isHermitian hπ
  set S := symmetrize M π with hSdef
  set u : Fin k → Fin k → ℝ := fun i ↦ ⇑(hS.eigenvectorBasis i) with hu
  set y : Fin k → ℝ := fun a ↦ q a / √(π a) with hy
  set z : Fin k → ℝ := fun a ↦ π a / √(π a) with hz
  have hSy : S *ᵥ y = y := symmetrize_mulVec hπ hq
  have hSz : S *ᵥ z = z := symmetrize_mulVec hπ (sum_mul_eq_of_isStationary M hM hπ)
  -- a vector fixed by `S` only has components on eigenvectors with eigenvalue `1`
  have key : ∀ x, S *ᵥ x = x → ∀ i, u i ⬝ᵥ x ≠ 0 → hS.eigenvalues i = 1 := by
    intro x hx i hi
    have h := eigenvector_dotProduct_mulVec hS i x
    rw [hx] at h
    exact mul_right_cancel₀ hi (h.symm.trans (one_mul _).symm)
  have hz0 : z ≠ 0 := fun h ↦
    (div_pos (hπ.1 a0) (Real.sqrt_pos.2 (hπ.1 a0))).ne' (congrFun h a0)
  obtain ⟨i0, hi0⟩ : ∃ i, u i ⬝ᵥ z ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (eq_zero_of_eigenvector_dotProduct_eq_zero hS h)
  have hcard := card_eigenvalues_symmetrize_pos_le hM hπ
  have honly : ∀ x, S *ᵥ x = x → ∀ i, i ≠ i0 → u i ⬝ᵥ x = 0 := by
    intro x hx i hi
    by_contra h
    have h1 := key x hx i h
    have h2 := key z hSz i0 hi0
    refine hi (Finset.card_le_one.1 hcard i ?_ i0 ?_)
    · rw [mem_filter, h1]
      exact ⟨mem_univ _, one_pos⟩
    · rw [mem_filter, h2]
      exact ⟨mem_univ _, one_pos⟩
  set t := (u i0 ⬝ᵥ y) / (u i0 ⬝ᵥ z) with ht
  have hw : y - t • z = 0 := by
    apply eq_zero_of_eigenvector_dotProduct_eq_zero hS
    intro i
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases hi : i = i0
    · subst hi
      rw [ht, div_mul_cancel₀ _ hi0, sub_self]
    · rw [honly y hSy i hi, honly z hSz i hi, mul_zero, sub_zero]
  have hqa : ∀ a, q a = t * π a := by
    intro a
    have h := congrFun hw a
    simp only [hy, hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rwa [sub_eq_zero, mul_div_assoc', div_left_inj' (Real.sqrt_pos.2 (hπ.1 a)).ne'] at h
  have ht0 : t = 0 := by
    have h : ∑ a, q a = t * ∑ a, π a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ hqa a
    rw [hs, hπ.2.1, mul_one] at h
    exact h.symm
  rw [hqa a0, ht0, zero_mul]
  rfl

variable (M) in
/-- The linear map `q ↦ (qᵀ M - qᵀ, ∑ q)`. -/
noncomputable def stabMap : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) × ℝ where
  toFun q := (fun b ↦ ∑ a, q a * M a b - q b, ∑ a, q a)
  map_add' q q' := by
    refine Prod.ext (funext fun b ↦ ?_) ?_
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.fst_add]
      ring
    · simp only [Pi.add_apply, Finset.sum_add_distrib, Prod.snd_add]
  map_smul' c q := by
    refine Prod.ext (funext fun b ↦ ?_) ?_
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply,
        Prod.smul_fst]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply, Prod.smul_snd]

theorem stabMap_apply (q : Fin k → ℝ) :
    stabMap M q = (fun b ↦ ∑ a, q a * M a b - q b, ∑ a, q a) :=
  rfl

theorem stabMap_injective (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π) :
    Function.Injective (stabMap M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  rw [stabMap_apply] at hq
  have h1 := congrArg Prod.fst hq
  have h2 := congrArg Prod.snd hq
  exact eq_zero_of_sum_mul_eq hM hπ (fun b ↦ sub_eq_zero.1 (congrFun h1 b)) h2

variable (M) in
/-- **[BHSV25, Lemma 7.3]** (stability of the stationary distribution): a probability vector that
is stationary for `M` up to `ε` is within `C ε` of `π`. -/
theorem exists_stationary_stable (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin k → ℝ) (ε : ℝ), ∑ a, p a = 1 →
      (∀ b, |∑ a, p a * M a b - p b| ≤ ε) → ∀ a, |p a - π a| ≤ C * ε := by
  obtain ⟨K, hK0, hK⟩ := (stabMap M).injective_iff_antilipschitz.1 (stabMap_injective hM hπ)
  refine ⟨K, NNReal.coe_pos.2 hK0, fun p ε hp hε a ↦ ?_⟩
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a)
  have hF : stabMap M (p - π) = (fun b ↦ ∑ a, p a * M a b - p b, 0) := by
    rw [stabMap_apply]
    refine Prod.ext (funext fun b ↦ ?_) ?_
    · simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
        sum_mul_eq_of_isStationary M hM hπ b]
      ring
    · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp, hπ.2.1, sub_self]
  have hFn : ‖stabMap M (p - π)‖ ≤ ε := by
    rw [hF, norm_prod_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg hε0).2 fun b ↦ ?_, by simpa using hε0⟩
    rw [Real.norm_eq_abs]
    exact hε b
  calc |p a - π a| = ‖(p - π) a‖ := by rw [Real.norm_eq_abs, Pi.sub_apply]
    _ ≤ ‖p - π‖ := norm_le_pi_norm _ a
    _ ≤ K * ‖stabMap M (p - π)‖ := ZeroHomClass.bound_of_antilipschitz (stabMap M) hK (p - π)
    _ ≤ K * ε := mul_le_mul_of_nonneg_left hFn K.2

variable (M)

/-! ### Groups of equal rows -/

open Classical in
/-- The colors whose rows equal the row of `a`. -/
noncomputable def rowGroup (a : Fin k) : Finset (Fin k) := univ.filter fun b ↦ M b = M a

/-- An element of `s` maximizing `π` (`d` if `s` is empty). -/
noncomputable def argmaxIn (π : Fin k → ℝ) (s : Finset (Fin k)) (d : Fin k) : Fin k :=
  if h : s.Nonempty then Classical.choose (s.exists_max_image π h) else d

/-- The representative of the group of `a`: the color with the largest `π` among those whose rows
equal the row of `a`. -/
noncomputable def rowRep (π : Fin k → ℝ) (a : Fin k) : Fin k := argmaxIn π (rowGroup M a) a

variable {M}

theorem argmaxIn_mem {π : Fin k → ℝ} {s : Finset (Fin k)} (d : Fin k) (h : s.Nonempty) :
    argmaxIn π s d ∈ s := by
  rw [argmaxIn, dite_eq_left h]
  exact (Classical.choose_spec (s.exists_max_image π h)).1

theorem le_argmaxIn {π : Fin k → ℝ} {s : Finset (Fin k)} (d : Fin k) {b : Fin k} (hb : b ∈ s) :
    π b ≤ π (argmaxIn π s d) := by
  have h : s.Nonempty := ⟨b, hb⟩
  rw [argmaxIn, dite_eq_left h]
  exact (Classical.choose_spec (s.exists_max_image π h)).2 b hb

theorem argmaxIn_congr {π : Fin k → ℝ} {s : Finset (Fin k)} (h : s.Nonempty) (d d' : Fin k) :
    argmaxIn π s d = argmaxIn π s d' := by
  rw [argmaxIn, argmaxIn, dite_eq_left h, dite_eq_left h]

theorem mem_rowGroup {a b : Fin k} : b ∈ rowGroup M a ↔ M b = M a := by
  classical
  simp only [rowGroup, mem_filter, mem_univ, true_and]

theorem self_mem_rowGroup (a : Fin k) : a ∈ rowGroup M a :=
  mem_rowGroup.2 rfl

theorem rowGroup_eq_of_row_eq {a b : Fin k} (h : M a = M b) : rowGroup M a = rowGroup M b := by
  ext c
  rw [mem_rowGroup, mem_rowGroup, h]

theorem row_rowRep (π : Fin k → ℝ) (a : Fin k) : M (rowRep M π a) = M a :=
  mem_rowGroup.1 (argmaxIn_mem a ⟨a, self_mem_rowGroup a⟩)

theorem rowRep_eq_rowRep_iff (π : Fin k → ℝ) {a b : Fin k} :
    rowRep M π a = rowRep M π b ↔ M a = M b := by
  constructor
  · intro h
    rw [← row_rowRep (M := M) π a, h, row_rowRep (M := M) π b]
  · intro h
    rw [rowRep, rowRep, rowGroup_eq_of_row_eq h]
    exact argmaxIn_congr ⟨b, self_mem_rowGroup b⟩ a b

theorem rowRep_rowRep (π : Fin k → ℝ) (a : Fin k) : rowRep M π (rowRep M π a) = rowRep M π a :=
  (rowRep_eq_rowRep_iff π).2 (row_rowRep π a)

theorem le_rowRep (π : Fin k → ℝ) {a b : Fin k} (h : M b = M a) : π b ≤ π (rowRep M π a) :=
  le_argmaxIn a (mem_rowGroup.2 h)

/-- Equal rows of a model have a `0` between them. -/
theorem eq_zero_of_row_eq (hM : IsModel M) {a b : Fin k} (h : M a = M b) : M a b = 0 := by
  rw [h]
  exact hM.diag b

/-- Within a group, the entries of a row are proportional to `π`. -/
theorem mul_eq_of_mem_rowGroup {π : Fin k → ℝ} (hπ : IsStationary M π) (i : Fin k) {b b' : Fin k}
    (hb' : b' ∈ rowGroup M b) : M i b' * π b = M i b * π b' := by
  have hrow : M b' i = M b i := congrFun (mem_rowGroup.1 hb') i
  have h1 := hπ.2.2 i b'
  have h2 := hπ.2.2 i b
  apply mul_left_cancel₀ (hπ.1 i).ne'
  calc π i * (M i b' * π b) = (π i * M i b') * π b := by ring
    _ = π b' * (π b * M b i) := by rw [h1, hrow]; ring
    _ = π i * (M i b * π b') := by rw [← h2]; ring

/-- **The contracted model has distinct rows**: rows with the same sums over every group are
equal. -/
theorem row_eq_of_sum_rowGroup_eq {π : Fin k → ℝ} (hπ : IsStationary M π) {i j : Fin k}
    (h : ∀ l, ∑ b ∈ rowGroup M l, M i b = ∑ b ∈ rowGroup M l, M j b) : M i = M j := by
  have hsum : ∀ i b, π b * ∑ b' ∈ rowGroup M b, M i b' = M i b * ∑ b' ∈ rowGroup M b, π b' := by
    intro i b
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' hb' ↦ ?_
    rw [mul_comm]
    exact mul_eq_of_mem_rowGroup hπ i hb'
  funext b
  have hpos : 0 < ∑ b' ∈ rowGroup M b, π b' :=
    Finset.sum_pos (fun b' _ ↦ hπ.1 b') ⟨b, self_mem_rowGroup b⟩
  apply mul_right_cancel₀ hpos.ne'
  rw [← hsum i b, ← hsum j b, h b]

/-! ### The uncovered fraction `α` -/

open Classical in
/-- The colors other than `a` whose rows equal the row of `a`. -/
theorem filter_ne_row_eq (a : Fin k) :
    univ.filter (fun b ↦ b ≠ a ∧ M b = M a) = (rowGroup M a).erase a := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_erase, mem_rowGroup]

/-- `α` with the inner sums written by groups. -/
theorem alpha_eq_sum_rowGroup (π : Fin k → ℝ) :
    alpha M π = ∑ a, min (π a) ((∑ b ∈ rowGroup M a, π b) - π a) := by
  unfold alpha
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [filter_ne_row_eq, Finset.sum_erase_eq_sub (self_mem_rowGroup a)]

/-- The contribution of one group to `α`. -/
theorem sum_rowGroup_min {π : Fin k → ℝ} (hπ : ∀ a, 0 < π a) {i : Fin k}
    (hi : rowRep M π i = i) :
    ∑ a ∈ rowGroup M i, min (π a) ((∑ b ∈ rowGroup M a, π b) - π a) =
      (∑ b ∈ rowGroup M i, π b) - max 0 (2 * π i - ∑ b ∈ rowGroup M i, π b) := by
  set P := ∑ b ∈ rowGroup M i, π b with hP
  have hgroup : ∀ a ∈ rowGroup M i, rowGroup M a = rowGroup M i := fun a ha ↦
    rowGroup_eq_of_row_eq (mem_rowGroup.1 ha)
  rw [Finset.sum_congr rfl fun a ha ↦ by rw [hgroup a ha], ← hP,
    ← Finset.add_sum_erase _ _ (self_mem_rowGroup i)]
  have hrest : ∀ a ∈ (rowGroup M i).erase i, min (π a) (P - π a) = π a := by
    intro a ha
    obtain ⟨hai, ha⟩ := mem_erase.1 ha
    have h1 : π a ≤ π i := by
      have h := le_rowRep π (mem_rowGroup.1 ha)
      rwa [hi] at h
    have h2 : π i ≤ P - π a := by
      rw [hP, ← Finset.sum_erase_eq_sub ha]
      exact Finset.single_le_sum (fun b _ ↦ (hπ b).le)
        (mem_erase.2 ⟨Ne.symm hai, self_mem_rowGroup i⟩)
    exact min_eq_left (h1.trans h2)
  rw [Finset.sum_congr rfl hrest, Finset.sum_erase_eq_sub (self_mem_rowGroup i), ← hP]
  rcases le_total (π i) (P - π i) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith only [h])]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith only [h])]
    ring

/-- **`α` by groups**: `α = ∑_i (π(S_i) - max(0, 2 π_{a_i^*} - π(S_i)))`, the sum over the
representatives `a_i^*` of the groups `S_i`. -/
theorem alpha_eq_sum_rowRep {π : Fin k → ℝ} (hπ : ∀ a, 0 < π a) :
    alpha M π = ∑ i ∈ univ.filter (fun a ↦ rowRep M π a = a),
      ((∑ b ∈ rowGroup M i, π b) - max 0 (2 * π i - ∑ b ∈ rowGroup M i, π b)) := by
  rw [alpha_eq_sum_rowGroup, ← Finset.sum_fiberwise_of_maps_to (g := rowRep M π)
    (t := univ.filter fun a ↦ rowRep M π a = a)
    (fun a _ ↦ mem_filter.2 ⟨mem_univ _, rowRep_rowRep π a⟩)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hii : rowRep M π i = i := (mem_filter.1 hi).2
  rw [← sum_rowGroup_min hπ hii]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext a
  rw [mem_filter, mem_rowGroup, ← rowRep_eq_rowRep_iff π, hii]
  exact and_iff_right (mem_univ _)

/-- `α = 0` for a model without repeated rows. -/
theorem alpha_eq_zero {π : Fin k → ℝ} (hπ : ∀ a, 0 < π a) (hrows : Function.Injective M) :
    alpha M π = 0 := by
  rw [alpha_eq_sum_rowGroup]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  have h : rowGroup M a = {a} := by
    ext b
    rw [mem_rowGroup, mem_singleton]
    exact hrows.eq_iff
  rw [h, sum_singleton, sub_self]
  exact min_eq_right (hπ a).le

end Alg

end BHSV25
