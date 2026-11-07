module

public import BGHKLMM26.IntGap.Tensor

/-!
# Approximate triangle inequalities for the long-code vectors (Khot–Saket)

The SDP vectors of Theorem 1.4 come from orthonormal tuples `{T_{u,i}}_{i ∈ L}` attached to the
vertices `u` of a Unique Games instance, with nonnegative inner products and the symmetry
`⟨T_{u,i+l}, T_{v,j+l}⟩ = ⟨T_{u,i}, T_{v,j}⟩` of Khot and Vishnoi's construction
(`BGHKLMM26.IntGap.SymTuples`). A long-code vertex is a pair `a = (u, x)` with `x : L → Bool`, and
its vector is, at scale `i < Δ`, `(1/√|L|) Σ_k (±1)^{x k} T_{u,k}^{⊗ sᵢ}`, `sᵢ = 8 · 4^{(i+1) T}`,
the scales combined by a normalized direct sum. We only use the resulting kernel
`BGHKLMM26.IntGap.lcK`, a Gram kernel (`BGHKLMM26.IntGap.lcK_posSemidef`) with unit diagonal
(`BGHKLMM26.IntGap.lcK_self`).

**The main result** (`BGHKLMM26.IntGap.approx_triangle`): every triple of long-code vertices
satisfies the signed triangle inequalities up to `3 (4/Δ + 2^{-T})`. This is Khot and Saket's
argument (FOCS 2009, Sections A and C), for three points:

* the distance `δ(u, v) = min_{k,l} ‖T_{u,k} - T_{v,l}‖` measures how close two tuples are
  (`KSAux.tdist`; by their Lemma 6 it is within a factor `2` of `‖T_u - T_v‖`,
  `T_u = (1/√|L|) Σᵢ T_{u,i}^{⊗4}`, and by the symmetry it is a pseudometric, so we use it in place
  of the latter); the minimum is attained along a shift `i ↦ i + k_{uv}` (`KSAux.shiftOf`,
  Lemma 7), and the shifts compose on sets of small diameter (`KSAux.shiftOf_add`, Lemma 8);
* for a triple of long-code vertices and a scale `i`, cluster their (at most three) Unique Games
  vertices by single linkage at distance `rᵢ = 2^{-(i+1) T}` (`KSAux.Same`); label a cluster from
  a uniform label of one of its vertices through the matchings, give each cluster an independent
  uniform sign `ω`, and set `y_{(u,x)} = (±1)^{x σ(u)} ω`. We only use the pair correlations of
  this rounding (`KSAux.rho`): `(1/|L|) Σ_j (±1)^{x j + y (j + k_{uv})}` (`KSAux.corr`) for a pair
  in one cluster, `0` otherwise;
* they satisfy the signed triangle inequalities (`KSAux.rho_triangle`): in one cluster the three
  correlations come from one labeling, and `y_a y_b + y_a y_c + y_b y_c ≥ -1` pointwise;
* at each scale they are within `2^{-T}` of the kernel (their Theorem 11,
  `KSAux.abs_rho_sub_lcKAt_le`), except at the at most two scales whose radii are within a factor
  `2^T` of `δ` (`KSAux.sum_badAt_le`): at the scales well below the distance of a pair the pair is
  in different clusters and the kernel is negligible, at the scales well above it the pair is in
  one cluster and the kernel is `corr` up to `2^{-T}`. Averaging over the scales costs
  `4/Δ + 2^{-T}` per pair.
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open scoped RealInnerProductSpace

/-- **Symmetric orthonormal tuples**: for each vertex `u` an orthonormal family `T_{u,i}`, `i ∈ L`,
with nonnegative inner products across vertices that only depend on the difference of the labels.
-/
structure SymTuples (V L I : Type) [Fintype V] [Fintype L] [AddCommGroup L] [DecidableEq L]
    [Fintype I] where
  vec : V → L → EuclideanSpace ℝ I
  orth : ∀ u i j, ⟪vec u i, vec u j⟫ = if i = j then 1 else 0
  nonneg : ∀ u i v j, 0 ≤ ⟪vec u i, vec v j⟫
  shift : ∀ u i v j l, ⟪vec u (i + l), vec v (j + l)⟫ = ⟪vec u i, vec v j⟫

/-- A bit as a sign: `false ↦ 1`, `true ↦ -1`. -/
def pm (b : Bool) : ℝ := if b then -1 else 1

/-- The tensor exponent at scale `i`: `sᵢ = 8 · 4^{(i+1) T}`. -/
def tExp (T i : ℕ) : ℕ := 8 * 4 ^ ((i + 1) * T)

variable {V L I : Type} [Fintype V] [Fintype L] [AddCommGroup L] [Fintype I] [DecidableEq L]

/-- **The long-code kernel** at `Δ` scales with spacing `T`: for `a = (u, x)` and `b = (v, y)`,
`(1/Δ) Σ_{i<Δ} (1/|L|) Σ_{k,l} (±1)^{x k} (±1)^{y l} ⟨T_{u,k}, T_{v,l}⟩^{sᵢ}`. -/
noncomputable def lcK (S : SymTuples V L I) (T Δ : ℕ) (a b : V × (L → Bool)) : ℝ :=
  (∑ i ∈ Finset.range Δ, (∑ k, ∑ l, pm (a.2 k) * pm (b.2 l) *
    ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i) / Fintype.card L) / Δ

/-! ### Auxiliary material

All helpers live in the namespace `BGHKLMM26.IntGap.KSAux`. -/

namespace KSAux

/-! #### Basic facts -/

lemma pm_mul_self (b : Bool) : pm b * pm b = 1 := by cases b <;> norm_num [pm]

lemma abs_pm (b : Bool) : |pm b| = 1 := by cases b <;> norm_num [pm]

omit [DecidableEq L] in
lemma card_L_pos : (0 : ℝ) < Fintype.card L := by
  have : Nonempty L := ⟨0⟩
  exact_mod_cast Fintype.card_pos

lemma two_le_tExp (T i : ℕ) : 2 ≤ tExp T i := by
  have := Nat.one_le_pow ((i + 1) * T) 4 (by norm_num)
  unfold tExp; omega

variable (S : SymTuples V L I)

lemma orthonormal (u : V) : Orthonormal ℝ (S.vec u) := by
  rw [orthonormal_iff_ite]; exact S.orth u

lemma norm_vec (u : V) (i : L) : ‖S.vec u i‖ = 1 := (orthonormal S u).1 i

lemma inner_le_one (u : V) (k : L) (v : V) (l : L) : ⟪S.vec u k, S.vec v l⟫ ≤ 1 := by
  have := real_inner_le_norm (S.vec u k) (S.vec v l)
  rwa [norm_vec, norm_vec, one_mul] at this

/-- Bessel's inequality for the orthonormal family `l ↦ T_{v,l}`. -/
lemma sum_inner_sq_le (u : V) (k : L) (v : V) : ∑ l, ⟪S.vec u k, S.vec v l⟫ ^ 2 ≤ 1 := by
  have := (orthonormal S v).sum_inner_products_le (S.vec u k) (s := Finset.univ)
  simpa [real_inner_comm, norm_vec, sq_abs] using this

/-- Squared distances between tuple vectors. -/
lemma norm_sub_sq (u : V) (k : L) (v : V) (l : L) :
    ‖S.vec u k - S.vec v l‖ ^ 2 = 2 - 2 * ⟪S.vec u k, S.vec v l⟫ := by
  rw [norm_sub_sq_real, norm_vec, norm_vec]; ring

/-- Distances between tuple vectors are shift invariant. -/
lemma norm_sub_shift (u : V) (k : L) (v : V) (l m : L) :
    ‖S.vec u (k + m) - S.vec v (l + m)‖ = ‖S.vec u k - S.vec v l‖ := by
  have h := norm_sub_sq S u (k + m) v (l + m)
  rw [S.shift, ← norm_sub_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! #### The kernel at one scale -/

/-- The kernel at the single scale `i`. -/
noncomputable def lcKAt (T i : ℕ) (a b : V × (L → Bool)) : ℝ :=
  (∑ k, ∑ l, pm (a.2 k) * pm (b.2 l) * ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i) /
    Fintype.card L

lemma lcK_eq (T Δ : ℕ) (a b : V × (L → Bool)) :
    lcK S T Δ a b = (∑ i ∈ Finset.range Δ, lcKAt S T i a b) / Δ := rfl

/-- If all inner products `⟪T_{u,k}, T_{v,l}⟫` are at most `M`, the kernel at scale `i` is at most
`M ^ (sᵢ - 2)` in absolute value. -/
lemma abs_lcKAt_le_pow (T i : ℕ) (a b : V × (L → Bool)) {M : ℝ}
    (hM : ∀ k l, ⟪S.vec a.1 k, S.vec b.1 l⟫ ≤ M) :
    |lcKAt S T i a b| ≤ M ^ (tExp T i - 2) := by
  have hs := two_le_tExp T i
  have hrow : ∀ k, ∑ l, ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i ≤ M ^ (tExp T i - 2) := by
    intro k
    calc ∑ l, ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i
        ≤ ∑ l, M ^ (tExp T i - 2) * ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ 2 := by
          refine Finset.sum_le_sum fun l _ ↦ ?_
          have h0 := S.nonneg a.1 k b.1 l
          rw [← Nat.sub_add_cancel hs, pow_add, Nat.add_sub_cancel]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (hM k l) _) (by positivity)
      _ = M ^ (tExp T i - 2) * ∑ l, ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ M ^ (tExp T i - 2) * 1 := by
          have hM0 : 0 ≤ M := (S.nonneg a.1 k b.1 k).trans (hM k k)
          exact mul_le_mul_of_nonneg_left (sum_inner_sq_le S _ _ _) (by positivity)
      _ = M ^ (tExp T i - 2) := mul_one _
  have hL := card_L_pos (L := L)
  rw [lcKAt, abs_div, abs_of_pos hL, div_le_iff₀ hL]
  calc |∑ k, ∑ l, pm (a.2 k) * pm (b.2 l) * ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i|
      ≤ ∑ k, ∑ l, ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
        rw [abs_mul, abs_mul, abs_pm, abs_pm, one_mul, one_mul,
          abs_of_nonneg (pow_nonneg (S.nonneg _ _ _ _) _)]
    _ ≤ ∑ _k : L, M ^ (tExp T i - 2) := Finset.sum_le_sum fun k _ ↦ hrow k
    _ = M ^ (tExp T i - 2) * Fintype.card L := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

lemma abs_lcKAt_le (T i : ℕ) (a b : V × (L → Bool)) : |lcKAt S T i a b| ≤ 1 :=
  (abs_lcKAt_le_pow S T i a b fun _ _ ↦ inner_le_one S _ _ _ _).trans_eq (one_pow _)

/-- The Gram vector of the kernel at scale `i`: `Σ_k (±1)^{x k} T_{u,k}^{⊗ sᵢ}`. -/
noncomputable def gramVec (T i : ℕ) (a : V × (L → Bool)) :
    EuclideanSpace ℝ (Fin (tExp T i) → I) :=
  ∑ k, pm (a.2 k) • tpow (tExp T i) (S.vec a.1 k)

lemma inner_gramVec (T i : ℕ) (a b : V × (L → Bool)) :
    ⟪gramVec S T i a, gramVec S T i b⟫ =
      ∑ k, ∑ l, pm (a.2 k) * pm (b.2 l) * ⟪S.vec a.1 k, S.vec b.1 l⟫ ^ tExp T i := by
  simp_rw [gramVec, sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_tpow]
  simp [mul_assoc]

/-! #### Matching the tuples of two vertices (Khot–Saket, Lemmas 6–8) -/

lemma exists_shiftOf (u v : V) :
    ∃ k, ∀ l, ‖S.vec u 0 - S.vec v k‖ ≤ ‖S.vec u 0 - S.vec v l‖ := by
  obtain ⟨k, -, hk⟩ := Finset.univ.exists_min_image (fun k ↦ ‖S.vec u 0 - S.vec v k‖)
    ⟨0, Finset.mem_univ _⟩
  exact ⟨k, fun l ↦ hk l (Finset.mem_univ _)⟩

/-- The shift `k_{uv}` matching the tuple of `u` with the tuple of `v`: `T_{u,j}` is closest to
`T_{v,j+k_{uv}}` (Khot–Saket, Lemma 7). -/
noncomputable def shiftOf (u v : V) : L := (exists_shiftOf S u v).choose

/-- The distance between the tuples of `u` and `v`, `δ(u, v) = min_{k,l} ‖T_{u,k} - T_{v,l}‖`. By
Khot and Saket's Lemma 6 it is within a factor `2` of `‖T_u - T_v‖`; we use it in its place. -/
noncomputable def tdist (u v : V) : ℝ := ‖S.vec u 0 - S.vec v (shiftOf S u v)‖

lemma tdist_le (u v : V) (k l : L) : tdist S u v ≤ ‖S.vec u k - S.vec v l‖ := by
  have h := norm_sub_shift S u 0 v (l - k) k
  rw [zero_add, sub_add_cancel] at h
  rw [h]
  exact (exists_shiftOf S u v).choose_spec _

lemma norm_sub_shiftOf (u v : V) (j : L) :
    ‖S.vec u j - S.vec v (j + shiftOf S u v)‖ = tdist S u v := by
  have h := norm_sub_shift S u 0 v (shiftOf S u v) j
  rwa [zero_add, add_comm (shiftOf S u v) j] at h

lemma tdist_nonneg (u v : V) : 0 ≤ tdist S u v := norm_nonneg _

lemma tdist_le_tdist (u v : V) : tdist S u v ≤ tdist S v u :=
  calc tdist S u v ≤ ‖S.vec u (shiftOf S v u) - S.vec v 0‖ := tdist_le S _ _ _ _
    _ = tdist S v u := norm_sub_rev _ _

lemma tdist_comm (u v : V) : tdist S u v = tdist S v u :=
  le_antisymm (tdist_le_tdist S u v) (tdist_le_tdist S v u)

lemma norm_sub_shiftOf_add_le (u v w : V) :
    ‖S.vec u 0 - S.vec w (shiftOf S u v + shiftOf S v w)‖ ≤ tdist S u v + tdist S v w := by
  calc _ ≤ ‖S.vec u 0 - S.vec v (shiftOf S u v)‖ +
        ‖S.vec v (shiftOf S u v) - S.vec w (shiftOf S u v + shiftOf S v w)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = tdist S u v + tdist S v w := by rw [norm_sub_shiftOf]; rfl

lemma tdist_triangle (u v w : V) : tdist S u w ≤ tdist S u v + tdist S v w :=
  (tdist_le S _ _ _ _).trans (norm_sub_shiftOf_add_le S u v w)

/-- **Local consistency** (Khot–Saket, Lemma 8): on three close vertices the matchings compose. -/
lemma shiftOf_add {u v w : V} (h : (tdist S u v + tdist S v w + tdist S u w) ^ 2 < 2) :
    shiftOf S u w = shiftOf S u v + shiftOf S v w := by
  by_contra hne
  have h1 : ‖S.vec w (shiftOf S u v + shiftOf S v w) - S.vec w (shiftOf S u w)‖ ≤
      tdist S u v + tdist S v w + tdist S u w := by
    calc _ ≤ ‖S.vec w (shiftOf S u v + shiftOf S v w) - S.vec u 0‖ +
          ‖S.vec u 0 - S.vec w (shiftOf S u w)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ tdist S u v + tdist S v w + tdist S u w := by
          rw [norm_sub_rev]
          exact add_le_add (norm_sub_shiftOf_add_le S u v w) le_rfl
  have h2 := norm_sub_sq S w (shiftOf S u v + shiftOf S v w) w (shiftOf S u w)
  rw [S.orth, ite_eq_right (Ne.symm hne)] at h2
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith

lemma inner_shiftOf (u v : V) (j : L) :
    ⟪S.vec u j, S.vec v (j + shiftOf S u v)⟫ = 1 - tdist S u v ^ 2 / 2 := by
  have := norm_sub_sq S u j v (j + shiftOf S u v)
  rw [norm_sub_shiftOf] at this
  linarith

lemma inner_le_tdist (u v : V) (k l : L) :
    ⟪S.vec u k, S.vec v l⟫ ≤ 1 - tdist S u v ^ 2 / 2 := by
  have h1 := norm_sub_sq S u k v l
  have h2 := pow_le_pow_left₀ (tdist_nonneg S u v) (tdist_le S u v k l) 2
  linarith

lemma tdist_sq_le (u v : V) : tdist S u v ^ 2 ≤ 2 := by
  have h1 := inner_shiftOf S u v 0
  have h2 := S.nonneg u 0 v (0 + shiftOf S u v)
  linarith

/-! #### The kernel of matched tuples -/

/-- The correlation of `a = (u, x)` and `b = (v, y)` through the matching `k_{uv}`:
`(1/|L|) Σ_j (±1)^{x j} (±1)^{y (j + k_{uv})}`. -/
noncomputable def corr (a b : V × (L → Bool)) : ℝ :=
  (∑ j, pm (a.2 j) * pm (b.2 (j + shiftOf S a.1 b.1))) / Fintype.card L

lemma abs_corr_le (a b : V × (L → Bool)) : |corr S a b| ≤ 1 := by
  have hL := card_L_pos (L := L)
  rw [corr, abs_div, abs_of_pos hL, div_le_one hL]
  calc _ ≤ ∑ j, |pm (a.2 j) * pm (b.2 (j + shiftOf S a.1 b.1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = Fintype.card L := by simp [abs_mul, abs_pm]

omit [AddCommGroup L] [DecidableEq L] in
/-- One row of the kernel of matched tuples: for nonnegative `g ≤ 1` with `Σ g² ≤ 1` and signs `c`,
`Σ_l c_l g_l^s` is `c_{l₀}` up to `(1 - g_{l₀}^s) + (1 - g_{l₀}^2)`. -/
lemma abs_row_sub_le {g c : L → ℝ} {s : ℕ} (hs : 2 ≤ s) (l₀ : L) (hg0 : ∀ l, 0 ≤ g l)
    (hg1 : ∀ l, g l ≤ 1) (hsq : ∑ l, g l ^ 2 ≤ 1) (hc : ∀ l, |c l| = 1) :
    |∑ l, c l * g l ^ s - c l₀| ≤ (1 - g l₀ ^ s) + (1 - g l₀ ^ 2) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l₀)] at hsq ⊢
  have hoff : |∑ l ∈ Finset.univ.erase l₀, c l * g l ^ s| ≤
      ∑ l ∈ Finset.univ.erase l₀, g l ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
    rw [abs_mul, hc, one_mul, abs_of_nonneg (pow_nonneg (hg0 l) _)]
    exact pow_le_pow_of_le_one (hg0 l) (hg1 l) hs
  have hdiag : |c l₀ * g l₀ ^ s - c l₀| = 1 - g l₀ ^ s := by
    rw [← mul_sub_one, abs_mul, hc, one_mul, abs_sub_comm, abs_of_nonneg]
    linarith [pow_le_one₀ (hg0 l₀) (hg1 l₀) (n := s)]
  calc |c l₀ * g l₀ ^ s + ∑ l ∈ Finset.univ.erase l₀, c l * g l ^ s - c l₀|
      = |(c l₀ * g l₀ ^ s - c l₀) + ∑ l ∈ Finset.univ.erase l₀, c l * g l ^ s| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by rw [hdiag]; linarith)

/-- **Matched tuples**: the kernel at scale `i` is `corr` up to `(sᵢ + 2) δ² / 2`. -/
lemma abs_lcKAt_sub_corr_le (T i : ℕ) (a b : V × (L → Bool)) :
    |lcKAt S T i a b - corr S a b| ≤ (tExp T i + 2) * tdist S a.1 b.1 ^ 2 / 2 := by
  have hL := card_L_pos (L := L)
  have hs := two_le_tExp T i
  have hδ := tdist_sq_le S a.1 b.1
  have hrow : ∀ j, |∑ l, pm (a.2 j) * pm (b.2 l) * ⟪S.vec a.1 j, S.vec b.1 l⟫ ^ tExp T i -
      pm (a.2 j) * pm (b.2 (j + shiftOf S a.1 b.1))| ≤
      (tExp T i + 2) * tdist S a.1 b.1 ^ 2 / 2 := by
    intro j
    refine (abs_row_sub_le (g := fun l ↦ ⟪S.vec a.1 j, S.vec b.1 l⟫)
      (c := fun l ↦ pm (a.2 j) * pm (b.2 l)) hs (j + shiftOf S a.1 b.1)
      (fun l ↦ S.nonneg _ _ _ _) (fun l ↦ inner_le_one S _ _ _ _) (sum_inner_sq_le S _ _ _)
      (fun l ↦ by rw [abs_mul, abs_pm, abs_pm, one_mul])).trans ?_
    simp only [inner_shiftOf]
    have hb := one_add_mul_le_pow (a := -(tdist S a.1 b.1 ^ 2 / 2)) (by linarith) (tExp T i)
    rw [← sub_eq_add_neg] at hb
    nlinarith [sq_nonneg (tdist S a.1 b.1 ^ 2)]
  rw [lcKAt, corr, ← sub_div, abs_div, abs_of_pos hL, div_le_iff₀ hL, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j, |∑ l, pm (a.2 j) * pm (b.2 l) * ⟪S.vec a.1 j, S.vec b.1 l⟫ ^ tExp T i -
        pm (a.2 j) * pm (b.2 (j + shiftOf S a.1 b.1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : L, (tExp T i + 2) * tdist S a.1 b.1 ^ 2 / 2 := Finset.sum_le_sum fun j _ ↦ hrow j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-! #### Scales -/

lemma cast_tExp (T i : ℕ) : (tExp T i : ℝ) = 8 * (2 ^ (i * T) * 2 ^ T) ^ 2 := by
  have h4 : ∀ n : ℕ, (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := fun n ↦ by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [tExp]; push_cast
  rw [h4, ← pow_add, add_one_mul]

lemma two_pow_add_two_mul (T i : ℕ) :
    (2 : ℝ) ^ ((i + 2) * T) = 2 ^ (i * T) * 2 ^ T * 2 ^ T := by
  rw [← pow_add, ← pow_add]; congr 1; ring

/-- At a scale well above the distance of a pair, the error of the matching is at most `2^{-T}`.
-/
lemma scale_near {T i : ℕ} (hT : 3 ≤ T) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 2 ^ ((i + 2) * T)) : (tExp T i + 2) * δ ^ 2 / 2 ≤ 1 / 2 ^ T := by
  have hR : (8 : ℝ) ≤ 2 ^ T :=
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT
  have hP : (1 : ℝ) ≤ 2 ^ (i * T) := one_le_pow₀ (by norm_num)
  rw [two_pow_add_two_mul] at hδ
  rw [cast_tExp]
  generalize (2 : ℝ) ^ (i * T) = P at *
  generalize (2 : ℝ) ^ T = R at *
  have hPR : 0 < P * R * R := by positivity
  rw [le_div_iff₀ hPR] at hδ
  rw [le_div_iff₀ (by positivity)]
  have hX : (δ * (P * R * R)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hδ
  have h1 : (δ * R) ^ 2 ≤ (δ * (P * R * R)) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have h2 : R ≤ R * R := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right hP (by positivity : (0 : ℝ) ≤ R * R)
    have : R ≤ P * R * R := by linarith
    exact mul_le_mul_of_nonneg_left this hδ0
  have e : (8 * (P * R) ^ 2 + 2) * δ ^ 2 / 2 * R * R =
      4 * (δ * (P * R * R)) ^ 2 + (δ * R) ^ 2 := by ring
  nlinarith

omit [Fintype L] [AddCommGroup L] [DecidableEq L] in
/-- `(1 - e)^n (1 + n e) ≤ 1` for `0 ≤ e ≤ 1`. -/
lemma one_sub_pow_mul_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (n : ℕ) :
    (1 - e) ^ n * (1 + n * e) ≤ 1 := by
  have h1 : 1 + n * e ≤ (1 + e) ^ n := one_add_mul_le_pow (by linarith) n
  calc (1 - e) ^ n * (1 + n * e) ≤ (1 - e) ^ n * (1 + e) ^ n :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) _)
    _ = (1 - e ^ 2) ^ n := by rw [← mul_pow]; ring
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- At a scale well below the distance of a pair, the kernel is at most `2^{-T}`. -/
lemma scale_far {T i : ℕ} (hT : 1 ≤ T) {δ : ℝ} (hδ2 : δ ^ 2 ≤ 2)
    (hδ : 1 / 2 ^ (i * T) ≤ δ) : (1 - δ ^ 2 / 2) ^ (tExp T i - 2) ≤ 1 / 2 ^ T := by
  have hs := two_le_tExp T i
  have hR : (2 : ℝ) ≤ 2 ^ T :=
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT
  have hP : (1 : ℝ) ≤ 2 ^ (i * T) := one_le_pow₀ (by norm_num)
  have hY : 0 ≤ (1 - δ ^ 2 / 2) ^ (tExp T i - 2) := pow_nonneg (by linarith) _
  have key := one_sub_pow_mul_le (e := δ ^ 2 / 2) (by positivity) (by linarith) (tExp T i - 2)
  rw [Nat.cast_sub hs, cast_tExp, Nat.cast_ofNat] at key
  generalize (1 - δ ^ 2 / 2) ^ (tExp T i - 2) = Y at *
  generalize (2 : ℝ) ^ (i * T) = P at *
  generalize (2 : ℝ) ^ T = R at *
  rw [div_le_iff₀ (by positivity)] at hδ
  have h1 : 1 ≤ (δ * P) ^ 2 := one_le_pow₀ hδ
  have h2 : R ^ 2 ≤ R ^ 2 * (δ * P) ^ 2 := le_mul_of_one_le_right (sq_nonneg _) h1
  have hne : R ≤ 1 + (8 * (P * R) ^ 2 - 2) * (δ ^ 2 / 2) := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc Y * R ≤ Y * (1 + (8 * (P * R) ^ 2 - 2) * (δ ^ 2 / 2)) := mul_le_mul_of_nonneg_left hne hY
    _ ≤ 1 := key

/-- The link threshold at scale `i`: `rᵢ = 2^{-(i+1) T}`. -/
noncomputable def rad (T i : ℕ) : ℝ := 1 / 2 ^ ((i + 1) * T)

lemma rad_nonneg (T i : ℕ) : 0 ≤ rad T i := by unfold rad; positivity

lemma le_rad (T i : ℕ) : 1 / 2 ^ ((i + 2) * T) ≤ rad T i :=
  one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ (by omega)))

lemma rad_le (T i : ℕ) : rad T i ≤ 1 / 2 ^ T :=
  one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left _ (by omega)))

lemma two_mul_rad_lt {T : ℕ} (hT : 2 ≤ T) (i : ℕ) : 2 * rad T i < 1 / 2 ^ (i * T) := by
  have hR : (4 : ℝ) ≤ 2 ^ T :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT
  have hP : (0 : ℝ) < 2 ^ (i * T) := by positivity
  rw [rad, add_one_mul, pow_add, mul_one_div, div_lt_div_iff₀ (by positivity) hP]
  nlinarith

/-! #### Rounding a triple -/

/-- Single-linkage clustering of `{u, v, w}` at threshold `θ`: `u` and `v` are in the same cluster,
joined directly or through `w`. -/
def Same (θ : ℝ) (u v w : V) : Prop :=
  tdist S u v ≤ θ ∨ (tdist S u w ≤ θ ∧ tdist S w v ≤ θ)

lemma tdist_le_of_same {θ : ℝ} (hθ : 0 ≤ θ) {u v w : V} (h : Same S θ u v w) :
    tdist S u v ≤ 2 * θ := by
  rcases h with h | ⟨h1, h2⟩
  · linarith
  · linarith [tdist_triangle S u w v]

open Classical in
/-- The correlation of `a` and `b` in the rounding of a triple `{a, b, (w, ·)}` at threshold `θ`:
`corr S a b` if `a.1` and `b.1` are in the same cluster, `0` otherwise (independent signs). -/
noncomputable def rho (θ : ℝ) (a b : V × (L → Bool)) (w : V) : ℝ :=
  if Same S θ a.1 b.1 w then corr S a b else 0

lemma rho_of_same {θ : ℝ} {a b : V × (L → Bool)} {w : V} (h : Same S θ a.1 b.1 w) :
    rho S θ a b w = corr S a b := by
  unfold rho; rw [ite_eq_left h]

lemma rho_of_not_same {θ : ℝ} {a b : V × (L → Bool)} {w : V} (h : ¬ Same S θ a.1 b.1 w) :
    rho S θ a b w = 0 := by
  unfold rho; rw [ite_eq_right h]

lemma abs_rho_le (θ : ℝ) (a b : V × (L → Bool)) (w : V) : |rho S θ a b w| ≤ 1 := by
  unfold rho; split_ifs
  · exact abs_corr_le S a b
  · simp

/-- The signed triangle inequalities for three signs. -/
lemma tri_pm {α β γ : ℝ} (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) (hγ : γ = 1 ∨ γ = -1)
    (x y z : Bool) :
    -1 ≤ α * β * (pm x * pm y) + α * γ * (pm x * pm z) + β * γ * (pm y * pm z) := by
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> rcases hγ with rfl | rfl <;>
    cases x <;> cases y <;> cases z <;> norm_num [pm]

lemma neg_one_le_sign_mul {β γ x : ℝ} (hβ : β = 1 ∨ β = -1) (hγ : γ = 1 ∨ γ = -1)
    (hx : |x| ≤ 1) : -1 ≤ β * γ * x := by
  have := abs_le.1 hx
  rcases hβ with rfl | rfl <;> rcases hγ with rfl | rfl <;> linarith

lemma sign_mul_le {β γ x y : ℝ} (hβ : β = 1 ∨ β = -1) (hγ : γ = 1 ∨ γ = -1) :
    β * γ * y ≤ β * γ * x + |y - x| := by
  have h : |β * γ| = 1 := by
    rcases hβ with rfl | rfl <;> rcases hγ with rfl | rfl <;> norm_num
  have := le_abs_self (β * γ * (y - x))
  rw [abs_mul, h, one_mul] at this
  linarith

/-- In one cluster, the three correlations come from one labeling: the triangle inequalities hold.
-/
lemma corr_triangle (a b c : V × (L → Bool))
    (hk : shiftOf S a.1 c.1 = shiftOf S a.1 b.1 + shiftOf S b.1 c.1) {α β γ : ℝ}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) (hγ : γ = 1 ∨ γ = -1) :
    -1 ≤ α * β * corr S a b + α * γ * corr S a c + β * γ * corr S b c := by
  have hL := card_L_pos (L := L)
  have hbc : corr S b c = (∑ j, pm (b.2 (j + shiftOf S a.1 b.1)) *
      pm (c.2 (j + shiftOf S a.1 c.1))) / Fintype.card L := by
    rw [corr, hk]
    congr 1
    rw [← Equiv.sum_comp (Equiv.addRight (shiftOf S a.1 b.1))]
    simp [add_assoc]
  rw [hbc, corr, corr, ← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
    ← add_div, le_div_iff₀ hL, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc -1 * (Fintype.card L : ℝ) = ∑ _j : L, (-1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ ↦ tri_pm hα hβ hγ _ _ _

/-- Single linkage on three points is transitive: if not all three pairs are joined, two of them
are not. -/
lemma not_all_three {P Q R : Prop} (h : ¬((P ∨ Q ∧ R) ∧ (Q ∨ P ∧ R) ∧ (R ∨ P ∧ Q))) :
    (¬(P ∨ Q ∧ R) ∧ ¬(Q ∨ P ∧ R)) ∨ (¬(P ∨ Q ∧ R) ∧ ¬(R ∨ P ∧ Q)) ∨
      (¬(Q ∨ P ∧ R) ∧ ¬(R ∨ P ∧ Q)) := by
  tauto

/-- **The rounding of a triple** satisfies the signed triangle inequalities. -/
lemma rho_triangle {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 36 * θ ^ 2 < 2) (a b c : V × (L → Bool))
    {α β γ : ℝ} (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) (hγ : γ = 1 ∨ γ = -1) :
    -1 ≤ α * β * rho S θ a b c.1 + α * γ * rho S θ a c b.1 + β * γ * rho S θ b c a.1 := by
  have e1 : Same S θ a.1 b.1 c.1 ↔
      tdist S a.1 b.1 ≤ θ ∨ (tdist S a.1 c.1 ≤ θ ∧ tdist S b.1 c.1 ≤ θ) := by
    rw [Same, tdist_comm S c.1 b.1]
  have e2 : Same S θ a.1 c.1 b.1 ↔
      tdist S a.1 c.1 ≤ θ ∨ (tdist S a.1 b.1 ≤ θ ∧ tdist S b.1 c.1 ≤ θ) := Iff.rfl
  have e3 : Same S θ b.1 c.1 a.1 ↔
      tdist S b.1 c.1 ≤ θ ∨ (tdist S a.1 b.1 ≤ θ ∧ tdist S a.1 c.1 ≤ θ) := by
    rw [Same, tdist_comm S b.1 a.1]
  by_cases hall : Same S θ a.1 b.1 c.1 ∧ Same S θ a.1 c.1 b.1 ∧ Same S θ b.1 c.1 a.1
  · obtain ⟨h1, h2, h3⟩ := hall
    rw [rho_of_same S h1, rho_of_same S h2, rho_of_same S h3]
    have d1 := tdist_le_of_same S hθ0 h1
    have d2 := tdist_le_of_same S hθ0 h2
    have d3 := tdist_le_of_same S hθ0 h3
    have n1 := tdist_nonneg S a.1 b.1
    have n2 := tdist_nonneg S b.1 c.1
    have n3 := tdist_nonneg S a.1 c.1
    have hsum : (tdist S a.1 b.1 + tdist S b.1 c.1 + tdist S a.1 c.1) ^ 2 ≤ (6 * θ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact corr_triangle S a b c (shiftOf_add S (by nlinarith)) hα hβ hγ
  · have : (¬ Same S θ a.1 b.1 c.1 ∧ ¬ Same S θ a.1 c.1 b.1) ∨
        (¬ Same S θ a.1 b.1 c.1 ∧ ¬ Same S θ b.1 c.1 a.1) ∨
        (¬ Same S θ a.1 c.1 b.1 ∧ ¬ Same S θ b.1 c.1 a.1) := by
      rw [e1, e2, e3] at hall ⊢; exact not_all_three hall
    rcases this with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · rw [rho_of_not_same S h1, rho_of_not_same S h2]
      have := neg_one_le_sign_mul hβ hγ (abs_rho_le S θ b c a.1)
      linarith
    · rw [rho_of_not_same S h1, rho_of_not_same S h3]
      have := neg_one_le_sign_mul hα hγ (abs_rho_le S θ a c b.1)
      linarith
    · rw [rho_of_not_same S h2, rho_of_not_same S h3]
      have := neg_one_le_sign_mul hα hβ (abs_rho_le S θ a b c.1)
      linarith

/-! #### The error of one pair -/

open Classical in
/-- The scales at which a pair at distance `δ` is neither clearly matched nor clearly separated
cost `2`. -/
noncomputable def badAt (T i : ℕ) (δ : ℝ) : ℝ :=
  if 1 / 2 ^ ((i + 2) * T) < δ ∧ δ < 1 / 2 ^ (i * T) then 2 else 0

lemma badAt_nonneg (T i : ℕ) (δ : ℝ) : 0 ≤ badAt T i δ := by
  unfold badAt; split_ifs <;> norm_num

/-- At most two scales are bad for a pair. -/
lemma sum_badAt_le (T : ℕ) (δ : ℝ) (Δ : ℕ) : ∑ i ∈ Finset.range Δ, badAt T i δ ≤ 4 := by
  classical
  set F := (Finset.range Δ).filter (fun i ↦ 1 / 2 ^ ((i + 2) * T) < δ ∧ δ < 1 / 2 ^ (i * T))
  have hsum : ∑ i ∈ Finset.range Δ, badAt T i δ = 2 * F.card := by
    simp only [badAt, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, F]
    ring
  have hcard : F.card ≤ 2 := by
    rcases F.eq_empty_or_nonempty with h | hne
    · simp [h]
    · have hsub : F ⊆ Finset.Icc (F.min' hne) (F.min' hne + 1) := by
        intro j hj
        have hm := F.min'_le j hj
        have hj' := (Finset.mem_filter.1 hj).2
        have hmF := (Finset.mem_filter.1 (F.min'_mem hne)).2
        have h := hmF.1.trans hj'.2
        rw [one_div_lt_one_div (by positivity) (by positivity),
          pow_lt_pow_iff_right₀ (by norm_num)] at h
        have := Nat.lt_of_mul_lt_mul_right h
        rw [Finset.mem_Icc]; omega
      calc F.card ≤ (Finset.Icc (F.min' hne) (F.min' hne + 1)).card := Finset.card_le_card hsub
        _ = 2 := by rw [Nat.card_Icc]; omega
  rw [hsum]
  have : (F.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  linarith

/-- **One pair**: at scale `i`, the correlation of the rounding is within `2^{-T}` of the kernel,
except at the bad scales. -/
lemma abs_rho_sub_lcKAt_le {T : ℕ} (hT : 3 ≤ T) (a b : V × (L → Bool)) (w : V) (i : ℕ) :
    |rho S (rad T i) a b w - lcKAt S T i a b| ≤ 1 / 2 ^ T + badAt T i (tdist S a.1 b.1) := by
  have hbad0 := badAt_nonneg T i (tdist S a.1 b.1)
  have hδ0 := tdist_nonneg S a.1 b.1
  by_cases hA : tdist S a.1 b.1 ≤ 1 / 2 ^ ((i + 2) * T)
  · rw [rho_of_same S (Or.inl (hA.trans (le_rad T i))), abs_sub_comm]
    have := (abs_lcKAt_sub_corr_le S T i a b).trans (scale_near hT hδ0 hA)
    linarith
  by_cases hB : 1 / 2 ^ (i * T) ≤ tdist S a.1 b.1
  · have hns : ¬ Same S (rad T i) a.1 b.1 w := fun h ↦ by
      have := tdist_le_of_same S (rad_nonneg T i) h
      have := two_mul_rad_lt (T := T) (by omega) i
      linarith
    rw [rho_of_not_same S hns, zero_sub, abs_neg]
    have := (abs_lcKAt_le_pow S T i a b (inner_le_tdist S a.1 b.1)).trans
      (scale_far (by omega) (tdist_sq_le S _ _) hB)
    linarith
  · have hbad : badAt T i (tdist S a.1 b.1) = 2 := by
      rw [badAt, ite_eq_left ⟨not_le.1 hA, not_le.1 hB⟩]
    rw [hbad]
    have h1 := abs_rho_le S (rad T i) a b w
    have h2 := abs_lcKAt_le S T i a b
    have h3 := abs_sub (rho S (rad T i) a b w) (lcKAt S T i a b)
    have h4 : (0 : ℝ) < 1 / 2 ^ T := by positivity
    linarith

end KSAux

open KSAux

/-- The kernel has unit diagonal. -/
theorem lcK_self (S : SymTuples V L I) (T : ℕ) {Δ : ℕ} (hΔ : 1 ≤ Δ) (a : V × (L → Bool)) :
    lcK S T Δ a a = 1 := by
  have hs : ∀ i, tExp T i ≠ 0 := fun i ↦ by have := two_le_tExp T i; omega
  have hi : ∀ i, lcKAt S T i a a = 1 := by
    intro i
    have hL := card_L_pos (L := L)
    rw [lcKAt, div_eq_one_iff_eq hL.ne']
    simp_rw [S.orth, ite_pow, one_pow, zero_pow (hs i), mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, pm_mul_self, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  have hΔ' : (Δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Δ ≠ 0)
  simp_rw [lcK_eq, hi, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    div_self hΔ']

/-- The kernel is bounded by `1`. -/
theorem abs_lcK_le (S : SymTuples V L I) (T Δ : ℕ) (a b : V × (L → Bool)) :
    |lcK S T Δ a b| ≤ 1 := by
  rw [lcK_eq]
  rcases Nat.eq_zero_or_pos Δ with rfl | hΔ
  · simp
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  rw [abs_div, abs_of_pos hΔ', div_le_one hΔ']
  calc |∑ i ∈ Finset.range Δ, lcKAt S T i a b|
      ≤ ∑ i ∈ Finset.range Δ, |lcKAt S T i a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range Δ, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ abs_lcKAt_le S T i a b
    _ = Δ := by simp

/-- The kernel is a Gram kernel: positive semidefinite on every finite family. -/
theorem lcK_posSemidef (S : SymTuples V L I) (T Δ : ℕ) {ι : Type} [Finite ι]
    (a : ι → V × (L → Bool)) : (Matrix.of fun i j ↦ lcK S T Δ (a i) (a j)).PosSemidef := by
  have := Fintype.ofFinite ι
  have heq : (Matrix.of fun i j ↦ lcK S T Δ (a i) (a j)) =
      ((Δ : ℝ)⁻¹ * (Fintype.card L : ℝ)⁻¹) •
        ∑ s ∈ Finset.range Δ, Matrix.gram ℝ (fun j ↦ gramVec S T s (a j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.gram_apply,
      inner_gramVec, lcK, smul_eq_mul, ← Finset.sum_div]
    field_simp
  rw [heq]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun s _ ↦ ?_) (by positivity)
  exact Matrix.posSemidef_gram ℝ _

/-- **Approximate triangle inequalities** (Khot–Saket): every triple of long-code vertices
satisfies the signed triangle inequalities up to `3 (4/Δ + 2^{-T})`. -/
theorem approx_triangle (S : SymTuples V L I) {T Δ : ℕ} (hT : 8 ≤ T) (hΔ : 1 ≤ Δ)
    (a b c : V × (L → Bool)) {α β γ : ℝ} (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (hγ : γ = 1 ∨ γ = -1) :
    -1 - 3 * (4 / Δ + 1 / 2 ^ T) ≤
      α * β * lcK S T Δ a b + α * γ * lcK S T Δ a c + β * γ * lcK S T Δ b c := by
  have hT3 : 3 ≤ T := by omega
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hR : (8 : ℝ) ≤ 2 ^ T :=
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hT3
  have hθ : ∀ i, 36 * rad T i ^ 2 < 2 := fun i ↦ by
    have h1 : rad T i ≤ 1 / 8 :=
      (rad_le T i).trans (one_div_le_one_div_of_le (by norm_num) hR)
    have h0 := rad_nonneg T i
    nlinarith
  have hstep : ∀ i ∈ Finset.range Δ,
      -1 - (3 / 2 ^ T + (badAt T i (tdist S a.1 b.1) + badAt T i (tdist S a.1 c.1) +
        badAt T i (tdist S b.1 c.1))) ≤
      α * β * lcKAt S T i a b + α * γ * lcKAt S T i a c + β * γ * lcKAt S T i b c := by
    intro i _
    have h0 := rho_triangle S (rad_nonneg T i) (hθ i) a b c hα hβ hγ
    have e1 := abs_rho_sub_lcKAt_le S hT3 a b c.1 i
    have e2 := abs_rho_sub_lcKAt_le S hT3 a c b.1 i
    have e3 := abs_rho_sub_lcKAt_le S hT3 b c a.1 i
    have f1 := sign_mul_le (x := lcKAt S T i a b) (y := rho S (rad T i) a b c.1) hα hβ
    have f2 := sign_mul_le (x := lcKAt S T i a c) (y := rho S (rad T i) a c b.1) hα hγ
    have f3 := sign_mul_le (x := lcKAt S T i b c) (y := rho S (rad T i) b c a.1) hβ hγ
    have : 3 / 2 ^ T = 1 / 2 ^ T + 1 / 2 ^ T + (1 : ℝ) / 2 ^ T := by ring
    linarith
  have hsum := Finset.sum_le_sum hstep
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hb1 := sum_badAt_le T (tdist S a.1 b.1) Δ
  have hb2 := sum_badAt_le T (tdist S a.1 c.1) Δ
  have hb3 := sum_badAt_le T (tdist S b.1 c.1) Δ
  rw [lcK_eq, lcK_eq, lcK_eq, ← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
    ← add_div, le_div_iff₀ hΔ']
  have e : (-1 - 3 * (4 / (Δ : ℝ) + 1 / 2 ^ T)) * Δ = -(Δ : ℝ) - 12 - Δ * (3 / 2 ^ T) := by
    field_simp; ring
  rw [e]
  linarith

end BGHKLMM26.IntGap
