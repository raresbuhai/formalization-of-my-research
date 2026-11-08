module

public import BS23.SmallRadius.Params
public import BS23.Common.Good

/-!
# The standard frame of the small-radius analysis

The analysis of the algorithm of [BS23, Theorem 1.3] runs in a **standard frame**: the whitened,
re-rounded data `z_j` the algorithm computes are an invertible linear image `G ζ_j` of
**standard points** `ζ_j = m_{ℓ_j} + g_j + e_j`, where the `m_c` are the means in the geometry of
the components, the `g_j` the standardized noises and the `e_j` small errors (the rounding of the
sample and the re-rounding of the data). `BS23.SmallRadius.SRFrame` holds these data and
`BS23.SmallRadius.SRFrame.Good` the facts the analysis uses about them. All squared lengths are
dot products `v ⬝ᵥ v` (the norm of `Fin d → ℝ` in Mathlib is the sup norm).

`SRFrame.Good F w R Csep s t` says:

* `z_j = G ζ_j`, with `G` invertible, `‖Gᵀ v‖² ≤ 20 ‖v‖²` and `‖v‖² ≤ 3 (R² + 2) ‖Gᵀ v‖²`
  (so `Σ' = G Gᵀ`, the covariance of the components in the data frame, is within those factors of
  the identity);
* `‖e_j‖² ≤ 4 / n²`, `‖m_c‖² ≤ R²` and `‖m_a - m_b‖² ≥ Csep ln (1/w)` for `a ≠ b`;
* the weights `wt c ≥ w` sum to `1`;
* the good events `GoodNoise wt (τ w d t r) r ℓ g` of all degrees `r ≤ 2t`;
* the parameter facts `BS23.SmallRadius.SRParams k d n w R s t`.

The parameter facts are the separate structure `SRParams`, and the standard point is the
definition `BS23.SmallRadius.SRFrame.ζ`.

Consequences:

* (F-a) cluster sizes: `w n / 2 ≤ wt_c n / 2 ≤ |S_c| ≤ 2 wt_c n`
  (`BS23.SmallRadius.SRFrame.Good.wt_mul_le_card`, `BS23.SmallRadius.SRFrame.Good.card_le`), and
  `k ≤ 1 / w ≤ n` (`BS23.SmallRadius.SRFrame.Good.k_le_inv_w`,
  `BS23.SmallRadius.SRFrame.Good.inv_w_le_n`);
* (F-b) `∑_j ‖g_j‖² ≤ 2 n d` (`BS23.SmallRadius.SRFrame.Good.sum_g_sq_le`);
* (F-c) `‖ζ_j‖² ≤ 3 (R² + 2 n d + 4 / n²)`, `z_{ja}² ≤ 20 ‖ζ_j‖²` and `|z_{ja}| ≤ n²`
  (`BS23.SmallRadius.SRFrame.Good.ζ_sq_le`, `BS23.SmallRadius.SRFrame.Good.z_sq_le`,
  `BS23.SmallRadius.SRFrame.Good.abs_z_le`);
* (F-d) `‖G u‖² ≤ 20 ‖u‖²`, `‖G⁻¹ u‖² ≤ 3 (R² + 2) ‖u‖²` and `‖G⁻¹ᵀ u‖² ≤ 3 (R² + 2) ‖u‖²`, with
  `3 (R² + 2) ≤ n` (`BS23.SmallRadius.SRFrame.Good.G_mulVec_le`,
  `BS23.SmallRadius.SRFrame.Good.Ginv_mulVec_le`, `BS23.SmallRadius.SRFrame.Good.GinvT_mulVec_le`,
  `BS23.SmallRadius.SRParams.three_R_sq_le_n`).
-/

@[expose] public section

namespace BS23.SmallRadius

open Matrix

/-! ### Two facts about dot products -/

/-- Cauchy–Schwarz for dot products. -/
theorem dotProduct_sq_le {d : ℕ} (u v : Fin d → ℝ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simpa only [dotProduct, sq] using h

theorem dotProduct_self_nonneg' {d : ℕ} (u : Fin d → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (u i)

/-- `‖a + b + c‖² ≤ 3 (‖a‖² + ‖b‖² + ‖c‖²)`. -/
theorem dotProduct_add_add_le {d : ℕ} (a b c : Fin d → ℝ) :
    (a + b + c) ⬝ᵥ (a + b + c) ≤ 3 * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c) := by
  simp only [dotProduct, Pi.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  nlinarith [sq_nonneg (a i - b i), sq_nonneg (b i - c i), sq_nonneg (a i - c i)]

/-- An operator-norm bound for `Aᵀ` is one for `A`: if `‖Aᵀ v‖² ≤ c ‖v‖²` for all `v`, then
`‖A u‖² ≤ c ‖u‖²` for all `u`. -/
theorem dotProduct_mulVec_le_of_transpose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ v, (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) ≤ c * (v ⬝ᵥ v)) (u : Fin d → ℝ) :
    (A *ᵥ u) ⬝ᵥ (A *ᵥ u) ≤ c * (u ⬝ᵥ u) := by
  set y := A *ᵥ u with hy
  have e : y ⬝ᵥ y = (Aᵀ *ᵥ y) ⬝ᵥ u := by
    conv_lhs => rw [hy, dotProduct_mulVec]
    rw [mulVec_transpose]
  have h1 := dotProduct_sq_le (Aᵀ *ᵥ y) u
  rw [← e] at h1
  have h2 := h y
  have hyy := dotProduct_self_nonneg' y
  have huu := dotProduct_self_nonneg' u
  rcases hyy.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h3 : (y ⬝ᵥ y) * (y ⬝ᵥ y) ≤ (y ⬝ᵥ y) * (c * (u ⬝ᵥ u)) := by
      calc (y ⬝ᵥ y) * (y ⬝ᵥ y) = (y ⬝ᵥ y) ^ 2 := (sq _).symm
        _ ≤ ((Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y)) * (u ⬝ᵥ u) := h1
        _ ≤ (c * (y ⬝ᵥ y)) * (u ⬝ᵥ u) := mul_le_mul_of_nonneg_right h2 huu
        _ = (y ⬝ᵥ y) * (c * (u ⬝ᵥ u)) := by ring
    exact le_of_mul_le_mul_left h3 hpos

/-! ### The frame -/

/-- The data of the **standard frame**: the labels `ℓ`, the whitened data `z` the algorithm
computes, the whitening map `G` from the standard frame to the data frame, the means `m` in the
standard frame, the standardized noises `g`, the errors `e`, and the weights `wt`. -/
structure SRFrame (n d k : ℕ) where
  /-- The labels of the sample. -/
  ℓ : Fin n → Fin k
  /-- The whitened, re-rounded data. -/
  z : Fin n → Fin d → ℚ
  /-- The map from the standard frame to the data frame. -/
  G : Matrix (Fin d) (Fin d) ℝ
  /-- The means in the standard frame. -/
  m : Fin k → Fin d → ℝ
  /-- The standardized noises. -/
  g : Fin n → Fin d → ℝ
  /-- The errors (rounding of the sample and re-rounding of the data). -/
  e : Fin n → Fin d → ℝ
  /-- The weights of the components. -/
  wt : Fin k → ℝ

namespace SRFrame

variable {n d k : ℕ}

/-- The **standard point** `ζ_j = m_{ℓ_j} + g_j + e_j`. -/
def ζ (F : SRFrame n d k) (j : Fin n) : Fin d → ℝ := F.m (F.ℓ j) + F.g j + F.e j

/-- The real coordinates of the whitened data. -/
def zR (F : SRFrame n d k) (j : Fin n) : Fin d → ℝ := fun a ↦ (F.z j a : ℝ)

/-- **A good frame**: the facts about the standard frame that the analysis uses, for a weight
bound `w`, a radius bound `R`, a separation constant `Csep` and degrees `s` and `t`. -/
structure Good (F : SRFrame n d k) (w R Csep : ℝ) (s t : ℕ) : Prop where
  z_eq : ∀ j, F.zR j = F.G *ᵥ F.ζ j
  G_inv : IsUnit F.G.det
  G_up : ∀ v, (F.Gᵀ *ᵥ v) ⬝ᵥ (F.Gᵀ *ᵥ v) ≤ 20 * (v ⬝ᵥ v)
  G_low : ∀ v, v ⬝ᵥ v ≤ 3 * (R ^ 2 + 2) * ((F.Gᵀ *ᵥ v) ⬝ᵥ (F.Gᵀ *ᵥ v))
  err : ∀ j, F.e j ⬝ᵥ F.e j ≤ 4 / (n : ℝ) ^ 2
  radius : ∀ c, F.m c ⬝ᵥ F.m c ≤ R ^ 2
  sep : ∀ a b, a ≠ b → Csep * Real.log (1 / w) ≤ (F.m a - F.m b) ⬝ᵥ (F.m a - F.m b)
  wt_ge : ∀ c, w ≤ F.wt c
  wt_sum : ∑ c, F.wt c = 1
  good : ∀ r ≤ 2 * t, GoodNoise F.wt (τ w d t r) r F.ℓ F.g
  params : SRParams k d n w R s t

namespace Good

variable {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

theorem n_pos (hF : F.Good w R Csep s t) : 0 < n := hF.params.n_pos

theorem n_pos_real (hF : F.Good w R Csep s t) : (0 : ℝ) < n := by
  exact_mod_cast hF.n_pos

theorem w_pos (hF : F.Good w R Csep s t) : 0 < w := hF.params.w_pos

theorem wt_pos (hF : F.Good w R Csep s t) (c : Fin k) : 0 < F.wt c :=
  hF.w_pos.trans_le (hF.wt_ge c)

/-! #### (F-a) Cluster sizes -/

/-- `k w ≤ 1`. -/
theorem k_mul_w_le (hF : F.Good w R Csep s t) : (k : ℝ) * w ≤ 1 := by
  calc (k : ℝ) * w = ∑ _c : Fin k, w := by simp
    _ ≤ ∑ c, F.wt c := Finset.sum_le_sum fun c _ ↦ hF.wt_ge c
    _ = 1 := hF.wt_sum

/-- `k ≤ 1 / w`. -/
theorem k_le_inv_w (hF : F.Good w R Csep s t) : (k : ℝ) ≤ 1 / w := by
  rw [le_div_iff₀ hF.w_pos]; exact hF.k_mul_w_le

/-- `1 / w ≤ n`. -/
theorem inv_w_le_n (hF : F.Good w R Csep s t) : 1 / w ≤ n := hF.params.inv_w_le_n

/-- `k ≤ n`. -/
theorem k_le_n (hF : F.Good w R Csep s t) : k ≤ n := hF.params.k_le

/-- The degree-`0` good event bounds the cluster fractions: `| |S_c| / n - wt_c | ≤ wt_c / 2`. -/
theorem abs_card_sub_le (hF : F.Good w R Csep s t) (c : Fin k) :
    |((cluster F.ℓ c).card : ℝ) / n - F.wt c| ≤ F.wt c / 2 := by
  have h := (hF.good 0 (Nat.zero_le _)).1 c
  have hτ : τ w d t 0 ≤ w / 128 :=
    τ_le_of_le_two hF.w_pos.le d (by have := hF.params.t_pos; omega) (by norm_num)
  have hw1 : w ≤ 1 := hF.params.w_le_one
  have hwc := hF.wt_pos c
  calc |((cluster F.ℓ c).card : ℝ) / n - F.wt c| ≤ τ w d t 0 * F.wt c := h
    _ ≤ (1 / 2) * F.wt c := mul_le_mul_of_nonneg_right (by linarith) hwc.le
    _ = F.wt c / 2 := by ring

/-- `wt_c n / 2 ≤ |S_c|`. -/
theorem wt_mul_le_card (hF : F.Good w R Csep s t) (c : Fin k) :
    F.wt c * n / 2 ≤ (cluster F.ℓ c).card := by
  have h := (abs_le.1 (hF.abs_card_sub_le c)).1
  have hn := hF.n_pos_real
  have : F.wt c / 2 ≤ ((cluster F.ℓ c).card : ℝ) / n := by linarith
  rw [le_div_iff₀ hn] at this
  linarith

/-- `w n / 2 ≤ |S_c|`. -/
theorem w_mul_le_card (hF : F.Good w R Csep s t) (c : Fin k) :
    w * n / 2 ≤ (cluster F.ℓ c).card := by
  have h := hF.wt_mul_le_card c
  have : w * n / 2 ≤ F.wt c * n / 2 := by
    have := hF.wt_ge c
    have := hF.n_pos_real
    gcongr
  linarith

/-- `|S_c| ≤ 2 wt_c n`. -/
theorem card_le (hF : F.Good w R Csep s t) (c : Fin k) :
    ((cluster F.ℓ c).card : ℝ) ≤ 2 * F.wt c * n := by
  have h := (abs_le.1 (hF.abs_card_sub_le c)).2
  have hn := hF.n_pos_real
  have hwc := hF.wt_pos c
  have : ((cluster F.ℓ c).card : ℝ) / n ≤ 2 * F.wt c := by linarith
  rwa [div_le_iff₀ hn] at this

/-! #### (F-b) The noise has bounded second moments -/

theorem sum_cluster_eq {β : Type*} [AddCommMonoid β] (ℓ : Fin n → Fin k) (f : Fin n → β) :
    ∑ c, ∑ j ∈ cluster ℓ c, f j = ∑ j, f j := by
  unfold cluster
  exact Finset.sum_fiberwise _ _ _

/-- `∑_j g_{ja}² ≤ n (1 + k τ_2)` for each coordinate `a`, from the degree-`2` good event. -/
theorem sum_g_coord_sq_le (hF : F.Good w R Csep s t) (a : Fin d) :
    ∑ j, F.g j a ^ 2 ≤ n * (1 + k * τ w d t 2) := by
  have h2 : 2 ≤ 2 * t := by have := hF.params.t_pos; omega
  have hgood := (hF.good 2 h2).2
  set α : Fin d → ℕ := Pi.single a 2 with hα
  have hαsum : ∑ i, α i ≤ 2 := by simp [hα]
  have hprod : ∀ j, ∏ i, F.g j i ^ α i = F.g j a ^ 2 := fun j ↦ by
    rw [Finset.prod_eq_single a (fun i _ hi ↦ by simp [hα, hi]) (by simp)]
    simp [hα]
  have hmom : (gaussMomMulti α : ℝ) = 1 := by
    have : gaussMomMulti α = 1 := by
      unfold gaussMomMulti
      refine Finset.prod_eq_one fun i _ ↦ ?_
      by_cases hi : i = a
      · subst hi; simp [hα, gaussMom]
      · simp [hα, hi, gaussMom]
    exact_mod_cast this
  have hn := hF.n_pos_real
  have hc : ∀ c, (∑ j ∈ cluster F.ℓ c, F.g j a ^ 2) ≤
      ((cluster F.ℓ c).card : ℝ) + n * τ w d t 2 := fun c ↦ by
    have h := (abs_le.1 (hgood c α hαsum)).2
    simp only [hprod, hmom, mul_one] at h
    have h' : (∑ j ∈ cluster F.ℓ c, F.g j a ^ 2) / n ≤
        ((cluster F.ℓ c).card : ℝ) / n + τ w d t 2 := by linarith
    rw [div_le_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne'] at h'
    linarith
  have hcard : ∑ c, ((cluster F.ℓ c).card : ℝ) = n := by
    have := sum_cluster_eq F.ℓ (fun _ ↦ (1 : ℝ))
    simpa using this
  calc ∑ j, F.g j a ^ 2 = ∑ c, ∑ j ∈ cluster F.ℓ c, F.g j a ^ 2 := (sum_cluster_eq _ _).symm
    _ ≤ ∑ c, (((cluster F.ℓ c).card : ℝ) + n * τ w d t 2) := Finset.sum_le_sum fun c _ ↦ hc c
    _ = n * (1 + k * τ w d t 2) := by
        rw [Finset.sum_add_distrib, hcard]
        simp
        ring

/-- `k τ_2 ≤ 1`. -/
theorem k_mul_τ_two_le (hF : F.Good w R Csep s t) : (k : ℝ) * τ w d t 2 ≤ 1 := by
  have hτ : τ w d t 2 ≤ w / 128 :=
    τ_le_of_le_two hF.w_pos.le d (by have := hF.params.t_pos; omega) le_rfl
  have hk := hF.k_mul_w_le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  calc (k : ℝ) * τ w d t 2 ≤ k * (w / 128) := mul_le_mul_of_nonneg_left hτ hk0
    _ = k * w / 128 := by ring
    _ ≤ 1 := by linarith

/-- **(F-b)** `∑_j ‖g_j‖² ≤ 2 n d`. -/
theorem sum_g_sq_le (hF : F.Good w R Csep s t) :
    ∑ j, F.g j ⬝ᵥ F.g j ≤ 2 * n * d := by
  have hkτ := hF.k_mul_τ_two_le
  have hn := hF.n_pos_real
  calc ∑ j, F.g j ⬝ᵥ F.g j = ∑ a, ∑ j, F.g j a ^ 2 := by
        simp only [dotProduct, ← sq]
        exact Finset.sum_comm
    _ ≤ ∑ _a : Fin d, (n : ℝ) * (1 + k * τ w d t 2) :=
        Finset.sum_le_sum fun a _ ↦ hF.sum_g_coord_sq_le a
    _ ≤ ∑ _a : Fin d, (n : ℝ) * 2 :=
        Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (by linarith) hn.le
    _ = 2 * n * d := by simp; ring

/-- `‖g_j‖² ≤ 2 n d`. -/
theorem g_sq_le (hF : F.Good w R Csep s t) (j : Fin n) : F.g j ⬝ᵥ F.g j ≤ 2 * n * d :=
  (Finset.single_le_sum (fun i _ ↦ dotProduct_self_nonneg' (F.g i)) (Finset.mem_univ j)).trans
    hF.sum_g_sq_le

/-! #### (F-d) The whitening map -/

/-- `‖G u‖² ≤ 20 ‖u‖²`. -/
theorem G_mulVec_le (hF : F.Good w R Csep s t) (u : Fin d → ℝ) :
    (F.G *ᵥ u) ⬝ᵥ (F.G *ᵥ u) ≤ 20 * (u ⬝ᵥ u) :=
  dotProduct_mulVec_le_of_transpose (by norm_num) hF.G_up u

theorem three_R_sq_nonneg (R : ℝ) : 0 ≤ 3 * (R ^ 2 + 2) := by positivity

/-- `‖G⁻¹ᵀ u‖² ≤ 3 (R² + 2) ‖u‖²`. -/
theorem GinvT_mulVec_le (hF : F.Good w R Csep s t) (u : Fin d → ℝ) :
    (F.G⁻¹ᵀ *ᵥ u) ⬝ᵥ (F.G⁻¹ᵀ *ᵥ u) ≤ 3 * (R ^ 2 + 2) * (u ⬝ᵥ u) := by
  have e : F.Gᵀ *ᵥ (F.G⁻¹ᵀ *ᵥ u) = u := by
    rw [mulVec_mulVec, ← transpose_mul, nonsing_inv_mul _ hF.G_inv, transpose_one,
      one_mulVec]
  have h := hF.G_low (F.G⁻¹ᵀ *ᵥ u)
  rwa [e] at h

/-- `‖G⁻¹ u‖² ≤ 3 (R² + 2) ‖u‖²`. -/
theorem Ginv_mulVec_le (hF : F.Good w R Csep s t) (u : Fin d → ℝ) :
    (F.G⁻¹ *ᵥ u) ⬝ᵥ (F.G⁻¹ *ᵥ u) ≤ 3 * (R ^ 2 + 2) * (u ⬝ᵥ u) :=
  dotProduct_mulVec_le_of_transpose (three_R_sq_nonneg R) hF.GinvT_mulVec_le u

/-- `3 (R² + 2) ≤ n`. -/
theorem three_R_sq_le_n (hF : F.Good w R Csep s t) : 3 * (R ^ 2 + 2) ≤ n :=
  hF.params.three_R_sq_le_n

/-- `ζ_j = G⁻¹ z_j`. -/
theorem ζ_eq (hF : F.Good w R Csep s t) (j : Fin n) : F.ζ j = F.G⁻¹ *ᵥ F.zR j := by
  rw [hF.z_eq j, mulVec_mulVec, nonsing_inv_mul _ hF.G_inv, one_mulVec]

/-! #### (F-c) The data are bounded -/

/-- `‖ζ_j‖² ≤ 3 (R² + 2 n d + 4 / n²)`. -/
theorem ζ_sq_le (hF : F.Good w R Csep s t) (j : Fin n) :
    F.ζ j ⬝ᵥ F.ζ j ≤ 3 * (R ^ 2 + 2 * n * d + 4 / (n : ℝ) ^ 2) := by
  have h := dotProduct_add_add_le (F.m (F.ℓ j)) (F.g j) (F.e j)
  have h1 := hF.radius (F.ℓ j)
  have h2 := hF.g_sq_le j
  have h3 := hF.err j
  unfold ζ
  linarith

/-- `z_{ja}² ≤ 20 ‖ζ_j‖²`. -/
theorem z_sq_le (hF : F.Good w R Csep s t) (j : Fin n) (a : Fin d) :
    ((F.z j a : ℝ)) ^ 2 ≤ 20 * (F.ζ j ⬝ᵥ F.ζ j) := by
  have e : (F.z j a : ℝ) = F.G a ⬝ᵥ F.ζ j := by
    have := congrFun (hF.z_eq j) a
    simpa [zR, mulVec] using this
  have hrow : F.G a = F.Gᵀ *ᵥ Pi.single a 1 := by
    funext i
    rw [mulVec_single_one]
    rfl
  have hGa : F.G a ⬝ᵥ F.G a ≤ 20 := by
    have := hF.G_up (Pi.single a 1)
    rw [← hrow] at this
    simpa using this
  rw [e]
  calc (F.G a ⬝ᵥ F.ζ j) ^ 2 ≤ (F.G a ⬝ᵥ F.G a) * (F.ζ j ⬝ᵥ F.ζ j) := dotProduct_sq_le _ _
    _ ≤ 20 * (F.ζ j ⬝ᵥ F.ζ j) :=
        mul_le_mul_of_nonneg_right hGa (dotProduct_self_nonneg' _)

/-- **(F-c)** `|z_{ja}| ≤ n²`. -/
theorem abs_z_le (hF : F.Good w R Csep s t) (j : Fin n) (a : Fin d) :
    |(F.z j a : ℝ)| ≤ (n : ℝ) ^ 2 := by
  have h1 := hF.z_sq_le j a
  have h2 := hF.ζ_sq_le j
  have hn := hF.n_pos_real
  have hn20 : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hF.params.n_ge
  push_cast at hn20
  have hR : R ^ 2 ≤ n := by have := hF.three_R_sq_le_n; nlinarith [sq_nonneg R]
  have hd : (d : ℝ) ≤ n := by exact_mod_cast hF.params.d_lt_n.le
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h4 : 4 / (n : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hnd : 2 * (n : ℝ) * d ≤ 2 * n * n := by
    have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * n)
    linarith
  have h5 : ((F.z j a : ℝ)) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 := by
    have h6 : (F.z j a : ℝ) ^ 2 ≤ 60 * (n + 2 * n * n + 4) := by nlinarith
    have a1 : (n : ℝ) + 2 * n * n + 4 ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
    have a2 : (180 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have a3 : 180 * (n : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 := by
      rw [sq ((n : ℝ) ^ 2)]
      exact mul_le_mul_of_nonneg_right a2 (sq_nonneg _)
    linarith
  exact abs_le_of_sq_le_sq h5 (by positivity)

end Good

end SRFrame

end BS23.SmallRadius
