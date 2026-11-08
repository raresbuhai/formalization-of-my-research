module

public import BS23.Colinear.Gradient
public import BS23.Colinear.Population
public import BS23.Colinear.OneDimApply

/-!
# Correctness of the colinear-means algorithm

The deterministic part of the proof of [BS23, Theorem 1.2]: on a sample whose cluster sizes are
within `1 ± η` of the weights and whose noise has the Gaussian directional moments up to `η'`
(`BS23.UniformNoise`, degree `BS23.Colinear.Dcol wmin`), rounded within `1/n`, the colinear-means
algorithm (`BS23.Colinear.alg` with the parameters `BS23.Colinear.params wmin`) clusters the sample
with error `(wmin / k)^c`, as soon as the means are separated by `Csep c · log (1/wmin)` and
`η + η' + 1/n ≤ colTarget wmin d σ²` (`BS23.Colinear.alg_correct`).

The constants (`L = logInv wmin`, `M = 40 (L + 1)` the largest Hermite degree, `T = 10 (L + 1)`):

* `Dcol wmin = 2 M + 2 L + 8` (`BS23.Colinear.Dcol`): moments up to degree `2M` for the Hermite
  scores, and `2 L + 8` for the tails of the line clustering;
* `Csep c = 4 · 10⁸ · 4^c` (`BS23.Colinear.Csep`);
* `colTarget wmin d σ² = η₀ σ² / (2^(M+8) (M+1)^(M+1) (d+1)^M · K_M · Lip_M)`
  (`BS23.Colinear.colTarget`), with `η₀ = (wmin/2)^(2T) / (4 · 16^T)` (`BS23.Colinear.colEta0`),
  `K_M = momConst M wmin` the constant of the moment comparison and
  `Lip_M = fmLip M (2 (M+1) / wmin)` the Lipschitz constant of the Hermite score.

The chain of the proof (`k ≥ 2`; for `k = 1` the algorithm outputs zeros, which is exact):

1. (MOM, `BS23.Colinear.MomHyp.close`) the empirical moments about `μ̄` along every `v` are within
   `δ ‖v‖_cov^r` of the population moments, `δ = (η + η' + 1/n) K_M`;
2. (COV, `BS23.Colinear.MomHyp.cov_close`) hence `Ĉ` is within `1 ± 2δ` of `cov`;
3. (SCORE, `BS23.Colinear.MomHyp.phat_close`) and `|P̂_m(v) - h̃_m ⟨u₀, v⟩^m| ≤ δ Lip_M ‖v‖_cov^m`;
4. (MISMATCH, `BS23.Colinear.hpop_mismatch`) some `3 ≤ m ≤ M` has `|h̃_m| κ^{m/2} ≥ η₀`;
5. (GRAD) the selected gradient is `c u₀ + E` with `E` small (`exists_selectBest_gradPhat`), so
   (DIR) `a = Ĉ⁻¹ g` (`BS23.Colinear.selDir`) has a large Fisher ratio (`fisher_ratio`; together
   `BS23.Colinear.exists_good_direction`), so the projected means are separated
   (`BS23.Colinear.sep_along`, `BS23.Colinear.exists_gamma`);
6. (1D) the line clustering is correct (`oneDim_clustersWithin_params`), with the scale `aᵀĈa`
   (`BS23.Colinear.scale_bounds`).

The smallness conditions on `δ` all follow from `η + η' + 1/n ≤ colTarget wmin d σ²`
(`BS23.Colinear.target_numerics`, `BS23.Colinear.acc_facts`).
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset

variable {k d n : ℕ}

/-! ### The constants -/

/-- The largest Hermite degree of the algorithm is `40 (logInv wmin + 1)`. -/
theorem params_M (wmin : ℚ) : (params wmin).M = 40 * (logInv wmin + 1) := rfl

/-- The degree of the good event used by the colinear algorithm: `2 M + 2 logInv wmin + 8`, with
`M = (params wmin).M = 40 (logInv wmin + 1)` the largest Hermite degree. -/
def Dcol (wmin : ℚ) : ℕ := 2 * (params wmin).M + 2 * logInv wmin + 8

/-- The separation constant for the error exponent `c`: `4 · 10⁸ · 4^c`. -/
def Csep (c : ℕ) : ℕ := 4 * 10 ^ 8 * 4 ^ c

/-- The size of the population mismatch: `η₀ = (wmin/2)^(2T) / (4 · 16^T)`, `T = 10 (L + 1)`,
`L = logInv wmin`. -/
noncomputable def colEta0 (wmin : ℚ) : ℝ :=
  ((wmin : ℝ) / 2) ^ (2 * (10 * (logInv wmin + 1))) / (4 * 16 ^ (10 * (logInv wmin + 1)))

/-- The accuracy the colinear algorithm needs from the sample: `η + η' + 1/n` at most
`η₀ σ² / (2^(M+8) (M+1)^(M+1) (d+1)^M · momConst M wmin · fmLip M (2 (M+1) / wmin))`, with
`M = (params wmin).M` and `η₀ = colEta0 wmin`. -/
noncomputable def colTarget (wmin : ℚ) (d : ℕ) (σ2 : ℝ) : ℝ :=
  colEta0 wmin * σ2 /
    (2 ^ ((params wmin).M + 8) * (((params wmin).M : ℝ) + 1) ^ ((params wmin).M + 1) *
      ((d : ℝ) + 1) ^ (params wmin).M * momConst (params wmin).M (wmin : ℝ) *
      fmLip (params wmin).M (2 * (((params wmin).M : ℝ) + 1) / (wmin : ℝ)))

/-! ### Elementary bounds on the constants -/

theorem one_le_momConst {wmin : ℝ} (hwmin : 0 < wmin) (hw1 : wmin ≤ 1) (r : ℕ) :
    1 ≤ momConst r wmin := by
  unfold momConst
  rw [one_le_div (by positivity)]
  have h1 : wmin ^ (r + 1) ≤ 1 := pow_le_one₀ hwmin.le hw1
  have h2 : (1 : ℝ) ≤ (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith)
  linarith

theorem momConst_mono {wmin : ℝ} (hwmin : 0 < wmin) (hw1 : wmin ≤ 1) {r R : ℕ} (hrR : r ≤ R) :
    momConst r wmin ≤ momConst R wmin := by
  unfold momConst
  have hr : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) ≤ (4 * ((R : ℝ) + 1)) ^ (2 * (R + 1)) :=
    calc (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) ≤ (4 * ((r : ℝ) + 1)) ^ (2 * (R + 1)) :=
          pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ _ := by gcongr
  have h2 : wmin ^ (R + 1) ≤ wmin ^ (r + 1) := pow_le_pow_of_le_one hwmin.le hw1 (by omega)
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

theorem one_le_fmLip {wmin : ℝ} (hwmin : 0 < wmin) (hw1 : wmin ≤ 1) (m : ℕ) :
    1 ≤ fmLip m (2 * ((m : ℝ) + 1) / wmin) := by
  unfold fmLip
  have hK := one_le_popK hwmin hw1 m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine one_le_pow₀ ?_
  nlinarith

theorem fmLip_mono {wmin : ℝ} (hwmin : 0 < wmin) (hw1 : wmin ≤ 1) {m R : ℕ} (hmR : m ≤ R) :
    fmLip m (2 * ((m : ℝ) + 1) / wmin) ≤ fmLip R (2 * ((R : ℝ) + 1) / wmin) := by
  unfold fmLip
  have hK := one_le_popK hwmin hw1 m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmR' : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hb : 1 ≤ 6 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) / wmin) := by nlinarith
  calc (6 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) / wmin)) ^ (2 * (m + 1))
      ≤ (6 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) / wmin)) ^ (2 * (R + 1)) :=
        pow_le_pow_right₀ hb (by omega)
    _ ≤ _ := by gcongr

theorem colEta0_pos {wmin : ℚ} (hwmin : 0 < wmin) : 0 < colEta0 wmin := by
  have : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  unfold colEta0
  positivity

theorem colEta0_le {wmin : ℚ} (hwmin : 0 < wmin) (hw1 : (wmin : ℝ) ≤ 1) :
    colEta0 wmin ≤ (wmin : ℝ) / 8 := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  unfold colEta0
  have h1 : ((wmin : ℝ) / 2) ^ (2 * (10 * (logInv wmin + 1))) ≤ ((wmin : ℝ) / 2) ^ 1 :=
    pow_le_pow_of_le_one (by positivity) (by linarith) (by omega)
  have h2 : (4 : ℝ) ≤ 4 * 16 ^ (10 * (logInv wmin + 1)) := by
    have : (1 : ℝ) ≤ 16 ^ (10 * (logInv wmin + 1)) := one_le_pow₀ (by norm_num)
    linarith
  calc ((wmin : ℝ) / 2) ^ (2 * (10 * (logInv wmin + 1))) / (4 * 16 ^ (10 * (logInv wmin + 1)))
      ≤ ((wmin : ℝ) / 2) ^ 1 / 4 := div_le_div₀ (by positivity) h1 (by norm_num) h2
    _ = (wmin : ℝ) / 8 := by ring

/-- The accuracy target is positive. -/
theorem colTarget_pos {wmin : ℚ} (hwmin : 0 < wmin) (d : ℕ) {σ2 : ℝ} (hσ2 : 0 < σ2) :
    0 < colTarget wmin d σ2 := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have h1 := colEta0_pos hwmin
  unfold colTarget momConst fmLip
  positivity

/-- The arithmetic behind the choice of `colTarget`: abstractly, with `Q = 2^(M+8) (M+1)^(M+1)`,
`Dd = d^M ≤ Dd' = (d+1)^M`, `K` the moment constant and `Lp` the Lipschitz constant. -/
theorem target_numerics {w σ2 η₀ x K Lp Q Dd Dd' : ℝ} {Mdeg : ℕ} (hw1 : w ≤ 1)
    (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hη₀ : 0 < η₀) (hη₀w : η₀ ≤ w / 8) (hK : 1 ≤ K) (hLp : 1 ≤ Lp)
    (hQ8 : 8 ≤ Q) (hQM : 2 * (Mdeg : ℝ) ≤ Q) (hMdeg : 1 ≤ Mdeg) (hDd : 1 ≤ Dd) (hDD : Dd ≤ Dd')
    (hx0 : 0 ≤ x) (hx : x ≤ η₀ * σ2 / (Q * Dd' * K * Lp)) :
    x * K * Lp ≤ η₀ * Real.sqrt σ2 / (Q * Dd) ∧ 2 * (x * K) ≤ 1 / (4 * (Mdeg : ℝ)) ∧
      2 * (x * K) ≤ Real.sqrt σ2 / 16 ∧ x * K ≤ 1 / 8 ∧ x ≤ w / 2 ∧ x ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hD0 : 0 < Dd := by linarith
  have hD'0 : 0 < Dd' := by linarith
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < Lp := by linarith
  have h1 : x * (Q * Dd' * K * Lp) ≤ η₀ * σ2 := by
    rwa [le_div_iff₀ (by positivity)] at hx
  set y := x * K * Lp with hy
  have hy0 : 0 ≤ y := by positivity
  have hyQD : y * (Q * Dd') ≤ η₀ * σ2 := by rw [hy]; linarith
  have hσs : σ2 ≤ Real.sqrt σ2 := by
    rw [Real.le_sqrt hσ0.le hσ0.le]
    nlinarith
  have hηs : η₀ * σ2 ≤ η₀ * Real.sqrt σ2 := mul_le_mul_of_nonneg_left hσs hη₀.le
  have hyQ : y * Q ≤ y * (Q * Dd') :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hQ0.le (by linarith)) hy0
  have hη8 : η₀ ≤ 1 / 8 := by linarith
  have hησ : η₀ * σ2 ≤ 1 / 8 := by nlinarith
  have hyQ8 : y * Q ≤ 1 / 8 := by linarith
  have hxK : x * K ≤ y := by
    rw [hy]
    nlinarith [mul_nonneg hx0 hK0.le]
  have hxx : x ≤ x * K := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : y * (Q * Dd) ≤ y * (Q * Dd') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDD hQ0.le) hy0
    linarith
  · have hM : (1 : ℝ) ≤ Mdeg := by exact_mod_cast hMdeg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have hyσ : y * Q ≤ η₀ * Real.sqrt σ2 := by linarith
    have : η₀ * Real.sqrt σ2 ≤ Real.sqrt σ2 / 8 := by
      have := Real.sqrt_nonneg σ2
      nlinarith
    nlinarith
  · nlinarith
  · have : y * 8 ≤ y * Q := mul_le_mul_of_nonneg_left hQ8 hy0
    nlinarith
  · have : y * 8 ≤ y * Q := mul_le_mul_of_nonneg_left hQ8 hy0
    nlinarith

/-! ### The case of one component -/

/-- With one component, labelling every point `0` is exact. -/
theorem clustersWithin_one (hn : 0 < n) (ℓ : Fin n → Fin 1) {ε : ℝ} (hε : 0 ≤ ε) :
    ClustersWithin ε ℓ (List.ofFn fun _ : Fin n ↦ (0 : ℕ)) := by
  have h0 : ∀ j : Fin n, outCluster (List.ofFn fun _ : Fin n ↦ (0 : ℕ)) j = 0 := by
    intro j
    simp [outCluster, List.getD_eq_getElem?_getD, j.isLt]
  refine ⟨List.length_ofFn, fun j ↦ by rw [h0]; norm_num, 1, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcl : ∀ i : Fin 1, cluster ℓ i = Finset.univ := fun i ↦
    Finset.filter_true_of_mem fun j _ ↦ Subsingleton.elim _ _
  have hf : ∀ i : Fin 1, (Finset.univ.filter fun j : Fin n ↦
      outCluster (List.ofFn fun _ : Fin n ↦ (0 : ℕ)) j = i) = Finset.univ := fun i ↦
    Finset.filter_true_of_mem fun j _ ↦ by rw [h0, Subsingleton.elim i 0]; rfl
  simp only [hf, hcl, Finset.univ_inter, Finset.card_univ, Fintype.card_fin,
    Fin.sum_univ_one]
  rw [div_self hn', sub_self]
  exact hε

/-! ### The moment comparison -/

/-- The hypotheses of the moment comparison (`BS23.Colinear.moment_close_homog`), bundled: a valid
mixture with weights at least `wmin > 0`; `n > 0` labelled points with labels `ℓ` and noise `ν`,
rounded to `yt` within `1/n` in the geometry of `Σ`; cluster fractions within `1 ± η` of the
weights; and noise moments within `η'` of the Gaussian ones up to degree `D`. -/
structure MomHyp (M : Mixture k d) (wmin : ℝ) (ℓ : Fin n → Fin k) (ν yt : Fin n → Fin d → ℝ)
    (η η' : ℝ) (D : ℕ) : Prop where
  valid : M.Valid
  wmin_pos : 0 < wmin
  w_ge : ∀ c, wmin ≤ M.w c
  n_pos : 0 < n
  round : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2
  size : ∀ c, |((cluster ℓ c).card : ℝ) / n - M.w c| ≤ η * M.w c
  noise : UniformNoise M.S η' D ℓ ν

namespace MomHyp

variable {M : Mixture k d} {wmin : ℝ} {ℓ : Fin n → Fin k} {ν yt : Fin n → Fin d → ℝ}
  {η η' : ℝ} {D : ℕ}

theorem wmin_le_one (H : MomHyp M wmin ℓ ν yt η η' D) : wmin ≤ 1 :=
  Colinear.wmin_le_one H.valid H.wmin_pos H.w_ge

theorem k_pos (H : MomHyp M wmin ℓ ν yt η η' D) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · have := H.valid.sum_w
    simp at this
  · exact h

theorem eta_nonneg (H : MomHyp M wmin ℓ ν yt η η' D) : 0 ≤ η := by
  have h := (abs_nonneg _).trans (H.size ⟨0, H.k_pos⟩)
  have hw := H.wmin_pos.trans_le (H.w_ge ⟨0, H.k_pos⟩)
  rcases le_or_gt 0 η with h0 | h0
  · exact h0
  · nlinarith

theorem eta'_nonneg (H : MomHyp M wmin ℓ ν yt η η' D) : 0 ≤ η' := by
  have h := H.noise ⟨0, H.k_pos⟩ 0 (Nat.zero_le _) 0
  simp only [pow_zero, mul_one] at h
  exact (abs_nonneg _).trans h

theorem acc_nonneg (H : MomHyp M wmin ℓ ν yt η η' D) : 0 ≤ η + η' + 1 / n := by
  have := H.eta_nonneg
  have := H.eta'_nonneg
  positivity

theorem quad_cov_nonneg (H : MomHyp M wmin ℓ ν yt η η' D) (v : Fin d → ℝ) :
    0 ≤ quad M.cov v :=
  (quad_S_nonneg H.valid v).trans
    (quad_S_le_quad_cov M (fun c ↦ H.wmin_pos.le.trans (H.w_ge c)) v)

/-- **(MOM)** The empirical moments about `μ̄` along `v` are close to the population moments. -/
theorem close (H : MomHyp M wmin ℓ ν yt η η' D) (v : Fin d → ℝ) {r : ℕ} (hr : 2 * r ≤ D) :
    |rawMom yt M.mean v r - popMom M r v| ≤
      (η + η' + 1 / n) * momConst r wmin * Real.sqrt (quad M.cov v) ^ r :=
  moment_close_homog M H.valid H.wmin_pos H.w_ge H.n_pos ℓ ν yt H.round H.size H.noise v hr

/-- **(COV)** The empirical covariance is within `1 ± 2δ` of the covariance of the mixture. -/
theorem cov_close (H : MomHyp M wmin ℓ ν yt η η' D) (hD : 4 ≤ D) {δ : ℝ}
    (hδ1 : (η + η' + 1 / n) * momConst 1 wmin ≤ δ) (hδ2 : (η + η' + 1 / n) * momConst 2 wmin ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (v : Fin d → ℝ) :
    (1 - 2 * δ) * quad M.cov v ≤ quad (empCov yt) v ∧
      quad (empCov yt) v ≤ (1 + 2 * δ) * quad M.cov v := by
  have hq0 := H.quad_cov_nonneg v
  have hs2 : Real.sqrt (quad M.cov v) ^ 2 = quad M.cov v := Real.sq_sqrt hq0
  have h1 := H.close v (r := 1) (by omega)
  have h2 := H.close v (r := 2) (by omega)
  have hp1 : popMom M 1 v = 0 := popMom_one M H.valid v
  have hp2 : popMom M 2 v = quad M.cov v := popMom_two M H.valid v
  rw [hp1, sub_zero, pow_one] at h1
  rw [hp2, hs2] at h2
  have hC := quad_empCov_eq yt M.mean v H.n_pos
  have e1 : |rawMom yt M.mean v 1| ≤ δ * Real.sqrt (quad M.cov v) :=
    h1.trans (mul_le_mul_of_nonneg_right hδ1 (Real.sqrt_nonneg _))
  have e1sq : rawMom yt M.mean v 1 ^ 2 ≤ δ ^ 2 * quad M.cov v := by
    rw [← hs2, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) e1 2
  have e2 : |rawMom yt M.mean v 2 - quad M.cov v| ≤ δ * quad M.cov v :=
    h2.trans (mul_le_mul_of_nonneg_right hδ2 hq0)
  have hδδ : δ ^ 2 * quad M.cov v ≤ δ * quad M.cov v := by
    have : δ ^ 2 ≤ δ := by nlinarith
    exact mul_le_mul_of_nonneg_right this hq0
  rw [abs_le] at e2
  have := sq_nonneg (rawMom yt M.mean v 1)
  constructor <;> nlinarith

/-- **(SCORE)** on the unit ball of `cov`: the empirical Hermite score is close to the population
score `h̃_m ⟨u₀, v⟩^m`. -/
theorem phat_close_unit (H : MomHyp M wmin ℓ ν yt η η' D) {base u0 : Fin d → ℝ}
    {t : Fin k → ℝ} (hμ : ∀ c, M.μ c = base + t c • u0) {R m : ℕ} (hm : m ≤ R)
    (hRD : 2 * R ≤ D) {δ : ℝ} (hδ : ∀ r ≤ R, (η + η' + 1 / n) * momConst r wmin ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {v : Fin d → ℝ} (hv : quad M.cov v ≤ 1) :
    |phat m yt v - hpop M t m * (u0 ⬝ᵥ v) ^ m| ≤ δ * fmLip m (2 * ((m : ℝ) + 1) / wmin) := by
  rw [phat_eq_Fm yt M.mean v H.n_pos m, ← Fm_popMom_eq_hpop H.valid hμ m v]
  refine abs_Fm_sub_Fm_le (one_le_popK H.wmin_pos H.wmin_le_one m) hδ0 hδ1
    (rawMom_zero yt M.mean v H.n_pos) (popMom_zero M H.valid v)
    (fun r hr ↦ abs_popMom_le M H.valid H.wmin_pos H.w_ge hv hr) (fun r _ hr ↦ ?_)
  have hs : Real.sqrt (quad M.cov v) ^ r ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hv)
  calc |rawMom yt M.mean v r - popMom M r v|
      ≤ (η + η' + 1 / n) * momConst r wmin * Real.sqrt (quad M.cov v) ^ r :=
        H.close v (by omega)
    _ ≤ δ * 1 := mul_le_mul (hδ r (hr.trans hm)) hs (by positivity) hδ0
    _ = δ := mul_one δ

/-- **(SCORE)** The empirical Hermite score is close to the population score `h̃_m ⟨u₀, v⟩^m`:
`|P̂_m(v) - h̃_m ⟨u₀, v⟩^m| ≤ δ Lip_R ‖v‖_cov^m` for `1 ≤ m ≤ R`, `2R ≤ D`. -/
theorem phat_close (H : MomHyp M wmin ℓ ν yt η η' D) {base u0 : Fin d → ℝ} {t : Fin k → ℝ}
    (hμ : ∀ c, M.μ c = base + t c • u0) {R m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ R) (hRD : 2 * R ≤ D)
    {δ : ℝ} (hδ : ∀ r ≤ R, (η + η' + 1 / n) * momConst r wmin ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (v : Fin d → ℝ) :
    |phat m yt v - hpop M t m * (u0 ⬝ᵥ v) ^ m| ≤
      δ * fmLip R (2 * ((R : ℝ) + 1) / wmin) * Real.sqrt (quad M.cov v) ^ m := by
  have hLip : δ * fmLip m (2 * ((m : ℝ) + 1) / wmin) ≤ δ * fmLip R (2 * ((R : ℝ) + 1) / wmin) :=
    mul_le_mul_of_nonneg_left (fmLip_mono H.wmin_pos H.wmin_le_one hm) hδ0
  have hcov : M.cov.PosDef := cov_posDef M H.valid fun c ↦ H.wmin_pos.le.trans (H.w_ge c)
  by_cases hv : v = 0
  · subst hv
    have hm0 : m ≠ 0 := by omega
    have h0 : phat m yt (0 : Fin d → ℝ) = 0 := by
      have := phat_smul m yt (0 : ℝ) (0 : Fin d → ℝ)
      rwa [zero_smul, zero_pow hm0, zero_mul] at this
    rw [h0, dotProduct_zero, zero_pow hm0, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hδ0
      (zero_le_one.trans (one_le_fmLip H.wmin_pos H.wmin_le_one R))) (by positivity)
  · have hq : 0 < quad M.cov v := quad_pos hcov hv
    set s := Real.sqrt (quad M.cov v) with hs_def
    have hs : 0 < s := Real.sqrt_pos.mpr hq
    have hs2 : s ^ 2 = quad M.cov v := Real.sq_sqrt hq.le
    have hv' : quad M.cov (s⁻¹ • v) ≤ 1 := by
      rw [quad_smul, ← hs2, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    have key := H.phat_close_unit hμ hm hRD hδ hδ0 hδ1 hv'
    rw [phat_smul, dotProduct_smul, smul_eq_mul, mul_pow] at key
    have e : s ^ m * s⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
    have heq : phat m yt v - hpop M t m * (u0 ⬝ᵥ v) ^ m =
        s ^ m * (s⁻¹ ^ m * phat m yt v - hpop M t m * (s⁻¹ ^ m * (u0 ⬝ᵥ v) ^ m)) := by
      linear_combination (-(phat m yt v - hpop M t m * (u0 ⬝ᵥ v) ^ m)) * e
    rw [heq, abs_mul, abs_of_pos (pow_pos hs m)]
    calc _ ≤ s ^ m * (δ * fmLip m (2 * ((m : ℝ) + 1) / wmin)) :=
          mul_le_mul_of_nonneg_left key (pow_pos hs m).le
      _ ≤ s ^ m * (δ * fmLip R (2 * ((R : ℝ) + 1) / wmin)) :=
          mul_le_mul_of_nonneg_left hLip (pow_pos hs m).le
      _ = _ := by ring

end MomHyp

/-! ### The population mismatch, the separation and the cluster sizes -/

/-- `10 log (1 / wmin) ≤ 10 (logInv wmin + 1)`. -/
theorem ten_log_le {wmin : ℚ} (hwmin : 0 < wmin) :
    10 * Real.log (1 / (wmin : ℝ)) ≤ ((10 * (logInv wmin + 1) : ℕ) : ℝ) := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have h := OneDimApply.one_le_mul_two_pow_logInv hwmin
  have h1 : 1 / (wmin : ℝ) ≤ 2 ^ logInv wmin := by
    rw [div_le_iff₀ hw0]
    linarith
  have h2 : Real.log (1 / (wmin : ℝ)) ≤ logInv wmin * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have h3 := Real.log_two_lt_d9
  have hL : (0 : ℝ) ≤ logInv wmin := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- **(MISMATCH)** Some degree `3 ≤ m ≤ M` has `|h̃_m| κ^{m/2} ≥ η₀`. -/
theorem hpop_mismatch {M : Mixture k d} (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin)
    (hw : ∀ c, (wmin : ℝ) ≤ M.w c) {base u0 : Fin d → ℝ} {t : Fin k → ℝ}
    (hμ : ∀ c, M.μ c = base + t c • u0) (hk : 2 ≤ k) {C : ℝ} (hC : 3 ≤ C)
    (hsep : ∀ a b, a ≠ b → C * Real.log (1 / (wmin : ℝ)) ≤ sqNormIn M.S (M.μ a - M.μ b)) :
    ∃ m, 3 ≤ m ∧ m ≤ (params wmin).M ∧
      colEta0 wmin ≤ |hpop M t m| * Real.sqrt (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)) ^ m := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  obtain ⟨m, hm3, hm4, hmis⟩ := exists_hpop_mismatch (t := t) hM hw0 hw hμ hk hC hsep
    (T := 10 * (logInv wmin + 1)) (by omega) (ten_log_le hwmin)
  refine ⟨m, hm3, by rw [params_M]; omega, le_trans ?_ hmis⟩
  have hs := wmin_half_le_s2 (t := t) hM hw0 hw hμ hk hC hsep
  unfold colEta0
  gcongr

/-- **The separation along the direction**: if `a` has Fisher ratio at least `1/4`, the
projections of the means are `√X / 2 · √(aᵀΣa)` apart when the means are `X` apart in the
geometry of `Σ`. -/
theorem sep_along {M : Mixture k d} {base u0 : Fin d → ℝ} {t : Fin k → ℝ}
    (hμ : ∀ c, M.μ c = base + t c • u0) {a : Fin d → ℝ}
    (hfish : 1 / 4 * quad M.S a * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) ≤ (a ⬝ᵥ u0) ^ 2) (hSa : 0 ≤ quad M.S a)
    {X : ℝ} (hX : 0 ≤ X) (hsep : ∀ i j, i ≠ j → X ≤ sqNormIn M.S (M.μ i - M.μ j))
    {i j : Fin k} (hij : i ≠ j) :
    Real.sqrt X / 2 * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ (M.μ i - M.μ j)| := by
  have hdiff : M.μ i - M.μ j = (t i - t j) • u0 := by
    rw [hμ i, hμ j, sub_smul]
    abel
  have h1 := hsep i j hij
  rw [sqNormIn_sub_eq hμ i j] at h1
  rw [hdiff, dotProduct_smul, smul_eq_mul, ← sq_le_sq₀ (by positivity) (abs_nonneg _), sq_abs,
    mul_pow, div_pow, Real.sq_sqrt hX, Real.sq_sqrt hSa, mul_pow]
  have h3 : X * quad M.S a ≤ (t i - t j) ^ 2 * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) * quad M.S a :=
    mul_le_mul_of_nonneg_right h1 hSa
  have h4 : (t i - t j) ^ 2 * (1 / 4 * quad M.S a * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0))) ≤
      (t i - t j) ^ 2 * (a ⬝ᵥ u0) ^ 2 :=
    mul_le_mul_of_nonneg_left hfish (sq_nonneg _)
  nlinarith

/-- Cluster fractions within `1 ± η` of the weights, `η ≤ 1/2`, give clusters of at least
`wmin n / 2` points. -/
theorem size_ge {ℓ : Fin n → Fin k} {M : Mixture k d} {wmin η : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ i, wmin ≤ M.w i) (hn : 0 < n) (hη : η ≤ 1 / 2)
    (hsize : ∀ i, |((cluster ℓ i).card : ℝ) / n - M.w i| ≤ η * M.w i) (i : Fin k) :
    wmin / 2 * n ≤ (cluster ℓ i).card := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (abs_le.mp (hsize i)).1
  have hwi := hw i
  have hηw : η * M.w i ≤ 1 / 2 * M.w i := mul_le_mul_of_nonneg_right hη (by linarith)
  have h2 : wmin / 2 ≤ ((cluster ℓ i).card : ℝ) / n := by linarith
  rwa [le_div_iff₀ hn'] at h2

/-! ### The algorithm is correct -/

/-- `Csep c ≥ 3`. -/
theorem three_le_Csep (c : ℕ) : (3 : ℝ) ≤ Csep c := by
  have h4 : 1 ≤ 4 ^ c := Nat.one_le_pow _ _ (by norm_num)
  have : 3 ≤ Csep c :=
    calc 3 ≤ 4 * 10 ^ 8 * 1 := by norm_num
      _ ≤ 4 * 10 ^ 8 * 4 ^ c := Nat.mul_le_mul_left _ h4
  exact_mod_cast this

/-- `Q = 2^(M+8) (M+1)^(M+1)` is at least `8` and at least `2M`. -/
theorem Q_bounds (m : ℕ) :
    (8 : ℝ) ≤ 2 ^ (m + 8) * ((m : ℝ) + 1) ^ (m + 1) ∧
      2 * (m : ℝ) ≤ 2 ^ (m + 8) * ((m : ℝ) + 1) ^ (m + 1) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (256 : ℝ) ≤ 2 ^ (m + 8) := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (m + 8) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ (m + 1) := by
    calc (m : ℝ) + 1 = ((m : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((m : ℝ) + 1) ^ (m + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : 256 * ((m : ℝ) + 1) ≤ 2 ^ (m + 8) * ((m : ℝ) + 1) ^ (m + 1) :=
    mul_le_mul h1 h2 (by linarith) (by positivity)
  constructor <;> linarith

/-- The accuracy target gives the smallness conditions of the analysis, for
`δ = (η + η' + 1/n) · momConst M wmin`. -/
theorem acc_facts {M : Mixture k d} {wmin : ℚ} {ℓ : Fin n → Fin k} {ν yt : Fin n → Fin d → ℝ}
    {η η' : ℝ} {D : ℕ} (H : MomHyp M (wmin : ℝ) ℓ ν yt η η' D) (hd : 1 ≤ d) {σ2 : ℝ}
    (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hacc : η + η' + 1 / n ≤ colTarget wmin d σ2) :
    ∃ δ : ℝ, (∀ r ≤ (params wmin).M, (η + η' + 1 / n) * momConst r wmin ≤ δ) ∧ 0 ≤ δ ∧
      δ ≤ 1 / 8 ∧ 2 * δ ≤ 1 / (4 * ((params wmin).M : ℝ)) ∧ 2 * δ ≤ Real.sqrt σ2 / 16 ∧
      δ * fmLip (params wmin).M (2 * (((params wmin).M : ℝ) + 1) / wmin) ≤
        colEta0 wmin * Real.sqrt σ2 /
          (2 ^ ((params wmin).M + 8) * (((params wmin).M : ℝ) + 1) ^ ((params wmin).M + 1) *
            (d : ℝ) ^ (params wmin).M) ∧
      η ≤ 1 / 2 ∧ η' ≤ (wmin : ℝ) / 2 := by
  have hw0 : (0 : ℝ) < wmin := H.wmin_pos
  have hwmin : 0 < wmin := by exact_mod_cast hw0
  have hw1 : (wmin : ℝ) ≤ 1 := H.wmin_le_one
  have hx0 := H.acc_nonneg
  have hη0 := H.eta_nonneg
  have hη'0 := H.eta'_nonneg
  have hinv0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hMdeg1 : 1 ≤ (params wmin).M := by rw [params_M]; omega
  obtain ⟨hQ8, hQM⟩ := Q_bounds (params wmin).M
  have hDd : (1 : ℝ) ≤ (d : ℝ) ^ (params wmin).M := one_le_pow₀ (by exact_mod_cast hd)
  have hDD : (d : ℝ) ^ (params wmin).M ≤ ((d : ℝ) + 1) ^ (params wmin).M :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
  obtain ⟨N1, N2, N3, N4, N5, N6⟩ := target_numerics hw1 hσ0 hσ1 (colEta0_pos hwmin)
    (colEta0_le hwmin hw1) (one_le_momConst hw0 hw1 _) (one_le_fmLip hw0 hw1 _) hQ8 hQM hMdeg1
    hDd hDD hx0 hacc
  exact ⟨_, fun r hr ↦ mul_le_mul_of_nonneg_left (momConst_mono hw0 hw1 hr) hx0,
    mul_nonneg hx0 (zero_le_one.trans (one_le_momConst hw0 hw1 _)), N4, N2, N3, N1,
    by linarith, by linarith⟩

/-- The direction `a = Ĉ⁻¹ ∇P̂_m(λᵢ)` of the selected pair `p = (m, i)`. -/
noncomputable def selDir (Y : Fin n → Fin d → ℝ) (p : ℕ × Fin d) : Fin d → ℝ :=
  direction (empCov Y) (gradPhat p.1 Y (basisVec (empCov Y) p.2))

/-- **(GRAD) and (DIR)**: the algorithm selects a pair, and the direction it computes has
Fisher ratio at least `1/4`, with `σ²/4 · aᵀ cov a ≤ aᵀΣa ≤ aᵀ cov a` and `aᵀΣa > 0`. -/
theorem exists_good_direction (c : ℕ) {M : Mixture k d} {wmin : ℚ} {ℓ : Fin n → Fin k}
    {ν yt : Fin n → Fin d → ℝ} {η η' : ℝ} (H : MomHyp M (wmin : ℝ) ℓ ν yt η η' (Dcol wmin))
    (hk : 2 ≤ k)
    (hsep : ∀ a b, a ≠ b → (Csep c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0)
    (hd : 1 ≤ d) (hσ0 : 0 < M.sigmaSq u0) {δ : ℝ}
    (hδr : ∀ r ≤ (params wmin).M, (η + η' + 1 / n) * momConst r wmin ≤ δ) (hδ0 : 0 ≤ δ)
    (hδ8 : δ ≤ 1 / 8) (hδM : 2 * δ ≤ 1 / (4 * ((params wmin).M : ℝ)))
    (hδσ : 2 * δ ≤ Real.sqrt (M.sigmaSq u0) / 16)
    (hδP : δ * fmLip (params wmin).M (2 * (((params wmin).M : ℝ) + 1) / wmin) ≤
        colEta0 wmin * Real.sqrt (M.sigmaSq u0) /
          (2 ^ ((params wmin).M + 8) * (((params wmin).M : ℝ) + 1) ^ ((params wmin).M + 1) *
            (d : ℝ) ^ (params wmin).M)) :
    ∃ p, selectBest (params wmin).M yt = some p ∧
      1 / 4 * quad M.S (selDir yt p) * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) ≤ (selDir yt p ⬝ᵥ u0) ^ 2 ∧
      M.sigmaSq u0 / 4 * quad M.cov (selDir yt p) ≤ quad M.S (selDir yt p) ∧
      0 < quad M.S (selDir yt p) ∧ quad M.S (selDir yt p) ≤ quad M.cov (selDir yt p) := by
  have hw0 : (0 : ℝ) < wmin := H.wmin_pos
  have hwmin : 0 < wmin := by exact_mod_cast hw0
  have hwpos : ∀ i, 0 ≤ M.w i := fun i ↦ hw0.le.trans (H.w_ge i)
  have hcov_eq := cov_eq H.valid hμ
  have hτ : 0 ≤ tau2 M t := tau2_nonneg hwpos
  have hcov : M.cov.PosDef := cov_posDef M H.valid hwpos
  have hσ1 : M.sigmaSq u0 ≤ 1 := (colinear_sigmaSq H.valid.posDef hcov hu0 hτ hcov_eq).2.2
  have hM3 : 3 ≤ (params wmin).M := by rw [params_M]; omega
  have hDcol : 2 * (params wmin).M ≤ Dcol wmin := by unfold Dcol; omega
  have HC := H.cov_close (by omega) (hδr 1 (by omega)) (hδr 2 (by omega)) hδ0 (by linarith)
  have HP : ∀ m, 3 ≤ m → m ≤ (params wmin).M → ∀ v,
      |phat m yt v - hpop M t m * (u0 ⬝ᵥ v) ^ m| ≤
        δ * fmLip (params wmin).M (2 * (((params wmin).M : ℝ) + 1) / wmin) *
          Real.sqrt (quad M.cov v) ^ m :=
    fun m hm3 hm v ↦ H.phat_close hμ (by omega) hm hDcol hδr hδ0 (by linarith) v
  have HM := hpop_mismatch H.valid hwmin H.w_ge hμ hk (three_le_Csep c) hsep
  obtain ⟨p, hp, cc, E, hc, hg, hE⟩ := exists_selectBest_gradPhat hd hM3 yt hcov hu0 (hpop M t)
    (by positivity) hδM (Real.sqrt_pos.mpr hσ0) (Real.sqrt_le_one.mpr hσ1) (colEta0_pos hwmin)
    HC HP HM hδP
  have hCpd : (empCov yt).PosDef := empCov_posDef_of_le yt hcov (by linarith) fun v ↦ (HC v).1
  have ha : selDir yt p = (empCov yt)⁻¹ *ᵥ (cc • u0 + E) := by
    rw [selDir, direction_eq hCpd, hg]
  exact ⟨p, hp, fisher_ratio H.valid.posDef hCpd hu0 hτ hcov_eq (σ2 := M.sigmaSq u0) rfl
    (by linarith) hδσ (by linarith) (fun v ↦ (HC v).1) (fun v ↦ (HC v).2) hc hE ha⟩

/-- **The scale** `V = aᵀĈa` is comparable to `aᵀΣa`: `aᵀΣa ≤ 2V ≤ 2 aᵀΣa · n²`. -/
theorem scale_bounds {qS qcov qC δ σ2 n : ℝ} (hq0 : 0 ≤ qcov) (hS0 : 0 ≤ qS) (hδ : δ ≤ 1 / 8)
    (hlow : (1 - 2 * δ) * qcov ≤ qC) (hup : qC ≤ (1 + 2 * δ) * qcov)
    (hF2 : σ2 / 4 * qcov ≤ qS) (hF4 : qS ≤ qcov) (hσn : 1 ≤ n * σ2) (hn : 8 ≤ n) :
    qS ≤ 2 * qC ∧ qC ≤ qS * n ^ 2 := by
  have h2 : δ * qcov ≤ 1 / 8 * qcov := mul_le_mul_of_nonneg_right hδ hq0
  have e1 : qcov ≤ (n * σ2) * qcov := le_mul_of_one_le_left hq0 hσn
  have e2 : n * (σ2 / 4 * qcov) ≤ n * qS := mul_le_mul_of_nonneg_left hF2 (by linarith)
  have e3 : 8 * n * qS ≤ n ^ 2 * qS := mul_le_mul_of_nonneg_right (by nlinarith) hS0
  have e4 : 0 ≤ n * qS := mul_nonneg (by linarith) hS0
  constructor <;> linarith

/-- **The separation along the direction**, in the form of the line clustering: for
`Γ = √(Csep c · log (1/wmin)) / 2`, `Γ² ≥ 10⁸ · 4^c · log (1/wmin)` and the projections of the
means are `Γ √(aᵀΣa)` apart. -/
theorem exists_gamma (c : ℕ) {M : Mixture k d} (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin)
    (hw : ∀ i, (wmin : ℝ) ≤ M.w i) (hk : 2 ≤ k)
    (hsep : ∀ a b, a ≠ b → (Csep c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0) {a : Fin d → ℝ}
    (hfish : 1 / 4 * quad M.S a * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) ≤ (a ⬝ᵥ u0) ^ 2)
    (hSa : 0 ≤ quad M.S a) :
    ∃ Γ : ℝ, 0 < Γ ∧ 10 ^ 8 * 4 ^ c * Real.log (1 / (wmin : ℝ)) ≤ Γ ^ 2 ∧
      ∀ i j, i ≠ j → Γ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ (M.μ i - M.μ j)| := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hw2 : 2 * (wmin : ℝ) ≤ 1 := two_mul_wmin_le_one hM hw0 hw hk
  have hlog : 0 < Real.log (1 / (wmin : ℝ)) :=
    Real.log_pos (by rw [one_lt_div hw0]; linarith)
  have hX : 0 < (Csep c : ℝ) * Real.log (1 / wmin) :=
    mul_pos (by linarith [three_le_Csep c]) hlog
  refine ⟨Real.sqrt ((Csep c : ℝ) * Real.log (1 / wmin)) / 2,
    by have := Real.sqrt_pos.mpr hX; positivity, ?_,
    fun i j hij ↦ sep_along hμ hfish hSa hX.le hsep hij⟩
  rw [div_pow, Real.sq_sqrt hX.le]
  simp only [Csep]
  push_cast
  linarith

/-- The algorithm with `k ≥ 2` components runs the line clustering along the selected direction
`BS23.Colinear.selDir`. -/
theorem alg_eq_of_selectBest {P : Params ℝ} (hk : 2 ≤ k) {Y : Fin n → Fin d → ℝ} {p : ℕ × Fin d}
    (hp : selectBest P.M Y = some p) :
    alg P k Y = OneDim.cluster k P.θ P.ε (topScale P.A (quad (empCov Y) (selDir Y p)))
      (Nat.clog 2 n + 8) (fun j ↦ selDir Y p ⬝ᵥ Y j) := by
  unfold alg
  split_ifs with h
  · exact absurd h (by omega)
  · rw [hp]
    rfl

/-- **Correctness for `k ≥ 2`**, with the positions `t` of the means on the line given. -/
theorem alg_correct_of_two_le (c : ℕ) {k d n : ℕ} (hk : 2 ≤ k) (M : Mixture k d)
    (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    (hsep : ∀ a b, a ≠ b → (Csep c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0)
    (hn : 8 ≤ n) (hσn : 1 / M.sigmaSq u0 ≤ n) {ℓ : Fin n → Fin k} {ν yt : Fin n → Fin d → ℝ}
    (hround : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2) {η η' : ℝ}
    (hsize : ∀ i, |((cluster ℓ i).card : ℝ) / n - M.w i| ≤ η * M.w i)
    (hU : UniformNoise M.S η' (Dcol wmin) ℓ ν)
    (hacc : η + η' + 1 / n ≤ colTarget wmin d (M.sigmaSq u0)) :
    ClustersWithin ((wmin / k : ℝ) ^ c) ℓ (List.ofFn (alg (params wmin).cast k yt)) := by
  have H : MomHyp M (wmin : ℝ) ℓ ν yt η η' (Dcol wmin) :=
    ⟨hM, by exact_mod_cast hwmin, hw, by omega, hround, hsize, hU⟩
  have hwpos : ∀ i, 0 ≤ M.w i := fun i ↦ H.wmin_pos.le.trans (hw i)
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd (Subsingleton.elim u0 0) hu0
    · exact h
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  -- `σ²`
  have hcov_eq := cov_eq hM hμ
  have hτ : 0 ≤ tau2 M t := tau2_nonneg hwpos
  have hcov : M.cov.PosDef := cov_posDef M hM hwpos
  have hσ0 : 0 < M.sigmaSq u0 := (colinear_sigmaSq hM.posDef hcov hu0 hτ hcov_eq).2.1
  have hσ1 : M.sigmaSq u0 ≤ 1 := (colinear_sigmaSq hM.posDef hcov hu0 hτ hcov_eq).2.2
  have hσn' : 1 ≤ n * M.sigmaSq u0 := (div_le_iff₀ hσ0).mp hσn
  -- the direction
  obtain ⟨δ, hδr, hδ0, hδ8, hδM, hδσ, hδP, hη, hη'⟩ := acc_facts H hd hσ0 hσ1 hacc
  obtain ⟨p, hp, hF1, hF2, hF3, hF4⟩ :=
    exists_good_direction c H hk hsep hu0 hμ hd hσ0 hδr hδ0 hδ8 hδM hδσ hδP
  have hM3 : 3 ≤ (params wmin).M := by rw [params_M]; omega
  have hDcol : 2 * (params wmin).M ≤ Dcol wmin := by unfold Dcol; omega
  have HC := H.cov_close (by omega) (hδr 1 (by omega)) (hδr 2 (by omega)) hδ0 (by linarith)
    (selDir yt p)
  -- the scale and the separation
  obtain ⟨hV1, hV2⟩ := scale_bounds (H.quad_cov_nonneg _) hF3.le hδ8 HC.1 HC.2 hF2 hF4 hσn' hn8
  obtain ⟨Γ, hΓ, hΓc, hsep'⟩ := exists_gamma c hM hwmin hw hk hsep hμ hF1 hF3.le
  -- (1D)
  have hsz := size_ge H.wmin_pos hw (by omega) hη hsize
  have hD : 2 * logInv wmin + 8 ≤ Dcol wmin := by unfold Dcol; omega
  have key := oneDim_clustersWithin_params hk (by omega) hM hwmin hw hround hsz hU hη' hD hF3 hΓ
    hsep' hΓc hV1 hV2
  rwa [alg_eq_of_selectBest hk (P := (params wmin).cast) hp]

/-- **Correctness of the colinear-means algorithm** [BS23, Theorem 1.2], deterministic part. Let
`M` be a valid mixture with weights at least `wmin > 0`, means on the line `base + ℝ u₀`
(`u₀ ≠ 0`) pairwise separated by `Csep c · log (1/wmin)` in the geometry of `Σ`. Take `n ≥ 8`
labelled points with labels `ℓ` and noise `ν`, rounded to `yt` within `1/n`, whose cluster
fractions are within `1 ± η` of the weights and whose noise has the Gaussian directional moments
up to `η'` up to degree `Dcol wmin`. If `1/σ² ≤ n` and `η + η' + 1/n ≤ colTarget wmin d σ²`
(`σ² = M.sigmaSq u0`), the algorithm with the parameters `params wmin` clusters the points with
error `(wmin / k)^c`. -/
theorem alg_correct (c : ℕ) {k d n : ℕ} (M : Mixture k d) (hM : M.Valid) {wmin : ℚ}
    (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    (hsep : ∀ a b, a ≠ b → (Csep c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) (hcol : ∀ i, ∃ t : ℝ, M.μ i = base + t • u0)
    (hn : 8 ≤ n) (hσn : 1 / M.sigmaSq u0 ≤ n) (ℓ : Fin n → Fin k) (ν yt : Fin n → Fin d → ℝ)
    (hround : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2) {η η' : ℝ}
    (hsize : ∀ i, |(cluster ℓ i).card / n - M.w i| ≤ η * M.w i)
    (hU : UniformNoise M.S η' (Dcol wmin) ℓ ν)
    (hacc : η + η' + 1 / n ≤ colTarget wmin d (M.sigmaSq u0)) :
    ClustersWithin ((wmin / k : ℝ) ^ c) ℓ (List.ofFn (alg (params wmin).cast k yt)) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by
      rcases k with _ | _ | k
      · have := hM.sum_w
        simp at this
      · rfl
      · omega
    have h0 : alg (params wmin).cast 1 yt = fun _ ↦ 0 := by
      unfold alg
      split_ifs with h
      · rfl
      · exact absurd le_rfl h
    rw [h0]
    exact clustersWithin_one (by omega) ℓ
      (pow_nonneg (div_nonneg (by exact_mod_cast hwmin.le) (Nat.cast_nonneg _)) _)
  · exact alg_correct_of_two_le c hk M hM hwmin hw hsep hu0
      (t := fun i ↦ Classical.choose (hcol i)) (fun i ↦ Classical.choose_spec (hcol i)) hn hσn
      hround hsize hU hacc

end BS23.Colinear
