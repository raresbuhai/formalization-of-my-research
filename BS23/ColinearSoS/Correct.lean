module

public import BS23.ColinearSoS.Alg
public import BS23.ColinearSoS.PseudoAnalysis
public import BS23.ColinearSoS.MomentPoly
public import BS23.Colinear.Main

/-!
# Correctness of the sum-of-squares algorithm for colinear means

The deterministic part of the proof of [BS23, Theorem 1.2] along the paper's sum-of-squares route:
on a sample in the good event `BS23.GoodNoise` of degree `D = BS23.ColinearSoS.DcolS wmin` and
accuracy `η`, rounded within `1/n`, the algorithm `BS23.ColinearSoS.colLabels` with the budget
`(d + 5)^(2t + 1)` clusters the sample with error `(wmin / k)^c`, as soon as the means are
separated by `CsepS c · log (1/wmin)` in the geometry of `Σ` and
`η + η (d + 1)^D + 1/n ≤ colSoSTarget wmin d σ²` (`BS23.ColinearSoS.colLabels_correct`).

The constants (`L = logInv wmin`, `s = L + 1`, `t = 256 s`):

* `DcolS wmin = 2t + 2L + 8` (`BS23.ColinearSoS.DcolS`): moments up to degree `2t` for the
  finite-sample transfer of program L, and `2L + 8` for the line clustering;
* `CsepS c = 4 · 10⁸ · 4^c` (`BS23.ColinearSoS.CsepS`, the constant of `BS23.Colinear.alg`);
* `colSoSTarget wmin d σ² = σ² / Q^(5t + 3)` (`BS23.ColinearSoS.colSoSTarget`), with
  `Q = mpBase d t wmin = 10⁶ (d + 1)⁶ (t + 1) / wmin` the base of the finite-sample error.

The chain of the proof (`k ≥ 2`; for `k = 1` all labels are `0`, which is exact):

1. (COV) On the good event `Ĉ` is within `1 ± 2δ` of `cov`, `δ = (η + η (d + 1)^D + 1/n) K₂`
   (`BS23.Colinear.MomHyp.cov_close`). So in the whitened frame `W = W Ĉ` the empirical variance
   `vᵀ diag(κ) v` is within `1 ± 2δ` of `vᵀ cov_W v` (`BS23.ColinearSoS.Cor.cmp_frame`), and the
   empirical moment polynomials are close to the population ones
   (`BS23.ColinearSoS.coeffNorm1_empPoly_sub_popPoly_le`).
2. (SoS) The pseudo-expectations behind both programs satisfy the hypotheses of the
   pseudo-expectation analysis (`BS23.ColinearSoS.Cor.pseudoHyp`). In case U
   (`OPT_U ≥ (5s)^s`) the moment along the line is at least `(4s)^s` and the defect
   `Ẽ[vᵀGv]` is small (`BS23.ColinearSoS.PseudoHyp.defect_le_of_max`). In case L the moment is at
   most `3 (5s)^s`, so all positions have `a_c² ≤ 20 s`
   (`BS23.ColinearSoS.Cor.sq_le_of_lineMom_le`), the separation forces `σ² ≤ 1/16`
   (`BS23.ColinearSoS.Cor.sigmaSq_le_of_sq_le`), and the defect of program L is small
   (`BS23.ColinearSoS.PseudoHyp.defect_le_of_min`, with `t ≥ 5 · 20 s + 8`).
3. (DIR) The column `â` of `Ẽ[vvᵀ]` at a maximal diagonal entry has `âᵀGâ ≤ 3 σ² ⟨ŭ, â⟩²`
   and `⟨ŭ, â⟩ ≠ 0` (`BS23.ColinearSoS.Cor.good_column`; both cases together:
   `BS23.ColinearSoS.Cor.exists_good_dir`), so `a = Wᵀ â` has Fisher ratio at least `1/4`
   (`BS23.ColinearSoS.fisher_ratio_of_perp_le`).
4. (1D) The line clustering along `a` is correct, as in `BS23.Colinear.alg_correct_of_two_le`
   (`BS23.Colinear.scale_bounds`, `BS23.Colinear.exists_gamma`,
   `BS23.Colinear.oneDim_clustersWithin_params`).

The smallness conditions follow from the accuracy hypothesis: with
`x = η + η (d + 1)^D + 1/n ≤ σ² / Q^(5t+3)` and the solver accuracies at most `2^-n ≤ 1/n`,
each of `m δc`, `γ`, `e 258^m` and `d² errQ` is at most `σ² / (3 · 10⁵ d)`, for both `m = s` and
`m = t`, hence `errD ≤ min (1/(10⁴ d), 3σ²/8)` (`BS23.ColinearSoS.Cor.errD_le`,
`BS23.ColinearSoS.Cor.small_m`); and `n σ² ≥ Q^(5t+3)` gives `n ≥ 8`, `n ≥ d` and `n σ² ≥ 1`
(`BS23.ColinearSoS.Cor.small_global`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open MvPolynomial Matrix Finset SoS Colinear PAn
open Separating (whiten kappa acc)

variable {k d n : ℕ}

/-! ### The constants -/

/-- The separation constant for the error exponent `c`: `Csep c = 4 · 10⁸ · 4^c`, the constant
of `BS23.Colinear.alg`. -/
def CsepS (c : ℕ) : ℕ := Csep c

/-- The degree of the good event: `2 t + 2 logInv wmin + 8`, with `t = tCol wmin` the degree of
program L (the finite-sample transfer needs degree `2t`, the line clustering
`2 logInv wmin + 8`). -/
def DcolS (wmin : ℚ) : ℕ := 2 * tCol wmin + 2 * logInv wmin + 8

/-- The accuracy the algorithm needs from the sample: `η + η (d + 1)^D + 1/n` at most
`σ² / Q^(5t + 3)`, with `t = tCol wmin` and `Q = mpBase d t wmin = 10⁶ (d + 1)⁶ (t + 1) / wmin`
the base of the finite-sample error. -/
noncomputable def colSoSTarget (wmin : ℚ) (d : ℕ) (σ2 : ℝ) : ℝ :=
  σ2 / mpBase d (tCol wmin) wmin ^ (5 * tCol wmin + 3)

/-- The accuracy target is positive. -/
theorem colSoSTarget_pos {wmin : ℚ} (hwmin : 0 < wmin) (d : ℕ) {σ2 : ℝ} (hσ2 : 0 < σ2) :
    0 < colSoSTarget wmin d σ2 := by
  have : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have := mpBase_pos (d := d) (m := tCol wmin) this
  unfold colSoSTarget
  positivity

namespace Cor

/-! ### Numerics -/

/-- `momConst 2 w = (144 / w)^3`. -/
theorem momConst_two (w : ℝ) : momConst 2 w = (144 / w) ^ 3 := by
  unfold momConst
  rw [div_pow]
  norm_num

/-- `10⁶ (d + 1)⁶ (t + 1) ≤ Q` for `w ≤ 1`. -/
theorem mpBase_ge {d t : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) :
    10 ^ 6 * ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) ≤ mpBase d t w := by
  unfold mpBase
  rw [le_div_iff₀ hw0]
  have : 0 ≤ 10 ^ 6 * ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) := by positivity
  nlinarith

/-- `Q` is monotone in the degree. -/
theorem mpBase_mono {d m t : ℕ} {w : ℝ} (hw0 : 0 < w) (hmt : m ≤ t) :
    mpBase d m w ≤ mpBase d t w := by
  unfold mpBase
  have : (m : ℝ) ≤ t := by exact_mod_cast hmt
  gcongr

/-- The lower bounds on `Q = mpBase d t w` used by the numerics. -/
theorem Q_facts {d t : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) :
    6 * 10 ^ 5 * (d : ℝ) ^ 3 * t ≤ mpBase d t w ∧ 6 * 10 ^ 5 * (d : ℝ) / w ≤ mpBase d t w ∧
      144 / w ≤ mpBase d t w ∧ 2 * (d : ℝ) + 1 ≤ mpBase d t w ∧ 258 ≤ mpBase d t w := by
  have ha : (1 : ℝ) ≤ (d : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hb : (1 : ℝ) ≤ (t : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) t; linarith
  have h6 : (d : ℝ) + 1 ≤ ((d : ℝ) + 1) ^ 6 := le_self_pow₀ ha (by norm_num)
  have h3 : (d : ℝ) ^ 3 ≤ ((d : ℝ) + 1) ^ 6 :=
    calc (d : ℝ) ^ 3 ≤ ((d : ℝ) + 1) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) 3
      _ ≤ ((d : ℝ) + 1) ^ 6 := pow_le_pow_right₀ ha (by norm_num)
  have hP := mpBase_ge (d := d) (t := t) hw0 hw1
  have hP' : 10 ^ 6 * ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) / w = mpBase d t w := rfl
  have hA : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (d : ℝ) ^ 3 * t ≤ ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) :=
      mul_le_mul h3 (by linarith) (Nat.cast_nonneg t) (by positivity)
    nlinarith
  · rw [← hP']
    refine div_le_div_of_nonneg_right ?_ hw0.le
    have : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1) := by nlinarith
    nlinarith
  · rw [← hP']
    refine div_le_div_of_nonneg_right ?_ hw0.le
    nlinarith
  · have : 2 * (d : ℝ) + 1 ≤ 2 * (((d : ℝ) + 1) ^ 6 * ((t : ℝ) + 1)) := by nlinarith
    nlinarith
  · nlinarith

/-- **The defect bound, abstractly**: if `m δc`, `γ`, `e 258^m` and `d² errQ` are at most
`y ≤ 1/32`, then `errN ≤ 4y` and `errD ≤ 28y`. -/
theorem errD_le {η₀ δc e γ y : ℝ} {m d : ℕ} (hd : 1 ≤ d) (hη₀ : 0 ≤ η₀) (hδc : 0 ≤ δc)
    (he : 0 ≤ e) (hγ : 0 ≤ γ) (h1 : m * δc ≤ y) (h2 : γ ≤ y) (h3 : e * 258 ^ m ≤ y)
    (h4 : (d : ℝ) ^ 2 * errQ η₀ m d ≤ y) (hy : y ≤ 1 / 32) :
    errN η₀ δc m d ≤ 4 * y ∧ errD η₀ δc e γ m d ≤ 28 * y := by
  have hQ0 : 0 ≤ errQ η₀ m d := by unfold errQ; positivity
  have hd' : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hd)
  have hQy : errQ η₀ m d ≤ y := le_trans (le_mul_of_one_le_left hQ0 hd') h4
  have hmδ : 0 ≤ (m : ℝ) * δc := by positivity
  have hN : errN η₀ δc m d ≤ 4 * y := by unfold errN; linarith
  have hN0 : 0 ≤ errN η₀ δc m d := by unfold errN; positivity
  refine ⟨hN, ?_⟩
  have he0 : 0 ≤ e * 258 ^ m := by positivity
  have hA : 2 * m * δc + γ + 2 * e * 258 ^ m + errN η₀ δc m d ≤ 9 * y := by linarith
  have hA0 : 0 ≤ 2 * m * δc + γ + 2 * e * 258 ^ m + errN η₀ δc m d := by linarith
  have hP : (1 + errN η₀ δc m d) * (2 * m * δc + γ + 2 * e * 258 ^ m + errN η₀ δc m d) ≤
      9 / 8 * (9 * y) := mul_le_mul (by linarith) hA hA0 (by norm_num)
  have hP2 : (m : ℝ) * δc * (1 + errN η₀ δc m d) ≤ y * (9 / 8) :=
    mul_le_mul h1 (by linarith) (by linarith) (by linarith)
  unfold errD errY
  linarith

/-- `c x ≤ σ² / z` from `x ≤ σ² / F` and `c z ≤ F`. -/
theorem mul_le_of_le_div {c x σ2 F z : ℝ} (hF : 0 < F) (hz : 0 < z) (hσ : 0 ≤ σ2)
    (hc : 0 ≤ c) (hx : x ≤ σ2 / F) (hcF : c * z ≤ F) : c * x ≤ σ2 / z := by
  calc c * x ≤ c * (σ2 / F) := mul_le_mul_of_nonneg_left hx hc
    _ ≤ σ2 / z := by
      rw [mul_div_assoc', div_le_div_iff₀ hF hz]
      nlinarith [mul_le_mul_of_nonneg_left hcF hσ]

/-- The global smallness conditions: from `x = η + η' + 1/n ≤ σ² / Q^(5t+3)`,
`x · momConst 2 w ≤ 1/8`, `η ≤ 1/2`, `η' ≤ w/2`, `2η ≤ w`, `n ≥ d`, `n ≥ 8` and `n σ² ≥ 1`. -/
theorem small_global {w σ2 η η' : ℝ} {d t n : ℕ} (hw0 : 0 < w) (hw1 : w ≤ 1) (ht : 1 ≤ t)
    (hn : 0 < n) (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hη : 0 ≤ η) (hη' : 0 ≤ η')
    (hx : η + η' + 1 / n ≤ σ2 / mpBase d t w ^ (5 * t + 3)) :
    (η + η' + 1 / n) * momConst 2 w ≤ 1 / 8 ∧ η ≤ 1 / 2 ∧ η' ≤ w / 2 ∧ 2 * η ≤ w ∧
      (d : ℝ) ≤ n ∧ (8 : ℝ) ≤ n ∧ 1 ≤ n * σ2 := by
  obtain ⟨-, -, hQ144, hQd, hQ258⟩ := Q_facts (d := d) (t := t) hw0 hw1
  set Q := mpBase d t w
  have hQ1 : 1 ≤ Q := by linarith
  have hF4 : Q ^ 4 ≤ Q ^ (5 * t + 3) := pow_le_pow_right₀ hQ1 (by omega)
  have hFQ : Q ≤ Q ^ (5 * t + 3) := le_self_pow₀ hQ1 (by omega)
  have hF0 : 0 < Q ^ (5 * t + 3) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
  have hK : momConst 2 w ≤ Q ^ 3 := by
    rw [momConst_two]
    exact pow_le_pow_left₀ (by positivity) hQ144 3
  have hK0 : 0 ≤ momConst 2 w := by rw [momConst_two]; positivity
  have h1 : momConst 2 w * (η + η' + 1 / n) ≤ σ2 / 8 := by
    refine mul_le_of_le_div hF0 (by norm_num) hσ0.le hK0 hx ?_
    calc momConst 2 w * 8 ≤ Q ^ 3 * Q := mul_le_mul hK (by linarith) (by norm_num) (by positivity)
      _ = Q ^ 4 := by ring
      _ ≤ _ := hF4
  have h2 : 1 * (η + η' + 1 / n) ≤ σ2 / (2 / w) := by
    refine mul_le_of_le_div hF0 (by positivity) hσ0.le zero_le_one hx ?_
    have : 2 / w ≤ 144 / w := div_le_div_of_nonneg_right (by norm_num) hw0.le
    linarith
  rw [one_mul, div_div_eq_mul_div] at h2
  have h2' : σ2 * w / 2 ≤ w / 2 := by nlinarith
  have h3 : Q ^ (5 * t + 3) ≤ σ2 * n := by
    have h := (le_add_of_nonneg_left (add_nonneg hη hη')).trans hx
    rwa [div_le_div_iff₀ hn' hF0, one_mul] at h
  have h4 : σ2 * n ≤ n := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The finite-sample error at degree `2m ≤ 2t`, times `258^m`, is at most
`(2/w) Q^(5t+2) x` when `η + 1/n ≤ x`. -/
theorem errMP_mul_le {w η x : ℝ} {d m t n : ℕ} (hw0 : 0 < w) (hw1 : w ≤ 1) (hmt : m ≤ t)
    (hη : 0 ≤ η) (hηx : η + 1 / n ≤ x) :
    errMP d m w η n * 258 ^ m ≤ (2 / w * mpBase d t w ^ (5 * t + 2)) * x := by
  obtain ⟨-, -, -, -, hQ258⟩ := Q_facts (d := d) (t := t) hw0 hw1
  have hQm0 : 0 ≤ mpBase d m w := (mpBase_pos hw0).le
  have hQm := mpBase_mono (d := d) hw0 hmt
  set Q := mpBase d t w
  have hQ1 : 1 ≤ Q := by linarith
  have e1 : mpBase d m w ^ (4 * m + 2) ≤ Q ^ (4 * m + 2) := pow_le_pow_left₀ hQm0 hQm _
  have e2 : (258 : ℝ) ^ m ≤ Q ^ m := pow_le_pow_left₀ (by norm_num) hQ258 _
  have e3 : Q ^ (4 * m + 2) * Q ^ m ≤ Q ^ (5 * t + 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hQ1 (by omega)
  have hw2 : 1 ≤ 2 / w := by rw [le_div_iff₀ hw0]; linarith
  have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
  have e4 : 2 * η / w + 1 / n ≤ 2 / w * x :=
    calc 2 * η / w + 1 / n ≤ 2 / w * η + 2 / w * (1 / n) := by
          rw [show 2 * η / w = 2 / w * η by ring]
          linarith [le_mul_of_one_le_left hinv hw2]
      _ = 2 / w * (η + 1 / n) := by ring
      _ ≤ 2 / w * x := mul_le_mul_of_nonneg_left hηx (by positivity)
  have hx0 : 0 ≤ x := by linarith
  unfold errMP
  calc (2 * η / w + 1 / n) * mpBase d m w ^ (4 * m + 2) * 258 ^ m
      ≤ 2 / w * x * Q ^ (4 * m + 2) * Q ^ m :=
        mul_le_mul (mul_le_mul e4 e1 (by positivity) (by positivity)) e2 (by positivity)
          (by positivity)
    _ = 2 / w * x * (Q ^ (4 * m + 2) * Q ^ m) := by ring
    _ ≤ 2 / w * x * Q ^ (5 * t + 2) := mul_le_mul_of_nonneg_left e3 (by positivity)
    _ = _ := by ring

/-- `d² errQ (2γ) m d ≤ 2 d² t Q^t x` for `γ ≤ x`, `m ≤ t` and `2d + 1 ≤ Q`. -/
theorem errQ_mul_le {γ x Q : ℝ} {d m t : ℕ} (hγ0 : 0 ≤ γ) (hγx : γ ≤ x) (hmt : m ≤ t)
    (hQ1 : 1 ≤ Q) (hQd : 2 * (d : ℝ) + 1 ≤ Q) :
    (d : ℝ) ^ 2 * errQ (2 * γ) m d ≤ (2 * d ^ 2 * t * Q ^ t) * x := by
  have e1 : (2 * (d : ℝ) + 1) ^ m ≤ Q ^ t :=
    (pow_le_pow_left₀ (by positivity) hQd m).trans (pow_le_pow_right₀ hQ1 hmt)
  have hm' : (m : ℝ) ≤ t := by exact_mod_cast hmt
  have e2 : 2 * γ * m ≤ 2 * x * t :=
    mul_le_mul (by linarith) hm' (Nat.cast_nonneg m) (by linarith)
  unfold errQ
  calc (d : ℝ) ^ 2 * (2 * γ * m * (2 * (d : ℝ) + 1) ^ m) ≤ (d : ℝ) ^ 2 * (2 * x * t * Q ^ t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul e2 e1 (by positivity) (by
          have : 0 ≤ x := hγ0.trans hγx
          positivity)) (by positivity)
    _ = _ := by ring

/-- **The smallness conditions for the program of degree `2m`** (`1 ≤ m ≤ t`), with the solver
accuracy `γ ≤ 2^-n`, `δc = 2 x momConst 2 w` and `e = errMP d m w η n`, when
`η + 1/n ≤ x ≤ σ² / Q^(5t+3)`. -/
theorem small_m {w σ2 η x : ℝ} {d m t n : ℕ} (hw0 : 0 < w) (hw1 : w ≤ 1) (hd : 1 ≤ d)
    (hm1 : 1 ≤ m) (hmt : m ≤ t) (hn : 0 < n) (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hη : 0 ≤ η)
    (hηx : η + 1 / n ≤ x) (hx : x ≤ σ2 / mpBase d t w ^ (5 * t + 3)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ 1 / 2 ^ n) :
    errN (2 * γ) (2 * (x * momConst 2 w)) m d ≤ 1 / 8 ∧ errMP d m w η n * 258 ^ m ≤ 1 / 4 ∧
      errD (2 * γ) (2 * (x * momConst 2 w)) (errMP d m w η n) γ m d ≤ 1 / (10 ^ 4 * d) ∧
      errD (2 * γ) (2 * (x * momConst 2 w)) (errMP d m w η n) γ m d ≤ 3 * σ2 / 8 ∧
      2 * (x * momConst 2 w) ≤ 1 / (8 * m) ∧ γ ≤ 1 := by
  obtain ⟨hQa, hQb, hQ144, hQd, hQ258⟩ := Q_facts (d := d) (t := t) hw0 hw1
  set Q := mpBase d t w
  have hQ1 : 1 ≤ Q := by linarith
  have hF0 : 0 < Q ^ (5 * t + 3) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx0 : 0 ≤ x := by linarith
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
  have hγn : γ ≤ 1 / n := hγ.trans (one_div_le_one_div_of_le hn' h2n)
  have hγx : γ ≤ x := by linarith
  have hz : (0 : ℝ) < 3 * 10 ^ 5 * d := by positivity
  have hK : momConst 2 w ≤ Q ^ 3 := by
    rw [momConst_two]
    exact pow_le_pow_left₀ (by positivity) hQ144 3
  have hK0 : 0 ≤ momConst 2 w := by rw [momConst_two]; positivity
  have hm' : (m : ℝ) ≤ t := by exact_mod_cast hmt
  have hd3 : (d : ℝ) ≤ d ^ 3 := le_self_pow₀ hd' (by norm_num)
  have hdm : (d : ℝ) * m ≤ d ^ 3 * t :=
    mul_le_mul hd3 hm' (Nat.cast_nonneg m) (by positivity)
  have hF1 : Q ≤ Q ^ (5 * t + 3) := le_self_pow₀ hQ1 (by omega)
  have hF4 : Q ^ 4 ≤ Q ^ (5 * t + 3) := pow_le_pow_right₀ hQ1 (by omega)
  have hFt : Q ^ (t + 1) ≤ Q ^ (5 * t + 3) := pow_le_pow_right₀ hQ1 (by omega)
  -- the four error terms are at most `y = σ² / (3 · 10⁵ d)`
  have ha : (m : ℝ) * (2 * (x * momConst 2 w)) ≤ σ2 / (3 * 10 ^ 5 * d) := by
    have h := mul_le_of_le_div hF0 hz hσ0.le (c := 2 * m * momConst 2 w) (by positivity) hx
      (calc 2 * m * momConst 2 w * (3 * 10 ^ 5 * d) = 6 * 10 ^ 5 * (d * m) * momConst 2 w := by
              ring
        _ ≤ 6 * 10 ^ 5 * (d ^ 3 * t) * Q ^ 3 :=
              mul_le_mul (by linarith) hK hK0 (by positivity)
        _ ≤ Q * Q ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = Q ^ 4 := by ring
        _ ≤ _ := hF4)
    linarith
  have hb : γ ≤ σ2 / (3 * 10 ^ 5 * d) := by
    have h := mul_le_of_le_div hF0 hz hσ0.le zero_le_one hx (by
      have : 3 * 10 ^ 5 * (d : ℝ) ≤ 6 * 10 ^ 5 * (d ^ 3 * t) := by
        have : (1 : ℝ) ≤ t := by exact_mod_cast hm1.trans hmt
        nlinarith
      linarith)
    linarith
  have hc : errMP d m w η n * 258 ^ m ≤ σ2 / (3 * 10 ^ 5 * d) :=
    (errMP_mul_le hw0 hw1 hmt hη hηx).trans (mul_le_of_le_div hF0 hz hσ0.le (by positivity) hx
      (calc 2 / w * Q ^ (5 * t + 2) * (3 * 10 ^ 5 * d) = 6 * 10 ^ 5 * d / w * Q ^ (5 * t + 2) := by
              ring
        _ ≤ Q * Q ^ (5 * t + 2) := mul_le_mul_of_nonneg_right hQb (by positivity)
        _ = Q ^ (5 * t + 3) := by ring))
  have hdd : (d : ℝ) ^ 2 * errQ (2 * γ) m d ≤ σ2 / (3 * 10 ^ 5 * d) :=
    (errQ_mul_le hγ0 hγx hmt hQ1 hQd).trans (mul_le_of_le_div hF0 hz hσ0.le (by positivity) hx
      (calc 2 * d ^ 2 * t * Q ^ t * (3 * 10 ^ 5 * d) = 6 * 10 ^ 5 * d ^ 3 * t * Q ^ t := by ring
        _ ≤ Q * Q ^ t := mul_le_mul_of_nonneg_right hQa (by positivity)
        _ = Q ^ (t + 1) := by ring
        _ ≤ _ := hFt))
  have hy : σ2 / (3 * 10 ^ 5 * d) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ hz (by norm_num)]
    nlinarith
  obtain ⟨hN, hD⟩ := errD_le hd (by positivity) (by positivity) (errMP_nonneg hw0 hη) hγ0 ha hb hc
    hdd hy
  have hD1 : 28 * (σ2 / (3 * 10 ^ 5 * d)) ≤ 1 / (10 ^ 4 * d) := by
    rw [mul_div_assoc', div_le_div_iff₀ hz (by positivity)]
    nlinarith
  have hD2 : 28 * (σ2 / (3 * 10 ^ 5 * d)) ≤ 3 * σ2 / 8 := by
    rw [mul_div_assoc', div_le_div_iff₀ hz (by norm_num)]
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, by linarith⟩
  rw [le_div_iff₀ (by positivity)]
  linarith

/-! ### The frame of the sample -/

/-- **The empirical variance in the whitened frame**: if `Ĉ ≻ 0` is within `1 ± δc` of `cov`,
then `vᵀ diag(κ) v` is within `1 ± δc` of `vᵀ cov_W v` for `W = W Ĉ`, `κ = kappa Ĉ`. -/
theorem cmp_frame {M : Mixture k d} {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef) {δc : ℝ}
    (hlow : ∀ v, (1 - δc) * quad M.cov v ≤ quad (empCov Y) v)
    (hup : ∀ v, quad (empCov Y) v ≤ (1 + δc) * quad M.cov v) (v : Fin d → ℝ) :
    (1 - δc) * quad (covW M (Separating.W (empCov Y))) v ≤ quad (diagonal (kappa (empCov Y))) v ∧
      quad (diagonal (kappa (empCov Y))) v ≤
        (1 + δc) * quad (covW M (Separating.W (empCov Y))) v := by
  have h1 : quad (diagonal (kappa (empCov Y))) v =
      quad (empCov Y) ((Separating.W (empCov Y))ᵀ *ᵥ v) :=
    (Separating.quad_transpose_W_mulVec (transpose_eq_of_posDef hC) v).symm
  rw [← quad_cov_transpose_mulVec, h1]
  exact ⟨hlow _, hup _⟩

/-- **A feasible point** of the programs: `v = e_i / √κᵢ` has `‖v‖² ≤ 256` and `vᵀ diag(κ) v = 1`
when all `κᵢ > 1/2`. -/
theorem exists_feasible (hd : 0 < d) {κ : Fin d → ℝ} (hκ : ∀ i, 1 / 2 < κ i) :
    ∃ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 ∧ eval v (quadPoly (diagonal κ)) = 1 := by
  set i₀ : Fin d := ⟨0, hd⟩
  have hκ0 : 0 < κ i₀ := by linarith [hκ i₀]
  set c := (Real.sqrt (κ i₀))⁻¹ with hc
  have hc2 : c ^ 2 = (κ i₀)⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hκ0.le]
  have hsum : ∀ f : ℝ → ℝ, f 0 = 0 →
      ∑ i, f (Pi.single (M := fun _ : Fin d ↦ ℝ) i₀ c i) = f c := by
    intro f hf
    rw [Fintype.sum_eq_single i₀ fun i hi ↦ by rw [Pi.single_eq_of_ne hi, hf],
      Pi.single_eq_same]
  refine ⟨Pi.single i₀ c, ?_, ?_⟩
  · rw [hsum (fun z ↦ z ^ 2) (by norm_num), hc2]
    have : (κ i₀)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hκ0 (by norm_num)]
      linarith [hκ i₀]
    linarith
  · rw [eval_quadPoly, quad_diagonal]
    have h := Fintype.sum_eq_single (f := fun i ↦ κ i * Pi.single (M := fun _ ↦ ℝ) i₀ c i ^ 2) i₀
      fun i hi ↦ by simp [Pi.single_eq_of_ne hi]
    rw [h, Pi.single_eq_same, hc2, mul_inv_cancel₀ hκ0.ne']

/-- **The hypotheses of the pseudo-expectation analysis** for a pseudo-expectation of degree `2m`
behind a solver output (`BS23.ColinearSoS.SolPE`), in the frame `W = W Ĉ` of the sample:
`cw = W cov Wᵀ`, `u = ŭ`, the positions `a_c` and `Σ_W = W Σ Wᵀ`. -/
theorem pseudoHyp {M : Mixture k d} (hM : M.Valid) {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0)
    {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0) {Y : Fin n → Fin d → ℚ}
    (hC : (empCov (ptsR Y)).PosDef) {δc : ℝ} (hδc0 : 0 ≤ δc)
    (hcmp : ∀ v, (1 - δc) * quad (covW M (Separating.W (empCov (ptsR Y)))) v ≤
        quad (diagonal (kappa (empCov (ptsR Y)))) v ∧
      quad (diagonal (kappa (empCov (ptsR Y)))) v ≤
        (1 + δc) * quad (covW M (Separating.W (empCov (ptsR Y)))) v)
    {m : ℕ} (hm : 1 ≤ m) (hδm : δc ≤ 1 / (8 * m)) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    {out : SoS.Solver.Output} {E : PseudoExpectation (Fin d) (2 * m)} (hE : SolPE m Y η₀ out E)
    {e : ℝ}
    (hΦ : coeffNorm1 (empPoly (whiten (ptsR Y)) (2 * m) -
      popPoly M.w (acoef M u0 t) (uhat M (Separating.W (empCov (ptsR Y))) u0)
        (SW M (Separating.W (empCov (ptsR Y)))) (2 * m)) ≤ e) :
    PseudoHyp E (kappa (empCov (ptsR Y))) (covW M (Separating.W (empCov (ptsR Y))))
      (uhat M (Separating.W (empCov (ptsR Y))) u0) M.w (acoef M u0 t) (M.sigmaSq u0)
      (SW M (Separating.W (empCov (ptsR Y)))) (empPoly (whiten (ptsR Y)) (2 * m)) η₀ δc e where
  one_le_m := hm
  kappa_gt := Separating.half_lt_kappa hC
  kappa_le := Separating.kappa_le_two _
  eta_nonneg := hη₀
  eq_approx := hE.sph
  abs_E_le := hE.bound
  cw_posDef := covW_posDef hM (Separating.isUnit_W hC)
  u_cw_inv := uhat_dot_covW_inv hM hu0 (Separating.isUnit_W hC)
  w_nonneg := hM.nonneg_w
  sum_w := hM.sum_w
  sigma_nonneg := (Fr.sigmaSq_pos hM hu0 hμ).le
  var_eq := sum_w_acoef_sq hM hu0 hμ
  quad_SWq := quad_SW_eq hM hu0 hμ _
  cmp_lower v := (hcmp v).1
  cmp_upper v := (hcmp v).2
  delta_nonneg := hδc0
  delta_le := hδm
  totalDegree_Phi_le := (MP.isHomogeneous_empPoly _ _).totalDegree_le
  Phi_close := hΦ

/-- **The column of the pseudo-moment matrix** at a maximal diagonal entry, when the defect is
small: `âᵀGâ ≤ 3σ² ⟨u, â⟩²` and `⟨u, â⟩ ≠ 0` for `âᵢ = Ẽ[vᵢ v_j]`. -/
theorem good_column {m : ℕ} {E : PseudoExpectation (Fin d) (2 * m)} {κ : Fin d → ℝ}
    {cw : Matrix (Fin d) (Fin d) ℝ} {u : Fin d → ℝ} {w a : Fin k → ℝ} {σ2 : ℝ}
    {SWq : Matrix (Fin d) (Fin d) ℝ} {Φ : MvPolynomial (Fin d) ℝ} {η₀ δc e : ℝ}
    (h : PseudoHyp E κ cw u w a σ2 SWq Φ η₀ δc e) {δ' : ℝ}
    (hdef : E (quadPoly (cw - vecMulVec u u)) ≤ δ') (hδd : δ' ≤ 1 / (10 ^ 4 * d))
    (hδσ : δ' ≤ 3 * σ2 / 8) (hN : errN η₀ δc m d ≤ 1 / 8) {j : Fin d}
    (hj : ∀ i, E (X i * X i) ≤ E (X j * X j)) :
    quad (cw - vecMulVec u u) (fun i ↦ E (X i * X j)) ≤
        3 * σ2 * (u ⬝ᵥ fun i ↦ E (X i * X j)) ^ 2 ∧ (u ⬝ᵥ fun i ↦ E (X i * X j)) ≠ 0 := by
  have hcol : secondMom E *ᵥ Pi.single j 1 = fun i ↦ E (X i * X j) := by
    rw [mulVec_single_one]
    rfl
  rw [← hcol]
  exact h.column_facts hdef hδd hδσ hN j hj

/-! ### Case L: the positions and the variance along the line -/

/-- If `M_{2s} ≤ 3 (5s)^s` (`s = sCol wmin`), all positions have `a_c² ≤ 20 s`: indeed
`wmin a_c^(2s) ≤ M_{2s}` and `1/wmin ≤ 2^(s-1)`. -/
theorem sq_le_of_lineMom_le {wmin : ℚ} (hwmin : 0 < wmin) {w a : Fin k → ℝ} {σ2 : ℝ}
    (hw : ∀ c, (wmin : ℝ) ≤ w c) (hσ : 0 ≤ σ2)
    (hL : lineMom w a σ2 (sCol wmin) ≤ 3 * (5 * (sCol wmin : ℝ)) ^ sCol wmin) (c : Fin k) :
    a c ^ 2 ≤ 20 * sCol wmin := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  set s := sCol wmin with hs
  have hs1 : 1 ≤ s := one_le_sCol wmin
  have h1 := mul_pow_le_lineMom (a := a) hw hw0.le hσ c s
  have h2 := OneDimApply.one_le_mul_two_pow_logInv hwmin
  have h4 : (3 : ℝ) * 2 ^ logInv wmin ≤ 4 ^ s := by
    have : (2 : ℝ) ^ logInv wmin ≤ 4 ^ logInv wmin :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have : (0 : ℝ) ≤ 4 ^ logInv wmin := by positivity
    rw [hs, sCol, pow_succ]
    linarith
  have h5 : (0 : ℝ) ≤ (5 * (s : ℝ)) ^ s := by positivity
  have h6 : (a c ^ 2) ^ s ≤ (20 * (s : ℝ)) ^ s := by
    have e1 : (a c ^ 2) ^ s = a c ^ (2 * s) := by rw [← pow_mul]
    have e2 : (20 * (s : ℝ)) ^ s = 4 ^ s * (5 * s) ^ s := by rw [← mul_pow]; ring
    rw [e1, e2]
    have h7 : a c ^ (2 * s) ≤ 2 ^ logInv wmin * (wmin * a c ^ (2 * s)) := by
      have := mul_le_mul_of_nonneg_right h2 ((even_two_mul s).pow_nonneg (a c))
      nlinarith
    calc a c ^ (2 * s) ≤ 2 ^ logInv wmin * (3 * (5 * (s : ℝ)) ^ s) :=
          h7.trans (mul_le_mul_of_nonneg_left (h1.trans hL) (by positivity))
      _ = 3 * 2 ^ logInv wmin * (5 * (s : ℝ)) ^ s := by ring
      _ ≤ 4 ^ s * (5 * (s : ℝ)) ^ s := mul_le_mul_of_nonneg_right h4 h5
  exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by omega)).1 h6

/-- `4 · 10⁸ ≤ Csep c`. -/
theorem Csep_ge (c : ℕ) : (4 * 10 ^ 8 : ℝ) ≤ CsepS c := by
  have h4 : 1 ≤ 4 ^ c := Nat.one_le_pow _ _ (by norm_num)
  have : 4 * 10 ^ 8 ≤ CsepS c :=
    calc 4 * 10 ^ 8 = 4 * 10 ^ 8 * 1 := by norm_num
      _ ≤ 4 * 10 ^ 8 * 4 ^ c := Nat.mul_le_mul_left _ h4
  exact_mod_cast this

/-- **The variance along the line is small in case L**: if all positions have `a_c² ≤ 20 s` and
the means are separated by `Csep c · log (1/wmin)`, then `σ² ≤ 1/16`. -/
theorem sigmaSq_le_of_sq_le {M : Mixture k d} (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin)
    (hw : ∀ c, (wmin : ℝ) ≤ M.w c) (hk : 2 ≤ k) (c : ℕ)
    (hsep : ∀ a b, a ≠ b → (CsepS c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0)
    (hA : ∀ c, acoef M u0 t c ^ 2 ≤ 20 * sCol wmin) : M.sigmaSq u0 ≤ 1 / 16 := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hw2 : 2 * (wmin : ℝ) ≤ 1 := two_mul_wmin_le_one hM hw0 hw hk
  have hσ := Fr.sigmaSq_pos hM hu0 hμ
  set i₀ : Fin k := ⟨0, by omega⟩
  set i₁ : Fin k := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h1 := hsep i₀ i₁ hne
  rw [sqNormIn_sub_eq_acoef hM hu0 hμ, le_div_iff₀ hσ] at h1
  have h2 : (acoef M u0 t i₀ - acoef M u0 t i₁) ^ 2 ≤ 80 * sCol wmin := by
    nlinarith [hA i₀, hA i₁, sq_nonneg (acoef M u0 t i₀ + acoef M u0 t i₁)]
  -- `s ≤ 8 log (1/wmin)`
  set ℓ := Real.log (1 / (wmin : ℝ)) with hℓ
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by
    rw [le_div_iff₀ hw0]
    linarith)
  have hl2 := Real.log_two_gt_d9
  have hs := logInv_add_one_le hwmin (by exact_mod_cast (by linarith : (wmin : ℝ) ≤ 1))
  have hsℓ : (sCol wmin : ℝ) ≤ 8 * ℓ := by
    rw [sCol]
    push_cast
    rw [← hℓ] at hs
    linarith
  have hC := Csep_ge c
  have hℓ0 : 0 < ℓ := by linarith
  have h3 : (CsepS c : ℝ) * ℓ * M.sigmaSq u0 ≤ 640 * ℓ := by linarith
  have h4 : 4 * 10 ^ 8 * ℓ * M.sigmaSq u0 ≤ (CsepS c : ℝ) * ℓ * M.sigmaSq u0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hℓ0.le) hσ.le
  nlinarith

/-! ### The direction -/

/-- **The direction found by the programs** (`k ≥ 2`, `d ≥ 1`). Let `Ĉ ≻ 0` be within `1 ± δc`
of `cov`, let the empirical moment polynomials of degree `2m ≤ 2t` be within `e m` of the
population ones in the whitened frame `W = W Ĉ`, and let the smallness conditions hold for both
programs. Then the labels are those of the line clustering along `a = Wᵀ â` for a vector `â`
with `âᵀGâ ≤ 3 σ² ⟨ŭ, â⟩²` and `⟨ŭ, â⟩ ≠ 0`. -/
theorem exists_good_dir (hk : 2 ≤ k) (hd : 0 < d) {M : Mixture k d} (hM : M.Valid) {wmin : ℚ}
    (hwmin : 0 < wmin) (hw : ∀ c, (wmin : ℝ) ≤ M.w c) (c : ℕ)
    (hsep : ∀ a b, a ≠ b → (CsepS c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0)
    {Y : Fin n → Fin d → ℚ} (hC : (empCov (ptsR Y)).PosDef) {δc : ℝ} (hδc0 : 0 ≤ δc)
    (hlow : ∀ v, (1 - δc) * quad M.cov v ≤ quad (empCov (ptsR Y)) v)
    (hup : ∀ v, quad (empCov (ptsR Y)) v ≤ (1 + δc) * quad M.cov v) {e : ℕ → ℝ}
    (hΦ : ∀ m ≤ tCol wmin, coeffNorm1 (empPoly (whiten (ptsR Y)) (2 * m) -
      popPoly M.w (acoef M u0 t) (uhat M (Separating.W (empCov (ptsR Y))) u0)
        (SW M (Separating.W (empCov (ptsR Y)))) (2 * m)) ≤ e m)
    (hsmall : ∀ m, 1 ≤ m → m ≤ tCol wmin → ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 2 ^ n →
      errN (2 * γ) δc m d ≤ 1 / 8 ∧ e m * 258 ^ m ≤ 1 / 4 ∧
        errD (2 * γ) δc (e m) γ m d ≤ 1 / (10 ^ 4 * d) ∧
        errD (2 * γ) δc (e m) γ m d ≤ 3 * M.sigmaSq u0 / 8 ∧ δc ≤ 1 / (8 * m) ∧ γ ≤ 1) :
    ∃ â : Fin d → ℝ, colLabels k wmin ((d + 5) ^ (2 * tCol wmin + 1)) Y =
        lineLabels (params wmin).cast k (ptsR Y) (dirOf (ptsR Y) â) ∧
      quad (Gm M (Separating.W (empCov (ptsR Y))) u0) â ≤
        3 * M.sigmaSq u0 * (uhat M (Separating.W (empCov (ptsR Y))) u0 ⬝ᵥ â) ^ 2 ∧
      uhat M (Separating.W (empCov (ptsR Y))) u0 ⬝ᵥ â ≠ 0 := by
  have hcmp := cmp_frame (M := M) hC hlow hup
  obtain ⟨v, hball, hsph⟩ := exists_feasible hd (Separating.half_lt_kappa hC)
  have hLb : 1 ≤ (d + 5) ^ (2 * tCol wmin + 1) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨EU, hU, hbrU, hbrL⟩ := colLabels_spec hk hd le_rfl hball hsph
  have hγU0 : (0 : ℝ) ≤ acc (progUY wmin ((d + 5) ^ (2 * tCol wmin + 1)) Y) := by
    exact_mod_cast (Separating.acc_pos _).le
  obtain ⟨hNU, heU, hDU1, hDU2, hδU, hγU1⟩ := hsmall _ (one_le_sCol wmin) (sCol_le_tCol wmin) _
    hγU0 (acc_progUY_le hLb Y)
  have hPU := pseudoHyp hM hu0 hμ hC hδc0 hcmp (one_le_sCol wmin) hδU (by positivity)
    hU.toSolPE (hΦ _ (sCol_le_tCol wmin))
  by_cases hT : (5 * (sCol wmin : ℝ)) ^ sCol wmin ≤
    EU (empPoly (whiten (ptsR Y)) (2 * sCol wmin))
  · -- case U: the upper program is used
    obtain ⟨j, hj, hlab⟩ := hbrU hT
    have hdef := hPU.defect_le_of_max hγU0 (hPU.lineMom_ge_of_test hNU heU hT) hU.opt
    obtain ⟨h1, h2⟩ := good_column hPU hdef hDU1 hDU2 hNU hj
    exact ⟨_, hlab, h1, h2⟩
  · -- case L: the lower program is used
    have hT' := not_le.1 hT
    obtain ⟨EL, hL, j, hj, hlab⟩ := hbrL hT'
    have hA := sq_le_of_lineMom_le hwmin hw (Fr.sigmaSq_pos hM hu0 hμ).le
      (hPU.lineMom_le_of_test hγU1 heU hT' hU.opt)
    have hσ := sigmaSq_le_of_sq_le hM hwmin hw hk c hsep hu0 hμ hA
    have hγL0 : (0 : ℝ) ≤ acc (progLY wmin ((d + 5) ^ (2 * tCol wmin + 1)) Y) := by
      exact_mod_cast (Separating.acc_pos _).le
    obtain ⟨hNL, -, hDL1, hDL2, hδL, -⟩ := hsmall _ (one_le_tCol wmin) le_rfl _ hγL0
      (acc_progLY_le hLb Y)
    have hPL := pseudoHyp hM hu0 hμ hC hδc0 hcmp (one_le_tCol wmin) hδL (by positivity)
      hL.toSolPE (hΦ _ le_rfl)
    have hm : 5 * (20 * (sCol wmin : ℝ)) + 8 ≤ tCol wmin := by
      have h1 : (1 : ℝ) ≤ sCol wmin := by exact_mod_cast one_le_sCol wmin
      rw [tCol]
      push_cast
      linarith
    have hdef := hPL.defect_le_of_min hγL0 hA (by positivity) hσ hm hL.opt
    obtain ⟨h1, h2⟩ := good_column hPL hdef hDL1 hDL2 hNL hj
    exact ⟨_, hlab, h1, h2⟩

end Cor

open Cor

/-! ### The algorithm is correct -/

/-- **Correctness for `k ≥ 2`**, with the positions `t` of the means on the line given. -/
theorem colLabels_correct_of_two_le (c : ℕ) (hk : 2 ≤ k) (M : Mixture k d) (hM : M.Valid)
    {wmin : ℚ} (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    (hsep : ∀ a b, a ≠ b → (CsepS c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {t : Fin k → ℝ} (hμ : ∀ i, M.μ i = base + t i • u0)
    (hn : 0 < n) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {η : ℝ}
    (hG : GoodNoise M.w η (DcolS wmin) (labels ω) (stdNoise M ω))
    (hacc : η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n ≤ colSoSTarget wmin d (M.sigmaSq u0)) :
    ClustersWithin ((wmin / k : ℝ) ^ c) (labels ω)
      (List.ofFn (colLabels k wmin ((d + 5) ^ (2 * tCol wmin + 1)) fun j a ↦ r (ω j) a)) := by
  set Y : Fin n → Fin d → ℚ := fun j a ↦ r (ω j) a
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hwpos : ∀ i, 0 ≤ M.w i := hM.nonneg_w
  have hw1 : (wmin : ℝ) ≤ 1 := Colinear.wmin_le_one hM hw0 hw
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd (Subsingleton.elim u0 0) hu0
    · exact h
  have hσ0 := Fr.sigmaSq_pos hM hu0 hμ
  have hσ1 := Fr.sigmaSq_le_one hM hu0 hμ
  -- the sample
  have hU := uniformNoise_of_goodNoise_stdNoise M hM.posDef hG
  have hround : ∀ j, sqNormIn M.S (ptsR Y j -
      (M.μ (labels ω j) + (fun j i ↦ (ω j).2 i - M.μ (ω j).1 i) j)) ≤ 1 / (n : ℝ) ^ 2 := by
    intro j
    have h := hr (ω j).1 (ω j).2
    rw [Prod.mk.eta, _root_.one_div_pow] at h
    convert h using 2
    funext a
    simp [labels, ptsR, Y]
  have H : MomHyp M (wmin : ℝ) (labels ω) (fun j i ↦ (ω j).2 i - M.μ (ω j).1 i) (ptsR Y) η
      (η * ((d : ℝ) + 1) ^ DcolS wmin) (DcolS wmin) := ⟨hM, hw0, hw, hn, hround, hG.1, hU⟩
  have hη0 := H.eta_nonneg
  have hη'0 : 0 ≤ η * ((d : ℝ) + 1) ^ DcolS wmin := by positivity
  -- the numerics
  have hx : η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n ≤
      M.sigmaSq u0 / mpBase d (tCol wmin) wmin ^ (5 * tCol wmin + 3) := hacc
  obtain ⟨hδ8, hη2, hη', hηw, hdn, hn8, hσn⟩ :=
    small_global hw0 hw1 (one_le_tCol wmin) hn hσ0 hσ1 hη0 hη'0 hx
  set δ := (η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n) * momConst 2 wmin
  have hδ0 : 0 ≤ δ := mul_nonneg H.acc_nonneg (by rw [momConst_two]; positivity)
  have hδ1 : (η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n) * momConst 1 wmin ≤ δ :=
    mul_le_mul_of_nonneg_left (momConst_mono hw0 hw1 (by norm_num)) H.acc_nonneg
  -- the covariance comparison
  have HC := H.cov_close (by unfold DcolS; omega) hδ1 le_rfl hδ0 (by linarith)
  have hC : (empCov (ptsR Y)).PosDef :=
    empCov_posDef_of_le (ptsR Y) (cov_posDef M hM hwpos) (εC := 2 * δ) (by linarith)
      fun v ↦ (HC v).1
  have hcv : ∀ v, (wmin : ℝ) / 4 * quad M.S v ≤ quad (empCov (Separating.yt r ω)) v := by
    intro v
    have h2 : quad M.S v ≤ quad M.cov v := Colinear.quad_S_le_quad_cov M hwpos v
    have h3 : 0 ≤ quad M.S v := quad_S_nonneg hM v
    have h4 : (wmin : ℝ) / 4 * quad M.S v ≤ (1 - 2 * δ) * quad M.S v :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    have h5 : (1 - 2 * δ) * quad M.S v ≤ (1 - 2 * δ) * quad M.cov v :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    exact h4.trans (h5.trans (HC v).1)
  have hcov2 : ∀ v, quad M.cov v ≤ 2 * quad (empCov (Separating.yt r ω)) v := by
    intro v
    have h1 := (HC v).1
    have h0 := H.quad_cov_nonneg v
    have : (1 / 2) * quad M.cov v ≤ (1 - 2 * δ) * quad M.cov v :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    change quad M.cov v ≤ 2 * quad (empCov (ptsR Y)) v
    linarith
  -- the finite-sample transfer
  have hΦ : ∀ m ≤ tCol wmin, coeffNorm1 (empPoly (whiten (ptsR Y)) (2 * m) -
      popPoly M.w (acoef M u0 t) (uhat M (Separating.W (empCov (ptsR Y))) u0)
        (SW M (Separating.W (empCov (ptsR Y)))) (2 * m)) ≤ errMP d m wmin η n :=
    fun m hm ↦ coeffNorm1_empPoly_sub_popPoly_le hM hu0 hμ hw0 hw hn (by exact_mod_cast hdn) hr
      hG hηw hcv hcov2 (by unfold DcolS; omega)
  -- the direction
  obtain ⟨â, hlab, hperp, hα⟩ := exists_good_dir hk hd hM hwmin hw c hsep hu0 hμ hC
    (δc := 2 * δ) (by positivity) (fun v ↦ (HC v).1) (fun v ↦ (HC v).2) hΦ
    (fun m hm1 hmt γ hγ0 hγ ↦ small_m hw0 hw1 hd hm1 hmt hn hσ0 hσ1 hη0 (by linarith) hx hγ0 hγ)
  have ha : dirOf (ptsR Y) â = (Separating.W (empCov (ptsR Y)))ᵀ *ᵥ â := rfl
  obtain ⟨hF1, hF2, hF3, hF4⟩ := fisher_ratio_of_perp_le hM hu0 hμ ha hperp hα
  -- the scale and the separation
  have HCa := HC (dirOf (ptsR Y) â)
  obtain ⟨hV1, hV2⟩ := scale_bounds (H.quad_cov_nonneg _) hF3.le hδ8 HCa.1 HCa.2 hF2 hF4 hσn hn8
  obtain ⟨Γ, hΓ, hΓc, hsepΓ⟩ := exists_gamma c hM hwmin hw hk hsep hμ hF1 hF3.le
  -- the line clustering
  have hsz := size_ge hw0 hw hn hη2 hG.1
  have hD : 2 * logInv wmin + 8 ≤ DcolS wmin := by unfold DcolS; omega
  have key := oneDim_clustersWithin_params hk hn hM hwmin hw hround hsz hU hη' hD hF3 hΓ hsepΓ
    hΓc hV1 hV2
  rw [hlab, lineLabels_def]
  exact key

/-- **Correctness of the sum-of-squares algorithm for colinear means** [BS23, Theorem 1.2],
deterministic part. Let `M` be a valid mixture with weights at least `wmin > 0` and means on the
line `base + ℝ u₀` (`u₀ ≠ 0`), pairwise separated by `CsepS c · log (1/wmin)` in the geometry of
`Σ`. Take a sample `ω` of size `n > 0`, rounded by `r` within `1/n`, in the good event of degree
`DcolS wmin` and accuracy `η`. If `η + η (d + 1)^(DcolS wmin) + 1/n ≤ colSoSTarget wmin d σ²`
(`σ² = M.sigmaSq u0`), the algorithm `colLabels` with the budget `(d + 5)^(2t + 1)` clusters the
rounded points with error `(wmin / k)^c`. -/
theorem colLabels_correct (c : ℕ) (M : Mixture k d) (hM : M.Valid) {wmin : ℚ}
    (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    (hsep : ∀ a b, a ≠ b → (CsepS c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {base u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) (hcol : ∀ i, ∃ t : ℝ, M.μ i = base + t • u0)
    (hn : 0 < n) (r : Rounding k d) (hr : IsRounding M.S (1 / n) r)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) {η : ℝ}
    (hG : GoodNoise M.w η (DcolS wmin) (labels ω) (stdNoise M ω))
    (hacc : η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n ≤ colSoSTarget wmin d (M.sigmaSq u0)) :
    ClustersWithin ((wmin / k : ℝ) ^ c) (labels ω)
      (List.ofFn (colLabels k wmin ((d + 5) ^ (2 * tCol wmin + 1)) fun j a ↦ r (ω j) a)) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by
      rcases k with _ | _ | k
      · have := hM.sum_w
        simp at this
      · rfl
      · omega
    rw [colLabels_of_le_one le_rfl]
    exact clustersWithin_one hn (labels ω)
      (pow_nonneg (div_nonneg (by exact_mod_cast hwmin.le) (Nat.cast_nonneg _)) _)
  · exact colLabels_correct_of_two_le c hk M hM hwmin hw hsep hu0
      (t := fun i ↦ Classical.choose (hcol i)) (fun i ↦ Classical.choose_spec (hcol i)) hn hr hG
      hacc

end BS23.ColinearSoS
