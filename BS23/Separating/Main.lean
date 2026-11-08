module

public import BS23.Separating.Feasible
public import BS23.Separating.PseudoAnalysis
public import BS23.Separating.Rounding
public import BS23.Common.Glue
public import BS23.Colinear.Main
public import BS23.Separating.RunTime

/-!
# Theorem 1.1 of [BS23]

`BS23.Separating.separating_bipartition_main` is the statement of `BS23.separating_bipartition`
(`BS23/Challenge.lean`), proved from its parts.

* **The algorithm** is `BS23.Separating.sepAlgU` (`BS23/Separating/Alg.lean`). On an input with
  failure probability `δ > 0` it is `BS23.Separating.sepAlg r Kc` with `r = 2^41 R`
  (`BS23.Separating.ratioR`) and `Kc = ⌈log₂ (4R)⌉` (`BS23.Separating.kcR`),
  `R = max ⌈1/δ⌉ 100` (`BS23.Separating.rOf`). One machine serves all `δ`: it runs in time
  `bipartitionTime C₀` (`BS23.Separating.sepAlgU_runsInTime`, `BS23/Separating/RunTime.lean`),
  hence in time `bipartitionTime C` for every `C ≥ C₀` (`BS23.Separating.bipartitionTime_mono`).
* **How `δ` enters.** The analysis below runs with `ε' = 1/R ≤ min δ (1/100)`, for which
  `r = 2^41 / ε'` and `2^Kc ≥ 4 / ε'` (`BS23.Separating.div_inv_eq_ratioR`,
  `BS23.Separating.div_inv_le_two_pow_kcR`). It needs the separation `Cs log (1/wmin)` and the
  sample size `B^(Cs (log (1/wmin) + 1))` for a constant `Cs ≥ max(1152 r, 3 K₁ r)`,
  `K₁ = 20 (r + 3) + 3 Kc + 207`, that is `Cs = O(R²)`. As `R ≤ 100 ⌈1/δ⌉`, the theorem's
  `Cs = C ⌈1/δ⌉^C` is enough for `C ≥ 2^106` (`BS23.Separating.params_le`). The algorithm and the
  time bound are uniform in `δ`; the generic part of the analysis is
  `BS23.Separating.success_bound`, for any algorithm that is `sepAlg r Kc` on the inputs and any
  time bound that leaves room for the coins.
* **One good sample** (`BS23.Separating.le_coinProb_of_goodNoise`). On a sample in the good event
  `BS23.GoodNoise` of degree `2t`, `t = r (L + 1)`, `L = logInv wmin`, and accuracy `η`: the
  covariance comparison CV1 holds, the program is valid (`BS23.Separating.progOf_valid_of_sample`),
  and the sample side of the pseudo-expectation analysis holds
  (`BS23.Separating.modelHyp_of_goodNoise`, collected in `BS23.Separating.ModelHyp`: whitened points
  `xⱼ = m_{ℓⱼ} + ζⱼ`, the noise form `N = ∑ᵢ φᵢ²` for the columns `φᵢ` of `B`, moment closeness
  with error `e = (2η/wmin + 1/n) (4 (d+1) (2t+1))^(2t+1) β^(2t)`, `β = 3 (d + 1) / √wmin`). It is
  transported to the indexing of the input by `BS23.Separating.modelHyp_xR`. Then
  `BS23.Separating.le_coinProb_sep`: the solver output is correct, `BS23.Separating.alg_spec` gives
  the pseudo-expectation, which with the sample side satisfies `BS23.Separating.PAHyp`; its
  consequences (`BS23.Separating.PAHyp.rounding_hyps`) give a set of at most `100 δ₁ n` bad pivots
  (`BS23.Separating.isSeparatingBipartition_ofFn`), which the pivot read from the coins avoids
  with probability at least `1 - 100 δ₁ - n / 2^b` (`BS23.Separating.le_coinProb_of_coinIdx`).
  Here `δ₁ ≤ ε'/400` (`BS23.Separating.delta1_le_of`, from `r ≥ 2^41 / ε'`) and
  `n / 2^b ≤ ε'/4` (`BS23.Separating.div_two_pow_coinBits_le`), and the `b` coins are among the
  `bipartitionTime C x` coins for `C ≥ 400`, as `Kc ≤ 4R ≤ 400 ⌈1/δ⌉`
  (`BS23.Separating.coinBits_le_time`).
* **The numerics.** The accuracy is `η = ε' wmin / Z` with
  `Z = 2^14 2^(17t) (4 (d+1) (2t+1))^(2t+1) β^(2t) Gst` (`BS23.Separating.zOf`), `Gst` the bound
  `(2t)^(2t) (d + 1)^t β^(2t)` on the Gaussian moment polynomials (`BS23.Separating.gstOf`). A
  sample of size `n ≥ 2 Z² X / (ε'³ wmin³)`, `X` the factor of the failure probability of the good
  event (`BS23.Separating.failX`), makes the error small enough for every step and the failure
  probability at most `ε'/2` (`BS23.Separating.numerics_abstract`, `BS23.Separating.fail_le`).
  With `B = (d + 1) / wmin ≥ 2`, `t ≤ B^(r+3)` (`BS23.Separating.tDeg_le_pow`) and
  `1/ε' ≤ 2^Kc ≤ B^Kc`, this size is at most `B^(K₁ t)`, `K₁ = 20 (r + 3) + 3 Kc + 207`
  (`BS23.Separating.sample_le_pow`), which the hypothesis
  `B^(Cs (log (1/wmin) + 1)) ≤ n` gives for `Cs ≥ 3 K₁ r`, since `L + 1 ≤ 3 (log (1/wmin) + 1)`
  (`BS23.Separating.exponent_le'`, `BS23.Colinear.logInv_add_one_le`).
* **The separation.** Two distinct components force `wmin ≤ 1/2`
  (`BS23.Separating.two_mul_wmin_le_one`), so `log (1/wmin) ≥ 1/2` and the hypothesis gives the
  distance `128 t` that feasibility needs for `Cs ≥ 1152 r` (`BS23.Separating.sep_le`).
* **The probability** (`BS23.Separating.success_bound`): `BS23.le_successProb_of_goodNoise` with
  `p = 1 - ε'/2` and failure at most `ε'/2` gives `(1 - ε'/2)² ≥ 1 - ε' ≥ 1 - δ`.

The constant of the theorem is `C = C₀ + 2^106`, with `C₀ = 5 (E + 1) · 100 (3 · 2^42 + 1)` the
time constant, `E` the exponent of the time bound of the machine
(`BS23.Separating.RT.pow_le_bipartitionTime`).
-/

@[expose] public section

namespace BS23.Separating

open MvPolynomial Finset SoS Matrix

/-! ### Parameters -/

theorem one_le_ceil_inv {δ : ℚ} (hδ : 0 < δ) : 1 ≤ ⌈1 / δ⌉₊ :=
  Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'

theorem hundred_le_rOf {δ : ℚ} (hδ : 0 < δ) : 100 ≤ rOf δ := by
  rw [rOf_of_pos hδ]
  exact le_max_right _ _

/-- `1/δ ≤ R`. -/
theorem inv_le_rOf {δ : ℚ} (hδ : 0 < δ) : 1 / (δ : ℝ) ≤ rOf δ := by
  have h : (1 / δ : ℚ) ≤ ⌈1 / δ⌉₊ := Nat.le_ceil _
  have h' : (1 / (δ : ℝ)) ≤ (⌈1 / δ⌉₊ : ℝ) := by exact_mod_cast h
  rw [rOf_of_pos hδ]
  exact h'.trans (by exact_mod_cast le_max_left _ _)

/-- `R ≤ 100 ⌈1/δ⌉`. -/
theorem rOf_le_hundred_mul (δ : ℚ) : rOf δ ≤ 100 * ⌈1 / δ⌉₊ := RT.rOf_le δ

/-- `2^41 / (1/R) = r`. -/
theorem div_inv_eq_ratioR (R : ℕ) : (2 : ℝ) ^ 41 / (1 / (R : ℝ)) = ratioR R := by
  unfold ratioR
  rw [div_div_eq_mul_div, div_one]
  push_cast
  ring

/-- `4 / (1/R) ≤ 2^Kc`. -/
theorem div_inv_le_two_pow_kcR (R : ℕ) : (4 : ℝ) / (1 / (R : ℝ)) ≤ 2 ^ kcR R := by
  rw [div_div_eq_mul_div, div_one]
  have h : 4 * R ≤ 2 ^ kcR R := Nat.le_pow_clog (by norm_num) _
  exact_mod_cast h

/-- **The constant of the separation and the sample size**: for `1 ≤ m`, `R ≤ 100 m`, `1 ≤ R`
and `C ≥ 2^106`, the requirements `1152 r ≤ C m^C` and `3 (20 (r + 3) + 3 Kc + 207) r ≤ C m^C`
on `r = ratioR R`, `Kc = kcR R`. -/
theorem params_le {R m C : ℕ} (hm : 1 ≤ m) (hRm : R ≤ 100 * m) (hR : 1 ≤ R) (hC : 2 ^ 106 ≤ C) :
    1152 * ratioR R ≤ C * m ^ C ∧
      3 * (20 * (ratioR R + 3) + 3 * kcR R + 207) * ratioR R ≤ C * m ^ C := by
  have hr : ratioR R ≤ 2 ^ 41 * 100 * m := by
    unfold ratioR
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ hRm
  have hK : kcR R ≤ ratioR R := by
    unfold kcR ratioR
    have : Nat.clog 2 (4 * R) ≤ 4 * R :=
      (Nat.clog_le_iff_le_pow (by norm_num)).2 Nat.lt_two_pow_self.le
    omega
  have hr1 : 1 ≤ ratioR R := by
    unfold ratioR
    omega
  have hm1 : m ≤ m ^ C := Nat.le_self_pow (by omega) m
  have hm2 : m ^ 2 ≤ m ^ C := Nat.pow_le_pow_right hm (by omega)
  constructor
  · calc 1152 * ratioR R ≤ 1152 * (2 ^ 41 * 100 * m) := Nat.mul_le_mul_left _ hr
      _ = (1152 * 2 ^ 41 * 100) * m := by ring
      _ ≤ 2 ^ 106 * m := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ C * m ^ C := Nat.mul_le_mul hC hm1
  · calc 3 * (20 * (ratioR R + 3) + 3 * kcR R + 207) * ratioR R ≤ 870 * ratioR R * ratioR R :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ 870 * (2 ^ 41 * 100 * m) * (2 ^ 41 * 100 * m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) hr
      _ = (870 * (2 ^ 41 * 100) ^ 2) * m ^ 2 := by ring
      _ ≤ 2 ^ 106 * m ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ C * m ^ C := Nat.mul_le_mul hC hm2

/-! ### The constants of the analysis -/

/-- `β² = 9 (d + 1)² / wmin`, the square of the bound `β = 3 (d + 1) / √wmin` on the `ℓ₁` norms
of the columns of `B`. -/
noncomputable def bsq (d : ℕ) (w : ℝ) : ℝ := 9 * ((d : ℝ) + 1) ^ 2 / w

/-- The constant `(4 (d + 1) (2t + 1))^(2t + 1)` of the moment closeness up to degree `2t`. -/
noncomputable def momC (d t : ℕ) : ℝ := (4 * ((d : ℝ) + 1) * (2 * t + 1)) ^ (2 * t + 1)

/-- The bound `(2t)^(2t) (d + 1)^t β^(2t)` on the Gaussian moment polynomials up to degree
`2t`. -/
noncomputable def gstOf (d t : ℕ) (w : ℝ) : ℝ :=
  (2 * (t : ℝ)) ^ (2 * t) * ((d : ℝ) + 1) ^ t * bsq d w ^ t

/-- `Z = 2^14 2^(17t) (4 (d + 1) (2t + 1))^(2t + 1) β^(2t) Gst`: the accuracy of the good event
is `η = ε' wmin / Z`. -/
noncomputable def zOf (d t : ℕ) (w : ℝ) : ℝ :=
  2 ^ 14 * 2 ^ (17 * t) * momC d t * bsq d w ^ t * gstOf d t w

/-- The factor `1/wmin + (d + 1)^D (2D)^D` of the failure probability of the good event of
degree `D`. -/
noncomputable def failX (d D : ℕ) (w : ℝ) : ℝ := 1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D

theorem one_le_bsq {d : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) : 1 ≤ bsq d w := by
  unfold bsq
  rw [le_div_iff₀ hw0]
  have : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  nlinarith

theorem sq_le_momC (d : ℕ) {t : ℕ} (ht1 : 1 ≤ t) : ((d : ℝ) + 1) ^ 2 ≤ momC d t := by
  unfold momC
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (1 : ℝ) ≤ 4 * ((d : ℝ) + 1) * (2 * t + 1) := by nlinarith
  calc ((d : ℝ) + 1) ^ 2 ≤ (4 * ((d : ℝ) + 1) * (2 * t + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

theorem one_le_gstOf {d t : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (ht : 1 ≤ t) :
    1 ≤ gstOf d t w := by
  unfold gstOf
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (1 : ℝ) ≤ (2 * (t : ℝ)) ^ (2 * t) := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ t :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have h3 : (1 : ℝ) ≤ bsq d w ^ t := one_le_pow₀ (one_le_bsq hw0 hw1)
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-! ### The numerics of the good event -/

/-- The failure probability: with `η = ε w / Z`, `k ≤ 1/w` and `n ≥ 2 Z² X / (ε³ w³)`,
`k / (n η²) X ≤ ε / 2`. -/
theorem fail_le {ε w n X kk Z η : ℝ} (hε0 : 0 < ε) (hw0 : 0 < w) (hX : 0 ≤ X) (hk : kk ≤ 1 / w)
    (hZ : 0 < Z) (hη : η = ε * w / Z) (hn0 : 0 < n) (hn : 2 * Z ^ 2 * X / (ε ^ 3 * w ^ 3) ≤ n) :
    kk / (n * η ^ 2) * X ≤ ε / 2 := by
  have hη0 : 0 < η := by rw [hη]; positivity
  have key : X / w ≤ ε / 2 * (n * η ^ 2) := by
    rw [hη, div_le_iff₀ hw0]
    have e1 : ε / 2 * (n * (ε * w / Z) ^ 2) * w = n * (ε ^ 3 * w ^ 3) / (2 * Z ^ 2) := by
      field_simp
    rw [e1, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hn
    linarith only [hn]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc kk * X ≤ 1 / w * X := mul_le_mul_of_nonneg_right hk hX
    _ = X / w := by ring
    _ ≤ _ := key

/-- **The numerics of the good event**, abstractly: `Φ` stands for `momC d t`, `bt` for
`β^(2t)`, `G` for `gstOf d t w`, `d2` for `(d + 1)²`, `X` for `failX d (2t) w`, `kk` for `k`, and
`Z = 2^14 2^(17t) Φ bt G`. With `η = ε w / Z` and `n ≥ 2 Z² X / (ε³ w³)`, the accuracy
`A = 2η/w + 1/n` and the error `e = A Φ bt` are as small as the analysis needs, and the failure
probability `k / (n η²) X` of the good event is at most `ε/2`. -/
theorem numerics_abstract {ε w n Φ bt G X d2 kk Z η : ℝ} {s t : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hd2 : 1 ≤ d2) (hΦ : d2 ≤ Φ) (hbt : 1 ≤ bt) (hG : 1 ≤ G)
    (hX : 1 ≤ X) (hst : s ≤ t) (hk : kk ≤ 1 / w)
    (hZ : Z = 2 ^ 14 * 2 ^ (17 * t) * Φ * bt * G) (hη : η = ε * w / Z)
    (hn : 2 * Z ^ 2 * X / (ε ^ 3 * w ^ 3) ≤ n) :
    0 < η ∧ 2 * η ≤ w ∧ 2 * η ≤ 1 ∧ Z ≤ n ∧
      2 * (η * d2) / w + 4 / n ≤ 1 / 8 ∧
      (2 * η / w + 1 / n) * Φ ≤ 1 ∧
      258 ^ t * (3 * 4 ^ t * G * ((2 * η / w + 1 / n) * Φ * bt)) ≤ 1 / 2 ∧
      4 * 64 ^ s * (4 ^ s * 258 ^ t * ((2 * η / w + 1 / n) * Φ * bt)) ≤ ε / 800 ∧
      kk / (n * η ^ 2) * X ≤ ε / 2 := by
  have hΦ1 : 1 ≤ Φ := hd2.trans hΦ
  have h17 : (1 : ℝ) ≤ 2 ^ (17 * t) := one_le_pow₀ (by norm_num)
  have hZ1 : 2 ^ 14 * Φ ≤ Z := by
    rw [hZ]
    calc (2 : ℝ) ^ 14 * Φ = 2 ^ 14 * 1 * Φ * 1 * 1 := by ring
      _ ≤ 2 ^ 14 * 2 ^ (17 * t) * Φ * bt * G := by gcongr
  have hZ14 : (2 : ℝ) ^ 14 ≤ Z := by nlinarith
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZ14
  have hηpos : 0 < η := by rw [hη]; positivity
  -- the sample size
  have hew : ε ^ 2 * w ^ 3 ≤ 1 := by
    have := mul_le_mul (pow_le_one₀ (n := 2) hε0.le hε1) (pow_le_one₀ (n := 3) hw0.le hw1)
      (by positivity) zero_le_one
    rwa [one_mul] at this
  have h2ZX : 1 ≤ 2 * Z * X := by nlinarith
  have hNZ : Z / ε ≤ 2 * Z ^ 2 * X / (ε ^ 3 * w ^ 3) := by
    rw [div_le_div_iff₀ hε0 (by positivity)]
    calc Z * (ε ^ 3 * w ^ 3) = (Z * ε) * (ε ^ 2 * w ^ 3) := by ring
      _ ≤ (Z * ε) * (2 * Z * X) :=
          mul_le_mul_of_nonneg_left (hew.trans h2ZX) (by positivity)
      _ = 2 * Z ^ 2 * X * ε := by ring
  have hnZ : Z / ε ≤ n := hNZ.trans hn
  have hZn : Z ≤ n := (le_div_self hZpos.le hε0 hε1).trans hnZ
  have hnpos : 0 < n := lt_of_lt_of_le hZpos hZn
  -- the accuracy
  have h2η : 2 * η / w = 2 * ε / Z := by
    rw [hη]
    field_simp
  have h1n : 1 / n ≤ ε / Z := by
    rw [div_le_div_iff₀ hnpos hZpos]
    rw [div_le_iff₀ hε0] at hnZ
    linarith
  set A := 2 * η / w + 1 / n with hA_def
  have hA0 : 0 ≤ A := by positivity
  have hA : A ≤ 3 * ε / Z := by
    rw [hA_def, h2η]
    have : 3 * ε / Z = 2 * ε / Z + ε / Z := by ring
    linarith
  have hAZ : A * Z ≤ 3 * ε := by
    have := mul_le_mul_of_nonneg_right hA hZpos.le
    rwa [div_mul_cancel₀ _ hZpos.ne'] at this
  set e := A * Φ * bt with he_def
  have he0 : 0 ≤ e := by positivity
  have heG : e * G * 2 ^ (17 * t) ≤ 3 * ε / 2 ^ 14 := by
    rw [le_div_iff₀ (by norm_num)]
    calc e * G * 2 ^ (17 * t) * 2 ^ 14 = A * Z := by rw [he_def, hZ]; ring
      _ ≤ 3 * ε := hAZ
  have hAΦ : A * Φ ≤ e * G * 2 ^ (17 * t) := by
    have h1 : A * Φ * 1 * 1 * 1 ≤ A * Φ * bt * G * 2 ^ (17 * t) := by gcongr
    rw [he_def]
    linarith
  have h1032 : (258 : ℝ) ^ t * 4 ^ t ≤ 2 ^ (17 * t) := by
    rw [← mul_pow, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have h66048 : (256 : ℝ) ^ t * 258 ^ t ≤ 2 ^ (17 * t) := by
    rw [← mul_pow, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have h256 : (64 : ℝ) ^ s * 4 ^ s ≤ 256 ^ t := by
    rw [← mul_pow]
    exact (pow_le_pow_right₀ (by norm_num) hst).trans_eq' (by norm_num)
  have h2εZ : 2 * ε ≤ Z := by
    have : (2 : ℝ) ^ 14 = 16384 := by norm_num
    linarith
  have h2ηw : 2 * η ≤ w := by
    rw [hη, mul_div_assoc', div_le_iff₀ hZpos]
    calc 2 * (ε * w) = (2 * ε) * w := by ring
      _ ≤ Z * w := mul_le_mul_of_nonneg_right h2εZ hw0.le
      _ = w * Z := by ring
  refine ⟨hηpos, h2ηw, h2ηw.trans hw1, hZn, ?_, ?_, ?_, ?_, ?_⟩
  · -- the covariance comparison
    have hn0 : 0 ≤ 1 / n := by positivity
    have hη0 : 0 ≤ 2 * η / w := by positivity
    have h1 : 2 * (η * d2) / w ≤ d2 * A := by
      have e1 : 2 * (η * d2) / w = d2 * (2 * η / w) := by ring
      rw [e1, hA_def]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hn0) (by linarith)
    have h2 : 4 / n ≤ 4 * d2 * A := by
      have e1 : 4 / n = 4 * 1 * (1 / n) := by ring
      rw [e1, hA_def]
      gcongr
      exact le_add_of_nonneg_left hη0
    have h3 : d2 * A ≤ Φ * A := mul_le_mul_of_nonneg_right hΦ hA0
    have h4 : A * Φ ≤ 3 * ε / 2 ^ 14 := hAΦ.trans heG
    have h5 : 15 * ε / 2 ^ 14 ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith only [hε1]
    have e2 : 15 * ε / 2 ^ 14 = 5 * (3 * ε / 2 ^ 14) := by ring
    have e3 : Φ * A = A * Φ := mul_comm _ _
    linarith only [h1, h2, h3, h4, h5, e2, e3]
  · -- feasibility
    have h1 : 3 * ε / 2 ^ 14 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      linarith only [hε1]
    exact (hAΦ.trans heG).trans h1
  · -- the bounded values
    have e1 : (258 : ℝ) ^ t * (3 * 4 ^ t * G * e) = 3 * (258 ^ t * 4 ^ t) * (G * e) := by ring
    rw [e1]
    have hGe : 0 ≤ G * e := by positivity
    have h2 : 3 * ((258 : ℝ) ^ t * 4 ^ t) * (G * e) ≤ 3 * 2 ^ (17 * t) * (G * e) := by gcongr
    have h3 : 3 * (2 : ℝ) ^ (17 * t) * (G * e) = 3 * (e * G * 2 ^ (17 * t)) := by ring
    have h4 : 3 * (3 * ε / 2 ^ 14) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith only [hε1]
    have h5 : 3 * (e * G * 2 ^ (17 * t)) ≤ 3 * (3 * ε / 2 ^ 14) := by linarith only [heG]
    linarith only [h2, h3, h4, h5]
  · -- the bad pairs
    have e1 : 4 * 64 ^ s * (4 ^ s * 258 ^ t * e) = 4 * (64 ^ s * 4 ^ s) * 258 ^ t * e := by ring
    rw [e1]
    have h2 : 4 * ((64 : ℝ) ^ s * 4 ^ s) * 258 ^ t * e ≤ 4 * 256 ^ t * 258 ^ t * e := by gcongr
    have h3 : 4 * (256 : ℝ) ^ t * 258 ^ t * e ≤ 4 * 2 ^ (17 * t) * e := by
      have e2 : 4 * (256 : ℝ) ^ t * 258 ^ t * e = 4 * (256 ^ t * 258 ^ t) * e := by ring
      rw [e2]
      gcongr
    have h4 : 4 * (2 : ℝ) ^ (17 * t) * e ≤ 4 * (e * G * 2 ^ (17 * t)) := by
      have e2 : 4 * (e * G * 2 ^ (17 * t)) = 4 * 2 ^ (17 * t) * (e * G) := by ring
      rw [e2]
      have : e ≤ e * G := le_mul_of_one_le_right he0 hG
      gcongr
    have h5 : 4 * (3 * ε / 2 ^ 14) ≤ ε / 800 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith only [hε0]
    have h6 : 4 * (e * G * 2 ^ (17 * t)) ≤ 4 * (3 * ε / 2 ^ 14) := by linarith only [heG]
    linarith only [h2, h3, h4, h5, h6]
  · exact fail_le hε0 hw0 (by linarith) hk hZpos hη (lt_of_lt_of_le hZpos hZn) hn

/-! ### The sample size as a power of `B = (d + 1) / wmin` -/

section Powers

variable {B w : ℝ} {d t P : ℕ}

theorem base_le_pow (hB2 : 2 ≤ B) (hBd : (d : ℝ) + 1 ≤ B) (ht1 : 1 ≤ t)
    (htB : (t : ℝ) ≤ B ^ P) : 4 * ((d : ℝ) + 1) * (2 * t + 1) ≤ B ^ (P + 7) := by
  have hB1 : 1 ≤ B := by linarith
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have h16 : (16 : ℝ) ≤ B ^ 4 :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ B ^ 4 := pow_le_pow_left₀ (by norm_num) hB2 4
  calc 4 * ((d : ℝ) + 1) * (2 * t + 1) ≤ 4 * B * (4 * t) := by gcongr; linarith
    _ = 16 * B * t := by ring
    _ ≤ B ^ 4 * B * B ^ P := by gcongr
    _ = B ^ (P + 5) := by ring
    _ ≤ B ^ (P + 7) := pow_le_pow_right₀ hB1 (by omega)

theorem momC_le_pow (hB2 : 2 ≤ B) (hBd : (d : ℝ) + 1 ≤ B) (ht1 : 1 ≤ t)
    (htB : (t : ℝ) ≤ B ^ P) : momC d t ≤ B ^ ((P + 7) * (3 * t)) := by
  have hB1 : 1 ≤ B := by linarith
  unfold momC
  calc (4 * ((d : ℝ) + 1) * (2 * t + 1)) ^ (2 * t + 1) ≤ (B ^ (P + 7)) ^ (2 * t + 1) :=
        pow_le_pow_left₀ (by positivity) (base_le_pow hB2 hBd ht1 htB) _
    _ = B ^ ((P + 7) * (2 * t + 1)) := by rw [← pow_mul]
    _ ≤ B ^ ((P + 7) * (3 * t)) :=
        pow_le_pow_right₀ hB1 (Nat.mul_le_mul_left _ (by omega))

theorem bsq_le_pow (hw0 : 0 < w) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B) (hBd : (d : ℝ) + 1 ≤ B) :
    bsq d w ≤ B ^ (P + 7) := by
  have hB1 : 1 ≤ B := by linarith
  have h16 : (16 : ℝ) ≤ B ^ 4 :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ B ^ 4 := pow_le_pow_left₀ (by norm_num) hB2 4
  unfold bsq
  calc 9 * ((d : ℝ) + 1) ^ 2 / w = 9 * ((d : ℝ) + 1) ^ 2 * (1 / w) := by ring
    _ ≤ B ^ 4 * B ^ 2 * B := by
        gcongr
        linarith
    _ = B ^ 7 := by ring
    _ ≤ B ^ (P + 7) := pow_le_pow_right₀ hB1 (by omega)

theorem gstOf_le_pow (hw0 : 0 < w) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B) (hBd : (d : ℝ) + 1 ≤ B)
    (ht1 : 1 ≤ t) (htB : (t : ℝ) ≤ B ^ P) : gstOf d t w ≤ B ^ ((P + 7) * (4 * t)) := by
  have hB1 : 1 ≤ B := by linarith
  have hbase := base_le_pow hB2 hBd ht1 htB
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h2t : 2 * (t : ℝ) ≤ B ^ (P + 7) := le_trans (by nlinarith) hbase
  have hd1 : (d : ℝ) + 1 ≤ B ^ (P + 7) := le_trans (by nlinarith) hbase
  unfold gstOf
  calc (2 * (t : ℝ)) ^ (2 * t) * ((d : ℝ) + 1) ^ t * bsq d w ^ t ≤
        (B ^ (P + 7)) ^ (2 * t) * (B ^ (P + 7)) ^ t * (B ^ (P + 7)) ^ t := by
        have hb0 : 0 ≤ bsq d w := by unfold bsq; positivity
        gcongr
        exact bsq_le_pow hw0 hB2 hBw hBd
    _ = B ^ ((P + 7) * (4 * t)) := by
        simp only [← pow_mul, ← pow_add]
        ring_nf

theorem zOf_le_pow (hw0 : 0 < w) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B) (hBd : (d : ℝ) + 1 ≤ B)
    (ht1 : 1 ≤ t) (htB : (t : ℝ) ≤ B ^ P) : zOf d t w ≤ B ^ ((8 * P + 87) * t) := by
  have hB1 : 1 ≤ B := by linarith
  have h2 : (2 : ℝ) ^ 14 * 2 ^ (17 * t) ≤ B ^ (31 * t) :=
    calc (2 : ℝ) ^ 14 * 2 ^ (17 * t) = 2 ^ (14 + 17 * t) := by rw [pow_add]
      _ ≤ 2 ^ (31 * t) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ B ^ (31 * t) := pow_le_pow_left₀ (by norm_num) hB2 _
  have hm := momC_le_pow hB2 hBd ht1 htB
  have hb : bsq d w ^ t ≤ B ^ ((P + 7) * t) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by unfold bsq; positivity) (bsq_le_pow hw0 hB2 hBw hBd) t
  have hg := gstOf_le_pow hw0 hB2 hBw hBd ht1 htB
  have hm0 : 0 ≤ momC d t := by unfold momC; positivity
  have hb0 : 0 ≤ bsq d w ^ t := by unfold bsq; positivity
  have hg0 : 0 ≤ gstOf d t w := by unfold gstOf bsq; positivity
  unfold zOf
  calc (2 : ℝ) ^ 14 * 2 ^ (17 * t) * momC d t * bsq d w ^ t * gstOf d t w ≤
        B ^ (31 * t) * B ^ ((P + 7) * (3 * t)) * B ^ ((P + 7) * t) *
          B ^ ((P + 7) * (4 * t)) := by gcongr
    _ = B ^ ((8 * P + 87) * t) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        ring_nf

theorem failX_le_pow (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B) (hBd : (d : ℝ) + 1 ≤ B)
    (ht1 : 1 ≤ t) (htB : (t : ℝ) ≤ B ^ P) : failX d (2 * t) w ≤ B ^ ((P + 7) * (4 * t) + 1) := by
  have hB1 : 1 ≤ B := by linarith
  have hbase := base_le_pow hB2 hBd ht1 htB
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h4t : 2 * ((2 * t : ℕ) : ℝ) ≤ B ^ (P + 7) := by
    push_cast
    exact le_trans (by nlinarith) hbase
  have hd1 : (d : ℝ) + 1 ≤ B ^ (P + 7) := le_trans (by nlinarith) hbase
  have hprod : ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t) ≤
      B ^ ((P + 7) * (4 * t)) :=
    calc ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t) ≤
          (B ^ (P + 7)) ^ (2 * t) * (B ^ (P + 7)) ^ (2 * t) := by gcongr
      _ = B ^ ((P + 7) * (4 * t)) := by
          rw [← pow_mul, ← pow_add]
          ring_nf
  have h1 : 1 / w ≤ B ^ ((P + 7) * (4 * t)) :=
    hBw.trans (le_self_pow₀ hB1 (by positivity))
  unfold failX
  calc 1 / w + ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t) ≤
        2 * B ^ ((P + 7) * (4 * t)) := by linarith
    _ ≤ B * B ^ ((P + 7) * (4 * t)) := by gcongr
    _ = B ^ ((P + 7) * (4 * t) + 1) := by ring

/-- **The sample size as a power of `B`.** If `B ≥ 2`, `1/w ≤ B`, `d + 1 ≤ B`, `1/ε ≤ B^Kc` and
`1 ≤ t ≤ B^P`, then `2 Z² X / (ε³ w³) ≤ B^((20 P + 3 Kc + 207) t)`. -/
theorem sample_le_pow {ε : ℝ} {Kc : ℕ} (hw0 : 0 < w) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B)
    (hBd : (d : ℝ) + 1 ≤ B) (hε0 : 0 < ε) (hεB : 1 / ε ≤ B ^ Kc) (ht1 : 1 ≤ t)
    (htB : (t : ℝ) ≤ B ^ P) :
    2 * zOf d t w ^ 2 * failX d (2 * t) w / (ε ^ 3 * w ^ 3) ≤
      B ^ ((20 * P + 3 * Kc + 207) * t) := by
  have hB1 : 1 ≤ B := by linarith
  have hZ := zOf_le_pow hw0 hB2 hBw hBd ht1 htB
  have hX := failX_le_pow hB2 hBw hBd ht1 htB
  have hZ0 : 0 ≤ zOf d t w := by unfold zOf momC gstOf bsq; positivity
  have hX0 : 0 ≤ failX d (2 * t) w := by unfold failX; positivity
  have hεw : 2 / (ε ^ 3 * w ^ 3) ≤ B ^ (3 * Kc + 4) :=
    calc 2 / (ε ^ 3 * w ^ 3) = 2 * (1 / ε) ^ 3 * (1 / w) ^ 3 := by field_simp
      _ ≤ B * (B ^ Kc) ^ 3 * B ^ 3 := by gcongr
      _ = B ^ (3 * Kc + 4) := by rw [← pow_mul]; ring
  calc 2 * zOf d t w ^ 2 * failX d (2 * t) w / (ε ^ 3 * w ^ 3) =
        zOf d t w ^ 2 * failX d (2 * t) w * (2 / (ε ^ 3 * w ^ 3)) := by ring
    _ ≤ (B ^ ((8 * P + 87) * t)) ^ 2 * B ^ ((P + 7) * (4 * t) + 1) * B ^ (3 * Kc + 4) := by
        gcongr
    _ = B ^ (2 * ((8 * P + 87) * t) + ((P + 7) * (4 * t) + 1) + (3 * Kc + 4)) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        ring_nf
    _ ≤ B ^ ((20 * P + 3 * Kc + 207) * t) := by
        refine pow_le_pow_right₀ hB1 ?_
        have : 3 * Kc + 5 ≤ (3 * Kc + 5) * t := Nat.le_mul_of_pos_right _ ht1
        nlinarith

end Powers

/-! ### The model side of the analysis -/

/-- The hypotheses of the pseudo-expectation analysis (`BS23.Separating.PAHyp`) that only concern
the sample, for points `X` with labels `ℓ`: `X j = m (ℓ j) + ζ j`, a sum of squares `N` of degree
at most `2`, the per-cluster moment closeness of `ζ` with error `e` up to degree `2t`, the bound `G`
on the Gaussian moment polynomials, and cluster sizes at least `wmin n / 2`. -/
def ModelHyp {n d k : ℕ} (ℓ : Fin n → Fin k) (X : Fin n → Fin d → ℝ) (t : ℕ) (wmin e G : ℝ) :
    Prop :=
  ∃ (m : Fin k → Fin d → ℝ) (ζ : Fin n → Fin d → ℝ) (N : MvPolynomial (Fin d) ℝ),
    (∀ j, X j = m (ℓ j) + ζ j) ∧ IsSumSq N ∧ N.totalDegree ≤ 2 ∧
    (∀ c l, l ≤ 2 * t → coeffNorm1 (PA.clusterMom ℓ lin ζ c l - PA.gaussPow N l) ≤ e) ∧
    (∀ l, l ≤ 2 * t → coeffNorm1 (PA.gaussPow N l) ≤ G) ∧
    ∀ c, wmin / 2 * n ≤ ((cluster ℓ c).card : ℝ)

/-- **Transport of `ModelHyp`** along the length and the dimension of a list of points. -/
theorem modelHyp_transport {n d k : ℕ} (L : Points) (hn : L.length = n) (hd : dim L = d)
    {Y : Fin n → Fin d → ℝ}
    (hY : ∀ j a, Y j a = (Colinear.pointsFun L (Fin.cast hn.symm j) (Fin.cast hd.symm a) : ℝ))
    {ℓ : Fin n → Fin k} {t : ℕ} {wmin e G : ℝ} (h : ModelHyp ℓ (whiten Y) t wmin e G) :
    ModelHyp (fun j ↦ ℓ (Fin.cast hn j)) (whiten fun j a ↦ (Colinear.pointsFun L j a : ℝ)) t
      wmin e G := by
  subst hn hd
  have hY' : Y = fun j a ↦ (Colinear.pointsFun L j a : ℝ) :=
    funext fun j ↦ funext fun a ↦ hY j a
  subst hY'
  exact h

/-- `ModelHyp` for the real whitened points `BS23.Separating.xR x` of an input. -/
theorem modelHyp_xR {n d k : ℕ} (x : BipartitionInput) (hn : x.points.length = n)
    (hd : dim x.points = d) {Y : Fin n → Fin d → ℝ}
    (hY : ∀ j a, Y j a =
      (Colinear.pointsFun x.points (Fin.cast hn.symm j) (Fin.cast hd.symm a) : ℝ))
    {ℓ : Fin n → Fin k} {t : ℕ} {wmin e G : ℝ} (h : ModelHyp ℓ (whiten Y) t wmin e G) :
    ModelHyp (fun j ↦ ℓ (Fin.cast hn j)) (xR x) t wmin e G := by
  rw [xR_eq_whiten]
  exact modelHyp_transport x.points hn hd hY h

/-- `⟨A g, v⟩ = ∑ᵢ gᵢ ⟨A eᵢ, v⟩`, as linear forms. -/
theorem lin_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    lin (A *ᵥ g) = ∑ i, C (g i) * lin (fun l ↦ A l i) := by
  simp only [lin, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- `E Z^l ≤ q^q` for `l ≤ q`. -/
theorem gaussMom_le_pow {l q : ℕ} (hl : l ≤ q) : gaussMom l ≤ q ^ q := by
  unfold gaussMom
  split_ifs
  · exact (Nat.doubleFactorial_le_factorial _).trans
      ((Nat.factorial_le (by omega)).trans (Nat.factorial_le_pow q))
  · exact Nat.zero_le _

/-- **The model side on the good event.** On the good event of degree `2t` and accuracy `η`
(with `2η ≤ wmin ≤ 1`, `d ≤ n`) and under the covariance comparison CV1, the whitened rounded
points satisfy `ModelHyp` with `m = mc`, `ζ = zeta`, `N = ∑ᵢ φᵢ²` for the columns
`φᵢ = ⟨B eᵢ, v⟩` of `B`, the error `e = (2η/wmin + 1/n) (4 (d+1) (2t+1))^(2t+1) β^(2t)` and the
bound `G = (2t)^(2t) (d + 1)^t β^(2t)`, `β = 3 (d + 1) / √wmin`. -/
theorem modelHyp_of_goodNoise {k d n : ℕ} (M : Mixture k d) (hS : M.S.PosDef)
    {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hn : 0 < n) {wmin η : ℝ} (hwmin : 0 < wmin)
    (hw1 : wmin ≤ 1) (hw : ∀ c, wmin ≤ M.w c) {t : ℕ}
    (hG : GoodNoise M.w η (2 * t) (labels ω) (stdNoise M ω)) (hη1 : 2 * η ≤ 1)
    (hηw : 2 * η ≤ wmin) (hd : d ≤ n)
    (hcv : ∀ v, wmin / 4 * Colinear.quad M.S v ≤ Colinear.quad (Colinear.empCov (yt r ω)) v) :
    ModelHyp (labels ω) (whiten (yt r ω)) t wmin
      ((2 * η / wmin + 1 / n) * momC d t * bsq d wmin ^ t) (gstOf d t wmin) := by
  set φ : Fin d → MvPolynomial (Fin d) ℝ := fun i ↦ lin fun l ↦ Bm M r ω l i with hφ_def
  set β : ℝ := 3 * ((d : ℝ) + 1) / Real.sqrt wmin with hβ_def
  have hs0 : 0 < Real.sqrt wmin := Real.sqrt_pos.mpr hwmin
  have hs1 : Real.sqrt wmin ≤ 1 := by
    have := Real.sqrt_le_sqrt hw1
    rwa [Real.sqrt_one] at this
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβ1 : 1 ≤ β := by
    rw [hβ_def, le_div_iff₀ hs0]
    nlinarith
  have hβ0 : 0 ≤ β := by linarith
  have hβsq : β ^ 2 = bsq d wmin := by
    rw [hβ_def, bsq, div_pow, Real.sq_sqrt hwmin.le]
    ring
  have hβt : ∀ l, l ≤ 2 * t → β ^ l ≤ bsq d wmin ^ t := fun l hl ↦ by
    rw [← hβsq, ← pow_mul]
    exact pow_le_pow_right₀ hβ1 hl
  have hφ : ∀ i, coeffNorm1 (φ i) ≤ β := fun i ↦
    (coeffNorm1_lin_le _).trans (sum_abs_Bm_col_le hS.posSemidef hwmin hcv i)
  have hzeta : ∀ j, lin (zeta M r ω j) = ∑ i, C (ghat M r ω j i) * φ i := fun j ↦
    lin_mulVec _ _
  have hgauss : ∀ l, PA.gaussPow (∑ i, φ i ^ 2) l = aeval φ (gaussPoly l) := fun l ↦ by
    rw [aeval_gaussPoly]
    rfl
  have hmom : ∀ c l, PA.clusterMom (labels ω) lin (zeta M r ω) c l =
      aeval φ (empMom (cluster (labels ω) c) (ghat M r ω) l) := by
    intro c l
    rw [aeval_empMom]
    unfold PA.clusterMom
    simp only [hzeta]
  have hghat : ghat M r ω = stdNoise M ω + roundErr M r ω := funext (ghat_eq M r ω)
  have hε : ∀ j, ∑ i, roundErr M r ω j i ^ 2 ≤ 1 / (n : ℝ) ^ 2 := sum_sq_roundErr_le M hS hr ω
  have hη0 : 0 ≤ η := eta_nonneg_of_goodNoise hG (labels ω ⟨0, hn⟩)
  refine ⟨mc M r ω, zeta M r ω, ∑ i, φ i ^ 2, whiten_yt M hS r ω, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSumSq.sum fun i _ ↦ by rw [sq]; exact IsSumSq.mul_self _
  · exact (IsHomogeneous.sum _ _ _ fun i _ ↦ (isHomogeneous_lin _).pow 2).totalDegree_le
  · intro c l hl
    have hwc : 0 < M.w c := hwmin.trans_le (hw c)
    rw [hmom, hgauss, hghat]
    refine (coeffNorm1_aeval_empMom_sub_le hG c hwc hη1 (hηw.trans (hw c)) hd hε hl φ hβ0
      hφ).trans ?_
    have h1 : 2 * η / M.w c + 1 / n ≤ 2 * η / wmin + 1 / n := by
      gcongr
      exact hw c
    have hl' : (l : ℝ) ≤ 2 * t := by exact_mod_cast hl
    have h2 : (4 * ((d : ℝ) + 1) * (l + 1)) ^ (l + 1) ≤ momC d t := by
      unfold momC
      have hb1 : (1 : ℝ) ≤ 4 * ((d : ℝ) + 1) * (2 * t + 1) := by
        have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        nlinarith
      calc (4 * ((d : ℝ) + 1) * (l + 1)) ^ (l + 1) ≤
            (4 * ((d : ℝ) + 1) * (2 * t + 1)) ^ (l + 1) := by gcongr
        _ ≤ _ := pow_le_pow_right₀ hb1 (by omega)
    have h3 := hβt l hl
    have hm0 : 0 ≤ momC d t := by unfold momC; positivity
    have h5 : 0 ≤ 2 * η / wmin + 1 / n := by positivity
    exact mul_le_mul (mul_le_mul h1 h2 (by positivity) h5) h3 (by positivity)
      (mul_nonneg h5 hm0)
  · intro l hl
    rw [hgauss]
    refine (coeffNorm1_aeval_gaussPoly_le φ hβ0 hφ l).trans ?_
    unfold gstOf
    have h1 : (gaussMom l : ℝ) ≤ (2 * (t : ℝ)) ^ (2 * t) := by
      exact_mod_cast gaussMom_le_pow hl
    have h2 : (d : ℝ) ^ (l / 2) ≤ ((d : ℝ) + 1) ^ t :=
      (pow_le_pow_left₀ hd0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
    have h3 := hβt l hl
    gcongr
  · intro c
    have := wmin_mul_le_card_cluster hG hn hw hwmin.le hη1 c
    calc wmin / 2 * n = wmin * n / 2 := by ring
      _ ≤ _ := this

/-! ### The algorithm side of the analysis -/

/-- **The success probability over the coins.** For an input `x` with `n > 0` points and labels
`ℓ` satisfying `ModelHyp` (with `wmin = x.wmin`, `t = tDeg r x`), if the program is valid and the
error `e` is small, the pivot read from the coins gives a separating bipartition with probability
at least `1 - 100 δ - n / 2^b` over `m ≥ b` coins, `b = coinBits n Kc`, where `δ ≥ δ₁` is the
fraction of bad pairs. -/
theorem le_coinProb_sep {r Kc k : ℕ} (hr : 1 ≤ r) (x : BipartitionInput)
    (hn : 0 < x.points.length) (hw : 0 < x.wmin) (ℓ : Fin x.points.length → Fin k) {e G : ℝ}
    (hM : ModelHyp ℓ (xR x) (tDeg r x) (x.wmin : ℝ) e G)
    (hP : (progOf r x (Lg r x)).Valid)
    (he : (258 : ℝ) ^ tDeg r x * (3 * 4 ^ tDeg r x * G * e) ≤ 1 / 2)
    {δ : ℝ} (hδ : PA.delta1 r (sDeg x) (258 ^ tDeg r x) e ≤ δ) (hδ1 : δ ≤ 1 / 10000)
    {m : ℕ} (hm : coinBits x.points.length Kc ≤ m) :
    1 - 100 * δ - x.points.length / 2 ^ coinBits x.points.length Kc ≤
      coinProb m (fun c ↦ IsSeparatingBipartition ℓ (sepAlg r Kc (x, c))) := by
  obtain ⟨E, hE, -⟩ := alg_spec (Kc := Kc) hr [] (pow_le_Lg r x) (correct_outOf hP)
  obtain ⟨mm, ζ, N, hx, hN, hNdeg, hmc, hgl, hcard⟩ := hM
  have hPA : PAHyp ℓ (xR x) mm ζ lin r (sDeg x) (tDeg r x) E N (x.wmin : ℝ)
      (258 ^ tDeg r x) e G :=
    { x_eq := hx
      L_add := lin_add
      L_neg := lin_neg
      totalDegree_L_le := fun u ↦ (isHomogeneous_lin u).totalDegree_le
      one_le_r := hr
      one_le_s := one_le_sDeg x
      t_eq := rfl
      two_mul_t_le := le_rfl
      abs_E_le := hE.bound
      E_pair_lower := hE.low
      E_pair_upper := hE.high
      N_isSumSq := hN
      totalDegree_N_le := hNdeg
      mom_close := hmc
      gauss_le := hgl
      n_pos := hn
      wmin_pos := by exact_mod_cast hw
      one_le_wmin_mul := by
        rw [sDeg, Nat.add_sub_cancel]
        exact one_le_wmin_mul_two_pow_logInv hw
      card_ge := hcard
      small_e := he
      small_delta := hδ.trans hδ1 }
  obtain ⟨-, hsymm, htri, hτT, hδ', hsame, a, b, hab, ha, hb, hfar⟩ := hPA.rounding_hyps
  obtain ⟨Bad, hBad, hgood⟩ := isSeparatingBipartition_ofFn ℓ
    (fun i j ↦ PA.qf E lin (sDeg x) (xR x i - xR x j)) (by positivity) hsymm htri hτT hδ' hsame
    ha hb hfar
  have hcoin := le_coinProb_of_coinIdx hm hn Bad
    (P := fun c ↦ IsSeparatingBipartition ℓ (sepAlg r Kc (x, c))) (fun l _ p hp hpB ↦ by
      rw [sepAlg_eq, run_eq_of_solverPE hE p hp, cast_tau]
      exact hgood p hpB)
  have hn' : (0 : ℝ) < x.points.length := by exact_mod_cast hn
  have hB : (Bad.card : ℝ) / x.points.length ≤ 100 * δ := by
    rw [div_le_iff₀ hn']
    have h1 : 100 * PA.delta1 r (sDeg x) (258 ^ tDeg r x) e * x.points.length ≤
        100 * δ * x.points.length := by gcongr
    linarith
  linarith

/-! ### One good sample -/

/-- `BS23.IsSeparatingBipartition` is invariant under reindexing the sample along `n' = n`. -/
theorem isSeparatingBipartition_cast {n n' k : ℕ} (h : n' = n) (ℓ : Fin n → Fin k)
    (out : Output) :
    IsSeparatingBipartition (fun j : Fin n' ↦ ℓ (Fin.cast h j)) out ↔
      IsSeparatingBipartition ℓ out := by
  subst h
  rfl

/-- `momC d` is monotone. -/
theorem momC_mono (d : ℕ) {p t : ℕ} (hpt : p ≤ t) : momC d p ≤ momC d t := by
  unfold momC
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpt' : (p : ℝ) ≤ t := by exact_mod_cast hpt
  have hb1 : (1 : ℝ) ≤ 4 * ((d : ℝ) + 1) * (2 * t + 1) := by nlinarith
  calc (4 * ((d : ℝ) + 1) * (2 * p + 1)) ^ (2 * p + 1) ≤
        (4 * ((d : ℝ) + 1) * (2 * t + 1)) ^ (2 * p + 1) := by gcongr
    _ ≤ _ := pow_le_pow_right₀ hb1 (by omega)

/-- **The algorithm on one good sample.** On a sample in the good event of degree `2t`,
`t = r (L + 1)`, with accuracy `η` small enough (the numerical hypotheses), and with two
components at distance at least `128 t`, the algorithm outputs a separating bipartition with
probability at least `1 - 100 δ - n / 2^b` over `m ≥ b = coinBits n Kc` coins. -/
theorem le_coinProb_of_goodNoise {k d n : ℕ} (M : Mixture k d) (hS : M.S.PosDef)
    {rr : Rounding k d} (hrr : IsRounding M.S (1 / n) rr)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hn : 0 < n) {q wmin : ℚ} (hwmin : 0 < wmin)
    (hw1 : (wmin : ℝ) ≤ 1) (hw : ∀ c, (wmin : ℝ) ≤ M.w c) {r Kc t : ℕ} (hr : 1 ≤ r)
    (ht : t = r * (logInv wmin + 1)) {η : ℝ}
    (hG : GoodNoise M.w η (2 * t) (labels ω) (stdNoise M ω)) (hη1 : 2 * η ≤ 1)
    (hηw : 2 * η ≤ wmin) (hd : d ≤ n)
    (hcv : 2 * (η * ((d : ℝ) + 1) ^ 2) / wmin + 4 / n ≤ 1 / 8)
    (hfeas : (2 * η / wmin + 1 / n) * momC d t ≤ 1)
    {e : ℝ} (he_def : e = (2 * η / wmin + 1 / n) * momC d t * bsq d wmin ^ t)
    (he : (258 : ℝ) ^ t * (3 * 4 ^ t * gstOf d t wmin * e) ≤ 1 / 2)
    {δ : ℝ} (hδ : PA.delta1 r (logInv wmin + 1) (258 ^ t) e ≤ δ) (hδ1 : δ ≤ 1 / 10000)
    {a₀ b₀ : Fin k} (hsep : 128 * (t : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀))
    {m : ℕ} (hm : coinBits n Kc ≤ m) :
    1 - 100 * δ - n / 2 ^ coinBits n Kc ≤
      coinProb m (fun c ↦ IsSeparatingBipartition (labels ω)
        (sepAlg r Kc (⟨q, wmin, roundedSample rr ω⟩, c))) := by
  subst ht he_def
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  set t := r * (logInv wmin + 1) with ht_def
  have hst : logInv wmin + 1 ≤ t := Nat.le_mul_of_pos_left _ hr
  have ht1 : 1 ≤ t := (Nat.succ_pos _).trans_le hst
  have hcv' := quad_S_le_quad_empCov_yt_of_goodNoise M hS hrr hn hw0 hw (by omega) hη1 hcv hG
  have hC := empCov_yt_posDef M hS hw0 hcv'
  have hsize : ∀ c, (wmin : ℝ) * n / 2 ≤ ((cluster (labels ω) c).card : ℝ) := fun c ↦
    wmin_mul_le_card_cluster hG hn hw hw0.le hη1 c
  have hη0 : 0 ≤ η := eta_nonneg_of_goodNoise hG (labels ω ⟨0, hn⟩)
  have hmc : ∀ p, p ≤ t → ∀ c (b : Fin d → ℝ),
      |eval b (empMom (cluster (labels ω) c) (ghat M rr ω) (2 * p)) -
        gaussMom (2 * p) * (∑ i, b i ^ 2) ^ p| ≤ 1 * (∑ i, b i ^ 2) ^ p := fun p hp c b ↦
    ghat_momClose_of_goodNoise M hS hrr hG hw0 hw hη1 hηw hd (by omega)
      ((mul_le_mul_of_nonneg_left (momC_mono d hp) (by positivity)).trans hfeas) c b
  have ht' : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hst' : ((logInv wmin + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hst
  have hsep_s : 128 * ((sDeg ⟨q, wmin, roundedSample rr ω⟩ : ℕ) : ℝ) ≤
      sqNormIn M.S (M.μ a₀ - M.μ b₀) := by
    change 128 * ((logInv wmin + 1 : ℕ) : ℝ) ≤ _
    linarith
  have hsep_t : 16 * ((tDeg r ⟨q, wmin, roundedSample rr ω⟩ : ℕ) : ℝ) ≤
      sqNormIn M.S (M.μ a₀ - M.μ b₀) := by
    change 16 * ((t : ℕ) : ℝ) ≤ _
    linarith
  have hP : (progOf r ⟨q, wmin, roundedSample rr ω⟩ (Lg r ⟨q, wmin, roundedSample rr ω⟩)).Valid :=
    progOf_valid_of_sample M hS rr ω hn hC hwmin rfl hr le_rfl hsize (hmc _ hst) (hmc _ le_rfl)
      hsep_s hsep_t (pow_le_Lg r _)
  have hMod := modelHyp_of_goodNoise M hS hrr hn hw0 hw1 hw hG hη1 hηw hd hcv'
  have hY : ∀ j a, yt rr ω j a = (Colinear.pointsFun (roundedSample rr ω)
      (Fin.cast (length_roundedSample rr ω).symm j)
      (Fin.cast (dim_roundedSample rr ω hn).symm a) : ℝ) := by
    intro j a
    rw [pointsFun_roundedSample]
    rfl
  have hlen : (roundedSample rr ω).length = n := length_roundedSample rr ω
  have hMod' := modelHyp_xR ⟨q, wmin, roundedSample rr ω⟩ hlen (dim_roundedSample rr ω hn) hY
    hMod
  have hm' : coinBits (roundedSample rr ω).length Kc ≤ m := by rw [hlen]; exact hm
  have key := le_coinProb_sep (Kc := Kc) hr ⟨q, wmin, roundedSample rr ω⟩ (by rw [hlen]; exact hn)
    hwmin (fun j ↦ labels ω (Fin.cast hlen j)) hMod' hP he hδ hδ1 hm'
  have hfun : (fun c ↦ IsSeparatingBipartition (fun j ↦ labels ω (Fin.cast hlen j))
      (sepAlg r Kc (⟨q, wmin, roundedSample rr ω⟩, c))) =
      fun c ↦ IsSeparatingBipartition (labels ω)
        (sepAlg r Kc (⟨q, wmin, roundedSample rr ω⟩, c)) :=
    funext fun c ↦ propext (isSeparatingBipartition_cast hlen _ _)
  rw [hfun] at key
  simpa only [hlen] using key

/-! ### Auxiliary facts for the assembly -/

/-- Two distinct components force `2 wmin ≤ 1`. -/
theorem two_mul_wmin_le_one {k d : ℕ} {M : Mixture k d} (hM : M.Valid) {wmin : ℝ}
    (hw0 : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) {a b : Fin k} (hab : a ≠ b) : 2 * wmin ≤ 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ {a, b})
    (fun i _ _ ↦ hw0.le.trans (hw i))
  rw [sum_pair hab, hM.sum_w] at h
  linarith [hw a, hw b]

/-- `t = r (L + 1) ≤ B^(r + 3)` for `L = logInv wmin`, `B ≥ 2`, `B ≥ 1/wmin`. -/
theorem tDeg_le_pow {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) {B : ℝ} (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) (r : ℕ) :
    ((r * (logInv wmin + 1) : ℕ) : ℝ) ≤ B ^ (r + 3) := by
  have h1 : (logInv wmin : ℝ) + 1 ≤ B ^ 3 := by
    have h := Nat.lt_two_pow_self (n := logInv wmin)
    have h' : ((logInv wmin + 1 : ℕ) : ℝ) ≤ ((2 ^ logInv wmin : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'.trans (Colinear.two_pow_logInv_le_B hw hw1 hB2 hBw)
  have h2 : (r : ℝ) ≤ B ^ r := by
    have h := Nat.lt_two_pow_self (n := r)
    have h' : ((r : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast h.le
    push_cast at h'
    exact h'.trans (pow_le_pow_left₀ (by norm_num) hB2 r)
  push_cast
  calc (r : ℝ) * ((logInv wmin : ℝ) + 1) ≤ B ^ r * B ^ 3 := by gcongr
    _ = B ^ (r + 3) := by rw [pow_add]

/-- From the sample size `B^(C Λ) ≤ n` (a real power) to `B^N ≤ n` for `N ≤ C Λ`. -/
theorem pow_le_of_rpow_le {B Λ n : ℝ} {C N : ℕ} (hB : 1 ≤ B) (hN : (N : ℝ) ≤ C * Λ)
    (hn : B ^ ((C : ℝ) * Λ) ≤ n) : B ^ N ≤ n := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_le_rpow_of_exponent_le hB hN).trans hn

/-- The exponent `K t = K r (L + 1)` is at most `C (x + 1)` when `L + 1 ≤ 3 (x + 1)` and
`3 K r ≤ C`. -/
theorem exponent_le' {K r L C : ℕ} {x : ℝ} (hx : 0 ≤ x) (hL : (L : ℝ) + 1 ≤ 3 * (x + 1))
    (hC : 3 * K * r ≤ C) : ((K * (r * (L + 1)) : ℕ) : ℝ) ≤ C * (x + 1) := by
  have hC' : (3 * K * r : ℝ) ≤ C := by exact_mod_cast hC
  push_cast
  calc (K : ℝ) * (r * (L + 1)) = (K * r) * (L + 1) := by ring
    _ ≤ (K * r) * (3 * (x + 1)) := by gcongr
    _ = (3 * K * r) * (x + 1) := by ring
    _ ≤ C * (x + 1) := by gcongr

/-- The separation `C x ≥ 1152 r x` covers `128 t = 128 r (L + 1)` when `x ≥ 1/2` and
`L + 1 ≤ 3 (x + 1)`. -/
theorem sep_le {r L C : ℕ} {x D : ℝ} (hx : 1 / 2 ≤ x) (hL : (L : ℝ) + 1 ≤ 3 * (x + 1))
    (hC : 1152 * r ≤ C) (hD : C * x ≤ D) : 128 * ((r * (L + 1) : ℕ) : ℝ) ≤ D := by
  have hC' : (1152 * r : ℝ) ≤ C := by exact_mod_cast hC
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  push_cast
  calc 128 * ((r : ℝ) * (L + 1)) ≤ 128 * (r * (3 * (x + 1))) := by gcongr
    _ ≤ 1152 * r * x := by nlinarith
    _ ≤ C * x := by gcongr
    _ ≤ D := hD

/-- The pivot misses the bad set: `n / 2^b ≤ ε / 4` for `b = ⌈log₂ n⌉ + Kc`, `2^Kc ≥ 4/ε`. -/
theorem div_two_pow_coinBits_le {n Kc : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hK : 4 / ε ≤ (2 : ℝ) ^ Kc) : (n : ℝ) / 2 ^ coinBits n Kc ≤ ε / 4 := by
  unfold coinBits
  have h1 : (n : ℝ) ≤ 2 ^ Nat.clog 2 n := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) n
    exact_mod_cast this
  have h2 : 1 ≤ ε / 4 * 2 ^ Kc := by
    rw [div_le_iff₀ hε] at hK
    linarith
  rw [pow_add, div_le_iff₀ (by positivity)]
  calc (n : ℝ) ≤ 2 ^ Nat.clog 2 n * 1 := by rw [mul_one]; exact h1
    _ ≤ 2 ^ Nat.clog 2 n * (ε / 4 * 2 ^ Kc) := by gcongr
    _ = ε / 4 * (2 ^ Nat.clog 2 n * 2 ^ Kc) := by ring

/-- `C m^C` is monotone in `C`. -/
theorem mul_pow_self_mono {C C' : ℕ} (h : C ≤ C') (m : ℕ) : C * m ^ C ≤ C' * m ^ C' := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos C with rfl | hC
    · simp
    · rw [zero_pow hC.ne', zero_pow (by omega), mul_zero, mul_zero]
  · exact Nat.mul_le_mul h (Nat.pow_le_pow_right hm h)

/-- `bipartitionTime C` is monotone in `C`. -/
theorem bipartitionTime_mono {C C' : ℕ} (h : C ≤ C') (x : BipartitionInput) :
    bipartitionTime C x ≤ bipartitionTime C' x := by
  unfold bipartitionTime
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) h)
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (mul_pow_self_mono h _)))

/-- An encoded list is at least as long as the list. -/
theorem length_le_encList {α : Type} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (Encoding.encList enc l).length := by
  change l.length ≤ (l.flatMap (Encoding.frame ∘ enc)).length
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (Encoding.frame (enc a)).length := by simp [Encoding.frame]
    simp only [Function.comp_apply]
    omega

/-- The input is at least as long as its number of points. -/
theorem length_points_le (x : BipartitionInput) :
    x.points.length ≤ (encBipartitionInput x).length := by
  change x.points.length ≤
    (Encoding.frame (Encoding.encRat x.δ) ++ (Encoding.frame (Encoding.encRat x.wmin) ++
      Encoding.encList (Encoding.encList Encoding.encRat) x.points)).length
  rw [List.length_append, List.length_append]
  have := length_le_encList (Encoding.encList Encoding.encRat) x.points
  omega

/-- **The coins suffice**: `b = ⌈log₂ n⌉ + Kc ≤ bipartitionTime C x` for `Kc = kcR (rOf δ)` and
`C ≥ 400`, as `Kc ≤ 4R ≤ 400 ⌈1/δ⌉`. -/
theorem coinBits_le_time {C : ℕ} (hC : 400 ≤ C) (x : BipartitionInput) :
    coinBits x.points.length (kcR (rOf x.δ)) ≤ bipartitionTime C x := by
  set a := (encBipartitionInput x).length
  set m := ⌈1 / x.δ⌉₊
  set X := C * m ^ C * (logInv x.wmin + 1)
  have h1 : Nat.clog 2 x.points.length ≤ a := by
    refine Nat.clog_le_of_le_pow ((length_points_le x).trans ?_)
    exact (Nat.lt_two_pow_self (n := a)).le
  have h2 : kcR (rOf x.δ) ≤ 400 * m := by
    unfold kcR
    have : Nat.clog 2 (4 * rOf x.δ) ≤ 4 * rOf x.δ :=
      (Nat.clog_le_iff_le_pow (by norm_num)).2 Nat.lt_two_pow_self.le
    have := rOf_le_hundred_mul x.δ
    omega
  have h3 : 400 * m ≤ X :=
    calc 400 * m ≤ C * m ^ C := Nat.mul_le_mul hC (Nat.le_self_pow (by omega) m)
      _ ≤ X := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h4 : X + 1 ≤ (dim x.points + 2) ^ X :=
    (Nat.lt_two_pow_self (n := X)).trans_le (Nat.pow_le_pow_left (by omega) X)
  have h5 : a + 2 ≤ (a + 2) ^ C := Nat.le_self_pow (by omega) _
  unfold coinBits bipartitionTime
  calc Nat.clog 2 x.points.length + kcR (rOf x.δ) ≤ (a + 2) * (X + 1) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul h5 h4

/-- **The fraction of bad pairs**: `δ₁ ≤ ε / 400` for `r ≥ 2^41 / ε` and
`4 · 64^s · 4^s R e ≤ ε / 800`. -/
theorem delta1_le_of {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {r s : ℕ}
    (hr : 2 ^ 41 / ε ≤ (r : ℝ)) (hs : 1 ≤ s) {R e : ℝ}
    (h : 4 * 64 ^ s * (4 ^ s * R * e) ≤ ε / 800) : PA.delta1 r s R e ≤ ε / 400 := by
  unfold PA.delta1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
  have hq : 64 * (32800 / (r : ℝ)) ≤ ε / 2 ^ 19 := by
    rw [mul_div_assoc', div_le_div_iff₀ hr0 (by norm_num)]
    rw [div_le_iff₀ hε0] at hr
    linarith
  have hq1 : ε / 2 ^ 19 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    linarith
  have h1 : 4 * 64 ^ s * (32800 / (r : ℝ)) ^ s ≤ ε / 800 := by
    rw [mul_assoc, ← mul_pow]
    calc 4 * (64 * (32800 / (r : ℝ))) ^ s ≤ 4 * (ε / 2 ^ 19) ^ s := by gcongr
      _ ≤ 4 * (ε / 2 ^ 19) := by
          gcongr
          exact pow_le_of_le_one (by positivity) hq1 (by omega)
      _ ≤ ε / 800 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by norm_num) (by norm_num)]
          linarith
  calc 4 * 64 ^ s * ((32800 / (r : ℝ)) ^ s + 4 ^ s * R * e) =
        4 * 64 ^ s * (32800 / (r : ℝ)) ^ s + 4 * 64 ^ s * (4 ^ s * R * e) := by ring
    _ ≤ ε / 800 + ε / 800 := add_le_add h1 h
    _ = ε / 400 := by ring

/-! ### The success probability -/

/-- **The success probability** of an algorithm `A` that is `sepAlg r Kc` on the inputs
`⟨δ, wmin, ·⟩`, with a time bound `T` that leaves room for the coins of the pivot, for
`ε ≤ 1/100`, `r ≥ 2^41 / ε` and `2^Kc ≥ 4 / ε`, when the separation is at least
`Cs log (1/wmin)` and the sample size at least `((d + 1) / wmin)^(Cs (log (1/wmin) + 1))` with
`Cs ≥ max(1152 r, 3 K₁ r)`, `K₁ = 20 (r + 3) + 3 Kc + 207`: at least `1 - ε`. -/
theorem success_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) {r Kc Cs : ℕ} (hr1 : 1 ≤ r)
    (hr : 2 ^ 41 / ε ≤ (r : ℝ)) (hKc : 4 / ε ≤ (2 : ℝ) ^ Kc)
    (hC2 : 1152 * r ≤ Cs) (hC3 : 3 * (20 * (r + 3) + 3 * Kc + 207) * r ≤ Cs)
    {k d : ℕ} (M : Mixture k d) {δ wmin : ℚ} (hM : M.Valid) (hwmin : 0 < wmin)
    (hw : ∀ i, (wmin : ℝ) ≤ M.w i) {a₀ b₀ : Fin k} (hab : a₀ ≠ b₀)
    (hsep : Cs * Real.log (1 / (wmin : ℝ)) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀)) {n : ℕ}
    (hn : ((d + 1) / (wmin : ℝ)) ^ ((Cs : ℝ) * (Real.log (1 / (wmin : ℝ)) + 1)) ≤ n)
    (rr : Rounding k d) (hrr : IsRounding M.S (1 / n) rr)
    {A : BipartitionInput × List Bool → BS23.Output} {T : BipartitionInput → ℕ}
    (hA : ∀ pts c, A (⟨δ, wmin, pts⟩, c) = sepAlg r Kc (⟨δ, wmin, pts⟩, c))
    (hT : ∀ pts : Points, coinBits pts.length Kc ≤ T ⟨δ, wmin, pts⟩) :
    1 - ε ≤ successProb M n rr (fun pts ↦ ⟨δ, wmin, pts⟩) A T IsSeparatingBipartition := by
  -- the weights
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hw2 : 2 * (wmin : ℝ) ≤ 1 := two_mul_wmin_le_one hM hw0 hw hab
  have hw1 : (wmin : ℝ) ≤ 1 := by linarith
  have hw1q : wmin ≤ 1 := by exact_mod_cast hw1
  have hkw : (k : ℝ) ≤ 1 / wmin := by
    rw [le_div_iff₀ hw0]
    calc (k : ℝ) * wmin = ∑ _i : Fin k, (wmin : ℝ) := by simp
      _ ≤ ∑ i, M.w i := Finset.sum_le_sum fun i _ ↦ hw i
      _ = 1 := hM.sum_w
  -- `Λ = log (1/wmin)`
  have hiw : (2 : ℝ) ≤ 1 / wmin := by
    rw [le_div_iff₀ hw0]
    linarith
  have hΛ : 1 / 2 ≤ Real.log (1 / (wmin : ℝ)) := by
    have h1 := Real.log_le_log (by norm_num) hiw
    have h2 := Real.log_two_gt_d9
    linarith
  have hLΛ := Colinear.logInv_add_one_le hwmin hw1q
  -- `B = (d + 1) / wmin`
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hBw : 1 / (wmin : ℝ) ≤ ((d : ℝ) + 1) / wmin :=
    div_le_div_of_nonneg_right (by linarith) hw0.le
  have hB2 : 2 ≤ ((d : ℝ) + 1) / wmin := hiw.trans hBw
  have hBd : (d : ℝ) + 1 ≤ ((d : ℝ) + 1) / wmin := by
    rw [le_div_iff₀ hw0]
    nlinarith
  have hB1 : 1 ≤ ((d : ℝ) + 1) / wmin := by linarith
  -- the degree `t`
  set t := r * (logInv wmin + 1) with ht_def
  have hst : logInv wmin + 1 ≤ t := Nat.le_mul_of_pos_left _ hr1
  have ht1 : 1 ≤ t := (Nat.succ_pos _).trans_le hst
  have htB := tDeg_le_pow hwmin hw1q hB2 hBw r
  -- `ε`
  have hεB : 1 / ε ≤ (((d : ℝ) + 1) / wmin) ^ Kc := by
    have h1 : 1 / ε ≤ 4 / ε := div_le_div_of_nonneg_right (by norm_num) hε0.le
    exact (h1.trans hKc).trans (pow_le_pow_left₀ (by norm_num) hB2 Kc)
  -- the sample size
  set K₁ := 20 * (r + 3) + 3 * Kc + 207 with hK₁
  have hnB : (((d : ℝ) + 1) / wmin) ^ (K₁ * t) ≤ n :=
    pow_le_of_rpow_le hB1 (exponent_le' (by linarith) hLΛ hC3) hn
  have hN := sample_le_pow hw0 hB2 hBw hBd hε0 hεB ht1 htB
  have hdn : (d : ℝ) + 1 ≤ n :=
    (hBd.trans (le_self_pow₀ hB1 (Nat.mul_ne_zero (by omega) (by omega)))).trans hnB
  have hn0 : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
  have hd : d ≤ n := by exact_mod_cast (by linarith : (d : ℝ) ≤ n)
  -- the numerics
  have hX : 1 ≤ failX d (2 * t) wmin := by
    unfold failX
    have : 0 ≤ ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t) := by positivity
    linarith
  obtain ⟨hη0, hηw, hη1, -, hcv, hfeas, he, hδ, hfail⟩ :=
    numerics_abstract (η := ε * wmin / zOf d t wmin) hε0 (by linarith) hw0 hw1
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (d : ℝ) + 1)) (sq_le_momC d ht1)
      (one_le_pow₀ (one_le_bsq hw0 hw1)) (one_le_gstOf hw0 hw1 ht1) hX hst hkw rfl rfl
      (hN.trans hnB)
  have hδ' := delta1_le_of hε0 (by linarith) hr (Nat.succ_pos _) hδ
  have hsep' : 128 * (t : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀) := sep_le hΛ hLΛ hC2 hsep
  -- the good event
  refine le_trans ?_ (le_successProb_of_goodNoise hM hw0 hw hη0 hn0 (2 * t) rr
    (fun pts ↦ (⟨δ, wmin, pts⟩ : BipartitionInput)) A T IsSeparatingBipartition
    (p := 1 - ε / 2) (by linarith) ?_)
  · have hfail' : (k : ℝ) / (n * (ε * wmin / zOf d t wmin) ^ 2) *
        (1 / (wmin : ℝ) + ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t)) ≤
        ε / 2 := hfail
    have h1 : (1 - ε / 2) * (1 - ε / 2) ≤ (1 - ε / 2) * (1 - (k : ℝ) /
        (n * (ε * wmin / zOf d t wmin) ^ 2) *
        (1 / (wmin : ℝ) + ((d : ℝ) + 1) ^ (2 * t) * (2 * ((2 * t : ℕ) : ℝ)) ^ (2 * t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : (1 - ε / 2) * (1 - ε / 2) = 1 - ε + ε ^ 2 / 4 := by ring
    have h3 := sq_nonneg ε
    have h4 : 1 - ε ≤ (1 - ε / 2) * (1 - ε / 2) := by linarith
    exact h4.trans (h1.trans (le_of_eq (by push_cast; ring)))
  · intro ω hG
    have hm : coinBits n Kc ≤ T ⟨δ, wmin, roundedSample rr ω⟩ := by
      have h := hT (roundedSample rr ω)
      rwa [show (roundedSample rr ω).length = n from length_roundedSample rr ω] at h
    have h := le_coinProb_of_goodNoise M hM.posDef hrr hn0 (q := δ) hwmin hw1 hw hr1 rfl hG hη1
      hηw hd hcv hfeas rfl he hδ' (by linarith) hsep' hm
    have hc := div_two_pow_coinBits_le (n := n) hε0 hKc
    simp only [hA]
    exact le_trans (by linarith) h

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1** of [BS23] (full version: Theorem 4.2): the statement of
`BS23.separating_bipartition`. The algorithm is `BS23.Separating.sepAlgU`: on an input with
failure probability `δ > 0`, `BS23.Separating.sepAlg r Kc` with `r = 2^41 R`,
`Kc = ⌈log₂ (4R)⌉`, `R = max ⌈1/δ⌉ 100`. The constant is `C = C₀ + 2^106`, with `C₀` its time
constant. -/
theorem separating_bipartition_main :
    ∃ (A : BipartitionInput × List Bool → Output) (C : ℕ),
      RunsInTime encBipartitionInput encOutput A (bipartitionTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin δ : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        0 < δ →
        (∃ a b, a ≠ b ∧ C * ⌈1 / δ⌉₊ ^ C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ n : ℕ, ((d + 1) / (wmin : ℝ)) ^ (C * ⌈1 / δ⌉₊ ^ C * (Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - (δ : ℝ) ≤ successProb M n r (fun pts ↦ ⟨δ, wmin, pts⟩) A (bipartitionTime C)
            IsSeparatingBipartition := by
  obtain ⟨C₀, hC₀⟩ := sepAlgU_runsInTime
  refine ⟨sepAlgU, C₀ + 2 ^ 106,
    Colinear.runsInTime_mono hC₀ (bipartitionTime_mono (Nat.le_add_right _ _)), ?_⟩
  intro k d M wmin δ hM hwmin hw hδ hsep n hn rr hrr
  obtain ⟨a₀, b₀, hab, hD⟩ := hsep
  set C := C₀ + 2 ^ 106 with hC
  set m := ⌈1 / δ⌉₊ with hm
  set R := rOf δ with hR
  have hm1 : 1 ≤ m := one_le_ceil_inv hδ
  have hR100 : 100 ≤ R := hundred_le_rOf hδ
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  obtain ⟨h2, h3⟩ := params_le hm1 (rOf_le_hundred_mul δ) (by omega) (Nat.le_add_left _ _)
  have hCs : ((C * m ^ C : ℕ) : ℝ) = (C : ℝ) * (m : ℝ) ^ C := by push_cast; ring
  have hε0 : (0 : ℝ) < 1 / R := by positivity
  have hε1 : 1 / (R : ℝ) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hR100)
  have hr1 : 1 ≤ ratioR R := by
    unfold ratioR
    omega
  have h := success_bound (ε := 1 / (R : ℝ)) (Cs := C * m ^ C) hε0 hε1 hr1
    (div_inv_eq_ratioR R).le (div_inv_le_two_pow_kcR R) h2 h3 M hM hwmin hw hab
    (by rw [hCs]; exact hD) (by rw [hCs]; exact hn) rr hrr (A := sepAlgU) (T := bipartitionTime C)
    (fun pts c ↦ sepAlgU_of_pos (x := ⟨δ, wmin, pts⟩) hδ c)
    (fun pts ↦ coinBits_le_time (by omega) ⟨δ, wmin, pts⟩)
  have hRδ : 1 / (R : ℝ) ≤ δ := by
    have h1 := inv_le_rOf hδ
    have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    rw [div_le_iff₀ hR0]
    rw [div_le_iff₀ hδ'] at h1
    linarith
  linarith

end BS23.Separating
