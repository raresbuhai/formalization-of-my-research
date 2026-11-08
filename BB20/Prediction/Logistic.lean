module

public import BB20.Model
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The logistic loss and Bernoulli divergences

Facts about the logistic loss `l(t) = log(1 + e^{-t})` (`BB20.logLoss`) used in the proof of
[BB20, Theorem 12].

* `l` is `1`-Lipschitz and `l(0) = log 2`.
* The conditional risk `φ_p(t) = p l(t) + (1 - p) l(-t)` (`BB20.Prediction.condRisk`), the
  expected loss of the score `t` when the label is `+1` with probability `p`, equals
  `A(t) - p t` with `A(t) = log(1 + eᵗ)` (`BB20.Prediction.softplus`). For `p = σ(a)`, the excess
  `φ_p(t) - φ_p(a)` is the Bernoulli divergence `KL(σ(a) ‖ σ(t))`.
* **Pinsker's inequality** for Bernoulli laws: `2 (σ(a) - σ(t))² ≤ φ_{σ(a)}(t) - φ_{σ(a)}(a)`
  (`BB20.Prediction.pinsker`).
* **Smoothness**: `φ_{σ(a)}(t) - φ_{σ(a)}(a) ≤ (t - a)² / 8` (`BB20.Prediction.condRisk_sub_le`),
  since `σ' = σ (1 - σ) ≤ 1/4`.

Both inequalities say that a function vanishing at `a` is nonnegative, because its derivative has
the sign of `t - a` (`BB20.Prediction.nonneg_of_hasDerivAt`).
-/

@[expose] public section

namespace BB20.Prediction

open Real

/-- The softplus function `A(t) = log(1 + eᵗ)`, so that `l(t) = A(-t)`. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- The conditional risk `φ_p(t) = p l(t) + (1 - p) l(-t)`: the expected logistic loss of the
score `t` for a label that is `+1` with probability `p` and `-1` otherwise. -/
noncomputable def condRisk (p t : ℝ) : ℝ := p * logLoss t + (1 - p) * logLoss (-t)

theorem sigmoid_eq (t : ℝ) : BB20.sigmoid t = Real.sigmoid t := by
  rw [BB20.sigmoid, Real.sigmoid_def, one_div]

theorem logLoss_eq (t : ℝ) : logLoss t = softplus (-t) := rfl

theorem softplus_neg (t : ℝ) : softplus (-t) = softplus t - t := by
  unfold softplus
  have h : 1 + exp t = exp t * (1 + exp (-t)) := by
    rw [mul_add, mul_one, ← exp_add, add_neg_cancel, exp_zero, add_comm]
  rw [h, log_mul (exp_pos _).ne' (by positivity), log_exp]
  ring

theorem condRisk_eq (p t : ℝ) : condRisk p t = softplus t - p * t := by
  unfold condRisk
  rw [logLoss_eq, logLoss_eq, neg_neg, softplus_neg]
  ring

theorem logLoss_zero : logLoss 0 = Real.log 2 := by
  norm_num [logLoss]

theorem softplus_mono {a b : ℝ} (h : a ≤ b) : softplus a ≤ softplus b :=
  log_le_log (by positivity) (by gcongr)

/-- The logistic loss is `1`-Lipschitz. -/
theorem abs_logLoss_sub_le (a b : ℝ) : |logLoss a - logLoss b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this b a (le_of_not_ge hab)
  have h1 : logLoss b ≤ logLoss a := softplus_mono (neg_le_neg hab)
  have h2 : logLoss a + a ≤ logLoss b + b := by
    rw [logLoss_eq, logLoss_eq, softplus_neg, softplus_neg]
    simpa using softplus_mono hab
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  linarith

theorem hasDerivAt_softplus (t : ℝ) : HasDerivAt softplus (Real.sigmoid t) t := by
  have h : HasDerivAt softplus (exp t / (1 + exp t)) t :=
    ((hasDerivAt_exp t).const_add 1).log (by positivity)
  convert h using 1
  rw [sigmoid_def, exp_neg]
  field_simp
  ring

theorem sigmoid_mul_one_sub_le (t : ℝ) : Real.sigmoid t * (1 - Real.sigmoid t) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (Real.sigmoid t - 1 / 2)]

/-- A function with a derivative of the sign of `t - a` is minimal at `a`. -/
theorem nonneg_of_hasDerivAt {h h' : ℝ → ℝ} {a : ℝ} (hd : ∀ t, HasDerivAt h (h' t) t)
    (ha : h a = 0) (hpos : ∀ t, a < t → 0 ≤ h' t) (hneg : ∀ t, t < a → h' t ≤ 0) (t : ℝ) :
    0 ≤ h t := by
  have hc : Continuous h := continuous_iff_continuousAt.2 fun x ↦ (hd x).continuousAt
  rcases le_or_gt a t with hat | hta
  · have hm : MonotoneOn h (Set.Ici a) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a) hc.continuousOn
        (fun x _ ↦ (hd x).hasDerivWithinAt) (fun x hx ↦ by
          rw [interior_Ici] at hx
          exact hpos x hx)
    have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hat) hat
    linarith
  · have hm : AntitoneOn h (Set.Iic a) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic a) hc.continuousOn
        (fun x _ ↦ (hd x).hasDerivWithinAt) (fun x hx ↦ by
          rw [interior_Iic] at hx
          exact hneg x hx)
    have := hm (Set.mem_Iic.2 hta.le) (Set.mem_Iic.2 le_rfl) hta.le
    linarith

/-- `t ↦ t / 4 - σ(t)` is monotone: `σ` is `1/4`-Lipschitz. -/
theorem monotone_quarter_sub_sigmoid : Monotone fun t ↦ t / 4 - Real.sigmoid t :=
  monotone_of_hasDerivAt_nonneg (f' := fun t ↦ 1 / 4 - Real.sigmoid t * (1 - Real.sigmoid t))
    (fun t ↦ ((hasDerivAt_id' t).div_const 4).sub (hasDerivAt_sigmoid t))
    (fun t ↦ by simpa using sigmoid_mul_one_sub_le t)

/-- **Smoothness** of the conditional risk: `KL(σ(a) ‖ σ(t)) ≤ (t - a)² / 8`. -/
theorem condRisk_sub_le (a t : ℝ) :
    condRisk (Real.sigmoid a) t - condRisk (Real.sigmoid a) a ≤ (t - a) ^ 2 / 8 := by
  set p := Real.sigmoid a
  have hd : ∀ s, HasDerivAt
      (fun s ↦ (s - a) ^ 2 / 8 - (softplus s - p * s - (softplus a - p * a)))
      ((s / 4 - Real.sigmoid s) - (a / 4 - Real.sigmoid a)) s := by
    intro s
    have h1 := (((hasDerivAt_id' s).sub_const a).pow 2).div_const 8
    have h2 := ((hasDerivAt_softplus s).sub ((hasDerivAt_id' s).const_mul p)).sub_const
      (softplus a - p * a)
    convert h1.sub h2 using 1
    simp only [p]
    push_cast
    ring
  have := nonneg_of_hasDerivAt hd (by simp)
    (fun s hs ↦ sub_nonneg.2 (monotone_quarter_sub_sigmoid hs.le))
    (fun s hs ↦ sub_nonpos.2 (monotone_quarter_sub_sigmoid hs.le)) t
  rw [condRisk_eq, condRisk_eq]
  linarith

/-- **Pinsker's inequality** for Bernoulli laws: `2 (σ(a) - σ(t))² ≤ KL(σ(a) ‖ σ(t))`. -/
theorem pinsker (a t : ℝ) :
    2 * (Real.sigmoid a - Real.sigmoid t) ^ 2 ≤
      condRisk (Real.sigmoid a) t - condRisk (Real.sigmoid a) a := by
  set p := Real.sigmoid a
  have hd : ∀ s, HasDerivAt
      (fun s ↦ softplus s - p * s - (softplus a - p * a) - 2 * (p - Real.sigmoid s) ^ 2)
      ((Real.sigmoid s - p) * (1 - 4 * (Real.sigmoid s * (1 - Real.sigmoid s)))) s := by
    intro s
    have h1 := ((hasDerivAt_softplus s).sub ((hasDerivAt_id' s).const_mul p)).sub_const
      (softplus a - p * a)
    have h2 := (((hasDerivAt_sigmoid s).const_sub p).pow 2).const_mul 2
    convert h1.sub h2 using 1
    push_cast
    ring
  have hq : ∀ s, 0 ≤ 1 - 4 * (Real.sigmoid s * (1 - Real.sigmoid s)) := fun s ↦ by
    nlinarith [sq_nonneg (2 * Real.sigmoid s - 1)]
  have := nonneg_of_hasDerivAt hd (by simp [p])
    (fun s hs ↦ mul_nonneg (sub_nonneg.2 (Real.sigmoid_le hs.le)) (hq s))
    (fun s hs ↦ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (Real.sigmoid_le hs.le)) (hq s)) t
  rw [condRisk_eq, condRisk_eq]
  linarith

end BB20.Prediction
