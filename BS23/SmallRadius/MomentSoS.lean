module

public import BS23.SmallRadius.Frame
public import BS23.Separating.MomentClose
public import Background.SumOfSquares.PowerSOS

/-!
# Moment inequalities in the standard frame

Sum-of-squares inequalities for the moments of the standard points of a good frame
(`BS23.SmallRadius.SRFrame.Good`), as polynomials in `d` variables `X_a`. Write `p ≼ q` when
`q - p` is a sum of squares. Notation: `lin u = ∑ₐ uₐ Xₐ` (`BS23.Separating.lin`),
`nsq d = ∑ₐ Xₐ²` (`BS23.SmallRadius.nsq`), `S_c` the cluster `c`, `ζ_j = m_{ℓ_j} + g_j + e_j`
the standard points, and

  `B_std = (1 / (n t^t)) ∑_j lin(ζ_j)^(2t)` (`BS23.SmallRadius.SRFrame.Bstd`),

the polynomial whose substitution `B_std(Gᵀ v)` is the scale estimate `B̃(v)` of the algorithm.

* **(E1) The noise polynomial** (`BS23.SmallRadius.SRFrame.Good.noise_poly`): for `p ≤ 2t`,
  `∑_{j ∈ S_c} lin(g_j)^p = |S_c| · gaussMom p · nsq^(p/2) + n · Err` with `Err` homogeneous of
  degree `p` and `‖Err‖₁ ≤ τ_p (d+1)^p`. The error is `BS23.SmallRadius.SRFrame.noiseErr`: by the
  multinomial theorem (`BS23.SmallRadius.sum_lin_pow_sub_eq`) its coefficients are the deviations
  `(1/n) ∑_{j ∈ S_c} g_j^α - (|S_c|/n) m_α` of the good event of degree `p`, weighted by
  multinomial coefficients summing to `d^p`.
* **(E2) Cluster moments** (`BS23.SmallRadius.SRFrame.Good.cluster_moment_sos`):
  `∑_{j ∈ S_c} lin(g_j + e_j)^(2s) ≼ |S_c| (8s)^s nsq^s`. Power mean for two terms, E1 and the
  coefficient-norm bound `SoS.isSumSq_l1` for the noise, and `lin(e)^(2s) ≼ (4/n²)^s nsq^s`
  (Cauchy–Schwarz and powers, `BS23.SmallRadius.isSumSq_lin_pow_le`).
* **(E3) Upper scale bound** (`BS23.SmallRadius.SRFrame.Good.covEst_upper`):
  `B_std ≼ 32^t nsq^t`. Power mean for three terms, `lin(m_c)^(2t) ≼ (R²)^t nsq^t`, E1 for the
  noise and `(2t-1)‼ ≤ (2t)^t`; the constant obtained is `18^t`.
* **(E4) Lower scale bound** (`BS23.SmallRadius.SRFrame.Good.covEst_lower`):
  `16^(-t) nsq^t ≼ B_std`. `lin(x + e)^(2t) ≽ 2^(1-2t) lin(x)^(2t) - lin(e)^(2t)`, and per cluster
  the binomial expansion of `(lin g_j + lin m_c)^(2t)` with E1 in every degree
  (`BS23.SmallRadius.SRFrame.Good.cluster_lower`): the Gaussian part is a sum of squares at least
  `|S_c| (2t-1)‼ nsq^t`, and the error part is homogeneous of degree `2t` with
  `‖·‖₁ ≤ n w 256^(-t) (√(2t) + R)^(2t) ≤ n w (9t/512)^t`. Then `(2t-1)‼ ≥ t! ≥ (t/3)^t`.

The polynomials compared are all homogeneous (`BS23.SmallRadius.SRFrame.isHomogeneous_Bstd`,
`BS23.SmallRadius.isHomogeneous_sum_lin_pow`, `BS23.SmallRadius.isHomogeneous_C_mul_nsq_pow_sub`),
so the squares in the certificates have degree at most `s` or `t`
(`SoS.two_mul_totalDegree_le`). Sums of even powers grow with the index set
(`BS23.SmallRadius.isSumSq_sum_lin_pow_sub_of_subset`).
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial Finset SoS
open BS23.Separating (lin lin_add isHomogeneous_lin coeffNorm1_lin_le eval_lin)
open scoped Nat

variable {n d k : ℕ}

/-! ### The squared norm polynomial and comparisons -/

/-- The squared norm `∑ₐ Xₐ²` of the standard frame's variables. -/
noncomputable def nsq (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ a, X a ^ 2

theorem isSumSq_nsq (d : ℕ) : IsSumSq (nsq d) :=
  IsSumSq.sum fun _ _ ↦ isSumSq_sq _

theorem isSumSq_nsq_pow (d m : ℕ) : IsSumSq (nsq d ^ m) := isSumSq_pow (isSumSq_nsq d) m

theorem isHomogeneous_nsq (d : ℕ) : (nsq d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun a _ ↦ isHomogeneous_X_pow a 2

theorem isHomogeneous_nsq_pow (d m : ℕ) : (nsq d ^ m).IsHomogeneous (2 * m) := by
  simpa [mul_comm] using (isHomogeneous_nsq d).pow m

/-- `C a · Q ≼ C b · Q` for `a ≤ b` and `Q` a sum of squares. -/
theorem isSumSq_C_mul_sub_C_mul {a b : ℝ} (hab : a ≤ b) {Q : MvPolynomial (Fin d) ℝ}
    (hQ : IsSumSq Q) : IsSumSq (C b * Q - C a * Q) := by
  rw [← sub_mul, ← C_sub]
  exact isSumSq_C_mul (by linarith) hQ

/-- Adding comparisons. -/
theorem isSumSq_add_sub_add {x₁ x₂ y₁ y₂ : MvPolynomial (Fin d) ℝ} (h₁ : IsSumSq (y₁ - x₁))
    (h₂ : IsSumSq (y₂ - x₂)) : IsSumSq (y₁ + y₂ - (x₁ + x₂)) := by
  have h := h₁.add h₂
  rwa [show y₁ - x₁ + (y₂ - x₂) = y₁ + y₂ - (x₁ + x₂) by ring] at h

/-- Summing comparisons. -/
theorem isSumSq_sum_sub_sum {ι : Type*} (s : Finset ι) {x y : ι → MvPolynomial (Fin d) ℝ}
    (h : ∀ i ∈ s, IsSumSq (y i - x i)) : IsSumSq (∑ i ∈ s, y i - ∑ i ∈ s, x i) := by
  rw [← sum_sub_distrib]
  exact IsSumSq.sum h

/-- Scaling comparisons by a nonnegative constant. -/
theorem isSumSq_C_mul_sub {c : ℝ} (hc : 0 ≤ c) {x y : MvPolynomial (Fin d) ℝ}
    (h : IsSumSq (y - x)) : IsSumSq (C c * y - C c * x) := by
  rw [← mul_sub]
  exact isSumSq_C_mul hc h

/-- Summing upper bounds `P i ≼ C (a i) Q`. -/
theorem isSumSq_sum_C_mul_sub {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Fin d) ℝ}
    {a : ι → ℝ} {Q : MvPolynomial (Fin d) ℝ} (h : ∀ i ∈ s, IsSumSq (C (a i) * Q - P i)) :
    IsSumSq (C (∑ i ∈ s, a i) * Q - ∑ i ∈ s, P i) := by
  have := isSumSq_sum_sub_sum s h
  rwa [← sum_mul, ← map_sum] at this

/-- Summing lower bounds `C (a i) Q ≼ P i`. -/
theorem isSumSq_sum_sub_C_mul {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Fin d) ℝ}
    {a : ι → ℝ} {Q : MvPolynomial (Fin d) ℝ} (h : ∀ i ∈ s, IsSumSq (P i - C (a i) * Q)) :
    IsSumSq (∑ i ∈ s, P i - C (∑ i ∈ s, a i) * Q) := by
  have := isSumSq_sum_sub_sum s h
  rwa [← sum_mul, ← map_sum] at this

/-! ### Linear forms -/

/-- `lin(u)² ≼ ‖u‖² nsq` (Cauchy–Schwarz). -/
theorem isSumSq_lin_sq_le (u : Fin d → ℝ) :
    IsSumSq (C (u ⬝ᵥ u) * nsq d - lin u ^ 2) := by
  have h := isSumSq_lagrange (univ : Finset (Fin d)) (fun a ↦ C (u a)) X
  have e : ∑ a, (C (u a) : MvPolynomial (Fin d) ℝ) ^ 2 = C (u ⬝ᵥ u) := by
    simp only [dotProduct, map_sum, map_mul, sq]
  rwa [e] at h

/-- `lin(u)^(2m) ≼ B^m nsq^m` for `‖u‖² ≤ B`. -/
theorem isSumSq_lin_pow_le {u : Fin d → ℝ} {B : ℝ} (hu : u ⬝ᵥ u ≤ B) (m : ℕ) :
    IsSumSq (C (B ^ m) * nsq d ^ m - lin u ^ (2 * m)) := by
  have h1 : IsSumSq (C B * nsq d - lin u ^ 2) :=
    isSumSq_sub_trans (isSumSq_lin_sq_le u) (isSumSq_C_mul_sub_C_mul hu (isSumSq_nsq d))
  have h2 := isSumSq_pow_sub_pow (isSumSq_sq (lin u)) h1 m
  rwa [mul_pow, ← C_pow, ← pow_mul] at h2

theorem isHomogeneous_lin_pow (u : Fin d → ℝ) (m : ℕ) : (lin u ^ m).IsHomogeneous m := by
  simpa using (isHomogeneous_lin u).pow m

theorem isHomogeneous_sum_lin_pow {ι : Type*} (S : Finset ι) (a : ι → Fin d → ℝ) (m : ℕ) :
    (∑ j ∈ S, lin (a j) ^ m).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun j _ ↦ isHomogeneous_lin_pow (a j) m

/-- The comparisons with `C a · nsq^m` are homogeneous: `C a · nsq^m - P` and `P - C a · nsq^m`
for `P` homogeneous of degree `2m` (so their squares have degree at most `m`). -/
theorem isHomogeneous_C_mul_nsq_pow_sub {P : MvPolynomial (Fin d) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous (2 * m)) (a : ℝ) :
    (C a * nsq d ^ m - P).IsHomogeneous (2 * m) ∧ (P - C a * nsq d ^ m).IsHomogeneous (2 * m) :=
  ⟨((isHomogeneous_nsq_pow d m).C_mul a).sub hP, hP.sub ((isHomogeneous_nsq_pow d m).C_mul a)⟩

/-- Sums of even powers over a larger set are larger: `∑_{j ∈ T} lin(a_j)^(2m) ≼
∑_{j ∈ S} lin(a_j)^(2m)` for `T ⊆ S`. -/
theorem isSumSq_sum_lin_pow_sub_of_subset {ι : Type*} {T S : Finset ι} (hTS : T ⊆ S)
    (a : ι → Fin d → ℝ) (m : ℕ) :
    IsSumSq (∑ j ∈ S, lin (a j) ^ (2 * m) - ∑ j ∈ T, lin (a j) ^ (2 * m)) := by
  classical
  rw [← sum_sdiff hTS, add_sub_cancel_right]
  exact IsSumSq.sum fun j _ ↦ by rw [pow_mul']; exact isSumSq_sq _

/-! ### (E1) The noise polynomial -/

/-- **The multinomial expansion** of the moments of linear forms minus the Gaussian ones:
`∑_{j ∈ S} lin(a_j)^p - |S| · gaussMom p · nsq^(p/2) =
∑_{|α| = p} (p; α) (∑_{j ∈ S} a_j^α - |S| m_α) X^α`. -/
theorem sum_lin_pow_sub_eq (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (p : ℕ) :
    ∑ j ∈ S, lin (a j) ^ p - C ((S.card : ℝ) * gaussMom p) * nsq d ^ (p / 2) =
      ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
        ((Nat.multinomial univ α : ℝ) *
          (∑ j ∈ S, ∏ i, a j i ^ α i - (S.card : ℝ) * gaussMomMulti α)) •
          ∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i := by
  apply MvPolynomial.funext
  intro b
  simp only [map_sub, map_sum, map_mul, map_pow, eval_C, nsq, eval_X, smul_eval, map_prod,
    eval_lin]
  rw [mul_assoc, BS23.Separating.gaussMom_mul_pow_div_two, ← sum_multinomial_gaussMomMulti]
  simp_rw [sum_pow_eq_sum_piAntidiag, mul_pow, prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have h : ∑ j ∈ S, (Nat.multinomial univ α : ℝ) * ((∏ i, a j i ^ α i) * ∏ i, b i ^ α i) =
      (Nat.multinomial univ α : ℝ) * (∑ j ∈ S, ∏ i, a j i ^ α i) * ∏ i, b i ^ α i := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h]
  ring

/-! ### Double factorials and tolerances -/

theorem doubleFactorial_le_two_mul_pow (t : ℕ) : (2 * t - 1)‼ ≤ (2 * t) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, Nat.doubleFactorial_add_one]
    calc (2 * t + 1) * (2 * t - 1)‼ ≤ (2 * (t + 1)) * (2 * t) ^ t :=
          Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (t + 1)) * (2 * (t + 1)) ^ t :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (2 * (t + 1)) ^ (t + 1) := by ring

theorem factorial_le_doubleFactorial (t : ℕ) : t ! ≤ (2 * t - 1)‼ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, Nat.doubleFactorial_add_one,
      Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

/-- `(t/3)^t ≤ t!`, from `t^t / t! ≤ e^t`. -/
theorem pow_le_three_pow_mul_factorial (t : ℕ) : (t : ℝ) ^ t ≤ 3 ^ t * t ! := by
  have h := Real.pow_div_factorial_le_exp (t : ℝ) (Nat.cast_nonneg t) t
  have he : Real.exp t ≤ 3 ^ t := by
    rw [show (t : ℝ) = t * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le t
  have hf : (0 : ℝ) < t ! := by exact_mod_cast Nat.factorial_pos t
  rw [div_le_iff₀ hf] at h
  nlinarith

/-- `(t/3)^t ≤ (2t-1)‼ = E Z^(2t)`. -/
theorem pow_le_three_pow_mul_gaussMom (t : ℕ) :
    (t : ℝ) ^ t ≤ 3 ^ t * (gaussMom (2 * t) : ℝ) := by
  rw [gaussMom_two_mul]
  have h : ((t ! : ℕ) : ℝ) ≤ ((2 * t - 1)‼ : ℕ) := by exact_mod_cast factorial_le_doubleFactorial t
  have := pow_le_three_pow_mul_factorial t
  have h3 : (0 : ℝ) ≤ 3 ^ t := by positivity
  nlinarith

/-- `E Z^(2t) = (2t-1)‼ ≤ (2t)^t`. -/
theorem gaussMom_le (t : ℕ) : (gaussMom (2 * t) : ℝ) ≤ (2 * (t : ℝ)) ^ t := by
  rw [gaussMom_two_mul]
  exact_mod_cast doubleFactorial_le_two_mul_pow t

theorem sqrt_two_mul_pow_two_mul (s : ℕ) :
    Real.sqrt (((2 * s : ℕ) : ℝ) ^ (2 * s)) = (2 * (s : ℝ)) ^ s := by
  rw [pow_mul', Real.sqrt_sq (by positivity)]
  push_cast
  ring

/-- `τ_r (d+1)^r ((d+1) ρ)^(2t-r) = w 256^(-t) √(r^r) ρ^(2t-r)` for `r ≤ 2t`. -/
theorem τ_mul_pow_mul_pow (w : ℝ) (d t r : ℕ) (ρ : ℝ) (hr : r ≤ 2 * t) :
    τ w d t r * ((d : ℝ) + 1) ^ r * (((d : ℝ) + 1) * ρ) ^ (2 * t - r) =
      w * (1 / 256) ^ t * Real.sqrt ((r : ℝ) ^ r) * ρ ^ (2 * t - r) := by
  have h : τ w d t r * ((d : ℝ) + 1) ^ (2 * t) = w * (1 / 256) ^ t * Real.sqrt ((r : ℝ) ^ r) := by
    have hA : ((d : ℝ) + 1) ^ (2 * t) ≠ 0 := by positivity
    unfold τ
    field_simp
  set A : ℝ := (d : ℝ) + 1
  have e : A ^ r * A ^ (2 * t - r) = A ^ (2 * t) := by rw [← pow_add, Nat.add_sub_cancel' hr]
  calc τ w d t r * A ^ r * (A * ρ) ^ (2 * t - r)
      = τ w d t r * (A ^ r * A ^ (2 * t - r)) * ρ ^ (2 * t - r) := by rw [mul_pow]; ring
    _ = τ w d t r * A ^ (2 * t) * ρ ^ (2 * t - r) := by rw [e]
    _ = _ := by rw [h]

/-- `τ_r (d+1)^r ≤ w 256^(-t) √(r^r)` for `r ≤ 2t`. -/
theorem τ_mul_pow_le {w : ℝ} (hw : 0 ≤ w) (d t r : ℕ) (hr : r ≤ 2 * t) :
    τ w d t r * ((d : ℝ) + 1) ^ r ≤ w * (1 / 256) ^ t * Real.sqrt ((r : ℝ) ^ r) := by
  have h := τ_mul_pow_mul_pow w d t r 1 hr
  rw [mul_one, one_pow, mul_one] at h
  have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * t - r) :=
    one_le_pow₀ (by linarith [d.cast_nonneg (α := ℝ)])
  have h0 : 0 ≤ τ w d t r * ((d : ℝ) + 1) ^ r := by unfold τ; positivity
  nlinarith

/-- `∑_{r ≤ 2t} C(2t, r) τ_r (d+1)^r ((d+1) ρ)^(2t-r) ≤ w 256^(-t) (9t/2)^t` for `ρ² ≤ t/4`:
the summands are `w 256^(-t) C(2t, r) √(r^r) ρ^(2t-r) ≤ w 256^(-t) C(2t, r) √(2t)^r ρ^(2t-r)`, and
`(√(2t) + ρ)² ≤ 4t + 2ρ² ≤ 9t/2`. -/
theorem sum_τ_binom_le {w ρ : ℝ} (hw : 0 ≤ w) (hρ : 0 ≤ ρ) (d t : ℕ) (hρt : ρ ^ 2 ≤ t / 4) :
    ∑ r ∈ range (2 * t + 1), τ w d t r * ((d : ℝ) + 1) ^ r * (((d : ℝ) + 1) * ρ) ^ (2 * t - r) *
        ((2 * t).choose r : ℝ) ≤ w * (1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t := by
  have hx : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ Real.sqrt (2 * t) := Real.sqrt_nonneg _
  have step : ∀ r ∈ range (2 * t + 1), τ w d t r * ((d : ℝ) + 1) ^ r *
      (((d : ℝ) + 1) * ρ) ^ (2 * t - r) * ((2 * t).choose r : ℝ) ≤
      w * (1 / 256) ^ t * (Real.sqrt (2 * t) ^ r * ρ ^ (2 * t - r) *
        ((2 * t).choose r : ℝ)) := by
    intro r hr
    have hr' : r ≤ 2 * t := Nat.lt_succ_iff.1 (mem_range.1 hr)
    rw [τ_mul_pow_mul_pow w d t r ρ hr']
    have hs : Real.sqrt ((r : ℝ) ^ r) ≤ Real.sqrt (2 * t) ^ r := by
      rw [Real.sqrt_le_left (by positivity), ← pow_mul, pow_mul', hx]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hr') r
    have h0 : 0 ≤ w * (1 / 256) ^ t := by positivity
    calc w * (1 / 256) ^ t * Real.sqrt ((r : ℝ) ^ r) * ρ ^ (2 * t - r) *
          ((2 * t).choose r : ℝ)
        = w * (1 / 256) ^ t * (Real.sqrt ((r : ℝ) ^ r) * ρ ^ (2 * t - r) *
          ((2 * t).choose r : ℝ)) := by ring
      _ ≤ w * (1 / 256) ^ t * (Real.sqrt (2 * t) ^ r * ρ ^ (2 * t - r) *
          ((2 * t).choose r : ℝ)) := by gcongr
  refine (sum_le_sum step).trans ?_
  rw [← mul_sum, ← add_pow]
  have hb : (Real.sqrt (2 * t) + ρ) ^ 2 ≤ 9 * t / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * t) - ρ)]
  have h2 : (Real.sqrt (2 * t) + ρ) ^ (2 * t) ≤ (9 * (t : ℝ) / 2) ^ t := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hb t
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Binomial expansion**: `∑_{j ∈ S} lin(u + a_j)^N =
∑_{r ≤ N} (∑_{j ∈ S} lin(a_j)^r) lin(u)^(N-r) C(N, r)`. -/
theorem sum_lin_add_pow_eq (S : Finset (Fin n)) (u : Fin d → ℝ) (a : Fin n → Fin d → ℝ)
    (N : ℕ) : ∑ j ∈ S, lin (u + a j) ^ N = ∑ r ∈ range (N + 1),
      (∑ j ∈ S, lin (a j) ^ r) * lin u ^ (N - r) * C (N.choose r : ℝ) := by
  simp_rw [lin_add, add_comm (lin u), add_pow]
  rw [sum_comm]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [sum_mul, sum_mul, map_natCast]

/-- **The Gaussian part of a binomial expansion**: with `N ≥ 0`,
`∑_{r ≤ 2t} N · gaussMom r · nsq^(r/2) · u^(2t-r) C(2t, r) ≽ N (2t-1)‼ nsq^t`; every summand is a
sum of squares (`gaussMom r = 0` for odd `r`, and `2t - r` is even for even `r`), and the last one
is `N (2t-1)‼ nsq^t`. -/
theorem isSumSq_gaussPart_sub {N : ℝ} (hN : 0 ≤ N) (u : MvPolynomial (Fin d) ℝ) (t : ℕ) :
    IsSumSq (∑ r ∈ range (2 * t + 1), C (N * gaussMom r) * nsq d ^ (r / 2) * u ^ (2 * t - r) *
        C ((2 * t).choose r : ℝ) - C (N * gaussMom (2 * t)) * nsq d ^ t) := by
  rw [sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, C_1, mul_one,
    mul_one, Nat.mul_div_cancel_left t two_pos, add_sub_cancel_right]
  refine IsSumSq.sum fun r hr ↦ ?_
  have hr' : r < 2 * t := mem_range.1 hr
  by_cases hev : Even r
  · obtain ⟨i, rfl⟩ := hev
    rw [show 2 * t - (i + i) = (t - i) + (t - i) by omega, pow_add]
    exact (((isSumSq_C (by positivity)).mul (isSumSq_nsq_pow _ _)).mul
      (IsSumSq.mul_self _)).mul (isSumSq_C (by positivity))
  · rw [BS23.Separating.gaussMom_eq_zero_of_not_even hev, Nat.cast_zero, mul_zero, C_0,
      zero_mul, zero_mul, zero_mul]
    exact IsSumSq.zero

namespace SRFrame

/-! ### (E1) The noise polynomial of a frame -/

/-- **The noise error polynomial** of cluster `c` in degree `p`:
`∑_{|α| = p} (p; α) ((1/n) ∑_{j ∈ S_c} g_j^α - (|S_c|/n) m_α) X^α`. -/
noncomputable def noiseErr (F : SRFrame n d k) (c : Fin k) (p : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
    ((Nat.multinomial univ α : ℝ) *
      ((∑ j ∈ cluster F.ℓ c, ∏ i, F.g j i ^ α i) / n -
        ((cluster F.ℓ c).card : ℝ) / n * gaussMomMulti α)) •
      ∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i

theorem isHomogeneous_noiseErr (F : SRFrame n d k) (c : Fin k) (p : ℕ) :
    (F.noiseErr c p).IsHomogeneous p := by
  refine IsHomogeneous.sum _ _ _ fun α hα ↦ ?_
  rw [smul_eq_C_mul]
  refine IsHomogeneous.C_mul ?_ _
  have h := IsHomogeneous.prod (univ : Finset (Fin d))
    (fun i ↦ (X i : MvPolynomial (Fin d) ℝ) ^ α i) α (fun i _ ↦ isHomogeneous_X_pow i (α i))
  rwa [(mem_piAntidiag.1 hα).1] at h

/-- **The noise moments**: `∑_{j ∈ S_c} lin(g_j)^p = |S_c| · gaussMom p · nsq^(p/2) + n · Err`. -/
theorem sum_lin_pow_eq (F : SRFrame n d k) (hn : (n : ℝ) ≠ 0) (c : Fin k) (p : ℕ) :
    ∑ j ∈ cluster F.ℓ c, lin (F.g j) ^ p =
      C (((cluster F.ℓ c).card : ℝ) * gaussMom p) * nsq d ^ (p / 2) +
        C (n : ℝ) * F.noiseErr c p := by
  rw [← sub_eq_iff_eq_add', sum_lin_pow_sub_eq, noiseErr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← C_mul]
  congr 2
  field_simp

/-- On the good event of degree `p`, `‖Err‖₁ ≤ η d^p`. -/
theorem coeffNorm1_noiseErr_le (F : SRFrame n d k) {c : Fin k} {p : ℕ} {η : ℝ}
    (h : GoodNoise F.wt η p F.ℓ F.g) : coeffNorm1 (F.noiseErr c p) ≤ η * (d : ℝ) ^ p := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  have hsum : ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p, (Nat.multinomial univ α : ℝ) =
      (d : ℝ) ^ p := by
    have := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin d)) (fun _ ↦ (1 : ℝ)) p
    simpa using this.symm
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα ↦ ?_
  have hα' : ∑ i, α i ≤ p := le_of_eq (mem_piAntidiag.1 hα).1
  rw [coeffNorm1_smul, abs_mul, Nat.abs_cast]
  have h1 := h.2 c α hα'
  have h2 := BS23.Separating.coeffNorm1_prod_X_pow_le α
  have h0 : 0 ≤ η := (abs_nonneg _).trans h1
  have hm : (0 : ℝ) ≤ Nat.multinomial univ α := Nat.cast_nonneg _
  calc (Nat.multinomial univ α : ℝ) *
        |(∑ j ∈ cluster F.ℓ c, ∏ i, F.g j i ^ α i) / n -
          ((cluster F.ℓ c).card : ℝ) / n * gaussMomMulti α| *
        coeffNorm1 (∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i)
      ≤ (Nat.multinomial univ α : ℝ) * η * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hm) h2 (coeffNorm1_nonneg _)
          (mul_nonneg hm h0)
    _ = η * (Nat.multinomial univ α : ℝ) := by ring

/-- **The scale estimate** in the standard frame: `B_std = (1 / (n t^t)) ∑_j lin(ζ_j)^(2t)`. -/
noncomputable def Bstd (F : SRFrame n d k) (t : ℕ) : MvPolynomial (Fin d) ℝ :=
  C (1 / ((n : ℝ) * (t : ℝ) ^ t)) * ∑ j, lin (F.ζ j) ^ (2 * t)

theorem isHomogeneous_Bstd (F : SRFrame n d k) (t : ℕ) : (F.Bstd t).IsHomogeneous (2 * t) := by
  have h := (IsHomogeneous.sum univ (fun j ↦ lin (F.ζ j) ^ (2 * t)) (2 * t)
    fun j _ ↦ isHomogeneous_lin_pow _ _).C_mul (1 / ((n : ℝ) * (t : ℝ) ^ t))
  exact h

namespace Good

variable {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

/-- On a good frame, `‖Err‖₁ ≤ τ_p (d+1)^p` for `p ≤ 2t`. -/
theorem coeffNorm1_noiseErr_le' (hF : F.Good w R Csep s t) (c : Fin k) {p : ℕ}
    (hp : p ≤ 2 * t) : coeffNorm1 (F.noiseErr c p) ≤ τ w d t p * ((d : ℝ) + 1) ^ p :=
  (F.coeffNorm1_noiseErr_le (hF.good p hp)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _) (τ_pos hF.w_pos _ _ _).le)

/-- **(E1) The noise polynomial.** For `p ≤ 2t`,
`∑_{j ∈ S_c} lin(g_j)^p = |S_c| · gaussMom p · nsq^(p/2) + n · Err` with `Err` homogeneous of
degree `p` and `‖Err‖₁ ≤ τ_p (d+1)^p` (`Err = BS23.SmallRadius.SRFrame.noiseErr F c p`). -/
theorem noise_poly (hF : F.Good w R Csep s t) {p : ℕ} (hp : p ≤ 2 * t) (c : Fin k) :
    ∃ Err : MvPolynomial (Fin d) ℝ, Err.IsHomogeneous p ∧
      coeffNorm1 Err ≤ τ w d t p * ((d : ℝ) + 1) ^ p ∧
      ∑ j ∈ cluster F.ℓ c, lin (F.g j) ^ p =
        C (((cluster F.ℓ c).card : ℝ) * gaussMom p) * nsq d ^ (p / 2) + C (n : ℝ) * Err :=
  ⟨F.noiseErr c p, F.isHomogeneous_noiseErr c p, hF.coeffNorm1_noiseErr_le' c hp,
    F.sum_lin_pow_eq hF.n_pos_real.ne' c p⟩

/-- `p ≼ ‖p‖₁ nsq^D` for `p` homogeneous of degree `2D`. -/
theorem _root_.BS23.SmallRadius.isSumSq_l1_nsq {p : MvPolynomial (Fin d) ℝ} {D : ℕ}
    (hp : p.IsHomogeneous (2 * D)) : IsSumSq (C (coeffNorm1 p) * nsq d ^ D - p) :=
  isSumSq_l1 hp

/-- Even noise moments: `∑_{j ∈ S_c} lin(g_j)^(2r) ≼ (|S_c| (2r-1)‼ + n τ_{2r} (d+1)^(2r)) nsq^r`
for `r ≤ t`. -/
theorem sum_lin_g_pow_le (hF : F.Good w R Csep s t) (c : Fin k) {r : ℕ} (hr : r ≤ t) :
    IsSumSq (C (((cluster F.ℓ c).card : ℝ) * gaussMom (2 * r) +
        n * (τ w d t (2 * r) * ((d : ℝ) + 1) ^ (2 * r))) * nsq d ^ r -
      ∑ j ∈ cluster F.ℓ c, lin (F.g j) ^ (2 * r)) := by
  have hr2 : 2 * r ≤ 2 * t := by omega
  rw [F.sum_lin_pow_eq hF.n_pos_real.ne' c (2 * r), Nat.mul_div_cancel_left r two_pos]
  have h1 := isSumSq_l1_nsq (F.isHomogeneous_noiseErr c (2 * r))
  have h2 := isSumSq_C_mul_sub_C_mul (hF.coeffNorm1_noiseErr_le' c hr2) (isSumSq_nsq_pow d r)
  have h3 := isSumSq_C_mul_sub (Nat.cast_nonneg n) (isSumSq_sub_trans h1 h2)
  convert h3 using 1
  rw [map_add, map_mul (C : ℝ →+* MvPolynomial (Fin d) ℝ) (n : ℝ)]
  ring

/-- Errors: `∑_{j ∈ T} lin(e_j)^(2r) ≼ |T| (4/n²)^r nsq^r`. -/
theorem sum_lin_e_pow_le (hF : F.Good w R Csep s t) (T : Finset (Fin n)) (r : ℕ) :
    IsSumSq (C ((T.card : ℝ) * (4 / (n : ℝ) ^ 2) ^ r) * nsq d ^ r -
      ∑ j ∈ T, lin (F.e j) ^ (2 * r)) := by
  have := isSumSq_sum_C_mul_sub T (a := fun _ ↦ (4 / (n : ℝ) ^ 2) ^ r) (Q := nsq d ^ r)
    (P := fun j ↦ lin (F.e j) ^ (2 * r)) fun j _ ↦ isSumSq_lin_pow_le (hF.err j) r
  rwa [sum_const, nsmul_eq_mul] at this

theorem four_div_sq_le (hF : F.Good w R Csep s t) : 4 / (n : ℝ) ^ 2 ≤ 1 / 16 := by
  have hn := hF.n_pos_real
  have h20 : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hF.params.n_ge
  push_cast at h20
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-! ### (E2) Cluster moments -/

/-- The arithmetic of (E2). -/
theorem cluster_moment_arith (hF : F.Good w R Csep s t) (c : Fin k) :
    (2 : ℝ) ^ (2 * s - 1) * ((((cluster F.ℓ c).card : ℝ) * gaussMom (2 * s) +
        n * (τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s))) +
        ((cluster F.ℓ c).card : ℝ) * (4 / (n : ℝ) ^ 2) ^ s) ≤
      ((cluster F.ℓ c).card : ℝ) * (8 * s) ^ s := by
  set N : ℝ := ((cluster F.ℓ c).card : ℝ)
  set P : ℝ := (2 * (s : ℝ)) ^ s
  set H : ℝ := (2 : ℝ) ^ (2 * s - 1)
  have hs := hF.params.s_pos
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hn := hF.n_pos_real
  have hw := hF.w_pos
  have hH : 0 ≤ H := by positivity
  have hP2 : 2 ≤ P := by
    have h1 : (1 : ℝ) ≤ 2 * s := by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    calc (2 : ℝ) ≤ 2 * s := by
          have : (1 : ℝ) ≤ s := by exact_mod_cast hs
          linarith
      _ ≤ P := le_self_pow₀ h1 (by omega)
  have hgm : (gaussMom (2 * s) : ℝ) ≤ P := gaussMom_le s
  have hτ : τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s) ≤ w * (1 / 256) * P := by
    have h := τ_mul_pow_le hw.le d t (2 * s) (by have := hF.params.s_le_t; omega)
    rw [sqrt_two_mul_pow_two_mul] at h
    have hK : ((1 : ℝ) / 256) ^ t ≤ 1 / 256 := by
      calc ((1 : ℝ) / 256) ^ t ≤ (1 / 256) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hF.params.t_pos
        _ = 1 / 256 := pow_one _
    calc τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s) ≤ w * (1 / 256) ^ t * P := h
      _ ≤ w * (1 / 256) * P := by gcongr
  have hwn : w * n ≤ 2 * N := by have := hF.w_mul_le_card c; linarith
  have hq : (4 / (n : ℝ) ^ 2) ^ s ≤ 1 :=
    pow_le_one₀ (by positivity) ((hF.four_div_sq_le).trans (by norm_num))
  have h8 : (8 * (s : ℝ)) ^ s = 2 * H * P := by
    have e1 : (8 * (s : ℝ)) ^ s = 4 ^ s * P := by
      rw [← mul_pow]; ring_nf
    have e2 : (4 : ℝ) ^ s = 2 * H := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
      congr 1
      omega
    rw [e1, e2]
  have hb : N * gaussMom (2 * s) + n * (τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s)) +
      N * (4 / (n : ℝ) ^ 2) ^ s ≤ 2 * N * P := by
    have a1 : N * gaussMom (2 * s) ≤ N * P := mul_le_mul_of_nonneg_left hgm hN
    have a2 : n * (τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s)) ≤ N * P / 128 := by
      calc n * (τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s)) ≤ n * (w * (1 / 256) * P) :=
            mul_le_mul_of_nonneg_left hτ hn.le
        _ = (w * n) * P / 256 := by ring
        _ ≤ (2 * N) * P / 256 := by gcongr
        _ = N * P / 128 := by ring
    have a3 : N * (4 / (n : ℝ) ^ 2) ^ s ≤ N * P / 2 := by
      calc N * (4 / (n : ℝ) ^ 2) ^ s ≤ N * 1 := mul_le_mul_of_nonneg_left hq hN
        _ ≤ N * P / 2 := by nlinarith
    nlinarith
  rw [h8]
  calc H * (N * gaussMom (2 * s) + n * (τ w d t (2 * s) * ((d : ℝ) + 1) ^ (2 * s)) +
        N * (4 / (n : ℝ) ^ 2) ^ s) ≤ H * (2 * N * P) := mul_le_mul_of_nonneg_left hb hH
    _ = N * (2 * H * P) := by ring

/-- **(E2) Cluster moments.** `∑_{j ∈ S_c} lin(g_j + e_j)^(2s) ≼ |S_c| (8s)^s nsq^s`. -/
theorem cluster_moment_sos (hF : F.Good w R Csep s t) (c : Fin k) :
    IsSumSq (C (((cluster F.ℓ c).card : ℝ) * (8 * s) ^ s) * nsq d ^ s -
      ∑ j ∈ cluster F.ℓ c, lin (F.g j + F.e j) ^ (2 * s)) := by
  obtain ⟨b, hb⟩ := hF.params.s_pow
  have h2s : 2 * s = 2 ^ (b + 1) := by rw [hb, pow_succ]; ring
  set S := cluster F.ℓ c with hS
  have h1 : IsSumSq (C ((2 : ℝ) ^ (2 * s - 1)) *
      (∑ j ∈ S, lin (F.g j) ^ (2 * s) + ∑ j ∈ S, lin (F.e j) ^ (2 * s)) -
      ∑ j ∈ S, lin (F.g j + F.e j) ^ (2 * s)) := by
    have := isSumSq_sum_sub_sum S (x := fun j ↦ lin (F.g j + F.e j) ^ (2 * s))
      (y := fun j ↦ C ((2 : ℝ) ^ (2 * s - 1)) * (lin (F.g j) ^ (2 * s) + lin (F.e j) ^ (2 * s)))
      fun j _ ↦ by
        have h := isSumSq_add_pow_le (lin (F.g j)) (lin (F.e j)) (b + 1)
        rw [← h2s, ← lin_add] at h
        exact h
    rwa [← mul_sum, sum_add_distrib] at this
  have h2 := hF.sum_lin_g_pow_le c hF.params.s_le_t
  have h3 := hF.sum_lin_e_pow_le S s
  have h4 := isSumSq_C_mul_sub (c := (2 : ℝ) ^ (2 * s - 1)) (by positivity)
    (isSumSq_add_sub_add h2 h3)
  refine isSumSq_sub_trans (isSumSq_sub_trans h1 h4) ?_
  rw [← add_mul, ← map_add, ← mul_assoc, ← C_mul]
  exact isSumSq_C_mul_sub_C_mul (hF.cluster_moment_arith c) (isSumSq_nsq_pow d s)

/-! ### (E3) The upper scale bound -/

/-- `∑_c |S_c| = n`. -/
theorem sum_card_cluster (F : SRFrame n d k) :
    ∑ c, ((cluster F.ℓ c).card : ℝ) = n := by
  have := sum_cluster_eq F.ℓ (fun _ ↦ (1 : ℝ))
  simpa using this

/-- The noise of all clusters: `∑_j lin(g_j)^(2t) ≼ (n (2t-1)‼ + k n τ_{2t} (d+1)^(2t)) nsq^t`. -/
theorem sum_all_lin_g_pow_le (hF : F.Good w R Csep s t) :
    IsSumSq (C ((n : ℝ) * gaussMom (2 * t) +
        k * (n * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t)))) * nsq d ^ t -
      ∑ j, lin (F.g j) ^ (2 * t)) := by
  have := isSumSq_sum_C_mul_sub univ fun c _ ↦ hF.sum_lin_g_pow_le c le_rfl
  rw [sum_cluster_eq, sum_add_distrib, ← sum_mul, sum_card_cluster, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- The arithmetic of (E3). -/
theorem covEst_upper_arith (hF : F.Good w R Csep s t) :
    (3 : ℝ) ^ (2 * t - 1) * (n * (R ^ 2) ^ t + (n * gaussMom (2 * t) +
        k * (n * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t)))) + n * (4 / (n : ℝ) ^ 2) ^ t) ≤
      n * (t : ℝ) ^ t * 32 ^ t := by
  set T : ℝ := (t : ℝ) ^ t
  set u : ℝ := (2 : ℝ) ^ t
  set H : ℝ := (3 : ℝ) ^ (2 * t - 1)
  have ht := hF.params.t_pos
  have ht8 := hF.params.eight_le_t
  have hn := hF.n_pos_real
  have hw := hF.w_pos
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hT1 : 1 ≤ T := one_le_pow₀ ht1
  have hH : 0 ≤ H := by positivity
  have hu : 0 ≤ u := by positivity
  have hR : (R ^ 2) ^ t ≤ T := by
    have := hF.params.R_sq_le
    exact pow_le_pow_left₀ (sq_nonneg R) (by linarith) t
  have hgm : (gaussMom (2 * t) : ℝ) ≤ u * T := by
    have := gaussMom_le t
    rwa [mul_pow] at this
  have hkτ : (k : ℝ) * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t)) ≤ T := by
    have h := τ_mul_pow_le hw.le d t (2 * t) le_rfl
    rw [sqrt_two_mul_pow_two_mul, mul_pow] at h
    have hk : (k : ℝ) * w ≤ 1 := hF.k_mul_w_le
    have h128 : ((1 : ℝ) / 256) ^ t * u ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    calc (k : ℝ) * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t))
        ≤ k * (w * (1 / 256) ^ t * (u * T)) := mul_le_mul_of_nonneg_left h hk0
      _ = (k * w) * ((1 / 256) ^ t * u) * T := by ring
      _ ≤ 1 * 1 * T := by gcongr
      _ = T := by ring
  have hq : (4 / (n : ℝ) ^ 2) ^ t ≤ T :=
    (pow_le_one₀ (by positivity) ((hF.four_div_sq_le).trans (by norm_num))).trans hT1
  have hu4 : 4 ≤ u := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ u := pow_le_pow_right₀ (by norm_num) (by omega)
  have hb : n * (R ^ 2) ^ t + (n * gaussMom (2 * t) +
        k * (n * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t)))) + n * (4 / (n : ℝ) ^ 2) ^ t ≤
      n * T * (2 * u) := by
    have a1 : n * (R ^ 2) ^ t ≤ n * T := mul_le_mul_of_nonneg_left hR hn.le
    have a2 : (n : ℝ) * gaussMom (2 * t) ≤ n * (u * T) := mul_le_mul_of_nonneg_left hgm hn.le
    have a3 : (k : ℝ) * (n * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t))) ≤ n * T := by
      have := mul_le_mul_of_nonneg_left hkτ hn.le
      linarith
    have a4 : n * (4 / (n : ℝ) ^ 2) ^ t ≤ n * T := mul_le_mul_of_nonneg_left hq hn.le
    have a5 : n * T * 3 ≤ n * T * u := by
      have : 0 ≤ n * T := by positivity
      nlinarith
    nlinarith
  have hH3 : H * 3 = 9 ^ t := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega), pow_mul]
    norm_num
  have h18 : (9 : ℝ) ^ t * u ≤ 32 ^ t := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
  calc H * (n * (R ^ 2) ^ t + (n * gaussMom (2 * t) +
        k * (n * (τ w d t (2 * t) * ((d : ℝ) + 1) ^ (2 * t)))) + n * (4 / (n : ℝ) ^ 2) ^ t)
      ≤ H * (n * T * (2 * u)) := mul_le_mul_of_nonneg_left hb hH
    _ ≤ n * T * (H * 3 * u) := by
        have : 0 ≤ n * T * H * u := by positivity
        nlinarith
    _ ≤ n * T * 32 ^ t := by
        rw [hH3]
        exact mul_le_mul_of_nonneg_left h18 (by positivity)

/-- `C a · nsq^t - B_std = (1 / (n t^t)) (n t^t a · nsq^t - ∑_j lin(ζ_j)^(2t))`. -/
theorem C_mul_sub_Bstd (hF : F.Good w R Csep s t) (a : ℝ) :
    C a * nsq d ^ t - F.Bstd t = C (1 / ((n : ℝ) * (t : ℝ) ^ t)) *
      (C ((n : ℝ) * (t : ℝ) ^ t * a) * nsq d ^ t - ∑ j, lin (F.ζ j) ^ (2 * t)) := by
  have hT : (n : ℝ) * (t : ℝ) ^ t ≠ 0 := by
    have := hF.n_pos_real
    have : (0 : ℝ) < t := by exact_mod_cast hF.params.t_pos
    positivity
  rw [Bstd, mul_sub, ← mul_assoc, ← C_mul, one_div, inv_mul_cancel_left₀ hT]

/-- **(E3) The upper scale bound.** `B_std ≼ 32^t nsq^t`. -/
theorem covEst_upper (hF : F.Good w R Csep s t) :
    IsSumSq (C ((32 : ℝ) ^ t) * nsq d ^ t - F.Bstd t) := by
  obtain ⟨a, ha⟩ := hF.params.t_pow
  have h2t : 2 * t = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
  have hn := hF.n_pos_real
  have h1 : IsSumSq (C ((3 : ℝ) ^ (2 * t - 1)) *
      (∑ j, lin (F.m (F.ℓ j)) ^ (2 * t) + ∑ j, lin (F.g j) ^ (2 * t) +
        ∑ j, lin (F.e j) ^ (2 * t)) - ∑ j, lin (F.ζ j) ^ (2 * t)) := by
    have := isSumSq_sum_sub_sum univ (x := fun j ↦ lin (F.ζ j) ^ (2 * t))
      (y := fun j ↦ C ((3 : ℝ) ^ (2 * t - 1)) * (lin (F.m (F.ℓ j)) ^ (2 * t) +
        lin (F.g j) ^ (2 * t) + lin (F.e j) ^ (2 * t)))
      fun j _ ↦ by
        have h := isSumSq_powMean (univ : Finset (Fin 3))
          ![lin (F.m (F.ℓ j)), lin (F.g j), lin (F.e j)] (a + 1)
        simp only [card_univ, Fintype.card_fin, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Nat.cast_ofNat] at h
        rw [← h2t, ← lin_add, ← lin_add] at h
        exact h
    rwa [← mul_sum, sum_add_distrib, sum_add_distrib] at this
  have h2 : IsSumSq (C (n * (R ^ 2) ^ t) * nsq d ^ t - ∑ j, lin (F.m (F.ℓ j)) ^ (2 * t)) := by
    have := isSumSq_sum_C_mul_sub univ (a := fun _ ↦ (R ^ 2) ^ t) (Q := nsq d ^ t)
      (P := fun j ↦ lin (F.m (F.ℓ j)) ^ (2 * t)) fun j _ ↦ isSumSq_lin_pow_le (hF.radius _) t
    rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have h3 := hF.sum_all_lin_g_pow_le
  have h4 := hF.sum_lin_e_pow_le univ t
  rw [card_univ, Fintype.card_fin] at h4
  have h5 := isSumSq_C_mul_sub (c := (3 : ℝ) ^ (2 * t - 1)) (by positivity)
    (isSumSq_add_sub_add (isSumSq_add_sub_add h2 h3) h4)
  rw [hF.C_mul_sub_Bstd]
  refine isSumSq_C_mul (by positivity) (isSumSq_sub_trans (isSumSq_sub_trans h1 h5) ?_)
  rw [← add_mul, ← add_mul, ← map_add, ← map_add, ← mul_assoc, ← C_mul]
  exact isSumSq_C_mul_sub_C_mul hF.covEst_upper_arith (isSumSq_nsq_pow d t)

/-! ### (E4) The lower scale bound -/

/-- `‖lin(m_c)‖₁ ≤ (d+1) √(R²)`. -/
theorem coeffNorm1_lin_m_le (hF : F.Good w R Csep s t) (c : Fin k) :
    coeffNorm1 (lin (F.m c)) ≤ ((d : ℝ) + 1) * Real.sqrt (R ^ 2) := by
  refine (coeffNorm1_lin_le _).trans ?_
  have hma : ∀ a, |F.m c a| ≤ Real.sqrt (R ^ 2) := fun a ↦ Real.abs_le_sqrt (by
    have h1 := hF.radius c
    have h2 : F.m c a ^ 2 ≤ F.m c ⬝ᵥ F.m c := by
      have := single_le_sum (f := fun i ↦ F.m c i ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ a)
      simpa [dotProduct, sq] using this
    linarith)
  have h0 := Real.sqrt_nonneg (R ^ 2)
  calc ∑ a, |F.m c a| ≤ ∑ _a : Fin d, Real.sqrt (R ^ 2) := sum_le_sum fun a _ ↦ hma a
    _ = d * Real.sqrt (R ^ 2) := by simp
    _ ≤ ((d : ℝ) + 1) * Real.sqrt (R ^ 2) := by nlinarith

/-- The error part of the binomial expansion of cluster `c`:
`∑_{r ≤ 2t} Err_{c,r} · lin(m_c)^(2t-r) · C(2t, r)`. -/
noncomputable def _root_.BS23.SmallRadius.SRFrame.binomErr (F : SRFrame n d k) (c : Fin k)
    (t : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ r ∈ range (2 * t + 1), F.noiseErr c r * lin (F.m c) ^ (2 * t - r) * C ((2 * t).choose r : ℝ)

theorem _root_.BS23.SmallRadius.SRFrame.isHomogeneous_binomErr (F : SRFrame n d k) (c : Fin k)
    (t : ℕ) : (F.binomErr c t).IsHomogeneous (2 * t) := by
  refine IsHomogeneous.sum _ _ _ fun r hr ↦ ?_
  have hr' : r ≤ 2 * t := Nat.lt_succ_iff.1 (mem_range.1 hr)
  have h := ((F.isHomogeneous_noiseErr c r).mul (isHomogeneous_lin_pow (F.m c) (2 * t - r))).mul
    (isHomogeneous_C (Fin d) ((2 * t).choose r : ℝ))
  rwa [Nat.add_sub_cancel' hr', add_zero] at h

/-- `‖binomErr‖₁ ≤ w 256^(-t) (9t/2)^t`. -/
theorem coeffNorm1_binomErr_le (hF : F.Good w R Csep s t) (c : Fin k) :
    coeffNorm1 (F.binomErr c t) ≤ w * (1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t := by
  have hρ : Real.sqrt (R ^ 2) ^ 2 ≤ t / 4 := by
    rw [Real.sq_sqrt (sq_nonneg R)]
    exact hF.params.R_sq_le
  refine (coeffNorm1_sum_le _ _).trans ((sum_le_sum fun r hr ↦ ?_).trans
    (sum_τ_binom_le hF.w_pos.le (Real.sqrt_nonneg _) d t hρ))
  have hr' : r ≤ 2 * t := Nat.lt_succ_iff.1 (mem_range.1 hr)
  have h1 := coeffNorm1_mul_le (F.noiseErr c r * lin (F.m c) ^ (2 * t - r))
    (C ((2 * t).choose r : ℝ))
  have h2 := coeffNorm1_mul_le (F.noiseErr c r) (lin (F.m c) ^ (2 * t - r))
  have h3 := coeffNorm1_pow_le (lin (F.m c)) (2 * t - r)
  have h4 := hF.coeffNorm1_noiseErr_le' c hr'
  have h5 : coeffNorm1 (lin (F.m c)) ^ (2 * t - r) ≤
      (((d : ℝ) + 1) * Real.sqrt (R ^ 2)) ^ (2 * t - r) :=
    pow_le_pow_left₀ (coeffNorm1_nonneg _) (hF.coeffNorm1_lin_m_le c) _
  rw [coeffNorm1_C, abs_of_nonneg (Nat.cast_nonneg _)] at h1
  have hch : (0 : ℝ) ≤ (2 * t).choose r := Nat.cast_nonneg _
  have hτ0 : 0 ≤ τ w d t r * ((d : ℝ) + 1) ^ r := by
    have := τ_pos hF.w_pos d t r
    positivity
  calc coeffNorm1 (F.noiseErr c r * lin (F.m c) ^ (2 * t - r) * C ((2 * t).choose r : ℝ))
      ≤ coeffNorm1 (F.noiseErr c r * lin (F.m c) ^ (2 * t - r)) * (2 * t).choose r := h1
    _ ≤ (τ w d t r * ((d : ℝ) + 1) ^ r *
          (((d : ℝ) + 1) * Real.sqrt (R ^ 2)) ^ (2 * t - r)) * (2 * t).choose r :=
        mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul h4 (h3.trans h5)
          (coeffNorm1_nonneg _) hτ0)) hch

/-- **Per-cluster lower bound.**
`(|S_c| (2t-1)‼ - n w 256^(-t) (9t/2)^t) nsq^t ≼ ∑_{j ∈ S_c} lin(m_c + g_j)^(2t)`. -/
theorem cluster_lower (hF : F.Good w R Csep s t) (c : Fin k) :
    IsSumSq (∑ j ∈ cluster F.ℓ c, lin (F.m c + F.g j) ^ (2 * t) -
      C (((cluster F.ℓ c).card : ℝ) * gaussMom (2 * t) -
        n * (w * (1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) * nsq d ^ t) := by
  have hn := hF.n_pos_real
  have hexp : ∑ j ∈ cluster F.ℓ c, lin (F.m c + F.g j) ^ (2 * t) =
      ∑ r ∈ range (2 * t + 1), C (((cluster F.ℓ c).card : ℝ) * gaussMom r) * nsq d ^ (r / 2) *
        lin (F.m c) ^ (2 * t - r) * C ((2 * t).choose r : ℝ) + C (n : ℝ) * F.binomErr c t := by
    rw [sum_lin_add_pow_eq]
    simp_rw [F.sum_lin_pow_eq hn.ne' c]
    rw [binomErr, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun r _ ↦ by ring
  rw [hexp]
  have hP5 := isSumSq_l1_nsq (F.isHomogeneous_binomErr c t).neg
  rw [coeffNorm1_neg, sub_neg_eq_add] at hP5
  have hE := (isSumSq_C_mul_sub_C_mul (hF.coeffNorm1_binomErr_le c) (isSumSq_nsq_pow d t)).add hP5
  have h := (isSumSq_gaussPart_sub (N := ((cluster F.ℓ c).card : ℝ)) (Nat.cast_nonneg _)
    (lin (F.m c)) t).add (isSumSq_C_mul (Nat.cast_nonneg n) hE)
  convert h using 1
  rw [map_sub, map_mul (C : ℝ →+* MvPolynomial (Fin d) ℝ) (n : ℝ)]
  ring

/-- All clusters: `(n (2t-1)‼ - n (9t/512)^t) nsq^t ≼ ∑_j lin(m_{ℓ_j} + g_j)^(2t)`
(with `(9t/512)^t` written `256^(-t) (9t/2)^t`). -/
theorem sum_all_lower (hF : F.Good w R Csep s t) :
    IsSumSq (∑ j, lin (F.m (F.ℓ j) + F.g j) ^ (2 * t) -
      C ((n : ℝ) * gaussMom (2 * t) - n * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) *
        nsq d ^ t) := by
  have h := isSumSq_sum_sub_C_mul univ fun c _ ↦ hF.cluster_lower c
  have e1 : ∑ c, ∑ j ∈ cluster F.ℓ c, lin (F.m c + F.g j) ^ (2 * t) =
      ∑ j, lin (F.m (F.ℓ j) + F.g j) ^ (2 * t) := by
    rw [← sum_cluster_eq F.ℓ]
    refine sum_congr rfl fun c _ ↦ sum_congr rfl fun j hj ↦ ?_
    rw [(mem_filter.1 hj).2]
  rw [e1, sum_sub_distrib, ← sum_mul, sum_card_cluster, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  refine isSumSq_sub_trans (isSumSq_C_mul_sub_C_mul ?_ (isSumSq_nsq_pow d t)) h
  have hk := hF.k_mul_w_le
  have hX : 0 ≤ (n : ℝ) * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t) := by positivity
  have : (k : ℝ) * (n * (w * (1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) =
      (k * w) * (n * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) := by ring
  rw [this]
  nlinarith

/-- The arithmetic of (E4): with `T = t^t`, `T/3^t ≤ (2t-1)‼`, `256^(-t) (9t/2)^t = (9/512)^t T`,
`(4/n²)^t ≤ 16^(-t)` and `(4/3)^t ≥ 2`. -/
theorem covEst_lower_arith (hF : F.Good w R Csep s t) :
    (n : ℝ) * (t : ℝ) ^ t * (1 / 16) ^ t ≤
      ((2 : ℝ) ^ (2 * t - 1))⁻¹ *
          (n * gaussMom (2 * t) - n * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) -
        n * (4 / (n : ℝ) ^ 2) ^ t := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (t : ℝ) ^ t := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = ((1 : ℝ) / 12) ^ t := ⟨_, rfl⟩
  rw [← hT]
  have ht := hF.params.t_pos
  have ht8 := hF.params.eight_le_t
  have hn := hF.n_pos_real
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hT1 : 1 ≤ T := hT ▸ one_le_pow₀ ht1
  have hv : 0 ≤ v := by rw [hvd]; positivity
  -- `c₀ = 2 (1/4)^t`
  have hc₀ : ((2 : ℝ) ^ (2 * t - 1))⁻¹ = 2 * (1 / 4) ^ t := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc (2 : ℝ) ^ (2 * t - 1) * (2 * (1 / 4) ^ t) = (2 ^ (2 * t - 1) * 2) * (1 / 4) ^ t := by
          ring
      _ = 4 ^ t * (1 / 4) ^ t := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), pow_mul]
          norm_num
      _ = 1 := by rw [← mul_pow]; norm_num
  -- the Gaussian moment: `c₀ (2t-1)‼ ≥ 2 v T`
  have hgm : 2 * v * T ≤ 2 * (1 / 4) ^ t * gaussMom (2 * t) := by
    have h := pow_le_three_pow_mul_gaussMom t
    have e3 : ((1 : ℝ) / 12) ^ t * 3 ^ t = (1 / 4) ^ t := by rw [← mul_pow]; norm_num
    rw [← hT] at h
    calc 2 * v * T ≤ 2 * v * (3 ^ t * gaussMom (2 * t)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * (((1 : ℝ) / 12) ^ t * 3 ^ t) * gaussMom (2 * t) := by rw [hvd]; ring
      _ = 2 * (1 / 4) ^ t * gaussMom (2 * t) := by rw [e3]
  rw [hc₀]
  have hκ : 2 * (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t) ≤ v * T / 4 := by
    have e : (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t) =
        v * (27 / 512) ^ t * T := by
      calc (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)
          = (1 / 4 * (1 / 256 * (9 * (t : ℝ) / 2))) ^ t := by rw [mul_pow, mul_pow]
        _ = (1 / 12 * (27 / 512) * (t : ℝ)) ^ t := by
            rw [show (1 / 4 : ℝ) * (1 / 256 * (9 * (t : ℝ) / 2)) = 1 / 12 * (27 / 512) * t by
              ring]
        _ = v * (27 / 512) ^ t * T := by rw [mul_pow, mul_pow, hvd, hT]
    have h27 : ((27 : ℝ) / 512) ^ t ≤ 1 / 8 :=
      (pow_le_of_le_one (by norm_num) (by norm_num) (by omega)).trans (by norm_num)
    have hvT : 0 ≤ v * T := by positivity
    calc 2 * (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)
        = 2 * ((1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) := by ring
      _ = 2 * (v * T) * (27 / 512) ^ t := by rw [e]; ring
      _ ≤ 2 * (v * T) * (1 / 8) := mul_le_mul_of_nonneg_left h27 (by positivity)
      _ = v * T / 4 := by ring
  have h16 : ((1 : ℝ) / 16) ^ t ≤ v / 2 := by
    have e : ((1 : ℝ) / 16) ^ t = v * (3 / 4) ^ t := by rw [hvd, ← mul_pow]; norm_num
    have h34 : ((3 : ℝ) / 4) ^ t ≤ 1 / 2 :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 3 ≤ t)).trans (by norm_num)
    rw [e]
    nlinarith
  have hq : (4 / (n : ℝ) ^ 2) ^ t ≤ v * T / 2 := by
    have h1 : (4 / (n : ℝ) ^ 2) ^ t ≤ (1 / 16) ^ t :=
      pow_le_pow_left₀ (by positivity) hF.four_div_sq_le t
    nlinarith
  have a1 : (n : ℝ) * (2 * v * T) ≤ n * (2 * (1 / 4) ^ t * gaussMom (2 * t)) :=
    mul_le_mul_of_nonneg_left hgm hn.le
  have a2 : (n : ℝ) * (2 * (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) ≤
      n * (v * T / 4) := mul_le_mul_of_nonneg_left hκ hn.le
  have a3 : (n : ℝ) * (4 / (n : ℝ) ^ 2) ^ t ≤ n * (v * T / 2) :=
    mul_le_mul_of_nonneg_left hq hn.le
  have a4 : (n : ℝ) * T * (1 / 16) ^ t ≤ n * T * (v / 2) :=
    mul_le_mul_of_nonneg_left h16 (by positivity)
  have a5 : 0 ≤ (n : ℝ) * v * T := by positivity
  have e : 2 * (1 / 4 : ℝ) ^ t * (n * gaussMom (2 * t) - n * ((1 / 256) ^ t *
      (9 * (t : ℝ) / 2) ^ t)) - n * (4 / (n : ℝ) ^ 2) ^ t =
      n * (2 * (1 / 4) ^ t * gaussMom (2 * t)) -
        n * (2 * (1 / 4 : ℝ) ^ t * ((1 / 256) ^ t * (9 * (t : ℝ) / 2) ^ t)) -
        n * (4 / (n : ℝ) ^ 2) ^ t := by ring
  rw [e]
  nlinarith

/-- `B_std - C a · nsq^t = (1 / (n t^t)) (∑_j lin(ζ_j)^(2t) - n t^t a · nsq^t)`. -/
theorem Bstd_sub_C_mul (hF : F.Good w R Csep s t) (a : ℝ) :
    F.Bstd t - C a * nsq d ^ t = C (1 / ((n : ℝ) * (t : ℝ) ^ t)) *
      (∑ j, lin (F.ζ j) ^ (2 * t) - C ((n : ℝ) * (t : ℝ) ^ t * a) * nsq d ^ t) := by
  have h := hF.C_mul_sub_Bstd a
  rw [← neg_sub, h, ← neg_sub, mul_neg, neg_neg]

/-- **(E4) The lower scale bound.** `16^(-t) nsq^t ≼ B_std`. -/
theorem covEst_lower (hF : F.Good w R Csep s t) :
    IsSumSq (F.Bstd t - C ((1 / 16 : ℝ) ^ t) * nsq d ^ t) := by
  obtain ⟨a, ha⟩ := hF.params.t_pow
  have h2t : 2 * t = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
  have hn := hF.n_pos_real
  have ht : (0 : ℝ) < t := by exact_mod_cast hF.params.t_pos
  have h1 : IsSumSq (∑ j, lin (F.ζ j) ^ (2 * t) -
      C ((2 : ℝ) ^ (2 * t - 1))⁻¹ * ∑ j, lin (F.m (F.ℓ j) + F.g j) ^ (2 * t) +
      ∑ j, lin (F.e j) ^ (2 * t)) := by
    have h : IsSumSq (∑ j, (lin (F.ζ j) ^ (2 * t) -
        C ((2 : ℝ) ^ (2 * t - 1))⁻¹ * lin (F.m (F.ℓ j) + F.g j) ^ (2 * t) +
        lin (F.e j) ^ (2 * t))) :=
      IsSumSq.sum fun j _ ↦ by
        have h := isSumSq_pow_add_ge (lin (F.m (F.ℓ j) + F.g j)) (lin (F.e j))
          (j := a + 1) (by omega)
        rw [← h2t, ← lin_add] at h
        exact h
    rwa [sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  have h2 := hF.sum_all_lower
  have h3 := hF.sum_lin_e_pow_le univ t
  rw [card_univ, Fintype.card_fin] at h3
  have h4 := (h1.add (isSumSq_C_mul (c := ((2 : ℝ) ^ (2 * t - 1))⁻¹) (by positivity) h2)).add h3
  rw [hF.Bstd_sub_C_mul]
  refine isSumSq_C_mul (by positivity) (isSumSq_sub_trans
    (isSumSq_C_mul_sub_C_mul hF.covEst_lower_arith (isSumSq_nsq_pow d t)) ?_)
  convert h4 using 1
  simp only [map_sub, map_mul]
  ring

end Good

end SRFrame

end BS23.SmallRadius
