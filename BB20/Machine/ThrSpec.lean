module

public import BB20.Machine.ThrDef
public import BB20.Learning.Algorithm
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The thresholds meet their specifications

`BB20.Machine.thr6` meets `BB20.ThrSpec6` (`BB20.Machine.Thr.thr6_spec`) and
`BB20.Machine.thr11` meets `BB20.ThrSpec11` (`BB20.Machine.Thr.thr11_spec`).

* `τ' = R / (E (1 + E)^K)` with `R = α² / (2 γ P)`, `E = e^{2γ}`, `K = d + D - 1`
  (`BB20.Machine.Thr.tauPrime_eq`), and `τ'(ζ η) = (R / Q) / (E (1 + E)^{K + D})` with
  `η² = δ^D / Q` (`BB20.Machine.Thr.tauPrime_eta_eq`).
* The sample size is at least `60 / τ'²` (`δ ≤ 1`, and its logarithmic factor is at least
  `2 log 2`), so `1 / τ' ≤ M` (`BB20.Machine.Thr.inv_tauPrime_le`) and
  `E (1 + E)^K P ≤ α² M / (2γ) < 2^Λ` (`BB20.Machine.Thr.mul_le_of_inv_le`,
  `BB20.Machine.Thr.sq_div_mul_lt`). Every factor is at least `1`, which bounds `K`, `⌊2γ⌋` and
  `2^s` by `Λ` (`BB20.Machine.Thr.bounds_of_lt`), and then the caps change nothing
  (`BB20.Machine.Thr.caps`).
* `E ≤ Ê ≤ E (1 + 2/m!)^N` (`BB20.Machine.Thr.expHi_bounds`), and then
  `0.9 R / (E (1 + E)^K) ≤ R / (Ê (1 + Ê)^K) ≤ R / (E (1 + E)^K)` as soon as
  `N (K + 1) · 2/m! ≤ 1/10` (`BB20.Machine.Thr.val_bounds`), by Bernoulli's inequality.
-/

@[expose] public section

namespace BB20.Machine.Thr

open Finset Real

/-! ### The form of `τ'` -/

theorem facP_pos {d : ℕ} (hd : 1 ≤ d) (D p : ℕ) : 0 < facP d D p := by
  unfold facP
  have h1 : 0 < max 1 (D.choose (d - 1)) := lt_max_of_lt_left one_pos
  have h2 : 0 < d := hd
  positivity

theorem facQ_pos {D : ℕ} (hD : 1 ≤ D) (p : ℕ) : 0 < facQ D p := by
  unfold facQ
  have : 0 < D := hD
  positivity

theorem cast_facP (d D s : ℕ) : ((facP d D (2 ^ s) : ℕ) : ℝ) =
    (d : ℝ) ^ (4 * d) * 2 ^ (d + 1) * max 1 ((D.choose (d - 1) : ℕ) : ℝ) *
      (4 * d : ℝ) ^ 2 ^ s * (d : ℝ) ^ (2 ^ s * (2 ^ s + 1)) := by
  unfold facP
  push_cast
  ring

theorem cast_facQ (D s : ℕ) : ((facQ D (2 ^ s) : ℕ) : ℝ) =
    6 * 2 ^ (D + 2 ^ (s + 1)) * (D : ℝ) ^ (2 ^ s * (2 ^ s + 2)) := by
  unfold facQ
  push_cast
  rw [pow_succ 2 s, mul_comm (2 ^ s) 2]

/-- **`τ' = R / (E (1 + E)^K)`** with `R = α² / (2 γ P)`, `E = e^{2γ}` and `K = d + D - 1`. -/
theorem tauPrime_eq (α : ℝ) {γ : ℝ} (hγ : 0 < γ) {d : ℕ} (hd : 1 ≤ d) (D s : ℕ) :
    tauPrime α γ d D s = α ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ)) /
      (exp (2 * γ) * (1 + exp (2 * γ)) ^ (d + D - 1)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hE : 0 < exp (2 * γ) := exp_pos _
  have hB : (0 : ℝ) < max 1 ((D.choose (d - 1) : ℕ) : ℝ) := lt_max_of_lt_left one_pos
  unfold tauPrime tau condLB
  rw [cast_facP, div_pow, one_pow]
  field_simp

theorem condLB_pos (γ : ℝ) : 0 < condLB γ := by
  unfold condLB
  positivity

theorem condLB_le_one (γ : ℝ) : condLB γ ≤ 1 := by
  unfold condLB
  rw [div_le_one (by positivity)]
  linarith [exp_pos (2 * γ)]

theorem eta_pos (γ : ℝ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) : 0 < eta γ D s := by
  unfold eta
  have := condLB_pos γ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  positivity

theorem eta_sq (γ : ℝ) (D s : ℕ) :
    eta γ D s ^ 2 = condLB γ ^ D / (facQ D (2 ^ s) : ℝ) := by
  unfold eta
  have := condLB_pos γ
  rw [sq_sqrt (by positivity), cast_facQ]

theorem eta_le_one (γ : ℝ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) : eta γ D s ≤ 1 := by
  have h0 := eta_pos γ hD s
  have hQ : (1 : ℝ) ≤ (facQ D (2 ^ s) : ℝ) := by exact_mod_cast facQ_pos hD _
  have h2 : eta γ D s ^ 2 ≤ 1 := by
    rw [eta_sq, div_le_one (by linarith)]
    exact (pow_le_one₀ (condLB_pos γ).le (condLB_le_one γ)).trans hQ
  nlinarith

/-- **`τ'(ζ η) = (R / Q) / (E (1 + E)^{K + D})`** with `R = ζ² / (2 γ P)`. -/
theorem tauPrime_eta_eq (ζ : ℝ) {γ : ℝ} (hγ : 0 < γ) {d : ℕ} (hd : 1 ≤ d) {D : ℕ} (hD : 1 ≤ D)
    (s : ℕ) :
    tauPrime (ζ * eta γ D s) γ d D s = ζ ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ)) /
      (facQ D (2 ^ s) : ℝ) / (exp (2 * γ) * (1 + exp (2 * γ)) ^ (d + D - 1 + D)) := by
  have hE : 0 < exp (2 * γ) := exp_pos _
  have hP : (0 : ℝ) < (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  have hQ : (0 : ℝ) < (facQ D (2 ^ s) : ℝ) := by exact_mod_cast facQ_pos hD _
  rw [tauPrime_eq _ hγ hd, mul_pow, eta_sq, pow_add]
  unfold condLB
  rw [div_pow, one_pow]
  field_simp

/-! ### The sample size bounds `1 / τ'` -/

theorem tauPrime_pos {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) {d : ℕ} (hd : 1 ≤ d) (D s : ℕ) :
    0 < tauPrime α γ d D s := by
  rw [tauPrime_eq α hγ hd]
  have : (0 : ℝ) < (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  positivity

/-- The logarithmic factor of the sample size is at least `1`. -/
theorem one_le_logFactor {L ω : ℝ} (hL : 0 ≤ L) (s n : ℕ) (hn : 1 ≤ n) (hω : 0 < ω)
    (hω1 : ω ≤ 1) :
    1 ≤ log (1 / ω) + log (L + 2 ^ s + 1) + (L + 2 ^ s + 1) * log (2 * n) + log 2 := by
  have h1 : 0 ≤ log (1 / ω) := log_nonneg (by rw [le_div_iff₀ hω]; linarith)
  have hs : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have h2 : log 2 ≤ log (L + 2 ^ s + 1) := log_le_log (by norm_num) (by linarith)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : 0 ≤ (L + 2 ^ s + 1) * log (2 * n) :=
    mul_nonneg (by linarith) (log_nonneg (by linarith))
  have h4 := log_two_gt_d9
  linarith

/-- **The sample size bounds `1 / τ'`**: `sampleSize ≥ 60 / τ'²`, so `1 / τ' ≤ M`. -/
theorem inv_tauPrime_le {α γ ω : ℝ} {d D s n M : ℕ} (hα : 0 < α) (hγ : 0 < γ) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hω : 0 < ω) (hω1 : ω ≤ 1) (hM : sampleSize α γ d D s n ω ≤ M) :
    1 / tauPrime α γ d D s ≤ M := by
  have hτ := tauPrime_pos hα hγ hd D s
  unfold sampleSize at hM
  set τ := tauPrime α γ d D s
  set L := stepBound α γ d D s
  set δ := condLB γ
  have hL : 0 ≤ L := by
    simp only [L, stepBound]
    positivity
  have hδ0 : 0 < δ := condLB_pos γ
  have hδ1 : δ ≤ 1 := condLB_le_one γ
  have h2L : 1 ≤ (2 : ℝ) ^ (2 * L) := one_le_rpow (by norm_num) (by positivity)
  have hδL : δ ^ (2 * L) ≤ 1 := rpow_le_one hδ0.le hδ1 (by positivity)
  have hδL0 : 0 < δ ^ (2 * L) := rpow_pos_of_pos hδ0 _
  have hF := one_le_logFactor hL s n hn hω hω1
  have hτ2 : 0 < τ ^ 2 := by positivity
  have h60 : 60 / τ ^ 2 ≤ 60 * 2 ^ (2 * L) / (τ ^ 2 * δ ^ (2 * L)) := by
    rw [div_le_div_iff₀ hτ2 (by positivity)]
    have : τ ^ 2 * δ ^ (2 * L) ≤ τ ^ 2 * 2 ^ (2 * L) :=
      mul_le_mul_of_nonneg_left (hδL.trans h2L) hτ2.le
    nlinarith
  have hS : 60 / τ ^ 2 ≤ (M : ℝ) := by
    refine (h60.trans ?_).trans hM
    exact le_mul_of_one_le_right (by positivity) hF
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hS
  have hM1 : (1 : ℝ) ≤ M := by
    have : (0 : ℕ) < M := by exact_mod_cast hM0
    exact_mod_cast this
  have hsq : (1 / τ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    rw [div_pow, one_pow]
    calc 1 / τ ^ 2 ≤ 60 / τ ^ 2 := div_le_div_of_nonneg_right (by norm_num) hτ2.le
      _ ≤ (M : ℝ) := hS
      _ ≤ (M : ℝ) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- `E (1 + E)^K P = α² / (2 γ τ') ≤ α² M / (2 γ)`. -/
theorem mul_le_of_inv_le {α γ M : ℝ} (hα : 0 < α) (hγ : 0 < γ) {d : ℕ} (hd : 1 ≤ d)
    {D s : ℕ} (h : 1 / tauPrime α γ d D s ≤ M) :
    exp (2 * γ) * (1 + exp (2 * γ)) ^ (d + D - 1) * (facP d D (2 ^ s) : ℝ) ≤
      α ^ 2 / (2 * γ) * M := by
  have hP : (0 : ℝ) < (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  have hE : 0 < exp (2 * γ) := exp_pos _
  rw [tauPrime_eq α hγ hd, one_div_div, div_le_iff₀ (by positivity)] at h
  have h' := mul_le_mul_of_nonneg_right h hP.le
  calc exp (2 * γ) * (1 + exp (2 * γ)) ^ (d + D - 1) * (facP d D (2 ^ s) : ℝ)
      ≤ M * (α ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ))) * (facP d D (2 ^ s) : ℝ) := h'
    _ = α ^ 2 / (2 * γ) * M := by field_simp

/-- `α² M / (2γ) < 2^Λ`. -/
theorem sq_div_mul_lt (α γ : ℚ) (hγ : 0 < γ) (M : ℕ) :
    (α : ℝ) ^ 2 / (2 * γ) * M < 2 ^ (2 * α.num.natAbs.size + γ.den.size + M) := by
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hnum : (α : ℝ) ^ 2 ≤ (α.num.natAbs : ℝ) ^ 2 := by
    have h : (α : ℝ) * α.den = α.num := by exact_mod_cast Rat.mul_den_eq_num α
    have hden : (1 : ℝ) ≤ α.den := by exact_mod_cast α.den_pos
    have habs : ((α.num.natAbs : ℕ) : ℝ) ^ 2 = (α.num : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [habs, ← h, mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hden)
  have hden : 1 / (γ : ℝ) ≤ γ.den := by
    have h : (γ : ℝ) * γ.den = γ.num := by exact_mod_cast Rat.mul_den_eq_num γ
    have hnum : (1 : ℝ) ≤ γ.num := by exact_mod_cast Rat.num_pos.2 hγ
    rw [div_le_iff₀ hγr]
    linarith
  have hnat : α.num.natAbs ^ 2 * γ.den * M <
      2 ^ (2 * α.num.natAbs.size + γ.den.size + M) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    have h1 : α.num.natAbs ^ 2 < 2 ^ (2 * α.num.natAbs.size) := by
      rw [pow_mul']
      exact Nat.pow_lt_pow_left (Nat.lt_size_self _) two_ne_zero
    have h2 : γ.den < 2 ^ γ.den.size := Nat.lt_size_self _
    have h3 : M < 2 ^ M := Nat.lt_two_pow_self
    rw [pow_add, pow_add]
    exact mul_lt_mul'' (mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)) h3
      (Nat.zero_le _) (Nat.zero_le _)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  calc (α : ℝ) ^ 2 / (2 * γ) * M = (α : ℝ) ^ 2 * (1 / γ) * M / 2 := by ring
    _ ≤ (α.num.natAbs : ℝ) ^ 2 * γ.den * M / 2 := by gcongr
    _ ≤ (α.num.natAbs : ℝ) ^ 2 * γ.den * M := by
      have : (0 : ℝ) ≤ (α.num.natAbs : ℝ) ^ 2 * γ.den * M := by positivity
      linarith
    _ < 2 ^ (2 * α.num.natAbs.size + γ.den.size + M) := by exact_mod_cast hnat

/-! ### The caps change nothing -/

theorem two_pow_le_facP (d D p : ℕ) (hd : 1 ≤ d) : 2 ^ p ≤ facP d D p := by
  unfold facP
  have h1 : 0 < max 1 (D.choose (d - 1)) := lt_max_of_lt_left one_pos
  have h2 : 0 < d := hd
  have hA : 0 < d ^ (4 * d) * 2 ^ (d + 1) * max 1 (D.choose (d - 1)) := by positivity
  have hB : 0 < d ^ (p * (p + 1)) := by positivity
  calc 2 ^ p ≤ (4 * d) ^ p := Nat.pow_le_pow_left (by omega) p
    _ ≤ d ^ (4 * d) * 2 ^ (d + 1) * max 1 (D.choose (d - 1)) * (4 * d) ^ p :=
      Nat.le_mul_of_pos_left _ hA
    _ ≤ _ := Nat.le_mul_of_pos_right _ hB

/-- **Every factor is below `2^Λ`**: `K`, `⌊2γ⌋` and `2^s` are below `Λ`. -/
theorem bounds_of_lt {γ : ℚ} (hγ : 0 < γ) {d D s Λ : ℕ} (hd : 1 ≤ d)
    (h : exp (2 * γ) * (1 + exp (2 * γ)) ^ (d + D - 1) * (facP d D (2 ^ s) : ℝ) < 2 ^ Λ) :
    d + D - 1 < Λ ∧ ⌊2 * γ⌋₊ < Λ ∧ 2 ^ s < Λ := by
  set E := exp (2 * (γ : ℝ))
  set K := d + D - 1
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hE1 : 1 ≤ E := one_le_exp (by positivity)
  have hP1 : (1 : ℝ) ≤ (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  have hK1 : (1 : ℝ) ≤ (1 + E) ^ K := one_le_pow₀ (by linarith)
  have hX1 : (1 + E) ^ K ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by
    calc (1 + E) ^ K = 1 * (1 + E) ^ K * 1 := by ring
      _ ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by gcongr
  have hX2 : E ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by
    calc E = E * 1 * 1 := by ring
      _ ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by gcongr
  have hX3 : (facP d D (2 ^ s) : ℝ) ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by
    calc (facP d D (2 ^ s) : ℝ) = 1 * 1 * (facP d D (2 ^ s) : ℝ) := by ring
      _ ≤ E * (1 + E) ^ K * (facP d D (2 ^ s) : ℝ) := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (2 : ℝ) ^ K ≤ (1 + E) ^ K := pow_le_pow_left₀ (by norm_num) (by linarith) K
    exact (pow_lt_pow_iff_right₀ one_lt_two).1 ((h2.trans hX1).trans_lt h)
  · have hfl : ((⌊2 * γ⌋₊ : ℕ) : ℝ) ≤ 2 * γ := by
      have := Nat.floor_le (a := 2 * γ) (by positivity)
      exact_mod_cast this
    have h2 : (2 : ℝ) ^ ⌊2 * γ⌋₊ ≤ E := by
      calc (2 : ℝ) ^ ⌊2 * γ⌋₊ ≤ exp 1 ^ ⌊2 * γ⌋₊ := by
            gcongr
            linarith [add_one_le_exp (1 : ℝ)]
        _ = exp (⌊2 * γ⌋₊ * 1) := (exp_nat_mul 1 _).symm
        _ ≤ E := by
          rw [mul_one]
          exact exp_le_exp.2 hfl
    exact (pow_lt_pow_iff_right₀ one_lt_two).1 ((h2.trans hX2).trans_lt h)
  · have h2 : (2 : ℝ) ^ 2 ^ s ≤ (facP d D (2 ^ s) : ℝ) := by
      exact_mod_cast two_pow_le_facP d D (2 ^ s) hd
    exact (pow_lt_pow_iff_right₀ one_lt_two).1 ((h2.trans hX3).trans_lt h)

/-- **The caps change nothing** when the parameters are below `Λ`. -/
theorem caps (x : Input) (hd : 1 ≤ x.d) (hK : x.d + x.D - 1 < cap x)
    (hN : ⌊2 * x.gamma⌋₊ < cap x) (hs : 2 ^ x.s < cap x) :
    dc x = x.d ∧ Dc x = x.D ∧ pc x = 2 ^ x.s ∧ Nc x = ⌊2 * x.gamma⌋₊ + 1 ∧
      Kc x = x.d + x.D - 1 := by
  have hs' : x.s < 2 ^ x.s := Nat.lt_two_pow_self
  have h1 : dc x = x.d := min_eq_right (by omega)
  have h2 : Dc x = x.D := min_eq_right (by omega)
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · unfold pc
    rw [min_eq_right (show x.s ≤ cap x by omega), min_eq_right hs.le]
  · unfold Nc
    rw [min_eq_right hN.le]
  · unfold Kc
    rw [h1, h2]

/-! ### The approximation of `e^{2γ}` -/

theorem cast_expUp (y : ℚ) (m : ℕ) : (expUp y m : ℝ) =
    ∑ i ∈ range m, (y : ℝ) ^ i / i.factorial + (y : ℝ) ^ m * (m + 1) / (m.factorial * m) := by
  unfold expUp
  push_cast
  rfl

/-- `e^y ≤ expUp y m ≤ e^y (1 + 2/m!)` for `0 ≤ y ≤ 1`. -/
theorem expUp_bounds {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {m : ℕ} (hm : 0 < m) :
    exp y ≤ (expUp y m : ℝ) ∧ (expUp y m : ℝ) ≤ exp y * (1 + 2 / m.factorial) := by
  have hy0' : (0 : ℝ) ≤ y := by exact_mod_cast hy0
  have hy1' : (y : ℝ) ≤ 1 := by exact_mod_cast hy1
  rw [cast_expUp]
  refine ⟨exp_bound' hy0' hy1' hm, ?_⟩
  have hsum := sum_le_exp_of_nonneg hy0' m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hym : (y : ℝ) ^ m ≤ 1 := pow_le_one₀ hy0' hy1'
  have hrem : (y : ℝ) ^ m * (m + 1) / (m.factorial * m) ≤ 2 / m.factorial := by
    rw [div_le_div_iff₀ (by positivity) hf]
    have : (y : ℝ) ^ m * (m + 1) ≤ 2 * m := by nlinarith
    nlinarith
  have he : 1 ≤ exp (y : ℝ) := one_le_exp hy0'
  have : 2 / (m.factorial : ℝ) ≤ exp y * (2 / m.factorial) :=
    le_mul_of_one_le_left (by positivity) he
  linarith [mul_add (exp (y : ℝ)) 1 (2 / m.factorial)]

/-- **`E ≤ Ê ≤ E (1 + 2/m!)^N`** with `N = ⌊2γ⌋ + 1`. -/
theorem expHi_bounds {γ : ℚ} (hγ : 0 < γ) {m : ℕ} (hm : 0 < m) :
    exp (2 * γ) ≤ (expHi γ (⌊2 * γ⌋₊ + 1) m : ℝ) ∧
      (expHi γ (⌊2 * γ⌋₊ + 1) m : ℝ) ≤
        exp (2 * γ) * (1 + 2 / m.factorial) ^ (⌊2 * γ⌋₊ + 1) := by
  set N := ⌊2 * γ⌋₊ + 1
  have hN : (0 : ℚ) < N := by positivity
  have hlt : 2 * γ < N := by
    simp only [N, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hy0 : 0 ≤ 2 * γ / N := by positivity
  have hy1 : 2 * γ / N ≤ 1 := by
    rw [div_le_one hN]
    exact hlt.le
  have hE : exp (2 * (γ : ℝ)) = exp (((2 * γ / N : ℚ) : ℝ)) ^ N := by
    have hN' : (N : ℝ) ≠ 0 := by positivity
    rw [← exp_nat_mul]
    congr 1
    push_cast
    field_simp
  obtain ⟨h1, h2⟩ := expUp_bounds hy0 hy1 hm
  unfold expHi
  rw [Rat.cast_pow, hE]
  refine ⟨pow_le_pow_left₀ (exp_pos _).le h1 N, ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ ((exp_pos _).le.trans h1) h2 N

/-! ### The thresholds are within a factor `0.9` -/

/-- **`0.9 R / (E (1 + E)^K) ≤ R / (Ê (1 + Ê)^K) ≤ R / (E (1 + E)^K)`** when
`E ≤ Ê ≤ E (1 + a)^N` and `N (K + 1) a ≤ 1/10`. -/
theorem val_bounds {R E Ehi a : ℝ} {N K : ℕ} (hN : 0 < N) (hR : 0 ≤ R) (hE : 0 < E)
    (h1 : E ≤ Ehi) (h2 : Ehi ≤ E * (1 + a) ^ N) (ha : 0 ≤ a)
    (hPa : (N * (K + 1) : ℝ) * a ≤ 1 / 10) :
    9 / 10 * (R / (E * (1 + E) ^ K)) ≤ R / (Ehi * (1 + Ehi) ^ K) ∧
      R / (Ehi * (1 + Ehi) ^ K) ≤ R / (E * (1 + E) ^ K) := by
  have hpos : 0 < E * (1 + E) ^ K := by positivity
  have hEhi : 0 < Ehi := hE.trans_le h1
  have hle : E * (1 + E) ^ K ≤ Ehi * (1 + Ehi) ^ K :=
    mul_le_mul h1 (pow_le_pow_left₀ (by positivity) (by linarith) K) (by positivity)
      hEhi.le
  refine ⟨?_, div_le_div_of_nonneg_left hR hpos hle⟩
  set c := (1 + a) ^ N
  have hc : 1 ≤ c := one_le_pow₀ (by linarith)
  -- `Ê (1 + Ê)^K ≤ E (1 + E)^K c^{K+1}`.
  have h3 : 1 + Ehi ≤ (1 + E) * c := by nlinarith
  have hup : Ehi * (1 + Ehi) ^ K ≤ E * (1 + E) ^ K * c ^ (K + 1) := by
    calc Ehi * (1 + Ehi) ^ K ≤ (E * c) * ((1 + E) * c) ^ K :=
          mul_le_mul h2 (pow_le_pow_left₀ (by positivity) h3 K) (by positivity) (by positivity)
      _ = E * (1 + E) ^ K * c ^ (K + 1) := by rw [mul_pow, pow_succ]; ring
  -- `c^{K+1} (1 - N (K + 1) a) ≤ 1`, by Bernoulli's inequality.
  set P := N * (K + 1)
  have hcP : c ^ (K + 1) = (1 + a) ^ P := by
    simp only [c, P, ← pow_mul]
  have hPa' : (P : ℝ) * a ≤ 1 / 10 := by
    simp only [P]
    push_cast
    exact hPa
  have ha1 : a ≤ 1 := by
    have : (1 : ℝ) ≤ P := by exact_mod_cast Nat.mul_pos hN (Nat.succ_pos K)
    nlinarith
  have hBern : 1 + (P : ℝ) * (-a) ≤ (1 + -a) ^ P := one_add_mul_le_pow (by linarith) P
  have hprod : (1 + a) ^ P * (1 - P * a) ≤ 1 := by
    calc (1 + a) ^ P * (1 - P * a) ≤ (1 + a) ^ P * (1 + -a) ^ P := by
          gcongr
          linarith
      _ = (1 - a ^ 2) ^ P := by rw [← mul_pow]; ring_nf
      _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  have hcK : 0 < c ^ (K + 1) := by positivity
  calc 9 / 10 * (R / (E * (1 + E) ^ K)) ≤ (1 - P * a) * (R / (E * (1 + E) ^ K)) := by
        gcongr
        linarith
    _ ≤ R / (E * (1 + E) ^ K * c ^ (K + 1)) := by
        rw [mul_div_assoc', div_le_div_iff₀ hpos (by positivity)]
        rw [hcP] at hcK ⊢
        have hR' : 0 ≤ R * (E * (1 + E) ^ K) := by positivity
        nlinarith
    _ ≤ R / (Ehi * (1 + Ehi) ^ K) := div_le_div_of_nonneg_left hR (by positivity) hup

/-- `N (K + 1) · 2/m! ≤ 1/10` for `m = 20 N J`, `J ≥ K + 1`. -/
theorem factor_le {N K J : ℕ} (hN : 0 < N) (hJ : K + 1 ≤ J) :
    (N * (K + 1) : ℝ) * (2 / (20 * N * J).factorial) ≤ 1 / 10 := by
  have hJ0 : 0 < J := by omega
  have hm : (20 * N * J : ℝ) ≤ (20 * N * J).factorial := by
    exact_mod_cast Nat.self_le_factorial _
  have hm0 : (0 : ℝ) < 20 * N * J := by positivity
  have hJ' : ((K + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hJ
  push_cast at hJ'
  calc (N * (K + 1) : ℝ) * (2 / (20 * N * J).factorial) ≤ (N * (K + 1) : ℝ) * (2 / (20 * N * J))
        := by gcongr
    _ = (K + 1) / (10 * J) := by field_simp; ring
    _ ≤ 1 / 10 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith

/-! ### The specifications -/

/-- The parameters of an input meeting the sample size of Theorem 6 (for some `α' ≤ α`). -/
theorem params {x : Input} (hγ : 0 < x.gamma) (hd : 1 ≤ x.d) {α' : ℝ}
    (hα' : 0 < α') (hαα : α' ≤ x.coeff) {ω : ℝ} (hn : 1 ≤ x.n) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hM : sampleSize α' x.gamma x.d x.D x.s x.n ω ≤ x.samples.length) :
    dc x = x.d ∧ Dc x = x.D ∧ pc x = 2 ^ x.s ∧ Nc x = ⌊2 * x.gamma⌋₊ + 1 ∧
      Kc x = x.d + x.D - 1 := by
  have hγr : (0 : ℝ) < x.gamma := by exact_mod_cast hγ
  have hinv := inv_tauPrime_le hα' hγr hd hn hω hω1 hM
  have hX := mul_le_of_inv_le hα' hγr hd hinv
  have hsq : α' ^ 2 / (2 * x.gamma) * x.samples.length ≤
      (x.coeff : ℝ) ^ 2 / (2 * x.gamma) * x.samples.length := by
    gcongr
  have hlt := (hX.trans hsq).trans_lt (sq_div_mul_lt x.coeff x.gamma hγ x.samples.length)
  obtain ⟨hK, hN, hs⟩ := bounds_of_lt hγ hd hlt
  exact caps x hd hK hN hs

/-- **`thr6` meets the specification of Theorem 6.** -/
theorem thr6_spec : ThrSpec6 thr6 := by
  intro n samples α γ d D s ω hn hα hγ hd hω hω1 hM
  set x : Input := ⟨n, samples, α, γ, d, D, s⟩ with hx
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hαr : (0 : ℝ) < α := by exact_mod_cast hα
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    params (x := x) hγ hd hαr le_rfl hn hω hω1 hM
  refine ⟨_, rfl, ?_⟩
  have hm : 0 < 20 * (⌊2 * γ⌋₊ + 1) * (d + D - 1 + 1) := by positivity
  obtain ⟨e1, e2⟩ := expHi_bounds hγ hm
  have hP : (0 : ℝ) < (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  have hv := val_bounds (R := (α : ℝ) ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ)))
    (Nat.succ_pos _) (by positivity) (exp_pos _) e1 e2 (by positivity)
    (factor_le (Nat.succ_pos _) le_rfl)
  rw [tauPrime_eq _ hγr hd]
  simp only [base, expHi6, val, h1, h2, h3, h4, h5]
  push_cast
  exact hv

/-- **`thr11` meets the specification of Theorem 11.** -/
theorem thr11_spec : ThrSpec11 thr11 := by
  intro n samples ζ γ d D s ω hn hζ hγ hd hD hω hω1 hM
  set x : Input := ⟨n, samples, ζ, γ, d, D, s⟩ with hx
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hζr : (0 : ℝ) < ζ := by exact_mod_cast hζ
  have hη := eta_pos (γ : ℝ) hD s
  have hη1 := eta_le_one (γ : ℝ) hD s
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    params (x := x) hγ hd (α' := ζ * eta γ D s) (by positivity)
      (mul_le_of_le_one_right hζr.le hη1) hn hω hω1 hM
  refine ⟨_, _, rfl, ?_⟩
  have hm : 0 < 20 * (⌊2 * γ⌋₊ + 1) * (d + D - 1 + D + 1) := by positivity
  obtain ⟨e1, e2⟩ := expHi_bounds hγ hm
  have hP : (0 : ℝ) < (facP d D (2 ^ s) : ℝ) := by exact_mod_cast facP_pos hd _ _
  have hQ : (0 : ℝ) < (facQ D (2 ^ s) : ℝ) := by exact_mod_cast facQ_pos hD _
  have hv₂ := val_bounds
    (R := (ζ : ℝ) ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ)) / (facQ D (2 ^ s) : ℝ))
    (K := d + D - 1 + D) (Nat.succ_pos _) (by positivity) (exp_pos _) e1 e2 (by positivity)
    (factor_le (Nat.succ_pos _) le_rfl)
  have hv₃ := val_bounds (R := (ζ : ℝ) ^ 2 / (2 * γ * (facP d D (2 ^ s) : ℝ)))
    (K := d + D - 1) (Nat.succ_pos _) (by positivity) (exp_pos _) e1 e2 (by positivity)
    (factor_le (Nat.succ_pos _) (by omega))
  rw [tauPrime_eta_eq _ hγr hd hD, tauPrime_eq _ hγr hd]
  simp only [base, expHi11, val, h1, h2, h3, h4, h5]
  push_cast
  exact ⟨hv₂.1, hv₂.2, hv₃.1, hv₃.2⟩

end BB20.Machine.Thr
