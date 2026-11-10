module

public import ABBKS26.Assembly.ExecData
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-! Rational inverse square roots for the final frame normalization (LA5). -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux

open Common Matrix
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

theorem sqrtP_nonneg (p : ℕ) (q : ℚ) : 0 ≤ SoS.Loop.sqrtP p q := by
  unfold SoS.Loop.sqrtP
  positivity

theorem sqrtP_le (p : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    (SoS.Loop.sqrtP p q : ℝ) ≤ Real.sqrt q := by
  have hf : 0 ≤ ⌊q * 4 ^ p⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : (⌊q * 4 ^ p⌋.natAbs : ℚ) = (⌊q * 4 ^ p⌋ : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hf)]
  have hs : (Nat.sqrt ⌊q * 4 ^ p⌋.natAbs : ℚ) ^ 2 ≤ q * 4 ^ p := by
    calc
      _ ≤ (⌊q * 4 ^ p⌋.natAbs : ℚ) := by exact_mod_cast Nat.sqrt_le' _
      _ ≤ _ := hcast ▸ Int.floor_le _
  have hfour : (4 : ℚ) ^ p = ((2 : ℚ) ^ p) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm p 2, pow_mul]
    norm_num
  have hsq : SoS.Loop.sqrtP p q ^ 2 ≤ q := by
    unfold SoS.Loop.sqrtP
    rw [div_pow, div_le_iff₀ (by positivity)]
    simpa only [hfour] using hs
  have hsq' : (SoS.Loop.sqrtP p q : ℝ) ^ 2 ≤ (Real.sqrt q) ^ 2 := by
    rw [Real.sq_sqrt (by exact_mod_cast hq)]
    exact_mod_cast hsq
  exact (sq_le_sq₀ (by exact_mod_cast sqrtP_nonneg p q) (Real.sqrt_nonneg _)).mp hsq'

/-- Two guard bits ensure strict positivity throughout the interval `[1,4)`. -/
def invSqrt (p : ℕ) (q : ℚ) : ℚ := SoS.Loop.sqrtP (p + 2) (1 / q)

theorem invSqrt_polytime {α : Type} {enc : α ↪ List Bool} {p : α → ℕ} {q : α → ℚ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hq : ComputableInPolyTime q enc encRat) :
    ComputableInPolyTime (fun x ↦ invSqrt (p x) (q x)) enc encRat :=
  SoS.PolyTime.sqrtP' (unary_add' hp (const 2)) (rat_div' (const 1) hq)

theorem invSqrt_spec (p : ℕ) {q : ℚ} (hq : 1 ≤ q ∧ q < 4) :
    0 < invSqrt p q ∧ |((invSqrt p q ^ 2 * q : ℚ) : ℝ) - 1| ≤ 1 / (2 : ℝ) ^ p := by
  let r : ℝ := invSqrt p q
  let t := Real.sqrt (1 / (q : ℝ))
  let δ : ℝ := 1 / (2 : ℝ) ^ (p + 2)
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq4 : (q : ℝ) < 4 := by exact_mod_cast hq.2
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 * (q : ℝ) = 1 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 / (q : ℝ))]
    exact div_mul_cancel₀ _ hq0.ne'
  have htlo : (1 / 2 : ℝ) < t := by
    have ht := Real.sq_sqrt (by positivity : 0 ≤ 1 / (q : ℝ))
    have hdiv : (1 / 4 : ℝ) < 1 / (q : ℝ) := by
      exact (div_lt_div_iff₀ (by norm_num) hq0).mpr (by linarith only [hq4])
    nlinarith only [ht, ht0, hdiv]
  have hr0 : 0 ≤ r := by
    dsimp only [r, invSqrt]
    exact_mod_cast sqrtP_nonneg (p + 2) (1 / q)
  have hrt : r ≤ t := by
    simpa only [r, invSqrt, Rat.cast_div, Rat.cast_one, t] using
      sqrtP_le (p + 2) (q := 1 / q) (by positivity)
  have herr : |r - t| ≤ δ := by
    simpa only [r, invSqrt, Rat.cast_div, Rat.cast_one, t, δ] using
      SoS.Loop.abs_sqrtP_sub_le (p + 2) (r := 1 / q) (by positivity)
  have hδ : δ ≤ 1 / 4 := by
    dsimp only [δ]
    rw [pow_add]
    have hp : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    norm_num at hp ⊢
    linarith only [hp]
  have hrpos : 0 < r := by
    have hh := (abs_le.mp herr).1
    linarith only [hh, htlo, hδ]
  refine ⟨by exact_mod_cast (show (0 : ℝ) < (invSqrt p q : ℝ) from hrpos), ?_⟩
  have htscale : (q : ℝ) * t < 2 := by
    have hs : ((q : ℝ) * t) ^ 2 < 4 := by
      nlinarith only [ht2, hq4]
    nlinarith only [hs, mul_nonneg hq0.le ht0]
  have hfactor : (q : ℝ) * (r + t) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_left hrt hq0.le
    linarith only [hh, htscale]
  have he : r ^ 2 * (q : ℝ) - 1 = (r - t) * ((q : ℝ) * (r + t)) := by
    nlinarith only [ht2]
  push_cast
  change |r ^ 2 * (q : ℝ) - 1| ≤ _
  rw [he, abs_mul, abs_of_nonneg (mul_nonneg hq0.le (add_nonneg hr0 ht0))]
  calc
    _ ≤ δ * 4 := mul_le_mul herr hfactor (by positivity) (by positivity)
    _ = _ := by dsimp only [δ]; rw [pow_add]; norm_num; ring

theorem invSqrt_le_one (p : ℕ) {q : ℚ} (hq : 1 ≤ q) : invSqrt p q ≤ 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hh : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : Real.sqrt (1 / (q : ℝ)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hh).mpr hq1)
  have hr : (invSqrt p q : ℝ) ≤ Real.sqrt (1 / (q : ℝ)) := by
    simpa only [invSqrt, Rat.cast_div, Rat.cast_one] using
      sqrtP_le (p + 2) (q := 1 / q) (by positivity)
  exact_mod_cast hr.trans ht


/-- LA5 with an explicit dimension-dependent error, without a density-selected witness. -/
theorem normalize_error {d : ℕ} (p : ℕ) (q : Fin d → ℚ)
    (hq : ∀ i, 1 ≤ q i ∧ q i < 4) :
    frobSq (diagonal (fun i ↦ ((invSqrt p (q i) ^ 2 * q i : ℚ) : ℝ)) - 1) ≤
      d / ((2 : ℝ) ^ p) ^ 2 := by
  have he : diagonal (fun i ↦ ((invSqrt p (q i) ^ 2 * q i : ℚ) : ℝ)) - 1 =
      diagonal (fun i ↦ ((invSqrt p (q i) ^ 2 * q i : ℚ) : ℝ) - 1) := by
    rw [← diagonal_one, ← diagonal_sub]
  rw [he, frobSq]
  simp only [diagonal_apply, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ ≤ ∑ _i : Fin d, (1 / (2 : ℝ) ^ p) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (invSqrt_spec p (hq i)).2 2
    _ = _ := by simp [div_eq_mul_inv]

/-- A logarithmic precision that makes the dimension-dependent normalization error small. -/
def normalizePrecision (d : ℕ) (ζ : ℚ) : ℕ := Nat.clog 2 ⌈(d + 1 : ℚ) / ζ⌉₊

theorem normalizePrecision_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {ζ : α → ℚ} (hd : ComputableInPolyTime d enc encUnary)
    (hζ : ComputableInPolyTime ζ enc encRat) :
    ComputableInPolyTime (fun x ↦ normalizePrecision (d x) (ζ x)) enc encUnary := by
  have hq := rat_div' (rat_add' (rat_natCast' (unary_to_binary.comp hd)) (const 1)) hζ
  have hceil := ComputableTidilyInPolyTime.intBin_toNat.comp
    (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hq)).tidy)
  have hc : ComputableInPolyTime (fun x ↦ ⌈(d x + 1 : ℚ) / ζ x⌉₊) enc encNat := by
    refine (ComputableInPolyTime.of_tidy hceil).of_enc_eq fun x ↦ ?_
    congr 1
  exact binary_clog_two.comp hc

theorem normalizePrecision_spec (d : ℕ) {ζ : ℚ} (hζ : 0 < ζ) :
    (d : ℝ) / ((2 : ℝ) ^ normalizePrecision d ζ) ^ 2 ≤ (ζ : ℝ) ^ 2 := by
  have hpow : (⌈(d + 1 : ℚ) / ζ⌉₊ : ℝ) ≤ 2 ^ normalizePrecision d ζ := by
    unfold normalizePrecision
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈(d + 1 : ℚ) / ζ⌉₊
  have hceil : (d + 1 : ℚ) / ζ ≤ ⌈(d + 1 : ℚ) / ζ⌉₊ := Nat.le_ceil _
  have hh : ((d : ℝ) + 1) / ζ ≤ 2 ^ normalizePrecision d ζ := by
    have hc : ((d : ℝ) + 1) / ζ ≤ (⌈(d + 1 : ℚ) / ζ⌉₊ : ℝ) := by
      exact_mod_cast hceil
    exact hc.trans hpow
  have hζ' : (0 : ℝ) < ζ := by exact_mod_cast hζ
  have hprod := (div_le_iff₀ hζ').mp hh
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1) hprod 2
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hsq, sq_nonneg (d : ℝ)]


/-- Apply the computed diagonal correction to the stored rows of the frame. -/
def finish (p : ℕ) (q : Vector) (T : MatrixL) : MatrixL :=
  (q.zip T).map fun qt ↦ qt.2.map (invSqrt p qt.1 * ·)

theorem finish_polytime {α : Type} {enc : α ↪ List Bool} {p : α → ℕ}
    {q : α → Vector} {T : α → MatrixL} (hp : ComputableInPolyTime p enc encUnary)
    (hq : ComputableInPolyTime q enc encVector) (hT : ComputableInPolyTime T enc encMatrix) :
    ComputableInPolyTime (fun x ↦ finish (p x) (q x) (T x)) enc encMatrix := by
  unfold finish
  apply mapWithInput ((zip encRat encVector).comp (hq.prod hT))
  apply mapWithInput ((snd _ _).comp (snd _ _))
  exact rat_mul'
    (invSqrt_polytime (hp.comp ((fst _ _).comp (fst _ _)))
      ((fst _ _).comp ((snd _ _).comp (fst _ _)))) (snd _ _)

/-- Choose the precision from the requested tolerance and the stored diagonal's length. -/
def finishRequested (ζ : ℚ) (q : Vector) (T : MatrixL) : MatrixL :=
  finish (normalizePrecision q.length ζ) q T

theorem finishRequested_polytime {α : Type} {enc : α ↪ List Bool}
    {ζ : α → ℚ} {q : α → Vector} {T : α → MatrixL}
    (hζ : ComputableInPolyTime ζ enc encRat) (hq : ComputableInPolyTime q enc encVector)
    (hT : ComputableInPolyTime T enc encMatrix) :
    ComputableInPolyTime (fun x ↦ finishRequested (ζ x) (q x) (T x)) enc encMatrix :=
  finish_polytime (normalizePrecision_polytime ((length_list _).comp hq) hζ) hq hT

theorem finish_ofFn {d : ℕ} (p : ℕ) (q : Fin d → ℚ)
    (T : Matrix (Fin d) (Fin d) ℚ) :
    finish p (List.ofFn q) (List.ofFn fun i ↦ List.ofFn (T i)) =
      List.ofFn (fun i ↦ List.ofFn fun j ↦ invSqrt p (q i) * T i j) := by
  apply List.ext_getElem
  · simp [finish]
  · intro i hi hi'
    simp [finish] at hi
    simp [finish, Function.comp_def]

theorem matrixOf_finish {d : ℕ} (p : ℕ) (q : Fin d → ℚ)
    (T : Matrix (Fin d) (Fin d) ℚ) :
    matrixOf d (finish p (List.ofFn q) (List.ofFn fun i ↦ List.ofFn (T i))) =
      diagonal (fun i ↦ invSqrt p (q i)) * T := by
  rw [finish_ofFn]
  ext i j
  simp [matrixOf, List.getD_eq_getElem?_getD, diagonal_mul]

private theorem diagonal_contraction {d : ℕ} (r : Vec d) (A : Mat d)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    frobSq (diagonal r * A * diagonal r) ≤ frobSq A := by
  unfold frobSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [mul_diagonal, diagonal_mul]
  have hi : r i ^ 2 ≤ 1 := by nlinarith only [(hr i).1, (hr i).2]
  have hj : r j ^ 2 ≤ 1 := by nlinarith only [(hr j).1, (hr j).2]
  calc
    _ = r i ^ 2 * r j ^ 2 * A i j ^ 2 := by ring
    _ ≤ 1 * 1 * A i j ^ 2 := by gcongr
    _ = _ := by ring

/-- Final rational normalization adds only the requested error to the filter's frame error. -/
theorem finish_error {d : ℕ} (p : ℕ) (q : Fin d → ℚ) (T C S : Mat d) (e ζ : ℝ)
    (hq : ∀ i, 1 ≤ q i ∧ q i < 4)
    (hTC : T * C * Tᵀ = diagonal (fun i ↦ (q i : ℝ)))
    (he : 0 ≤ e) (hζ : 0 ≤ ζ)
    (herror : frobSq (T * (S - C) * Tᵀ) ≤ e ^ 2)
    (hprecision : d / ((2 : ℝ) ^ p) ^ 2 ≤ ζ ^ 2) :
    let B := diagonal (fun i ↦ (invSqrt p (q i) : ℝ))
    frobSq ((B * T) * S * (B * T)ᵀ - 1) ≤ (e + ζ) ^ 2 := by
  let B := diagonal (fun i ↦ (invSqrt p (q i) : ℝ))
  let E := T * (S - C) * Tᵀ
  let Q := diagonal (fun i ↦ ((invSqrt p (q i) ^ 2 * q i : ℚ) : ℝ)) - 1
  have hB : ∀ i, 0 ≤ (invSqrt p (q i) : ℝ) ∧ (invSqrt p (q i) : ℝ) ≤ 1 := by
    intro i
    constructor
    · exact_mod_cast (invSqrt_spec p (hq i)).1.le
    · exact_mod_cast invSqrt_le_one p (hq i).1
  have hEB : frobSq (B * E * B) ≤ e ^ 2 :=
    (diagonal_contraction _ E hB).trans herror
  have hQ : frobSq Q ≤ ζ ^ 2 := (normalize_error p q hq).trans hprecision
  have hnormE : Robust.RBAux.FrameLoop.fnorm (B * E * B) ≤ e := by
    apply (sq_le_sq₀ (Robust.RBAux.FrameLoop.fnorm_nonneg _) he).mp
    rwa [Robust.RBAux.FrameLoop.fnorm_sq]
  have hnormQ : Robust.RBAux.FrameLoop.fnorm Q ≤ ζ := by
    apply (sq_le_sq₀ (Robust.RBAux.FrameLoop.fnorm_nonneg _) hζ).mp
    rwa [Robust.RBAux.FrameLoop.fnorm_sq]
  have hdiag : B * (T * C * Tᵀ) * B = Q + 1 := by
    rw [hTC]
    ext i j
    simp only [B, Q, mul_diagonal, sub_add_cancel]
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, Rat.cast_mul, Rat.cast_pow]
      ring
    · simp only [diagonal_apply_ne _ hij, zero_mul]
  have hdecomp : (B * T) * S * (B * T)ᵀ - 1 = B * E * B + Q := by
    rw [transpose_mul, show Bᵀ = B from diagonal_transpose _]
    change B * T * S * (Tᵀ * B) - 1 = B * (T * (S - C) * Tᵀ) * B + Q
    calc
      _ = B * (T * (S - C) * Tᵀ) * B + (B * (T * C * Tᵀ) * B - 1) := by
        noncomm_ring
      _ = _ := by rw [hdiag]; abel
  change frobSq ((B * T) * S * (B * T)ᵀ - 1) ≤ _
  rw [hdecomp]
  have hh := (Robust.RBAux.FrameLoop.fnorm_add (B * E * B) Q).trans
    (add_le_add hnormE hnormQ)
  have hs := pow_le_pow_left₀ (Robust.RBAux.FrameLoop.fnorm_nonneg _) hh 2
  rwa [Robust.RBAux.FrameLoop.fnorm_sq] at hs

theorem matrixOf_finishRequested {d : ℕ} (ζ : ℚ) (q : Fin d → ℚ)
    (T : Matrix (Fin d) (Fin d) ℚ) :
    matrixOf d (finishRequested ζ (List.ofFn q) (List.ofFn fun i ↦ List.ofFn (T i))) =
      diagonal (fun i ↦ invSqrt (normalizePrecision d ζ) (q i)) * T := by
  unfold finishRequested
  rw [List.length_ofFn]
  exact matrixOf_finish _ q T

end ABBKS26.Assembly.Exec.FrameAux
