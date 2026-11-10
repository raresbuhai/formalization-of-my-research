module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdReify

/-! Rational ball and concentration norms for the executable plain SUB family. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdNorms

open Common MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def ident (a : Args) : ℚ :=
  (IdPayload.size a ^ 2) ^ (29 * IdInput.degree a) *
    (1 + (2 * IdInput.degree a + 1 : ℚ) *
      IdPayload.size a ^ (16 * IdInput.degree a + 1))

def projection (a : Args) : ℚ :=
  max 1 ((ident a + (2 + IdPayload.tolerance a / 3) * (a.1.1 : ℚ) ^ 2) /
    (IdPayload.tolerance a / 3))

def complement (a : Args) : ℚ :=
  max 1 (IdPayload.size a ^ (20 * IdInput.degree a))

theorem ident_polytime : ComputableInPolyTime ident encArgs encRat := by
  have ht := rat_natCast' (unary_to_binary.comp IdInput.degree_polytime)
  exact rat_mul'
    (FrameAux.Linear.rat_pow' (FrameAux.Linear.rat_pow' IdPayload.size_polytime
      (const 2)) (unary_mul' (const 29) IdInput.degree_polytime))
    (rat_add' (const 1) (rat_mul' (rat_add' (rat_mul' (const 2) ht) (const 1))
      (FrameAux.Linear.rat_pow' IdPayload.size_polytime
        (unary_add' (unary_mul' (const 16) IdInput.degree_polytime) (const 1)))))

theorem projection_polytime : ComputableInPolyTime projection encArgs encRat := by
  have hτ := rat_div' IdPayload.tolerance_polytime (const 3)
  exact rat_max' (const 1) (rat_div' (rat_add' ident_polytime
    (rat_mul' (rat_add' (const 2) hτ)
      (FrameAux.Linear.rat_pow' (rat_natCast' (unary_to_binary.comp
        (show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary
          by fun_prop))) (const 2)))) hτ)

theorem complement_polytime : ComputableInPolyTime complement encArgs encRat :=
  rat_max' (const 1) (FrameAux.Linear.rat_pow' IdPayload.size_polytime
    (unary_mul' (const 20) IdInput.degree_polytime))

/-- A factorial-free interpolation bound with polynomially many bits. -/
def interpolation (e : ℕ) : ℚ := (e + 1 : ℚ) ^ ((e + 1) ^ 2)

theorem interpolation_polytime : ComputableInPolyTime interpolation encUnary encRat :=
  FrameAux.Linear.rat_pow'
    (rat_add' (rat_natCast' unary_to_binary) (const 1))
    ((unary_pow 2).comp (unary_add' id' (const 1)))

def ball (d e m : ℕ) (ε M : ℚ) : ℚ :=
  2 + (m + 1 : ℚ) * (d + 1 : ℚ) ^ e * interpolation e ^ (2 * d) *
    (e + 1 : ℚ) ^ d * (e + 1 : ℚ) ^ d *
      (2 * M + 2 * ε + 6 * (d + 1 : ℚ) ^ 2) * (e : ℚ) ^ (2 * e)

theorem ball_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d e m : α → ℕ} {ε M : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (he : ComputableInPolyTime e enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hε : ComputableInPolyTime ε enc encRat)
    (hM : ComputableInPolyTime M enc encRat) :
    ComputableInPolyTime (fun a ↦ ball (d a) (e a) (m a) (ε a) (M a)) enc encRat := by
  have hdQ := rat_add' (rat_natCast' (unary_to_binary.comp hd)) (const 1)
  have heQ := rat_natCast' (unary_to_binary.comp he)
  have hep := FrameAux.Linear.rat_pow' (rat_add' heQ (const 1)) hd
  exact rat_add' (const 2) (rat_mul' (rat_mul' (rat_mul' (rat_mul' (rat_mul'
    (rat_mul' (rat_add' (rat_natCast' (unary_to_binary.comp hm)) (const 1))
      (FrameAux.Linear.rat_pow' hdQ he))
    (FrameAux.Linear.rat_pow' (interpolation_polytime.comp he)
      (unary_mul' (const 2) hd))) hep) hep)
    (rat_add' (rat_add' (rat_mul' (const 2) hM) (rat_mul' (const 2) hε))
      (rat_mul' (const 6) (FrameAux.Linear.rat_pow' hdQ (const 2)))))
    (FrameAux.Linear.rat_pow' heQ (unary_mul' (const 2) he)))

def norm (d K m : ℕ) (ε M : ℚ) : ℚ :=
  let b := (d + 1 : ℚ) ^ K
  ((m + 1 : ℚ) * (2 * (M + 1) * (d + 1 : ℚ) ^ (2 * K) * b ^ 5) +
    b * (b + 1) ^ 2 + ((d + 1 : ℚ) ^ 2 + 2) ^ 2) / (4 * ε) + 1

theorem norm_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d K m : α → ℕ} {ε M : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hK : ComputableInPolyTime K enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hε : ComputableInPolyTime ε enc encRat)
    (hM : ComputableInPolyTime M enc encRat) :
    ComputableInPolyTime (fun a ↦ norm (d a) (K a) (m a) (ε a) (M a)) enc encRat := by
  have hdQ := rat_add' (rat_natCast' (unary_to_binary.comp hd)) (const 1)
  have hb := FrameAux.Linear.rat_pow' hdQ hK
  exact rat_add' (rat_div'
    (rat_add' (rat_add' (rat_mul'
      (rat_add' (rat_natCast' (unary_to_binary.comp hm)) (const 1))
      (rat_mul' (rat_mul' (rat_mul' (const 2) (rat_add' hM (const 1)))
        (FrameAux.Linear.rat_pow' hdQ (unary_mul' (const 2) hK)))
        (FrameAux.Linear.rat_pow' hb (const 5))))
      (rat_mul' hb (FrameAux.Linear.rat_pow' (rat_add' hb (const 1)) (const 2))))
      (FrameAux.Linear.rat_pow'
        (rat_add' (FrameAux.Linear.rat_pow' hdQ (const 2)) (const 2)) (const 2)))
    (rat_mul' (const 4) hε)) (const 1)

def ballInput (a : Args) : ℚ :=
  ball a.1.1 (4 * IdInput.degree a) (2 * IdInput.degree a + 1)
    (IdPayload.tolerance a) (projection a)

def normInput (a : Args) : ℚ :=
  norm a.1.1 (8 * IdInput.degree a) (2 * IdInput.degree a + 1)
    (IdPayload.tolerance a) (complement a)

theorem ballInput_polytime : ComputableInPolyTime ballInput encArgs encRat :=
  ball_polytime_of (by fun_prop) (unary_mul' (const 4) IdInput.degree_polytime)
    (unary_add' (unary_mul' (const 2) IdInput.degree_polytime) (const 1))
    IdPayload.tolerance_polytime projection_polytime

theorem normInput_polytime : ComputableInPolyTime normInput encArgs encRat :=
  norm_polytime_of (by fun_prop) (unary_mul' (const 8) IdInput.degree_polytime)
    (unary_add' (unary_mul' (const 2) IdInput.degree_polytime) (const 1))
    IdPayload.tolerance_polytime complement_polytime

noncomputable section

theorem ident_cast (a : Args) :
    (ident a : ℝ) = IdCov.SubspaceAux.identBound a.1.1 (field a 0) (field a 10) := by
  simp only [ident, IdCov.SubspaceAux.identBound, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_add, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, IdPayload.size_cast,
    IdInput.degree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

theorem projection_cast (a : Args) :
    (projection a : ℝ) =
      IdCov.SubspaceAux.projectionBound a.1.1 (field a 0) (field a 10) := by
  simp only [projection, IdCov.SubspaceAux.projectionBound, Rat.cast_max,
    Rat.cast_one, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_pow, Rat.cast_natCast, ident_cast, IdPayload.tolerance, IdCov.tauStar]

theorem complement_cast (a : Args) :
    (complement a : ℝ) = max 1 (IdCov.sizeParameter a.1.1 (field a 0) (field a 10) ^
      (20 * IdCov.tDegree (field a 0))) := by
  simp only [complement, Rat.cast_max, Rat.cast_one, Rat.cast_pow,
    IdPayload.size_cast, IdInput.degree]

theorem interpolation_le (e : ℕ) : (SoS.interpBound e : ℝ) ≤ (interpolation e : ℝ) := by
  have hb : SoS.interpBound e ≤ (e + 1) ^ ((e + 1) ^ 2) := by
    unfold SoS.interpBound
    apply (Nat.mul_le_mul_right _ (Nat.factorial_le_pow (e + 1))).trans_eq
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  unfold interpolation
  exact_mod_cast hb

theorem ball_le {d : ℕ} (A : List (RPoly d)) (e m : ℕ) (ε M : ℚ) (X : ℝ)
    (hm : A.length ≤ m) (hε : 0 ≤ ε) (hM : 0 ≤ M) :
    ballBound (plainSystem A) (2 * e) ε M X ≤ (ball d e m ε M : ℝ) := by
  have he : (2 * e) / 2 = e := by omega
  simp only [ballBound, plainSystem, List.length_nil, Nat.cast_zero, zero_mul,
    add_zero, he, gridConst, ball, Rat.cast_add, Rat.cast_ofNat, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_pow]
  have hεR : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hMR : (0 : ℝ) ≤ M := by exact_mod_cast hM
  have hmR : (A.length : ℝ) ≤ m := by exact_mod_cast hm
  have hI := interpolation_le e
  have hI0 : (0 : ℝ) ≤ interpolation e := by unfold interpolation; positivity
  have heR : ((2 * e : ℕ) : ℝ) / 2 = e := by push_cast; ring
  simp only [heR, mul_assoc]
  gcongr

theorem norm_le {d : ℕ} (A : List (RPoly d)) (K m : ℕ) (ε M : ℚ)
    (hm : A.length ≤ m) (hε : 0 < ε ∧ ε ≤ 1) (hM : 0 ≤ M) :
    nestedNorm (plainSystem A) K ε M ≤ (norm d K m ε M : ℝ) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε.1
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε.2
  have hs : (ε : ℝ) ≤ Real.sqrt (ε : ℝ) := by
    apply (Real.le_sqrt hεR.le hεR.le).mpr
    nlinarith only [hεR, hεR1]
  have hMR : (0 : ℝ) ≤ M := by exact_mod_cast hM
  have hmR : (A.length : ℝ) ≤ m := by exact_mod_cast hm
  simp only [nestedNorm, plainSystem, List.length_nil, Nat.cast_zero, add_zero,
    norm, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat]
  apply add_le_add _ le_rfl
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4))).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr

theorem norm_one_le (d K m : ℕ) (ε M : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M) :
    1 ≤ norm d K m ε M := by
  unfold norm
  have he : 0 ≤ ((m + 1 : ℚ) *
      (2 * (M + 1) * (d + 1 : ℚ) ^ (2 * K) * ((d + 1 : ℚ) ^ K) ^ 5) +
        (d + 1 : ℚ) ^ K * ((d + 1 : ℚ) ^ K + 1) ^ 2 +
          ((d + 1 : ℚ) ^ 2 + 2) ^ 2) / (4 * ε) := by positivity
  linarith only [he]

theorem input_ball (a : Args) (k : ℕ) (Q : ℕ → QPoly a.1.1) :
    let J := IdCov.SubspaceAux.input k a.1.1 (field a 0) (field a 10) Q
    ballBound J.system J.degree J.tolerance J.M₁ J.X ≤ (ballInput a : ℝ) := by
  have hε : 0 ≤ IdPayload.tolerance a := by
    unfold IdPayload.tolerance IdCov.epsilonR
    positivity
  have hM : 0 ≤ projection a := (by norm_num : (0 : ℚ) ≤ 1).trans (le_max_left _ _)
  have hb := ball_le
    (IdCov.system (IdCov.SubspaceAux.roundedMoments a.1.1 (field a 0) (field a 10) Q)
      (IdInput.degree a) (IdCov.epsilonSys (field a 0) (field a 10)))
    (4 * IdInput.degree a) (2 * IdInput.degree a + 1)
    (IdPayload.tolerance a) (projection a) 1
    (IdCov.SubspaceAux.system_length _ _ _) hε hM
  rw [projection_cast] at hb
  simpa only [IdCov.SubspaceAux.input, IdInput.degree, IdPayload.tolerance, ballInput,
    show 2 * (4 * IdCov.tDegree (field a 0)) = 8 * IdCov.tDegree (field a 0) by omega]
    using hb

theorem input_norm (a : Args) (k : ℕ) (Q : ℕ → QPoly a.1.1)
    (hβ : 0 < field a 10 ∧ field a 10 ≤ 1 / 4) :
    let J := IdCov.SubspaceAux.input k a.1.1 (field a 0) (field a 10) Q
    nestedNorm J.system J.degree J.tolerance J.M₂ ≤ (normInput a : ℝ) := by
  have hε := (IdCov.SubspaceAux.bounds (field a 0) (field a 10) hβ).rounding
  have hM : 0 ≤ complement a := (by norm_num : (0 : ℚ) ≤ 1).trans (le_max_left _ _)
  have hb := norm_le
    (IdCov.system (IdCov.SubspaceAux.roundedMoments a.1.1 (field a 0) (field a 10) Q)
      (IdInput.degree a) (IdCov.epsilonSys (field a 0) (field a 10)))
    (8 * IdInput.degree a) (2 * IdInput.degree a + 1)
    (IdPayload.tolerance a) (complement a)
    (IdCov.SubspaceAux.system_length _ _ _) hε hM
  rw [complement_cast] at hb
  exact hb

theorem normInput_one_le (a : Args) : 1 ≤ normInput a := by
  apply norm_one_le
  · unfold IdPayload.tolerance IdCov.epsilonR
    positivity
  · exact (by norm_num : (0 : ℚ) ≤ 1).trans (le_max_left _ _)

end

end ABBKS26.Assembly.Exec.RefineSynth.IdNorms
