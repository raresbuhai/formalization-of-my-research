module

public import ABBKS26.Assembly.ExecData
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-! # Arithmetic and bounded leakage iteration for the executable schedule -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.ScheduleAux

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

private theorem rat_pow {α : Type} {enc : α ↪ List Bool} {f : α → ℚ} {n : α → ℕ}
    (hf : ComputableInPolyTime f enc encRat)
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun x ↦ f x ^ n x) enc encRat := by
  simpa only [Function.comp_def, List.prod_replicate] using rat_prod.comp (replicate hn hf)

@[local fun_prop]
private theorem rat_pow_const {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) (n : ℕ) :
    ComputableInPolyTime (fun x ↦ f x ^ n) enc encRat := rat_pow hf (const n)

@[local fun_prop]
private theorem rat_ceil {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ ⌈f x⌉₊) enc encNat := by
  have h := ComputableTidilyInPolyTime.intBin_toNat.comp
    (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hf)).tidy)
  refine (ComputableInPolyTime.of_tidy h).of_enc_eq fun x ↦ ?_
  congr 1

@[local fun_prop]
private theorem dyadic_up {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ dyadicUp (f x)) enc encRat := by
  unfold dyadicUp
  exact rat_two_pow' (binary_clog_two.comp
    (ite_decide (by
      exact .of_tidy (ComputableTidilyInPolyTime.binary_le' (const 1).tidy
        (rat_ceil hf).tidy)) (rat_ceil hf) (const 1)))

@[local fun_prop]
private theorem dyadic_down {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ dyadicDown (f x)) enc encRat := by
  unfold dyadicDown
  apply ite_decide (rat_lt' (const 0) hf)
  · apply rat_inv'
    apply rat_two_pow'
    exact unary_add' (binary_clog_two.comp (rat_ceil (rat_div' (const 1) hf)))
      (const 1)
  · exact const 0

@[local fun_prop]
private theorem sqrt_up {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ sqrtUp (f x)) enc encRat := by
  unfold sqrtUp
  fun_prop

@[local fun_prop]
private theorem log_inv {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ logInv (f x)) enc encUnary := by
  unfold logInv
  exact binary_clog_two.comp (by fun_prop)

@[local fun_prop]
private theorem degree_unary {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ IdCov.tDegree (f x)) enc encUnary := by
  unfold IdCov.tDegree
  exact unary_add' (log_inv hf) (const 3)

@[local fun_prop]
private theorem degree_binary {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ IdCov.tDegree (f x)) enc encNat :=
  unary_to_binary.comp (degree_unary hf)

@[local fun_prop]
private theorem centered_gamma {α : Type} {enc : α ↪ List Bool} {w b : α → ℚ}
    (hw : ComputableInPolyTime w enc encRat) (hb : ComputableInPolyTime b enc encRat) :
    ComputableInPolyTime (fun x ↦ Centered.gammaStar (w x) (b x)) enc encRat := by
  unfold Centered.gammaStar Centered.delta Centered.nu
  fun_prop

@[local fun_prop]
private theorem centered_eta {α : Type} {enc : α ↪ List Bool} {w b : α → ℚ}
    (hw : ComputableInPolyTime w enc encRat) (hb : ComputableInPolyTime b enc encRat) :
    ComputableInPolyTime (fun x ↦ Centered.etaStar (w x) (b x)) enc encRat := by
  unfold Centered.etaStar Centered.delta Centered.nu
  fun_prop

@[local fun_prop]
private theorem identical_gamma {α : Type} {enc : α ↪ List Bool} {b : α → ℚ}
    (hb : ComputableInPolyTime b enc encRat) :
    ComputableInPolyTime (fun x ↦ IdCov.gammaStar (b x)) enc encRat := by
  unfold IdCov.gammaStar IdCov.epsilonR
  fun_prop

@[local fun_prop]
private theorem identical_tau {α : Type} {enc : α ↪ List Bool} {b : α → ℚ}
    (hb : ComputableInPolyTime b enc encRat) :
    ComputableInPolyTime (fun x ↦ IdCov.tauStar (b x)) enc encRat := by
  unfold IdCov.tauStar IdCov.epsilonR
  fun_prop

@[local fun_prop]
private theorem identical_eta {α : Type} {enc : α ↪ List Bool} {w b : α → ℚ}
    (hw : ComputableInPolyTime w enc encRat) (hb : ComputableInPolyTime b enc encRat) :
    ComputableInPolyTime (fun x ↦ IdCov.etaStar (w x) (b x)) enc encRat := by
  unfold IdCov.etaStar IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
  apply rat_div'
  · apply rat_div' _ (const 4)
    apply rat_pow (by fun_prop)
    exact unary_mul' (const 4) (degree_unary hw)
  · apply rat_pow (by fun_prop)
    exact unary_add' (unary_mul' (const 4) (degree_unary hw)) (const 2)

def withLeakage (q : ℚ) : StepParams := { Schedule.terminal 0 with leakage := q }

abbrev StepInput := ℚ × ℕ × ℚ
abbrev encStepInput := encPair encRat (encPair encUnary encRat)

def stepList (mode : Mode) (x : StepInput) : Vector :=
  paramsList (Schedule.step mode x.1 x.2.1 (withLeakage x.2.2))

-- Each arithmetic stage has its own certificate, keeping the composition proofs small.
def phi (x : StepInput) : ℚ := x.2.2 / 4
def window (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then 1 / 2 else (1 / (16 * x.2.1 : ℚ)) * (phi x / 2) ^ 9 / 16
def mass (mode : Mode) (x : StepInput) : ℚ := x.1 * window mode x / 8
def tail (mode : Mode) (x : StepInput) : ℚ :=
  min (phi x / 64) (min (mass mode x / 64) (x.1 / 4096))
def kval (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then dyadicUp (32 / phi x) else 1
def wf (x : StepInput) : ℚ := dyadicUp (8 * (40 / x.1) * sqrtUp (1 / phi x))
def df (mode : Mode) (x : StepInput) : ℚ :=
  dyadicUp (max (4 * wf x) (4 * (40 / x.1) * sqrtUp (1 / tail mode x)))
def radius (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then
    dyadicUp (2 * (x.2.1 - 1 : ℚ) * (2 * df mode x + 3 * wf x) + 1)
  else dyadicUp (sqrtUp 40 / (x.1 / 2))
def sigma (mode : Mode) (x : StepInput) : ℚ :=
  600 / (x.1 / 2) ^ 2 + 2 * radius mode x ^ 2
def beta (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then
    dyadicDown ((128 * (4 / x.1))⁻¹ *
      (tail mode x / (1024 * kval mode x ^ 2)) ^ (2 * (x.2.1 - 1)))
  else dyadicDown (min (1 / 100) (1 / sqrtUp (10 ^ 6 * (x.2.1 : ℚ) ^ 2 / tail mode x)))
def gamma (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then Centered.gammaStar (x.1 / 2) (beta mode x)
  else IdCov.gammaStar (beta mode x)
def moment (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then Centered.etaStar (x.1 / 2) (beta mode x)
  else IdCov.etaStar x.1 (beta mode x) / 4
def momentBound (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then 2 * (80 / x.1) ^ 4
  else 2 * (80 * IdCov.tDegree x.1 / x.1) ^ (4 * IdCov.tDegree x.1)
def req (mode : Mode) (x : StepInput) : ℚ :=
  dyadicDown (min (1 / (64000 * sigma mode x))
    (min ((x.1 / 2) / 400) (min (gamma mode x ^ 2 / (10 ^ 10 * sigma mode x))
      (min (moment mode x / (10 ^ 4 * momentBound mode x)) (min (mass mode x / 64)
        (min (phi x / 64) (min (x.1 / 4096) (x.1 ^ 2 / 10 ^ 8))))))))
def leakage (mode : Mode) (x : StepInput) : ℚ :=
  dyadicDown (min (x.1 * req mode x / 128) (min (x.2.2 / 4) (x.1 * window mode x / 1024)))
def separation (mode : Mode) (x : StepInput) : ℚ :=
  if mode = .centered then
    dyadicUp (max (2 * sqrtUp ((4 / x.1) / (3 * beta mode x ^ 8)))
      (max (4 * sqrtUp (10000 * sigma mode x / (x.1 / 2) + 10) * (4 / x.1) /
        (9 * beta mode x ^ 16)) 1))
  else dyadicUp (sqrtUp (32 / (x.1 * IdCov.tauStar (beta mode x))))

@[local fun_prop]
private theorem weight_polytime :
    ComputableInPolyTime (fun x : StepInput ↦ x.1) encStepInput encRat := fst _ _

@[local fun_prop]
private theorem k_unary_polytime :
    ComputableInPolyTime (fun x : StepInput ↦ x.2.1) encStepInput encUnary :=
  (fst _ _).comp (snd _ _)

@[local fun_prop]
private theorem k_binary_polytime :
    ComputableInPolyTime (fun x : StepInput ↦ x.2.1) encStepInput encNat :=
  unary_to_binary.comp k_unary_polytime

@[local fun_prop]
private theorem q_polytime :
    ComputableInPolyTime (fun x : StepInput ↦ x.2.2) encStepInput encRat :=
  (snd _ _).comp (snd _ _)

@[local fun_prop]
private theorem phi_polytime : ComputableInPolyTime phi encStepInput encRat := by
  unfold phi
  fun_prop

@[local fun_prop]
private theorem window_polytime (mode : Mode) :
    ComputableInPolyTime (window mode) encStepInput encRat := by
  cases mode <;> unfold window <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

@[local fun_prop]
private theorem mass_polytime (mode : Mode) :
    ComputableInPolyTime (mass mode) encStepInput encRat := by
  unfold mass
  fun_prop

@[local fun_prop]
private theorem tail_polytime (mode : Mode) :
    ComputableInPolyTime (tail mode) encStepInput encRat := by
  unfold tail
  fun_prop

@[local fun_prop]
private theorem kval_polytime (mode : Mode) :
    ComputableInPolyTime (kval mode) encStepInput encRat := by
  cases mode <;> unfold kval <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

@[local fun_prop]
private theorem wf_polytime : ComputableInPolyTime wf encStepInput encRat := by
  unfold wf
  fun_prop

@[local fun_prop]
private theorem df_polytime (mode : Mode) :
    ComputableInPolyTime (df mode) encStepInput encRat := by
  unfold df
  fun_prop

@[local fun_prop]
private theorem radius_polytime (mode : Mode) :
    ComputableInPolyTime (radius mode) encStepInput encRat := by
  cases mode <;> unfold radius <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

@[local fun_prop]
private theorem sigma_polytime (mode : Mode) :
    ComputableInPolyTime (sigma mode) encStepInput encRat := by
  unfold sigma
  fun_prop

@[local fun_prop]
private theorem beta_polytime (mode : Mode) :
    ComputableInPolyTime (beta mode) encStepInput encRat := by
  cases mode <;> unfold beta <;> simp only [reduceCtorEq, ite_true, ite_false]
  · apply dyadic_down
    apply rat_mul' (by fun_prop)
    exact rat_pow (by fun_prop) (unary_mul' (const 2)
      (unary_sub' k_unary_polytime (const 1)))
  · fun_prop

@[local fun_prop]
private theorem gamma_polytime (mode : Mode) :
    ComputableInPolyTime (gamma mode) encStepInput encRat := by
  cases mode <;> unfold gamma <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

@[local fun_prop]
private theorem moment_polytime (mode : Mode) :
    ComputableInPolyTime (moment mode) encStepInput encRat := by
  cases mode <;> unfold moment <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

@[local fun_prop]
private theorem moment_bound_polytime (mode : Mode) :
    ComputableInPolyTime (momentBound mode) encStepInput encRat := by
  cases mode <;> unfold momentBound <;> simp only [reduceCtorEq, ite_true, ite_false]
  · fun_prop
  · apply rat_mul' (const 2)
    exact rat_pow (by fun_prop) (unary_mul' (const 4) (degree_unary weight_polytime))

@[local fun_prop]
private theorem req_polytime (mode : Mode) :
    ComputableInPolyTime (req mode) encStepInput encRat := by
  unfold req
  fun_prop

@[local fun_prop]
private theorem leakage_polytime (mode : Mode) :
    ComputableInPolyTime (leakage mode) encStepInput encRat := by
  unfold leakage
  fun_prop

@[local fun_prop]
private theorem separation_polytime (mode : Mode) :
    ComputableInPolyTime (separation mode) encStepInput encRat := by
  cases mode <;> unfold separation <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fun_prop

private theorem step_list_polytime (mode : Mode) :
    ComputableInPolyTime (stepList mode) encStepInput encVector := by
  have h : ComputableInPolyTime (fun x : StepInput ↦
      [x.1, phi x, window mode x, mass mode x, tail mode x, kval mode x, wf x, df mode x,
        radius mode x, sigma mode x, beta mode x, gamma mode x, moment mode x,
        dyadicDown (gamma mode x / 10000), req mode x, leakage mode x, separation mode x])
      encStepInput encVector := by fun_prop
  exact h.of_enc_eq fun _ ↦ rfl

private theorem input_weight_polytime :
    ComputableInPolyTime Input.wmin encInput encRat := by
  have h : ComputableInPolyTime
      (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
      (encPair encNat (encPair encRat
        (encPair encRat (encPair encRat encPoints)))) := of_eq fun _ ↦ rfl
  exact (fst _ _).comp ((snd _ _).comp h)

abbrev ParamInput := (Input × ℕ) × ℕ
abbrev encParamInput := encPair encPadded encUnary

def initial (x : ParamInput) : ℚ := (Schedule.terminal x.1.1.wmin).leakage
def boundedK (x : ParamInput) : ℕ := min x.1.2 x.1.1.k
def count (x : ParamInput) : ℕ := min x.1.2 (x.1.1.k - 2 - x.2)

def boundedStep (mode : Mode) (x : ParamInput) (q : ℚ) : ℚ :=
  cap encRat x.1.2 (initial x) (leakage mode (x.1.1.wmin, boundedK x, q))

def loop (mode : Mode) (x : ParamInput) : ℚ :=
  (boundedStep mode x)^[count x] (initial x)

def paramRun (mode : Mode) (x : ParamInput) : Vector :=
  if x.1.1.k - 1 - x.2 = 0 then paramsList (Schedule.terminal x.1.1.wmin)
  else stepList mode (x.1.1.wmin, boundedK x, loop mode x)

@[local fun_prop]
private theorem param_weight_polytime :
    ComputableInPolyTime (fun x : ParamInput ↦ x.1.1.wmin) encParamInput encRat :=
  input_weight_polytime.comp ((fst _ _).comp (fst _ _))

@[local fun_prop]
private theorem fuel_polytime :
    ComputableInPolyTime (fun x : ParamInput ↦ x.1.2) encParamInput encUnary :=
  (snd _ _).comp (fst _ _)

@[local fun_prop]
private theorem input_k_polytime :
    ComputableInPolyTime (fun x : ParamInput ↦ x.1.1.k) encParamInput encNat :=
  k_polytime.comp ((fst _ _).comp (fst _ _))

@[local fun_prop]
private theorem index_polytime :
    ComputableInPolyTime (fun x : ParamInput ↦ x.2) encParamInput encNat :=
  unary_to_binary.comp (snd _ _)

@[local fun_prop]
private theorem initial_polytime : ComputableInPolyTime initial encParamInput encRat := by
  unfold initial Schedule.terminal
  fun_prop

@[local fun_prop]
private theorem bounded_k_polytime : ComputableInPolyTime boundedK encParamInput encUnary :=
  binary_min_unary' fuel_polytime input_k_polytime

private theorem count_polytime : ComputableInPolyTime count encParamInput encUnary :=
  binary_min_unary' fuel_polytime
    (binary_sub' (binary_sub' input_k_polytime (const 2)) index_polytime)

private theorem bounded_step_polytime (mode : Mode) :
    ComputableInPolyTime (fun x : ParamInput × ℚ ↦ boundedStep mode x.1 x.2)
      (encPair encParamInput encRat) encRat := by
  have hq := leakage_polytime mode |>.comp
    ((param_weight_polytime.comp (fst _ _)).prod
      ((bounded_k_polytime.comp (fst _ _)).prod (snd _ _)))
  have hl := ComputableTidilyInPolyTime.encoding_length encRat |>.comp hq.tidy
  unfold boundedStep cap
  exact ite_decide (.of_tidy (ComputableTidilyInPolyTime.unary_le'
    hl (fuel_polytime.comp (fst _ _)).tidy)) hq (initial_polytime.comp (fst _ _))

private theorem bounded_step_length (mode : Mode) (x : ParamInput) (q : ℚ) :
    (encRat (boundedStep mode x q)).length ≤ x.1.2 + (encRat (initial x)).length := by
  unfold boundedStep cap
  split_ifs with h
  · exact h.trans (Nat.le_add_right _ _)
  · exact Nat.le_add_left _ _

private theorem loop_polytime (mode : Mode) :
    ComputableInPolyTime (loop mode) encParamInput encRat := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.iterateWith
    (step := boundedStep mode) ComputableTidilyInPolyTime.id' count_polytime.tidy
    initial_polytime.tidy (bounded_step_polytime mode).tidy
    (fuel_polytime.tidy.polyBounded.add initial_polytime.polyBounded_length)
  intro x i _
  cases i with
  | zero => exact Nat.le_add_left _ _
  | succ i =>
    rw [Function.iterate_succ_apply']
    exact bounded_step_length mode x _

private theorem param_run_polytime (mode : Mode) :
    ComputableInPolyTime (paramRun mode) encParamInput encVector := by
  have ht : ComputableInPolyTime
      (fun x : ParamInput ↦ paramsList (Schedule.terminal x.1.1.wmin))
      encParamInput encVector := by
    unfold paramsList Schedule.terminal
    fun_prop
  unfold paramRun
  apply ite_decide
  · exact .of_tidy (ComputableTidilyInPolyTime.decide_eq'
      (binary_sub' (binary_sub' input_k_polytime (const 1)) index_polytime).tidy (const 0).tidy)
  · exact ht
  · exact (step_list_polytime mode).comp
      (param_weight_polytime.prod (bounded_k_polytime.prod (loop_polytime mode)))

/-- The loop count and every stored leakage are capped by the supplied unary fuel. -/
def run (mode : Mode) (x : Input × ℕ) : Points :=
  (List.range (min x.2 x.1.k)).map fun h ↦ paramRun mode (x, h)

theorem run_polytime (mode : Mode) : ComputableInPolyTime (run mode) encPadded encPoints := by
  have hr := ComputableTidilyInPolyTime.range.comp
    (binary_min_unary' (snd _ _) (k_polytime.comp (fst _ _))).tidy
  exact mapWithInput (.of_tidy hr) (param_run_polytime mode)

private theorem local_budget_pos (mode : Mode) (k n d : ℕ) (ps : ℕ → StepParams) :
    0 < localBudget mode k n d ps := by
  unfold localBudget
  apply Nat.mul_pos
  · exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  · split_ifs
    · exact Nat.zero_lt_one
    · exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))

private theorem k_le_local_budget (mode : Mode) (k n d : ℕ) (ps : ℕ → StepParams) :
    k ≤ localBudget mode k n d ps := by
  have hb : 2 ≤ branchCap mode k ps + 1 := by unfold branchCap; omega
  have hp : k ≤ (branchCap mode k ps + 1) ^ (k + 1) :=
    (Nat.lt_two_pow_self.le).trans
      ((Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)).trans
        (Nat.pow_le_pow_left hb _))
  have hn : 0 < (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) := by positivity
  have hd : 0 < (if mode = .centered then 1 else
      (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) * (logInv (ps 0).w + 3) ^ 2) *
            (idReserves k ps + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
              (logInv (ps 0).w + 3) ^ 2)) := by
    split_ifs
    · exact Nat.zero_lt_one
    · exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  calc
    k ≤ (branchCap mode k ps + 1) ^ (k + 1) := hp
    _ ≤ (branchCap mode k ps + 1) ^ (k + 1) *
        (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
      Nat.le_mul_of_pos_right _ hn
    _ ≤ localBudget mode k n d ps := Nat.le_mul_of_pos_right _ hd

theorem k_le_need (mode : Mode) (x : Input) : x.k ≤ need mode x := by
  have hp : 1 ≤ ((encInput x).length + 2) ^ 100 := one_le_pow₀ (by omega)
  unfold need
  split_ifs with hk
  · exact hk.trans hp
  · exact (k_le_local_budget mode x.k x.points.length (dim x.points)
      (Schedule.params mode x.wmin x.k)).trans
      ((Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega)))

private theorem ledger_room (mode : Mode) (x : Input) (hk : 2 ≤ x.k) :
    Schedule.ledger mode x.wmin x.k + 5 ≤ need mode x := by
  have hl := local_budget_pos mode x.k x.points.length (dim x.points)
    (Schedule.params mode x.wmin x.k)
  have hp : 4 ≤ ((encInput x).length + 2) ^ 100 := by
    exact (by norm_num : 4 ≤ (2 : ℕ) ^ 100).trans (Nat.pow_le_pow_left (by omega) _)
  rw [need, ite_eq_right (by omega : ¬x.k ≤ 1)]
  calc
    _ ≤ (Schedule.ledger mode x.wmin x.k + 2) * 4 := by omega
    _ ≤ _ := Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hl) hp

def ledgerNumbers (mode : Mode) (w : ℚ) (k : ℕ) : List ℕ :=
  ((List.range k).map (Schedule.params mode w k)).flatMap fun p ↦
    [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
      ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]

private theorem leakage_ledger (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k) :
    ⌈1 / (Schedule.params mode w k h).leakage⌉₊ ≤ Schedule.ledger mode w k := by
  let xs := (ledgerNumbers mode w k).map (· + 2)
  have hall : ∀ a ∈ xs, 1 ≤ a := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    omega
  have hm : ⌈1 / (Schedule.params mode w k h).leakage⌉₊ + 2 ∈ xs := by
    apply List.mem_map.mpr
    refine ⟨_, List.mem_flatMap.mpr ?_, rfl⟩
    exact ⟨Schedule.params mode w k h, List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩,
      by simp⟩
  have he := List.single_le_prod hall _ hm
  have hp : xs.prod ≤ Schedule.ledger mode w k := by
    apply le_trans _ (Schedule.ledgerCore_le mode w k)
    change xs.prod ≤ xs.prod * (Schedule.nWeight mode w k + 2) *
      (treeCap mode k (Schedule.params mode w k) + 2) *
        (⌈1 / Schedule.etaReq mode w k⌉₊ + 2)
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans
      ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega)))
  omega

private theorem zero_length : (encRat (0 : ℚ)).length = 4 := by
  change (encPair encIntBin encNat ((0 : ℚ).num, (0 : ℚ).den)).length = 4
  rw [length_encPair, length_encIntBin]
  norm_num [encNat_apply, Nat.size_eq_bits_len]

private theorem inverse_nat_length (d : ℕ) :
    (encRat (d : ℚ)⁻¹).length ≤ d + 5 := by
  by_cases hd : d = 0
  · subst d
    simp only [Nat.cast_zero, inv_zero, zero_length]
    omega
  · change (encPair encIntBin encNat ((d : ℚ)⁻¹.num, (d : ℚ)⁻¹.den)).length ≤ d + 5
    rw [length_encPair, length_encIntBin, Rat.inv_natCast_num_of_pos (by omega),
      Rat.inv_natCast_den_of_pos (by omega)]
    simp only [Int.natAbs_one, encNat_apply, Nat.size_eq_bits_len, Nat.size_one]
    have h := Nat.size_le_self d
    omega

private theorem dyadic_down_length (q : ℚ) :
    (encRat (dyadicDown q)).length ≤ ⌈1 / dyadicDown q⌉₊ + 5 := by
  unfold dyadicDown
  split_ifs
  · have he : (2 : ℚ) ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1) =
        ((2 ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1) : ℕ) : ℚ) := by push_cast; rfl
    rw [he]
    change (encRat ((2 ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1) : ℕ) : ℚ)⁻¹).length ≤
      ⌈1 / ((2 ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1) : ℕ) : ℚ)⁻¹⌉₊ + 5
    simpa only [one_div, inv_inv, Nat.ceil_natCast] using
      inverse_nat_length (2 ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1))
  · simp only [div_zero, Nat.ceil_zero, zero_length]
    omega

private theorem step_depends (mode : Mode) (w : ℚ) (k : ℕ) (p : StepParams) :
    Schedule.step mode w k (withLeakage p.leakage) = Schedule.step mode w k p := by
  rfl

private theorem iterate_leakage (mode : Mode) (w : ℚ) (k i : ℕ) :
    (leakage mode ∘ fun q ↦ (w, k, q))^[i] (Schedule.terminal w).leakage =
      ((Schedule.step mode w k)^[i] (Schedule.terminal w)).leakage := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    change (Schedule.step mode w k (withLeakage _)).leakage = _
    rw [step_depends]

private theorem iterate_leakage_length (mode : Mode) (w : ℚ) (k i : ℕ)
    (hi : 0 < i) (hik : i ≤ k - 1) :
    (encRat ((leakage mode ∘ fun q ↦ (w, k, q))^[i]
      (Schedule.terminal w).leakage)).length ≤ Schedule.ledger mode w k + 5 := by
  rw [iterate_leakage]
  have he : k - 1 - (k - 1 - i) = i := by omega
  have hl := leakage_ledger mode w k (k - 1 - i) (by omega)
  unfold Schedule.params at hl
  rw [he] at hl
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [Function.iterate_succ_apply'] at hl ⊢
  exact (dyadic_down_length _).trans (Nat.add_le_add_right hl 5)

private theorem loop_agrees (mode : Mode) (x : Input) (fuel h : ℕ)
    (hk : 2 ≤ x.k) (hf : need mode x ≤ fuel) :
    loop mode ((x, fuel), h) =
      (leakage mode ∘ fun q ↦ (x.wmin, x.k, q))^[x.k - 2 - h]
        (Schedule.terminal x.wmin).leakage := by
  have hkf := (k_le_need mode x).trans hf
  have hn : x.k - 2 - h ≤ fuel := by omega
  have hi : ∀ i, i ≤ x.k - 2 - h →
      (boundedStep mode ((x, fuel), h))^[i] (initial ((x, fuel), h)) =
        (leakage mode ∘ fun q ↦ (x.wmin, x.k, q))^[i]
          (Schedule.terminal x.wmin).leakage := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hik
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      unfold boundedStep boundedK
      rw [min_eq_right hkf]
      apply cap_eq
      change (encRat ((leakage mode ∘ fun q ↦ (x.wmin, x.k, q))
        ((leakage mode ∘ fun q ↦ (x.wmin, x.k, q))^[i]
          (Schedule.terminal x.wmin).leakage))).length ≤ fuel
      rw [← Function.iterate_succ_apply'
        (leakage mode ∘ fun q ↦ (x.wmin, x.k, q)) i (Schedule.terminal x.wmin).leakage]
      exact (iterate_leakage_length mode x.wmin x.k (i + 1) (by omega) (by omega)).trans
        ((ledger_room mode x hk).trans hf)
  unfold loop count
  rw [min_eq_right hn]
  exact hi _ le_rfl

private theorem param_run_agrees (mode : Mode) (x : Input) (fuel h : ℕ)
    (hf : need mode x ≤ fuel) :
    paramRun mode ((x, fuel), h) = paramsList (Schedule.params mode x.wmin x.k h) := by
  have hkf := (k_le_need mode x).trans hf
  unfold paramRun
  dsimp only
  split_ifs with hz
  · simp only [Schedule.params, hz, Function.iterate_zero, id_eq]
  · have hk : 2 ≤ x.k := by omega
    rw [loop_agrees mode x fuel h hk hf, iterate_leakage]
    unfold boundedK stepList
    dsimp only
    rw [min_eq_right hkf, step_depends]
    have he : x.k - 1 - h = (x.k - 2 - h) + 1 := by omega
    rw [Schedule.params, he, Function.iterate_succ_apply']

theorem run_agrees (mode : Mode) (x : Input) (fuel : ℕ) (hf : need mode x ≤ fuel) :
    run mode (x, fuel) =
      (List.range x.k).map (fun h ↦ paramsList (Schedule.params mode x.wmin x.k h)) := by
  unfold run
  rw [min_eq_right ((k_le_need mode x).trans hf)]
  exact List.map_congr_left fun h _ ↦ param_run_agrees mode x fuel h hf

end ABBKS26.Assembly.Exec.ScheduleAux
