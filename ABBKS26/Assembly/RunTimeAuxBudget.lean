module

public import ABBKS26.Assembly.RunTimeAuxComputable
public import ABBKS26.Assembly.RunTimeAuxPadding
public import ABBKS26.Assembly.RunTimeAuxBudgetAuxCost

/-!
# Clock-padded, constructible budgets

The budget uses only the parameter majorant, input length and dimension. Computing the clock
is a separate machine obligation; no cost certificate is inferred from mere computability.
-/

@[expose] public section

namespace ABBKS26.Assembly.RunTimeAuxBudget

noncomputable section

open Common
open Turing.MultiTapeTM
open RunTimeAuxPadding

theorem exponent_exists :
    ∃ a : ℕ, a + 1 = 1000000000 * (Rounding.solverConstant + 1) := by
  exact ⟨1000000000 * (Rounding.solverConstant + 1) - 1,
    Nat.sub_add_cancel (by omega)⟩

/-- Keep the universal exponent abstract while elaborating unary machine certificates. -/
abbrev A : ℕ := Classical.choose exponent_exists + 1

theorem A_eq : A = 1000000000 * (Rounding.solverConstant + 1) :=
  Classical.choose_spec exponent_exists
abbrev K : ℕ := 17 * A + 101

def exponent (clock : ℕ → ℕ) (a : ℕ) : ℕ :=
  Schedule.H (max 2 a) + clock (max 2 a) + a + 1

def base (clock : ℕ → ℕ) (a : ℕ) : ℕ := (2 ^ exponent clock a) ^ (A + 10)

def dimensionFactor (mode : Mode) (C : ℕ) (x : Input) : ℕ :=
  if mode = .centered then 1 else (dim x.points + 2) ^ (C * (logInv x.wmin ^ 2 + 1))

def budget (clock : ℕ → ℕ) (mode : Mode) (x : Input) : ℕ :=
  if Exec.Valid x then base clock ⌈1 / x.wmin⌉₊ * ((encInput x).length + 2) ^ K *
    dimensionFactor mode K x else 0

private theorem sample_size_le (x : Input) :
    x.points.length + dim x.points + 2 ≤ 2 * ((encInput x).length + 2) := by
  have hp : (encPoints x.points).length ≤ (encInput x).length := by
    change _ ≤ (Encoding.frame (Encoding.encNat x.k) ++
      (Encoding.frame (Encoding.encRat x.wmin) ++
        (Encoding.frame (Encoding.encRat x.Δ) ++
          (Encoding.frame (Encoding.encRat x.δ) ++ encPoints x.points)))).length
    simp only [List.length_append]
    omega
  have hn := Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) x.points
  have hd : dim x.points ≤ (encPoints x.points).length := by
    cases he : x.points with
    | nil => simp [dim]
    | cons row rows =>
      have hr := Rounding.RawAux.length_count Encoding.encRat row
      have hl := Rounding.RawAux.length_elem (Encoding.encList Encoding.encRat)
        (row :: rows) row (by simp)
      simpa only [dim, he, List.headD_cons, encPoints] using hr.trans hl
  change x.points.length ≤ (encPoints x.points).length at hn
  omega

private theorem treeCap_le_ledger (mode : Mode) (w : ℚ) (k : ℕ) :
    _root_.ABBKS26.Tree.treeCap mode k (Schedule.params mode w k) ≤
      Schedule.ledger mode w k := by
  let ps := (List.range k).map (Schedule.params mode w k)
  let numbers := ps.flatMap fun p ↦
    [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
      ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]
  let P := (numbers.map (fun a ↦ a + 2)).prod
  have hP : 0 < P := by
    apply lt_of_lt_of_le (by decide : 0 < 1)
    apply List.one_le_prod_of_one_le
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    omega
  apply le_trans _ (Schedule.ledgerCore_le mode w k)
  change _ ≤ P * (Schedule.nWeight mode w k + 2) *
    (_root_.ABBKS26.Tree.treeCap mode k (Schedule.params mode w k) + 2) *
      (⌈1 / Schedule.etaReq mode w k⌉₊ + 2)
  exact (Nat.le_add_right _ 2).trans
    ((Nat.le_mul_of_pos_left _ (Nat.mul_pos hP (by omega))).trans
      (Nat.le_mul_of_pos_right _ (by omega)))

private theorem parameter_budget_le (mode : Mode) (x : Input) (hx : Exec.Valid x)
    (hk : 2 ≤ x.k) :
    (Schedule.ledger mode x.wmin x.k + 2) *
      (_root_.ABBKS26.Tree.branchCap mode x.k (Schedule.params mode x.wmin x.k) + 1) ^
        (x.k + 1) ≤ (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 3 := by
  have hw : x.wmin ≤ 1 / 2 := by
    have hkq : (2 : ℚ) ≤ x.k := by exact_mod_cast hk
    nlinarith only [hx.2.2.1, mul_le_mul_of_nonneg_right hkq hx.1.le]
  have hledger := Schedule.majorant mode x.wmin x.k (max 2 ⌈1 / x.wmin⌉₊)
    ⟨hx.1, hw⟩ hx.2.2.1 hk (le_max_right _ _)
  have ht := (treeCap_le_ledger mode x.wmin x.k).trans hledger
  have hb :
      (_root_.ABBKS26.Tree.branchCap mode x.k (Schedule.params mode x.wmin x.k) + 1) ^
        (x.k + 1) ≤
      (_root_.ABBKS26.Tree.treeCap mode x.k (Schedule.params mode x.wmin x.k)) ^ 2 := by
    rw [_root_.ABBKS26.Tree.treeCap, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) *
        (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 2 :=
      Nat.mul_le_mul (by omega) (hb.trans (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by ring

private theorem reserved_parameter_budget_le (mode : Mode) (x : Input) (hx : Exec.Valid x)
    (hk : 2 ≤ x.k) :
    (Schedule.ledger mode x.wmin x.k + 2) *
      (_root_.ABBKS26.Tree.branchCap mode x.k (Schedule.params mode x.wmin x.k) + 1) ^
        (x.k + 1) *
      (if mode = .centered then 1 else
        (_root_.ABBKS26.Tree.idReserves x.k (Schedule.params mode x.wmin x.k) + 2) ^
          (1000000000 * (Rounding.solverConstant + 1) * (logInv x.wmin + 3) ^ 2)) ≤
      (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 3 := by
  cases mode with
  | centered => simpa only [ite_true, Nat.mul_one] using parameter_budget_le .centered x hx hk
  | identical =>
    have hw : x.wmin ≤ 1 / 2 := by
      have hkq : (2 : ℚ) ≤ x.k := by exact_mod_cast hk
      nlinarith only [hx.2.2.1, mul_le_mul_of_nonneg_right hkq hx.1.le]
    have hledger := Schedule.majorant .identical x.wmin x.k (max 2 ⌈1 / x.wmin⌉₊)
      ⟨hx.1, hw⟩ hx.2.2.1 hk (le_max_right _ _)
    have hr := Schedule.identical_reserve x.k ⟨hx.1, hw⟩ hk hx.2.2.1
    have hb :
        (_root_.ABBKS26.Tree.branchCap .identical x.k
          (Schedule.params .identical x.wmin x.k) + 1) ^ (x.k + 1) ≤
        (_root_.ABBKS26.Tree.treeCap .identical x.k
          (Schedule.params .identical x.wmin x.k)) ^ 2 := by
      rw [_root_.ABBKS26.Tree.treeCap, ← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hp := (Nat.mul_le_mul_right
      ((_root_.ABBKS26.Tree.idReserves x.k
        (Schedule.params .identical x.wmin x.k) + 2) ^
          (1000000000 * (Rounding.solverConstant + 1) * (logInv x.wmin + 3) ^ 2)) hb).trans hr
    simp only [reduceCtorEq, ↓reduceIte]
    calc
      _ ≤ (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) *
          (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul (Nat.add_le_add_right hledger 2)
          (hp.trans (hledger.trans (Nat.le_add_right _ 2)))
      _ = (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 2 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)

private theorem reserve_factors (p b n d r q : ℕ) (h : Prop) [Decidable h] :
    p * (b * n * (if h then 1 else d * r)) * q =
      p * b * (if h then 1 else r) * n * (if h then 1 else d) * q := by
  split_ifs <;> ring

private theorem sample_power (p q d a : ℕ) :
    p * (2 * q) ^ a * d * q ^ 100 = (2 ^ a * p) * q ^ (a + 100) * d := by
  rw [mul_pow, pow_add]
  ring


theorem need_envelope (mode : Mode) (x : Input) (hx : Exec.Valid x) :
    Exec.need mode x ≤ (2 ^ A * (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 3) *
      ((encInput x).length + 2) ^ (A + 100) *
        (if mode = .centered then 1 else
          (dim x.points + 2) ^ (A * (logInv x.wmin + 3) ^ 2)) := by
  let Q := (encInput x).length + 2
  let M := 2 ^ A * (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 3
  let D := if mode = .centered then 1 else
    (dim x.points + 2) ^ (A * (logInv x.wmin + 3) ^ 2)
  let R := if mode = .centered then 1 else
    (_root_.ABBKS26.Tree.idReserves x.k (Schedule.params mode x.wmin x.k) + 2) ^
      (A * (logInv x.wmin + 3) ^ 2)
  have hQ : 2 ≤ Q := by dsimp [Q]; omega
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; split_ifs <;> positivity
  change Exec.need mode x ≤ M * Q ^ (A + 100) * D
  by_cases hk : x.k ≤ 1
  · rw [Exec.need, ite_eq_left hk]
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ Q) (by omega : 100 ≤ A + 100)).trans
      ((Nat.le_mul_of_pos_left _ hM).trans (Nat.le_mul_of_pos_right _ hD))
  · have hw : (Schedule.params mode x.wmin x.k 0).w = x.wmin := by
      unfold Schedule.params
      generalize x.k - 1 - 0 = m
      cases m with
      | zero => rfl
      | succ m => rw [Function.iterate_succ_apply']; rfl
    have hp := reserved_parameter_budget_le mode x hx (by omega)
    simp only [← A_eq] at hp
    have hn := sample_size_le x
    calc
      _ = (Schedule.ledger mode x.wmin x.k + 2) *
          (_root_.ABBKS26.Tree.branchCap mode x.k
            (Schedule.params mode x.wmin x.k) + 1) ^ (x.k + 1) * R *
          (x.points.length + dim x.points + 2) ^ A * D * Q ^ 100 := by
        simp only [Exec.need, ite_eq_right hk, _root_.ABBKS26.Tree.localBudget, hw]
        simp only [← A_eq]
        change (Schedule.ledger mode x.wmin x.k + 2) *
          ((_root_.ABBKS26.Tree.branchCap mode x.k
            (Schedule.params mode x.wmin x.k) + 1) ^ (x.k + 1) *
              (x.points.length + dim x.points + 2) ^ A *
                (if mode = .centered then 1 else
                  (dim x.points + 2) ^ (A * (logInv x.wmin + 3) ^ 2) *
                    (_root_.ABBKS26.Tree.idReserves x.k
                      (Schedule.params mode x.wmin x.k) + 2) ^
                        (A * (logInv x.wmin + 3) ^ 2))) * Q ^ 100 = _
        exact reserve_factors _ _ _ _ _ _ (mode = .centered)
      _ ≤ (Schedule.H (max 2 ⌈1 / x.wmin⌉₊) + 2) ^ 3 *
          (2 * Q) ^ A * D * Q ^ 100 := by gcongr
      _ = M * Q ^ (A + 100) * D := by
        exact sample_power _ Q D A


theorem base_pos (clock : ℕ → ℕ) (a : ℕ) : 0 < base clock a := by
  unfold base
  positivity

theorem parameter_le_base (clock : ℕ → ℕ) (a : ℕ) :
    2 ^ A * (Schedule.H (max 2 a) + 2) ^ 3 ≤ base clock a := by
  have he : 1 ≤ exponent clock a := by unfold exponent; omega
  have hh : Schedule.H (max 2 a) + 2 ≤ 2 ^ exponent clock a := by
    have h := Nat.lt_two_pow_self (n := Schedule.H (max 2 a) + 1)
    exact (by omega : Schedule.H (max 2 a) + 2 ≤
      2 ^ (Schedule.H (max 2 a) + 1)).trans
        (Nat.pow_le_pow_right (by omega) (by unfold exponent; omega))
  calc
    _ ≤ 2 ^ A * (2 ^ exponent clock a) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 3)
    _ = 2 ^ (A + exponent clock a * 3) := by
      simpa only [pow_mul] using (pow_add (2 : ℕ) A (exponent clock a * 3)).symm
    _ ≤ 2 ^ (exponent clock a * (A + 10)) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    _ = base clock a := by rw [base, pow_mul]

theorem budget_sufficient (clock : ℕ → ℕ) (mode : Mode) (x : Input)
    (hx : Exec.Valid x) : Exec.need mode x ≤ budget clock mode x := by
  apply (need_envelope mode x hx).trans
  rw [budget, ite_eq_left hx]
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (parameter_le_base clock _)
      (Nat.pow_le_pow_right (by omega) (by unfold K; omega))
  · cases mode with
    | centered => simp only [dimensionFactor, ite_true, le_refl]
    | identical =>
      simp only [dimensionFactor, reduceCtorEq, ite_false]
      apply Nat.pow_le_pow_right (by omega)
      have hlog : (logInv x.wmin + 3) ^ 2 ≤ 16 * (logInv x.wmin ^ 2 + 1) := by
        nlinarith [sq_nonneg ((logInv x.wmin : ℤ) - 1)]
      calc A * (logInv x.wmin + 3) ^ 2 ≤ A * (16 * (logInv x.wmin ^ 2 + 1)) :=
          Nat.mul_le_mul_left _ hlog
        _ ≤ K * (logInv x.wmin ^ 2 + 1) := by unfold K; nlinarith

/-- The original frozen time expression, available without importing RunTime. -/
def frozenTime (mode : Mode) (g : ℕ → ℕ → ℕ) (C : ℕ) : Input → ℕ :=
  match mode with
  | .centered => centeredTime g C
  | .identical => identicalCovTime g C

theorem base_computable (clock : ℕ → ℕ) (hc : Computable clock) :
    Computable (base clock) := by
  have hpow : Computable₂ (fun a b : ℕ ↦ a ^ b) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp
  have hmax := Primrec.nat_max.to_comp
  have hadd := Primrec.nat_add.to_comp
  have hm := hmax.comp (Computable.const 2) Computable.id
  have hexp := hadd.comp
    (hadd.comp (hadd.comp (RunTimeAux.H_primrec.to_comp.comp hm) (hc.comp hm)) Computable.id)
    (Computable.const 1)
  exact hpow.comp (hpow.comp (Computable.const 2) hexp) (Computable.const (A + 10))

private theorem measure_mul (b q d j : ℕ) :
    q * (2 * (b * q ^ j * d)) = (2 * b) * q ^ (j + 1) * d := by
  rw [pow_succ]
  ring

open RunTimeAuxBudgetAuxCost

private theorem exponent_le_base (clock : ℕ → ℕ) (a : ℕ) :
    exponent clock a ≤ base clock a := by
  exact Nat.lt_two_pow_self.le.trans (Nat.le_self_pow (by unfold A; omega) _)

private theorem base_feasible (clock : ℕ → ℕ)
    (hcost : Feasible clock (fun a ↦ (Schedule.H a, clock a))
      encUnary (encPair encUnary encUnary)) :
    Feasible (base clock) (base clock) encUnary encUnary := by
  have ha (a : ℕ) : a ≤ base clock a :=
    (by unfold exponent; omega : a ≤ exponent clock a).trans (exponent_le_base clock a)
  have ht (a : ℕ) : clock (max 2 a) ≤ base clock a :=
    (by unfold exponent; omega : clock (max 2 a) ≤ exponent clock a).trans
      (exponent_le_base clock a)
  have hlen : PolyBounded (base clock) (fun a ↦ (encUnary a).length) :=
    PolyBounded.self.mono fun a ↦ by simpa only [encUnary_apply, List.length_replicate] using ha a
  have hm : Feasible (base clock) (fun a ↦ max 2 a) encUnary encUnary :=
    Feasible.of_polytime (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.unary_max.comp (g := fun a : ℕ ↦ (2, a))
        (by fun_prop))) hlen
  have hh := hcost.comp hm (PolyBounded.self.mono ht)
  have hid : Feasible (base clock) id encUnary encUnary :=
    Feasible.of_polytime ComputableInPolyTime.id' hlen
  have he := Feasible.post (encOut := encUnary)
    (f := fun p : (ℕ × ℕ) × ℕ ↦ p.1.1 + p.1.2 + p.2 + 1)
    (ComputableInPolyTime.of_tidy (by fun_prop)) (hh.prod hid)
  have htwo : Feasible (base clock) (fun _ : ℕ ↦ 2) encUnary encUnary :=
    Feasible.of_polytime (.const 2) hlen
  have hp : PolyBounded (base clock) (fun a ↦ 2 ^ exponent clock a) :=
    PolyBounded.self.mono fun a ↦ Nat.le_self_pow (by unfold A; omega) _
  exact (htwo.pow he hp).pow_const (A + 10)

private def rawBudget (clock : ℕ → ℕ) (mode : Mode) (x : Input) : ℕ :=
  base clock ⌈1 / x.wmin⌉₊ * ((encInput x).length + 2) ^ K * dimensionFactor mode K x

private theorem length_le_measure (f : Input → ℕ) (x : Input) :
    (encInput x).length ≤ RunTimeAuxPadding.measure f x := by
  unfold RunTimeAuxPadding.measure
  nlinarith

private theorem rawBudget_factors_le (clock : ℕ → ℕ) (mode : Mode) (x : Input) :
    base clock ⌈1 / x.wmin⌉₊ ≤ RunTimeAuxPadding.measure (rawBudget clock mode) x ∧
      dimensionFactor mode K x ≤ RunTimeAuxPadding.measure (rawBudget clock mode) x ∧
      ⌈1 / x.wmin⌉₊ ≤ RunTimeAuxPadding.measure (rawBudget clock mode) x := by
  have hq : 0 < (encInput x).length + 2 := by omega
  have hd : 0 < dimensionFactor mode K x := by
    unfold dimensionFactor
    split_ifs <;> positivity
  have hr : rawBudget clock mode x ≤ RunTimeAuxPadding.measure (rawBudget clock mode) x :=
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hq)
  have hb : base clock ⌈1 / x.wmin⌉₊ ≤ rawBudget clock mode x :=
    (Nat.le_mul_of_pos_right _ (pow_pos hq K)).trans (Nat.le_mul_of_pos_right _ hd)
  refine ⟨hb.trans hr,
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (base_pos clock _) (pow_pos hq K))).trans hr, ?_⟩
  exact ((by unfold exponent; omega : ⌈1 / x.wmin⌉₊ ≤
    exponent clock ⌈1 / x.wmin⌉₊).trans (exponent_le_base clock _)).trans (hb.trans hr)

private theorem rawBudget_parameter_feasible (clock : ℕ → ℕ) (mode : Mode) :
    Feasible (RunTimeAuxPadding.measure (rawBudget clock mode))
      (fun x : Input ↦ ⌈1 / x.wmin⌉₊) encInput encUnary :=
  (Feasible.of_polytime parameter_polytime
    (PolyBounded.self.mono (length_le_measure _))).unaryOfBinary
      (PolyBounded.self.mono fun x ↦ (rawBudget_factors_le clock mode x).2.2)

private theorem logInv_feasible (size : Input → ℕ)
    (hp : Feasible size (fun x : Input ↦ ⌈1 / x.wmin⌉₊) encInput encUnary) :
    Feasible size (fun x : Input ↦ logInv x.wmin) encInput encUnary := by
  simpa only [logInv, one_div] using
    Feasible.post (ComputableInPolyTime.unary_clog_const 2) hp

private theorem dimension_exponent_feasible (size : Input → ℕ) (C : ℕ)
    (hlen : PolyBounded size (fun x ↦ (encInput x).length))
    (hp : Feasible size (fun x : Input ↦ ⌈1 / x.wmin⌉₊) encInput encUnary) :
    Feasible size (fun x : Input ↦ C * (logInv x.wmin ^ 2 + 1)) encInput encUnary := by
  have hone : Feasible size (fun _ : Input ↦ 1) encInput encUnary :=
    Feasible.of_polytime (.const 1) hlen
  have hC : Feasible size (fun _ : Input ↦ C) encInput encUnary :=
    Feasible.of_polytime (.const C) hlen
  exact hC.mul (((logInv_feasible size hp).pow_const 2).add hone)

private theorem identical_factor_feasible (size : Input → ℕ) (C : ℕ)
    (hlen : PolyBounded size (fun x ↦ (encInput x).length))
    (hp : Feasible size (fun x : Input ↦ ⌈1 / x.wmin⌉₊) encInput encUnary)
    (hbound : PolyBounded size
      (fun x : Input ↦ (dim x.points + 2) ^ (C * (logInv x.wmin ^ 2 + 1)))) :
    Feasible size (fun x : Input ↦ (dim x.points + 2) ^ (C * (logInv x.wmin ^ 2 + 1)))
      encInput encUnary := by
  have hdim : Feasible size (fun x : Input ↦ dim x.points + 2) encInput encUnary :=
    Feasible.of_polytime (ComputableInPolyTime.unary_add' dim_polytime (.const 2)) hlen
  exact hdim.pow (dimension_exponent_feasible size C hlen hp) hbound

private theorem dimensionFactor_feasible (clock : ℕ → ℕ) (mode : Mode) :
    Feasible (RunTimeAuxPadding.measure (rawBudget clock mode))
      (dimensionFactor mode K) encInput encUnary := by
  cases mode with
  | centered =>
    exact Feasible.of_polytime (.const 1) (PolyBounded.self.mono (length_le_measure _))
  | identical =>
    exact identical_factor_feasible _ K (PolyBounded.self.mono (length_le_measure _))
      (rawBudget_parameter_feasible clock .identical)
      (PolyBounded.self.mono fun x ↦ (rawBudget_factors_le clock .identical x).2.1)

private theorem rawBudget_base_feasible (clock : ℕ → ℕ)
    (hcost : Feasible clock (fun a ↦ (Schedule.H a, clock a))
      encUnary (encPair encUnary encUnary)) (mode : Mode) :
    Feasible (RunTimeAuxPadding.measure (rawBudget clock mode))
      (fun x : Input ↦ base clock ⌈1 / x.wmin⌉₊) encInput encUnary :=
  (base_feasible clock hcost).comp (rawBudget_parameter_feasible clock mode)
    (PolyBounded.self.mono fun x ↦ (rawBudget_factors_le clock mode x).1)

private theorem rawBudget_feasible (clock : ℕ → ℕ)
    (hcost : Feasible clock (fun a ↦ (Schedule.H a, clock a))
      encUnary (encPair encUnary encUnary)) (mode : Mode) :
    Feasible (RunTimeAuxPadding.measure (rawBudget clock mode))
      (rawBudget clock mode) encInput encUnary := by
  have hQ : Feasible (RunTimeAuxPadding.measure (rawBudget clock mode))
      (fun x : Input ↦ ((encInput x).length + 2) ^ K) encInput encUnary :=
    Feasible.of_polytime
      ((ComputableInPolyTime.unary_pow K).comp
        (ComputableInPolyTime.unary_add' input_length_polytime (.const 2)))
      (PolyBounded.self.mono (length_le_measure _))
  exact ((rawBudget_base_feasible clock hcost mode).mul hQ).mul
    (dimensionFactor_feasible clock mode)

/-- Every fixed polynomial in the padded measure fits one larger frozen time bound. -/
theorem budget_power_absorption (clock : ℕ → ℕ) (hc : Computable clock)
    (mode : Mode) (E : ℕ) : ∃ (g : ℕ → ℕ → ℕ) (C : ℕ), Computable₂ g ∧
      ∀ x, measure (budget clock mode) x ^ E ≤ frozenTime mode g C x := by
  let g : ℕ → ℕ → ℕ := fun a _ ↦ (2 * base clock a) ^ E
  let C := (K + 1) * E
  have hpow : Computable₂ (fun a b : ℕ ↦ a ^ b) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp
  have hg : Computable₂ g := hpow.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2)
      ((base_computable clock hc).comp Computable.fst)) (Computable.const E)
  refine ⟨g, C, hg, fun x ↦ ?_⟩
  let B := base clock ⌈1 / x.wmin⌉₊
  let Q := (encInput x).length + 2
  let D := dimensionFactor mode K x
  have hB : 0 < B := base_pos clock _
  have hQ : 2 ≤ Q := by dsimp [Q]; omega
  have hD : 0 < D := by dsimp [D, dimensionFactor]; split_ifs <;> positivity
  have hbudget : budget clock mode x ≤ B * Q ^ K * D := by
    unfold budget
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have hpos : 0 < B * Q ^ K * D := by positivity
  have hm : measure (budget clock mode) x ≤ (2 * B) * Q ^ (K + 1) * D := by
    calc _ ≤ Q * (2 * (B * Q ^ K * D)) :=
          Nat.mul_le_mul_left Q (by omega)
      _ = _ := measure_mul B Q D K
  have hp := Nat.pow_le_pow_left hm E
  rw [mul_pow, mul_pow, ← pow_mul] at hp
  cases mode with
  | centered =>
    simpa only [D, dimensionFactor, ite_true, one_pow, mul_one, frozenTime, centeredTime,
      g, C, B, Q] using hp
  | identical =>
    have hd : D ^ E ≤ (dim x.points + 2) ^ (C * (logInv x.wmin ^ 2 + 1)) := by
      simp only [D, dimensionFactor, reduceCtorEq, ite_false, ← pow_mul]
      apply Nat.pow_le_pow_right (by omega)
      dsimp [C]
      nlinarith
    exact hp.trans (Nat.mul_le_mul_left _ hd)

/-- Simulate the fixed evaluator, count its steps, then write the clock-padded budget. -/
theorem exists_budget_constructor (mode : Mode) :
    ∃ clock : ℕ → ℕ, Computable clock ∧ ∃ E : ℕ,
      ComputableTidilyInO (budget clock mode) encInput encUnary
        (fun x ↦ measure (budget clock mode) x ^ E)
        (fun x ↦ measure (budget clock mode) x ^ E) := by
  obtain ⟨_, clock, hclock, _, hcost⟩ := primrec_hasCost RunTimeAux.H_primrec
  refine ⟨clock, hclock, ?_⟩
  have hlen : PolyBounded (RunTimeAuxPadding.measure (budget clock mode))
      (fun x ↦ (encInput x).length) := PolyBounded.self.mono fun x ↦ by
    unfold RunTimeAuxPadding.measure
    nlinarith
  have h := Feasible.guard valid_polytime (rawBudget_feasible clock hcost mode) hlen
    (fun x hx ↦ by
      change ((encInput x).length + 2) * (rawBudget clock mode x + 1) ≤
        ((encInput x).length + 2) * (budget clock mode x + 1)
      rw [budget, ite_eq_left hx]
      exact le_rfl)
  change Feasible (RunTimeAuxPadding.measure (budget clock mode))
    (budget clock mode) encInput encUnary at h
  exact h.power_certificate fun x ↦ by unfold RunTimeAuxPadding.measure; nlinarith

end

end ABBKS26.Assembly.RunTimeAuxBudget
