module

public import Background.SumOfSquares.Solver
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Paying for `n^O(ℓ)` time with a budget

The solver's running time `(|P| + 2)^(C (ℓ + 1)) (|η, γ| + 2)^C` is not polynomial in the length of
the input, since the degree `ℓ` is part of it. The algorithm is therefore written as a function
`core` of the input and a *budget* `L`, given in unary, which bounds its loops and the sizes of its
data. `core` runs in polynomial time in the length of `(x, L)`, and with the budget
`L = (|P| + 2)^(ℓ + 1)` (`SoS.Solver.budget`) nothing it computes is cut short.

`SoS.Solver.exists_computableInTimeAndSpace_of_budget`: if `core` is computable in polynomial time,
then `x ↦ core (x, budget x)` is computable within the time bound of `SoS.Solver.exists_solver`.
Writing the budget takes time polynomial in `budget x`, and `core` takes time polynomial in
`budget x` and the length of `x`; both are at most `(|P| + 2)^(C (ℓ + 1)) (|η, γ| + 2)^C`.

The encodings of `Background/Encoding.lean` are, by definition, those of complexitylib's machine
library, so its results apply to them directly.
-/

@[expose] public section

namespace SoS.Solver

open Turing.MultiTapeTM

/-- The budget `(|P| + 2)^(ℓ + 1)`, where `|P|` is the length of the encoded problem. -/
def budget (x : Input) : ℕ := ((encProblem x.1).length + 2) ^ (x.1.degree + 1)

/-- The measure that bounds the cost of padding: `(|P| + 2)^(ℓ + 2)`. -/
def padMeasure (P : Problem) : ℕ := ((encProblem P).length + 2) ^ (P.degree + 2)

theorem one_le_padMeasure (P : Problem) : 1 ≤ padMeasure P :=
  Nat.one_le_pow _ _ (by omega)

theorem length_le_padMeasure (P : Problem) : (encProblem P).length + 2 ≤ padMeasure P :=
  (Nat.le_self_pow (by omega) _).trans_eq rfl

theorem degree_succ_le_padMeasure (P : Problem) : P.degree + 1 ≤ padMeasure P := by
  calc P.degree + 1 ≤ 2 ^ (P.degree + 1) := (Nat.lt_two_pow_self).le
    _ ≤ ((encProblem P).length + 2) ^ (P.degree + 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ padMeasure P := Nat.pow_le_pow_right (by omega) (by omega)

theorem budget_le_padMeasure (x : Input) : budget x ≤ padMeasure x.1 :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- The certificate for `(N + 2)^(ℓ + 1)` with `N` in binary and `ℓ` in unary. -/
theorem budgetPow_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 + 2) ^ (p.2 + 1))
      (encPair encNat encUnary) encNat :=
  ComputableTidilyInPolyTime.binary_pow'
    (ComputableTidilyInPolyTime.binary_add' (ComputableTidilyInPolyTime.fst encNat encUnary)
      (ComputableTidilyInPolyTime.const 2))
    (ComputableTidilyInDegree.unary_succ.computableTidilyInPolyTime.comp
      (ComputableTidilyInPolyTime.snd encNat encUnary))

/-- **Writing the budget**: `P ↦ (|P| + 2)^(ℓ + 1)` in unary, within time and space polynomial in
`(|P| + 2)^(ℓ + 2)`. -/
theorem exists_budget_inO : ∃ K D : ℕ, ComputableTidilyInO
    (fun P : Problem => ((encProblem P).length + 2) ^ (P.degree + 1)) encProblem encUnary
    (fun P => K * padMeasure P ^ D) (fun P => K * padMeasure P ^ D) := by
  -- The length of the encoded problem, in binary.
  have hlen : ComputableTidilyInO (fun P : Problem => (encProblem P).length) encProblem encNat
      (fun P => ((encProblem P).length + 1) ^ 2) (fun P => (encProblem P).length + 1) :=
    (ComputableInO.tidy ComputableInO.lengthNat).of_encIn_eq (fun P : Problem => encProblem P)
      fun _ => rfl
  -- The degree, in unary.
  have hdeg : ComputableTidilyInO (fun P : Problem => P.degree) encProblem encNat
      (fun P => (encProblem P).length) (fun P => (encProblem P).length) :=
    (ComputableTidilyInO.snd encNat _).fst'
  have hdegU := (ComputableInO.tidy ComputableInO.natToUnary).comp hdeg
  have hpair := hlen.prod hdegU
  obtain ⟨d, e, hpow⟩ := budgetPow_polytime.exists_degree
  have hL := hpow.inO.comp hpair
  have hLU := (ComputableInO.tidy ComputableInO.natToUnary).comp hL
  -- Every bound is at most a constant times a power of the measure.
  refine ⟨8 * 4 ^ d + 12, d + 2, ?_⟩
  refine hLU.mono_le (fun P => ?_) (fun P => ?_)
  all_goals
    simp only [Function.comp_apply]
    set m := padMeasure P
    have hm : 1 ≤ m := one_le_padMeasure P
    have hlenP : (encProblem P).length + 2 ≤ m := length_le_padMeasure P
    have hdegP : P.degree + 1 ≤ m := degree_succ_le_padMeasure P
    have hbud : ((encProblem P).length + 2) ^ (P.degree + 1) ≤ m :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpenc : (encPair encNat encUnary ((encProblem P).length, P.degree)).length + 1 ≤
        4 * m := by
      rw [length_encPair]
      simp only [encNat_apply, encUnary_apply, List.length_replicate]
      have := Nat.size_le_self ((encProblem P).length)
      rw [Nat.size_eq_bits_len]
      omega
    have hmd : m ^ 2 ≤ m ^ (d + 2) := Nat.pow_le_pow_right hm (by omega)
    have hmd' : m ^ d ≤ m ^ (d + 2) := Nat.pow_le_pow_right hm (by omega)
    have hm1 : m ≤ m ^ 2 := Nat.le_self_pow (by omega) _
    have h1 : ((encProblem P).length + 1) ^ 2 ≤ m ^ (d + 2) :=
      (Nat.pow_le_pow_left (by omega) 2).trans hmd
    have h2 : (P.degree + 1) ^ 2 ≤ m ^ (d + 2) := (Nat.pow_le_pow_left hdegP 2).trans hmd
    have h3 : (encProblem P).length + 1 ≤ m ^ (d + 2) := by omega
    have h4 : ((encPair encNat encUnary ((encProblem P).length, P.degree)).length + 1) ^ d ≤
        4 ^ d * m ^ (d + 2) := by
      calc _ ≤ (4 * m) ^ d := Nat.pow_le_pow_left hpenc d
        _ = 4 ^ d * m ^ d := mul_pow _ _ _
        _ ≤ 4 ^ d * m ^ (d + 2) := Nat.mul_le_mul_left _ hmd'
    have h5 : (((encProblem P).length + 2) ^ (P.degree + 1) + 1) ^ 2 ≤ 4 * m ^ (d + 2) := by
      calc _ ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * m ^ 2 := by ring
        _ ≤ 4 * m ^ (d + 2) := Nat.mul_le_mul_left _ hmd
    have h6 : ((encProblem P).length + 2) ^ (P.degree + 1) ≤ m ^ (d + 2) := by omega
    have h7 : P.degree ≤ m ^ (d + 2) := by omega
    have h8 := Nat.zero_le (4 ^ d * m ^ (d + 2))
    linarith

/-- `size (x, budget x) ≤ 3 (budget x) (|x| + 2)`, the measure of the padded input. -/
theorem length_encPair_budget_le (x : Input) :
    (encPair encInput encUnary (x, budget x)).length + 1 ≤
      3 * (budget x * ((encInput x).length + 2)) := by
  rw [length_encPair]
  simp only [encUnary_apply, List.length_replicate]
  have hb : 1 ≤ budget x := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The measure of the padded input is at most the time bound, up to constants. -/
theorem exists_le_timeBound (K D : ℕ) : ∃ C, ∀ x : Input,
    K * (budget x * ((encInput x).length + 2)) ^ D ≤ timeBound C x := by
  refine ⟨K + 2 * D, fun x => ?_⟩
  set a := (encProblem x.1).length
  set b := (encPair Encoding.encRat Encoding.encRat x.2).length
  set l := x.1.degree
  have ha : 2 ≤ a + 2 := by omega
  have hlen : (encInput x).length = 2 * a + 1 + b :=
    length_encPair (enc₁ := encProblem)
      (enc₂ := Turing.MultiTapeTM.encPair Encoding.encRat Encoding.encRat) x
  have hM : budget x * ((encInput x).length + 2) ≤ (a + 2) ^ (l + 2) * (b + 2) := by
    rw [hlen, budget, pow_succ _ (l + 1), mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have hK : K ≤ (a + 2) ^ K :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left ha K)
  calc K * (budget x * ((encInput x).length + 2)) ^ D
      ≤ (a + 2) ^ K * ((a + 2) ^ (l + 2) * (b + 2)) ^ D :=
        Nat.mul_le_mul hK (Nat.pow_le_pow_left hM D)
    _ = (a + 2) ^ (K + (l + 2) * D) * (b + 2) ^ D := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    _ ≤ (a + 2) ^ ((K + 2 * D) * (l + 1)) * (b + 2) ^ (K + 2 * D) := by
        refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ?_)
          (Nat.pow_le_pow_right (by omega) (by omega))
        nlinarith
    _ = timeBound (K + 2 * D) x := rfl

/-- **Paying for `n^O(ℓ)` time with a budget.** If `core` is computable in polynomial time in the
length of the input and a unary budget, then running it with the budget `(|P| + 2)^(ℓ + 1)` is
computable within the time bound of `SoS.Solver.exists_solver`. -/
theorem exists_computableInTimeAndSpace_of_budget {core : Input × ℕ → Output}
    (hcore : ComputableInPolyTime core (encPair encInput encUnary) encOutput) :
    ∃ C, ComputableInTimeAndSpace (fun x => core (x, budget x)) encInput encOutput
      (timeBound C) (fun x => timeBound C x + (encInput x).length) := by
  obtain ⟨K, D, hbud⟩ := exists_budget_inO
  -- Pad: the input, and the budget written in unary.
  have hP : ComputableTidilyInO (fun x : Input => x.1) encInput encProblem
      (fun x => (encInput x).length) (fun x => (encInput x).length) :=
    ComputableTidilyInO.fst encProblem (encPair Encoding.encRat Encoding.encRat)
  have hLx := hbud.comp hP
  have hid : ComputableTidilyInO (fun x : Input => x) encInput encInput
      (fun x => (encInput x).length) (fun x => (encInput x).length) :=
    ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)
  have hpad := hid.prod hLx
  -- Run the core.
  obtain ⟨dc, ec, hc⟩ := hcore.tidy.exists_degree
  have h := hc.inO.comp hpad
  -- Every bound is at most a constant times a power of the measure of the padded input.
  set M : Input → ℕ := fun x => budget x * ((encInput x).length + 2)
  have hMbound : ∀ x : Input, (encInput x).length + 1 ≤ M x ∧ padMeasure x.1 ≤ M x ∧ 1 ≤ M x := by
    intro x
    have hb : 1 ≤ budget x := Nat.one_le_pow _ _ (by omega)
    have hlen : (encProblem x.1).length + 2 ≤ (encInput x).length + 2 := by
      have : (encInput x).length = 2 * (encProblem x.1).length + 1 +
          (encPair Encoding.encRat Encoding.encRat x.2).length :=
        length_encPair (enc₁ := encProblem)
          (enc₂ := Turing.MultiTapeTM.encPair Encoding.encRat Encoding.encRat) x
      omega
    refine ⟨by simp only [M]; nlinarith, ?_, by simp only [M]; nlinarith⟩
    calc padMeasure x.1 = budget x * ((encProblem x.1).length + 2) := by
          rw [padMeasure, budget, pow_succ]
      _ ≤ M x := Nat.mul_le_mul_left _ hlen
  have hbound : ∀ x : Input,
      ((encInput x).length + K * padMeasure x.1 ^ D +
        ((encPair encInput encUnary (x, budget x)).length + 1) ^ dc) ≤
        (2 + K + 3 ^ dc) * M x ^ (D + dc + 1) := by
    intro x
    obtain ⟨h1, h2, h3⟩ := hMbound x
    have hp1 : M x ≤ M x ^ (D + dc + 1) := Nat.le_self_pow (by omega) _
    have hp2 : padMeasure x.1 ^ D ≤ M x ^ (D + dc + 1) :=
      (Nat.pow_le_pow_left h2 D).trans (Nat.pow_le_pow_right h3 (by omega))
    have hp3 : ((encPair encInput encUnary (x, budget x)).length + 1) ^ dc ≤
        3 ^ dc * M x ^ (D + dc + 1) := by
      calc ((encPair encInput encUnary (x, budget x)).length + 1) ^ dc ≤ (3 * M x) ^ dc :=
            Nat.pow_le_pow_left (length_encPair_budget_le x) dc
        _ = 3 ^ dc * M x ^ dc := mul_pow _ _ _
        _ ≤ 3 ^ dc * M x ^ (D + dc + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h3 (by omega))
    nlinarith
  obtain ⟨c, hcomp, -⟩ := h.computableInO
  obtain ⟨C, hC⟩ := exists_le_timeBound (c * (3 + K + 3 ^ dc)) (D + dc + 1)
  have hfinal : ∀ x : Input, c * ((encInput x).length +
      ((encInput x).length + K * padMeasure x.1 ^ D) +
      ((encPair encInput encUnary (x, budget x)).length + 1) ^ dc + 1) ≤ timeBound C x := by
    intro x
    have hb := hbound x
    obtain ⟨h1, -, h3⟩ := hMbound x
    have hMp : M x ≤ M x ^ (D + dc + 1) := Nat.le_self_pow (by omega) _
    calc _ ≤ c * ((3 + K + 3 ^ dc) * M x ^ (D + dc + 1)) := Nat.mul_le_mul_left c (by linarith)
      _ = c * (3 + K + 3 ^ dc) * M x ^ (D + dc + 1) := by ring
      _ ≤ timeBound C x := hC x
  exact ⟨C, hcomp.mono (fun x => hfinal x) fun x => (hfinal x).trans (Nat.le_add_right _ _)⟩

end SoS.Solver
