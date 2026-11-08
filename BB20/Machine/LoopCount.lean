module

public import BB20.Machine.LoopUnary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# The unary round count of a loop

A loop of `a · b^k` rounds is driven by the count `a · b^k` written in unary. When `a`, `b` and `k`
are polynomial-time computable in binary and polynomially bounded, the count is computed within
time and space `O(poly(|x|) + (k + 1)(a b^k + a + 1)(b + 1))`: `a`, `b` and `k` are converted to
unary (`Turing.MultiTapeTM.ComputableInO.natToUnary`, quadratic in their values) and then
`BB20.Machine.Loop.unaryPow` writes the power.
-/

@[expose] public section

namespace BB20.Machine.Loop

open Turing.MultiTapeTM

/-- A polynomially bounded function computable in polynomial time in binary is computable in unary
within polynomial bounds. -/
theorem unary_of_polyTime {α : Type} {encIn : α ↪ List Bool} {f B : α → ℕ}
    (hf : ComputableInPolyTime f encIn encNat) (hB : PolyBounded (fun x => (encIn x).length) B)
    (hfB : ∀ x, f x ≤ B x) :
    ∃ T, PolyBounded (fun x => (encIn x).length) T ∧ ComputableTidilyInO f encIn encUnary T T := by
  obtain ⟨T, S, hT, hS, h⟩ := hf.exists_computableInO
  have h₂ := ComputableInO.natToUnary.tidy.comp h.tidy
  refine ⟨fun x => T x + S x + (f x + 1) ^ 2, ?_, ?_⟩
  · exact (hT.add hS).add (((hB.add (.const 1)).pow 2).mono fun x =>
      Nat.pow_le_pow_left (Nat.add_le_add_right (hfB x) 1) 2)
  · exact h₂.mono_le (fun x => by omega) (fun x => by nlinarith)

/-- **The unary count `a · b^k`** within time and space `O(T + (k + 1)(a b^k + a + 1)(b + 1))` for
a polynomially bounded `T`. -/
theorem count_inO {α : Type} {encIn : α ↪ List Bool} {a b k B : α → ℕ}
    (ha : ComputableInPolyTime a encIn encNat) (hb : ComputableInPolyTime b encIn encNat)
    (hk : ComputableInPolyTime k encIn encNat) (hB : PolyBounded (fun x => (encIn x).length) B)
    (habk : ∀ x, a x + b x + k x ≤ B x) :
    ∃ T, PolyBounded (fun x => (encIn x).length) T ∧
      ComputableTidilyInO (fun x => a x * b x ^ k x) encIn encUnary
        (fun x => T x + (k x + 1) * ((a x * b x ^ k x + a x + 1) * (b x + 1)))
        (fun x => T x + (k x + 1) * ((a x * b x ^ k x + a x + 1) * (b x + 1))) := by
  obtain ⟨Ta, hTa, ha'⟩ := unary_of_polyTime ha hB fun x => by have := habk x; omega
  obtain ⟨Tb, hTb, hb'⟩ := unary_of_polyTime hb hB fun x => by have := habk x; omega
  obtain ⟨Tk, hTk, hk'⟩ := unary_of_polyTime hk hB fun x => by have := habk x; omega
  exact ⟨fun x => Tb x + Ta x + Tk x, (hTb.add hTa).add hTk,
    unaryPow.comp ((hb'.prod ha').prod hk')⟩

end BB20.Machine.Loop
