module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace

/-!
# Iterating a state map a unary number of times

From a state `s` and a unary count `n`, a tidy machine computes `finish (step^[n] s)` within time
and space `O((n + 1) · (U + 1))`, where `U` bounds, for every state `step^[i] s` with `i ≤ n`, the
time and space of `step` and `finish` on it and its encoded length. Each round is charged only its
own cost: this is complexitylib's streaming loop
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`), which reads the
count from the input one bit per round, with nothing emitted during the rounds.
-/

@[expose] public section

namespace BB20.Machine.Loop

open Turing.MultiTapeTM

/-- **Iterating a state map `n` times, then finishing.** The bound `U` may be any function of the
input `(s, n)`, as long as it dominates the costs of `step` and `finish` and the encoded length on
the states `step^[i] s` with `i ≤ n`. -/
theorem iterate_finish {σ β : Type} {encS : σ ↪ List Bool} {encOut : β ↪ List Bool}
    {step : σ → σ} {finish : σ → β} {tN sN tF sF : σ → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace step encS encS tN sN)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encOut tF sF) (U : σ × ℕ → ℕ)
    (hU : ∀ x : σ × ℕ, ∀ i ≤ x.2, tN (step^[i] x.1) + sN (step^[i] x.1) + tF (step^[i] x.1) +
      sF (step^[i] x.1) + (encS (step^[i] x.1)).length ≤ U x) :
    ComputableTidilyInO (fun x : σ × ℕ => finish (step^[x.2] x.1)) (encPair encS encUnary)
      encOut (fun x => (x.2 + 1) * (U x + 1)) (fun x => (x.2 + 1) * (U x + 1)) := by
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const (α := σ) (encIn := encS)
    (encOut := encBits) ([] : List Bool)
  have hfin' : ComputableTidilyInTimeAndSpace (fun s => encOut (finish s)) encS encBits tF sF :=
    hfinish.of_enc_eq fun _ => rfl
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum hstep
    he.computableTidilyInTimeAndSpace hfin'
    (R := fun x _ => 3 * U x + 2 * ce + 3) (Q := U) (B := U)
    (fun x i hi => by
      have h₀ := hU x i hi.le
      have h₁ := hU x (i + 1) hi
      omega)
    (fun x i hi => by
      have h₀ := hU x i hi.le
      omega)
    (fun x i hi => by
      have h₀ := hU x i hi
      omega)
  have hout (x : σ × ℕ) : encOut (finish (step^[x.2] x.1)) =
      encBits ((((List.range x.2).map fun i => Function.const σ ([] : List Bool)
        (step^[i] x.1)).flatten ++ encOut (finish (step^[x.2] x.1)))) := by
    simp [encBits]
  refine ComputableTidilyInO.of_bounds ((h.of_enc_eq hout)) (c * (2 * ce + 6) + 1)
    (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · have hn := hU x x.2 le_rfl
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h₁ : tF (step^[x.2] x.1) + x.2 * (3 * U x + 2 * ce + 3) + U x + 1 ≤
        (2 * ce + 6) * ((x.2 + 1) * (U x + 1)) := by
      nlinarith [Nat.zero_le (ce * x.2 * U x), Nat.zero_le (ce * U x), Nat.zero_le (x.2 * U x),
        Nat.zero_le (ce * x.2)]
    calc c * (tF (step^[x.2] x.1) + x.2 * (3 * U x + 2 * ce + 3) + U x + 1)
        ≤ c * ((2 * ce + 6) * ((x.2 + 1) * (U x + 1))) := Nat.mul_le_mul_left c h₁
      _ ≤ (c * (2 * ce + 6) + 1) * ((x.2 + 1) * (U x + 1) + 1) := by nlinarith
  · have hn := hU x x.2 le_rfl
    have h₁ : sF (step^[x.2] x.1) + U x + U x + 1 ≤ (2 * ce + 6) * ((x.2 + 1) * (U x + 1)) := by
      nlinarith [Nat.zero_le (ce * x.2 * U x), Nat.zero_le (ce * U x), Nat.zero_le (x.2 * U x),
        Nat.zero_le (ce * x.2)]
    calc c * (sF (step^[x.2] x.1) + U x + U x + 1)
        ≤ c * ((2 * ce + 6) * ((x.2 + 1) * (U x + 1))) := Nat.mul_le_mul_left c h₁
      _ ≤ (c * (2 * ce + 6) + 1) * ((x.2 + 1) * (U x + 1) + 1) := by nlinarith
  · have hn := hU x x.2 le_rfl
    have hl := hfinish.length_le (step^[x.2] x.1)
    have h₁ : U x ≤ (x.2 + 1) * (U x + 1) + 1 := by nlinarith
    exact (hl.trans (by omega)).trans
      (h₁.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))

end BB20.Machine.Loop
