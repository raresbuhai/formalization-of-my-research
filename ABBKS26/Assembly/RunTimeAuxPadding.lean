module

public import ABBKS26.Assembly.ExecData
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-! # Unary padding and ignoring coins with linear overhead -/

@[expose] public section

namespace ABBKS26.Assembly.RunTimeAuxPadding

open Turing.MultiTapeTM

/-- The common measure pays for the original input and for writing the unary budget. -/
def measure (budget : Input → ℕ) (x : Input) : ℕ :=
  ((encInput x).length + 2) * (budget x + 1)

/-- A deterministic padded list program has only linear dependence on the coin-string length. -/
theorem padded_runtime (raw : Input × ℕ → Output) (budget : Input → ℕ)
    (hraw : ComputableInPolyTime raw Exec.encPadded encOutput) (E : ℕ)
    (hbudget : ComputableTidilyInO budget encInput encUnary
      (fun x ↦ measure budget x ^ E) (fun x ↦ measure budget x ^ E)) :
    ∃ D, RunsInTime encInput encOutput (fun xr ↦ raw (xr.1, budget xr.1))
      (fun x ↦ measure budget x ^ D) := by
  obtain ⟨d, e, hdeg⟩ := hraw.tidy.exists_degree
  have hid : ComputableTidilyInO (id : Input → Input) encInput encInput
      (fun x ↦ (encInput x).length) (fun x ↦ (encInput x).length) :=
    .of_linear (.of_eq fun _ ↦ rfl)
  have hp := hid.prod hbudget
  have hr := hdeg.inO.comp hp
  have hx := ComputableTidilyInO.fst encInput encBits
  have hall := hr.comp hx
  obtain ⟨c, hc, _⟩ := hall.computableInO
  refine ⟨E + d + 1, c * (2 + 3 ^ d), hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals
    let W := measure budget xr.1
    have hW : 1 ≤ W := by dsimp [W, measure]; nlinarith
    have hlen : (encInput xr.1).length ≤ W := by dsimp [W, measure]; nlinarith
    have hpad : (Exec.encPadded (xr.1, budget xr.1)).length + 1 ≤ 3 * W := by
      change (Turing.MultiTapeTM.encPair encInput encUnary (xr.1, budget xr.1)).length + 1 ≤ _
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      dsimp [W, measure]
      nlinarith
    have hE : W ^ E ≤ W ^ (E + d + 1) := Nat.pow_le_pow_right hW (by omega)
    have hd : ((Exec.encPadded (xr.1, budget xr.1)).length + 1) ^ d ≤
        3 ^ d * W ^ (E + d + 1) := by
      calc _ ≤ (3 * W) ^ d := Nat.pow_le_pow_left hpad d
        _ = 3 ^ d * W ^ d := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (by omega))
    have hWp : W ≤ W ^ (E + d + 1) := Nat.le_self_pow (by omega) W
    simp only [id]
    change c * ((encPair encInput encBits xr).length +
      ((encInput xr.1).length + W ^ E +
        ((Exec.encPadded (xr.1, budget xr.1)).length + 1) ^ d) + 1) ≤
      c * (2 + 3 ^ d) * (W ^ (E + d + 1) + (encPair encInput encBits xr).length + 1)
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith [Nat.zero_le (3 ^ d * (encPair encInput encBits xr).length),
      Nat.zero_le (3 ^ d)]

/-- Increasing an input-only time bound preserves the linear allowance for arbitrary coins. -/
theorem runtime_of_le {A : Input × List Bool → Output} {T U : Input → ℕ}
    (h : RunsInTime encInput encOutput A T) (hle : ∀ x, T x ≤ U x) :
    RunsInTime encInput encOutput A U := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals
    exact Nat.mul_le_mul_left c
      (Nat.add_le_add_right (Nat.add_le_add_right (hle xr.1) _) 1)

end ABBKS26.Assembly.RunTimeAuxPadding
