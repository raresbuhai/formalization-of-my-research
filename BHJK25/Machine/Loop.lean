module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Background.Encoding
public import BHJK25.Machine.LoopCount

/-!
# Loops whose running time is linear in the number of rounds

A state machine with a polynomial-time step, started from a polynomial-time initial state and
stopped after `a · b^k` rounds, with a polynomial-time map from the final state to the output,
runs on a multitape Turing machine in time `O((a b^k + 1) · poly(|x|))`, as long as `a`, `b`,
`k` and all intermediate states are polynomially bounded. Unlike a composition of
polynomial-time certificates, the bound is linear in the number of rounds, which may be
exponential in the input.

The rounds are driven by a unary count produced in linear time (repeated multiplication of a
unary number by `b`), and iterated with complexitylib's streaming loop
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`), which charges each
round only its own cost. The loop is `BHJK25.Machine.Loop.iterate_finish`, the unary count is
`BHJK25.Machine.Loop.count_inO` (built on `BHJK25.Machine.Loop.unaryPow`), and the bounds of the
pieces are collected into a polynomial factor times the number of rounds. Copied from BB20's
`BB20/Machine`, since papers do not import each other.
-/

@[expose] public section

namespace BHJK25.Machine.Loop

open Turing.MultiTapeTM

/-- **A loop of `a · b^k` rounds runs in time linear in the number of rounds.** -/
theorem iterate_inTime {α σ β : Type} {encIn : α ↪ List Bool} {encS : σ ↪ List Bool}
    {encOut : β ↪ List Bool} (init : α → σ) (step : σ → σ) (finish : σ → β) (a b k : α → ℕ)
    (hinit : ComputableInPolyTime init encIn encS)
    (hstep : ComputableInPolyTime step encS encS)
    (hfinish : ComputableInPolyTime finish encS encOut)
    (ha : ComputableInPolyTime a encIn Encoding.encNat)
    (hb : ComputableInPolyTime b encIn Encoding.encNat)
    (hk : ComputableInPolyTime k encIn Encoding.encNat)
    (B : α → ℕ) (hB : PolyBounded (fun x ↦ (encIn x).length) B)
    (habk : ∀ x, a x + b x + k x ≤ B x)
    (hstates : ∀ x, ∀ i ≤ a x * b x ^ k x, (encS (step^[i] (init x))).length ≤ B x) :
    ∃ c : ℕ, ComputableInTimeAndSpace (fun x ↦ finish (step^[a x * b x ^ k x] (init x)))
      encIn encOut
      (fun x ↦ c * ((a x * b x ^ k x + 1) * ((encIn x).length + 2) ^ c))
      (fun x ↦ c * ((a x * b x ^ k x + 1) * ((encIn x).length + 2) ^ c)) := by
  -- the unary round count, and the pair of the initial state with it
  obtain ⟨Tc, hTc, hc⟩ := count_inO ha hb hk hB habk
  obtain ⟨Ti, Si, hTi, hSi, hi⟩ := hinit.exists_computableInO
  have hpair := hi.tidy.prod hc
  -- the loop, charged on every state by `g`
  obtain ⟨Ts, Ss, hTs, hSs, hs⟩ := hstep.exists_computableInO
  obtain ⟨Tf, Sf, hTf, hSf, hf⟩ := hfinish.exists_computableInO
  obtain ⟨cs, hs', -⟩ := hs.tidy
  obtain ⟨cf, hf', -⟩ := hf.tidy
  let g : σ → ℕ := fun s ↦ cs * (Ts s + 1) + cs * (Ss s + 1) + cf * (Tf s + 1) +
    cf * (Sf s + 1) + (encS s).length
  have hg : PolyBounded (fun s ↦ (encS s).length) g :=
    (((((PolyBounded.const cs).mul (hTs.add (.const 1))).add
      ((PolyBounded.const cs).mul (hSs.add (.const 1)))).add
      ((PolyBounded.const cf).mul (hTf.add (.const 1)))).add
      ((PolyBounded.const cf).mul (hSf.add (.const 1)))).add .self
  obtain ⟨cg, dg, hg'⟩ := hg.exists_le
  have hloop := iterate_finish hs' hf'
    (fun y ↦ (Finset.range (y.2 + 1)).sup fun i ↦ g (step^[i] y.1))
    (fun y i hi ↦ Finset.le_sup (f := fun i ↦ g (step^[i] y.1))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hU (x : α) : (Finset.range (a x * b x ^ k x + 1)).sup
      (fun i ↦ g (step^[i] (init x))) ≤ cg * (B x + 1) ^ dg :=
    Finset.sup_le fun i hi ↦ (hg' _).trans (Nat.mul_le_mul_left cg (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hstates x i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) 1) dg))
  -- a polynomial bound on everything but the number of rounds
  let P : α → ℕ := fun x ↦ Ti x + Si x + Tc x + (k x + 1) * (a x + 1) * (b x + 1) +
    cg * (B x + 1) ^ dg + 1
  have hP : PolyBounded (fun x ↦ (encIn x).length) P := by
    have hB1 : PolyBounded (fun x ↦ (encIn x).length) fun x ↦ B x + 1 := hB.add (.const 1)
    have hkab : PolyBounded (fun x ↦ (encIn x).length)
        fun x ↦ (k x + 1) * (a x + 1) * (b x + 1) :=
      ((hB1.mul hB1).mul hB1).mono fun x ↦ by
        have := habk x
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    exact ((((hTi.add hSi).add hTc).add hkab).add ((PolyBounded.const cg).mul (hB1.pow dg))).add
      (.const 1)
  obtain ⟨cP, dP, hP'⟩ := hP.exists_le
  have hall := (hloop.comp hpair).mono_le
    (T' := fun x ↦ 5 * ((a x * b x ^ k x + 1) * P x))
    (S' := fun x ↦ 5 * ((a x * b x ^ k x + 1) * P x)) ?_ ?_
  · obtain ⟨c, hc', -⟩ := hall
    refine ⟨5 * c * cP + c + dP, hc'.computableInTimeAndSpace.mono (fun x ↦ ?_) (fun x ↦ ?_)⟩ <;>
    · beta_reduce
      have h₁ : ((encIn x).length + 1) ^ dP ≤ ((encIn x).length + 2) ^ (5 * c * cP + c + dP) :=
        (Nat.pow_le_pow_left (by omega) dP).trans
          (Nat.pow_le_pow_right (by omega) (by omega))
      have h₂ := (hP' x).trans (Nat.mul_le_mul_left cP h₁)
      have hE : 1 ≤ ((encIn x).length + 2) ^ (5 * c * cP + c + dP) := Nat.one_le_pow _ _ (by omega)
      have hM : 1 ≤ a x * b x ^ k x + 1 := by omega
      generalize a x * b x ^ k x + 1 = M at *
      generalize ((encIn x).length + 2) ^ (5 * c * cP + c + dP) = E at *
      have h₃ : M * P x ≤ cP * (M * E) := by
        calc M * P x ≤ M * (cP * E) := Nat.mul_le_mul_left M h₂
          _ = cP * (M * E) := by ring
      have h₄ := Nat.mul_le_mul_left (5 * c) h₃
      have h₅ := Nat.mul_le_mul_left c (Nat.mul_pos hM hE)
      nlinarith [Nat.zero_le (dP * (M * E))]
  all_goals
    intro x
    dsimp only
    have hUx := hU x
    have hPx : Ti x + Si x + Tc x + (k x + 1) * (a x + 1) * (b x + 1) + cg * (B x + 1) ^ dg + 1 =
      P x := rfl
    generalize (Finset.range (a x * b x ^ k x + 1)).sup (fun i ↦ g (step^[i] (init x))) = U
      at hUx ⊢
    generalize a x * b x ^ k x = N at *
    have h₃ : (k x + 1) * ((N + a x + 1) * (b x + 1)) ≤
        (N + 1) * ((k x + 1) * (a x + 1) * (b x + 1)) := by
      have : N + a x + 1 ≤ (N + 1) * (a x + 1) := by nlinarith
      calc _ ≤ (k x + 1) * (((N + 1) * (a x + 1)) * (b x + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
        _ = _ := by ring
    have h₄ := Nat.mul_le_mul_left (N + 1) (show U + 1 ≤ P x by omega)
    have h₅ := Nat.mul_le_mul_left (N + 1)
      (show (k x + 1) * (a x + 1) * (b x + 1) ≤ P x by omega)
    have h₆ : P x ≤ (N + 1) * P x := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega

end BHJK25.Machine.Loop
