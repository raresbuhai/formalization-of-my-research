module

public import BHJK25.Machine.LoopStream

/-!
# Unary powers in time linear in their value

From unary `b`, `a` and `k`, a tidy machine writes `a · b^k` in unary within time and space
`O((k + 1) · (a b^k + a + 1) · (b + 1))`. A unary product `m · b` is streamed as `m` copies of
`b` (`BHJK25.Machine.Loop.unaryMul`), and the map `(b, m) ↦ (b, m · b)` is iterated `k` times from
`(b, a)` with `BHJK25.Machine.Loop.iterate_finish`. Each round costs `O((a b^i + 1)(b + 1))`,
which is at most `O((a b^k + a + 1)(b + 1))`.
-/

@[expose] public section

namespace BHJK25.Machine.Loop

open Turing.MultiTapeTM

/-- **Unary multiplication**, by emitting `m` copies of `b`, from `(b, m)`. -/
theorem unaryMul : ComputableTidilyInO (fun p : ℕ × ℕ => p.2 * p.1)
    (encPair encUnary encUnary) encUnary
    (fun p => (p.2 + 1) * (p.1 + 1)) (fun p => (p.2 + 1) * (p.1 + 1)) := by
  obtain ⟨cc, hc⟩ := computableInTimeAndSpace_of_const (α := ℕ) (encIn := encUnary)
    (encOut := encBits) ([] : List Bool)
  have hid := computableTidilyInTimeAndSpace_id (enc := encUnary)
  have hemit : ComputableTidilyInTimeAndSpace (fun n : ℕ => List.replicate n true) encUnary
      encBits (fun n => 2 * (encUnary n).length + 4) (fun _ => 0) :=
    hid.of_enc_eq fun _ => rfl
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum hid hemit
    hc.computableTidilyInTimeAndSpace
    (R := fun x _ => 6 * x.1 + 9) (Q := fun _ => 0) (B := fun x => x.1)
    (fun x i _ => by simp [encUnary_apply]; omega)
    (fun x i _ => by simp)
    (fun x i _ => by simp)
  have hout (p : ℕ × ℕ) : encUnary (p.2 * p.1) = encBits
      (((List.range p.2).map fun i => List.replicate (id^[i] p.1) true).flatten ++
        Function.const ℕ ([] : List Bool) (id^[p.2] p.1)) := by
    simp [encBits, List.map_const']
  refine ComputableTidilyInO.of_bounds (h.of_enc_eq hout) (c * (2 * cc + 20) + 1)
    (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h₁ : 2 * cc + 2 + p.2 * (6 * p.1 + 9) + p.1 + 1 ≤
        (2 * cc + 20) * ((p.2 + 1) * (p.1 + 1)) := by
      nlinarith [Nat.zero_le (cc * p.2 * p.1), Nat.zero_le (cc * p.1), Nat.zero_le (p.2 * p.1),
        Nat.zero_le (cc * p.2)]
    calc c * (2 * cc + 2 + p.2 * (6 * p.1 + 9) + p.1 + 1)
        ≤ c * ((2 * cc + 20) * ((p.2 + 1) * (p.1 + 1))) := Nat.mul_le_mul_left c h₁
      _ ≤ (c * (2 * cc + 20) + 1) * ((p.2 + 1) * (p.1 + 1) + 1) := by nlinarith
  · have h₁ : 0 + 0 + p.1 + 1 ≤ (2 * cc + 20) * ((p.2 + 1) * (p.1 + 1)) := by
      nlinarith [Nat.zero_le (cc * p.2 * p.1), Nat.zero_le (cc * p.1), Nat.zero_le (p.2 * p.1),
        Nat.zero_le (cc * p.2)]
    calc c * (0 + 0 + p.1 + 1)
        ≤ c * ((2 * cc + 20) * ((p.2 + 1) * (p.1 + 1))) := Nat.mul_le_mul_left c h₁
      _ ≤ (c * (2 * cc + 20) + 1) * ((p.2 + 1) * (p.1 + 1) + 1) := by nlinarith
  · simp only [encUnary_apply, List.length_replicate]
    have h₁ : p.2 * p.1 ≤ (p.2 + 1) * (p.1 + 1) + 1 := by nlinarith
    exact h₁.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

/-- One round of the unary power: `(b, m) ↦ (b, m · b)`. -/
theorem unaryMulStep : ComputableTidilyInO (fun p : ℕ × ℕ => (p.1, p.2 * p.1))
    (encPair encUnary encUnary) (encPair encUnary encUnary)
    (fun p => (p.2 + 1) * (p.1 + 1)) (fun p => (p.2 + 1) * (p.1 + 1)) :=
  ((ComputableTidilyInO.fst encUnary encUnary).prod unaryMul).mono 4
    (fun p => by simp only [length_encPair, encUnary_apply, List.length_replicate]; nlinarith)
    (fun p => by simp only [length_encPair, encUnary_apply, List.length_replicate]; nlinarith)

theorem iterate_mulStep (b a i : ℕ) :
    (fun p : ℕ × ℕ => (p.1, p.2 * p.1))^[i] (b, a) = (b, a * b ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ, ← Nat.mul_assoc]

theorem mul_pow_le_add (a b i k : ℕ) (hi : i ≤ k) : a * b ^ i ≤ a * b ^ k + a := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · simp [Nat.zero_pow hi0]
  · have := Nat.mul_le_mul_left a (Nat.pow_le_pow_right hb hi)
    omega

/-- **Unary powers**: `a · b^k` from `((b, a), k)`, in time and space
`O((k + 1)(a b^k + a + 1)(b + 1))`. -/
theorem unaryPow : ComputableTidilyInO (fun y : (ℕ × ℕ) × ℕ => y.1.2 * y.1.1 ^ y.2)
    (encPair (encPair encUnary encUnary) encUnary) encUnary
    (fun y => (y.2 + 1) * ((y.1.2 * y.1.1 ^ y.2 + y.1.2 + 1) * (y.1.1 + 1)))
    (fun y => (y.2 + 1) * ((y.1.2 * y.1.1 ^ y.2 + y.1.2 + 1) * (y.1.1 + 1))) := by
  obtain ⟨cG, hG, -⟩ := unaryMulStep
  obtain ⟨cS, hS, -⟩ := ComputableTidilyInO.snd encUnary encUnary
  set P : (ℕ × ℕ) × ℕ → ℕ := fun y => (y.1.2 * y.1.1 ^ y.2 + y.1.2 + 1) * (y.1.1 + 1) with hP
  have h := iterate_finish hG hS (fun y => (4 * cG + 4 * cS + 3) * P y) (fun y i hi => by
    obtain ⟨⟨b, a⟩, k⟩ := y
    simp only [iterate_mulStep, length_encPair, encUnary_apply, List.length_replicate, hP] at hi ⊢
    have hw := mul_pow_le_add a b i k hi
    generalize a * b ^ i = w at hw ⊢
    generalize a * b ^ k + a = W at hw ⊢
    have hP1 : (w + 1) * (b + 1) ≤ (W + 1) * (b + 1) := Nat.mul_le_mul_right _ (by omega)
    have hP2 : w + b + 1 ≤ (W + 1) * (b + 1) := by nlinarith
    generalize (W + 1) * (b + 1) = Q at hP1 hP2 ⊢
    have h₃ := Nat.mul_le_mul_left cG (show (w + 1) * (b + 1) + 1 ≤ 2 * Q by omega)
    have h₄ := Nat.mul_le_mul_left cS (show 2 * b + 1 + w + 1 ≤ 2 * Q by omega)
    linarith)
  have hout (y : (ℕ × ℕ) × ℕ) : encUnary (y.1.2 * y.1.1 ^ y.2) =
      encUnary ((fun p : ℕ × ℕ => (p.1, p.2 * p.1))^[y.2] y.1).2 := by
    obtain ⟨⟨b, a⟩, k⟩ := y
    simp [iterate_mulStep]
  refine (h.of_enc_eq hout).mono (8 * cG + 8 * cS + 8) (fun y => ?_) (fun y => ?_) <;>
  · have h₀ : 1 ≤ P y := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have h₁ := Nat.mul_le_mul_left (y.2 + 1)
      (show (4 * cG + 4 * cS + 3) * P y + 1 ≤ (4 * cG + 4 * cS + 4) * P y by nlinarith)
    rw [hP] at h₁ ⊢
    nlinarith

end BHJK25.Machine.Loop
