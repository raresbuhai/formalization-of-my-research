module

public import BDT24.Alg.Numerics
public import Background.SumOfSquares.Algorithm.PolyTime
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial

/-!
# The numerics in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the rational approximations of
`BDT24/Alg/Numerics.lean`, copied from `BGHKLMM26/PolyTime.lean` (papers do not import each
other): the series of `Φ`, `π` from nested square roots, and the Gaussian of a cell by bisection
on `Φ` (`BDT24.Alg.PT.cellInv'`), whose endpoints stay dyadic with a bounded number of bits.
-/

@[expose] public section

namespace BDT24.Alg.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS.PolyTime SoS.Loop

variable {α : Type} {input : α ↪ List Bool}

/-- A unary natural, in binary. -/
theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-- A power of a rational with a unary exponent. -/
theorem rat_pow' {f : α → ℚ} {k : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ k a) input encRat := by
  have e : (fun a ↦ f a ^ k a) = fun a ↦ (List.replicate (k a) (f a)).prod :=
    funext fun a ↦ (List.prod_replicate _ _).symm
  rw [e]
  exact rat_prod' (replicate hk hf)

/-- A term of the series of `Φ`. -/
@[fun_prop]
theorem phiTermQ' {f : α → ℚ} {m : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.phiTermQ (f a) (m a)) input encRat := by
  unfold Num.phiTermQ
  have h1 := rat_pow' (const (-1 : ℚ)) hm
  have h2 := rat_pow' hf (show ComputableInPolyTime (fun a ↦ 2 * m a + 1) input encUnary by
    fun_prop)
  have h3 : ComputableInPolyTime (fun a ↦ ((m a).factorial : ℚ)) input encRat :=
    rat_natCast' (binary_factorial.comp hm)
  have h4 : ComputableInPolyTime (fun a ↦ ((m a : ℕ) : ℚ)) input encRat :=
    rat_natCast' (toBinary' hm)
  have h5 := rat_two_pow' hm
  exact rat_div' (rat_mul' h1 h2) (rat_mul' (rat_mul' h5 h3)
    (rat_add' (rat_mul' (const 2) h4) (const 1)))

/-- A partial sum of the series of `Φ`. -/
@[fun_prop]
theorem phiSumQ' {N : α → ℕ} {f : α → ℚ} (hN : ComputableInPolyTime N input encUnary)
    (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ Num.phiSumQ (N a) (f a)) input encRat := by
  unfold Num.phiSumQ
  exact rat_sum' (mapWithInput (f := fun a (m : ℕ) ↦ Num.phiTermQ (f a) m) (by fun_prop)
    (phiTermQ' (hf.comp (fst _ _)) (snd _ _)))

/-- The nested square roots as an iteration. -/
theorem nestQ_eq_iterate (p n : ℕ) :
    Num.nestQ p n = (fun y ↦ sqrtP p (2 + y))^[n] 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The nested square roots are at most `2` and multiples of `2^-p`. -/
theorem small_nestQ (p n : ℕ) : Small p 1 (Num.nestQ p n) := by
  rcases n with _ | n
  · exact small_zero p 1
  · have h0 : (0 : ℚ) ≤ 2 + Num.nestQ p n := by have := Num.nestQ_nonneg p n; linarith
    refine ⟨?_, ?_⟩
    · rw [Num.nestQ, abs_of_nonneg (Num.sqrtP_nonneg _ _), pow_one]
      have h1 := Num.sqrtP_le_sqrt p h0
      have h2 := (Num.nestQ_spec p n).1
      have h3 := Real.sqrtTwoAddSeries_lt_two n
      have h4 : √((2 + Num.nestQ p n : ℚ) : ℝ) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; push_cast; linarith
      exact_mod_cast h1.trans h4
    · refine ⟨Nat.sqrt (⌊(2 + Num.nestQ p n) * 4 ^ p⌋.natAbs), ?_⟩
      rw [Num.nestQ, sqrtP]
      field_simp
      push_cast
      ring

/-- The nested square roots. -/
@[fun_prop]
theorem nestQ' {p n : α → ℕ} (hp : ComputableInPolyTime p input encUnary)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.nestQ (p a) (n a)) input encRat := by
  have e : (fun a ↦ Num.nestQ (p a) (n a)) =
      fun a ↦ ((fun (q : ℕ) (y : ℚ) ↦ sqrtP q (2 + y)) (p a))^[n a] 0 :=
    funext fun a ↦ nestQ_eq_iterate _ _
  rw [e]
  have hstep : ComputableInPolyTime (fun q : ℕ × ℚ ↦ sqrtP q.1 (2 + q.2))
      (encPair encUnary encRat) encRat := sqrtP' (by fun_prop) (by fun_prop)
  refine iterateWith (par := p) (count := n) (init := fun _ ↦ (0 : ℚ))
    (step := fun (q : ℕ) (y : ℚ) ↦ sqrtP q (2 + y)) hp hn (const 0) hstep
    (bound := fun a ↦ 3 * (1 + p a) + 6)
    (by have := hp.polyBounded; exact ((PolyBounded.const 3).mul ((PolyBounded.const 1).add
      this)).add (.const 6)) fun a i _ ↦ ?_
  rw [← nestQ_eq_iterate]
  exact length_encRat_le_of_small (small_nestQ _ _)

/-- The approximation of `π`. -/
@[fun_prop]
theorem piQ' {n : α → ℕ} (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.piQ (n a)) input encRat := by
  unfold Num.piQ
  have h4 : ComputableInPolyTime (fun a ↦ 4 * n a + 3) input encUnary := by fun_prop
  have := nestQ' h4 hn
  have := sqrtP' h4 (rat_sub' (const 2) this)
  have := rat_two_pow' (show ComputableInPolyTime (fun a ↦ n a + 1) input encUnary by fun_prop)
  fun_prop

/-- The approximation of `Φ`. -/
@[fun_prop]
theorem phiQ' {n N : α → ℕ} {f : α → ℚ} (hn : ComputableInPolyTime n input encUnary)
    (hN : ComputableInPolyTime N input encUnary) (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ Num.phiQ (n a) (N a) (f a)) input encRat := by
  unfold Num.phiQ Num.invSqrt2piQ
  have := sqrtP' hn (rat_mul' (const 2) (piQ' hn))
  have := phiSumQ' hN hf
  fun_prop

/-! ### Bisection and the Gaussians -/

/-- The bisection's endpoints are multiples of `2^-i` after `i` steps. -/
theorem bisect_dyadic (f : ℚ → ℚ) (u X : ℚ) (hX : ∃ z : ℤ, X = z) (i : ℕ) :
    (∃ z : ℤ, (Num.bisect f u X i).1 * 2 ^ i = z) ∧
      ∃ z : ℤ, (Num.bisect f u X i).2 * 2 ^ i = z := by
  obtain ⟨x, rfl⟩ := hX
  induction i with
  | zero => exact ⟨⟨-x, by simp [Num.bisect]⟩, ⟨x, by simp [Num.bisect]⟩⟩
  | succ i ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hs : Num.bisect f u x (i + 1) = Num.bisectStep f u (Num.bisect f u x i) := by
      simp only [Num.bisect, Function.iterate_succ_apply']
    rw [hs]
    unfold Num.bisectStep
    have hm : ((Num.bisect f u x i).1 + (Num.bisect f u x i).2) / 2 * 2 ^ (i + 1) = a + b := by
      rw [← ha, ← hb, pow_succ]; ring
    have hlo : (Num.bisect f u x i).1 * 2 ^ (i + 1) = (2 * a : ℤ) := by
      push_cast; rw [← ha, pow_succ]; ring
    have hhi : (Num.bisect f u x i).2 * 2 ^ (i + 1) = (2 * b : ℤ) := by
      push_cast; rw [← hb, pow_succ]; ring
    split_ifs
    · exact ⟨⟨a + b, by rw [hm]; push_cast; ring⟩, ⟨2 * b, hhi⟩⟩
    · exact ⟨⟨2 * a, hlo⟩, ⟨a + b, by rw [hm]; push_cast; ring⟩⟩

/-- The bisection's endpoints are small. -/
theorem small_bisect (f : ℚ → ℚ) (u : ℚ) (R K i : ℕ) (hi : i ≤ K) :
    Small K (R + 1) (Num.bisect f u ((R : ℚ) + 1) i).1 ∧
      Small K (R + 1) (Num.bisect f u ((R : ℚ) + 1) i).2 := by
  have hX : (0 : ℚ) ≤ (R : ℚ) + 1 := by positivity
  obtain ⟨h0, h1, h5, -, -, -⟩ := Num.bisect_spec f u hX i
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bisect_dyadic f u ((R : ℚ) + 1) ⟨R + 1, by push_cast; ring⟩ i
  have hR : (R : ℚ) + 1 ≤ 2 ^ (R + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := R + 1)).le
  have hK : (2 : ℚ) ^ K = 2 ^ i * 2 ^ (K - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  refine ⟨⟨abs_le.2 ⟨by linarith, by linarith⟩, a * 2 ^ (K - i), ?_⟩,
    ⟨abs_le.2 ⟨by linarith, by linarith⟩, b * 2 ^ (K - i), ?_⟩⟩
  · rw [hK, ← mul_assoc, ha]; push_cast; ring
  · rw [hK, ← mul_assoc, hb]; push_cast; ring

/-- Pairs of rationals. -/
abbrev encQQ : ℚ × ℚ ↪ List Bool := encPair encRat encRat

/-- One step of the bisection on `Φ`. -/
theorem bisectStep_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ Num.bisectStep (Num.phiQ q.1.1 q.1.2.1) q.1.2.2 q.2)
    (encPair (encPair encUnary (encPair encUnary encRat)) encQQ) encQQ := by
  unfold Num.bisectStep
  have hm : ComputableInPolyTime (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ (q.2.1 + q.2.2) / 2)
      (encPair (encPair encUnary (encPair encUnary encRat)) encQQ) encRat := by fun_prop
  have hc := rat_lt' (phiQ' (n := fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.1.1)
    (N := fun q ↦ q.1.2.1) (by fun_prop) (by fun_prop) hm)
    (show ComputableInPolyTime (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.1.2.2) _ encRat by fun_prop)
  exact ite' hc (hm.prod (by fun_prop)) ((by fun_prop : ComputableInPolyTime
    (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.2.1) _ encRat).prod hm)

/-- **The Gaussian of a cell**, by bisection on `Φ`. -/
@[fun_prop]
theorem cellInv' {n N K B R j : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hN : ComputableInPolyTime N input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hB : ComputableInPolyTime B input encUnary) (hR : ComputableInPolyTime R input encUnary)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ Num.cellInv (n a) (N a) (K a) (B a) ((R a : ℚ) + 1) (j a))
      input encRat := by
  unfold Num.cellInv Num.bisect
  have hu : ComputableInPolyTime (fun a ↦ ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1))) input encRat := by
    have := rat_natCast' hj
    have := rat_two_pow' (show ComputableInPolyTime (fun a ↦ B a + 1) input encUnary by fun_prop)
    fun_prop
  have hX : ComputableInPolyTime (fun a ↦ ((R a : ℚ) + 1)) input encRat := by
    have := rat_natCast' (toBinary' hR)
    fun_prop
  have hit := iterateWith (par := fun a ↦ (n a, N a, (2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)))
    (count := K) (init := fun a ↦ (-((R a : ℚ) + 1), (R a : ℚ) + 1))
    (step := fun (q : ℕ × ℕ × ℚ) (s : ℚ × ℚ) ↦ Num.bisectStep (Num.phiQ q.1 q.2.1) q.2.2 s)
    (hn.prod (hN.prod hu)) hK ((rat_neg' hX).prod hX) bisectStep_polytime
    (bound := fun a ↦ 9 * (R a + 1 + K a) + 19)
    (by
      have h1 := hR.polyBounded
      have h2 := hK.polyBounded
      exact ((PolyBounded.const 9).mul ((h1.add (.const 1)).add h2)).add (.const 19))
    (fun a i hi ↦ by
      obtain ⟨h1, h2⟩ := small_bisect (Num.phiQ (n a) (N a))
        ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)) (R a) (K a) i hi
      have l1 := length_encRat_le_of_small h1
      have l2 := length_encRat_le_of_small h2
      have : ((Num.bisectStep (Num.phiQ (n a) (N a)) ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)))^[i]
          (-((R a : ℚ) + 1), (R a : ℚ) + 1)) = Num.bisect (Num.phiQ (n a) (N a))
          ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)) ((R a : ℚ) + 1) i := rfl
      rw [this, length_encPair]
      omega)
  exact hit.fst'

end BDT24.Alg.PT
