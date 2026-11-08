module

public import BS23.Colinear.Alg
public import Background.PolyTime.Rat
public import Background.PolyTime.Lists
public import Mathlib.Data.List.GetD
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# Polynomial time for the colinear algorithm: scalar tools

Tools for `BS23/Colinear/PolyTime.lean`, which certifies that the algorithm of [BS23, Theorem
1.2] (`BS23.Colinear.colinearAlg`) runs in polynomial time:

* small certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) missing from complexitylib and
  `Background/PolyTime`: case distinctions on propositions, powers of rationals with a unary
  exponent, natural ceilings and floors of rationals;
* sums over `Fin n` and `Finset.range n` as sums of lists (`BS23.Colinear.PT.sum_fin_eq_list`);
* the Hermite polynomials `BS23.hermite` as list programs (`BS23.Colinear.PT.hermL`), with their
  coefficients from factorials (`BS23.Colinear.PT.hermCoeffL`);
* the scalar parameters: `BS23.logInv`, and the top scale `BS23.Colinear.topScale`, whose base-`4`
  logarithms are computed from base-`2` ones (`BS23.Colinear.PT.topScaleL`).
-/

@[expose] public section

namespace BS23.Colinear.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Small certificates -/

/-- A case distinction on a decidable proposition. -/
theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a ↦ decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a ↦ if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- A unary natural, in binary. -/
theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-- The sum of two binary naturals. -/
theorem binAdd' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add.comp (g := fun a ↦ (f a, g a))
    (hf.prod hg).tidy)

/-- The quotient of two binary naturals. -/
theorem binDiv' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a / g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_div' hf.tidy hg.tidy)

/-- A unary natural, as a rational. -/
theorem rat_ofUnary {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ (f a : ℚ)) input encRat :=
  rat_natCast' (toBinary' hf)

/-- A power of a rational with a unary exponent: the powers of the numerator and the
denominator, which stay coprime. -/
theorem rat_pow' {f : α → ℚ} {e : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ e a) input encRat :=
  rat_of_numDen (g := fun a ↦ ((f a).num ^ e a, (f a).den ^ e a))
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.intBin_pow' (rat_num' hf).tidy
      he.tidy)).prod (binary_pow' (rat_den' hf) he))
    fun a ↦ by rw [Rat.num_pow, Rat.den_pow]

/-- The natural ceiling of a rational, in binary. -/
theorem rat_natCeil' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌈f a⌉₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (-⌊-f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp
      (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hf)).tidy))
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_neg, neg_neg, Int.ceil_toNat]

/-- The natural floor of a rational, in binary. -/
theorem rat_natFloor' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌊f a⌋₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (⌊f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp (rat_floor' hf).tidy)
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_toNat]

/-! ### Sums as sums of lists -/

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
                 simp

theorem sum_fin_eq_list {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (g : ℕ → M)
    (h : ∀ i : Fin n, g i = f i) : ∑ i, f i = ((List.range n).map g).sum := by
  rw [← sum_range_eq_list, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ (h i).symm

theorem getD_map_range {β : Type*} (g : ℕ → β) {n a : ℕ} (d : β) (h : a < n) :
    ((List.range n).map g).getD a d = g a := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]

/-! ### Hermite polynomials -/

/-- The double factorial `(2i - 1)‼ = (2i)! / (2^i i!)`. -/
theorem doubleFactorial_eq_div (i : ℕ) :
    Nat.doubleFactorial (2 * i - 1) = (2 * i).factorial / (2 ^ i * i.factorial) := by
  have hpos : 0 < 2 ^ i * i.factorial := Nat.mul_pos (Nat.two_pow_pos i) i.factorial_pos
  rcases i with _ | j
  · simp
  · have h : (2 * (j + 1)).factorial = 2 ^ (j + 1) * (j + 1).factorial *
        Nat.doubleFactorial (2 * (j + 1) - 1) := by
      have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
      have e' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [e', e, Nat.factorial_eq_mul_doubleFactorial, ← e, Nat.doubleFactorial_two_mul]
    rw [h, Nat.mul_div_cancel_left _ hpos]

/-- The Hermite coefficient `C(m, 2i) (2i-1)‼`, from factorials. -/
def hermCoeffL (m i : ℕ) : ℕ :=
  (if 2 * i ≤ m then m.factorial / ((2 * i).factorial * (m - 2 * i).factorial) else 0) *
    ((2 * i).factorial / (2 ^ i * i.factorial))

theorem hermCoeffL_eq (m i : ℕ) : hermCoeffL m i = hermCoeff m i := by
  rw [hermCoeffL, hermCoeff, doubleFactorial_eq_div]
  congr 1
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

/-- The Hermite polynomial `BS23.hermite` as a sum of a list. -/
def hermL (m : ℕ) (x q : ℚ) : ℚ :=
  ((List.range (m / 2 + 1)).map fun i ↦
    (-1 : ℚ) ^ i * (hermCoeffL m i : ℚ) * x ^ (m - 2 * i) * q ^ i).sum

theorem hermL_eq (m : ℕ) (x q : ℚ) : hermL m x q = hermite m x q := by
  rw [hermL, hermite, sum_range_eq_list]
  simp only [hermCoeffL_eq]

theorem hermCoeffL_polytime : ComputableInPolyTime (fun p : ℕ × ℕ ↦ hermCoeffL p.1 p.2)
    (encPair encUnary encUnary) encNat := by
  unfold hermCoeffL
  have h2i : ComputableInPolyTime (fun p : ℕ × ℕ ↦ 2 * p.2) (encPair encUnary encUnary)
      encUnary := unary_mul' (const 2) (snd _ _)
  have hm : ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.1) (encPair encUnary encUnary) encUnary :=
    fst _ _
  have hf2i : ComputableInPolyTime (fun p : ℕ × ℕ ↦ (2 * p.2).factorial)
      (encPair encUnary encUnary) encNat := binary_factorial.comp h2i
  refine binary_mul' (ite_prop (unary_le' h2i hm) (binDiv' (binary_factorial.comp hm)
    (binary_mul' hf2i (binary_factorial.comp (unary_sub' hm h2i)))) (const 0))
    (binDiv' hf2i (binary_mul' (binary_two_pow.comp (snd _ _))
      (binary_factorial.comp (snd _ _))))

@[fun_prop]
theorem hermCoeffL' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ hermCoeffL (f a) (g a)) input encNat :=
  hermCoeffL_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem hermL_polytime : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ ↦ hermL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encRat encRat)) encRat := by
  unfold hermL
  set E := encPair encUnary (encPair encRat encRat)
  have hr : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ ↦ List.range (p.1 / 2 + 1)) E
      (encList encUnary) :=
    range.comp (unary_add' ((unary_div_const 2).comp (fst _ _)) (const 1))
  have hi : ComputableInPolyTime (fun p : (ℕ × ℚ × ℚ) × ℕ ↦ p.2) (encPair E encUnary) encUnary :=
    snd _ _
  have hm : ComputableInPolyTime (fun p : (ℕ × ℚ × ℚ) × ℕ ↦ p.1.1) (encPair E encUnary)
      encUnary := (fst _ _).comp (fst _ _)
  have hx : ComputableInPolyTime (fun p : (ℕ × ℚ × ℚ) × ℕ ↦ p.1.2.1) (encPair E encUnary)
      encRat := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hq : ComputableInPolyTime (fun p : (ℕ × ℚ × ℚ) × ℕ ↦ p.1.2.2) (encPair E encUnary)
      encRat := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact rat_sum' (mapWithInput hr (rat_mul' (rat_mul' (rat_mul' (rat_pow' (const (-1)) hi)
    (rat_natCast' (hermCoeffL' hm hi))) (rat_pow' hx (unary_sub' hm (unary_mul' (const 2) hi))))
    (rat_pow' hq hi)))

@[fun_prop]
theorem hermL' {f : α → ℕ} {g h : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encRat) (hh : ComputableInPolyTime h input encRat) :
    ComputableInPolyTime (fun a ↦ hermL (f a) (g a) (h a)) input encRat :=
  hermL_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

/-! ### The scalar parameters -/

theorem logInv_polytime : ComputableInPolyTime logInv encRat encUnary :=
  binary_clog_two.comp (rat_natCeil' (rat_inv' id'))

@[fun_prop]
theorem logInv' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ logInv (f a)) input encUnary :=
  logInv_polytime.comp hf

/-- Base-`4` logarithms from base-`2` ones. -/
theorem log_four (N : ℕ) : Nat.log 4 N = Nat.log 2 N / 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h2 := Nat.pow_log_le_self 2 hN.ne'
  have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hN.ne'⟩)]
  have e : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k ↦ by rw [pow_mul]; norm_num
  constructor
  · rw [e]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h2
  · rw [e]
    exact h3.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Base-`4` ceiling logarithms from base-`2` ones. -/
theorem clog_four (N : ℕ) : Nat.clog 4 N = (Nat.clog 2 N + 1) / 2 := by
  have e : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k ↦ by rw [pow_mul]; norm_num
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), e]
    exact (Nat.le_pow_clog (by norm_num) N).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have h := Nat.le_pow_clog (by norm_num : 1 < 4) N
    rw [e, ← Nat.clog_le_iff_le_pow (by norm_num)] at h
    omega

/-- The top scale `BS23.Colinear.topScale`, with base-`2` logarithms. -/
def topScaleL (A v : ℚ) : ℚ :=
  if 1 ≤ 2 * A ^ 2 * v then (2 : ℚ) ^ ((Nat.clog 2 ⌈2 * A ^ 2 * v⌉₊ + 1) / 2)
  else ((2 : ℚ) ^ (Nat.log 2 ⌊(2 * A ^ 2 * v)⁻¹⌋₊ / 2))⁻¹

theorem topScaleL_eq (A v : ℚ) : topScaleL A v = topScale A v := by
  rw [topScaleL, topScale, Int.clog]
  split_ifs
  · rw [zpow_natCast, clog_four]
  · rw [zpow_neg, zpow_natCast, log_four]

theorem topScaleL_polytime : ComputableInPolyTime (fun p : ℚ × ℚ ↦ topScaleL p.1 p.2)
    (encPair encRat encRat) encRat := by
  unfold topScaleL
  have hr : ComputableInPolyTime (fun p : ℚ × ℚ ↦ 2 * p.1 ^ 2 * p.2) (encPair encRat encRat)
      encRat := rat_mul' (rat_mul' (const 2) (rat_sq' (fst _ _))) (snd _ _)
  exact ite_prop (rat_le' (const 1) hr)
    (rat_two_pow' ((unary_div_const 2).comp (unary_add' (binary_clog_two.comp (rat_natCeil' hr))
      (const 1))))
    (rat_inv' (rat_two_pow' ((unary_div_const 2).comp
      (binary_log_two.comp (rat_natFloor' (rat_inv' hr))))))

@[fun_prop]
theorem topScaleL' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a ↦ topScaleL (f a) (g a)) input encRat :=
  topScaleL_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

end BS23.Colinear.PT
