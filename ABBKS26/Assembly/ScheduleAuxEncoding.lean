module

public import ABBKS26.Select.Recluster

/-! Rational encoding estimates for the schedule ledger. -/

@[expose] public section

namespace ABBKS26.Schedule.EncodingBounds

open Common Turing.MultiTapeTM

/-- Magnitude and denominator bounds suffice for binary encoding, without a dyadic input. -/
structure RatBound (b : ℕ) (q : ℚ) : Prop where
  magnitude : |q| ≤ 2 ^ b
  denominator : q.den ≤ 2 ^ b

theorem RatBound.mono {a b : ℕ} {q : ℚ} (h : RatBound a q) (hab : a ≤ b) :
    RatBound b q :=
  ⟨h.magnitude.trans (pow_le_pow_right₀ (by norm_num) hab),
    h.denominator.trans (Nat.pow_le_pow_right (by norm_num) hab)⟩

theorem RatBound.zero (b : ℕ) : RatBound b 0 := by
  exact ⟨by simp, by simpa using Nat.one_le_two_pow⟩

theorem RatBound.one : RatBound 0 1 := by constructor <;> norm_num

theorem RatBound.neg {b : ℕ} {q : ℚ} (h : RatBound b q) : RatBound b (-q) := by
  exact ⟨by simpa only [abs_neg] using h.magnitude,
    by simpa only [Rat.den_neg_eq_den] using h.denominator⟩

theorem RatBound.mul {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b) (q * r) := by
  constructor
  · rw [abs_mul, pow_add]
    exact mul_le_mul hq.magnitude hr.magnitude (abs_nonneg _) (by positivity)
  · apply (Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd q r)).trans
    simpa only [pow_add] using Nat.mul_le_mul hq.denominator hr.denominator

theorem RatBound.add {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b + 1) (q + r) := by
  have ha : (1 : ℚ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hb : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  constructor
  · apply (abs_add_le q r).trans
    calc
      _ ≤ 2 ^ a + 2 ^ b := add_le_add hq.magnitude hr.magnitude
      _ ≤ 2 ^ a * 2 ^ b + 2 ^ a * 2 ^ b :=
        add_le_add (le_mul_of_one_le_right (by positivity) hb)
          (le_mul_of_one_le_left (by positivity) ha)
      _ = _ := by rw [pow_succ, pow_add]; ring
  · apply (Nat.le_of_dvd (by positivity) (Rat.add_den_dvd q r)).trans
    exact (Nat.mul_le_mul hq.denominator hr.denominator).trans
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))

theorem RatBound.sub {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b + 1) (q - r) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg


theorem RatBound.bits {b : ℕ} {q : ℚ} (h : RatBound b q) :
    (Encoding.encRat q).length ≤ 6 * b + 6 := by
  have hn : q.num.natAbs ≤ 2 ^ (2 * b) := by
    have he : (q.num.natAbs : ℚ) = |q| * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
    have hd : (q.den : ℚ) ≤ 2 ^ b := by exact_mod_cast h.denominator
    have hb : (q.num.natAbs : ℚ) ≤ 2 ^ (2 * b) := by
      rw [he, two_mul, pow_add]
      exact mul_le_mul h.magnitude hd (by positivity) (by positivity)
    exact_mod_cast hb
  have hn' : q.num.natAbs < 2 ^ (2 * b + 1) :=
    hn.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hd' : q.den < 2 ^ (2 * b + 1) :=
    h.denominator.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  change (encPair encIntBin encNat (q.num, q.den)).length ≤ _
  rw [length_encPair, length_encIntBin]
  have hnum := Nat.size_le.mpr hn'
  have hden := length_encNat_le_of_lt_two_pow hd'
  simp only at hnum hden ⊢
  omega

theorem of_encoding {b : ℕ} {q : ℚ} (hq : (Encoding.encRat q).length ≤ b) :
    RatBound b q := by
  change (encPair encIntBin encNat (q.num, q.den)).length ≤ b at hq
  simp only [length_encPair, length_encIntBin, encNat_apply, Nat.size_eq_bits_len] at hq
  have hn : q.num.natAbs < 2 ^ b := Nat.size_le.mp (by omega)
  have hd : q.den < 2 ^ b := Nat.size_le.mp (by omega)
  constructor
  · have he : (q.num.natAbs : ℚ) = |q| * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
    have hd1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have hm : |q| ≤ (q.num.natAbs : ℚ) := by
      rw [he]
      exact le_mul_of_one_le_right (abs_nonneg _) hd1
    exact hm.trans (by exact_mod_cast hn.le)
  · exact hd.le


theorem RatBound.inv {q : ℚ} {b : ℕ} (h : RatBound b q) :
    RatBound (2 * b) q⁻¹ := by
  by_cases hq : q = 0
  · simpa only [hq, inv_zero] using RatBound.zero (2 * b)
  have hn : 1 ≤ q.num.natAbs := by
    have hne : q.num ≠ 0 := fun hn ↦ hq (Rat.num_eq_zero.mp hn)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have he : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
      abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  have hnum : q.num.natAbs ≤ 2 ^ (2 * b) := by
    have hd : (q.den : ℚ) ≤ 2 ^ b := by exact_mod_cast h.denominator
    have hb : (q.num.natAbs : ℚ) ≤ 2 ^ (2 * b) := by
      rw [he, two_mul, pow_add]
      exact mul_le_mul h.magnitude hd (by positivity) (by positivity)
    exact_mod_cast hb
  constructor
  · have hinv : |q⁻¹| ≤ q.den := by
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hq)]
      have hn' : (1 : ℚ) ≤ q.num.natAbs := by exact_mod_cast hn
      simpa only [he, mul_comm] using hn'
    exact hinv.trans ((by exact_mod_cast h.denominator : (q.den : ℚ) ≤ 2 ^ b).trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  · simpa only [Rat.den_inv_of_ne_zero hq] using hnum


theorem RatBound.pow {b : ℕ} {q : ℚ} (hq : RatBound b q) (m : ℕ) :
    RatBound (b * m) (q ^ m) := by
  induction m with
  | zero => simpa using RatBound.one
  | succ m ih => simpa only [pow_succ, Nat.mul_succ, Nat.add_comm] using ih.mul hq

theorem RatBound.min {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (max a b) (min q r) := by
  rcases le_total q r with h | h
  · simpa only [min_eq_left h] using hq.mono (le_max_left _ _)
  · simpa only [min_eq_right h] using hr.mono (le_max_right _ _)

/-- A positive dyadic reciprocal is paid for by its numerical reciprocal. -/
theorem down {q : ℚ} (b : ℕ) (h : 1 / dyadicDown q ≤ b) :
    RatBound (b + 1) (dyadicDown q) := by
  by_cases hq : 0 < q
  · simp only [dyadicDown, ite_eq_left hq] at h ⊢
    let m := Nat.clog 2 ⌈1 / q⌉₊ + 1
    have he : (2 : ℚ) ^ m = ((2 ^ m : ℕ) : ℚ) := by push_cast; rfl
    change RatBound (b + 1) ((2 : ℚ) ^ m)⁻¹
    rw [he]
    constructor
    · rw [abs_of_nonneg (by positivity)]
      have hh : (1 : ℚ) ≤ (2 ^ m : ℕ) := by exact_mod_cast Nat.one_le_two_pow
      exact (inv_le_one_of_one_le₀ hh).trans (one_le_pow₀ (by norm_num))
    · rw [Rat.inv_natCast_den_of_pos (by positivity)]
      have hh : 2 ^ m ≤ b := by
        change 1 / ((2 : ℚ) ^ m)⁻¹ ≤ b at h
        simp only [one_div, inv_inv] at h
        exact_mod_cast h
      exact hh.trans ((Nat.le_add_right b 1).trans (Nat.lt_two_pow_self (n := b + 1)).le)
  · simp only [dyadicDown, ite_eq_right hq]
    exact RatBound.zero _

/-- Upward dyadics are integers, so their value also pays for their denominator. -/
theorem up {q : ℚ} (b : ℕ) (h : dyadicUp q ≤ b) : RatBound (b + 1) (dyadicUp q) := by
  constructor
  · rw [abs_of_nonneg (by unfold dyadicUp; positivity)]
    exact h.trans (by exact_mod_cast
      (Nat.le_add_right b 1).trans (Nat.lt_two_pow_self (n := b + 1)).le)
  · simp only [dyadicUp, Rat.den_pow, Rat.den_ofNat, one_pow]
    exact Nat.one_le_two_pow

theorem up_bound {b : ℕ} {q : ℚ} (hq : RatBound b q) : RatBound b (dyadicUp q) := by
  have he : max 1 ⌈q⌉₊ ≤ 2 ^ b := by
    apply max_le (Nat.one_le_two_pow)
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (le_abs_self q).trans hq.magnitude
  have hc := Nat.clog_le_of_le_pow he
  constructor
  · rw [abs_of_nonneg (by unfold dyadicUp; positivity)]
    exact pow_le_pow_right₀ (by norm_num) hc
  · simp only [dyadicUp, Rat.den_pow, Rat.den_ofNat, one_pow]
    exact Nat.one_le_two_pow

theorem sqrt_bound {b : ℕ} {q : ℚ} (hq : RatBound b q) :
    RatBound (b + 1) (sqrtUp q) := by
  have he : ⌈max 0 q⌉₊ ≤ 2 ^ b := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (max_le (by positivity) ((le_abs_self q).trans hq.magnitude) :
        max 0 q ≤ (2 : ℚ) ^ b)
  have hn : Nat.sqrt ⌈max 0 q⌉₊ + 1 ≤ 2 ^ (b + 1) := by
    have hh := (Nat.sqrt_le_self ⌈max 0 q⌉₊).trans he
    have hp : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  constructor
  · rw [sqrtUp, abs_of_nonneg (by positivity)]
    exact_mod_cast hn
  · simp only [sqrtUp, Rat.den_natCast]
    exact Nat.one_le_two_pow

theorem RatBound.div {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + 2 * b) (q / r) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

theorem RatBound.max {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (max a b) (max q r) := by
  rcases le_total q r with h | h
  · simpa only [max_eq_right h] using hr.mono (le_max_right _ _)
  · simpa only [max_eq_left h] using hq.mono (le_max_left _ _)

def values (p : Tree.StepParams) : List ℚ :=
  [p.w, p.straddle, p.windowMass, p.verifyMass, p.tail, p.K, p.WF, p.DF, p.R,
    p.sigmaSq, p.subspaceAccuracy, p.isotropy, p.momentError, p.frameAccuracy,
    p.contamination, p.leakage, p.separation]


theorem list_bits (xs : List ℚ) (b : ℕ) (hb : ∀ q ∈ xs, RatBound b q) :
    (Encoding.encList Encoding.encRat xs).length ≤ xs.length * (12 * b + 13) := by
  have hh := length_encList_le Encoding.encRat xs (fun q hq ↦ (hb q hq).bits)
  exact hh.trans_eq (by congr 1; ring)

end ABBKS26.Schedule.EncodingBounds
