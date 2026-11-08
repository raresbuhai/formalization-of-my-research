module

public import BHJK25.RS.Alg.PolyTimeGuess
public import BHJK25.RS.Basic.Params
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# The data of a run in polynomial time

Certificates for the data computed once from the input (`BHJK25.RS.AlgAux.mkDat`), ending with
`BHJK25.RS.AlgAux.mkDat_polytime`, from `T` and `n` in unary, `n` also in binary, and the table.
The parameters `r` (`BHJK25.RS.rbits`) and `ℓ` (`BHJK25.RS.ell`) are computed in unary from
`⌈log₂ n⌉`; the numbers `m ≤ 2n + 1`, `W ≤ 2n + 2` and `q = 2^r ≤ 16 (2n + 1)²` are computed in
binary and written in unary under these bounds (`BHJK25.RS.AlgAux.mdeg_le`,
`BHJK25.RS.AlgAux.wdeg_le`, `BHJK25.RS.AlgAux.two_pow_rbits_le`). The list of the `q` field
elements is tabulated, and the modulus `BHJK25.RS.irrPoly` is the first of them without zero
divisors, which is tested on all `q²` pairs of elements, with `q` read from the data
(`BHJK25.RS.AlgAux.irrPoly_eq`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Bounds on the parameters -/

theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
    obtain ⟨c, hc⟩ : ∃ c, Nat.clog 2 n = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.clog_pos (by norm_num) hn)).symm⟩
    rw [hc, Nat.pred_succ] at h
    rw [hc, pow_succ]
    omega
  · rw [Nat.clog_of_right_le_one hn]
    omega

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 (Nat.lt_two_pow_self).le

theorem two_pow_rbits_le (T n : ℕ) : 2 ^ rbits T n ≤ 16 * (2 * n + 1) ^ 2 := by
  calc 2 ^ rbits T n ≤ 2 ^ (2 * Nat.clog 2 n + 4) :=
        Nat.pow_le_pow_right (by norm_num) (rbits_le T n)
    _ = 16 * (2 ^ Nat.clog 2 n) ^ 2 := by ring
    _ ≤ 16 * (2 * n + 1) ^ 2 := by
        have := two_pow_clog_le n
        gcongr

theorem mdeg_le (T n : ℕ) : mdeg T n ≤ 2 * n + 1 := by
  unfold mdeg
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (two_pow_clog_le n)
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  · refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hT).2 ?_)
    have : (T - 1) * Nat.clog 2 n ≤ Nat.clog 2 n * T := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [Nat.succ_mul]
    omega

theorem wdeg_le (T n : ℕ) : wdeg T n ≤ 2 * n + 2 := by
  unfold wdeg
  have h : Nat.sqrt (2 * n * mdeg T n) < 2 * n + 1 := by
    rw [Nat.sqrt_lt']
    have := Nat.mul_le_mul_left (2 * n) (mdeg_le T n)
    nlinarith
  omega

/-! ### The parameters -/

variable {α : Type} {input : α ↪ List Bool}

theorem rbits_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) :
    ComputableInPolyTime (fun a ↦ rbits (T a) (n a)) input encUnary := by
  have hc := binary_clog_two.comp' hn
  have h2T := unary_mul' (const 2) hT
  exact unary_add' (unary_add' hc
    (unary_div.comp' ((unary_sub' (unary_add' hc h2T) (const 1)).prod h2T))) (const 4)

theorem ell_polytime (k : ℕ) {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) :
    ComputableInPolyTime (fun a ↦ ell k (T a) (n a)) input encUnary := by
  have hr := rbits_polytime hT hn
  have hfind := findWithInput (test := fun a l ↦ decide (rbits (T a) (n a) ≤ l ^ (k - 1)))
    (range.comp' (unary_add' hr (const 1)))
    (unary_le' (hr.comp' (fst _ _)) ((unary_pow (k - 1)).comp' (snd _ _)))
  exact (optionGetD encUnary).comp' (hfind.prod hr)

theorem mdeg_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) (hnu : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ mdeg (T a) (n a)) input encUnary := by
  have hc := binary_clog_two.comp' hn
  have he := unary_div.comp' ((unary_sub' (unary_add' (unary_mul' (unary_sub' hT (const 1)) hc)
    hT) (const 1)).prod hT)
  exact binary_to_unary_bounded (binary_two_pow.comp' he)
    (unary_add' (unary_mul' (const 2) hnu) (const 1)) fun a ↦ mdeg_le (T a) (n a)

theorem wdeg_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) (hnu : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ wdeg (T a) (n a)) input encUnary := by
  have hW : ComputableInPolyTime (fun a ↦ wdeg (T a) (n a)) input encNat :=
    binary_add.comp' ((binary_sqrt' (binary_mul' (binary_mul' (const 2) hn)
      (toBin (mdeg_polytime hT hn hnu)))).prod (const 1))
  exact binary_to_unary_bounded hW (unary_add' (unary_mul' (const 2) hnu) (const 2))
    fun a ↦ wdeg_le (T a) (n a)

/-- The number `q = 2^r` of field elements, in unary. -/
theorem fieldSize_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) (hnu : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ 2 ^ rbits (T a) (n a)) input encUnary :=
  binary_to_unary_bounded (binary_two_pow.comp' (rbits_polytime hT hn))
    (unary_mul' (const 16) ((unary_pow 2).comp' (unary_add' (unary_mul' (const 2) hnu)
      (const 1)))) fun a ↦ two_pow_rbits_le (T a) (n a)

/-! ### The field -/

theorem bitsOf_polytime {r a : α → ℕ} (hr : ComputableInPolyTime r input encUnary)
    (ha : ComputableInPolyTime a input encUnary) :
    ComputableInPolyTime (fun x ↦ bitsOf (r x) (a x)) input (encList encNat) := by
  have hdm : ComputableInPolyTime (fun p : α × ℕ ↦ decide (a p.1 / 2 ^ p.2 % 2 = 1))
      (encPair input encUnary) encBool :=
    decide_eq' (binary_mod.comp' ((binary_div.comp' ((toBin (ha.comp' (fst _ _))).prod
      (binary_two_pow.comp' (snd _ _)))).prod (const 2))) (const 1)
  have hbit : ComputableInPolyTime (fun p : α × ℕ ↦ (a p.1).testBit p.2)
      (encPair input encUnary) encBool :=
    hdm.of_enc_eq fun p ↦ by rw [Nat.testBit_eq_decide_div_mod_eq]
  exact mapWithInput (range.comp' hr) (ite' hbit (const 1) (const 0))

/-- `BHJK25.RS.noZeroDiv`, with the number `q` of elements given. -/
def noZeroDivQ (q : ℕ) (fl : List ℕ) : Bool :=
  (List.range q).all fun a ↦ (List.range q).all fun b ↦
    a == 0 || b == 0 ||
      (Cslib.GaloisRingArith.mul 1 fl (bitsOf fl.length a) (bitsOf fl.length b)).any (· != 0)

theorem irrPoly_eq (r : ℕ) : irrPoly r =
    (((List.range (2 ^ r)).map (bitsOf r)).find? (noZeroDivQ (2 ^ r))).getD
      (List.replicate r 0) := by
  unfold irrPoly
  congr 1
  refine List.find?_congr fun fl hfl ↦ ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hfl
  change noZeroDivQ (2 ^ (bitsOf r a).length) (bitsOf r a) = _
  rw [FieldAux.length_bitsOf]

theorem noZeroDivQ_polytime {q : α → ℕ} {fl : α → List ℕ}
    (hq : ComputableInPolyTime q input encUnary)
    (hfl : ComputableInPolyTime fl input (encList encNat)) :
    ComputableInPolyTime (fun x ↦ noZeroDivQ (q x) (fl x)) input encBool := by
  have hx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).comp' (fst _ _)
  have hfl2 := hfl.comp' hx
  have hlen := (length_list encNat).comp' hfl2
  have ha : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (snd _ _).comp' (fst _ _)
  have hb : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.2)
      (encPair (encPair input encUnary) encUnary) encUnary := snd _ _
  have hmul := Cslib.GaloisRingArith.computableInPolyTime_mul (const 1) hfl2
    (bitsOf_polytime hlen ha) (bitsOf_polytime hlen hb)
  have hany := anyWithInput (test := fun _ (c : ℕ) ↦ c != 0) hmul
    (bne (snd _ _) (const 0))
  have htest : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2 == 0 || p.2 == 0 ||
      (Cslib.GaloisRingArith.mul 1 (fl p.1.1) (bitsOf (fl p.1.1).length p.1.2)
        (bitsOf (fl p.1.1).length p.2)).any (· != 0))
      (encPair (encPair input encUnary) encUnary) encBool :=
    bool_or.comp' ((bool_or.comp' ((beq ha (const 0)).prod (beq hb (const 0)))).prod hany)
  exact allWithInput (range.comp' hq) (allWithInput (range.comp' (hq.comp' (fst _ _))) htest)

theorem elts_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) (hnu : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ (List.range (2 ^ rbits (T a) (n a))).map
      (bitsOf (rbits (T a) (n a)))) input (encList (encList encNat)) :=
  mapWithInput (range.comp' (fieldSize_polytime hT hn hnu))
    (bitsOf_polytime ((rbits_polytime hT hn).comp' (fst _ _)) (snd _ _))

theorem irrPoly_polytime {T n : α → ℕ} (hT : ComputableInPolyTime T input encUnary)
    (hn : ComputableInPolyTime n input encNat) (hnu : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ irrPoly (rbits (T a) (n a))) input (encList encNat) := by
  have hfind := findWithInput (test := fun a fl ↦ noZeroDivQ (2 ^ rbits (T a) (n a)) fl)
    (elts_polytime hT hn hnu)
    (noZeroDivQ_polytime ((fieldSize_polytime hT hn hnu).comp' (fst _ _)) (snd _ _))
  have h := (optionGetD (encList encNat)).comp' (hfind.prod
    (replicate (rbits_polytime hT hn) (const (encOut := encNat) 0)))
  exact h.of_enc_eq fun a ↦ by rw [irrPoly_eq]

/-! ### The data -/

/-- **The data of a run is computed in polynomial time.** -/
theorem mkDat_polytime (k : ℕ) {T n : α → ℕ} {w : α → List Bool}
    (hT : ComputableInPolyTime T input encUnary) (hn : ComputableInPolyTime n input encNat)
    (hnu : ComputableInPolyTime n input encUnary) (hw : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun a ↦ mkDat k (T a) (n a) (w a)) input encDat := by
  have hl := ell_polytime k hT hn
  have htup : ComputableInPolyTime (fun a ↦ (mkDat k (T a) (n a) (w a)).toTuple) input encTuple :=
    hnu.prod (hw.prod (hl.prod ((rbits_polytime hT hn).prod
      ((unary_mul' (const (2 * (k - 1))) hl).prod ((mdeg_polytime hT hn hnu).prod
        ((wdeg_polytime hT hn hnu).prod ((irrPoly_polytime hT hn hnu).prod
          (elts_polytime hT hn hnu))))))))
  exact htup.of_enc_eq fun _ ↦ rfl

end BHJK25.RS.AlgAux
