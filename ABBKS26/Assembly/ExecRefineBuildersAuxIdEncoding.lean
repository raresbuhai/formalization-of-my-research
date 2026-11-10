module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobScan
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdStorage
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdSchedule

/-! Encoding the canonical schedule within its arithmetic reserve. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdEncoding

open Common _root_.ABBKS26.Tree Sources Builders
open Turing.MultiTapeTM

private theorem input_sizes (x : Input) :
    let L := (encInput x).length
    dim x.points ≤ L ∧ x.points.length ≤ L ∧ (Encoding.encRat x.wmin).length ≤ L ∧
      (encNat x.k).length ≤ L ∧ (encPoints x.points).length ≤ L := by
  have hL : (encInput x).length = 2 * (encNat x.k).length + 1 +
      (2 * (Encoding.encRat x.wmin).length + 1 +
        (2 * (Encoding.encRat x.Δ).length + 1 +
          (2 * (Encoding.encRat x.δ).length + 1 + (encPoints x.points).length))) := by
    change (encPair encNat (encPair Encoding.encRat
      (encPair Encoding.encRat (encPair Encoding.encRat encPoints)))
        (x.k, x.wmin, x.Δ, x.δ, x.points)).length = _
    simp only [length_encPair]
  have hn := Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) x.points
  have hd : dim x.points ≤ (encPoints x.points).length := by
    cases he : x.points with
    | nil => simp [dim]
    | cons row rows =>
      have hr := Rounding.RawAux.length_count Encoding.encRat row
      have hl := Rounding.RawAux.length_elem (Encoding.encList Encoding.encRat)
        (row :: rows) row (by simp)
      simpa only [dim, he, List.headD_cons, encPoints] using hr.trans hl
  change x.points.length ≤ (encPoints x.points).length at hn
  dsimp only
  omega

private theorem schedule_size (x : Input) (hx : Valid x) (hk : 2 ≤ x.k) :
    (encPoints ((List.range x.k).map fun j ↦
      paramsList (Schedule.params .identical x.wmin x.k j))).length ≤
        4000001 * Schedule.ledgerCore .identical x.wmin x.k ^ 3 *
          ((encInput x).length + 2) ^ 2 := by
  let B := Schedule.ledgerCore .identical x.wmin x.k
  let L := (encInput x).length
  let Y := L + 2
  have hw2 : x.wmin ≤ 1 / 2 := by
    have hkq : (2 : ℚ) ≤ x.k := by exact_mod_cast hk
    nlinarith only [hx.2.2.1, mul_le_mul_of_nonneg_right hkq hx.1.le]
  have hw : 0 < x.wmin ∧ x.wmin ≤ 1 / 2 := ⟨hx.1, hw2⟩
  obtain ⟨hB, hkB⟩ := IdSchedule.ledgerCore_large x.k hw hx.2.2.1
  change 100000000 ≤ B at hB
  change x.k ≤ B at hkB
  have hBY : 1 ≤ B * Y := Nat.mul_pos (by omega) (by dsimp only [Y]; omega)
  have hbL := (input_sizes x).2.2.1
  have hsmall : (Encoding.encRat x.wmin).length + B + 100 ≤ 2 * B * Y := by
    dsimp only [Y, L] at *
    nlinarith only [hbL, hB, Nat.zero_le (B * (encInput x).length)]
  have hrow (j : ℕ) (hj : j < x.k) :
      (encVector (paramsList (Schedule.params .identical x.wmin x.k j))).length ≤
        2000000 * B ^ 2 * Y ^ 2 := by
    have hq := IdSchedule.params_encoding_bound x.k j
      (Encoding.encRat x.wmin).length hw hk hx.2.2.1 hj
        (Schedule.EncodingBounds.of_encoding (le_refl _))
    have hb := Schedule.EncodingBounds.list_bits _ _ hq
    change (encVector (paramsList (Schedule.params .identical x.wmin x.k j))).length ≤
      17 * (12 * (2000 * ((Encoding.encRat x.wmin).length + B + 100) ^ 2) + 13) at hb
    have hs := Nat.pow_le_pow_left hsmall 2
    rw [mul_pow, mul_pow] at hs
    have hBY2 : 1 ≤ B ^ 2 * Y ^ 2 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left hBY 2
    nlinarith only [hb, hs, hBY2]
  have hs : (encPoints ((List.range x.k).map fun j ↦
      paramsList (Schedule.params .identical x.wmin x.k j))).length ≤
        x.k * (2 * (2000000 * B ^ 2 * Y ^ 2) + 1) := by
    apply (length_encList_le (b := 2000000 * B ^ 2 * Y ^ 2) encVector _ ?_).trans_eq (by simp only
      [List.length_map, List.length_range])
    intro row hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact hrow j (List.mem_range.mp hj)
  apply hs.trans
  calc
    _ ≤ B * (2 * (2000000 * B ^ 2 * Y ^ 2) + 1) := Nat.mul_le_mul_right _ hkB
    _ ≤ 4000001 * B ^ 3 * Y ^ 2 := by
      have hBY2 : 1 ≤ B ^ 2 * Y ^ 2 := by
        simpa only [mul_pow] using Nat.pow_le_pow_left hBY 2
      nlinarith only [Nat.mul_le_mul_left B hBY2]

private theorem indices_size {n : ℕ} (N : Finset (Fin n)) (L : ℕ) (hn : n ≤ L) :
    (encIndices (indexList N)).length ≤ 3 * (L + 2) ^ 2 := by
  have hc : (indexList N).length ≤ n := by
    simpa only [indexList, List.length_map, Finset.length_sort, Fintype.card_fin]
      using N.card_le_univ
  have hb : (encIndices (indexList N)).length ≤
      (indexList N).length * (2 * (Nat.log2 n + 1) + 1) := by
    apply length_encList_le
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact length_encNat_le_log2 (Nat.le_of_lt j.isLt)
  have hn' := Nat.log2_le_self n
  have hh := hb.trans (Nat.mul_le_mul_right _ hc)
  have hmul := Nat.mul_le_mul_left n (show 2 * (Nat.log2 n + 1) + 1 ≤ 2 * n + 3 by omega)
  have hsq := Nat.mul_self_le_mul_self hn
  nlinarith only [hh, hmul, hsq, hn]

/-- The canonical block key fits a fixed power of the original input and parameter reserve. -/
theorem key_bound (x : Input) (hx : Valid x) (fuel h : ℕ) (hh : h < x.k - 1)
    (N : Finset (Fin x.points.length)) :
    FrobScan.key (args x.k (Schedule.params .identical x.wmin x.k) (inputPoints x) h N, fuel) ≤
      Schedule.ledgerCore .identical x.wmin x.k ^ 4 * ((encInput x).length + 2) ^ 2 := by
  let B := Schedule.ledgerCore .identical x.wmin x.k
  let L := (encInput x).length
  let Y := L + 2
  let T := B ^ 3 * Y ^ 2
  have hk : 2 ≤ x.k := by omega
  have hw2 : x.wmin ≤ 1 / 2 := by
    have hkq : (2 : ℚ) ≤ x.k := by exact_mod_cast hk
    nlinarith only [hx.2.2.1, mul_le_mul_of_nonneg_right hkq hx.1.le]
  obtain ⟨hB, hkB⟩ := IdSchedule.ledgerCore_large x.k ⟨hx.1, hw2⟩ hx.2.2.1
  change 100000000 ≤ B at hB
  change x.k ≤ B at hkB
  obtain ⟨hd, hn, hw, hkbits, hpts⟩ := input_sizes x
  change dim x.points ≤ L at hd
  change x.points.length ≤ L at hn
  change (encNat x.k).length ≤ L at hkbits
  change (encPoints x.points).length ≤ L at hpts
  have hY : 2 ≤ Y := by dsimp only [Y]; omega
  have hY1 : 1 ≤ Y ^ 2 := one_le_pow₀ (by omega)
  have hB1 : 1 ≤ B ^ 3 := one_le_pow₀ (by omega)
  have hT1 : 1 ≤ T := Nat.mul_pos hB1 hY1
  have hYT : Y ^ 2 ≤ T := Nat.le_mul_of_pos_left _ hB1
  have hBT : B ≤ T := by
    apply le_trans _ (Nat.le_mul_of_pos_right _ hY1)
    exact le_self_pow₀ (by omega) (by norm_num)
  have hLT : L ≤ T := by
    have hLY : L ≤ Y ^ 2 := by dsimp only [Y]; nlinarith
    exact hLY.trans hYT
  have hbits : (encNat h).length ≤ B := by
    have he := length_encNat_le_log2 (le_refl h)
    have hlog := Nat.log2_le_self h
    omega
  have hi := indices_size N L hn
  have hs := schedule_size x hx hk
  change _ ≤ 4000001 * B ^ 3 * Y ^ 2 at hs
  have hsT : (encPoints ((List.range x.k).map fun j ↦
      paramsList (Schedule.params .identical x.wmin x.k j))).length ≤ 4000001 * T := by
    simpa only [T, Nat.mul_assoc] using hs
  have hkey : FrobScan.key (args x.k (Schedule.params .identical x.wmin x.k)
      (inputPoints x) h N, fuel) ≤ 10000000 * T := by
    simp only [FrobScan.key, args, encBlockArgs, length_encPair, encUnary_apply,
      List.length_replicate]
    rw [points_input x hx]
    have hdT := hd.trans hLT
    have hkT := hkbits.trans hLT
    have hpT := hpts.trans hLT
    have hhT := hbits.trans hBT
    have hiT := hi.trans (Nat.mul_le_mul_left 3 hYT)
    omega
  apply hkey.trans
  calc
    _ ≤ B * T := Nat.mul_le_mul_right _ (by omega : 10000000 ≤ B)
    _ = _ := by dsimp only [T, Y, L, B]; ring

/-- The encoding reserve pays for the complete canonical scan at every parent subset. -/
theorem canonical_envelope : IdStorage.CanonicalEnvelope FrobScan.limit := by
  intro x hx fuel h hh N
  let B := Schedule.ledgerCore .identical x.wmin x.k
  have hk := key_bound x hx fuel h hh N
  have hp := Nat.pow_le_pow_left hk 20
  have hb : B ^ 80 ≤ Schedule.ledger .identical x.wmin x.k + 2 := by
    apply le_trans _ (Nat.le_add_right _ 2)
    change B ^ 80 ≤ 2 ^ (B + Rounding.solverConstant + 2) ^ 100
    apply le_trans _ (Nat.lt_two_pow_self (n :=
      (B + Rounding.solverConstant + 2) ^ 100)).le
    exact (Nat.pow_le_pow_left (by omega : B ≤ B + Rounding.solverConstant + 2) 80).trans
      (Nat.pow_le_pow_right (by omega) (by norm_num))
  apply le_trans hp
  rw [mul_pow, ← pow_mul, ← pow_mul]
  exact Nat.mul_le_mul_right _ hb

end ABBKS26.Assembly.Exec.RefineSynth.IdEncoding
