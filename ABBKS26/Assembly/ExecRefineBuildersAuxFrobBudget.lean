module

public import ABBKS26.Assembly.ExecRefineSourcesAuxBuilders

/-! A binary, fuel-independent bit budget with whole-level storage accounting. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobBudget

open Common _root_.ABBKS26.Tree Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime

private theorem points_size (x : Input) :
    (encPoints x.points).length ≤ (encInput x).length := by
  change _ ≤ (Encoding.frame (Encoding.encNat x.k) ++
    (Encoding.frame (Encoding.encRat x.wmin) ++
      (Encoding.frame (Encoding.encRat x.Δ) ++
        (Encoding.frame (Encoding.encRat x.δ) ++ encPoints x.points)))).length
  simp only [List.length_append]
  omega

private theorem count_size (x : Input) : x.points.length ≤ (encInput x).length := by
  exact (Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) x.points).trans
    (points_size x)

private theorem index_bound (n L : ℕ) (hn : n ≤ L) : indexBits n ≤ (L + 2) ^ 3 := by
  have hlog := Nat.log2_le_self n
  have hn2 := Nat.mul_self_le_mul_self hn
  unfold indexBits
  calc
    _ ≤ n * (2 * (n + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ (L + 2) ^ 3 := by nlinarith

private theorem candidate_bound (n k L : ℕ) (hk : 1 ≤ k) (hn : n ≤ L) :
    2 * candidateBits n k ((L + 2) ^ 20) + 1 ≤ k * (L + 2) ^ 25 := by
  let z := L + 2
  have hz : 2 ≤ z := by omega
  have hi : indexBits n ≤ z ^ 20 := (index_bound n L hn).trans
    (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hb : 1 ≤ z ^ 20 := one_le_pow₀ (by omega)
  have hsmall : 2 * candidateBits n k (z ^ 20) + 1 ≤ 21 * k * z ^ 20 := by
    unfold candidateBits
    nlinarith [Nat.mul_le_mul_left k hi, Nat.mul_le_mul_left k hb]
  have h5 : 21 ≤ z ^ 5 := by
    have h := Nat.pow_le_pow_left hz 5
    norm_num at h
    omega
  calc
    _ ≤ 21 * k * z ^ 20 := hsmall
    _ ≤ k * z ^ 25 := by
      rw [show (25 : ℕ) = 20 + 5 by norm_num, pow_add]
      nlinarith [Nat.mul_le_mul_left (k * z ^ 20) h5]

private theorem branch_storage (b m : ℕ) : (m + 1) * b ^ m ≤ (b + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : b ^ (m + 1) ≤ (b + 1) ^ (m + 1) := Nat.pow_le_pow_left (by omega) _
    have hm := Nat.mul_le_mul_right b ih
    rw [pow_succ] at hp
    rw [pow_succ, pow_succ]
    nlinarith

/-- The branching factor absorbs persistent paths and all parents in one complete level. -/
theorem level_bound (n k b L : ℕ) (hk : 1 ≤ k) (hn : n ≤ L) (hb : 1 ≤ b) :
    levelBits n k b ((L + 2) ^ 20) ≤ (b + 1) ^ (k + 1) * (L + 2) ^ 25 := by
  have hc := candidate_bound n k L hk hn
  have ht : k * b ^ (k - 1) ≤ (b + 1) ^ (k + 1) := by
    have hh := branch_storage b (k - 1)
    rw [Nat.sub_add_cancel hk] at hh
    exact hh.trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold levelBits
  calc
    _ ≤ b ^ (k - 1) * (k * (L + 2) ^ 25) := Nat.mul_le_mul_left _ hc
    _ ≤ (b + 1) ^ (k + 1) * (L + 2) ^ 25 := by
      simpa only [Nat.mul_assoc, Nat.mul_comm k] using Nat.mul_le_mul_right _ ht


def bits (x : Input) : ℕ := ((encInput x).length + 2) ^ 20


theorem storage (x : Input) (hx : Valid x) :
    levelBits x.points.length x.k
      (branchCap .centered x.k (Schedule.params .centered x.wmin x.k)) (bits x) ≤
        need .centered x := by
  have hk := hx.2.2.2.1
  have hn := count_size x
  have hpow : ((encInput x).length + 2) ^ 25 ≤ ((encInput x).length + 2) ^ 100 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  by_cases hsmall : x.k ≤ 1
  · have heq : x.k = 1 := by omega
    have hc := candidate_bound x.points.length x.k (encInput x).length hk hn
    rw [need, ite_eq_left hsmall]
    simp only [levelBits, heq, Nat.sub_self, pow_zero, one_mul, bits]
    apply le_trans _ hpow
    simpa only [heq, one_mul] using hc
  · let b := branchCap .centered x.k (Schedule.params .centered x.wmin x.k)
    have hl := level_bound x.points.length x.k b (encInput x).length hk hn
      (le_max_left _ _)
    have hs : (b + 1) ^ (x.k + 1) ≤
        localBudget .centered x.k x.points.length (dim x.points)
          (Schedule.params .centered x.wmin x.k) := by
      unfold localBudget
      simp only [ite_true, Nat.mul_one]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    have hm := Nat.mul_le_mul hs hpow
    have hledger : 1 ≤ Schedule.ledger .centered x.wmin x.k + 2 := by omega
    have hledger' := Nat.mul_le_mul_right
      (localBudget .centered x.k x.points.length (dim x.points)
        (Schedule.params .centered x.wmin x.k)) hledger
    have hall := Nat.mul_le_mul_right (((encInput x).length + 2) ^ 100) hledger'
    rw [need, ite_eq_right hsmall]
    change levelBits _ _ b (((encInput x).length + 2) ^ 20) ≤ _
    exact hl.trans (hm.trans (by simpa only [one_mul] using hall))


end ABBKS26.Assembly.Exec.RefineSynth.FrobBudget
