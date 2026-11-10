module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobBudget

/-! Whole-level accounting for a scan budget including a canonical schedule ledger. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobStorage

open Common _root_.ABBKS26.Tree Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime

theorem levelBits_mono (n k b : ℕ) {u v : ℕ} (h : u ≤ v) :
    levelBits n k b u ≤ levelBits n k b v := by
  unfold levelBits candidateBits
  gcongr

theorem levelBits_scale (n k b u m : ℕ) (hm : 1 ≤ m) :
    levelBits n k b (m * u) ≤ m * levelBits n k b u := by
  have hc : 2 * candidateBits n k (m * u) + 1 ≤
      m * (2 * candidateBits n k u + 1) := by
    have hh := Nat.mul_le_mul_left (4 * (k * (2 * indexBits n + 1)) + 2 * k + 3) hm
    unfold candidateBits
    nlinarith only [hh]
  unfold levelBits
  simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left (b ^ (k - 1)) hc

/-- A larger sample polynomial still fits the frozen exponent `100` in `need`. -/
theorem level_bound (n k b L : ℕ) (hk : 1 ≤ k) (hn : n ≤ L) (hb : 1 ≤ b) :
    levelBits n k b ((L + 2) ^ 40) ≤ (b + 1) ^ (k + 1) * (L + 2) ^ 75 := by
  let z := L + 2
  have hz : 2 ≤ z := by omega
  have hn' : n ≤ z ^ 2 := hn.trans (by dsimp only [z]; nlinarith)
  have hsmall : z ^ 40 ≤ (z ^ 2 + 2) ^ 20 := by
    rw [show (40 : ℕ) = 2 * 20 by norm_num, pow_mul]
    exact Nat.pow_le_pow_left (by omega) _
  have hkey : z ^ 2 + 2 ≤ z ^ 3 := by
    have hh := Nat.mul_le_mul_left (z ^ 2) hz
    have hsq : 4 ≤ z ^ 2 := (by norm_num : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_left hz 2
    rw [pow_succ]
    nlinarith only [hh, hsq]
  have h75 : (z ^ 2 + 2) ^ 25 ≤ z ^ 75 := by
    rw [show (75 : ℕ) = 3 * 25 by norm_num, pow_mul]
    exact Nat.pow_le_pow_left hkey _
  exact (levelBits_mono n k b hsmall).trans
    ((FrobBudget.level_bound n k b (z ^ 2) hk hn' hb).trans
      (Nat.mul_le_mul_left _ h75))

noncomputable def bits (x : Input) : ℕ :=
  if x.k ≤ 1 then FrobBudget.bits x else
    (Schedule.ledger .centered x.wmin x.k + 2) * ((encInput x).length + 2) ^ 40

theorem storage (x : Input) (hx : Valid x) :
    levelBits x.points.length x.k
      (branchCap .centered x.k (Schedule.params .centered x.wmin x.k)) (bits x) ≤
        need .centered x := by
  by_cases hk : x.k ≤ 1
  · simpa only [bits, ite_eq_left hk] using FrobBudget.storage x hx
  · let b := branchCap .centered x.k (Schedule.params .centered x.wmin x.k)
    let L := (encInput x).length
    let m := Schedule.ledger .centered x.wmin x.k + 2
    have hn : x.points.length ≤ L := by
      have hcount := Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) x.points
      have hp : (encPoints x.points).length ≤ (encInput x).length := by
        change _ ≤ (Encoding.frame (Encoding.encNat x.k) ++
          (Encoding.frame (Encoding.encRat x.wmin) ++
            (Encoding.frame (Encoding.encRat x.Δ) ++
              (Encoding.frame (Encoding.encRat x.δ) ++ encPoints x.points)))).length
        simp only [List.length_append]
        omega
      exact hcount.trans hp
    have hl := level_bound x.points.length x.k b L hx.2.2.2.1 hn (le_max_left _ _)
    have hbudget : (b + 1) ^ (x.k + 1) ≤
        localBudget .centered x.k x.points.length (dim x.points)
          (Schedule.params .centered x.wmin x.k) := by
      unfold localBudget
      simp only [ite_true, Nat.mul_one]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hpoly : (L + 2) ^ 75 ≤ (L + 2) ^ 100 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    have hlevel := (levelBits_scale x.points.length x.k b ((L + 2) ^ 40) m
      (by dsimp only [m]; omega)).trans (Nat.mul_le_mul_left m hl)
    rw [bits, ite_eq_right hk, need, ite_eq_right hk]
    exact hlevel.trans (by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left m (Nat.mul_le_mul hbudget hpoly))

/-- This is a pure arithmetic statement about the canonical schedule and its encoding.
It does not quantify over mixture models or the frame implementation. -/
def CanonicalEnvelope (lim : Args → ℕ) : Prop :=
  ∀ x, Valid x → ∀ fuel h, h < x.k - 1 → ∀ N,
    lim (args x.k (Schedule.params .centered x.wmin x.k) (inputPoints x) h N, fuel) ≤
      (Schedule.ledger .centered x.wmin x.k + 2) * ((encInput x).length + 2) ^ 40

/-- The canonical encoding bound is the only remaining premise for the entire budget,
including all parents, persistent paths, and the binary local evaluator. -/
noncomputable def budget (lim : Args → ℕ) (hlim : ComputableInPolyTime lim encArgs encNat)
    (he : CanonicalEnvelope lim) : Budget .centered where
  limit := lim
  bits := bits
  polytime := hlim
  envelope x fuel hx _ h hh N := by
    have hk : ¬x.k ≤ 1 := by omega
    simpa only [bits, ite_eq_right hk] using he x hx fuel h hh N
  storage := storage

end ABBKS26.Assembly.Exec.RefineSynth.FrobStorage
