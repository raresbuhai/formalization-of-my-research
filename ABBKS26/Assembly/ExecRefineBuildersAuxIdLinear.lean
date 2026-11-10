module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdWindows

/-! Bounded dyadic linear statistics with their complete edge-encoding ledger. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdLinear

open Common _root_.ABBKS26.Tree Sources Builders Matrix
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Rounding retains the affine part and fixes the quadratic part to zero. -/
def run (d p b : ℕ) (q : StatisticL) : StatisticL :=
  (List.replicate d (List.replicate d 0),
    (List.range d).map (fun i ↦ FrobRound.entry p b 1 (q.2.1.getD i 0)),
    FrobRound.entry p b 1 q.2.2)

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d p b : α → ℕ} {q : α → StatisticL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (hq : ComputableInPolyTime q enc encStatistic) :
    ComputableInPolyTime (fun a ↦ run (d a) (p a) (b a) (q a)) enc encStatistic := by
  apply ComputableInPolyTime.prod
  · exact replicate hd (replicate hd (const 0))
  · apply ComputableInPolyTime.prod
    · apply mapWithInput (range.comp hd)
      exact FrobRound.entry_polytime (hp.comp (fst _ _)) (hb.comp (fst _ _)) (const 1)
        (listGetDWithInput (((fst _ _).comp ((snd _ _).comp hq)).comp (fst _ _))
          (snd _ _) 0)
    · exact FrobRound.entry_polytime hp hb (const 1) ((snd _ _).comp ((snd _ _).comp hq))

private theorem vector_bits (v : Vector) (B : ℕ)
    (hv : ∀ a ∈ v, (encRat a).length ≤ B) :
    (encVector v).length ≤ v.length * (2 * B + 1) := by
  induction v with
  | nil => simp [encVector]
  | cons a v ih =>
    have ha := hv a List.mem_cons_self
    have ht := ih (fun x hx ↦ hv x (List.mem_cons_of_mem _ hx))
    simp only [encVector, length_encList, List.map_cons, List.sum_cons] at *
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem encoding_envelope (d p b z : ℕ) (q : StatisticL)
    (hz : 2 ≤ z) (hd : d ≤ z) (hpb : b + p + 1 ≤ z ^ 4) :
    (encStatistic (run d p b q)).length ≤ 200 * z ^ 6 := by
  have hzero : (encRat 0).length ≤ 6 := by
    simpa using SoS.PolyTime.length_encRat_le_of_small (SoS.PolyTime.small_zero 0 0)
  have hrow : (encVector (List.replicate d 0)).length ≤ 13 * d := by
    apply (vector_bits _ 6 ?_).trans_eq (by simp; omega)
    intro a ha
    rw [(List.mem_replicate.mp ha).2]
    exact hzero
  have hmat : (encMatrix (List.replicate d (List.replicate d 0))).length ≤
      d * (26 * d + 1) := by
    simp only [encMatrix, length_encList, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    apply Nat.mul_le_mul_left d
    have hr : d * (2 * (encRat 0).length + 1) ≤ 13 * d := by
      simpa only [encVector, length_encList, List.map_replicate,
        List.sum_replicate, smul_eq_mul] using hrow
    omega
  have hv : (encVector (run d p b q).2.1).length ≤ d * (6 * (b + p) + 13) := by
    apply (vector_bits _ (3 * (b + p) + 6) ?_).trans_eq
    · simp only [run, List.length_map, List.length_range]
      ring
    · intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact FrobRound.entry_bits p b 1 _
  have hc := FrobRound.entry_bits p b 1 q.2.2
  have hp : 6 * (b + p) + 13 ≤ 13 * z ^ 4 := by
    have hZ : 1 ≤ z ^ 4 := one_le_pow₀ (by omega)
    omega
  have hsimple : (encStatistic (run d p b q)).length ≤
      52 * d ^ 2 + 2 * d + 2 * d * (6 * (b + p) + 13) +
        3 * (b + p) + 8 := by
    change (encPair encMatrix (encPair encVector encRat) (run d p b q)).length ≤ _
    rw [length_encPair, length_encPair]
    change 2 * (encMatrix (List.replicate d (List.replicate d 0))).length + 1 +
      (2 * (encVector (run d p b q).2.1).length + 1 +
        (encRat (FrobRound.entry p b 1 q.2.2)).length) ≤ _
    nlinarith only [hmat, hv, hc]
  have hz26 : z ^ 2 ≤ z ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz56 : z ^ 5 ≤ z ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz46 : z ^ 4 ≤ z ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz16 : z ≤ z ^ 6 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : 1 ≤ z) (by norm_num : 1 ≤ 6)
  have hz06 : 1 ≤ z ^ 6 := one_le_pow₀ (by omega)
  calc
    _ ≤ 52 * d ^ 2 + 2 * d + 2 * d * (6 * (b + p) + 13) +
        3 * (b + p) + 8 := hsimple
    _ ≤ 52 * z ^ 2 + 2 * z + 2 * z * (13 * z ^ 4) + 3 * z ^ 4 + 8 := by
      gcongr
      omega
    _ ≤ 200 * z ^ 6 := by nlinarith only [hz26, hz56, hz46, hz16, hz06]

theorem edge_envelope (a : Args) (p b : ℕ) (q : StatisticL) (t lo hi : ℚ)
    (hpb : b + p + 1 ≤ FrobScan.key a ^ 4)
    (ht : FrobSize.RatBound (FrobScan.key a ^ 4) t)
    (hlo : FrobSize.RatBound (FrobScan.key a ^ 4) lo)
    (hhi : FrobSize.RatBound (FrobScan.key a ^ 4) hi) :
    (encEdge (pairEdgeL .identical a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (run a.1.1 p b q) (t, lo, hi))).length ≤ FrobScan.limit a := by
  let z := FrobScan.key a
  have hz64 : 64 ≤ z := (FrobScan.key_bounds a).1
  have hz : 2 ≤ z := by omega
  have hq := encoding_envelope a.1.1 p b z q hz (FrobScan.key_bounds a).2.1 hpb
  have hh : (encNat a.1.2.2.2.2.1).length ≤ z :=
    (FrobScan.key_bounds a).2.2.2.2.1
  have hN : (encIndices a.1.2.2.2.2.2).length ≤ z :=
    (FrobScan.key_bounds a).2.2.2.2.2
  have ht' := ht.bits
  have hlo' := hlo.bits
  have hhi' := hhi.bits
  have h46 : z ^ 4 ≤ z ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h16 : z ≤ z ^ 6 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega) (by norm_num : 1 ≤ 6)
  have h6 : 1 ≤ z ^ 6 := one_le_pow₀ (by omega)
  have hsmall : (encEdge (pairEdgeL .identical a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (run a.1.1 p b q) (t, lo, hi))).length ≤ 2048 * z ^ 6 := by
    simp only [encStatistic, length_encPair] at hq
    have htwo : (encNat 2).length = 2 := rfl
    change (encPair encNat (encPair encIndices (encPair encStatistic
      (encPair encNat (encPair encRat (encPair encRat encRat)))))
        (pairEdgeL .identical a.1.2.2.2.2.1 a.1.2.2.2.2.2
          (run a.1.1 p b q) (t, lo, hi))).length ≤ _
    simp only [pairEdgeL, length_encPair, htwo]
    change _ ≤ 6 * z ^ 4 + 6 at ht' hlo' hhi'
    omega
  have hc : 2048 ≤ z ^ 2 := by
    have hb := Nat.pow_le_pow_left hz64 2
    norm_num at hb
    omega
  exact hsmall.trans ((Nat.mul_le_mul_right _ hc).trans (by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by norm_num : 2 + 6 ≤ 20)))

theorem decoded (d p b : ℕ) (q : StatisticL) :
    statisticOf d (run d p b q) =
      ⟨0, fun i ↦ FrobRound.entry p b 1 (q.2.1.getD i.val 0),
        FrobRound.entry p b 1 q.2.2⟩ := by
  change (⟨matrixOf d (run d p b q).1, vectorOf d (run d p b q).2.1,
    (run d p b q).2.2⟩ : Statistic d) = _
  congr 1
  · funext i j
    simp [run, matrixOf]
  · funext i
    exact FrameAux.Linear.getD_map_range _ _ i.isLt

theorem canonical (d p b : ℕ) (q : StatisticL) :
    FramePool.canonical d (run d p b q) = run d p b q := by
  rw [FramePool.canonical_agrees, decoded]
  apply Prod.ext
  · change List.ofFn (fun _ : Fin d ↦ List.ofFn fun _ : Fin d ↦ (0 : ℚ)) = _
    simp only [List.ofFn_const]
    rfl
  · apply Prod.ext
    · change List.ofFn (fun i : Fin d ↦ FrobRound.entry p b 1 (q.2.1.getD i.val 0)) = _
      rw [List.ofFn_eq_map]
      change _ = (List.range d).map (fun i ↦ FrobRound.entry p b 1 (q.2.1.getD i 0))
      rw [← List.map_coe_finRange_eq_range (n := d), List.map_map]
      rfl
    · rfl


end ABBKS26.Assembly.Exec.RefineSynth.IdLinear
