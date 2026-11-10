module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecInput
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobRound
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobEncoding

/-! Bounded dyadic squares for the spectral statistic factor. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecSquare

open Common _root_.ABBKS26.Tree Sources Builders Matrix
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def run (d p b : ℕ) (v : Vector) : StatisticL :=
  (FrameAux.Features.table d d fun i j ↦
    FrobRound.entry p b 1 (v.getD i 0) * FrobRound.entry p b 1 (v.getD j 0),
    List.replicate d 0, 0)

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d p b : α → ℕ} {v : α → Vector}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (hv : ComputableInPolyTime v enc encVector) :
    ComputableInPolyTime (fun a ↦ run (d a) (p a) (b a) (v a))
      enc encStatistic := by
  unfold run
  apply ComputableInPolyTime.prod
  · apply FrameAux.Features.table_polytime hd hd
    have hbase := (fst enc encUnary).comp (fst _ encUnary)
    apply rat_mul'
    · exact FrobRound.entry_polytime (hp.comp hbase) (hb.comp hbase) (const 1)
        (listGetDWithInput (hv.comp hbase) ((snd _ _).comp (fst _ _)) 0)
    · exact FrobRound.entry_polytime (hp.comp hbase) (hb.comp hbase) (const 1)
        (listGetDWithInput (hv.comp hbase) (snd _ _) 0)
  · exact (replicate hd (const 0)).prod (const 0)

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

theorem coefficient_bits (p b : ℕ) (v : Vector) (i j : ℕ) :
    (encRat (FrobRound.entry p b 1 (v.getD i 0) *
      FrobRound.entry p b 1 (v.getD j 0))).length ≤ 12 * (b + p) + 18 := by
  have hi := FrobSize.of_small (FrobRound.entry_small p b 1 (v.getD i 0))
  have hj := FrobSize.of_small (FrobRound.entry_small p b 1 (v.getD j 0))
  have hh := (hi.mul hj).bits
  omega

/-- Squaring after vector rounding retains the square form and a coefficient-bit ledger
that is independent of the input vector, solver output, and external fuel. -/
theorem encoding_bound (d p b : ℕ) (v : Vector) :
    (encStatistic (run d p b v)).length ≤
      2 * (d * (2 * (d * (24 * (b + p) + 37)) + 1)) +
        2 * (d * (2 * (encRat 0).length + 1)) + (encRat 0).length + 2 := by
  have hrow (i : ℕ) : (encVector ((List.range d).map fun j ↦
      FrobRound.entry p b 1 (v.getD i 0) * FrobRound.entry p b 1 (v.getD j 0))).length ≤
        d * (24 * (b + p) + 37) := by
    apply (vector_bits _ (12 * (b + p) + 18) ?_).trans_eq
    · simp only [List.length_map, List.length_range]
      ring
    · intro a ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      exact coefficient_bits p b v i j
  have hmat : (encMatrix (run d p b v).1).length ≤
      d * (2 * (d * (24 * (b + p) + 37)) + 1) := by
    simp only [run, FrameAux.Features.table, encMatrix, length_encList]
    calc
      _ ≤ ((List.range d).map fun _ ↦
          2 * (d * (24 * (b + p) + 37)) + 1).sum := by
        simp only [List.map_map]
        apply List.sum_le_sum
        intro i hi
        simpa only [encVector, length_encList, Function.comp_apply] using
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hrow i)) 1
      _ = _ := by simp
  have hv : (encVector (List.replicate d 0)).length ≤
      d * (2 * (encRat 0).length + 1) := by
    apply (vector_bits _ (encRat 0).length ?_).trans_eq
    · rw [List.length_replicate]
    · intro a ha
      rw [(List.mem_replicate.mp ha).2]
  change (encPair encMatrix (encPair encVector encRat) (run d p b v)).length ≤ _
  rw [length_encPair, length_encPair]
  change 2 * (encMatrix (run d p b v).1).length + 1 +
    (2 * (encVector (List.replicate d 0)).length + 1 + (encRat 0).length) ≤ _
  omega

theorem encoding_envelope (d p b z : ℕ) (v : Vector)
    (hz : 2 ≤ z) (hd : d ≤ z) (hpb : b + p + 1 ≤ z ^ 4) :
    (encStatistic (run d p b v)).length ≤ 200 * z ^ 6 := by
  have hzero : (encRat 0).length ≤ 6 := by
    simpa using SoS.PolyTime.length_encRat_le_of_small (SoS.PolyTime.small_zero 0 0)
  have hZ : 1 ≤ z ^ 4 := one_le_pow₀ (by omega)
  have hcoeff : 24 * (b + p) + 37 ≤ 37 * z ^ 4 := by omega
  have hsimple : (encStatistic (run d p b v)).length ≤
      4 * d ^ 2 * (24 * (b + p) + 37) + 28 * d + 8 := by
    have hb := encoding_bound d p b v
    nlinarith only [hb, hzero, Nat.mul_le_mul_left (4 * d) hzero]
  have hz6 : 1 ≤ z ^ 6 := one_le_pow₀ (by omega)
  have hz16 : z ≤ z ^ 6 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega) (by norm_num : 1 ≤ 6)
  calc
    _ ≤ 4 * d ^ 2 * (24 * (b + p) + 37) + 28 * d + 8 := hsimple
    _ ≤ 4 * z ^ 2 * (37 * z ^ 4) + 28 * z + 8 := by gcongr
    _ ≤ 200 * z ^ 6 := by nlinarith only [hz6, hz16]

/-- The existing reserve pays for all parents and the full level of a spectral block too. -/
noncomputable def budget : Budget .centered :=
  FrobStorage.budget FrobScan.limit FrobScan.limit_polytime FrobEncoding.canonical_envelope

/-- The local limit includes the statistic, depth, arbitrary parent indices, and all
three window endpoints. It does not charge an intermediate solver's coefficient bits. -/
theorem edge_envelope (a : Args) (p b : ℕ) (v : Vector) (t lo hi : ℚ)
    (hpb : b + p + 1 ≤ FrobScan.key a ^ 4)
    (ht : FrobSize.RatBound (FrobScan.key a ^ 4) t)
    (hlo : FrobSize.RatBound (FrobScan.key a ^ 4) lo)
    (hhi : FrobSize.RatBound (FrobScan.key a ^ 4) hi) :
    (encEdge (pairEdgeL .centered a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (run a.1.1 p b v) (t, lo, hi))).length ≤ FrobScan.limit a := by
  let z := FrobScan.key a
  have hz64 : 64 ≤ z := (FrobScan.key_bounds a).1
  have hz : 2 ≤ z := by omega
  have hd : a.1.1 ≤ z := (FrobScan.key_bounds a).2.1
  have hq := encoding_envelope a.1.1 p b z v hz hd hpb
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
  have hsmall : (encEdge (pairEdgeL .centered a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (run a.1.1 p b v) (t, lo, hi))).length ≤ 2048 * z ^ 6 := by
    simp only [encStatistic, length_encPair] at hq
    have hzero : (encNat 0).length = 0 := rfl
    change (encPair encNat (encPair encIndices (encPair encStatistic
      (encPair encNat (encPair encRat (encPair encRat encRat)))))
        (pairEdgeL .centered a.1.2.2.2.2.1 a.1.2.2.2.2.2
          (run a.1.1 p b v) (t, lo, hi))).length ≤ _
    simp only [pairEdgeL, length_encPair, hzero]
    change _ ≤ 6 * z ^ 4 + 6 at ht' hlo' hhi'
    omega
  have hc : 2048 ≤ z ^ 2 := by
    have hb := Nat.pow_le_pow_left hz64 2
    norm_num at hb
    omega
  exact hsmall.trans ((Nat.mul_le_mul_right _ hc).trans (by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by norm_num : 2 + 6 ≤ 20)))

noncomputable section

theorem decoded (d p b : ℕ) (v : Vector) : statisticOf d (run d p b v) =
    ⟨vecMulVec (fun i ↦ FrobRound.entry p b 1 (v.getD i.val 0))
      (fun i ↦ FrobRound.entry p b 1 (v.getD i.val 0)), 0, 0⟩ := by
  change (⟨matrixOf d (run d p b v).1, vectorOf d (run d p b v).2.1,
    (run d p b v).2.2⟩ : Statistic d) = _
  congr 1
  · funext i j
    simp only [run, matrixOf, FrameAux.Features.table]
    rw [FrameAux.Linear.getD_map_range _ _ i.isLt,
      FrameAux.Linear.getD_map_range _ _ j.isLt]
    rfl
  · funext i
    simp [run, vectorOf]

/-- Scale validity is uniform over every squared direction and every positive fixed window. -/
theorem scaleValid {n k d : ℕ} (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (ps : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (h : ℕ) (hh : h < k - 1)
    (P : Finset (Fin n)) (I : Finset (Fin k)) (v : Fin d → ℚ) (t : ℚ) (ht : 0 < t) :
    ScaleValid M I (ps h) (pairEdge .centered h P ⟨vecMulVec v v, 0, 0⟩
      (t, t / (ps h).K ^ 2, t * (ps h).K ^ 2)) := by
  obtain ⟨_, hcen, _, _, _, _, _, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨_, _, _, _, hφ, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hready h hh
  obtain ⟨hmass, hK, _⟩ := hm
  have hφ1 : ((ps h).straddle : ℝ) ≤ 1 :=
    ((hparams h (by omega)).2.2.2.2.2.2 hh).2.2.1.trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hK1 : (1 : ℚ) ≤ (ps h).K := by
    apply le_trans _ hK
    rw [le_div_iff₀ hφ]
    have hφQ : (ps h).straddle ≤ 1 := by exact_mod_cast hφ1
    linarith only [hφQ]
  have hKsq : (1 : ℚ) ≤ (ps h).K ^ 2 := one_le_pow₀ hK1
  refine ⟨div_le_self ht.le hKsq, le_mul_of_one_le_right ht.le hKsq,
    ?_, hK, hcen, ht, rfl, rfl, v, ?_⟩
  · rw [hmass]
    norm_num
  · intro y
    simp [pairEdge, Statistic.evalQ, vecMulVec_mulVec, dotProduct_smul,
      pow_two, dotProduct_comm]

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecSquare
