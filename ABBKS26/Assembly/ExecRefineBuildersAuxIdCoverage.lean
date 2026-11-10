module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdFuel

/-! Normalization and shell-filtered nets for the executable SUB rounder. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdCoverage

open Common Rounding Matrix _root_.ABBKS26.Tree Sources Builders FrameAux.Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def call (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (a : Args) : RoundArgs :=
  (P a, a.1.1, IdFuel.accuracy a, IdFuel.rank a, B a)

def basis (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args) : Points := roundL R (call P B a, a.2)

def accuracy (a : Args) : ℚ :=
  IdFuel.accuracy a / (8 * (IdFuel.dimension a + 1 : ℚ))

def normalized (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args) : Points := SpecBasis.run a.1.1 (basis P B R a) (accuracy a)

def shell (a : Args) (q : Vector) : Bool :=
  decide ((1 - IdFuel.accuracy a / 2) ^ 2 ≤ dotL a.1.1 q q ∧
    dotL a.1.1 q q ≤ (1 + IdFuel.accuracy a / 2) ^ 2)

def run (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args) : Points := (IdFuel.grid (normalized P B R) a).filter (shell a)

theorem accuracy_polytime : ComputableInPolyTime accuracy encArgs encRat :=
  rat_div' (field_polytime 10) (rat_mul' (const 8)
    (rat_add' (rat_natCast' (unary_to_binary.comp IdFuel.dimension_polytime)) (const 1)))

theorem normalized_polytime (P : Args → SoS.Solver.Problem) (B : Args → ℚ)
    (R : RoundCode) (hR : RoundSpecL R)
    (hP : ComputableInPolyTime P encArgs SoS.Solver.encProblem)
    (hB : ComputableInPolyTime B encArgs encRat) :
    ComputableInPolyTime (normalized P B R) encArgs encPoints := by
  have hc : ComputableInPolyTime (call P B) encArgs encRoundArgs :=
    hP.prod ((show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary
      from by fun_prop).prod ((field_polytime 10).prod (IdFuel.rank_polytime.prod hB)))
  have hb : ComputableInPolyTime (basis P B R) encArgs encPoints :=
    hR.polytime.comp (hc.prod (snd _ _))
  exact SpecBasis.run_polytime_of (by fun_prop) hb accuracy_polytime

theorem shell_polytime : ComputableInPolyTime (fun q : Args × Vector ↦ shell q.1 q.2)
    (encPair encArgs encVector) encBool := by
  have hsq : ComputableInPolyTime (fun q : Args × Vector ↦ dotL q.1.1.1 q.2 q.2)
      (encPair encArgs encVector) encRat := dotL' (by fun_prop) (by fun_prop) (by fun_prop)
  have hβ := rat_div' ((field_polytime 10).comp (fst encArgs encVector)) (const 2)
  have hlo := rat_pow' (rat_sub' (const 1) hβ) (const 2)
  have hhi := rat_pow' (rat_add' (const 1) hβ) (const 2)
  refine (bool_and.comp ((rat_le' hlo hsq).prod (rat_le' hsq hhi))).of_enc_eq fun q ↦ ?_
  congr 1

theorem run_polytime (P : Args → SoS.Solver.Problem) (B : Args → ℚ)
    (R : RoundCode) (hR : RoundSpecL R)
    (hP : ComputableInPolyTime P encArgs SoS.Solver.encProblem)
    (hB : ComputableInPolyTime B encArgs encRat) :
    ComputableInPolyTime (run P B R) encArgs encPoints :=
  filterWithInput (IdFuel.grid_polytime _ (normalized_polytime P B R hR hP hB))
    shell_polytime

theorem length_run (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args) :
    (run P B R a).length ≤
      netBound (IdCov.N_pack (IdFuel.accuracy a) a.1.2.1) (IdFuel.accuracy a) :=
  (List.length_filter_le _ _).trans (IdFuel.grid_length _ a)

noncomputable section

private theorem norm_square (d : ℕ) (q : Vector) :
    (dotL d q q : ℝ) = sqnorm (fun i ↦ (vectorOf d q i : ℝ)) := by
  rw [dotL_eq (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp [sqnorm, dotProduct, vectorOf]

/-- All returned points satisfy the prescribed norm shell, not just the complete point. -/
theorem norms (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args) (hβ : 0 < IdFuel.accuracy a ∧ IdFuel.accuracy a ≤ 1 / 100)
    (q : Vector) (hq : q ∈ run P B R a) :
    (1 - (IdFuel.accuracy a : ℝ)) ^ 2 ≤ sqnorm (fun i ↦ (vectorOf a.1.1 q i : ℝ)) ∧
      sqnorm (fun i ↦ (vectorOf a.1.1 q i : ℝ)) ≤ (1 + (IdFuel.accuracy a : ℝ)) ^ 2 := by
  have hs := of_decide_eq_true (List.mem_filter.mp hq).2
  change (1 - IdFuel.accuracy a / 2) ^ 2 ≤ dotL a.1.1 q q ∧
    dotL a.1.1 q q ≤ (1 + IdFuel.accuracy a / 2) ^ 2 at hs
  have hsq := norm_square a.1.1 q
  have hlo : (1 - (IdFuel.accuracy a : ℝ) / 2) ^ 2 ≤
      sqnorm (fun i ↦ (vectorOf a.1.1 q i : ℝ)) := by
    rw [← hsq]
    exact_mod_cast hs.1
  have hhi : sqnorm (fun i ↦ (vectorOf a.1.1 q i : ℝ)) ≤
      (1 + (IdFuel.accuracy a : ℝ) / 2) ^ 2 := by
    rw [← hsq]
    exact_mod_cast hs.2
  have hβ0 : (0 : ℝ) < IdFuel.accuracy a := by exact_mod_cast hβ.1
  have hβ1 : (IdFuel.accuracy a : ℝ) ≤ 1 := by
    exact_mod_cast hβ.2.trans (by norm_num : (1 / 100 : ℚ) ≤ 1)
  constructor
  · exact (pow_le_pow_left₀ (by linarith) (by linarith) 2).trans hlo
  · exact hhi.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)

/-- A supplied subspace coverage result transfers to the actual shell-filtered net. -/
theorem covers (P : Args → SoS.Solver.Problem) (B : Args → ℚ) (R : RoundCode)
    (a : Args)
    (hβ : 0 < IdFuel.accuracy a ∧ IdFuel.accuracy a ≤ 1 / 100)
    (hk : a.1.2.1 ≤ a.2)
    (hd : IdCov.N_pack (IdFuel.accuracy a) a.1.2.1 ≤ a.2)
    (hn : netBound (IdCov.N_pack (IdFuel.accuracy a) a.1.2.1) (IdFuel.accuracy a) ≤ a.2)
    (Y : RoundOutput a.1.1) (hbasis : basis P B R a = Y.basis.map List.ofFn)
    (hlen : Y.basis.length ≤ IdCov.N_pack (IdFuel.accuracy a) a.1.2.1)
    (hyRank : Y.proj.rank = Y.basis.length)
    {S : Set (Vec a.1.1)} (hcover : Covers Y.proj S (IdFuel.accuracy a))
    (v : Vec a.1.1) (hv : v ∈ S) :
    ∃ q ∈ run P B R a,
      sqnorm ((fun i ↦ (vectorOf a.1.1 q i : ℝ)) - v) ≤
        (2 * (IdFuel.accuracy a : ℝ)) ^ 2 := by
  let D := IdCov.N_pack (IdFuel.accuracy a) a.1.2.1
  have hr : IdFuel.rank a = a.1.2.1 := min_eq_right hk
  have hdim : IdFuel.dimension a = D := by
    unfold IdFuel.dimension
    rw [hr]
    exact min_eq_right hd
  have hD0 : 0 < D := by
    dsimp only [D, IdCov.N_pack, rankCap]
    unfold greedyCap
    positivity
  obtain ⟨u, hu, huY, hnear⟩ : ∃ u : Vec a.1.1, sqnorm u = 1 ∧
      InRange Y.proj u ∧ sqnorm (v - u) ≤ (IdFuel.accuracy a : ℝ) ^ 2 :=
    hcover v hv
  have hζ : 0 < accuracy a := by
    unfold accuracy
    have hβ0 := hβ.1
    positivity
  have hζβ : (accuracy a : ℝ) ≤ (IdFuel.accuracy a : ℝ) / (8 * D) := by
    simp only [accuracy, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_one, hdim]
    apply div_le_div_of_nonneg_left (by exact_mod_cast hβ.1.le) (by positivity)
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
    linarith only [hDR]
  obtain ⟨q, hq, hqu⟩ := SpecSpan.normalized_covers (IdFuel.accuracy a)
    (accuracy a) (Y.basis.map List.ofFn) (SpecCoverage.stored_gram Y hyRank)
    (by simpa only [List.length_map] using hlen) hD0 hβ hζ hζβ
    (by
      simp only [List.length_map]
      exact (SpecPrepared.grid_fuel D Y.basis.length (IdFuel.accuracy a)
        hlen hD0 hβ).trans hn) u (SpecCoverage.stored_mem Y u huY) hu
  have hqraw : q ∈ IdFuel.grid (normalized P B R) a := by
    unfold IdFuel.grid
    rw [ite_eq_left hβ, normalized, hbasis, hdim]
    rw [List.take_of_length_le (by rwa [SpecBasis.length_run, List.length_map])]
    simpa only [IdFuel.mesh, hdim, RoundProgram.input, call] using hq
  have hβR : (0 : ℝ) < IdFuel.accuracy a := by exact_mod_cast hβ.1
  have hβ1 : (IdFuel.accuracy a : ℝ) ≤ 1 := by
    exact_mod_cast hβ.2.trans (by norm_num : (1 / 100 : ℚ) ≤ 1)
  have hunorm : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin a.1.1))‖ = 1 := by
    have he := CompleteAux.norm_sq u
    rw [hu] at he
    nlinarith only [he, norm_nonneg (WithLp.toLp 2 u)]
  have hnorm := (abs_norm_sub_norm_le
    (WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ))) (WithLp.toLp 2 u)).trans hqu
  rw [hunorm, abs_le] at hnorm
  have hqshell : shell a q = true := by
    unfold shell
    apply decide_eq_true
    have he := CompleteAux.norm_sq (fun c ↦ (vectorOf a.1.1 q c : ℝ))
    have hlo : (1 - (IdFuel.accuracy a : ℝ) / 2) ^ 2 ≤
        sqnorm (fun c ↦ (vectorOf a.1.1 q c : ℝ)) := by
      rw [← he]
      exact pow_le_pow_left₀ (by linarith) (by linarith only [hnorm.1, hβR]) 2
    have hhi : sqnorm (fun c ↦ (vectorOf a.1.1 q c : ℝ)) ≤
        (1 + (IdFuel.accuracy a : ℝ) / 2) ^ 2 := by
      rw [← he]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith only [hnorm.2, hβR]) 2
    rw [← norm_square] at hlo hhi
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  have huv : ‖WithLp.toLp 2 u - WithLp.toLp 2 v‖ ≤ (IdFuel.accuracy a : ℝ) := by
    have he := CompleteAux.norm_sq (v - u)
    change sqnorm (v - u) ≤ (IdFuel.accuracy a : ℝ) ^ 2 at hnear
    have hn' : ‖WithLp.toLp 2 (v - u)‖ ≤ (IdFuel.accuracy a : ℝ) := by
      nlinarith only [he, hnear, norm_nonneg (WithLp.toLp 2 (v - u)), hβR]
    simpa only [WithLp.toLp_sub, norm_sub_rev] using hn'
  refine ⟨q, List.mem_filter.mpr ⟨hqraw, hqshell⟩, ?_⟩
  rw [← CompleteAux.norm_sq, WithLp.toLp_sub]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have he := norm_add_le
    (WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ)) - WithLp.toLp 2 u)
    (WithLp.toLp 2 u - WithLp.toLp 2 v)
  rw [sub_add_sub_cancel] at he
  linarith only [he, hqu, huv, hβR]

end

end ABBKS26.Assembly.Exec.RefineSynth.IdCoverage
