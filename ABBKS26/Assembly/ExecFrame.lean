module

public import ABBKS26.Assembly.ExecFrameAuxSymmetry
public import ABBKS26.Assembly.ExecFrameAuxComponent

/-!
# Effective frame/filter interface

`FrameCode.run` is a P1 implementation on rational lists. Its certificate must cover junk
blocks as well as prepared blocks. The decoder introduces real coefficients only for the
existing analytic contract; the machine stores their rational antecedents.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Matrix
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

abbrev FrameArgs := ℕ × Points × ℚ × ℚ × ℚ
abbrev FrameData := Bool × MatrixL × Vector × MatrixL × List StatisticL × List Bool
abbrev encFrameArgs := encPair encUnary
  (encPair encPoints (encPair encRat (encPair encRat encRat)))
abbrev encFrameData := encPair encBool (encPair encMatrix (encPair encVector
  (encPair encMatrix (encPair (encList encStatistic) (encList encBool)))))

structure FrameCode where
  run : Mode → FrameArgs × ℕ → FrameData

noncomputable def frameOf (d : ℕ) (F : FrameData) : Robust.FrameResult d :=
  ⟨F.1, matrixOf d F.2.1, vectorOf d F.2.2.1, matrixOf d F.2.2.2.1,
    F.2.2.2.2.1.map (fun q ↦
      ⟨(matrixOf d q.1).map (algebraMap ℚ ℝ),
        fun i ↦ (vectorOf d q.2.1 i : ℝ), (q.2.2 : ℝ)⟩), F.2.2.2.2.2⟩

noncomputable def frameProc (F : FrameCode) : Robust.FrameProc :=
  fun d pts mode π R ζ fuel ↦ frameOf d (F.run mode ((d, pts, π, R, ζ), fuel))

structure FrameSpec (F : FrameCode) : Prop where
  polytime : ∀ mode, ComputableInPolyTime (F.run mode)
    (encPair encFrameArgs encUnary) encFrameData
  contract : Robust.FrameContract (frameProc F)
  symmetric : ∀ mode (a : FrameArgs × ℕ) (i : ℕ) (q : StatisticL),
    (F.run mode a).2.2.2.2.1[i]? = some q →
    (F.run mode a).2.2.2.2.2[i]? = some true →
    (statisticOf a.1.1 q).Aᵀ = (statisticOf a.1.1 q).A
  component_bound : FrameAux.Component.Bound (frameProc F)

private theorem frame_resilience {n k d : ℕ} (D : Robust.Reference n k d) (ζ : ℚ)
    (hres : D.Resilient 4 (min (1 / 10 ^ 8) ((ζ : ℝ) ^ 2 / 10 ^ 8))) :
    D.Resilient 4 (1 / 10000) := by
  intro T a j r hr
  apply (hres T a j r hr).trans
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right
      ((min_le_left _ _).trans (by norm_num)) (by positivity)
  · exact pow_nonneg (add_nonneg
      (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _))
      (SoS.coeffNorm1_nonneg _)) r

private theorem frame_pool_valid {n k d : ℕ} (D : Robust.Reference n k d)
    (pts : Points) (π R : ℚ) (history : List Vector)
    (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000)) (hπ : (π : ℝ) ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R)
    (hh : ∀ w ∈ history, FrameProgram.Ready d pts w) (q : StatisticL)
    (hq : (q, true) ∈ FrameProgram.certificatePool d pts π history) :
    ∀ l, Robust.statVariance D.model l (FrameProgram.quadOf d q) ≤
      (20 / (π : ℝ)) ^ 2 := by
  obtain ⟨w, hw, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨q', hq', heq⟩ := List.mem_map.mp hq
  have hqeq : q' = q := congrArg Prod.fst heq
  have hel : FrameProgram.Eligible pts π w := by
    simpa using congrArg Prod.snd heq
  exact FrameProgram.eligible_certificate_valid D pts π R w hrep hD hres hπ
    he (hh w hw) hel q (hqeq ▸ hq')

private theorem frame_pool_far {n k d : ℕ} (D : Robust.Reference n k d)
    (pool : List (StatisticL × Bool)) (passed : Bool)
    (T : Matrix (Fin d) (Fin d) ℚ) (a : Fin d → ℚ)
    (C : Matrix (Fin d) (Fin d) ℚ) (R sb : ℝ) (q : StatisticL)
    (hq : (q, true) ∈ pool) (i j : Fin k)
    (hgap : R ≤ |Robust.statCenter D.model i (FrameProgram.quadOf d q) -
      Robust.statCenter D.model j (FrameProgram.quadOf d q)|)
    (hv : ∀ l, Robust.statVariance D.model l (FrameProgram.quadOf d q) ≤ sb ^ 2) :
    Robust.Far D ⟨passed, T, a, C, pool.map (fun p ↦ FrameProgram.quadOf d p.1),
      pool.map Prod.snd⟩ R sb := by
  obtain ⟨b, hb⟩ := List.mem_iff_get.mp hq
  have hlen : b.val < (pool.map (fun p ↦ FrameProgram.quadOf d p.1)).length := by
    rw [List.length_map]
    exact b.isLt
  refine ⟨⟨b.val, hlen⟩, ?_, i, j, ?_, ?_⟩
  · change (pool.map Prod.snd)[b.val]? = some true
    rw [List.getElem?_map, List.getElem?_eq_getElem b.isLt]
    exact congrArg (fun p ↦ some p.2) hb
  · have hb' : (pool[b.val]).1 = q := congrArg Prod.fst hb
    simpa only [Fin.getElem_fin, List.getElem_map, hb'] using hgap
  · have hb' : (pool[b.val]).1 = q := congrArg Prod.fst hb
    simpa only [Fin.getElem_fin, List.getElem_map, hb'] using hv

private theorem frame_pool_flag (pool : List (StatisticL × Bool))
    (j : ℕ) (hj : j < pool.length) (hf : (pool.map Prod.snd)[j]? = some true) :
    ((pool[j]).1, true) ∈ pool := by
  have hflag : (pool[j]).2 = true := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
      Option.some.injEq] using hf
  rw [← hflag]
  exact List.getElem_mem hj

private theorem rounded_component_bound
    (hcontract : Robust.FrameContract (fun d pts mode π R ζ fuel ↦
      FrameProgram.decode d (FrameProgram.run mode ((d, pts, π, R, ζ), fuel)))) :
    FrameAux.Component.Bound (fun d pts mode π R ζ fuel ↦
      FrameProgram.decode d (FrameProgram.run mode ((d, pts, π, R, ζ), fuel))) := by
  intro n k d M ε w η Δ D ω r ps hp h hh fuel hf P I hI hl hP
  dsimp only
  intro hnf
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let pts := (P.sort (· ≤ ·)).map fun l ↦
    List.ofFn fun i ↦ r ((ω l).1, (ω l).2.2) i
  have hpts : pts = ABBKS26.RefineAux.blockInput
      (fun l i ↦ r ((ω l).1, (ω l).2.2) i) P := by
    dsimp only [pts, ABBKS26.RefineAux.blockInput]
    rw [← P.listMap_orderEmbOfFin_finRange rfl]
    simp only [List.map_map, List.ofFn_eq_map]
    rfl
  have hlen : pts.length = P.card := by simp [pts]
  have hrep : Robust.Represents ref pts := by
    rw [hpts]
    exact ABBKS26.RefineAux.blockInput_represents M ω r P I hI
  have hcompat := hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh P I hI hl hP
  have hres := hp.reference_resilient_at .centered M ε w η Δ D ω r ps P I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .centered M ε w η Δ D ω r ps)) (by decide)
  have hcont := hp.contamination_at .centered M ε w η Δ D ω r ps h (by omega)
    P I hI hl hP
  have hprepared := hp
  obtain ⟨_, hcenter, _, hwR, _, _, _, hη100, _, hg, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, hζ, hζle, _⟩ :=
    hready h hh
  have hηζ := (hparams h (by omega)).2.2.2.2.2.1
  have hres' : ref.Resilient 4
      (min (1 / 10 ^ 8) ((p.frameAccuracy : ℝ) ^ 2 / 10 ^ 8)) := by
    apply ABBKS26.RefineAux.resilient_tolerance_mono ref 4 _ _ hres
    apply le_min
    · linarith only [hη100]
    · exact div_le_div_of_nonneg_right hηζ (by norm_num)
  have he : ref.contamination ≤ min (Robust.maxContamination
      (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ)) (((p.w / 2 : ℚ) : ℝ) / 400) := by
    apply le_min hcompat.1.2.2.2.2.2
    apply hcont.trans
    have hb := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hbR : (p.contamination : ℝ) ≤ (p.w : ℝ) / 800 := by exact_mod_cast hb
    push_cast
    simpa only [div_div, show (2 : ℝ) * 400 = 800 by norm_num] using hbR
  have hmax0 : 0 < Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) := by
    unfold Robust.maxContamination Robust.sigmaSq
    have hw' : (0 : ℝ) < p.w := by exact_mod_cast hw
    push_cast
    positivity
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (SoundAux.good_cluster_pos M ε w η D ω hg hI.choose).trans_le
      ((Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n))
  have hP0 : (0 : ℝ) < P.card := (by positivity : 0 < w * n / 4).trans_le hP
  have hn : 2 / Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) ≤
      pts.length := by
    rw [hlen, div_le_iff₀ hmax0]
    have hfinite : 2 / (P.card : ℝ) ≤ ref.contamination :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hb := (div_le_iff₀ hP0).mp (hfinite.trans (he.trans (min_le_left _ _)))
    linarith only [hb]
  have hfu : (pts.length + d + 2) ^ 100 ≤ fuel := by
    apply le_trans _ hf
    have hc : P.card ≤ n := (Finset.card_le_univ P).trans_eq (Fintype.card_fin n)
    rw [hlen]
    calc
      _ ≤ (n + d + 2) ^ 100 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ localBudget .centered k n d ps := by
        simp only [localBudget, ite_true, mul_one]
        exact Nat.le_mul_of_pos_left _ (by positivity)
  let Y := FrameProgram.decode d
    (FrameProgram.run .centered ((d, pts, p.w / 2, |p.R|, p.frameAccuracy), fuel))
  have hc := hcontract.2 ref pts .centered (p.w / 2) |p.R| p.frameAccuracy fuel
    hrep hcompat.1.1 hres' (by positivity) (by linarith only [hw2]) (abs_nonneg _) hζ
    (fun _ j ↦ hcenter _) he hn hfu
  have hclose : Robust.CloseFrame ref Y (p.w / 2 : ℚ) (|p.R| : ℚ)
      (((p.isotropy / 10000 : ℚ) : ℝ)) := by
    have hb := hc.1.resolve_left hnf
    refine ⟨hb.1, hb.2.trans ?_⟩
    apply pow_le_pow_left₀ (by positivity)
    have hzR : (p.frameAccuracy : ℝ) ≤ ((p.isotropy / 10000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hζle
    linarith only [hzR]
  apply FrameAux.Component.prepared_bound M ε w η Δ D ω r ps hprepared h hh P I hI hl hP
    Y hclose
  let result := FrameProgram.loop d pts (p.w / 2) |p.R| fuel pts.length
    (List.replicate pts.length 1)
  let pool := FrameProgram.certificatePool d pts (p.w / 2) result.2.1
  have hπ' : (((p.w / 2 : ℚ) : ℝ)) ≤ 1 := by
    have hb : p.w / 2 ≤ 1 := by linarith only [hw2]
    exact_mod_cast hb
  have hvalid (q : StatisticL) (hq : (q, true) ∈ pool) :
      ∀ l, Robust.statVariance ref.model l (FrameProgram.quadOf d q) ≤
        (20 / (((p.w / 2 : ℚ) : ℝ))) ^ 2 := by
    exact frame_pool_valid ref pts (p.w / 2) |p.R| result.2.1 hrep hcompat.1.1
      (frame_resilience ref p.frameAccuracy hres') hπ' (he.trans (min_le_left _ _))
      (fun w hw ↦ ((FrameProgram.rounded_loop_bound d pts (p.w / 2) |p.R| fuel
        pts.length (List.replicate pts.length 1)).2 w hw).1) q hq
  obtain ⟨idx, _, _, hloop⟩ := FrameProgram.rounded_loop_invariant ref pts
    (p.w / 2) |p.R| p.frameAccuracy fuel hrep hcompat.1.1 hres'
    (by positivity) (by linarith only [hw2]) (abs_nonneg _) hζ he hn hfu
  rcases hloop with ⟨w, hw, hc, hel, hb⟩ | ⟨hc, _, hpass⟩
  · have hfail := ((FrameProgram.rounded_loop_bound d pts (p.w / 2) |p.R| fuel
        pts.length (List.replicate pts.length 1)).2 w hw).2
    obtain ⟨q, hq, i, j, hgap⟩ := FrameProgram.first_typeB_certificate ref pts idx
      (p.w / 2) |p.R| w hrep (by linarith only [hw2]) (abs_nonneg _) he hc hfail hb
    have hmem : (q, true) ∈ pool := by
      apply List.mem_flatMap.mpr
      refine ⟨w, hw, List.mem_map.mpr ⟨q, hq, ?_⟩⟩
      simp [hel]
    apply (hnf ?_).elim
    rw [FrameProgram.rounded_frame_agrees]
    exact frame_pool_far ref pool _ _ _ _ (|p.R| : ℚ) _ q hmem i j hgap
      (hvalid q hmem)
  · intro i j
    have hb := FrameAux.Component.normalizedL_pairwise ref
      (FrameProgram.liftState idx d pts result.2.2) (p.w / 2 : ℚ) (|p.R| : ℚ)
      (FrameAux.Features.covariance d pts result.2.2) p.frameAccuracy hc.positive
      (by rw [FrameProgram.liftState, FrameProgram.iterationFrame,
        FrameAux.Linear.matrixOf_whitenL]) hc.invariant hc.normalized he hpass
      (fun j ↦ hcenter _) i j
    rw [ABBKS26.RefineAux.frame_sigmaSq p hσ] at hb
    exact hb

/-- Replace the semantic P1 witness by one rational, guarded filter implementation. -/
theorem exists_frame_code : ∃ F : FrameCode, FrameSpec F := by
  let F : FrameCode := ⟨FrameProgram.run⟩
  have hc : Robust.FrameContract (frameProc F) := by
    change Robust.FrameContract (fun d pts mode π R ζ fuel ↦
      FrameProgram.decode d (FrameProgram.run mode ((d, pts, π, R, ζ), fuel)))
    constructor
    · intro d pts mode π R ζ fuel
      dsimp only
      rw [FrameProgram.rounded_frame_agrees]
      dsimp only
      rw [List.length_map, FrameProgram.certificate_pool_bounds]
      exact Nat.mul_le_mul_right (d ^ 2)
        (FrameProgram.rounded_loop_bound d pts π R fuel pts.length
          (List.replicate pts.length 1)).1
    · intro n k d D pts mode π R ζ fuel hrep hD hres hπ hπ1 hR hζ _ he hn hf
      let result := FrameProgram.loop d pts π R fuel pts.length
        (List.replicate pts.length 1)
      let pool := FrameProgram.certificatePool d pts π result.2.1
      have hπ' : (π : ℝ) ≤ 1 := by
        have hh : (π : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hπ1
        norm_num at hh
        linarith only [hh]
      have hvalid (q : StatisticL) (hq : (q, true) ∈ pool) :
          ∀ l, Robust.statVariance D.model l (FrameProgram.quadOf d q) ≤
            (20 / (π : ℝ)) ^ 2 := by
        exact frame_pool_valid D pts π R result.2.1 hrep hD (frame_resilience D ζ hres)
          hπ' (he.trans (min_le_left _ _))
          (fun w hw ↦ ((FrameProgram.rounded_loop_bound d pts π R fuel pts.length
            (List.replicate pts.length 1)).2 w hw).1) q hq
      dsimp only
      simp only [FrameProgram.rounded_frame_agrees]
      change (_ ∨ _) ∧ _ ∧ _
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨idx, _, _, hloop⟩ := FrameProgram.rounded_loop_invariant D pts
          π R ζ fuel hrep hD hres hπ hπ1 hR hζ he hn hf
        rcases hloop with ⟨w, hw, hc, hel, hb⟩ | ⟨hc, hpass, hp⟩
        · have hfail := ((FrameProgram.rounded_loop_bound d pts π R fuel pts.length
            (List.replicate pts.length 1)).2 w hw).2
          obtain ⟨q, hq, i, j, hgap⟩ := FrameProgram.first_typeB_certificate D pts idx
            π R w hrep hπ1 hR he hc hfail hb
          have hmem : (q, true) ∈ pool := by
            apply List.mem_flatMap.mpr
            refine ⟨w, hw, List.mem_map.mpr ⟨q, hq, ?_⟩⟩
            simp [hel]
          exact Or.inl (frame_pool_far D pool _ _ _ _ R (20 / π) q hmem i j hgap
            (hvalid q hmem))
        · refine Or.inr ⟨hpass, ?_⟩
          exact FrameAux.Linear.normalizedL_pass D (FrameProgram.liftState idx d pts
            result.2.2) π R (FrameAux.Features.covariance d pts result.2.2) ζ
            hc.positive hζ hc.covariance_agrees
            (by rw [FrameProgram.liftState, FrameProgram.iterationFrame,
              FrameAux.Linear.matrixOf_whitenL]) hc.invariant hc.normalized he hp
      · intro hmode
        simp only [hmode, ite_true]
      · intro j hj
        have hj' := j.isLt
        change j.val < ((pool.map Prod.fst).map (FrameProgram.quadOf d)).length at hj'
        simp only [List.length_map] at hj'
        have hmem := frame_pool_flag pool j.val hj' hj
        simpa only [Fin.getElem_fin, List.getElem_map] using hvalid _ hmem
  refine ⟨F, ⟨FrameProgram.rounded_frame_polytime, hc, ?_, ?_⟩⟩
  · intro mode a i q hq _
    have hm := List.mem_of_getElem? hq
    change q ∈ (FrameProgram.certificatePool a.1.1 a.1.2.1 a.1.2.2.1
      (FrameProgram.loop a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.2
        a.1.2.1.length (List.replicate a.1.2.1.length 1)).2.1).map Prod.fst at hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨w, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
    have he : q = p.1 := congrArg Prod.fst heq
    exact FrameAux.Symmetry.columns_symmetric _ _ w p.1 (he ▸ hq)
  · exact rounded_component_bound hc


end ABBKS26.Assembly.Exec
