module

public import ABBKS26.Select.Recluster
public import ABBKS26.Assembly.ScheduleAuxSample
public import ABBKS26.Assembly.ScheduleAuxEncoding

/-!
# Backward schedule, finite majorant and sample bounds

The rational schedule satisfies the deterministic and quantitative sample requirements.
-/

@[expose] public section

namespace ABBKS26.Schedule

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree
open scoped BigOperators

/-- Fixed terminal tolerances; algorithmic parameters are independent of ε, Δ and n. -/
def terminal (w : ℚ) : StepParams :=
  ⟨w, 0, 1 / 2, w / 16, 0, 1, 1, 4, 0, 2400, 1 / 100, 1 / 1000000,
    1 / 100000000, 1 / 1000000, 2 / 10 ^ 10, w * (2 / 10 ^ 10) / 128, 2 ^ 40⟩

def step (mode : Mode) (w : ℚ) (k : ℕ) (next : StepParams) : StepParams :=
  let π := w / 2
  let φ := next.leakage / 4
  let WI := 1 / (16 * k : ℚ)
  let ω₀ := if mode = .centered then 1 / 2 else WI * (φ / 2) ^ 9 / 16
  let ω := w * ω₀ / 8
  let tail := min (φ / 64) (min (ω / 64) (w / 4096))
  let sb := 40 / w
  let K := if mode = .centered then dyadicUp (32 / φ) else 1
  let WF := dyadicUp (8 * sb * sqrtUp (1 / φ))
  let DF := dyadicUp (max (4 * WF) (4 * sb * sqrtUp (1 / tail)))
  let R := if mode = .centered then dyadicUp (2 * (k - 1 : ℚ) * (2 * DF + 3 * WF) + 1)
    else dyadicUp (sqrtUp 40 / π)
  let σ₂ := 600 / π ^ 2 + 2 * R ^ 2
  let β := if mode = .centered then
      dyadicDown ((128 * (4 / w))⁻¹ * (tail / (1024 * K ^ 2)) ^ (2 * (k - 1)))
    else dyadicDown (min (1 / 100) (1 / sqrtUp (10 ^ 6 * (k : ℚ) ^ 2 / tail)))
  let γ := if mode = .centered then Centered.gammaStar π β else IdCov.gammaStar β
  let E := if mode = .centered then Centered.etaStar π β else IdCov.etaStar w β / 4
  let B := if mode = .centered then 2 * (80 / w) ^ 4
    else 2 * (80 * IdCov.tDegree w / w) ^ (4 * IdCov.tDegree w)
  let req := dyadicDown (min (1 / (64000 * σ₂))
    (min (π / 400) (min (γ ^ 2 / (10 ^ 10 * σ₂))
      (min (E / (10 ^ 4 * B)) (min (ω / 64) (min (φ / 64)
        (min (w / 4096) (w ^ 2 / 10 ^ 8))))))))
  let Ψ := dyadicDown (min (w * req / 128) (min (next.leakage / 4) (w * ω₀ / 1024)))
  let rF := 10000 * σ₂ / π + 10
  let Δ := if mode = .centered then
      dyadicUp (max (2 * sqrtUp ((4 / w) / (3 * β ^ 8)))
        (max (4 * sqrtUp rF * (4 / w) / (9 * β ^ 16)) 1))
    else dyadicUp (sqrtUp (32 / (w * IdCov.tauStar β)))
  ⟨w, φ, ω₀, ω, tail, K, WF, DF, R, σ₂, β, γ, E, dyadicDown (γ / 10000), req, Ψ, Δ⟩

def params (mode : Mode) (w : ℚ) (k h : ℕ) : StepParams :=
  (step mode w k)^[k - 1 - h] (terminal w)

def etaReq (mode : Mode) (w : ℚ) (k : ℕ) : ℚ :=
  ((List.range (k - 1)).map fun h ↦
    let p := params mode w k h
    min (p.frameAccuracy ^ 2) (min (w * p.windowMass / 10000)
      (min (p.straddle ^ 2 / (1000 * p.K ^ 2))
        (min (p.tail ^ 2 / 10 ^ 6) (min (w * p.isotropy / 10000)
          (1 / (100 * sqrtUp (1 / p.momentError)))))))).foldl min
    (min ((terminal w).frameAccuracy ^ 2)
      (min (w / 10000) (min (1 / 10 ^ 8) (min ((params mode w k 0).leakage / 128)
        (if mode = .identical then 1 / (16000 * k) else 1)))))

def nWeight (mode : Mode) (w : ℚ) (k : ℕ) : ℕ :=
  ⌈max (128 / (params mode w k 0).leakage) (max (8 / w)
    (max (4 * 10 ^ 10 / w)
      (((List.range k).map fun h ↦
        8 * 64000 * (params mode w k h).sigmaSq / w).foldl max 0)))⌉₊

def momentDegree (mode : Mode) (w : ℚ) : ℕ :=
  if mode = .centered then 8 else 8 * IdCov.tDegree w

/-- A finite arithmetic ledger, evaluated at a dyadic outward weight bound. -/
def ledgerCore (mode : Mode) (w : ℚ) (k : ℕ) : ℕ :=
  let ps := (List.range k).map (params mode w k)
  let numbers := ps.flatMap fun p ↦
    [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
      ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]
  (numbers.map (fun a ↦ a + 2)).prod * (nWeight mode w k + 2) *
    (treeCap mode k (params mode w k) + 2) * (⌈1 / etaReq mode w k⌉₊ + 2)

/-- A parameter-only reserve pays for schedule bits and high-degree rounder fuel. -/
def ledger (mode : Mode) (w : ℚ) (k : ℕ) : ℕ :=
  2 ^ (ledgerCore mode w k + Rounding.solverConstant + 2) ^ 100

theorem ledgerCore_le (mode : Mode) (w : ℚ) (k : ℕ) :
    ledgerCore mode w k ≤ ledger mode w k := by
  apply (Nat.lt_two_pow_self (n := ledgerCore mode w k)).le.trans
  apply Nat.pow_le_pow_right (by norm_num)
  exact (by omega : ledgerCore mode w k ≤
    ledgerCore mode w k + Rounding.solverConstant + 2).trans
    (le_self_pow₀ (by omega) (by norm_num))

def H (a : ℕ) : ℕ :=
  let a := max 2 a
  ((((List.range (a - 1)).map fun j ↦
    (ledger .centered (1 / (a : ℚ)) (j + 2) + 2) *
      (ledger .identical (1 / (a : ℚ)) (j + 2) + 2))).prod + 2) ^ 100

def f (_mode : Mode) (x : ℝ) : ℝ := max 1 (H (max 2 ⌈x⌉₊) + 1 : ℕ)

def analysisEta (mode : Mode) (w Δ : ℚ) (k : ℕ) : ℝ :=
  min (etaReq mode w k : ℝ) ((w : ℝ) ^ 2 / (10000 * (k : ℝ) ^ 2 * Δ))

def sampleBound (mode : Mode) (C _k d : ℕ) (w Δ δ : ℚ) : ℝ :=
  match mode with
  | .centered => ((d + 1) * (Δ + 1) / ((w : ℝ) * δ)) ^ C
  | .identical => ((d + 1) / (w : ℝ)) ^ (C * (Real.log (1 / w) + 1)) *
      ((Δ + 1) / (δ : ℝ)) ^ C

def SampleReady (mode : Mode) (k d n : ℕ) (w Δ δ : ℚ) : Prop :=
  let η := analysisEta mode w Δ k
  nWeight mode w k ≤ n ∧ sampleNeed w η δ k d (momentDegree mode w) ≤ n ∧
    sampleNeed w η (1 / 2) k d (momentDegree mode w) ≤ n

private lemma dyadicDown_pos {q : ℚ} (hq : 0 < q) : 0 < dyadicDown q := by
  rw [dyadicDown, ite_eq_left hq]
  change 0 < ((2 : ℚ) ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1))⁻¹
  positivity

private lemma dyadicUp_pos (q : ℚ) : 0 < dyadicUp q := by
  unfold dyadicUp
  positivity

private lemma sqrtUp_pos (q : ℚ) : 0 < sqrtUp q := by
  unfold sqrtUp
  positivity

private lemma centered_gamma_pos {w β : ℚ} (hw : 0 < w) (hβ : 0 < β) :
    0 < Centered.gammaStar w β := by
  unfold Centered.gammaStar Centered.delta Centered.nu
  positivity

private lemma centered_eta_pos {w β : ℚ} (hw : 0 < w) (hβ : 0 < β) :
    0 < Centered.etaStar w β := by
  unfold Centered.etaStar Centered.delta Centered.nu
  positivity

private lemma identical_gamma_pos {β : ℚ} (hβ : 0 < β) :
    0 < IdCov.gammaStar β := by
  unfold IdCov.gammaStar IdCov.epsilonR
  positivity

private lemma identical_eta_pos (w : ℚ) {β : ℚ} (hβ : 0 < β) :
    0 < IdCov.etaStar w β := by
  have ht : 0 < (IdCov.tDegree w : ℚ) := by
    unfold IdCov.tDegree
    positivity
  unfold IdCov.etaStar IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
  positivity

private structure PositiveParams (p : StepParams) : Prop where
  weight : 0 < p.w
  window : 0 < p.windowMass
  K : 0 < p.K
  accuracy : 0 < p.subspaceAccuracy
  isotropy : 0 < p.isotropy
  moment : 0 < p.momentError
  sigma : 0 < p.sigmaSq
  contamination : 0 < p.contamination
  leakage : 0 < p.leakage

private lemma terminal_positive {w : ℚ} (hw : 0 < w) : PositiveParams (terminal w) := by
  constructor <;> dsimp [terminal] <;> positivity

private lemma step_positive (mode : Mode) {w : ℚ} (k : ℕ) (next : StepParams)
    (hw : 0 < w) (hk : 0 < k) (hn : 0 < next.leakage) :
    PositiveParams (step mode w k next) ∧
      0 < (step mode w k next).straddle ∧ 0 < (step mode w k next).tail := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hφ : 0 < next.leakage / 4 := by positivity
  have hω₀ : 0 < (if mode = .centered then 1 / 2
      else (1 / (16 * k : ℚ)) * (next.leakage / 4 / 2) ^ 9 / 16) := by
    split_ifs <;> positivity
  have hω : 0 < w * (if mode = .centered then 1 / 2
      else (1 / (16 * k : ℚ)) * (next.leakage / 4 / 2) ^ 9 / 16) / 8 := by
    positivity
  dsimp only [step]
  generalize ht : (min _ _ : ℚ) = tail
  have htail : 0 < tail := by
    rw [← ht]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  generalize hK : (if mode = .centered then dyadicUp _ else 1) = K
  have hKpos : 0 < K := by
    rw [← hK]
    split_ifs
    · exact dyadicUp_pos _
    · norm_num
  generalize hR : (if mode = .centered then dyadicUp _ else dyadicUp _) = R
  generalize hσ : 600 / (w / 2) ^ 2 + 2 * R ^ 2 = σ
  have hσpos : 0 < σ := by rw [← hσ]; positivity
  generalize hβ : (if mode = .centered then dyadicDown _ else dyadicDown _) = β
  have hβpos : 0 < β := by
    rw [← hβ]
    split_ifs
    · apply dyadicDown_pos
      positivity
    · apply dyadicDown_pos
      exact lt_min (by norm_num) (by exact div_pos (by norm_num) (sqrtUp_pos _))
  generalize hγ : (if mode = .centered then Centered.gammaStar _ _
      else IdCov.gammaStar _) = γ
  have hγpos : 0 < γ := by
    rw [← hγ]
    split_ifs
    · exact centered_gamma_pos (by positivity) hβpos
    · exact identical_gamma_pos hβpos
  generalize hE : (if mode = .centered then Centered.etaStar _ _
      else IdCov.etaStar _ _ / 4) = E
  have hEpos : 0 < E := by
    rw [← hE]
    split_ifs
    · exact centered_eta_pos (by positivity) hβpos
    · exact div_pos (identical_eta_pos w hβpos) (by norm_num)
  generalize hB : (if mode = .centered then 2 * (80 / w) ^ 4 else _) = B
  have hBpos : 0 < B := by
    rw [← hB]
    have htd : 0 < (IdCov.tDegree w : ℚ) := by unfold IdCov.tDegree; positivity
    split_ifs <;> positivity
  generalize hr : dyadicDown (min _ _) = req
  have hrpos : 0 < req := by
    rw [← hr]
    apply dyadicDown_pos
    repeat' apply lt_min
    all_goals positivity
  refine ⟨⟨hw, hω₀, hKpos, hβpos, hγpos, hEpos, hσpos, hrpos, ?_⟩, hφ, htail⟩
  apply dyadicDown_pos
  repeat' apply lt_min
  all_goals positivity

private lemma params_succ (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k - 1) :
    params mode w k h = step mode w k (params mode w k (h + 1)) := by
  unfold params
  have he : k - 1 - h = (k - 1 - (h + 1)) + 1 := by omega
  rw [he, Function.iterate_succ_apply']

private lemma iterate_positive (mode : Mode) {w : ℚ} (k m : ℕ)
    (hw : 0 < w) (hk : 0 < k) :
    PositiveParams ((step mode w k)^[m] (terminal w)) := by
  induction m with
  | zero => exact terminal_positive hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (step_positive mode k _ hw hk ih.leakage).1

private lemma params_positive (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w) (hk : 0 < k) : PositiveParams (params mode w k h) :=
  iterate_positive mode k _ hw hk

private lemma params_budgets_nonneg (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w) (hk : 0 < k) :
    0 ≤ (params mode w k h).straddle ∧ 0 ≤ (params mode w k h).tail := by
  unfold params
  generalize k - 1 - h = m
  cases m with
  | zero => norm_num [terminal]
  | succ m =>
    rw [Function.iterate_succ_apply']
    have hp := step_positive mode k ((step mode w k)^[m] (terminal w)) hw hk
      (iterate_positive mode k m hw hk).leakage
    exact ⟨hp.2.1.le, hp.2.2.le⟩

private lemma foldl_min_pos (xs : List ℚ) {q : ℚ} (hq : 0 < q)
    (hxs : ∀ x ∈ xs, 0 < x) : 0 < xs.foldl min q := by
  induction xs generalizing q with
  | nil => exact hq
  | cons x xs ih =>
    exact ih (lt_min hq (hxs x (by simp))) (fun y hy ↦ hxs y (by simp [hy]))

private lemma etaReq_pos (mode : Mode) {w : ℚ} (k : ℕ)
    (hw : 0 < w) (hk0 : 0 < k) : 0 < etaReq mode w k := by
  have hp := params_positive mode k 0 hw hk0
  apply foldl_min_pos
  · have hkq : (0 : ℚ) < k := by exact_mod_cast hk0
    repeat' apply lt_min
    · norm_num [terminal]
    · positivity
    · norm_num
    · exact div_pos hp.leakage (by norm_num)
    · split_ifs <;> positivity
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    have hh' := List.mem_range.mp hh
    have hp := params_positive mode k h hw hk0
    have hwindow := hp.window
    have hK := hp.K
    have hisotropy := hp.isotropy
    have hs := (step_positive mode k (params mode w k (h + 1)) hw hk0
      (params_positive mode k (h + 1) hw hk0).leakage).2
    rw [← params_succ mode w k h hh'] at hs
    have hframe : 0 < (params mode w k h).frameAccuracy := by
      rw [params_succ mode w k h hh']
      exact dyadicDown_pos (div_pos
        (step_positive mode k _ hw hk0
          (params_positive mode k (h + 1) hw hk0).leakage).1.isotropy (by norm_num))
    dsimp
    repeat' apply lt_min
    · exact sq_pos_of_pos hframe
    · positivity
    · exact div_pos (sq_pos_of_pos hs.1) (by positivity)
    · exact div_pos (sq_pos_of_pos hs.2) (by norm_num)
    · positivity
    · exact div_pos (by norm_num) (mul_pos (by norm_num) (sqrtUp_pos _))

/-- The backward rational schedule meets all positivity and one-step inequalities. -/
theorem schedule_valid
    (mode : Mode) (w : ℚ) (k : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 2 ≤ k)
    (hkw : (k : ℚ) * w ≤ 1) :
    0 < etaReq mode w k ∧ ∀ h, h < k →
      0 < (params mode w k h).contamination ∧
      0 < (params mode w k h).leakage ∧
      (h < k - 1 →
        (params mode w k h).straddle = (params mode w k (h + 1)).leakage / 4) := by
  have hk0 : 0 < k := by omega
  have _ := hkw
  constructor
  · exact etaReq_pos mode k hw.1 hk0
  · intro h _
    have hp := params_positive mode k h hw.1 hk0
    refine ⟨hp.contamination, hp.leakage, fun hh ↦ ?_⟩
    rw [params_succ mode w k h hh]
    rfl

@[gcongr]
private lemma dyadicUp_mono {x y : ℚ} (h : x ≤ y) : dyadicUp x ≤ dyadicUp y := by
  unfold dyadicUp
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.clog_mono_right 2 (max_le_max_left 1 (Nat.ceil_mono h)))

@[gcongr]
private lemma sqrtUp_mono {x y : ℚ} (h : x ≤ y) : sqrtUp x ≤ sqrtUp y := by
  unfold sqrtUp
  exact_mod_cast Nat.add_le_add_right
    (Nat.sqrt_le_sqrt (Nat.ceil_mono (max_le_max_left 0 h))) 1

@[gcongr]
private lemma dyadicDown_mono {x y : ℚ} (hx : 0 < x) (h : x ≤ y) :
    dyadicDown x ≤ dyadicDown y := by
  have hy := hx.trans_le h
  simp only [dyadicDown, ite_eq_left hx, ite_eq_left hy]
  change ((2 : ℚ) ^ _)⁻¹ ≤ ((2 : ℚ) ^ _)⁻¹
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  apply pow_le_pow_right₀ (by norm_num)
  exact Nat.add_le_add_right
    (Nat.clog_mono_right 2 (Nat.ceil_mono (one_div_le_one_div_of_le hx h))) 1

private lemma degree_antitone {w u : ℚ} (hw : 0 < w) (hwu : w ≤ u) :
    IdCov.tDegree u ≤ IdCov.tDegree w := by
  unfold IdCov.tDegree logInv
  gcongr

private lemma identical_eta_mono {w u b c : ℚ} (hw : 0 < w) (hwu : w ≤ u)
    (hb : 0 < b) (hbc : b ≤ c) (hc : c ≤ 1) :
    IdCov.etaStar w b ≤ IdCov.etaStar u c := by
  have ht := degree_antitone hw hwu
  have hc0 := hb.trans_le hbc
  have ht0 : (0 : ℚ) < IdCov.tDegree u := by unfold IdCov.tDegree; positivity
  have ht1 : (1 : ℚ) ≤ IdCov.tDegree u := by
    unfold IdCov.tDegree
    push_cast
    linarith [Nat.cast_nonneg (α := ℚ) (logInv u)]
  have htr : (IdCov.tDegree u : ℚ) ≤ IdCov.tDegree w := by exact_mod_cast ht
  have hbase : 0 ≤ IdCov.cStar b / (64 * IdCov.tDegree w) := by
    unfold IdCov.cStar IdCov.epsilonR
    positivity
  have hbasele : IdCov.cStar b / (64 * IdCov.tDegree w) ≤
      IdCov.cStar c / (64 * IdCov.tDegree u) := by
    unfold IdCov.cStar IdCov.epsilonR
    gcongr
  have hbase1 : IdCov.cStar c / (64 * IdCov.tDegree u) ≤ 1 := by
    have he : IdCov.epsilonR c ≤ 1 := by
      apply pow_le_one₀ (by positivity)
        (by linarith)
    have hcstar : IdCov.cStar c ≤ 1 := by
      unfold IdCov.cStar
      have he0 : 0 ≤ IdCov.epsilonR c := by unfold IdCov.epsilonR; positivity
      have he2 : IdCov.epsilonR c ^ 2 ≤ 1 := pow_le_one₀ he0 he
      linarith
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hnum : IdCov.epsilonSys w b ≤ IdCov.epsilonSys u c := by
    unfold IdCov.epsilonSys IdCov.epsilonId
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (pow_le_pow_left₀ hbase hbasele _).trans
      (pow_le_pow_of_le_one (by unfold IdCov.cStar IdCov.epsilonR; positivity)
        hbase1 (by omega))
  have hden : (8 * IdCov.tDegree u : ℚ) ^ (4 * IdCov.tDegree u + 2) ≤
      (8 * IdCov.tDegree w : ℚ) ^ (4 * IdCov.tDegree w + 2) := by
    calc
      _ ≤ (8 * IdCov.tDegree w : ℚ) ^ (4 * IdCov.tDegree u + 2) := by gcongr
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  unfold IdCov.etaStar
  exact div_le_div₀ (by
    unfold IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
    positivity)
    hnum (by positivity) hden

private structure ScheduleOrder (p q : StepParams) : Prop where
  w : p.w ≤ q.w
  straddle : p.straddle ≤ q.straddle
  window : p.windowMass ≤ q.windowMass
  tail : p.tail ≤ q.tail
  K : q.K ≤ p.K
  sigma : q.sigmaSq ≤ p.sigmaSq
  accuracy : p.subspaceAccuracy ≤ q.subspaceAccuracy
  isotropy : p.isotropy ≤ q.isotropy
  moment : p.momentError ≤ q.momentError
  contamination : p.contamination ≤ q.contamination
  leakage : p.leakage ≤ q.leakage
  separation : q.separation ≤ p.separation

private lemma dyadicDown_le_half (x : ℚ) : dyadicDown x ≤ 1 / 2 := by
  unfold dyadicDown
  split_ifs
  · change ((2 : ℚ) ^ _)⁻¹ ≤ 1 / 2
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have h : (1 : ℚ) ≤ 2 ^ Nat.clog 2 ⌈1 / x⌉₊ := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  · norm_num

private def momentBound (mode : Mode) (w : ℚ) : ℚ :=
  if mode = .centered then 2 * (80 / w) ^ 4
  else 2 * (80 * IdCov.tDegree w / w) ^ (4 * IdCov.tDegree w)

private lemma momentBound_pos (mode : Mode) {w : ℚ} (hw : 0 < w) :
    0 < momentBound mode w := by
  have ht : 0 < (IdCov.tDegree w : ℚ) := by unfold IdCov.tDegree; positivity
  unfold momentBound
  split_ifs <;> positivity

private structure StepFormulas (mode : Mode) (w : ℚ) (k : ℕ) (next p : StepParams) : Prop where
  weight : p.w = w
  straddle : p.straddle = next.leakage / 4
  window : p.windowMass = if mode = .centered then 1 / 2
    else (1 / (16 * k : ℚ)) * (p.straddle / 2) ^ 9 / 16
  verify : p.verifyMass = w * p.windowMass / 8
  tail : p.tail = min (p.straddle / 64) (min (p.verifyMass / 64) (w / 4096))
  K : p.K = if mode = .centered then dyadicUp (32 / p.straddle) else 1
  WF : p.WF = dyadicUp (8 * (40 / w) * sqrtUp (1 / p.straddle))
  DF : p.DF = dyadicUp (max (4 * p.WF) (4 * (40 / w) * sqrtUp (1 / p.tail)))
  R : p.R = if mode = .centered then
    dyadicUp (2 * (k - 1 : ℚ) * (2 * p.DF + 3 * p.WF) + 1)
    else dyadicUp (sqrtUp 40 / (w / 2))
  sigma : p.sigmaSq = 600 / (w / 2) ^ 2 + 2 * p.R ^ 2
  accuracy : p.subspaceAccuracy = if mode = .centered then
    dyadicDown ((128 * (4 / w))⁻¹ * (p.tail / (1024 * p.K ^ 2)) ^ (2 * (k - 1)))
    else dyadicDown (min (1 / 100) (1 / sqrtUp (10 ^ 6 * (k : ℚ) ^ 2 / p.tail)))
  isotropy : p.isotropy = if mode = .centered then Centered.gammaStar (w / 2) p.subspaceAccuracy
    else IdCov.gammaStar p.subspaceAccuracy
  moment : p.momentError = if mode = .centered then Centered.etaStar (w / 2) p.subspaceAccuracy
    else IdCov.etaStar w p.subspaceAccuracy / 4
  frame : p.frameAccuracy = dyadicDown (p.isotropy / 10000)
  contamination : p.contamination = dyadicDown (min (1 / (64000 * p.sigmaSq))
    (min ((w / 2) / 400) (min (p.isotropy ^ 2 / (10 ^ 10 * p.sigmaSq))
      (min (p.momentError / (10 ^ 4 * momentBound mode w)) (min (p.verifyMass / 64)
        (min (p.straddle / 64) (min (w / 4096) (w ^ 2 / 10 ^ 8))))))))
  leakage : p.leakage = dyadicDown (min (w * p.contamination / 128)
    (min (next.leakage / 4) (w * p.windowMass / 1024)))
  separation : p.separation = if mode = .centered then dyadicUp
    (max (2 * sqrtUp ((4 / w) / (3 * p.subspaceAccuracy ^ 8)))
      (max (4 * sqrtUp (10000 * p.sigmaSq / (w / 2) + 10) * (4 / w) /
        (9 * p.subspaceAccuracy ^ 16)) 1))
    else dyadicUp (sqrtUp (32 / (w * IdCov.tauStar p.subspaceAccuracy)))

private lemma step_formulas (mode : Mode) (w : ℚ) (k : ℕ) (next : StepParams) :
    StepFormulas mode w k next (step mode w k next) := by
  constructor <;> rfl

private structure GeometryOrder (p q : StepParams) : Prop where
  straddle : p.straddle ≤ q.straddle
  window : p.windowMass ≤ q.windowMass
  verify : p.verifyMass ≤ q.verifyMass
  tail : p.tail ≤ q.tail
  K : q.K ≤ p.K
  sigma : q.sigmaSq ≤ p.sigmaSq

private lemma formulas_geometry (mode : Mode) {w u : ℚ} (k : ℕ) (a b p q : StepParams)
    (hw : 0 < w) (hwu : w ≤ u) (_hu1 : u ≤ 1 / 2) (hk : 1 ≤ k)
    (ha : 0 < a.leakage) (hab : a.leakage ≤ b.leakage)
    (hp : StepFormulas mode w k a p) (hq : StepFormulas mode u k b q)
    (hppos : PositiveParams p) (hqpos : PositiveParams q)
    (hpφ : 0 < p.straddle) (_hqφ : 0 < q.straddle)
    (hptail : 0 < p.tail) (_hqtail : 0 < q.tail) : GeometryOrder p q := by
  have hu := hw.trans_le hwu
  have hb := ha.trans_le hab
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hpposCopy := hppos
  have hqposCopy := hqpos
  obtain ⟨_, hpm, hpK, _, hpγ, hpE, _, hpreq, hpleak⟩ := hpposCopy
  obtain ⟨_, hqm, hqK, _, hqγ, hqE, _, hqreq, hqleak⟩ := hqposCopy
  have hφ : p.straddle ≤ q.straddle := by
    rw [hp.straddle, hq.straddle]
    gcongr
  have hm : p.windowMass ≤ q.windowMass := by
    rw [hp.window, hq.window]
    split_ifs
    · exact le_rfl
    · gcongr
  have hω : p.verifyMass ≤ q.verifyMass := by
    rw [hp.verify, hq.verify]
    gcongr
  have htail : p.tail ≤ q.tail := by
    rw [hp.tail, hq.tail]
    gcongr
  have hK : q.K ≤ p.K := by
    rw [hp.K, hq.K]
    split_ifs
    · gcongr
    · exact le_rfl
  have hWF : q.WF ≤ p.WF := by
    rw [hp.WF, hq.WF]
    gcongr
    exact (sqrtUp_pos _).le
  have hpWF : 0 < p.WF := by rw [hp.WF]; exact dyadicUp_pos _
  have hqWF : 0 < q.WF := by rw [hq.WF]; exact dyadicUp_pos _
  have hDF : q.DF ≤ p.DF := by
    rw [hp.DF, hq.DF]
    gcongr
    exact (sqrtUp_pos _).le
  have hpDF : 0 < p.DF := by rw [hp.DF]; exact dyadicUp_pos _
  have hqDF : 0 < q.DF := by rw [hq.DF]; exact dyadicUp_pos _
  have hR : q.R ≤ p.R := by
    rw [hp.R, hq.R]
    split_ifs <;> gcongr
    exact (sqrtUp_pos _).le
  have hpR : 0 < p.R := by
    rw [hp.R]
    split_ifs <;> exact dyadicUp_pos _
  have hqR : 0 < q.R := by
    rw [hq.R]
    split_ifs <;> exact dyadicUp_pos _
  have hσ : q.sigmaSq ≤ p.sigmaSq := by
    rw [hp.sigma, hq.sigma]
    gcongr
  have hpσ : 0 < p.sigmaSq := by rw [hp.sigma]; positivity
  have hqσ : 0 < q.sigmaSq := by rw [hq.sigma]; positivity
  exact ⟨hφ, hm, hω, htail, hK, hσ⟩

private lemma formulas_accuracy (mode : Mode) {w u : ℚ} (k : ℕ) (a b p q : StepParams)
    (hw : 0 < w) (hwu : w ≤ u) (_hu1 : u ≤ 1 / 2) (hk : 1 ≤ k)
    (ha : 0 < a.leakage) (hab : a.leakage ≤ b.leakage)
    (hp : StepFormulas mode w k a p) (hq : StepFormulas mode u k b q)
    (hppos : PositiveParams p) (hqpos : PositiveParams q)
    (_hpφ : 0 < p.straddle) (_hqφ : 0 < q.straddle)
    (hptail : 0 < p.tail) (hqtail : 0 < q.tail) (ho : GeometryOrder p q) :
    p.subspaceAccuracy ≤ q.subspaceAccuracy ∧ p.isotropy ≤ q.isotropy ∧
      p.momentError ≤ q.momentError := by
  have hu := hw.trans_le hwu
  have hb := ha.trans_le hab
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hpposCopy := hppos
  have hqposCopy := hqpos
  obtain ⟨_, hpm, hpK, _, hpγ, hpE, _, hpreq, hpleak⟩ := hpposCopy
  obtain ⟨_, hqm, hqK, _, hqγ, hqE, _, hqreq, hqleak⟩ := hqposCopy
  obtain ⟨hφ, hm, hω, htail, hK, hσ⟩ := ho
  have hpβ := hppos.accuracy
  have hqβ := hqpos.accuracy
  have hβ : p.subspaceAccuracy ≤ q.subspaceAccuracy := by
    rw [hp.accuracy, hq.accuracy]
    split_ifs
    · apply dyadicDown_mono (by positivity)
      gcongr
    · apply dyadicDown_mono (lt_min (by norm_num)
        (div_pos (by norm_num) (sqrtUp_pos _)))
      gcongr
      exact sqrtUp_pos _
  have hqβ1 : q.subspaceAccuracy ≤ 1 := by
    rw [hq.accuracy]
    split_ifs <;> exact (dyadicDown_le_half _).trans (by norm_num)
  have hγ : p.isotropy ≤ q.isotropy := by
    rw [hp.isotropy, hq.isotropy]
    split_ifs
    · unfold Centered.gammaStar Centered.delta Centered.nu
      gcongr
    · unfold IdCov.gammaStar IdCov.epsilonR
      gcongr
  have hE : p.momentError ≤ q.momentError := by
    rw [hp.moment, hq.moment]
    split_ifs
    · unfold Centered.etaStar Centered.delta Centered.nu
      gcongr
    · exact div_le_div_of_nonneg_right (identical_eta_mono hw hwu hpβ hβ hqβ1)
        (by norm_num)
  exact ⟨hβ, hγ, hE⟩

private lemma momentBound_antitone (mode : Mode) {w u : ℚ}
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) :
    momentBound mode u ≤ momentBound mode w := by
  have hu := hw.trans_le hwu
  have ht := degree_antitone hw hwu
  have htu : (1 : ℚ) ≤ IdCov.tDegree u := by
    unfold IdCov.tDegree
    push_cast
    linarith [Nat.cast_nonneg (α := ℚ) (logInv u)]
  have htq : (IdCov.tDegree u : ℚ) ≤ IdCov.tDegree w := by exact_mod_cast ht
  have hB : (if mode = .centered then 2 * (80 / u) ^ 4
      else 2 * (80 * IdCov.tDegree u / u) ^ (4 * IdCov.tDegree u)) ≤
      (if mode = .centered then 2 * (80 / w) ^ 4
      else 2 * (80 * IdCov.tDegree w / w) ^ (4 * IdCov.tDegree w)) := by
    split_ifs
    · gcongr
    · have hbase : 1 ≤ 80 * (IdCov.tDegree u : ℚ) / u := by
        rw [le_div_iff₀ hu]
        linarith
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hbasele : 80 * (IdCov.tDegree u : ℚ) / u ≤
          80 * (IdCov.tDegree w : ℚ) / w := by gcongr
      exact (pow_le_pow_left₀ (by positivity) hbasele _).trans
        (pow_le_pow_right₀ (hbase.trans hbasele) (by omega))
  exact hB

private lemma formulas_order (mode : Mode) {w u : ℚ} (k : ℕ) (a b p q : StepParams)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k)
    (ha : 0 < a.leakage) (hab : a.leakage ≤ b.leakage)
    (hp : StepFormulas mode w k a p) (hq : StepFormulas mode u k b q)
    (hppos : PositiveParams p) (hqpos : PositiveParams q)
    (hpφ : 0 < p.straddle) (hqφ : 0 < q.straddle)
    (hptail : 0 < p.tail) (hqtail : 0 < q.tail) : ScheduleOrder p q := by
  have hu := hw.trans_le hwu
  have hb := ha.trans_le hab
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hpposCopy := hppos
  have hqposCopy := hqpos
  obtain ⟨_, hpm, hpK, _, hpγ, hpE, _, hpreq, hpleak⟩ := hpposCopy
  obtain ⟨_, hqm, hqK, _, hqγ, hqE, _, hqreq, hqleak⟩ := hqposCopy
  obtain ⟨hφ, hm, hω, htail, hK, hσ⟩ :=
    formulas_geometry mode k a b p q hw hwu hu1 hk ha hab hp hq hppos hqpos
      hpφ hqφ hptail hqtail
  obtain ⟨hβ, hγ, hE⟩ := formulas_accuracy mode k a b p q hw hwu hu1 hk ha hab hp hq
    hppos hqpos hpφ hqφ hptail hqtail ⟨hφ, hm, hω, htail, hK, hσ⟩
  have hpβ := hppos.accuracy
  have hqβ := hqpos.accuracy
  have hpσ := hppos.sigma
  have hqσ := hqpos.sigma
  have hB := momentBound_antitone mode hw hwu hu1
  have hpω : 0 < p.verifyMass := by rw [hp.verify]; positivity
  have hpB := momentBound_pos mode hw
  have hqB := momentBound_pos mode hu
  have hreq : p.contamination ≤ q.contamination := by
    rw [hp.contamination, hq.contamination]
    apply dyadicDown_mono
    · repeat' apply lt_min
      all_goals positivity
    · gcongr
  have hleak : p.leakage ≤ q.leakage := by
    rw [hp.leakage, hq.leakage]
    apply dyadicDown_mono (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
    gcongr
  have hroot := (sqrtUp_pos (10000 * p.sigmaSq / (w / 2) + 10)).le
  have hsep : q.separation ≤ p.separation := by
    rw [hp.separation, hq.separation]
    split_ifs
    · gcongr
    · unfold IdCov.tauStar IdCov.epsilonR
      gcongr
  refine ⟨?_, hφ, hm, htail, hK, hσ, hβ, hγ, hE, hreq, hleak, hsep⟩
  simpa only [hp.weight, hq.weight] using hwu


private lemma step_order (mode : Mode) {w u : ℚ} (k : ℕ) (a b : StepParams)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k)
    (ha : 0 < a.leakage) (hab : a.leakage ≤ b.leakage) :
    ScheduleOrder (step mode w k a) (step mode u k b) := by
  have hp := step_positive mode k a hw (by omega) ha
  have hq := step_positive mode k b (hw.trans_le hwu) (by omega) (ha.trans_le hab)
  exact formulas_order mode k a b _ _ hw hwu hu1 hk ha hab
    (step_formulas mode w k a) (step_formulas mode u k b)
    hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2

private lemma params_weight (mode : Mode) (w : ℚ) (k h : ℕ) :
    (params mode w k h).w = w := by
  have hi (m : ℕ) : ((step mode w k)^[m] (terminal w)).w = w := by
    cases m with
    | zero => rfl
    | succ m => rw [Function.iterate_succ_apply']; rfl
  exact hi _

private lemma params_order (mode : Mode) {w u : ℚ} (k h : ℕ)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k) :
    ScheduleOrder (params mode w k h) (params mode u k h) := by
  have hi (m : ℕ) : ScheduleOrder ((step mode w k)^[m] (terminal w))
      ((step mode u k)^[m] (terminal u)) := by
    induction m with
    | zero =>
      constructor <;> dsimp [terminal]
      · exact hwu
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · gcongr
      · exact le_rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply step_order mode k _ _ hw hwu hu1 hk _ ih.leakage
      have hp (m : ℕ) : PositiveParams ((step mode w k)^[m] (terminal w)) := by
        induction m with
        | zero => exact terminal_positive hw
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact (step_positive mode k _ hw (by omega) ih.leakage).1
      exact (hp m).leakage
  exact hi _

private lemma foldl_min_mono {α : Type*} (xs : List α) (f g : α → ℚ) {p q : ℚ}
    (hpq : p ≤ q) (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).foldl min p ≤ (xs.map g).foldl min q := by
  induction xs generalizing p q with
  | nil => exact hpq
  | cons x xs ih =>
    exact ih (min_le_min hpq (hfg x (by simp))) (fun y hy ↦ hfg y (by simp [hy]))

private lemma foldl_max_mono {α : Type*} (xs : List α) (f g : α → ℚ) {p q : ℚ}
    (hpq : p ≤ q) (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).foldl max p ≤ (xs.map g).foldl max q := by
  induction xs generalizing p q with
  | nil => exact hpq
  | cons x xs ih =>
    exact ih (max_le_max hpq (hfg x (by simp))) (fun y hy ↦ hfg y (by simp [hy]))

private lemma etaReq_mono (mode : Mode) {w u : ℚ} (k : ℕ)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k) :
    etaReq mode w k ≤ etaReq mode u k := by
  have hu := hw.trans_le hwu
  have h0 := (params_order mode k 0 hw hwu hu1 hk).leakage
  unfold etaReq
  apply foldl_min_mono
  · dsimp only [terminal]
    gcongr
  · intro h hh
    have hh' := List.mem_range.mp hh
    have hframe (v : ℚ) : (params mode v k h).frameAccuracy =
        dyadicDown ((params mode v k h).isotropy / 10000) := by
      rw [params_succ mode v k h hh']
      rfl
    have hpframe : 0 < (params mode w k h).frameAccuracy := by
      rw [hframe]
      exact dyadicDown_pos (div_pos
        (params_positive mode k h hw (by omega)).isotropy (by norm_num))
    have hframele : (params mode w k h).frameAccuracy ≤
        (params mode u k h).frameAccuracy := by
      rw [hframe, hframe]
      apply dyadicDown_mono
      · exact div_pos (params_positive mode k h hw (by omega)).isotropy (by norm_num)
      · gcongr
        exact (params_order mode k h hw hwu hu1 hk).isotropy
    obtain ⟨_, hφ, hm, htail, hK, _, _, hγ, hE, _, _, _⟩ :=
      params_order mode k h hw hwu hu1 hk
    obtain ⟨_, hpm, hpK, _, hpγ, hpE, _, _, _⟩ :=
      params_positive mode k h hw (by omega)
    obtain ⟨_, hqm, hqK, _, hqγ, hqE, _, _, _⟩ :=
      params_positive mode k h hu (by omega)
    obtain ⟨hpφ, hptail⟩ := params_budgets_nonneg mode k h hw (by omega)
    dsimp
    gcongr
    exact mul_pos (by norm_num) (sqrtUp_pos _)

private lemma nWeight_antitone (mode : Mode) {w u : ℚ} (k : ℕ)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k) :
    nWeight mode u k ≤ nWeight mode w k := by
  have hu := hw.trans_le hwu
  have hp := params_positive mode k 0 hw (by omega)
  have hq := params_positive mode k 0 hu (by omega)
  have hleak := (params_order mode k 0 hw hwu hu1 hk).leakage
  have hpl := hp.leakage
  have hql := hq.leakage
  unfold nWeight
  apply Nat.ceil_mono
  apply max_le_max
  · gcongr
  · apply max_le_max
    · gcongr
    · apply max_le_max
      · gcongr
      · apply foldl_max_mono _ _ _ le_rfl
        intro h _
        have hσ := (params_order mode k h hw hwu hu1 hk).sigma
        have hpσ := (params_positive mode k h hw (by omega)).sigma
        gcongr

private lemma sqrtUp_one_le (x : ℚ) : 1 ≤ sqrtUp x := by
  unfold sqrtUp
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)

private lemma rankCap_mono {γ δ : ℚ} {r s : ℕ}
    (hγ : 0 < γ) (hγδ : γ ≤ δ) (hδ : δ ≤ 40) (hrs : r ≤ s) :
    Rounding.rankCap δ r ≤ Rounding.rankCap γ s := by
  have hδ0 := hγ.trans_le hγδ
  have hroot := sqrtUp_one_le (r : ℚ)
  have hroots : sqrtUp (r : ℚ) ≤ sqrtUp (s : ℚ) :=
    sqrtUp_mono (by exact_mod_cast hrs)
  have hbasele : 2 * ⌈40 * sqrtUp r / δ⌉₊ ≤ 2 * ⌈40 * sqrtUp s / γ⌉₊ := by
    gcongr
    exact mul_nonneg (by norm_num) (sqrtUp_pos _).le
  have hbase1 : 1 ≤ 2 * ⌈40 * sqrtUp s / γ⌉₊ := by
    have hx : (1 : ℚ) ≤ 40 * sqrtUp r / δ := by
      rw [le_div_iff₀ hδ0]
      linarith
    have hn : 1 ≤ ⌈40 * sqrtUp r / δ⌉₊ := by
      exact_mod_cast hx.trans (Nat.le_ceil _)
    omega
  have hpack : Rounding.packCount δ r ≤ Rounding.packCount γ s := by
    exact (Nat.pow_le_pow_left hbasele _).trans (Nat.pow_le_pow_right hbase1 hrs)
  have hgreedy : Rounding.greedyCap δ r ≤ Rounding.greedyCap γ s := by
    unfold Rounding.greedyCap Rounding.greedyThreshold
    simp only [one_div, div_inv_eq_mul]
    gcongr
    norm_num
  unfold Rounding.rankCap
  gcongr

private lemma netBound_mono {a b : ℚ} {D E : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hDE : D ≤ E) : netBound D b ≤ netBound E a := by
  have hb := ha.trans_le hab
  have hbase : 1 + ⌈64 * (D : ℚ) / b⌉₊ ≤ 1 + ⌈64 * (E : ℚ) / a⌉₊ := by
    gcongr
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (by omega) hDE)

private lemma stepBranchCap_mono (mode : Mode) (k : ℕ) (p q : StepParams)
    (hp : PositiveParams p) (hq : PositiveParams q) (ho : ScheduleOrder p q)
    (hqβ1 : q.subspaceAccuracy ≤ 1 / 2) : stepBranchCap mode k q ≤ stepBranchCap mode k p := by
  obtain ⟨hwp, hpm, hpK, hpβ, hpγ, hpE, hpσ, hpreq, hpleak⟩ := hp
  obtain ⟨hwq, hqm, hqK, hqβ, hqγ, hqE, hqσ, hqreq, hqleak⟩ := hq
  obtain ⟨hw, hφ, hm, htail, hK, hσ, hβ, hγ, hE, hreq, hleak, hsep⟩ := ho
  cases mode with
  | centered =>
    have hrank : Centered.rankBound (q.w / 2)
        (10000 * q.sigmaSq / (q.w / 2) + 10) q.subspaceAccuracy ≤
        Centered.rankBound (p.w / 2)
        (10000 * p.sigmaSq / (p.w / 2) + 10) p.subspaceAccuracy := by
      unfold Centered.rankBound Centered.delta Centered.nu
      gcongr
    have hdim : Centered.dimensionCap (q.w / 2)
        (10000 * q.sigmaSq / (q.w / 2) + 10) q.subspaceAccuracy ≤
        Centered.dimensionCap (p.w / 2)
        (10000 * p.sigmaSq / (p.w / 2) + 10) p.subspaceAccuracy := by
      apply rankCap_mono (by unfold Centered.radius; positivity)
        (by unfold Centered.radius; gcongr) _ hrank
      unfold Centered.radius
      linarith
    have hnet := netBound_mono hpβ hβ hdim
    dsimp only [stepBranchCap]
    gcongr
  | identical =>
    have hdim : IdCov.N_pack q.subspaceAccuracy k ≤ IdCov.N_pack p.subspaceAccuracy k :=
      rankCap_mono hpβ hβ (hqβ1.trans (by norm_num)) le_rfl
    have hnet := netBound_mono hpβ hβ hdim
    dsimp only [stepBranchCap]
    gcongr

private lemma params_accuracy_le_half (mode : Mode) (w : ℚ) (k h : ℕ) :
    (params mode w k h).subspaceAccuracy ≤ 1 / 2 := by
  unfold params
  generalize k - 1 - h = m
  cases m with
  | zero => norm_num [terminal]
  | succ m =>
    rw [Function.iterate_succ_apply']
    rw [(step_formulas mode w k _).accuracy]
    split_ifs <;> exact dyadicDown_le_half _

private lemma foldl_max_nat_mono {α : Type*} (xs : List α) (f g : α → ℕ) {p q : ℕ}
    (hpq : p ≤ q) (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).foldl max p ≤ (xs.map g).foldl max q := by
  induction xs generalizing p q with
  | nil => exact hpq
  | cons x xs ih =>
    exact ih (max_le_max hpq (hfg x (by simp))) (fun y hy ↦ hfg y (by simp [hy]))

private lemma treeCap_antitone (mode : Mode) {w u : ℚ} (k : ℕ)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k) :
    treeCap mode k (params mode u k) ≤ treeCap mode k (params mode w k) := by
  unfold treeCap branchCap
  gcongr
  apply foldl_max_nat_mono _ _ _ le_rfl
  intro h _
  exact stepBranchCap_mono mode k _ _
    (params_positive mode k h hw (by omega))
    (params_positive mode k h (hw.trans_le hwu) (by omega))
    (params_order mode k h hw hwu hu1 hk) (params_accuracy_le_half mode u k h)

private lemma flatMap_prod_mono {α : Type*} (xs : List α) (f g : α → List ℕ)
    (hfg : ∀ x ∈ xs, ((f x).map (· + 2)).prod ≤ ((g x).map (· + 2)).prod) :
    ((xs.flatMap f).map (· + 2)).prod ≤ ((xs.flatMap g).map (· + 2)).prod := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append]
    exact Nat.mul_le_mul (hfg x (by simp)) (ih (fun y hy ↦ hfg y (by simp [hy])))

private lemma ledger_antitone (mode : Mode) {w u : ℚ} (k : ℕ)
    (hw : 0 < w) (hwu : w ≤ u) (hu1 : u ≤ 1 / 2) (hk : 1 ≤ k) :
    ledger mode u k ≤ ledger mode w k := by
  have hu := hw.trans_le hwu
  have hη := etaReq_mono mode k hw hwu hu1 hk
  have hη0 := etaReq_pos mode k hw (by omega)
  have hn := nWeight_antitone mode k hw hwu hu1 hk
  have ht := treeCap_antitone mode k hw hwu hu1 hk
  unfold ledger
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.pow_le_pow_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  unfold ledgerCore
  simp only [List.flatMap_map]
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul
    · apply Nat.mul_le_mul
      · apply flatMap_prod_mono
        intro h _
        obtain ⟨_, _, _, _, _, _, hβ, hγ, hE, hreq, hleak, hsep⟩ :=
          params_order mode k h hw hwu hu1 hk
        have hp := params_positive mode k h hw (by omega)
        have hq := params_positive mode k h hu (by omega)
        have hβp := hp.accuracy
        have hγp := hp.isotropy
        have hEp := hp.moment
        have hreqp := hp.contamination
        have hleakp := hp.leakage
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        gcongr
      · omega
    · omega
  · gcongr

private lemma majorant_power
    (mode : Mode) (w : ℚ) (k a : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hkw : (k : ℚ) * w ≤ 1) (hk : 2 ≤ k) (ha : ⌈1 / w⌉₊ ≤ a) :
    (ledger mode w k + 2) ^ 100 ≤ H a := by
  have hinv : 1 / w ≤ (a : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have htwo : (2 : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr (by linarith [hw.2])
  have ha2 : 2 ≤ a := by exact_mod_cast htwo.trans hinv
  have ha0 : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hwa : 1 / (a : ℚ) ≤ w := by
    rw [div_le_iff₀ ha0]
    have hh := (div_le_iff₀ hw.1).mp hinv
    nlinarith only [hh]
  have hka : k ≤ a := by
    have hh : (k : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr hkw
    exact_mod_cast hh.trans hinv
  have hbound := ledger_antitone mode k (by positivity : 0 < 1 / (a : ℚ))
    hwa hw.2 (by omega)
  let xs := (List.range (a - 1)).map fun j ↦
    (ledger .centered (1 / (a : ℚ)) (j + 2) + 2) *
      (ledger .identical (1 / (a : ℚ)) (j + 2) + 2)
  have hmem : (ledger .centered (1 / (a : ℚ)) k + 2) *
      (ledger .identical (1 / (a : ℚ)) k + 2) ∈ xs := by
    apply List.mem_map.mpr
    refine ⟨k - 2, List.mem_range.mpr (by omega), ?_⟩
    simp only [show k - 2 + 2 = k by omega]
  have hall : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.mul_pos (by omega) (by omega)
  have hprod := List.single_le_prod hall _ hmem
  have hpair : ledger mode (1 / (a : ℚ)) k ≤
      (ledger .centered (1 / (a : ℚ)) k + 2) *
        (ledger .identical (1 / (a : ℚ)) k + 2) := by
    cases mode with
    | centered =>
      exact (Nat.le_add_right _ 2).trans (Nat.le_mul_of_pos_right _ (by omega))
    | identical =>
      exact (Nat.le_add_right _ 2).trans (Nat.le_mul_of_pos_left _ (by omega))
  calc
    (ledger mode w k + 2) ^ 100 ≤ (xs.prod + 2) ^ 100 := by
      gcongr
      exact hbound.trans (hpair.trans hprod)
    _ = H a := by simp only [H, max_eq_right ha2]; rfl

/-- The arithmetic majorant controls every valid schedule independently of dimension. -/
theorem majorant
    (mode : Mode) (w : ℚ) (k a : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hkw : (k : ℚ) * w ≤ 1) (hk : 2 ≤ k) (ha : ⌈1 / w⌉₊ ≤ a) :
    ledger mode w k ≤ H a := by
  have hh := majorant_power mode w k a hw hkw hk ha
  exact (Nat.le_add_right (ledger mode w k) 2).trans
    ((le_self_pow₀ (by omega) (by norm_num)).trans hh)

/-- The separation/corruption cutoff is at least one everywhere. -/
theorem f_ge_one
    (mode : Mode) (x : ℝ) : 1 ≤ f mode x := by
  exact le_max_left _ _

private def parameterNumbers (p : StepParams) : List ℕ :=
  [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
    ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]

private def ledgerNumbers (mode : Mode) (w : ℚ) (k : ℕ) : List ℕ :=
  ((List.range k).map (params mode w k)).flatMap parameterNumbers

private lemma ledger_factors (mode : Mode) (w : ℚ) (k : ℕ) :
    ((ledgerNumbers mode w k).map (· + 2)).prod ≤ ledger mode w k ∧
      nWeight mode w k ≤ ledger mode w k ∧ ⌈1 / etaReq mode w k⌉₊ ≤ ledger mode w k := by
  let P := ((ledgerNumbers mode w k).map (· + 2)).prod
  have hP : 1 ≤ P := by
    apply List.one_le_prod_of_one_le
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    omega
  let xs := [P, nWeight mode w k + 2, treeCap mode k (params mode w k) + 2,
    ⌈1 / etaReq mode w k⌉₊ + 2]
  have hall : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  have hfac (x : ℕ) (hx : x ∈ xs) : x ≤ ledger mode w k := by
    have hh := List.single_le_prod hall x hx
    dsimp only [xs, P, ledgerNumbers] at hh
    unfold parameterNumbers at hh
    apply le_trans _ (ledgerCore_le mode w k)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ledgerCore, mul_assoc] using hh
  exact ⟨hfac P (by simp [xs]),
    (by omega : nWeight mode w k ≤ nWeight mode w k + 2).trans
      (hfac _ (by simp [xs])),
    (by omega : ⌈1 / etaReq mode w k⌉₊ ≤ ⌈1 / etaReq mode w k⌉₊ + 2).trans
      (hfac _ (by simp [xs]))⟩

private lemma ledger_entry (mode : Mode) (w : ℚ) (k h x : ℕ) (hh : h < k)
    (hx : x ∈ parameterNumbers (params mode w k h)) : x ≤ ledger mode w k := by
  have hall : ∀ y ∈ (ledgerNumbers mode w k).map (· + 2), 1 ≤ y := by
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    omega
  have hmem : x + 2 ∈ (ledgerNumbers mode w k).map (· + 2) := by
    apply List.mem_map.mpr
    refine ⟨x, List.mem_flatMap.mpr ?_, rfl⟩
    refine ⟨params mode w k h, ?_, hx⟩
    exact List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩
  exact (by omega : x ≤ x + 2).trans
    ((List.single_le_prod hall _ hmem).trans (ledger_factors mode w k).1)

private lemma core_factors (mode : Mode) (w : ℚ) (k : ℕ) :
    ((ledgerNumbers mode w k).map (· + 2)).prod ≤ ledgerCore mode w k ∧
      nWeight mode w k ≤ ledgerCore mode w k ∧ ⌈1 / etaReq mode w k⌉₊ ≤ ledgerCore mode w k := by
  let P := ((ledgerNumbers mode w k).map (· + 2)).prod
  have hP : 1 ≤ P := by
    apply List.one_le_prod_of_one_le
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    omega
  let xs := [P, nWeight mode w k + 2, treeCap mode k (params mode w k) + 2,
    ⌈1 / etaReq mode w k⌉₊ + 2]
  have hall : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  have hfac (x : ℕ) (hx : x ∈ xs) : x ≤ ledgerCore mode w k := by
    have hh := List.single_le_prod hall x hx
    dsimp only [xs, P, ledgerNumbers] at hh
    unfold parameterNumbers at hh
    simpa only [List.prod_cons, List.prod_nil, mul_one, ledgerCore, mul_assoc] using hh
  exact ⟨hfac P (by simp [xs]),
    (by omega : nWeight mode w k ≤ nWeight mode w k + 2).trans
      (hfac _ (by simp [xs])),
    (by omega : ⌈1 / etaReq mode w k⌉₊ ≤ ⌈1 / etaReq mode w k⌉₊ + 2).trans
      (hfac _ (by simp [xs]))⟩

private lemma core_entry (mode : Mode) (w : ℚ) (k h x : ℕ) (hh : h < k)
    (hx : x ∈ parameterNumbers (params mode w k h)) : x ≤ ledgerCore mode w k := by
  have hall : ∀ y ∈ (ledgerNumbers mode w k).map (· + 2), 1 ≤ y := by
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    omega
  have hmem : x + 2 ∈ (ledgerNumbers mode w k).map (· + 2) := by
    apply List.mem_map.mpr
    refine ⟨x, List.mem_flatMap.mpr ?_, rfl⟩
    refine ⟨params mode w k h, ?_, hx⟩
    exact List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩
  exact (by omega : x ≤ x + 2).trans
    ((List.single_le_prod hall _ hmem).trans (core_factors mode w k).1)

private lemma reciprocal_le_ledger (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k) :
    1 / (params mode w k h).leakage ≤ (ledger mode w k : ℚ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast ledger_entry mode w k h _ hh (by simp [parameterNumbers])

private lemma separation_le_ledger (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k) :
    (params mode w k h).separation ≤ (ledger mode w k : ℚ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast ledger_entry mode w k h _ hh (by simp [parameterNumbers])

private lemma large_power (x : ℕ) : 128 * x ≤ (x + 2) ^ 100 := by
  have h2 : 2 ≤ x + 2 := by omega
  have hp : 128 ≤ (x + 2) ^ 7 := by
    exact (by norm_num : 128 ≤ (2 : ℕ) ^ 7).trans (Nat.pow_le_pow_left h2 7)
  have hh : 128 * (x + 2) ≤ (x + 2) ^ 8 := by
    rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_succ]
    gcongr
  exact (by nlinarith : 128 * x ≤ 128 * (x + 2)).trans
    (hh.trans (Nat.pow_le_pow_right (by omega) (by norm_num)))

private lemma f_dominates (mode : Mode) {w : ℚ} (k : ℕ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1) :
    (128 * ledger mode w k : ℝ) ≤ f mode (1 / w) := by
  have heq : ⌈1 / (w : ℝ)⌉₊ = ⌈1 / w⌉₊ := by
    rw [← Rat.cast_one, ← Rat.cast_div]
    exact Nat.map_ceil (Rat.castHom ℝ) Rat.cast_strictMono _
  have hh := majorant_power mode w k (max 2 ⌈1 / w⌉₊) hw hkw hk (le_max_right _ _)
  have hp := (large_power (ledger mode w k)).trans hh
  have hf : (H (max 2 ⌈1 / w⌉₊) : ℝ) ≤ f mode (1 / w) := by
    unfold f
    rw [heq]
    have hle : (H (max 2 ⌈1 / w⌉₊) : ℝ) ≤ (H (max 2 ⌈1 / w⌉₊) + 1 : ℕ) := by
      exact_mod_cast Nat.le_succ (H (max 2 ⌈1 / w⌉₊))
    exact hle.trans (le_max_right _ _)
  exact (show (128 * ledger mode w k : ℝ) ≤ (H (max 2 ⌈1 / w⌉₊) : ℝ) by
    exact_mod_cast hp).trans hf

private lemma dyadicUp_ge (x : ℚ) : x ≤ dyadicUp x := by
  unfold dyadicUp
  apply (Nat.le_ceil x).trans
  apply (show (⌈x⌉₊ : ℚ) ≤ max 1 (⌈x⌉₊ : ℕ) from by exact_mod_cast le_max_right 1 ⌈x⌉₊).trans
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (max 1 ⌈x⌉₊)

private lemma dyadicUp_one_le (x : ℚ) : 1 ≤ dyadicUp x := by
  unfold dyadicUp
  exact one_le_pow₀ (by norm_num)

private lemma dyadicDown_le {x : ℚ} (hx : 0 < x) : dyadicDown x ≤ x := by
  rw [dyadicDown, ite_eq_left hx]
  change ((2 : ℚ) ^ _)⁻¹ ≤ x
  apply (inv_le_comm₀ (by positivity) hx).mpr
  have hceil : 1 / x ≤ (⌈1 / x⌉₊ : ℚ) := Nat.le_ceil _
  have hpow : (⌈1 / x⌉₊ : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 ⌈1 / x⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈1 / x⌉₊
  simpa only [one_div] using hceil.trans
    (hpow.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)))

private lemma dyadicDown_le_of_pos {x : ℚ} (hx : 0 < dyadicDown x) :
    dyadicDown x ≤ x := by
  have hx0 : 0 < x := by
    by_contra hn
    simp only [dyadicDown, ite_eq_right hn, lt_self_iff_false] at hx
  exact dyadicDown_le hx0

private lemma sqrtUp_sq (x : ℚ) : x ≤ sqrtUp x ^ 2 := by
  have hceil := Nat.le_ceil (max 0 x)
  have hs := Nat.lt_succ_sqrt ⌈max 0 x⌉₊
  have hnat : (⌈max 0 x⌉₊ : ℚ) ≤ sqrtUp x ^ 2 := by
    unfold sqrtUp
    have hs' : ⌈max 0 x⌉₊ ≤ (Nat.sqrt ⌈max 0 x⌉₊ + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one, pow_two] using hs.le
    exact_mod_cast hs'
  exact (le_max_right 0 x).trans (hceil.trans hnat)

private lemma sqrt_le_sqrtUp (x : ℚ) : Real.sqrt x ≤ (sqrtUp x : ℝ) := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by exact_mod_cast (sqrtUp_pos x).le, by exact_mod_cast sqrtUp_sq x⟩

private lemma step_leakage_bound (mode : Mode) {w : ℚ} (k : ℕ) (next : StepParams)
    (hw : 0 < w) (hk : 0 < k) (hn : 0 < next.leakage) :
    (step mode w k next).leakage ≤ next.leakage / 4 ∧
      (step mode w k next).leakage ≤ w * (step mode w k next).contamination / 128 ∧
      (step mode w k next).leakage ≤ w * (step mode w k next).windowMass / 1024 := by
  have hp := (step_positive mode k next hw hk hn).1.leakage
  rw [(step_formulas mode w k next).leakage] at hp ⊢
  have hh := dyadicDown_le_of_pos hp
  exact ⟨hh.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hh.trans (min_le_left _ _), hh.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

private lemma params_leakage_mono (mode : Mode) {w : ℚ} (k : ℕ)
    (hw : 0 < w) (hk : 0 < k) : Monotone fun h ↦ (params mode w k h).leakage := by
  apply monotone_nat_of_le_succ
  intro h
  by_cases hh : h < k - 1
  · rw [params_succ mode w k h hh]
    have hp := step_leakage_bound mode k (params mode w k (h + 1)) hw hk
      (params_positive mode k (h + 1) hw hk).leakage
    have hn := (params_positive mode k (h + 1) hw hk).leakage
    exact hp.1.trans (by linarith)
  · have hz : k - 1 - h = 0 := by omega
    have hz' : k - 1 - (h + 1) = 0 := by omega
    simp only [params, hz, hz', Function.iterate_zero_apply, le_refl]

private lemma params_leakage_small (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w) (hk : 0 < k) (hh : h < k) :
    (params mode w k h).leakage ≤ w * (2 / 10 ^ 10) / 128 := by
  have hp := params_leakage_mono mode k hw hk (show h ≤ k - 1 by omega)
  simpa only [params, Nat.sub_self, Function.iterate_zero_apply, terminal] using hp

private lemma params_leakage_contamination (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w) (hk : 0 < k) :
    (params mode w k h).leakage ≤ w * (params mode w k h).contamination / 128 := by
  by_cases hh : h < k - 1
  · rw [params_succ mode w k h hh]
    exact (step_leakage_bound mode k (params mode w k (h + 1)) hw hk
      (params_positive mode k (h + 1) hw hk).leakage).2.1
  · simp only [params, show k - 1 - h = 0 by omega, Function.iterate_zero_apply,
      terminal, le_refl]

private lemma centered_accuracy_bound {w : ℚ} {k : ℕ} {next p : StepParams}
    (hw : 0 < w ∧ w ≤ 1 / 2) (hp : StepFormulas .centered w k next p)
    (hpos : PositiveParams p) (htail : 0 < p.tail) :
    p.subspaceAccuracy ≤ (128 * (4 / w))⁻¹ ∧ p.subspaceAccuracy ≤ 1 / 100 := by
  have hw0 := hw.1
  have hK : 1 ≤ p.K := by
    rw [hp.K]
    exact dyadicUp_one_le _
  have ht : p.tail ≤ w / 4096 := by
    rw [hp.tail]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hbase : p.tail / (1024 * p.K ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    have hKsq := one_le_pow₀ hK (n := 2)
    linarith [hw.2]
  have hb0 : 0 ≤ p.tail / (1024 * p.K ^ 2) := by positivity
  have hβ := hpos.accuracy
  rw [hp.accuracy] at hβ
  have hh := dyadicDown_le_of_pos hβ
  have hbound : p.subspaceAccuracy ≤ (128 * (4 / w))⁻¹ := by
    rw [hp.accuracy]
    apply hh.trans
    calc
      _ ≤ (128 * (4 / w))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left (pow_le_one₀ hb0 hbase) (by positivity)
      _ = _ := mul_one _
  have heq : (128 * (4 / w))⁻¹ = w / 512 := by field_simp; ring
  exact ⟨hbound, hbound.trans (by rw [heq]; linarith [hw.2])⟩

private lemma formulas_accuracy_bound (mode : Mode) {w : ℚ} {k : ℕ}
    {next p : StepParams} (hw : 0 < w ∧ w ≤ 1 / 2)
    (hp : StepFormulas mode w k next p) (hpos : PositiveParams p)
    (htail : 0 < p.tail) : p.subspaceAccuracy ≤ 1 / 100 := by
  cases mode with
  | centered => exact (centered_accuracy_bound hw hp hpos htail).2
  | identical =>
    have hh := hpos.accuracy
    rw [hp.accuracy] at hh
    rw [hp.accuracy]
    exact (dyadicDown_le_of_pos hh).trans (min_le_left _ _)

private lemma centered_separation_bounds {w : ℚ} {k : ℕ} {next p : StepParams}
    (hw : 0 < w) (hp : StepFormulas .centered w k next p)
    (hpos : PositiveParams p) :
    (4 / w : ℝ) < (p.separation : ℝ) ^ 2 * 3 * p.subspaceAccuracy ^ 8 ∧
      (2 * Real.sqrt (10000 * (p.sigmaSq : ℝ) / (w / 2) + 10)) * (4 / w) ≤
        9 * p.separation * p.subspaceAccuracy ^ 16 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hβ := hpos.accuracy
  have hβR : (0 : ℝ) < p.subspaceAccuracy := by exact_mod_cast hβ
  have hs : 2 * sqrtUp ((4 / w) / (3 * p.subspaceAccuracy ^ 8)) ≤ p.separation := by
    rw [hp.separation]
    exact (le_max_left _ _).trans (dyadicUp_ge _)
  have hr : 4 * sqrtUp (10000 * p.sigmaSq / (w / 2) + 10) * (4 / w) /
      (9 * p.subspaceAccuracy ^ 16) ≤ p.separation := by
    rw [hp.separation]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (dyadicUp_ge _)
  have hs0 := sqrtUp_pos ((4 / w) / (3 * p.subspaceAccuracy ^ 8))
  have hs2 := sqrtUp_sq ((4 / w) / (3 * p.subspaceAccuracy ^ 8))
  have hsq : (4 / w) * 4 ≤ p.separation ^ 2 * 3 * p.subspaceAccuracy ^ 8 := by
    have hh := (div_le_iff₀ (by positivity)).mp hs2
    have hssq : 4 * sqrtUp ((4 / w) / (3 * p.subspaceAccuracy ^ 8)) ^ 2 ≤
        p.separation ^ 2 := by nlinarith only [hs, hs0]
    have hm := mul_le_mul_of_nonneg_right hssq
      (by positivity : 0 ≤ 3 * p.subspaceAccuracy ^ 8)
    have hc : (0 : ℚ) < 4 / w := by positivity
    nlinarith only [hh, hm, hc]
  constructor
  · have hh : (4 / w : ℚ) < p.separation ^ 2 * 3 * p.subspaceAccuracy ^ 8 := by
      have hc : (0 : ℚ) < 4 / w := by positivity
      linarith
    exact_mod_cast hh
  · have hh := (div_le_iff₀ (by positivity)).mp hr
    have hhR : 4 * (sqrtUp (10000 * p.sigmaSq / (w / 2) + 10) : ℝ) * (4 / w) ≤
        9 * p.separation * p.subspaceAccuracy ^ 16 := by
      exact_mod_cast (show 4 * sqrtUp (10000 * p.sigmaSq / (w / 2) + 10) * (4 / w) ≤
        9 * p.separation * p.subspaceAccuracy ^ 16 by nlinarith only [hh])
    have hroot := sqrt_le_sqrtUp (10000 * p.sigmaSq / (w / 2) + 10)
    push_cast at hroot
    have hm := mul_le_mul_of_nonneg_right hroot (by positivity : (0 : ℝ) ≤ 4 / w)
    have hn := Real.sqrt_nonneg (10000 * (p.sigmaSq : ℝ) / (w / 2) + 10)
    nlinarith only [hhR, hm, mul_nonneg hn (by positivity : (0 : ℝ) ≤ 4 / w)]

private lemma centered_ready {w : ℚ} {k : ℕ} {next p : StepParams}
    (hw : 0 < w ∧ w ≤ 1 / 2) (hp : StepFormulas .centered w k next p)
    (hpos : PositiveParams p) (htail : 0 < p.tail) :
    p.windowMass = 1 / 2 ∧ 32 / p.straddle ≤ p.K ∧
      8 * (40 / w) * sqrtUp (1 / p.straddle) ≤ p.WF ∧
      4 * p.WF ≤ p.DF ∧ 4 * (40 / w) ^ 2 ≤ p.tail * p.DF ^ 2 ∧
      2 * (k - 1 : ℚ) * (2 * p.DF + 3 * p.WF) + 1 ≤ p.R ∧
      p.subspaceAccuracy ≤ 1 / (128 * (4 / w)) ∧
      p.subspaceAccuracy ≤ (128 * (4 / w))⁻¹ *
        (p.tail / (1024 * p.K ^ 2)) ^ (2 * (k - 1)) ∧
      p.isotropy = Centered.gammaStar (w / 2) p.subspaceAccuracy ∧
      p.momentError = Centered.etaStar (w / 2) p.subspaceAccuracy ∧
      (4 / w : ℝ) < (p.separation : ℝ) ^ 2 * 3 * p.subspaceAccuracy ^ 8 ∧
      (2 * Real.sqrt (10000 * (p.sigmaSq : ℝ) / (w / 2) + 10)) * (4 / w) ≤
        9 * p.separation * p.subspaceAccuracy ^ 16 := by
  have hw0 := hw.1
  have hacc := centered_accuracy_bound hw hp hpos htail
  have hβ := hpos.accuracy
  rw [hp.accuracy] at hβ
  have hsep := centered_separation_bounds hw.1 hp hpos
  have hDF : 4 * (40 / w) * sqrtUp (1 / p.tail) ≤ p.DF := by
    rw [hp.DF]
    exact (le_max_right _ _).trans (dyadicUp_ge _)
  have htDF : 4 * (40 / w) ^ 2 ≤ p.tail * p.DF ^ 2 := by
    have hs := sqrtUp_sq (1 / p.tail)
    have hs0 := sqrtUp_pos (1 / p.tail)
    have hsf := (div_le_iff₀ htail).mp hs
    have hDFsq : 16 * (40 / w) ^ 2 * sqrtUp (1 / p.tail) ^ 2 ≤ p.DF ^ 2 := by
      have h0 : 0 ≤ 4 * (40 / w) * sqrtUp (1 / p.tail) := by positivity
      have hh := pow_le_pow_left₀ h0 hDF 2
      nlinarith only [hh]
    have hmul := mul_le_mul_of_nonneg_left hDFsq htail.le
    have hmul' := mul_le_mul_of_nonneg_left hsf (sq_nonneg (40 / w))
    nlinarith only [hmul, hmul', sq_nonneg (40 / w)]
  refine ⟨?_, ?_, ?_, ?_, htDF, ?_, ?_, ?_, ?_, ?_, hsep.1, hsep.2⟩
  · simpa only [ite_true] using hp.window
  · rw [hp.K]
    exact dyadicUp_ge _
  · rw [hp.WF]
    exact dyadicUp_ge _
  · rw [hp.DF]
    exact (le_max_left _ _).trans (dyadicUp_ge _)
  · rw [hp.R]
    exact dyadicUp_ge _
  · simpa only [one_div] using hacc.1
  · rw [hp.accuracy]
    exact dyadicDown_le_of_pos hβ
  · simpa only [ite_true] using hp.isotropy
  · simpa only [ite_true] using hp.moment

private lemma identical_ready {w : ℚ} {k : ℕ} {next p : StepParams}
    (hw : 0 < w) (hk : 0 < k) (hp : StepFormulas .identical w k next p)
    (hpos : PositiveParams p) (htail : 0 < p.tail) :
    p.windowMass = (1 / (16 * k : ℚ)) * (p.straddle / 2) ^ 9 / 16 ∧
      40 / (w / 2) ^ 2 ≤ p.R ^ 2 ∧
      200 * (k : ℚ) ^ 2 * p.subspaceAccuracy ^ 2 ≤ p.tail ∧
      p.isotropy = IdCov.gammaStar p.subspaceAccuracy ∧
      p.momentError = IdCov.etaStar w p.subspaceAccuracy / 4 ∧
      16 ≤ p.separation ^ 2 * w * IdCov.tauStar p.subspaceAccuracy := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hβ := hpos.accuracy
  rw [hp.accuracy] at hβ
  have hβle : p.subspaceAccuracy ≤ 1 / sqrtUp (10 ^ 6 * (k : ℚ) ^ 2 / p.tail) := by
    rw [hp.accuracy]
    exact (dyadicDown_le_of_pos hβ).trans (min_le_right _ _)
  have hR : sqrtUp 40 / (w / 2) ≤ p.R := by
    rw [hp.R]
    exact dyadicUp_ge _
  have hR2 : 40 / (w / 2) ^ 2 ≤ p.R ^ 2 := by
    have hsq := sqrtUp_sq 40
    have h0 := sqrtUp_pos 40
    calc
      _ ≤ (sqrtUp 40 / (w / 2)) ^ 2 := by simp only [div_pow]; gcongr
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hR 2
  have hβ2 : 200 * (k : ℚ) ^ 2 * p.subspaceAccuracy ^ 2 ≤ p.tail := by
    let s := sqrtUp (10 ^ 6 * (k : ℚ) ^ 2 / p.tail)
    have hs : 0 < s := sqrtUp_pos _
    have hssq := sqrtUp_sq (10 ^ 6 * (k : ℚ) ^ 2 / p.tail)
    have hbudget : 10 ^ 6 * (k : ℚ) ^ 2 ≤ s ^ 2 * p.tail :=
      (div_le_iff₀ htail).mp hssq
    have hsmall : p.subspaceAccuracy ^ 2 * s ^ 2 ≤ 1 := by
      have hh : p.subspaceAccuracy * s ≤ 1 := (le_div_iff₀ hs).mp hβle
      have h0 : 0 ≤ p.subspaceAccuracy * s := by have hb := hpos.accuracy; positivity
      nlinarith only [hh, h0]
    have hm := mul_le_mul_of_nonneg_left hbudget (sq_nonneg p.subspaceAccuracy)
    have hm' := mul_le_mul_of_nonneg_right hsmall htail.le
    nlinarith only [hm, hm', sq_nonneg (k : ℚ), sq_nonneg p.subspaceAccuracy]
  have hsep : 16 ≤ p.separation ^ 2 * w * IdCov.tauStar p.subspaceAccuracy := by
    have hβ0 := hpos.accuracy
    have hτ : 0 < IdCov.tauStar p.subspaceAccuracy := by
      unfold IdCov.tauStar IdCov.epsilonR
      positivity
    have hroot := sqrtUp_pos (32 / (w * IdCov.tauStar p.subspaceAccuracy))
    have hs : sqrtUp (32 / (w * IdCov.tauStar p.subspaceAccuracy)) ≤ p.separation := by
      rw [hp.separation]
      exact dyadicUp_ge _
    have hs2 := sqrtUp_sq (32 / (w * IdCov.tauStar p.subspaceAccuracy))
    have hh := (div_le_iff₀ (mul_pos hw hτ)).mp hs2
    have hsq := pow_le_pow_left₀ hroot.le hs 2
    have hm := mul_le_mul_of_nonneg_right hsq (mul_pos hw hτ).le
    nlinarith only [hh, hm]
  refine ⟨?_, hR2, hβ2, ?_, ?_, hsep⟩
  · simpa using hp.window
  · simpa using hp.isotropy
  · simpa using hp.moment

private lemma formulas_ready (mode : Mode) {w : ℚ} {k : ℕ} {next p : StepParams}
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 0 < k)
    (hp : StepFormulas mode w k next p) (hpos : PositiveParams p)
    (hφ : 0 < p.straddle) (htail : 0 < p.tail)
    (hleak : p.leakage ≤ next.leakage / 4 ∧
      p.leakage ≤ w * p.contamination / 128 ∧
      p.leakage ≤ w * p.windowMass / 1024) : StepReady mode k p next := by
  have hβ := formulas_accuracy_bound mode hw hp hpos htail
  have hcont := hpos.contamination
  rw [hp.contamination] at hcont
  have hh := dyadicDown_le_of_pos hcont
  rw [← hp.contamination] at hh
  rcases le_min_iff.mp hh with ⟨h1, hh⟩
  rcases le_min_iff.mp hh with ⟨h2, hh⟩
  rcases le_min_iff.mp hh with ⟨h3, hh⟩
  rcases le_min_iff.mp hh with ⟨h4, hrest⟩
  have h2' : p.contamination ≤ w / 800 := by convert h2 using 1; ring
  have hbound : p.contamination ≤ min (1 / (64000 * p.sigmaSq))
      (min (w / 800) (min (p.isotropy ^ 2 / (10 ^ 10 * p.sigmaSq))
        (min (p.verifyMass / 64) (min (p.straddle / 64)
          (min (w / 4096) (w ^ 2 / 10 ^ 8)))))) :=
    le_min h1 (le_min h2' (le_min h3 hrest))
  have hframe : 0 < p.frameAccuracy := by
    rw [hp.frame]
    exact dyadicDown_pos (div_pos hpos.isotropy (by norm_num))
  have hframele : p.frameAccuracy ≤ p.isotropy / 10000 := by
    rw [hp.frame]
    exact dyadicDown_le (div_pos hpos.isotropy (by norm_num))
  unfold StepReady
  rw [hp.weight]
  refine ⟨hw.1, hw.2, hpos.accuracy, hβ, hφ, htail, hp.straddle,
    hleak.1, hleak.2.1, hleak.2.2, hp.verify, ?_, hp.sigma, hbound,
    hframe, hframele, ?_⟩
  · exact le_of_eq hp.tail
  · cases mode with
    | centered =>
      obtain ⟨hm, hK, hWF, hDF, htDF, hR, hβ1, hβ2, hγ, hE, hs1, hs2⟩ :=
        centered_ready hw hp hpos htail
      exact ⟨hm, hK, hWF, hDF, htDF, hR, hβ1, hβ2, hγ, hE,
        by simpa only [momentBound, ite_true, show (10 : ℚ) ^ 4 = 10000 by norm_num] using h4,
        hs1, hs2⟩
    | identical =>
      obtain ⟨hm, hR, hβ2, hγ, hE, hs⟩ := identical_ready hw.1 hk hp hpos htail
      exact ⟨hm, hR, hβ2, hγ, hE,
        by simpa [momentBound, show (10 : ℚ) ^ 4 = 10000 by norm_num] using h4, hs⟩

private lemma step_ready (mode : Mode) {w : ℚ} (k : ℕ) (next : StepParams)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 0 < k) (hn : 0 < next.leakage) :
    StepReady mode k (step mode w k next) next := by
  have hp := step_positive mode k next hw.1 hk hn
  exact formulas_ready mode hw hk (step_formulas mode w k next) hp.1 hp.2.1 hp.2.2
    (step_leakage_bound mode k next hw.1 hk hn)

private lemma foldl_min_le_initial (xs : List ℚ) (q : ℚ) : xs.foldl min q ≤ q := by
  induction xs generalizing q with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih _).trans (min_le_left _ _)

private lemma foldl_min_le_entry (xs : List ℚ) (q x : ℚ) (hx : x ∈ xs) :
    xs.foldl min q ≤ x := by
  induction xs generalizing q with
  | nil => simp at hx
  | cons y xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (foldl_min_le_initial xs _).trans (min_le_right _ _)
    · exact ih _ hx

private lemma etaReq_base (mode : Mode) (w : ℚ) (k : ℕ) :
    etaReq mode w k ≤ min (w / 10000)
      (min (1 / 10 ^ 8) (min ((params mode w k 0).leakage / 128)
        (if mode = .identical then 1 / (16000 * k) else 1))) :=
  (foldl_min_le_initial _ _).trans (min_le_right _ _)

private lemma etaReq_entry (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k - 1) :
    etaReq mode w k ≤ min (w * (params mode w k h).windowMass / 10000)
      (min ((params mode w k h).straddle ^ 2 / (1000 * (params mode w k h).K ^ 2))
        (min ((params mode w k h).tail ^ 2 / 10 ^ 6)
          (min (w * (params mode w k h).isotropy / 10000)
            (1 / (100 * sqrtUp (1 / (params mode w k h).momentError)))))) := by
  apply le_trans (foldl_min_le_entry _ _ _
    (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩))
  exact min_le_right _ _

private lemma leakageBudget_bound (mode : Mode) {w : ℚ} (k : ℕ) (η : ℝ)
    (hw : 0 < w) (hk : 0 < k)
    (hη : η ≤ ((params mode w k 0).leakage : ℝ) / 128) :
    ∀ h, h < k → leakageBudget (params mode w k) η h ≤ (params mode w k h).leakage := by
  intro h
  induction h with
  | zero =>
    intro _
    simpa only [leakageBudget, List.range_zero, List.map_nil, List.sum_nil] using
      (show (0 : ℝ) ≤ (params mode w k 0).leakage by
        exact_mod_cast (params_positive mode k 0 hw hk).leakage.le)
  | succ h ih =>
    intro hh
    have hi := ih (by omega)
    have hl := (step_leakage_bound mode k (params mode w k (h + 1)) hw hk
      (params_positive mode k (h + 1) hw hk).leakage).1
    rw [← params_succ mode w k h (by omega)] at hl
    have hφ : (params mode w k h).straddle = (params mode w k (h + 1)).leakage / 4 := by
      rw [params_succ mode w k h (by omega)]
      rfl
    have hm := params_leakage_mono mode k hw hk (show 0 ≤ h + 1 by omega)
    have hnext := (params_positive mode k (h + 1) hw hk).leakage
    have hlR : ((params mode w k h).leakage : ℝ) ≤
        (params mode w k (h + 1)).leakage / 4 := by exact_mod_cast hl
    have hφR : ((params mode w k h).straddle : ℝ) =
        (params mode w k (h + 1)).leakage / 4 := by exact_mod_cast hφ
    have hmR : ((params mode w k 0).leakage : ℝ) ≤
        (params mode w k (h + 1)).leakage := by exact_mod_cast hm
    have hnR : (0 : ℝ) < (params mode w k (h + 1)).leakage := by exact_mod_cast hnext
    simp only [leakageBudget, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton] at hi ⊢
    linarith only [hi, hlR, hφR, hmR, hnR, hη]

private lemma params_ready (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 0 < k) (hh : h < k - 1) :
    StepReady mode k (params mode w k h) (params mode w k (h + 1)) := by
  rw [params_succ mode w k h hh]
  exact step_ready mode k _ hw hk (params_positive mode k (h + 1) hw.1 hk).leakage

private lemma params_window_bound (mode : Mode) {w : ℚ} (k h : ℕ)
    (hw : 0 < w) (hk : 0 < k) (hh : h < k - 1) :
    (params mode w k h).leakage ≤ w * (params mode w k h).windowMass / 1024 := by
  rw [params_succ mode w k h hh]
  exact (step_leakage_bound mode k _ hw hk
    (params_positive mode k (h + 1) hw hk).leakage).2.2

private lemma exp_neg_two_lower : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
  have hh : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 2)]
  norm_num
  exact hh

private lemma params_sound (mode : Mode) {w : ℚ} (k h : ℕ) (ε η Φ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 0 < k) (hh : h < k - 1)
    (he : ε ≤ ((params mode w k 0).leakage : ℝ) / 128)
    (hη : η ≤ (etaReq mode w k : ℝ))
    (hΦ : Φ ≤ (params mode w k h).leakage) :
    SoundConditions (params mode w k h) ε η Φ := by
  let p := params mode w k h
  have hp := params_positive mode k h hw.1 hk
  have hpφ : 0 < p.straddle := by
    dsimp only [p]
    rw [params_succ mode w k h hh]
    exact (step_positive mode k _ hw.1 hk
      (params_positive mode k (h + 1) hw.1 hk).leakage).2.1
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR1 : (w : ℝ) ≤ 1 / 2 := by
    have hh : (w : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hw.2
    norm_num at hh ⊢
    exact hh
  have hwindow : (0 : ℝ) < p.windowMass := by exact_mod_cast hp.window
  have hφR : (0 : ℝ) < p.straddle := by exact_mod_cast hpφ
  have hleak := params_leakage_small mode k h hw.1 hk (by omega)
  have hsmall : (p.leakage : ℝ) ≤ w * (2 / 10 ^ 10) / 128 := by
    dsimp only [p]
    have hR : ((params mode w k h).leakage : ℝ) ≤
        ((w * (2 / 10 ^ 10) / 128 : ℚ) : ℝ) := Rat.cast_le.mpr hleak
    push_cast at hR
    exact hR
  have hwin := params_window_bound mode k h hw.1 hk hh
  have hwinR : (p.leakage : ℝ) ≤ w * p.windowMass / 1024 := by exact_mod_cast hwin
  have hm := params_leakage_mono mode k hw.1 hk (show 0 ≤ h by omega)
  have hmR : ((params mode w k 0).leakage : ℝ) ≤ p.leakage := by exact_mod_cast hm
  have hbase := (etaReq_base mode w k)
  have hb : (etaReq mode w k : ℝ) ≤ ((params mode w k 0).leakage : ℝ) / 128 := by
    exact_mod_cast hbase.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hηleak := hη.trans hb
  have heη : ε + η ≤ (p.leakage : ℝ) / 64 := by linarith only [he, hηleak, hmR]
  have hentry : (etaReq mode w k : ℝ) ≤
      (w : ℝ) * p.windowMass / 10000 := by
    exact_mod_cast (etaReq_entry mode w k h hh).trans (min_le_left _ _)
  have hηwin := hη.trans hentry
  have hφ : (p.straddle : ℝ) ≤ w * (2 / 10 ^ 10) / 512 := by
    have hn := params_leakage_small mode k (h + 1) hw.1 hk (by omega)
    have heq : p.straddle = (params mode w k (h + 1)).leakage / 4 := by
      dsimp only [p]
      rw [params_succ mode w k h hh]
      rfl
    have hq : p.straddle ≤ w * (2 / 10 ^ 10) / 512 := by rw [heq]; linarith
    have hR : (p.straddle : ℝ) ≤ ((w * (2 / 10 ^ 10) / 512 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hq
    push_cast at hR
    exact hR
  have hηK : η ≤ (p.straddle : ℝ) ^ 2 / (1000 * (p.K : ℝ) ^ 2) := by
    have hh := (etaReq_entry mode w k h hh).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hhR : (etaReq mode w k : ℝ) ≤
        (p.straddle : ℝ) ^ 2 / (1000 * (p.K : ℝ) ^ 2) := by exact_mod_cast hh
    exact hη.trans hhR
  have hWF : 8 * (40 / w) * sqrtUp (1 / p.straddle) ≤ p.WF := by
    dsimp only [p]
    rw [params_succ mode w k h hh]
    rw [(step_formulas mode w k _).WF]
    exact dyadicUp_ge _
  have hWFR : 8 * (40 / (w : ℝ)) / Real.sqrt p.straddle ≤ p.WF := by
    have hs := sqrt_le_sqrtUp (1 / p.straddle)
    push_cast at hs
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one] at hs
    calc
      _ = 8 * (40 / (w : ℝ)) * (1 / Real.sqrt p.straddle) := by ring
      _ ≤ 8 * (40 / (w : ℝ)) * (sqrtUp (1 / p.straddle) : ℝ) := by gcongr
      _ ≤ _ := by exact_mod_cast hWF
  have hverify : p.verifyMass = p.w * p.windowMass / 8 := by
    have hr := params_ready mode k h hw hk hh
    exact hr.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [p] at *
  unfold SoundConditions
  rw [params_weight mode w k h]
  refine ⟨hw.1, hpφ, ?_, ?_, ?_, ?_, ?_, by simpa only [params_weight] using hverify, hηK, hWFR⟩
  · exact (by nlinarith only [hφ, hwR1] : (p.straddle : ℝ) ≤ 1 / 9).trans exp_neg_two_lower
  · nlinarith only [hΦ, hwinR, hwR1, hwindow]
  · linarith only [heη, hwinR, mul_pos hwR hwindow]
  · nlinarith only [hηwin, hwR1, hwindow]
  · linarith only [hΦ, hsmall, hφ, hηleak, hmR, he, hwR]

private lemma mixture_weight_sum {k d : ℕ} (M : Mixture k d) (w : ℚ)
    (hM : M.Valid) (hwj : ∀ i, (w : ℝ) ≤ M.w i) : (k : ℚ) * w ≤ 1 := by
  have hh : (k : ℝ) * w ≤ 1 := by
    calc
      (k : ℝ) * w = ∑ _ : Fin k, (w : ℝ) := by simp
      _ ≤ ∑ i : Fin k, M.w i := Finset.sum_le_sum (fun i _ ↦ hwj i)
      _ = 1 := hM.sum_w
  exact_mod_cast hh

private lemma sample_weight_bounds (mode : Mode) {w : ℚ} (k n : ℕ)
    (hw : 0 < w) (hk : 0 < k) (hn : nWeight mode w k ≤ n) :
    0 < n ∧ 1 / (n : ℝ) ≤ ((params mode w k 0).leakage : ℝ) / 128 ∧
      (10 : ℝ) ^ 10 ≤ (w : ℝ) * n / 4 := by
  have hp := (params_positive mode k 0 hw hk).leakage
  have hceil : max (128 / (params mode w k 0).leakage) (max (8 / w)
      (max (4 * 10 ^ 10 / w) (((List.range k).map fun h ↦
        8 * 64000 * (params mode w k h).sigmaSq / w).foldl max 0))) ≤ (n : ℚ) :=
    (show _ ≤ (nWeight mode w k : ℚ) from Nat.le_ceil _).trans
      (show (nWeight mode w k : ℚ) ≤ n by exact_mod_cast hn)
  have hl := (le_max_left _ _).trans hceil
  have hs := ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _))).trans hceil
  have hnq : (0 : ℚ) < n := (div_pos (by norm_num) hp).trans_le hl
  have hmul := (div_le_iff₀ hp).mp hl
  have hr : 1 / (n : ℚ) ≤ (params mode w k 0).leakage / 128 := by
    rw [div_le_div_iff₀ hnq (by norm_num)]
    nlinarith only [hmul]
  have hs' : (10 : ℚ) ^ 10 ≤ w * n / 4 := by
    have hh := (div_le_iff₀ hw).mp hs
    nlinarith only [hh]
  have hrR : ((1 / (n : ℚ) : ℚ) : ℝ) ≤
      (((params mode w k 0).leakage / 128 : ℚ) : ℝ) := Rat.cast_le.mpr hr
  push_cast at hrR
  exact ⟨by exact_mod_cast hnq, hrR, by exact_mod_cast hs'⟩

private lemma analysisEta_bounds (mode : Mode) {w Δ : ℚ} (k : ℕ)
    (hw : 0 < w) (hΔ : 0 < Δ) (hk : 0 < k) :
    0 < analysisEta mode w Δ k ∧ analysisEta mode w Δ k ≤ 1 / 100 ∧
      analysisEta mode w Δ k ≤ (etaReq mode w k : ℝ) ∧
      analysisEta mode w Δ k ≤ (w : ℝ) ^ 2 / (10000 * (k : ℝ) ^ 2 * Δ) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hη : (0 : ℝ) < etaReq mode w k := by exact_mod_cast etaReq_pos mode k hw hk
  have hq : etaReq mode w k ≤ 1 / 100 := by
    apply (etaReq_base mode w k).trans
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (by norm_num)
  have hqR : (etaReq mode w k : ℝ) ≤ 1 / 100 := by
    have hh : (etaReq mode w k : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    norm_num at hh
    exact hh
  exact ⟨lt_min hη (by positivity), (min_le_left _ _).trans hqR,
    min_le_left _ _, min_le_right _ _⟩

private lemma corruption_le_leakage (mode : Mode) {w : ℚ} (k : ℕ) (ε : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1)
    (he : ε ≤ 1 / f mode (1 / w)) : ε ≤ ((params mode w k 0).leakage : ℝ) / 128 := by
  have hp := (params_positive mode k 0 hw.1 (by omega)).leakage
  have hpR : (0 : ℝ) < (params mode w k 0).leakage := by exact_mod_cast hp
  have hf : 0 < f mode (1 / w) := zero_lt_one.trans_le (f_ge_one mode _)
  have hh : 128 / (params mode w k 0).leakage ≤ (128 * ledger mode w k : ℚ) := by
    have hl := reciprocal_le_ledger mode w k 0 (by omega)
    have hm := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℚ) ≤ 128)
    convert hm using 1; ring
  have hhR : 128 / ((params mode w k 0).leakage : ℝ) ≤ f mode (1 / w) := by
    apply le_trans _ (f_dominates mode k hw hk hkw)
    exact_mod_cast hh
  have hmul := (div_le_iff₀ hpR).mp hhR
  apply he.trans
  rw [div_le_div_iff₀ hf (by norm_num)]
  nlinarith only [hmul]

private lemma params_separation_nonneg (mode : Mode) (w : ℚ) (k h : ℕ) :
    0 ≤ (params mode w k h).separation := by
  unfold params
  generalize k - 1 - h = m
  cases m with
  | zero => norm_num [terminal]
  | succ m =>
    rw [Function.iterate_succ_apply', (step_formulas mode w k _).separation]
    split_ifs <;> exact (dyadicUp_pos _).le

private lemma f_large (mode : Mode) (x : ℝ) : (2 : ℝ) ^ 40 ≤ f mode x := by
  have hh (a : ℕ) : (2 : ℕ) ^ 100 ≤ H a := by
    dsimp only [H]
    gcongr
    omega
  have h40 : (2 : ℝ) ^ 40 ≤ (H (max 2 ⌈x⌉₊) : ℝ) := by
    exact_mod_cast (show (2 : ℕ) ^ 40 ≤ H (max 2 ⌈x⌉₊) from
      (by norm_num : (2 : ℕ) ^ 40 ≤ 2 ^ 100).trans (hh _))
  apply h40.trans
  apply le_trans _ (le_max_right _ _)
  exact_mod_cast Nat.le_succ (H (max 2 ⌈x⌉₊))

private lemma degree_log_bound (mode : Mode) {w : ℚ} (hw : 0 < w ∧ w ≤ 1) :
    (momentDegree mode w : ℝ) ≤ 40 * (Real.log (1 / (w : ℝ)) + 1) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR1 : (w : ℝ) ≤ 1 := by exact_mod_cast hw.2
  have hlog : 0 ≤ Real.log (1 / (w : ℝ)) :=
    Real.log_nonneg ((le_div_iff₀ hwR).mpr (by linarith))
  cases mode with
  | centered => change (8 : ℝ) ≤ _; linarith
  | identical =>
    change ((8 * (logInv w + 3) : ℕ) : ℝ) ≤ _
    push_cast
    by_cases hw2 : w ≤ 1 / 2
    · have hh := (IdCov.degree_bounds w ⟨hw.1, hw2⟩).2.2
      nlinarith only [hh, hlog]
    · have hinv : 1 / w ≤ (2 : ℚ) := (div_le_iff₀ hw.1).mpr (by linarith)
      have hceil : ⌈w⁻¹⌉₊ ≤ 2 := Nat.ceil_le.mpr (by norm_num; simpa only [one_div] using hinv)
      have hl : logInv w ≤ 1 := by
        unfold logInv
        exact Nat.clog_le_of_le_pow (by simpa using hceil)
      have hlR : (logInv w : ℝ) ≤ 1 := by exact_mod_cast hl
      nlinarith only [hlR, hlog]

private lemma degree_weight_bound (mode : Mode) {w : ℚ} (hw : 0 < w ∧ w ≤ 1) :
    (momentDegree mode w : ℝ) ≤ 64 / w := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hwR)
  calc
    _ ≤ 40 * (Real.log (1 / (w : ℝ)) + 1) := degree_log_bound mode hw
    _ ≤ 40 * (1 / (w : ℝ)) := by gcongr; linarith only [hh]
    _ ≤ 64 / w := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by norm_num) hwR.le

private lemma etaReq_one_lower (mode : Mode) {w : ℚ} (hw : 0 < w ∧ w ≤ 1) :
    w / 10 ^ 16 ≤ etaReq mode w 1 := by
  have hw0 := hw.1
  simp only [etaReq, Nat.sub_self, List.range_zero, List.map_nil, List.foldl_nil,
    params, Function.iterate_zero_apply, terminal]
  repeat' apply le_min
  · nlinarith only [hw.2]
  · nlinarith only [hw.1]
  · nlinarith only [hw.2]
  · nlinarith only [hw.1]
  · split_ifs <;> norm_num <;> linarith only [hw.2]

private lemma analysisEta_inverse (mode : Mode) {w Δ : ℚ} (k : ℕ)
    (hw : 0 < w ∧ w ≤ 1) (hk : 0 < k) (hkw : (k : ℚ) * w ≤ 1)
    (hΔ : f mode (1 / w) ≤ Δ) :
    (analysisEta mode w Δ k)⁻¹ ≤ 10000 * (Δ : ℝ) / (w : ℝ) ^ 4 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR1 : (w : ℝ) ≤ 1 := by exact_mod_cast hw.2
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hΔlarge : (2 : ℝ) ^ 40 ≤ Δ := (f_large mode _).trans hΔ
  have hΔR : (0 : ℝ) < Δ := lt_of_lt_of_le (by norm_num) hΔlarge
  have hη0 := (analysisEta_bounds mode k hw.1 (by exact_mod_cast hΔR) hk).1
  have hL0 : 0 < (w : ℝ) ^ 4 / (10000 * Δ) := by positivity
  have hLreq : (w : ℝ) ^ 4 / (10000 * Δ) ≤ etaReq mode w k := by
    by_cases hk2 : 2 ≤ k
    · have hw2 : w ≤ 1 / 2 := by
        have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk2
        nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.1.le]
      have hdom := f_dominates mode k ⟨hw.1, hw2⟩ hk2 hkw
      have hh : 1 / etaReq mode w k ≤ (ledger mode w k : ℚ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (ledger_factors mode w k).2.2)
      have hhR : 1 / (etaReq mode w k : ℝ) ≤ (ledger mode w k : ℝ) := by
        exact_mod_cast hh
      have hledger : (ledger mode w k : ℝ) ≤ Δ := by
        apply le_trans _ (hdom.trans hΔ)
        nlinarith only [Nat.cast_nonneg (α := ℝ) (ledger mode w k)]
      have hreqR : (0 : ℝ) < etaReq mode w k := by exact_mod_cast etaReq_pos mode k hw.1 hk
      have hmul := (div_le_iff₀ hreqR).mp (hhR.trans hledger)
      rw [div_le_iff₀ (by positivity)]
      have hw4 := pow_le_one₀ hwR.le hwR1 (n := 4)
      nlinarith only [hmul, hw4]
    · have hk1 : k = 1 := by omega
      subst k
      have hh := etaReq_one_lower mode hw
      have hhR : (w : ℝ) / 10 ^ 16 ≤ etaReq mode w 1 := by exact_mod_cast hh
      apply le_trans _ hhR
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hw3 := pow_le_one₀ hwR.le hwR1 (n := 3)
      have hw4 : (w : ℝ) ^ 4 ≤ w := by nlinarith only [mul_le_mul_of_nonneg_left hw3 hwR.le]
      have hc : (10 : ℝ) ^ 16 ≤ 10000 * Δ := by nlinarith only [hΔlarge]
      nlinarith only [hw4, mul_le_mul_of_nonneg_right hc hwR.le]
  have hLsecond : (w : ℝ) ^ 4 / (10000 * Δ) ≤
      (w : ℝ) ^ 2 / (10000 * (k : ℝ) ^ 2 * Δ) := by
    have hkwR : (k : ℝ) * w ≤ 1 := by exact_mod_cast hkw
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k * w) hkwR 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ 10000 * Δ * (w : ℝ) ^ 2)
    nlinarith only [hm]
  have hL := le_min hLreq hLsecond
  calc
    (analysisEta mode w Δ k)⁻¹ ≤ ((w : ℝ) ^ 4 / (10000 * Δ))⁻¹ := inv_anti₀ hL0 hL
    _ = _ := by field_simp

private lemma nWeight_one_bound (mode : Mode) {w : ℚ} (hw : 0 < w) :
    (nWeight mode w 1 : ℝ) ≤ 10 ^ 14 / (w : ℝ) + 1 := by
  have hi : 0 < w⁻¹ := inv_pos.mpr hw
  have hh : nWeight mode w 1 ≤ ⌈10 ^ 14 / w⌉₊ := by
    unfold nWeight
    apply Nat.ceil_mono
    norm_num [params, terminal, div_eq_mul_inv, _root_.mul_inv_rev]
    repeat' apply And.intro
    all_goals nlinarith only [hi, hw]
  have hceil : ((⌈10 ^ 14 / w⌉₊ : ℕ) : ℚ) < 10 ^ 14 / w + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceilR : (⌈10 ^ 14 / w⌉₊ : ℝ) ≤ 10 ^ 14 / (w : ℝ) + 1 := by
    exact_mod_cast hceil.le
  exact (show (nWeight mode w 1 : ℝ) ≤ ⌈10 ^ 14 / w⌉₊ by exact_mod_cast hh).trans hceilR

private lemma sample_envelope_le (mode : Mode) (C k d : ℕ) (w Δ δ : ℚ)
    (hC : 10000000 ≤ C) (hw : 0 < w ∧ w ≤ 1)
    (hΔ : (1 : ℝ) ≤ Δ) (hδ : (0 : ℝ) < δ ∧ (δ : ℝ) < 1) :
    (max 2 (((d : ℝ) + 1) / w)) ^ (40000 * (momentDegree mode w + 1)) *
      (((Δ : ℝ) + 1) / δ) ^ 200 ≤ sampleBound mode C k d w Δ δ := by
  let A : ℝ := ((d : ℝ) + 1) / w
  let B : ℝ := ((Δ : ℝ) + 1) / δ
  let D := momentDegree mode w
  let P := 40000 * (D + 1)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR1 : (w : ℝ) ≤ 1 := by exact_mod_cast hw.2
  have hA1 : 1 ≤ A := by
    rw [le_div_iff₀ hwR]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hB2 : 2 ≤ B := by
    rw [le_div_iff₀ hδ.1]
    linarith only [hΔ, hδ.2]
  have hB1 : 1 ≤ B := by linarith
  have hlog : 0 ≤ Real.log (1 / (w : ℝ)) :=
    Real.log_nonneg ((le_div_iff₀ hwR).mpr (by linarith))
  have hC200 : 200 ≤ C := by omega
  have hCReal : (10000000 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : (((d : ℝ) + 1) * (Δ + 1) / ((w : ℝ) * δ)) = A * B := by
    dsimp [A, B]
    ring
  by_cases hA2 : 2 ≤ A
  · rw [max_eq_right hA2]
    cases mode with
    | centered =>
      change A ^ P * B ^ 200 ≤
        (((d : ℝ) + 1) * (Δ + 1) / ((w : ℝ) * δ)) ^ C
      rw [hbase, mul_pow]
      apply mul_le_mul _ (pow_le_pow_right₀ hB1 hC200) (by positivity) (by positivity)
      apply pow_le_pow_right₀ hA1
      change 40000 * (8 + 1) ≤ C
      omega
    | identical =>
      change A ^ P * B ^ 200 ≤ A ^ ((C : ℝ) * (Real.log (1 / (w : ℝ)) + 1)) * B ^ C
      apply mul_le_mul _ (pow_le_pow_right₀ hB1 hC200) (by positivity) (by positivity)
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hA1
      have hD := degree_log_bound .identical hw
      have hmul := mul_le_mul_of_nonneg_right hCReal (by linarith :
        (0 : ℝ) ≤ Real.log (1 / (w : ℝ)) + 1)
      dsimp [P, D]
      push_cast
      nlinarith only [hD, hmul, hlog]
  · have hAeq : max 2 A = 2 := max_eq_left (le_of_not_ge hA2)
    rw [hAeq]
    have hw2 : (1 / 2 : ℝ) < w := by
      have hh := (div_lt_iff₀ hwR).mp (lt_of_not_ge hA2)
      linarith [Nat.cast_nonneg (α := ℝ) d]
    have hD128 : D ≤ 128 := by
      have hh := degree_weight_bound mode hw
      have hc : (64 : ℝ) / w ≤ 128 := (div_le_iff₀ hwR).mpr (by linarith only [hw2])
      exact_mod_cast hh.trans hc
    have hPC : P + 200 ≤ C := by dsimp [P]; omega
    have hbound : (2 : ℝ) ^ P * B ^ 200 ≤ B ^ C := by
      calc
        _ ≤ B ^ P * B ^ 200 := by gcongr
        _ = B ^ (P + 200) := (pow_add ..).symm
        _ ≤ _ := pow_le_pow_right₀ hB1 hPC
    apply hbound.trans
    cases mode with
    | centered =>
      change B ^ C ≤ (((d : ℝ) + 1) * (Δ + 1) / ((w : ℝ) * δ)) ^ C
      rw [hbase]
      apply pow_le_pow_left₀ (by positivity)
      exact le_mul_of_one_le_left (by positivity) hA1
    | identical =>
      change B ^ C ≤ A ^ ((C : ℝ) * (Real.log (1 / (w : ℝ)) + 1)) * B ^ C
      exact le_mul_of_one_le_left (by positivity)
        (Real.one_le_rpow hA1 (by positivity))

/-- One absolute sample exponent dominates both explicit probability ledgers. -/
theorem exists_sampleExponent
    (mode : Mode) : ∃ Cs : ℕ, 1 ≤ Cs ∧
      ∀ (C k d n : ℕ) (M : Mixture k d) (w Δ δ : ℚ), Cs ≤ C → M.Valid →
        0 < w → (∀ i, (w : ℝ) ≤ M.w i) → f mode (1 / w) ≤ Δ →
        0 < δ → (δ : ℝ) < 1 → sampleBound mode C k d w Δ δ ≤ n →
        SampleReady mode k d n w Δ δ := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro C k d n M w Δ δ hC hM hw hwj hΔ hδ hδ1 hn
  have hk : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    have hh := hM.sum_w
    simp [hk0] at hh
  have hkw := mixture_weight_sum M w hM hwj
  have hw1 : w ≤ 1 := by
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
  have hw' : 0 < w ∧ w ≤ 1 := ⟨hw, hw1⟩
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwR1 : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hΔlarge : (2 : ℝ) ^ 40 ≤ Δ := (f_large mode _).trans hΔ
  have hΔ1 : (1 : ℝ) ≤ Δ := (by norm_num : (1 : ℝ) ≤ 2 ^ 40).trans hΔlarge
  have hΔ0 : (0 : ℝ) < Δ := zero_lt_one.trans_le hΔ1
  have hΔq : (0 : ℚ) < Δ := by exact_mod_cast hΔ0
  let D := momentDegree mode w
  let A : ℝ := max 2 (((d : ℝ) + 1) / w)
  let B : ℝ := ((Δ : ℝ) + 1) / δ
  let T : ℝ := A ^ (40000 * (D + 1)) * B ^ 200
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA1 : 1 ≤ A := by linarith
  have hB2 : 2 ≤ B := by
    dsimp [B]
    rw [le_div_iff₀ hδR]
    linarith only [hΔ1, hδ1]
  have hB1 : 1 ≤ B := by linarith
  have hwi : (w : ℝ)⁻¹ ≤ A := by
    apply le_trans _ (le_max_right _ _)
    rw [← one_div]
    gcongr
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hkA : (k : ℝ) ≤ A := by
    have hkwR : (k : ℝ) * w ≤ 1 := by exact_mod_cast hkw
    exact ((le_div_iff₀ hwR).mpr hkwR).trans (by simpa only [one_div] using hwi)
  have hdA : (d : ℝ) + 1 ≤ A := by
    apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hwR]
    nlinarith only [mul_le_mul_of_nonneg_left hwR1
      (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]
  have hδB : (δ : ℝ)⁻¹ ≤ B := by
    dsimp [B]
    rw [← one_div]
    gcongr
    linarith only [hΔ1]
  have hΔB : (Δ : ℝ) ≤ B := by
    dsimp [B]
    rw [le_div_iff₀ hδR]
    nlinarith only [mul_le_mul_of_nonneg_left hδ1.le hΔ0.le]
  have hη0 := (analysisEta_bounds mode k hw hΔq hk).1
  have hηi := analysisEta_inverse mode k hw' hk hkw hΔ
  have hD := degree_weight_bound mode hw'
  have hneed : sampleNeed w (analysisEta mode w Δ k) δ k d D ≤ T :=
    SampleAux.sampleNeed_envelope hwR hη0 hδR hk hA2 hB2 hwi hηi hδB hkA hdA hD hΔB hΔ0.le
  have hhalf : sampleNeed w (analysisEta mode w Δ k) (1 / 2) k d D ≤ T :=
    SampleAux.sampleNeed_envelope hwR hη0 (by norm_num) hk hA2 hB2 hwi hηi
      (by norm_num; exact hB2) hkA hdA hD hΔB hΔ0.le
  have hBT : B ≤ T := by
    calc
      B ≤ B ^ 200 := le_self_pow₀ hB1 (by norm_num)
      _ ≤ T := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hA1)
  have hweight : (nWeight mode w k : ℝ) ≤ T := by
    by_cases hk2 : 2 ≤ k
    · have hw2 : w ≤ 1 / 2 := by
        have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk2
        nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
      have hdom := f_dominates mode k ⟨hw, hw2⟩ hk2 hkw
      have hledger : (ledger mode w k : ℝ) ≤ f mode (1 / w) := by
        apply le_trans _ hdom
        nlinarith only [Nat.cast_nonneg (α := ℝ) (ledger mode w k)]
      have hh : (nWeight mode w k : ℝ) ≤ ledger mode w k := by
        exact_mod_cast (ledger_factors mode w k).2.1
      exact hh.trans (hledger.trans (hΔ.trans (hΔB.trans hBT)))
    · have hk1 : k = 1 := by omega
      subst k
      have hc : (10 : ℝ) ^ 14 ≤ A ^ 47 := (by norm_num : (10 : ℝ) ^ 14 ≤ 2 ^ 47).trans
        (pow_le_pow_left₀ (by norm_num) hA2 47)
      have hh : (10 : ℝ) ^ 14 / w ≤ A ^ 48 := by
        calc
          _ = (10 : ℝ) ^ 14 * (w : ℝ)⁻¹ := div_eq_mul_inv _ _
          _ ≤ A ^ 47 * A := by gcongr
          _ = _ := by ring
      have hsum : A ^ 48 + 1 ≤ A ^ 49 := by
        have hp : 2 * A ^ 48 ≤ A ^ 49 := by
          calc
            _ ≤ A * A ^ 48 := by gcongr
            _ = _ := by ring
        linarith only [hp, one_le_pow₀ hA1 (n := 48)]
      calc
        (nWeight mode w 1 : ℝ) ≤ 10 ^ 14 / (w : ℝ) + 1 := nWeight_one_bound mode hw
        _ ≤ A ^ 49 := by linarith only [hh, hsum]
        _ ≤ A ^ (40000 * (D + 1)) := pow_le_pow_right₀ hA1 (by omega)
        _ ≤ T := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hT := sample_envelope_le mode C k d w Δ δ hC hw' hΔ1 ⟨hδR, hδ1⟩
  have hTn : T ≤ n := hT.trans hn
  exact ⟨by exact_mod_cast hweight.trans hTn, hneed.trans hTn, hhalf.trans hTn⟩

/-- Admissible inputs and the good event supply every deterministic precondition. -/
theorem prepared_sample
    {k d n : ℕ} (mode : Mode) (M : Mixture k d) (w Δ δ : ℚ) (ε : ℝ)
    (ω : Fin n → Triple k d) (r : Rounding k d)
    (hM : M.Valid) (hm : mode.Condition M) (hs : mode.Separated M Δ)
    (hk : 2 ≤ k) (hw : 0 < w) (hwj : ∀ i, (w : ℝ) ≤ M.w i)
    (hΔ : f mode (1 / w) ≤ Δ) (he : 0 ≤ ε ∧ ε ≤ 1 / f mode (1 / w))
    (hn : SampleReady mode k d n w Δ δ)
    (hg : Good M ε w (analysisEta mode w Δ k) (momentDegree mode w) ω)
    (hr : IsRounding M (1 / n) r) :
    Prepared mode M ε w (analysisEta mode w Δ k) Δ (momentDegree mode w) ω r
      (params mode w k) ∧ (2 : ℝ) ^ 40 ≤ Δ ∧
    0 < analysisEta mode w Δ k ∧
    analysisEta mode w Δ k ≤ min (1 / 100) ((w : ℝ) ^ 2 / (10000 * k ^ 2 * Δ)) := by
  have hk0 : 0 < k := by omega
  have hkw := mixture_weight_sum M w hM hwj
  have hw2 : w ≤ 1 / 2 := by
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
  have hw' : 0 < w ∧ w ≤ 1 / 2 := ⟨hw, hw2⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := (f_ge_one mode _).trans hΔ
  have hΔ0 : (0 : ℚ) < Δ := by exact_mod_cast (zero_lt_one.trans_le hΔ1)
  obtain ⟨hη0, hη100, hηreq, hηΔ⟩ := analysisEta_bounds mode k hw hΔ0 hk0
  have hηleak : analysisEta mode w Δ k ≤ ((params mode w k 0).leakage : ℝ) / 128 := by
    have hh := (etaReq_base mode w k).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    apply hηreq.trans
    exact_mod_cast hh
  have hε := corruption_le_leakage mode k ε hw' hk hkw he.2
  obtain ⟨hn0, hround, hsize⟩ := sample_weight_bounds mode k n hw hk0 hn.1
  have hbudget := leakageBudget_bound mode k (analysisEta mode w Δ k) hw hk0 hηleak
  have hdom := f_dominates mode k hw' hk hkw
  have hledger : (ledger mode w k : ℝ) ≤ f mode (1 / w) := by
    apply le_trans _ hdom
    nlinarith only [Nat.cast_nonneg (α := ℝ) (ledger mode w k)]
  have hsep (h : ℕ) (hh : h < k) : ((params mode w k h).separation : ℝ) ≤ Δ := by
    apply le_trans _ (hledger.trans hΔ)
    exact_mod_cast separation_le_ledger mode w k h hh
  have h40 : (2 : ℝ) ^ 40 ≤ Δ := by
    have hh := hsep (k - 1) (by omega)
    simpa only [params, Nat.sub_self, Function.iterate_zero_apply, terminal,
      Rat.cast_pow, Rat.cast_ofNat] using hh
  refine ⟨?_, h40, hη0, le_min hη100 hηΔ⟩
  unfold Prepared
  refine ⟨hM, hm, hs, ?_, hwj, he.1, hη0, hη100, ?_, hg, hr, hn.2.2,
    hsize, ?_, ?_, ?_⟩
  · exact_mod_cast hw
  · cases mode <;> simp [momentDegree, params_weight]
  · simp only [params, Nat.sub_self, Function.iterate_zero_apply, terminal, le_refl]
  · intro h hh
    exact params_ready mode k h hw' hk0 hh
  · intro h hh
    have hp := params_positive mode k h hw hk0
    have hmono := params_leakage_mono mode k hw hk0 (show 0 ≤ h by omega)
    have hmonoR : ((params mode w k 0).leakage : ℝ) ≤
        (params mode w k h).leakage := by exact_mod_cast hmono
    have hcont := params_leakage_contamination mode k h hw hk0
    have hcontR : ((params mode w k h).leakage : ℝ) ≤
        w * (params mode w k h).contamination / 128 := by exact_mod_cast hcont
    have hwR : (0 : ℝ) < w := by exact_mod_cast hw
    have hreqR : (0 : ℝ) < (params mode w k h).contamination := by
      exact_mod_cast hp.contamination
    refine ⟨?_, hbudget h hh, ?_, params_separation_nonneg mode w k h, hsep h hh,
      ?_, ?_⟩
    · exact_mod_cast params_weight mode w k h
    · rw [div_le_iff₀ hwR]
      nlinarith only [hcontR, hmonoR, hε, hηleak, hround, mul_pos hwR hreqR]
    · have hb : etaReq mode w k ≤ (params mode w k h).frameAccuracy ^ 2 := by
        by_cases hh' : h < k - 1
        · exact (foldl_min_le_entry _ _ _
            (List.mem_map.mpr ⟨h, List.mem_range.mpr hh', rfl⟩)).trans (min_le_left _ _)
        · have ht : params mode w k h = terminal w := by
            simp [params, Nat.sub_eq_zero_of_le (by omega : k - 1 ≤ h)]
          rw [ht]
          exact (foldl_min_le_initial _ _).trans (min_le_left _ _)
      exact hηreq.trans (by exact_mod_cast hb)
    · intro hh'
      exact params_sound mode k h ε (analysisEta mode w Δ k)
        (leakageBudget (params mode w k) (analysisEta mode w Δ k) h)
        hw' hk0 hh' hε hηreq (hbudget h hh)

open EncodingBounds

private lemma encoding_constant (q : ℚ)
    (hq : q ∈ [0, 1, 1 / 2, 2, 3, 4, 8, 9, 16, 20, 32, 40, 64, 600, 4096,
      1 / 16, 1 / 640000000000, 1 / 100, 1 / 1000000, 1 / 100000000,
      2 / 10 ^ 10, 2 ^ 40, 2400]) : RatBound 50 q := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> norm_num

private lemma terminal_encoding {b : ℕ} {w : ℚ} (hw : RatBound b w) :
    ∀ q ∈ values (terminal w), RatBound (b + 50) q := by
  have hc (q : ℚ) (hq : q ∈ values (terminal w)) :
      q = w ∨ q = w / 16 ∨ q = w * (1 / 640000000000) ∨
        q ∈ [0, 1 / 2, 1, 4, 2400, 1 / 100, 1 / 1000000, 1 / 100000000,
          2 / 10 ^ 10, 2 ^ 40] := by
    norm_num only [values, terminal, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | tauto | right; right; left; ring
  intro q hq
  rcases hc q hq with rfl | rfl | rfl | hq
  · exact hw.mono (by omega)
  · have hh := hw.mul (encoding_constant (1 / 16) (by simp))
    simpa only [div_eq_mul_inv, one_div, one_mul] using hh
  · exact hw.mul (encoding_constant _ (by simp))
  · apply (encoding_constant q ?_).mono (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    tauto

/-- The sample-count factor supplies ample constant and component-count reserves. -/
theorem ledgerCore_large {w : ℚ} (k : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hkw : (k : ℚ) * w ≤ 1) :
    1000000 ≤ ledgerCore .centered w k ∧ k ≤ ledgerCore .centered w k := by
  have hn := (core_factors .centered w k).2.1
  have hn8 : 8 / w ≤ (nWeight .centered w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
  have hn4 : 4 * 10 ^ 10 / w ≤ (nWeight .centered w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _)))
  have hB : (nWeight .centered w k : ℚ) ≤ ledgerCore .centered w k := by exact_mod_cast hn
  constructor
  · have hl : (1000000 : ℚ) ≤ 4 * 10 ^ 10 / w := by
      rw [le_div_iff₀ hw.1]
      nlinarith only [hw.2]
    exact_mod_cast hl.trans (hn4.trans hB)
  · have hkw' : (k : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr hkw
    have hh : (1 : ℚ) / w ≤ 8 / w :=
      div_le_div_of_nonneg_right (by norm_num) hw.1.le
    exact_mod_cast hkw'.trans (hh.trans (hn8.trans hB))

/-- The numerical reserve controls every encoded schedule row. -/
theorem params_encoding_bound {w : ℚ} (k h b : ℕ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1)
    (hh : h < k) (hwb : RatBound b w) :
    ∀ q ∈ values (params .centered w k h),
      RatBound (200 * (b + ledgerCore .centered w k + 100)) q := by
  let B := ledgerCore .centered w k
  let z := b + B + 100
  have hz : 100 ≤ z := by dsimp [z]; omega
  have hc (q : ℚ)
      (hq : q ∈ [0, 1, 1 / 2, 2, 3, 4, 8, 9, 16, 20, 32, 40, 64, 600, 4096]) :
      RatBound 50 q := encoding_constant q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto)
  have hrec (j : ℕ) (hj : j < k) (q : ℚ)
      (hq : ⌈1 / q⌉₊ ∈ parameterNumbers (params .centered w k j)) : 1 / q ≤ B := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast core_entry .centered w k j _ hj hq)
  by_cases ht : h < k - 1
  · let p := params .centered w k h
    let next := params .centered w k (h + 1)
    have hpeq : p = step .centered w k next := params_succ .centered w k h ht
    have f := step_formulas .centered w k next
    rw [← hpeq] at f
    have hnext : RatBound z next.leakage := by
      by_cases hnext : h + 1 < k - 1
      · have fe := (step_formulas .centered w k (params .centered w k (h + 2))).leakage
        rw [← params_succ .centered w k (h + 1) hnext] at fe
        have hr := hrec (h + 1) (by omega) next.leakage (by simp [next, parameterNumbers])
        rw [show next.leakage = _ from fe] at hr ⊢
        exact (down B hr).mono (by dsimp only [z]; omega)
      · have heq : next = terminal w := by
          simp only [next, params, Nat.sub_eq_zero_of_le (by omega : k - 1 ≤ h + 1),
            Function.iterate_zero_apply]
        rw [heq]
        exact (terminal_encoding hwb _ (by simp [values])).mono (by dsimp only [z]; omega)
    have hbrec := hrec h hh p.subspaceAccuracy (by simp [p, parameterNumbers])
    have hrrec := hrec h hh p.contamination (by simp [p, parameterNumbers])
    have hlrec := hrec h hh p.leakage (by simp [p, parameterNumbers])
    have hβ : RatBound z p.subspaceAccuracy := by
      have heq := f.accuracy
      rw [heq] at hbrec ⊢
      exact (down B hbrec).mono (by dsimp only [z]; omega)
    have hreq : RatBound z p.contamination := by
      rw [f.contamination] at hrrec ⊢
      exact (down B hrrec).mono (by dsimp only [z]; omega)
    have hleak : RatBound z p.leakage := by
      rw [f.leakage] at hlrec ⊢
      exact (down B hlrec).mono (by dsimp only [z]; omega)
    have hframe : RatBound z p.frameAccuracy := by
      have hη := etaReq_pos .centered k hw.1 (by omega)
      have hfpos := (params_ready .centered k h hw (by omega) ht).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hηf : etaReq .centered w k ≤ p.frameAccuracy ^ 2 :=
        (foldl_min_le_entry _ _ _
          (List.mem_map.mpr ⟨h, List.mem_range.mpr ht, rfl⟩)).trans (min_le_left _ _)
      have hf1 : p.frameAccuracy ≤ 1 := by
        rw [f.frame]
        exact (dyadicDown_le_half _).trans (by norm_num)
      have hηf' : etaReq .centered w k ≤ p.frameAccuracy := by
        nlinarith only [hηf, hf1, hfpos]
      have he := (core_factors .centered w k).2.2
      have hr : 1 / p.frameAccuracy ≤ B :=
        (one_div_le_one_div_of_le hη hηf').trans ((Nat.le_ceil _).trans (by exact_mod_cast he))
      rw [f.frame] at hr ⊢
      exact (down B hr).mono (by dsimp only [z]; omega)
    have hw' : RatBound z w := hwb.mono (by dsimp only [z]; omega)
    have hφ : RatBound (2 * z) p.straddle := by
      rw [f.straddle]
      exact (hnext.div (hc 4 (by simp))).mono (by omega)
    have hω : RatBound 50 p.windowMass := by
      rw [f.window, ite_eq_left rfl]
      exact hc _ (by simp)
    have hv : RatBound (3 * z) p.verifyMass := by
      rw [f.verify]
      exact ((hw'.mul hω).div (hc 8 (by simp))).mono (by omega)
    have htail : RatBound (4 * z) p.tail := by
      rw [f.tail]
      exact ((hφ.div (hc 64 (by simp))).min
        ((hv.div (hc 64 (by simp))).min (hw'.div (hc 4096 (by simp))))).mono (by omega)
    have hK : RatBound (5 * z) p.K := by
      rw [f.K, ite_eq_left rfl]
      exact (up_bound ((hc 32 (by simp)).div hφ)).mono (by omega)
    have hWF : RatBound (8 * z) p.WF := by
      rw [f.WF]
      exact (up_bound (((hc 8 (by simp)).mul ((hc 40 (by simp)).div hw')).mul
        (sqrt_bound ((hc 1 (by simp)).div hφ)))).mono (by omega)
    have hDF : RatBound (12 * z) p.DF := by
      rw [f.DF]
      exact (up_bound (((hc 4 (by simp)).mul hWF).max
        (((hc 4 (by simp)).mul ((hc 40 (by simp)).div hw')).mul
          (sqrt_bound ((hc 1 (by simp)).div htail))))).mono (by omega)
    have hkB : k ≤ B := by
      have hn := (core_factors .centered w k).2.1
      have hn' : 8 / w ≤ (nWeight .centered w k : ℚ) := by
        unfold nWeight
        exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
      have hkw' : (k : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr hkw
      have hB : (k : ℚ) ≤ B := by
        apply hkw'.trans
        apply le_trans _ (hn'.trans (by exact_mod_cast hn))
        exact div_le_div_of_nonneg_right (by norm_num) hw.1.le
      exact_mod_cast hB
    have hkn : RatBound z (k : ℚ) := by
      constructor
      · rw [abs_of_nonneg (by positivity)]
        exact_mod_cast hkB.trans ((by dsimp only [z]; omega : B ≤ z).trans
          (Nat.lt_two_pow_self (n := z)).le)
      · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
    have hR : RatBound (30 * z) p.R := by
      rw [f.R, ite_eq_left rfl]
      exact (up_bound ((((hc 2 (by simp)).mul (hkn.sub (hc 1 (by simp)))).mul
        (((hc 2 (by simp)).mul hDF).add ((hc 3 (by simp)).mul hWF))).add
          (hc 1 (by simp)))).mono (by omega)
    have hσ : RatBound (70 * z) p.sigmaSq := by
      rw [f.sigma]
      exact (((hc 600 (by simp)).div ((hw'.div (hc 2 (by simp))).pow 2)).add
        ((hc 2 (by simp)).mul (hR.pow 2))).mono (by omega)
    have hγ : RatBound (200 * z) p.isotropy := by
      rw [f.isotropy, ite_eq_left rfl]
      unfold Centered.gammaStar Centered.delta Centered.nu
      exact (((hw'.div (hc 2 (by simp))).mul (hβ.pow 4)).pow 8 |>.pow 2 |>.div
        (hc 20 (by simp))).mono (by omega)
    have hE : RatBound (200 * z) p.momentError := by
      rw [f.moment, ite_eq_left rfl]
      unfold Centered.etaStar Centered.delta Centered.nu
      exact (((hw'.div (hc 2 (by simp))).mul (hβ.pow 4)).pow 8 |>.pow 4 |>.div
        (hc 9 (by simp))).mono (by omega)
    have hsep : RatBound z p.separation := by
      have heq := f.separation
      have hb : p.separation ≤ B := (Nat.le_ceil _).trans
        (by exact_mod_cast core_entry .centered w k h _ hh (by simp [p, parameterNumbers]))
      rw [heq] at hb ⊢
      exact (up B hb).mono (by dsimp only [z]; omega)
    intro q hq
    change RatBound (200 * z) q
    simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [f.weight]; exact hw'.mono (by omega)
    · exact hφ.mono (by omega)
    · exact hω.mono (by omega)
    · exact hv.mono (by omega)
    · exact htail.mono (by omega)
    · exact hK.mono (by omega)
    · exact hWF.mono (by omega)
    · exact hDF.mono (by omega)
    · exact hR.mono (by omega)
    · exact hσ.mono (by omega)
    · exact hβ.mono (by omega)
    · exact hγ
    · exact hE
    · exact hframe.mono (by omega)
    · exact hreq.mono (by omega)
    · exact hleak.mono (by omega)
    · exact hsep.mono (by omega)
  · have heq : params .centered w k h = terminal w := by
      simp only [params, Nat.sub_eq_zero_of_le (by omega : k - 1 ≤ h),
        Function.iterate_zero_apply]
    rw [heq]
    intro q hq
    exact (terminal_encoding hwb q hq).mono (by omega)

end

noncomputable section

open Common _root_.ABBKS26.Tree EncodingBounds

/-- Every arithmetic tree cap is one of the factors in the original ledger core. -/
theorem treeCap_le_core (mode : Mode) (w : ℚ) (k : ℕ) :
    treeCap mode k (params mode w k) ≤ ledgerCore mode w k := by
  let ps := (List.range k).map (params mode w k)
  let numbers := ps.flatMap fun p ↦
    [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
      ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]
  let P := (numbers.map (fun a ↦ a + 2)).prod
  have hP : 0 < P := by
    apply lt_of_lt_of_le (by decide : 0 < 1)
    apply List.one_le_prod_of_one_le
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    omega
  change _ ≤ P * (nWeight mode w k + 2) *
    (treeCap mode k (params mode w k) + 2) * (⌈1 / etaReq mode w k⌉₊ + 2)
  exact (Nat.le_add_right _ 2).trans
    ((Nat.le_mul_of_pos_left _ (Nat.mul_pos hP (by omega))).trans
      (Nat.le_mul_of_pos_right _ (by omega)))

/-- The numerical core supplies all fixed reserves and the number of schedule levels. -/
theorem core_large (mode : Mode) {w : ℚ} (k : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hkw : (k : ℚ) * w ≤ 1) :
    100000000 ≤ ledgerCore mode w k ∧ k ≤ ledgerCore mode w k := by
  have hn := (core_factors mode w k).2.1
  have hn8 : 8 / w ≤ (nWeight mode w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
  have hn4 : 4 * 10 ^ 10 / w ≤ (nWeight mode w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _)))
  have hB : (nWeight mode w k : ℚ) ≤ ledgerCore mode w k := by exact_mod_cast hn
  constructor
  · have hl : (100000000 : ℚ) ≤ 4 * 10 ^ 10 / w := by
      rw [le_div_iff₀ hw.1]
      nlinarith only [hw.2]
    exact_mod_cast hl.trans (hn4.trans hB)
  · have hkw' : (k : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr hkw
    have hh : (1 : ℚ) / w ≤ 8 / w :=
      div_le_div_of_nonneg_right (by norm_num) hw.1.le
    exact_mod_cast hkw'.trans (hh.trans (hn8.trans hB))

private theorem id_reserve_row {w : ℚ} (k h : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1) (hh : h < k - 1) :
    idReserve k (params .identical w k h) + 2 ≤
      2 ^ (ledgerCore .identical w k + 8) := by
  let B := ledgerCore .identical w k
  let p := params .identical w k h
  have hB : 100000000 ≤ B := (core_large .identical k hw hkw).1
  have hn := (core_factors .identical w k).2.1
  have hn8 : ⌈8 / w⌉₊ ≤ B := by
    apply le_trans _ hn
    apply Nat.ceil_le.mpr
    unfold nWeight
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
  have htw : IdCov.tDegree w ≤ B + 3 := by
    have hi : ⌈w⁻¹⌉₊ ≤ B := Nat.ceil_mono (by
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) hw.1.le) |>.trans hn8
    have hl := (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := ⌈w⁻¹⌉₊)).le).trans hi
    change Nat.clog 2 ⌈w⁻¹⌉₊ + 3 ≤ B + 3
    omega
  have hf := step_formulas .identical w k (params .identical w k (h + 1))
  rw [← params_succ .identical w k h hh] at hf
  have hβrec : 1 / p.subspaceAccuracy ≤ (B : ℚ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast core_entry .identical w k h _ (by omega)
        (by simp [p, parameterNumbers]))
  have hden : p.subspaceAccuracy.den ≤ 2 ^ (B + 1) := by
    rw [hf.accuracy, ite_eq_right (by decide : Mode.identical ≠ .centered)] at hβrec ⊢
    exact (down B hβrec).denominator
  have hs := params_ready .identical k h hw (by omega) hh
  have hβ := hs.2.2.1
  have hβ100 := hs.2.2.2.1
  let D := IdCov.N_pack p.subspaceAccuracy k
  have hD : D ≤ netBound D p.subspaceAccuracy := by
    have hD0 : 0 < D := by unfold D IdCov.N_pack Rounding.rankCap Rounding.greedyCap; positivity
    have hceil : 0 < ⌈64 * (D : ℚ) / p.subspaceAccuracy⌉₊ :=
      Nat.ceil_pos.mpr (by positivity)
    exact (Nat.lt_two_pow_self (n := D)).le.trans (Nat.pow_le_pow_left (by omega) _)
  have hstep : stepBranchCap .identical k p ≤ branchCap .identical k (params .identical w k) := by
    have hm : stepBranchCap .identical k p ≤
        ((List.range (k - 1)).map fun j ↦
          stepBranchCap .identical k (params .identical w k j)).foldl max 0 :=
      SoS.Poly.le_foldl_max (x := stepBranchCap .identical k p)
      (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩) 0
    exact hm.trans ((Nat.le_mul_of_pos_left _ (by omega)).trans (le_max_right 1 _))
  have hpack : D ≤ B := by
    apply hD.trans
    apply (Nat.le_mul_of_pos_right _ (by omega :
      0 < 2 * ⌈64 * k * sqrtUp (1 / p.w)⌉₊ + 3)).trans
    apply hstep.trans
    apply le_trans _ (treeCap_le_core .identical w k)
    exact (Nat.le_succ _).trans (le_self_pow₀ (by unfold branchCap; omega) (by omega))
  have hpw : p.w = w := params_weight .identical w k h
  have hpow : B ≤ 2 ^ B := (Nat.lt_two_pow_self (n := B)).le
  have hpow0 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hden' : p.subspaceAccuracy.den ≤ 2 ^ B * 2 := by
    simpa only [pow_succ] using hden
  dsimp only [idReserve]
  rw [hpw]
  rw [show B + 8 = B + 1 + 7 by omega, pow_add, pow_add]
  norm_num only [show (2 : ℕ) ^ 1 = 2 by norm_num,
    show (2 : ℕ) ^ 7 = 128 by norm_num]
  change p.subspaceAccuracy.den + ⌈8 / w⌉₊ + IdCov.tDegree w + D + 100 + 2 ≤ _
  nlinarith only [hden', hn8, htw, hpack, hB, hpow, hpow0]

/-- The enlarged parameter ledger pays for the bit-sensitive identical-mode reserve.
No sample encoding enters this reserve, including in the high-degree exponent. -/
theorem identical_reserve {w : ℚ} (k : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1) :
    treeCap .identical k (params .identical w k) ^ 2 *
      (idReserves k (params .identical w k) + 2) ^
        (1000000000 * (Rounding.solverConstant + 1) * (IdCov.tDegree w) ^ 2) ≤
      ledger .identical w k := by
  let B := ledgerCore .identical w k
  let G := B + Rounding.solverConstant + 2
  have hB : 100000000 ≤ B := (core_large .identical k hw hkw).1
  have hkB : k ≤ B := (core_large .identical k hw hkw).2
  have hG : 100000000 ≤ G := by dsimp only [G]; omega
  have ht : IdCov.tDegree w ≤ 2 * G := by
    have hn := (core_factors .identical w k).2.1
    have hi : ⌈w⁻¹⌉₊ ≤ B := by
      apply le_trans _ hn
      apply Nat.ceil_le.mpr
      unfold nWeight
      apply le_trans _ ((le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _)))
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) hw.1.le
    have hl := (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := ⌈w⁻¹⌉₊)).le).trans hi
    dsimp only [IdCov.tDegree, logInv, G]
    omega
  let xs := (List.range (k - 1)).map fun h ↦ idReserve k (params .identical w k h) + 2
  have hp : xs.prod ≤ 2 ^ ((B + 8) * B) := by
    have hp := List.prod_le_pow_length (l := xs) (n := 2 ^ (B + 8)) (by
      intro q hq
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hq
      exact id_reserve_row k h hw hk hkw (List.mem_range.mp hh))
    simp only [xs, List.length_map, List.length_range, ← pow_mul] at hp
    exact hp.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (by omega : k - 1 ≤ B)))
  have hS : idReserves k (params .identical w k) + 2 ≤ 2 ^ G ^ 4 := by
    have h1 : 1 ≤ 2 ^ ((B + 8) * B) := Nat.one_le_two_pow
    have he : (B + 8) * B + 3 ≤ G ^ 4 := by
      have hBG : B ≤ G := by dsimp only [G]; omega
      have h2 : B ^ 2 ≤ G ^ 2 := Nat.pow_le_pow_left hBG 2
      have h3 : 100 * G ^ 2 ≤ G ^ 3 := by
        have hm := Nat.mul_le_mul_right (G ^ 2) (show 100 ≤ G by omega)
        nlinarith only [hm]
      have h4 : G ^ 3 ≤ G ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      nlinarith only [hBG, hG, h2, h3, h4]
    apply le_trans _ (Nat.pow_le_pow_right (by norm_num) he)
    change xs.prod + 2 + 2 ≤ _
    rw [pow_add]
    norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num]
    omega
  have htree : treeCap .identical k (params .identical w k) ^ 2 ≤ 2 ^ (2 * B) := by
    apply (Nat.pow_le_pow_left (treeCap_le_core .identical w k) 2).trans
    apply (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := B)).le 2).trans_eq
    rw [← pow_mul]
    congr 1
    omega
  have he : 2 * B + G ^ 4 *
      (1000000000 * (Rounding.solverConstant + 1) * (IdCov.tDegree w) ^ 2) ≤ G ^ 100 := by
    have hC : Rounding.solverConstant + 1 ≤ G := by dsimp only [G]; omega
    have hBG : B ≤ G := by dsimp only [G]; omega
    have hbig : 1000000000 ≤ G ^ 2 := by nlinarith only [hG]
    have hp : G ^ 4 * (1000000000 * (Rounding.solverConstant + 1) *
        (IdCov.tDegree w) ^ 2) ≤ 4 * G ^ 9 := by
      calc
        _ ≤ G ^ 4 * (G ^ 2 * G * (2 * G) ^ 2) := by gcongr
        _ = _ := by ring
    have hG1 : 1 ≤ G := (by norm_num : 1 ≤ 100000000).trans hG
    have hG6 : 6 ≤ G := (by norm_num : 6 ≤ 100000000).trans hG
    have hG9 : G ≤ G ^ 9 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hG1 (by norm_num : 1 ≤ 9)
    have hten : 6 * G ^ 9 ≤ G ^ 10 := by
      calc
        _ ≤ G * G ^ 9 := Nat.mul_le_mul_right (G ^ 9) hG6
        _ = _ := by ring
    have hlarge : G ^ 10 ≤ G ^ 100 := Nat.pow_le_pow_right hG1 (by norm_num)
    nlinarith only [hp, hBG, hG9, hten, hlarge]
  apply (Nat.mul_le_mul htree (Nat.pow_le_pow_left hS _)).trans
  rw [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) he

end

end ABBKS26.Schedule
