module

public import ABBKS26.Assembly.Schedule

/-! Encoding the identical-covariance schedule in its numerical ledger. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdSchedule

open Common _root_.ABBKS26.Tree _root_.ABBKS26.Schedule
open _root_.ABBKS26.Schedule.EncodingBounds

private lemma params_succ (mode : Mode) (w : ℚ) (k h : ℕ) (hh : h < k - 1) :
    params mode w k h = step mode w k (params mode w k (h + 1)) := by
  unfold params
  have he : k - 1 - h = (k - 1 - (h + 1)) + 1 := by omega
  rw [he, Function.iterate_succ_apply']

private def momentBound (mode : Mode) (w : ℚ) : ℚ :=
  if mode = .centered then 2 * (80 / w) ^ 4
  else 2 * (80 * IdCov.tDegree w / w) ^ (4 * IdCov.tDegree w)

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

private def parameterNumbers (p : StepParams) : List ℕ :=
  [⌈1 / p.contamination⌉₊, ⌈1 / p.leakage⌉₊, ⌈1 / p.subspaceAccuracy⌉₊,
    ⌈1 / p.isotropy⌉₊, ⌈1 / p.momentError⌉₊, ⌈p.separation⌉₊]

private def ledgerNumbers (mode : Mode) (w : ℚ) (k : ℕ) : List ℕ :=
  ((List.range k).map (params mode w k)).flatMap parameterNumbers

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

private lemma encoding_constant (q : ℚ)
    (hq : q ∈ [0, 1, 1 / 2, 2, 3, 4, 8, 9, 16, 20, 32, 40, 64, 600, 4096,
      6, 25, 10000, 1 / 16, 1 / 640000000000, 1 / 100, 1 / 1000000, 1 / 100000000,
      2 / 10 ^ 10, 2 ^ 40, 2400]) : RatBound 50 q := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
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

private theorem down_bound {b : ℕ} {q : ℚ} (hq : RatBound b q) :
    RatBound (2 * b + 2) (dyadicDown q) := by
  by_cases hq0 : 0 < q
  · have hi := hq.inv.magnitude
    have hc : ⌈1 / q⌉₊ ≤ 2 ^ (2 * b) := by
      apply Nat.ceil_le.mpr
      simpa only [abs_of_pos (inv_pos.mpr hq0), one_div, Nat.cast_pow,
        Nat.cast_ofNat] using hi
    have he := Nat.clog_le_of_le_pow hc
    let m := Nat.clog 2 ⌈1 / q⌉₊ + 1
    have hcast : (2 : ℚ) ^ m = ((2 ^ m : ℕ) : ℚ) := by push_cast; rfl
    simp only [dyadicDown, ite_eq_left hq0]
    change RatBound (2 * b + 2) ((2 : ℚ) ^ m)⁻¹
    rw [hcast]
    constructor
    · rw [abs_of_nonneg (by positivity)]
      have hone : (1 : ℚ) ≤ (2 ^ m : ℕ) := by exact_mod_cast Nat.one_le_two_pow
      exact (inv_le_one_of_one_le₀ hone).trans (one_le_pow₀ (by norm_num))
    · rw [Rat.inv_natCast_den_of_pos (by positivity)]
      exact Nat.pow_le_pow_right (by norm_num) (by dsimp only [m]; omega)
  · simp only [dyadicDown, ite_eq_right hq0]
    exact RatBound.zero _

theorem ledgerCore_large {w : ℚ} (k : ℕ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hkw : (k : ℚ) * w ≤ 1) :
    100000000 ≤ ledgerCore .identical w k ∧ k ≤ ledgerCore .identical w k := by
  have hn := (core_factors .identical w k).2.1
  have hn8 : 8 / w ≤ (nWeight .identical w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
  have hn4 : 4 * 10 ^ 10 / w ≤ (nWeight .identical w k : ℚ) := by
    unfold nWeight
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _)))
  have hB : (nWeight .identical w k : ℚ) ≤ ledgerCore .identical w k := by exact_mod_cast hn
  constructor
  · have hl : (100000000 : ℚ) ≤ 4 * 10 ^ 10 / w := by
      rw [le_div_iff₀ hw.1]
      nlinarith only [hw.2]
    exact_mod_cast hl.trans (hn4.trans hB)
  · have hkw' : (k : ℚ) ≤ 1 / w := (le_div_iff₀ hw.1).mpr hkw
    have hh : (1 : ℚ) / w ≤ 8 / w :=
      div_le_div_of_nonneg_right (by norm_num) hw.1.le
    exact_mod_cast hkw'.trans (hh.trans (hn8.trans hB))

private theorem error_encoding (w β : ℚ) (z : ℕ) (hz : 1000000 ≤ z)
    (hβ : RatBound z β) (ht : IdCov.tDegree w ≤ z) :
    RatBound (12 * z) (IdCov.gammaStar β) ∧
      RatBound (1000 * z ^ 2) (IdCov.etaStar w β / 4) ∧
      RatBound (30 * z) (dyadicDown (IdCov.gammaStar β / 10000)) := by
  have hc (q : ℚ) (hq : q ∈ [3, 4, 6, 8, 25, 64, 10000]) : RatBound 50 q :=
    encoding_constant q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      tauto)
  have hγ : RatBound (12 * z) (IdCov.gammaStar β) := by
    unfold IdCov.gammaStar IdCov.epsilonR
    exact (((hβ.div (hc 25 (by simp))).pow 8).div
      (hc 6 (by simp))).mono (by omega)
  have htn : RatBound z (IdCov.tDegree w : ℚ) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast ht.trans (Nat.lt_two_pow_self (n := z)).le
    · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
  have hE : RatBound (1000 * z ^ 2) (IdCov.etaStar w β / 4) := by
    unfold IdCov.etaStar IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
    have he := (((((hβ.div (hc 25 (by norm_num))).pow 8).pow 2).div
      (hc 3 (by simp))).div ((hc 64 (by simp)).mul htn)).pow
        (4 * IdCov.tDegree w)
    have he' := (((he.div (hc 4 (by simp))).div
      (((hc 8 (by simp)).mul htn).pow (4 * IdCov.tDegree w + 2))).div
        (hc 4 (by simp)))
    apply he'.mono
    nlinarith only [hz, ht, Nat.mul_le_mul_left z ht]
  have hframe : RatBound (30 * z) (dyadicDown (IdCov.gammaStar β / 10000)) := by
    exact (down_bound (hγ.div (hc 10000 (by norm_num)))).mono (by omega)
  exact ⟨hγ, hE, hframe⟩

private theorem values_encoding (p : StepParams) (z : ℕ) (hz : 1 ≤ z)
    (hw : RatBound z p.w) (hφ : RatBound (2 * z) p.straddle)
    (hω : RatBound (30 * z) p.windowMass) (hv : RatBound (32 * z) p.verifyMass)
    (htail : RatBound (34 * z) p.tail) (hK : RatBound (5 * z) p.K)
    (hWF : RatBound (8 * z) p.WF) (hDF : RatBound (80 * z) p.DF)
    (hR : RatBound (30 * z) p.R) (hσ : RatBound (70 * z) p.sigmaSq)
    (hβ : RatBound z p.subspaceAccuracy) (hγ : RatBound (12 * z) p.isotropy)
    (hE : RatBound (1000 * z ^ 2) p.momentError)
    (hframe : RatBound (30 * z) p.frameAccuracy) (hreq : RatBound z p.contamination)
    (hleak : RatBound z p.leakage) (hsep : RatBound z p.separation) :
    ∀ q ∈ values p, RatBound (2000 * z ^ 2) q := by
  have hzs : z ≤ z ^ 2 := le_self_pow₀ hz (by norm_num)
  have hm {c : ℕ} {q : ℚ} (h : RatBound (c * z) q) (hc : c ≤ 100) :
      RatBound (2000 * z ^ 2) q := h.mono (by nlinarith only [hzs, Nat.mul_le_mul_right z hc])
  intro q hq
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.mono (by omega)
  · exact hm hφ (by norm_num)
  · exact hm hω (by norm_num)
  · exact hm hv (by norm_num)
  · exact hm htail (by norm_num)
  · exact hm hK (by norm_num)
  · exact hm hWF (by norm_num)
  · exact hm hDF (by norm_num)
  · exact hm hR (by norm_num)
  · exact hm hσ (by norm_num)
  · exact hβ.mono (by omega)
  · exact hm hγ (by norm_num)
  · exact hE.mono (by omega)
  · exact hm hframe (by norm_num)
  · exact hreq.mono (by omega)
  · exact hleak.mono (by omega)
  · exact hsep.mono (by omega)

private theorem geometry_encoding (w : ℚ) (k z : ℕ) (p next : StepParams)
    (f : StepFormulas .identical w k next p) (hz : 1000000 ≤ z)
    (hw' : RatBound z w) (hnext : RatBound z next.leakage)
    (hkn : RatBound z (k : ℚ)) :
    RatBound (2 * z) p.straddle ∧ RatBound (30 * z) p.windowMass ∧
      RatBound (32 * z) p.verifyMass ∧ RatBound (34 * z) p.tail ∧
      RatBound (5 * z) p.K ∧ RatBound (8 * z) p.WF ∧ RatBound (80 * z) p.DF ∧
      RatBound (30 * z) p.R ∧ RatBound (70 * z) p.sigmaSq := by
  have hc (q : ℚ) (hq : q ∈ [1, 2, 4, 8, 16, 40, 64, 600, 4096]) :
      RatBound 50 q := encoding_constant q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    tauto)
  have hφ : RatBound (2 * z) p.straddle := by
    rw [f.straddle]
    exact (hnext.div (hc 4 (by simp))).mono (by omega)
  have hω : RatBound (30 * z) p.windowMass := by
    rw [f.window, ite_eq_right (by decide)]
    exact ((((hc 1 (by simp)).div ((hc 16 (by simp)).mul hkn)).mul
      ((hφ.div (hc 2 (by simp))).pow 9)).div (hc 16 (by simp))).mono (by omega)
  have hv : RatBound (32 * z) p.verifyMass := by
    rw [f.verify]
    exact ((hw'.mul hω).div (hc 8 (by simp))).mono (by omega)
  have htail : RatBound (34 * z) p.tail := by
    rw [f.tail]
    exact ((hφ.div (hc 64 (by simp))).min
      ((hv.div (hc 64 (by simp))).min (hw'.div (hc 4096 (by simp))))).mono (by omega)
  have hK : RatBound (5 * z) p.K := by
    rw [f.K, ite_eq_right (by decide)]
    exact RatBound.one.mono (by omega)
  have hWF : RatBound (8 * z) p.WF := by
    rw [f.WF]
    exact (up_bound (((hc 8 (by simp)).mul ((hc 40 (by simp)).div hw')).mul
      (sqrt_bound ((hc 1 (by simp)).div hφ)))).mono (by omega)
  have hDF : RatBound (80 * z) p.DF := by
    rw [f.DF]
    exact (up_bound (((hc 4 (by simp)).mul hWF).max
      (((hc 4 (by simp)).mul ((hc 40 (by simp)).div hw')).mul
        (sqrt_bound ((hc 1 (by simp)).div htail))))).mono (by omega)
  have hR : RatBound (30 * z) p.R := by
    rw [f.R, ite_eq_right (by decide)]
    exact (up_bound ((sqrt_bound (hc 40 (by simp))).div
      (hw'.div (hc 2 (by simp))))).mono (by omega)
  have hσ : RatBound (70 * z) p.sigmaSq := by
    rw [f.sigma]
    exact (((hc 600 (by simp)).div ((hw'.div (hc 2 (by simp))).pow 2)).add
      ((hc 2 (by simp)).mul (hR.pow 2))).mono (by omega)
  exact ⟨hφ, hω, hv, htail, hK, hWF, hDF, hR, hσ⟩

theorem params_encoding_bound {w : ℚ} (k h b : ℕ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hk : 2 ≤ k) (hkw : (k : ℚ) * w ≤ 1)
    (hh : h < k) (hwb : RatBound b w) :
    ∀ q ∈ values (params .identical w k h),
      RatBound (2000 * (b + ledgerCore .identical w k + 100) ^ 2) q := by
  let B := ledgerCore .identical w k
  let z := b + B + 100
  have hz : 1000000 ≤ z := by
    have hB := (ledgerCore_large k hw hkw).1
    dsimp only [z, B]
    omega
  have hrec (j : ℕ) (hj : j < k) (q : ℚ)
      (hq : ⌈1 / q⌉₊ ∈ parameterNumbers (params .identical w k j)) : 1 / q ≤ B := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast core_entry .identical w k j _ hj hq)
  by_cases ht : h < k - 1
  · let p := params .identical w k h
    let next := params .identical w k (h + 1)
    have hpeq : p = step .identical w k next := params_succ .identical w k h ht
    have f := step_formulas .identical w k next
    rw [← hpeq] at f
    have hnext : RatBound z next.leakage := by
      by_cases hnext : h + 1 < k - 1
      · have fe := (step_formulas .identical w k (params .identical w k (h + 2))).leakage
        rw [← params_succ .identical w k (h + 1) hnext] at fe
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
    have hw' : RatBound z w := hwb.mono (by dsimp only [z]; omega)
    have hkB : k ≤ B := (ledgerCore_large k hw hkw).2
    have hkn : RatBound z (k : ℚ) := by
      constructor
      · rw [abs_of_nonneg (by positivity)]
        exact_mod_cast hkB.trans ((by dsimp only [z]; omega : B ≤ z).trans
          (Nat.lt_two_pow_self (n := z)).le)
      · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
    obtain ⟨hφ, hω, hv, htail, hK, hWF, hDF, hR, hσ⟩ :=
      geometry_encoding w k z p next f hz hw' hnext hkn
    have ht : IdCov.tDegree w ≤ z := by
      change Nat.clog 2 ⌈w⁻¹⌉₊ + 3 ≤ z
      -- The original weight's bit length is also paid by the numerical ledger.
      have hinvB : (1 / w : ℚ) ≤ B := by
        have hn := (core_factors .identical w k).2.1
        have hn' : 8 / w ≤ (nWeight .identical w k : ℚ) := by
          unfold nWeight
          exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))
        exact (div_le_div_of_nonneg_right (by norm_num) hw.1.le).trans
          (hn'.trans (by exact_mod_cast hn))
      have hclB : ⌈w⁻¹⌉₊ ≤ B := Nat.ceil_le.mpr (by simpa only [one_div] using hinvB)
      have hlogB := (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := ⌈w⁻¹⌉₊)).le).trans hclB
      dsimp only [z]
      omega
    have herrors := error_encoding w p.subspaceAccuracy z hz hβ ht
    have hγ : RatBound (12 * z) p.isotropy := by
      rw [f.isotropy, ite_eq_right (by decide)]
      exact herrors.1
    have hE : RatBound (1000 * z ^ 2) p.momentError := by
      rw [f.moment, ite_eq_right (by decide)]
      exact herrors.2.1
    have hframe : RatBound (30 * z) p.frameAccuracy := by
      rw [f.frame, f.isotropy, ite_eq_right (by decide)]
      exact herrors.2.2
    have hsep : RatBound z p.separation := by
      have heq := f.separation
      have hb : p.separation ≤ B := (Nat.le_ceil _).trans
        (by exact_mod_cast core_entry .identical w k h _ hh (by simp [p, parameterNumbers]))
      rw [heq] at hb ⊢
      exact (up B hb).mono (by dsimp only [z]; omega)
    apply values_encoding p z (by omega)
      (by rw [f.weight]; exact hw') hφ hω hv htail hK hWF hDF hR hσ hβ hγ hE
      hframe hreq hleak hsep
  · have heq : params .identical w k h = terminal w := by
      simp only [params, Nat.sub_eq_zero_of_le (by omega : k - 1 ≤ h),
        Function.iterate_zero_apply]
    rw [heq]
    intro q hq
    apply (terminal_encoding hwb q hq).mono
    have hzs : z ≤ z ^ 2 := le_self_pow₀ (by omega) (by norm_num)
    dsimp only [z, B] at hzs ⊢
    omega

end ABBKS26.Assembly.Exec.RefineSynth.IdSchedule
