module

public import BGHKLMM26.Hardness.Main

/-!
# Soundness of the reduction for a given instance

`BGHKLMM26.IntGap.sound_at`: the soundness half of the proof of Theorem 1.2
(`BGHKLMM26.Hard.randReducible_at`), for any good instance with enough labels and small value
instead of the instances given by the Unique Games Conjecture. For every large `d` there are a
dyadic correlation `ρ_d = 1 - 2q/2^b ∈ (-1, 0)` within `C/d` of `ρ*` in `(1 - ρ)/2`, a number of
labels `R₀` and a value `ε₀` such that, with `R ≥ R₀` labels and value at most `ε₀`, the
reduction with parameters `(R, b, q, ⌊d/10⌋, d)` outputs a graph of maximum degree at most `d`
and Max-Cut value at most `s* + C log d / d` with probability `9/10`.

The proof is the soundness branch of `randReducible_at`: KKMO soundness
(`BGHKLMM26.Hard.kkmo_sound`), the robust inverse from Theorem 7.1
(`BGHKLMM26.Hard.kkmo_robust`, `BGHKLMM26.Hard.hrob_of_robust`), the sparsification
(`BGHKLMM26.Hard.sparsify_no_at`), and `BGHKLMM26.Hard.no_case`, with `R` large enough for the
counting of LTFs and for `((1 + |ρ_d|)/2)^R ≤ 1/(2 D²)`.
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open UniqueGames

open Hard Cslib

/-- **Soundness of the reduction at a given instance.** -/
theorem sound_at (hMIS : RobustMIS) :
    ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ 30 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∃ (b q R₀ : ℕ) (ε₀ : ℝ),
      0 < ε₀ ∧ q ≤ 2 ^ b ∧ -1 < 1 - 2 * (q : ℝ) / 2 ^ b ∧ 1 - 2 * (q : ℝ) / 2 ^ b < 0 ∧
      (1 - GW.rhoStar) / 2 - C / d ≤ (1 - (1 - 2 * (q : ℝ) / 2 ^ b)) / 2 ∧
      ∀ R : ℕ, R₀ ≤ R →
        ((1 + |1 - 2 * (q : ℝ) / 2 ^ b|) / 2) ^ R ≤ 1 / (2 * ((d / 10 : ℕ) : ℝ) ^ 2) ∧
        ∀ G : UGInstance, GoodI R G → G.2.2.2 ≠ [] → ugValue G ≤ ε₀ →
          9 / 10 ≤ ((ProbComp.eval (redProg ⟨R, b, q, d / 10, d⟩ G)).toOuterMeasure
            (maxCutGap d ((1 - GW.rhoStar) / 2 - C / d)
              (Real.arccos GW.rhoStar / Real.pi + C * Real.log d / d)).no).toReal := by
  have hw := GW.rhoStar_mem_window
  obtain ⟨CK, ηK, hCK, hηK, hηK1, hrobK⟩ :=
    kkmo_robust hMIS (ρ := GW.rhoStar) (by linarith [hw.1]) (by linarith [hw.2])
  obtain ⟨C₀n, D₀n, hC₀n, hSn⟩ := sparsify_no_at (C₁ := 2 * CK + 1)
    (η₀ := min (ηK / 2) (1 / 6)) (by positivity) (by positivity)
    ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨M, hM, hlip⟩ := kkmoCut_lipschitz (r := 9 / 10) (by norm_num) (by norm_num)
  have hKC : 0 ≤ lamK (2 * CK + 1) * C₀n :=
    mul_nonneg (zero_le_one.trans (one_le_lamK _)) hC₀n.le
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 20 * (lamK (2 * CK + 1) * C₀n) + 3 := ⟨_, rfl⟩
  have hC3 : 3 ≤ C := by rw [hCdef]; linarith
  have hCK' : 20 * lamK (2 * CK + 1) * C₀n ≤ C := by rw [hCdef]; linarith
  obtain ⟨d₁, hd₁⟩ := eventually_small C _ (20 * lamK (2 * CK + 1)) (sub_pos.2 gap_pos)
  refine ⟨C, max (max 30 (10 * D₀n)) d₁, by linarith, le_max_of_le_left (le_max_left _ _),
    fun d hd ↦ ?_⟩
  obtain ⟨hsmall, hlam7⟩ := hd₁ d (le_of_max_le_right hd)
  have hd30 : 30 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hdD : 10 * D₀n ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hD3, hDn, hΔ, hΔ2, hlam0, hlamle, hlam1, -, htv, -⟩ :=
    d_facts (2 * CK + 1) hd30 hdD hlam7
  obtain ⟨b, q, hq, hρd1, hρd0, hρdabs, hsd, hMd, -, hhi⟩ := exists_rho_d hM hlam0 hdr
  have hρsabs : |GW.rhoStar| ≤ 9 / 10 := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
  -- `ε₀`
  obtain ⟨ε₁s, hε₁s, hsound⟩ :=
    kkmo_sound hρd1 hρd0 (show 0 < lam (2 * CK + 1) (d / 10) / 8 by positivity)
  have hξr : 0 < Real.sqrt (lam (2 * CK + 1) (d / 10)) := Real.sqrt_pos.2 hlam0
  obtain ⟨ε₁r, hε₁r, hrob⟩ := hrobK _ hξr
  -- `R₀`
  obtain ⟨A₀, n₀n, hA₀, hSn'⟩ := hSn (d / 10) hDn
  have hκ1 : (1 + |1 - 2 * (q : ℝ) / 2 ^ b|) / 2 < 1 := by linarith
  obtain ⟨Ra, hRa⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (2 * ((d / 10 : ℕ) : ℝ) ^ 2) by positivity) hκ1
  obtain ⟨Rc, hRc⟩ := eventually_sq_le_two_pow A₀
  refine ⟨b, q, max (max Ra Rc) n₀n, min ε₁s ε₁r, lt_min hε₁s hε₁r, hq, hρd1, hρd0, ?_,
    fun R hR ↦ ?_⟩
  · have h1 : 1 / (d : ℝ) ≤ C / d := div_le_div_of_nonneg_right (by linarith) hdr.le
    have h0 : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  have hRa' : Ra ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRc' : Rc ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hnn : n₀n ≤ 2 ^ R := le_trans (le_trans (le_max_right _ _) hR) Nat.lt_two_pow_self.le
  have hκ : ((1 + |1 - 2 * (q : ℝ) / 2 ^ b|) / 2) ^ R ≤ 1 / (2 * ((d / 10 : ℕ) : ℝ) ^ 2) :=
    (pow_le_pow_of_le_one (by positivity) hκ1.le hRa').trans hRa.le
  refine ⟨hκ, fun G hG _ hval ↦ ?_⟩
  -- soundness
  let P : Prm := ⟨R, b, q, d / 10, d⟩
  have hA : ((2 ^ P.R + 1) ^ (P.R + 1) : ℝ) ≤ Real.exp (2 ^ P.R / A₀) :=
    ltf_count_le_exp hA₀ (hRc R hRc')
  have hss0 : 0 ≤ Real.arccos GW.rhoStar / Real.pi :=
    div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
  have hss1 : Real.arccos GW.rhoStar / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; exact Real.arccos_le_pi _
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  obtain ⟨hs', hsc⟩ := no_arith hdr hC₀n.le (K := 20 * lamK (2 * CK + 1)) hCK' hlog0
    hlamle hsmall
  have hlogd : 0 ≤ C * Real.log d / d := by
    have : 0 ≤ C := by linarith
    positivity
  have hε0 : 0 < min ε₁s ε₁r := lt_min hε₁s hε₁r
  refine no_case (P := P) hG hq hSn' hnn hΔ (show 1 ≤ d / 10 by omega) hκ hΔ2 hA hss0 hss1 htv
    (fun f' ↦ ?_) ?_ hs' (by linarith) hsc
  · have := hsound _ hε0 (min_le_left _ _) R G hG hval f'
    exact this.trans (by linarith)
  · refine hrob_of_robust (ρ := GW.rhoStar) hlam0 (min_le_left _ _) hCK.le
      (hrob _ hε0 (min_le_right _ _) R G hG hval) fun f ↦ ?_
    exact (hlip GW.rhoStar _ hρsabs hρdabs R G hG f).trans hMd

end BGHKLMM26.IntGap
