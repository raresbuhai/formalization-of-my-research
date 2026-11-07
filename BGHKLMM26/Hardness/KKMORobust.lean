module

public import BGHKLMM26.Hardness.KKMO
public import BGHKLMM26.Hardness.LTF
public import BGHKLMM26.Hardness.KKMORobustFourier
public import BGHKLMM26.Hardness.KKMORobustJensen
public import BGHKLMM26.Hardness.KKMORobustRegular

/-!
# The robust inverse of soundness

[BGHKLMM26, Lemma 5.3], with the error of Remark 7.3: assuming the robust Majority is Stablest
theorem (`BGHKLMM26.Hard.RobustMIS`), a cut of the KKMO graph of an instance of value at most `ε`
that cuts at least `arccos ρ / π - η` has tables `f_v` within `C √(η log(1/η)) + ξ` of LTFs on
average (`BGHKLMM26.Hard.kkmo_robust`).

The paper applies Theorem 7.1 to `g_u`, which is smooth because its reduction adds noise. Here the
reduction has no noise, the good left vertices are those whose `g_u` has small low-degree
influences (`BGHKLMM26.Hard.kkmo_few_bad`), and Theorem 7.1 is applied to the smoothed
`T_{1-γ} g_u`, whose influences are then small, whose cut value is within `O(γ)` of that of `g_u`
(`KKMORobustFourier`), and which still bounds the distance of the tables (Lemma bound-1,
`KKMORobustRegular`). The averaging of Lemma bound-2 (Claims c-1 to c-3, Jensen's inequality for
`√(z log(1/z))`) is `KKMORobustJensen`; the good vertices cut at most `arccos ρ / π + t` by Majority
is Stablest with low-degree influences (`BGHKLMM26.Hard.cut_le_of_lowInfluence`).

Unlike the paper, `C` and `η₀` depend only on `ρ` (through Theorem 7.1), and all the error terms
(the bad vertices, the smoothing, the slack of Majority is Stablest, the `ξ` of Theorem 7.1) are
absorbed into `ξ` by the choice of `ε₁`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

namespace KKMORobust

theorem kkmoCut_nil (ρ : ℝ) (R : ℕ) (f : ℕ → Cube (Fin R) → Bool) : kkmoCut ρ R [] f = 0 := by
  simp [kkmoCut]

theorem half_lt_arccos_div_pi {ρ : ℝ} (hρ0 : ρ < 0) : 1 / 2 < Real.arccos ρ / Real.pi := by
  rw [lt_div_iff₀ Real.pi_pos]
  have := Real.pi_div_two_lt_arccos.mpr hρ0
  linarith

/-- The choice of the parameters: the smoothing `u = 1 - γ`, the degree `K` and the threshold
`τ'` of the low-degree influences, for the error terms `t` of the cut values. -/
theorem exists_params {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) {t τM : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1 / 2) (hτM : 0 < τM) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (1 - u) / (1 - |ρ|) = t ∧ ∃ K : ℕ, ∃ τ' : ℝ, 0 < τ' ∧ τ' ≤ τM ∧
      u ^ (2 * (K + 1)) ≤ τM ∧
      ∀ (n : ℕ) (g : Cube (Fin n) → ℝ), (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ') →
        cutValue ρ g ≤ Real.arccos ρ / Real.pi + t := by
  have habs : |ρ| = -ρ := abs_of_neg hρ0
  refine ⟨1 - t * (1 + ρ), by nlinarith, by nlinarith, ?_, ?_⟩
  · have hρ' : (1 + ρ) ≠ 0 := by linarith
    rw [habs, show 1 - (1 - t * (1 + ρ)) = t * (1 + ρ) by ring, show 1 - -ρ = 1 + ρ by ring,
      mul_div_assoc, div_self hρ', mul_one]
  obtain ⟨K₀, -, τc, hτc, hcut⟩ := cut_le_of_lowInfluence hρ1 hρ0 ht
  have hu1 : 1 - t * (1 + ρ) < 1 := by nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hτM hu1
  refine ⟨max K₀ n, min τc τM, lt_min hτc hτM, min_le_right _ _, ?_, ?_⟩
  · refine le_trans ?_ hn.le
    exact pow_le_pow_of_le_one (by nlinarith) hu1.le (by omega)
  · intro n g hg hinf
    exact hcut n g hg fun i ↦ (cutoffInfluence_mono (le_max_left _ _) i _).trans_lt
      ((hinf i).trans_le (min_le_left _ _))

end KKMORobust

open KKMORobust

/-- **Robust inverse of soundness** [BGHKLMM26, Lemma 5.3], Eldan form. -/
theorem kkmo_robust (hMIS : RobustMIS) {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧ ∀ ξ : ℝ, 0 < ξ → ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ (R : ℕ) (G : UGInstance), Good R G → ugValue G ≤ ε →
        ∀ (f : ℕ → Cube (Fin R) → Bool) (η : ℝ), 0 ≤ η → η ≤ η₀ →
          Real.arccos ρ / Real.pi - η ≤ kkmoCut ρ R G.2.2.2 f →
          (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x))) / G.2.1 ≤
            C * Real.sqrt (η * Real.log (1 / η)) + ξ := by
  obtain ⟨CM, ηM, hCM, hηM, hηM1, hM⟩ := hMIS ρ hρ1 hρ0
  refine ⟨CM + 1 / ηM, 1 / 4, by positivity, by norm_num, by norm_num, fun ξ hξ ↦ ?_⟩
  obtain ⟨τM, hτM, hM'⟩ := hM (ξ / 2) (by linarith)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := exists_sqrt_negMulLog_small (C := CM) (ε := ξ / 8) (by linarith)
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = min (min (δ₀ / 4) (ηM * ξ / 16)) (min (ξ / 16) (1 / 40)) :=
    ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htδ : t ≤ δ₀ / 4 := by rw [htdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have htη : t ≤ ηM * ξ / 16 := by rw [htdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have htξ : t ≤ ξ / 16 := by rw [htdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : t ≤ 1 / 40 := by rw [htdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨u, hu0, hu1, hut, K, τ', hτ', hτ'M, huK, hcutle⟩ :=
    exists_params hρ1 hρ0 ht0 (by linarith) hτM
  obtain ⟨ε₁, hε₁, hfew⟩ := kkmo_few_bad K hτ' ht0
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ R G hG hval f η hη0 hη1 hcut ↦ ?_⟩
  set s := Real.arccos ρ / Real.pi with hsdef
  have hs : 1 / 2 < s := half_lt_arccos_div_pi hρ0
  by_cases hcs : G.2.2.2 = []
  · rw [hcs, kkmoCut_nil] at hcut
    linarith
  have hm : 0 < G.1 := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hcs
    exact Nat.zero_lt_of_lt (hG.1 c hc).1
  rw [kkmoCut_eq ρ hG hcs f] at hcut
  have hρabs : |ρ| < 1 := abs_lt.mpr ⟨hρ1, by linarith⟩
  set g : ℕ → Cube (Fin R) → ℝ := avgTable G.2.2.2 f with hgdef
  have hg : ∀ w x, 0 ≤ g w x ∧ g w x ≤ 1 := fun w x ↦ avgTable_mem _ f w x
  have hTg : ∀ w x, 0 ≤ noise u (g w) x ∧ noise u (g w) x ≤ 1 :=
    fun w x ↦ noise_mem' hu0 hu1 (hg w) x
  have hbound := avg_bound hm
    (fun w ↦ ∃ i, τ' ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable G.2.2.2 f w x - 1))
    (fun w ↦ cutValue ρ (g w)) (fun w ↦ cutValue ρ (noise u (g w)))
    (fun w ↦ ltfDist (noise u (g w))) (s := s) (η := η) (η₁ := ηM) (κ := t) (ν := t)
    (ξ₂ := t) (ξ' := ξ / 2) (CM := CM)
    (by rw [hsdef]; positivity) hη0 hηM hηM1.le ht0.le ht0.le ht0.le (by linarith) hCM.le
    (by linarith) (hfew ε hε hεε₁ R G hG hval f) hcut
    (fun w _ ↦ by rw [← hut]; exact cutValue_noise_ge hρabs hu0 hu1 (hg w))
    (fun w _ ↦ cutValue_le_one hρabs.le (hTg w))
    (fun w _ ↦ ltfDist_le_one (hTg w))
    (fun w _ hgood ↦ by
      push Not at hgood
      refine hcutle R (noise u (g w)) (hTg w) fun i ↦ ?_
      rw [← noise_two_mul_sub_one]
      exact (cutoffInfluence_noise_le u hu0 hu1 K i _).trans_lt (hgood i))
    (fun w _ hgood hcw ↦ by
      push Not at hgood
      have hinf : ∀ i, influence i (noise u (g w)) ≤ τM := fun i ↦ by
        have := influence_noise_le' hu0 hu1 K i (hg w)
        have := hgood i
        linarith
      have hZ0 : 0 ≤ max 0 (s - cutValue ρ (noise u (g w))) := le_max_left _ _
      have hZ1 : max 0 (s - cutValue ρ (noise u (g w))) ≤ ηM := max_le hηM.le (by linarith)
      have hZ2 : s - max 0 (s - cutValue ρ (noise u (g w))) ≤ cutValue ρ (noise u (g w)) := by
        have := le_max_right 0 (s - cutValue ρ (noise u (g w))); linarith
      have := hM' R (noise u (g w)) (hTg w) hinf _ hZ0 hZ1 hZ2
      rw [negMulLog_eq_mul_log_one_div]
      exact this)
  have hright := avg_right_le hG hcs f hu0 hu1
  refine hright.trans (hbound.trans ?_)
  -- the final bookkeeping
  rw [← negMulLog_eq_mul_log_one_div]
  obtain ⟨X, hX⟩ : ∃ X, X = √(Real.negMulLog η) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = √(Real.negMulLog (t + t + t)) := ⟨_, rfl⟩
  rw [← hX, ← hY]
  have hηX : η ≤ X := by rw [hX]; exact le_sqrt_negMulLog hη0 (by linarith)
  have hY' : CM * Y < ξ / 8 := by rw [hY]; exact hδ₀' _ (by linarith) (by linarith)
  have h1 : (η + (t + t + t)) / ηM = η / ηM + 3 * t / ηM := by ring
  have h2 : η / ηM ≤ X / ηM := div_le_div_of_nonneg_right hηX hηM.le
  have h3 : 3 * t / ηM ≤ 3 * ξ / 16 := by
    rw [div_le_iff₀ hηM]; linarith
  have h4 : (CM + 1 / ηM) * X = CM * X + X / ηM := by ring
  rw [h1, h4]
  nlinarith

end BGHKLMM26.Hard
