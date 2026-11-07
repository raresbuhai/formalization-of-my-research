module

public import BGHKLMM26.RobustMIS.Invariance
public import Background.GaussianCalculus
public import BGHKLMM26.Hardness.LTF

/-!
# The truncation error of the Gaussian extension

[BGHKLMM26, Theorem `MN-invariance`] (Mossel–Neeman, Theorem 7.1; [MOO10]), qualitative form: for
`u : {±1}^R → [0, 1]` with small influences, the extension `P_{u,r}` of `T_r u` to Gaussian space is
close in `L²(γ)` to its truncation to `[0, 1]`.

Proof: `T_r u ∈ [0, 1]` on the cube (`noise_mem`), so for the `2K`-Lipschitz
`Ψ_K(a) = min(dist(a, [0,1]), K)²`, `E_cube Ψ_K(T_r u) = 0` and `invariance` gives
`E_γ Ψ_K(P) ≤ ε/3`. The tail: with `Q = P^{≤d}` the degree-`d` truncation, pointwise
`dist(P, [0,1])² ≤ Ψ_K(P) + (2/K) Q² |P| + 2 (P - Q)²` (`Truncation.dist01_sq_le`), and
`E[Q² |P|] ≤ √(E Q⁴ · E P²) ≤ 3^d` (Cauchy–Schwarz, `bonami_gauss`), `E (P - Q)² ≤ r^d`
(`integral_mlEval_sq`). Choose `d`, then `K`, then `τ`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic Gaussian BGHKLMM26.Hard

namespace Truncation

variable {R : ℕ}

/-- The distance to `[0, 1]`. -/
theorem dist01_eq (a : ℝ) : |a - clamp01 a| = max (max (-a) (a - 1)) 0 := by
  unfold clamp01
  rcases le_total a 0 with h | h
  · have e1 : max 0 (min 1 a) = 0 := by rw [min_eq_right (by linarith)]; exact max_eq_left h
    have e2 : max (max (-a) (a - 1)) 0 = -a := by
      rw [max_eq_left (by linarith : a - 1 ≤ -a)]; exact max_eq_left (by linarith)
    rw [e1, e2, sub_zero, abs_of_nonpos h]
  rcases le_total a 1 with h' | h'
  · have e1 : max 0 (min 1 a) = a := by rw [min_eq_right h']; exact max_eq_right h
    have e2 : max (max (-a) (a - 1)) 0 = 0 := max_eq_right (max_le (by linarith) (by linarith))
    rw [e1, e2, sub_self, abs_zero]
  · have e1 : max 0 (min 1 a) = 1 := by rw [min_eq_left h']; exact max_eq_right zero_le_one
    have e2 : max (max (-a) (a - 1)) 0 = a - 1 := by
      rw [max_eq_right (by linarith : -a ≤ a - 1)]; exact max_eq_left (by linarith)
    rw [e1, e2, abs_of_nonneg (by linarith)]

theorem abs_dist01_sub_le (a b : ℝ) :
    |(|a - clamp01 a|) - (|b - clamp01 b|)| ≤ |a - b| := by
  rw [dist01_eq, dist01_eq]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · rw [show -a - -b = -(a - b) by ring, abs_neg]
  · rw [show a - 1 - (b - 1) = a - b by ring]

theorem dist01_le_abs (a : ℝ) : |a - clamp01 a| ≤ |a| := by
  rw [dist01_eq]
  refine max_le (max_le (neg_le_abs a) ?_) (abs_nonneg a)
  linarith [le_abs_self a]

theorem dist01_eq_zero {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : |a - clamp01 a| = 0 := by
  rw [dist01_eq]
  exact max_eq_right (max_le (by linarith) (by linarith))

/-- The test function `Ψ_K(a) = min(dist(a, [0,1]), K)²`. -/
noncomputable def psiK (K a : ℝ) : ℝ := min (|a - clamp01 a|) K ^ 2

theorem psiK_lip {K : ℝ} (hK : 0 ≤ K) (a b : ℝ) : |psiK K a - psiK K b| ≤ 2 * K * |a - b| := by
  unfold psiK
  set x := min (|a - clamp01 a|) K
  set y := min (|b - clamp01 b|) K
  have hx0 : 0 ≤ x := le_min (abs_nonneg _) hK
  have hy0 : 0 ≤ y := le_min (abs_nonneg _) hK
  have hxK : x ≤ K := min_le_right _ _
  have hyK : y ≤ K := min_le_right _ _
  have hxy : |x - y| ≤ |a - b| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    exact max_le (abs_dist01_sub_le a b) (abs_nonneg _)
  rw [sq_sub_sq, abs_mul]
  calc |x + y| * |x - y| ≤ |a - b| * (2 * K) := by
        rw [mul_comm]
        refine mul_le_mul hxy ?_ (abs_nonneg _) (abs_nonneg _)
        rw [abs_of_nonneg (by linarith)]
        linarith
    _ = 2 * K * |a - b| := by ring

theorem psiK_nonneg (K a : ℝ) : 0 ≤ psiK K a := sq_nonneg _

/-- The pointwise tail bound
`(P - clamp P)² ≤ Ψ_K(P) + (2/K) Q² |P| + 2 (P - Q)²`. -/
theorem dist01_sq_le {K : ℝ} (hK : 0 < K) (p q : ℝ) :
    (p - clamp01 p) ^ 2 ≤ psiK K p + 2 / K * (q ^ 2 * |p|) + 2 * (p - q) ^ 2 := by
  have hD := dist01_le_abs p
  have h2 : 0 ≤ 2 / K * (q ^ 2 * |p|) := by positivity
  have h3 : 0 ≤ 2 * (p - q) ^ 2 := by positivity
  rcases lt_or_ge (|p|) K with h | h
  · have : psiK K p = (p - clamp01 p) ^ 2 := by
      rw [psiK, min_eq_left (hD.trans h.le), sq_abs]
    rw [this]; linarith
  · have e1 : (p - clamp01 p) ^ 2 ≤ p ^ 2 := by
      rw [← sq_abs, ← sq_abs p]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have e2 : p ^ 2 ≤ 2 * q ^ 2 + 2 * (p - q) ^ 2 := by nlinarith [sq_nonneg (p - 2 * q)]
    have e3 : 2 * q ^ 2 ≤ 2 / K * (q ^ 2 * |p|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hK]
      have := mul_le_mul_of_nonneg_left h (sq_nonneg q)
      nlinarith
    linarith [psiK_nonneg K p]

theorem mlEval_sub (c e : Cube (Fin R) → ℝ) (x : Fin R → ℝ) :
    mlEval (fun s ↦ c s - e s) x = mlEval c x - mlEval e x := by
  simp only [mlEval, sub_mul, Finset.sum_sub_distrib]

theorem smoothC_sq_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (c : Cube (Fin R) → ℝ)
    (s : Cube (Fin R)) : smoothC r c s ^ 2 ≤ c s ^ 2 := by
  rw [smoothC, mul_pow]
  have h1 : (r ^ sdeg s) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hr0 hr1)
  nlinarith [sq_nonneg (c s)]

theorem sum_coefficient_sq_le (u : Cube (Fin R) → ℝ) (h01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) :
    ∑ s, coefficient u s ^ 2 ≤ 1 := by
  rw [walsh_parseval]
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  nlinarith [h01 x]

end Truncation

open Truncation in
/-- **Truncation**: `‖P_{u,r} - clamp(P_{u,r})‖²_{L²(γ)} = o_{τ↓0}(1)`. -/
theorem truncation {r ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ τ > 0, ∀ (R : ℕ) (u : Cube (Fin R) → ℝ), (∀ x, 0 ≤ u x ∧ u x ≤ 1) →
      (∀ i, influence i u ≤ τ) →
        ∫ G, (gaussExt r u G - clamp01 (gaussExt r u G)) ^ 2 ∂gm R ≤ ε := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, r ^ d < ε / 6 := exists_pow_lt_of_lt_one (by positivity) hr1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 6 * 3 ^ d / ε + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨τ, hτ, hinv⟩ := invariance (M := 1) (K := 2 * K) hr0 hr1 (ε := ε / 3) (by positivity)
  refine ⟨τ, hτ, fun R u h01 hinf ↦ ?_⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = coefficient u := ⟨_, rfl⟩
  have hc : ∑ s, c s ^ 2 ≤ 1 := hcdef ▸ sum_coefficient_sq_le u h01
  have hcinf : ∀ i, inflC c i ≤ τ := fun i ↦ hcdef ▸ hinf i
  have hΨ : LipPair (fun a _ ↦ psiK K a) (2 * K) := fun a b a' b' ↦
    (psiK_lip hK0.le a a').trans (by nlinarith [abs_nonneg (b - b'), abs_nonneg (a - a')])
  have h1 := hinv R c c hc hc hcinf hcinf _ hΨ
  simp only at h1
  have hcube : (𝔼 x, psiK K (mlEval (smoothC r c) (bitVec x))) = 0 := by
    rw [hcdef]
    simp_rw [mlEval_smoothC_bitVec]
    refine Finset.expect_eq_zero fun x _ ↦ ?_
    obtain ⟨h0, h1⟩ := noise_mem (by linarith) hr1.le h01 x
    rw [psiK, dist01_eq_zero h0 h1, min_eq_left hK0.le]
    norm_num
  rw [hcube, zero_sub, abs_neg] at h1
  have hpsi : ∫ G, psiK K (mlEval (smoothC r c) G) ∂gm R ≤ ε / 3 := (le_abs_self _).trans h1
  -- the degree-`d` truncation `Q`
  obtain ⟨e, he⟩ : ∃ e : Cube (Fin R) → ℝ,
      e = fun s ↦ if sdeg s ≤ d then smoothC r c s else 0 := ⟨_, rfl⟩
  have hed : ∀ s, d < sdeg s → e s = 0 := fun s hs ↦ by
    rw [he]; simp [not_le.mpr hs]
  have hsc : ∑ s, smoothC r c s ^ 2 ≤ 1 :=
    (Finset.sum_le_sum fun s _ ↦ smoothC_sq_le hr0.le hr1.le c s).trans hc
  have hes : ∑ s, e s ^ 2 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun s _ ↦ ?_) hsc
    rw [he]; dsimp only; split_ifs <;> simp [sq_nonneg]
  have hQ4 : ∫ G, mlEval e G ^ 4 ∂gm R ≤ 9 ^ d := by
    refine (bonami_gauss e hed).trans ?_
    have h0 : 0 ≤ ∑ s, e s ^ 2 := Finset.sum_nonneg fun s _ ↦ sq_nonneg _
    have : (∑ s, e s ^ 2) ^ 2 ≤ 1 := pow_le_one₀ h0 hes
    calc (9 : ℝ) ^ d * (∑ s, e s ^ 2) ^ 2 ≤ 9 ^ d * 1 := by gcongr
      _ = 9 ^ d := mul_one _
  have hP2 : ∫ G, mlEval (smoothC r c) G ^ 2 ∂gm R ≤ 1 := by
    rw [integral_mlEval_sq]; exact hsc
  have hPQ : ∫ G, (mlEval (smoothC r c) G - mlEval e G) ^ 2 ∂gm R ≤ r ^ d := by
    have : (fun G : Gs R ↦ (mlEval (smoothC r c) G - mlEval e G) ^ 2) =
        fun G : Gs R ↦ mlEval (fun s ↦ smoothC r c s - e s) G ^ 2 := by
      funext G; rw [mlEval_sub]
    rw [this, integral_mlEval_sq]
    calc ∑ s, (smoothC r c s - e s) ^ 2 ≤ ∑ s, r ^ d * c s ^ 2 := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          rw [he]; dsimp only
          split_ifs with h
          · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            positivity
          · rw [sub_zero, smoothC, mul_pow, ← pow_mul]
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
      _ = r ^ d * ∑ s, c s ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ r ^ d * 1 := by gcongr
      _ = r ^ d := mul_one _
  -- Cauchy–Schwarz for `E[Q² |P|]`
  have hmP := memLp_mlEval (R := R) (smoothC r c) 2 (by simp)
  have hmQ4 := memLp_mlEval (R := R) e 4 (by simp)
  have hmQ2 : MemLp (fun G : Gs R ↦ mlEval e G ^ 2) 2 (gm R) := by
    have hcont := continuous_mlEval (R := R) e
    refine (memLp_two_iff_integrable_sq (hcont.pow 2).aestronglyMeasurable).2 ?_
    have := (memLp_mlEval (R := R) e ((4 : ℕ) : ENNReal) (by simp)).integrable_norm_pow
      (by norm_num)
    refine this.congr (ae_of_all _ fun G ↦ ?_)
    simp only [Real.norm_eq_abs, Pi.pow_apply]
    rw [← pow_mul, show 2 * 2 = 4 by rfl, Even.pow_abs (by decide)]
  have hmPabs : MemLp (fun G : Gs R ↦ |mlEval (smoothC r c) G|) 2 (gm R) := by
    simpa [Real.norm_eq_abs] using hmP.norm
  have hCS : ∫ G, mlEval e G ^ 2 * |mlEval (smoothC r c) G| ∂gm R ≤ 3 ^ d := by
    have h := sq_integral_mul_le hmQ2 hmPabs
    have e1 : ∫ G, (mlEval e G ^ 2) ^ 2 ∂gm R = ∫ G, mlEval e G ^ 4 ∂gm R := by
      congr 1; funext G; ring
    have e2 : ∫ G, |mlEval (smoothC r c) G| ^ 2 ∂gm R = ∫ G, mlEval (smoothC r c) G ^ 2 ∂gm R := by
      congr 1; funext G; rw [sq_abs]
    rw [e1, e2] at h
    have h9 : (∫ G, mlEval e G ^ 2 * |mlEval (smoothC r c) G| ∂gm R) ^ 2 ≤ (3 ^ d) ^ 2 := by
      have h0 : 0 ≤ ∫ G, mlEval (smoothC r c) G ^ 2 ∂gm R := integral_nonneg fun G ↦ sq_nonneg _
      calc _ ≤ _ := h
        _ ≤ 9 ^ d * 1 := mul_le_mul hQ4 hP2 h0 (by positivity)
        _ = (3 ^ d) ^ 2 := by rw [mul_one, ← pow_mul, mul_comm, pow_mul]; norm_num
    exact abs_le_of_sq_le_sq' h9 (by positivity) |>.2
  -- integrate the pointwise bound
  have hcP := continuous_mlEval (R := R) (smoothC r c)
  have hcQ := continuous_mlEval (R := R) e
  have hpsiC : Continuous (psiK K) := by unfold psiK clamp01; fun_prop
  have hi1 : Integrable (fun G : Gs R ↦ psiK K (mlEval (smoothC r c) G)) (gm R) := by
    refine hmP.integrable_sq.mono' (hpsiC.comp hcP).aestronglyMeasurable (ae_of_all _ fun G ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psiK_nonneg _ _), psiK]
    set p := mlEval (smoothC r c) G
    have h0 : 0 ≤ min (|p - clamp01 p|) K := le_min (abs_nonneg _) hK0.le
    calc min (|p - clamp01 p|) K ^ 2 ≤ |p| ^ 2 :=
          pow_le_pow_left₀ h0 ((min_le_left _ _).trans (dist01_le_abs p)) 2
      _ = p ^ 2 := sq_abs p
  have hi2 : Integrable (fun G : Gs R ↦ mlEval e G ^ 2 * |mlEval (smoothC r c) G|) (gm R) :=
    hmQ2.integrable_mul hmPabs
  have hi3 : Integrable (fun G : Gs R ↦ (mlEval (smoothC r c) G - mlEval e G) ^ 2) (gm R) :=
    (hmP.sub (memLp_mlEval (R := R) e 2 (by simp))).integrable_sq
  have hmain : ∫ G, (gaussExt r u G - clamp01 (gaussExt r u G)) ^ 2 ∂gm R ≤
      ∫ G, (psiK K (mlEval (smoothC r c) G) +
        2 / K * (mlEval e G ^ 2 * |mlEval (smoothC r c) G|) +
        2 * (mlEval (smoothC r c) G - mlEval e G) ^ 2) ∂gm R := by
    refine integral_mono_of_nonneg (ae_of_all _ fun G ↦ sq_nonneg _)
      ((hi1.add (hi2.const_mul _)).add (hi3.const_mul _)) (ae_of_all _ fun G ↦ ?_)
    simp only [gaussExt, ← hcdef]
    exact dist01_sq_le hK0 _ _
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul] at hmain
  rotate_left
  · exact hi1
  · exact hi2.const_mul _
  · exact hi1.add (hi2.const_mul _)
  · exact hi3.const_mul _
  have hKb : 2 / K * 3 ^ d ≤ ε / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK0, hK]
    have : (0 : ℝ) < 3 ^ d := by positivity
    field_simp
    nlinarith
  have h2K : 0 ≤ 2 / K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hCS h2K]

end BGHKLMM26.RobustMIS
