module

public import BHJK25.Spectral.LDA.Symmetry
public import BHJK25.Spectral.Legendre

/-!
# The low-degree advantage for general parameters

[BHJK25, Lemmas 3.8–3.10] for general parameters `γ`, `m`, `λ*`: the planted distribution has
degree-`D` advantage at most `(1/√(1 - γ) + 10 D³ λ*/√γ)/√m` over the null distribution when
`0 < γ < 1`, `m ≥ 1` and `0 ≤ λ* ≤ 1/(2 D (D + 1))`
(`BHJK25.Spectral.LDAAux.advantage_spectral`).

For a polynomial `f` of degree `d`, let `φ(λ, U) = f(U diag(λ) Uᵀ)` and let `G` be its projection
on the last coordinate of `λ`, a polynomial of degree at most `d` (the projections on all
coordinates are the same). Then `E_P f = G(λ*)`, `E_Q f = E_{μ_γ} G`, and
`Var_Q f ≥ m Var_{μ_γ} G` (the projections on the `m` coordinates are orthogonal), so the
Legendre bound on `G(λ*) - E_{μ_γ} G` gives the advantage.
-/

@[expose] public section

namespace BHJK25.Spectral.LDAAux

open MeasureTheory ProbabilityTheory Polynomial

variable {n m : ℕ}

/-- The last coordinate of `ℝ^m`, which carries the spike of the planted distribution. -/
def lastIdx (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

theorem plantedEig_eq (γ spike : ℝ) (hm : 0 < m) :
    plantedEig γ m spike = Measure.pi
      (Function.update (fun _ : Fin m ↦ eigLaw γ) (lastIdx hm) (Measure.dirac spike)) := by
  unfold plantedEig
  congr 1
  funext i
  by_cases h : (i : ℕ) + 1 = m
  · have hi : i = lastIdx hm := Fin.ext (by simp only [lastIdx]; omega)
    rw [ite_eq_left h, hi, Function.update_self]
  · have hi : i ≠ lastIdx hm := fun h' ↦ h (by rw [h']; simp only [lastIdx]; omega)
    rw [ite_eq_right h, Function.update_of_ne hi]

theorem isProbabilityMeasure_plantedCoord {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (spike : ℝ)
    (i : Fin m) :
    IsProbabilityMeasure (if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ) := by
  split_ifs
  · infer_instance
  · exact isProbabilityMeasure_eigLaw hγ0 hγ1

theorem allMoments_plantedCoord {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (spike : ℝ) (i : Fin m) :
    AllMoments (if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ) fun x ↦ x := by
  split_ifs
  · exact allMoments_dirac spike
  · have := isProbabilityMeasure_eigLaw hγ0 hγ1
    exact allMoments_eigLaw γ

/-- `K √V' ≤ (K/√m) √V` when `m V' ≤ V`: the last step of the chain. -/
theorem mul_sqrt_le_of_mul_le {K V V' : ℝ} (hK : 0 ≤ K) (hV' : 0 ≤ V') (hm : 0 < m)
    (h : (m : ℝ) * V' ≤ V) : K * √V' ≤ K / √m * √V := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm'
  have h1 : √V' ≤ √V / √m := by
    rw [le_div_iff₀ hsm, ← Real.sqrt_mul hV', mul_comm V']
    exact Real.sqrt_le_sqrt h
  calc K * √V' ≤ K * (√V / √m) := mul_le_mul_of_nonneg_left h1 hK
    _ = K / √m * √V := by ring

/-- The advantage of one polynomial `f` of degree `d`, as a function of `(λ, U)`. -/
theorem advantage_phi {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hm : 0 < m) {t : ℝ} (ht0 : 0 ≤ t)
    (f : MvPolynomial (Fin n × Fin n) ℝ)
    (hft : t * (2 * (f.totalDegree : ℝ) * (f.totalDegree + 1)) ≤ 1) :
    Integrable (phi f) ((plantedEig γ m t).prod (gaussMat n m)) ∧
      MemLp (phi f) 2 ((nullEig γ m).prod (gaussMat n m)) ∧
      (∫ p, phi f p ∂((plantedEig γ m t).prod (gaussMat n m))) -
          ∫ p, phi f p ∂((nullEig γ m).prod (gaussMat n m)) ≤
        (1 / √(1 - γ) + 10 * (f.totalDegree : ℝ) ^ 3 * t / √γ) / √m *
          √(variance (phi f) ((nullEig γ m).prod (gaussMat n m))) := by
  have := isProbabilityMeasure_eigLaw hγ0.le hγ1.le
  have := isProbabilityMeasure_plantedCoord (m := m) hγ0.le hγ1.le t
  have hnull : nullEig γ m = Measure.pi fun _ : Fin m ↦ eigLaw γ := rfl
  have hμ : ∀ k : Fin m, AllMoments ((fun _ : Fin m ↦ eigLaw γ) k) fun x ↦ x :=
    fun _ ↦ allMoments_eigLaw γ
  have hQ : AllMoments ((nullEig γ m).prod (gaussMat n m)) (phi f) := allMoments_phi hμ f
  have hP : AllMoments ((plantedEig γ m t).prod (gaussMat n m)) (phi f) :=
    allMoments_phi (allMoments_plantedCoord hγ0.le hγ1.le t) f
  have hQ2 : MemLp (phi f) 2 ((nullEig γ m).prod (gaussMat n m)) := by exact_mod_cast hQ 2
  refine ⟨hP.integrable, hQ2, ?_⟩
  have hmeas : Measurable (phi (m := m) f) := (continuous_phi f).measurable
  obtain ⟨G, hGdeg, hG⟩ := proj_polynomial (eigLaw γ) (gaussMat n m) f.totalDegree
    (fun p i ↦ phi_update_poly f p i)
    (fun i x ↦ (allMoments_phi_update hμ f i x).integrable) (lastIdx hm)
  have hEP : ∫ p, phi f p ∂((plantedEig γ m t).prod (gaussMat n m)) = G.eval t := by
    rw [plantedEig_eq γ t hm, integral_update_dirac (eigLaw γ) (gaussMat n m) hmeas, hG]
  have hEQ : ∫ p, phi f p ∂((nullEig γ m).prod (gaussMat n m)) = ∫ x, G.eval x ∂(eigLaw γ) := by
    rw [hnull, ← integral_proj (eigLaw γ) (gaussMat n m) hmeas (hnull ▸ hQ.integrable)
      (lastIdx hm)]
    exact integral_congr_ae (Filter.Eventually.of_forall hG)
  have hVar : (m : ℝ) * variance (fun x ↦ G.eval x) (eigLaw γ) ≤
      variance (phi f) ((nullEig γ m).prod (gaussMat n m)) := by
    have h := sum_variance_proj_le (eigLaw γ) (gaussMat n m) hmeas (hnull ▸ hQ2)
    have hsym : ∀ i, proj (eigLaw γ) (gaussMat n m) (phi f) i = fun x ↦ G.eval x := by
      intro i
      rw [proj_phi_eq (eigLaw γ) f i (lastIdx hm)]
      exact funext hG
    simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rwa [hnull]
  have hL := legendre_bound hγ0 hγ1 ht0 hft G hGdeg
  rw [hEP, hEQ]
  refine hL.trans (mul_sqrt_le_of_mul_le (by positivity) (variance_nonneg _ _) hm hVar)

/-- **The low-degree advantage for general parameters** [BHJK25, Lemmas 3.8–3.10]: for
`0 < γ < 1`, `m ≥ 1` and `0 ≤ λ* ≤ 1/(2 D (D + 1))`, the planted distribution has degree-`D`
advantage at most `(1/√(1 - γ) + 10 D³ λ*/√γ)/√m` over the null distribution. -/
theorem advantage_spectral {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hm : 0 < m) {t : ℝ}
    (ht0 : 0 ≤ t) {D : ℝ} (hD : t * (2 * D * (D + 1)) ≤ 1) (n : ℕ) :
    AdvantageAtMost entries D (plantedLaw γ m t n) (nullLaw γ m n)
      ((1 / √(1 - γ) + 10 * D ^ 3 * t / √γ) / √m) := by
  intro f hf
  have hd0 : (0 : ℝ) ≤ f.totalDegree := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := hd0.trans hf
  have hft : t * (2 * (f.totalDegree : ℝ) * (f.totalDegree + 1)) ≤ 1 :=
    le_trans (by gcongr) hD
  obtain ⟨hI, hL, hA⟩ := advantage_phi (n := n) hγ0 hγ1 hm ht0 f hft
  have hg : Continuous fun M : Matrix (Fin n) (Fin n) ℝ ↦ MvPolynomial.eval (entries M) f :=
    (MvPolynomial.continuous_eval f).comp continuous_entries
  have hs : AEMeasurable (specMap n m) ((nullEig γ m).prod (gaussMat n m)) :=
    measurable_specMap.aemeasurable
  have hs' : AEMeasurable (specMap n m) ((plantedEig γ m t).prod (gaussMat n m)) :=
    measurable_specMap.aemeasurable
  rw [plantedLaw_eq, nullLaw_eq]
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hs').2 hI,
    (memLp_map_measure_iff hg.aestronglyMeasurable hs).2 hL, ?_⟩
  rw [integral_map hs' hg.aestronglyMeasurable, integral_map hs hg.aestronglyMeasurable,
    variance_map hg.measurable.aemeasurable hs]
  have hcomp : (fun M : Matrix (Fin n) (Fin n) ℝ ↦ MvPolynomial.eval (entries M) f) ∘
      specMap n m = phi f := rfl
  rw [hcomp]
  refine hA.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  gcongr

end BHJK25.Spectral.LDAAux
