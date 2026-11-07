module

public import BGHKLMM26.RobustMIS.ItoAux

/-!
# The Gaussian Itô formula in expectation

Lemma 5.4 of `eldan-proof.tex`: for `G ∈ C²` near `[a, b] × ℝⁿ` with `G, ∂_s G, ∇G, ∇²G`
bounded there, `s ↦ E G(s, √s Z)` is continuous on `[a, b]` and has derivative
`E[(∂_s G + ½ Δ G)(s, √s Z)]` on `(a, b)` (for `0 ≤ a`).

Proof sketch: continuity by dominated convergence; for `s₀ ∈ (a, b)`, differentiate under the
integral (`d/ds G(s, √s z) = ∂_s G + ⟨∇G, z⟩/(2√s)`, dominated by `M₁ + M₂|z|/√(2 s₀)` for
`s ∈ (max a (s₀/2), b)`, audit issue 5), then Stein's identity `E[Zᵢ h(Z)] = E[∂ᵢ h(Z)]` (S3)
for `h = ∂ᵢG(s₀, √s₀ ·)`.

Stein's identity is `Ito.integration_by_parts` (`ItoAux.lean`, copied from OpenAI's
`GaussianPropeller/Stein.lean`); summed over the standard basis it gives
`Ito.integral_fderiv_apply_eq`: `E ⟨∇g(rZ), Z⟩ = r E Δg(rZ)`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace ContDiff

variable {n : ℕ}

namespace Ito

theorem contDiff_slice {G : ℝ → Gs n → ℝ} {O : Set (ℝ × Gs n)}
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ G p.1 p.2) O) {s : ℝ} (hs : ∀ x, (s, x) ∈ O) :
    ContDiff ℝ 2 (G s) := by
  have : ContDiffOn ℝ 2 ((fun p : ℝ × Gs n ↦ G p.1 p.2) ∘ fun x : Gs n ↦ (s, x)) univ :=
    hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ ↦ hs x)
  exact contDiffOn_univ.1 this

/-- The partial derivatives of `G` from the joint derivative. -/
theorem partials {G : ℝ → Gs n → ℝ} {O : Set (ℝ × Gs n)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ G p.1 p.2) O) {s : ℝ} {x : Gs n} (hp : (s, x) ∈ O) :
    HasFDerivAt (fun p : ℝ × Gs n ↦ G p.1 p.2) (fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (s, x))
        (s, x) ∧
      deriv (fun r ↦ G r x) s = fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (s, x) (1, 0) ∧
      fderiv ℝ (G s) x = (fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Gs n)) := by
  have hd : HasFDerivAt (fun p : ℝ × Gs n ↦ G p.1 p.2)
      (fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (s, x)) (s, x) :=
    ((hG.contDiffAt (hO.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨hd, ?_, ?_⟩
  · have := hd.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
    exact this.deriv
  · exact (hd.comp x (hasFDerivAt_prodMk_right s x)).fderiv

theorem abs_fderiv_fderiv_le {g : Gs n → ℝ} (y v w : Gs n) :
    |fderiv ℝ (fderiv ℝ g) y v w| ≤ ‖iteratedFDeriv ℝ 2 g y‖ * ‖v‖ * ‖w‖ := by
  have h := (iteratedFDeriv ℝ 2 g y).le_opNorm ![v, w]
  rw [iteratedFDeriv_two_apply] at h
  simpa [Fin.prod_univ_two, mul_assoc] using h

theorem norm_fderiv_fderiv_le {g : Gs n → ℝ} (y : Gs n) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ ‖iteratedFDeriv ℝ 2 g y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  simpa [Real.norm_eq_abs] using abs_fderiv_fderiv_le (g := g) y v w

/-- Stein's identity summed over a basis: `E ⟨∇g(rZ), Z⟩ = r E Δg(rZ)`. -/
theorem integral_fderiv_apply_eq {g : Gs n → ℝ} (hg : ContDiff ℝ 2 g) {M : ℝ}
    (h1 : ∀ x, ‖fderiv ℝ g x‖ ≤ M) (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ M) {r : ℝ} (hr : 0 < r) :
    ∫ z, fderiv ℝ g (r • z) z ∂gm n = r * ∫ z, Laplacian.laplacian g (r • z) ∂gm n := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hdd : ∀ y, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y := fun y ↦
    (hg1.differentiable (by norm_num) y).hasFDerivAt
  have hc1 : Continuous (fderiv ℝ g) := hg1.continuous
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv (by norm_num)
  have hM : 0 ≤ M := (norm_nonneg _).trans (h1 0)
  -- the integrands `H i` and their derivatives `D i`
  set H : Fin n → Gs n → ℝ := fun i z ↦ fderiv ℝ g (r • z) (b i) with hH
  set D : Fin n → Gs n → Gs n →L[ℝ] ℝ := fun i z ↦
    r • (ContinuousLinearMap.apply ℝ ℝ (b i)).comp (fderiv ℝ (fderiv ℝ g) (r • z)) with hD
  have hHD : ∀ i z, HasFDerivAt (H i) (D i z) z := by
    intro i z
    have hc : HasFDerivAt (fun z : Gs n ↦ fderiv ℝ g (r • z))
        ((fderiv ℝ (fderiv ℝ g) (r • z)).comp (r • ContinuousLinearMap.id ℝ (Gs n))) z :=
      (hdd (r • z)).comp z ((hasFDerivAt_id z).const_smul r)
    have := hc.clm_apply (hasFDerivAt_const (b i) z)
    convert this using 1
    ext v
    simp [hD]
  have hDc : ∀ i, Continuous (D i) := fun i ↦
    (continuous_const.clm_comp (hc2.comp (continuous_const_smul r))).const_smul r
  have hHb : ∀ i z, ‖H i z‖ ≤ M := fun i z ↦ by
    calc ‖H i z‖ ≤ ‖fderiv ℝ g (r • z)‖ * ‖b i‖ := (fderiv ℝ g (r • z)).le_opNorm _
      _ ≤ M := by simpa using h1 (r • z)
  have hDb : ∀ i z, ‖D i z‖ ≤ r * M := fun i z ↦ by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
    have := abs_fderiv_fderiv_le (g := g) (r • z) v (b i)
    simp only [hD, smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, norm_mul,
      Real.norm_eq_abs, abs_of_pos hr]
    have hb : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [hb, mul_one] at this
    calc r * |fderiv ℝ (fderiv ℝ g) (r • z) v (b i)| ≤ r * (‖iteratedFDeriv ℝ 2 g (r • z)‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left this hr.le
      _ ≤ r * (M * ‖v‖) := by gcongr; exact h2 _
      _ = r * M * ‖v‖ := by ring
  have hstein : ∀ i, ∫ z, D i z (b i) ∂gm n = ∫ z, H i z * ⟪b i, z⟫ ∂gm n := fun i ↦
    integration_by_parts (hHD i) (hDc i) (hHb i) (hDb i) (b i)
  have hint1 : ∀ i, Integrable (fun z ↦ H i z * ⟪b i, z⟫) (gm n) := by
    intro i
    refine Integrable.mono' ((IsGaussian.integrable_id (μ := gm n)).norm.const_mul M) ?_ ?_
    · exact ((hc1.comp (continuous_const_smul r)).clm_apply continuous_const |>.mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · refine ae_of_all _ fun z ↦ ?_
      rw [norm_mul]
      have hb : ‖b i‖ = 1 := b.orthonormal.1 i
      have hi : ‖⟪b i, z⟫‖ ≤ ‖z‖ := by
        simpa [hb] using norm_inner_le_norm (𝕜 := ℝ) (b i) z
      simpa using mul_le_mul (hHb i z) hi (norm_nonneg _) hM
  have hint2 : ∀ i, Integrable (fun z ↦ fderiv ℝ (fderiv ℝ g) (r • z) (b i) (b i)) (gm n) := by
    intro i
    refine Integrable.mono' (integrable_const M) ?_ (ae_of_all _ fun z ↦ ?_)
    · exact (((hc2.comp (continuous_const_smul r)).clm_apply continuous_const).clm_apply
        continuous_const).aestronglyMeasurable
    · have := abs_fderiv_fderiv_le (g := g) (r • z) (b i) (b i)
      have hb : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [hb, mul_one, mul_one] at this
      simpa [Real.norm_eq_abs] using this.trans (h2 _)
  have hsum : ∀ z, fderiv ℝ g (r • z) z = ∑ i, H i z * ⟪b i, z⟫ := by
    intro z
    have h := congrArg (fderiv ℝ g (r • z)) (b.sum_repr' z)
    rw [← h, map_sum]
    simp [hH, mul_comm]
  have hlap : ∀ z, Laplacian.laplacian g (r • z) =
      ∑ i, fderiv ℝ (fderiv ℝ g) (r • z) (b i) (b i) := by
    intro z
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b]
    simp [iteratedFDeriv_two_apply]
  simp_rw [hsum, hlap]
  rw [integral_finsetSum _ (fun i _ ↦ hint1 i), integral_finsetSum _ (fun i _ ↦ hint2 i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hstein i, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp [hD]

end Ito

open Ito in
/-- **Gaussian Itô formula in expectation** (Lemma 5.4). -/
theorem gauss_ito {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (G : ℝ → Gs n → ℝ)
    {O : Set (ℝ × Gs n)} (hO : IsOpen O) (hsub : Icc a b ×ˢ univ ⊆ O)
    (hG : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ G p.1 p.2) O)
    (hb : ∃ M, ∀ s ∈ Icc a b, ∀ x, |G s x| ≤ M ∧ |deriv (fun r ↦ G r x) s| ≤ M ∧
      ‖fderiv ℝ (G s) x‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 (G s) x‖ ≤ M) :
    ContinuousOn (fun s ↦ ∫ z, G s (√s • z) ∂gm n) (Icc a b) ∧
      ∀ s ∈ Ioo a b, HasDerivAt (fun s ↦ ∫ z, G s (√s • z) ∂gm n)
        (∫ z, (deriv (fun r ↦ G r (√s • z)) s +
          (1 / 2) * Laplacian.laplacian (G s) (√s • z)) ∂gm n) s := by
  obtain ⟨M, hM⟩ := hb
  have hmem : ∀ s ∈ Icc a b, ∀ x : Gs n, (s, x) ∈ O := fun s hs x ↦ hsub ⟨hs, mem_univ x⟩
  have hcont : ContinuousOn (fun p : ℝ × Gs n ↦ G p.1 p.2) O := hG.continuousOn
  have hfcont : ContinuousOn (fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2)) O :=
    hG.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, hab.le⟩ 0).1
  -- measurability of the integrands
  have hmeas : ∀ s ∈ Icc a b, AEStronglyMeasurable (fun z : Gs n ↦ G s (√s • z)) (gm n) := by
    intro s hs
    have : Continuous (fun z : Gs n ↦ G s (√s • z)) :=
      hcont.comp_continuous (by fun_prop) (fun z ↦ hmem s hs _)
    exact this.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine continuousOn_of_dominated (bound := fun _ ↦ M) hmeas
      (fun s hs ↦ ae_of_all _ fun z ↦ (hM s hs _).1) (integrable_const M)
      (ae_of_all _ fun z ↦ ?_)
    have : ContinuousOn (fun s : ℝ ↦ (s, √s • z)) (Icc a b) := by fun_prop
    exact hcont.comp this (fun s hs ↦ hmem s hs _)
  · intro s₀ hs₀
    have hs₀0 : 0 < s₀ := ha.trans_lt hs₀.1
    set ε := min (s₀ - a) (b - s₀) / 2 with hε
    have hε0 : 0 < ε := by
      have := hs₀.1; have := hs₀.2
      rw [hε]; positivity
    have hεa : ε ≤ (s₀ - a) / 2 := by rw [hε]; gcongr; exact min_le_left _ _
    have hεb : ε ≤ (b - s₀) / 2 := by rw [hε]; gcongr; exact min_le_right _ _
    set S := Ioo (s₀ - ε) (s₀ + ε) with hS
    have hSn : S ∈ nhds s₀ := Ioo_mem_nhds (by linarith) (by linarith)
    have hSI : ∀ t ∈ S, t ∈ Icc a b := fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hSpos : ∀ t ∈ S, s₀ / 2 ≤ t := fun t ht ↦ by linarith [ht.1]
    set F' : ℝ → Gs n → ℝ := fun t z ↦
      fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (t, √t • z) (1, (1 / (2 * √t)) • z) with hF'
    set c₀ := 1 / (2 * √(s₀ / 2)) with hc₀
    have hdiff : ∀ z, ∀ t ∈ S, HasDerivAt (fun t ↦ G t (√t • z)) (F' t z) t := by
      intro z t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) (hSpos t ht)
      have hd := (partials hO hG (hmem t (hSI t ht) (√t • z))).1
      have hl : HasDerivAt (fun t : ℝ ↦ (t, √t • z)) ((1 : ℝ), (1 / (2 * √t)) • z) t :=
        (hasDerivAt_id t).prodMk ((Real.hasDerivAt_sqrt ht0.ne').smul_const z)
      exact hd.comp_hasDerivAt t hl
    have hbound : ∀ z, ∀ t ∈ S, ‖F' t z‖ ≤ M + M * (c₀ * ‖z‖) := by
      intro z t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) (hSpos t ht)
      obtain ⟨-, h2, h3⟩ := partials hO hG (hmem t (hSI t ht) (√t • z))
      have hsplit : F' t z = deriv (fun r ↦ G r (√t • z)) t +
          fderiv ℝ (G t) (√t • z) ((1 / (2 * √t)) • z) := by
        rw [h2, h3, hF']
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.inr_apply]
        rw [← map_add]
        congr 1
        ext <;> simp
      have hc : 1 / (2 * √t) ≤ c₀ := by
        rw [hc₀]; gcongr; exact hSpos t ht
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · simpa [Real.norm_eq_abs] using (hM t (hSI t ht) _).2.1
      · refine ((fderiv ℝ (G t) (√t • z)).le_opNorm _).trans ?_
        refine mul_le_mul (hM t (hSI t ht) _).2.2.1 ?_ (norm_nonneg _) hM0
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        gcongr
    have hbint : Integrable (fun z : Gs n ↦ M + M * (c₀ * ‖z‖)) (gm n) :=
      (integrable_const M).add
        (((IsGaussian.integrable_id (μ := gm n)).norm.const_mul c₀).const_mul M)
    have hF'meas : AEStronglyMeasurable (F' s₀) (gm n) := by
      have h1 : Continuous (fun z : Gs n ↦ fderiv ℝ (fun p : ℝ × Gs n ↦ G p.1 p.2) (s₀, √s₀ • z)) :=
        hfcont.comp_continuous (by fun_prop) (fun z ↦ hmem s₀ (hSI s₀ (mem_Ioo.2
          ⟨by linarith, by linarith⟩)) _)
      exact (h1.clm_apply (by fun_prop)).aestronglyMeasurable
    have hs₀I : s₀ ∈ Icc a b := ⟨hs₀.1.le, hs₀.2.le⟩
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gm n) (x₀ := s₀)
      (F := fun t z ↦ G t (√t • z)) (F' := F') hSn
      (Filter.eventually_of_mem hSn fun t ht ↦ hmeas t (hSI t ht))
      (Integrable.mono' (integrable_const M) (hmeas s₀ hs₀I)
        (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using (hM s₀ hs₀I _).1))
      hF'meas (ae_of_all _ fun z t ht ↦ hbound z t ht) hbint
      (ae_of_all _ fun z t ht ↦ hdiff z t ht)
    refine key.2.congr_deriv ?_
    -- identify the derivative
    have hsplit : ∀ z, F' s₀ z = deriv (fun r ↦ G r (√s₀ • z)) s₀ +
        (1 / (2 * √s₀)) * fderiv ℝ (G s₀) (√s₀ • z) z := by
      intro z
      obtain ⟨-, h2, h3⟩ := partials hO hG (hmem s₀ hs₀I (√s₀ • z))
      rw [h2, h3, hF']
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inr_apply]
      have hv : ((1 : ℝ), (1 / (2 * √s₀)) • z) = ((1 : ℝ), (0 : Gs n)) +
          (1 / (2 * √s₀)) • ((0 : ℝ), z) := by ext <;> simp
      rw [hv, map_add, map_smul, smul_eq_mul]
    have hcd : ContDiff ℝ 2 (G s₀) := contDiff_slice hG (hmem s₀ hs₀I)
    have hr : 0 < √s₀ := Real.sqrt_pos.2 hs₀0
    have hstein := integral_fderiv_apply_eq hcd (fun x ↦ (hM s₀ hs₀I x).2.2.1)
      (fun x ↦ (hM s₀ hs₀I x).2.2.2) hr
    have hint_f : Integrable (fun z : Gs n ↦ (1 / (2 * √s₀)) * fderiv ℝ (G s₀) (√s₀ • z) z)
        (gm n) := by
      refine Integrable.mono' (((IsGaussian.integrable_id (μ := gm n)).norm.const_mul M).const_mul
        (1 / (2 * √s₀))) ?_ (ae_of_all _ fun z ↦ ?_)
      · have hc1 : Continuous (fderiv ℝ (G s₀)) := hcd.continuous_fderiv (by norm_num)
        exact (continuous_const.mul ((hc1.comp (continuous_const_smul _)).clm_apply
          continuous_id)).aestronglyMeasurable
      · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        gcongr
        exact ((fderiv ℝ (G s₀) (√s₀ • z)).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right (hM s₀ hs₀I _).2.2.1 (norm_nonneg _))
    have hint_d : Integrable (fun z : Gs n ↦ deriv (fun r ↦ G r (√s₀ • z)) s₀) (gm n) := by
      refine (key.1.sub hint_f).congr (ae_of_all _ fun z ↦ ?_)
      change F' s₀ z - _ = _
      rw [hsplit z]; ring
    have hint_l : Integrable (fun z : Gs n ↦ Laplacian.laplacian (G s₀) (√s₀ • z)) (gm n) := by
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
        (EuclideanSpace.basisFun (Fin n) ℝ)]
      refine integrable_finsetSum _ fun i _ ↦ ?_
      refine Integrable.mono' (integrable_const M) ?_ (ae_of_all _ fun z ↦ ?_)
      · exact ((continuous_eval_const _).comp ((hcd.continuous_iteratedFDeriv (by norm_num)).comp
          (continuous_const_smul _))).aestronglyMeasurable
      · refine ((iteratedFDeriv ℝ 2 (G s₀) (√s₀ • z)).le_opNorm _).trans ?_
        have hb : ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 :=
          (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i
        simpa [Fin.prod_univ_two, hb] using (hM s₀ hs₀I _).2.2.2
    simp_rw [hsplit]
    rw [integral_add hint_d hint_f, integral_add hint_d (hint_l.const_mul _), integral_const_mul,
      integral_const_mul, hstein]
    congr 1
    field_simp

end BGHKLMM26.RobustMIS
