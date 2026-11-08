module

public import BGHKLMM26.RobustMIS.SharpHalf
public import BGHKLMM26.RobustMIS.SharpFiber
public import BGHKLMM26.RobustMIS.SharpHermite

/-!
# The sharp Gaussian lemma: the local estimate

Near a halfspace `H = {α ≤ ⟨u, x⟩}`, the deficit of `F` is at least `(1 - t)` times its defect
`I = ⟨𝟙_H - F, T_t 𝟙_H⟩`, when `F` has the mean of `H`, its first Hermite vector is along `u`, and
`‖F - 𝟙_H‖₁` is small. With `h = F - 𝟙_H` split into its part `u_r` in the strip
`|⟨u, x⟩ - α| ≤ r` and the rest `v`, and `I = I_u + I_v` accordingly:

1. **Collapse the strip** (`nBil_strip_le`): `Q(u_r) ≤ k Q(g) + o_r(1) k B`, where `k = K_t(α, α)`,
   `g = p - q` is the signed fiber mass (`p ≥ 0` below `α`, `q ≥ 0` above), `B = E(p² + q²)`, and
   the first moments give `I_u ≥ (t k / 2)(1 - o_r(1)) B` (`wfun_strip`, layer cake).
2. **Remove the constant and linear modes** (`nBil_le_hermite`, `hermite_le_nBil`): `E g = -E v`
   and `F̂⁽¹⁾(g) = -F̂⁽¹⁾(v)` on `u⊥`, so `Q(g) ≤ t² B + Q(v)`, and `Q(u_r) ≤ (2t + o_r(1)) I_u +
   k Q(v)`.
3. **Absorb the rest** (`nBil_young`, `nBil_small`, `wfun_gap`): `Q(v) = o(‖v‖₁)` and
   `I_v ≥ c_r ‖v‖₁`, so `Q(h) ≤ (1 + t) I`, and the deficit identity
   `Δ = 2 I - Q(h)` (`gDef_eq_hDefect`) gives `Δ ≥ (1 - t) I`.

The helpers are in `BGHKLMM26.RobustMIS.SharpL`: the one-dimensional layer cake bound
(`sq_le_moment_left`, `sq_le_moment_right`: a mass `p` on one side of `α` with Lebesgue density
`≤ M` has first moment `≥ p²/(2M)`), the split `sIn`/`sOut` of `F - 𝟙_H` at the strip and the
halves `sLo`/`sHi` of `|u_r|` below and above `α`, the moment bound on the fibers (`fiber_moment`,
`B_le_Iu`), the strip and mode steps (`nBil_sIn_le`, `nBil_gfib_le`), the gap step (`gap_le`),
and the final arithmetic (`combine`), with `η = (1 - t)/16` in `mehler_near`, `wfun_strip` and
`λ = (1 - t)/(4t)` in `nBil_young`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace
open Gaussian StaticFiber

variable {n : ℕ}

namespace SharpL

/-! ### The layer cake bound in one dimension -/

/-- `∫ 𝟙_{(α - c, α]}(s) (s - (α - c)) ds = c²/2`. -/
theorem integral_ramp (α : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ s, (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s = c ^ 2 / 2 := by
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem integrable_ramp (α c : ℝ) :
    Integrable (fun s ↦ (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s) :=
  ((continuous_id.sub continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    |>.integrable_indicator measurableSet_Ioc

theorem ramp_nonneg (α c s : ℝ) : 0 ≤ (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s := by
  by_cases hs : s ∈ Ioc (α - c) α
  · rw [indicator_of_mem hs]; linarith [hs.1]
  · rw [indicator_of_notMem hs]

theorem ramp_le (α c s : ℝ) : (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s ≤ |c| := by
  by_cases hs : s ∈ Ioc (α - c) α
  · rw [indicator_of_mem hs]; linarith [hs.2, le_abs_self c]
  · rw [indicator_of_notMem hs]; exact abs_nonneg c

/-- **The layer cake bound**: a mass `p` below `α` with density at most `M` (with respect to
Lebesgue measure) has first moment about `α` at least `p²/(2M)`. -/
theorem sq_le_moment_left {f : ℝ → ℝ} (hf : Measurable f) (h01 : ∀ s, 0 ≤ f s ∧ f s ≤ 1)
    {M α : ℝ} (hM : 0 < M) (hd : ∀ s, npdf s * f s ≤ M) (hs : ∀ s, α < s → f s = 0) :
    (∫ s, f s ∂gaussianReal 0 1) ^ 2 ≤ 2 * M * ∫ s, f s * (α - s) ∂gaussianReal 0 1 := by
  obtain ⟨p, hp⟩ : ∃ p, p = ∫ s, f s ∂gaussianReal 0 1 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := hp ▸ integral_nonneg fun s ↦ (h01 s).1
  obtain ⟨c, hc⟩ : ∃ c, c = p / M := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ div_nonneg hp0 hM.le
  have hMc : M * c = p := by rw [hc]; field_simp
  have hmr : Measurable fun s ↦ (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s :=
    (measurable_id.sub measurable_const).indicator measurableSet_Ioc
  -- the pointwise bound `c f - f ramp ≤ f (α - s)`
  have hpt (s : ℝ) : c * f s - f s * (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s ≤
      f s * (α - s) := by
    by_cases hsα : α < s
    · rw [hs s hsα]; simp
    by_cases hsc : α - c < s
    · rw [indicator_of_mem (show s ∈ Ioc (α - c) α from ⟨hsc, not_lt.1 hsα⟩)]; linarith
    · rw [indicator_of_notMem (show s ∉ Ioc (α - c) α from fun h ↦ hsc h.1)]
      nlinarith [(h01 s).1]
  have hf1 : Integrable f (gaussianReal 0 1) :=
    integrable_of_abs_le hf fun s ↦ abs_le.2 ⟨by linarith [(h01 s).1], (h01 s).2⟩
  have hfr : Integrable (fun s ↦ f s * (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s)
      (gaussianReal 0 1) := by
    refine integrable_of_abs_le (hf.mul hmr) (C := |c|) fun s ↦ ?_
    rw [abs_mul, abs_of_nonneg (ramp_nonneg α c s), abs_of_nonneg (h01 s).1]
    calc f s * _ ≤ 1 * |c| := mul_le_mul (h01 s).2 (ramp_le α c s) (ramp_nonneg α c s) zero_le_one
      _ = |c| := one_mul _
  have hlin : Integrable (fun s : ℝ ↦ α - s) (gaussianReal 0 1) :=
    (integrable_const α).sub Static1D.integrable_id
  have hfm : Integrable (fun s ↦ f s * (α - s)) (gaussianReal 0 1) :=
    hlin.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs]; exact abs_le.2 ⟨by linarith [(h01 s).1], (h01 s).2⟩)
  -- the ramp term is at most `M c² / 2`
  have hE : ∫ s, f s * (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s ∂gaussianReal 0 1 ≤
      M * (c ^ 2 / 2) := by
    rw [integral_gaussianReal_eq, ← integral_ramp α hc0, ← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun s ↦ ?_) ((integrable_ramp α c).const_mul M)
      (ae_of_all _ fun s ↦ ?_)
    · exact mul_nonneg (Normal.npdf_nonneg s) (mul_nonneg (h01 s).1 (ramp_nonneg α c s))
    · dsimp only
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hd s) (ramp_nonneg α c s)
  have hint : c * p - ∫ s, f s * (Ioc (α - c) α).indicator (fun s ↦ s - (α - c)) s
      ∂gaussianReal 0 1 ≤ ∫ s, f s * (α - s) ∂gaussianReal 0 1 := by
    rw [hp, ← integral_const_mul, ← integral_sub (hf1.const_mul c) hfr]
    exact integral_mono ((hf1.const_mul c).sub hfr) hfm hpt
  rw [← hp]
  nlinarith

/-- The layer cake bound above `α`. -/
theorem sq_le_moment_right {f : ℝ → ℝ} (hf : Measurable f) (h01 : ∀ s, 0 ≤ f s ∧ f s ≤ 1)
    {M α : ℝ} (hM : 0 < M) (hd : ∀ s, npdf s * f s ≤ M) (hs : ∀ s, s < α → f s = 0) :
    (∫ s, f s ∂gaussianReal 0 1) ^ 2 ≤ 2 * M * ∫ s, f s * (s - α) ∂gaussianReal 0 1 := by
  have h := sq_le_moment_left (f := fun s ↦ f (-s)) (hf.comp measurable_neg) (fun s ↦ h01 (-s))
    hM (fun s ↦ by rw [← npdf_neg]; exact hd (-s)) (α := -α)
    (fun s hs' ↦ hs (-s) (by linarith))
  rw [Static1D.integral_comp_neg hf] at h
  have h2 := Static1D.integral_comp_neg (F := fun s ↦ f s * (s - α))
    (hf.mul (measurable_id.sub measurable_const))
  calc _ ≤ _ := h
    _ = 2 * M * ∫ s, f s * (s - α) ∂gaussianReal 0 1 := by
      rw [← h2]
      congr 2
      funext s
      ring_nf

/-! ### The halfspace and the strip -/

theorem measurable_halfInd (u : Gs n) (α : ℝ) : Measurable (halfInd u α) :=
  measurable_one.indicator (measurableSet_le measurable_const (by fun_prop))

theorem halfInd_of_lt {u x : Gs n} {α : ℝ} (h : ⟪u, x⟫ < α) : halfInd u α x = 0 := by
  simp [halfInd, not_le.2 h]

theorem halfInd_of_le {u x : Gs n} {α : ℝ} (h : α ≤ ⟪u, x⟫) : halfInd u α x = 1 := by
  simp [halfInd, h]

theorem abs_sub_halfInd_le {F : Gs n → ℝ} (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (u : Gs n) (α : ℝ)
    (x : Gs n) : |F x - halfInd u α x| ≤ 1 := by
  rcases lt_or_ge ⟪u, x⟫ α with h | h
  · rw [halfInd_of_lt h, abs_le]; constructor <;> linarith [h01 x]
  · rw [halfInd_of_le h, abs_le]; constructor <;> linarith [h01 x]

/-- The part `u_r = (F - 𝟙_H) 𝟙{|⟨u, x⟩ - α| ≤ r}` of `F - 𝟙_H` in the strip. -/
noncomputable def sIn (F : Gs n → ℝ) (u : Gs n) (α r : ℝ) (x : Gs n) : ℝ :=
  if |⟪u, x⟫ - α| ≤ r then F x - halfInd u α x else 0

/-- The rest `v = F - 𝟙_H - u_r`. -/
noncomputable def sOut (F : Gs n → ℝ) (u : Gs n) (α r : ℝ) (x : Gs n) : ℝ :=
  if |⟪u, x⟫ - α| ≤ r then 0 else F x - halfInd u α x

/-- The part `|u_r| 𝟙{⟨u, x⟩ < α}` of the strip below `α` (where `u_r ≥ 0`). -/
noncomputable def sLo (F : Gs n → ℝ) (u : Gs n) (α r : ℝ) (x : Gs n) : ℝ :=
  if ⟪u, x⟫ < α then |sIn F u α r x| else 0

/-- The part `|u_r| 𝟙{α ≤ ⟨u, x⟩}` of the strip above `α` (where `u_r ≤ 0`). -/
noncomputable def sHi (F : Gs n → ℝ) (u : Gs n) (α r : ℝ) (x : Gs n) : ℝ :=
  if ⟪u, x⟫ < α then 0 else |sIn F u α r x|

section Strip

variable {F : Gs n → ℝ} {u : Gs n} {α r : ℝ}

theorem measurableSet_strip (u : Gs n) (α r : ℝ) : MeasurableSet {x : Gs n | |⟪u, x⟫ - α| ≤ r} :=
  measurableSet_le (by fun_prop) measurable_const

theorem measurableSet_below (u : Gs n) (α : ℝ) : MeasurableSet {x : Gs n | ⟪u, x⟫ < α} :=
  measurableSet_lt (by fun_prop) measurable_const

theorem measurable_sIn (hF : Measurable F) : Measurable (sIn F u α r) :=
  Measurable.ite (measurableSet_strip u α r) (hF.sub (measurable_halfInd u α)) measurable_const

theorem measurable_sOut (hF : Measurable F) : Measurable (sOut F u α r) :=
  Measurable.ite (measurableSet_strip u α r) measurable_const (hF.sub (measurable_halfInd u α))

theorem measurable_sLo (hF : Measurable F) : Measurable (sLo F u α r) :=
  Measurable.ite (measurableSet_below u α) (continuous_abs.measurable.comp (measurable_sIn hF))
    measurable_const

theorem measurable_sHi (hF : Measurable F) : Measurable (sHi F u α r) :=
  Measurable.ite (measurableSet_below u α) measurable_const
    (continuous_abs.measurable.comp (measurable_sIn hF))

theorem abs_sIn_le (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) : |sIn F u α r x| ≤ 1 := by
  unfold sIn; split_ifs
  · exact abs_sub_halfInd_le h01 u α x
  · simp

theorem abs_sOut_le (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) : |sOut F u α r x| ≤ 1 := by
  unfold sOut; split_ifs
  · simp
  · exact abs_sub_halfInd_le h01 u α x

theorem sLo_mem (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) :
    0 ≤ sLo F u α r x ∧ sLo F u α r x ≤ 1 := by
  unfold sLo; split_ifs
  · exact ⟨abs_nonneg _, abs_sIn_le h01 x⟩
  · simp

theorem sHi_mem (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) :
    0 ≤ sHi F u α r x ∧ sHi F u α r x ≤ 1 := by
  unfold sHi; split_ifs
  · simp
  · exact ⟨abs_nonneg _, abs_sIn_le h01 x⟩

theorem sIn_of_lt {x : Gs n} (h : r < |⟪u, x⟫ - α|) : sIn F u α r x = 0 := by
  simp [sIn, not_le.2 h]

theorem sOut_of_le {x : Gs n} (h : |⟪u, x⟫ - α| ≤ r) : sOut F u α r x = 0 := by
  simp [sOut, h]

theorem sub_eq_sIn_add_sOut (x : Gs n) :
    F x - halfInd u α x = sIn F u α r x + sOut F u α r x := by
  unfold sIn sOut; split_ifs <;> ring

theorem abs_sub_eq (x : Gs n) :
    |F x - halfInd u α x| = |sIn F u α r x| + |sOut F u α r x| := by
  unfold sIn sOut; split_ifs <;> simp

/-- `u_r = (u_r)₊ - (u_r)₋`, the positive part below `α` and the negative part above. -/
theorem sIn_eq (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) :
    sIn F u α r x = sLo F u α r x - sHi F u α r x := by
  unfold sLo sHi
  rcases lt_or_ge ⟪u, x⟫ α with h | h
  · simp only [h, ↓reduceIte, sub_zero]
    unfold sIn; split_ifs
    · rw [halfInd_of_lt h, sub_zero, abs_of_nonneg (h01 x).1]
    · simp
  · simp only [not_lt.2 h, ↓reduceIte, zero_sub]
    unfold sIn; split_ifs
    · rw [halfInd_of_le h, abs_of_nonpos (by linarith [(h01 x).2]), neg_neg]
    · simp

theorem abs_sIn_eq (x : Gs n) : |sIn F u α r x| = sLo F u α r x + sHi F u α r x := by
  unfold sLo sHi; split_ifs <;> simp

end Strip

/-! ### The fiber masses -/

theorem integrable_fib {φ : Gs n → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (u y : Gs n) : Integrable (fun s ↦ φ (fpt u y s)) (gaussianReal 0 1) :=
  integrable_of_abs_le (hφ.comp (measurable_fpt_left u y)) fun _ ↦ hC _

theorem integrable_bdd_mul {f g : ℝ → ℝ} (hf : Measurable f) (hf1 : ∀ s, |f s| ≤ 1)
    (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun s ↦ f s * g s) (gaussianReal 0 1) :=
  hg.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun s ↦ by rw [Real.norm_eq_abs]; exact hf1 s)

section Fiber

variable {F : Gs n → ℝ} {u : Gs n} {α r : ℝ}

/-- `g = p - q`: the signed fiber mass of `u_r`. -/
theorem gfib_sIn (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (y : Gs n) :
    gfib (sIn F u α r) u y = gfib (sLo F u α r) u y - gfib (sHi F u α r) u y := by
  unfold gfib
  rw [← integral_sub (integrable_fib (measurable_sLo hF) (fun x ↦ abs_le_one_of (sLo_mem h01 x))
    u y) (integrable_fib (measurable_sHi hF) (fun x ↦ abs_le_one_of (sHi_mem h01 x)) u y)]
  congr 1
  funext s
  exact sIn_eq h01 _

/-- `p + q`: the fiber mass of `|u_r|`. -/
theorem gfib_abs_sIn (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (y : Gs n) :
    gfib (fun x ↦ |sIn F u α r x|) u y = gfib (sLo F u α r) u y + gfib (sHi F u α r) u y := by
  unfold gfib
  rw [← integral_add (integrable_fib (measurable_sLo hF) (fun x ↦ abs_le_one_of (sLo_mem h01 x))
    u y) (integrable_fib (measurable_sHi hF) (fun x ↦ abs_le_one_of (sHi_mem h01 x)) u y)]
  congr 1
  funext s
  exact abs_sIn_eq _

theorem abs_sIn_mul_le (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) :
    |sIn F u α r x| * |⟪u, x⟫ - α| ≤ |r| := by
  by_cases hx : |⟪u, x⟫ - α| ≤ r
  · calc |sIn F u α r x| * |⟪u, x⟫ - α| ≤ 1 * r :=
          mul_le_mul (abs_sIn_le h01 x) hx (abs_nonneg _) zero_le_one
      _ ≤ |r| := by rw [one_mul]; exact le_abs_self r
  · rw [sIn_of_lt (not_le.1 hx)]; simp

theorem measurable_moment (hF : Measurable F) :
    Measurable fun x ↦ |sIn F u α r x| * |⟪u, x⟫ - α| :=
  (continuous_abs.measurable.comp (measurable_sIn hF)).mul (by fun_prop)

/-- **The first moments of the fiber masses** (the layer cake bound on each side of each fiber):
`E(p² + q²) ≤ 2 M E[|u_r| |⟨u, x⟩ - α|]` when `φ ≤ M` on the strip. -/
theorem fiber_moment (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hu : ‖u‖ = 1)
    {M : ℝ} (hM : 0 < M) (hd : ∀ s, |s - α| ≤ r → npdf s ≤ M) :
    ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n ≤
      2 * M * ∫ x, |sIn F u α r x| * |⟪u, x⟫ - α| ∂gm n := by
  have hlo := measurable_sLo (u := u) (α := α) (r := r) hF
  have hhi := measurable_sHi (u := u) (α := α) (r := r) hF
  -- the bound on each fiber
  have hfib (y : Gs n) : gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2 ≤
      2 * M * ∫ s, |sIn F u α r (fpt u y s)| * |s - α| ∂gaussianReal 0 1 := by
    have hdens (f : Gs n → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
        (hf0 : ∀ x, r < |⟪u, x⟫ - α| → f x = 0) (s : ℝ) : npdf s * f (fpt u y s) ≤ M := by
      by_cases hs : |s - α| ≤ r
      · calc npdf s * f (fpt u y s) ≤ npdf s * 1 :=
              mul_le_mul_of_nonneg_left (hf _).2 (Normal.npdf_nonneg s)
          _ ≤ M := by rw [mul_one]; exact hd s hs
      · rw [hf0 _ (by rw [inner_fpt_self hu]; exact not_le.1 hs)]; linarith
    have hz : ∀ x, r < |⟪u, x⟫ - α| → |sIn F u α r x| = 0 := fun x hx ↦ by
      rw [sIn_of_lt hx, abs_zero]
    have h1 := sq_le_moment_left (f := fun s ↦ sLo F u α r (fpt u y s)) (α := α)
      (hlo.comp (measurable_fpt_left u y)) (fun s ↦ sLo_mem h01 _) hM
      (hdens _ (sLo_mem h01) fun x hx ↦ by unfold sLo; split_ifs <;> simp [hz x hx])
      (fun s hs ↦ by unfold sLo; rw [inner_fpt_self hu]; simp [not_lt.2 hs.le])
    have h2 := sq_le_moment_right (f := fun s ↦ sHi F u α r (fpt u y s)) (α := α)
      (hhi.comp (measurable_fpt_left u y)) (fun s ↦ sHi_mem h01 _) hM
      (hdens _ (sHi_mem h01) fun x hx ↦ by unfold sHi; split_ifs <;> simp [hz x hx])
      (fun s hs ↦ by unfold sHi; rw [inner_fpt_self hu]; simp [hs])
    have hi1 : Integrable (fun s ↦ sLo F u α r (fpt u y s) * (α - s)) (gaussianReal 0 1) :=
      integrable_bdd_mul (hlo.comp (measurable_fpt_left u y))
      (fun s ↦ abs_le_one_of (sLo_mem h01 _))
      ((integrable_const α).sub Static1D.integrable_id : Integrable (fun s : ℝ ↦ α - s) _)
    have hi2 : Integrable (fun s ↦ sHi F u α r (fpt u y s) * (s - α)) (gaussianReal 0 1) :=
      integrable_bdd_mul (hhi.comp (measurable_fpt_left u y))
      (fun s ↦ abs_le_one_of (sHi_mem h01 _))
      (Static1D.integrable_id.sub (integrable_const α) : Integrable (fun s : ℝ ↦ s - α) _)
    have hsum : ∫ s, |sIn F u α r (fpt u y s)| * |s - α| ∂gaussianReal 0 1 =
        (∫ s, sLo F u α r (fpt u y s) * (α - s) ∂gaussianReal 0 1) +
          ∫ s, sHi F u α r (fpt u y s) * (s - α) ∂gaussianReal 0 1 := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext s
      unfold sLo sHi
      rw [inner_fpt_self hu]
      split_ifs with hs
      · rw [abs_of_neg (show s - α < 0 by linarith)]; ring
      · rw [abs_of_nonneg (show 0 ≤ s - α by linarith)]; ring
    rw [hsum, mul_add]
    exact add_le_add h1 h2
  have hint : Integrable (fun y ↦ ∫ s, |sIn F u α r (fpt u y s)| * |s - α| ∂gaussianReal 0 1)
      (gm n) := by
    refine integrable_of_abs_le (C := |r|)
      (measurable_fiberInt (F := fun y s ↦ |sIn F u α r (fpt u y s)| * |s - α|)
        ((continuous_abs.measurable.comp
          ((measurable_sIn hF).comp (continuous_fpt u).measurable)).mul (by fun_prop)))
      fun y ↦ ?_
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := |r|) (ae_of_all _ fun s ↦ ?_)).trans
      (by simp)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := abs_sIn_mul_le (u := u) (α := α) (r := r) h01 (fpt u y s)
    rwa [inner_fpt_self hu] at this
  have hsq : Integrable (fun y ↦ gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2)
      (gm n) := by
    refine integrable_of_abs_le (C := 2)
      (((measurable_gfib hlo).pow_const 2).add ((measurable_gfib hhi).pow_const 2)) fun y ↦ ?_
    have h1 := gfib_mem (u := u) hlo (sLo_mem h01) y
    have h2 := gfib_mem (u := u) hhi (sHi_mem h01) y
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  calc _ ≤ ∫ y, 2 * M * ∫ s, |sIn F u α r (fpt u y s)| * |s - α| ∂gaussianReal 0 1 ∂gm n :=
        integral_mono hsq (hint.const_mul _) hfib
    _ = 2 * M * ∫ x, |sIn F u α r x| * |⟪u, x⟫ - α| ∂gm n := by
      rw [integral_const_mul, integral_fiber hu (integrable_of_abs_le (measurable_moment hF)
        (fun x ↦ by rw [abs_of_nonneg (by positivity)]; exact abs_sIn_mul_le h01 x))]
      congr 2
      funext y
      congr 1
      funext s
      rw [inner_fpt_self hu]

end Fiber

/-! ### The constant and linear modes -/

theorem gMean_add {φ ψ : Gs n → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {C : ℝ}
    (hφC : ∀ x, |φ x| ≤ C) (hψC : ∀ x, |ψ x| ≤ C) :
    gMean (fun x ↦ φ x + ψ x) = gMean φ + gMean ψ :=
  integral_add (integrable_of_abs_le hφ hφC) (integrable_of_abs_le hψ hψC)

theorem gMean_sub {φ ψ : Gs n → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {C : ℝ}
    (hφC : ∀ x, |φ x| ≤ C) (hψC : ∀ x, |ψ x| ≤ C) :
    gMean (fun x ↦ φ x - ψ x) = gMean φ - gMean ψ :=
  integral_sub (integrable_of_abs_le hφ hφC) (integrable_of_abs_le hψ hψC)

theorem hermite1_add {φ ψ : Gs n → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {C : ℝ}
    (hφC : ∀ x, |φ x| ≤ C) (hψC : ∀ x, |ψ x| ≤ C) :
    hermite1 (fun x ↦ φ x + ψ x) = hermite1 φ + hermite1 ψ := by
  unfold hermite1
  rw [← integral_add (integrable_smul_id hφ hφC) (integrable_smul_id hψ hψC)]
  congr 1
  funext x
  exact add_smul _ _ _

theorem hermite1_sub {φ ψ : Gs n → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {C : ℝ}
    (hφC : ∀ x, |φ x| ≤ C) (hψC : ∀ x, |ψ x| ≤ C) :
    hermite1 (fun x ↦ φ x - ψ x) = hermite1 φ - hermite1 ψ := by
  unfold hermite1
  rw [← integral_sub (integrable_smul_id hφ hφC) (integrable_smul_id hψ hψC)]
  congr 1
  funext x
  exact sub_smul _ _ _

/-- If `w₁ + w₂ = w - c u` with `w` along `u`, then the projection of `w₁` on `u⊥` is at most
`‖w₂‖`. -/
theorem norm_proj_sq_le {u w₁ w₂ w : Gs n} (c : ℝ) (hu : ‖u‖ = 1)
    (hw : ∀ z : Gs n, ⟪z, u⟫ = 0 → ⟪z, w⟫ = 0) (hsum : w₁ + w₂ = w - c • u) :
    ‖w₁ - ⟪u, w₁⟫ • u‖ ^ 2 ≤ ‖w₂‖ ^ 2 := by
  obtain ⟨z, hz⟩ : ∃ z, z = w₁ - ⟪u, w₁⟫ • u := ⟨_, rfl⟩
  rw [← hz]
  have huu : ⟪u, u⟫ = 1 := inner_self_of_norm hu
  have hzu : ⟪z, u⟫ = 0 := by
    rw [hz, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
  have h1 : w₁ = w - c • u - w₂ := by rw [← hsum]; abel
  have hzz : ⟪z, z⟫ = -⟪z, w₂⟫ := by
    calc ⟪z, z⟫ = ⟪z, w₁ - ⟪u, w₁⟫ • u⟫ := by rw [← hz]
      _ = ⟪z, w - c • u - w₂⟫ - ⟪u, w₁⟫ * ⟪z, u⟫ := by
          rw [inner_sub_right, real_inner_smul_right, ← h1]
      _ = -⟪z, w₂⟫ := by
          rw [inner_sub_right, inner_sub_right, real_inner_smul_right, hw z hzu, hzu]; ring
  have h2 : ‖z‖ ^ 2 ≤ ‖z‖ * ‖w₂‖ := by
    rw [← real_inner_self_eq_norm_sq, hzz]
    exact (neg_le_abs _).trans (abs_real_inner_le_norm z w₂)
  nlinarith [norm_nonneg z, norm_nonneg w₂, sq_nonneg (‖w₂‖ - ‖z‖)]

section Modes

variable {F : Gs n → ℝ} {u : Gs n} {α r : ℝ}

theorem abs_gfib_sIn_le (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (y : Gs n) :
    |gfib (sIn F u α r) u y| ≤ 1 := by
  rw [gfib_sIn hF h01]
  have h1 := gfib_mem (u := u) (measurable_sLo (u := u) (α := α) (r := r) hF)
    (sLo_mem (u := u) h01) y
  have h2 := gfib_mem (u := u) (measurable_sHi (u := u) (α := α) (r := r) hF)
    (sHi_mem (u := u) h01) y
  rw [abs_le]; constructor <;> linarith

/-- `E g² ≤ E(p² + q²)`. -/
theorem integral_gfib_sq_le (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    ∫ y, gfib (sIn F u α r) u y ^ 2 ∂gm n ≤
      ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n := by
  have hlo := measurable_sLo (u := u) (α := α) (r := r) hF
  have hhi := measurable_sHi (u := u) (α := α) (r := r) hF
  refine integral_mono (integrable_of_abs_le (C := 1)
    ((measurable_gfib (measurable_sIn hF)).pow_const 2) fun y ↦ ?_)
    (integrable_of_abs_le (C := 2)
      (((measurable_gfib hlo).pow_const 2).add ((measurable_gfib hhi).pow_const 2)) fun y ↦ ?_)
    fun y ↦ ?_
  · rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have := abs_gfib_sIn_le (u := u) (α := α) (r := r) hF h01 y
    nlinarith [abs_nonneg (gfib (sIn F u α r) u y)]
  · have h1 := gfib_mem (u := u) hlo (sLo_mem h01) y
    have h2 := gfib_mem (u := u) hhi (sHi_mem h01) y
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · dsimp only
    rw [gfib_sIn hF h01]
    have h1 := gfib_mem (u := u) hlo (sLo_mem h01) y
    have h2 := gfib_mem (u := u) hhi (sHi_mem h01) y
    nlinarith [mul_nonneg h1.1 h2.1]

/-- **The spectral gap step**: `Q(g) ≤ t² B + Q(v)`, from `E g = -E v` and
`F̂⁽¹⁾(g) = -P_{u⊥} F̂⁽¹⁾(v)`. -/
theorem nBil_gfib_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hF : Measurable F)
    (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hu : ‖u‖ = 1) (hm : gMean F = 1 - Phi α)
    (horth : ∀ v : Gs n, ⟪v, u⟫ = 0 → ⟪v, hermite1 F⟫ = 0) :
    nBil t (gfib (sIn F u α r) u) (gfib (sIn F u α r) u) ≤
      t ^ 2 * ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n +
        nBil t (sOut F u α r) (sOut F u α r) := by
  have hin := measurable_sIn (u := u) (α := α) (r := r) hF
  have hout := measurable_sOut (u := u) (α := α) (r := r) hF
  have hb := nBil_le_hermite ht0.le ht1.le (measurable_gfib (u := u) hin)
    (abs_gfib_sIn_le hF h01)
  have hlow := hermite_le_nBil ht0.le ht1.le hout (abs_sOut_le h01)
  have hsplit : (fun x ↦ F x - halfInd u α x) = fun x ↦ sIn F u α r x + sOut F u α r x :=
    funext fun x ↦ sub_eq_sIn_add_sOut x
  have hH := measurable_halfInd u α
  have hH1 : ∀ x, |halfInd u α x| ≤ 1 := fun x ↦ by
    rcases lt_or_ge ⟪u, x⟫ α with h | h
    · rw [halfInd_of_lt h]; simp
    · rw [halfInd_of_le h]; simp
  have hF1 : ∀ x, |F x| ≤ 1 := fun x ↦ abs_le_one_of (h01 x)
  -- the constant mode
  have hmean : gMean (gfib (sIn F u α r) u) = -gMean (sOut F u α r) := by
    have h0 : gMean (fun x ↦ F x - halfInd u α x) = 0 := by
      rw [gMean_sub hF hH hF1 hH1, hm, gMean_halfInd hu]; ring
    rw [hsplit, gMean_add hin hout (abs_sIn_le h01) (abs_sOut_le h01)] at h0
    rw [gMean, integral_gfib_signed hu hin (abs_sIn_le h01), ← gMean]
    linarith
  -- the linear mode
  have hherm : ‖hermite1 (gfib (sIn F u α r) u)‖ ^ 2 ≤ ‖hermite1 (sOut F u α r)‖ ^ 2 := by
    have h0 := hermite1_sub hF hH hF1 hH1
    rw [hsplit, hermite1_add hin hout (abs_sIn_le h01) (abs_sOut_le h01),
      hermite1_halfInd hu] at h0
    rw [hermite1_gfib hu hin (abs_sIn_le h01)]
    exact norm_proj_sq_le (npdf α) hu horth h0
  have hsq := integral_gfib_sq_le (u := u) (α := α) (r := r) hF h01
  rw [hmean, neg_sq] at hb
  have e1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
  have e2 := mul_le_mul_of_nonneg_left hherm ht0.le
  have e3 : 0 ≤ t ^ 2 * gMean (sOut F u α r) ^ 2 := by positivity
  have e4 : 0 ≤ t ^ 2 * ‖hermite1 (gfib (sIn F u α r) u)‖ ^ 2 := by positivity
  nlinarith

/-- **The strip step**: `Q(u_r) ≤ k Q(g) + 2 ε k B`. -/
theorem nBil_sIn_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hF : Measurable F)
    (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hK : ∀ s s', |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α) :
    nBil t (sIn F u α r) (sIn F u α r) ≤
      mehler t α α * nBil t (gfib (sIn F u α r) u) (gfib (sIn F u α r) u) +
        2 * ε * mehler t α α *
          ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n := by
  have hin := measurable_sIn (u := u) (α := α) (r := r) hF
  have hlo := measurable_sLo (u := u) (α := α) (r := r) hF
  have hhi := measurable_sHi (u := u) (α := α) (r := r) hF
  have h := nBil_strip_le ht0 ht1 hu hK hin (abs_sIn_le h01) fun x hx ↦ sIn_of_lt hx
  have habs : Measurable fun x ↦ |sIn F u α r x| := continuous_abs.measurable.comp hin
  have habs01 : ∀ x, 0 ≤ |sIn F u α r x| ∧ |sIn F u α r x| ≤ 1 :=
    fun x ↦ ⟨abs_nonneg _, abs_sIn_le h01 x⟩
  have h2 := nBil_self_le_sq (t := t) ⟨by linarith, ht1.le⟩ (measurable_gfib (u := u) habs)
    (C := 1) fun y ↦ abs_le_one_of (gfib_mem habs habs01 y)
  have h3 : ∫ y, gfib (fun x ↦ |sIn F u α r x|) u y ^ 2 ∂gm n ≤
      2 * ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_abs_le (C := 1)
      ((measurable_gfib habs).pow_const 2) fun y ↦ ?_)
      ((integrable_of_abs_le (C := 2)
        (((measurable_gfib hlo).pow_const 2).add ((measurable_gfib hhi).pow_const 2))
        fun y ↦ ?_).const_mul 2) fun y ↦ ?_
    · have := gfib_mem (u := u) habs habs01 y
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith
    · change |gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2| ≤ 2
      have h1 := gfib_mem (u := u) hlo (sLo_mem h01) y
      have h2 := gfib_mem (u := u) hhi (sHi_mem h01) y
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · dsimp only
      rw [gfib_abs_sIn hF h01]
      nlinarith [sq_nonneg (gfib (sLo F u α r) u y - gfib (sHi F u α r) u y)]
  have hk : 0 ≤ ε * mehler t α α :=
    mul_nonneg hε (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (exp_pos _).le)
  have := mul_le_mul_of_nonneg_left (h2.trans h3) hk
  linarith

end Modes

/-! ### The defect -/

section Defect

variable {F : Gs n → ℝ} {u : Gs n} {α r : ℝ}

theorem integrable_abs_mul_W {φ : Gs n → ℝ} (hφ : Measurable φ) (hφ1 : ∀ x, |φ x| ≤ 1)
    {W : ℝ → ℝ} (hWm : Measurable W) (hW1 : ∀ s, |W s| ≤ 1) (u : Gs n) :
    Integrable (fun x ↦ |φ x| * W ⟪u, x⟫) (gm n) := by
  refine integrable_of_abs_le (C := 1)
    ((continuous_abs.measurable.comp hφ).mul (hWm.comp (by fun_prop))) fun x ↦ ?_
  rw [abs_mul, abs_abs]
  calc |φ x| * |W ⟪u, x⟫| ≤ 1 * 1 := mul_le_mul (hφ1 x) (hW1 _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The first moment step**: `L B ≤ 2 M I_u` when `W(s) ≥ L |s - α|` and `φ(s) ≤ M` on the
strip. -/
theorem B_le_Iu (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hu : ‖u‖ = 1)
    {W : ℝ → ℝ} (hWm : Measurable W) (hW1 : ∀ s, |W s| ≤ 1) {L M : ℝ} (hL : 0 ≤ L)
    (hM : 0 < M) (hW : ∀ s, |s - α| ≤ r → L * |s - α| ≤ W s ∧ npdf s ≤ M) :
    L * ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n ≤
      2 * M * ∫ x, |sIn F u α r x| * W ⟪u, x⟫ ∂gm n := by
  have h1 := fiber_moment hF h01 hu hM fun s hs ↦ (hW s hs).2
  have h2 : L * ∫ x, |sIn F u α r x| * |⟪u, x⟫ - α| ∂gm n ≤
      ∫ x, |sIn F u α r x| * W ⟪u, x⟫ ∂gm n := by
    rw [← integral_const_mul]
    refine integral_mono ((integrable_of_abs_le (measurable_moment hF) (C := |r|) fun x ↦ ?_
      ).const_mul L) (integrable_abs_mul_W (measurable_sIn hF) (abs_sIn_le h01) hWm hW1 u)
      fun x ↦ ?_
    · rw [abs_of_nonneg (by positivity)]; exact abs_sIn_mul_le h01 x
    · dsimp only
      by_cases hx : |⟪u, x⟫ - α| ≤ r
      · calc L * (|sIn F u α r x| * |⟪u, x⟫ - α|) = |sIn F u α r x| * (L * |⟪u, x⟫ - α|) := by
              ring
          _ ≤ |sIn F u α r x| * W ⟪u, x⟫ :=
              mul_le_mul_of_nonneg_left (hW _ hx).1 (abs_nonneg _)
      · rw [sIn_of_lt (not_le.1 hx)]; simp
  calc _ ≤ L * (2 * M * ∫ x, |sIn F u α r x| * |⟪u, x⟫ - α| ∂gm n) :=
        mul_le_mul_of_nonneg_left h1 hL
    _ = 2 * M * (L * ∫ x, |sIn F u α r x| * |⟪u, x⟫ - α| ∂gm n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `I = I_u + I_v`. -/
theorem integral_split (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) {W : ℝ → ℝ}
    (hWm : Measurable W) (hW1 : ∀ s, |W s| ≤ 1) :
    ∫ x, |F x - halfInd u α x| * W ⟪u, x⟫ ∂gm n =
      ∫ x, |sIn F u α r x| * W ⟪u, x⟫ ∂gm n + ∫ x, |sOut F u α r x| * W ⟪u, x⟫ ∂gm n := by
  rw [← integral_add (integrable_abs_mul_W (measurable_sIn hF) (abs_sIn_le h01) hWm hW1 u)
    (integrable_abs_mul_W (measurable_sOut hF) (abs_sOut_le h01) hWm hW1 u)]
  congr 1
  funext x
  rw [abs_sub_eq (r := r)]
  ring

/-- **The gap step**: `I_v ≥ c ‖v‖₁` when `W ≥ c` off the strip. -/
theorem gap_le (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) {W : ℝ → ℝ}
    (hWm : Measurable W) (hW1 : ∀ s, |W s| ≤ 1) {c : ℝ} (hW : ∀ s, r < |s - α| → c ≤ W s) :
    c * ∫ x, |sOut F u α r x| ∂gm n ≤ ∫ x, |sOut F u α r x| * W ⟪u, x⟫ ∂gm n := by
  rw [← integral_const_mul]
  refine integral_mono ((integrable_of_abs_le (C := 1)
    (continuous_abs.measurable.comp (measurable_sOut hF)) fun x ↦ ?_).const_mul c)
    (integrable_abs_mul_W (measurable_sOut hF) (abs_sOut_le h01) hWm hW1 u) fun x ↦ ?_
  · rw [Function.comp_apply, abs_abs]; exact abs_sOut_le h01 x
  · dsimp only
    by_cases hx : |⟪u, x⟫ - α| ≤ r
    · rw [sOut_of_le hx]; simp
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hW _ (not_le.1 hx)) (abs_nonneg _)

end Defect

/-! ### The constants -/

theorem mehler_pos {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (s s' : ℝ) : 0 < mehler t s s' :=
  mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by nlinarith))) (exp_pos _)

theorem mehler_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A α : ℝ} (hα : |α| ≤ A) :
    mehler t α α ≤ (√(1 - t ^ 2))⁻¹ * exp (2 * t * A ^ 2 / (2 * (1 - t ^ 2))) := by
  unfold mehler
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hα2 : α ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg α) hα 2
  refine div_le_div_of_nonneg_right ?_ (by nlinarith)
  nlinarith [sq_nonneg (t * α)]

/-- The choice of the parameters: `(1 + 3t)(1 + η)² ≤ 2(1 + t)(1 - η)` for `η = (1 - t)/16`. -/
theorem param_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 + 3 * t) * (1 + (1 - t) / 16) ^ 2 ≤ 2 * (1 + t) * (1 - (1 - t) / 16) := by
  nlinarith [mul_pos ht0 (sub_pos.2 ht1), mul_pos (mul_pos ht0 ht0) (sub_pos.2 ht1)]

/-- **The final combination**: with `η = (1 - t)/16` and `λ = (1 - t)/(4t)`, the strip, mode,
moment, Young and gap steps give `Q(h) ≤ (1 + t) I`. -/
theorem combine {t η l k K C B Iu Iv Qh Qur Qg Qv : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hη : η = (1 - t) / 16) (hl : l = (1 - t) / (4 * t)) (hC : C = (1 + l) * K + (1 + l⁻¹))
    (hk0 : 0 < k) (hkK : k ≤ K) (hB0 : 0 ≤ B) (hIu0 : 0 ≤ Iu) (hIv0 : 0 ≤ Iv) (hQv0 : 0 ≤ Qv)
    (h1 : (1 - η) * t * k * B ≤ 2 * (1 + η) * Iu)
    (h2 : Qur ≤ k * Qg + 2 * (η * t ^ 2 / 2) * k * B)
    (h3 : Qg ≤ t ^ 2 * B + Qv)
    (h4 : Qh ≤ (1 + l) * Qur + (1 + l⁻¹) * Qv)
    (h5 : C * Qv ≤ Iv) :
    Qh ≤ (1 + t) * (Iu + Iv) := by
  have hl0 : 0 < l := hl ▸ div_pos (by linarith) (by linarith)
  have hη1 : 0 < 1 - η := by rw [hη]; linarith
  have hX : 0 ≤ k * B := mul_nonneg hk0.le hB0
  have hlt : (1 + l) * t ^ 2 = t * (1 + 3 * t) / 4 := by
    rw [hl]; field_simp; ring
  have hP := param_le ht0 ht1
  rw [← hη] at hP
  -- the linear cost
  have hA : (1 + l) * (t ^ 2 * (1 + η) * (k * B)) ≤ (1 + t) * Iu := by
    have e1 : (1 + 3 * t) * (1 + η) * ((1 - η) * t * k * B) ≤
        (1 + 3 * t) * (1 + η) * (2 * (1 + η) * Iu) :=
      mul_le_mul_of_nonneg_left h1 (by nlinarith)
    have e2 := mul_le_mul_of_nonneg_right hP hIu0
    have key : (1 - η) * ((1 + 3 * t) * (1 + η) * (t * (k * B))) ≤
        (1 - η) * (4 * (1 + t) * Iu) := by nlinarith
    have key' := le_of_mul_le_mul_left key hη1
    calc (1 + l) * (t ^ 2 * (1 + η) * (k * B)) = (1 + l) * t ^ 2 * ((1 + η) * (k * B)) := by
          ring
      _ = (1 + 3 * t) * (1 + η) * (t * (k * B)) / 4 := by rw [hlt]; ring
      _ ≤ (1 + t) * Iu := by linarith
  -- the rest
  have hB : (1 + l) * k * Qv + (1 + l⁻¹) * Qv ≤ C * Qv := by
    rw [hC]
    nlinarith [mul_le_mul_of_nonneg_right hkK hQv0]
  have e3 := mul_le_mul_of_nonneg_left h3 hk0.le
  have e4 : (1 + l) * Qur ≤ (1 + l) * (k * (t ^ 2 * B + Qv) + 2 * (η * t ^ 2 / 2) * k * B) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

end SharpL

/-- **The local estimate**: near the halfspace, `Γ_t(E F) - Stab_t(F) ≥ (1 - t) I_t(F, H)`. -/
theorem sharp_local {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : ℝ) :
    ∃ ε₀ > 0, ∀ (n : ℕ) (u : Gs n) (α : ℝ), ‖u‖ = 1 → |α| ≤ A →
      ∀ F : Gs n → ℝ, Measurable F → (∀ x, 0 ≤ F x ∧ F x ≤ 1) → gMean F = 1 - Phi α →
        (∀ v : Gs n, ⟪v, u⟫ = 0 → ⟪v, hermite1 F⟫ = 0) →
        ∫ x, |F x - halfInd u α x| ∂gm n ≤ ε₀ →
        (1 - t) * hDefect t u α F ≤ gDef t F := by
  open SharpL in
  -- the constants: `η` for the strip, `λ = l` for Young, `C` for the rest
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (1 - t) / 16 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨r₁, hr₁, hK⟩ := mehler_near (by linarith : (-1 : ℝ) < t) ht1 A
    (ε := η * t ^ 2 / 2) (by positivity)
  obtain ⟨r₂, hr₂, hWs⟩ := wfun_strip ht0 ht1 A hη0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min r₁ r₂ := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ lt_min hr₁ hr₂
  have hrr₁ : r ≤ r₁ := hr ▸ min_le_left _ _
  have hrr₂ : r ≤ r₂ := hr ▸ min_le_right _ _
  obtain ⟨c, hc, hgap⟩ := wfun_gap ht0 ht1 A hr0
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (1 - t) / (4 * t) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ div_pos (by linarith) (by linarith)
  obtain ⟨K, hK'⟩ : ∃ K : ℝ,
      K = (√(1 - t ^ 2))⁻¹ * exp (2 * t * A ^ 2 / (2 * (1 - t ^ 2))) := ⟨_, rfl⟩
  have hK0 : 0 < K := hK' ▸ mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by nlinarith))) (exp_pos _)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + l) * K + (1 + l⁻¹) := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  obtain ⟨τ₀, hτ₀, hsmall⟩ := nBil_small ht0 ht1 (div_pos hc hC0)
  refine ⟨τ₀, hτ₀, fun n u α hu hα F hF h01 hm horth hL1 ↦ ?_⟩
  -- the weight `W(s) = |w(s) - w(α)|`
  have hwc : Continuous (wfun t α) :=
    continuous_Phi.comp (((continuous_const.mul continuous_id).sub continuous_const).div_const _)
  have hWm : Measurable fun s ↦ |wfun t α s - wfun t α α| :=
    ((hwc.sub continuous_const).abs).measurable
  have hW1 (s : ℝ) : |(fun s ↦ |wfun t α s - wfun t α α|) s| ≤ 1 := by
    have h1 := Phi_pos ((t * s - α) / √(1 - t ^ 2))
    have h2 := Phi_lt_one ((t * s - α) / √(1 - t ^ 2))
    have h3 := Phi_pos ((t * α - α) / √(1 - t ^ 2))
    have h4 := Phi_lt_one ((t * α - α) / √(1 - t ^ 2))
    simp only [abs_abs, wfun]
    rw [abs_le]; constructor <;> linarith
  have hk0 := mehler_pos (by linarith) ht1 α α
  have hkK : mehler t α α ≤ K := hK' ▸ mehler_le ht0 ht1 hα
  -- the pieces `I_u`, `I_v`, `B`
  obtain ⟨Iu, hIu⟩ : ∃ Iu : ℝ,
      Iu = ∫ x, |sIn F u α r x| * |wfun t α ⟪u, x⟫ - wfun t α α| ∂gm n := ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ Iv : ℝ,
      Iv = ∫ x, |sOut F u α r x| * |wfun t α ⟪u, x⟫ - wfun t α α| ∂gm n := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ,
      B = ∫ y, (gfib (sLo F u α r) u y ^ 2 + gfib (sHi F u α r) u y ^ 2) ∂gm n := ⟨_, rfl⟩
  have hdef : hDefect t u α F = Iu + Iv := by
    rw [hDefect_eq_weighted ht0 ht1 hu α hF h01 hm, hIu, hIv]
    exact integral_split hF h01 hWm hW1
  have hB0 : 0 ≤ B := hB ▸ integral_nonneg fun y ↦ by positivity
  have hIu0 : 0 ≤ Iu := hIu ▸ integral_nonneg fun x ↦ by positivity
  have hIv0 : 0 ≤ Iv := hIv ▸ integral_nonneg fun x ↦ by positivity
  -- 1. the first moments: `(1 - η) t k B ≤ 2 (1 + η) I_u`
  have h1 : (1 - η) * t * mehler t α α * B ≤ 2 * (1 + η) * Iu := by
    have h := B_le_Iu (r := r) hF h01 hu hWm hW1
      (L := (1 - η) * (t * mehler t α α * npdf α)) (M := (1 + η) * npdf α)
      (mul_nonneg (by rw [hη]; linarith) (by have := npdf_pos α; positivity))
      (mul_pos (by linarith) (npdf_pos α))
      fun s hs ↦ hWs α s hα (hs.trans hrr₂)
    rw [← hB, ← hIu] at h
    refine le_of_mul_le_mul_right ?_ (npdf_pos α)
    calc (1 - η) * t * mehler t α α * B * npdf α
        = (1 - η) * (t * mehler t α α * npdf α) * B := by ring
      _ ≤ 2 * ((1 + η) * npdf α) * Iu := h
      _ = 2 * (1 + η) * Iu * npdf α := by ring
  -- 2. the strip and the modes
  have h2 := nBil_sIn_le ht0 ht1 hF h01 hu (ε := η * t ^ 2 / 2) (by positivity)
    fun s s' hs hs' ↦ hK α s s' hα (hs.trans hrr₁) (hs'.trans hrr₁)
  rw [← hB] at h2
  have h3 := nBil_gfib_le (r := r) ht0 ht1 hF h01 hu hm horth
  rw [← hB] at h3
  -- 3. Young, the small-mass bound and the gap
  have h4 := nBil_young ht0.le ht1.le hl0 (measurable_sIn (u := u) (α := α) (r := r) hF)
    (measurable_sOut (u := u) (α := α) (r := r) hF) (C := 1) (abs_sIn_le h01) (abs_sOut_le h01)
  have hsplit : (fun x ↦ F x - halfInd u α x) = fun x ↦ sIn F u α r x + sOut F u α r x :=
    funext fun x ↦ sub_eq_sIn_add_sOut x
  have hQv0 := nBil_self_nonneg ht0.le ht1.le (measurable_sOut (u := u) (α := α) (r := r) hF)
    (abs_sOut_le h01)
  have hτ : ∫ x, |sOut F u α r x| ∂gm n ≤ τ₀ := by
    have i1 : Integrable (fun x ↦ |sOut F u α r x|) (gm n) :=
      integrable_of_abs_le (C := 1) (continuous_abs.measurable.comp (measurable_sOut hF))
        fun x ↦ by rw [abs_abs]; exact abs_sOut_le h01 x
    have i2 : Integrable (fun x ↦ |F x - halfInd u α x|) (gm n) :=
      integrable_of_abs_le (C := 1)
        (continuous_abs.measurable.comp (hF.sub (measurable_halfInd u α)))
        fun x ↦ by rw [abs_abs]; exact abs_sub_halfInd_le h01 u α x
    refine le_trans (integral_mono i1 i2 fun x ↦ ?_) hL1
    dsimp only
    rw [abs_sub_eq (r := r)]
    linarith [abs_nonneg (sIn F u α r x)]
  have hsm := hsmall n (sOut F u α r) (measurable_sOut hF) (abs_sOut_le h01) hτ
  have hg := gap_le (u := u) (r := r) hF h01 hWm hW1 (c := c) fun s hs ↦ hgap α s hα hs
  rw [← hIv] at hg
  have h5 : C * nBil t (sOut F u α r) (sOut F u α r) ≤ Iv := by
    calc C * nBil t (sOut F u α r) (sOut F u α r)
        ≤ C * (c / C * ∫ x, |sOut F u α r x| ∂gm n) := mul_le_mul_of_nonneg_left hsm hC0.le
      _ = c * ∫ x, |sOut F u α r x| ∂gm n := by field_simp
      _ ≤ Iv := hg
  have hfin := combine ht0 ht1 hη hl hC hk0 hkK hB0 hIu0 hIv0 hQv0 h1 h2 h3 h4 h5
  rw [gDef_eq_hDefect ht0 ht1 hu α hF h01 hm, hdef, gStab_eq_nBil, hsplit]
  linarith

end BGHKLMM26.RobustMIS
