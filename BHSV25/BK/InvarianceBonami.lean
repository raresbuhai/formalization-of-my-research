module

public import BHSV25.BK.InvarianceMultilinear
public import Background.GaussianCalculus

/-!
# The Bonami lemma

Copied from `BGHKLMM26/RobustMIS/Bonami.lean` (papers do not import each other), with the
namespace changed to `BHSV25.BK.Aint` and the Gaussian parts left out.

`(2, 4)`-hypercontractivity of low-degree multilinear polynomials in independent random variables
`Xᵢ ∼ νᵢ` with `E Xᵢ = E Xᵢ³ = 0`, `E Xᵢ² = 1`, `E Xᵢ⁴ ≤ 9` (`GoodLaw`): `E p⁴ ≤ 9^d (E p²)²` for
`deg p ≤ d` (`bonami`; O'Donnell, *Analysis of Boolean functions*, Thm 9.21 and §11.2; [MOO10]).
Induction on `R` through `MeasurableEquiv.piFinSuccAbove`: `p = q + X r` with `deg q ≤ d`,
`deg r ≤ d - 1` independent of `X`, `E p⁴ = E q⁴ + 6 E[q² r²] + E X⁴ E r⁴`,
`E[q² r²] ≤ √(E q⁴ E r⁴)`. Also: the uniform law `signLaw` on `{±1}` is good, and the monomials
are orthonormal under products of good laws (`integral_mlEval_mul_pi`).
-/

@[expose] public section

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

/-- The moment conditions on the coordinates. -/
structure GoodLaw (ν : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  int4 : Integrable (fun x ↦ x ^ 4) ν
  m1 : ∫ x, x ∂ν = 0
  m2 : ∫ x, x ^ 2 ∂ν = 1
  m3 : ∫ x, x ^ 3 ∂ν = 0
  m4 : ∫ x, x ^ 4 ∂ν ≤ 9

namespace Bonami

open MultilinearGauss

theorem integrable_pow_of_goodLaw {ν : Measure ℝ} (h : GoodLaw ν) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun y ↦ y ^ k) ν := by
  have := h.prob
  refine Integrable.mono' ((integrable_const 1).add h.int4)
    (continuous_pow k).aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_pow]
  rcases le_total |y| 1 with hy | hy
  · have := pow_le_one₀ (abs_nonneg y) hy (n := k)
    nlinarith [pow_two_nonneg (y ^ 2), sq_nonneg y]
  · have h1 : |y| ^ k ≤ |y| ^ 4 := pow_le_pow_right₀ hy hk
    have h2 : |y| ^ 4 = y ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    linarith

theorem memLp_of_goodLaw {ν : Measure ℝ} (h : GoodLaw ν) : MemLp (fun y ↦ y) 4 ν := by
  rw [← integrable_norm_rpow_iff (f := fun y : ℝ ↦ y) aestronglyMeasurable_id (by norm_num)
    (by norm_num)]
  have e : (fun y : ℝ ↦ ‖y‖ ^ (4 : ENNReal).toReal) = fun y ↦ y ^ 4 := by
    funext y
    rw [show (4 : ENNReal).toReal = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [e]
  exact h.int4

theorem integrable_pow_four {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : MemLp f 4 μ) : Integrable (fun x ↦ f x ^ 4) μ := by
  have := h.integrable_norm_pow (p := 4) (by norm_num)
  refine this.congr (ae_of_all _ fun x ↦ ?_)
  simp only [Real.norm_eq_abs]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]

/-- Splitting off the first coordinate of a multilinear polynomial. -/
theorem mlEval_cons (c : Cube (Fin (R + 1)) → ℝ) (y : ℝ) (x : Fin R → ℝ) :
    mlEval c (Fin.cons y x) = mlEval (fun s ↦ c (Fin.cons false s)) x +
      y * mlEval (fun s ↦ c (Fin.cons true s)) x := by
  unfold mlEval
  rw [← (Fin.consEquiv (fun _ ↦ Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp [Fin.prod_univ_succ]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp [Fin.prod_univ_succ]
    ring

theorem sum_cube_succ (f : Cube (Fin (R + 1)) → ℝ) :
    ∑ s, f s = ∑ s, f (Fin.cons false s) + ∑ s, f (Fin.cons true s) := by
  rw [← (Fin.consEquiv (fun _ ↦ Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    add_comm]
  rfl

theorem sdeg_cons (b : Bool) (s : Cube (Fin R)) :
    sdeg (Fin.cons b s : Cube (Fin (R + 1))) = (if b then 1 else 0) + sdeg s := by
  simp only [sdeg, OAI.OptimalMaxCut.Analytic.degree]
  rw [Fin.card_filter_univ_succ']
  simp

theorem integral_pi_succ (ν : Fin (R + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (F : (Fin (R + 1) → ℝ) → ℝ) :
    ∫ z, F z ∂Measure.pi ν =
      ∫ p, F (Fin.cons p.1 p.2) ∂(ν 0).prod (Measure.pi fun j ↦ ν j.succ) := by
  rw [← ((measurePreserving_piFinSuccAbove ν 0).symm).integral_comp']
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Equiv.coe_fn_mk, Fin.zero_succAbove]

theorem integrable_pi_succ (ν : Fin (R + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {F : (Fin (R + 1) → ℝ) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    Integrable (fun p : ℝ × (Fin R → ℝ) ↦ F (Fin.cons p.1 p.2))
      ((ν 0).prod (Measure.pi fun j ↦ ν j.succ)) := by
  have h := ((measurePreserving_piFinSuccAbove ν 0).symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := F)
  rw [← h] at hF
  convert hF using 2 with p
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  · simp [Fin.zero_succAbove]

theorem integral_quartic {ν : Measure ℝ} (h : GoodLaw ν) (a b : ℝ) :
    ∫ y, (a + y * b) ^ 4 ∂ν = a ^ 4 + 6 * a ^ 2 * b ^ 2 + (∫ y, y ^ 4 ∂ν) * b ^ 4 := by
  have := h.prob
  have e : ∀ y : ℝ, (a + y * b) ^ 4 = a ^ 4 + (4 * a ^ 3 * b) * y ^ 1 +
      (6 * a ^ 2 * b ^ 2) * y ^ 2 + (4 * a * b ^ 3) * y ^ 3 + b ^ 4 * y ^ 4 := fun y ↦ by ring
  simp_rw [e]
  have I1 := (integrable_pow_of_goodLaw h (k := 1) (by norm_num)).const_mul (4 * a ^ 3 * b)
  have h1 : ∫ y, y ^ 1 ∂ν = 0 := by simpa using h.m1
  have I2 := (integrable_pow_of_goodLaw h (k := 2) (by norm_num)).const_mul (6 * a ^ 2 * b ^ 2)
  have I3 := (integrable_pow_of_goodLaw h (k := 3) (by norm_num)).const_mul (4 * a * b ^ 3)
  have I4 := (integrable_pow_of_goodLaw h (k := 4) (by norm_num)).const_mul (b ^ 4)
  have I0 := integrable_const (μ := ν) (a ^ 4)
  have K1 : Integrable (fun y ↦ a ^ 4 + 4 * a ^ 3 * b * y ^ 1) ν := I0.add I1
  have K2 : Integrable (fun y ↦ a ^ 4 + 4 * a ^ 3 * b * y ^ 1 + 6 * a ^ 2 * b ^ 2 * y ^ 2) ν :=
    K1.add I2
  have K3 : Integrable (fun y ↦ a ^ 4 + 4 * a ^ 3 * b * y ^ 1 + 6 * a ^ 2 * b ^ 2 * y ^ 2 +
      4 * a * b ^ 3 * y ^ 3) ν := K2.add I3
  rw [integral_add K3 I4, integral_add K2 I3, integral_add K1 I2, integral_add I0 I1]
  simp only [integral_const, integral_const_mul, h1, h.m2, h.m3, probReal_univ, smul_eq_mul]
  ring

/-- **The Bonami lemma**, by induction on the number of variables. -/
theorem bonami_aux (R : ℕ) : ∀ (ν : Fin R → Measure ℝ), (∀ i, GoodLaw (ν i)) →
    ∀ (d : ℕ) (c : Cube (Fin R) → ℝ), (∀ s, d < sdeg s → c s = 0) →
    ∫ x, mlEval c x ^ 4 ∂Measure.pi ν ≤ 9 ^ d * (∑ s, c s ^ 2) ^ 2 := by
  induction R with
  | zero =>
    intro ν hν d c hc
    have hP : ∀ i, IsProbabilityMeasure (ν i) := fun i ↦ (hν i).prob
    have hconst : ∀ x : Fin 0 → ℝ, mlEval c x = c (fun _ ↦ false) := by
      intro x
      unfold mlEval
      rw [Finset.sum_eq_single (fun _ ↦ false)
        (fun s _ hs ↦ absurd (Subsingleton.elim s _) hs) (fun h ↦ absurd (Finset.mem_univ _) h)]
      simp
    have hsum0 : ∑ s, c s ^ 2 = c (fun _ ↦ false) ^ 2 :=
      Finset.sum_eq_single (fun _ ↦ false) (fun s _ hs ↦ absurd (Subsingleton.elim s _) hs)
        (fun h ↦ absurd (Finset.mem_univ _) h)
    simp_rw [hconst]
    rw [integral_const, hsum0]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h9 : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
    have h0 : 0 ≤ c (fun _ ↦ false) ^ 4 := by positivity
    nlinarith
  | succ R ih =>
    intro ν hν d c hc
    have hP : ∀ i, IsProbabilityMeasure (ν i) := fun i ↦ (hν i).prob
    obtain ⟨c0, hc0def⟩ : ∃ c0 : Cube (Fin R) → ℝ, c0 = fun s ↦ c (Fin.cons false s) := ⟨_, rfl⟩
    obtain ⟨c1, hc1def⟩ : ∃ c1 : Cube (Fin R) → ℝ, c1 = fun s ↦ c (Fin.cons true s) := ⟨_, rfl⟩
    have hcons : ∀ (y : ℝ) (x : Fin R → ℝ),
        mlEval c (Fin.cons y x) = mlEval c0 x + y * mlEval c1 x := by
      intro y x
      rw [hc0def, hc1def]
      exact mlEval_cons c y x
    have hsum : ∑ s, c s ^ 2 = ∑ s, c0 s ^ 2 + ∑ s, c1 s ^ 2 := by
      rw [hc0def, hc1def]
      exact sum_cube_succ _
    have hc0 : ∀ s, d < sdeg s → c0 s = 0 := fun s hs ↦ by
      rw [hc0def]
      exact hc _ (by rw [sdeg_cons]; simp; omega)
    have hc1 : ∀ s, d - 1 < sdeg s → c1 s = 0 := fun s hs ↦ by
      rw [hc1def]
      exact hc _ (by rw [sdeg_cons]; simp; omega)
    have hν' : ∀ j : Fin R, GoodLaw (ν j.succ) := fun j ↦ hν j.succ
    obtain ⟨μ', hμ'⟩ : ∃ μ', μ' = Measure.pi (fun j : Fin R ↦ ν j.succ) := ⟨_, rfl⟩
    have IH0 := ih (fun j ↦ ν j.succ) hν' d c0 hc0
    have IH1 := ih (fun j ↦ ν j.succ) hν' (d - 1) c1 hc1
    rw [← hμ'] at IH0 IH1
    have hq : MemLp (mlEval c0) 4 μ' := hμ' ▸ memLp_mlEval_pi' _ (by norm_num)
      (fun j ↦ memLp_of_goodLaw (hν' j)) c0
    have hr : MemLp (mlEval c1) 4 μ' := hμ' ▸ memLp_mlEval_pi' _ (by norm_num)
      (fun j ↦ memLp_of_goodLaw (hν' j)) c1
    have hq4 := integrable_pow_four hq
    have hr4 := integrable_pow_four hr
    have hq2 : MemLp (fun x ↦ mlEval c0 x ^ 2) 2 μ' :=
      (memLp_two_iff_integrable_sq ((continuous_mlEval' c0).pow 2).aestronglyMeasurable).2
        (by simpa [← pow_mul] using hq4)
    have hr2 : MemLp (fun x ↦ mlEval c1 x ^ 2) 2 μ' :=
      (memLp_two_iff_integrable_sq ((continuous_mlEval' c1).pow 2).aestronglyMeasurable).2
        (by simpa [← pow_mul] using hr4)
    have hqr : Integrable (fun x ↦ mlEval c0 x ^ 2 * mlEval c1 x ^ 2) μ' := hq2.integrable_mul hr2
    have hCS := Gaussian.sq_integral_mul_le hq2 hr2
    simp only [← pow_mul] at hCS
    have hint : Integrable (fun x ↦ mlEval c x ^ 4) (Measure.pi ν) :=
      integrable_pow_four (memLp_mlEval_pi' _ (by norm_num) (fun i ↦ memLp_of_goodLaw (hν i)) c)
    have hE : ∫ x, mlEval c x ^ 4 ∂Measure.pi ν = ∫ x, mlEval c0 x ^ 4 ∂μ' +
        6 * ∫ x, mlEval c0 x ^ 2 * mlEval c1 x ^ 2 ∂μ' +
        (∫ y, y ^ 4 ∂ν 0) * ∫ x, mlEval c1 x ^ 4 ∂μ' := by
      rw [integral_pi_succ, integral_prod_symm _ (integrable_pi_succ ν hint), ← hμ']
      simp_rw [hcons, integral_quartic (hν 0)]
      have J : Integrable (fun y ↦ 6 * mlEval c0 y ^ 2 * mlEval c1 y ^ 2) μ' :=
        (hqr.const_mul 6).congr (ae_of_all _ fun x ↦ by ring)
      have J1 : Integrable (fun y ↦ mlEval c0 y ^ 4 + 6 * mlEval c0 y ^ 2 * mlEval c1 y ^ 2) μ' :=
        hq4.add J
      have J2 : Integrable (fun y ↦ (∫ y, y ^ 4 ∂ν 0) * mlEval c1 y ^ 4) μ' := hr4.const_mul _
      have e6 : ∫ y, 6 * mlEval c0 y ^ 2 * mlEval c1 y ^ 2 ∂μ' =
          6 * ∫ x, mlEval c0 x ^ 2 * mlEval c1 x ^ 2 ∂μ' := by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
      rw [integral_add J1 J2, integral_add hq4 J, integral_const_mul, e6]
    rw [hE, hsum]
    -- the numerical inequality
    obtain ⟨A4, hA4⟩ : ∃ A, A = ∫ x, mlEval c0 x ^ 4 ∂μ' := ⟨_, rfl⟩
    obtain ⟨B4, hB4⟩ : ∃ B, B = ∫ x, mlEval c1 x ^ 4 ∂μ' := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = ∫ x, mlEval c0 x ^ 2 * mlEval c1 x ^ 2 ∂μ' := ⟨_, rfl⟩
    obtain ⟨m4, hm4⟩ : ∃ m, m = ∫ y, y ^ 4 ∂ν 0 := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, a = ∑ s, c0 s ^ 2 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = ∑ s, c1 s ^ 2 := ⟨_, rfl⟩
    rw [← hA4, ← hB4, ← hC, ← hm4, ← ha, ← hb]
    rw [← hA4, ← ha] at IH0
    rw [← hB4, ← hb] at IH1
    norm_num at hCS
    rw [← hA4, ← hB4, ← hC] at hCS
    have hA0 : 0 ≤ A4 := hA4 ▸ integral_nonneg fun x ↦ by positivity
    have hB0 : 0 ≤ B4 := hB4 ▸ integral_nonneg fun x ↦ by positivity
    have hC0 : 0 ≤ C := hC ▸ integral_nonneg fun x ↦ by positivity
    have hm0 : 0 ≤ m4 := hm4 ▸ integral_nonneg fun x ↦ by positivity
    have hm9 : m4 ≤ 9 := hm4 ▸ (hν 0).m4
    have ha0 : 0 ≤ a := ha ▸ Finset.sum_nonneg fun s _ ↦ sq_nonneg _
    have hb0 : 0 ≤ b := hb ▸ Finset.sum_nonneg fun s _ ↦ sq_nonneg _
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have hb' : b = 0 := by
        rw [hb]
        refine Finset.sum_eq_zero fun s _ ↦ ?_
        rw [hc1def]
        simp only
        rw [hc _ (by rw [sdeg_cons]; simp)]
        ring
      rw [hb'] at IH1 ⊢
      have hB : B4 = 0 := le_antisymm (by simpa using IH1) hB0
      rw [hB] at hCS ⊢
      have hC' : C = 0 := by nlinarith
      rw [hC']
      simpa using IH0
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at IH1
      have hK : (0 : ℝ) < 9 ^ k := by positivity
      rw [pow_succ] at IH0 ⊢
      have hAB : A4 * B4 ≤ (9 ^ k * 9 * a ^ 2) * (9 ^ k * b ^ 2) :=
        mul_le_mul IH0 IH1 hB0 (by positivity)
      have hC3 : C ≤ 3 * 9 ^ k * a * b := by
        have h1 : C ^ 2 ≤ (3 * 9 ^ k * a * b) ^ 2 := by nlinarith
        exact (pow_le_pow_iff_left₀ hC0 (by positivity) (by norm_num)).1 h1
      have hmB : m4 * B4 ≤ 9 * B4 := mul_le_mul_of_nonneg_right hm9 hB0
      nlinarith

end Bonami

open Bonami

/-- The uniform law on `{±1}`. -/
noncomputable def signLaw : Measure ℝ := (1 / 2 : ENNReal) • (Measure.dirac 1 + Measure.dirac (-1))

theorem goodLaw_signLaw : GoodLaw signLaw := by
  have hint : ∀ f : ℝ → ℝ, Integrable f signLaw := fun f ↦
    ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
      (by simp)
  have hI : ∀ f : ℝ → ℝ, ∫ x, f x ∂signLaw = (f 1 + f (-1)) / 2 := by
    intro f
    rw [signLaw, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
      (integrable_dirac (by simp)), integral_dirac, integral_dirac]
    simp only [smul_eq_mul]
    norm_num
    ring
  refine ⟨⟨?_⟩, hint _, ?_, ?_, ?_, ?_⟩
  · simp only [signLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  all_goals rw [hI]; norm_num

/-- Orthonormality of the multilinear monomials under a product of good laws. -/
theorem integral_mlEval_mul_pi (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    (c d : Cube (Fin R) → ℝ) :
    ∫ x, mlEval c x * mlEval d x ∂Measure.pi ν = ∑ s, c s * d s := by
  have := fun i ↦ (hν i).prob
  exact MultilinearGauss.integral_mlEval_mul_pi' ν
    (fun i ↦ integrable_pow_of_goodLaw (hν i) (k := 2) (by norm_num)) (fun i ↦ (hν i).m1)
    (fun i ↦ (hν i).m2) c d

theorem memLp_mlEval_pi (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i))
    (c : Cube (Fin R) → ℝ) : MemLp (fun x ↦ mlEval c x) 4 (Measure.pi ν) := by
  have := fun i ↦ (hν i).prob
  exact MultilinearGauss.memLp_mlEval_pi' ν (by norm_num) (fun i ↦ memLp_of_goodLaw (hν i)) c

/-- **The Bonami lemma**. -/
theorem bonami (ν : Fin R → Measure ℝ) (hν : ∀ i, GoodLaw (ν i)) {d : ℕ}
    (c : Cube (Fin R) → ℝ) (hc : ∀ s, d < sdeg s → c s = 0) :
    ∫ x, mlEval c x ^ 4 ∂Measure.pi ν ≤ 9 ^ d * (∑ s, c s ^ 2) ^ 2 :=
  bonami_aux R ν hν d c hc

end BHSV25.BK.Aint
