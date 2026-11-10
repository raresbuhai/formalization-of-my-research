module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobRound
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobSize

/-! Population covariance bounds obtained from the encoded observed sample. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobBounds

open Common _root_.ABBKS26.Tree Matrix
open Sources Builders Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

theorem observedCenter_bound {n d : ℕ} (x : Fin n → Vec d) (N : Finset (Fin n))
    (X : ℝ) (hX : 0 ≤ X) (hx : ∀ l ∈ N, ∀ i, |x l i| ≤ X) (i : Fin d) :
    |ABBKS26.RefineAux.observedCenter x N i| ≤ X := by
  classical
  by_cases hN : N.Nonempty
  · have hc : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.mpr hN
    change |(N.card : ℝ)⁻¹ * (∑ l ∈ N, x l) i| ≤ X
    rw [Finset.sum_apply, abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le)]
    calc
      _ ≤ (N.card : ℝ)⁻¹ * ∑ l ∈ N, |x l i| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (N.card : ℝ)⁻¹ * ∑ _l ∈ N, X := by
        gcongr with l hl
        exact hx l hl i
      _ = X := by simp [hc.ne']
  · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    simpa [ABBKS26.RefineAux.observedCenter, he] using hX

theorem observedCov_entries {n d : ℕ} (x : Fin n → Vec d) (N : Finset (Fin n))
    (X : ℝ) (hX : 0 ≤ X) (hx : ∀ l ∈ N, ∀ i, |x l i| ≤ X) (i j : Fin d) :
    |ABBKS26.RefineAux.observedCov x N i j| ≤ 4 * X ^ 2 := by
  classical
  by_cases hN : N.Nonempty
  · have hc : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.mpr hN
    have herr (l : Fin n) (hl : l ∈ N) (a : Fin d) :
        |x l a - ABBKS26.RefineAux.observedCenter x N a| ≤ 2 * X := by
      exact (abs_sub _ _).trans (by
        have hm := observedCenter_bound x N X hX hx a
        linarith only [hx l hl a, hm])
    simp only [ABBKS26.RefineAux.observedCov, Matrix.smul_apply, Matrix.sum_apply,
      vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le)]
    calc
      _ ≤ (N.card : ℝ)⁻¹ * ∑ l ∈ N,
          |(x l i - ABBKS26.RefineAux.observedCenter x N i) *
            (x l j - ABBKS26.RefineAux.observedCenter x N j)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (N.card : ℝ)⁻¹ * ∑ _l ∈ N, (2 * X) * (2 * X) := by
        gcongr with l hl
        rw [abs_mul]
        exact mul_le_mul (herr l hl i) (herr l hl j) (abs_nonneg _) (by positivity)
      _ = _ := by simp [hc.ne']; ring
  · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    simp only [ABBKS26.RefineAux.observedCov, he, Finset.sum_empty, smul_zero,
      Matrix.zero_apply, abs_zero]
    positivity

theorem observedCov_upper {n d : ℕ} (x : Fin n → Vec d) (N : Finset (Fin n))
    (X : ℝ) (hX : 0 ≤ X) (hx : ∀ l ∈ N, ∀ i, |x l i| ≤ X) (v : Vec d) :
    qform (ABBKS26.RefineAux.observedCov x N) v ≤ 4 * d * X ^ 2 * sqnorm v := by
  have he := FrobRound.frobSq_le_of_entries (ABBKS26.RefineAux.observedCov x N)
    (4 * X ^ 2) (by positivity) (observedCov_entries x N X hX hx)
  apply (le_abs_self _).trans
  apply Rounding.DetRoundAux.abs_qform_le _ (4 * d * X ^ 2) (by positivity) _ v
  nlinarith only [he]

theorem sample_entry {n d : ℕ} (x : Fin n → Fin d → ℚ) (l : Fin n) (i : Fin d) :
    |(x l i : ℝ)| ≤ (2 : ℝ) ^ (encPoints (pointsOf x)).length := by
  have hb := (FrobSize.point_bound (pointsOf x) l.val i.val).magnitude
  rw [pointsOf_get] at hb
  exact_mod_cast hb

/-- The same sample-determined bound holds for every compatible component at this node. -/
theorem prepared_cov_upper {n k d : ℕ} (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (h : ℕ) (N : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card) :
    ∀ j ∈ I, ∀ v, qform (M.S j) v ≤
      (16 * d * ((2 : ℝ) ^ (encPoints (pointsOf x)).length) ^ 2 /
        ((ps h).w : ℝ)) * sqnorm v := by
  classical
  let ref := ABBKS26.RefineAux.roundedReference M ω r N I hI
  obtain ⟨hc, hπ⟩ := hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh N I hI hl hN
  obtain ⟨hv, hres, _, _, _, he⟩ := hc
  have hw : (0 : ℝ) < (ps h).w := by
    have hw' := (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).1
    exact_mod_cast hw'
  intro j hj v
  have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [I.range_orderEmbOfFin]
    exact hj
  obtain ⟨a, rfl⟩ := hj'
  have hb := ABBKS26.RefineAux.component_cov_le_observed ref _ _ hv hres hπ he a v
  have hobs := observedCov_upper (fun l i ↦ (x l i : ℝ)) N
    ((2 : ℝ) ^ (encPoints (pointsOf x)).length) (by positivity)
    (fun l _ i ↦ sample_entry x l i) v
  have hsame : ref.observed = fun l i ↦ (x l i : ℝ) := by
    subst x
    rfl
  rw [hsame] at hb
  change (((ps h).w / 2 : ℚ) : ℝ) * qform (M.S _) v ≤
    2 * qform (ABBKS26.RefineAux.observedCov (fun l i ↦ (x l i : ℝ)) N) v at hb
  push_cast at hb
  change (ps h).w / 2 * qform (M.S ((I.orderEmbOfFin rfl) a)) v ≤ _ at hb
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  nlinarith only [hb, hobs]

/-- An executable rational upper bound for the component covariance forms. -/
def covBound (a : Args) : ℚ :=
  16 * a.1.1 * ((2 : ℚ) ^ (encPoints a.1.2.2.2.1).length) ^ 2 / field a 0

/-- Encoding lengths give an exponent without converting a binary magnitude to unary. -/
def exponent (a : Args) : ℕ :=
  (Encoding.encRat (covBound a)).length + (Encoding.encRat (field a 8)).length + a.1.1 + 1

theorem exponent_cov (a : Args) : (covBound a : ℝ) ≤ (2 : ℝ) ^ exponent a := by
  have hb := (FrobSize.of_encoding (le_refl (Encoding.encRat (covBound a)).length)).mono
    (show (Encoding.encRat (covBound a)).length ≤ exponent a by unfold exponent; omega)
  exact_mod_cast (le_abs_self (covBound a)).trans hb.magnitude

theorem exponent_radius (a : Args) : (field a 8 : ℝ) ≤ (2 : ℝ) ^ exponent a := by
  have hb := (FrobSize.of_encoding (le_refl (Encoding.encRat (field a 8)).length)).mono
    (show (Encoding.encRat (field a 8)).length ≤ exponent a by unfold exponent; omega)
  exact_mod_cast (le_abs_self (field a 8)).trans hb.magnitude

theorem exponent_dim (a : Args) : (a.1.1 : ℝ) ≤ (2 : ℝ) ^ exponent a := by
  have hd : a.1.1 ≤ exponent a := by unfold exponent; omega
  exact_mod_cast hd.trans (Nat.lt_two_pow_self (n := exponent a)).le

theorem covBound_agrees {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k) :
    (covBound (args k ps x h N, fuel) : ℝ) =
      16 * d * ((2 : ℝ) ^ (encPoints (pointsOf x)).length) ^ 2 / ((ps h).w : ℝ) := by
  unfold covBound
  rw [field_args _ _ _ _ _ _ hh]
  change ((16 * (d : ℚ) * ((2 : ℚ) ^ (encPoints (pointsOf x)).length) ^ 2 /
    (ps h).w : ℚ) : ℝ) = _
  push_cast
  rfl

theorem covBound_polytime : ComputableInPolyTime covBound encArgs Encoding.encRat := by
  have hd : ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary := by fun_prop
  have hx : ComputableInPolyTime (fun a : Args ↦ a.1.2.2.2.1)
      encArgs encPoints := by fun_prop
  have hlen := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encPoints).comp hx.tidy)
  have hpow := rat_two_pow' hlen
  exact rat_div' (rat_mul' (rat_mul' (const 16)
    (rat_natCast' (unary_to_binary.comp hd))) (rat_mul' hpow hpow))
      (field_polytime 0) |>.of_enc_eq (fun _ ↦ by
        congr 1
        simp only [covBound, pow_two, Function.comp_apply])

theorem exponent_polytime : ComputableInPolyTime exponent encArgs encUnary := by
  have hc := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.encoding_length Encoding.encRat).comp covBound_polytime.tidy)
  have hR := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.encoding_length Encoding.encRat).comp (field_polytime 8).tidy)
  exact unary_add' (unary_add' (unary_add' hc hR) (by fun_prop)) (const 1)

end ABBKS26.Assembly.Exec.RefineSynth.FrobBounds
