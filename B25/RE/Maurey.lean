module

public import B25.Basic

/-!
# Sparsification with `ℓ₁`-norm error [B25, Lemma 2.1]

`B25.exists_tuple_approx`: for a matrix whose columns have norm at most `D`, every `β ≠ 0` and
every `s ≥ 1`, there is a tuple `a` of `s` signed coordinates of the support of `β` with
`‖Xβ - (‖β‖₁/s) X (∑ₜ ±e_{aₜ})‖₂² ≤ D² ‖β‖₁² / s`.

This is Maurey's empirical method, as in the proof of [B25, Lemma 2.1] from the approximate
Carathéodory theorem [Vershynin, Theorem 0.0.2]: draw `s` independent coordinates `j` with
probability `|βⱼ|/‖β‖₁` and the sign of `βⱼ`; the vector `Z = sign(βⱼ) ‖β‖₁ Xⱼ` has mean `Xβ`
and `E ‖Z‖₂² ≤ D² ‖β‖₁²`, so the average of `s` independent copies has
`E ‖avg - Xβ‖₂² = (E ‖Z‖₂² - ‖Xβ‖₂²)/s ≤ D² ‖β‖₁²/s`, and some outcome of positive probability
does at least as well. The average is `(‖β‖₁/s) X (∑ₜ ±e_{jₜ})`, an integer combination of the
columns up to the factor `‖β‖₁/s`; this is what lets the union bound of Theorem 1.5 run over
finitely many directions.

No measure theory is needed: the expectation is a finite sum with weights `pⱼ = |βⱼ|/‖β‖₁`, and
the draws are fixed one at a time (the method of conditional expectations). With
`Yⱼ = Zⱼ - Xβ`, of weighted mean `0`, every vector `S` has
`∑ⱼ pⱼ ‖S + Yⱼ‖₂² = ‖S‖₂² + ∑ⱼ pⱼ ‖Yⱼ‖₂²` (`B25.MR.wsumDotAddEqMaurey`), so some `j` of the
support has `‖S + Yⱼ‖₂² ≤ ‖S‖₂² + E ‖Z - Xβ‖₂²` (`B25.MR.existsStepMaurey`); after `s` steps,
`‖∑ₜ Y_{jₜ}‖₂² ≤ s E ‖Z - Xβ‖₂²` (`B25.MR.existsTupleSumLeMaurey`), the bound that the expectation
gives for a random tuple, and `E ‖Z - Xβ‖₂² ≤ E ‖Z‖₂²` is the same expansion with `S = Xβ`.
-/

@[expose] public section

namespace B25

open Matrix

namespace MR

/-- The expansion behind Maurey's method: for weights `p` summing to `1` and vectors `Y` of
weighted mean `0`, `∑ⱼ pⱼ ‖S + Yⱼ‖₂² = ‖S‖₂² + ∑ⱼ pⱼ ‖Yⱼ‖₂²`. -/
theorem wsumDotAddEqMaurey {n d : ℕ} (p : Fin d → ℝ) (hp : ∑ j, p j = 1)
    (Y : Fin d → Fin n → ℝ) (hY : ∑ j, p j • Y j = 0) (S : Fin n → ℝ) :
    ∑ j, p j * ((S + Y j) ⬝ᵥ (S + Y j)) = S ⬝ᵥ S + ∑ j, p j * (Y j ⬝ᵥ Y j) := by
  have h2 : ∑ j, p j * (S ⬝ᵥ Y j) = 0 := by
    have : S ⬝ᵥ (∑ j, p j • Y j) = ∑ j, p j * (S ⬝ᵥ Y j) := by
      rw [dotProduct_sum]
      simp [dotProduct_smul]
    rw [← this, hY, dotProduct_zero]
  calc ∑ j, p j * ((S + Y j) ⬝ᵥ (S + Y j))
      = ∑ j, (p j * (S ⬝ᵥ S) + 2 * (p j * (S ⬝ᵥ Y j)) + p j * (Y j ⬝ᵥ Y j)) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [add_dotProduct, dotProduct_add, dotProduct_comm (Y j) S]
        ring
    _ = (∑ j, p j) * (S ⬝ᵥ S) + 2 * ∑ j, p j * (S ⬝ᵥ Y j) + ∑ j, p j * (Y j ⬝ᵥ Y j) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = S ⬝ᵥ S + ∑ j, p j * (Y j ⬝ᵥ Y j) := by
        rw [hp, h2]
        ring

/-- A weighted average is attained: if `∑ⱼ pⱼ Fⱼ ≤ A` for weights summing to `1` that are
positive exactly on the support of `β ≠ 0`, some `j` with `βⱼ ≠ 0` has `Fⱼ ≤ A`. -/
theorem existsStepMaurey {d : ℕ} {β : Fin d → ℝ} (hβ : β ≠ 0) {p : Fin d → ℝ}
    (hp : ∑ j, p j = 1) (hp0 : ∀ j, β j ≠ 0 → 0 < p j) (hpz : ∀ j, β j = 0 → p j = 0)
    (F : Fin d → ℝ) {A : ℝ} (hF : ∑ j, p j * F j ≤ A) : ∃ j, β j ≠ 0 ∧ F j ≤ A := by
  by_contra h
  push Not at h
  obtain ⟨j₀, hj₀⟩ : ∃ j, β j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hβ (funext h')
  have hlt : ∑ j, p j * A < ∑ j, p j * F j := by
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : β j = 0
      · simp [hpz j hj]
      · exact mul_le_mul_of_nonneg_left (h j hj).le (hp0 j hj).le
    · exact ⟨j₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h j₀ hj₀) (hp0 j₀ hj₀)⟩
  rw [← Finset.sum_mul, hp, one_mul] at hlt
  linarith

/-- The method of conditional expectations applied to Maurey's empirical method: choosing the
coordinates one at a time, each no worse than the average, gives `k` coordinates of the support
with `‖∑ₜ Y_{Jₜ}‖₂² ≤ k ∑ⱼ pⱼ ‖Yⱼ‖₂²`. -/
theorem existsTupleSumLeMaurey {n d : ℕ} {β : Fin d → ℝ} (hβ : β ≠ 0) {p : Fin d → ℝ}
    (hp : ∑ j, p j = 1) (hp0 : ∀ j, β j ≠ 0 → 0 < p j) (hpz : ∀ j, β j = 0 → p j = 0)
    {Y : Fin d → Fin n → ℝ} (hY : ∑ j, p j • Y j = 0) (k : ℕ) :
    ∃ J : Fin k → Fin d, (∀ t, β (J t) ≠ 0) ∧
      (∑ t, Y (J t)) ⬝ᵥ (∑ t, Y (J t)) ≤ k * ∑ j, p j * (Y j ⬝ᵥ Y j) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun t ↦ t.elim0, by simp⟩
  | succ k ih =>
    obtain ⟨J, hJ, hle⟩ := ih
    obtain ⟨j, hj, hjle⟩ := existsStepMaurey hβ hp hp0 hpz
      (fun j ↦ (∑ t, Y (J t) + Y j) ⬝ᵥ (∑ t, Y (J t) + Y j))
      (wsumDotAddEqMaurey p hp Y hY _).le
    refine ⟨Fin.cons j J, fun t ↦ ?_, ?_⟩
    · refine Fin.cases ?_ (fun t ↦ ?_) t
      · simpa using hj
      · simpa using hJ t
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [add_comm (Y j)]
      push_cast
      linarith

end MR

/-- **Maurey's empirical method** [B25, Lemma 2.1]. -/
theorem exists_tuple_approx {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) {D : ℝ}
    (hD : ∀ j, ∑ i, X i j ^ 2 ≤ D ^ 2) {β : Fin d → ℝ} (hβ : β ≠ 0) {s : ℕ} (hs : 1 ≤ s) :
    ∃ a : Fin s → Fin d × Bool, (∀ t, β (a t).1 ≠ 0) ∧
      (X *ᵥ β - (l1 β / s) • (X *ᵥ tupleVec a)) ⬝ᵥ
          (X *ᵥ β - (l1 β / s) • (X *ᵥ tupleVec a)) ≤ D ^ 2 * l1 β ^ 2 / s := by
  classical
  set L := l1 β
  have hL : 0 < L := by
    obtain ⟨j₀, hj₀⟩ : ∃ j, β j ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hβ (funext h')
    exact Finset.sum_pos' (fun j _ ↦ abs_nonneg _) ⟨j₀, Finset.mem_univ _, abs_pos.mpr hj₀⟩
  set p : Fin d → ℝ := fun j ↦ |β j| / L with hpdef
  set σ : Fin d → ℝ := fun j ↦ if 0 < β j then 1 else -1 with hσdef
  set col : Fin d → Fin n → ℝ := fun j ↦ X *ᵥ Pi.single j 1 with hcoldef
  set Z : Fin d → Fin n → ℝ := fun j ↦ (L * σ j) • col j with hZdef
  set Y : Fin d → Fin n → ℝ := fun j ↦ Z j - X *ᵥ β with hYdef
  have hp : ∑ j, p j = 1 := by
    simp only [hpdef, ← Finset.sum_div]
    exact div_self hL.ne'
  have hp0 : ∀ j, β j ≠ 0 → 0 < p j := fun j hj ↦ div_pos (abs_pos.mpr hj) hL
  have hpz : ∀ j, β j = 0 → p j = 0 := fun j hj ↦ by simp [hpdef, hj]
  have hpσ : ∀ j, p j * (L * σ j) = β j := by
    intro j
    simp only [hpdef, hσdef]
    split_ifs with h
    · rw [abs_of_pos h]
      field_simp
    · rw [abs_of_nonpos (not_lt.mp h)]
      field_simp
  have hXβ : X *ᵥ β = ∑ j, β j • col j := by
    funext i
    simp [hcoldef, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hmean : ∑ j, p j • Z j = X *ᵥ β := by
    rw [hXβ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hZdef, smul_smul, hpσ]
  have hY : ∑ j, p j • Y j = 0 := by
    simp only [hYdef, smul_sub, Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hp, one_smul,
      sub_self]
  have hZZ : ∀ j, Z j ⬝ᵥ Z j ≤ L ^ 2 * D ^ 2 := by
    intro j
    have hσ2 : σ j * σ j = 1 := by
      simp only [hσdef]
      split_ifs <;> norm_num
    have hc : col j ⬝ᵥ col j = ∑ i, X i j ^ 2 := by
      simp [hcoldef, dotProduct, sq]
    calc Z j ⬝ᵥ Z j = L ^ 2 * (σ j * σ j) * (col j ⬝ᵥ col j) := by
          simp only [hZdef, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          ring
      _ ≤ L ^ 2 * D ^ 2 := by
          rw [hσ2, mul_one, hc]
          exact mul_le_mul_of_nonneg_left (hD j) (sq_nonneg L)
  have hV : ∑ j, p j * (Y j ⬝ᵥ Y j) ≤ L ^ 2 * D ^ 2 := by
    have h := MR.wsumDotAddEqMaurey p hp Y hY (X *ᵥ β)
    have hsub : ∀ j, X *ᵥ β + Y j = Z j := fun j ↦ by simp [hYdef]
    simp only [hsub] at h
    have hnn : 0 ≤ (X *ᵥ β) ⬝ᵥ (X *ᵥ β) := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    have hle : ∑ j, p j * (Z j ⬝ᵥ Z j) ≤ ∑ j, p j * (L ^ 2 * D ^ 2) :=
      Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hZZ j) (div_nonneg (abs_nonneg _) hL.le)
    rw [← Finset.sum_mul, hp, one_mul] at hle
    linarith
  obtain ⟨J, hJ, hJle⟩ := MR.existsTupleSumLeMaurey hβ hp hp0 hpz hY s
  refine ⟨fun t ↦ (J t, decide (0 < β (J t))), hJ, ?_⟩
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have htup : X *ᵥ tupleVec (fun t ↦ (J t, decide (0 < β (J t)))) =
      ∑ t, σ (J t) • col (J t) := by
    simp only [tupleVec, mulVec_sum, mulVec_smul, hσdef, hcoldef, decide_eq_true_eq]
  have hsumY : ∑ t, Y (J t) = ∑ t, Z (J t) - (s : ℝ) • X *ᵥ β := by
    simp only [hYdef]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_smul_eq_nsmul]
  have hsumZ : (L / s) • ∑ t, σ (J t) • col (J t) = (1 / s : ℝ) • ∑ t, Z (J t) := by
    simp only [Finset.smul_sum, hZdef, smul_smul]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    congr 1
    ring
  have hvec : X *ᵥ β - (L / s) • (X *ᵥ tupleVec (fun t ↦ (J t, decide (0 < β (J t))))) =
      (-(1 / s : ℝ)) • ∑ t, Y (J t) := by
    rw [htup, hsumZ, hsumY, smul_sub, smul_smul,
      show -(1 / (s : ℝ)) * s = -1 by field_simp, neg_smul, neg_one_smul, sub_neg_eq_add,
      neg_add_eq_sub]
  rw [hvec, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hq : (∑ t, Y (J t)) ⬝ᵥ (∑ t, Y (J t)) ≤ s * (L ^ 2 * D ^ 2) :=
    hJle.trans (mul_le_mul_of_nonneg_left hV hspos.le)
  calc -(1 / (s : ℝ)) * (-(1 / s) * ((∑ t, Y (J t)) ⬝ᵥ (∑ t, Y (J t))))
      = (∑ t, Y (J t)) ⬝ᵥ (∑ t, Y (J t)) / s / s := by ring
    _ ≤ s * (L ^ 2 * D ^ 2) / s / s := by gcongr
    _ = D ^ 2 * L ^ 2 / s := by
        field_simp

end B25
