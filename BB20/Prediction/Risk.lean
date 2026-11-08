module

public import BB20.Basic
public import BB20.Prediction.Logistic

/-!
# The population risk of the regression step

Fix a variable `u` and a set `V ∌ u` of variables whose characters `χ_T`, `T ⊆ V`, are the
features. The population risk of weights `w` is `L(w) = E[l(X_u (w · z))]`
(`BB20.Prediction.popRisk`), with `l` the logistic loss.

* `BB20.Prediction.popRisk_eq`: conditioning on `X_{∖u}`,
  `L(w) = E[φ_{p(X)}(w · z)]` with `p = P(X_u = 1 | X_{∖u})` and the conditional risk `φ`
  (`BB20.Prediction.condRisk`). Configurations are paired with the one that differs at `u`
  (`BB20.Prediction.sum_update_add_update`).
* `BB20.Prediction.predError_le`: by Pinsker's inequality, the prediction error is at most half
  the excess risk `L(w) - L*`, where `L* = E[φ_p(2 E_u)]` (`BB20.Prediction.optRisk`) is the risk
  of the true local field `p = σ(2 E_u)`.
* The weights `w̄_T = 2 f̂(T ∪ {u})` (`BB20.Prediction.wbar`) have `‖w̄‖₁ ≤ 2γ`, and
  `2 E_u - w̄ · z` is `2 ∑ f̂(S) χ_{S ∖ u}` over the `S ∋ u` with `S ∖ u ⊄ V`. If `V` contains the
  `ζ`-strong neighbours of `u`, each nonzero such `f̂(S)` is smaller than `ζ`, and there are at most
  `D^d` of them (`S ∖ u` is a nonempty set of fewer than `d` neighbours,
  `BB20.Prediction.card_small_subsets_le`). So `|2 E_u - w̄ · z| ≤ 2√ε` under the hypothesis on `ζ`
  of [BB20, Theorem 12], and by smoothness `L(w̄) - L* ≤ ε / 2`
  (`BB20.Prediction.popRisk_wbar_sub_le`).
* `BB20.Prediction.predError_le_of_dev`: if the empirical and population risks are close
  (uniformly on the ball for `L ≤ L̂ + ε/8`, and at `w̄` for `L̂ ≤ L + ε/8`), then every
  near-minimizer within `ε/4` of the empirical risk has prediction error at most `ε`.
-/

@[expose] public section

namespace BB20.Prediction

open Finset

variable {n m : ℕ}

theorem update_eq_self_of_eq {x : Config n} {u : Fin n} {b : Bool} (h : x u = b) :
    Function.update x u b = x := by
  rw [← h]
  exact Function.update_eq_self u x

/-- Pairing each configuration with the one that differs from it at `u`. -/
theorem sum_update_add_update (u : Fin n) (F : Config n → ℝ) :
    ∑ x, (F (Function.update x u true) + F (Function.update x u false)) = 2 * ∑ x, F x := by
  set fl : Config n → Config n := fun x ↦ Function.update x u (!x u) with hfl
  have hinv : Function.Involutive fl := by
    intro x
    simp [fl]
  have hpt : ∀ x, F (Function.update x u true) + F (Function.update x u false) =
      F x + F (fl x) := by
    intro x
    cases hx : x u
    · rw [update_eq_self_of_eq hx]
      simp only [fl, hx, Bool.not_false]
      ring
    · rw [update_eq_self_of_eq hx]
      simp only [fl, hx, Bool.not_true]
  have hfl := Equiv.sum_comp hinv.toPerm F
  simp only [Function.Involutive.coe_toPerm] at hfl
  rw [Finset.sum_congr rfl fun x _ ↦ hpt x, Finset.sum_add_distrib, hfl]
  ring

theorem condProb_update (R : RBM n m) (u : Fin n) (x : Config n) (b : Bool) :
    R.condProb u (Function.update x u b) = R.condProb u x := by
  simp [RBM.condProb, Function.update_idem]

/-- **Conditioning on `X_{∖u}`**: for `h` not depending on the value at `u`,
`E[h(X_u, X)] = E[p(X) h(1, X) + (1 - p(X)) h(-1, X)]` with `p = P(X_u = 1 | X_{∖u})`. -/
theorem sum_obsProb_mul_eq (R : RBM n m) (u : Fin n) (h : Bool → Config n → ℝ)
    (hh : ∀ b c x, h b (Function.update x u c) = h b x) :
    ∑ x, R.obsProb x * h (x u) x =
      ∑ x, R.obsProb x * (R.condProb u x * h true x + (1 - R.condProb u x) * h false x) := by
  have key : ∀ G : Config n → ℝ, ∑ x, G x =
      1 / 2 * ∑ x, (G (Function.update x u true) + G (Function.update x u false)) := by
    intro G
    rw [sum_update_add_update]
    ring
  rw [key (fun x ↦ R.obsProb x * h (x u) x),
    key (fun x ↦ R.obsProb x * (R.condProb u x * h true x + (1 - R.condProb u x) * h false x))]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Function.update_self, hh, condProb_update]
  have hp := R.obsProb_pos (Function.update x u true)
  have hq := R.obsProb_pos (Function.update x u false)
  have hc : R.condProb u x = R.obsProb (Function.update x u true) /
      (R.obsProb (Function.update x u true) + R.obsProb (Function.update x u false)) := rfl
  rw [hc]
  field_simp
  ring

theorem chi_update {T : Finset (Fin n)} {u : Fin n} (hu : u ∉ T) (x : Config n) (b : Bool) :
    chi T (Function.update x u b) = chi T x :=
  Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hu)]

theorem score_update {V : Finset (Fin n)} {u : Fin n} (hu : u ∉ V) (w : Finset (Fin n) → ℝ)
    (x : Config n) (b : Bool) : score V w (Function.update x u b) = score V w x :=
  Finset.sum_congr rfl fun T hT ↦ by
    rw [chi_update fun h ↦ hu (Finset.mem_powerset.1 hT h)]

theorem abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> simp [spin]

theorem abs_chi (T : Finset (Fin n)) (x : Config n) : |chi T x| = 1 := by
  rw [chi, Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ ↦ abs_spin _

/-- The population risk `L(w) = E[l(X_u (w · z))]`. -/
noncomputable def popRisk (R : RBM n m) (u : Fin n) (V : Finset (Fin n))
    (w : Finset (Fin n) → ℝ) : ℝ :=
  ∑ x, R.obsProb x * logLoss (spin (x u) * score V w x)

/-- The risk `L* = E[φ_p(2 E_u)]` of the true local field. -/
noncomputable def optRisk (R : RBM n m) (u : Fin n) : ℝ :=
  ∑ x, R.obsProb x * condRisk (R.condProb u x) (2 * R.field u x)

theorem popRisk_eq (R : RBM n m) {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V)
    (w : Finset (Fin n) → ℝ) :
    popRisk R u V w = ∑ x, R.obsProb x * condRisk (R.condProb u x) (score V w x) := by
  unfold popRisk
  rw [sum_obsProb_mul_eq R u (fun b x ↦ logLoss (spin b * score V w x))
    (fun b c x ↦ by simp only [score_update hu])]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [condRisk, spin]

/-- The prediction error is at most half the excess risk (Pinsker's inequality). -/
theorem predError_le (R : RBM n m) {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V)
    (w : Finset (Fin n) → ℝ) :
    R.predError u V w ≤ (popRisk R u V w - optRisk R u) / 2 := by
  rw [popRisk_eq R hu, optRisk, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hp := R.obsProb_pos x
  have h := pinsker (2 * R.field u x) (score V w x)
  rw [R.condProb_eq, sigmoid_eq, sigmoid_eq]
  have h' := mul_le_mul_of_nonneg_left h hp.le
  nlinarith

/-- The weights `w̄_T = 2 f̂(T ∪ {u})` of the local field. -/
noncomputable def wbar (R : RBM n m) (u : Fin n) (T : Finset (Fin n)) : ℝ :=
  2 * R.fourier (insert u T)

theorem l1Norm_wbar_le (R : RBM n m) {γ : ℝ} (hW : R.WidthLE γ) {u : Fin n}
    {V : Finset (Fin n)} (hu : u ∉ V) : l1Norm V (wbar R u) ≤ 2 * γ := by
  unfold l1Norm wbar
  have hinj : Set.InjOn (insert u) (V.powerset : Set (Finset (Fin n))) := by
    intro T hT T' hT' h
    have h1 : u ∉ T := fun h' ↦ hu (Finset.mem_powerset.1 hT h')
    have h2 : u ∉ T' := fun h' ↦ hu (Finset.mem_powerset.1 hT' h')
    rw [← Finset.erase_insert h1, ← Finset.erase_insert h2]
    exact congrArg (·.erase u) h
  calc ∑ T ∈ V.powerset, |2 * R.fourier (insert u T)|
      = 2 * ∑ T ∈ V.powerset, |R.fourier (insert u T)| := by
        simp [abs_mul, Finset.mul_sum]
    _ = 2 * ∑ S ∈ V.powerset.image (insert u), |R.fourier S| := by
        rw [Finset.sum_image hinj]
    _ ≤ 2 * ∑ S ∈ univ.filter (u ∈ ·), |R.fourier S| := by
        gcongr
        intro S hS
        simp only [Finset.mem_image] at hS
        obtain ⟨T, _, rfl⟩ := hS
        simp
    _ ≤ 2 * γ := by
        gcongr
        exact hW u

/-- `2 E_u - w̄ · z` collects the coefficients `f̂(S)`, `S ∋ u`, with `S ∖ u ⊄ V`. -/
theorem two_field_sub_score (R : RBM n m) {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V)
    (x : Config n) :
    2 * R.field u x - score V (wbar R u) x =
      2 * ∑ S ∈ (univ.filter (u ∈ ·)).filter (fun S ↦ ¬ S.erase u ⊆ V),
        R.fourier S * chi (S.erase u) x := by
  have hgood : ∑ S ∈ (univ.filter (u ∈ ·)).filter (fun S ↦ S.erase u ⊆ V),
      R.fourier S * chi (S.erase u) x = ∑ T ∈ V.powerset, R.fourier (insert u T) * chi T x := by
    apply Finset.sum_nbij' (fun S ↦ S.erase u) (fun T ↦ insert u T)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.mem_powerset.2 hS.2
    · intro T hT
      have hT' := Finset.mem_powerset.1 hT
      have huT : u ∉ T := fun h ↦ hu (hT' h)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert_self,
        Finset.erase_insert huT]
      exact hT'
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.insert_erase hS.1
    · intro T hT
      exact Finset.erase_insert fun h ↦ hu (Finset.mem_powerset.1 hT h)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.insert_erase hS.1]
  have hscore : score V (wbar R u) x = 2 * ∑ T ∈ V.powerset, R.fourier (insert u T) * chi T x := by
    simp only [score, wbar, Finset.mul_sum, mul_assoc]
  rw [RBM.field, ← Finset.sum_filter_add_sum_filter_not _ (fun S ↦ S.erase u ⊆ V), hgood, hscore]
  ring

/-- There are at most `|N|^d` nonempty subsets of `N` with fewer than `d` elements. -/
theorem card_small_subsets_le {α : Type*} (N : Finset α) (d : ℕ) :
    (N.powerset.filter fun T ↦ T.Nonempty ∧ T.card < d).card ≤ N.card ^ d := by
  classical
  rcases Nat.eq_zero_or_pos N.card with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp [Finset.filter_singleton]
  have hsub : N.powerset.filter (fun T ↦ T.Nonempty ∧ T.card < d) ⊆
      (Fintype.piFinset fun _ : Fin (d - 1) ↦ N).image (fun f ↦ Finset.univ.image f) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTN, ⟨t0, ht0⟩, hTd⟩ := hT
    rw [Finset.mem_image]
    refine ⟨fun i ↦ if h : i.val < T.card then (T.equivFin.symm ⟨i.val, h⟩ : α) else t0, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      split_ifs
      · exact hTN (T.equivFin.symm _).2
      · exact hTN ht0
    · ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        split_ifs
        · exact (T.equivFin.symm _).2
        · exact ht0
      · intro ha
        have hlt := (T.equivFin ⟨a, ha⟩).2
        refine ⟨⟨(T.equivFin ⟨a, ha⟩).val, by omega⟩, ?_⟩
        simp
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin (d - 1) ↦ N).card := Finset.card_image_le
    _ = N.card ^ (d - 1) := by simp [Fintype.card_piFinset]
    _ ≤ N.card ^ d := Nat.pow_le_pow_right hpos (Nat.sub_le d 1)

/-- If `V` contains the `ζ`-strong neighbours of `u`, then `|2 E_u - w̄ · z| ≤ 2 c ζ` for some
`c ≤ D^d`: the number of nonzero coefficients left out. -/
theorem abs_two_field_sub_score_le (R : RBM n m) {d D : ℕ} (hd : R.LatentDegreeLE d)
    (hD : R.DegreeLE D) {ζ : ℝ} {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V)
    (hstrong : R.strongNbhd ζ u ⊆ V) :
    ∃ c : ℕ, c ≤ D ^ d ∧ ∀ x, |2 * R.field u x - score V (wbar R u) x| ≤ 2 * c * ζ := by
  set bad := ((univ.filter (u ∈ ·)).filter (fun S ↦ ¬ S.erase u ⊆ V)).filter
    (fun S ↦ R.fourier S ≠ 0) with hbad
  have hmem : ∀ S ∈ bad, u ∈ S ∧ ¬ S.erase u ⊆ V ∧ R.fourier S ≠ 0 := by
    intro S hS
    simp only [hbad, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact ⟨hS.1.1, hS.1.2, hS.2⟩
  -- each left-out coefficient is small
  have hsmall : ∀ S ∈ bad, |R.fourier S| ≤ ζ := by
    intro S hS
    obtain ⟨huS, hV, -⟩ := hmem S hS
    obtain ⟨j, hj, hjV⟩ := Finset.not_subset.1 hV
    by_contra hlt
    apply hjV
    apply hstrong
    simp only [RBM.strongNbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.ne_of_mem_erase hj, S, huS, Finset.mem_of_mem_erase hj, (not_le.1 hlt).le⟩
  -- and there are at most `D^d` of them
  have hcard : bad.card ≤ D ^ d := by
    have hinj : Set.InjOn (fun S ↦ S.erase u) (bad : Set (Finset (Fin n))) := by
      intro S hS S' hS' h
      have h1 := (hmem S hS).1
      have h2 := (hmem S' hS').1
      rw [← Finset.insert_erase h1, ← Finset.insert_erase h2]
      exact congrArg (insert u) h
    rw [← Finset.card_image_of_injOn hinj]
    refine le_trans (Finset.card_le_card ?_) ((card_small_subsets_le (R.nbhd u) d).trans
      (Nat.pow_le_pow_left (hD u) d))
    intro T hT
    simp only [Finset.mem_image] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    obtain ⟨huS, hV, hf⟩ := hmem S hS
    have hne : (S.erase u).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      exact hV (h ▸ Finset.empty_subset V)
    have hcardS : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one huS
    have h2 : 2 ≤ S.card := by
      have := hne.card_pos
      omega
    have hSd := R.card_le_of_fourier_ne_zero hd S h2 hf
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun i hi ↦ ?_, hne, by omega⟩
    simp only [RBM.nbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.ne_of_mem_erase hi, S, huS, Finset.mem_of_mem_erase hi, hf⟩
  refine ⟨bad.card, hcard, fun x ↦ ?_⟩
  rw [two_field_sub_score R hu x, abs_mul, abs_two]
  have hsum : ∑ S ∈ (univ.filter (u ∈ ·)).filter (fun S ↦ ¬ S.erase u ⊆ V),
      R.fourier S * chi (S.erase u) x = ∑ S ∈ bad, R.fourier S * chi (S.erase u) x := by
    rw [hbad]
    exact (Finset.sum_filter_of_ne fun S _ h ↦ left_ne_zero_of_mul h).symm
  rw [hsum, mul_assoc]
  gcongr
  calc |∑ S ∈ bad, R.fourier S * chi (S.erase u) x|
      ≤ ∑ S ∈ bad, |R.fourier S * chi (S.erase u) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ bad, ζ := Finset.sum_le_sum fun S hS ↦ by
        rw [abs_mul, abs_chi, mul_one]
        exact hsmall S hS
    _ = bad.card * ζ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Under the hypothesis on `ζ` of [BB20, Theorem 12], `(2 E_u - w̄ · z)² ≤ 4 ε`. -/
theorem sq_two_field_sub_score_le (R : RBM n m) {γ : ℝ} {d D : ℕ} (hd : R.LatentDegreeLE d)
    (hD : R.DegreeLE D) {ζ ε : ℝ} (hζ0 : 0 < ζ) (hε : 0 < ε)
    (hζ : ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))))
    {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V) (hstrong : R.strongNbhd ζ u ⊆ V)
    (x : Config n) : (2 * R.field u x - score V (wbar R u) x) ^ 2 ≤ 4 * ε := by
  obtain ⟨c, hc, hx⟩ := abs_two_field_sub_score_le R hd hD hu hstrong
  have hcζ : (c : ℝ) * ζ ≤ Real.sqrt ε := by
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul]
      exact Real.sqrt_nonneg _
    have hDd : (0 : ℝ) < (D : ℝ) ^ d := by
      have : 0 < D ^ d := lt_of_lt_of_le hpos hc
      exact_mod_cast this
    have hs1 : 1 ≤ Real.sqrt (1 + Real.exp (2 * γ)) := by
      rw [Real.one_le_sqrt]
      linarith [Real.exp_pos (2 * γ)]
    have hcD : (c : ℝ) ≤ (D : ℝ) ^ d := by exact_mod_cast hc
    have h1 : ζ * ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))) ≤ Real.sqrt ε :=
      (le_div_iff₀ (by positivity)).1 hζ
    calc (c : ℝ) * ζ ≤ (D : ℝ) ^ d * ζ := mul_le_mul_of_nonneg_right hcD hζ0.le
      _ ≤ (D : ℝ) ^ d * ζ * Real.sqrt (1 + Real.exp (2 * γ)) :=
          le_mul_of_one_le_right (by positivity) hs1
      _ = ζ * ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))) := by ring
      _ ≤ Real.sqrt ε := h1
  have h1 : |2 * R.field u x - score V (wbar R u) x| ≤ 2 * Real.sqrt ε := by
    calc _ ≤ 2 * c * ζ := hx x
      _ = 2 * (c * ζ) := by ring
      _ ≤ 2 * Real.sqrt ε := by linarith
  calc (2 * R.field u x - score V (wbar R u) x) ^ 2
      = |2 * R.field u x - score V (wbar R u) x| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * Real.sqrt ε) ^ 2 := by gcongr
    _ = 4 * ε := by rw [mul_pow, Real.sq_sqrt hε.le]; ring

/-- The excess risk of `w̄` is at most `ε / 2`. -/
theorem popRisk_wbar_sub_le (R : RBM n m) {γ : ℝ} {d D : ℕ} (hd : R.LatentDegreeLE d)
    (hD : R.DegreeLE D) {ζ ε : ℝ} (hζ0 : 0 < ζ) (hε : 0 < ε)
    (hζ : ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))))
    {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V) (hstrong : R.strongNbhd ζ u ⊆ V) :
    popRisk R u V (wbar R u) - optRisk R u ≤ ε / 2 := by
  rw [popRisk_eq R hu, optRisk, ← Finset.sum_sub_distrib]
  calc ∑ x, (R.obsProb x * condRisk (R.condProb u x) (score V (wbar R u) x) -
        R.obsProb x * condRisk (R.condProb u x) (2 * R.field u x))
      ≤ ∑ x, R.obsProb x * (ε / 2) := Finset.sum_le_sum fun x _ ↦ by
        rw [← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (R.obsProb_pos x).le
        rw [R.condProb_eq, sigmoid_eq]
        have h1 := condRisk_sub_le (2 * R.field u x) (score V (wbar R u) x)
        have h2 := sq_two_field_sub_score_le R hd hD hζ0 hε hζ hu hstrong x
        have h3 : (score V (wbar R u) x - 2 * R.field u x) ^ 2 =
            (2 * R.field u x - score V (wbar R u) x) ^ 2 := by ring
        linarith
    _ = ε / 2 := by rw [← Finset.sum_mul, R.sum_obsProb, one_mul]

/-- **The deterministic step**: if `L(w) ≤ L̂(w) + ε/8` on the ball and `L̂(w̄) ≤ L(w̄) + ε/8`, then
every near-minimizer has prediction error at most `ε`. -/
theorem predError_le_of_dev (R : RBM n m) {γ : ℝ} (hW : R.WidthLE γ) {d D : ℕ}
    (hd : R.LatentDegreeLE d) (hD : R.DegreeLE D) {ζ ε : ℝ} (hζ0 : 0 < ζ) (hε : 0 < ε)
    (hζ : ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))))
    {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V) (hstrong : R.strongNbhd ζ u ⊆ V) {M : ℕ}
    (X : Fin M → Config n)
    (h1 : ∀ w, l1Norm V w ≤ 2 * γ → popRisk R u V w ≤ empRisk u V X w + ε / 8)
    (h2 : empRisk u V X (wbar R u) ≤ popRisk R u V (wbar R u) + ε / 8)
    (w : Finset (Fin n) → ℝ) (hw : IsNearMinimizer γ (ε / 4) u V X w) :
    R.predError u V w ≤ ε := by
  have hgap := popRisk_wbar_sub_le R hd hD hζ0 hε hζ hu hstrong
  have hpe := predError_le R hu w
  have hw1 := h1 w hw.1
  have hw2 := hw.2 (wbar R u) (l1Norm_wbar_le R hW hu)
  linarith

end BB20.Prediction
