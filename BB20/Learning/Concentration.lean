module

public import BB20.Learning.Progress
public import BB20.Learning.Link
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Concentration of the empirical marginals, and the accuracy of the empirical proxy

* `BB20.Learning.sampleProb_abs_ge_le`: Hoeffding's inequality for the empirical frequency of an
  event over independent samples, `P(|P̂(E) - P(E)| ≥ σ) ≤ 2 e^{-2Mσ²}`, from Hoeffding's lemma
  (Mathlib's, for a Bernoulli variable) and the product form of `BB20.RBM.sampleProb`.
* `BB20.Learning.good_prob`: with a union bound over the at most `K (2n)^K` events
  `X_T = z_T` with `1 ≤ |T| ≤ K`, all empirical marginals on at most `K` variables are within `σ`
  with probability at least `1 - ω` once `2Mσ² ≥ log 2 + log K + K log(2n) + log(1/ω)`.
* `BB20.Learning.abs_empNu_sub_nu_le`: then `|ν̂_{u,I|S} - ν_{u,I|S}| ≤ 4 · 2^{|S|} σ`, with no
  lower bound on the probabilities (`BB20.Learning.pattern_bound`).
-/

@[expose] public section

namespace BB20.Learning

open Finset MeasureTheory ProbabilityTheory

/-- Hoeffding's lemma for a Bernoulli variable: `p e^{t(1-p)} + (1-p) e^{-tp} ≤ e^{t²/8}`. -/
theorem bernoulli_mgf_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (t * -p) ≤ Real.exp (t ^ 2 / 8) := by
  let q : PMF Bool := PMF.ofFintype
    (fun b ↦ if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) (by
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add hp0 (sub_nonneg.2 hp1)]
      simp)
  let X : Bool → ℝ := fun b ↦ if b then 1 - p else -p
  have hq : ∀ b, (q b).toReal = if b then p else 1 - p := by
    intro b
    cases b <;> simp [q, PMF.ofFintype_apply, ENNReal.toReal_ofReal hp0,
      ENNReal.toReal_ofReal (sub_nonneg.2 hp1)]
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂q.toMeasure = p * f true + (1 - p) * f false := by
    intro f
    rw [PMF.integral_eq_sum, Fintype.sum_bool, hq, hq]
    simp
  have hm : AEMeasurable X q.toMeasure := (Measurable.of_discrete).aemeasurable
  have hb : ∀ᵐ b ∂q.toMeasure, X b ∈ Set.Icc (-p) (1 - p) := by
    refine ae_of_all _ fun b ↦ ?_
    cases b <;> simp [X]
  have hc : ∫ b, X b ∂q.toMeasure = 0 := by
    rw [hint]
    simp [X]
    ring
  have h := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le t
  rw [mgf, hint] at h
  have e1 : X true = 1 - p := rfl
  have e2 : X false = -p := rfl
  have e3 : (1 : ℝ) - p - -p = 1 := by ring
  rw [e1, e2, e3, nnnorm_one] at h
  refine h.trans_eq ?_
  congr 1
  push_cast
  ring

variable {n m : ℕ} (R : RBM n m)

/-! ### Probabilities of events over the samples -/

theorem sampleProb_nonneg (M : ℕ) (Q : (Fin M → Config n) → Prop) : 0 ≤ R.sampleProb M Q := by
  classical
  refine sum_nonneg fun X _ ↦ ?_
  split_ifs
  · exact prod_nonneg fun k _ ↦ (R.obsProb_pos _).le
  · exact le_rfl

theorem sampleProb_mono (M : ℕ) {Q Q' : (Fin M → Config n) → Prop} (h : ∀ X, Q X → Q' X) :
    R.sampleProb M Q ≤ R.sampleProb M Q' := by
  classical
  refine sum_le_sum fun X _ ↦ ?_
  by_cases hQ : Q X
  · rw [ite_eq_left hQ, ite_eq_left (h X hQ)]
  · rw [ite_eq_right hQ]
    split_ifs
    · exact prod_nonneg fun k _ ↦ (R.obsProb_pos _).le
    · exact le_rfl

theorem sum_prod_obsProb (M : ℕ) : ∑ X : Fin M → Config n, ∏ k, R.obsProb (X k) = 1 := by
  rw [← Fintype.prod_sum (fun _ x ↦ R.obsProb x)]
  simp [R.sum_obsProb]

theorem sampleProb_eq_one_sub (M : ℕ) (Q : (Fin M → Config n) → Prop) :
    R.sampleProb M Q = 1 - R.sampleProb M fun X ↦ ¬ Q X := by
  classical
  rw [eq_sub_iff_add_eq, ← sum_prod_obsProb R M]
  unfold RBM.sampleProb
  rw [← sum_add_distrib]
  refine sum_congr rfl fun X _ ↦ ?_
  by_cases hQ : Q X <;> simp [hQ]

theorem sampleProb_or (M : ℕ) (Q₁ Q₂ : (Fin M → Config n) → Prop) :
    R.sampleProb M (fun X ↦ Q₁ X ∨ Q₂ X) ≤ R.sampleProb M Q₁ + R.sampleProb M Q₂ := by
  classical
  unfold RBM.sampleProb
  rw [← sum_add_distrib]
  refine sum_le_sum fun X _ ↦ ?_
  have hp : 0 ≤ ∏ k, R.obsProb (X k) := prod_nonneg fun k _ ↦ (R.obsProb_pos _).le
  by_cases h₁ : Q₁ X <;> by_cases h₂ : Q₂ X <;> simp [h₁, h₂, hp]

/-- The union bound. -/
theorem sampleProb_exists_le {ι : Type*} (M : ℕ) (J : Finset ι)
    (Q : ι → (Fin M → Config n) → Prop) :
    R.sampleProb M (fun X ↦ ∃ j ∈ J, Q j X) ≤ ∑ j ∈ J, R.sampleProb M (Q j) := by
  classical
  unfold RBM.sampleProb
  rw [sum_comm]
  refine sum_le_sum fun X _ ↦ ?_
  have hp : 0 ≤ ∏ k, R.obsProb (X k) := prod_nonneg fun k _ ↦ (R.obsProb_pos _).le
  split_ifs with h
  · obtain ⟨j, hj, hQ⟩ := h
    calc ∏ k, R.obsProb (X k) = if Q j X then ∏ k, R.obsProb (X k) else 0 := by simp [hQ]
      _ ≤ ∑ j ∈ J, if Q j X then ∏ k, R.obsProb (X k) else 0 :=
        single_le_sum (f := fun j ↦ if Q j X then ∏ k, R.obsProb (X k) else 0)
          (fun j _ ↦ by split_ifs <;> simp [hp]) hj
  · exact sum_nonneg fun j _ ↦ by split_ifs <;> simp [hp]

/-! ### Hoeffding's inequality for empirical frequencies -/

/-- The moment generating function of a centred indicator. -/
theorem sum_obsProb_mul_exp (E : Config n → Prop) [DecidablePred E] (t : ℝ) :
    ∑ x, R.obsProb x * Real.exp (t * ((if E x then 1 else 0) -
        ∑ y, if E y then R.obsProb y else 0)) ≤ Real.exp (t ^ 2 / 8) := by
  obtain ⟨p, hp⟩ : ∃ p, p = ∑ y, if E y then R.obsProb y else 0 := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 ≤ p := hp ▸ sum_nonneg fun y _ ↦ by split_ifs <;> simp [(R.obsProb_pos y).le]
  have hq : ∑ y, (if E y then 0 else R.obsProb y) = 1 - p := by
    rw [hp, eq_sub_iff_add_eq, ← sum_add_distrib, ← R.sum_obsProb]
    refine sum_congr rfl fun y _ ↦ ?_
    split_ifs <;> simp
  have hp1 : p ≤ 1 := by
    have : 0 ≤ ∑ y, (if E y then 0 else R.obsProb y) :=
      sum_nonneg fun y _ ↦ by split_ifs <;> simp [(R.obsProb_pos y).le]
    linarith
  have hpt : ∀ y, R.obsProb y * Real.exp (t * ((if E y then 1 else 0) - p)) =
      (if E y then R.obsProb y else 0) * Real.exp (t * (1 - p)) +
        (if E y then 0 else R.obsProb y) * Real.exp (t * -p) := by
    intro y
    split_ifs <;> simp
  rw [sum_congr rfl fun y _ ↦ hpt y, sum_add_distrib, ← sum_mul, ← sum_mul, hq, ← hp]
  exact bernoulli_mgf_le hp0 hp1 t

/-- **Hoeffding's inequality** for the empirical frequency of an event (one side, `s = ±1`). -/
theorem sampleProb_freq_ge (M : ℕ) (E : Config n → Prop) [DecidablePred E] {s : ℝ}
    (hs : s * s = 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    R.sampleProb M (fun X ↦ M * σ ≤ s * ∑ k, ((if E (X k) then 1 else 0) -
        ∑ y, if E y then R.obsProb y else 0)) ≤ Real.exp (-2 * M * σ ^ 2) := by
  classical
  set p := ∑ y, if E y then R.obsProb y else 0 with hp
  set Y : Config n → ℝ := fun x ↦ s * ((if E x then 1 else 0) - p) with hY
  set lam := 4 * σ with hlam
  have hlam0 : 0 ≤ lam := by positivity
  -- Markov's inequality for `exp(lam (∑ Y - Mσ))`
  have hpt : ∀ X : Fin M → Config n,
      (if (M : ℝ) * σ ≤ s * ∑ k, ((if E (X k) then 1 else 0) - p) then ∏ k, R.obsProb (X k)
        else 0) ≤
      Real.exp (-(lam * (M * σ))) * ∏ k, (R.obsProb (X k) * Real.exp (lam * Y (X k))) := by
    intro X
    have hprod : ∏ k, (R.obsProb (X k) * Real.exp (lam * Y (X k))) =
        (∏ k, R.obsProb (X k)) * Real.exp (lam * ∑ k, Y (X k)) := by
      rw [prod_mul_distrib, mul_sum, Real.exp_sum]
    rw [hprod, ← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    have hp0 : 0 ≤ ∏ k, R.obsProb (X k) := prod_nonneg fun k _ ↦ (R.obsProb_pos _).le
    split_ifs with h
    · refine le_mul_of_one_le_right hp0 (Real.one_le_exp ?_)
      have : ∑ k, Y (X k) = s * ∑ k, ((if E (X k) then 1 else 0) - p) := by
        rw [hY, mul_sum]
      rw [this]
      nlinarith
    · exact mul_nonneg hp0 (Real.exp_pos _).le
  calc R.sampleProb M _ ≤ ∑ X : Fin M → Config n,
        Real.exp (-(lam * (M * σ))) * ∏ k, (R.obsProb (X k) * Real.exp (lam * Y (X k))) :=
        sum_le_sum fun X _ ↦ hpt X
    _ = Real.exp (-(lam * (M * σ))) *
          (∑ x, R.obsProb x * Real.exp (lam * Y x)) ^ M := by
        rw [← mul_sum, ← Fintype.prod_sum (fun _ x ↦ R.obsProb x * Real.exp (lam * Y x)),
          prod_const, card_univ, Fintype.card_fin]
    _ ≤ Real.exp (-(lam * (M * σ))) * Real.exp ((lam * s) ^ 2 / 8) ^ M := by
        gcongr
        · exact sum_nonneg fun x _ ↦ mul_nonneg (R.obsProb_pos x).le (Real.exp_pos _).le
        · have := sum_obsProb_mul_exp R E (lam * s)
          simp only [hY, ← hp] at this ⊢
          simpa only [mul_assoc] using this
    _ = Real.exp (-2 * M * σ ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        have : (lam * s) ^ 2 = lam ^ 2 := by rw [mul_pow, sq s, hs, mul_one]
        rw [this, hlam]
        ring

theorem card_filter_eq_mul_empMarg {M : ℕ} (hM : 1 ≤ M) (X : Fin M → Config n)
    (T : Finset (Fin n)) (z : Config n) :
    ∑ k, ((if ∀ i ∈ T, X k i = z i then (1 : ℝ) else 0)) = M * empMarg X T z := by
  rw [sum_boole, empMarg]
  have : (M : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Hoeffding's inequality** for an empirical marginal: `P(|P̂(z_T) - P(z_T)| ≥ σ) ≤
2 e^{-2Mσ²}`. -/
theorem sampleProb_abs_ge_le {M : ℕ} (hM : 1 ≤ M) (T : Finset (Fin n)) (z : Config n) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    R.sampleProb M (fun X ↦ σ ≤ |empMarg X T z - R.marg T z|) ≤
      2 * Real.exp (-2 * M * σ ^ 2) := by
  set E : Config n → Prop := fun x ↦ ∀ i ∈ T, x i = z i with hE
  have hmarg : R.marg T z = ∑ y, if E y then R.obsProb y else 0 := rfl
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : ∀ X : Fin M → Config n, ∑ k, ((if E (X k) then 1 else 0) - R.marg T z) =
      M * (empMarg X T z - R.marg T z) := by
    intro X
    rw [sum_sub_distrib, card_filter_eq_mul_empMarg hM X T z, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  calc R.sampleProb M (fun X ↦ σ ≤ |empMarg X T z - R.marg T z|)
      ≤ R.sampleProb M (fun X ↦ (M * σ ≤ 1 * ∑ k, ((if E (X k) then 1 else 0) -
          ∑ y, if E y then R.obsProb y else 0)) ∨
          (M * σ ≤ (-1) * ∑ k, ((if E (X k) then 1 else 0) -
          ∑ y, if E y then R.obsProb y else 0))) := by
        refine sampleProb_mono R M fun X h ↦ ?_
        rw [← hmarg, hsum X]
        rcases le_abs'.1 h with h' | h'
        · right
          nlinarith
        · left
          nlinarith
    _ ≤ _ := sampleProb_or R M _ _
    _ ≤ Real.exp (-2 * M * σ ^ 2) + Real.exp (-2 * M * σ ^ 2) := by
        gcongr
        · exact sampleProb_freq_ge R M E (by norm_num) hσ
        · exact sampleProb_freq_ge R M E (by norm_num) hσ
    _ = 2 * Real.exp (-2 * M * σ ^ 2) := by ring

/-! ### The union bound over marginals -/

/-- There are at most `K (2n)^K` pairs `(T, z_T)` with `1 ≤ |T| ≤ K`. -/
theorem sum_two_pow_card_le (n K : ℕ) (hn : 1 ≤ n) :
    ∑ T ∈ univ.filter (fun T : Finset (Fin n) ↦ T.card ≤ K ∧ T.Nonempty), (2 : ℝ) ^ T.card ≤
      K * (2 * n) ^ K := by
  set 𝒯 := univ.filter (fun T : Finset (Fin n) ↦ T.card ≤ K ∧ T.Nonempty)
  have hmaps : ∀ T ∈ 𝒯, T.card ∈ Icc 1 K := by
    intro T hT
    obtain ⟨hK, hne⟩ := (mem_filter.1 hT).2
    exact mem_Icc.2 ⟨hne.card_pos, hK⟩
  have h2n : (1 : ℝ) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ j ∈ Icc 1 K, ∑ T ∈ 𝒯 with T.card = j, (2 : ℝ) ^ T.card
      ≤ ∑ j ∈ Icc 1 K, (2 * n : ℝ) ^ K := by
        refine sum_le_sum fun j hj ↦ ?_
        have hsum : ∑ T ∈ 𝒯 with T.card = j, (2 : ℝ) ^ T.card =
            (𝒯.filter (·.card = j)).card * 2 ^ j := by
          rw [sum_congr rfl fun T hT ↦ by rw [(mem_filter.1 hT).2], sum_const, nsmul_eq_mul]
        rw [hsum]
        have hc : (𝒯.filter (·.card = j)).card ≤ n.choose j := by
          calc (𝒯.filter (·.card = j)).card ≤ (powersetCard j (univ : Finset (Fin n))).card :=
                card_le_card fun T hT ↦ mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hT).2⟩
            _ = n.choose j := by simp [card_powersetCard]
        have hc2 : ((𝒯.filter (·.card = j)).card : ℝ) ≤ (n : ℝ) ^ j := by
          calc ((𝒯.filter (·.card = j)).card : ℝ) ≤ (n.choose j : ℕ) := by exact_mod_cast hc
            _ ≤ ((n ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_pow n j
            _ = (n : ℝ) ^ j := by push_cast; ring
        calc ((𝒯.filter (·.card = j)).card : ℝ) * 2 ^ j ≤ (n : ℝ) ^ j * 2 ^ j := by gcongr
          _ = (2 * n : ℝ) ^ j := by ring
          _ ≤ (2 * n : ℝ) ^ K := pow_le_pow_right₀ h2n (mem_Icc.1 hj).2
    _ = K * (2 * n) ^ K := by simp [sum_const, Nat.card_Icc]

theorem empMarg_empty {M : ℕ} (hM : 1 ≤ M) (X : Fin M → Config n) (z : Config n) :
    empMarg X ∅ z = 1 := by
  have : (M : ℝ) ≠ 0 := by positivity
  simp [empMarg, this]

theorem empMarg_congr {M : ℕ} (X : Fin M → Config n) (T : Finset (Fin n)) {z z' : Config n}
    (h : ∀ i ∈ T, z i = z' i) : empMarg X T z = empMarg X T z' := by
  unfold empMarg
  congr 3
  ext k
  simp only [mem_filter, mem_univ, true_and]
  exact forall₂_congr fun i hi ↦ by rw [h i hi]

/-- **The good event**: all empirical marginals on at most `K` variables are within `σ` of the
true ones, with probability at least `1 - ω` once `2Mσ² ≥ log 2 + log K + K log(2n) + log(1/ω)`.
-/
theorem good_prob {M K : ℕ} {σ ω : ℝ} (hM : 1 ≤ M) (hn : 1 ≤ n) (hσ : 0 < σ) (hK : 1 ≤ K)
    (hω : 0 < ω)
    (hMσ : Real.log 2 + Real.log K + K * Real.log (2 * n) + Real.log (1 / ω) ≤
      2 * M * σ ^ 2) :
    1 - ω ≤ R.sampleProb M fun X ↦
      ∀ T : Finset (Fin n), T.card ≤ K → ∀ z, |empMarg X T z - R.marg T z| < σ := by
  classical
  set 𝒯 := univ.filter (fun T : Finset (Fin n) ↦ T.card ≤ K ∧ T.Nonempty)
  set reps : Finset (Fin n) → Finset (Config n) := fun T ↦
    univ.filter fun z : Config n ↦ ∀ i ∈ Tᶜ, false = z i
  have hreps : ∀ T, (reps T).card = 2 ^ T.card := by
    intro T
    rw [card_agree, card_compl, Fintype.card_fin]
    congr 1
    have := card_le_univ T
    simp only [Fintype.card_fin] at this
    omega
  -- the bad event is covered by the union over `𝒯` and representatives
  have hbad : R.sampleProb M (fun X ↦ ¬ ∀ T : Finset (Fin n), T.card ≤ K →
      ∀ z, |empMarg X T z - R.marg T z| < σ) ≤
      ∑ T ∈ 𝒯, ∑ z ∈ reps T, R.sampleProb M (fun X ↦ σ ≤ |empMarg X T z - R.marg T z|) := by
    calc _ ≤ R.sampleProb M (fun X ↦ ∃ T ∈ 𝒯, ∃ z ∈ reps T,
          σ ≤ |empMarg X T z - R.marg T z|) := by
          refine sampleProb_mono R M fun X h ↦ ?_
          push Not at h
          obtain ⟨T, hTK, z, hz⟩ := h
          have hne : T.Nonempty := by
            rw [nonempty_iff_ne_empty]
            rintro rfl
            rw [empMarg_empty hM, R.marg_empty, sub_self, abs_zero] at hz
            linarith
          refine ⟨T, mem_filter.2 ⟨mem_univ _, hTK, hne⟩,
            fun i ↦ if i ∈ T then z i else false, ?_, ?_⟩
          · simp only [reps, mem_filter, mem_univ, true_and, mem_compl]
            intro i hi
            simp [hi]
          · have hag : ∀ i ∈ T, z i = (fun i ↦ if i ∈ T then z i else false) i := by
              intro i hi
              simp [hi]
            rwa [← empMarg_congr X T hag, ← marg_congr R T hag]
      _ ≤ ∑ T ∈ 𝒯, R.sampleProb M (fun X ↦ ∃ z ∈ reps T,
          σ ≤ |empMarg X T z - R.marg T z|) := sampleProb_exists_le R M 𝒯 _
      _ ≤ _ := sum_le_sum fun T _ ↦ sampleProb_exists_le R M (reps T) _
  have hbound : ∑ T ∈ 𝒯, ∑ z ∈ reps T,
      R.sampleProb M (fun X ↦ σ ≤ |empMarg X T z - R.marg T z|) ≤
      2 * Real.exp (-2 * M * σ ^ 2) * (K * (2 * n) ^ K) := by
    calc _ ≤ ∑ T ∈ 𝒯, ∑ z ∈ reps T, 2 * Real.exp (-2 * M * σ ^ 2) :=
          sum_le_sum fun T _ ↦ sum_le_sum fun z _ ↦ sampleProb_abs_ge_le R hM T z hσ.le
      _ = 2 * Real.exp (-2 * M * σ ^ 2) * ∑ T ∈ 𝒯, (2 : ℝ) ^ T.card := by
          rw [mul_sum]
          refine sum_congr rfl fun T _ ↦ ?_
          rw [sum_const, hreps, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := by
          gcongr
          exact sum_two_pow_card_le n K hn
  have hfinal : 2 * Real.exp (-2 * M * σ ^ 2) * (K * (2 * n) ^ K) ≤ ω := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hn' : (0 : ℝ) < 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have heq : 2 * Real.exp (-2 * M * σ ^ 2) * (K * (2 * n) ^ K) =
        Real.exp (Real.log 2 + Real.log K + K * Real.log (2 * n) - 2 * M * σ ^ 2) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
        Real.exp_log hK', Real.exp_nat_mul, Real.exp_log hn',
        show -2 * (M : ℝ) * σ ^ 2 = -(2 * M * σ ^ 2) by ring, Real.exp_neg]
      field_simp
    rw [heq]
    calc Real.exp (Real.log 2 + Real.log K + K * Real.log (2 * n) - 2 * M * σ ^ 2)
        ≤ Real.exp (-Real.log (1 / ω)) := Real.exp_le_exp.2 (by linarith)
      _ = ω := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hω]
  rw [sampleProb_eq_one_sub R M]
  linarith

/-! ### From the marginals to the proxy -/

/-- One term of `ν` is stable under perturbations of the four marginals it involves, with no
lower bound on `P(z_S)`: with `p = P(z_S)`, `a = P(z_u, z_S)`, `b = P(z_I, z_S)`,
`c = P(z_u, z_I, z_S)` and empirical `q, a', b', c'` within `σ`,
`||c' - a' b'/q| - |c - a b/p|| ≤ 4σ`. -/
theorem pattern_bound {p a b c q a' b' c' σ : ℝ} (hp : 0 < p) (hb0 : 0 ≤ b) (hbp : b ≤ p)
    (hc0 : 0 ≤ c) (hca : c ≤ a) (hap : a ≤ p) (ha'0 : 0 ≤ a') (ha'q : a' ≤ q) (hb'0 : 0 ≤ b')
    (hb'q : b' ≤ q) (hc'0 : 0 ≤ c') (hc'a' : c' ≤ a') (hq : |q - p| ≤ σ) (ha : |a' - a| ≤ σ)
    (hb : |b' - b| ≤ σ) (hc : |c' - c| ≤ σ) :
    abs (|c' - a' * b' / q| - |c - a * b / p|) ≤ 4 * σ := by
  have hσ : 0 ≤ σ := (abs_nonneg _).trans hq
  have ha0 : 0 ≤ a := hc0.trans hca
  have habp0 : 0 ≤ a * b / p := div_nonneg (mul_nonneg ha0 hb0) hp.le
  have habp : a * b / p ≤ a := by
    rw [div_le_iff₀ hp]
    exact mul_le_mul_of_nonneg_left hbp ha0
  rcases (ha'0.trans ha'q).lt_or_eq with hq0 | hq0
  · refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    have key : (c' - a' * b' / q) - (c - a * b / p) =
        (c' - c) - a' / q * (b' - b) - b * (a' * (p - q) + q * (a' - a)) / (q * p) := by
      field_simp
      ring
    rw [key]
    have h1 : |a' / q * (b' - b)| ≤ σ := by
      rw [abs_mul, abs_of_nonneg (div_nonneg ha'0 hq0.le)]
      calc a' / q * |b' - b| ≤ 1 * σ :=
            mul_le_mul ((div_le_one hq0).2 ha'q) hb (abs_nonneg _) zero_le_one
        _ = σ := one_mul σ
    have h2 : |b * (a' * (p - q) + q * (a' - a)) / (q * p)| ≤ 2 * σ := by
      have hqp : 0 < q * p := mul_pos hq0 hp
      rw [abs_div, abs_mul, abs_of_nonneg hb0, abs_of_pos hqp, div_le_iff₀ hqp]
      have h3 : |a' * (p - q) + q * (a' - a)| ≤ a' * σ + q * σ := by
        calc |a' * (p - q) + q * (a' - a)| ≤ |a' * (p - q)| + |q * (a' - a)| := abs_add_le _ _
          _ = a' * |q - p| + q * |a' - a| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha'0, abs_of_nonneg hq0.le, abs_sub_comm p q]
          _ ≤ a' * σ + q * σ := by gcongr
      calc b * |a' * (p - q) + q * (a' - a)| ≤ b * (a' * σ + q * σ) :=
            mul_le_mul_of_nonneg_left h3 hb0
        _ ≤ 2 * σ * (q * p) := by
            have e1 : b * a' ≤ p * q := mul_le_mul hbp ha'q ha'0 hp.le
            have e2 : b * q ≤ p * q := mul_le_mul_of_nonneg_right hbp hq0.le
            nlinarith
    set A := a' / q * (b' - b)
    set B := b * (a' * (p - q) + q * (a' - a)) / (q * p)
    have := neg_abs_le (c' - c)
    have := le_abs_self (c' - c)
    have := neg_abs_le A
    have := le_abs_self A
    have := neg_abs_le B
    have := le_abs_self B
    rw [abs_le]
    constructor <;> linarith
  · subst hq0
    have ha' : a' = 0 := le_antisymm ha'q ha'0
    have hb' : b' = 0 := le_antisymm hb'q hb'0
    have hc' : c' = 0 := le_antisymm (hc'a'.trans ha'q) hc'0
    subst ha' hb' hc'
    simp only [sub_zero, mul_zero, zero_div, abs_zero, zero_sub, abs_neg, abs_abs]
    rw [zero_sub, abs_neg, abs_of_pos hp] at hq
    rw [abs_le]
    constructor <;> linarith

theorem empMarg_nonneg {M : ℕ} (X : Fin M → Config n) (T : Finset (Fin n)) (z : Config n) :
    0 ≤ empMarg X T z := by
  unfold empMarg
  positivity

theorem empMarg_mono {M : ℕ} (X : Fin M → Config n) {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (z : Config n) : empMarg X B z ≤ empMarg X A z := by
  unfold empMarg
  gcongr

/-- **Perturbation**: if the empirical marginals on the subsets of `{u} ∪ I ∪ S` are within `σ`,
then `|ν̂_{u,I|S} - ν_{u,I|S}| ≤ 4 · 2^{|S|} σ`. -/
theorem abs_empNu_sub_nu_le {M : ℕ} (X : Fin M → Config n) (u : Fin n) (I S : Finset (Fin n))
    {σ : ℝ} (h : ∀ T ⊆ insert u (I ∪ S), ∀ z, |empMarg X T z - R.marg T z| ≤ σ) :
    |empNu X u I S - R.nu u I S| ≤ 4 * 2 ^ S.card * σ := by
  have hterm : ∀ z, abs (|empMarg X (insert u (I ∪ S)) z -
      empMarg X (insert u S) z * empMarg X (I ∪ S) z / empMarg X S z| -
      |R.marg (insert u (I ∪ S)) z - R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z|)
      ≤ 4 * σ := by
    intro z
    have hS : S ⊆ insert u S := subset_insert u S
    have hIS : S ⊆ I ∪ S := subset_union_right
    have huS : insert u S ⊆ insert u (I ∪ S) := insert_subset_insert u subset_union_right
    have hIS' : I ∪ S ⊆ insert u (I ∪ S) := subset_insert u (I ∪ S)
    exact pattern_bound (marg_pos R S z) (R.marg_nonneg _ z) (marg_mono R hIS z)
      (R.marg_nonneg _ z) (marg_mono R huS z) (marg_mono R hS z) (empMarg_nonneg X _ z)
      (empMarg_mono X hS z) (empMarg_nonneg X _ z) (empMarg_mono X hIS z)
      (empMarg_nonneg X _ z) (empMarg_mono X huS z)
      (h S (hS.trans huS) z) (h _ huS z) (h _ hIS' z) (h _ subset_rfl z)
  have hcard : S.card ≤ n := (card_le_univ S).trans (by simp)
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - S.card) * 2 ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  have hpos : (0 : ℝ) < 2 ^ (n - S.card) := by positivity
  unfold empNu RBM.nu
  rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ z, _| ≤ ∑ z : Config n, (4 * σ) := (abs_sum_le_sum_abs _ _).trans (sum_le_sum
        fun z _ ↦ hterm z)
    _ = 2 ^ n * (4 * σ) := by simp [sum_const, card_univ]
    _ = 4 * 2 ^ S.card * σ * 2 ^ (n - S.card) := by rw [hpow]; ring

/-- On the good event, the algorithm's empirical proxy is accurate: within `4 · 2^L σ` of `ν` on
the sets with `|I| ≤ 2^s` and `|S| ≤ L`, if `K ≥ ⌊L⌋ + 2^s + 1`. -/
theorem accurate_of_good {M : ℕ} (X : Fin M → Config n) (u : Fin n) (s K : ℕ) {L σ : ℝ}
    (hσ : 0 ≤ σ) (hK : ⌊L⌋₊ + 2 ^ s + 1 ≤ K)
    (hgood : ∀ T : Finset (Fin n), T.card ≤ K → ∀ z, |empMarg X T z - R.marg T z| < σ) :
    Accurate R u (fun I S ↦ empNuL (sampleList X) n u I S) (2 ^ s) L
      (4 * (2 : ℝ) ^ L * σ) := by
  intro I S huI huS hIS hI hS
  rw [empNuL_eq]
  have hSL : S.card ≤ ⌊L⌋₊ := Nat.le_floor hS
  refine (abs_empNu_sub_nu_le R X u I S fun T hT z ↦ (hgood T ?_ z).le).trans ?_
  · calc T.card ≤ (insert u (I ∪ S)).card := card_le_card hT
      _ ≤ (I ∪ S).card + 1 := card_insert_le _ _
      _ ≤ I.card + S.card + 1 := by gcongr; exact card_union_le _ _
      _ ≤ K := by omega
  · have : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ L := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
    gcongr

end BB20.Learning
