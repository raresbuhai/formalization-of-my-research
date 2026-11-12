module

public import BDT24.Model

/-!
# The exchangeability argument [BDT24, Lemma 4.1]

Let `Y₀, …, Y_M` be independent with law `μ`, and let a paired test `D(y, y', r)` with coins `r`
be run on every ordered pair `(a, b)` with its own independent coins `r_{ab}`. The events `Eₐ`
that `Yₐ` wins against every other, `D(Yₐ, Y_b, r_{ab})` and `¬D(Y_b, Yₐ, r_{ba})` for all
`b ≠ a`, are pairwise disjoint (`Eₐ` and `E_b` disagree on `D(Yₐ, Y_b, r_{ab})`) and have the same
probability (permute the indices). So `P(E₀) ≤ 1/(M+1)`. Integrating out `Y₁, …, Y_M` and the
coins of the pairs not involving `0`, this is `BDT24.Prob.exch`: with
`p(y) = E_{y'} [P_r(D(y, y', r)) P_r(¬D(y', y, r))]`, `E_y [p(y)^M] ≤ 1/(M+1)`.

The formal proof conditions on the points `y : Fin (M+1) → X`: given them, the coin tables
`r : Fin (M+1) → Fin (M+1) → (Fin L → Bool)` are uniform, `Eₐ` is a box of coin tables
(`BDT24.Prob.X.event`) of probability `allWin y a = ∏_{b ≠ a} P(D(y a, y b, ·)) P(¬D(y b, y a, ·))`,
and the boxes are pairwise disjoint, so `∑ₐ allWin y a ≤ 1`. Permuting the indices shows that
`E_y [allWin y a]` does not depend on `a`, and Fubini identifies `E_y [allWin y 0]` with
`E_y [p(y)^M]`.
-/

@[expose] public section

namespace BDT24.Prob

open MeasureTheory ProbabilityTheory

namespace X

variable {X : Type*} (L : ℕ) (D : X → X → List Bool → Bool)

/-! ### The coins, given the points -/

/-- The coin strings `r` of length `L` with `D(u, v, r) = w`. -/
def coins (u v : X) (w : Bool) : Finset (Fin L → Bool) :=
  Finset.univ.filter fun r ↦ D u v (List.ofFn r) = w

/-- `coinProb` is the proportion of coin strings in `coins`. -/
theorem coinProb_eq (u v : X) (w : Bool) :
    coinProb L (fun r ↦ D u v r = w) = ((coins L D u v w).card : ℝ) / 2 ^ L := by
  unfold coinProb coins
  rw [Fintype.card_subtype]

/-- A coin probability lies in `[0, 1]`. -/
theorem coinProb_mem (u v : X) (w : Bool) :
    0 ≤ coinProb L (fun r ↦ D u v r = w) ∧ coinProb L (fun r ↦ D u v r = w) ≤ 1 := by
  rw [coinProb_eq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  have h := Finset.card_le_univ (coins L D u v w)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- The probability `P_r(D(u, v, r)) · P_r(¬D(v, u, r))` that `u` beats `v` when the test runs
both ways with independent coins. -/
noncomputable def win (u v : X) : ℝ :=
  coinProb L (fun r ↦ D u v r = true) * coinProb L (fun r ↦ D v u r = false)

/-- `win` lies in `[0, 1]`. -/
theorem win_mem (u v : X) : 0 ≤ win L D u v ∧ win L D u v ≤ 1 := by
  obtain ⟨h1, h2⟩ := coinProb_mem L D u v true
  obtain ⟨h3, h4⟩ := coinProb_mem L D v u false
  exact ⟨mul_nonneg h1 h3, by rw [win]; nlinarith⟩

/-- The probability, given the points `y`, of the event `Eₐ` that `y a` beats every other
point. -/
noncomputable def allWin {N : ℕ} (y : Fin N → X) (a : Fin N) : ℝ :=
  ∏ b, if b = a then 1 else win L D (y a) (y b)

/-- `allWin` lies in `[0, 1]`. -/
theorem allWin_mem {N : ℕ} (y : Fin N → X) (a : Fin N) :
    0 ≤ allWin L D y a ∧ allWin L D y a ≤ 1 := by
  refine ⟨Finset.prod_nonneg fun b _ ↦ ?_, Finset.prod_le_one₀ (fun b _ ↦ ?_) fun b _ ↦ ?_⟩
  · split_ifs
    exacts [zero_le_one, (win_mem L D _ _).1]
  · split_ifs
    exacts [zero_le_one, (win_mem L D _ _).1]
  · split_ifs
    exacts [le_rfl, (win_mem L D _ _).2]

/-- The allowed coins `r c d` of the test on `(y c, y d)` in the event `Eₐ`. -/
def box {N : ℕ} (y : Fin N → X) (a c d : Fin N) : Finset (Fin L → Bool) :=
  if c = a then (if d = a then Finset.univ else coins L D (y a) (y d) true)
  else if d = a then coins L D (y c) (y a) false else Finset.univ

/-- The event `Eₐ`, as a set of coin tables `r` (`r c d` the coins of the test on `(y c, y d)`):
`D(y a, y b, r a b)` and `¬D(y b, y a, r b a)` for all `b ≠ a`. -/
def event {N : ℕ} (y : Fin N → X) (a : Fin N) : Finset (Fin N → Fin N → Fin L → Bool) :=
  Fintype.piFinset fun c ↦ Fintype.piFinset fun d ↦ box L D y a c d

/-- The events `Eₐ` are pairwise disjoint: `Eₐ` and `E_b` disagree on `D(y a, y b, r a b)`. -/
theorem event_disjoint {N : ℕ} (y : Fin N → X) {a a' : Fin N} (h : a ≠ a') :
    Disjoint (event L D y a) (event L D y a') := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  simp only [event, Fintype.mem_piFinset] at hr hr'
  have h1 := hr a a'
  have h2 := hr' a a'
  simp [box, h, h.symm, coins] at h1 h2
  simp [h1] at h2

/-- The proportion of coins in a box entry. -/
theorem card_box {N : ℕ} (y : Fin N → X) (a c d : Fin N) :
    ((box L D y a c d).card : ℝ) / 2 ^ L =
      (if c = a ∧ d ≠ a then coinProb L (fun r ↦ D (y a) (y d) r = true) else 1) *
      (if d = a ∧ c ≠ a then coinProb L (fun r ↦ D (y c) (y a) r = false) else 1) := by
  by_cases hc : c = a <;> by_cases hd : d = a <;> simp [box, hc, hd, coinProb_eq]

/-- The probability of `Eₐ` is `allWin`: the coins of distinct ordered pairs are independent. -/
theorem card_event {N : ℕ} (y : Fin N → X) (a : Fin N) :
    ((event L D y a).card : ℝ) / (((2 : ℝ) ^ L) ^ N) ^ N = allWin L D y a := by
  have h2 : (((2 : ℝ) ^ L) ^ N) ^ N = ∏ _c : Fin N, ∏ _d : Fin N, (2 : ℝ) ^ L := by
    simp [Finset.prod_const]
  rw [event, Fintype.card_piFinset, Nat.cast_prod, h2, ← Finset.prod_div_distrib]
  simp_rw [Fintype.card_piFinset, Nat.cast_prod, ← Finset.prod_div_distrib, card_box,
    Finset.prod_mul_distrib]
  simp only [ite_and, Finset.prod_ite_irrel, Finset.prod_const_one, Finset.prod_ite_eq',
    Finset.mem_univ, ite_true]
  rw [allWin, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  by_cases hb : b = a <;> simp [hb, win]

/-- The events `Eₐ` are disjoint, so their probabilities sum to at most `1`. -/
theorem sum_allWin_le {N : ℕ} (y : Fin N → X) : ∑ a, allWin L D y a ≤ 1 := by
  simp_rw [← card_event, ← Finset.sum_div, ← Nat.cast_sum]
  rw [div_le_one (by positivity),
    ← Finset.card_biUnion fun a _ a' _ h ↦ event_disjoint L D y h]
  have h := Finset.card_le_univ (Finset.univ.biUnion (event L D y))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- Relabelling the points by `σ` relabels the winner. -/
theorem allWin_perm {N : ℕ} (y : Fin N → X) (σ : Equiv.Perm (Fin N)) (a : Fin N) :
    allWin L D (fun k ↦ y (σ k)) a = allWin L D y (σ a) := by
  unfold allWin
  exact Fintype.prod_equiv σ _ _ fun b ↦ by simp [σ.apply_eq_iff_eq]

/-! ### Integrating over the points -/

variable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- On a countable space with measurable singletons, a bounded function is integrable. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (ν : Measure α) [IsFiniteMeasure ν] (f : α → ℝ) (C : ℝ)
    (h : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x ↦ by simpa using h x)

/-- `allWin` is integrable. -/
theorem integrable_allWin {N : ℕ} (ν : Measure (Fin N → X)) [IsFiniteMeasure ν] (a : Fin N) :
    Integrable (fun y ↦ allWin L D y a) ν :=
  integrable_of_abs_le ν _ 1 fun y ↦ by
    rw [abs_of_nonneg (allWin_mem L D y a).1]
    exact (allWin_mem L D y a).2

omit [MeasurableSingletonClass X] [Countable X] in
/-- Permuting the coordinates of i.i.d. points does not change their law. -/
theorem measurePreserving_perm (μ : Measure X) [IsProbabilityMeasure μ] {N : ℕ}
    (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun y : Fin N → X ↦ fun k ↦ y (σ k)) (Measure.pi fun _ ↦ μ)
      (Measure.pi fun _ ↦ μ) := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin N ↦ μ) (fun _ : Fin N ↦ μ) σ.symm
    (MeasurableEquiv.refl X) (fun _ ↦ MeasurePreserving.id μ)
  convert h using 1
  funext y k
  rfl

/-- The events `Eₐ` have the same probability (permute the indices). -/
theorem integral_allWin_eq (μ : Measure X) [IsProbabilityMeasure μ] {N : ℕ} (a a₀ : Fin N) :
    ∫ y, allWin L D y a ∂(Measure.pi fun _ ↦ μ) =
      ∫ y, allWin L D y a₀ ∂(Measure.pi fun _ ↦ μ) := by
  have hT := measurePreserving_perm μ (Equiv.swap a₀ a)
  conv_rhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  simp_rw [allWin_perm, Equiv.swap_apply_left]

/-- Integrating out `y 1, …, y M`: the probability of `E₀` is `E_y [p(y)^M]`. -/
theorem integral_allWin_zero (μ : Measure X) [IsProbabilityMeasure μ] (M : ℕ) :
    ∫ y, allWin L D y 0 ∂(Measure.pi fun _ : Fin (M + 1) ↦ μ) =
      ∫ y, (∫ y', win L D y y' ∂μ) ^ M ∂μ := by
  have hT := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) ↦ μ) 0
  rw [← hT.symm.integral_comp' (fun y ↦ allWin L D y 0)]
  rw [integral_prod _ (integrable_of_abs_le _ _ 1 fun p ↦ ?_)]
  · congr 1
    funext x
    have h := integral_fintype_prod_eq_pow (ι := Fin M) (fun y' ↦ win L D x y') (μ := μ)
    rw [Fintype.card_fin] at h
    rw [← h]
    congr 1
    funext z
    simp [allWin, Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply]
  · rw [abs_of_nonneg (allWin_mem L D _ 0).1]
    exact (allWin_mem L D _ 0).2

end X

open X in
/-- **The exchangeability bound** [BDT24, Lemma 4.1]. -/
theorem exch {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    (μ : Measure X) [IsProbabilityMeasure μ] (L : ℕ) (D : X → X → List Bool → Bool) (M : ℕ) :
    ∫ y, (∫ y', coinProb L (fun r ↦ D y y' r = true) * coinProb L (fun r ↦ D y' y r = false) ∂μ)
        ^ M ∂μ ≤ 1 / ((M : ℝ) + 1) := by
  change ∫ y, (∫ y', win L D y y' ∂μ) ^ M ∂μ ≤ _
  have hsum : ∑ a : Fin (M + 1), ∫ y, allWin L D y a ∂(Measure.pi fun _ ↦ μ) ≤ 1 := by
    rw [← integral_finsetSum _ fun a _ ↦ integrable_allWin L D _ a]
    calc _ ≤ ∫ _, (1 : ℝ) ∂(Measure.pi fun _ : Fin (M + 1) ↦ μ) :=
          integral_mono (integrable_finsetSum _ fun a _ ↦ integrable_allWin L D _ a)
            (integrable_const 1) fun y ↦ sum_allWin_le L D y
      _ = 1 := by simp
  simp_rw [integral_allWin_eq L D μ _ 0] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← integral_allWin_zero L D μ M, le_div_iff₀ (by positivity)]
  push_cast at hsum
  linarith

end BDT24.Prob
