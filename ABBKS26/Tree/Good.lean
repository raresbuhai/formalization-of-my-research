module

public import ABBKS26.Prob.Counts
public import ABBKS26.Prob.Moments
public import ABBKS26.Prob.Transfer
public import ABBKS26.Prob.Uniform
public import ABBKS26.Prob.Glue
public import ABBKS26.Robust.RB

/-!
# The good event

One measurable event on the labelled sample combining accurate label counts, few corrupted
points, uniform window counts for all quadratic statistics and nearly Gaussian standardized
moments. The analysis of every (not necessarily measurable) rounding and data-dependent step
is deterministic on this event.
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section

open Matrix

open Common MeasureTheory MvPolynomial
open scoped BigOperators
variable {n k d : ℕ}

def momentAccuracy (w η : ℝ) (d D : ℕ) : ℝ :=
  η * (w / (64 * (d + 1) * D)) ^ (4 * D)

def radius (d : ℕ) (η : ℝ) : ℝ := 4 * Real.sqrt (d / η) + 1

def Good (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d) : Prop :=
  GoodCounts M.w η (labels ω) ∧ (corrupted ω).card ≤ (ε + η) * n ∧
    (∀ j, clusterPts M ω j ∉ Unif.badSet d (cluster (labels ω) j).card
      (η / 4) (η / 4) (radius d η)) ∧
    GoodMoments (momentAccuracy w η d D) D (labels ω) (stdClean M ω)

def componentThreshold (w η δ : ℝ) (k d : ℕ) : ℝ :=
  Unif.sampleSize d (η / 4) (η / 4) (radius d η) (δ / (4 * k)) / (0.9 * w)

def sampleNeed (w η δ : ℝ) (k d D : ℕ) : ℝ :=
  let KD := (64 * D / w) ^ (4 * D)
  max (componentThreshold w η δ k d)
    (max (32 * (d + 1) / η ^ 2)
      (max (2 * KD * (d + 1) ^ (2 * D) / η)
        (32 * k * KD ^ 2 * (2 * D) ^ D * (d + 1) ^ (9 * D) / (w * η ^ 2 * δ))))

def referenceSet (ω : Fin n → Triple k d) (I : Finset (Fin k)) : Finset (Fin n) :=
  Finset.univ.filter (fun l ↦ (ω l).1 ∈ I)

def leakage (ω : Fin n → Triple k d) (N : Finset (Fin n)) (I : Finset (Fin k)) : ℝ :=
  (List.ofFn fun j : Fin k ↦
    let cleanj := cluster (labels ω) j \ corrupted ω
    if j ∈ I then ((cleanj \ N).card : ℝ) / (cluster (labels ω) j).card
    else ((cleanj ∩ N).card : ℝ) / (cluster (labels ω) j).card).foldl max 0

def nodeContamination (ω : Fin n → Triple k d) (N : Finset (Fin n))
    (I : Finset (Fin k)) : ℝ :=
  let G := referenceSet ω I
  let good := G ∩ (Finset.univ \ corrupted ω) ∩ N
  max (((N \ good).card : ℝ) / N.card)
    (max (((G \ good).card : ℝ) / G.card) (2 / N.card))

def WeakPartition (S : List (Finset (Fin n))) : Prop :=
  (∀ a b : Fin S.length, a ≠ b → Disjoint S[a] S[b]) ∧ S.toFinset.biUnion id = Finset.univ

def GoodPartition (ω : Fin n → Triple k d) (w Φ : ℝ)
    (S : List (Finset (Fin n))) : Prop :=
  WeakPartition S ∧ ∃ I : Fin S.length → Finset (Fin k),
    (∀ a, (I a).Nonempty) ∧ (∀ a b, a ≠ b → Disjoint (I a) (I b)) ∧
    Finset.univ.biUnion I = Finset.univ ∧
    ∀ a, leakage ω S[a] (I a) ≤ Φ ∧ w * n / 4 ≤ S[a].card

private theorem notMem_badSet_pos {m : ℕ} {a ρ R : ℝ}
    {g : Fin m → EuclideanSpace ℝ (Fin d)} (hg : g ∉ Unif.badSet d m a ρ R) :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  apply hg
  apply Or.inl
  simp [Unif.upperBad, Unif.indCount, hm0]

private theorem radius_pos (d : ℕ) (η : ℝ) : 0 < radius d η := by
  unfold radius
  positivity

private theorem radius_bound (d : ℕ) {η : ℝ} (hη : 0 < η) :
    4 * d ≤ (η / 4) * radius d η ^ 2 := by
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg d) hη.le)
  have hh : η * (Real.sqrt (d / η)) ^ 2 = d := by
    rw [hs, mul_div_cancel₀ _ hη.ne']
  unfold radius
  nlinarith [Real.sqrt_nonneg (d / η)]

private theorem good_unif (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (hg : Good M ε w η D ω)
    (hη : 0 < η ∧ η ≤ 1 / 100) (j : Fin k) :
    Unif.UnifWin (η / 4) (η / 4) (radius d η) (clusterPts M ω j) := by
  have hη0 := hη.1
  exact Unif.unifWin_of_notMem_badSet (by positivity) (by positivity)
    (by linarith [hη.2]) (radius_pos d η) (radius_bound d hη.1) (hg.2.2.1 j)

/-- The common good event is measurable and contains no rounded-point map. -/
theorem measurable_good
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) :
    MeasurableSet {ω : Fin n → Triple k d | Good M ε w η D ω} := by
  unfold Good
  refine (measurableSet_goodCounts M.w η).inter
    ((measurableSet_corrupted_card_le _).inter ((?_ : MeasurableSet {ω : Fin n → Triple k d |
      ∀ j, clusterPts M ω j ∉ Unif.badSet d (cluster (labels ω) j).card
        (η / 4) (η / 4) (radius d η)}).inter
      (measurableSet_goodMoments M n _ D)))
  simpa only [Set.ofPred_forall, Set.compl_ofPred] using
    MeasurableSet.iInter fun j ↦
      (measurableSet_clusterPts_mem M
        (fun m ↦ Unif.measurableSet_badSet d m (η / 4) (η / 4) (radius d η)) j).compl

/-- Good samples have accurate label counts and few corrupted indices. -/
theorem good_counts
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (hg : Good M ε w η D ω) (hη : 0 ≤ η ∧ η ≤ 1 / 100) :
    (∀ j, 0.9 * M.w j * n ≤ (cluster (labels ω) j).card ∧
      (cluster (labels ω) j).card ≤ 1.1 * M.w j * n) ∧
    (corrupted ω).card ≤ (ε + η) * n := by
  refine ⟨fun j ↦ ?_, hg.2.1⟩
  have hj := abs_le.mp (hg.1 j)
  have hx : 0 ≤ (n : ℝ) * M.w j := by
    by_cases hn : n = 0
    · simp [hn]
    · by_contra hx
      have hneg : η * ((n : ℝ) * M.w j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hη.1
        (le_of_not_ge hx)
      have hc := Nat.cast_nonneg (α := ℝ) (cluster (labels ω) j).card
      linarith
  have he : η * ((n : ℝ) * M.w j) ≤ (1 / 100) * ((n : ℝ) * M.w j) :=
    mul_le_mul_of_nonneg_right hη.2 hx
  constructor <;> nlinarith

private theorem probability_ledger (ε w η δ : ℝ) (D : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hη0 : 0 < η) (hδ0 : 0 < δ)
    (hk1 : (1 : ℝ) ≤ k) (hD : 4 ≤ D) (he : ε ≤ 1)
    (hn : sampleNeed w η δ k d D ≤ n) :
    0 < n ∧ 0 < momentAccuracy w η d D ∧
      k / (n * η ^ 2 * w) ≤ δ / 4 ∧
      ε / (n * η ^ 2) ≤ δ / 4 ∧
      k * (d + 1) ^ D * (2 * D) ^ D / (n * momentAccuracy w η d D ^ 2) ≤ δ / 4 := by
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  let K : ℝ := (64 * D / w) ^ (4 * D)
  have hK1 : 1 ≤ K := by
    apply one_le_pow₀
    rw [le_div_iff₀ hw]
    linarith only [hD4, hw1]
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hd1 : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hT1 : (1 : ℝ) ≤ (2 * D) ^ D := one_le_pow₀ (by linarith)
  have hL1 : (1 : ℝ) ≤ (d + 1) ^ (9 * D) := one_le_pow₀ hd1
  change max (componentThreshold w η δ k d)
    (max (32 * (d + 1) / η ^ 2)
      (max (2 * K * (d + 1) ^ (2 * D) / η)
        (32 * k * K ^ 2 * (2 * D) ^ D * (d + 1) ^ (9 * D) /
          (w * η ^ 2 * δ)))) ≤ n at hn
  have hcpt := (max_le_iff.mp hn).1
  have hnsmall := (max_le_iff.mp (max_le_iff.mp hn).2).1
  have hlast := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hn).2).2).2
  have hn0 : (0 : ℝ) < n := (by positivity : (0 : ℝ) <
    32 * (d + 1) / η ^ 2).trans_le hnsmall
  have hnNat : 0 < n := Nat.cast_pos.mp hn0
  let A : ℝ := k * K ^ 2 * (2 * D) ^ D * (d + 1) ^ (9 * D)
  have hAk : (k : ℝ) ≤ A := by
    calc (k : ℝ) = k * 1 * 1 * 1 := by ring
      _ ≤ A := by
        dsimp [A]
        gcongr
        exact one_le_pow₀ hK1
  have hA0 : 0 ≤ A := hk0.le.trans hAk
  have hsize : 32 * A ≤ n * w * η ^ 2 * δ := by
    have hh := (div_le_iff₀ (by positivity : 0 < w * η ^ 2 * δ)).mp hlast
    dsimp [A]
    nlinarith only [hh]
  have hcBound : k / (n * η ^ 2 * w) ≤ δ / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hAk, hsize]
  have huBound : ε / (n * η ^ 2) ≤ δ / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hh : n * w * η ^ 2 * δ ≤ n * η ^ 2 * δ := by
      have hh := mul_le_mul_of_nonneg_right hw1
        (by positivity : (0 : ℝ) ≤ n * η ^ 2 * δ)
      nlinarith only [hh]
    nlinarith only [hh, hsize, hAk, hk1, he]
  have hacc : momentAccuracy w η d D = η / (K * (d + 1) ^ (4 * D)) := by
    have heq : w / (64 * (d + 1) * D) = 1 / ((64 * D / w) * (d + 1)) := by
      field_simp
    rw [momentAccuracy, heq, _root_.one_div_pow, mul_pow]
    change η * (1 / (K * (d + 1) ^ (4 * D))) = _
    ring
  have ha0 : 0 < momentAccuracy w η d D := by rw [hacc]; positivity
  have hmExpr : k * (d + 1) ^ D * (2 * D) ^ D /
      (n * momentAccuracy w η d D ^ 2) = A / (n * η ^ 2) := by
    rw [hacc]
    have hp : (d + 1 : ℝ) ^ (9 * D) =
        (d + 1) ^ D * ((d + 1) ^ (4 * D)) ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    dsimp [A]
    rw [hp]
    field_simp
  have hmBound : k * (d + 1) ^ D * (2 * D) ^ D /
      (n * momentAccuracy w η d D ^ 2) ≤ δ / 4 := by
    rw [hmExpr, div_le_iff₀ (by positivity)]
    have hh : n * w * η ^ 2 * δ ≤ n * η ^ 2 * δ := by
      have hh := mul_le_mul_of_nonneg_right hw1
        (by positivity : (0 : ℝ) ≤ n * η ^ 2 * δ)
      nlinarith only [hh]
    nlinarith only [hh, hsize, hA0]
  exact ⟨hnNat, ha0, hcBound, huBound, hmBound⟩

/-- The existing probability layer bounds failure of the common good event. -/
theorem good_probability
    (M : Mixture k d) (P : Measure (Triple k d)) (ε w η δ : ℝ) (D : ℕ)
    (hM : M.Valid) (hP : IsCorruption M ε P) (he : 0 ≤ ε ∧ ε ≤ 1)
    (hw : 0 < w) (hweights : ∀ i, w ≤ M.w i) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hδ : 0 < δ ∧ δ < 1) (hD : 4 ≤ D) (hn : sampleNeed w η δ k d D ≤ n) :
    (Measure.pi fun _ : Fin n ↦ P).real {ω | ¬ Good M ε w η D ω} ≤ δ := by
  classical
  have hη0 := hη.1
  have hδ0 := hδ.1
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    have hh := hM.sum_w
    simp [hk0] at hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hw1 : w ≤ 1 := by
    refine (hweights ⟨0, hk⟩).trans ?_
    rw [← hM.sum_w]
    exact Finset.single_le_sum (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ _)
  obtain ⟨hnNat, ha0, hcBound, huBound, hmBound⟩ :=
    probability_ledger ε w η δ D hw hw1 hη0 hδ0 hk1 hD he.2 hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnNat
  have hcpt : componentThreshold w η δ k d ≤ n := (le_max_left _ _).trans hn
  let B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d)) := fun m ↦
    if Unif.sampleSize d (η / 4) (η / 4) (radius d η) (δ / (4 * k)) ≤ m then
      Unif.badSet d m (η / 4) (η / 4) (radius d η) else ∅
  have hB : ∀ m, MeasurableSet (B m) := by
    intro m
    dsimp [B]
    split_ifs
    · exact Unif.measurableSet_badSet _ _ _ _ _
    · exact MeasurableSet.empty
  have hβ : ∀ m, (Measure.pi fun _ : Fin m ↦
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).real (B m) ≤ δ / (4 * k) := by
    intro m
    dsimp [B]
    split_ifs with hm
    · exact (Unif.measureReal_badSet_le (by positivity) _ _).trans
        (Unif.bound_le (by positivity) (by positivity) (by linarith [hη.2])
          (radius_pos d η).le (by positivity) hm)
    · simp only [measureReal_empty]
      positivity
  have hlarge : ∀ ω : Fin n → Triple k d, GoodCounts M.w η (labels ω) →
      ∀ j, Unif.sampleSize d (η / 4) (η / 4) (radius d η) (δ / (4 * k)) ≤
        (cluster (labels ω) j).card := by
    intro ω hc j
    have hcount := abs_le.mp (hc j)
    have hηw : η * (n * M.w j) ≤ (1 / 100) * (n * M.w j) :=
      mul_le_mul_of_nonneg_right hη.2 (mul_nonneg hn0.le (hM.nonneg_w j))
    have hc' : 0.9 * w * n ≤ (cluster (labels ω) j).card := by
      have hh := mul_le_mul_of_nonneg_right (hweights j) hn0.le
      nlinarith
    have ht := (div_le_iff₀ (by positivity : 0 < 0.9 * w)).mp hcpt
    exact (by nlinarith : Unif.sampleSize d (η / 4) (η / 4) (radius d η)
      (δ / (4 * k)) ≤ 0.9 * w * n).trans hc'
  have := hP.isProbabilityMeasure hM
  let μ := Measure.pi fun _ : Fin n ↦ P
  have hsub : {ω : Fin n → Triple k d | ¬ Good M ε w η D ω} ⊆
      {ω | ¬ GoodCounts M.w η (labels ω)} ∪
      ({ω | (ε + η) * n < ((corrupted ω).card : ℝ)} ∪
      ({ω | ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card} ∪
      {ω | ¬ GoodMoments (momentAccuracy w η d D) D (labels ω) (stdClean M ω)})) := by
    intro ω hω
    change ¬ Good M ε w η D ω at hω
    by_cases hc : GoodCounts M.w η (labels ω)
    · by_cases hu : ((corrupted ω).card : ℝ) ≤ (ε + η) * n
      · by_cases hm : GoodMoments (momentAccuracy w η d D) D (labels ω) (stdClean M ω)
        · have hj : ∃ j, clusterPts M ω j ∈
              Unif.badSet d (cluster (labels ω) j).card (η / 4) (η / 4) (radius d η) := by
            simpa only [Good, hc, hu, hm, true_and, and_true, not_forall, not_not] using hω
          obtain ⟨j, hj⟩ := hj
          exact Or.inr (Or.inr (Or.inl ⟨j, by simpa [B, hlarge ω hc j] using hj⟩))
        · exact Or.inr (Or.inr (Or.inr hm))
      · exact Or.inr (Or.inl (lt_of_not_ge hu))
    · exact Or.inl hc
  have hcP := (pi_not_goodCounts_le hM hP hw hweights hη0 hnNat).trans hcBound
  have huP := (pi_corrupted_card_gt_le hM hP he.1 hη0 hnNat).trans huBound
  have hmP := (pi_not_goodMoments_le hM hP ha0 hnNat D).trans hmBound
  have hBP := hP.pi_exists_clusterPts_mem_le hM hB hβ (n := n)
  have hBP' : μ.real {ω | ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card} ≤
      δ / 4 := by
    convert hBP using 1
    field_simp
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have huP' := measureReal_union_le (μ := μ)
    {ω | (ε + η) * n < ((corrupted ω).card : ℝ)}
    ({ω | ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card} ∪
      {ω | ¬ GoodMoments (momentAccuracy w η d D) D (labels ω) (stdClean M ω)})
  have hmP' := measureReal_union_le (μ := μ)
    {ω | ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card}
    {ω | ¬ GoodMoments (momentAccuracy w η d D) D (labels ω) (stdClean M ω)}
  change μ.real _ ≤ _ at hcP huP hmP
  linarith

private theorem winProb_mono (q : Unif.Quad d) {a b a' b' : ℝ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    Unif.winProb q a b ≤ Unif.winProb q a' b' := by
  exact measureReal_mono fun _ hx ↦ ⟨ha.trans hx.1, hx.2.trans hb⟩

private theorem reindex_window_le (s U : Finset (Fin n))
    (x y : Fin n → EuclideanSpace ℝ (Fin d))
    (hxy : ∀ l ∈ s, l ∉ U → x l = y l) (q : Unif.Quad d) (a b : ℝ) :
    (Unif.winCount q a b (reindex s x) : ℝ) ≤
      Unif.winCount q a b (reindex s y) + (U ∩ s).card := by
  classical
  let e := s.orderEmbOfFin rfl
  have hbad : (Finset.univ.filter fun t ↦ e t ∈ U).card ≤ (U ∩ s).card := by
    apply Finset.card_le_card_of_injOn e
    · intro t ht
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp ht).2, s.orderEmbOfFin_mem rfl t⟩
    · exact e.injective.injOn
  have h := Unif.card_filter_le_add (m := s.card)
    (p := fun t ↦ q.eval (reindex s x t) ∈ Set.Icc a b)
    (r := fun t ↦ q.eval (reindex s y t) ∈ Set.Icc a b)
    (s := fun t ↦ e t ∈ U) (fun t ht ↦ by
      by_cases hU : e t ∈ U
      · exact Or.inr hU
      · exact Or.inl (by
          change q.eval (x (e t)) ∈ Set.Icc a b at ht
          change q.eval (y (e t)) ∈ Set.Icc a b
          rwa [hxy (e t) (s.orderEmbOfFin_mem rfl t) hU] at ht))
  exact h.trans (add_le_add le_rfl (Nat.cast_le.mpr hbad))

private theorem rounding_margin (d : ℕ) {η : ℝ} (hη : 0 < η) {n : ℕ}
    (hn0 : (0 : ℝ) < n) (hn : (2 * radius d η + 2) / η ≤ n) :
    1 / n * (2 * radius d η + 1) + (1 / n) ^ 2 + η / 4 ≤ 2 * η := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.cast_pos.mp hn0)))
  have hi : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
  have hi0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hh : 2 * radius d η + 2 ≤ n * η := (div_le_iff₀ hη).mp hn
  have hh' : (1 / n : ℝ) * (2 * radius d η + 2) ≤ η := by
    rw [one_div_mul_eq_div, div_le_iff₀ hn0]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hi hi0]

private theorem rounded_clean_windows (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (hM : M.Valid)
    (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (q : Unif.Quad d) (hq : q.normSq ≤ 1) (a b : ℝ) :
    let g := reindex (cluster (labels ω) j) (fun l ↦
      stdPt M ((ω l).1) (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ))))
    (Unif.winProb q (a + 2 * η) (b - 2 * η) - η) *
        (cluster (labels ω) j).card ≤ Unif.winCount q a b g ∧
    (Unif.winCount q a b g : ℝ) ≤
      (Unif.winProb q (a - 2 * η) (b + 2 * η) + η) * (cluster (labels ω) j).card := by
  dsimp only
  have hcp := notMem_badSet_pos (hg.2.2.1 j)
  have hcn : (cluster (labels ω) j).card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hcp.trans_le hcn)
  have hnear : ∀ t : Fin (cluster (labels ω) j).card,
      ‖reindex (cluster (labels ω) j) (fun l ↦ stdPt M (ω l).1
          (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ)))) t -
        clusterPts M ω j t‖ ≤ 1 / n := by
    intro t
    exact norm_stdPt_sub_le_of_isRounding hM (by positivity) hr _ _
  have hW := good_unif M ε w η D ω hg hη j
  have hlo := hW.le_winCount_of_near hnear hq a b
  have hup := hW.winCount_le_of_near hnear hq a b
  have ht := rounding_margin d hη.1 hn0 hn
  have hpl := winProb_mono q (a := a + 2 * η) (b := b - 2 * η)
    (a' := a + (1 / n * (2 * radius d η + 1) + (1 / n) ^ 2) + η / 4)
    (b' := b - (1 / n * (2 * radius d η + 1) + (1 / n) ^ 2) - η / 4)
    (by linarith : a + (1 / n * (2 * radius d η + 1) + (1 / n) ^ 2) + η / 4 ≤
      a + 2 * η) (by linarith)
  have hpu := winProb_mono q
    (a := a - (1 / n * (2 * radius d η + 1) + (1 / n) ^ 2) - η / 4)
    (b := b + (1 / n * (2 * radius d η + 1) + (1 / n) ^ 2) + η / 4)
    (a' := a - 2 * η) (b' := b + 2 * η) (by linarith) (by linarith)
  constructor
  · refine le_trans ?_ hlo
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith [hη.1]
  · refine hup.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith [hη.1]

-- The fixed statement retains its unused clean-sample `g` let binding.
set_option linter.unusedVariables false in
/-- Uniform windows tolerate own-component rounding for every quadratic statistic. -/
theorem rounded_windows
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hg : Good M ε w η D ω)
    (hr : IsRounding M (1 / n) r) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (q : Unif.Quad d) (hq : q.normSq ≤ 1) (a b : ℝ) :
    let g := clusterPts M ω j
    let g' := reindex (cluster (labels ω) j) (fun l ↦
      stdPt M ((ω l).1) (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ))))
    (Unif.winProb q (a + 2 * η) (b - 2 * η) - η) * (cluster (labels ω) j).card ≤
      Unif.winCount q a b g' + (corrupted ω ∩ cluster (labels ω) j).card := by
  dsimp only
  have hlo := (rounded_clean_windows M ε w η D ω r hM hg hr hη hn j q hq a b).1
  refine hlo.trans (reindex_window_le _ (corrupted ω) _ _ ?_ q a b)
  intro l _ hl
  have he : (ω l).2.1 = (ω l).2.2 := not_not.mp (mem_corrupted.not.mp hl)
  rw [he]

/-- Uniform rounded window counts also have the enlarged-population upper bound. -/
theorem rounded_windows_upper
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hg : Good M ε w η D ω)
    (hr : IsRounding M (1 / n) r) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hn : (2 * radius d η + 2) / η ≤ n)
    (j : Fin k) (q : Unif.Quad d) (hq : q.normSq ≤ 1) (a b : ℝ) :
    let g' := reindex (cluster (labels ω) j) (fun l ↦
      stdPt M ((ω l).1) (WithLp.toLp 2 (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ))))
    (Unif.winCount q a b g' : ℝ) ≤
      (Unif.winProb q (a - 2 * η) (b + 2 * η) + η) * (cluster (labels ω) j).card +
        (corrupted ω ∩ cluster (labels ω) j).card := by
  dsimp only
  have hup := (rounded_clean_windows M ε w η D ω r hM hg hr hη hn j q hq a b).2
  refine (reindex_window_le _ (corrupted ω) _ _ ?_ q a b).trans
    (add_le_add hup le_rfl)
  intro l _ hl
  have he : (ω l).2.1 = (ω l).2.2 := not_not.mp (mem_corrupted.not.mp hl)
  rw [he]

private theorem foldl_max_le_iff (l : List ℝ) (a b : ℝ) :
    l.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ l, x ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc, and_left_comm]

private theorem sum_cluster_card (ω : Fin n → Triple k d) (s : Finset (Fin n)) :
    ∑ j, ((s ∩ cluster (labels ω) j).card : ℝ) = s.card := by
  classical
  have he : ∀ j, s ∩ cluster (labels ω) j = s.filter (labels ω · = j) := by
    intro j
    ext l
    simp [cluster]
  simp_rw [he]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]

private theorem leakage_accounting (ω : Fin n → Triple k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) {Φ : ℝ}
    (hΦ : leakage ω N I ≤ Φ) :
    0 ≤ Φ ∧
      let G := referenceSet ω I
      let good := G ∩ (Finset.univ \ corrupted ω) ∩ N
      ((N \ good).card : ℝ) ≤ Φ * n + (corrupted ω).card ∧
      ((G \ good).card : ℝ) ≤ Φ * n + (corrupted ω).card := by
  classical
  have hle := (foldl_max_le_iff _ 0 Φ).mp hΦ
  refine ⟨hle.1, ?_⟩
  dsimp only
  let G := referenceSet ω I
  let E := ((G \ N) ∪ (N \ G)) \ corrupted ω
  have hj (j : Fin k) : ((E ∩ cluster (labels ω) j).card : ℝ) ≤
      Φ * (cluster (labels ω) j).card := by
    have hh := hle.2 _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    change (if j ∈ I then
      (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ) /
        (cluster (labels ω) j).card else
      (((cluster (labels ω) j \ corrupted ω) ∩ N).card : ℝ) /
        (cluster (labels ω) j).card) ≤ Φ at hh
    have he : E ∩ cluster (labels ω) j =
        if j ∈ I then (cluster (labels ω) j \ corrupted ω) \ N
        else (cluster (labels ω) j \ corrupted ω) ∩ N := by
      ext l
      have hcl : l ∈ cluster (labels ω) j ↔ (ω l).1 = j := by
        exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ l))
      have hgl : l ∈ G ↔ (ω l).1 ∈ I := by
        exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ l))
      by_cases hji : j ∈ I <;> by_cases hl : (ω l).1 = j <;>
        simp only [E, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union,
          hcl, hgl, hl, hji, ite_true, ite_false] <;> tauto
    rw [he]
    by_cases hc : (cluster (labels ω) j).card = 0
    · have hz : cluster (labels ω) j = ∅ := Finset.card_eq_zero.mp hc
      simp [hz]
    · have hc0 : (0 : ℝ) < (cluster (labels ω) j).card :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
      split_ifs at hh ⊢ <;> exact (div_le_iff₀ hc0).mp hh
  have hE : (E.card : ℝ) ≤ Φ * n := by
    rw [← sum_cluster_card ω E]
    refine (Finset.sum_le_sum fun j _ ↦ hj j).trans_eq ?_
    rw [← Finset.mul_sum]
    have hh := sum_cluster_card ω Finset.univ
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hh
    rw [hh]
  have hsubN : N \ (G ∩ (Finset.univ \ corrupted ω) ∩ N) ⊆ E ∪ corrupted ω := by
    intro l hl
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and,
      not_and, Finset.mem_union, E] at hl ⊢
    tauto
  have hsubG : G \ (G ∩ (Finset.univ \ corrupted ω) ∩ N) ⊆ E ∪ corrupted ω := by
    intro l hl
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and,
      not_and, Finset.mem_union, E] at hl ⊢
    tauto
  have hbound : ((E ∪ corrupted ω).card : ℝ) ≤ Φ * n + (corrupted ω).card := by
    exact (Nat.cast_le.mpr (Finset.card_union_le E (corrupted ω))).trans
      (by push_cast; linarith)
  exact ⟨(Nat.cast_le.mpr (Finset.card_le_card hsubN)).trans hbound,
    (Nat.cast_le.mpr (Finset.card_le_card hsubG)).trans hbound⟩

/-- Node contamination includes deletions, insertions and the finite-size term. -/
theorem contamination_bound
    (M : Mixture k d) (ε w η Φ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hg : Good M ε w η D ω)
    (hM : M.Valid) (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j)
    (hη : 0 ≤ η ∧ η ≤ 1 / 100) (hI : I.Nonempty)
    (hΦ : leakage ω N I ≤ Φ) (hN : w * n / 4 ≤ N.card) :
    nodeContamination ω N I ≤ 8 * (Φ + ε + η + 1 / n) / w := by
  have _ := hM
  classical
  obtain ⟨j, hj⟩ := hI
  have hcp := notMem_badSet_pos (hg.2.2.1 j)
  have hcn : (cluster (labels ω) j).card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hcp.trans_le hcn)
  have hc := (good_counts M ε w η D ω hg hη).1 j |>.1
  have hcw : w * n / 2 ≤ (cluster (labels ω) j).card := by
    have := mul_le_mul_of_nonneg_right (hwj j) hn0.le
    nlinarith
  have hsub : cluster (labels ω) j ⊆ referenceSet ω I := by
    intro l hl
    have hl' : (ω l).1 = j := (Finset.mem_filter.mp hl).2
    simp [referenceSet, hl', hj]
  have hG : w * n / 2 ≤ ((referenceSet ω I).card : ℝ) :=
    hcw.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hG0 : (0 : ℝ) < (referenceSet ω I).card :=
    (by positivity : (0 : ℝ) < w * n / 2).trans_le hG
  have hN0 : (0 : ℝ) < N.card := (by positivity : (0 : ℝ) < w * n / 4).trans_le hN
  obtain ⟨hΦ0, hbad, hdel⟩ := leakage_accounting ω N I hΦ
  have hξ : 0 ≤ ε + η := by
    have hc0 : (0 : ℝ) ≤ (corrupted ω).card := Nat.cast_nonneg _
    nlinarith [hg.2.1]
  have hx : 0 ≤ Φ + ε + η := by linarith
  have hbad' : ((N \ (referenceSet ω I ∩ (Finset.univ \ corrupted ω) ∩ N)).card : ℝ) ≤
      (Φ + ε + η) * n := by nlinarith [hg.2.1]
  have hdel' : ((referenceSet ω I \
      (referenceSet ω I ∩ (Finset.univ \ corrupted ω) ∩ N)).card : ℝ) ≤
      (Φ + ε + η) * n := by nlinarith [hg.2.1]
  unfold nodeContamination
  dsimp only
  refine max_le ?_ (max_le ?_ ?_)
  · rw [div_le_iff₀ hN0, div_mul_eq_mul_div, le_div_iff₀ hw]
    have hh := mul_le_mul_of_nonneg_left hN (by positivity :
      0 ≤ 8 * (Φ + ε + η + 1 / n))
    have hi : (1 / (n : ℝ)) * n = 1 := one_div_mul_cancel hn0.ne'
    nlinarith [mul_le_mul_of_nonneg_right hbad' hw.le]
  · rw [div_le_iff₀ hG0, div_mul_eq_mul_div, le_div_iff₀ hw]
    have hh := mul_le_mul_of_nonneg_left hG (by positivity :
      0 ≤ 8 * (Φ + ε + η + 1 / n))
    have hi : (1 / (n : ℝ)) * n = 1 := one_div_mul_cancel hn0.ne'
    nlinarith [mul_le_mul_of_nonneg_right hdel' hw.le]
  · rw [div_le_iff₀ hN0, div_mul_eq_mul_div, le_div_iff₀ hw]
    have hh := mul_le_mul_of_nonneg_left hN (by positivity :
      0 ≤ 8 * (Φ + ε + η + 1 / n))
    have hi : (1 / (n : ℝ)) * n = 1 := one_div_mul_cancel hn0.ne'
    nlinarith [mul_nonneg hx hn0.le]

/-- Good standardized moments imply uniform-in-frame reference resilience. -/
theorem moment_resilience
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hg : Good M ε w η D ω)
    (hr : IsRounding M (1 / n) r) (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hD : 4 ≤ D) :
    ∀ j (s : ℕ), s ≤ D →
      ∀ α : Fin d → ℕ, (∑ i, α i) ≤ s →
      |(∑ l ∈ cluster (labels ω) j, ∏ i, stdClean M ω l i ^ α i) /
        (cluster (labels ω) j).card - gaussMomMulti α| ≤
          2 * momentAccuracy w η d D / w := by
  have _ := hM
  have _ := hr
  have _ := hD
  intro j s hs α hα
  have ha : 0 ≤ momentAccuracy w η d D := by
    exact mul_nonneg hη.1.le (pow_nonneg (by positivity) _)
  have hcp := notMem_badSet_pos (hg.2.2.1 j)
  have hcn : (cluster (labels ω) j).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hcp.trans_le hcn)
  have hc := (good_counts M ε w η D ω hg ⟨hη.1.le, hη.2⟩).1 j |>.1
  have hc0 : (0 : ℝ) < (cluster (labels ω) j).card := Nat.cast_pos.mpr hcp
  have hcw : w * n / 2 ≤ (cluster (labels ω) j).card := by
    have := mul_le_mul_of_nonneg_right (hwj j) hn0.le
    nlinarith
  have hm := hg.2.2.2 j α (hα.trans hs)
  rw [div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos hn0,
    div_le_iff₀ hn0] at hm
  rw [div_sub' hc0.ne', abs_div,
    abs_of_pos hc0, div_le_iff₀ hc0]
  have hb : momentAccuracy w η d D * n ≤
      2 * momentAccuracy w η d D / w * (cluster (labels ω) j).card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    nlinarith [mul_le_mul_of_nonneg_left hcw ha]
  simpa only [mul_comm] using hm.trans hb

end

end ABBKS26.Tree
