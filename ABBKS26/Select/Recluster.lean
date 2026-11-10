module

public import ABBKS26.Select.Pairwise

/-!
# Reclustering

The final classification: each point gets the unique label that wins all pairwise tests
between the learned components, which recovers every component on the good event.
-/

@[expose] public section

namespace ABBKS26.Select

noncomputable section


open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

open Common _root_.ABBKS26.Tree
variable {n k d : ℕ}

def wins (tests : Fin k → Fin k → PairTest d) (a b : Fin k) (x : Fin d → ℚ) : Bool :=
  if a < b then (tests a b).first x else if b < a then !(tests b a).first x else true

def label (tests : Fin k → Fin k → PairTest d) (x : Fin d → ℚ) : ℕ :=
  ((List.finRange k).find? (fun a ↦ (List.finRange k).all (fun b ↦ wins tests a b x))).map
    Fin.val |>.getD 0

def recluster (tests : Fin k → Fin k → PairTest d) (x : Fin n → Fin d → ℚ) : Output :=
  List.ofFn (fun l ↦ label tests (x l))

/-- A component winning every comparison is the unique selected label. -/
theorem winner_label
    (tests : Fin k → Fin k → PairTest d) (a : Fin k) (x : Fin d → ℚ)
    (h : ∀ b, wins tests a b x = true) : label tests x = a := by
  have hall : (List.finRange k).all (fun b ↦ wins tests a b x) = true := by
    simpa using h
  have hex : ((List.finRange k).find?
      (fun c ↦ (List.finRange k).all (fun b ↦ wins tests c b x))).isSome := by
    rw [List.find?_isSome]
    exact ⟨a, by simp, hall⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hex
  have hcwin : ∀ b, wins tests c b x = true := by
    simpa using List.find?_some hc
  have hca : c = a := by
    by_contra hne
    have ha := h c
    have hb := hcwin a
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · simp [wins, hlt, not_lt_of_gt hlt] at ha hb
      simp_all
    · simp [wins, hlt, not_lt_of_gt hlt] at ha hb
      simp_all
  simp [label, hc, hca]

private theorem label_lt (tests : Fin k → Fin k → PairTest d) (x : Fin d → ℚ)
    (hk : 1 ≤ k) : label tests x < k := by
  unfold label
  cases (List.finRange k).find?
      (fun a ↦ (List.finRange k).all (fun b ↦ wins tests a b x)) with
  | none => simpa using (show 0 < k by omega)
  | some a => simp

private theorem empirical_halfline
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hg : Good M ε w η D ω)
    (hr : IsRounding M (1 / n) r) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hn : (2 * radius d η + 2) / η ≤ n) (j : Fin k) (f : Statistic d)
    (t e : ℝ) (left : Bool)
    (hp : (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
      {y | if left then f.eval y.ofLp ≤ t + 2 * η * Real.sqrt
        (variance (fun y ↦ f.eval y.ofLp)
          (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)))
      else t - 2 * η * Real.sqrt (variance (fun y ↦ f.eval y.ofLp)
        (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))) < f.eval y.ofLp} ≤ e) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      if left then SoundAux.value f ω r l ≤ t else t < SoundAux.value f ω r l).card : ℝ) ≤
        (e + η) * (cluster (labels ω) j).card := by
  classical
  have hη0 := hη.1
  let ν := multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  let margin := 2 * η * Real.sqrt (variance (fun y ↦ f.eval y.ofLp) ν)
  have hm0 : 0 ≤ margin := by dsimp [margin]; positivity
  have he : 0 ≤ e := measureReal_nonneg.trans hp
  obtain ⟨C⟩ := SoundAux.exists_coordinates M hM j f
  have hscale : C.s ≤ Real.sqrt (variance (fun y ↦ f.eval y.ofLp) ν) :=
    (Real.le_sqrt C.nonneg (variance_nonneg _ _)).mpr C.variance
  have hm : 2 * η * C.s ≤ margin :=
    mul_le_mul_of_nonneg_left hscale (by positivity)
  by_cases hs : 0 < C.s
  · have hp' : ν.real {y | if left then f.eval y.ofLp ≤ t + 2 * η * C.s
        else t - 2 * η * C.s < f.eval y.ofLp} ≤ e := by
      refine (measureReal_mono ?_).trans hp
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy ⊢
      cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hy ⊢
      all_goals dsimp only [margin, ν] at hm; linarith only [hy, hm]
    cases left with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hp' ⊢
      exact (C.upper_right M ε w η D ω r hM hg hr hη hn j f hs t).trans
        (mul_le_mul_of_nonneg_right (add_le_add hp' (le_refl η)) (Nat.cast_nonneg _))
    | true =>
      simp only [ite_true] at hp' ⊢
      exact (C.upper_left M ε w η D ω r hM hg hr hη hn j f hs t).trans
        (mul_le_mul_of_nonneg_right (add_le_add hp' (le_refl η)) (Nat.cast_nonneg _))
  · have hs0 : C.s = 0 := le_antisymm (le_of_not_gt hs) C.nonneg
    have hconst (y : EuclideanSpace ℝ (Fin d)) : f.eval y.ofLp = C.c := by
      simp only [C.eval, hs0, zero_mul, zero_add]
    have hval (l : Fin n) : SoundAux.value f ω r l = C.c := by
      simpa only [SoundAux.value, WithLp.ofLp_toLp, SoundAux.eval_cast] using
        hconst (WithLp.toLp 2 fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ))
    by_cases ht : if left then C.c ≤ t else t < C.c
    · have huniv : {y : EuclideanSpace ℝ (Fin d) | if left then
          f.eval y.ofLp ≤ t + margin else t - margin < f.eval y.ofLp} = Set.univ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, hconst]
        cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ht ⊢
        all_goals linarith
      change ν.real {y | if left then f.eval y.ofLp ≤ t + margin
        else t - margin < f.eval y.ofLp} ≤ e at hp
      rw [huniv, probReal_univ] at hp
      have hc : (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
          if left then SoundAux.value f ω r l ≤ t
          else t < SoundAux.value f ω r l).card : ℝ) ≤ (cluster (labels ω) j).card :=
        Nat.cast_le.mpr (Finset.card_le_card
          ((Finset.filter_subset _ _).trans Finset.sdiff_subset))
      exact hc.trans (by
        nlinarith only [hp, hη.1, Nat.cast_nonneg (α := ℝ) (cluster (labels ω) j).card])
    · have hz : ((cluster (labels ω) j \ corrupted ω).filter fun l ↦
          if left then SoundAux.value f ω r l ≤ t
          else t < SoundAux.value f ω r l) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro l _
        simpa only [hval] using ht
      rw [hz, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by positivity) (Nat.cast_nonneg _)

private theorem empirical_test
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hg : Good M ε w η D ω)
    (hr : IsRounding M (1 / n) r) (hη : 0 < η ∧ η ≤ 1 / 100)
    (hn : (2 * radius d η + 2) / η ≤ n) (j : Fin k) (T : PairTest d)
    (side : Bool) (e : ℝ)
    (hp : (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)).real
      {y | if side then ¬ T.contracted (2 * η * Real.sqrt
        (variance (fun y ↦ T.statistic.eval y.ofLp)
          (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)))) y.ofLp
      else T.expanded (2 * η * Real.sqrt
        (variance (fun y ↦ T.statistic.eval y.ofLp)
          (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)))) y.ofLp} ≤ e) :
    (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
      T.first (r ((ω l).1, (ω l).2.2)) ≠ side).card : ℝ) ≤
        (e + η) * (cluster (labels ω) j).card := by
  have hh := empirical_halfline M ε w η D ω r hM hg hr hη hn j T.statistic
    T.threshold e (side != T.firstOnLeft) (by
      cases hs : side <;> cases ht : T.firstOnLeft <;>
        simpa [hs, ht, PairTest.contracted, PairTest.expanded, not_lt] using hp)
  convert hh using 2
  congr 1
  apply Finset.filter_congr
  intro l _
  simp only [PairTest.first, SoundAux.value]
  have hc : (T.statistic.evalQ (r ((ω l).1, (ω l).2.2)) : ℝ) ≤ T.threshold ↔
      T.statistic.evalQ (r ((ω l).1, (ω l).2.2)) ≤ T.threshold := Rat.cast_le
  cases side <;> cases T.firstOnLeft <;> split_ifs <;> simp_all

private theorem tolerance_bounds (w η Δ : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hk : 1 ≤ k) (hΔ : 1 ≤ Δ)
    (hη : 0 < η ∧ η ≤ w ^ 2 / (10000 * k ^ 2 * Δ)) :
    η ≤ 1 / 100 ∧ η ≤ 1 / Δ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
  have hw2 : w ^ 2 ≤ 1 := by nlinarith only [hw, hw1]
  have hΔ0 : 0 < Δ := by linarith only [hΔ]
  have hden : 10000 * Δ ≤ 10000 * (k : ℝ) ^ 2 * Δ := by
    nlinarith only [mul_le_mul_of_nonneg_right hk2 hΔ0.le]
  have hden0 : 0 < 10000 * (k : ℝ) ^ 2 * Δ := by positivity
  have hηden := (le_div_iff₀ hden0).mp hη.2
  have hm := mul_le_mul_of_nonneg_left hden hη.1.le
  have hηΔ : η * Δ ≤ 1 / 10000 := by nlinarith only [hm, hηden, hw2]
  have hηsmall : η ≤ 1 / 100 := by
    nlinarith only [hηΔ, mul_le_mul_of_nonneg_left hΔ hη.1.le]
  exact ⟨hηsmall, (le_div_iff₀ hΔ0).mpr (by linarith only [hηΔ])⟩

private theorem recovery_budget (mode : Mode) (ε w η Δ : ℝ) (C : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hk : 1 ≤ k) (hC : 32 ≤ C) (he : 0 ≤ ε)
    (hΔ : 1 ≤ Δ) (hη : η ≤ 1 / Δ) :
    k * (pairError mode Δ + η) + 2 * (ε + η) / w ≤
      C * k / w * max ε (Δ ^ (-(1 / ((C : ℝ) * k)))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hC32 : (32 : ℝ) ≤ C := by exact_mod_cast hC
  have hCk : (32 : ℝ) ≤ C * k := by nlinarith only [hk1, hC32]
  have hCk0 : (0 : ℝ) < C * k := by linarith only [hCk]
  have hexp : -(1 / 8 : ℝ) ≤ -(1 / ((C : ℝ) * k)) := by
    rw [neg_le_neg_iff, div_le_div_iff₀ hCk0 (by norm_num)]
    linarith only [hCk]
  let S := max ε (Δ ^ (-(1 / ((C : ℝ) * k))))
  have hS : 0 ≤ S := he.trans (le_max_left _ _)
  have hpow : Δ ^ (-(1 / 8 : ℝ)) ≤ S :=
    (Real.rpow_le_rpow_of_exponent_le hΔ hexp).trans (le_max_right _ _)
  have hηS : η ≤ S := hη.trans (by
    rw [one_div, ← Real.rpow_neg_one]
    exact (Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num)).trans hpow)
  have herr : pairError mode Δ ≤ 16 * S := by
    cases mode with
    | centered => exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    | identical =>
      have hh : Δ ^ (-(2 : ℝ)) ≤ S :=
        (Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num)).trans hpow
      dsimp only [pairError]
      nlinarith only [hh, hS]
  have hfirst : k * (pairError mode Δ + η) ≤ 17 * k / w * S := by
    calc
      _ ≤ 17 * k * S := by
        nlinarith only [mul_le_mul_of_nonneg_left herr (by positivity : (0 : ℝ) ≤ k),
          mul_le_mul_of_nonneg_left hηS (by positivity : (0 : ℝ) ≤ k)]
      _ ≤ 17 * k / w * S := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hw]
        exact mul_le_of_le_one_right (by positivity) hw1
  have hsecond : 2 * (ε + η) / w ≤ 4 * k / w * S := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hw]
    have hεS : ε ≤ S := le_max_left _ _
    have hh : S ≤ k * S := by nlinarith only [mul_le_mul_of_nonneg_right hk1 hS]
    linarith only [hεS, hηS, hh]
  calc
    _ ≤ (17 * k / w * S) + (4 * k / w * S) := add_le_add hfirst hsecond
    _ = 21 * k / w * S := by ring
    _ ≤ C * k / w * S := by gcongr; linarith only [hC32]

/-- Uniform rounded windows turn pairwise population bounds into component recovery. -/
theorem recluster_recovers
    (mode : Mode) (build : TestBuilder) (hb : TestSpec build) (M : Mixture k d)
    (ε w η : ℝ) (Δ : ℚ) (D C : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (E : Fin k → Robust.Estimate d) (π : Equiv.Perm (Fin k)) (fuel : ℕ)
    (hM : M.Valid) (hm : mode.Condition M) (hs : mode.Separated M Δ)
    (hk : 1 ≤ k) (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j) (hC : 32 ≤ C)
    (he : 0 ≤ ε) (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hη : 0 < η ∧ η ≤ w ^ 2 / (10000 * k ^ 2 * Δ))
    (hΔ : (2 : ℝ) ^ 40 ≤ Δ) (hE : ∀ a, Robust.Accurate M (π a) (E a))
    (hn : (2 * radius d η + 2) / η ≤ n) :
    RecoversClusters (C * k / w * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))
      (labels ω) (recluster (fun a b ↦ build mode Δ (E a) (E b) fuel)
        (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) := by
  classical
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let tests := fun a b ↦ build mode Δ (E a) (E b) fuel
  let e := pairError mode Δ
  have he0 : 0 ≤ e := by cases mode <;> dsimp [e, pairError] <;> positivity
  have hw1 : w ≤ 1 := by
    let a : Fin k := ⟨0, by omega⟩
    exact (hwj a).trans (hM.sum_w ▸ Finset.single_le_sum
      (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ a))
  have hΔ1 : (1 : ℝ) ≤ Δ := (by norm_num : (1 : ℝ) ≤ 2 ^ 40).trans hΔ
  obtain ⟨hηsmall, hηΔ⟩ := tolerance_bounds w η Δ hw hw1 hk hΔ1 hη
  have hηgood : 0 < η ∧ η ≤ 1 / 100 := ⟨hη.1, hηsmall⟩
  have hbudget := recovery_budget mode ε w η Δ C hw hw1 hk hC he hΔ1 hηΔ
  have hout (l : Fin n) : outCluster (recluster tests x) l = label tests (x l) := by
    simp [outCluster, recluster]
  refine ⟨by simp [recluster], fun l ↦ by rw [hout]; exact label_lt tests (x l) hk,
    π, fun a ↦ ?_⟩
  let S := cluster (labels ω) (π a)
  let clean := S \ corrupted ω
  let bad := fun b ↦ clean.filter fun l ↦ wins tests a b (x l) ≠ true
  have hpair (b : Fin k) : ((bad b).card : ℝ) ≤ (e + η) * S.card := by
    by_cases hab : a < b
    · have hp := (hb mode M (π a) (π b) (E a) (E b) Δ fuel hM hm hs
        (π.injective.ne (ne_of_lt hab)) (hE a) (hE b) hΔ w η hw hwj hη.1.le hη.2).1
      have hh := empirical_test M ε w η D ω r hM hg hr hηgood hn (π a)
        (tests a b) true e hp
      simpa only [bad, clean, S, wins, hab, ite_true, x] using hh
    · by_cases hba : b < a
      · have hp := (hb mode M (π b) (π a) (E b) (E a) Δ fuel hM hm hs
          (π.injective.ne (ne_of_lt hba)) (hE b) (hE a) hΔ w η hw hwj hη.1.le hη.2).2
        have hh := empirical_test M ε w η D ω r hM hg hr hηgood hn (π a)
          (tests b a) false e hp
        convert hh using 2
        congr 1
        apply Finset.filter_congr
        intro l _
        simp [wins, hab, hba, x]
      · have hab' : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
        subst b
        have hz : bad a = ∅ := by simp [bad, wins]
        rw [hz, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (add_nonneg he0 hη.1.le) (Nat.cast_nonneg _)
  let B := Finset.univ.biUnion bad
  have hB : (B.card : ℝ) ≤ k * (e + η) * S.card := by
    calc
      _ ≤ ∑ b : Fin k, ((bad b).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := bad))
      _ ≤ ∑ _b : Fin k, (e + η) * S.card :=
        Finset.sum_le_sum fun b _ ↦ hpair b
      _ = _ := by simp [mul_assoc]
  let wrong := S.filter fun l ↦ label tests (x l) ≠ a
  have hsub : wrong ⊆ B ∪ corrupted ω := by
    intro l hl
    obtain ⟨hlS, hlwrong⟩ := Finset.mem_filter.mp hl
    by_cases hlbad : l ∈ corrupted ω
    · exact Finset.mem_union_right _ hlbad
    · apply Finset.mem_union_left
      have hex : ∃ b, wins tests a b (x l) ≠ true := by
        by_contra hb
        push Not at hb
        exact hlwrong (winner_label tests a (x l) hb)
      obtain ⟨b, hb⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hlS, hlbad⟩, hb⟩⟩
  have hwrong : (wrong.card : ℝ) ≤ k * (e + η) * S.card + (corrupted ω).card := by
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc' : (wrong.card : ℝ) ≤ B.card + (corrupted ω).card := by exact_mod_cast hc
    linarith only [hc', hB]
  have hn0 : (0 : ℝ) < n := by
    have hpos := SoundAux.good_cluster_pos M ε w η D ω hg (π a)
    have hle : S.card ≤ n := (Finset.card_le_card (Finset.subset_univ _)).trans_eq
      (Finset.card_fin n)
    exact Nat.cast_pos.mpr (hpos.trans_le hle)
  have hcount : w * n / 2 ≤ (S.card : ℝ) := by
    have hc := ((good_counts M ε w η D ω hg ⟨hη.1.le, hηsmall⟩).1 (π a)).1
    have hh := mul_le_mul_of_nonneg_right (hwj (π a)) hn0.le
    change _ ≤ (S.card : ℝ) at hc
    nlinarith only [hc, hh, mul_nonneg hw.le hn0.le]
  have hcorrupt : ((corrupted ω).card : ℝ) ≤ 2 * (ε + η) / w * S.card := by
    refine hg.2.1.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    nlinarith only [mul_le_mul_of_nonneg_left hcount
      (show 0 ≤ ε + η by linarith only [he, hη.1])]
  have hwrong' : (wrong.card : ℝ) ≤
      C * k / w * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))) * S.card := by
    have hh := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) S.card)
    dsimp only [e] at hwrong
    nlinarith only [hwrong, hcorrupt, hh]
  have hpartition : S.card = wrong.card +
      (((Finset.univ.filter fun l : Fin n ↦ outCluster (recluster tests x) l = a) ∩
        S).card) := by
    have hh := Finset.card_filter_add_card_filter_not (s := S)
      (fun l ↦ label tests (x l) ≠ a)
    have heq : (S.filter fun l ↦ ¬ label tests (x l) ≠ a) =
        (Finset.univ.filter fun l : Fin n ↦ outCluster (recluster tests x) l = a) ∩ S := by
      ext l
      simp [hout, and_comm]
    rw [heq] at hh
    exact hh.symm
  have hpartition' : (S.card : ℝ) = wrong.card +
      ((((Finset.univ.filter fun l : Fin n ↦ outCluster (recluster tests x) l = a) ∩
        S).card) : ℝ) := by exact_mod_cast hpartition
  change (1 - _) * (S.card : ℝ) ≤ _
  linarith only [hwrong', hpartition']

end

end ABBKS26.Select
