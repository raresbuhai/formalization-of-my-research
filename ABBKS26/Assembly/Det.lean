module

public import ABBKS26.Assembly.Alg

/-!
# Deterministic recovery on the good event

On the one measurable good event of `ABBKS26.Tree.Good`, the deterministic pipeline recovers
every component, for every rounding of the points and every corruption; and the scheduled
sample size makes the good event likely.
-/

@[expose] public section

namespace ABBKS26.Assembly

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree Select MeasureTheory

private theorem component_count_pos {k d : ℕ} (M : Mixture k d) (hM : M.Valid) :
    1 ≤ k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  have hs := hM.sum_w
  simp [hk0] at hs

private theorem weight_sum_le {k d : ℕ} (M : Mixture k d) (w : ℚ)
    (hM : M.Valid) (hwj : ∀ i, (w : ℝ) ≤ M.w i) : (k : ℚ) * w ≤ 1 := by
  have hs : (k : ℝ) * w ≤ 1 := by
    calc
      (k : ℝ) * w = ∑ _ : Fin k, (w : ℝ) := by simp
      _ ≤ ∑ i : Fin k, M.w i := Finset.sum_le_sum (fun i _ ↦ hwj i)
      _ = 1 := hM.sum_w
  exact_mod_cast hs

private theorem replicate_recovers {k n : ℕ} (hk : k = 1) (ℓ : Fin n → Fin k)
    (η : ℝ) (hη : 0 ≤ η) : RecoversClusters η ℓ (List.replicate n 0) := by
  subst k
  have hout (j : Fin n) : outCluster (List.replicate n 0) j = 0 := by
    simp [outCluster, List.getD_eq_getElem?_getD]
  refine ⟨by simp, fun j ↦ by rw [hout]; omega, Equiv.refl _, fun i ↦ ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  simp only [hi, Equiv.refl_apply, hout, Fin.val_zero, Finset.filter_true,
    Finset.univ_inter]
  nlinarith only [hη, Nat.cast_nonneg (α := ℝ) (cluster ℓ 0).card]

private theorem foldl_min_le (xs : List ℚ) (q : ℚ) : xs.foldl min q ≤ q := by
  induction xs generalizing q with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih _).trans (min_le_left _ _)

private theorem analysis_eta_bounds {k d : ℕ} (mode : Mode) (M : Mixture k d)
    (w Δ : ℚ) (hM : M.Valid) (hw : 0 < w) (hwj : ∀ i, (w : ℝ) ≤ M.w i)
    (hΔ : Schedule.f mode (1 / w) ≤ Δ) :
    0 < Schedule.analysisEta mode w Δ k ∧
      Schedule.analysisEta mode w Δ k ≤ 1 / 100 := by
  have hk := component_count_pos M hM
  have hkw := weight_sum_le M w hM hwj
  have hreq : 0 < Schedule.etaReq mode w k := by
    by_cases hk2 : 2 ≤ k
    · have hw2 : w ≤ 1 / 2 := by
        have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk2
        nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
      exact (Schedule.schedule_valid mode w k ⟨hw, hw2⟩ hk2 hkw).1
    · have hk1 : k = 1 := by omega
      simp only [Schedule.etaReq, hk1, Nat.sub_self, List.range_zero, List.map_nil,
        List.foldl_nil, Schedule.params, Function.iterate_zero_apply]
      dsimp only [Schedule.terminal]
      split_ifs <;> positivity
  have hsmall : Schedule.etaReq mode w k ≤ 1 / 100 := by
    apply (foldl_min_le _ _).trans
    exact ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))).trans (by norm_num)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hΔR : (0 : ℝ) < Δ :=
    zero_lt_one.trans_le ((Schedule.f_ge_one mode _).trans hΔ)
  have hreqR : (0 : ℝ) < Schedule.etaReq mode w k := by exact_mod_cast hreq
  refine ⟨lt_min hreqR (by positivity), (min_le_left _ _).trans ?_⟩
  have hh : (Schedule.etaReq mode w k : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hsmall
  norm_num at hh
  exact hh

private theorem rounding_sample_bound {k d n : ℕ} (w η δ : ℝ) (D : ℕ)
    (hη : 0 < η ∧ η ≤ 1 / 100) (hn : sampleNeed w η δ k d D ≤ n) :
    (2 * radius d η + 2) / η ≤ n := by
  have hsample : 32 * (d + 1 : ℝ) / η ^ 2 ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hη1 : η ≤ 1 := by linarith only [hη.2]
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg d) hη.1.le)
  have hroot : η * Real.sqrt (d / η) ≤ d + 1 := by
    have hsq : (η * Real.sqrt (d / η)) ^ 2 = η * d := by
      rw [mul_pow, hs]
      field_simp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hηd : η * d ≤ d := mul_le_of_le_one_left hd hη1
    have hnonneg : 0 ≤ η * Real.sqrt (d / η) :=
      mul_nonneg hη.1.le (Real.sqrt_nonneg _)
    nlinarith only [hsq, hηd, hd, hnonneg, sq_nonneg (d : ℝ)]
  have hnum : (2 * radius d η + 2) * η ≤ 32 * (d + 1 : ℝ) := by
    unfold radius
    nlinarith only [hroot, hη1, Nat.cast_nonneg (α := ℝ) d]
  apply le_trans ?_ hsample
  rw [div_le_div_iff₀ hη.1 (sq_pos_of_pos hη.1)]
  nlinarith only [mul_le_mul_of_nonneg_right hnum hη.1.le]

private theorem dim_vectors {n d : ℕ} (x : Fin n → Fin d → ℚ) (hn : 0 < n) :
    dim (List.ofFn fun l ↦ List.ofFn (x l)) = d := by
  cases n with
  | zero => omega
  | succ n => simp only [dim, List.ofFn_succ, List.headD_cons, List.length_ofFn]

private theorem execute_on_vectors {n d : ℕ} (P : Program) (mode : Mode)
    (k : ℕ) (w Δ δ : ℚ) (x : Fin n → Fin d → ℚ) (fuel : ℕ)
    (hn : 0 < n) (hk : ¬ k ≤ 1) :
    execute P mode ⟨k, w, Δ, δ, List.ofFn fun l ↦ List.ofFn (x l)⟩ fuel =
      let params := Schedule.params mode w k
      match select params x (learnAll P.learn mode x fuel
          (leaves P.refine mode k params x fuel)) with
      | none => List.replicate n 0
      | some L =>
        if L.estimates.length ≠ k ∨ L.estimates.any Option.isNone then List.replicate n 0
        else
          let E := fun a : Fin k ↦ (L.estimates[a.val]?.bind id).getD (defaultEstimate d)
          recluster (fun a b ↦ P.tests mode Δ (E a) (E b) fuel) x := by
  have hlength : (List.ofFn fun l ↦ List.ofFn (x l)).length = n := List.length_ofFn
  have hdimension := dim_vectors x hn
  generalize hpoints : (List.ofFn fun l ↦ List.ofFn (x l)) = points at *
  subst n d
  have hread : (fun l : Fin points.length ↦ fun i : Fin (dim points) ↦
      (points[l]).getD i 0) = x := by
    funext l i
    have hrow : points.getD l [] = List.ofFn (x l) := by
      have hh := congrArg (fun ys : Points ↦ ys.getD l []) hpoints.symm
      simpa [List.getD_eq_getElem?_getD, l.isLt] using hh
    rw [Fin.getElem_fin, ← List.getD_eq_getElem points [] l.isLt, hrow]
    simp [i.isLt]
  simp only [execute, ite_eq_right hk, hread, id]
  rfl

/-- On the common good event the complete deterministic pipeline recovers every component. -/
theorem deterministic
    {k d n : ℕ} (mode : Mode) (budget : Input → ℕ)
    (hb : ∀ x, WellFormed x → budgetNeed mode x ≤ budget x)
    (C : ℕ) (hC : 32 ≤ C) (M : Mixture k d) (w Δ δ : ℚ)
    (hM : M.Valid) (hm : mode.Condition M) (hw : 0 < w)
    (hwj : ∀ i, (w : ℝ) ≤ M.w i) (hΔ : Schedule.f mode (1 / w) ≤ Δ)
    (hs : mode.Separated M Δ) (hδ : 0 < δ)
    (ε : ℝ) (he : 0 ≤ ε) (he' : ε ≤ 1 / Schedule.f mode (1 / w))
    (hn : Schedule.SampleReady mode k d n w Δ δ)
    (r : Rounding k d) (hr : IsRounding M (1 / n) r)
    (ω : Fin n → Triple k d)
    (hg : Good M ε w (Schedule.analysisEta mode w Δ k) (Schedule.momentDegree mode w) ω)
    (coins : List Bool) :
    RecoversClusters (C * k / w * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))
      (labels ω) (algorithm mode budget (⟨k, w, Δ, δ, roundedSample r ω⟩, coins)) := by
  classical
  have hk := component_count_pos M hM
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  by_cases hk1 : k ≤ 1
  · have hout : algorithm mode budget (⟨k, w, Δ, δ, roundedSample r ω⟩, coins) =
        List.replicate n 0 := by
      simpa only [algorithm, roundedSample, List.length_ofFn] using
        (program_spec mode).2.2.2.2.2
          ⟨k, w, Δ, δ, roundedSample r ω⟩ (budget _) hk1
    rw [hout]
    exact replicate_recovers (by omega) (labels ω) _ (by positivity)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hp, hsep, hη0, hηle⟩ := Schedule.prepared_sample mode M w Δ δ ε ω r
    hM hm hs hk2 hw hwj hΔ ⟨he, he'⟩ hn hg hr
  let η := Schedule.analysisEta mode w Δ k
  let D := Schedule.momentDegree mode w
  let params := Schedule.params mode w k
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let input : Input := ⟨k, w, Δ, δ, roundedSample r ω⟩
  let fuel := budget input
  have hn0 : 0 < n := by
    have hc := SoundAux.good_cluster_pos M ε w η D ω hg ⟨0, by omega⟩
    exact hc.trans_le ((Finset.card_le_card (Finset.subset_univ _)).trans_eq
      (Finset.card_fin n))
  have hdim : dim input.points = d := dim_vectors x hn0
  have hlen : input.points.length = n := List.length_ofFn
  have hkw := weight_sum_le M w hM hwj
  have hw1 : w ≤ 1 := by
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
  have hinput : WellFormed input := by
    refine ⟨hw, hw1, hkw, hk, hδ, ?_⟩
    intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    rw [hdim]
    exact List.length_ofFn
  have hf : localBudget mode k n d params ≤ fuel := by
    apply le_trans ?_ (hb input hinput)
    dsimp only [budgetNeed]
    rw [ite_eq_right (show ¬ input.k ≤ 1 by change ¬ k ≤ 1; omega), hlen, hdim]
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨href, hlearn, htests, _⟩ := program_spec mode
  obtain ⟨L, hselect, π, hπ⟩ := accepted_complete (program mode).refine
    (program mode).learn href hlearn mode M ε w η Δ D ω r params fuel hk2 hp hf
  change select (Schedule.params mode w k) x
    (learnAll (program mode).learn mode x fuel
      (leaves (program mode).refine mode k (Schedule.params mode w k) x fuel)) =
        some L at hselect
  choose E hget hacc using hπ
  have hmem : L ∈ learnAll (program mode).learn mode x fuel
      (leaves (program mode).refine mode k params x fuel) :=
    List.mem_of_find?_eq_some hselect
  have hlength : L.estimates.length = k := by
    obtain ⟨candidate, hc, rfl⟩ := List.mem_map.mp hmem
    simpa only [List.length_map] using
      (leaf_history (program mode).refine href mode k params x fuel candidate hc).1
  have hest : L.estimates = List.ofFn (fun a : Fin k ↦ some (E a)) := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · simpa only [List.getElem?_ofFn, dite_eq_left hi] using hget ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_ofFn, dite_eq_right hi]
  have hnone : L.estimates.any Option.isNone = false := by
    rw [hest, List.any_eq_false]
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    simp
  have hexecute : execute (program mode) mode input fuel =
      recluster (fun a b ↦ (program mode).tests mode Δ (E a) (E b) fuel) x := by
    change execute (program mode) mode
      ⟨k, w, Δ, δ, List.ofFn fun l ↦ List.ofFn (x l)⟩ fuel = _
    rw [execute_on_vectors (program mode) mode k w Δ δ x fuel hn0 hk1]
    dsimp only
    rw [hselect]
    simp only [hlength, ne_eq, not_true_eq_false, hnone, Bool.false_eq_true, or_self,
      ite_false]
    simp only [hget, Option.bind_some, id_eq, Option.getD_some]
  rw [algorithm_on_sample mode budget M w Δ δ ω r coins hM hw hwj hδ hb]
  rw [hexecute]
  exact recluster_recovers mode (program mode).tests htests M ε w η Δ D C ω r E π fuel
    hM hm hs hk hwR hwj hC he hg hr ⟨hη0, hηle.trans (min_le_right _ _)⟩ hsep hacc
    (rounding_sample_bound w η δ D ⟨hη0, hηle.trans (min_le_left _ _)⟩ hn.2.1)


/-- The scheduled probability parameters satisfy the existing good-event bound. -/
theorem probability_setup
    {k d : ℕ} (mode : Mode) (M : Mixture k d) (w Δ δ : ℚ) (ε : ℝ)
    (P : Measure (Triple k d)) (hM : M.Valid) (hw : 0 < w)
    (hwj : ∀ i, (w : ℝ) ≤ M.w i) (hΔ : Schedule.f mode (1 / w) ≤ Δ)
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) (he : 0 ≤ ε)
    (he' : ε ≤ 1 / Schedule.f mode (1 / w)) (hP : IsCorruption M ε P)
    (n : ℕ) (hn : Schedule.SampleReady mode k d n w Δ δ) :
    (Measure.pi fun _ : Fin n ↦ P).real
      {ω | ¬ Good M ε w (Schedule.analysisEta mode w Δ k) (Schedule.momentDegree mode w) ω}
      ≤ δ := by
  have hε1 : ε ≤ 1 := he'.trans (by
    exact (div_le_one (zero_lt_one.trans_le (Schedule.f_ge_one mode _))).mpr
      (Schedule.f_ge_one mode _))
  have hD : 4 ≤ Schedule.momentDegree mode w := by
    cases mode with
    | centered => simp [Schedule.momentDegree]
    | identical => change 4 ≤ 8 * (logInv w + 3); omega
  exact good_probability M P ε w (Schedule.analysisEta mode w Δ k) δ
    (Schedule.momentDegree mode w) hM hP ⟨he, hε1⟩ (by exact_mod_cast hw) hwj
    (analysis_eta_bounds mode M w Δ hM hw hwj hΔ) ⟨by exact_mod_cast hδ, hδ1⟩ hD hn.2.1

end

end ABBKS26.Assembly
