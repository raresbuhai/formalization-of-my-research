module

public import ABBKS26.Assembly.ExecRefineKernelsAuxRB3

/-! A finite rational scan preserving every empirical split and closed window. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.Thresholds

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- Representatives of the points and open cells cut out by a rational list.
The quadratic scan avoids sorting and includes both unbounded cells. -/
def cells (xs : List ℚ) : List ℚ :=
  [0] ++ xs ++ xs.map (· - 1) ++ xs.map (· + 1) ++
    xs.flatMap (fun a ↦ xs.map fun b ↦ (a + b) / 2)


@[fun_prop] theorem cells_polytime {α : Type} {input : α ↪ List Bool}
    {xs : α → List ℚ} (hx : ComputableInPolyTime xs input (encList encRat)) :
    ComputableInPolyTime (fun x ↦ cells (xs x)) input (encList encRat) := by
  unfold cells
  apply listAppend'
  · apply listAppend'
    · apply listAppend'
      · exact listAppend' (const [0]) hx
      · exact mapWithInput hx (rat_sub' (snd _ _) (const 1))
    · exact mapWithInput hx (rat_add' (snd _ _) (const 1))
  · apply flatMapWithInput hx
    apply mapWithInput (hx.comp (fst _ _))
    exact rat_div' (rat_add' ((snd _ _).comp (fst _ _)) (snd _ _)) (const 2)

private theorem same_cuts (xs : List ℚ) (t z : ℚ) (ht : t ∉ xs)
    (hl : ∀ s ∈ xs, s < t → s < z) (hr : ∀ s ∈ xs, t < s → z < s) :
    ∀ s ∈ xs, (s ≤ z ↔ s ≤ t) ∧ (z ≤ s ↔ t ≤ s) := by
  intro s hs
  have hne : s ≠ t := fun he ↦ ht (he ▸ hs)
  rcases lt_or_gt_of_ne hne with h | h
  · have hz := hl s hs h
    exact ⟨iff_of_true hz.le h.le, iff_of_false (not_le.mpr hz) (not_le.mpr h)⟩
  · have hz := hr s hs h
    exact ⟨iff_of_false (not_le.mpr hz) (not_le.mpr h), iff_of_true hz.le h.le⟩

/-- Every threshold has a representative with exactly the same weak comparisons to all
cut points. In particular, equality at a closed-window endpoint is preserved. -/
theorem cells_complete (xs : List ℚ) (t : ℚ) :
    ∃ z ∈ cells xs, ∀ s ∈ xs, (s ≤ z ↔ s ≤ t) ∧ (z ≤ s ↔ t ≤ s) := by
  classical
  by_cases ht : t ∈ xs
  · exact ⟨t, by simp [cells, ht], fun _ _ ↦ ⟨Iff.rfl, Iff.rfl⟩⟩
  let L := xs.toFinset.filter (· < t)
  let U := xs.toFinset.filter (t < ·)
  by_cases hL : L.Nonempty
  · let a := L.max' hL
    have ha : a ∈ xs ∧ a < t := by
      simpa only [L, Finset.mem_filter, List.mem_toFinset] using L.max'_mem hL
    have hmax (s : ℚ) (hs : s ∈ xs) (hst : s < t) : s ≤ a :=
      L.le_max' s (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩)
    by_cases hU : U.Nonempty
    · let b := U.min' hU
      have hb : b ∈ xs ∧ t < b := by
        simpa only [U, Finset.mem_filter, List.mem_toFinset] using U.min'_mem hU
      have hmin (s : ℚ) (hs : s ∈ xs) (hst : t < s) : b ≤ s :=
        U.min'_le s (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩)
      refine ⟨(a + b) / 2, ?_, same_cuts xs t _ ht ?_ ?_⟩
      · simp only [cells, List.mem_append, List.mem_singleton, List.mem_map,
          List.mem_flatMap]
        exact Or.inr ⟨a, ha.1, b, hb.1, rfl⟩
      · intro s hs hst
        have hh := hmax s hs hst
        linarith only [hh, ha.2, hb.2]
      · intro s hs hst
        have hh := hmin s hs hst
        linarith only [hh, ha.2, hb.2]
    · refine ⟨a + 1, ?_, same_cuts xs t _ ht ?_ ?_⟩
      · simp only [cells, List.mem_append, List.mem_singleton, List.mem_map]
        exact Or.inl (Or.inr ⟨a, ha.1, rfl⟩)
      · intro s hs hst
        have hh := hmax s hs hst
        linarith only [hh]
      · intro s hs hst
        exact (hU ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩⟩).elim
  · by_cases hU : U.Nonempty
    · let b := U.min' hU
      have hb : b ∈ xs ∧ t < b := by
        simpa only [U, Finset.mem_filter, List.mem_toFinset] using U.min'_mem hU
      have hmin (s : ℚ) (hs : s ∈ xs) (hst : t < s) : b ≤ s :=
        U.min'_le s (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩)
      refine ⟨b - 1, ?_, same_cuts xs t _ ht ?_ ?_⟩
      · simp only [cells, List.mem_append, List.mem_singleton, List.mem_map]
        exact Or.inl (Or.inl (Or.inr ⟨b, hb.1, rfl⟩))
      · intro s hs hst
        exact (hL ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩⟩).elim
      · intro s hs hst
        have hh := hmin s hs hst
        linarith only [hh]
    · refine ⟨0, by simp [cells], same_cuts xs t 0 ht ?_ ?_⟩
      · intro s hs hst
        exact (hL ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩⟩).elim
      · intro s hs hst
        exact (hU ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hst⟩⟩).elim

/-- A Frobenius window changes only when its threshold crosses one of these cut points. -/
def cuts (d : ℕ) (pts : Points) (N : List ℕ) (q : StatisticL) (W : ℚ) : List ℚ :=
  N.flatMap fun i ↦
    let v := evalL d q (pts.getD i [])
    [v, v - W, v + W]

def scan (d : ℕ) (pts : Points) (N : List ℕ) (q : StatisticL) (W : ℚ) : List ℚ :=
  cells (cuts d pts N q W)

def edge (h : ℕ) (N : List ℕ) (q : StatisticL) (W t : ℚ) : EdgeL :=
  (h, N, q, 1, t, t - W, t + W)


private theorem cuts_mem (d : ℕ) (pts : Points) (N : List ℕ) (q : StatisticL)
    (W : ℚ) (i : ℕ) (hi : i ∈ N) :
    let v := evalL d q (pts.getD i [])
    v ∈ cuts d pts N q W ∧ v - W ∈ cuts d pts N q W ∧ v + W ∈ cuts d pts N q W := by
  dsimp only
  exact ⟨List.mem_flatMap.mpr ⟨i, hi, by simp⟩,
    List.mem_flatMap.mpr ⟨i, hi, by simp⟩,
    List.mem_flatMap.mpr ⟨i, hi, by simp⟩⟩

/-- The finite scan preserves both the split and its closed window, even with ties. -/
theorem scan_complete (d : ℕ) (pts : Points) (h : ℕ) (N : List ℕ)
    (q : StatisticL) (W t : ℚ) :
    ∃ z ∈ scan d pts N q W,
      leftL d pts (edge h N q W z) = leftL d pts (edge h N q W t) ∧
      RB3.windowL d pts (edge h N q W z) = RB3.windowL d pts (edge h N q W t) := by
  obtain ⟨z, hz, hc⟩ := cells_complete (cuts d pts N q W) t
  refine ⟨z, hz, ?_, ?_⟩
  · apply List.filter_congr
    intro i hi
    exact decide_eq_decide.mpr (hc _ (cuts_mem d pts N q W i hi).1).1
  · apply List.filter_congr
    intro i hi
    apply decide_eq_decide.mpr
    have hlo := (hc _ (cuts_mem d pts N q W i hi).2.2).2
    have hhi := (hc _ (cuts_mem d pts N q W i hi).2.1).1
    change (z - W ≤ evalL d q (pts.getD i []) ∧
      evalL d q (pts.getD i []) ≤ z + W) ↔
        (t - W ≤ evalL d q (pts.getD i []) ∧ evalL d q (pts.getD i []) ≤ t + W)
    constructor
    · intro hv
      constructor
      · have hh := hlo.mp (by linarith only [hv.1])
        linarith only [hh]
      · have hh := hhi.mp (by linarith only [hv.2])
        linarith only [hh]
    · intro hv
      constructor
      · have hh := hlo.mpr (by linarith only [hv.1])
        linarith only [hh]
      · have hh := hhi.mpr (by linarith only [hv.2])
        linarith only [hh]

theorem verify_scan_complete (d n : ℕ) (pts : Points) (h : ℕ) (N : List ℕ)
    (q : StatisticL) (W t w mass : ℚ)
    (hv : RB3.verifyL d n w mass pts (edge h N q W t) = true) :
    ∃ z ∈ scan d pts N q W,
      RB3.verifyL d n w mass pts (edge h N q W z) = true := by
  obtain ⟨z, hz, hl, hw⟩ := scan_complete d pts h N q W t
  refine ⟨z, hz, ?_⟩
  unfold RB3.verifyL RB3.rightL at hv ⊢
  rw [hl, hw]
  exact hv

@[fun_prop] theorem scan_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {N : α → List ℕ}
    {q : α → StatisticL} {W : α → ℚ}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime pts input encPoints)
    (hN : ComputableInPolyTime N input encIndices)
    (hq : ComputableInPolyTime q input encStatistic)
    (hW : ComputableInPolyTime W input encRat) :
    ComputableInPolyTime (fun x ↦ scan (d x) (pts x) (N x) (q x) (W x))
      input (encList encRat) := by
  unfold scan
  apply cells_polytime
  unfold cuts
  apply flatMapWithInput hN
  have hv : ComputableInPolyTime (fun a : α × ℕ ↦
      evalL (d a.1) (q a.1) ((pts a.1).getD a.2 []))
      (encPair input encNat) encRat := by
    apply eval_polytime (hd.comp (fst _ _)) (hq.comp (fst _ _))
    exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector) []
      (hp.comp (fst _ _)).tidy (snd _ _).tidy)
  exact cons' hv (cons' (rat_sub' hv (hW.comp (fst _ _)))
    (cons' (rat_add' hv (hW.comp (fst _ _))) (const [])))

/-- The list scan retains every representative; verification belongs to the packing loop. -/
def rawL (d : ℕ) (pts : Points) (h : ℕ) (N : List ℕ) (q : StatisticL)
    (W : ℚ) : List EdgeL :=
  (scan d pts N q W).map (edge h N q W)

def typedEdge {n d : ℕ} (h : ℕ) (N : Finset (Fin n)) (q : Statistic d)
    (W t : ℚ) : Edge n d :=
  ⟨h, N, q, .frobenius, t, t - W, t + W⟩

def raw {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (q : Statistic d) (W : ℚ) : List (Edge n d) :=
  (scan d pts (indexList N) (statisticList q) W).map (typedEdge h N q W)

theorem raw_agrees {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (q : Statistic d) (W : ℚ) :
    rawL d pts h (indexList N) (statisticList q) W =
      (raw pts h N q W).map edgeList := by
  simp only [rawL, raw, List.map_map]
  rfl

theorem raw_provenance {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (q : Statistic d) (W : ℚ) :
    ∀ e ∈ raw pts h N q W,
      e.parent = N ∧ e.depth = h ∧ e.statistic = q ∧ e.kind = .frobenius := by
  intro e he
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp he
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem raw_scaleValid {n k d : ℕ} (M : Mixture k d) (I : Finset (Fin k))
    (p : StepParams) (pts : Points) (h : ℕ) (N : Finset (Fin n)) (q : Statistic d)
    (hW : 0 ≤ p.WF) (hmass : (p.windowMass : ℝ) ≤ 1 / 2)
    (hvar : ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / (p.w : ℝ)) ^ 2) :
    ∀ e ∈ raw pts h N q p.WF, ScaleValid M I p e := by
  intro e he
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp he
  exact ⟨sub_le_self _ hW, le_add_of_nonneg_right hW, hmass, rfl, rfl, hvar⟩

/-- An arbitrary rational geometric witness can be replaced by an enumerated threshold
without changing its empirical verification result. -/
theorem raw_complete {n d : ℕ} (p : StepParams) (pts : Points) (h : ℕ)
    (N : Finset (Fin n)) (q : Statistic d) (t : ℚ)
    (hv : Verify p (fun l ↦ vectorOf d (pts.getD l.val []))
      (typedEdge h N q p.WF t)) :
    ∃ e ∈ raw pts h N q p.WF,
      Verify p (fun l ↦ vectorOf d (pts.getD l.val [])) e := by
  have ht : RB3.verifyL d n p.w p.verifyMass pts
      (edge h (indexList N) (statisticList q) p.WF t) = true := by
    change RB3.verifyL d n p.w p.verifyMass pts
      (edgeList (typedEdge h N q p.WF t)) = true
    rw [RB3.verify_agrees]
    exact decide_eq_true hv
  obtain ⟨z, hz, hvz⟩ := verify_scan_complete d n pts h (indexList N)
    (statisticList q) p.WF t p.w p.verifyMass ht
  refine ⟨typedEdge h N q p.WF z, List.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
  change RB3.verifyL d n p.w p.verifyMass pts
    (edgeList (typedEdge h N q p.WF z)) = true at hvz
  rw [RB3.verify_agrees] at hvz
  exact of_decide_eq_true hvz

@[fun_prop] theorem raw_polytime {α : Type} {input : α ↪ List Bool}
    {d h : α → ℕ} {pts : α → Points} {N : α → List ℕ}
    {q : α → StatisticL} {W : α → ℚ}
    (hd : ComputableInPolyTime d input encUnary)
    (hh : ComputableInPolyTime h input encNat)
    (hp : ComputableInPolyTime pts input encPoints)
    (hN : ComputableInPolyTime N input encIndices)
    (hq : ComputableInPolyTime q input encStatistic)
    (hW : ComputableInPolyTime W input encRat) :
    ComputableInPolyTime (fun x ↦ rawL (d x) (pts x) (h x) (N x) (q x) (W x))
      input (encList encEdge) := by
  unfold rawL
  apply mapWithInput (scan_polytime hd hp hN hq hW)
  unfold edge
  fun_prop

/-- Eligibility stays paired with its own certificate throughout the scan. -/
def poolL (d : ℕ) (pts : Points) (h : ℕ) (N : List ℕ)
    (qs : List (StatisticL × Bool)) (W : ℚ) : List EdgeL :=
  qs.flatMap fun q ↦ if q.2 then rawL d pts h N q.1 W else []

def pool {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (qs : List (Statistic d × Bool)) (W : ℚ) : List (Edge n d) :=
  qs.flatMap fun q ↦ if q.2 then raw pts h N q.1 W else []

theorem pool_agrees {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (qs : List (Statistic d × Bool)) (W : ℚ) :
    poolL d pts h (indexList N) (qs.map fun q ↦ (statisticList q.1, q.2)) W =
      (pool pts h N qs W).map edgeList := by
  simp only [poolL, pool, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  cases q.2
  · simp only [Bool.false_eq_true, ite_false, List.map_nil]
  · simp only [ite_true, raw_agrees]

theorem pool_mem {n d : ℕ} (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (qs : List (Statistic d × Bool)) (W : ℚ) (e : Edge n d) :
    e ∈ pool pts h N qs W ↔ ∃ q, (q, true) ∈ qs ∧ e ∈ raw pts h N q W := by
  simp only [pool, List.mem_flatMap]
  constructor
  · rintro ⟨⟨q, b⟩, hq, he⟩
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.not_mem_nil] at he
    · exact ⟨q, hq, he⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨(q, true), hq, he⟩


/-- Every eligible certificate with a verified rational threshold contributes a verified
member, independently of how that threshold was obtained in the geometric proof. -/
theorem pool_complete {n d : ℕ} (p : StepParams) (pts : Points) (h : ℕ)
    (N : Finset (Fin n)) (qs : List (Statistic d × Bool)) (q : Statistic d) (t : ℚ)
    (hq : (q, true) ∈ qs)
    (hv : Verify p (fun l ↦ vectorOf d (pts.getD l.val []))
      (typedEdge h N q p.WF t)) :
    ∃ e ∈ pool pts h N qs p.WF,
      Verify p (fun l ↦ vectorOf d (pts.getD l.val [])) e := by
  obtain ⟨e, he, hv⟩ := raw_complete p pts h N q t hv
  exact ⟨e, (pool_mem pts h N qs p.WF e).mpr ⟨q, hq, he⟩, hv⟩

@[fun_prop] theorem pool_polytime {α : Type} {input : α ↪ List Bool}
    {d h : α → ℕ} {pts : α → Points} {N : α → List ℕ}
    {qs : α → List (StatisticL × Bool)} {W : α → ℚ}
    (hd : ComputableInPolyTime d input encUnary)
    (hh : ComputableInPolyTime h input encNat)
    (hp : ComputableInPolyTime pts input encPoints)
    (hN : ComputableInPolyTime N input encIndices)
    (hq : ComputableInPolyTime qs input (encList (encPair encStatistic encBool)))
    (hW : ComputableInPolyTime W input encRat) :
    ComputableInPolyTime (fun x ↦ poolL (d x) (pts x) (h x) (N x) (qs x) (W x))
      input (encList encEdge) := by
  unfold poolL
  apply flatMapWithInput hq
  apply ite_decide (by fun_prop)
  · exact raw_polytime (hd.comp (fst _ _)) (hh.comp (fst _ _)) (hp.comp (fst _ _))
      (hN.comp (fst _ _)) (by fun_prop) (hW.comp (fst _ _))
  · exact const []

/-- The finite scan and the existing RB3 loop construct compatible typed and list outputs. -/
theorem packed_pool_agrees {n d : ℕ} (p : StepParams) (pts : Points) (k h : ℕ)
    (N : Finset (Fin n)) (qs : List (Statistic d × Bool)) :
    RB3.run d n p.w p.verifyMass pts k
      (poolL d pts h (indexList N) (qs.map fun q ↦ (statisticList q.1, q.2)) p.WF) =
      (frobSplits p k (fun l ↦ vectorOf d (pts.getD l.val []))
        (pool pts h N qs p.WF)).map edgeList := by
  rw [pool_agrees, RB3.run_agrees]

/-- Packing preserves provenance, scales and verification, and cannot erase a witness. -/
theorem packed_pool_spec {n k d : ℕ} (M : Mixture k d) (I : Finset (Fin k))
    (p : StepParams) (pts : Points) (h : ℕ) (N : Finset (Fin n))
    (qs : List (Statistic d × Bool))
    (hW : 0 ≤ p.WF) (hmass : (p.windowMass : ℝ) ≤ 1 / 2)
    (hvar : ∀ q, (q, true) ∈ qs → ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / (p.w : ℝ)) ^ 2) :
    let x := fun l : Fin n ↦ vectorOf d (pts.getD l.val [])
    let out := frobSplits p k x (pool pts h N qs p.WF)
    out.length ≤ frobCap k ∧
      (∀ e ∈ out, e.parent = N ∧ e.depth = h ∧ ScaleValid M I p e ∧ Verify p x e) ∧
      ((∃ q, (q, true) ∈ qs ∧ ∃ t, Verify p x (typedEdge h N q p.WF t)) →
        ∃ e ∈ out, Verify p x e) := by
  dsimp only
  let x := fun l : Fin n ↦ vectorOf d (pts.getD l.val [])
  let out := frobSplits p k x (pool pts h N qs p.WF)
  have hv : ∀ e ∈ out, e ∈ pool pts h N qs p.WF ∧ Verify p x e :=
    frobSplits_verified p k x _
  refine ⟨frobSplits_bound p k x _, ?_, ?_⟩
  · intro e he
    obtain ⟨q, hq, heq⟩ := (pool_mem pts h N qs p.WF e).mp (hv e he).1
    have hp := raw_provenance pts h N q p.WF e heq
    exact ⟨hp.1, hp.2.1, raw_scaleValid M I p pts h N q hW hmass (hvar q hq) e heq,
      (hv e he).2⟩
  · rintro ⟨q, hq, t, ht⟩
    have hne : out ≠ [] := frobSplits_complete p k x _ (pool_complete p pts h N qs q t hq ht)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil out hne
    exact ⟨e, he, (hv e he).2⟩

end ABBKS26.Assembly.Exec.RefineSynth.Thresholds
