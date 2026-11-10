module

public import BHSV25.Net.Resid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.List.GetD

/-!
# Greedy column selection

The greedy net (`BHSV25/Net/GSMachine.lean`) spans an eigenspace by a few columns of a spectral
filter, chosen greedily: in each of `T` rounds, the column whose residual against the columns
chosen so far is longest (pivoted Gram–Schmidt). The machine compares the Gram determinants
`det Gram(S ∪ {v}) = det Gram(S) · ‖resid_S(v)‖²` instead of the residuals.

* `BHSV25.Net.argmaxPos`, `BHSV25.Net.greedySel`: the first maximizer of a positive score, and
  `T` rounds of greedy selection, for scores in any linear order (integers for the machine, reals
  for the analysis). Selections agree for scores that compare the same way
  (`BHSV25.Net.greedySel_congr`).
* `BHSV25.Net.backsubst`: back substitution in a unit upper triangular system with entries at most
  `1`, which multiplies the error by at most `2^k - 1`.
* `BHSV25.Net.greedy_resid_le`: **after `T` rounds, every column has residual at most
  `(2^(T+1) - 1) ℓ`** when the columns are `aᵥ + bᵥ` with every `aᵥ` in a space of dimension at
  most `T` and the map `eᵥ ↦ bᵥ` of norm at most `ℓ`. The `T + 1` columns made of the chosen ones
  and the worst one have dependent `a`-parts; in the Gram–Schmidt coordinates of the chosen
  columns their dependency is a triangular system whose diagonal entries are the residuals, at
  least the last one, and whose other entries are at most the diagonal ones (greedy choice).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix

/-! ### The first maximizer of a positive score -/

section ArgMax

variable {α : Type*} [LinearOrder α] [Zero α]

/-- One step of the search for the first maximizer of a positive score. -/
def argStep (f : ℕ → α) (acc : Option ℕ) (v : ℕ) : Option ℕ :=
  match acc with
  | none => if 0 < f v then some v else none
  | some u => if f u < f v then some v else some u

/-- The first `v < N` with the largest score, if some score is positive. -/
def argmaxPos (N : ℕ) (f : ℕ → α) : Option ℕ := (List.range N).foldl (argStep f) none

theorem argmaxPos_succ (N : ℕ) (f : ℕ → α) :
    argmaxPos (N + 1) f = argStep f (argmaxPos N f) N := by
  rw [argmaxPos, argmaxPos, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The invariant of the search. -/
theorem argmaxPos_spec (N : ℕ) (f : ℕ → α) :
    (argmaxPos N f = none → ∀ u < N, f u ≤ 0) ∧
      ∀ v, argmaxPos N f = some v → v < N ∧ 0 < f v ∧ ∀ u < N, f u ≤ f v := by
  induction N with
  | zero => exact ⟨fun _ u hu ↦ absurd hu (Nat.not_lt_zero u), fun v h ↦ by simp [argmaxPos] at h⟩
  | succ N ih =>
    rw [argmaxPos_succ]
    rcases hN : argmaxPos N f with _ | w
    · have h0 := ih.1 hN
      by_cases hp : 0 < f N
      · simp only [argStep, hp, ite_true, reduceCtorEq, false_imp_iff, true_and]
        intro v hv
        cases hv
        refine ⟨Nat.lt_succ_self _, hp, fun u hu ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact (h0 u hu).trans hp.le
        · exact le_rfl
      · simp only [argStep, hp, ite_false, reduceCtorEq, false_imp_iff, implies_true, and_true,
          forall_const]
        intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact h0 u hu
        · exact not_lt.1 hp
    · obtain ⟨hw, hpos, hmax⟩ := ih.2 w hN
      by_cases hlt : f w < f N
      · simp only [argStep, hlt, ite_true, reduceCtorEq, false_imp_iff, true_and]
        intro v hv
        cases hv
        refine ⟨Nat.lt_succ_self _, hpos.trans hlt, fun u hu ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact (hmax u hu).trans hlt.le
        · exact le_rfl
      · simp only [argStep, hlt, ite_false, reduceCtorEq, false_imp_iff, true_and]
        intro v hv
        cases hv
        refine ⟨Nat.lt_succ_of_lt hw, hpos, fun u hu ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact hmax u hu
        · exact not_lt.1 hlt

theorem argmaxPos_none {N : ℕ} {f : ℕ → α} (h : argmaxPos N f = none) : ∀ u < N, f u ≤ 0 :=
  (argmaxPos_spec N f).1 h

theorem argmaxPos_some {N : ℕ} {f : ℕ → α} {v : ℕ} (h : argmaxPos N f = some v) :
    v < N ∧ 0 < f v ∧ ∀ u < N, f u ≤ f v :=
  (argmaxPos_spec N f).2 v h

/-- Scores that compare the same way have the same first maximizer. -/
theorem argmaxPos_congr {β : Type*} [LinearOrder β] [Zero β] {N : ℕ} {f : ℕ → α} {g : ℕ → β}
    (hpos : ∀ v < N, (0 < f v ↔ 0 < g v)) (hlt : ∀ u < N, ∀ v < N, (f u < f v ↔ g u < g v)) :
    argmaxPos N f = argmaxPos N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have ih' := ih (fun v hv ↦ hpos v (Nat.lt_succ_of_lt hv))
      (fun u hu v hv ↦ hlt u (Nat.lt_succ_of_lt hu) v (Nat.lt_succ_of_lt hv))
    rw [argmaxPos_succ, argmaxPos_succ, ih']
    rcases h : argmaxPos N g with _ | w
    · simp only [argStep, hpos N (Nat.lt_succ_self N)]
    · have hw := (argmaxPos_some h).1
      simp only [argStep, hlt w (Nat.lt_succ_of_lt hw) N (Nat.lt_succ_self N)]

end ArgMax

/-! ### Greedy selection -/

section Select

variable {α : Type*} [LinearOrder α] [Zero α]

/-- One round: append the first maximizer of the score, if some score is positive. -/
def greedyStep (N : ℕ) (score : List ℕ → ℕ → α) (S : List ℕ) : List ℕ :=
  match argmaxPos N (score S) with
  | none => S
  | some v => S ++ [v]

/-- The list chosen in the first `t` rounds. -/
def greedySeq (N : ℕ) (score : List ℕ → ℕ → α) (t : ℕ) : List ℕ := (greedyStep N score)^[t] []

/-- **Greedy selection**: `T` rounds. -/
def greedySel (N T : ℕ) (score : List ℕ → ℕ → α) : List ℕ := greedySeq N score T

theorem greedySeq_succ (N : ℕ) (score : List ℕ → ℕ → α) (t : ℕ) :
    greedySeq N score (t + 1) = greedyStep N score (greedySeq N score t) :=
  Function.iterate_succ_apply' _ _ _

theorem greedyStep_of_none {N : ℕ} {score : List ℕ → ℕ → α} {S : List ℕ}
    (h : argmaxPos N (score S) = none) : greedyStep N score S = S := by
  simp [greedyStep, h]

theorem greedyStep_of_some {N : ℕ} {score : List ℕ → ℕ → α} {S : List ℕ} {v : ℕ}
    (h : argmaxPos N (score S) = some v) : greedyStep N score S = S ++ [v] := by
  simp [greedyStep, h]

theorem length_greedySeq_le (N : ℕ) (score : List ℕ → ℕ → α) (t : ℕ) :
    (greedySeq N score t).length ≤ t := by
  induction t with
  | zero => simp [greedySeq]
  | succ t ih =>
    rw [greedySeq_succ]
    rcases h : argmaxPos N (score (greedySeq N score t)) with _ | v
    · rw [greedyStep_of_none h]; omega
    · rw [greedyStep_of_some h, List.length_append, List.length_singleton]; omega

theorem greedySeq_prefix (N : ℕ) (score : List ℕ → ℕ → α) {t t' : ℕ} (h : t ≤ t') :
    greedySeq N score t <+: greedySeq N score t' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    rw [greedySeq_succ]
    rcases hs : argmaxPos N (score (greedySeq N score _)) with _ | v
    · rw [greedyStep_of_none hs]
    · rw [greedyStep_of_some hs]
      exact List.prefix_append _ _

/-- Selections with scores that compare the same way on every list agree. -/
theorem greedySel_congr {β : Type*} [LinearOrder β] [Zero β] {N T : ℕ}
    {f : List ℕ → ℕ → α} {g : List ℕ → ℕ → β}
    (hpos : ∀ S, ∀ v < N, (0 < f S v ↔ 0 < g S v))
    (hlt : ∀ S, ∀ u < N, ∀ v < N, (f S u < f S v ↔ g S u < g S v)) :
    greedySel N T f = greedySel N T g := by
  unfold greedySel
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [greedySeq_succ, greedySeq_succ, ih]
    simp only [greedyStep, argmaxPos_congr (hpos _) (hlt _)]

/-- A round that adds nothing is a fixed point: the selection stays the same afterwards. -/
theorem greedySeq_stable {N : ℕ} {score : List ℕ → ℕ → α} {j : ℕ}
    (h : greedySeq N score (j + 1) = greedySeq N score j) :
    ∀ t ≥ j, greedySeq N score t = greedySeq N score j := by
  intro t ht
  induction ht with
  | refl => rfl
  | step _ ih =>
    rw [greedySeq_succ, ih, ← greedySeq_succ, h]

/-- **The prefixes of the selection are the earlier selections.** -/
theorem take_greedySeq (N : ℕ) (score : List ℕ → ℕ → α) {t l : ℕ}
    (hl : l ≤ (greedySeq N score t).length) :
    (greedySeq N score t).take l = greedySeq N score l := by
  have hlt : l ≤ t := hl.trans (length_greedySeq_le N score t)
  have hlen : (greedySeq N score l).length = l := by
    by_contra hne
    have hshort : (greedySeq N score l).length < l :=
      lt_of_le_of_ne (length_greedySeq_le N score l) hne
    -- some round before `l` added nothing
    have hj : ∃ j < l, greedySeq N score (j + 1) = greedySeq N score j := by
      by_contra hall
      push Not at hall
      have : ∀ j ≤ l, (greedySeq N score j).length = j := by
        intro j hj
        induction j with
        | zero => simp [greedySeq]
        | succ j ih =>
          have ih' := ih (by omega)
          have hne' := hall j (by omega)
          rw [greedySeq_succ] at hne' ⊢
          rcases hs : argmaxPos N (score (greedySeq N score j)) with _ | v
          · rw [greedyStep_of_none hs] at hne'; exact absurd rfl hne'
          · rw [greedyStep_of_some hs, List.length_append, List.length_singleton, ih']
      exact hne (this l le_rfl)
    obtain ⟨j, hjl, hj⟩ := hj
    have h1 := greedySeq_stable hj t (by omega)
    have h2 := greedySeq_stable hj l (by omega)
    rw [h1, ← h2] at hl
    omega
  have hp := greedySeq_prefix N score hlt
  obtain ⟨u, hu⟩ := hp
  rw [← hu, List.take_left' hlen]

end Select

/-! ### Back substitution -/

/-- **Back substitution.** If `|c_l + ∑_{j > l} t_{lj} c_j| ≤ ε` for all `l < k`, with every
`|t_{lj}| ≤ 1`, then `∑_l |c_l| ≤ (2^k - 1) ε`. -/
theorem backsubst (k : ℕ) (c : ℕ → ℝ) (t : ℕ → ℕ → ℝ) {ε : ℝ} (ht : ∀ l j, |t l j| ≤ 1)
    (h : ∀ l < k, |c l + ∑ j ∈ Finset.Ico (l + 1) k, t l j * c j| ≤ ε) :
    ∑ l ∈ Finset.range k, |c l| ≤ (2 ^ k - 1) * ε := by
  have key : ∀ m ≤ k, ∑ j ∈ Finset.Ico (k - m) k, |c j| ≤ (2 ^ m - 1) * ε := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      set l := k - (m + 1) with hl
      have hlk : l < k := by omega
      have hsplit : Finset.Ico l k = insert l (Finset.Ico (l + 1) k) := by
        rw [Finset.insert_Ico_add_one_left_eq_Ico hlk]
      have hl1 : l + 1 = k - m := by omega
      rw [hsplit, Finset.sum_insert (by simp), hl1]
      have h1 := h l hlk
      rw [hl1] at h1
      have h2 : |∑ j ∈ Finset.Ico (k - m) k, t l j * c j| ≤ ∑ j ∈ Finset.Ico (k - m) k, |c j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [abs_mul]
        calc |t l j| * |c j| ≤ 1 * |c j| := mul_le_mul_of_nonneg_right (ht l j) (abs_nonneg _)
          _ = |c j| := one_mul _
      have h3 : |c l| ≤ ε + ∑ j ∈ Finset.Ico (k - m) k, |c j| := by
        have := abs_sub_abs_le_abs_sub (c l + ∑ j ∈ Finset.Ico (k - m) k, t l j * c j)
          (∑ j ∈ Finset.Ico (k - m) k, t l j * c j)
        simp only [add_sub_cancel_right] at this
        have h4 := abs_add_le (c l + ∑ j ∈ Finset.Ico (k - m) k, t l j * c j)
          (-∑ j ∈ Finset.Ico (k - m) k, t l j * c j)
        rw [add_neg_cancel_right, abs_neg] at h4
        linarith
      have h5 : (2 : ℝ) ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by ring
      rw [h5]
      linarith
  have := key k le_rfl
  rwa [Nat.sub_self, ← Finset.range_eq_Ico] at this

/-! ### Cauchy–Schwarz -/

theorem abs_dotProduct_le {n : ℕ} (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  rw [← Real.sqrt_mul (dot_self_nonneg x)]
  refine Real.abs_le_sqrt ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [dotProduct, sq] using this

/-- The `ℓ²` norm is at most the `ℓ¹` norm. -/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, c i ^ 2) ≤ ∑ i ∈ s, |c i| := by
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ ↦ abs_nonneg _, ?_⟩
  calc ∑ i ∈ s, c i ^ 2 = ∑ i ∈ s, |c i| ^ 2 := by simp only [sq_abs]
    _ ≤ (∑ i ∈ s, |c i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ abs_nonneg _

/-! ### Greedy selection of columns -/

variable {n : ℕ}

/-- The score of appending `v` to `S`: the Gram determinant of the columns of `S ++ [v]`. -/
noncomputable def scoreR (col : ℕ → Fin n → ℝ) (S : List ℕ) (v : ℕ) : ℝ :=
  (gramF (colsL col (S ++ [v]))).det

theorem scoreR_eq (col : ℕ → Fin n → ℝ) (S : List ℕ) (v : ℕ)
    (hS : (gramF (colsL col S)).det ≠ 0) :
    scoreR col S v = (gramF (colsL col S)).det *
      (resid (colsL col S) (col v) ⬝ᵥ resid (colsL col S) (col v)) := by
  rw [scoreR, det_gramF_colsL_append, det_gramF_snocF _ hS]

/-- The invariant of the greedy lists: positive Gram determinant, distinct entries below `N`. -/
def GoodSel (col : ℕ → Fin n → ℝ) (N : ℕ) (S : List ℕ) : Prop :=
  0 < (gramF (colsL col S)).det ∧ S.Nodup ∧ ∀ s ∈ S, s < N

theorem resid_colsL_mem (col : ℕ → Fin n → ℝ) {S : List ℕ} (hS : (gramF (colsL col S)).det ≠ 0)
    {s : ℕ} (hs : s ∈ S) : resid (colsL col S) (col s) = 0 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  exact resid_col (colsL col S) hS ⟨j, hj⟩

/-- A greedy round keeps the invariant. -/
theorem goodSel_greedyStep (col : ℕ → Fin n → ℝ) (N : ℕ) {S : List ℕ} (hS : GoodSel col N S) :
    GoodSel col N (greedyStep N (scoreR col) S) := by
  rcases h : argmaxPos N (scoreR col S) with _ | v
  · rwa [greedyStep_of_none h]
  · rw [greedyStep_of_some h]
    obtain ⟨hv, hpos, -⟩ := argmaxPos_some h
    refine ⟨hpos, ?_, ?_⟩
    · refine List.nodup_append.2 ⟨hS.2.1, List.nodup_singleton v, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb hab
      rw [scoreR_eq col S a hS.1.ne', resid_colsL_mem col hS.1.ne' ha, dotProduct_zero,
        mul_zero] at hpos
      exact lt_irrefl _ hpos
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hS.2.2 s hs
      · rw [List.mem_singleton] at hs
        exact hs ▸ hv

theorem goodSel_greedySeq (col : ℕ → Fin n → ℝ) (N t : ℕ) :
    GoodSel col N (greedySeq N (scoreR col) t) := by
  induction t with
  | zero =>
    refine ⟨?_, List.nodup_nil, fun s hs ↦ absurd hs List.not_mem_nil⟩
    rw [greedySeq, Function.iterate_zero, id, det_gramF_nil]
    exact one_pos
  | succ t ih =>
    rw [greedySeq_succ]
    exact goodSel_greedyStep col N ih

/-- **The greedy choice**: the chosen column has the longest residual. -/
theorem resid_le_of_some (col : ℕ → Fin n → ℝ) {N : ℕ} {S : List ℕ} (hS : GoodSel col N S)
    {v : ℕ} (h : argmaxPos N (scoreR col S) = some v) {u : ℕ} (hu : u < N) :
    resid (colsL col S) (col u) ⬝ᵥ resid (colsL col S) (col u) ≤
      resid (colsL col S) (col v) ⬝ᵥ resid (colsL col S) (col v) := by
  have := (argmaxPos_some h).2.2 u hu
  rw [scoreR_eq col S u hS.1.ne', scoreR_eq col S v hS.1.ne'] at this
  exact le_of_mul_le_mul_left this hS.1

/-- Without a positive score, every residual is `0`. -/
theorem resid_eq_zero_of_none (col : ℕ → Fin n → ℝ) {N : ℕ} {S : List ℕ} (hS : GoodSel col N S)
    (h : argmaxPos N (scoreR col S) = none) {u : ℕ} (hu : u < N) :
    resid (colsL col S) (col u) = 0 := by
  have h1 := argmaxPos_none h u hu
  rw [scoreR_eq col S u hS.1.ne'] at h1
  have h2 : resid (colsL col S) (col u) ⬝ᵥ resid (colsL col S) (col u) ≤ 0 := by
    by_contra hc
    push Not at hc
    exact absurd h1 (not_le.2 (mul_pos hS.1 hc))
  exact dotProduct_self_eq_zero.1 (le_antisymm h2 (dot_self_nonneg _))

/-- If the selection stopped early, every residual is `0`. -/
theorem resid_eq_zero_of_short (col : ℕ → Fin n → ℝ) (N : ℕ) :
    ∀ t, (greedySeq N (scoreR col) t).length < t →
      ∀ u < N, resid (colsL col (greedySeq N (scoreR col) t)) (col u) = 0 := by
  intro t
  induction t with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ t ih =>
    intro hlen u hu
    have hgood := goodSel_greedySeq col N t
    rw [greedySeq_succ] at hlen ⊢
    rcases h : argmaxPos N (scoreR col (greedySeq N (scoreR col) t)) with _ | v
    · rw [greedyStep_of_none h]
      exact resid_eq_zero_of_none col hgood h hu
    · rw [greedyStep_of_some h, List.length_append, List.length_singleton] at hlen
      have h0 := ih (by omega) v (argmaxPos_some h).1
      have hpos := (argmaxPos_some h).2.1
      rw [scoreR_eq col _ v hgood.1.ne', h0, dotProduct_zero, mul_zero] at hpos
      exact absurd hpos (lt_irrefl _)

/-- Residuals shrink along the greedy rounds. -/
theorem resid_greedySeq_anti (col : ℕ → Fin n → ℝ) (N : ℕ) (y : Fin n → ℝ) {t t' : ℕ}
    (h : t ≤ t') :
    resid (colsL col (greedySeq N (scoreR col) t')) y ⬝ᵥ
        resid (colsL col (greedySeq N (scoreR col) t')) y ≤
      resid (colsL col (greedySeq N (scoreR col) t)) y ⬝ᵥ
        resid (colsL col (greedySeq N (scoreR col) t)) y := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ?_ ih
    rename_i m _
    rw [greedySeq_succ]
    rcases hs : argmaxPos N (scoreR col (greedySeq N (scoreR col) m)) with _ | v
    · rw [greedyStep_of_none hs]
    · rw [greedyStep_of_some hs]
      have hgood := (goodSel_greedySeq col N (m + 1)).1
      rw [greedySeq_succ, greedyStep_of_some hs] at hgood
      rw [resid_colsL_append col _ v hgood.ne']
      rw [det_gramF_colsL_append] at hgood
      exact resid_snocF_le _ hgood.ne' y

/-! ### The bound -/

/-- **The greedy bound.** Let every column be `col v = a v + b v`, with `a v` in a space of
dimension at most `T` and `‖∑ⱼ cⱼ b (L j)‖² ≤ ℓ² ∑ⱼ cⱼ²` for distinct indices. After `T` greedy
rounds, every column `v < N` has residual at most `(2^(T+1) - 1) ℓ`. -/
theorem greedy_resid_le (col a b : ℕ → Fin n → ℝ) (hab : ∀ v, col v = a v + b v)
    (V : Submodule ℝ (Fin n → ℝ)) {T : ℕ} (hV : Module.finrank ℝ V ≤ T) (haV : ∀ v, a v ∈ V)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hb : ∀ L : List ℕ, L.Nodup → ∀ c : Fin L.length → ℝ,
      (∑ j, c j • b L[j]) ⬝ᵥ (∑ j, c j • b L[j]) ≤ ℓ ^ 2 * ∑ j, c j ^ 2)
    (N : ℕ) {v : ℕ} (hv : v < N) :
    resid (colsL col (greedySel N T (scoreR col))) (col v) ⬝ᵥ
        resid (colsL col (greedySel N T (scoreR col))) (col v) ≤
      ((2 ^ (T + 1) - 1) * ℓ) ^ 2 := by
  classical
  set seq := greedySeq N (scoreR col) with hseq
  set S := seq T with hSdef
  change resid (colsL col S) (col v) ⬝ᵥ resid (colsL col S) (col v) ≤ _
  have hgoodS : GoodSel col N S := goodSel_greedySeq col N T
  -- the selection stopped early: residual `0`
  rcases (length_greedySeq_le N (scoreR col) T).lt_or_eq with hshort | hfull
  · rw [resid_eq_zero_of_short col N T hshort v hv, dotProduct_zero]
    positivity
  rw [← hseq, ← hSdef] at hfull
  set r := resid (colsL col S) (col v) with hr
  set ρ := Real.sqrt (r ⬝ᵥ r) with hρ
  by_cases hρ0 : ρ = 0
  · have : r ⬝ᵥ r = 0 := by
      have h0 := Real.sqrt_eq_zero (dot_self_nonneg r) |>.1 hρ0
      exact h0
    rw [this]
    positivity
  have hρpos : 0 < ρ := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hρ0)
  -- every round added a column
  have hlen : ∀ l ≤ T, (seq l).length = l := by
    intro l hl
    have h1 := length_greedySeq_le N (scoreR col) l
    rw [← hseq] at h1
    have h2 : (seq T).length ≤ (seq l).length + (T - l) := by
      have key : ∀ m, (seq (l + m)).length ≤ (seq l).length + m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [← add_assoc, hseq, greedySeq_succ, ← hseq]
          rcases hs : argmaxPos N (scoreR col (seq (l + m))) with _ | w
          · rw [greedyStep_of_none hs]; omega
          · rw [greedyStep_of_some hs, List.length_append, List.length_singleton]; omega
      have := key (T - l)
      rwa [Nat.add_sub_cancel' hl] at this
    rw [← hSdef, hfull] at h2
    omega
  have hpre : ∀ l ≤ T, seq l <+: S := fun l hl ↦ greedySeq_prefix N (scoreR col) hl
  have hsome : ∀ l (hl : l < T), argmaxPos N (scoreR col (seq l)) =
      some (S[l]'(by rw [hfull]; exact hl)) := by
    intro l hl
    have hl1 := hlen (l + 1) hl
    have hl0 := hlen l hl.le
    rcases hs : argmaxPos N (scoreR col (seq l)) with _ | w
    · have : seq (l + 1) = seq l := by rw [hseq, greedySeq_succ, greedyStep_of_none hs]
      rw [this, hl0] at hl1
      omega
    · have hstep : seq (l + 1) = seq l ++ [w] := by
        rw [hseq, greedySeq_succ, greedyStep_of_some hs]
      congr 1
      have hp := hpre (l + 1) hl
      rw [hstep] at hp
      obtain ⟨t, ht⟩ := hp
      have : S[l]'(by rw [hfull]; exact hl) = (seq l ++ [w] ++ t)[l]'(by simp [hl0]) := by
        simp only [← ht]
      rw [this, List.getElem_append_left (by simp [hl0]), List.getElem_append_right (by omega)]
      simp [hl0]
  have hstep : ∀ l (hl : l < T), seq (l + 1) = seq l ++ [S[l]'(by rw [hfull]; exact hl)] :=
    fun l hl ↦ by rw [hseq, greedySeq_succ, greedyStep_of_some (hsome l hl)]
  have hgood : ∀ l, GoodSel col N (seq l) := fun l ↦ goodSel_greedySeq col N l
  -- the columns: `x l` for `l < T` the chosen ones, `x T = v`
  set L' := S ++ [v] with hL'
  have hL'len : L'.length = T + 1 := by simp [hL', hfull]
  set x : ℕ → ℕ := fun l ↦ L'.getD l 0 with hx
  have hxS : ∀ l (hl : l < T), x l = S[l]'(by rw [hfull]; exact hl) := fun l hl ↦ by
    simp only [hx, hL']
    rw [List.getD_eq_getElem _ _ (by simp [hfull]; omega), List.getElem_append_left]
  have hxT : x T = v := by
    simp only [hx, hL']
    rw [List.getD_eq_getElem _ _ (by simp [hfull]), List.getElem_append_right (by omega)]
    simp [hfull]
  have hxN : ∀ l ≤ T, x l < N := by
    intro l hl
    rcases hl.lt_or_eq with hl | rfl
    · rw [hxS l hl]; exact hgoodS.2.2 _ (List.getElem_mem _)
    · rw [hxT]; exact hv
  -- the residuals of the chosen columns
  set rr : ℕ → Fin n → ℝ := fun l ↦ resid (colsL col (seq l)) (col (x l)) with hrr
  set ρ' : ℕ → ℝ := fun l ↦ Real.sqrt (rr l ⬝ᵥ rr l) with hρ'
  have hrrT : rr T = r := by simp only [hrr]; rw [hxT]
  -- every column of `seq l` is orthogonal to `rr l`
  have horth : ∀ l ≤ T, ∀ j < l, col (x j) ⬝ᵥ rr l = 0 := by
    intro l hl j hj
    have hmem : x j ∈ seq l := by
      rw [hxS j (by omega)]
      have hp := hpre l hl
      have hjl : j < (seq l).length := by rw [hlen l hl]; exact hj
      have : (seq l)[j] = S[j]'(by rw [hfull]; omega) := by
        obtain ⟨t, ht⟩ := hp
        simp only [← ht, List.getElem_append_left hjl]
      rw [← this]
      exact List.getElem_mem _
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmem
    have := col_dotProduct_resid (colsL col (seq l)) (hgood l).1.ne' (col (x l)) ⟨i, hi⟩
    simpa [colsL, hieq] using this
  have hdiag : ∀ l ≤ T, col (x l) ⬝ᵥ rr l = rr l ⬝ᵥ rr l := fun l _ ↦
    dotProduct_resid_eq _ (hgood l).1.ne' _ _
  -- the greedy choice: later columns have residuals at most `ρ' l` at round `l`
  have hgreedy : ∀ l < T, ∀ j ≤ T, |col (x j) ⬝ᵥ rr l| ≤ ρ' l * ρ' l := by
    intro l hl j hj
    rw [dotProduct_resid_eq _ (hgood l).1.ne']
    refine (abs_dotProduct_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    refine Real.sqrt_le_sqrt ?_
    have := resid_le_of_some col (hgood l) (hsome l hl) (hxN j hj)
    simpa [hrr, hxS l hl] using this
  -- every `ρ' l` is at least `ρ`
  have hρle : ∀ l ≤ T, ρ ≤ ρ' l := by
    intro l hl
    rcases hl.lt_or_eq with hl | rfl
    · refine Real.sqrt_le_sqrt ?_
      have h1 := resid_le_of_some col (hgood l) (hsome l hl) hv
      have h2 := resid_greedySeq_anti col N (col v) hl.le
      simp only [hrr, hxS l hl] at h1 ⊢
      rw [hr]
      exact h2.trans h1
    · simp only [hρ', hrrT, hρ, le_refl]
  -- the dependency of the `a`-parts
  have hdep : ∃ c : Fin (T + 1) → ℝ, (∑ i, c i • a (x i) = 0) ∧ ∃ i, c i ≠ 0 := by
    have hnot : ¬ LinearIndependent ℝ (fun i : Fin (T + 1) ↦ (⟨a (x i), haV _⟩ : V)) := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
    refine ⟨g, ?_, i, hi⟩
    have := congrArg Subtype.val hg
    simpa using this
  obtain ⟨c, hca, i₀, hi₀⟩ := hdep
  -- the vector `y = ∑ c_i col (x i) = ∑ c_i b (x i)`
  set y : Fin n → ℝ := ∑ i : Fin (T + 1), c i • col (x i) with hy
  have hyb : y = ∑ i : Fin (T + 1), c i • b (x i) := by
    simp only [hy, hab, smul_add, Finset.sum_add_distrib, hca, zero_add]
  have hnod : L'.Nodup := by
    refine List.nodup_append.2 ⟨hgoodS.2.1, List.nodup_singleton v, ?_⟩
    intro s hs w hw hsw
    rw [List.mem_singleton] at hw
    subst hw hsw
    apply hρ0
    rw [hρ, hr, resid_colsL_mem col hgoodS.1.ne' hs, dotProduct_zero, Real.sqrt_zero]
  have hyy : y ⬝ᵥ y ≤ ℓ ^ 2 * ∑ i, c i ^ 2 := by
    have := hb L' hnod (fun j ↦ c (Fin.cast hL'len j))
    have hsum : ∑ j : Fin L'.length, c (Fin.cast hL'len j) • b L'[j] =
        ∑ i : Fin (T + 1), c i • b (x i) := by
      refine Fintype.sum_equiv (finCongr hL'len) _ _ fun j ↦ ?_
      simp only [finCongr_apply, hx]
      rw [Fin.val_cast, List.getD_eq_getElem _ _ j.2]
      rfl
    have hsum2 : ∑ j : Fin L'.length, c (Fin.cast hL'len j) ^ 2 = ∑ i : Fin (T + 1), c i ^ 2 :=
      Fintype.sum_equiv (finCongr hL'len) _ _ fun j ↦ rfl
    rw [hsum, hsum2] at this
    rwa [hyb]
  set cN : ℕ → ℝ := fun l ↦ if h : l < T + 1 then c ⟨l, h⟩ else 0 with hcN
  have hy' : y = ∑ j ∈ Finset.range (T + 1), cN j • col (x j) := by
    rw [hy, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj' : (j : ℕ) ≤ T := Fin.is_le j
    simp [hcN, hj']
  -- the triangular system
  set ε := Real.sqrt (y ⬝ᵥ y) / ρ with hε
  set tt : ℕ → ℕ → ℝ := fun l j ↦ (col (x j) ⬝ᵥ rr l) / (rr l ⬝ᵥ rr l) with htt
  have hρ'pos : ∀ l ≤ T, 0 < ρ' l := fun l hl ↦ hρpos.trans_le (hρle l hl)
  have hrrpos : ∀ l ≤ T, 0 < rr l ⬝ᵥ rr l := by
    intro l hl
    have := hρ'pos l hl
    simp only [hρ'] at this
    exact Real.sqrt_pos.1 this
  have hsys : ∀ l < T + 1,
      |cN l + ∑ j ∈ Finset.Ico (l + 1) (T + 1), tt l j * cN j| ≤ ε := by
    intro l hl
    have hlT : l ≤ T := by omega
    have hexp : y ⬝ᵥ rr l = (rr l ⬝ᵥ rr l) *
        (cN l + ∑ j ∈ Finset.Ico (l + 1) (T + 1), tt l j * cN j) := by
      rw [hy', sum_dotProduct]
      have hsplit : Finset.range (T + 1) =
          Finset.range l ∪ insert l (Finset.Ico (l + 1) (T + 1)) := by
        ext j; simp [Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_union (by
        rw [Finset.disjoint_left]; intro j hj hj'; simp [Finset.mem_Ico] at hj hj'; omega),
        Finset.sum_insert (by simp)]
      have h0 : ∑ j ∈ Finset.range l, (cN j • col (x j)) ⬝ᵥ rr l = 0 :=
        Finset.sum_eq_zero fun j hj ↦ by
          rw [smul_dotProduct, horth l hlT j (Finset.mem_range.1 hj), smul_zero]
      rw [h0, zero_add, smul_dotProduct, hdiag l hlT, smul_eq_mul, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [smul_dotProduct, smul_eq_mul, htt]
        field_simp [(hrrpos l hlT).ne']
    have hbound : |y ⬝ᵥ rr l| ≤ Real.sqrt (y ⬝ᵥ y) * ρ' l := abs_dotProduct_le _ _
    rw [hexp, abs_mul, abs_of_pos (hrrpos l hlT)] at hbound
    have hrr' : rr l ⬝ᵥ rr l = ρ' l * ρ' l := by
      simp only [hρ']
      rw [Real.mul_self_sqrt (dot_self_nonneg _)]
    rw [hrr'] at hbound
    have h1 : |cN l + ∑ j ∈ Finset.Ico (l + 1) (T + 1), tt l j * cN j| ≤
        Real.sqrt (y ⬝ᵥ y) / ρ' l := by
      rw [le_div_iff₀ (hρ'pos l hlT)]
      nlinarith [hρ'pos l hlT, abs_nonneg (cN l + ∑ j ∈ Finset.Ico (l + 1) (T + 1),
        tt l j * cN j)]
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hρpos (hρle l hlT)
  have htt1 : ∀ l j, |(if l < T ∧ j ≤ T then tt l j else 0)| ≤ 1 := by
    intro l j
    split_ifs with hlj
    · rw [htt, abs_div, abs_of_pos (hrrpos l (by omega)), div_le_one (hrrpos l (by omega))]
      have := hgreedy l hlj.1 j hlj.2
      have hrr' : rr l ⬝ᵥ rr l = ρ' l * ρ' l := by
        simp only [hρ']
        rw [Real.mul_self_sqrt (dot_self_nonneg _)]
      rwa [hrr']
    · simp
  have hsys' : ∀ l < T + 1, |cN l + ∑ j ∈ Finset.Ico (l + 1) (T + 1),
      (if l < T ∧ j ≤ T then tt l j else 0) * cN j| ≤ ε := by
    intro l hl
    have h1 := hsys l hl
    convert h1 using 3
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_Ico] at hj
    have : l < T ∧ j ≤ T := ⟨by omega, by omega⟩
    simp [this]
  have hback := backsubst (T + 1) cN _ htt1 hsys'
  -- conclude
  have hc2 : 0 < ∑ i, c i ^ 2 :=
    lt_of_lt_of_le (pow_pos (abs_pos.2 hi₀) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (f := fun i ↦ c i ^ 2) (fun i _ ↦ sq_nonneg _) (Finset.mem_univ i₀))
  have hsumc : ∑ l ∈ Finset.range (T + 1), |cN l| = ∑ i, |c i| := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj' : (j : ℕ) ≤ T := Fin.is_le j
    simp [hcN, hj']
  have hl2 : Real.sqrt (∑ i, c i ^ 2) ≤ ∑ i, |c i| := sqrt_sum_sq_le_sum_abs _ _
  have hyle : Real.sqrt (y ⬝ᵥ y) ≤ ℓ * Real.sqrt (∑ i, c i ^ 2) := by
    rw [← Real.sqrt_sq hℓ, ← Real.sqrt_mul (sq_nonneg ℓ)]
    exact Real.sqrt_le_sqrt hyy
  have hsq : 0 < Real.sqrt (∑ i, c i ^ 2) := Real.sqrt_pos.2 hc2
  have hmain : ρ ≤ (2 ^ (T + 1) - 1) * ℓ := by
    have h1 : Real.sqrt (∑ i, c i ^ 2) ≤ (2 ^ (T + 1) - 1) * ε := by
      rw [← hsumc] at hl2
      exact hl2.trans hback
    rw [hε] at h1
    have h2 : Real.sqrt (∑ i, c i ^ 2) * ρ ≤ (2 ^ (T + 1) - 1) * Real.sqrt (y ⬝ᵥ y) := by
      have h3 := mul_le_mul_of_nonneg_right h1 hρpos.le
      rwa [mul_assoc, div_mul_cancel₀ _ hρpos.ne'] at h3
    have h4 : (0 : ℝ) ≤ 2 ^ (T + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (T + 1) := one_le_pow₀ (by norm_num)
      linarith
    have h5 := mul_le_mul_of_nonneg_left hyle h4
    have h6 : Real.sqrt (∑ i, c i ^ 2) * ρ ≤
        Real.sqrt (∑ i, c i ^ 2) * ((2 ^ (T + 1) - 1) * ℓ) := by nlinarith
    exact le_of_mul_le_mul_left h6 hsq
  have hρsq : r ⬝ᵥ r = ρ ^ 2 := by rw [hρ, Real.sq_sqrt (dot_self_nonneg _)]
  rw [hρsq]
  exact pow_le_pow_left₀ hρpos.le hmain 2

end Net

end BHSV25
