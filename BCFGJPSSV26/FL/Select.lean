module

public import BCFGJPSSV26.FL.Algorithm

/-!
# Theorem 1.4: the trivial solution and the choice of the output

The guarantee of [BCFGJPSSV26a, Theorem 1.4], `cost S ≤ λ (OPT_f - f |S|)`, is
`cost S + λ f |S| ≤ λ OPT_f`, a bound on the objective `BCFGJPSSV26.FL.score` of `S`
(`BCFGJPSSV26.FL.lmp_of_score`). The output of `BCFGJPSSV26.FL.alg` has the least objective of
the trivial solution and the greedy run when the run is a list of distinct facilities, so it meets
the bound whenever one of them does (`BCFGJPSSV26.FL.alg_spec_of`).

The trivial solution meets it when it has at most as many facilities as an optimal set `O`
(`BCFGJPSSV26.FL.score_trivialSol_le`), as it costs at most every nonempty set
(`BCFGJPSSV26.FL.cost_trivialSol_le_cost`). This holds when `n = 1` or `m = 1`, and when `O`
costs `0` (`BCFGJPSSV26.FL.trivialSol_length_le_card`: clients at distance `0` from the same
facility of `O` have the same nearest facility), and the bound holds for `f = 0` too.
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-! ### Optimal sets -/

/-- **An optimal set for facility location**: a nonempty set of facilities `O` with
`OPT_f = cost O + f |O|`. -/
theorem exists_optFL (hI : I.Valid) (f : ℝ) :
    ∃ O : Finset (Fin I.m), O.Nonempty ∧ I.optFL f = I.cost O + f * O.card := by
  have : Nonempty {S : Finset (Fin I.m) // S.Nonempty} := ⟨⟨{⟨0, hI.one_le_m⟩}, by simp⟩⟩
  obtain ⟨⟨O, hO⟩, h⟩ := Finite.exists_min
    (fun S : {S : Finset (Fin I.m) // S.Nonempty} ↦ I.cost S.1 + f * S.1.card)
  refine ⟨O, hO, le_antisymm ?_ (le_ciInf h)⟩
  exact ciInf_le (Set.finite_range _).bddBelow (⟨O, hO⟩ : {S : Finset (Fin I.m) // S.Nonempty})

/-! ### The trivial solution -/

/-- **The trivial solution costs at most every nonempty set.** -/
theorem cost_trivialSol_le_cost (hI : I.Valid) (hn : 1 ≤ I.n) {S : Finset (Fin I.m)}
    (hS : S.Nonempty) : I.cost (I.centers (trivialSol (toRaw I))) ≤ I.cost S := by
  have hm := hI.one_le_m
  have hT := isCenterList_trivialSol hI hn
  rw [← Instance.costF_eq_cost hS,
    ← Instance.costF_eq_cost (Instance.centers_nonempty hT.1 hT.2.2)]
  refine sum_le_sum fun j _ ↦ ?_
  obtain ⟨i, -, h⟩ := Instance.exists_dSet_eq hS (.inl j)
  rw [h]
  have hmem : (⟨nearest (toRaw I) j, nearest_lt hm j⟩ : Fin I.m) ∈
      I.centers (trivialSol (toRaw I)) :=
    Instance.mem_centers.2 (mem_trivialSol.2 ⟨j, j.2, rfl⟩)
  refine (Instance.dSet_le hmem _).trans ?_
  unfold Instance.dd
  exact_mod_cast nearest_le hm j i

/-- **If a nonempty set costs `0`, the trivial solution has at most as many facilities**: every
client is at distance `0` from a facility of the set, and clients at distance `0` from the same
facility have the same nearest facility. -/
theorem trivialSol_length_le_card (hI : I.Valid) {O : Finset (Fin I.m)} (hO : O.Nonempty)
    (h : I.cost O = 0) : (trivialSol (toRaw I)).length ≤ O.card := by
  have h0 : ∀ j : Fin I.n, ∃ o ∈ O, I.d (.inl j) (.inr o) = 0 := by
    intro j
    have hsum : I.costF O = 0 := (Instance.costF_eq_cost hO).trans h
    have hj := (sum_eq_zero_iff_of_nonneg fun j _ ↦
      Instance.dSet_nonneg hI (.inl j) O).1 hsum j (mem_univ j)
    obtain ⟨o, ho, he⟩ := Instance.exists_dSet_eq hO (.inl j)
    refine ⟨o, ho, ?_⟩
    have : I.dd (.inl j) (.inr o) = 0 := he ▸ hj
    unfold Instance.dd at this
    exact_mod_cast this
  have hnd : (trivialSol (toRaw I)).Nodup := List.nodup_eraseDups _
  have hsub : (trivialSol (toRaw I)).toFinset ⊆
      O.image fun o : Fin I.m ↦ nearest (toRaw I) (I.n + o) := fun i hi ↦ by
    obtain ⟨j, hj, rfl⟩ := mem_trivialSol.1 (List.mem_toFinset.1 hi)
    obtain ⟨o, ho, hd⟩ := h0 ⟨j, hj⟩
    exact mem_image.2 ⟨o, ho, (nearest_eq_of_d_eq_zero hI hd).symm⟩
  have := (card_le_card hsub).trans card_image_le
  rwa [List.toFinset_card_of_nodup hnd] at this

/-! ### The objective -/

theorem lmpC_cast : ((lmpC : ℚ) : ℝ) = 1.9499 := by
  norm_num [lmpC]

theorem one_le_lmpC : (1 : ℝ) ≤ (lmpC : ℝ) := by
  rw [lmpC_cast]
  norm_num

/-- The objective of a list of facilities is `cost S + λ f |S|`. -/
theorem score_cast {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) (f : ℚ) :
    (score (toRaw I) f S : ℝ) = I.cost (I.centers S) + (lmpC : ℝ) * f * S.length := by
  unfold score
  push_cast
  rw [← Combine.costQ_eq I hS hm]
  rfl

/-- **The LMP guarantee from the objective**: `cost S + λ f |S| ≤ λ OPT_f` is
`cost S ≤ λ (OPT_f - f |S|)`. -/
theorem lmp_of_score {S : List ℕ} (hS : I.IsCenterList S) {f : ℚ}
    (h : (score (toRaw I) f S : ℝ) ≤ (lmpC : ℝ) * I.optFL f) :
    I.cost (I.centers S) ≤ 1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * S.length) := by
  rw [score_cast hS.1 hS.2.2, lmpC_cast] at h
  linarith

/-- The trivial solution meets the bound if it has at most as many facilities as an optimal
set, or if `f = 0`. -/
theorem score_trivialSol_le (hI : I.Valid) (hn : 1 ≤ I.n) {f : ℚ} (hf : 0 ≤ f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hopt : I.optFL f = I.cost O + f * O.card)
    (h : (trivialSol (toRaw I)).length ≤ O.card ∨ f = 0) :
    (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f := by
  have hT := isCenterList_trivialSol hI hn
  rw [score_cast hT.1 hT.2.2, hopt]
  have h1 := cost_trivialSol_le_cost hI hn hO
  have h2 := Instance.cost_nonneg' hI O
  have hl := one_le_lmpC
  have hf' : (0 : ℝ) ≤ f := by exact_mod_cast hf
  have h3 : (lmpC : ℝ) * f * (trivialSol (toRaw I)).length ≤ (lmpC : ℝ) * f * O.card := by
    rcases h with h | h
    · have : ((trivialSol (toRaw I)).length : ℝ) ≤ O.card := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · rw [h]
      simp
  nlinarith

/-! ### The choice of the output -/

/-- A list of distinct facilities has at most `m` entries. -/
theorem length_le_of_isCenterList {S : List ℕ} (hS : I.IsCenterList S) : S.length ≤ I.m := by
  have hsub : S.toFinset ⊆ range I.m := fun i hi ↦ mem_range.2 (hS.2.2 i (List.mem_toFinset.1 hi))
  have := card_le_card hsub
  rwa [List.toFinset_card_of_nodup hS.2.1, card_range] at this

/-- **The output meets the bound** if the trivial solution does, or if the greedy run is a list
of distinct facilities that does. -/
theorem alg_spec_of (hI : I.Valid) (hn : 1 ≤ I.n) (f : ℚ)
    (h : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f ∨
      (I.IsCenterList (runFL (toRaw I) f) ∧
        (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f)) :
    I.IsCenterList (alg (toRaw I) f) ∧
      (score (toRaw I) f (alg (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f := by
  have hT := isCenterList_trivialSol hI hn
  unfold alg
  split_ifs with hc
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hv, hlt⟩ := hc
    obtain ⟨h1, h2, h3, -⟩ := Combine.valid_iff.1 hv
    refine ⟨⟨h1, h2, h3⟩, ?_⟩
    rcases h with h | ⟨-, h⟩
    · have : (score (toRaw I) f (runFL (toRaw I) f) : ℝ) <
          score (toRaw I) f (trivialSol (toRaw I)) := by exact_mod_cast hlt
      linarith
    · exact h
  · refine ⟨hT, ?_⟩
    rcases h with h | ⟨hS, h⟩
    · exact h
    · have hv : Combine.valid (toRaw I).m (toRaw I).m (runFL (toRaw I) f) = true :=
        Combine.valid_iff.2 ⟨hS.1, hS.2.1, hS.2.2, length_le_of_isCenterList hS⟩
      rw [hv, Bool.true_and, decide_eq_true_eq, not_lt] at hc
      have : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤
          score (toRaw I) f (runFL (toRaw I) f) := by exact_mod_cast hc
      linarith

end BCFGJPSSV26.FL
