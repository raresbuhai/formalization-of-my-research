module

public import BHSV25.Spectral.Basic

/-!
# Edge density and expansion in one-sided expanders

For a `d`-regular graph `H` with at most one eigenvalue above `c ∈ [0, 1)` (`c` bounds `λ₂`):

* **[BHSV25, Lemma 7.18]** (edge density upper bound, `BHSV25.Planted.pairs_le`): every set `S`
  spans at most `d (|S|² / n + c |S|)` ordered pairs of adjacent vertices, that is
  `|E(H_S)| ≤ (d |S| / 2) (|S| / n + c)`. It is the quadratic form of `A / d` on the indicator of
  `S`.
* **[BHSV25, Lemma B.19], adapted** (`BHSV25.Planted.exists_closed_superset`): for `|S| ≤ γ n`
  and `ε > 2 γ + c`, some `T ⊇ S` with `|T| ≤ 2 |S|` leaves every vertex outside `T` with at most
  `ε d` neighbors in `T`. The paper removes vertices one at a time; here `T` is a largest set
  containing `S`, of at most `2 |S|` vertices, spanning `2 ε d |T \ S|` ordered pairs, and the
  density bound shows that it cannot be extended.
* **[BHSV25, Lemma 7.19]** (vertex expansion, `BHSV25.Planted.card_boundary_ge`): a set `S` of at
  most `β n` vertices has at least `(1 / (c + √β) - 1) |S|` neighbors outside itself.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset Matrix

variable (H : Graph)

/-! ### Pairs -/

open Classical in
/-- The number of ordered pairs of adjacent vertices of `S`. -/
noncomputable def pairs (S : Finset (Fin H.1)) : ℕ := ∑ u ∈ S, (S.filter (H.2.Adj u)).card

open Classical in
/-- The vertices outside `S` with a neighbor in `S`. -/
noncomputable def boundary (S : Finset (Fin H.1)) : Finset (Fin H.1) :=
  univ.filter fun w ↦ w ∉ S ∧ ∃ u ∈ S, H.2.Adj u w

variable {H}

open Classical in
/-- **[BHSV25, Lemma 7.18]**: `#{(u, v) ∈ S² : u ~ v} ≤ d (|S|² / n + c |S|)`. -/
theorem pairs_le {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hexp : H.numEigGT c ≤ 1) (S : Finset (Fin H.1)) :
    (pairs H S : ℝ) ≤ d * ((S.card : ℝ) ^ 2 / H.1 + c * S.card) := by
  set x : Fin H.1 → ℝ := fun v ↦ if v ∈ S then 1 else 0 with hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h := H.quad_le_of_numEigGT_le_one hreg hd hc0 hc1 hexp x
  have hsum : ∑ v, x v = S.card := by simp [hx]
  have hdot : x ⬝ᵥ x = S.card := by simp [hx, dotProduct]
  have hquad : x ⬝ᵥ (H.normAdj *ᵥ x) = pairs H S / d := by
    simp only [dotProduct, Matrix.mulVec, hx, H.normAdj_of_isRegularOfDegree hreg, pairs]
    push_cast
    rw [sum_div]
    rw [← sum_filter_add_sum_filter_not univ (· ∈ S)]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    rw [sum_eq_zero (s := univ.filter fun v ↦ v ∉ S) (fun v hv ↦ by
      rw [mem_filter] at hv; simp [hv.2]), add_zero]
    rw [filter_mem_eq_inter, univ_inter]
    refine sum_congr rfl fun u hu ↦ ?_
    simp only [hu, ite_true]
    rw [card_eq_sum_ones, Nat.cast_sum, sum_div, sum_filter]
    rw [← sum_filter_add_sum_filter_not univ (· ∈ S), filter_mem_eq_inter, univ_inter]
    rw [sum_eq_zero (s := univ.filter fun v ↦ v ∉ S) (fun v hv ↦ by
      rw [mem_filter] at hv; simp [hv.2]), add_zero]
    refine sum_congr rfl fun v hv ↦ ?_
    simp only [hv, ite_true]
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hquad, hsum, hdot] at h
  have h2 : (S.card : ℝ) ^ 2 / H.1 + c * (S.card - (S.card : ℝ) ^ 2 / H.1) ≤
      (S.card : ℝ) ^ 2 / H.1 + c * S.card := by
    have : 0 ≤ (S.card : ℝ) ^ 2 / H.1 := by positivity
    nlinarith
  rw [div_le_iff₀ hdR] at h
  nlinarith

open Classical in
theorem pairs_insert {T : Finset (Fin H.1)} {v : Fin H.1} (hv : v ∉ T) :
    pairs H (insert v T) = pairs H T + 2 * (T.filter (H.2.Adj v)).card := by
  have h1 : ∀ u ∈ T, ((insert v T).filter (H.2.Adj u)).card =
      (T.filter (H.2.Adj u)).card + if H.2.Adj u v then 1 else 0 := by
    intro u _
    rw [filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' ↦ hv (mem_filter.1 h').1)]
    · rfl
  have h2 : ((insert v T).filter (H.2.Adj v)).card = (T.filter (H.2.Adj v)).card := by
    rw [filter_insert, ite_eq_right (H.2.loopless.irrefl v)]
  rw [pairs, sum_insert hv, h2, sum_congr rfl h1, sum_add_distrib, ← pairs]
  have h3 : ∑ u ∈ T, (if H.2.Adj u v then 1 else 0) = (T.filter (H.2.Adj v)).card := by
    rw [card_eq_sum_ones, sum_filter]
    exact sum_congr rfl fun u _ ↦ by simp [H.2.adj_comm u v]
  rw [h3]
  ring

/-! ### Lemma B.19 -/

open Classical in
/-- **[BHSV25, Lemma B.19], adapted**: for `|S| ≤ γ n` and `ε > 2 γ + c`, some `T ⊇ S` with
`|T| ≤ 2 |S|` leaves every vertex outside `T` with at most `ε d` neighbors in `T`. -/
theorem exists_closed_superset {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hexp : H.numEigGT c ≤ 1) (S : Finset (Fin H.1)) {γ ε : ℝ}
    (hγ : 0 ≤ γ) (hS : (S.card : ℝ) ≤ γ * H.1) (hε : 2 * γ + c < ε) :
    ∃ T : Finset (Fin H.1), S ⊆ T ∧ T.card ≤ 2 * S.card ∧
      ∀ v ∉ T, ((T.filter (H.2.Adj v)).card : ℝ) ≤ ε * d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hε0 : 0 < ε := by linarith
  set F := (univ : Finset (Fin H.1)).powerset.filter fun T ↦
    S ⊆ T ∧ T.card ≤ 2 * S.card ∧ 2 * ε * d * ((T \ S).card : ℝ) ≤ pairs H T with hF
  have hSF : S ∈ F := by
    rw [hF, mem_filter]
    refine ⟨mem_powerset.2 (subset_univ _), subset_refl _, by omega, ?_⟩
    simp
  obtain ⟨T, hT, hmax⟩ := exists_max_image F card ⟨S, hSF⟩
  rw [hF, mem_filter] at hT
  obtain ⟨-, hST, hTc, hTp⟩ := hT
  refine ⟨T, hST, hTc, fun v hv ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hpos : (0 : ℝ) < (T.filter (H.2.Adj v)).card := lt_of_le_of_lt (by positivity) hlt
  -- `T ∪ {v}` satisfies the inequality
  have hsd : (insert v T \ S).card = (T \ S).card + 1 := by
    rw [insert_sdiff_of_notMem _ (fun h ↦ hv (hST h)), card_insert_of_notMem
      (fun h ↦ hv (mem_sdiff.1 h).1)]
  have hp' : 2 * ε * d * (((insert v T) \ S).card : ℝ) ≤ pairs H (insert v T) := by
    rw [pairs_insert hv, hsd]
    push_cast
    nlinarith
  by_cases hsize : (insert v T).card ≤ 2 * S.card
  · -- contradicts maximality
    have hmem : insert v T ∈ F := by
      rw [hF, mem_filter]
      exact ⟨mem_powerset.2 (subset_univ _), hST.trans (subset_insert _ _), hsize, hp'⟩
    have := hmax _ hmem
    rw [card_insert_of_notMem hv] at this
    omega
  · -- `|T| = 2 |S|` contradicts the density bound
    rw [card_insert_of_notMem hv] at hsize
    have hT2 : T.card = 2 * S.card := by omega
    have hTS : (T \ S).card = S.card := by rw [card_sdiff_of_subset hST]; omega
    have hdens := pairs_le hreg hd hc0 hc1 hexp T
    rw [hTS] at hTp
    rw [hT2] at hdens
    push_cast at hdens
    have hS0 : (0 : ℝ) < S.card := by
      have hTne : T.Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        simp [hne] at hpos
      have : 0 < T.card := hTne.card_pos
      have : 0 < S.card := by omega
      exact_mod_cast this
    have hn : (0 : ℝ) < H.1 := by
      have := card_le_univ S
      rw [Fintype.card_fin] at this
      have : 0 < H.1 := lt_of_lt_of_le (by exact_mod_cast hS0) this
      exact_mod_cast this
    -- `2 ε d |S| ≤ d (4 |S|² / n + 2 c |S|)`, so `ε ≤ 2 |S| / n + c ≤ 2 γ + c`
    have h1 : 2 * ε * d * S.card ≤ d * (2 * (2 * S.card ^ 2 / H.1) + 2 * c * S.card) := by
      calc 2 * ε * d * S.card ≤ pairs H T := hTp
        _ ≤ _ := by
            refine hdens.trans (le_of_eq ?_)
            ring
    have h2 : ε ≤ 2 * S.card / H.1 + c := by
      have h3 : 2 * d * S.card * ε ≤ 2 * d * S.card * (2 * S.card / H.1 + c) := by
        have e : 2 * (d : ℝ) * S.card * (2 * S.card / H.1 + c) =
            d * (2 * (2 * S.card ^ 2 / H.1) + 2 * c * S.card) := by ring
        rw [e]; linarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    have h4 : 2 * (S.card : ℝ) / H.1 ≤ 2 * γ := by
      rw [div_le_iff₀ hn]; linarith
    linarith

/-! ### Lemma 7.19 -/

open Classical in
/-- **[BHSV25, Lemma 7.19]** (vertex expansion): a set of at most `β n` vertices has at least
`(1 / (c + √β) - 1) |S|` neighbors outside itself. -/
theorem card_boundary_ge {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hexp : H.numEigGT c ≤ 1) {β : ℝ} (hβ : 0 < β)
    (S : Finset (Fin H.1)) (hS : (S.card : ℝ) ≤ β * H.1) :
    (1 / (c + Real.sqrt β) - 1) * S.card ≤ (boundary H S).card := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  set T := S ∪ boundary H S with hTdef
  have hdisj : Disjoint S (boundary H S) :=
    disjoint_left.2 fun u hu hb ↦ (mem_filter.1 hb).2.1 hu
  have hTcard : (T.card : ℝ) = S.card + (boundary H S).card := by
    rw [hTdef, card_union_of_disjoint hdisj]; push_cast; ring
  -- every vertex of `S` has all its `d` neighbors in `T`
  have hpairs : (d : ℝ) * S.card ≤ pairs H T := by
    have h1 : ∀ u ∈ S, d ≤ (T.filter (H.2.Adj u)).card := by
      intro u hu
      rw [← hreg u, ← SimpleGraph.card_neighborFinset_eq_degree]
      refine card_le_card fun w hw ↦ ?_
      rw [SimpleGraph.mem_neighborFinset] at hw
      rw [mem_filter, hTdef, mem_union]
      refine ⟨?_, hw⟩
      by_cases hwS : w ∈ S
      · exact Or.inl hwS
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, hwS, u, hu, hw⟩)
    have h2 : d * S.card ≤ pairs H T := by
      calc d * S.card = ∑ _u ∈ S, d := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ S, (T.filter (H.2.Adj u)).card := sum_le_sum h1
        _ ≤ pairs H T := sum_le_sum_of_subset_of_nonneg subset_union_left fun _ _ _ ↦ by omega
    exact_mod_cast h2
  have hdens := pairs_le hreg hd hc0 hc1 hexp T
  have hmain : (S.card : ℝ) ≤ (T.card : ℝ) ^ 2 / H.1 + c * T.card := by
    have := hpairs.trans hdens
    rw [mul_comm (d : ℝ) (S.card : ℝ), mul_comm (d : ℝ)] at this
    exact le_of_mul_le_mul_right this hdR
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]; simp
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast hpos
  have hn : (0 : ℝ) < H.1 := by
    have := card_le_univ S
    rw [Fintype.card_fin] at this
    have : 0 < H.1 := lt_of_lt_of_le hpos this
    exact_mod_cast this
  -- `|T| ≥ |S| / (c + √β)`
  have hT : (S.card : ℝ) / (c + Real.sqrt β) ≤ T.card := by
    by_contra hlt
    push Not at hlt
    have hcs : 0 < c + Real.sqrt β := by linarith
    have h1 : (T.card : ℝ) * (c + Real.sqrt β) < S.card := by
      rwa [lt_div_iff₀ hcs] at hlt
    have h2 : (T.card : ℝ) / H.1 ≤ Real.sqrt β := by
      have h3 : (T.card : ℝ) < S.card / Real.sqrt β :=
        lt_of_lt_of_le hlt (div_le_div_of_nonneg_left hS0.le hsb (by linarith))
      rw [div_le_iff₀ hn]
      have h4 : (S.card : ℝ) / Real.sqrt β ≤ Real.sqrt β * H.1 := by
        rw [div_le_iff₀ hsb]
        have := Real.mul_self_sqrt hβ.le
        nlinarith
      linarith
    have hT0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    have h5 : (T.card : ℝ) ^ 2 / H.1 + c * T.card ≤ T.card * (Real.sqrt β + c) := by
      have e : (T.card : ℝ) ^ 2 / H.1 = T.card * (T.card / H.1) := by ring
      rw [e]
      nlinarith
    linarith
  have hcs : 0 < c + Real.sqrt β := by linarith
  rw [hTcard] at hT
  have e : (1 / (c + Real.sqrt β) - 1) * S.card = S.card / (c + Real.sqrt β) - S.card := by
    field_simp
  rw [e]
  linarith

end Planted

end BHSV25
