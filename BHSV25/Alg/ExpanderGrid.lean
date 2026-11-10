module

public import BHSV25.Alg.ExpanderAccount
public import BHSV25.Alg.GridPartition

/-!
# The analysis of Theorem 7.1

The algorithm of [BHSV25, Theorem 7.1] is the greedy net followed by the grid clustering
(`BHSV25.Alg.gridAlg`), with one cluster per group of equal rows of `M`. On a regular graph with
at most one eigenvalue above `λ` and an `(M, δ)`-coloring `χ` whose monochromatic edges are covered
by a set `S` of `δ n` vertices (`BHSV25.Alg.expander_numColored_grid`):

* the degree is positive (the model of an edgeless graph is `0`, far from `M`);
* the part sizes are within `C δ n` of `π n` ([BHSV25, Lemma 7.3]), since the fractions
  `p_a = |V_a| / n` are exactly stationary for the model of `χ`;
* the contracted partition `χ'` (merging the parts with equal rows of `M`) has parts of at least
  `min π / 2 · n` vertices, weight at most `(2 + k) δ n` inside its parts, and a model whose rows
  are `α_N / 2`-separated;
* Theorem 5.1 with the grid of centers (`BHSV25.Alg.exists_good_grid`), with Lemma 6.1 at the
  upper bound `λ` on the second eigenvalue, gives a candidate agreeing with `χ'` on all but
  `(E + F) n` vertices, `E = O_M(δ/λ + λ)` and `F = 512 m² η² / α²` for a net of precision `η`;
* rounding each cluster against the part of its representative minus `S` colors all but
  `(α + O_M(δ) + 2 δ + 2 (E + F)) n` vertices (`BHSV25.Alg.numColored_ge_contract_grid`,
  `BHSV25.Alg.sub_sum_max_le_alpha`).

The output has `m` colors, `m` the number of distinct rows of `M` (`BHSV25.Alg.card_reps_eq`), with
the uncolored vertices marked `m`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {π : Fin k → ℝ}

/-- **The number of colors**: the representatives of the groups of equal rows are as many as the
distinct rows of `M`. -/
theorem card_reps_eq (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ) :
    Fintype.card (Reps M π) = Nat.card (Set.range M) := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective (fun i ↦ ⟨M i.1, i.1, rfl⟩) ⟨fun i j hij ↦ ?_, fun r ↦ ?_⟩
  · have h : M i.1 = M j.1 := congrArg Subtype.val hij
    have h2 : rowRep M π i.1 = rowRep M π j.1 := (rowRep_eq_rowRep_iff (M := M) π).2 h
    rw [i.2, j.2] at h2
    exact Subtype.ext h2
  · obtain ⟨_, a, rfl⟩ := r
    exact ⟨toRep M π a, Subtype.ext (row_rowRep (M := M) π a)⟩

/-- **Rounding the merged parts, with the grid clustering**: the algorithm colors at least
`∑_i max(0, 2 |V_{a_i^*}| - |V'_i|) - 2 |S| - 2 |B|` vertices, for every candidate of net vectors
`us` and grid indices `ts` whose clusters agree with the contracted partition outside `B`. -/
theorem numColored_ge_contract_grid (G : Graph) (χ : Fin G.1 → Fin k) (S : Finset (Fin G.1))
    (hS : ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ S ∨ v ∈ S) {m K₀ : ℕ} (hm : 0 < m)
    (hmK : m ≤ K₀) (e : Reps M π ≃ Fin m) (Sg Kg Bg : ℕ) (U : List (List ℚ))
    (hB1 : U.length ^ m ≤ Bg) (hB2 : (2 * Kg + 1) ^ (m * m) ≤ Bg) (us : Fin m → List ℚ)
    (hus : ∀ j, us j ∈ U) (ts : Fin (m * m) → Fin (2 * Kg + 1)) (B : Finset (Fin G.1))
    (hB : ∀ y, y ∉ B → clusterIdxC (List.ofFn us)
      (gridCenters m Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y =
        e (contract M π χ y)) :
    ∑ i : Reps M π, max 0 (2 * ((part G χ i.1).card : ℝ) - (part G (contract M π χ) i).card) -
        2 * S.card - 2 * B.card ≤
      G.numColored K₀ (gridAlg m K₀ Sg Kg Bg U (G.1, adjTable G)) := by
  set p := clustersC G.1 (List.ofFn us)
    (gridCenters m Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) with hp
  set q : Fin G.1 → ℕ := fun y ↦ clusterIdxC (List.ofFn us)
    (gridCenters m Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y with hq
  set I : ℕ → Finset (Fin G.1) := fun j ↦
    if h : j < m then part G χ (e.symm ⟨j, h⟩).1 \ S else ∅ with hI
  have hIind : ∀ j, G.2.IsIndepSet (I j : Set (Fin G.1)) := by
    intro j
    simp only [hI]
    split_ifs
    · exact isIndepSet_part_sdiff χ S hS _
    · simp
  have hspec := (gridAlg_spec G hm hmK Sg Kg Bg U hB1 hB2).2 us hus ts I hIind
  rw [← hp] at hspec
  -- reindex the sum by the representatives
  have hreindex : ∀ F : ℕ → ℝ, ∑ j ∈ range m, F j = ∑ i : Reps M π, F (e i) := by
    intro F
    rw [sum_range]
    exact (Equiv.sum_comp e (fun j ↦ F j)).symm
  rw [hreindex] at hspec
  have hIe : ∀ i : Reps M π, I (e i) = part G χ i.1 \ S := by
    intro i
    simp only [hI, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  have hR : ∀ i : Reps M π, classSet G m p (e i) = univ.filter fun y ↦ q y = e i := by
    intro i
    ext y
    rw [classSet, mem_filter, mem_filter, hp, getD_clustersC _ _ y.2]
  -- the bound for each group
  have hgroup : ∀ i : Reps M π,
      max 0 (2 * ((part G χ i.1).card : ℝ) - (part G (contract M π χ) i).card) -
        (2 * (S ∩ part G (contract M π χ) i).card + (B ∩ part G (contract M π χ) i).card +
          (B ∩ univ.filter fun y ↦ q y = e i).card) ≤
      max 0 (((classSet G m p (e i) ∩ I (e i)).card : ℝ) -
        (classSet G m p (e i) \ I (e i)).card) := by
    intro i
    rw [hIe, hR]
    have h := card_inter_sub_card_sdiff_ge (univ.filter fun y ↦ q y = e i) (part G χ i.1)
      (part G (contract M π χ) i) S B (part_subset_part_contract χ i)
      (fun y hy hyB ↦ by
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rw [hq]
        simp only
        rw [hB y hyB, mem_part.1 hy])
      (fun y hy hyB ↦ by
        rw [mem_filter] at hy
        rw [mem_part]
        have h1 := hB y hyB
        have h2 := hy.2
        rw [hq] at h2
        simp only at h2
        rw [h1] at h2
        exact e.injective (Fin.ext h2))
    have hz : 0 ≤ 2 * ((S ∩ part G (contract M π χ) i).card : ℝ) +
        (B ∩ part G (contract M π χ) i).card + (B ∩ univ.filter fun y ↦ q y = e i).card := by
      positivity
    have := max_zero_le_add_abs
      (((univ.filter fun y ↦ q y = e i) ∩ (part G χ i.1 \ S)).card -
        ((univ.filter fun y ↦ q y = e i) \ (part G χ i.1 \ S)).card : ℝ)
      (2 * ((part G χ i.1).card : ℝ) - (part G (contract M π χ) i).card)
    have hle : max 0 (2 * ((part G χ i.1).card : ℝ) - (part G (contract M π χ) i).card) ≤
        max 0 ((((univ.filter fun y ↦ q y = e i) ∩ (part G χ i.1 \ S)).card : ℝ) -
          ((univ.filter fun y ↦ q y = e i) \ (part G χ i.1 \ S)).card) +
        (2 * ((S ∩ part G (contract M π χ) i).card : ℝ) +
          (B ∩ part G (contract M π χ) i).card + (B ∩ univ.filter fun y ↦ q y = e i).card) := by
      refine max_le (by positivity) ?_
      linarith [le_max_right (0 : ℝ) ((((univ.filter fun y ↦ q y = e i) ∩
        (part G χ i.1 \ S)).card : ℝ) - ((univ.filter fun y ↦ q y = e i) \
          (part G χ i.1 \ S)).card)]
    linarith
  -- the sums of the losses
  have hS' : ∑ i : Reps M π, ((S ∩ part G (contract M π χ) i).card : ℝ) = S.card :=
    sum_card_inter_part _ S
  have hB' : ∑ i : Reps M π, ((B ∩ part G (contract M π χ) i).card : ℝ) = B.card :=
    sum_card_inter_part _ B
  have hBR : ∑ i : Reps M π, ((B ∩ univ.filter fun y ↦ q y = e i).card : ℝ) ≤ B.card := by
    have hdisj : ((univ : Finset (Reps M π)) : Set (Reps M π)).PairwiseDisjoint
        fun i ↦ B ∩ univ.filter fun y ↦ q y = e i := by
      intro i _ j _ hij
      refine disjoint_left.2 fun y hyi hyj ↦ hij ?_
      rw [mem_inter, mem_filter] at hyi hyj
      exact e.injective (Fin.ext (hyi.2.2.symm.trans hyj.2.2))
    have h := card_biUnion hdisj
    have hsub : (univ.biUnion fun i ↦ B ∩ univ.filter fun y ↦ q y = e i) ⊆ B :=
      biUnion_subset.2 fun i _ ↦ inter_subset_left
    have h2 := card_le_card hsub
    rw [h] at h2
    exact_mod_cast h2
  have hsum := sum_le_sum fun i (_ : i ∈ univ) ↦ hgroup i
  rw [sum_sub_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, hS', hB'] at hsum
  linarith

open Classical in
theorem pmodel_zero_of_degree_zero {G : Graph} (h : G.2.IsRegularOfDegree 0)
    (χ : Fin G.1 → Fin k) (a b : Fin k) : pmodel G χ a b = 0 := by
  have h0 : ∀ x y, G.normAdj x y = 0 := fun x y ↦ by
    rw [G.normAdj_of_isRegularOfDegree h]
    split_ifs <;> simp
  simp [pmodel, wt, h0]

/-- **The analysis of the algorithm of Theorem 7.1 with the grid clustering**: on a regular graph
with at most one eigenvalue above `λ` and an `(M, δ)`-coloring, the algorithm colors all but
`(α + m (2k + 2) C δ + 2 δ + 2 (E + F)) n` vertices, where `E = O_M(δ/λ + λ)` is the error of
Theorem 5.1 for the contracted partition and `F = 512 m² η² / α²` the cost of the net. -/
theorem expander_numColored_grid (hM : IsModel M) (hπ : IsStationary M π) (hk : 0 < k) {C : ℝ}
    (hC : 0 < C)
    (hstab : ∀ (p : Fin k → ℝ) (ε : ℝ), ∑ a, p a = 1 →
      (∀ b, |∑ a, p a * M a b - p b| ≤ ε) → ∀ a, |p a - π a| ≤ C * ε)
    {αN : ℝ} (hαN : 0 < αN)
    (hsepN : ∀ i j : Reps M π, i ≠ j → ∃ l : Reps M π,
      αN ≤ |∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b|)
    {πmin : ℝ} (hπmin : 0 < πmin) (hπle : ∀ a, πmin ≤ π a)
    {θ : ℝ} (hθ : 0 < θ) (hθα : (2 * θ) ^ 2 * (2 / (πmin / 2)) ≤ (αN / 2) ^ 2 / 2)
    {δ lam η : ℝ} (hδ0 : 0 ≤ δ) (hδk : k * δ < 1) (hδC : C * δ ≤ πmin / 2)
    (hδN : 2 * k * δ ≤ αN / 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (U : List (List ℚ)) {Sg Kg Bg : ℕ}
    (hSg : 128 * (Fintype.card (Reps M π) : ℝ) ^ 2 ≤ (αN / 2) ^ 2 * (Sg : ℝ) ^ 2) (hK1 : 1 ≤ Kg)
    (hK : (Sg : ℝ) ^ 2 ≤ πmin / 2 * ((Kg : ℝ) - 1) ^ 2)
    (hB1 : U.length ^ Fintype.card (Reps M π) ≤ Bg)
    (hB2 : (2 * Kg + 1) ^ (Fintype.card (Reps M π) * Fintype.card (Reps M π)) ≤ Bg)
    (G : Graph) (hreg : G.IsRegular) (hexp : G.numEigGT lam ≤ 1) (hcol : G.MColorable M δ)
    (hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ η ^ 2) :
    (1 - (alpha M π + (Fintype.card (Reps M π) * ((2 * k + 2) * (C * δ)) + 2 * δ +
      2 * (512 * (Fintype.card (Reps M π) : ℝ) ^ 4 * ((2 + k) * δ / lam + lam) /
        (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) +
        512 * (Fintype.card (Reps M π) : ℝ) ^ 2 * η ^ 2 / (αN / 2) ^ 2)))) * G.1 ≤
      G.numColored (Fintype.card (Reps M π))
        (gridAlg (Fintype.card (Reps M π)) (Fintype.card (Reps M π)) Sg Kg Bg U
          (G.1, adjTable G)) := by
  classical
  obtain ⟨χ, hmod, S, hScard, hS⟩ := hcol
  set m := Fintype.card (Reps M π) with hmdef
  set E := 512 * (m : ℝ) ^ 4 * ((2 + k) * δ / lam + lam) /
    (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) + 512 * (m : ℝ) ^ 2 * η ^ 2 / (αN / 2) ^ 2
    with hEdef
  have hm : 0 < m := Fintype.card_pos_iff.2 ⟨toRep M π ⟨0, hk⟩⟩
  have hmod' : ∀ a b, |M a b - pmodel G χ a b| ≤ δ := hmod
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · rw [hn0, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  obtain ⟨d, hd⟩ := hreg
  -- the degree is positive
  have hd0 : d ≠ 0 := by
    rintro rfl
    have hrow := hM.rowSum ⟨0, hk⟩
    have hle : ∑ b, M ⟨0, hk⟩ b ≤ ∑ _b : Fin k, δ := sum_le_sum fun b _ ↦ by
      have := hmod' ⟨0, hk⟩ b
      rw [pmodel_zero_of_degree_zero hd, sub_zero] at this
      exact (le_abs_self _).trans this
    rw [hrow] at hle
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    linarith
  -- the part sizes are close to `π`
  set s : Fin k → ℝ := fun a ↦ ((part G χ a).card : ℝ) with hsdef
  have hs : ∑ a, s a = G.1 := sum_card_part χ
  have hclose : ∀ a, |s a / G.1 - π a| ≤ C * δ := by
    refine hstab (fun a ↦ s a / G.1) δ ?_ ?_
    · rw [← sum_div, hs, div_self hnR.ne']
    · intro b
      have hst' : ∑ a, s a * pmodel G χ a b = s b := sum_card_mul_pmodel hd hd0 χ b
      have h3 : (∑ a, s a * pmodel G χ a b) / G.1 = s b / G.1 := by rw [hst']
      have h4 : ∑ a, s a / G.1 * pmodel G χ a b = (∑ a, s a * pmodel G χ a b) / G.1 := by
        rw [sum_div]
        exact sum_congr rfl fun a _ ↦ by ring
      have h5 : ∑ a, s a / G.1 * (M a b - pmodel G χ a b) =
          ∑ a, s a / G.1 * M a b - ∑ a, s a / G.1 * pmodel G χ a b := by
        simp only [mul_sub, sum_sub_distrib]
      have e1 : ∑ a, s a / G.1 * M a b - s b / G.1 =
          ∑ a, s a / G.1 * (M a b - pmodel G χ a b) := by
        linarith
      rw [e1]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ a, |s a / G.1 * (M a b - pmodel G χ a b)| ≤ ∑ a, s a / G.1 * δ :=
            sum_le_sum fun a _ ↦ by
              rw [abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_left (hmod' a b) (by positivity)
        _ = δ := by rw [← sum_mul, ← sum_div, hs, div_self hnR.ne', one_mul]
  have hsize0 : ∀ a, πmin / 2 * G.1 ≤ s a := by
    intro a
    have h := hclose a
    have h1 : π a - C * δ ≤ s a / G.1 := by linarith [neg_abs_le (s a / G.1 - π a)]
    have h2 : πmin / 2 ≤ s a / G.1 := by linarith [hπle a]
    rwa [le_div_iff₀ hnR] at h2
  -- the contracted partition
  set χ' := contract M π χ with hχ'
  have hsize : ∀ i : Reps M π, πmin / 2 * G.1 ≤ (part G χ' i).card := by
    intro i
    refine (hsize0 i.1).trans ?_
    change ((part G χ i.1).card : ℝ) ≤ (part G (contract M π χ) i).card
    exact_mod_cast card_le_card (part_subset_part_contract χ i)
  have hne : ∀ i : Reps M π, (part G χ' i).Nonempty := by
    intro i
    have : (0 : ℝ) < (part G χ' i).card := lt_of_lt_of_le (by positivity) (hsize i)
    exact card_pos.1 (by exact_mod_cast this)
  have hint : intWt G χ' ≤ (2 + k) * δ * G.1 := by
    have h1 := intWt_contract_le (π := π) hM χ hδ0 hmod'
    have h2 := intWt_le_of_cover hd χ S hS
    linarith
  have hsep : ∀ i j : Reps M π, i ≠ j →
      (αN / 2) ^ 2 ≤ ∑ l, (pmodel G χ' i l - pmodel G χ' j l) ^ 2 := by
    intro i j hij
    obtain ⟨l, hl⟩ := hsepN i j hij
    have hi := pmodel_contract_close χ hmod' i l (hne i)
    have hj := pmodel_contract_close χ hmod' j l (hne j)
    have hdiff : αN / 2 ≤ |pmodel G χ' i l - pmodel G χ' j l| := by
      have := abs_sub_abs_le_abs_sub
        (∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b)
        (pmodel G χ' i l - pmodel G χ' j l)
      have e : ∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b -
          (pmodel G χ' i l - pmodel G χ' j l) =
          -(pmodel G χ' i l - ∑ b ∈ rowGroup M l.1, M i.1 b) +
            (pmodel G χ' j l - ∑ b ∈ rowGroup M l.1, M j.1 b) := by ring
      rw [e] at this
      have := this.trans (abs_add_le _ _)
      rw [abs_neg] at this
      linarith
    calc (αN / 2) ^ 2 ≤ |pmodel G χ' i l - pmodel G χ' j l| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hdiff 2
      _ = (pmodel G χ' i l - pmodel G χ' j l) ^ 2 := sq_abs _
      _ ≤ ∑ l, (pmodel G χ' i l - pmodel G χ' j l) ^ 2 :=
          single_le_sum (fun l _ ↦ sq_nonneg (pmodel G χ' i l - pmodel G χ' j l)) (mem_univ l)
  -- Theorem 5.1 with the grid of centers
  obtain ⟨us, hus, ts, hcount⟩ := exists_good_grid hd hd0 χ' (Fintype.equivFin (Reps M π))
    hn (by positivity) hsize (by positivity) hsep hl0 hl1 hexp hint
    (by linarith : θ < 2 * θ) hθα U hnet hSg hK1 hK
  set B := univ.filter fun y : Fin G.1 ↦ clusterIdxC (List.ofFn us)
    (gridCenters m Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y ≠
      Fintype.equivFin (Reps M π) (χ' y) with hB
  have hBy : ∀ y, y ∉ B → clusterIdxC (List.ofFn us)
      (gridCenters m Sg Kg (Nat.sqrt G.1) (List.ofFn fun j ↦ (ts j : ℕ))) y =
        Fintype.equivFin (Reps M π) (contract M π χ y) := by
    intro y hy
    rw [hB, mem_filter] at hy
    push Not at hy
    exact hy (mem_univ y)
  -- the accounting
  have hacc := numColored_ge_contract_grid G χ S hS hm le_rfl (Fintype.equivFin (Reps M π))
    Sg Kg Bg U hB1 hB2 us hus ts B hBy
  have hcardc : ∀ i : Reps M π,
      ((part G (contract M π χ) i).card : ℝ) = ∑ a ∈ rowGroup M i.1, s a :=
    fun i ↦ card_part_contract χ i
  simp only [hcardc] at hacc
  have halpha := sub_sum_max_le_alpha (M := M) hπ.1 G.1 s hs (by positivity) hclose hn
  have hSn : (S.card : ℝ) ≤ δ * G.1 := hScard
  have hBn : (B.card : ℝ) ≤ E * G.1 := hcount
  nlinarith

end Alg

end BHSV25
