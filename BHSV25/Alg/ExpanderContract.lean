module

public import BHSV25.Alg.Variance
public import BHSV25.Alg.ModelFacts

/-!
# The contracted partition

The partition `χ'` of [BHSV25, Theorem 7.1] obtained from a partition `χ` into `k` parts by merging
the parts whose rows in the model `M` are equal (`BHSV25.Alg.contract`), with parts indexed by the
representatives of the groups of equal rows (`BHSV25.Alg.Reps`, `BHSV25.Alg.rowRep`).

* The parts of `χ'` are the unions of the parts of `χ` over the groups
  (`BHSV25.Alg.part_contract`), so weights and sizes add up (`BHSV25.Alg.wt_contract`,
  `BHSV25.Alg.card_part_contract`).
* **Few edges inside the merged parts** (`BHSV25.Alg.intWt_contract_le`): two colors with equal
  rows have `M_ab = 0` (the diagonal of `M` is `0`), so if the model of `χ` is `δ`-close to `M`,
  merging adds weight at most `k δ n` inside the parts.
* **The model of `χ'` is close to the contracted model** `N_il = ∑_{b ∈ S_l} M_ib`
  (`BHSV25.Alg.pmodel_contract_close`, the paper's Claim on `M(Ã, χ')`), and the rows of `N` are
  separated (`BHSV25.Alg.exists_sep_contracted`), since rows with equal sums over every group are
  equal.
* **The rounding of a merged part** (`BHSV25.Alg.card_inter_sub_card_sdiff_ge`): if a cluster `R`
  agrees with a merged part `P'` outside a set `B`, rounding it against the independent set
  `P \ S`, for a part `P ⊆ P'` of `χ` and the cover `S` of its inner edges, keeps at least
  `2 |P| - |P'| - 2 |S ∩ P'| - |B ∩ P'| - |B ∩ R|` vertices (net of the removals; the paper's
  `min(∑_{a ∈ S_i} |V_a|, 2 ∑_{a ≠ a*} |V_a|)`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix

variable {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ)

/-- The representatives of the groups of equal rows of `M`. -/
abbrev Reps : Type := {a : Fin k // rowRep M π a = a}

/-- The representative of the group of the color `a`. -/
noncomputable def toRep (a : Fin k) : Reps M π := ⟨rowRep M π a, rowRep_rowRep π a⟩

variable {M π}

theorem toRep_eq_iff {a : Fin k} {i : Reps M π} : toRep M π a = i ↔ M a = M i.1 := by
  rw [Subtype.ext_iff, toRep]
  constructor
  · intro h
    have h' : M (rowRep M π a) = M i.1 := congrArg M h
    exact (row_rowRep π a).symm.trans h'
  · intro h
    rw [← i.2]
    exact (rowRep_eq_rowRep_iff π).2 h

theorem mem_rowGroup_iff_toRep {b : Fin k} {i : Reps M π} :
    b ∈ rowGroup M i.1 ↔ toRep M π b = i := by
  rw [mem_rowGroup, toRep_eq_iff]

theorem toRep_val (i : Reps M π) : toRep M π i.1 = i := toRep_eq_iff.2 rfl

theorem rowGroup_toRep (a : Fin k) : rowGroup M (toRep M π a).1 = rowGroup M a :=
  rowGroup_eq_of_row_eq (row_rowRep π a)

/-- A sum over the colors, grouped by groups of equal rows. -/
theorem sum_reps_rowGroup {β : Type*} [AddCommMonoid β] (f : Fin k → β) :
    ∑ i : Reps M π, ∑ b ∈ rowGroup M i.1, f b = ∑ b, f b := by
  rw [← Finset.sum_fiberwise univ (toRep M π) f]
  refine sum_congr rfl fun i _ ↦ sum_congr ?_ fun _ _ ↦ rfl
  ext b
  simp [mem_rowGroup_iff_toRep]

/-- A positive lower bound for finitely many monotone properties, each holding for some positive
number. -/
theorem exists_pos_forall {β : Type*} [Finite β] (P : β → ℝ → Prop)
    (h : ∀ b, ∃ v, 0 < v ∧ P b v) (hmono : ∀ b v w, w ≤ v → P b v → P b w) :
    ∃ α, 0 < α ∧ ∀ b, P b α := by
  have := Fintype.ofFinite β
  choose v hv hP using h
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨1, one_pos, fun b ↦ hβ.elim b⟩
  refine ⟨univ.inf' univ_nonempty v, (lt_inf'_iff _).2 fun b _ ↦ hv b, fun b ↦ ?_⟩
  exact hmono b (v b) _ (inf'_le _ (mem_univ b)) (hP b)

/-- **The rows of the contracted model are separated.** -/
theorem exists_sep_contracted (hπ : IsStationary M π) :
    ∃ αN, 0 < αN ∧ ∀ i j : Reps M π, i ≠ j → ∃ l : Reps M π,
      αN ≤ |∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b| := by
  refine exists_pos_forall (fun (p : Reps M π × Reps M π) v ↦ p.1 ≠ p.2 → ∃ l : Reps M π,
    v ≤ |∑ b ∈ rowGroup M l.1, M p.1.1 b - ∑ b ∈ rowGroup M l.1, M p.2.1 b|) ?_ ?_
    |>.imp fun α h ↦ ⟨h.1, fun i j hij ↦ h.2 (i, j) hij⟩
  · rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h ↦ absurd hij h⟩
    have hrow : M i.1 ≠ M j.1 := by
      intro h
      apply hij
      rw [← toRep_val i]
      exact toRep_eq_iff.2 h
    have : ¬ ∀ l, ∑ b ∈ rowGroup M l, M i.1 b = ∑ b ∈ rowGroup M l, M j.1 b :=
      fun h ↦ hrow (row_eq_of_sum_rowGroup_eq hπ h)
    push Not at this
    obtain ⟨l0, hl0⟩ := this
    refine ⟨|∑ b ∈ rowGroup M l0, M i.1 b - ∑ b ∈ rowGroup M l0, M j.1 b|,
      abs_pos.2 (sub_ne_zero.2 hl0), fun _ ↦ ⟨toRep M π l0, ?_⟩⟩
    rw [rowGroup_toRep]
  · rintro p v w hwv h hne
    obtain ⟨l, hl⟩ := h hne
    exact ⟨l, hwv.trans hl⟩

/-! ### The contracted partition of a graph -/

section Graph

variable {G : Graph}

variable (M π) in
/-- **The contracted partition**: the group of equal rows of the color of each vertex. -/
noncomputable def contract (χ : Fin G.1 → Fin k) : Fin G.1 → Reps M π :=
  fun x ↦ toRep M π (χ x)

theorem part_contract (χ : Fin G.1 → Fin k) (i : Reps M π) :
    part G (contract M π χ) i = (rowGroup M i.1).biUnion (part G χ) := by
  ext x
  rw [mem_part, mem_biUnion, contract]
  constructor
  · intro h
    exact ⟨χ x, mem_rowGroup_iff_toRep.2 h, mem_part_self χ x⟩
  · rintro ⟨a, ha, hx⟩
    rw [mem_part.1 hx]
    exact mem_rowGroup_iff_toRep.1 ha

theorem pairwiseDisjoint_part (χ : Fin G.1 → Fin k) (s : Finset (Fin k)) :
    (s : Set (Fin k)).PairwiseDisjoint (part G χ) := by
  intro a _ b _ hab
  refine disjoint_left.2 fun x hxa hxb ↦ hab ?_
  rw [← mem_part.1 hxa, ← mem_part.1 hxb]

theorem sum_part_contract {β : Type*} [AddCommMonoid β] (χ : Fin G.1 → Fin k) (i : Reps M π)
    (F : Fin G.1 → β) :
    ∑ x ∈ part G (contract M π χ) i, F x = ∑ a ∈ rowGroup M i.1, ∑ x ∈ part G χ a, F x := by
  rw [part_contract, sum_biUnion (pairwiseDisjoint_part χ _)]

theorem wt_contract (χ : Fin G.1 → Fin k) (x : Fin G.1) (i : Reps M π) :
    wt G (contract M π χ) x i = ∑ b ∈ rowGroup M i.1, wt G χ x b :=
  sum_part_contract χ i (G.normAdj x)

theorem card_part_contract (χ : Fin G.1 → Fin k) (i : Reps M π) :
    ((part G (contract M π χ) i).card : ℝ) = ∑ a ∈ rowGroup M i.1, ((part G χ a).card : ℝ) := by
  rw [part_contract, card_biUnion (pairwiseDisjoint_part χ _)]
  push_cast
  rfl

theorem part_subset_part_contract (χ : Fin G.1 → Fin k) (i : Reps M π) :
    part G χ i.1 ⊆ part G (contract M π χ) i := by
  rw [part_contract]
  exact subset_biUnion_of_mem (part G χ) (self_mem_rowGroup i.1)

/-- **Few edges inside the merged parts.** -/
theorem intWt_contract_le (hM : IsModel M) (χ : Fin G.1 → Fin k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmod : ∀ a b, |M a b - pmodel G χ a b| ≤ δ) :
    intWt G (contract M π χ) ≤ intWt G χ + k * δ * G.1 := by
  have hsplit : ∀ x, wt G (contract M π χ) x (contract M π χ x) =
      wt G χ x (χ x) + ∑ b ∈ (rowGroup M (χ x)).erase (χ x), wt G χ x b := by
    intro x
    rw [wt_contract, contract, rowGroup_toRep, add_sum_erase _ _ (self_mem_rowGroup _)]
  have hsmall : ∀ a, ∀ b ∈ (rowGroup M a).erase a, pmodel G χ a b ≤ δ := by
    intro a b hb
    have hrow : M a = M b := (mem_rowGroup.1 (mem_of_mem_erase hb)).symm
    have h0 := eq_zero_of_row_eq hM hrow
    have := hmod a b
    rw [h0, zero_sub, abs_neg] at this
    exact (le_abs_self _).trans this
  rw [intWt, sum_congr rfl fun x _ ↦ hsplit x, sum_add_distrib, ← intWt]
  have hrest : ∑ x, ∑ b ∈ (rowGroup M (χ x)).erase (χ x), wt G χ x b ≤ k * δ * G.1 := by
    rw [← sum_part χ]
    calc ∑ a, ∑ x ∈ part G χ a, ∑ b ∈ (rowGroup M (χ x)).erase (χ x), wt G χ x b
        = ∑ a, ∑ b ∈ (rowGroup M a).erase a, (part G χ a).card * pmodel G χ a b := by
          refine sum_congr rfl fun a _ ↦ ?_
          rw [sum_congr rfl fun x hx ↦ by rw [mem_part.1 hx], sum_comm]
          exact sum_congr rfl fun b _ ↦ (card_mul_pmodel χ a b).symm
      _ ≤ ∑ a, ∑ _b : Fin k, (part G χ a).card * δ := by
          refine sum_le_sum fun a _ ↦ ?_
          calc ∑ b ∈ (rowGroup M a).erase a, (part G χ a).card * pmodel G χ a b
              ≤ ∑ _b ∈ (rowGroup M a).erase a, ((part G χ a).card : ℝ) * δ :=
                sum_le_sum fun b hb ↦ mul_le_mul_of_nonneg_left (hsmall a b hb)
                  (Nat.cast_nonneg _)
            _ ≤ ∑ _b : Fin k, ((part G χ a).card : ℝ) * δ :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦
                  mul_nonneg (Nat.cast_nonneg _) hδ
      _ = k * δ * G.1 := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← mul_sum, ← sum_mul, sum_card_part]
          ring
  linarith

/-- **The model of the contracted partition is close to the contracted model**
`N_il = ∑_{b ∈ S_l} M_ib`. -/
theorem pmodel_contract_close (χ : Fin G.1 → Fin k) {δ : ℝ}
    (hmod : ∀ a b, |M a b - pmodel G χ a b| ≤ δ) (i l : Reps M π)
    (hne : (part G (contract M π χ) i).Nonempty) :
    |pmodel G (contract M π χ) i l - ∑ b ∈ rowGroup M l.1, M i.1 b| ≤ k * δ := by
  set N := ∑ b ∈ rowGroup M l.1, M i.1 b with hN
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hmod i.1 i.1)
  have hden : (0 : ℝ) < ∑ a ∈ rowGroup M i.1, ((part G χ a).card : ℝ) := by
    rw [← card_part_contract]
    exact_mod_cast hne.card_pos
  have hnum : ∑ x ∈ part G (contract M π χ) i, wt G (contract M π χ) x l =
      ∑ a ∈ rowGroup M i.1, (part G χ a).card * ∑ b ∈ rowGroup M l.1, pmodel G χ a b := by
    rw [sum_part_contract]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [wt_contract]
    rw [sum_comm, mul_sum]
    exact sum_congr rfl fun b _ ↦ (card_mul_pmodel χ a b).symm
  have hrowN : ∀ a ∈ rowGroup M i.1, ∑ b ∈ rowGroup M l.1, M a b = N := by
    intro a ha
    rw [hN, mem_rowGroup.1 ha]
  have hdiff : ∀ a ∈ rowGroup M i.1,
      |∑ b ∈ rowGroup M l.1, pmodel G χ a b - N| ≤ k * δ := by
    intro a ha
    rw [← hrowN a ha, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b ∈ rowGroup M l.1, |pmodel G χ a b - M a b| ≤ ∑ _b ∈ rowGroup M l.1, δ :=
          sum_le_sum fun b _ ↦ by rw [abs_sub_comm]; exact hmod a b
      _ ≤ ∑ _b : Fin k, δ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ hδ
      _ = k * δ := by simp
  rw [pmodel, hnum, card_part_contract]
  rw [div_sub' hden.ne', abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have : ∑ a ∈ rowGroup M i.1, (part G χ a).card * ∑ b ∈ rowGroup M l.1, pmodel G χ a b -
      (∑ a ∈ rowGroup M i.1, ((part G χ a).card : ℝ)) * N =
      ∑ a ∈ rowGroup M i.1, (part G χ a).card *
        (∑ b ∈ rowGroup M l.1, pmodel G χ a b - N) := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ ↦ by ring
  rw [this, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha ↦ ?_)
  rw [abs_mul, Nat.abs_cast, mul_comm]
  exact mul_le_mul_of_nonneg_right (hdiff a ha) (Nat.cast_nonneg _)

end Graph

/-! ### The rounding of a merged part -/

/-- **The rounding of a merged part**: if `R` agrees with `P'` outside `B` and `P ⊆ P'`, then
`|R ∩ (P \ S)| - |R \ (P \ S)| ≥ 2 |P| - |P'| - 2 |S ∩ P'| - |B ∩ P'| - |B ∩ R|`. -/
theorem card_inter_sub_card_sdiff_ge {α : Type*} [DecidableEq α] (R P P' S B : Finset α)
    (hPP' : P ⊆ P') (h1 : ∀ y ∈ P', y ∉ B → y ∈ R) (h2 : ∀ y ∈ R, y ∉ B → y ∈ P') :
    2 * (P.card : ℝ) - P'.card - 2 * (S ∩ P').card - (B ∩ P').card - (B ∩ R).card ≤
      (R ∩ (P \ S)).card - (R \ (P \ S)).card := by
  -- `|P \ S| ≥ |P| - |S ∩ P'|`
  have hPS : (P.card : ℝ) - (S ∩ P').card ≤ (P \ S).card := by
    have e := card_sdiff_add_card_inter P S
    have : (P ∩ S).card ≤ (S ∩ P').card :=
      card_le_card fun y hy ↦ mem_inter.2 ⟨(mem_inter.1 hy).2, hPP' (mem_inter.1 hy).1⟩
    have e' : ((P \ S).card : ℝ) + (P ∩ S).card = P.card := by exact_mod_cast e
    have : ((P ∩ S).card : ℝ) ≤ (S ∩ P').card := by exact_mod_cast this
    linarith
  -- `|R ∩ (P \ S)| ≥ |P \ S| - |B ∩ P'|`
  have hin : ((P \ S).card : ℝ) - (B ∩ P').card ≤ (R ∩ (P \ S)).card := by
    have hsub : (P \ S) \ B ⊆ R ∩ (P \ S) := by
      intro y hy
      rw [mem_sdiff] at hy
      exact mem_inter.2 ⟨h1 y (hPP' (mem_sdiff.1 hy.1).1) hy.2, hy.1⟩
    have e := card_sdiff_add_card_inter (P \ S) B
    have hB : ((P \ S) ∩ B).card ≤ (B ∩ P').card :=
      card_le_card fun y hy ↦ mem_inter.2 ⟨(mem_inter.1 hy).2,
        hPP' (mem_sdiff.1 (mem_inter.1 hy).1).1⟩
    have h3 : (((P \ S) \ B).card : ℝ) ≤ (R ∩ (P \ S)).card := by exact_mod_cast card_le_card hsub
    have e' : (((P \ S) \ B).card : ℝ) + ((P \ S) ∩ B).card = (P \ S).card := by exact_mod_cast e
    have : (((P \ S) ∩ B).card : ℝ) ≤ (B ∩ P').card := by exact_mod_cast hB
    linarith
  -- `|R \ (P \ S)| ≤ |B ∩ R| + |P'| - |P \ S|`
  have hout : ((R \ (P \ S)).card : ℝ) ≤ (B ∩ R).card + P'.card - (P \ S).card := by
    have hsub : R \ (P \ S) ⊆ (B ∩ R) ∪ (P' \ (P \ S)) := by
      intro y hy
      rw [mem_sdiff] at hy
      by_cases hyB : y ∈ B
      · exact mem_union_left _ (mem_inter.2 ⟨hyB, hy.1⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨h2 y hy.1 hyB, hy.2⟩)
    have h3 := (card_le_card hsub).trans (card_union_le _ _)
    have e := card_sdiff_add_card_inter P' (P \ S)
    have hinter : P' ∩ (P \ S) = P \ S :=
      inter_eq_right.2 fun y hy ↦ hPP' (mem_sdiff.1 hy).1
    rw [hinter] at e
    have h3' : ((R \ (P \ S)).card : ℝ) ≤ (B ∩ R).card + (P' \ (P \ S)).card := by
      exact_mod_cast h3
    have e' : ((P' \ (P \ S)).card : ℝ) + (P \ S).card = P'.card := by exact_mod_cast e
    linarith
  linarith

end Alg

end BHSV25
