module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Repeated values among uniformly random columns

For values `α : Fin n → F` and a set `cols` of indices, the columns whose value is repeated
(`BHJK25.RS.PlantedAux.dupCols`) are at most twice as many as the columns whose value repeats an
earlier column (`BHJK25.RS.PlantedAux.laterCols`). For a fixed set `S` of `s` indices, at most
`n^s q^(n - s)` of the `q^n` values `α` (`q = |F|`) have every `v ∈ S` repeat an earlier value:
fix, for each `v ∈ S`, the earlier index `π v` it repeats; then `α` is determined by its values
outside `S`. So at least `t` repeating columns occur for at most `C(|cols|, t) n^t q^(n - t)` of
the values.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset

variable {F : Type*} {n : ℕ}

/-- Values that agree outside `S` and in which every `v ∈ S` repeats the earlier index `π v` are
equal. -/
theorem eq_of_repeat {S : Finset (Fin n)} (π : S → Fin n) {α α' : Fin n → F}
    (hα : ∀ v : S, π v < v ∧ α (π v) = α v) (hα' : ∀ v : S, π v < v ∧ α' (π v) = α' v)
    (hout : ∀ v, v ∉ S → α v = α' v) : α = α' := by
  suffices h : ∀ m, ∀ v : Fin n, (v : ℕ) = m → α v = α' v from funext fun v ↦ h _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hv
    by_cases hS : v ∈ S
    · obtain ⟨hlt, hα1⟩ := hα ⟨v, hS⟩
      obtain ⟨-, hα2⟩ := hα' ⟨v, hS⟩
      rw [← hα1, ← hα2]
      exact ih _ (hv ▸ hlt) _ rfl
    · exact hout v hS

variable [DecidableEq F]

/-- The columns `v ∈ cols` whose value `α v` is also the value of another column. -/
def dupCols (cols : Finset (Fin n)) (α : Fin n → F) : Finset (Fin n) :=
  cols.filter fun v ↦ ∃ w ∈ cols, w ≠ v ∧ α w = α v

/-- The columns `v ∈ cols` whose value `α v` is also the value of an earlier column. -/
def laterCols (cols : Finset (Fin n)) (α : Fin n → F) : Finset (Fin n) :=
  cols.filter fun v ↦ ∃ w ∈ cols, w < v ∧ α w = α v

/-- A column with a repeated value either repeats an earlier column, or is the first of its
value, and then its value is that of a later column, which repeats it. -/
theorem card_dupCols_le (cols : Finset (Fin n)) (α : Fin n → F) :
    (dupCols cols α).card ≤ 2 * (laterCols cols α).card := by
  have h1 : dupCols cols α ⊆ laterCols cols α ∪ (dupCols cols α \ laterCols cols α) := by
    intro v hv
    by_cases h : v ∈ laterCols cols α
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.2 ⟨hv, h⟩)
  have h2 : (dupCols cols α \ laterCols cols α).card ≤ (laterCols cols α).card := by
    calc _ ≤ ((laterCols cols α).image α).card := by
          apply card_le_card_of_injOn α
          · intro v hv
            simp only [coe_sdiff, Set.mem_sdiff, mem_coe, dupCols, laterCols, mem_filter] at hv
            obtain ⟨⟨hvc, w, hwc, hwv, hαw⟩, hnot⟩ := hv
            have hlt : v < w := by
              rcases lt_or_gt_of_ne hwv with h | h
              · exact absurd ⟨hvc, w, hwc, h, hαw⟩ hnot
              · exact h
            simp only [coe_image, Set.mem_image, mem_coe]
            exact ⟨w, mem_filter.2 ⟨hwc, v, hvc, hlt, hαw.symm⟩, hαw⟩
          · intro v hv v' hv' hαv
            simp only [coe_sdiff, Set.mem_sdiff, mem_coe, dupCols, laterCols, mem_filter] at hv hv'
            by_contra hne
            rcases lt_or_gt_of_ne hne with h | h
            · exact hv'.2 ⟨hv'.1.1, v, hv.1.1, h, hαv⟩
            · exact hv.2 ⟨hv.1.1, v', hv'.1.1, h, hαv.symm⟩
      _ ≤ _ := card_image_le
  calc (dupCols cols α).card
      ≤ (laterCols cols α ∪ (dupCols cols α \ laterCols cols α)).card := card_le_card h1
    _ ≤ (laterCols cols α).card + (dupCols cols α \ laterCols cols α).card := card_union_le _ _
    _ ≤ _ := by omega

variable [Fintype F]

/-- At most `n^|S| q^(n - |S|)` values have every `v ∈ S` repeat an earlier value. -/
theorem card_repeat_le (S : Finset (Fin n)) :
    (univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v).card *
        Fintype.card F ^ S.card ≤ n ^ S.card * Fintype.card F ^ n := by
  classical
  set A : (S → Fin n) → Finset (Fin n → F) :=
    fun π ↦ univ.filter fun α ↦ ∀ v : S, π v < v ∧ α (π v) = α v with hAdef
  have hsub : (univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v) ⊆
      univ.biUnion A := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and] at hα
    rw [mem_biUnion]
    refine ⟨fun v ↦ (hα v v.2).choose, mem_univ _, ?_⟩
    simp only [hAdef, mem_filter, mem_univ, true_and]
    exact fun v ↦ (hα v v.2).choose_spec
  have hout : Fintype.card {v : Fin n // v ∉ S} + S.card = n := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
    have := card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  have hA : ∀ π, (A π).card * Fintype.card F ^ S.card ≤ Fintype.card F ^ n := by
    intro π
    have hinj : Set.InjOn (fun α : Fin n → F ↦ fun v : {v : Fin n // v ∉ S} ↦ α v) (A π) := by
      intro α hα α' hα' heq
      simp only [hAdef, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hα hα'
      exact eq_of_repeat π hα hα' fun v hv ↦ congrFun heq ⟨v, hv⟩
    have hcard := card_le_card_of_injOn _ (fun _ _ ↦ mem_coe.2 (mem_univ _)) hinj
    rw [card_univ, Fintype.card_fun] at hcard
    calc (A π).card * Fintype.card F ^ S.card
        ≤ Fintype.card F ^ Fintype.card {v : Fin n // v ∉ S} * Fintype.card F ^ S.card :=
          Nat.mul_le_mul_right _ hcard
      _ = Fintype.card F ^ n := by rw [← pow_add, hout]
  calc _ ≤ (univ.biUnion A).card * Fintype.card F ^ S.card :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ π, (A π).card) * Fintype.card F ^ S.card := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ π, (A π).card * Fintype.card F ^ S.card := sum_mul _ _ _
    _ ≤ ∑ _π : S → Fin n, Fintype.card F ^ n := sum_le_sum fun π _ ↦ hA π
    _ = n ^ S.card * Fintype.card F ^ n := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
          smul_eq_mul]

/-- At least `t` columns repeat an earlier column for at most `C(|cols|, t) n^t q^(n - t)` of the
values. -/
theorem card_laterCols_le (cols : Finset (Fin n)) (t : ℕ) :
    (univ.filter fun α : Fin n → F ↦ t ≤ (laterCols cols α).card).card * Fintype.card F ^ t ≤
      cols.card.choose t * n ^ t * Fintype.card F ^ n := by
  classical
  have hsub : (univ.filter fun α : Fin n → F ↦ t ≤ (laterCols cols α).card) ⊆
      (cols.powersetCard t).biUnion
        fun S ↦ univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and] at hα
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hα
    rw [mem_biUnion]
    refine ⟨S, mem_powersetCard.2 ⟨hS.trans (filter_subset _ _), hcard⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro v hv
    obtain ⟨-, w, -, hw⟩ := mem_filter.1 (hS hv)
    exact ⟨w, hw⟩
  calc _ ≤ ((cols.powersetCard t).biUnion
        fun S ↦ univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v).card *
          Fintype.card F ^ t := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ S ∈ cols.powersetCard t,
          (univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v).card) *
          Fintype.card F ^ t := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ S ∈ cols.powersetCard t,
          (univ.filter fun α : Fin n → F ↦ ∀ v ∈ S, ∃ w, w < v ∧ α w = α v).card *
          Fintype.card F ^ t := sum_mul _ _ _
    _ ≤ ∑ _S ∈ cols.powersetCard t, n ^ t * Fintype.card F ^ n := by
        refine sum_le_sum fun S hS ↦ ?_
        have := card_repeat_le (F := F) S
        rwa [(mem_powersetCard.1 hS).2] at this
    _ = _ := by rw [sum_const, card_powersetCard, smul_eq_mul, mul_assoc]

end BHJK25.RS.PlantedAux
