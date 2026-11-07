module

public import BHSV25.Hard.ModelDesign

/-!
# The design for Theorem 1.9 (2): labels and counts

The coloring of the yes-instances (`BHSV25.Hard.ModelRed.Data.labels`): a type `(x, u, α, β)` of
group `i` has the color `c₁ = col_i u` outside `J` and `c₂ = col_i (u + H)` on `J` (`c₂ = c₁` for
`β = m`), and the absorbers are the garbage. All colors of a type are in the class of its group,
so types of adjacent groups have disjoint colors (`BHSV25.Hard.ModelRed.Data.labels_valid`).

Counts: the color `b` is `c₁` of `m (m + 1) ∑_i s_i ℓ_ib` types, where `ℓ_ib` is the number of
units of group `i` of color `b`, and as many types have `c₂ = b`; the absorbers are at most a
`1 / (m + 1)` fraction of the types; and the independent types (`W⁰ τ τ ≠ 1`) are
`m (m + 1) ∑_i s_i e_i`, where `e_i` is the number of units `u` of group `i` with
`col_i u = col_i (u + H)`.
-/

@[expose] public section

namespace BHSV25.Hard.ModelRed

open Finset LowRank

namespace Data

variable (X : Data)

/-! ### Colors -/

/-- The color of a type outside `J`. -/
noncomputable def c₁ (τ : X.Ty) : Fin X.k := X.colC τ.1.1.1 τ.2.1

/-- The color of a type on `J`. -/
noncomputable def c₂ (τ : X.Ty) : Fin X.k :=
  if τ.2.2.2 = Fin.last X.m then X.colC τ.1.1.1 τ.2.1 else X.colC τ.1.1.1 (Units.sh X.H τ.2.1)

theorem row_c₁ (τ : X.Ty) : X.M (X.c₁ τ) = X.M τ.1.1.1 := X.row_colC _ _

theorem row_c₂ (τ : X.Ty) : X.M (X.c₂ τ) = X.M τ.1.1.1 := by
  unfold c₂; split_ifs <;> exact X.row_colC _ _

/-- The labels of the cells. -/
noncomputable abbrev labels (a : ℕ) : (X.design.template a).Labels X.k :=
  X.design.labels a X.c₁ X.c₂ X.absb

theorem W0_self (τ : X.Ty) : X.W0 τ τ = zi (X.copy τ) + zi (X.absb τ) := by
  unfold W0
  have e1 : zi (X.copy τ ∧ τ = τ) = zi (X.copy τ) := zi_congr (and_iff_left rfl)
  have e2 : zi (X.absb τ ∧ X.absb τ ∧ τ.1 = τ.1 ∧ τ.2.1 = τ.2.1) = zi (X.absb τ) :=
    zi_congr ⟨fun h ↦ h.1, fun h ↦ ⟨h, h, rfl, rfl⟩⟩
  have e3 : zi (X.copy τ ∧ τ = X.host τ) = 0 :=
    zi_of_not fun h ↦ h.1.1 (congrArg (fun y : X.Ty ↦ y.2.2.2) h.2)
  have e4 : zi (X.absb τ ∧ τ.1 = X.swap τ.1 ∧ τ.2.1 = τ.2.1 ∧ τ.2.2.1 = τ.2.2.1 ∧
      τ.2.2.2 ≠ Fin.last X.m) = 0 := zi_of_not fun h ↦ X.swap_ne τ.1 h.2.1.symm
  rw [e1, e2, e3, e4]
  ring

theorem absb_host {τ : X.Ty} (h : X.copy τ) : X.absb (X.host τ) := ⟨rfl, h.2⟩

/-- **The labels are valid.** -/
theorem labels_valid (a : ℕ) : (X.labels a).Valid := by
  refine Design.labels_valid X.design a X.c₁ X.c₂ X.absb (fun τ τ' hne hq ↦ ?_)
    (fun τ τ' hne hW ↦ ?_) (fun τ h ↦ ?_)
  · -- adjacent groups have disjoint colors
    have hw : 0 < X.w τ.1.1.1 τ'.1.1.1 := by
      have : 0 < X.q τ.1.1.1 τ'.1.1.1 := hq
      unfold q at this
      exact Nat.pos_of_ne_zero fun h ↦ by rw [h, mul_zero] at this; exact lt_irrefl _ this
    have hM := X.M_pos_of_w hw
    have key : ∀ c c' : Fin X.k, X.M c = X.M τ.1.1.1 → X.M c' = X.M τ'.1.1.1 → c ≠ c' := by
      intro c c' hc hc' hcc
      rw [hcc, hc'] at hc
      have := Alg.eq_zero_of_row_eq X.hM hc.symm
      rw [this] at hM
      exact lt_irrefl _ hM
    exact ⟨key _ _ (X.row_c₁ τ) (X.row_c₁ τ'), key _ _ (X.row_c₁ τ) (X.row_c₂ τ'),
      key _ _ (X.row_c₂ τ) (X.row_c₁ τ'), key _ _ (X.row_c₂ τ) (X.row_c₂ τ')⟩
  · -- the correction only joins copies to absorbers and absorbers to absorbers
    by_cases ha : X.absb τ
    · exact Or.inl ha
    · right; left
      change X.W0 τ τ' ≠ 0 at hW
      unfold W0 at hW
      rw [zi_of_not (P := X.copy τ ∧ τ' = τ) fun h ↦ hne h.2.symm,
        zi_of_not (P := X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) fun h ↦ ha h.1,
        zi_of_not (P := X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
          τ'.2.2.2 ≠ Fin.last X.m) fun h ↦ ha h.1] at hW
      by_cases h3 : X.copy τ ∧ τ' = X.host τ
      · rw [h3.2]; exact X.absb_host h3.1
      · rw [zi_of_not h3] at hW; exact absurd rfl hW
  · -- copies have two colors
    change X.W0 τ τ = 1 at h
    rw [W0_self] at h
    by_cases ha : X.absb τ
    · exact Or.inl ha
    · right
      have hc : X.copy τ := by
        by_contra hc
        rw [zi_of_not hc, zi_of_not ha] at h
        exact absurd h (by norm_num)
      unfold c₁ c₂
      rw [ite_eq_right hc.1]
      exact hc.2

/-! ### Counting types -/

theorem card_HU : Fintype.card X.HU = ∑ i, X.s i := by
  have := X.sum_HU (R := ℕ) (fun _ _ ↦ 1)
  simp only [smul_eq_mul, mul_one, sum_const, card_univ] at this
  rw [this]
  rfl

theorem card_Ty : Fintype.card X.Ty = (∑ i, X.s i) * X.cnt := by
  simp only [Fintype.card_prod, Fintype.card_fin, card_HU, cnt]

/-- Counting the types by their host unit and color unit. -/
theorem card_filter_ty (Q : X.HU → Fin (2 * X.H) → Prop) [∀ x u, Decidable (Q x u)] :
    ((univ.filter fun τ : X.Ty ↦ Q τ.1 τ.2.1).card : ℝ) =
      X.m * (X.m + 1) * ∑ x, ((univ.filter fun u ↦ Q x u).card : ℝ) := by
  rw [card_filter, mul_sum]
  push_cast
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [card_filter, Fintype.sum_prod_type]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [Fintype.sum_prod_type]
  by_cases hQ : Q x u <;> simp [hQ]
  ring

/-- The number of color units of group `i` with color `b`. -/
noncomputable def ℓ (i b : Fin X.k) : ℕ := (univ.filter fun u ↦ X.colC i u = b).card

/-- The number of color units of group `i` with the color of their shift. -/
noncomputable def e (i : Fin X.k) : ℕ :=
  (univ.filter fun u ↦ X.colC i u = X.colC i (Units.sh X.H u)).card

theorem sum_HU_real (G : Fin X.k → ℝ) : ∑ x : X.HU, G x.1.1 = ∑ i, (X.s i : ℝ) * G i := by
  rw [X.sum_HU (fun i _ ↦ G i)]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [nsmul_eq_mul, ← sum_mul, s]
  push_cast
  rfl

theorem card_c₁ (b : Fin X.k) :
    ((univ.filter fun τ ↦ X.c₁ τ = b).card : ℝ) =
      X.m * (X.m + 1) * ∑ i, (X.s i : ℝ) * X.ℓ i b := by
  have := X.card_filter_ty (fun x u ↦ X.colC x.1.1 u = b)
  rw [X.sum_HU_real (fun i ↦ ((univ.filter fun u ↦ X.colC i u = b).card : ℝ))] at this
  exact this

/-- The involution of the types exchanging the two colors. -/
def φ (τ : X.Ty) : X.Ty :=
  (τ.1, if τ.2.2.2 = Fin.last X.m then τ.2.1 else Units.sh X.H τ.2.1, τ.2.2.1, τ.2.2.2)

theorem φ_φ (τ : X.Ty) : X.φ (X.φ τ) = τ := by
  obtain ⟨x, u, α, β⟩ := τ
  unfold φ
  by_cases h : β = Fin.last X.m
  · simp [h]
  · simp [h, Units.sh_sh]

theorem c₂_eq (τ : X.Ty) : X.c₂ τ = X.c₁ (X.φ τ) := by
  unfold c₂ c₁ φ
  split_ifs <;> rfl

theorem card_c₂ (b : Fin X.k) :
    (univ.filter fun τ ↦ X.c₂ τ = b).card = (univ.filter fun τ ↦ X.c₁ τ = b).card := by
  refine card_bij (fun τ _ ↦ X.φ τ) (fun τ hτ ↦ ?_) (fun τ _ τ' _ h ↦ ?_) (fun τ hτ ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    rw [← c₂_eq]; exact hτ
  · rw [← X.φ_φ τ, h, X.φ_φ]
  · refine ⟨X.φ τ, ?_, X.φ_φ τ⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    rw [c₂_eq, X.φ_φ]; exact hτ

theorem card_absb_le :
    ((univ.filter X.absb).card : ℝ) * (X.m + 1) ≤ Fintype.card X.Ty := by
  have hsub : univ.filter X.absb ⊆ univ.filter fun τ : X.Ty ↦ τ.2.2.2 = Fin.last X.m :=
    fun τ hτ ↦ by simp only [mem_filter, mem_univ, true_and] at hτ ⊢; exact hτ.1
  have h1 : ((univ.filter fun τ : X.Ty ↦ τ.2.2.2 = Fin.last X.m).card : ℝ) * (X.m + 1) =
      Fintype.card X.Ty := by
    rw [card_filter]
    push_cast
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin]
    simp [sum_ite_eq']
    ring
  rw [← h1]
  have := (Nat.cast_le (α := ℝ)).2 (card_le_card hsub)
  nlinarith

/-- **The independent types.** -/
theorem card_indep :
    ((univ.filter fun τ : X.Ty ↦ ¬ X.copy τ ∧ ¬ X.absb τ).card : ℝ) =
      X.m * (X.m + 1) * ∑ i, (X.s i : ℝ) * X.e i := by
  have hpt : ∀ τ : X.Ty, (¬ X.copy τ ∧ ¬ X.absb τ) ↔
      (if τ.2.2.2 = Fin.last X.m then ¬ X.cp (X.swap τ.1) τ.2.1 else ¬ X.cp τ.1 τ.2.1) := by
    intro τ
    unfold copy absb
    by_cases h : τ.2.2.2 = Fin.last X.m <;> simp [h]
  rw [card_filter]
  push_cast
  simp_rw [hpt]
  simp only [Fintype.sum_prod_type]
  have hx : ∀ x : X.HU, (∑ u, ∑ _α : Fin X.m, ∑ β : Fin (X.m + 1),
      (if (if β = Fin.last X.m then ¬ X.cp (X.swap x) u else ¬ X.cp x u) then (1 : ℝ) else 0)) =
      X.m * (X.m * ((univ.filter fun u ↦ ¬ X.cp x u).card : ℝ) +
        ((univ.filter fun u ↦ ¬ X.cp (X.swap x) u).card : ℝ)) := by
    intro x
    have hu : ∀ u, ∑ _α : Fin X.m, ∑ β : Fin (X.m + 1),
        (if (if β = Fin.last X.m then ¬ X.cp (X.swap x) u else ¬ X.cp x u) then (1 : ℝ)
          else 0) =
        X.m * (X.m * (if ¬ X.cp x u then 1 else 0) + (if ¬ X.cp (X.swap x) u then 1 else 0)) := by
      intro u
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_ne_last, ↓reduceIte, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [sum_congr rfl fun u _ ↦ hu u, card_filter, card_filter]
    push_cast
    rw [← mul_sum, sum_add_distrib, ← mul_sum]
  simp_rw [hx]
  rw [← mul_sum, sum_add_distrib, ← mul_sum]
  have hsw : ∑ x : X.HU, ((univ.filter fun u ↦ ¬ X.cp (X.swap x) u).card : ℝ) =
      ∑ x : X.HU, ((univ.filter fun u ↦ ¬ X.cp x u).card : ℝ) :=
    Fintype.sum_equiv (Function.Involutive.toPerm X.swap X.swap_swap) _ _ fun _ ↦ rfl
  rw [hsw]
  have he : ∑ x : X.HU, ((univ.filter fun u ↦ ¬ X.cp x u).card : ℝ) =
      ∑ i, (X.s i : ℝ) * X.e i := by
    rw [← X.sum_HU_real (fun i ↦ (X.e i : ℝ))]
    refine sum_congr rfl fun x _ ↦ ?_
    unfold e cp
    simp only [not_not]
  rw [he]
  ring

end Data

end BHSV25.Hard.ModelRed
