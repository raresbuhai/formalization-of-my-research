module

public import BHSV25.Hard.ModelYes

/-!
# The design for Theorem 1.9 (2): no-instances

For a no-instance `G` of the gap problem of Bansal and Khot, without independent sets of `γ_B n`
vertices, a partial `k`-coloring of the blow-up `H` of the design of
`BHSV25/Hard/ModelDesign.lean` colors at most `(1 - α + 2k² / D + k / H + k γ_B) |V(H)|` vertices
(`BHSV25.Hard.ModelRed.Data.no`): the copies of `G` and the absorbers have color classes of fewer
than `γ_B n` vertices each (`BHSV25.Hard.Template.numColored_le`), and the independent types are
`m (m + 1) ∑_i s_i e_i ≤ m (m + 1) ∑_i s_i (2H κ_i + 2k)` of the `m (m + 1) 2H ∑_i s_i` types,
with `∑_i s_i κ_i ≤ D ∑_i π_i κ_i = D (1 - α)`.
-/

@[expose] public section

namespace BHSV25.Hard.ModelRed

open Finset LowRank Cayley

namespace Data

variable (X : Data) (a : ℕ)

theorem alpha_le_one : alpha X.M X.π ≤ 1 := by
  unfold alpha
  rw [← X.hπ.2.1]
  exact sum_le_sum fun c _ ↦ min_le_left _ _

theorem alpha_nonneg : 0 ≤ alpha X.M X.π := by
  unfold alpha
  exact sum_nonneg fun c _ ↦ le_min (X.π_pos c).le (sum_nonneg fun d _ ↦ (X.π_pos d).le)

theorem two_k_sq_le_D : 2 * (X.k : ℝ) ^ 2 ≤ X.D := by
  have h : ∑ i : Fin X.k, (2 * (X.k : ℝ) + 1) ≤ ∑ i, (X.D : ℝ) * X.π i :=
    sum_le_sum fun i _ ↦ X.hD i
  rw [← mul_sum, X.hπ.2.1, mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
  nlinarith

theorem W0_self_ne_one {τ : X.Ty} : X.W0 τ τ ≠ 1 ↔ ¬ X.copy τ ∧ ¬ X.absb τ := by
  rw [W0_self]
  constructor
  · intro h
    refine ⟨fun hc ↦ h ?_, fun ha ↦ h ?_⟩
    · rw [zi_of hc, zi_of_not (X.not_absb_of_copy hc)]; norm_num
    · rw [zi_of ha, zi_of_not (fun hc ↦ X.not_absb_of_copy hc ha)]; norm_num
  · rintro ⟨hc, ha⟩
    rw [zi_of_not hc, zi_of_not ha]
    norm_num

/-- The independent types are few. -/
theorem sum_s_e_le : ∑ i, (X.s i : ℝ) * X.e i ≤
    (1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D + X.k / X.H) * (2 * X.H * ∑ i, (X.s i : ℝ)) := by
  set S := ∑ i, (X.s i : ℝ)
  have hH : (0 : ℝ) < X.H := by exact_mod_cast X.hH
  have hk2 := X.two_k_sq_le_D
  have hk : (1 : ℝ) ≤ X.k := by exact_mod_cast X.one_le_k
  have hD : (0 : ℝ) < X.D := by nlinarith
  have hα1 := X.alpha_le_one
  have hα0 := X.alpha_nonneg
  have h1 : ∑ i, (X.s i : ℝ) * X.e i ≤ ∑ i, (X.s i : ℝ) * (2 * X.H * X.κc i + 2 * X.k) :=
    sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (X.e_le i) (Nat.cast_nonneg _)
  have h2 : ∑ i, (X.s i : ℝ) * (2 * X.H * X.κc i + 2 * X.k) =
      2 * X.H * ∑ i, (X.s i : ℝ) * X.κc i + 2 * X.k * S := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  have h3 : ∑ i, (X.s i : ℝ) * X.κc i ≤ X.D * (1 - alpha X.M X.π) := by
    rw [← X.sum_π_κ, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    have := mul_le_mul_of_nonneg_right (X.s_le i) (X.κc_nonneg i)
    linarith
  have hS : (X.D : ℝ) - X.k ^ 2 ≤ S := by
    have h : ∑ i : Fin X.k, ((X.D : ℝ) * X.π i - X.k) ≤ S := sum_le_sum fun i _ ↦ X.le_s i
    rw [sum_sub_distrib, ← mul_sum, X.hπ.2.1, mul_one, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    nlinarith
  have h4 : X.D * (1 - alpha X.M X.π) ≤ (1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D) * S := by
    have hc : 0 ≤ 1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D := by positivity
    have h5 := mul_le_mul_of_nonneg_left hS hc
    have h6 : (1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D) * (X.D - X.k ^ 2) =
        X.D * (1 - alpha X.M X.π) + X.k ^ 2 * (1 + alpha X.M X.π) -
          2 * (X.k : ℝ) ^ 4 / X.D := by
      field_simp; ring
    have h7 : 2 * (X.k : ℝ) ^ 4 / X.D ≤ X.k ^ 2 := by
      rw [div_le_iff₀ hD]; nlinarith
    nlinarith
  have hfin : 2 * X.k * S = X.k / X.H * (2 * X.H * S) := by field_simp
  calc ∑ i, (X.s i : ℝ) * X.e i ≤ 2 * X.H * ∑ i, (X.s i : ℝ) * X.κc i + 2 * X.k * S := h2 ▸ h1
    _ ≤ 2 * X.H * ((1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D) * S) + 2 * X.k * S := by
        have := h3.trans h4
        nlinarith
    _ = _ := by rw [hfin]; ring

/-- **No-instances**: a partial `k`-coloring of the blow-up colors at most
`(1 - α + 2k² / D + k / H + k γ_B) N` vertices. -/
theorem no (G : Graph) {γB : ℝ} (hγB : 0 ≤ γB)
    (hno : ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < γB * G.1)
    (c : List ℕ) (hc : (X.design.blow a G).IsPartialColoring X.k c) :
    ((X.design.blow a G).numColored X.k c : ℝ) ≤
      (1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D + X.k / X.H + X.k * γB) * (X.design.blow a G).1 := by
  have h0 := (X.design.template a).numColored_le G X.k c hc (γB * G.1) hno
  have hW1 : ((univ.filter fun u ↦ (X.design.template a).W u u ≠ 1).card : ℝ) =
      (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1) * ∑ i, (X.s i : ℝ) * X.e i) := by
    rw [← X.card_indep]
    have : (univ.filter fun u ↦ (X.design.template a).W u u ≠ 1) =
        univ.filter fun u ↦ ¬ X.copy (X.design.typ a u) ∧ ¬ X.absb (X.design.typ a u) := by
      refine filter_congr fun u _ ↦ ?_
      rw [← W0_self_ne_one]
      simp only [Design.Wc, Design.typ, ite_true]
    rw [this]
    exact_mod_cast X.design.card_cells a (fun τ ↦ ¬ X.copy τ ∧ ¬ X.absb τ)
  have hW2 : ((univ.filter fun u ↦ (X.design.template a).W u u = 1).card : ℝ) ≤
      Fintype.card (X.design.Cell a) := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have hN : ((X.design.blow a G).1 : ℝ) = Fintype.card (X.design.Cell a) * G.1 := by
    push_cast; rfl
  rw [hN, X.card_cells a]
  rw [hW1] at h0
  rw [X.card_cells a] at hW2
  have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have hse := X.sum_s_e_le
  set Γ : ℝ := (2 * 4 ^ a) ^ X.r
  set S := ∑ i, (X.s i : ℝ)
  have hΓ : 0 < Γ := by positivity
  have hm : (0 : ℝ) ≤ X.m * (X.m + 1) := by positivity
  have hk : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
  have e1 : Γ * (X.m * (X.m + 1) * ∑ i, (X.s i : ℝ) * X.e i) * G.1 ≤
      (1 - alpha X.M X.π + 2 * X.k ^ 2 / X.D + X.k / X.H) * (S * X.cnt * Γ * G.1) := by
    have hcnt : (X.cnt : ℝ) = 2 * X.H * (X.m * (X.m + 1)) := by unfold cnt; push_cast; ring
    rw [hcnt]
    have := mul_le_mul_of_nonneg_left hse (mul_nonneg (mul_nonneg hΓ.le hm) hn)
    nlinarith
  have e2 : ((univ.filter fun u ↦ (X.design.template a).W u u = 1).card : ℝ) *
      (X.k * (γB * G.1)) ≤ X.k * γB * (S * X.cnt * Γ * G.1) := by
    have := mul_le_mul_of_nonneg_right hW2 (mul_nonneg hk (mul_nonneg hγB hn))
    nlinarith
  push_cast at h0
  nlinarith

end Data

end BHSV25.Hard.ModelRed
