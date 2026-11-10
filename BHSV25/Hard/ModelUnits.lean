module

public import BHSV25.Model

/-!
# Coloring units along an interval

A tool for the design of `BHSV25/Hard/ModelDesign.lean`. For a probability vector `ρ` on `k`
colors and `L` units, the coloring `BHSV25.Hard.Units.col` gives the unit `u` the color `b` whose
interval `[F_b, F_b + ρ_b)` of `[0, 1)` contains the point `(2u + 1) / (2L)`, where `F_b` is the
weight of the colors before `b` (`BHSV25.Hard.Units.col_spec`).

* Only colors of positive weight are used (`BHSV25.Hard.Units.col_pos`), and each color `b` has
  `L ρ_b` units up to `k` (`BHSV25.Hard.Units.abs_card_col_sub_le`).
* For `L = 2H`, the units `u` and `u + H` (mod `L`, `BHSV25.Hard.Units.sh`) have the same color for
  at most `L ∑_b max(0, 2 ρ_b - 1) + 2k` units (`BHSV25.Hard.Units.card_col_sh_le`): two points at
  distance `1/2` lie in the same interval only if it is longer than `1/2`.
-/

@[expose] public section

namespace BHSV25.Hard.Units

open Finset

variable {k : ℕ} (ρ : Fin k → ℝ)

/-- The weight of the colors `c < j`. -/
noncomputable def cum (j : ℕ) : ℝ := ∑ c ∈ univ.filter (fun c : Fin k ↦ (c : ℕ) < j), ρ c

theorem cum_zero : cum ρ 0 = 0 := by simp [cum]

theorem cum_of_le {j : ℕ} (hj : k ≤ j) : cum ρ j = ∑ c, ρ c := by
  unfold cum
  rw [filter_true_of_mem fun c _ ↦ lt_of_lt_of_le c.2 hj]

theorem cum_succ {j : ℕ} (hj : j < k) : cum ρ (j + 1) = cum ρ j + ρ ⟨j, hj⟩ := by
  unfold cum
  have : univ.filter (fun c : Fin k ↦ (c : ℕ) < j + 1) =
      insert ⟨j, hj⟩ (univ.filter (fun c : Fin k ↦ (c : ℕ) < j)) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

/-- The point of `[0, 1)` of the unit `u` out of `L`. -/
noncomputable def pt (L u : ℕ) : ℝ := (2 * u + 1) / (2 * L)

open Classical in
/-- The index of the color of the unit `u`: the least `j` with `pt u < cum (j + 1)`. -/
noncomputable def colN (L u : ℕ) : ℕ :=
  if h : ∃ j, pt L u < cum ρ (j + 1) then Nat.find h else 0

variable {ρ}

theorem pos_of_sum_eq_one (h1 : ∑ c, ρ c = 1) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp at h1
  · exact h

theorem pt_lt_one {L u : ℕ} (hu : u < L) : pt L u < 1 := by
  unfold pt
  have hL' : (0 : ℝ) < L := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hu)
  have hL : (0 : ℝ) < 2 * L := by positivity
  rw [div_lt_one hL]
  have : (u : ℝ) + 1 ≤ L := by exact_mod_cast hu
  linarith

theorem pt_nonneg (L u : ℕ) : 0 ≤ pt L u := by unfold pt; positivity

open Classical in
theorem colN_spec (h1 : ∑ c, ρ c = 1) {L u : ℕ} (hu : u < L) :
    colN ρ L u < k ∧ cum ρ (colN ρ L u) ≤ pt L u ∧ pt L u < cum ρ (colN ρ L u + 1) := by
  have hk := pos_of_sum_eq_one h1
  have hex : ∃ j, pt L u < cum ρ (j + 1) :=
    ⟨k - 1, by rw [Nat.sub_add_cancel hk, cum_of_le ρ le_rfl, h1]; exact pt_lt_one hu⟩
  unfold colN
  rw [dite_eq_left hex]
  have hspec := Nat.find_spec hex
  have hlow : cum ρ (Nat.find hex) ≤ pt L u := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, cum_zero]; exact pt_nonneg L u
    · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show j' < Nat.find hex by omega)
      rw [hj']
      exact not_lt.1 this
  refine ⟨?_, hlow, hspec⟩
  by_contra hc
  rw [not_lt] at hc
  have e1 := cum_of_le ρ hc
  have e2 := cum_of_le ρ (show k ≤ Nat.find hex + 1 by omega)
  rw [h1] at e1 e2
  have := pt_lt_one hu
  linarith

variable (ρ)

/-- The color of the unit `u` out of `L` (`d` if there is none, which does not happen for
probability vectors). -/
noncomputable def col (d : Fin k) (L : ℕ) (u : Fin L) : Fin k :=
  if h : colN ρ L u < k then ⟨colN ρ L u, h⟩ else d

variable {ρ}

/-- **The color of a unit**: its point is in the interval of its color. -/
theorem col_spec (h1 : ∑ c, ρ c = 1) (d : Fin k) {L : ℕ} (u : Fin L) :
    cum ρ (col ρ d L u) ≤ pt L u ∧ pt L u < cum ρ (col ρ d L u) + ρ (col ρ d L u) := by
  obtain ⟨hk, hl, hu⟩ := colN_spec h1 u.2
  have : col ρ d L u = ⟨colN ρ L u, hk⟩ := dite_eq_left hk
  rw [this]
  exact ⟨hl, by rw [← cum_succ ρ hk]; exact hu⟩

theorem col_pos (h1 : ∑ c, ρ c = 1) (d : Fin k) {L : ℕ} (u : Fin L) : 0 < ρ (col ρ d L u) := by
  have := col_spec h1 d u
  linarith

/-- At most `L ℓ + 1` points lie in an interval of length `ℓ`. -/
theorem card_pt_le (L : ℕ) (x ℓ : ℝ) :
    ((univ.filter fun u : Fin L ↦ x ≤ pt L u ∧ pt L u < x + ℓ).card : ℝ) ≤ L * max 0 ℓ + 1 := by
  set S := univ.filter fun u : Fin L ↦ x ≤ pt L u ∧ pt L u < x + ℓ
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, card_empty, Nat.cast_zero]; positivity
  have h0 := (mem_filter.1 (S.min'_mem hS)).2
  have h1 := (mem_filter.1 (S.max'_mem hS)).2
  have hsub : S ⊆ Icc (S.min' hS) (S.max' hS) :=
    fun u hu ↦ mem_Icc.2 ⟨S.min'_le u hu, S.le_max' u hu⟩
  have hcard := card_le_card hsub
  rw [Fin.card_Icc] at hcard
  have hle : ((S.min' hS : Fin L) : ℕ) ≤ (S.max' hS : Fin L) :=
    Fin.le_iff_val_le_val.1 (S.min'_le _ (S.max'_mem hS))
  have hL : (0 : ℝ) < L := by
    have := (S.min' hS).2
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) this)
  have hcard' : (S.card : ℝ) ≤ ((S.max' hS : Fin L) : ℝ) - (S.min' hS : Fin L) + 1 := by
    have : S.card ≤ ((S.max' hS : Fin L) : ℕ) - (S.min' hS : Fin L) + 1 := by omega
    calc (S.card : ℝ) ≤ ((((S.max' hS : Fin L) : ℕ) - (S.min' hS : Fin L) + 1 : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = _ := by rw [Nat.cast_add, Nat.cast_sub hle]; simp
  have hdiff : pt L (S.max' hS : Fin L) - pt L (S.min' hS : Fin L) =
      (((S.max' hS : Fin L) : ℝ) - (S.min' hS : Fin L)) / L := by
    unfold pt; field_simp; ring
  have hlt : (((S.max' hS : Fin L) : ℝ) - (S.min' hS : Fin L)) / L < ℓ := by
    rw [← hdiff]; linarith [h0.1, h1.2]
  rw [div_lt_iff₀ hL] at hlt
  have : ℓ ≤ max 0 ℓ := le_max_right _ _
  nlinarith

theorem card_col_le (h0 : ∀ c, 0 ≤ ρ c) (h1 : ∑ c, ρ c = 1) (d : Fin k) (L : ℕ) (b : Fin k) :
    ((univ.filter fun u : Fin L ↦ col ρ d L u = b).card : ℝ) ≤ L * ρ b + 1 := by
  have hsub : (univ.filter fun u : Fin L ↦ col ρ d L u = b) ⊆
      univ.filter fun u : Fin L ↦ cum ρ b ≤ pt L u ∧ pt L u < cum ρ b + ρ b := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    rw [← hu]
    exact col_spec h1 d u
  have h := card_pt_le L (cum ρ b) (ρ b)
  rw [max_eq_right (h0 b)] at h
  exact (by exact_mod_cast card_le_card hsub : ((univ.filter fun u : Fin L ↦
    col ρ d L u = b).card : ℝ) ≤ _).trans h

theorem sum_card_col (d : Fin k) (L : ℕ) :
    ∑ b, ((univ.filter fun u : Fin L ↦ col ρ d L u = b).card : ℝ) = L := by
  have h := card_eq_sum_card_fiberwise (f := col ρ d L) (s := (univ : Finset (Fin L)))
    (t := univ) (fun _ _ ↦ mem_coe.2 (mem_univ _))
  rw [card_univ, Fintype.card_fin] at h
  exact_mod_cast h.symm

/-- **Each color has `L ρ_b` units, up to `k`.** -/
theorem abs_card_col_sub_le (h0 : ∀ c, 0 ≤ ρ c) (h1 : ∑ c, ρ c = 1) (d : Fin k) (L : ℕ)
    (b : Fin k) :
    |((univ.filter fun u : Fin L ↦ col ρ d L u = b).card : ℝ) - L * ρ b| ≤ k := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast pos_of_sum_eq_one h1
  set f : Fin k → ℝ := fun c ↦ ((univ.filter fun u : Fin L ↦ col ρ d L u = c).card : ℝ)
  have hup : ∀ c, f c ≤ L * ρ c + 1 := fun c ↦ card_col_le h0 h1 d L c
  have hsum : ∑ c, f c = L := sum_card_col d L
  have hrest : ∑ c ∈ univ.erase b, f c ≤ ∑ c ∈ univ.erase b, (L * ρ c + 1) :=
    sum_le_sum fun c _ ↦ hup c
  rw [sum_add_distrib, ← mul_sum, sum_const, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hrest
  have e1 := add_sum_erase univ f (mem_univ b)
  have e2 := add_sum_erase univ ρ (mem_univ b)
  rw [hsum] at e1
  rw [h1] at e2
  have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
    rw [Nat.cast_sub (by exact_mod_cast hk)]; simp
  rw [hk1] at hrest
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  refine abs_le.2 ⟨?_, ?_⟩
  · have : f b = L - ∑ c ∈ univ.erase b, f c := by linarith
    have h3 : ∑ c ∈ univ.erase b, ρ c = 1 - ρ b := by linarith
    rw [h3] at hrest
    change -(k : ℝ) ≤ f b - L * ρ b
    nlinarith
  · change f b - L * ρ b ≤ k
    linarith [hup b]

/-! ### The half shift -/

/-- The shift by `H` modulo `2H`. -/
def sh (H : ℕ) (u : Fin (2 * H)) : Fin (2 * H) :=
  ⟨(u + H) % (2 * H), Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) u.2)⟩

theorem sh_val_lt {H : ℕ} {u : Fin (2 * H)} (h : (u : ℕ) < H) : (sh H u : ℕ) = u + H := by
  simp only [sh]
  exact Nat.mod_eq_of_lt (by omega)

theorem sh_val_ge {H : ℕ} {u : Fin (2 * H)} (h : H ≤ (u : ℕ)) : (sh H u : ℕ) = u - H := by
  simp only [sh]
  have hu := u.2
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem sh_sh (H : ℕ) (u : Fin (2 * H)) : sh H (sh H u) = u := by
  ext
  rcases lt_or_ge (u : ℕ) H with h | h
  · rw [sh_val_ge (by rw [sh_val_lt h]; omega), sh_val_lt h]; omega
  · have h' : ((sh H u : Fin (2 * H)) : ℕ) < H := by rw [sh_val_ge h]; have := u.2; omega
    rw [sh_val_lt h', sh_val_ge h]; omega

theorem pt_sh_lt {H : ℕ} {u : Fin (2 * H)} (h : (u : ℕ) < H) :
    pt (2 * H) (sh H u) = pt (2 * H) u + 1 / 2 := by
  have hH : (0 : ℝ) < H := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) h)
  unfold pt
  rw [sh_val_lt h]
  push_cast
  field_simp
  ring

theorem pt_sh_ge {H : ℕ} {u : Fin (2 * H)} (h : H ≤ (u : ℕ)) :
    pt (2 * H) (sh H u) = pt (2 * H) u - 1 / 2 := by
  have hH : (0 : ℝ) < H := by
    have := u.2; exact_mod_cast (show 0 < H by omega)
  unfold pt
  rw [sh_val_ge h, Nat.cast_sub h]
  push_cast
  field_simp
  ring

/-- **Few units share their color with their shift**: at most
`2H ∑_b max(0, 2 ρ_b - 1) + 2k`. -/
theorem card_col_sh_le (h1 : ∑ c, ρ c = 1) (d : Fin k) (H : ℕ) :
    ((univ.filter fun u : Fin (2 * H) ↦ col ρ d (2 * H) u = col ρ d (2 * H) (sh H u)).card : ℝ)
      ≤ 2 * H * ∑ b, max 0 (2 * ρ b - 1) + 2 * k := by
  set S := univ.filter fun u : Fin (2 * H) ↦ col ρ d (2 * H) u = col ρ d (2 * H) (sh H u)
  have hfib := card_eq_sum_card_fiberwise (f := col ρ d (2 * H)) (s := S) (t := univ)
    (fun _ _ ↦ mem_coe.2 (mem_univ _))
  have hb : ∀ b, (((S.filter fun u ↦ col ρ d (2 * H) u = b).card : ℕ) : ℝ) ≤
      2 * H * max 0 (2 * ρ b - 1) + 2 := by
    intro b
    set x := cum ρ b
    have hsub : (S.filter fun u ↦ col ρ d (2 * H) u = b) ⊆
        (univ.filter fun u : Fin (2 * H) ↦ x ≤ pt (2 * H) u ∧ pt (2 * H) u < x + (ρ b - 1 / 2)) ∪
        (univ.filter fun u : Fin (2 * H) ↦
          x + 1 / 2 ≤ pt (2 * H) u ∧ pt (2 * H) u < x + 1 / 2 + (ρ b - 1 / 2)) := by
      intro u hu
      simp only [S, mem_filter, mem_univ, true_and] at hu
      obtain ⟨hsh, hub⟩ := hu
      have hs1 := col_spec h1 d u
      have hs2 := col_spec h1 d (sh H u)
      rw [hub] at hs1
      rw [← hsh, hub] at hs2
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases lt_or_ge (u : ℕ) H with h | h
      · rw [pt_sh_lt h] at hs2
        left; constructor <;> linarith
      · rw [pt_sh_ge h] at hs2
        right; constructor <;> linarith
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    have hA := card_pt_le (2 * H) x (ρ b - 1 / 2)
    have hB := card_pt_le (2 * H) (x + 1 / 2) (ρ b - 1 / 2)
    have hmax : 2 * max 0 (ρ b - 1 / 2) = max 0 (2 * ρ b - 1) := by
      rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]; ring_nf
    have hc' : ((S.filter fun u ↦ col ρ d (2 * H) u = b).card : ℝ) ≤
        ((univ.filter fun u : Fin (2 * H) ↦
          x ≤ pt (2 * H) u ∧ pt (2 * H) u < x + (ρ b - 1 / 2)).card : ℝ) +
        ((univ.filter fun u : Fin (2 * H) ↦
          x + 1 / 2 ≤ pt (2 * H) u ∧ pt (2 * H) u < x + 1 / 2 + (ρ b - 1 / 2)).card : ℝ) := by
      exact_mod_cast hc
    push_cast at hA hB ⊢
    rw [← hmax]
    linarith
  rw [hfib]
  push_cast
  calc ∑ b, (((S.filter fun u ↦ col ρ d (2 * H) u = b).card : ℕ) : ℝ)
      ≤ ∑ b : Fin k, (2 * H * max 0 (2 * ρ b - 1) + 2) := sum_le_sum fun b _ ↦ hb b
    _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end BHSV25.Hard.Units
