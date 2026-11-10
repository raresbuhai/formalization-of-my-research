module

public import ABBKS26.Assembly.ExecData

/-! Executable weight-grid resets and their accounting for the frame filter. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux

open Common
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

variable {α : Type} {enc : α ↪ List Bool}

theorem roundRat_polytime {p : α → ℕ} {q : α → ℚ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hq : ComputableInPolyTime q enc encRat) :
    ComputableInPolyTime (fun x ↦ roundRat (p x) (q x)) enc encRat := by
  unfold roundRat
  exact rat_div' (rat_intCast' (rat_floor' (rat_mul' (rat_two_pow' hp) hq)))
    (rat_two_pow' hp)

theorem updateWeight_polytime {p : α → ℕ} {w s M : α → ℚ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hw : ComputableInPolyTime w enc encRat)
    (hs : ComputableInPolyTime s enc encRat)
    (hM : ComputableInPolyTime M enc encRat) :
    ComputableInPolyTime (fun x ↦ Robust.updateWeight (p x) (w x) (s x) (M x))
      enc encRat := by
  unfold Robust.updateWeight
  exact roundRat_polytime hp (rat_mul' hw (rat_sub' (const 1) (rat_div' hs hM)))

def reset (p : ℕ) (M : ℚ) (weights scores : Vector) : Vector :=
  (weights.zip scores).map fun ws ↦ Robust.updateWeight p ws.1 ws.2 M

theorem reset_length (p : ℕ) (M : ℚ) (weights scores : Vector) :
    (reset p M weights scores).length = min weights.length scores.length := by
  simp [reset]

theorem reset_polytime {p : α → ℕ} {M : α → ℚ} {w s : α → Vector}
    (hp : ComputableInPolyTime p enc encUnary)
    (hM : ComputableInPolyTime M enc encRat)
    (hw : ComputableInPolyTime w enc encVector)
    (hs : ComputableInPolyTime s enc encVector) :
    ComputableInPolyTime (fun x ↦ reset (p x) (M x) (w x) (s x)) enc encVector := by
  unfold reset
  apply mapWithInput ((zip encRat encRat).comp (hw.prod hs))
  exact updateWeight_polytime (hp.comp (fst _ _)) ((fst _ _).comp (snd _ _))
    ((snd _ _).comp (snd _ _)) (hM.comp (fst _ _))


theorem roundRat_error (p : ℕ) (q : ℚ) :
    0 ≤ q - roundRat p q ∧ q - roundRat p q < 1 / (2 : ℚ) ^ p := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have hlo := Int.floor_le ((2 : ℚ) ^ p * q)
  have hhi := Int.lt_floor_add_one ((2 : ℚ) ^ p * q)
  have he : (q - roundRat p q) * 2 ^ p =
      2 ^ p * q - (⌊(2 : ℚ) ^ p * q⌋ : ℚ) := by
    unfold roundRat
    field_simp
  constructor
  · apply (mul_nonneg_iff_of_pos_right hp).mp
    rw [he]
    linarith only [hlo]
  · apply (lt_div_iff₀ hp).mpr
    rw [he]
    linarith only [hhi]

theorem roundRat_nonneg (p : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ roundRat p q := by
  unfold roundRat
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity) hq)

theorem roundRat_le (p : ℕ) (q : ℚ) : roundRat p q ≤ q :=
  sub_nonneg.mp (roundRat_error p q).1

theorem updateWeight_bounds (p : ℕ) {w s M : ℚ}
    (hw : 0 ≤ w) (hs : 0 ≤ s) (hM : 0 < M) (hsM : s ≤ M) :
    0 ≤ Robust.updateWeight p w s M ∧ Robust.updateWeight p w s M ≤ w := by
  have hraw : 0 ≤ w * (1 - s / M) :=
    mul_nonneg hw (sub_nonneg.mpr ((div_le_one hM).mpr hsM))
  refine ⟨roundRat_nonneg p hraw, (roundRat_le p _).trans ?_⟩
  exact mul_le_of_le_one_right hw (sub_le_self _ (div_nonneg hs hM.le))

theorem updateWeight_eq_zero (p : ℕ) (w M : ℚ) (hM : M ≠ 0) :
    Robust.updateWeight p w M M = 0 := by
  simp [Robust.updateWeight, hM, roundRat]

theorem updateWeight_loss (p : ℕ) (w s M : ℚ) :
    w * s / M ≤ w - Robust.updateWeight p w s M ∧
      w - Robust.updateWeight p w s M ≤ w * s / M + 1 / (2 : ℚ) ^ p := by
  have h := roundRat_error p (w * (1 - s / M))
  change 0 ≤ w * (1 - s / M) - Robust.updateWeight p w s M ∧
    w * (1 - s / M) - Robust.updateWeight p w s M < 1 / (2 : ℚ) ^ p at h
  have he : w * (1 - s / M) = w - w * s / M := by ring
  rw [he] at h
  constructor <;> linarith only [h.1, h.2]

theorem reset_loss {n : ℕ} (p : ℕ) (w s : Fin n → ℚ) (M : ℚ)
    (S : Finset (Fin n)) :
    (∑ i ∈ S, w i * s i) / M ≤
        ∑ i ∈ S, (w i - Robust.updateWeight p (w i) (s i) M) ∧
      (∑ i ∈ S, (w i - Robust.updateWeight p (w i) (s i) M)) ≤
        (∑ i ∈ S, w i * s i) / M + S.card / (2 : ℚ) ^ p := by
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ ↦ (updateWeight_loss p (w i) (s i) M).1
  · calc
      _ ≤ ∑ i ∈ S, (w i * s i / M + 1 / (2 : ℚ) ^ p) :=
        Finset.sum_le_sum fun i _ ↦ (updateWeight_loss p (w i) (s i) M).2
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div]
        simp [div_eq_mul_inv]

/-- A type-A step charges good-weight loss to bad-weight loss plus the reset error. -/
theorem reset_typeA {n : ℕ} (p : ℕ) (w s : Fin n → ℚ) (M : ℚ)
    (G B : Finset (Fin n)) (hM : 0 < M)
    (hA : (∑ i ∈ G, w i * s i) ≤ ∑ i ∈ B, w i * s i) :
    (∑ i ∈ G, (w i - Robust.updateWeight p (w i) (s i) M)) ≤
      (∑ i ∈ B, (w i - Robust.updateWeight p (w i) (s i) M)) +
        G.card / (2 : ℚ) ^ p := by
  have hG := (reset_loss p w s M G).2
  have hB := (reset_loss p w s M B).1
  have hdiv := div_le_div_of_nonneg_right hA hM.le
  linarith only [hG, hB, hdiv]

/-- Resetting preserves the type-A accounting with an explicit accumulated slack. -/
theorem reset_accounting {n : ℕ} (p : ℕ) (w s : Fin n → ℚ) (M e : ℚ)
    (G B : Finset (Fin n)) (hM : 0 < M)
    (hA : (∑ i ∈ G, w i * s i) ≤ ∑ i ∈ B, w i * s i)
    (hw : (∑ i ∈ G, (1 - w i)) ≤ (∑ i ∈ B, (1 - w i)) + e) :
    (∑ i ∈ G, (1 - Robust.updateWeight p (w i) (s i) M)) ≤
      (∑ i ∈ B, (1 - Robust.updateWeight p (w i) (s i) M)) +
        (e + G.card / (2 : ℚ) ^ p) := by
  have h := reset_typeA p w s M G B hM hA
  simp only [Finset.sum_sub_distrib] at h hw ⊢
  linarith only [h, hw]


def resetPrecision (n : ℕ) : ℕ := 4 * n + 16

theorem resetPrecision_polytime {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun x ↦ resetPrecision (n x)) enc encUnary :=
  unary_add' (unary_mul' (const 4) hn) (const 16)

/-- Polynomial unary precision makes the total error of at most `n` resets at most `1/(n+1)`.
-/
theorem resetPrecision_error (n : ℕ) :
    (n : ℚ) ^ 2 / (2 : ℚ) ^ resetPrecision n ≤ 1 / (n + 1) := by
  have hbase : n + 1 ≤ 2 ^ (n + 1) := (Nat.lt_two_pow_self (n := n + 1)).le
  have hcube : (n + 1) ^ 3 ≤ 2 ^ (3 * (n + 1)) := by
    calc
      _ ≤ (2 ^ (n + 1)) ^ 3 := Nat.pow_le_pow_left hbase 3
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hexp : 3 * (n + 1) ≤ resetPrecision n := by unfold resetPrecision; omega
  have hpow := hcube.trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp)
  have hq : (n + 1 : ℚ) ^ 3 ≤ (2 : ℚ) ^ resetPrecision n := by exact_mod_cast hpow
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hq, sq_nonneg (n : ℚ), show (0 : ℚ) ≤ n by positivity]

def support {n : ℕ} (w : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ 0 < w i

/-- An attained positive score maximum removes an index even after the grid reset. -/
theorem reset_support_lt {n : ℕ} (p : ℕ) (w s : Fin n → ℚ) (M : ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i) (hM : 0 < M)
    (hmax : ∀ i, s i ≤ M) (i : Fin n) (hi : 0 < w i) (hsi : s i = M) :
    (support (fun j ↦ Robust.updateWeight p (w j) (s j) M)).card < (support w).card := by
  have hsub : support (fun j ↦ Robust.updateWeight p (w j) (s j) M) ⊆ support w := by
    intro j hj
    have hj' : 0 < Robust.updateWeight p (w j) (s j) M := (Finset.mem_filter.mp hj).2
    have hb := (updateWeight_bounds p (hw j) (hs j) hM (hmax j)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.trans_le hb⟩
  apply Finset.card_lt_card
  refine ⟨hsub, ?_⟩
  intro hback
  have hm := hback (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hz : Robust.updateWeight p (w i) (s i) M = 0 := by
    rw [hsi]
    exact updateWeight_eq_zero p (w i) M hM.ne'
  have hpos : 0 < Robust.updateWeight p (w i) (s i) M := (Finset.mem_filter.mp hm).2
  rw [hz] at hpos
  exact lt_irrefl _ hpos

end ABBKS26.Assembly.Exec.FrameAux
