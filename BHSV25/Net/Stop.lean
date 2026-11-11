module

public import BHSV25.Net.GSPolyTime

/-!
# Stopping the greedy selection

The algorithms of Theorems 7.12 and 7.20 do not know the number `t` of eigenvalues their nets
cover. They choose the number of rounds of the greedy selection themselves: they stop at the
first round after which every row of the filter has a small residual against the chosen rows.

* **The test** (`BHSV25.Net.okZ`): every row `v < n` has `det G_(S ++ [v]) X ≤ det G_S Y`, for the
  Gram matrix `G` of the rows and integers `X, Y`. For a greedy selection `S`, this says that
  every row has squared residual at most `Y / X` (`BHSV25.Net.okZ_iff`), and it stays true in
  later rounds, as the residuals shrink (`BHSV25.Net.okZ_mono`).
* **The stopping round** (`BHSV25.Net.stopZ`): the number of rounds `s < n` after which the test
  fails. If the test holds after some round `j ≤ n`, then it holds after the stopping round, which
  is at most `j` (`BHSV25.Net.stopZ_spec`).
* `BHSV25.Net.stopZ_polytime`: the stopping round is computed in polynomial time.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix
open Cslib (rowEntry)

/-! ### The test and the stopping round -/

/-- **The test** of a selection `S`: `det G_(S ++ [v]) X ≤ det G_S Y` for every row `v < n`. -/
def okZ (n : ℕ) (G : List (List ℤ)) (X Y : ℤ) (S : List ℕ) : Bool :=
  (List.range n).all fun v ↦ decide (scoreZ G S v * X ≤ deltaZ G S S.length * Y)

/-- **The stopping round**: the number of rounds `s < n` after which the test fails. -/
def stopZ (n : ℕ) (G : List (List ℤ)) (X Y : ℤ) : ℕ :=
  (List.range n).countP fun s ↦ !okZ n G X Y (selOf n s G)

/-! ### What the test says -/

variable {n : ℕ}

/-- **The test of a greedy selection** says that every row has squared residual at most
`Y / X`, for `X > 0`. -/
theorem okZ_iff (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) {X : ℤ} (hX : 0 < X) (Y : ℤ) (s : ℕ) :
    okZ n G X Y (selOf n s G) = true ↔ ∀ v < n,
      resid (colsL col (selOf n s G)) (col v) ⬝ᵥ resid (colsL col (selOf n s G)) (col v) *
        X ≤ Y := by
  set S := selOf n s G with hS
  have hSsel : S = greedySeq n (scoreR col) s := selZ_eq G col hG n s
  have hdet : 0 < (gramF (colsL col S)).det := by
    rw [hSsel]; exact (goodSel_greedySeq col n s).1
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have hΔ : ((deltaZ G S S.length : ℤ) : ℝ) = (gramF (colsL col S)).det := by
    rw [deltaZ_eq G col hG, deltaR, List.take_length]
  simp only [okZ, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine forall₂_congr fun v _ ↦ ?_
  rw [← Int.cast_le (R := ℝ), Int.cast_mul, Int.cast_mul, scoreZ_eq G col hG,
    scoreR_eq col S v hdet.ne', hΔ, mul_assoc, mul_le_mul_iff_of_pos_left hdet]

/-- **The test stays true** in later rounds: the residuals shrink. -/
theorem okZ_mono (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) {X : ℤ} (hX : 0 < X) (Y : ℤ) {s s' : ℕ}
    (hss' : s ≤ s') (h : okZ n G X Y (selOf n s G) = true) :
    okZ n G X Y (selOf n s' G) = true := by
  rw [okZ_iff G col hG hX] at h ⊢
  intro v hv
  have hX' : (0 : ℝ) ≤ X := by exact_mod_cast hX.le
  have hanti := resid_greedySeq_anti col n (col v) hss'
  have e : ∀ s, selOf n s G = greedySeq n (scoreR col) s := fun s ↦ selZ_eq G col hG n s
  have h' := h v hv
  rw [e] at h' ⊢
  exact (mul_le_mul_of_nonneg_right hanti hX').trans h'

/-- The number of `s < n` below `T` is `min T n`. -/
theorem countP_range_lt (T n : ℕ) :
    (List.range n).countP (fun s ↦ decide (s < T)) = min T n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : n < T
    · simp [h]; omega
    · simp [h]; omega

/-- **The stopping round**: if the test holds after round `j ≤ n`, it holds after the stopping
round, which is at most `j`. -/
theorem stopZ_spec (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) {X : ℤ} (hX : 0 < X) (Y : ℤ) {j : ℕ}
    (hjn : j ≤ n) (hj : okZ n G X Y (selOf n j G) = true) :
    okZ n G X Y (selOf n (stopZ n G X Y) G) = true ∧ stopZ n G X Y ≤ j := by
  classical
  have hex : ∃ s, okZ n G X Y (selOf n s G) = true := ⟨j, hj⟩
  set T := Nat.find hex with hT
  have hiff : ∀ s, (!okZ n G X Y (selOf n s G)) = decide (s < T) := by
    intro s
    by_cases hs : s < T
    · have := Nat.find_min hex hs
      simp only [Bool.not_eq_true] at this
      simp [this, hs]
    · have := okZ_mono G col hG hX Y (not_lt.1 hs) (Nat.find_spec hex)
      simp [this, hs]
  have hTj : T ≤ j := Nat.find_min' hex hj
  have hstop : stopZ n G X Y = T := by
    rw [stopZ, List.countP_congr (fun s _ ↦ by rw [hiff s]), countP_range_lt]
    omega
  rw [hstop]
  exact ⟨Nat.find_spec hex, hTj⟩

/-! ### Polynomial time -/

open Turing.MultiTapeTM ComputableInPolyTime

/-- The input of the test: the number of vertices, the Gram matrix, the numbers `X, Y`. -/
abbrev encStop : (ℕ × List (List ℤ)) × (ℤ × ℤ) ↪ List Bool :=
  encPair (encPair encUnary encMat) (encPair encIntBin encIntBin)

/-- **The test is computed in polynomial time**, on the input of the test and a list. -/
theorem okZ_polytime : ComputableInPolyTime
    (fun q : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ ↦ okZ q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2)
    (encPair encStop encVs) encBool := by
  unfold okZ
  set I := encPair encStop encVs
  have hn : ComputableInPolyTime (fun q : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ ↦ q.1.1.1) I
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hrange : ComputableInPolyTime
      (fun q : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ ↦ List.range q.1.1.1) I
      (encList encUnary) := .of_tidy (ComputableTidilyInPolyTime.range.comp hn.tidy)
  set J := encPair I encUnary
  have hq : ComputableInPolyTime (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.1)
      J I := fst _ _
  have hv : ComputableInPolyTime (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.2)
      J encUnary := snd _ _
  have hG : ComputableInPolyTime
      (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.1.1.1.2) J encMat :=
    (snd _ _).comp ((fst _ _).comp ((fst _ _).comp hq))
  have hX : ComputableInPolyTime
      (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.1.1.2.1) J encIntBin :=
    (fst _ _).comp ((snd _ _).comp ((fst _ _).comp hq))
  have hY : ComputableInPolyTime
      (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.1.1.2.2) J encIntBin :=
    (snd _ _).comp ((snd _ _).comp ((fst _ _).comp hq))
  have hS : ComputableInPolyTime
      (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦ z.1.2) J encVs :=
    (snd _ _).comp hq
  have hlen := (length_list encUnary).comp hS
  have hscore := scoreZ_polytime.comp ((hG.prod hS).prod hv)
  have hdelta := deltaZ_polytime.comp ((hG.prod hS).prod hlen)
  have hlhs := intBin_mul' hscore hX
  have hrhs := intBin_mul' hdelta hY
  have htest : ComputableInPolyTime
      (fun z : (((ℕ × List (List ℤ)) × (ℤ × ℤ)) × List ℕ) × ℕ ↦
        decide (scoreZ z.1.1.1.2 z.1.2 z.2 * z.1.1.2.1 ≤
          deltaZ z.1.1.1.2 z.1.2 z.1.2.length * z.1.1.2.2)) J encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_le' hlhs.tidy hrhs.tidy)
  exact allWithInput hrange htest

/-- **The stopping round is computed in polynomial time.** -/
theorem stopZ_polytime : ComputableInPolyTime
    (fun r : (ℕ × List (List ℤ)) × (ℤ × ℤ) ↦ stopZ r.1.1 r.1.2 r.2.1 r.2.2) encStop encUnary := by
  unfold stopZ
  have hn : ComputableInPolyTime (fun r : (ℕ × List (List ℤ)) × (ℤ × ℤ) ↦ r.1.1) encStop
      encUnary := (fst _ _).comp (fst _ _)
  have hrange : ComputableInPolyTime (fun r : (ℕ × List (List ℤ)) × (ℤ × ℤ) ↦ List.range r.1.1)
      encStop (encList encUnary) := .of_tidy (ComputableTidilyInPolyTime.range.comp hn.tidy)
  set J := encPair encStop encUnary
  have hr : ComputableInPolyTime (fun z : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × ℕ ↦ z.1) J encStop :=
    fst _ _
  have hs : ComputableInPolyTime (fun z : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × ℕ ↦ z.2) J encUnary :=
    snd _ _
  have hn' := hn.comp hr
  have hG : ComputableInPolyTime (fun z : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × ℕ ↦ z.1.1.2) J
      encMat := (snd _ _).comp ((fst _ _).comp hr)
  have hsel := selOf_polytime.comp ((hn'.prod hs).prod hG)
  have hok := okZ_polytime.comp (hr.prod hsel)
  have htest : ComputableInPolyTime (fun z : ((ℕ × List (List ℤ)) × (ℤ × ℤ)) × ℕ ↦
      !okZ z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 (selOf z.1.1.1 z.2 z.1.1.2)) J encBool :=
    .of_tidy (ComputableTidilyInPolyTime.bool_not.comp hok.tidy)
  exact countPWithInput hrange htest

end Net

end BHSV25
