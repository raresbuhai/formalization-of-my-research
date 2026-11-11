module

public import BHSV25.Net.Stop
public import BHSV25.Net.GSCorrect

/-!
# The greedy net with the stopping round

For a symmetric integer table `Q` whose scaled real matrix `P = c Q` acts on the eigenbasis of a
symmetric matrix by numbers `φᵢ`, with `|φᵢ| ≤ ℓ` outside a set `R` of indices, and integers
`X > 0`, `Y` of a test whose threshold `c √(Y / X)` lies above the greedy bound
`(2^(|R|+1) - 1) ℓ` (`BHSV25.Net.stopZ_le_and_resid`):

* the stopping round is at most `|R|`: after `|R|` rounds the test holds
  (`BHSV25.Net.greedy_resid_le`), so it holds after the stopping round, which is the first;
* after the stopping round, every column of `P` has residual at most `c √(Y / X)`, so the net
  with that many rounds contains, for every vector `w` of length at most `1` whose coefficients
  vanish where `φ < h`, a vector within `2 √T / N + √n ρ / h`, for `T` the stopping round and
  `ρ ≥ c √(Y / X)` (`BHSV25.Net.exists_cand_near_stop`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral
open Cslib (rowEntry)

variable {n : ℕ}

/-- The residuals of the scaled columns are the scaled residuals. -/
theorem resid_colsL_smul (Q : List (List ℤ)) (hQ : Q.length ≤ n) {c : ℝ} (hc : c ≠ 0) (T v : ℕ) :
    resid (colsL (fun v ↦ c • colZ n Q v) (selOf n T (gramRows n Q))) (c • colZ n Q v) =
      c • resid (colsL (colZ n Q) (selOf n T (gramRows n Q))) (colZ n Q v) := by
  have hG := rowEntry_gramRows Q hQ
  have hdet : (gramF (colsL (colZ n Q) (selOf n T (gramRows n Q)))).det ≠ 0 := by
    rw [selZ_eq _ _ hG n T]
    exact (goodSel_greedySeq (colZ n Q) n T).1.ne'
  have e : colsL (fun v ↦ c • colZ n Q v) (selOf n T (gramRows n Q)) =
      fun j ↦ c • colsL (colZ n Q) (selOf n T (gramRows n Q)) j := rfl
  rw [e, resid_smul_family _ hdet hc, resid_smul]

/-- **The stopping round** is at most `|R|`, and after it every column of `c Q` has squared
residual at most `c² Y / X`, when the threshold is above the greedy bound. -/
theorem stopZ_le_and_resid {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (Q : List (List ℤ)) (hQ : Q.length ≤ n) (hsym : ∀ u v : ℕ, rowEntry Q u v = rowEntry Q v u)
    {c : ℝ} (hc : 0 < c) (φ : Fin n → ℝ)
    (hP : ∀ i x, coeff hA i ((c • Matrix.of fun u v : Fin n ↦ (rowEntry Q u v : ℝ)) *ᵥ x) =
      φ i * coeff hA i x)
    (R : Finset (Fin n)) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hφl : ∀ i ∉ R, |φ i| ≤ ℓ) {X Y : ℤ} (hX : 0 < X)
    (hτ : ((2 ^ (R.card + 1) - 1) * ℓ) ^ 2 * X ≤ c ^ 2 * Y) :
    stopZ n (gramRows n Q) X Y ≤ R.card ∧ ∀ v < n,
      resid (colsL (fun v ↦ c • colZ n Q v) (selOf n (stopZ n (gramRows n Q) X Y)
          (gramRows n Q))) (c • colZ n Q v) ⬝ᵥ
        resid (colsL (fun v ↦ c • colZ n Q v) (selOf n (stopZ n (gramRows n Q) X Y)
          (gramRows n Q))) (c • colZ n Q v) * X ≤ c ^ 2 * Y := by
  have hG := rowEntry_gramRows Q hQ
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have hc2 : 0 < c ^ 2 := by positivity
  have hscale : ∀ T v, resid (colsL (fun v ↦ c • colZ n Q v) (selOf n T (gramRows n Q)))
      (c • colZ n Q v) ⬝ᵥ resid (colsL (fun v ↦ c • colZ n Q v) (selOf n T (gramRows n Q)))
      (c • colZ n Q v) = c ^ 2 * (resid (colsL (colZ n Q) (selOf n T (gramRows n Q)))
        (colZ n Q v) ⬝ᵥ resid (colsL (colZ n Q) (selOf n T (gramRows n Q))) (colZ n Q v)) := by
    intro T v
    rw [resid_colsL_smul Q hQ hc.ne', smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, sq]
  -- the test holds after `|R|` rounds
  have hR : R.card ≤ n := (Finset.card_le_univ R).trans (by simp)
  have hok : okZ n (gramRows n Q) X Y (selOf n R.card (gramRows n Q)) = true := by
    rw [okZ_iff _ (colZ n Q) hG hX]
    intro v hv
    have h1 := resid_le_of_spectral hA Q hQ hsym hc φ hP R le_rfl hℓ hφl v hv
    rw [hscale] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hX'.le
    have h3 : c ^ 2 * ((resid (colsL (colZ n Q) (selOf n R.card (gramRows n Q))) (colZ n Q v) ⬝ᵥ
        resid (colsL (colZ n Q) (selOf n R.card (gramRows n Q))) (colZ n Q v)) * X) ≤
        c ^ 2 * Y := by
      rw [← mul_assoc]; exact h2.trans hτ
    exact le_of_mul_le_mul_left h3 hc2
  obtain ⟨hstop, hle⟩ := stopZ_spec _ (colZ n Q) hG hX Y hR hok
  refine ⟨hle, fun v hv ↦ ?_⟩
  rw [okZ_iff _ (colZ n Q) hG hX] at hstop
  rw [hscale, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hstop v hv) hc2.le

/-- **The net at the stopping round.** When the threshold `c √(Y / X)` is above the greedy bound
`(2^(|R|+1) - 1) ℓ` and at most `ρ`, the stopping round `T` is at most `|R|`, and the greedy net
with `T` rounds contains, for every vector `w` of length at most `1` whose coefficients vanish
where `φ < h`, a vector within `2 √T / N + √n ρ / h`. -/
theorem exists_cand_near_stop {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (Q : List (List ℤ)) (hQ : Q.length ≤ n) (hsym : ∀ u v : ℕ, rowEntry Q u v = rowEntry Q v u)
    {c : ℝ} (hc : 0 < c) (φ : Fin n → ℝ)
    (hP : ∀ i x, coeff hA i ((c • Matrix.of fun u v : Fin n ↦ (rowEntry Q u v : ℝ)) *ᵥ x) =
      φ i * coeff hA i x)
    (R : Finset (Fin n)) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hφl : ∀ i ∉ R, |φ i| ≤ ℓ) {X Y : ℤ} (hX : 0 < X)
    (hτ : ((2 ^ (R.card + 1) - 1) * ℓ) ^ 2 * X ≤ c ^ 2 * Y) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρY : c ^ 2 * Y ≤ ρ ^ 2 * X) {h : ℝ} (hh : 0 < h) (w : Fin n → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : ∀ i, coeff hA i w ≠ 0 → h ≤ φ i) {N B : ℕ} (hN : 0 < N)
    (hB : BallBudget N (stopZ n (gramRows n Q) X Y) B) :
    stopZ n (gramRows n Q) X Y ≤ R.card ∧
    ∃ cand ∈ candsOf N B (dataOf n Q (gramRows n Q)
        (selOf n (stopZ n (gramRows n Q) X Y) (gramRows n Q))),
      Real.sqrt ((ratVec n cand - w) ⬝ᵥ (ratVec n cand - w)) ≤
        2 * Real.sqrt (stopZ n (gramRows n Q) X Y) / N + Real.sqrt n * ρ / h := by
  obtain ⟨hle, hres⟩ := stopZ_le_and_resid hA Q hQ hsym hc φ hP R hℓ hφl hX hτ
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  refine ⟨hle, exists_cand_near_of_resid hA Q hQ hsym hc φ hP hρ hh (fun v hv ↦ ?_) w hw1 hw hN
    hB⟩
  exact le_of_mul_le_mul_right ((hres v hv).trans hρY) hX'

end Net

end BHSV25
