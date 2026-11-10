module

public import BHSV25.Net.GSGrid
public import BHSV25.Net.Machine
public import BHSV25.Net.Ball
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.PolyTime.Int.Table
public import Mathlib.Data.Nat.Sqrt

/-!
# The greedy net on lists of numbers

The algorithm of the greedy net (`BHSV25.Net.netGS`), as a function on lists, on the input
`(n, a)` of a graph with adjacency matrix `A` and degree `d`. It reads its parameters: the
eigenspace (`bottom`), the exponent `E` of the filter, the number `T` of rounds, the resolution
`N` of the grid and the budget `B` of the tuples.

1. **The filter**: the exact integer power `Q = M^E` of `M = d I - A` (bottom) or `M = A`
   (absolute), by `BHSV25.Net.powL`, and the Gram matrix `G = (Q_u ⬝ Q_v)` of its rows.
2. **Greedy selection** of `T` rows (`BHSV25.Net.greedySel` with the scores
   `det G_(S ++ [v])`, computed by complexitylib's division-free determinant
   `Cslib.Circuits.Rational.detRows`).
3. **Gram–Schmidt by Cramer's rule**: the leading determinants `Δ_l` of the chosen rows, the
   integer rows `r̃_l = Δ_l Q_(S_l) - ∑_(j<l) γ_(l,j) Q_(S_j)` with `γ_(l,j)` the Cramer
   determinants, and `σ_l = ⌊√(Δ_(l+1) Δ_l)⌋`.
4. **The candidates** `∑_l ((m_l - N) / (N σ_l)) r̃_l` for all tuples `m` over `{0, …, 2N}` in
   the ball `∑ (m_l - N)² ≤ N²` (`BHSV25.Net.ballTuples`, cut at the budget `B`).

The second half of the file says what this computes, with the rows of `Q` read as real vectors
(`BHSV25.Net.colZ`): the greedy selection is that of `BHSV25/Net/Greedy.lean`
(`BHSV25.Net.selZ_eq`), `Δ_l` is `BHSV25.Net.deltaR` (`BHSV25.Net.deltaZ_eq`), and
`r̃_l = Δ_l r_l` for the Gram–Schmidt vector `r_l = BHSV25.Net.gsR` (`BHSV25.Net.rtZ_eq`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix
open Cslib (rowEntry tabulateTable rowEntry_tabulateTable rowEntry_tabulateTable_of_lt)
open Cslib.Circuits.Rational (detRows detRows_eq_det_of_rowEntry)

/-! ### The algorithm -/

/-- The integer filter `Q = M^E`. -/
def filtQ (bottom : Bool) (E : ℕ) (x : ℕ × List Bool) : List (List ℤ) :=
  powL (numV x) (baseMat bottom (numV x) (deg (numV x) x.2) x.2) E

/-- The Gram matrix `(Q_u ⬝ Q_v)_(u,v < n)` of the rows of a table. -/
def gramRows (n : ℕ) (Q : List (List ℤ)) : List (List ℤ) :=
  tabulateTable n n fun u v ↦ ((List.range n).map fun w ↦ rowEntry Q u w * rowEntry Q v w).sum

/-- The table `(G_(L i, L j))_(i,j)` of a list of indices. -/
def subTable (G : List (List ℤ)) (L : List ℕ) : List (List ℤ) :=
  tabulateTable L.length L.length fun i j ↦ rowEntry G (L.getD i 0) (L.getD j 0)

/-- The score of appending `v` to `S`: `det G_(S ++ [v])`. -/
def scoreZ (G : List (List ℤ)) (S : List ℕ) (v : ℕ) : ℤ := detRows (subTable G (S ++ [v]))

/-- The leading determinant `Δ_l = det G_(first l of S)`. -/
def deltaZ (G : List (List ℤ)) (S : List ℕ) (l : ℕ) : ℤ := detRows (subTable G (S.take l))

/-- The leading `l × l` block of `G_S` with its column `j` replaced by `(G_(S_i, S_l))_i`. -/
def cramerTable (G : List (List ℤ)) (S : List ℕ) (l j : ℕ) : List (List ℤ) :=
  tabulateTable l l fun i i' ↦
    if i' = j then rowEntry G (S.getD i 0) (S.getD l 0) else rowEntry G (S.getD i 0) (S.getD i' 0)

/-- The Cramer coefficient `γ_(l,j)`. -/
def gammaZ (G : List (List ℤ)) (S : List ℕ) (l j : ℕ) : ℤ := detRows (cramerTable G S l j)

/-- The integer row `r̃_l = Δ_l Q_(S_l) - ∑_(j<l) γ_(l,j) Q_(S_j)`. -/
def rtZ (n : ℕ) (Q G : List (List ℤ)) (S : List ℕ) (l : ℕ) : List ℤ :=
  (List.range n).map fun u ↦ deltaZ G S l * rowEntry Q (S.getD l 0) u -
    ((List.range l).map fun j ↦ gammaZ G S l j * rowEntry Q (S.getD j 0) u).sum

/-- `σ_l = ⌊√(Δ_(l+1) Δ_l)⌋`. -/
def sigmaZ (G : List (List ℤ)) (S : List ℕ) (l : ℕ) : ℕ :=
  Nat.sqrt (deltaZ G S (l + 1) * deltaZ G S l).toNat

/-- The candidate of a tuple `m` over `{0, …, 2N}`: `∑_l ((m_l - N) / (N σ_l)) r̃_l`. -/
def candGS (n N : ℕ) (rts : List (List ℤ)) (sig : List ℕ) (ms : List ℕ) : List ℚ :=
  (List.range n).map fun u ↦ ((List.range rts.length).map fun l ↦
    ((ms.getD l 0 : ℚ) - N) / ((N : ℚ) * (sig.getD l 0 : ℚ)) * (rowEntry rts l u : ℚ)).sum

/-- The data of the candidates: the number of vertices, the rows `r̃_l`, the numbers `σ_l`. -/
def dataOf (n : ℕ) (Q G : List (List ℤ)) (S : List ℕ) : ℕ × List (List ℤ) × List ℕ :=
  (n, (List.range S.length).map (rtZ n Q G S), (List.range S.length).map (sigmaZ G S))

/-- The selection: `T` greedy rounds on the rows of `Q`. -/
def selOf (n T : ℕ) (G : List (List ℤ)) : List ℕ := greedySel n T (scoreZ G)

/-- The data of the greedy net on the input of a graph. -/
def gsData (bottom : Bool) (E T : ℕ) (x : ℕ × List Bool) : ℕ × List (List ℤ) × List ℕ :=
  dataOf (numV x) (filtQ bottom E x) (gramRows (numV x) (filtQ bottom E x))
    (selOf (numV x) T (gramRows (numV x) (filtQ bottom E x)))

/-- The candidates of the data, for all tuples over `{0, …, 2N}` in the ball (cut at `B`). -/
def candsOf (N B : ℕ) (d : ℕ × List (List ℤ) × List ℕ) : List (List ℚ) :=
  (ballTuples B N d.2.1.length).map (candGS d.1 N d.2.1 d.2.2)

/-- **The greedy net.** -/
def netGS (bottom : Bool) (E T N B : ℕ) (x : ℕ × List Bool) : List (List ℚ) :=
  candsOf N B (gsData bottom E T x)

/-! ### What it computes -/

variable {n : ℕ}

/-- The rows of a table, as real vectors of length `n` (missing entries are `0`). -/
def colZ (n : ℕ) (Q : List (List ℤ)) : ℕ → Fin n → ℝ := fun a u ↦ (rowEntry Q a u : ℝ)

theorem rowEntry_of_length_le {Q : List (List ℤ)} {a : ℕ} (ha : Q.length ≤ a) (u : ℕ) :
    rowEntry Q a u = 0 := by
  simp [rowEntry, List.getElem?_eq_none ha]

/-- The Gram matrix of the rows, read with `rowEntry`, is that of the real rows. -/
theorem rowEntry_gramRows (Q : List (List ℤ)) (hQ : Q.length ≤ n) (a b : ℕ) :
    (rowEntry (gramRows n Q) a b : ℝ) = colZ n Q a ⬝ᵥ colZ n Q b := by
  rw [gramRows, rowEntry_tabulateTable]
  split_ifs with h
  · rw [sum_map_range]
    push_cast
    rfl
  · push Not at h
    simp only [Int.cast_zero, colZ, dotProduct]
    symm
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases ha : a < n
    · rw [rowEntry_of_length_le (hQ.trans (h ha)), Int.cast_zero, mul_zero]
    · rw [rowEntry_of_length_le (hQ.trans (not_lt.1 ha)), Int.cast_zero, zero_mul]

/-- A determinant of a table of a list, computed by `detRows`, is the Gram determinant of the
real rows. -/
theorem detRows_subTable (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) (L : List ℕ) :
    ((detRows (subTable G L) : ℤ) : ℝ) = (gramF (colsL col L)).det := by
  have h := detRows_eq_det_of_rowEntry (rows := subTable G L)
    (Matrix.of fun i j : Fin L.length ↦ rowEntry G (L.getD i 0) (L.getD j 0))
    (by simp [subTable]) (fun i j ↦ by
      rw [subTable, rowEntry_tabulateTable_of_lt _ i.2 j.2]
      rfl)
  rw [h, Int.cast_det]
  congr 1
  ext i j
  simp only [map_apply, of_apply, gramF, colsL, hG, List.getD_eq_getElem _ _ i.2,
    List.getD_eq_getElem _ _ j.2]
  rfl

theorem scoreZ_eq (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) (S : List ℕ) (v : ℕ) :
    ((scoreZ G S v : ℤ) : ℝ) = scoreR col S v :=
  detRows_subTable G col hG (S ++ [v])

/-- **The machine's selection is the greedy selection of the real rows.** -/
theorem selZ_eq (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) (N T : ℕ) :
    selOf N T G = greedySel N T (scoreR col) := by
  refine greedySel_congr (fun S v _ ↦ ?_) (fun S u _ v _ ↦ ?_)
  · rw [← scoreZ_eq G col hG]; exact Int.cast_pos.symm
  · rw [← scoreZ_eq G col hG, ← scoreZ_eq G col hG]; exact Int.cast_lt.symm

theorem deltaZ_eq (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) (S : List ℕ) (l : ℕ) :
    ((deltaZ G S l : ℤ) : ℝ) = deltaR col S l :=
  detRows_subTable G col hG (S.take l)

/-- The Cramer coefficients are those of `adj(G_l) (G_(S_i, S_l))_i`. -/
theorem gammaZ_eq (G : List (List ℤ)) (col : ℕ → Fin n → ℝ)
    (hG : ∀ a b, (rowEntry G a b : ℝ) = col a ⬝ᵥ col b) (S : List ℕ) {l : ℕ}
    (hl : l ≤ S.length) (j : Fin (S.take l).length) :
    ((gammaZ G S l j : ℤ) : ℝ) = cramer (gramF (colsL col (S.take l)))
      (fun i ↦ colsL col (S.take l) i ⬝ᵥ col (S.getD l 0)) j := by
  have hlen : (S.take l).length = l := by simp [hl]
  have h := detRows_eq_det_of_rowEntry (rows := cramerTable G S l j)
    (Matrix.of fun i i' : Fin (S.take l).length ↦
      if (i' : ℕ) = j then rowEntry G (S.getD i 0) (S.getD l 0)
      else rowEntry G (S.getD i 0) (S.getD i' 0))
    (by simp [cramerTable, hlen]) (fun i i' ↦ by
      rw [cramerTable, rowEntry_tabulateTable_of_lt _ (by omega) (by omega)]
      rfl)
  rw [gammaZ, h, Int.cast_det, cramer_apply]
  congr 1
  ext i i'
  have hi : (i : ℕ) < S.length := by omega
  have hi' : (i' : ℕ) < S.length := by omega
  simp only [map_apply, of_apply, updateCol_apply, gramF, colsL]
  have e1 : (S.take l)[i] = S.getD i 0 := by
    rw [Fin.getElem_fin, List.getElem_take, List.getD_eq_getElem _ _ hi]
  have e2 : (S.take l)[i'] = S.getD i' 0 := by
    rw [Fin.getElem_fin, List.getElem_take, List.getD_eq_getElem _ _ hi']
  rw [e1, e2]
  by_cases hij : i' = j
  · subst hij; simp [hG]
  · have : (i' : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
    simp [hij, this, hG]

/-- **The integer rows are `Δ_l r_l`.** -/
theorem rtZ_eq (Q G : List (List ℤ)) (hG : ∀ a b, (rowEntry G a b : ℝ) =
    colZ n Q a ⬝ᵥ colZ n Q b) (S : List ℕ) {l : ℕ} (hl : l < S.length)
    (hdet : deltaR (colZ n Q) S l ≠ 0) :
    (fun u : Fin n ↦ (rowEntry ((List.range S.length).map (rtZ n Q G S)) l u : ℝ)) =
      deltaR (colZ n Q) S l • gsR (colZ n Q) S l := by
  set col := colZ n Q with hcol
  set F := colsL col (S.take l) with hF
  set g : Fin (S.take l).length → ℝ := fun i ↦ F i ⬝ᵥ col (S.getD l 0) with hg
  have hdetF : (gramF F).det ≠ 0 := hdet
  have hlen : (S.take l).length = l := by simp [hl.le]
  -- `Δ_l` times the coefficients of the projection are the Cramer coefficients
  have hcoef : deltaR col S l • coefF F (col (S.getD l 0)) = cramer (gramF F) g := by
    rw [coefF, cramer_eq_adjugate_mulVec, Matrix.inv_def, smul_mulVec, smul_smul]
    have : deltaR col S l * Ring.inverse (gramF F).det = 1 := by
      rw [Ring.inverse_eq_inv', deltaR, ← hF, mul_inv_cancel₀ hdetF]
    rw [this, one_smul]
  have key : deltaR col S l • gsR col S l =
      deltaR col S l • col (S.getD l 0) - combF F (cramer (gramF F) g) := by
    rw [gsR, resid, smul_sub, ← combF_smul, hcoef]
  rw [key]
  funext u
  have hrow : rowEntry ((List.range S.length).map (rtZ n Q G S)) l u =
      (rtZ n Q G S l).getD u 0 := by
    rw [rowEntry, getD_map_range S.length _ _ hl]
  rw [hrow, rtZ, getD_map_range n _ _ u.2, sum_map_range]
  push_cast
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, combF, Finset.sum_apply]
  rw [← deltaZ_eq G col hG S l]
  congr 1
  refine Fintype.sum_equiv (finCongr hlen.symm) _ _ fun j ↦ ?_
  rw [← gammaZ_eq G col hG S hl.le]
  simp only [finCongr_apply, Fin.val_cast, colsL, hF, hcol, colZ]
  rw [Fin.getElem_fin, List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
  rfl

/-- The real vector of a list of rationals (missing entries are `0`); the same as
`BHSV25.Net.vecOf`. -/
def ratVec (n : ℕ) (c : List ℚ) : Fin n → ℝ := fun i ↦ ((c.getD i 0 : ℚ) : ℝ)

/-- **A candidate is a combination of the scaled rows.** -/
theorem ratVec_candGS (N : ℕ) (rts : List (List ℤ)) (sig : List ℕ) (ms : List ℕ) :
    ratVec n (candGS n N rts sig ms) = ∑ l ∈ Finset.range rts.length,
      (((ms.getD l 0 : ℝ) - N) / ((N : ℝ) * (sig.getD l 0 : ℝ))) •
        fun u : Fin n ↦ (rowEntry rts l u : ℝ) := by
  funext u
  rw [ratVec, candGS, getD_map_range n _ _ u.2, sum_map_range, Finset.sum_apply,
    Finset.sum_range]
  push_cast
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]

end Net

end BHSV25
