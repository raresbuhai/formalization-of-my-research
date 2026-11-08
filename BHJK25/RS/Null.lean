module

public import BHJK25.RS.Null.Bound

/-!
# Uniform tensors are rejected

[BHJK25, Lemma 2.11, null case]: a uniformly random tensor is accepted with probability at most
`exp(-n^(1 - 1/T))` for large `n`. Union bound over the guesses (at most `n^{2(k-1)ℓ}`), the
polynomials of degree `< m` (`q^m`) and the sets of `W + 1` columns: for a fixed valid guess, the
`β`-cells and `α`-cells of distinct columns are distinct entries, so `W + 1` prescribed
agreements have probability `q^{-(W + 1)}`, while `W + 1 ≈ √(2nm)` is much larger than `m` and
than `2 (k - 1) ℓ`.

* `BHJK25/RS/Basic/Params.lean` and `BHJK25/RS/Basic/Cells.lean` (shared with the other parts):
  bounds on the parameters `r`, `ℓ`, `m` and `W + 1`; the cells of a valid guess are `k`-sets,
  distinct, and no `α`-cell is a `β`-cell.
* `BHJK25/RS/Null/Count.lean`: prescribed agreements at the columns of a set `J` have probability
  `q^{-|J|}`.
* `BHJK25/RS/Null/Union.lean`: the union bound `n^{2(k-1)ℓ} q^m n^{W+1} / q^{W+1}`.
* `BHJK25/RS/Null/Asymp.lean` and `BHJK25/RS/Null/Bound.lean`: it is at most `exp(-n^(1 - 1/T))`
  for large `n`.
-/

@[expose] public section

namespace BHJK25.RS

open MeasureTheory Filter

/-- **[BHJK25, Lemma 2.11, null case].** For large `n`, a uniformly random tensor is rejected with
probability at least `1 - exp(-n^(1 - 1/T))`. -/
theorem null_bound {k T : ℕ} (hk : 2 ≤ k) (hT : 1 ≤ T) :
    ∀ᶠ n : ℕ in atTop, 1 - Real.exp (-(n : ℝ) ^ (1 - 1 / (T : ℝ))) ≤
      uniformProb k n (fun M ↦ ¬ Accept k T n M) := by
  filter_upwards [NullAux.uniformProb_accept_le_exp hk hT, eventually_gt_atTop 0] with n h hn
  rw [NullAux.uniformProb_not, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  linarith

end BHJK25.RS
