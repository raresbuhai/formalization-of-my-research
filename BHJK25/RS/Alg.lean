module

public import BHJK25.RS.Alg.Correct
public import BHJK25.RS.Alg.Time
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The algorithm of Theorem 2.1

For every guess of the row vertices, read the pairs `(α_v, β_v)` of the columns, list decode
them with Sudan's algorithm (`BHJK25.RS.decodeL`: interpolation by Gaussian elimination over
`F_q`, then the roots `Y = p(X)` of the interpolant by Roth–Ruckenstein), and accept when some
listed polynomial agrees with `W + 1` distinct values. This decides `BHJK25.RS.Accept`, in time
`n^{2(k-1)ℓ} · poly(n) = n^{O(log^{1/(k-1)} n)}`.

The algorithm is a program on lists (`BHJK25/RS/Alg/Basic.lean`): the guesses are the indices
`idx < n^L`, read in base `n`, and the bits of the columns are read from the table of the tensor.
That it decides acceptance is `BHJK25/RS/Alg/Guess.lean` and `BHJK25/RS/Alg/Correct.lean`. It runs
as a loop of `n^L` rounds of polynomial time (`BHJK25/RS/Alg/PolyTimeGuess.lean`,
`BHJK25/RS/Alg/PolyTimeData.lean`, `BHJK25/RS/Alg/Loop.lean`), on a machine that reads `T` in
unary so that the degree of the polynomial does not depend on `T`; the bound
`n^L ≤ (n + 2)^{O(log^{1/(k-1)} (n + 2))}` is `BHJK25/RS/Alg/Time.lean`.
-/

@[expose] public section

namespace BHJK25.RS

open Filter

/-- **The algorithm of Theorem 2.1.** On `⟨n, M⟩`, for every index `idx < n^L` (`L = 2 (k - 1) ℓ`),
read as the guess of its `L` digits in base `n`: if the digits are distinct, read the bits of
`α_v` and `β_v` for every column `v` from the table of `M`, and decode them
(`BHJK25.RS.decodeL`, or, when the polynomials are constants, by trying every value). Accept when
some guess is accepted. -/
noncomputable def rsAlg (k T : ℕ) (x : TensorInput k) : Bool :=
  AlgAux.run k T x

open Classical in
/-- **The algorithm decides acceptance.** -/
theorem rsAlg_correct {k T : ℕ} (hk : 2 ≤ k) (hT : 1 ≤ T) :
    ∀ᶠ n : ℕ in atTop, ∀ M : Tensor k n, rsAlg k T ⟨n, M⟩ = decide (Accept k T n M) := by
  -- `T ≥ 1` is not needed: for `T = 1` the polynomials are the constants, which the algorithm
  -- decodes by trying every value
  have _ := hT
  exact Eventually.of_forall fun _ M ↦ AlgAux.run_eq (by omega) M

/-- **The algorithm runs in time `n^{O(log^{1/(k-1)} n)}`**, with a constant that does not depend
on `T`. -/
theorem rsAlg_time {k : ℕ} (hk : 2 ≤ k) : ∃ C : ℕ, ∀ T : ℕ, 1 ≤ T →
    RunsInTime (encTensor k) Encoding.encBool (rsAlg k T) (tensorTime k C) := by
  obtain ⟨C, hC⟩ := AlgAux.run_time hk
  exact ⟨C, fun T _ ↦ hC T⟩

end BHJK25.RS
