module

public import BCFGJPSSV26.Model

/-!
# Main results: statements

The main results of [BCFGJPSSV26a] (Part I) and [BCFGJPSSV26b] (Part II), with proofs `sorry`.
`lake comparator` checks that `Solution.lean` proves exactly these statements using only the
axioms listed in `comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BCFGJPSSV26/Model.lean` (k-median, stability, randomized algorithms, encodings), the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, complexitylib's polynomial time,
and Mathlib.

## The model

* **Instances** (`BCFGJPSSV26.Instance`): `n` clients and `m ≥ 1` facilities with rational
  distances forming a pseudometric on the `n + m` points, and a number `k ≥ 1` of centers
  (`BCFGJPSSV26.Instance.Valid`). The paper's metric space `(D ∪ F, d)` may have points that are
  both clients and facilities; here they are two points at distance `0`.
* **Costs.** `opt ℓ` is the least cost `∑_j d(j, S)` of a nonempty set `S` of at most `ℓ`
  facilities, the paper's `OPT_ℓ`. For `k ≤ m` it is also the least cost of exactly `k` facilities,
  Part II's definition.
* **Outputs** are lists of distinct facilities (`BCFGJPSSV26.Instance.IsCenterList`), read as the
  set of facilities they list (`BCFGJPSSV26.Instance.centers`).
* **Running times** are bounds on multitape Turing machines over the encoded instance
  (`BCFGJPSSV26.encInstance`: `n`, `m`, `k` and the table of distances), so polynomial time is
  polynomial in `n + m` and in the bits of the distances.
* **Randomized algorithms** (`BCFGJPSSV26.RunsInTime`) read the instance and a string of coin
  flips; as in the other papers of this repository, the time bound is explicit, and it is also
  the number of coins the probability is over (`BCFGJPSSV26.coinProb`).

## Theorem 1.1 of Part I

[BCFGJPSSV26a, Theorem 1.1]: there is a randomized polynomial-time `1.95`-approximation algorithm
for k-median.

Formally (`BCFGJPSSV26.kMedian_approximation`): an algorithm running in time `O((N + 2)^e)` on
instances of encoded length `N` that always outputs at most `k` distinct facilities, and with
probability at least `2/3` outputs facilities of cost at most `1.95 · opt k`. The paper does not
fix the probability; any constant can be raised by repetition, keeping the cheapest output.

## Theorem 1.2 of Part I

[BCFGJPSSV26a, Theorem 1.2] (Theorem 5.16 in full): for every `ε > 0` there is a polynomial-time
algorithm that outputs at most `k + O(log n / ε²)` centers of cost at most `(1.9499 + ε) opt k`.

Formally (`BCFGJPSSV26.kMedian_pseudoApproximation`): one constant `C` serves every `ε > 0`, and
`n` is the number of clients. For each `ε` the algorithm is deterministic, as in the paper, and
runs in polynomial time (complexitylib's `Turing.MultiTapeTM.ComputableInPolyTime`), with a
polynomial that may depend on `ε`. The full version, Theorem 5.16, is stated for small `ε`, with
the error `(1 + ε) 1.9499`; scaling `ε` changes only `C`. For larger `ε`, the algorithm for a
fixed small `ε` serves up to a constant, with a larger `C`, and beyond it a constant-factor
approximation with `k` centers does: local search with swaps of constant size [Arya et al. 2004],
as in Part II.

## Theorem 1.3 of Part I (Theorem 1.1 of Part II)

[BCFGJPSSV26b, Theorem 1.1]: for a `β`-stable instance and `ε ∈ (0, 1/200)`, an algorithm running
in time `exp(O(β⁻¹ poly(1/ε))) n^poly(1/ε)` outputs, with probability `1 - ε`, a set of exactly `k`
facilities of cost at most `(1.89 + O(ε)) opt k`.

Formally (`BCFGJPSSV26.stable_kMedian_approximation`):

* **Stability** (`BCFGJPSSV26.Instance.IsStable`): `opt (k - 1) ≥ (1 + β) opt k`, asked for
  `k ≥ 2`. In the paper, `opt 0 = ∞`, so every instance with `k = 1` is stable; here `opt` is
  real-valued and `opt 0` is not used, and the definition makes every instance with `k = 1`
  stable directly. The theorem asks for `k ≤ m`, so that `k` facilities exist.
* **The parameter `β`** reaches the algorithm as a number `L ≥ 1/β` in unary: the algorithm uses
  `β` (its number of rounds depends on it), and the time is exponential in `L` whatever the
  encoding.
* **The accuracy `ε`** is part of the input, a rational number in binary: one algorithm serves
  every `ε`, which may depend on the instance. The guarantees are asked for `ε ∈ (0, 1/200)`, as
  in the paper; on other inputs the algorithm still halts within its time bound and outputs `k`
  distinct facilities.
* **Time `exp(O(β⁻¹ poly(1/ε))) n^poly(1/ε)`.** The algorithm runs in time
  `O(2^(e L) (N + 2)^e + N + L + |ε|)` with `e = a (⌈1/ε⌉ + 1)^b` (`BCFGJPSSV26.stableTimeOf`),
  where `N` is the encoded length of the instance and `|ε|` that of `ε` (not its absolute value);
  `BCFGJPSSV26.RunsInTime` adds the length of the input to the bound. The constants `a` and `b`,
  the constant factor of `O(·)` (that of the machine) and the constant `C` of `O(ε)` are
  absolute.
* **Output.** The algorithm always outputs exactly `k` distinct facilities, and, for
  `ε ∈ (0, 1/200)` and `L ≥ 1/β` on a `β`-stable instance, with probability at least `1 - ε`
  their cost is at most `(1.89 + C ε) opt k`.

## Theorem 1.4 of Part I

[BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): there is a polynomial-time `1.9499`-LMP
approximation algorithm for uncapacitated facility location, that is, one that, on every instance
with a uniform opening cost `f`, outputs a set `S` of facilities with
`∑_j d(j, S) ≤ 1.9499 (OPT_f - f |S|)` [BCFGJPSSV26a, Definition 2.1].

Formally (`BCFGJPSSV26.facilityLocation_lmp`):

* **Instances** are the valid instances above with at least one client, together with a
  rational opening cost `f ≥ 0`, given to the algorithm; the number `k` plays no role. Without
  clients the paper's optimum opens no facility and is `0`, while outputs here are nonempty and
  `OPT_f` ranges over nonempty sets, so that degenerate case is excluded. (The k-median theorems
  need no such condition: without clients every set costs `0`, under either convention.)
* **`OPT_f`** is `BCFGJPSSV26.Instance.optFL f`, the least `cost S + f |S|` over nonempty sets
  `S` of facilities. The output is a nonempty list of distinct facilities, and `|S|` is its
  length.
* **The algorithm** is deterministic and runs in polynomial time (complexitylib's
  `Turing.MultiTapeTM.ComputableInPolyTime`), as the paper's is. The full version, Theorem 4.3,
  says that Algorithm 1 with the bid `[α - 1.224 d]⁺` and the opening cost `1.9499 f` is such an
  algorithm; the formal statement asserts that some algorithm has the guarantee.
-/

public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.1** of [BCFGJPSSV26a]: a randomized polynomial-time `1.95`-approximation algorithm
for k-median. It always outputs at most `k` distinct facilities, and with probability at least
`2/3` their cost is at most `1.95` times the optimum. -/
theorem kMedian_approximation :
    ∃ (A : Instance × List Bool → List ℕ) (e : ℕ),
      RunsInTime encInstance encCenters A (fun I ↦ ((encInstance I).length + 2) ^ e) ∧
      ∀ I : Instance, I.Valid →
        (∀ r, I.IsCenterList (A (I, r)) ∧ (A (I, r)).length ≤ I.k) ∧
        2 / 3 ≤ coinProb (((encInstance I).length + 2) ^ e)
          fun r ↦ I.cost (I.centers (A (I, r))) ≤ 1.95 * I.opt I.k :=
  sorry

/-- **Theorem 1.2** of [BCFGJPSSV26a]: for every `ε > 0`, a polynomial-time algorithm that
outputs at most `k + C log n / ε²` distinct facilities, of cost at most `(1.9499 + ε)` times the
optimum with `k` facilities. -/
theorem kMedian_pseudoApproximation :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ A : Instance → List ℕ, Turing.MultiTapeTM.ComputableInPolyTime A encInstance encCenters ∧
        ∀ I : Instance, I.Valid →
          I.IsCenterList (A I) ∧ ((A I).length : ℝ) ≤ I.k + C * Real.log I.n / ε ^ 2 ∧
          I.cost (I.centers (A I)) ≤ (1.9499 + ε) * I.opt I.k :=
  sorry

/-- **Theorem 1.3** of [BCFGJPSSV26a], **Theorem 1.1** of [BCFGJPSSV26b]: an algorithm that,
given an instance, a number `L` and a rational accuracy `ε`, runs in time
`O(2^(e L) (N + 2)^e + N + L + |ε|)` with `e = a (⌈1/ε⌉ + 1)^b`, where `N` is the encoded length
of the instance and `|ε|` that of `ε` (not its absolute value), always outputs exactly `k`
distinct facilities, and, if `ε ∈ (0, 1/200)` and the instance is `β`-stable with `L ≥ 1/β`, with
probability at least `1 - ε` outputs facilities of cost at most `(1.89 + C ε)` times the
optimum. -/
theorem stable_kMedian_approximation :
    ∃ (A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ) (a b : ℕ) (C : ℝ),
      RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
        (stableTimeOf a b) ∧
      ∀ I : Instance, I.Valid → I.k ≤ I.m → ∀ (L : ℕ) (ε : ℚ),
        (∀ r, I.IsCenterList (A (((I, L), ε), r)) ∧ (A (((I, L), ε), r)).length = I.k) ∧
        (0 < ε → ε < 1 / 200 → ∀ β : ℝ, 0 < β → I.IsStable β → 1 / β ≤ L →
          1 - (ε : ℝ) ≤ coinProb (stableTimeOf a b ((I, L), ε))
            fun r ↦ I.cost (I.centers (A (((I, L), ε), r))) ≤
              (1.89 + C * ε) * I.opt I.k) :=
  sorry


/-- **Theorem 1.4** of [BCFGJPSSV26a] (Theorem 4.3 in full): a polynomial-time `1.9499`-LMP
approximation algorithm for uncapacitated facility location. Given an instance with at least one
client and an opening cost `f ≥ 0`, it outputs a nonempty set `S` of distinct facilities with
`cost S ≤ 1.9499 (OPT_f - f |S|)`. -/
theorem facilityLocation_lmp :
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length) :=
  sorry

end BCFGJPSSV26
