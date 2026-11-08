module

public import BMW26.Cube.Basic
public import Background.SumOfSquares.Normed

/-!
# Polynomials of the sum-of-squares analysis

The program of the algorithm, read on the hypercube: its variables are `X x`, `x ∈ Cube m` (the
value `f(x) ∈ {±1}` of the cut), and the analysis works with

* `BMW26.fcP S = ∑ₓ χ_S(x) X x` and `BMW26.aP S = 2^{-m} fcP S`: the Fourier coefficients
  `2^m f̂(S)` and `f̂(S)` as linear polynomials;
* `BMW26.energyP w`: the energy `∑ᵢ ∑_{xᵢ = false} w i x (X x - X (flip x i))²`;
* `BMW26.dirCount H i`: the number of edges of `H` in direction `i`, and
  `BMW26.cutPolyCube H δ`: the cut constraint `(2 + δ) · 2 |E(H)| - m · E_H(X) ≥ 0`, which says
  `E_H(f) / p̂ ≤ (2 + δ) 2^m` for the edge density `p̂ = 2 |E(H)| / (m 2^m)`;
* `BMW26.Good H p ε ξ τ₀`: what the analysis needs of the sample `H`: spectral closeness of `H`
  and of its half-cubes with diagonal errors of trace at most `ξ p 2^m`, and edge counts in each
  direction within a factor `1 ± τ₀` of `p 2^m / 2`.
-/

@[expose] public section

namespace BMW26

open Finset MvPolynomial SoS

variable {m : ℕ}

/-- The unnormalized Fourier coefficient `∑ₓ χ_S(x) X x`. -/
noncomputable def fcP (S : Finset (Fin m)) : MvPolynomial (Cube m) ℝ := ∑ x, C (chi S x) * X x

/-- The Fourier coefficient `f̂(S) = 2^{-m} ∑ₓ χ_S(x) X x`. -/
noncomputable def aP (S : Finset (Fin m)) : MvPolynomial (Cube m) ℝ := C (1 / 2 ^ m) * fcP S

/-- The energy polynomial `∑ᵢ ∑_{xᵢ = false} w i x (X x - X (flip x i))²`. -/
noncomputable def energyP (w : Fin m → Cube m → ℝ) : MvPolynomial (Cube m) ℝ :=
  ∑ i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), C (w i x) * (X x - X (flip x i)) ^ 2

open Classical in
/-- The number of edges of `H` in direction `i`. -/
noncomputable def dirCount (H : SimpleGraph (Cube m)) (i : Fin m) : ℕ :=
  (univ.filter fun x : Cube m ↦ x i = false ∧ H.Adj x (flip x i)).card

/-- The cut constraint of the program for a subgraph `H` of `Q_m`: `(2 + δ) · 2 |E(H)| - m E_H(X)`,
with `|E(H)| = ∑ᵢ dirCount H i`. -/
noncomputable def cutPolyCube (H : SimpleGraph (Cube m)) (δ : ℝ) : MvPolynomial (Cube m) ℝ :=
  C ((2 + δ) * 2 * ∑ i, (dirCount H i : ℝ)) - C (m : ℝ) * energyP (graphW H)

/-- What the analysis needs of the sample `H`. -/
structure Good (H : SimpleGraph (Cube m)) (p ε ξ τ₀ : ℝ) : Prop where
  le_cube : H ≤ cube m
  full : ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧ ∑ x, D x ≤ ξ * p * 2 ^ m ∧
    SpecClose (graphW H) 1 p ε D
  half : ∀ i, ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧ ∑ x, D x ≤ ξ * p * 2 ^ m ∧
    SpecClose (halfW i (graphW H)) (halfW i 1) p ε D
  count : ∀ i, |(dirCount H i : ℝ) - p * 2 ^ m / 2| ≤ τ₀ * (p * 2 ^ m / 2)

end BMW26
