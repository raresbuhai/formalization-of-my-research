module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# Functions on the Boolean cube

The definitions that [BGHKLMM26, Theorem 7.1] (`BGHKLMM26.robust_majority_is_stablest` in
`BGHKLMM26/Challenge.lean`) is stated in, following the notation of [BGHKLMM26, Sections 4
and 7.1]. A point `x ∈ {0,1}^R` is a function `Fin R → Bool`, with `true` for `1`; the expectations
are under the uniform measure on `{0,1}^R`, written as sums divided by `2^R`.

* **Signs and characters** (`BGHKLMM26.cubeSign`): the bit `xᵢ` has the sign `σᵢ = 2xᵢ - 1`, and
  the character of `S ⊆ [R]` is `χ_S(x) = ∏_{i ∈ S} σᵢ`.
* **Fourier coefficients and influences** (`BGHKLMM26.cubeFourier`, `BGHKLMM26.cubeInfluence`):
  `f̂(S) = E[f χ_S]` and `Inf_i(f) = ∑_{S ∋ i} f̂(S)²`.
* **Correlated pairs and the cut value** (`BGHKLMM26.corrProb`, `BGHKLMM26.cubeCut`): `X` uniform
  and `Y` a `ρ`-correlated copy of `X`, each `Yᵢ = Xᵢ` with probability `(1 + ρ)/2`
  independently; `Cut_ρ(f) = E[Cut(f(X), f(Y))]` with `Cut(a, b) = a + b - 2ab`.
* **Linear threshold functions and the `L¹` distance** (`BGHKLMM26.IsCubeLTF`,
  `BGHKLMM26.cubeL1`): `L(x) = 1(∑ᵢ wᵢ (2xᵢ - 1) + θ ≥ 0)`, constants included, and
  `‖f - g‖₁ = E|f - g|`.
-/

@[expose] public section

namespace BGHKLMM26

/-- The sign `σ = 2b - 1 ∈ {±1}` of a bit `b ∈ {0, 1}`, with `true` for `1`: the identification
of `{0,1}^R` with `{±1}^R` in [BGHKLMM26, Section 7.1]. -/
def cubeSign (b : Bool) : ℝ := 2 * (b.toNat : ℝ) - 1

/-- The **Fourier coefficient** `f̂(S) = E_x[f(x) χ_S(x)]` of `f : {0,1}^R → ℝ` at `S ⊆ [R]`, for
the character `χ_S(x) = ∏_{i ∈ S} (2xᵢ - 1)`. The characters are an orthonormal basis, so these
are the coefficients of `f = ∑_S f̂(S) χ_S`. -/
noncomputable def cubeFourier {R : ℕ} (f : (Fin R → Bool) → ℝ) (S : Finset (Fin R)) : ℝ :=
  (∑ x, f x * ∏ i ∈ S, cubeSign (x i)) / 2 ^ R

/-- The **influence** `Inf_i(f) = ∑_{S ∋ i} f̂(S)²` of the coordinate `i` on `f : {0,1}^R → ℝ`. -/
noncomputable def cubeInfluence {R : ℕ} (f : (Fin R → Bool) → ℝ) (i : Fin R) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin R) ↦ i ∈ S), cubeFourier f S ^ 2

/-- The probability that `(X, Y) = (x, y)` when `X` is uniform on `{0,1}^R` and `Y` is a
`ρ`-correlated copy of `X`: each `Yᵢ` is `Xᵢ` with probability `(1 + ρ)/2` and `1 - Xᵢ` with
probability `(1 - ρ)/2`, independently. -/
noncomputable def corrProb (ρ : ℝ) {R : ℕ} (x y : Fin R → Bool) : ℝ :=
  (∏ i, if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2) / 2 ^ R

/-- The **cut value** `Cut_ρ(f) = E[Cut(f(X), f(Y))]` of `f : {0,1}^R → ℝ` over `ρ`-correlated
`X, Y`, where `Cut(a, b) = a + b - 2ab` is `1(a ≠ b)` on bits. -/
noncomputable def cubeCut (ρ : ℝ) {R : ℕ} (f : (Fin R → Bool) → ℝ) : ℝ :=
  ∑ x, ∑ y, corrProb ρ x y * (f x + f y - 2 * f x * f y)

/-- `L` is a **linear threshold function** (LTF) on `{0,1}^R`:
`L(x) = 1(∑ᵢ wᵢ (2xᵢ - 1) + θ ≥ 0)` for some real `w` and `θ`. The constants `0` and `1` are LTFs
(`w = 0`). -/
def IsCubeLTF {R : ℕ} (L : (Fin R → Bool) → ℝ) : Prop :=
  ∃ (w : Fin R → ℝ) (θ : ℝ), ∀ x,
    L x = if 0 ≤ ∑ i, w i * cubeSign (x i) + θ then 1 else 0

/-- The **`L¹` distance** `‖f - g‖₁ = E_x |f(x) - g(x)|` of functions on `{0,1}^R`. -/
noncomputable def cubeL1 {R : ℕ} (f g : (Fin R → Bool) → ℝ) : ℝ :=
  (∑ x, |f x - g x|) / 2 ^ R

end BGHKLMM26
