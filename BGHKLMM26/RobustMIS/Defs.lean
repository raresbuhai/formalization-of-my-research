module

public import BGHKLMM26.Hardness.Defs
public import Background.GaussianCoins
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Robust Majority is Stablest: definitions

The objects of the proof of [BGHKLMM26, Theorem 7.1], shared by the files of
`BGHKLMM26/RobustMIS/`. See `BGHKLMM26/RobustMIS/README.md` for the route of the proof.

* **One-dimensional Gaussian functions**: the density `npdf = φ`, the quantile `Psi = Φ⁻¹`, the
  isoperimetric function `qf = φ ∘ Φ⁻¹`, the bivariate quadrant function `Gam r a = Γ_r(a)`
  (`= Λ_r(a, a)` of the paper), `kap r = √((1-r)/(1+r))`, `lam a = a(1-a)`, and the two rates
  `psiL x = x √(log(1/x))` (Eldan's `ψ`) and `sqrtLog x = √(x̄ log(e/x̄))`, `x̄ = min(max x 0, 1)`
  (the `ω` of `eldan-proof.tex`).
* **Gaussian space** `Gs n = EuclideanSpace ℝ (Fin n)` with its standard Gaussian `gm n`: the mean
  `gMean`, the first Hermite (level-one) vector `hermite1 F = E[F(G) G]`, the noise stability
  `gStab t F = E[F(X) F(Y)]` with `Y = t X + √(1-t²) Z`, the deficit
  `gDef t F = Γ_t(E F) - gStab t F`, halfspace indicators `halfInd w θ = 𝟙{θ ≤ ⟨w, x⟩}`.
* **Eldan's static quantities** of `g : ℝⁿ → [0,1]` (§4 of `eldan-proof.tex`): the matrix
  `bMat g = E[(x xᵀ - I) g]`, its squared Hilbert–Schmidt norm `hs2 g`, the bilinear form
  `bForm g v w = ⟨B v, w⟩`, the centroid deficit `epsF g = q(S)² - |U|²` and the drift numerator
  `driftD g = Ψ(S)² |U|² - ‖B‖²_HS`.
* **Eldan's heat flow** (§5): `flowFun f s x = f(x + √(1-s) ·)`, `heatU f s x = u(s,x)`,
  `eFlow f s x = e(s,x)`, `betaFlow f s x = β(s,x)`, `yFlow f s = E e(s, √s Z)`.
* **Multilinear polynomials** on the cube and on Gaussian space: `mlEval c x = ∑_S c_S ∏_{i∈S} xᵢ`
  (subsets `S` are points `s : Cube (Fin R)`, as in `OAI`'s Walsh analysis), the smoothing
  `smoothC r c` (`c_S ↦ r^|S| c_S`, i.e. `T_r`), influences `inflC`, linear forms `linC`, the
  sign vector `bitVec x = (σ(xᵢ))ᵢ` of a cube point, the multilinear extension `gaussExt r u` of
  `T_r u` to Gaussian space (the paper's `P_{u,r}`), and the truncation `clamp01`.
* **Test functions** of two variables for the invariance principle: `LipPair Ψ K` (`K`-Lipschitz
  for the `ℓ¹` distance on `ℝ²`) and `LineC3 Φ B` (`C³` along lines, third derivative
  `≤ B ‖direction‖₁³`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic Gaussian

/-! ### One-dimensional Gaussian functions -/

/-- The standard normal density `φ(y) = e^{-y²/2}/√(2π)`. -/
noncomputable abbrev npdf (y : ℝ) : ℝ := gaussianPDFReal 0 1 y

/-- The quantile `Ψ = Φ⁻¹` on `(0, 1)`, and `0` outside. -/
noncomputable def Psi (a : ℝ) : ℝ :=
  if h : a ∈ Ioo (0 : ℝ) 1 then Classical.choose (exists_Phi_eq h) else 0

/-- The Gaussian isoperimetric function `q(a) = φ(Φ⁻¹(a))` on `(0, 1)`, with `q(0) = q(1) = 0`
(and `0` outside `[0, 1]`). -/
noncomputable def qf (a : ℝ) : ℝ := if a ∈ Ioo (0 : ℝ) 1 then npdf (Psi a) else 0

/-- `λ(a) = a (1 - a)`. -/
def lam (a : ℝ) : ℝ := a * (1 - a)

/-- `κ_r = √((1 - r)/(1 + r))`. -/
noncomputable def kap (r : ℝ) : ℝ := √((1 - r) / (1 + r))

/-- `Γ_r(a) = P(G ≤ Φ⁻¹(a), H ≤ Φ⁻¹(a))` for a standard bivariate Gaussian pair `(G, H)` with
correlation `r` (the paper's `Λ_r(a, a)`), written as `P(Φ(G) ≤ a, Φ(H) ≤ a)`: so `Γ_r(0) = 0`,
`Γ_r(1) = 1`, and `Γ_r` is constant outside `[0, 1]`. -/
noncomputable def Gam (r a : ℝ) : ℝ := (corrPair r).real {p | Phi p.1 ≤ a ∧ Phi p.2 ≤ a}

/-- Eldan's `ψ(x) = x √(log(1/x))` (`ψ(0) = 0`); used for `0 ≤ x ≤ e^{-1/2}`. -/
noncomputable def psiL (x : ℝ) : ℝ := x * √(Real.log (1 / x))

/-- `x̄ = min(max x 0, 1)`. -/
noncomputable def clip01 (x : ℝ) : ℝ := min (max x 0) 1

/-- The rate `ω(x) = √(x̄ log(e/x̄))`, `x̄ = min(max x 0, 1)`, `ω(0) = 0` (Lemma 1.3 of
`eldan-proof.tex`): the rate of Eldan's estimate (`gaussian_main`). -/
noncomputable def sqrtLog (x : ℝ) : ℝ := √(clip01 x * Real.log (exp 1 / clip01 x))

/-- The truncation `x ↦ max 0 (min 1 x)` to `[0, 1]`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-! ### Gaussian space -/

/-- Gaussian space `ℝⁿ`. -/
abbrev Gs (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard Gaussian measure `γₙ`. -/
noncomputable abbrev gm (n : ℕ) : Measure (Gs n) := stdGaussian (Gs n)

variable {n : ℕ}

/-- The mean `E F(G)`. -/
noncomputable def gMean (F : Gs n → ℝ) : ℝ := ∫ x, F x ∂gm n

/-- The first Hermite (level-one Fourier) vector `F̂⁽¹⁾ = E[F(G) G]`. -/
noncomputable def hermite1 (F : Gs n → ℝ) : Gs n := ∫ x, F x • x ∂gm n

/-- Gaussian noise stability `Stab_t(F) = E[F(X) F(Y)]` for `t`-correlated standard Gaussian
vectors, `Y = t X + √(1 - t²) Z` with `X, Z` independent. -/
noncomputable def gStab (t : ℝ) (F : Gs n → ℝ) : ℝ :=
  ∫ x, ∫ z, F x * F (t • x + √(1 - t ^ 2) • z) ∂gm n ∂gm n

/-- The stability deficit `Δ(F) = Γ_t(E F) - Stab_t(F)`. -/
noncomputable def gDef (t : ℝ) (F : Gs n → ℝ) : ℝ := Gam t (gMean F) - gStab t F

/-- Eldan's constant `c₁(t, m) = ½ κ_t min(t, λ(m)³/1280)` (Theorem A of `eldan-proof.tex`). -/
noncomputable def eldanC1 (t m : ℝ) : ℝ := 1 / 2 * kap t * min t (lam m ^ 3 / 1280)

/-- The indicator of the halfspace `{x : θ ≤ ⟨w, x⟩}`. -/
noncomputable def halfInd (w : Gs n) (θ : ℝ) : Gs n → ℝ := Set.indicator {x | θ ≤ ⟪w, x⟫} 1

/-! ### Eldan's static quantities (§4 of `eldan-proof.tex`) -/

/-- `B = E[(x xᵀ - I) g(x)]`, as a matrix. -/
noncomputable def bMat (g : Gs n → ℝ) (i j : Fin n) : ℝ :=
  ∫ x, (x i * x j - if i = j then 1 else 0) * g x ∂gm n

/-- `⟨B v, w⟩ = E[(⟨v, x⟩⟨w, x⟩ - ⟨v, w⟩) g(x)]`. -/
noncomputable def bForm (g : Gs n → ℝ) (v w : Gs n) : ℝ :=
  ∫ x, (⟪v, x⟫ * ⟪w, x⟫ - ⟪v, w⟫) * g x ∂gm n

/-- `‖B‖²_HS`. -/
noncomputable def hs2 (g : Gs n → ℝ) : ℝ := ∑ i, ∑ j, bMat g i j ^ 2

/-- The centroid deficit `ε(g) = q(S)² - |U|²`, `S = E g`, `U = E[g(x) x]`. -/
noncomputable def epsF (g : Gs n → ℝ) : ℝ := qf (gMean g) ^ 2 - ‖hermite1 g‖ ^ 2

/-- The drift numerator `D(g) = Ψ(S)² |U|² - ‖B‖²_HS`. -/
noncomputable def driftD (g : Gs n → ℝ) : ℝ := Psi (gMean g) ^ 2 * ‖hermite1 g‖ ^ 2 - hs2 g

/-! ### Eldan's heat flow (§5 of `eldan-proof.tex`) -/

/-- `f_{s,x}(y) = f(x + √(1 - s) y)`. -/
noncomputable def flowFun (f : Gs n → ℝ) (s : ℝ) (x : Gs n) : Gs n → ℝ :=
  fun y ↦ f (x + √(1 - s) • y)

/-- The heat flow `u(s, x) = E f(x + √(1 - s) Z)`. -/
noncomputable def heatU (f : Gs n → ℝ) (s : ℝ) (x : Gs n) : ℝ := gMean (flowFun f s x)

/-- `e(s, x) = q(u)² - |U|²`, `U(s, x) = E[Z f(x + √(1-s) Z)]`. -/
noncomputable def eFlow (f : Gs n → ℝ) (s : ℝ) (x : Gs n) : ℝ := epsF (flowFun f s x)

/-- The drift `β(s, x) = (1 - s)⁻¹ (Ψ(u)² |U|² - ‖B‖²_HS)`. -/
noncomputable def betaFlow (f : Gs n → ℝ) (s : ℝ) (x : Gs n) : ℝ :=
  (1 - s)⁻¹ * driftD (flowFun f s x)

/-- `y(s) = E e(s, √s Z)`. -/
noncomputable def yFlow (f : Gs n → ℝ) (s : ℝ) : ℝ := ∫ z, eFlow f s (√s • z) ∂gm n

/-! ### Multilinear polynomials on the cube and on Gaussian space -/

variable {R : ℕ}

/-- The size `|S|` of a subset `S`, given as a point of the cube (`OAI`'s `degree`; the name is
taken by `BGHKLMM26.degree` here). -/
abbrev sdeg (s : Cube (Fin R)) : ℕ := OAI.OptimalMaxCut.Analytic.degree s

/-- The sign vector `(σ(xᵢ))ᵢ ∈ {±1}^R` of a cube point (`σ = bitSign`, `σ(false) = 1`). -/
def bitVec (x : Cube (Fin R)) : Fin R → ℝ := fun i ↦ bitSign (x i)

/-- The multilinear polynomial with coefficients `c`, `x ↦ ∑_S c_S ∏_{i ∈ S} xᵢ` (a subset `S` is a
point `s : Cube (Fin R)`, `i ∈ S ↔ s i`). -/
noncomputable def mlEval (c : Cube (Fin R) → ℝ) (x : Fin R → ℝ) : ℝ :=
  ∑ s, c s * ∏ i, if s i then x i else 1

/-- The noise operator on coefficients: `c_S ↦ r^|S| c_S`. -/
noncomputable def smoothC (r : ℝ) (c : Cube (Fin R) → ℝ) : Cube (Fin R) → ℝ :=
  fun s ↦ r ^ sdeg s * c s

/-- The influence `∑_{S ∋ i} c_S²` of a coefficient vector (for `c = coefficient f` this is
`influence i f`). -/
noncomputable def inflC (c : Cube (Fin R) → ℝ) (i : Fin R) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Cube (Fin R) ↦ s i = true), c s ^ 2

/-- The coefficients of the linear form `x ↦ ∑ᵢ wᵢ xᵢ`. -/
noncomputable def linC (w : Fin R → ℝ) : Cube (Fin R) → ℝ :=
  fun s ↦ ∑ i, if s = (fun j ↦ decide (j = i)) then w i else 0

/-- The paper's `P_{u,r}`: the multilinear extension of `T_r u` evaluated on Gaussian space. -/
noncomputable def gaussExt (r : ℝ) (u : Cube (Fin R) → ℝ) (G : Gs R) : ℝ :=
  mlEval (smoothC r (coefficient u)) G

/-! ### Test functions for the invariance principle -/

/-- `Ψ : ℝ × ℝ → ℝ` (curried) is `K`-Lipschitz for the `ℓ¹` distance. -/
def LipPair (Ψ : ℝ → ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ a b a' b' : ℝ, |Ψ a b - Ψ a' b'| ≤ K * (|a - a'| + |b - b'|)

/-- `Φ` is `C³` along every line `x ↦ (a + x a', b + x b')`, with third derivative at most
`B (|a'| + |b'|)³`. -/
def LineC3 (Φ : ℝ → ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ a b a' b' : ℝ, ContDiff ℝ 3 (fun x : ℝ ↦ Φ (a + x * a') (b + x * b')) ∧
    ∀ x : ℝ, |iteratedDeriv 3 (fun x : ℝ ↦ Φ (a + x * a') (b + x * b')) x| ≤
      B * (|a'| + |b'|) ^ 3

end BGHKLMM26.RobustMIS
