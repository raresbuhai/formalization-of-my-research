module

public import BGHKLMM26.RobustMIS.Defs

/-!
# The sharp Gaussian lemma: definitions

The objects of the proof of the Gaussian lemma with the error `C √Δ` ([BGHKLMM26, Lemma 7.4]),
shared by the files `BGHKLMM26/RobustMIS/Sharp*.lean`, and the lemma itself as a statement,
`BGHKLMM26.RobustMIS.GaussSharp`.

The proof is local: Eldan's estimate (`BGHKLMM26.RobustMIS.gaussian_main`) puts `F` close to the
halfspace `H` whose normal is the first Hermite vector of `F`; near `H`, the deficit is at least
`(1 - t)` times the defect `I_t(F, H) = ⟨𝟙_H - F, T_t 𝟙_H⟩`, which is at least `c ‖F - 𝟙_H‖₁²`.

* `nBil t F G = ⟨F, T_t G⟩ = E[F(X) G(Y)]` for `t`-correlated `X, Y`; `gStab t F = nBil t F F`.
* `mehler t s s'`: the one-dimensional Mehler kernel, the density of a `t`-correlated pair of
  standard Gaussians with respect to the product of two standard Gaussians.
* `wfun t α s = T_t 𝟙{α ≤ ·}(s) = Φ((t s - α)/√(1 - t²))`.
* `hDefect t u α F = I_t(F, H) = ⟨𝟙_H - F, T_t 𝟙_H⟩` for the halfspace `H = {α ≤ ⟨u, x⟩}`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace
open Gaussian

variable {n : ℕ}

/-- The noise form `⟨F, T_t G⟩ = E[F(X) G(Y)]` for `t`-correlated standard Gaussian vectors,
`Y = t X + √(1 - t²) Z` with `X, Z` independent. -/
noncomputable def nBil (t : ℝ) (F G : Gs n → ℝ) : ℝ :=
  ∫ x, ∫ z, F x * G (t • x + √(1 - t ^ 2) • z) ∂gm n ∂gm n

theorem gStab_eq_nBil (t : ℝ) (F : Gs n → ℝ) : gStab t F = nBil t F F := rfl

/-- The **Mehler kernel**
`K_t(s, s') = (1 - t²)^{-1/2} exp((2 t s s' - t² (s² + s'²))/(2(1 - t²)))`:
`E f(t s + √(1 - t²) G) = ∫ f(s') K_t(s, s') dγ(s')`. -/
noncomputable def mehler (t s s' : ℝ) : ℝ :=
  (√(1 - t ^ 2))⁻¹ *
    Real.exp ((2 * t * s * s' - t ^ 2 * (s ^ 2 + s' ^ 2)) / (2 * (1 - t ^ 2)))

/-- `w(s) = T_t 𝟙{α ≤ ·}(s) = P(α ≤ t s + √(1 - t²) G) = Φ((t s - α)/√(1 - t²))`. -/
noncomputable def wfun (t α s : ℝ) : ℝ := Phi ((t * s - α) / √(1 - t ^ 2))

/-- The defect `I_t(F, H) = ⟨𝟙_H - F, T_t 𝟙_H⟩` of `F` against the halfspace
`H = {x : α ≤ ⟨u, x⟩}`. -/
noncomputable def hDefect (t : ℝ) (u : Gs n) (α : ℝ) (F : Gs n → ℝ) : ℝ :=
  nBil t (fun x ↦ halfInd u α x - F x) (halfInd u α)

/-- **The Gaussian lemma with the error `C √Δ`** ([BGHKLMM26, Lemma 7.4]), in the form of
`BGHKLMM26.RobustMIS.gaussian_main`: for a closed interval `[a, b] ⊂ (0, 1)` there are
`C, c₀, δ₀ > 0` such that a measurable `F : ℝⁿ → [0, 1]` with mean in `[a, b]` has
`Δ = Γ_t(E F) - Stab_t(F) ≥ 0`, and if `Δ ≤ δ₀` then `|F̂⁽¹⁾| ≥ c₀` and the halfspace with normal
`F̂⁽¹⁾` and the mean of `F` is within `C √Δ` of `F` in `L¹(γ)`. -/
def GaussSharp : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
    ∃ C c₀ δ₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < δ₀ ∧
      ∀ (n : ℕ) (F : Gs n → ℝ), Measurable F → (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
        a ≤ gMean F → gMean F ≤ b →
        0 ≤ gDef t F ∧
          (gDef t F ≤ δ₀ → c₀ ≤ ‖hermite1 F‖ ∧
            ∫ x, |F x - halfInd (hermite1 F) (-Psi (gMean F) * ‖hermite1 F‖) x| ∂gm n ≤
              C * √(gDef t F))

end BGHKLMM26.RobustMIS
