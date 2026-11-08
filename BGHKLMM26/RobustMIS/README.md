# Robust Majority is Stablest

[BGHKLMM26, Theorem 7.1], `BGHKLMM26.RobustMIS.robustMIS : BGHKLMM26.Hard.RobustMIS`
([Final.lean](Final.lean); the statement is in [../Hardness/Defs.lean](../Hardness/Defs.lean)): for
`ρ ∈ (-1, 0)` there are `C, η₀` such that for every `ξ > 0` there is `τ > 0` with the following
property. A table `g : {0,1}^R → [0,1]` with all influences at most `τ` that cuts at least
`arccos ρ / π - η` of the `ρ`-correlated pairs, `0 ≤ η ≤ η₀`, is within `C √η + ξ` of an LTF.

The paper's proof rests on Heilman's robust Borell inequality, a preprint, for its Gaussian lemma
(Lemma 7.4, with the error `C √Δ`). Here the Gaussian lemma is proved in two steps. Eldan's
estimate (Invent. Math. 2015), in an analytic form of his argument that replaces stochastic calculus
by the heat semigroup, gives the error `C √(Δ log(e/Δ))`, and so puts the function close to the
halfspace. Near the halfspace, a local spectral argument gives the error `C √Δ`.

## The route

1. **The Gaussian lemma** (Lemma 7.4, `BGHKLMM26.RobustMIS.gaussian_sharp :
   BGHKLMM26.RobustMIS.GaussSharp`): a function `F : ℝⁿ → [0,1]` of mean in a compact subinterval
   of `(0,1)`, whose noise stability is within `Δ` of Borell's bound `Γ_t(E F)`, is within `C √Δ`
   in `L¹` of the halfspace `H` whose normal is its first Hermite coefficient vector.
   * **Eldan's estimate** (`BGHKLMM26.RobustMIS.gaussian_main`), with `C √(Δ log(e/Δ))`. Along the
     heat flow `u(s, x) = E F(x + √(1-s) Z)`: the deficit is an integral of a nonnegative quantity
     `e` (deficit identity), whose drift is controlled by static Gaussian bounds (bathtub, fiber
     decomposition, Bessel bounds); a bootstrap on the drift and the concentration of `u` give the
     lower bound on the deficit, and a quantitative bathtub turns it into an `L¹` bound.
   * **The local estimate** (`BGHKLMM26.RobustMIS.sharp_local`): when `F` is close to `H`, has its
     mean and its first Hermite vector along its normal, `Δ ≥ (1 - t) I`, where
     `I = ⟨𝟙_H - F, T_t 𝟙_H⟩ = Δ/2 + Stab_t(F - 𝟙_H)/2`. The part of `F - 𝟙_H` in a thin strip
     around the boundary collapses, through the Mehler kernel along the normal, to its signed fiber
     mass, whose constant and linear Hermite modes are those of the rest; the spectral gap of the
     noise operator (levels above one damped by `t²`, from TauCeti's Hermite basis of `L²(γ)`)
     beats the first moments of the fiber masses, which carry the factor `t`. The rest, outside the
     strip, costs `o(‖·‖₁)` by Borell's inequality, in place of hypercontractivity.
   * **The transport bound** (`BGHKLMM26.RobustMIS.sharp_transport`): `I ≥ c ‖F - 𝟙_H‖₁²`. With
     the local estimate, `‖F - 𝟙_H‖₁ ≤ C √Δ`.
2. **Back to the cube** (Lemma 7.5, `BGHKLMM26.RobustMIS.smoothed_transfer`, which takes the
   Gaussian lemma with the error `C √Δ`, `BGHKLMM26.RobustMIS.GaussSharp`, as a hypothesis): the
   smoothed table `T_r u`, read as a multilinear polynomial in Gaussian variables and truncated to
   `[0,1]`, has the same mean and nearly the same stability, so the Gaussian lemma applies; one
   invariance principle, for the pair `(T_r u, ⟨w, x⟩)` with a Lipschitz test function, brings the
   halfspace back to the cube, within `C √(Γ_t(E u) - Stab_t(u)) + C √(1 - r) + ξ`. It replaces the
   paper's anti-concentration of regular linear forms and Mossel–Neeman's Lemma 7.3.
3. **Smoothing removal** (Lemma 7.6, `BGHKLMM26.RobustMIS.smoothing_removal`,
   `BGHKLMM26.RobustMIS.regular_ltf_noise`): `‖u - L‖₁ ≤ ‖T_r u - L‖₁ + 2 ‖L - T_r L‖₁`, with the
   noise sensitivity of regular LTFs bounded by anti-concentration (from the invariance principle)
   instead of Peres's bound for all LTFs; `r` depends only on `ξ`, so the rate in `1 - r` does not
   matter.
4. **Invariance** in qualitative form (`BGHKLMM26.RobustMIS.invariance`): degree truncation, the
   Bonami lemma, Lindeberg's replacement for pairs of low-degree polynomials, and mollification of
   the test function.
5. **Theorem 7.1** (`BGHKLMM26.RobustMIS.robustMIS_of_sharp (hG : GaussSharp)` in
   [Main.lean](Main.lean), with the error `C √η`): the paper's proof. Majority is Stablest for the
   odd part bounds the mean, and the even part turns the condition at `ρ < 0` into one at `-ρ > 0`
   (Corollary 7.7, `BGHKLMM26.RobustMIS.positive_transfer`, with the error
   `C √([Γ_t(E u) - Stab_t(u)]⁺) + ξ`).

## Files

| Files | Content |
| --- | --- |
| [Defs.lean](Defs.lean) | Definitions: `Φ⁻¹`, `q = φ ∘ Φ⁻¹`, `Γ_t`, the rates, Gaussian space and noise stability, Eldan's quantities, the heat flow, multilinear polynomials and their Gaussian extensions. |
| [Normal.lean](Normal.lean), [Quantile.lean](Quantile.lean), [Rates.lean](Rates.lean), [Gamma.lean](Gamma.lean), [GammaCalc.lean](GammaCalc.lean) | One-dimensional facts: Gaussian integrals and tails, the quantile and `q`, the rates `ψ` and `ω`, the quadrant function `Γ_r` through Owen's `T` function (TauCeti). |
| [Static1D.lean](Static1D.lean), [Static.lean](Static.lean), [Bessel.lean](Bessel.lean), [StaticFiberAux.lean](StaticFiberAux.lean), [StaticFiber.lean](StaticFiber.lean), [StaticDrift.lean](StaticDrift.lean), [QBath.lean](QBath.lean) | Static Gaussian bounds: bathtub, marginals, Bessel bounds, the fiber decomposition, the drift bound (constant `10`), the quantitative bathtub. |
| [ItoAux.lean](ItoAux.lean), [Ito.lean](Ito.lean), [FlowAux.lean](FlowAux.lean), [Flow.lean](Flow.lean) | The Gaussian Itô formula in expectation (Stein's identity) and the regularity of the heat flow for measurable `F` (kernel integrals, all derivatives, both heat equations). |
| [DriftAux.lean](DriftAux.lean), [Deficit.lean](Deficit.lean), [Drift.lean](Drift.lean), [Concentration.lean](Concentration.lean) | The deficit identity and Borell's inequality with a remainder, the drift identity, the sub-Gaussian concentration of `u`. |
| [DriftEstimate.lean](DriftEstimate.lean), [Bootstrap.lean](Bootstrap.lean), [Gaussian.lean](Gaussian.lean) | The drift estimate, the bootstrap, and Eldan's estimate. |
| [SharpDefs.lean](SharpDefs.lean), [SharpBasic.lean](SharpBasic.lean), [SharpHalf.lean](SharpHalf.lean) | The noise form `⟨F, T_t G⟩`, the Mehler kernel, the defect `I`, and the statement `GaussSharp`; symmetry, positivity, Young's inequality and the small-mass bound of the noise form; the halfspace, the defect as a weighted mismatch, the deficit identity, the transport bound. |
| [SharpFiber.lean](SharpFiber.lean), [SharpHermite.lean](SharpHermite.lean), [SharpLocal.lean](SharpLocal.lean), [Sharp.lean](Sharp.lean) | The Mehler kernel along the normal and the strip bound; the spectral gap of the noise operator (Hermite basis from TauCeti, in [../../Imported/TauCeti](../../Imported/TauCeti)); the local estimate; the Gaussian lemma with the error `C √Δ`. |
| [Multilinear.lean](Multilinear.lean), [MultilinearGauss.lean](MultilinearGauss.lean), [GaussL2.lean](GaussL2.lean), [Bonami.lean](Bonami.lean) | Multilinear polynomials on the cube and on Gaussian space, `L²` continuity, the Bonami lemma. |
| [Mollify.lean](Mollify.lean), [Lindeberg.lean](Lindeberg.lean), [Invariance.lean](Invariance.lean) | The invariance principle. |
| [Truncation.lean](Truncation.lean), [NoiseLTF.lean](NoiseLTF.lean), [BackToCube.lean](BackToCube.lean), [Transfer.lean](Transfer.lean), [Main.lean](Main.lean), [Final.lean](Final.lean) | The truncation, the smoothing removal, the transfer to the cube, and Theorem 7.1. |

Some lemmas are adapted from, or follow, OpenAI's library (`openai/math`, Apache-2.0, commit
`4eaee87`): Gaussian densities, translation and Stein's identity (`ItoAux.lean`, from
`GaussianPropeller/{Translation,Stein}.lean`), Gaussian moments (`Bonami.lean`, from
`Analysis/ProductSpaces/ScalarBounds.lean`), and the calculus of `Φ⁻¹` and of tail moments
(`Quantile.lean`, `Normal.lean`, after `GaussianPropeller/{Quantile,OneCell}.lean`); the files say
where.
