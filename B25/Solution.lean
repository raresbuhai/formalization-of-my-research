module

public import B25.Model
import B25.RE.Main
import B25.Lasso.Main
import B25.Rot.Sphere
import B25.Rot.SubGauss

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder: Lemma 1.3 by `B25.partiallyRotated_of_uniform_main`
(`B25/Rot/Sphere.lean`), Lemma 1.4 by `B25.partiallyRotated_of_subgaussian_main`
(`B25/Rot/SubGauss.lean`), Theorem 1.5 by `B25.re_of_partiallyRotated_main` (`B25/RE/Main.lean`)
and Corollary 1.6 by `B25.lasso_of_partiallyRotated_main` (`B25/Lasso/Main.lean`). Don't import
`Challenge` here: the names would clash.
-/

public section

namespace B25

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma 1.3** of [B25]: rotating the columns outside `S` by a random matrix that maps every
fixed unit vector to a uniform point of the sphere gives a partially-rotated design. -/
theorem partiallyRotated_of_uniform :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ),
        (∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → P.map (fun ω ↦ R ω *ᵥ v) = uniformSphere n) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) c :=
  partiallyRotated_of_uniform_main

/-- **Lemma 1.4** of [B25]: rotating the columns outside `S` by a random matrix with independent
sub-Gaussian entries gives a partially-rotated design. -/
theorem partiallyRotated_of_subgaussian :
    ∃ c K : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ) (σ σ' : ℝ), 0 < σ → K * (σ' / σ) ^ 4 ≤ n →
        iIndepFun (fun (ij : Fin n × Fin n) (ω : Ω) ↦ R ω ij.1 ij.2) P →
        (∀ i j, ∫ ω, R ω i j ∂P = 0) →
        (∀ i j, Var[fun ω ↦ R ω i j; P] = σ ^ 2) →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ R ω i j) (σ' ^ 2).toNNReal P) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) (c * σ ^ 4 / σ' ^ 4) :=
  partiallyRotated_of_subgaussian_main

/-- **Theorem 1.5** of [B25]: with probability `1 - e^(-Ω(n))`, a partially-rotated design with
columns of norm `√n` has `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)` for every `S' ⊆ S` with
`n ≥ C |S'| log d / γ_{S'}(X_S)`. -/
theorem re_of_partiallyRotated :
    ∀ c : ℝ, 0 < c → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ),
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        P {ω | ∃ S' ⊆ S,
            C * S'.card * Real.log d ≤ n * reConst (cols (X ω) S) (S'.subtype (· ∈ S)) ∧
              reConst (X ω) S' < 9 / 10 * reConst (cols (X ω) S) (S'.subtype (· ∈ S))} ≤
          ENNReal.ofReal (Real.exp (-(c' * n))) :=
  re_of_partiallyRotated_main

/-- **Corollary 1.6** of [B25]: for a partially-rotated design with columns of norm `√n` and a
secret supported in `S`, with high probability every Lasso estimate has prediction error
`(1/n) ‖X β̂ - X β‖₂² ≤ C σ² |supp β| log d / (γ_{supp β}(X_S) n)`. -/
theorem lasso_of_partiallyRotated :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 1 ≤ τ → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ), Measurable X →
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        ∀ (σ : ℝ) (β : Fin d → ℝ), supp β ⊆ S →
          (∀ ω w, ∃ b, IsLasso (X ω) (X ω *ᵥ β + w) (l1 β) b) ∧
          (P.prod (noiseLaw n σ))
              {p | ∃ b, IsLasso (X p.1) (X p.1 *ᵥ β + p.2) (l1 β) b ∧
                C * σ ^ 2 * (supp β).card * Real.log d <
                  reConst (cols (X p.1) S) ((supp β).subtype (· ∈ S)) *
                    ((X p.1 *ᵥ (b - β)) ⬝ᵥ (X p.1 *ᵥ (b - β)))} ≤
            ENNReal.ofReal (Real.exp (-(c' * n)) + 2 * (d : ℝ) ^ (-τ)) :=
  lasso_of_partiallyRotated_main

end B25
