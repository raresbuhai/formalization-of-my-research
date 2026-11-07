module

public import BKS23.Model

/-!
# The spectral norm of the cut: definitions

The property of the cut of a graph `R` between a set `U` and its complement that the degree-4
certificate of [BKS23, Lemma 4.13] needs: the centred cut matrix `M_uv = 𝟙[u ∼ v] - q`
(`u ∈ U`, `v ∉ U`) has spectral norm at most `√Λ` (`BKS23.Spectral.NormLE`).

`BKS23/SpectralNorm.lean` shows that the cut of `G(n, q)` has it with `Λ = 18 n q (1 - q)` with
high probability ([BKS23, Fact 3.14]); `BKS23/SpectralCertificate.lean` turns it into the
certificate.
-/

@[expose] public section

namespace BKS23.Spectral

open Finset

variable {n : ℕ}

open Classical in
/-- The centred adjacency: `1 - q` across an edge of `R`, `-q` across a non-edge. -/
noncomputable def cent (q : ℝ) (R : SimpleGraph (Fin n)) (u v : Fin n) : ℝ :=
  if R.Adj u v then 1 - q else -q

/-- **The centred cut matrix has norm at most `√Λ`**:
`∑_{u ∈ U} (∑_{v ∉ U} M_uv y_v)² ≤ Λ ∑_{v ∉ U} y_v²` for every `y`, with `M_uv = 𝟙[u ∼ v] - q`. -/
def NormLE (q : ℝ) (U : Finset (Fin n)) (Λ : ℝ) (R : SimpleGraph (Fin n)) : Prop :=
  ∀ y : Fin n → ℝ, ∑ u ∈ U, (∑ v ∈ Uᶜ, cent q R u v * y v) ^ 2 ≤ Λ * ∑ v ∈ Uᶜ, y v ^ 2

end BKS23.Spectral
