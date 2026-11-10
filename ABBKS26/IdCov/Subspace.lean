module

public import ABBKS26.IdCov.SubspaceAux

/-!
# Subspace theorem for identical covariances

[ABBKS26, Theorem 6.5] (`thmSUB`): the output of the orthogonal-complement rounding on the
rounded moment system approximately contains every direction of small variance of every
compatible mixture, and has bounded dimension.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial
variable {d : ℕ}

/-- SUB's full output contract, uniform over all counts below the public component cap. -/
def IdCovResultSpec (cap : ℕ) (w β : ℚ) (M : ℕ → QPoly d)
    (Y : Rounding.RoundOutput d) : Prop :=
  Y.basis.length ≤ N_pack β cap ∧ Projection Y.proj ∧
    Y.proj.rank = Y.basis.length ∧
    ∀ {m : ℕ} (D : Data m d) γ, m ≤ cap →
      0 < w → w ≤ 1 / 2 → 0 < β → β ≤ 1 / 4 →
      D.Valid (w / 2) γ → γ ≤ gammaStar β →
      momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w) (etaStar w β / 4) →
      Covers Y.proj {u | sqnorm u = 1 ∧ qform D.cov u ≤ tauStar β} β


/-- Every compatible thin direction is covered by the supplied RC2 output.
The input rounds the original moment estimates once, before forming its constraints. -/
theorem thmSUB (cap : ℕ) (w β : ℚ) (M : ℕ → QPoly d)
    (Y : Rounding.RoundOutput d)
    (hY : Rounding.ComplementResultSpec (SubspaceAux.input cap d w β M) Y) :
    IdCovResultSpec cap w β M Y := by
  obtain ⟨hlen, hproj, hrank, hcover⟩ := hY
  refine ⟨hlen, hproj, hrank, ?_⟩
  intro m D γ hm hw hw' hβ hβ' hD hγ hM u hu
  obtain ⟨P, hI, hnear⟩ := SubspaceAux.input_hypotheses_bounded D cap hm M w β γ
    ⟨hw, hw'⟩ ⟨hβ, hβ'⟩ hD hγ hM
  exact hcover [P] hI u ⟨hu.1, P, by simp, hnear u hu.1 hu.2⟩


end

end ABBKS26.IdCov
