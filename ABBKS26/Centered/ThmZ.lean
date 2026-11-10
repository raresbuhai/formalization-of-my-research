module

public import ABBKS26.Centered.ThmZEmpirical

/-!
# Subspace theorem for centered mixtures

[ABBKS26, Theorem 5.6] (`thmZ`): the output of the orthogonal-complement rounding on the
rounded empirical centered system approximately contains the thin directions of every
compatible centered mixture, and has bounded dimension.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial
variable {k d : ℕ}


/-- The supplied RC2 output covers thin directions of every compatible centered model. -/
theorem thmZ (w r μ : ℚ) (p : QPoly d) (I : Rounding.ComplementInput d)
    (Y : Rounding.RoundOutput d) (hI : CenteredInputSpec w r μ p I)
    (hY : Rounding.ComplementResultSpec I Y) : CenteredResultSpec w r μ p Y := by
  obtain ⟨hlen, hproj, hrank, hcover⟩ := hY
  refine ⟨?_, hproj, hrank, ?_⟩
  · simpa only [dimensionCap, hI.radius_eq, hI.rank_eq] using hlen
  · intro m F γ hw hw' hμ hμ' hr hF hγ hp he v hv
    obtain ⟨Ps, hPs, hnear⟩ := hI.targets F γ hw hw' hμ hμ' hr hF hγ hp he
    have ht := hcover Ps hPs v ⟨hv.1, hnear v hv.1 hv.2⟩
    simpa only [hI.radius_eq] using ht


end

end ABBKS26.Centered
