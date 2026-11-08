module

public import BHJK25.RS.Defs

/-!
# Relabelling and the planted distribution on a tensor

Relabelling a tensor by a permutation `σ` of the vertices (`BHJK25.relabel`) reads the entry at
`σ⁻¹(S)` (`BHJK25.RS.relabel_apply`); it is an action of the permutations
(`BHJK25.RS.relabel_mul`) by bijections (`BHJK25.RS.relabelEquiv`); it commutes with reading an
entry (`BHJK25.RS.readAt_relabel`) and with the noise (`BHJK25.RS.noiseMass_relabel`). The planted
distribution (`BHJK25.RS.planted`) gives a tensor the fraction of the pairs (sample, permutation)
that produce it (`BHJK25.RS.planted_singleton`).
-/

@[expose] public section

namespace BHJK25.RS

open MeasureTheory Finset

variable {k T n : ℕ}

/-! ### Relabelling -/

/-- The image of a `k`-set under a permutation. -/
def kmap (σ : Equiv.Perm (Fin n)) : KSet k n ≃ KSet k n where
  toFun S := ⟨S.1.map σ.toEmbedding, by rw [card_map]; exact S.2⟩
  invFun S := ⟨S.1.map σ.symm.toEmbedding, by rw [card_map]; exact S.2⟩
  left_inv S := by
    apply Subtype.ext
    ext x
    simp
  right_inv S := by
    apply Subtype.ext
    ext x
    simp

theorem relabel_apply (σ : Equiv.Perm (Fin n)) (M : Tensor k n) (S : KSet k n) :
    relabel σ M S = M (kmap σ.symm S) := rfl

theorem relabel_mul (σ σ' : Equiv.Perm (Fin n)) (M : Tensor k n) :
    relabel (σ * σ') M = relabel σ (relabel σ' M) := by
  funext S
  simp only [relabel, Finset.map_map]
  rfl

theorem relabel_one (M : Tensor k n) : relabel 1 M = M := by
  funext S
  simp only [relabel]
  congr
  exact Finset.map_refl

/-- Relabelling as an equivalence of tensors. -/
def relabelEquiv (σ : Equiv.Perm (Fin n)) : Tensor k n ≃ Tensor k n where
  toFun := relabel σ
  invFun := relabel σ⁻¹
  left_inv M := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv M := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

theorem relabel_injective (σ : Equiv.Perm (Fin n)) :
    Function.Injective (relabel (k := k) σ) :=
  (relabelEquiv σ).injective

theorem readAt_relabel (σ : Equiv.Perm (Fin n)) (M : Tensor k n) (S : Finset (Fin n)) :
    readAt (relabel σ M) (S.map σ.toEmbedding) = readAt M S := by
  unfold readAt
  by_cases hS : S.card = k
  · rw [dite_eq_left (by rwa [card_map]), dite_eq_left hS]
    simp only [relabel]
    congr 1
    apply Subtype.ext
    ext x
    simp
  · rw [dite_eq_right (by rwa [card_map]), dite_eq_right hS]

/-- The noise is invariant under relabelling. -/
theorem noiseMass_relabel (ε : ℝ) (σ : Equiv.Perm (Fin n)) (M M' : Tensor k n) :
    noiseMass ε (relabel σ M) (relabel σ M') = noiseMass ε M M' :=
  Equiv.prod_comp (kmap σ.symm) fun S ↦ if M' S = M S then 1 - ε / 2 else ε / 2

/-! ### The planted distribution on a tensor -/

/-- The mass of a tensor under the planted distribution: the fraction of the pairs
(sample, permutation) that produce it. -/
theorem planted_singleton (h : 2 * (k - 1) * ell k T n < n) (M : Tensor k n) :
    planted k T n {M} = (Fintype.card (Sample k T n) * n.factorial : ENNReal)⁻¹ *
      ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n),
        if relabel σ (encode h ω) = M then 1 else 0 := by
  unfold planted
  rw [dite_eq_left h, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Measure.dirac_apply, Set.indicator_apply]
  simp only [Set.mem_singleton_iff, Pi.one_apply]

/-- `BHJK25.RS.planted_singleton`, in real numbers. -/
theorem planted_singleton_toReal (h : 2 * (k - 1) * ell k T n < n) (M : Tensor k n) :
    (planted k T n {M}).toReal = ((Fintype.card (Sample k T n) * n.factorial : ℕ) : ℝ)⁻¹ *
      ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n),
        if relabel σ (encode h ω) = M then 1 else 0 := by
  rw [planted_singleton h, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [sum_boole, ← Nat.cast_sum, ← Nat.cast_mul, ENNReal.toReal_natCast]

end BHJK25.RS
