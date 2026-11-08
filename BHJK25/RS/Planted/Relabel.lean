module

public import BHJK25.RS.Basic.Relabel

/-!
# Acceptance and the noise commute with relabelling

Relabelling the vertices of a tensor by `σ` and the vertices of a guess by `σ` maps cells to
cells, so a tensor accepted with the guess `g` is accepted, after relabelling, with the relabelled
guess; and the noise turns `relabel σ M` into `relabel σ M'` with the probability with which it
turns `M` into `M'` (`BHJK25.RS.noiseMass_relabel`). Hence the probability that a noisy planted
tensor is accepted is at least the average, over the samples `ω`, of the probability that the
noisy (unrelabelled) planted tensor `encode ω` is accepted.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open MeasureTheory Finset

variable {k T n : ℕ}

/-! ### The noise -/

theorem noiseMass_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) (M M' : Tensor k n) :
    0 ≤ noiseMass ε M M' :=
  prod_nonneg fun _ _ ↦ by split_ifs <;> linarith

/-! ### Acceptance is preserved by relabelling -/

/-- The guess `g` with its vertices relabelled by `σ`. -/
def relabelGuess (σ : Equiv.Perm (Fin n)) (g : Guess k T n) : Guess k T n :=
  fun s b t ↦ σ (g s b t)

theorem cell_relabelGuess (σ : Equiv.Perm (Fin n)) (g : Guess k T n) (s : Fin 2) (v : Fin n)
    (i : ℕ) : cell (relabelGuess σ g) s (σ v) i = (cell g s v i).map σ.toEmbedding := by
  ext x
  simp only [cell, relabelGuess, mem_insert, mem_image, mem_univ, true_and, mem_map_equiv]
  constructor
  · rintro (rfl | ⟨b, rfl⟩)
    · exact Or.inl (σ.symm_apply_apply v)
    · exact Or.inr ⟨b, (σ.symm_apply_apply _).symm⟩
  · rintro (h | ⟨b, h⟩)
    · exact Or.inl (σ.symm_apply_eq.1 h)
    · exact Or.inr ⟨b, (σ.eq_symm_apply.1 h)⟩

theorem readElt_relabel (σ : Equiv.Perm (Fin n)) (g : Guess k T n) (s : Fin 2) (M : Tensor k n)
    (v : Fin n) : readElt (relabelGuess σ g) s (relabel σ M) (σ v) = readElt g s M v := by
  unfold readElt
  congr 1
  funext i
  rw [cell_relabelGuess, readAt_relabel]

theorem isCol_relabelGuess (σ : Equiv.Perm (Fin n)) (g : Guess k T n) (v : Fin n) :
    IsCol (relabelGuess σ g) (σ v) ↔ IsCol g v := by
  simp only [IsCol, relabelGuess, ne_eq, EmbeddingLike.apply_eq_iff_eq]

theorem agreeSet_subset (σ : Equiv.Perm (Fin n)) (g : Guess k T n) (M : Tensor k n)
    (p : Polynomial (Fld T n)) :
    agreeSet g M p ⊆ agreeSet (relabelGuess σ g) (relabel σ M) p := by
  intro x hx
  simp only [agreeSet, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨v, hv, h0, h1⟩ := hx
  exact ⟨σ v, (isCol_relabelGuess σ g v).2 hv, (readElt_relabel σ g 0 M v).trans h0,
    (readElt_relabel σ g 1 M v).trans h1⟩

/-- A relabelled accepted tensor is accepted. -/
theorem accept_relabel (σ : Equiv.Perm (Fin n)) {M : Tensor k n} (h : Accept k T n M) :
    Accept k T n (relabel σ M) := by
  obtain ⟨g, hg, p, hp, hcard⟩ := h
  exact ⟨relabelGuess σ g, σ.injective.comp hg, p, hp,
    hcard.trans (card_le_card (agreeSet_subset σ g M p))⟩

/-! ### The noisy planted distribution -/

/-- The probability that a noisy planted tensor satisfies `E`, as an average over the samples
and the permutations. -/
theorem noisyProb_planted (h : 2 * (k - 1) * ell k T n < n) (ε : ℝ) (E : Tensor k n → Prop)
    [DecidablePred E] :
    noisyProb ε (planted k T n) E =
      ((Fintype.card (Sample k T n) * n.factorial : ℕ) : ℝ)⁻¹ *
        ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n),
          ∑ M', if E M' then noiseMass ε (relabel σ (encode h ω)) M' else 0 := by
  classical
  set G : Tensor k n → ℝ := fun M ↦ ∑ M', if E M' then noiseMass ε M M' else 0 with hG
  have h1 : noisyProb ε (planted k T n) E = ∑ M, (planted k T n {M}).toReal * G M := by
    unfold noisyProb
    refine sum_congr rfl fun M _ ↦ ?_
    rw [hG, mul_sum]
    refine sum_congr rfl fun M' _ ↦ ?_
    split_ifs <;> simp
  rw [h1]
  simp_rw [planted_singleton_toReal h, mul_assoc, ← mul_sum]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun σ _ ↦ ?_
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq univ (relabel σ (encode h ω)) G, ite_eq_left (mem_univ _)]

/-- Relabelling the planted tensor does not decrease the probability that the noisy tensor is
accepted. -/
theorem sum_accept_le_relabel {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) (σ : Equiv.Perm (Fin n))
    (X : Tensor k n) [DecidablePred (Accept k T n)] :
    ∑ M', (if Accept k T n M' then noiseMass ε X M' else 0) ≤
      ∑ M', (if Accept k T n M' then noiseMass ε (relabel σ X) M' else 0) := by
  rw [← Equiv.sum_comp (relabelEquiv σ)
    (fun M' ↦ if Accept k T n M' then noiseMass ε (relabel σ X) M' else 0)]
  refine sum_le_sum fun M' _ ↦ ?_
  simp only [relabelEquiv, Equiv.coe_fn_mk, noiseMass_relabel]
  by_cases hA : Accept k T n M'
  · rw [ite_eq_left hA, ite_eq_left (accept_relabel σ hA)]
  · rw [ite_eq_right hA]
    split_ifs
    · exact noiseMass_nonneg hε0 hε2 _ _
    · exact le_rfl

/-- **Dropping the relabelling**: the noisy planted tensor is accepted with probability at least
the average over the samples `ω` of the probability that the noisy `encode ω` is accepted. -/
theorem le_noisyProb_planted (h : 2 * (k - 1) * ell k T n < n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε2 : ε ≤ 2) [DecidablePred (Accept k T n)] :
    (Fintype.card (Sample k T n) : ℝ)⁻¹ * ∑ ω : Sample k T n,
        ∑ M', (if Accept k T n M' then noiseMass ε (encode h ω) M' else 0) ≤
      noisyProb ε (planted k T n) (fun M ↦ Accept k T n M) := by
  rw [noisyProb_planted h]
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = n.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  calc (Fintype.card (Sample k T n) : ℝ)⁻¹ * ∑ ω : Sample k T n,
        ∑ M', (if Accept k T n M' then noiseMass ε (encode h ω) M' else 0)
      = ((Fintype.card (Sample k T n) * n.factorial : ℕ) : ℝ)⁻¹ * ∑ ω : Sample k T n,
          ∑ _σ : Equiv.Perm (Fin n),
            ∑ M', (if Accept k T n M' then noiseMass ε (encode h ω) M' else 0) := by
        simp_rw [sum_const, card_univ, nsmul_eq_mul, hcard, ← mul_sum]
        push_cast
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun ω _ ↦ sum_le_sum fun σ _ ↦
        sum_accept_le_relabel hε0 hε2 σ _) (by positivity)

end BHJK25.RS.PlantedAux
