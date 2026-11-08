module

public import BHJK25.RS.Defs

/-!
# Uniformity from flips

A counting lemma behind the `m`-wise uniformity of the planted distribution [BHJK25, Lemma 2.10].
Let `Ψ : Ω → (ι → Bool)` be a map from a finite set. If, for every nonempty set `A` of at most `m`
coordinates, some coordinate `S ∈ A` can be flipped by an injective map of `Ω` that keeps the
other coordinates in `A`, then every set `A` of at most `m` coordinates is all `true` on exactly a
`2^(-|A|)` fraction of `Ω` (`BHJK25.RS.ConsAux.card_ones`). By induction on `|A|`: the flip maps
the points that are all `true` on `A` injectively to those that are all `true` on `A \ {S}` and
`false` at `S`, and back, so these two sets have the same size.
-/

@[expose] public section

namespace BHJK25.RS.ConsAux

/-- If some coordinate of every nonempty set `A` of at most `m` coordinates can be flipped by an
injective map that keeps the others in `A`, every such `A` is all `true` on a `2^(-|A|)` fraction
of `Ω`. -/
theorem card_ones {Ω ι : Type*} [Fintype Ω] (Ψ : Ω → ι → Bool) (m : ℕ)
    (hflip : ∀ A : Finset ι, A.Nonempty → A.card ≤ m → ∃ S ∈ A, ∃ τ : Ω → Ω,
      Function.Injective τ ∧ ∀ ω, Ψ (τ ω) S = !Ψ ω S ∧ ∀ S' ∈ A, S' ≠ S → Ψ (τ ω) S' = Ψ ω S')
    (A : Finset ι) (hA : A.card ≤ m) :
    (Finset.univ.filter fun ω ↦ ∀ S ∈ A, Ψ ω S = true).card * 2 ^ A.card = Fintype.card Ω := by
  classical
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨S, hS, τ, hτ, hτS⟩ := hflip A hne hA
    have hcard : (A.erase S).card + 1 = A.card := Finset.card_erase_add_one hS
    have ih' := ih (A.erase S) (Finset.erase_ssubset hS) (by omega)
    set F := Finset.univ.filter fun ω ↦ ∀ S' ∈ A.erase S, Ψ ω S' = true with hF
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun ω ↦ Ψ ω S = true)
    have hA_eq : F.filter (fun ω ↦ Ψ ω S = true) =
        Finset.univ.filter fun ω ↦ ∀ S' ∈ A, Ψ ω S' = true := by
      ext ω
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩ S' hS'
        by_cases hSS : S' = S
        · rw [hSS]
          exact h2
        · exact h1 S' (Finset.mem_erase.2 ⟨hSS, hS'⟩)
      · intro h1
        exact ⟨fun S' hS' ↦ h1 S' (Finset.mem_of_mem_erase hS'), h1 S hS⟩
    have hkeep : ∀ ω ∈ F, τ ω ∈ F := by
      intro ω hω
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      intro S' hS'
      rw [(hτS ω).2 S' (Finset.mem_of_mem_erase hS') (Finset.ne_of_mem_erase hS')]
      exact hω S' hS'
    have hle1 : (F.filter fun ω ↦ Ψ ω S = true).card ≤
        (F.filter fun ω ↦ ¬Ψ ω S = true).card := by
      refine Finset.card_le_card_of_injOn τ (fun ω hω ↦ ?_) hτ.injOn
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hω ⊢
      refine ⟨hkeep ω hω.1, ?_⟩
      rw [(hτS ω).1, hω.2]
      decide
    have hle2 : (F.filter fun ω ↦ ¬Ψ ω S = true).card ≤
        (F.filter fun ω ↦ Ψ ω S = true).card := by
      refine Finset.card_le_card_of_injOn τ (fun ω hω ↦ ?_) hτ.injOn
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hω ⊢
      refine ⟨hkeep ω hω.1, ?_⟩
      rw [(hτS ω).1, Bool.eq_false_iff.2 hω.2]
      rfl
    rw [← hA_eq, ← hcard, pow_succ, ← ih', ← hsplit, le_antisymm hle2 hle1]
    ring

end BHJK25.RS.ConsAux
