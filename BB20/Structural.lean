module

public import BB20.Model
public import BB20.Structural.Pigeonhole

/-!
# Theorem 4 (in the form of Lemma 10)

[BB20, Theorem 4 / Lemma 10]: if `I` is a set of MRF neighbours of `u`, and `u`, `I`, `S` are
disjoint, then some `I' ⊆ I` with `|I'| ≤ 2^s` satisfies
`ν_{u,I'|S} ≥ (4|I|)^{-2^s} (1/|I|)^{2^s (2^s + 1)} ν_{u,I|S}`.

The proof is in `BB20/Structural/`:

* `Latent.lean`: the marginals of the observed variables as mixtures over the latent variables
  [BB20, Lemmas 13 and 14];
* `NonCancel.lean`: non-cancellation of sums of products of numbers in `[-1, 1]`
  [BB20, Lemmas 16 and 8];
* `Pattern.lean`: the term of one configuration in `ν_{u,I|S}` as such a sum, with at most `2^s`
  rows, and the bound for one configuration [BB20, Lemmas 15, 7 and 9];
* `Pigeonhole.lean`: from one configuration to `ν_{u,I|S}` [BB20, Lemma 10].
-/

@[expose] public section

namespace BB20.Structural

/-- **Theorem 4** of [BB20], in the form of Lemma 10. -/
theorem nuSubsetBound {n m : ℕ} (R : RBM n m) (s : ℕ) (hs : R.SparsityLE s) (u : Fin n)
    (I S : Finset (Fin n)) (hI : I ⊆ R.nbhd u) (hu : u ∉ S) (hIS : Disjoint I S) :
    ∃ I' ⊆ I, I'.card ≤ 2 ^ s ∧
      R.nu u I S / ((4 * I.card : ℝ) ^ 2 ^ s * (I.card : ℝ) ^ (2 ^ s * (2 ^ s + 1))) ≤
        R.nu u I' S :=
  exists_subset_nu_ge R s hs u I S hI hu hIS

end BB20.Structural
