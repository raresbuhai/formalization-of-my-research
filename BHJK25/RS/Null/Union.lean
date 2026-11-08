module

public import BHJK25.RS.Null.Count

/-!
# The union bound

An accepted tensor has a valid guess `g`, the coefficients `c ∈ F^m` of a polynomial of degree
`< m`, and a set `J` of `W + 1` columns of `g` with `β_v = Σ cᵢ α_vⁱ` for every `v ∈ J` (one column
for each of `W + 1` agreeing values). There are at most `n^{2(k-1)ℓ}` guesses, `q^m` coefficient
vectors and `C(n, W + 1) ≤ n^{W+1}` sets `J`, and each triple has probability `q^{-(W+1)}`
(`BHJK25.RS.NullAux.card_prescribed`), so a uniformly random tensor is accepted with probability
at most `n^{2(k-1)ℓ} q^m n^{W+1} / q^{W+1}`.
-/

@[expose] public section

namespace BHJK25.RS.NullAux

open Finset

variable {k T n : ℕ}

/-- The polynomial with coefficients `c` evaluated at `x`: `Σ cᵢ xⁱ`. -/
def evalCoeffs {F : Type} [CommRing F] {m : ℕ} (c : Fin m → F) (x : F) : F :=
  ∑ i, c i * x ^ (i : ℕ)

/-- An accepted tensor has a valid guess, a coefficient vector and a set of `W + 1` columns with
`β_v = Σ cᵢ α_vⁱ`. -/
theorem exists_of_accept {M : Tensor k n} (h : Accept k T n M) :
    ∃ g : Guess k T n, g.Valid ∧ ∃ c : Fin (mdeg T n) → Fld T n, ∃ J : Finset (Fin n),
      J.card = thr T n ∧ (∀ v ∈ J, IsCol g v) ∧
        ∀ v ∈ J, readElt g 1 M v = evalCoeffs c (readElt g 0 M v) := by
  classical
  obtain ⟨g, hg, p, hp, hA⟩ := h
  refine ⟨g, hg, fun i ↦ p.coeff i, ?_⟩
  set J' := univ.filter fun v ↦ IsCol g v ∧ readElt g 1 M v = p.eval (readElt g 0 M v)
  have hsub : agreeSet g M p ⊆ J'.image (readElt g 0 M) := by
    intro x hx
    simp only [agreeSet, mem_filter, mem_univ, true_and] at hx
    obtain ⟨v, hv, rfl, h1⟩ := hx
    exact mem_image.2 ⟨v, mem_filter.2 ⟨mem_univ _, hv, h1⟩, rfl⟩
  have hc1 : (agreeSet g M p).card ≤ (J'.image (readElt g 0 M)).card := card_le_card hsub
  have hc2 : (J'.image (readElt g 0 M)).card ≤ J'.card := card_image_le
  have hcard : thr T n ≤ J'.card := le_trans hA (le_trans hc1 hc2)
  obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq hcard
  refine ⟨J, hJc, fun v hv ↦ (mem_filter.1 (hJ hv)).2.1, fun v hv ↦ ?_⟩
  rw [(mem_filter.1 (hJ hv)).2.2, Polynomial.eval_eq_sum_range' hp, evalCoeffs,
    Fin.sum_univ_eq_sum_range (fun i ↦ p.coeff i * readElt g 0 M v ^ i)]

/-- There are `n^{2(k-1)ℓ}` guesses. -/
theorem card_guess : Fintype.card (Guess k T n) = n ^ (2 * (k - 1) * ell k T n) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  ring_nf

/-- **The union bound**, counting: accepted tensors, times `q^{W+1}`, are at most
`n^{2(k-1)ℓ} q^m C(n, W + 1)` times all tensors. -/
theorem card_accept_mul_le (hk : 2 ≤ k) [DecidablePred fun M : Tensor k n ↦ Accept k T n M] :
    (univ.filter fun M : Tensor k n ↦ Accept k T n M).card * 2 ^ (rbits T n * thr T n) ≤
      n ^ (2 * (k - 1) * ell k T n) * (2 ^ rbits T n) ^ mdeg T n * n.choose (thr T n) *
        2 ^ Fintype.card (KSet k n) := by
  classical
  set t := thr T n
  set r := rbits T n
  set N := Fintype.card (KSet k n)
  set V := univ.filter fun g : Guess k T n ↦ g.Valid
  set S : Guess k T n → Finset (Finset (Fin n)) := fun g ↦
    (powersetCard t (univ : Finset (Fin n))).filter fun J ↦ ∀ v ∈ J, IsCol g v
  set E : Guess k T n → (Fin (mdeg T n) → Fld T n) → Finset (Fin n) → Finset (Tensor k n) :=
    fun g c J ↦ univ.filter fun M : Tensor k n ↦
      ∀ v ∈ J, readElt g 1 M v = evalCoeffs c (readElt g 0 M v)
  have hsub : (univ.filter fun M : Tensor k n ↦ Accept k T n M) ⊆
      V.biUnion fun g ↦ (univ : Finset (Fin (mdeg T n) → Fld T n)).biUnion fun c ↦
        (S g).biUnion fun J ↦ E g c J := by
    intro M hM
    obtain ⟨g, hg, c, J, hJc, hJ, hE⟩ := exists_of_accept (mem_filter.1 hM).2
    simp only [mem_biUnion]
    exact ⟨g, mem_filter.2 ⟨mem_univ _, hg⟩, c, mem_univ _, J,
      mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hJc⟩, hJ⟩,
      mem_filter.2 ⟨mem_univ _, hE⟩⟩
  have hE : ∀ g ∈ V, ∀ c, ∀ J ∈ S g, (E g c J).card * 2 ^ (r * t) = 2 ^ N := by
    intro g hg c J hJ
    obtain ⟨hJ1, hJ2⟩ := mem_filter.1 hJ
    have hJc : J.card = t := (mem_powersetCard.1 hJ1).2
    have h := card_prescribed hk (mem_filter.1 hg).2 J hJ2 (evalCoeffs c)
    rw [Fintype.card_subtype, hJc] at h
    exact h
  have hS : ∀ g, (S g).card ≤ n.choose t := fun g ↦
    (card_filter_le _ _).trans (by rw [card_powersetCard, card_univ, Fintype.card_fin])
  have hV : V.card ≤ n ^ (2 * (k - 1) * ell k T n) :=
    (card_filter_le _ _).trans (by rw [card_univ, card_guess])
  have hC : (univ : Finset (Fin (mdeg T n) → Fld T n)).card = (2 ^ r) ^ mdeg T n := by
    rw [card_univ, Fintype.card_fun, card_fld, Fintype.card_fin]
  have h1 : (univ.filter fun M : Tensor k n ↦ Accept k T n M).card ≤
      ∑ g ∈ V, ∑ c, ∑ J ∈ S g, (E g c J).card :=
    (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun g _ ↦
      card_biUnion_le.trans (sum_le_sum fun c _ ↦ card_biUnion_le)))
  have h2 : (∑ g ∈ V, ∑ c, ∑ J ∈ S g, (E g c J).card) * 2 ^ (r * t) ≤
      ∑ _g ∈ V, ∑ _c : Fin (mdeg T n) → Fld T n, n.choose t * 2 ^ N := by
    rw [sum_mul]
    refine sum_le_sum fun g hg ↦ ?_
    rw [sum_mul]
    refine sum_le_sum fun c _ ↦ ?_
    rw [sum_mul, sum_congr rfl fun J hJ ↦ hE g hg c J hJ, sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hS g)
  have h3 : ∑ _g ∈ V, ∑ _c : Fin (mdeg T n) → Fld T n, n.choose t * 2 ^ N =
      V.card * (2 ^ r) ^ mdeg T n * n.choose t * 2 ^ N := by
    rw [sum_const, sum_const, hC, smul_eq_mul, smul_eq_mul]
    ring
  calc _ ≤ (∑ g ∈ V, ∑ c, ∑ J ∈ S g, (E g c J).card) * 2 ^ (r * t) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_right _ hV

/-- **The union bound**: a uniformly random tensor is accepted with probability at most
`n^{2(k-1)ℓ} q^m n^{W+1} / q^{W+1}`. -/
theorem uniformProb_accept_le (hk : 2 ≤ k) :
    uniformProb k n (fun M ↦ Accept k T n M) ≤
      (n : ℝ) ^ (2 * (k - 1) * ell k T n) * ((2 : ℝ) ^ rbits T n) ^ mdeg T n *
        (n : ℝ) ^ thr T n / ((2 : ℝ) ^ rbits T n) ^ thr T n := by
  classical
  unfold uniformProb
  rw [Fintype.card_subtype]
  have h := card_accept_mul_le (T := T) (n := n) hk
  have hN : (0 : ℝ) < 2 ^ Fintype.card (KSet k n) := by positivity
  have hq : (0 : ℝ) < ((2 : ℝ) ^ rbits T n) ^ thr T n := by positivity
  have hch : ((n.choose (thr T n) : ℕ) : ℝ) ≤ (n : ℝ) ^ thr T n := by
    exact_mod_cast Nat.choose_le_pow n (thr T n)
  have hR : ((univ.filter fun M : Tensor k n ↦ Accept k T n M).card : ℝ) *
      ((2 : ℝ) ^ rbits T n) ^ thr T n ≤
      (n : ℝ) ^ (2 * (k - 1) * ell k T n) * ((2 : ℝ) ^ rbits T n) ^ mdeg T n *
        (n.choose (thr T n) : ℝ) * 2 ^ Fintype.card (KSet k n) := by
    rw [← pow_mul]
    exact_mod_cast h
  rw [div_le_div_iff₀ hN hq]
  calc _ ≤ (n : ℝ) ^ (2 * (k - 1) * ell k T n) * ((2 : ℝ) ^ rbits T n) ^ mdeg T n *
        (n.choose (thr T n) : ℝ) * 2 ^ Fintype.card (KSet k n) := hR
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hN.le
        apply mul_le_mul_of_nonneg_left hch
        positivity

end BHJK25.RS.NullAux
