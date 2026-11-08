module

public import BHJK25.RS.Construction.Flip
public import BHJK25.RS.Construction.Count
public import BHJK25.RS.Construction.Measure
public import BHJK25.RS.Basic.Relabel

/-!
# `m`-wise uniformity of the planted distribution

[BHJK25, Lemma 2.10]: every set `A` of at most `m` entries of a planted tensor is all ones with
probability `2^(-|A|)`, as for a uniform tensor (`BHJK25.RS.ConsAux.planted_ones`,
`BHJK25.RS.ConsAux.uniform_ones`): for each relabelling, the entries at `A` are those of the
unrelabelled tensor at another set of `|A|` entries, where the flips of
`BHJK25.RS.ConsAux.exists_flip` apply. At points with coordinates `0` and `1`, a monomial is the
indicator that the entries in its support are all ones, so the averages of a polynomial of degree
at most `m` under the two distributions agree (`BHJK25.RS.ConsAux.avg_eval`).
-/

@[expose] public section

namespace BHJK25.RS.ConsAux

open MeasureTheory

variable {k T n : ℕ}

/-- For each relabelling, every set of at most `m` entries of the planted tensor is all ones for
a `2^(-|A|)` fraction of the samples. -/
theorem card_ones_relabel (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n)
    (σ : Equiv.Perm (Fin n)) (A : Finset (KSet k n)) (hA : A.card ≤ mdeg T n) :
    (Finset.univ.filter fun ω : Sample k T n ↦ ∀ S ∈ A, relabel σ (encode h ω) S = true).card *
      2 ^ A.card = Fintype.card (Sample k T n) := by
  classical
  convert card_ones (fun ω ↦ relabel σ (encode h ω)) (mdeg T n) (fun B hB hBm ↦ ?_) A hA
  set ρ := kmap (k := k) σ.symm
  obtain ⟨S₀, hS₀, τ, hτ, hτS⟩ :=
    exists_flip hk h (B.image ρ) (hB.image ρ) (Finset.card_image_le.trans hBm)
  obtain ⟨S, hSB, rfl⟩ := Finset.mem_image.1 hS₀
  refine ⟨S, hSB, τ, hτ, fun ω ↦ ⟨?_, fun S' hS' hne ↦ ?_⟩⟩
  · simp only [relabel_apply]
    exact (hτS ω).1
  · simp only [relabel_apply]
    exact (hτS ω).2 (ρ S') (Finset.mem_image_of_mem ρ hS') (ρ.injective.ne hne)

theorem planted_ones (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (A : Finset (KSet k n))
    (hA : A.card ≤ mdeg T n) :
    ((Fintype.card (Sample k T n) : ℝ) * n.factorial)⁻¹ *
      ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n),
        (if ∀ S ∈ A, relabel σ (encode h ω) S = true then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ A.card)⁻¹ := by
  rw [Finset.sum_comm]
  have hσ (σ : Equiv.Perm (Fin n)) : ∑ ω : Sample k T n,
      (if ∀ S ∈ A, relabel σ (encode h ω) S = true then (1 : ℝ) else 0) =
        (Fintype.card (Sample k T n) : ℝ) / 2 ^ A.card := by
    rw [Finset.sum_boole, eq_div_iff (by positivity)]
    exact_mod_cast card_ones_relabel hk h σ A hA
  simp_rw [hσ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have h1 : (Fintype.card (Sample k T n) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  field_simp

theorem uniform_ones (A : Finset (KSet k n)) :
    ((2 : ℝ) ^ Fintype.card (KSet k n))⁻¹ *
      ∑ M : Tensor k n, (if ∀ S ∈ A, M S = true then (1 : ℝ) else 0) = ((2 : ℝ) ^ A.card)⁻¹ := by
  have hc := card_ones (fun M : Tensor k n ↦ M) A.card (fun B hB _ ↦ ?_) A le_rfl
  · rw [Finset.sum_boole]
    rw [card_tensor] at hc
    have hc' : ((Finset.univ.filter fun M : Tensor k n ↦ ∀ S ∈ A, M S = true).card : ℝ) *
        2 ^ A.card = 2 ^ Fintype.card (KSet k n) := by
      have h1 := congrArg (Nat.cast (R := ℝ)) hc
      push_cast at h1
      convert h1
    have hX : ((Finset.univ.filter fun M : Tensor k n ↦ ∀ S ∈ A, M S = true).card : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hc'
      exact (pow_ne_zero _ two_ne_zero) hc'.symm
    rw [← hc']
    field_simp
  · classical
    obtain ⟨S, hS⟩ := hB
    refine ⟨S, hS, fun M ↦ Function.update M S (!M S), fun M M' hM ↦ ?_, fun M ↦ ⟨?_, ?_⟩⟩
    · have h1 := congrArg (fun X : Tensor k n ↦ Function.update X S (!X S)) hM
      simpa only [Function.update_self, Function.update_idem, Bool.not_not,
        Function.update_eq_self] using h1
    · simp only [Function.update_self]
    · intro S' _ hne
      simp only [Function.update_of_ne hne]

theorem prod_entryBits (M : Tensor k n) (d : KSet k n →₀ ℕ) :
    ∏ S ∈ d.support, entryBits M S ^ d S = if ∀ S ∈ d.support, M S = true then 1 else 0 := by
  split_ifs with hall
  · refine Finset.prod_eq_one fun S hS ↦ ?_
    simp [entryBits, hall S hS]
  · simp only [not_forall] at hall
    obtain ⟨S, hS, hMS⟩ := hall
    refine Finset.prod_eq_zero hS ?_
    have hd : d S ≠ 0 := Finsupp.mem_support_iff.1 hS
    simp [entryBits, hMS, hd]

theorem card_support_le (d : KSet k n →₀ ℕ) : d.support.card ≤ d.sum fun _ e ↦ e := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun S hS ↦ Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hS)

/-- If every set of at most `m` entries is all ones with weight `2^(-|A|)`, every polynomial of
degree at most `m` has the average it has under the uniform distribution. -/
theorem avg_eval {Ω : Type*} [Fintype Ω] (Y : Ω → Tensor k n) (w : ℝ) (m : ℕ)
    (hY : ∀ A : Finset (KSet k n), A.card ≤ m →
      w * ∑ x, (if ∀ S ∈ A, Y x S = true then (1 : ℝ) else 0) = ((2 : ℝ) ^ A.card)⁻¹)
    (f : MvPolynomial (KSet k n) ℝ) (hf : f.totalDegree ≤ m) :
    w * ∑ x, MvPolynomial.eval (entryBits (Y x)) f =
      ∑ d ∈ f.support, f.coeff d * ((2 : ℝ) ^ d.support.card)⁻¹ := by
  simp_rw [MvPolynomial.eval_eq, prod_entryBits]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [← Finset.mul_sum, mul_left_comm,
    hY d.support ((card_support_le d).trans ((MvPolynomial.le_totalDegree hd).trans hf))]

end BHJK25.RS.ConsAux
