module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sudan's interpolation: the algebra

Here `F[X][Y]` is `Polynomial (Polynomial F)`: the outer variable is `Y`, the inner one `X`, and
`Q(x, y)` is `(Q.map (evalRingHom x)).eval y`.

* **Sudan's lemma** (`BHJK25.RS.Sudan.eval_eq_zero`): if `Q` has `(1, m - 1)`-weighted degree at
  most `W` and vanishes at `(x, p(x))` for more than `W` distinct `x`, where `deg p < m`, then
  `Q(X, p(X)) = 0`, since `Q(X, p(X))` has degree at most `W`.
* **Enough monomials** (`BHJK25.RS.Sudan.card_low`): with `W² > 2 n m` and `m ≥ 2`, there are more
  than `n` monomials `X^a Y^b` with `a, b ≤ W` and `a + (m - 1) b ≤ W`; the monomial `X^a Y^b` is
  numbered `k = b (W + 1) + a`.
* **A nonzero kernel vector** (`BHJK25.RS.Sudan.exists_kernel`): fewer rows than allowed columns
  leave a nonzero vector supported on the allowed columns and killed by every row.
-/

@[expose] public section

namespace BHJK25.RS.Sudan

open Polynomial

variable {F : Type*} [Field F]

/-- Evaluating `Q(X, p(X))` at `x` gives `Q(x, p(x))`. -/
theorem eval_eval (Q : F[X][X]) (p : F[X]) (x : F) :
    (Q.eval p).eval x = (Q.map (evalRingHom x)).eval (p.eval x) := by
  rw [eval_map, ← coe_evalRingHom, eval₂_hom]

/-- If `Q` has `(1, m - 1)`-weighted degree at most `W` and `deg p < m`, then `Q(X, p(X))` has
degree at most `W`. -/
theorem natDegree_eval_le {Q : F[X][X]} {m W : ℕ}
    (hQ : ∀ b a, (Q.coeff b).coeff a ≠ 0 → a + (m - 1) * b ≤ W) {p : F[X]}
    (hp : p.natDegree < m) : (Q.eval p).natDegree ≤ W := by
  rw [eval_eq_sum, Polynomial.sum]
  refine natDegree_sum_le_of_forall_le _ _ fun b hb ↦ ?_
  have hb' : Q.coeff b ≠ 0 := mem_support_iff.mp hb
  have h1 := hQ b _ (mt leadingCoeff_eq_zero.mp hb')
  have h2 : p.natDegree ≤ m - 1 := by omega
  calc (Q.coeff b * p ^ b).natDegree ≤ (Q.coeff b).natDegree + (p ^ b).natDegree :=
        natDegree_mul_le
    _ ≤ (Q.coeff b).natDegree + (m - 1) * b := by
        gcongr
        exact natDegree_pow_le.trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ h2)
    _ ≤ W := h1

/-- **Sudan's lemma.** If `Q` has `(1, m - 1)`-weighted degree at most `W`, `deg p < m`, and
`Q(x, p(x)) = 0` for more than `W` distinct `x`, then `Q(X, p(X)) = 0`. -/
theorem eval_eq_zero {Q : F[X][X]} {m W : ℕ}
    (hQ : ∀ b a, (Q.coeff b).coeff a ≠ 0 → a + (m - 1) * b ≤ W) {p : F[X]}
    (hp : p.natDegree < m) (S : Finset F)
    (hS : ∀ x ∈ S, (Q.map (evalRingHom x)).eval (p.eval x) = 0) (hcard : W < S.card) :
    Q.eval p = 0 := by
  exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
    (fun x hx ↦ by rw [eval_eval]; exact hS x hx)
    ((natDegree_eval_le hQ hp).trans_lt hcard)

namespace Aux

/-- Counting the numbers `k = b (W + 1) + a < (W + 1)²` with `a + c b ≤ W` block by block. -/
theorem card_filter_eq_sum (W c : ℕ) :
    ((Finset.range ((W + 1) * (W + 1))).filter
      fun k ↦ k % (W + 1) + c * (k / (W + 1)) ≤ W).card =
    ∑ b ∈ Finset.range (W + 1), (W + 1 - c * b) := by
  have e : ((Finset.range ((W + 1) * (W + 1))).filter
      fun k ↦ k % (W + 1) + c * (k / (W + 1)) ≤ W).card =
      ((Finset.range (W + 1) ×ˢ Finset.range (W + 1)).filter
        fun ab : ℕ × ℕ ↦ ab.1 + c * ab.2 ≤ W).card := by
    apply Finset.card_nbij' (fun k ↦ (k % (W + 1), k / (W + 1)))
      (fun ab ↦ ab.2 * (W + 1) + ab.1)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq,
        Finset.mem_product] at hk ⊢
      refine ⟨⟨Nat.mod_lt _ (Nat.succ_pos W), ?_⟩, hk.2⟩
      exact Nat.div_lt_of_lt_mul hk.1
    · intro ab hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq,
        Finset.mem_product] at hab ⊢
      obtain ⟨⟨ha, hb⟩, hle⟩ := hab
      have hmod : (ab.2 * (W + 1) + ab.1) % (W + 1) = ab.1 := by
        rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
      have hdiv : (ab.2 * (W + 1) + ab.1) / (W + 1) = ab.2 := by
        rw [add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos W), Nat.div_eq_of_lt ha, zero_add]
      refine ⟨?_, by rw [hmod, hdiv]; exact hle⟩
      calc ab.2 * (W + 1) + ab.1 < ab.2 * (W + 1) + (W + 1) := by omega
        _ = (ab.2 + 1) * (W + 1) := by ring
        _ ≤ (W + 1) * (W + 1) := Nat.mul_le_mul_right _ hb
    · intro k _
      simp only
      rw [mul_comm, Nat.div_add_mod]
    · intro ab hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq,
        Finset.mem_product] at hab
      have ha := hab.1.1
      ext
      · simp only
        rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
      · simp only
        rw [add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos W), Nat.div_eq_of_lt ha, zero_add]
  rw [e, Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.card_filter]
  have : (Finset.range (W + 1)).filter (fun a ↦ a + c * b ≤ W) =
      Finset.range (W + 1 - c * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- Pairing `b` with `B - b`: if `c B ≤ W`, then `2 ∑_{b ≤ B} (W + 1 - c b) ≥ (B + 1)(W + 2)`. -/
theorem two_mul_sum_ge (W c B : ℕ) (hB : c * B ≤ W) :
    (B + 1) * (W + 2) ≤ 2 * ∑ b ∈ Finset.range (B + 1), (W + 1 - c * b) := by
  have h := Finset.sum_range_reflect (fun b ↦ W + 1 - c * b) (B + 1)
  rw [two_mul]
  nth_rewrite 1 [← h]
  rw [← Finset.sum_add_distrib]
  have : ∑ _b ∈ Finset.range (B + 1), (W + 2) = (B + 1) * (W + 2) := by simp
  rw [← this]
  apply Finset.sum_le_sum
  intro b hb
  have hb' : b ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h1 : c * b ≤ c * B := Nat.mul_le_mul_left c hb'
  have h2 : c * (B + 1 - 1 - b) = c * B - c * b := by rw [Nat.add_sub_cancel, Nat.mul_sub]
  omega

end Aux

/-- **Enough monomials.** If `m ≥ 2` and `W² > 2 n m`, more than `n` of the numbers
`k = b (W + 1) + a < (W + 1)²` (with `a = k % (W + 1)`, `b = k / (W + 1)`) have
`a + (m - 1) b ≤ W`. -/
theorem card_low {n m W : ℕ} (hm : 2 ≤ m) (hW : 2 * n * m < W * W) :
    n < ((Finset.range ((W + 1) * (W + 1))).filter
      fun k ↦ k % (W + 1) + (m - 1) * (k / (W + 1)) ≤ W).card := by
  rw [Aux.card_filter_eq_sum]
  set c := m - 1 with hc
  have hc1 : 0 < c := by omega
  set B := W / c with hBdef
  have hBW : c * B ≤ W := by rw [mul_comm]; exact Nat.div_mul_le_self W c
  have hB : W + 1 ≤ (B + 1) * c := by
    have := Nat.lt_div_mul_add (a := W) hc1
    rw [← hBdef] at this
    rw [add_mul, one_mul]
    omega
  have hBle : B + 1 ≤ W + 1 := by
    have := Nat.div_le_self W c
    omega
  set S := ∑ b ∈ Finset.range (W + 1), (W + 1 - c * b) with hSdef
  have hS : (B + 1) * (W + 2) ≤ 2 * S :=
    (Aux.two_mul_sum_ge W c B hBW).trans (Nat.mul_le_mul_left 2
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hBle)))
  have h1 : (W + 1) * (W + 2) ≤ 2 * S * c :=
    calc (W + 1) * (W + 2) ≤ (B + 1) * c * (W + 2) := Nat.mul_le_mul_right _ hB
      _ = (B + 1) * (W + 2) * c := by ring
      _ ≤ 2 * S * c := Nat.mul_le_mul_right _ hS
  have h2 : W * W < (W + 1) * (W + 2) :=
    Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)
  have h3 : 2 * n * c ≤ 2 * n * m := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * n * c < 2 * S * c := by omega
  have h5 := Nat.lt_of_mul_lt_mul_right h4
  omega

/-- **A nonzero kernel vector.** If there are fewer rows than allowed columns `k < K`, some
vector supported on the allowed columns, nonzero on `[0, K)`, is killed by every row. -/
theorem exists_kernel {K : ℕ} (low : ℕ → Prop) [DecidablePred low] (rows : List (ℕ → F))
    (h : rows.length < ((Finset.range K).filter low).card) :
    ∃ v : ℕ → F, (∀ k < K, ¬ low k → v k = 0) ∧ (∃ k < K, v k ≠ 0) ∧
      ∀ a ∈ rows, ∑ k ∈ Finset.range K, a k * v k = 0 := by
  set s := (Finset.range K).filter low with hs
  let col : s → Fin rows.length → F := fun k i ↦ rows[i] k
  have hdep : ¬ LinearIndependent F col := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_coe, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨fun k ↦ if hk : k ∈ s then g ⟨k, hk⟩ else 0, ?_, ?_, ?_⟩
  · intro k _ hlow
    have hk : k ∉ s := by simp [hs, hlow]
    simp [hk]
  · refine ⟨i₀.1, (Finset.mem_range.mp (Finset.mem_filter.mp i₀.2).1), ?_⟩
    simpa [i₀.2] using hi₀
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    have hi := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, col] at hi
    rw [← Finset.sum_subset (Finset.filter_subset low (Finset.range K))]
    · rw [← Finset.sum_coe_sort s]
      simpa [mul_comm] using hi
    · intro k _ hk
      have hk' : k ∉ s := hk
      simp [hk']

end BHJK25.RS.Sudan
