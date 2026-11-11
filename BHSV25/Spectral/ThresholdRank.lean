module

public import BHSV25.Spectral.GraphFacts

/-!
# Large bottom threshold rank implies large top threshold rank

[BHSV25, Theorem 4.1] (Theorem 1.7 of the introduction): for a symmetric matrix `A` with
nonnegative entries and eigenvalues in `[-1, 1]`, all `τ ≥ 0` and `τ' < τ²`,
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`
(`BHSV25.Spectral.thresholdRank`), and the same for the normalized adjacency matrix of every graph
(`BHSV25.Spectral.thresholdRank_graph`). In the parameters of Theorem 4.1, `λ ≥ 0` and
`σ ∈ (0, 1)`: `σ² · #{eigenvalues ≤ -λ} ≤ #{eigenvalues ≥ (λ² - σ) / (1 - σ)}`
(`BHSV25.Spectral.thresholdRank_sigma`). For `λ < 1` this is `τ = λ` and
`τ' = (λ² - σ) / (1 - σ)`, with `(τ² - τ') / (1 - τ') = σ`; for `λ = 1` the threshold is `1`, and
`τ'` between `1` and the largest eigenvalue below `1` counts the same eigenvalues; for `λ > 1` no
eigenvalue is at most `-λ`.

The proof is that of the paper, written with families of vectors instead of matrices. A positive
semidefinite matrix `M` is given as a Gram matrix `M_ij = ∑_p y_p(i) y_p(j)` of finitely many
vectors `y_p`, so that `⟨A, M⟩ = ∑_p y_pᵀ A y_p`, `Tr M = ∑_p ‖y_p‖²` and
`‖M‖_F² = ∑_{p,q} ⟨y_p, y_q⟩²`.

* **The generalized Barak–Raghavendra–Steurer lemma** ([BHSV25, Lemma 4.3], proved in their
  appendix; `BHSV25.Spectral.Impl.brs`): if the eigenvalues of `A` are at most `1`, then
  `(⟨A, M⟩ - θ Tr M)² ≤ (1 - θ)² · #{eigenvalues ≥ θ} · ‖M‖_F²` whenever `⟨A, M⟩ ≥ θ Tr M`.
  In the eigenbasis `(u_s)` of `A`, with `m_s = u_sᵀ M u_s ≥ 0`,
  `⟨A, M⟩ - θ Tr M = ∑ (μ_s - θ) m_s ≤ (1 - θ) ∑_{μ_s ≥ θ} m_s`, and by Cauchy–Schwarz
  `(∑_{μ_s ≥ θ} m_s)² ≤ #{μ_s ≥ θ} ∑ m_s² ≤ #{μ_s ≥ θ} ‖M‖_F²`.
* **The witness** ([BHSV25, Lemma 4.4]; `BHSV25.Spectral.Impl.witnessVec`): from vectors
  `w_i ∈ ℝ^κ`, one per row of `A`, with `∑ ‖w_i‖² = t`, `∑_{i,j} ⟨w_i, w_j⟩² ≤ t` and
  `∑_{i,j} A_ij ⟨w_i, w_j⟩ ≤ -τ t`, the vectors `v_i = w_i ⊗ w_i / ‖w_i‖` (`0` when `w_i = 0`)
  have Gram matrix `M_ij = ⟨w_i, w_j⟩² / (‖w_i‖ ‖w_j‖)` with `Tr M = t`, `‖M‖_F² ≤ t` and, by
  Cauchy–Schwarz with the weights `A_ij ≥ 0`, `⟨A, M⟩ ≥ τ² t`. The family `y_p` is indexed by the
  coordinates `p ∈ κ × κ` of the tensors.
* For `w_i(s) = u_s(i)` over the `t` eigenvectors `u_s` with eigenvalues at most `-τ`, these
  hypotheses hold, and the two lemmas give `((τ² - τ') t)² ≤ (1 - τ')² · #{μ ≥ τ'} · t`.

The vectors are not normalized to `Tr M = 1` as in the paper; all bounds are scaled by `t`. The
argument applies to every `τ ≥ 0`: when some eigenvalue is at most `-τ`, `τ ≤ 1` and `τ' < 1`, and
otherwise the left-hand side is `0`. Negative `τ'` needs no special care.
-/

@[expose] public section

namespace BHSV25

namespace Spectral

namespace Impl

open Matrix

/-! ### Sums -/

/-- Exchanging the roles of the two indices in the squared Frobenius norm of a Gram matrix:
`∑_{a,a'} ⟨f_a, f_a'⟩² = ∑_{b,b'} ⟨f^b, f^b'⟩²` for the rows `f_a` and columns `f^b` of `f`. -/
theorem sum_sum_sq_sum_mul_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    ∑ a, ∑ a', (∑ b, f a b * f a' b) ^ 2 = ∑ b, ∑ b', (∑ a, f a b * f a b') ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  calc ∑ a, ∑ a', ∑ b, ∑ b', f a b * f a' b * (f a b' * f a' b')
      = ∑ a, ∑ b, ∑ a', ∑ b', f a b * f a' b * (f a b' * f a' b') :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ b', ∑ a', f a b * f a' b * (f a b' * f a' b') :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ b', ∑ a', f a b * f a' b * (f a b' * f a' b') := Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ a, ∑ a', f a b * f a' b * (f a b' * f a' b') :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ a, ∑ a', f a b * f a b' * (f a' b * f a' b') := by
        refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
        ring

theorem sum_diag_le_sum_sum {α : Type*} [Fintype α] (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b) :
    ∑ a, F a a ≤ ∑ a, ∑ b, F a b :=
  Finset.sum_le_sum fun a _ ↦ Finset.single_le_sum (fun b _ ↦ hF a b) (Finset.mem_univ a)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

omit [DecidableEq ι] in
/-- `⟨A, M⟩ = ∑_p y_pᵀ A y_p` for the Gram matrix `M_ij = ∑_p y_p(i) y_p(j)`. -/
theorem sum_dotProduct_mulVec {P : Type*} [Fintype P] (A : Matrix ι ι ℝ) (y : P → ι → ℝ) :
    ∑ p, y p ⬝ᵥ (A *ᵥ y p) = ∑ i, ∑ j, A i j * ∑ p, y p i * y p j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_)
  ring

omit [DecidableEq ι] in
theorem sum_dotProduct_self {P : Type*} [Fintype P] (y : P → ι → ℝ) :
    ∑ p, y p ⬝ᵥ y p = ∑ i, ∑ p, y p i * y p i := by
  simp only [dotProduct]
  exact Finset.sum_comm

/-! ### The generalized Barak–Raghavendra–Steurer lemma -/

/-- **[BHSV25, Lemma 4.3]**, for the Gram matrix `M` of a family `y`: if the eigenvalues of `A`
are at most `1` and `⟨A, M⟩ ≥ θ Tr M`, then
`(⟨A, M⟩ - θ Tr M)² ≤ (1 - θ)² · #{eigenvalues ≥ θ} · ‖M‖_F²`. -/
theorem brs (hA : A.IsHermitian) (hle : ∀ s, hA.eigenvalues s ≤ 1) {θ : ℝ}
    {P : Type*} [Fintype P] (y : P → ι → ℝ)
    (hX : θ * ∑ p, y p ⬝ᵥ y p ≤ ∑ p, y p ⬝ᵥ (A *ᵥ y p)) :
    (∑ p, y p ⬝ᵥ (A *ᵥ y p) - θ * ∑ p, y p ⬝ᵥ y p) ^ 2 ≤
      (1 - θ) ^ 2 * (Finset.univ.filter fun s ↦ θ ≤ hA.eigenvalues s).card *
        ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2 := by
  set m : ι → ℝ := fun s ↦ ∑ p, coeff hA s (y p) ^ 2 with hm
  have hm0 : ∀ s, 0 ≤ m s := fun s ↦ Finset.sum_nonneg fun p _ ↦ sq_nonneg _
  have hXm : ∑ p, y p ⬝ᵥ (A *ᵥ y p) = ∑ s, hA.eigenvalues s * m s := by
    simp only [quad_eq hA, hm, Finset.mul_sum]
    exact Finset.sum_comm
  have hTm : ∑ p, y p ⬝ᵥ y p = ∑ s, m s := by
    simp only [← sum_coeff_sq hA, hm]
    exact Finset.sum_comm
  set K := Finset.univ.filter fun s ↦ θ ≤ hA.eigenvalues s with hK
  have hstep : ∑ p, y p ⬝ᵥ (A *ᵥ y p) - θ * ∑ p, y p ⬝ᵥ y p ≤ (1 - θ) * ∑ s ∈ K, m s := by
    have h1 : ∑ p, y p ⬝ᵥ (A *ᵥ y p) - θ * ∑ p, y p ⬝ᵥ y p =
        ∑ s, (hA.eigenvalues s * m s - θ * m s) := by
      rw [hXm, hTm, Finset.mul_sum, Finset.sum_sub_distrib]
    have h2 : (1 - θ) * ∑ s ∈ K, m s =
        ∑ s, (if θ ≤ hA.eigenvalues s then (1 - θ) * m s else 0) := by
      rw [hK, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      split_ifs <;> simp
    rw [h1, h2]
    refine Finset.sum_le_sum fun s _ ↦ ?_
    split_ifs with hs
    · have := mul_le_mul_of_nonneg_right (hle s) (hm0 s)
      linarith only [this]
    · have := mul_le_mul_of_nonneg_right (lt_of_not_ge hs).le (hm0 s)
      linarith only [this]
  have hsq : (∑ s ∈ K, m s) ^ 2 ≤ K.card * ∑ s, m s ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq K m (fun _ ↦ (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    refine h.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun s _ _ ↦ sq_nonneg _)
      (Nat.cast_nonneg _)
  have hfro : ∑ s, m s ^ 2 ≤ ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2 := by
    calc ∑ s, m s ^ 2 = ∑ s, (∑ p, coeff hA s (y p) * coeff hA s (y p)) ^ 2 := by
          simp only [hm, sq]
      _ ≤ ∑ s, ∑ s', (∑ p, coeff hA s (y p) * coeff hA s' (y p)) ^ 2 :=
          sum_diag_le_sum_sum (fun s s' ↦ (∑ p, coeff hA s (y p) * coeff hA s' (y p)) ^ 2)
            fun _ _ ↦ sq_nonneg _
      _ = ∑ p, ∑ q, (∑ s, coeff hA s (y p) * coeff hA s (y q)) ^ 2 :=
          sum_sum_sq_sum_mul_comm (fun s p ↦ coeff hA s (y p))
      _ = ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2 := by
          simp only [dotProduct_eq_sum_coeff hA]
  have h0 : 0 ≤ ∑ p, y p ⬝ᵥ (A *ᵥ y p) - θ * ∑ p, y p ⬝ᵥ y p := by linarith only [hX]
  have hK0 : 0 ≤ ∑ s ∈ K, m s := Finset.sum_nonneg fun s _ ↦ hm0 s
  calc (∑ p, y p ⬝ᵥ (A *ᵥ y p) - θ * ∑ p, y p ⬝ᵥ y p) ^ 2
      ≤ ((1 - θ) * ∑ s ∈ K, m s) ^ 2 := pow_le_pow_left₀ h0 hstep 2
    _ = (1 - θ) ^ 2 * (∑ s ∈ K, m s) ^ 2 := by ring
    _ ≤ (1 - θ) ^ 2 * (K.card * ∑ s, m s ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ ≤ (1 - θ) ^ 2 * (K.card * ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfro (Nat.cast_nonneg _))
          (sq_nonneg _)
    _ = _ := by ring

/-! ### The witness -/

section Witness

variable {κ : Type*} [Fintype κ]

/-- The norm `‖w_i‖ = √(∑_s w_i(s)²)` of the `i`-th vector of the family `w`. -/
noncomputable def rad (w : ι → κ → ℝ) (i : ι) : ℝ := Real.sqrt (∑ s, w i s ^ 2)

/-- The witness of [BHSV25, Lemma 4.4]: the coordinate `p ∈ κ × κ` of the vectors
`v_i = w_i ⊗ w_i / ‖w_i‖` (`0` when `w_i = 0`), as a vector indexed by `i`. -/
noncomputable def witnessVec (w : ι → κ → ℝ) (p : κ × κ) (i : ι) : ℝ :=
  w i p.1 * w i p.2 / rad w i

omit [Fintype ι] [DecidableEq ι] in
theorem rad_nonneg (w : ι → κ → ℝ) (i : ι) : 0 ≤ rad w i := Real.sqrt_nonneg _

omit [Fintype ι] [DecidableEq ι] in
theorem rad_sq (w : ι → κ → ℝ) (i : ι) : rad w i ^ 2 = ∑ s, w i s ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
/-- Cauchy–Schwarz: `⟨w_i, w_j⟩² ≤ (‖w_i‖ ‖w_j‖)²`. -/
theorem sq_sum_mul_le (w : ι → κ → ℝ) (i j : ι) :
    (∑ s, w i s * w j s) ^ 2 ≤ (rad w i * rad w j) ^ 2 := by
  rw [mul_pow, rad_sq, rad_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [Fintype ι] [DecidableEq ι] in
/-- `⟨v_i, v_j⟩ = ⟨w_i, w_j⟩² / (‖w_i‖ ‖w_j‖)`. -/
theorem sum_witnessVec_mul (w : ι → κ → ℝ) (i j : ι) :
    ∑ p, witnessVec w p i * witnessVec w p j =
      (∑ s, w i s * w j s) ^ 2 / (rad w i * rad w j) := by
  simp only [witnessVec, Fintype.sum_prod_type]
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s' _ ↦ ?_
  ring

omit [DecidableEq ι] in
/-- `Tr M = ∑_i ‖w_i‖²`. -/
theorem sum_witnessVec_dotProduct_self (w : ι → κ → ℝ) :
    ∑ p, witnessVec w p ⬝ᵥ witnessVec w p = ∑ i, ∑ s, w i s ^ 2 := by
  rw [sum_dotProduct_self]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sum_witnessVec_mul, ← rad_sq]
  have h : ∑ s, w i s * w i s = rad w i ^ 2 := by
    rw [rad_sq]
    exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm
  rw [h]
  rcases eq_or_ne (rad w i) 0 with h0 | h0
  · simp [h0]
  · field_simp

omit [Fintype ι] [DecidableEq ι] in
theorem sq_div_sq_le {G R : ℝ} (h : G ^ 2 ≤ R ^ 2) : (G ^ 2 / R) ^ 2 ≤ G ^ 2 := by
  rcases eq_or_ne R 0 with h0 | h0
  · simp only [h0, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg G
  · have hR : 0 < R ^ 2 := lt_of_le_of_ne (sq_nonneg R) (pow_ne_zero 2 h0).symm
    have h1 : G ^ 2 / R ^ 2 ≤ 1 := (div_le_one hR).2 h
    calc (G ^ 2 / R) ^ 2 = G ^ 2 * (G ^ 2 / R ^ 2) := by ring
      _ ≤ G ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg G)
      _ = G ^ 2 := mul_one _

omit [DecidableEq ι] in
/-- `‖M‖_F² ≤ ∑_{i,j} ⟨w_i, w_j⟩²`. -/
theorem sum_sum_witnessVec_sq_le (w : ι → κ → ℝ) :
    ∑ p, ∑ q, (witnessVec w p ⬝ᵥ witnessVec w q) ^ 2 ≤ ∑ i, ∑ j, (∑ s, w i s * w j s) ^ 2 := by
  have h : ∑ p, ∑ q, (witnessVec w p ⬝ᵥ witnessVec w q) ^ 2 =
      ∑ i, ∑ j, (∑ p, witnessVec w p i * witnessVec w p j) ^ 2 :=
    sum_sum_sq_sum_mul_comm (fun p i ↦ witnessVec w p i)
  rw [h]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  rw [sum_witnessVec_mul]
  exact sq_div_sq_le (sq_sum_mul_le w i j)

omit [DecidableEq ι] in
/-- `⟨A, M⟩ ≥ τ² t`: by Cauchy–Schwarz with the weights `A_ij ≥ 0`,
`(∑ A_ij ⟨w_i, w_j⟩)² ≤ (∑ A_ij ⟨w_i, w_j⟩² / (‖w_i‖ ‖w_j‖)) (∑ A_ij ‖w_i‖ ‖w_j‖)`, where the
first factor is `⟨A, M⟩`, the left-hand side is at least `τ² t²`, and the last factor is at most
`∑ ‖w_i‖² = t` since the eigenvalues of `A` are at most `1`. -/
theorem le_sum_witnessVec_quad (hnonneg : ∀ i j, 0 ≤ A i j)
    (hle : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) (w : ι → κ → ℝ) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 < t)
    (htr : ∑ i, ∑ s, w i s ^ 2 = t)
    (hneg : ∑ i, ∑ j, A i j * ∑ s, w i s * w j s ≤ -(τ * t)) :
    τ ^ 2 * t ≤ ∑ p, witnessVec w p ⬝ᵥ (A *ᵥ witnessVec w p) := by
  set G : ι → ι → ℝ := fun i j ↦ ∑ s, w i s * w j s with hG
  set r := rad w
  have hX : ∑ p, witnessVec w p ⬝ᵥ (A *ᵥ witnessVec w p) =
      ∑ i, ∑ j, A i j * (G i j ^ 2 / (r i * r j)) := by
    rw [sum_dotProduct_mulVec]
    simp only [sum_witnessVec_mul]
    rfl
  have hD : ∑ i, ∑ j, A i j * (r i * r j) ≤ t := by
    have h1 : ∑ i, ∑ j, A i j * (r i * r j) = r ⬝ᵥ (A *ᵥ r) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have h2 : r ⬝ᵥ r = t := by
      rw [← htr, dotProduct]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← rad_sq, sq]
    rw [h1, ← h2]
    exact hle r
  have hcs : (∑ i, ∑ j, A i j * G i j) ^ 2 ≤
      (∑ i, ∑ j, A i j * (G i j ^ 2 / (r i * r j))) * ∑ i, ∑ j, A i j * (r i * r j) := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (ι × ι))
      (r := fun q ↦ A q.1 q.2 * G q.1 q.2)
      (f := fun q ↦ A q.1 q.2 * (G q.1 q.2 ^ 2 / (r q.1 * r q.2)))
      (g := fun q ↦ A q.1 q.2 * (r q.1 * r q.2))
      (fun q _ ↦ mul_nonneg (hnonneg _ _)
        (div_nonneg (sq_nonneg _) (mul_nonneg (rad_nonneg w _) (rad_nonneg w _))))
      (fun q _ ↦ mul_nonneg (hnonneg _ _) (mul_nonneg (rad_nonneg w _) (rad_nonneg w _)))
      (fun q _ ↦ ?_)
    · simpa only [Fintype.sum_prod_type] using h
    · obtain ⟨i, j⟩ := q
      dsimp only
      rcases eq_or_ne (r i * r j) 0 with h0 | h0
      · have hG0 : G i j ^ 2 ≤ 0 := by
          have h1 : G i j ^ 2 ≤ (r i * r j) ^ 2 := sq_sum_mul_le w i j
          rw [h0] at h1
          simpa using h1
        have : G i j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
          (le_antisymm hG0 (sq_nonneg _))
        simp [this]
      · apply le_of_eq
        field_simp
        rw [eq_div_iff h0]
        ring
  have hN : (τ * t) ^ 2 ≤ (∑ i, ∑ j, A i j * G i j) ^ 2 := by
    have h0 : 0 ≤ τ * t := mul_nonneg hτ ht.le
    have h1 : τ * t ≤ -∑ i, ∑ j, A i j * G i j := by linarith only [hneg]
    calc (τ * t) ^ 2 ≤ (-∑ i, ∑ j, A i j * G i j) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = _ := neg_sq _
  have hX0 : 0 ≤ ∑ i, ∑ j, A i j * (G i j ^ 2 / (r i * r j)) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hnonneg _ _)
      (div_nonneg (sq_nonneg _) (mul_nonneg (rad_nonneg w _) (rad_nonneg w _)))
  rw [hX]
  refine le_of_mul_le_mul_right ?_ ht
  calc τ ^ 2 * t * t = (τ * t) ^ 2 := by ring
    _ ≤ (∑ i, ∑ j, A i j * (G i j ^ 2 / (r i * r j))) * ∑ i, ∑ j, A i j * (r i * r j) :=
        hN.trans hcs
    _ ≤ (∑ i, ∑ j, A i j * (G i j ^ 2 / (r i * r j))) * t := mul_le_mul_of_nonneg_left hD hX0

end Witness

/-! ### The eigenvectors with eigenvalues at most `-τ` -/

/-- The vectors `w_i(s) = u_s(i)` for the eigenvectors `u_s` of `A` with eigenvalue at most `-τ`
(and `w_i(s) = 0` for the other `s`). -/
noncomputable def bottomVecs (hA : A.IsHermitian) (τ : ℝ) (i s : ι) : ℝ :=
  (if hA.eigenvalues s ≤ -τ then 1 else 0) * hA.eigenvectorBasis s i

theorem sum_bottomVecs_mul (hA : A.IsHermitian) (τ : ℝ) (s s' : ι) :
    ∑ i, bottomVecs hA τ i s * bottomVecs hA τ i s' =
      if s = s' then (if hA.eigenvalues s ≤ -τ then 1 else 0) else 0 := by
  have hu : ⇑(hA.eigenvectorBasis s) ⬝ᵥ ⇑(hA.eigenvectorBasis s') = if s = s' then 1 else 0 :=
    coeff_eigenvector hA s s'
  have h : ∑ i, bottomVecs hA τ i s * bottomVecs hA τ i s' =
      (if hA.eigenvalues s ≤ -τ then 1 else 0) * (if hA.eigenvalues s' ≤ -τ then 1 else 0) *
        (⇑(hA.eigenvectorBasis s) ⬝ᵥ ⇑(hA.eigenvectorBasis s')) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [bottomVecs]
    ring
  rw [h, hu]
  by_cases hss : s = s'
  · subst hss
    split_ifs <;> simp
  · simp [hss]

theorem sum_sum_bottomVecs_sq (hA : A.IsHermitian) (τ : ℝ) :
    ∑ i, ∑ s, bottomVecs hA τ i s ^ 2 =
      ((Finset.univ.filter fun s ↦ hA.eigenvalues s ≤ -τ).card : ℝ) := by
  rw [Finset.sum_comm, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have h := sum_bottomVecs_mul hA τ s s
  rw [ite_eq_left rfl] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ sq _

theorem sum_sum_bottomVecs_gram_sq (hA : A.IsHermitian) (τ : ℝ) :
    ∑ i, ∑ j, (∑ s, bottomVecs hA τ i s * bottomVecs hA τ j s) ^ 2 =
      ((Finset.univ.filter fun s ↦ hA.eigenvalues s ≤ -τ).card : ℝ) := by
  rw [sum_sum_sq_sum_mul_comm (fun i s ↦ bottomVecs hA τ i s), ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [sum_bottomVecs_mul, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> simp

theorem sum_sum_bottomVecs_quad (hA : A.IsHermitian) (τ : ℝ) :
    ∑ i, ∑ j, A i j * ∑ s, bottomVecs hA τ i s * bottomVecs hA τ j s ≤
      -(τ * ((Finset.univ.filter fun s ↦ hA.eigenvalues s ≤ -τ).card : ℝ)) := by
  rw [← sum_dotProduct_mulVec A (fun s i ↦ bottomVecs hA τ i s), ← Finset.sum_boole,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  set c : ℝ := if hA.eigenvalues s ≤ -τ then 1 else 0 with hc
  have hv : (fun i ↦ bottomVecs hA τ i s) = c • ⇑(hA.eigenvectorBasis s) := by
    funext i
    simp [bottomVecs, hc]
  have hu : ⇑(hA.eigenvectorBasis s) ⬝ᵥ ⇑(hA.eigenvectorBasis s) = 1 := by
    have := coeff_eigenvector hA s s
    rw [ite_eq_left rfl] at this
    exact this
  rw [hv, mulVec_smul, hA.mulVec_eigenvectorBasis s, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, hu]
  simp only [smul_eq_mul, mul_one]
  rw [hc]
  split_ifs with h
  · linarith only [h]
  · simp

end Impl

open Matrix Impl

/-- **[BHSV25, Theorem 4.1]**, in the parameters of Theorem 1.7: for a symmetric matrix with
nonnegative entries and eigenvalues in `[-1, 1]`, and all `τ ≥ 0` and `τ' < τ²`,
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`. -/
theorem thresholdRank {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) (hnorm : ∀ i, |hA.eigenvalues i| ≤ 1)
    (τ τ' : ℝ) (hτ : 0 ≤ τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 *
        ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ hA.eigenvalues i).card := by
  set T := Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -τ with hT
  set k : ℝ := ((Finset.univ.filter fun i ↦ τ' ≤ hA.eigenvalues i).card : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  rcases T.eq_empty_or_nonempty with hT0 | ⟨s₀, hs₀⟩
  · rw [hT0, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact hk0
  have hle1 : ∀ s, hA.eigenvalues s ≤ 1 := fun s ↦ (abs_le.1 (hnorm s)).2
  have hτ1 : τ ≤ 1 := by
    have h1 := (abs_le.1 (hnorm s₀)).1
    have h2 : hA.eigenvalues s₀ ≤ -τ := (Finset.mem_filter.1 hs₀).2
    linarith only [h1, h2]
  have hθ1 : τ' < 1 := by
    have : τ ^ 2 ≤ 1 := by
      have := mul_le_mul hτ1 hτ1 hτ zero_le_one
      rw [sq]
      linarith only [this]
    linarith only [this, hτ']
  set t : ℝ := (T.card : ℝ) with ht_def
  have ht : 0 < t := Nat.cast_pos.2 (Finset.card_pos.2 ⟨s₀, hs₀⟩)
  set w := bottomVecs hA τ
  have W1 : ∑ i, ∑ s, w i s ^ 2 = t := sum_sum_bottomVecs_sq hA τ
  have W2 : ∑ i, ∑ j, (∑ s, w i s * w j s) ^ 2 = t := sum_sum_bottomVecs_gram_sq hA τ
  have W3 : ∑ i, ∑ j, A i j * ∑ s, w i s * w j s ≤ -(τ * t) := sum_sum_bottomVecs_quad hA τ
  set y := witnessVec w
  have Y1 : ∑ p, y p ⬝ᵥ y p = t := (sum_witnessVec_dotProduct_self w).trans W1
  have Y2 : ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2 ≤ t := (sum_sum_witnessVec_sq_le w).trans W2.le
  have hquad : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x := fun x ↦ by
    have := quad_le_of_inEigSpan hA (τ := 1) (x := x) fun i hi ↦ absurd (hle1 i) hi
    linarith only [this]
  have Y3 : τ ^ 2 * t ≤ ∑ p, y p ⬝ᵥ (A *ᵥ y p) :=
    le_sum_witnessVec_quad hnonneg hquad w hτ ht W1 W3
  have hθt : τ' * t ≤ τ ^ 2 * t := mul_le_mul_of_nonneg_right hτ'.le ht.le
  have hX : τ' * ∑ p, y p ⬝ᵥ y p ≤ ∑ p, y p ⬝ᵥ (A *ᵥ y p) := by
    rw [Y1]
    linarith only [Y3, hθt]
  have hb := brs hA hle1 y hX
  rw [Y1, ← hk] at hb
  have h1 : ((τ ^ 2 - τ') * t) ^ 2 ≤ (∑ p, y p ⬝ᵥ (A *ᵥ y p) - τ' * t) ^ 2 := by
    refine pow_le_pow_left₀ ?_ ?_ 2
    · exact mul_nonneg (sub_nonneg.2 hτ'.le) ht.le
    · linarith only [Y3]
  have h2 : (1 - τ') ^ 2 * k * ∑ p, ∑ q, (y p ⬝ᵥ y q) ^ 2 ≤ (1 - τ') ^ 2 * k * t :=
    mul_le_mul_of_nonneg_left Y2 (mul_nonneg (sq_nonneg _) hk0)
  have h3 : (τ ^ 2 - τ') ^ 2 * t * t ≤ k * (1 - τ') ^ 2 * t := by
    calc (τ ^ 2 - τ') ^ 2 * t * t = ((τ ^ 2 - τ') * t) ^ 2 := by ring
      _ ≤ _ := h1.trans (hb.trans h2)
      _ = k * (1 - τ') ^ 2 * t := by ring
  have h4 := le_of_mul_le_mul_right h3 ht
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos (sub_pos.2 hθ1) 2)]
  exact h4

/-- **[BHSV25, Theorem 4.1]**: for a symmetric matrix with nonnegative entries and eigenvalues in
`[-1, 1]`, `λ ≥ 0` and `σ ∈ (0, 1)`,
`σ² · #{eigenvalues ≤ -λ} ≤ #{eigenvalues ≥ (λ² - σ) / (1 - σ)}`. -/
theorem thresholdRank_sigma {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) (hnorm : ∀ i, |hA.eigenvalues i| ≤ 1)
    (lam σ : ℝ) (hlam : 0 ≤ lam) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    σ ^ 2 * ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -lam).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ (lam ^ 2 - σ) / (1 - σ) ≤ hA.eigenvalues i).card := by
  have h1σ : 0 < 1 - σ := by linarith
  rcases lt_trichotomy lam 1 with hl | rfl | hl
  · -- `λ < 1`: the case `τ = λ`
    have hl2 : lam ^ 2 < 1 := by nlinarith
    set τ' := (lam ^ 2 - σ) / (1 - σ) with hτ'
    have hτ'lt : τ' < lam ^ 2 := by
      rw [hτ', div_lt_iff₀ h1σ]
      nlinarith
    have h1τ : 1 - τ' ≠ 0 := (by linarith : (0 : ℝ) < 1 - τ').ne'
    have hcoef : (lam ^ 2 - τ') / (1 - τ') = σ := by
      rw [div_eq_iff h1τ, hτ']
      field_simp
      ring
    have := thresholdRank A hA hnonneg hnorm lam τ' hlam hτ'lt
    rwa [hcoef] at this
  · -- `λ = 1`: the threshold is `1`
    have hthr : ((1 : ℝ) ^ 2 - σ) / (1 - σ) = 1 := by rw [one_pow]; exact div_self h1σ.ne'
    rw [hthr]
    obtain ⟨τ', hτ'1, hτ'eq⟩ : ∃ τ' : ℝ, τ' < 1 ∧
        ∀ i, τ' ≤ hA.eigenvalues i ↔ 1 ≤ hA.eigenvalues i := by
      by_cases hS : (Finset.univ.filter fun i ↦ hA.eigenvalues i < 1).Nonempty
      · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ hA.eigenvalues hS
        have h0 : hA.eigenvalues i₀ < 1 := (Finset.mem_filter.1 hi₀).2
        refine ⟨(hA.eigenvalues i₀ + 1) / 2, by linarith, fun i ↦ ⟨fun h ↦ ?_, fun h ↦ by linarith⟩⟩
        by_contra hlt
        push Not at hlt
        have := hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
        linarith
      · refine ⟨0, by norm_num, fun i ↦ ⟨fun _ ↦ ?_, fun h ↦ by linarith⟩⟩
        by_contra hlt
        push Not at hlt
        exact hS ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩⟩
    have h := thresholdRank A hA hnonneg hnorm 1 τ' zero_le_one (by rw [one_pow]; exact hτ'1)
    have hc : ((1 : ℝ) ^ 2 - τ') / (1 - τ') = 1 := by
      rw [one_pow]; exact div_self (by linarith)
    rw [hc, one_pow, one_mul, Finset.filter_congr fun i _ ↦ hτ'eq i] at h
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
    calc σ ^ 2 * ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -1).card : ℝ)
        ≤ 1 * ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -1).card : ℝ) :=
          mul_le_mul_of_nonneg_right hσ2 (Nat.cast_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h
  · -- `λ > 1`: no eigenvalue is at most `-λ`
    have h0 : (Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -lam) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun i _ h ↦ ?_
      have := (abs_le.1 (hnorm i)).1
      linarith
    rw [h0, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _

/-- **[BHSV25, Theorem 1.7]**: for every graph and all `τ ≥ 0` and `τ' < τ²`, the spectrum `σ(G)`
of its normalized adjacency matrix satisfies
`((τ² - τ') / (1 - τ'))² · |σ(G) ∩ (-∞, -τ]| ≤ |σ(G) ∩ [τ', ∞)|`. -/
theorem thresholdRank_graph (G : Graph) (τ τ' : ℝ) (hτ : 0 ≤ τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card :=
  thresholdRank G.normAdj G.normAdj_isHermitian (Impl.normAdj_nonneg G) (Impl.abs_eig_le_one G)
    τ τ' hτ hτ'

end Spectral

end BHSV25
