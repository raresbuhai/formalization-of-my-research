module

public import BHSV25.Spectral.ThresholdRank

/-!
# Spectral toolkit

Facts about symmetric real matrices through an orthonormal basis of eigenvectors (Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`), and about the normalized adjacency matrix of a graph.

* **Coordinates in the eigenbasis** (`BHSV25.Spectral.coeff`): `x = ∑ᵢ cᵢ uᵢ` with
  `cᵢ = ⟨uᵢ, x⟩`, so `‖x‖² = ∑ cᵢ²` and `xᵀ A x = ∑ μᵢ cᵢ²`.
* **Spans of eigenvectors** (`BHSV25.Spectral.InEigSpan`): `x` has no component on the
  eigenvectors whose eigenvalues fail a property `S`; `BHSV25.Spectral.proj` is the orthogonal
  projection onto that span.
* **Counting eigenvalues** by subspaces, in the direction of the Courant–Fischer theorem: if the
  only vector of the span of the eigenvectors with eigenvalues in `S` that is orthogonal to `r`
  given vectors is `0`, at most `r` eigenvalues lie in `S`
  (`BHSV25.Spectral.card_le_of_inEigSpan`).
* **Graphs**: the normalized adjacency matrix has nonnegative entries and eigenvalues in
  `[-1, 1]`; for a `d`-regular graph it is `A / d` and fixes the all-ones vector; a regular graph
  with at most one eigenvalue above `L` has `xᵀ Ã x ≤ (∑ x)² / n + L (‖x‖² - (∑ x)² / n)`; and
  [BHSV25, Corollary 4.2] bounds the number of eigenvalues near `-1` by the number near `1`
  (`BHSV25.Graph.card_eig_le_neg_le`), from Theorem 4.1 (`BHSV25.Spectral.thresholdRank_graph`).

The proofs are in `BHSV25/Spectral/Eigen.lean`, `BHSV25/Spectral/GraphFacts.lean` and
`BHSV25/Spectral/ThresholdRank.lean`.
-/

@[expose] public section

namespace BHSV25

namespace Spectral

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}

/-- The coefficient of `x` on the `i`-th eigenvector of `A`. -/
noncomputable def coeff (hA : A.IsHermitian) (i : ι) (x : ι → ℝ) : ℝ :=
  ⇑(hA.eigenvectorBasis i) ⬝ᵥ x

/-- `x` lies in the span of the eigenvectors of `A` whose eigenvalues satisfy `S`: its coefficient
on every other eigenvector is `0`. -/
def InEigSpan (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) : Prop :=
  ∀ i, ¬ S (hA.eigenvalues i) → coeff hA i x = 0

open Classical in
/-- The orthogonal projection of `x` onto the span of the eigenvectors of `A` whose eigenvalues
satisfy `S`. -/
noncomputable def proj (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) : ι → ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ S (hA.eigenvalues i)), coeff hA i x • ⇑(hA.eigenvectorBasis i)

theorem dotProduct_eq_sum_coeff (hA : A.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ y = ∑ i, coeff hA i x * coeff hA i y :=
  Impl.dotProduct_eq_sum_coeff hA x y

theorem sum_coeff_sq (hA : A.IsHermitian) (x : ι → ℝ) : ∑ i, coeff hA i x ^ 2 = x ⬝ᵥ x :=
  Impl.sum_coeff_sq hA x

theorem eq_of_coeff_eq (hA : A.IsHermitian) {x y : ι → ℝ} (h : ∀ i, coeff hA i x = coeff hA i y) :
    x = y :=
  Impl.eq_of_coeff_eq hA h

theorem coeff_mulVec (hA : A.IsHermitian) (i : ι) (x : ι → ℝ) :
    coeff hA i (A *ᵥ x) = hA.eigenvalues i * coeff hA i x :=
  Impl.coeff_mulVec hA i x

theorem quad_eq (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * coeff hA i x ^ 2 :=
  Impl.quad_eq hA x

theorem coeff_proj (hA : A.IsHermitian) (S : ℝ → Prop) (i : ι) (x : ι → ℝ)
    [Decidable (S (hA.eigenvalues i))] :
    coeff hA i (proj hA S x) = if S (hA.eigenvalues i) then coeff hA i x else 0 :=
  Impl.coeff_proj hA S i x

theorem inEigSpan_proj (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    InEigSpan hA S (proj hA S x) :=
  Impl.inEigSpan_proj hA S x

open Classical in
/-- **Courant–Fischer, counting form**: if the only vector in the span of the eigenvectors with
eigenvalues in `S` that is orthogonal to `w 0, …, w (r - 1)` is `0`, then at most `r` eigenvalues
(with multiplicity) lie in `S`. -/
theorem card_le_of_inEigSpan (hA : A.IsHermitian) (S : ℝ → Prop) {r : ℕ} (w : Fin r → ι → ℝ)
    (h : ∀ x, InEigSpan hA S x → (∀ j, w j ⬝ᵥ x = 0) → x = 0) :
    (Finset.univ.filter fun i ↦ S (hA.eigenvalues i)).card ≤ r :=
  Impl.card_le_of_inEigSpan hA S w h

theorem quad_gt_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (τ < ·) x) (hx : x ≠ 0) : τ * (x ⬝ᵥ x) < x ⬝ᵥ (A *ᵥ x) :=
  Impl.quad_gt_of_inEigSpan hA h hx

end Spectral

namespace Graph

open Matrix

variable (G : Graph)

/-- `w` lies in the span of the eigenvectors of the normalized adjacency matrix whose
eigenvalues satisfy `S`. -/
def InEigSpan (S : ℝ → Prop) (w : Fin G.1 → ℝ) : Prop :=
  Spectral.InEigSpan G.normAdj_isHermitian S w

theorem normAdj_nonneg (u v : Fin G.1) : 0 ≤ G.normAdj u v :=
  Spectral.Impl.normAdj_nonneg G u v

theorem abs_quad_normAdj_le (x : Fin G.1 → ℝ) : |x ⬝ᵥ (G.normAdj *ᵥ x)| ≤ x ⬝ᵥ x :=
  Spectral.Impl.abs_quad_normAdj_le G x

theorem abs_eig_le_one (i : Fin G.1) : |G.eig i| ≤ 1 :=
  Spectral.Impl.abs_eig_le_one G i

open Classical in
theorem normAdj_of_isRegularOfDegree {d : ℕ} (h : G.2.IsRegularOfDegree d) (u v : Fin G.1) :
    G.normAdj u v = if G.2.Adj u v then (d : ℝ)⁻¹ else 0 :=
  Spectral.Impl.normAdj_of_isRegularOfDegree G h u v

open Classical in
theorem normAdj_mulVec_one {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) :
    G.normAdj *ᵥ (fun _ ↦ (1 : ℝ)) = fun _ ↦ 1 :=
  Spectral.Impl.normAdj_mulVec_one G h hd

open Classical in
/-- In a regular graph with at most one eigenvalue above `L ∈ [0, 1)`, the quadratic form of the
normalized adjacency matrix is at most `L` on the vectors orthogonal to the all-ones vector. -/
theorem quad_le_of_numEigGT_le_one {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) {L : ℝ}
    (hL0 : 0 ≤ L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1) (x : Fin G.1 → ℝ) :
    x ⬝ᵥ (G.normAdj *ᵥ x) ≤
      (∑ v, x v) ^ 2 / G.1 + L * (x ⬝ᵥ x - (∑ v, x v) ^ 2 / G.1) :=
  Spectral.Impl.quad_le_of_numEigGT_le_one G h hd hL0 hL1 hexp x

/-- **[BHSV25, Corollary 4.2]** for graphs: few eigenvalues at least `τ` imply few eigenvalues at
most `-√(τ (1 - σ) + σ)`. -/
theorem card_eig_le_neg_le {τ σ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    σ ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -Real.sqrt (τ * (1 - σ) + σ)).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ ≤ G.eig i).card := by
  have hpos : 0 < τ * (1 - σ) + σ := by
    have := mul_nonneg hτ0 (sub_nonneg.2 hσ1.le)
    linarith only [this, hσ0]
  have hsq : Real.sqrt (τ * (1 - σ) + σ) ^ 2 = τ * (1 - σ) + σ := Real.sq_sqrt hpos.le
  have hlt : τ < Real.sqrt (τ * (1 - σ) + σ) ^ 2 := by
    rw [hsq]
    have := mul_pos hσ0 (sub_pos.2 hτ1)
    linarith only [this]
  have hσ : (Real.sqrt (τ * (1 - σ) + σ) ^ 2 - τ) / (1 - τ) = σ := by
    rw [hsq, div_eq_iff (sub_pos.2 hτ1).ne']
    ring
  have h := Spectral.thresholdRank_graph G _ τ (Real.sqrt_pos.2 hpos).le hlt
  rwa [hσ] at h

end Graph

end BHSV25
