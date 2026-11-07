module

public import BHSV25.Hard.Design

/-!
# Blow-ups of designs: regularity and spectra

For a design `D` (`BHSV25/Hard/Design.lean`) and a graph `G` of maximum degree `Δ`, the blow-up
`H` of the template of `D` by `G` (`BHSV25.Hard.Design.blow`):

* is `d n`-regular, `d = d₀ 4^(a r)` (`BHSV25.Hard.Design.blow_isRegular`);
* has adjacency matrix within `E = t · err a r · n + w Δ / 2` of the planted matrix
  `Ĉ (group p) (group q)` in bilinear form (`BHSV25.Hard.Design.bil_blow_sub_le`), where `w`
  bounds the absolute row sums of `W⁰`;
* so, if the quadratic form of a matrix `B` on groups is at most `0` on the vectors orthogonal to
  `L` weight vectors, and `Ĉ` is within `δ` of `B`, at most `L` eigenvalues of `H` exceed
  `(2E + δ N) / (d n)` (`BHSV25.Hard.Design.numEigGT_blow_le`); and at most `K` eigenvalues are
  below `-2E / (d n)` (`BHSV25.Hard.Design.card_eig_blow_lt_neg_le`).
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Matrix Cayley

theorem sum_ind_adj_eq_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    ∑ v', ind (G.Adj v v') = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    card_filter]
  push_cast
  exact sum_congr rfl fun v' _ ↦ by unfold ind; split_ifs <;> simp

namespace Design

variable (D : Design) (a : ℕ)

/-- The blow-up of the template of `D` by `G`. -/
noncomputable abbrev blow (G : Graph) : Graph := (D.template a).blowup G

/-- The group of a vertex of the blow-up. -/
noncomputable def grp {n : ℕ} (p : Fin (Fintype.card (D.Cell a) * n)) : Fin D.K :=
  D.grc a ((D.template a).cell p)

/-- The degree of the template. -/
abbrev deg : ℕ := D.d₀ * (4 ^ a) ^ D.r

open Classical in
theorem blow_isRegular (G : Graph) : (D.blow a G).2.IsRegularOfDegree (D.deg a * G.1) :=
  (D.template a).blowup_isRegular G

/-- **The blow-up is close to the planted matrix.** -/
theorem bil_blow_sub_le (G : Graph) {w Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hw : ∀ τ, ∑ τ', |(D.W0 τ τ' : ℝ)| ≤ w) (hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ Δ)
    (x y : Fin (D.blow a G).1 → ℝ) :
    |bil (D.blow a G) x y - ∑ p, ∑ q, x p * D.Chat (D.grp a p) (D.grp a q) * y q| ≤
      (Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2) * (x ⬝ᵥ x + y ⬝ᵥ y) :=
  (D.template a).bil_blowup_sub_le G (fun u u' ↦ D.Chat (D.grc a u) (D.grc a u'))
    (mul_nonneg (by positivity) (err_nonneg a D.r)) hΔ0 (D.template_approx a)
    (fun u ↦ (D.sum_abs_W a u).le.trans (hw _)) hΔ x y

/-- The planted form in terms of the group sums. -/
theorem sum_planted {n : ℕ} (B : Fin D.K → Fin D.K → ℝ)
    (x : Fin (Fintype.card (D.Cell a) * n) → ℝ) :
    ∑ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q =
      ∑ i, ∑ j, (∑ p ∈ univ.filter (D.grp a · = i), x p) * B i j *
        ∑ q ∈ univ.filter (D.grp a · = j), x q := by
  have h1 : ∀ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q =
      ∑ j, x p * B (D.grp a p) j * ∑ q ∈ univ.filter (D.grp a · = j), x q := by
    intro p
    rw [← sum_fiberwise univ (D.grp a)]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun q hq ↦ by rw [(mem_filter.1 hq).2]
  simp_rw [h1]
  rw [← sum_fiberwise univ (D.grp a)]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_mul, sum_mul]
  exact sum_congr rfl fun p hp ↦ by rw [(mem_filter.1 hp).2]

theorem sq_sum_abs_le {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ p, |x p|) ^ 2 ≤ Fintype.card ι * ∑ p, x p ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun p ↦ |x p|)
  simpa [sq_abs] using this

/-- **Few large eigenvalues**: if `B` is at most `0` on the group vectors orthogonal to `L`
weight vectors and `Ĉ` is within `δ` of `B`, at most `L` eigenvalues of the blow-up exceed
`(2E + δ N) / (d n)`. -/
theorem numEigGT_blow_le (G : Graph) (hn : 0 < G.1) (hd : 0 < D.deg a) {w Δ δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hw : ∀ τ, ∑ τ', |(D.W0 τ τ' : ℝ)| ≤ w)
    (hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ Δ) (B : Fin D.K → Fin D.K → ℝ) (hδ : 0 ≤ δ)
    (hB : ∀ i j, |D.Chat i j - B i j| ≤ δ) {L : ℕ} (wt : Fin L → Fin D.K → ℝ)
    (hneg : ∀ X : Fin D.K → ℝ, (∀ l, ∑ i, wt l i * X i = 0) → ∑ i, ∑ j, X i * B i j * X j ≤ 0) :
    (D.blow a G).numEigGT ((2 * (Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2) +
      δ * (Fintype.card (D.Cell a) * G.1)) / (D.deg a * G.1)) ≤ L := by
  set E := Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2
  set N : ℝ := Fintype.card (D.Cell a) * G.1
  have hD : (0 : ℝ) < (D.deg a * G.1 : ℕ) := by exact_mod_cast Nat.mul_pos hd hn
  refine numEigGT_le_of_quad (D.blow a G) (fun l p ↦ wt l (D.grp a p))
    (fun x ↦ (∑ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q) / (D.deg a * G.1 : ℕ)) _
    (fun x ↦ ?_) (fun x hx ↦ ?_)
  · rw [(D.template a).quad_normAdj_blowup G x]
    have h1 := D.bil_blow_sub_le a G hΔ0 hw hΔ x x
    have h2 : ∑ p, ∑ q, x p * D.Chat (D.grp a p) (D.grp a q) * x q -
        ∑ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q ≤ δ * N * (x ⬝ᵥ x) := by
      rw [← sum_sub_distrib]
      have hpt : ∀ p q, |x p * D.Chat (D.grp a p) (D.grp a q) * x q -
          x p * B (D.grp a p) (D.grp a q) * x q| ≤ δ * (|x p| * |x q|) := by
        intro p q
        rw [← sub_mul, ← mul_sub, abs_mul, abs_mul]
        have := hB (D.grp a p) (D.grp a q)
        nlinarith [abs_nonneg (x p), abs_nonneg (x q), mul_nonneg (abs_nonneg (x p))
          (abs_nonneg (x q))]
      refine (le_abs_self _).trans ?_
      calc _ ≤ ∑ p, |∑ q, x p * D.Chat (D.grp a p) (D.grp a q) * x q -
            ∑ q, x p * B (D.grp a p) (D.grp a q) * x q| := abs_sum_le_sum_abs _ _
        _ = ∑ p, |∑ q, (x p * D.Chat (D.grp a p) (D.grp a q) * x q -
            x p * B (D.grp a p) (D.grp a q) * x q)| := by simp_rw [sum_sub_distrib]
        _ ≤ ∑ p, ∑ q, δ * (|x p| * |x q|) :=
            sum_le_sum fun p _ ↦ (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ ↦ hpt p q)
        _ = δ * (∑ p, |x p|) ^ 2 := by
            rw [sq, sum_mul_sum, mul_sum]; simp_rw [mul_sum]
        _ ≤ δ * N * (x ⬝ᵥ x) := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hδ
            have := sq_sum_abs_le x
            simp only [Fintype.card_fin, dotProduct, ← sq] at this ⊢
            push_cast at this
            exact this
    have key : bil (D.blow a G) x x ≤ ∑ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q +
        (2 * E + δ * N) * (x ⬝ᵥ x) := by
      have := (abs_le.1 h1).2
      have hE : (Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2 : ℝ) = E := rfl
      rw [hE] at this
      linarith
    calc bil (D.blow a G) x x / ((D.deg a * G.1 : ℕ) : ℝ)
        ≤ (∑ p, ∑ q, x p * B (D.grp a p) (D.grp a q) * x q + (2 * E + δ * N) * (x ⬝ᵥ x)) /
          ((D.deg a * G.1 : ℕ) : ℝ) := div_le_div_of_nonneg_right key hD.le
      _ = _ := by push_cast; ring
  · -- the planted form is at most `0`
    rw [sum_planted]
    refine div_nonpos_of_nonpos_of_nonneg (hneg _ fun l ↦ ?_) (by positivity)
    have := hx l
    simp only [dotProduct] at this
    rw [← this, ← sum_fiberwise univ (D.grp a)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun p hp ↦ by rw [(mem_filter.1 hp).2]

/-- **Few very negative eigenvalues**: at most `K` eigenvalues of the blow-up are below
`-2E / (d n)`. -/
theorem card_eig_blow_lt_neg_le (G : Graph) (hn : 0 < G.1) (hd : 0 < D.deg a) {w Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hw : ∀ τ, ∑ τ', |(D.W0 τ τ' : ℝ)| ≤ w)
    (hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ Δ) :
    (univ.filter fun i ↦ (D.blow a G).eig i <
      -(2 * (Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2) / (D.deg a * G.1))).card ≤ D.K := by
  set E := Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2
  have hD : (0 : ℝ) < (D.deg a * G.1 : ℕ) := by exact_mod_cast Nat.mul_pos hd hn
  refine card_eig_lt_neg_le (D.blow a G) (fun i p ↦ if D.grp a p = i then 1 else 0) _
    (fun x hx ↦ ?_)
  rw [(D.template a).quad_normAdj_blowup G x]
  have h1 := D.bil_blow_sub_le a G hΔ0 hw hΔ x x
  have h0 : ∑ p, ∑ q, x p * D.Chat (D.grp a p) (D.grp a q) * x q = 0 := by
    rw [sum_planted]
    refine sum_eq_zero fun i _ ↦ ?_
    have := hx i
    simp only [dotProduct, ite_mul, one_mul, zero_mul] at this
    rw [sum_ite, sum_const_zero, add_zero] at this
    rw [this]; simp
  rw [h0, sub_zero] at h1
  have h1' := (abs_le.1 h1).1
  have hE : (Fintype.card D.Ty * err a D.r * G.1 + w * Δ / 2 : ℝ) = E := rfl
  rw [hE] at h1'
  have key : -(2 * E) * (x ⬝ᵥ x) ≤ bil (D.blow a G) x x := by linarith
  calc -(2 * E / (D.deg a * G.1)) * (x ⬝ᵥ x) = -(2 * E) * (x ⬝ᵥ x) / ((D.deg a * G.1 : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ bil (D.blow a G) x x / ((D.deg a * G.1 : ℕ) : ℝ) := div_le_div_of_nonneg_right key hD.le

end Design

end BHSV25.Hard
