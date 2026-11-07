module

public import BHSV25.Hard.Spectral
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Blow-ups of templates

Every reduction of [BHSV25, Section 8] here builds its output graph `H` from the input graph `G`
of the gap problem of Bansal and Khot and a fixed finite **template** (`BHSV25.Hard.Template`):
`C` cells, a symmetric irreflexive `d`-regular adjacency `T` between cells, and a symmetric
integer matrix `W` with entries in `{-1, 0, 1}` and zero row sums, `-1` only on edges of `T` and
`1` only off them. The vertices of the **blow-up** `H` (`BHSV25.Hard.Template.blowup`) are the
pairs `(u, v)` of a cell `u` and a vertex `v` of `G`, and its adjacency matrix is
`T ⊗ J + W ⊗ A_G`: two vertices in cells with `W = 1` are adjacent when their vertices of `G`
are, in cells with `W = -1` when they are not, and otherwise when the cells are adjacent in `T`.

* `H` is exactly `d n`-regular (`BHSV25.Hard.Template.blowup_isRegular`), since the rows of `W`
  sum to `0`.
* If `T` is close to a matrix `P` in bilinear form (`|Xᵀ (T - P) Y| ≤ e (‖X‖² + ‖Y‖²)`), then the
  adjacency matrix of `H` is close to the blow-up of `P`, up to `e n + w Δ` for `G` of maximum
  degree `Δ` and rows of `W` of absolute sum at most `w`
  (`BHSV25.Hard.Template.bil_blowup_sub_le`).
-/

@[expose] public section

namespace BHSV25.Hard

open Matrix Finset

/-- The `0`-`1` indicator of a proposition, as a real number. -/
noncomputable def ind (P : Prop) : ℝ := by classical exact if P then 1 else 0

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem ind_of {P : Prop} (h : P) : ind P = 1 := by
  unfold ind; rw [ite_eq_left h]

theorem ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind; rw [ite_eq_right h]

/-- The bilinear form of the adjacency matrix of a graph. -/
noncomputable def bil (H : Graph) (x y : Fin H.1 → ℝ) : ℝ :=
  ∑ p, ∑ q, x p * ind (H.2.Adj p q) * y q

/-- A **template**: `C` cells, a symmetric irreflexive `d`-regular adjacency `T`, and a symmetric
correction `W` with entries in `{-1, 0, 1}` and zero row sums, `-1` only on edges of `T` and `1`
only off them. -/
structure Template where
  /-- The number of cells. -/
  C : ℕ
  /-- The adjacency between cells. -/
  T : Fin C → Fin C → Bool
  /-- The correction by the input graph. -/
  W : Fin C → Fin C → ℤ
  /-- The degree of `T`. -/
  d : ℕ
  T_symm : ∀ u u', T u u' = T u' u
  T_irrefl : ∀ u, T u u = false
  W_symm : ∀ u u', W u u' = W u' u
  W_cases : ∀ u u', W u u' = -1 ∨ W u u' = 0 ∨ W u u' = 1
  W_neg : ∀ u u', W u u' = -1 → T u u' = true
  W_pos : ∀ u u', W u u' = 1 → T u u' = false
  W_sum : ∀ u, ∑ u', W u u' = 0
  T_reg : ∀ u, (univ.filter fun u' ↦ T u u' = true).card = d

namespace Template

variable (Tm : Template)

/-- The adjacency of the blow-up, on pairs (cell, vertex of `G`). -/
def adj {n : ℕ} (G : SimpleGraph (Fin n)) (p q : Fin Tm.C × Fin n) : Prop :=
  if Tm.W p.1 q.1 = 1 then G.Adj p.2 q.2
  else if Tm.W p.1 q.1 = -1 then Tm.T p.1 q.1 = true ∧ ¬ G.Adj p.2 q.2
  else Tm.T p.1 q.1 = true

theorem adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) {p q : Fin Tm.C × Fin n}
    (h : Tm.adj G p q) : Tm.adj G q p := by
  unfold adj at *
  rw [Tm.W_symm q.1 p.1, Tm.T_symm q.1 p.1]
  split_ifs at h ⊢
  · exact h.symm
  · exact ⟨h.1, fun h' ↦ h.2 h'.symm⟩
  · exact h

theorem adj_irrefl {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin Tm.C × Fin n) :
    ¬ Tm.adj G p p := by
  unfold adj
  split_ifs
  · exact G.irrefl
  · simp [Tm.T_irrefl]
  · simp [Tm.T_irrefl]

/-- The blow-up of the template by the graph `G`: vertex `p` of `H` is the pair
`finProdFinEquiv.symm p` of a cell and a vertex of `G`. -/
abbrev blowup (G : Graph) : Graph :=
  ⟨Tm.C * G.1,
    { Adj := fun p q ↦ Tm.adj G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q)
      symm := ⟨fun _ _ h ↦ Tm.adj_symm G.2 h⟩
      loopless := ⟨fun _ ↦ Tm.adj_irrefl G.2 _⟩ }⟩

/-- The cell of a vertex of the blow-up. -/
def cell {n : ℕ} (p : Fin (Tm.C * n)) : Fin Tm.C := (finProdFinEquiv.symm p).1

/-- The vertex of `G` of a vertex of the blow-up. -/
def vtx {n : ℕ} (p : Fin (Tm.C * n)) : Fin n := (finProdFinEquiv.symm p).2

theorem blowup_adj (G : Graph) (p q : Fin (Tm.C * G.1)) :
    (Tm.blowup G).2.Adj p q ↔ Tm.adj G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q) :=
  Iff.rfl

/-- The adjacency of the blow-up is `T ⊗ J + W ⊗ A_G`. -/
theorem ind_adj {n : ℕ} (G : SimpleGraph (Fin n)) (p q : Fin Tm.C × Fin n) :
    ind (Tm.adj G p q) = ind (Tm.T p.1 q.1 = true) + (Tm.W p.1 q.1 : ℝ) * ind (G.Adj p.2 q.2) := by
  unfold adj
  rcases Tm.W_cases p.1 q.1 with h | h | h
  · have hT := Tm.W_neg _ _ h
    rw [ite_eq_right (by rw [h]; decide), ite_eq_left h, h, ind_of hT]
    by_cases hG : G.Adj p.2 q.2
    · rw [ind_of_not (fun h' ↦ h'.2 hG), ind_of hG]; norm_num
    · rw [ind_of ⟨hT, hG⟩, ind_of_not hG]; norm_num
  · rw [ite_eq_right (by rw [h]; decide), ite_eq_right (by rw [h]; decide), h]; simp
  · have hT := Tm.W_pos _ _ h
    rw [ite_eq_left h, h, ind_of_not (P := Tm.T p.1 q.1 = true) (by rw [hT]; decide)]; simp

/-! ### Regularity -/

theorem sum_ind_T (u : Fin Tm.C) : ∑ u', ind (Tm.T u u' = true) = Tm.d := by
  rw [← Tm.T_reg u, card_filter]
  push_cast
  exact sum_congr rfl fun u' _ ↦ by unfold ind; split_ifs <;> simp

/-- The degree of a vertex of the blow-up, as a sum over cells and vertices of `G`. -/
theorem sum_ind_adj {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin Tm.C × Fin n) :
    ∑ q : Fin Tm.C × Fin n, ind (Tm.adj G p q) = Tm.d * n := by
  classical
  simp_rw [ind_adj, sum_add_distrib, Fintype.sum_prod_type, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ x : Fin Tm.C, (n : ℝ) * ind (Tm.T p.1 x = true) = Tm.d * n := by
    rw [← mul_sum, sum_ind_T]; ring
  have h2 : ∑ x : Fin Tm.C, ∑ y : Fin n, (Tm.W p.1 x : ℝ) * ind (G.Adj p.2 y) = 0 := by
    simp_rw [← mul_sum]
    rw [← sum_mul]
    have : ∑ x, (Tm.W p.1 x : ℝ) = 0 := by exact_mod_cast Tm.W_sum p.1
    rw [this, zero_mul]
  rw [h1, h2, add_zero]

open Classical in
theorem blowup_degree (G : Graph) (p : Fin (Tm.blowup G).1) :
    (Tm.blowup G).2.degree p = Tm.d * G.1 := by
  have h := Tm.sum_ind_adj G.2 (finProdFinEquiv.symm p)
  rw [← Equiv.sum_comp finProdFinEquiv.symm] at h
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hc : ((univ.filter fun q ↦ (Tm.blowup G).2.Adj p q).card : ℝ) =
      ∑ q, ind (Tm.adj G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q)) := by
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun q _ ↦ ?_
    unfold ind
    by_cases hq : (Tm.blowup G).2.Adj p q
    · rw [ite_eq_left hq]
    · rw [ite_eq_right hq]
  exact_mod_cast hc.trans h

open Classical in
/-- **The blow-up is regular**, of degree `d n`. -/
theorem blowup_isRegular (G : Graph) :
    (Tm.blowup G).2.IsRegularOfDegree (Tm.d * G.1) :=
  fun p ↦ Tm.blowup_degree G p

/-! ### The bilinear form -/

/-- The bilinear form of the adjacency matrix of `G` is at most `Δ (‖a‖² + ‖b‖²) / 2`. -/
theorem abs_sum_adj_le {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ)
    (hΔ : ∀ v, ∑ v', ind (G.Adj v v') ≤ Δ) (a b : Fin n → ℝ) :
    |∑ v, ∑ v', a v * ind (G.Adj v v') * b v'| ≤ Δ * (a ⬝ᵥ a + b ⬝ᵥ b) / 2 := by
  have hterm : ∀ v v', |a v * ind (G.Adj v v') * b v'| ≤
      ind (G.Adj v v') * (a v ^ 2 + b v' ^ 2) / 2 := by
    intro v v'
    rw [abs_mul, abs_mul, abs_of_nonneg (ind_nonneg _)]
    have h := two_mul_le_add_sq |a v| |b v'|
    rw [sq_abs, sq_abs] at h
    have := ind_nonneg (G.Adj v v')
    nlinarith [abs_nonneg (a v), abs_nonneg (b v')]
  have hsym : ∀ v', ∑ v, ind (G.Adj v v') ≤ Δ := fun v' ↦ by
    simpa [G.adj_comm] using hΔ v'
  calc |∑ v, ∑ v', a v * ind (G.Adj v v') * b v'|
      ≤ ∑ v, ∑ v', ind (G.Adj v v') * (a v ^ 2 + b v' ^ 2) / 2 :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ ↦
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v' _ ↦ hterm v v'))
    _ = (∑ v, (∑ v', ind (G.Adj v v')) * a v ^ 2 +
          ∑ v', (∑ v, ind (G.Adj v v')) * b v' ^ 2) / 2 := by
        have e1 : ∀ v v', ind (G.Adj v v') * (a v ^ 2 + b v' ^ 2) / 2 =
            ind (G.Adj v v') * a v ^ 2 / 2 + ind (G.Adj v v') * b v' ^ 2 / 2 := fun v v' ↦ by
          ring
        simp_rw [e1, sum_add_distrib]
        rw [sum_comm (f := fun v v' ↦ ind (G.Adj v v') * b v' ^ 2 / 2), add_div]
        congr 1
        · rw [sum_div]; exact sum_congr rfl fun v _ ↦ by rw [sum_mul, sum_div]
        · rw [sum_div]; exact sum_congr rfl fun v' _ ↦ by rw [sum_mul, sum_div]
    _ ≤ (∑ v, Δ * a v ^ 2 + ∑ v', Δ * b v' ^ 2) / 2 := by
        gcongr with v _ v' _
        · exact hΔ v
        · exact hsym v'
    _ = Δ * (a ⬝ᵥ a + b ⬝ᵥ b) / 2 := by
        simp only [dotProduct, ← mul_sum, sq]; ring

/-- The sums of a vector over the cells. -/
def cellSum {n : ℕ} (x : Fin Tm.C × Fin n → ℝ) (u : Fin Tm.C) : ℝ := ∑ v, x (u, v)

theorem cellSum_sq_le {n : ℕ} (x : Fin Tm.C × Fin n → ℝ) :
    Tm.cellSum x ⬝ᵥ Tm.cellSum x ≤ n * ∑ p, x p ^ 2 := by
  simp only [dotProduct, cellSum, Fintype.sum_prod_type, mul_sum]
  refine sum_le_sum fun u _ ↦ ?_
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun v ↦ x (u, v))
  rw [card_univ, Fintype.card_fin] at h
  calc ∑ i, (∑ v, x (u, v)) * x (u, i) = (∑ v, x (u, v)) ^ 2 := by rw [← mul_sum, sq]
    _ ≤ _ := h.trans (le_of_eq (mul_sum _ _ _))

theorem sum_pairs {n : ℕ} (f : Fin Tm.C → Fin Tm.C → ℝ) (x y : Fin Tm.C × Fin n → ℝ) :
    ∑ p, ∑ q, x p * f p.1 q.1 * y q = ∑ u, ∑ u', Tm.cellSum x u * f u u' * Tm.cellSum y u' := by
  simp only [cellSum, Fintype.sum_prod_type, sum_mul, mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun u' _ ↦ ?_
  rw [sum_comm]

/-- **The blow-up is close to the blow-up of `P`**, on pairs (cell, vertex of `G`). -/
theorem sum_pairs_sub_le {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin Tm.C → Fin Tm.C → ℝ)
    {e w Δ : ℝ} (he : 0 ≤ e) (hΔ0 : 0 ≤ Δ)
    (hT : ∀ X Y : Fin Tm.C → ℝ, |∑ u, ∑ u', X u * (ind (Tm.T u u' = true) - P u u') * Y u'| ≤
      e * (X ⬝ᵥ X + Y ⬝ᵥ Y))
    (hw : ∀ u, ∑ u', |(Tm.W u u' : ℝ)| ≤ w) (hΔ : ∀ v, ∑ v', ind (G.Adj v v') ≤ Δ)
    (x y : Fin Tm.C × Fin n → ℝ) :
    |∑ p, ∑ q, x p * (ind (Tm.adj G p q) - P p.1 q.1) * y q| ≤
      (e * n + w * Δ / 2) * (∑ p, x p ^ 2 + ∑ q, y q ^ 2) := by
  have hsplit : ∑ p, ∑ q, x p * (ind (Tm.adj G p q) - P p.1 q.1) * y q =
      ∑ p, ∑ q, x p * (ind (Tm.T p.1 q.1 = true) - P p.1 q.1) * y q +
        ∑ u, ∑ u', (Tm.W u u' : ℝ) *
          ∑ v, ∑ v', x (u, v) * ind (G.Adj v v') * y (u', v') := by
    have hpt : ∀ p q : Fin Tm.C × Fin n, x p * (ind (Tm.adj G p q) - P p.1 q.1) * y q =
        x p * (ind (Tm.T p.1 q.1 = true) - P p.1 q.1) * y q +
          (Tm.W p.1 q.1 : ℝ) * (x p * ind (G.Adj p.2 q.2) * y q) := fun p q ↦ by
      rw [ind_adj]; ring
    simp_rw [hpt, sum_add_distrib]
    congr 1
    simp only [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [sum_comm]
  rw [hsplit, Tm.sum_pairs (fun u u' ↦ ind (Tm.T u u' = true) - P u u')]
  have h1 := hT (Tm.cellSum x) (Tm.cellSum y)
  have hx := Tm.cellSum_sq_le x
  have hy := Tm.cellSum_sq_le y
  have h2 : |∑ u, ∑ u', (Tm.W u u' : ℝ) * ∑ v, ∑ v', x (u, v) * ind (G.Adj v v') * y (u', v')|
      ≤ w * Δ / 2 * (∑ p, x p ^ 2 + ∑ q, y q ^ 2) := by
    have hterm : ∀ u u', |(Tm.W u u' : ℝ) *
        ∑ v, ∑ v', x (u, v) * ind (G.Adj v v') * y (u', v')| ≤
        |(Tm.W u u' : ℝ)| * (Δ / 2) * (∑ v, x (u, v) ^ 2 + ∑ v, y (u', v) ^ 2) := by
      intro u u'
      rw [abs_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_sum_adj_le G Δ hΔ (fun v ↦ x (u, v)) (fun v ↦ y (u', v))
      simp only [dotProduct, ← sq] at this
      linarith
    have hwsym : ∀ u', ∑ u, |(Tm.W u u' : ℝ)| ≤ w := fun u' ↦ by
      simpa [Tm.W_symm] using hw u'
    set sx : Fin Tm.C → ℝ := fun u ↦ ∑ v, x (u, v) ^ 2 with hsx
    set sy : Fin Tm.C → ℝ := fun u ↦ ∑ v, y (u, v) ^ 2 with hsy
    calc _ ≤ ∑ u, ∑ u', |(Tm.W u u' : ℝ)| * (Δ / 2) * (sx u + sy u') :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ ↦
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u' _ ↦ hterm u u'))
      _ = (Δ / 2) * (∑ u, (∑ u', |(Tm.W u u' : ℝ)|) * sx u +
            ∑ u', (∑ u, |(Tm.W u u' : ℝ)|) * sy u') := by
          have hpt : ∀ u u', |(Tm.W u u' : ℝ)| * (Δ / 2) * (sx u + sy u') =
              (Δ / 2) * (|(Tm.W u u' : ℝ)| * sx u) + (Δ / 2) * (|(Tm.W u u' : ℝ)| * sy u') :=
            fun u u' ↦ by ring
          simp_rw [hpt, sum_add_distrib, ← mul_sum]
          rw [sum_comm (f := fun u u' ↦ |(Tm.W u u' : ℝ)| * sy u'), mul_add]
          simp_rw [sum_mul]
      _ ≤ (Δ / 2) * (∑ u, w * sx u + ∑ u', w * sy u') := by
          have hsx0 : ∀ u, 0 ≤ sx u := fun u ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
          have hsy0 : ∀ u, 0 ≤ sy u := fun u ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
          gcongr with u _ u' _
          · exact hw u
          · exact hwsym u'
      _ = w * Δ / 2 * (∑ p, x p ^ 2 + ∑ q, y q ^ 2) := by
          simp only [hsx, hsy, Fintype.sum_prod_type, ← mul_sum]; ring
  calc _ ≤ |∑ u, ∑ u', Tm.cellSum x u * (ind (Tm.T u u' = true) - P u u') * Tm.cellSum y u'| +
        |∑ u, ∑ u', (Tm.W u u' : ℝ) * ∑ v, ∑ v', x (u, v) * ind (G.Adj v v') * y (u', v')| :=
        abs_add_le _ _
    _ ≤ e * (n * ∑ p, x p ^ 2 + n * ∑ q, y q ^ 2) + w * Δ / 2 * (∑ p, x p ^ 2 + ∑ q, y q ^ 2) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left (add_le_add hx hy) he)
    _ = (e * n + w * Δ / 2) * (∑ p, x p ^ 2 + ∑ q, y q ^ 2) := by ring

/-- **The blow-up is close to the blow-up of `P`**: `|xᵀ (A_H - P ⊗ J) y| ≤
(e n + w Δ / 2) (‖x‖² + ‖y‖²)`. -/
theorem bil_blowup_sub_le (G : Graph) (P : Fin Tm.C → Fin Tm.C → ℝ)
    {e w Δ : ℝ} (he : 0 ≤ e) (hΔ0 : 0 ≤ Δ)
    (hT : ∀ X Y : Fin Tm.C → ℝ, |∑ u, ∑ u', X u * (ind (Tm.T u u' = true) - P u u') * Y u'| ≤
      e * (X ⬝ᵥ X + Y ⬝ᵥ Y))
    (hw : ∀ u, ∑ u', |(Tm.W u u' : ℝ)| ≤ w) (hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ Δ)
    (x y : Fin (Tm.blowup G).1 → ℝ) :
    |bil (Tm.blowup G) x y - ∑ p, ∑ q, x p * P (Tm.cell p) (Tm.cell q) * y q| ≤
      (e * G.1 + w * Δ / 2) * (x ⬝ᵥ x + y ⬝ᵥ y) := by
  have h := Tm.sum_pairs_sub_le G.2 P he hΔ0 hT hw hΔ (fun a ↦ x (finProdFinEquiv a))
    (fun a ↦ y (finProdFinEquiv a))
  have e1 : bil (Tm.blowup G) x y - ∑ p, ∑ q, x p * P (Tm.cell p) (Tm.cell q) * y q =
      ∑ a, ∑ b, x (finProdFinEquiv a) * (ind (Tm.adj G.2 a b) - P a.1 b.1) *
        y (finProdFinEquiv b) := by
    unfold bil
    rw [← sum_sub_distrib]
    refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun p ↦ ?_
    rw [← sum_sub_distrib]
    refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun q ↦ ?_
    simp only [cell, Equiv.apply_symm_apply]
    rw [show ind ((Tm.blowup G).2.Adj p q) =
      ind (Tm.adj G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q)) from rfl]
    ring
  have e2 : ∀ z : Fin (Tm.blowup G).1 → ℝ, ∑ a, z (finProdFinEquiv a) ^ 2 = z ⬝ᵥ z := by
    intro z
    rw [Equiv.sum_comp finProdFinEquiv (fun p ↦ z p ^ 2)]
    simp [dotProduct, sq]
  rw [e1]
  rw [e2 x, e2 y] at h
  exact h

/-- The quadratic form of the normalized adjacency matrix of the blow-up. -/
theorem quad_normAdj_blowup (G : Graph) (x : Fin (Tm.blowup G).1 → ℝ) :
    x ⬝ᵥ ((Tm.blowup G).normAdj *ᵥ x) = bil (Tm.blowup G) x x / (Tm.d * G.1 : ℕ) := by
  classical
  have hreg := Tm.blowup_isRegular G
  simp only [dotProduct, mulVec, Graph.normAdj_of_isRegularOfDegree _ hreg, bil, sum_div,
    mul_sum]
  refine sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ ?_
  unfold ind
  split_ifs
  · simp only [div_eq_mul_inv]; ring
  · simp

end Template

end BHSV25.Hard
