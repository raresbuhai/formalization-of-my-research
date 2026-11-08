module

public import BHJK25.RS.Planted.Cells
public import BHJK25.RS.Planted.Collide
public import BHJK25.RS.Planted.Noise
public import BHJK25.RS.Planted.Relabel

/-!
# Clean unique columns make the noisy planted tensor accepted

Write the noisy tensor as `encode ω` with the entries flipped by a pattern `e`
(`BHJK25.RS.PlantedAux.flipBy`); the noise flips each entry independently with probability `ε/2`
(`BHJK25.RS.PlantedAux.flipW`). A column `v` of the layout is *clean* when `e` flips none of its
`2r` cells; then the guess `layout` reads `α_v` and `β_v` at `v`. If moreover `α_v` is unique
among the columns, `β_v = p(α_v)` for the planted polynomial `p = Σ xᵢ Xⁱ`, and these `α_v` are
distinct. So the noisy tensor is accepted as soon as `#clean ≥ #repeated + (W + 1)`, and the
probability that it is accepted is at least `1 - Pr_e[#clean < 3t] - Pr_α[#repeated ≥ 2t]`.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset

variable {k T n : ℕ}

/-- The columns of the layout. -/
def cols (h : 2 * (k - 1) * ell k T n < n) : Finset (Fin n) :=
  univ.filter fun v ↦ ∀ s b t, layout h s b t ≠ v

theorem mem_cols {h : 2 * (k - 1) * ell k T n < n} {v : Fin n} :
    v ∈ cols h ↔ IsCol (layout h) v := by
  simp [cols, IsCol]

/-- The tensor `X` with the entries flipped where `e` is `true`. -/
def flipBy (X e : Tensor k n) : Tensor k n := fun S ↦ xor (X S) (e S)

/-- Flipping by a pattern, as an equivalence of patterns and tensors. -/
def flipEquiv (X : Tensor k n) : Tensor k n ≃ Tensor k n where
  toFun := flipBy X
  invFun := flipBy X
  left_inv e := by
    funext S
    simp only [flipBy]
    cases X S <;> cases e S <;> rfl
  right_inv e := by
    funext S
    simp only [flipBy]
    cases X S <;> cases e S <;> rfl

/-- The noise turns `X` into `X` flipped by `e` with the probability of the pattern `e`. -/
theorem noiseMass_flip (ε : ℝ) (X e : Tensor k n) :
    noiseMass ε X (flipBy X e) = flipW (ε / 2) e := by
  unfold noiseMass flipW flipBy
  refine prod_congr rfl fun S _ ↦ ?_
  cases X S <;> cases e S <;> simp

/-- The columns of the layout none of whose cells is flipped by `e`. -/
def cleanCols (h : 2 * (k - 1) * ell k T n < n) (e : Tensor k n) : Finset (Fin n) :=
  (cols h).filter fun v ↦ ∀ S ∈ cellSet (layout h) v, e S = false

theorem readAt_flip_of_clean (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) {v : Fin n}
    (hv : IsCol (layout h) v) (X e : Tensor k n) (hcl : ∀ S ∈ cellSet (layout h) v, e S = false)
    (s : Fin 2) (i : Fin (rbits T n)) :
    readAt (flipBy X e) (cell (layout h) s v i) = readAt X (cell (layout h) s v i) := by
  have hc := card_cell (by omega) (layout_valid h) hv s i
  rw [readAt, readAt, dite_eq_left hc, dite_eq_left hc, flipBy,
    hcl _ (mem_cellSet.2 ⟨s, i, rfl⟩), Bool.xor_false]

/-- At a clean column, the layout reads `α_v`. -/
theorem readElt_zero_flip (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    (e : Tensor k n) {v : Fin n} (hv : IsCol (layout h) v)
    (hcl : ∀ S ∈ cellSet (layout h) v, e S = false) :
    readElt (layout h) 0 (flipBy (encode h ω) e) v = ω.2.1 v := by
  unfold readElt
  have : (fun i : Fin (rbits T n) ↦ readAt (flipBy (encode h ω) e) (cell (layout h) 0 v i)) =
      (bitEquiv T n).symm (ω.2.1 v) := by
    funext i
    rw [readAt_flip_of_clean hk h hv _ _ hcl, readAt_encode_alpha hk h ω hv]
  rw [this]
  exact (bitEquiv T n).apply_symm_apply _

/-- At a clean column, the layout reads `β_v`. -/
theorem readElt_one_flip (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    (e : Tensor k n) {v : Fin n} (hv : IsCol (layout h) v)
    (hcl : ∀ S ∈ cellSet (layout h) v, e S = false) :
    readElt (layout h) 1 (flipBy (encode h ω) e) v = betaVal (layout h) ω v := by
  unfold readElt
  have : (fun i : Fin (rbits T n) ↦ readAt (flipBy (encode h ω) e) (cell (layout h) 1 v i)) =
      (bitEquiv T n).symm (betaVal (layout h) ω v) := by
    funext i
    rw [readAt_flip_of_clean hk h hv _ _ hcl, readAt_encode_beta hk h ω hv]
  rw [this]
  exact (bitEquiv T n).apply_symm_apply _

/-- **Acceptance**: if the clean columns outnumber the columns with a repeated `α_v` by the
threshold `W + 1`, the noisy planted tensor is accepted, with the layout and the planted
polynomial. -/
theorem accept_of_good (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    (e : Tensor k n) (hgood : (dupCols (cols h) ω.2.1).card + thr T n ≤ (cleanCols h e).card) :
    Accept k T n (flipBy (encode h ω) e) := by
  set p : Polynomial (Fld T n) :=
    ∑ i : Fin (mdeg T n), Polynomial.C (ω.1 i) * Polynomial.X ^ (i : ℕ) with hpdef
  have hp : p.natDegree < mdeg T n := by
    by_cases hp0 : p = 0
    · rw [hp0, Polynomial.natDegree_zero]
      exact mdeg_pos T n
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 (Polynomial.degree_sum_fin_lt _)
  refine ⟨layout h, layout_valid h, p, hp, ?_⟩
  set G := cleanCols h e \ dupCols (cols h) ω.2.1 with hGdef
  have hG : ∀ v ∈ G, IsCol (layout h) v ∧ (∀ S ∈ cellSet (layout h) v, e S = false) ∧
      UniqueCol (layout h) ω.2.1 v := by
    intro v hv
    simp only [hGdef, mem_sdiff, cleanCols, dupCols, mem_filter, mem_cols] at hv
    obtain ⟨⟨hvc, hcl⟩, hnd⟩ := hv
    exact ⟨hvc, hcl, fun w hw hwv hαw ↦ hnd ⟨hvc, w, hw, hwv, hαw⟩⟩
  have hinj : Set.InjOn ω.2.1 G := by
    intro v hv w hw hαvw
    by_contra hne
    exact (hG w hw).2.2 v (hG v hv).1 hne hαvw
  calc thr T n ≤ G.card := by
        have := le_card_sdiff (dupCols (cols h) ω.2.1) (cleanCols h e)
        rw [← hGdef] at this
        omega
    _ = (G.image ω.2.1).card := (card_image_of_injOn hinj).symm
    _ ≤ (agreeSet (layout h) (flipBy (encode h ω) e) p).card := by
        refine card_le_card fun x hx ↦ ?_
        obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
        obtain ⟨hvc, hcl, hU⟩ := hG v hv
        simp only [agreeSet, mem_filter, mem_univ, true_and]
        refine ⟨v, hvc, readElt_zero_flip hk h ω e hvc hcl, ?_⟩
        rw [readElt_one_flip hk h ω e hvc hcl, betaVal, ite_eq_left hU, hpdef,
          Polynomial.eval_finsetSum]
        simp

/-! ### The probability of acceptance -/

/-- The probability that the noise leaves fewer than `a` columns of the layout clean. -/
noncomputable def probFewClean (h : 2 * (k - 1) * ell k T n < n) (ε : ℝ) (a : ℕ) : ℝ :=
  ∑ e : Tensor k n, if (cleanCols h e).card < a then flipW (ε / 2) e else 0

/-- The probability that at least `b` columns of the layout have a repeated value `α_v`. -/
noncomputable def probManyDup (h : 2 * (k - 1) * ell k T n < n) (b : ℕ) : ℝ :=
  (Fintype.card (Fin n → Fld T n) : ℝ)⁻¹ *
    ∑ α : Fin n → Fld T n, if b ≤ (dupCols (cols h) α).card then 1 else 0

/-- Averaging a function of the middle coordinate. -/
theorem avg_snd_fst {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [Nonempty C] (f : B → ℝ) :
    (Fintype.card (A × B × C) : ℝ)⁻¹ * ∑ ω : A × B × C, f ω.2.1 =
      (Fintype.card B : ℝ)⁻¹ * ∑ b, f b := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [Fintype.card_prod, Fintype.card_prod]
  push_cast
  field_simp

/-- For one sample: the noisy `encode ω` is accepted with probability at least
`1 - Pr[few clean] - 1[many repeated]`. -/
theorem sum_accept_ge (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε2 : ε ≤ 2) [DecidablePred (Accept k T n)] (ω : Sample k T n) :
    1 - probFewClean h ε (3 * thr T n) -
        (if 2 * thr T n ≤ (dupCols (cols h) ω.2.1).card then 1 else 0) ≤
      ∑ M', (if Accept k T n M' then noiseMass ε (encode h ω) M' else 0) := by
  have hp0 : 0 ≤ ε / 2 := by linarith
  have hp1 : ε / 2 ≤ 1 := by linarith
  rw [← Equiv.sum_comp (flipEquiv (encode h ω))]
  simp only [flipEquiv, Equiv.coe_fn_mk, noiseMass_flip]
  set B : ℝ := if 2 * thr T n ≤ (dupCols (cols h) ω.2.1).card then 1 else 0 with hB
  calc 1 - probFewClean h ε (3 * thr T n) - B =
        ∑ e, (flipW (ε / 2) e -
          (if (cleanCols h e).card < 3 * thr T n then flipW (ε / 2) e else 0) -
          B * flipW (ε / 2) e) := by
        rw [sum_sub_distrib, sum_sub_distrib, sum_flipW, ← mul_sum, sum_flipW, mul_one,
          probFewClean]
    _ ≤ _ := by
        refine sum_le_sum fun e _ ↦ ?_
        have hw := flipW_nonneg hp0 hp1 e
        have hacc : 0 ≤ if Accept k T n (flipBy (encode h ω) e) then flipW (ε / 2) e else 0 := by
          split_ifs
          · exact hw
          · exact le_rfl
        by_cases hA : (cleanCols h e).card < 3 * thr T n
        · rw [ite_eq_left hA]
          have hB0 : 0 ≤ B := by rw [hB]; split_ifs <;> norm_num
          nlinarith
        · rw [ite_eq_right hA]
          by_cases hdup : 2 * thr T n ≤ (dupCols (cols h) ω.2.1).card
          · rw [hB, ite_eq_left hdup]
            linarith
          · rw [hB, ite_eq_right hdup, ite_eq_left (accept_of_good hk h ω e (by omega))]
            linarith

/-- **The probability of acceptance**: the noisy planted tensors `encode ω` are accepted with
average probability at least `1 - Pr_e[#clean < 3t] - Pr_α[#repeated ≥ 2t]`. -/
theorem accept_prob_ge (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε2 : ε ≤ 2) [DecidablePred (Accept k T n)] :
    1 - probFewClean h ε (3 * thr T n) - probManyDup h (2 * thr T n) ≤
      (Fintype.card (Sample k T n) : ℝ)⁻¹ * ∑ ω : Sample k T n,
        ∑ M', (if Accept k T n M' then noiseMass ε (encode h ω) M' else 0) := by
  have hΩ : (0 : ℝ) < Fintype.card (Sample k T n) := by exact_mod_cast Fintype.card_pos
  have havg := avg_snd_fst (A := Fin (mdeg T n) → Fld T n)
    (C := (Fin n → Fld T n) × Tensor k n)
    (fun α : Fin n → Fld T n ↦ if 2 * thr T n ≤ (dupCols (cols h) α).card then (1 : ℝ) else 0)
  calc 1 - probFewClean h ε (3 * thr T n) - probManyDup h (2 * thr T n) =
        (Fintype.card (Sample k T n) : ℝ)⁻¹ * ∑ ω : Sample k T n,
          (1 - probFewClean h ε (3 * thr T n) -
            (if 2 * thr T n ≤ (dupCols (cols h) ω.2.1).card then 1 else 0)) := by
        rw [sum_sub_distrib, mul_sub, probManyDup, ← havg, sum_const, card_univ, nsmul_eq_mul,
          ← mul_assoc, inv_mul_cancel₀ hΩ.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun ω _ ↦ sum_accept_ge hk h hε0 hε2 ω)
        (by positivity)

end BHJK25.RS.PlantedAux
