module

public import BHSV25.Spectral.Basic

/-!
# Variance of colorings in expanders

[BHSV25, Lemmas 6.1 and 7.4], for a partition `χ` of the vertices of a graph into parts indexed by
a finite type `ι`, in terms of the normalized adjacency matrix `Ã`.

* **Partitions** (`BHSV25.Alg.part`, `BHSV25.Alg.wt`, `BHSV25.Alg.intWt`, `BHSV25.Alg.pmodel`):
  the parts `V_a`, the weights `D_x(a) = ∑_{y ∈ V_a} Ã_xy`, the weight `∑_{χ x = χ y} Ã_xy` of the
  edges inside the parts, and the model `M_ab = 𝔼_{x ∈ V_a} D_x(b)` (`BHSV25.Graph.model`, for
  parts indexed by `ι`; `BHSV25.Alg.model_eq_pmodel`).
* **Lemma 6.1** (`BHSV25.Alg.disp_le`): in a regular graph with at most one eigenvalue above `L`,
  for `0 < L < 1`, the dispersion `∑_{x ∈ V_a} (D_x(b) - M_ab)²` is at most `I / L + L n`, where `I`
  is the weight of the edges inside the parts. The paper states it with `L` the second eigenvalue
  and `I ≤ 2 δ n`; its proof only uses `L` as an upper bound on the second eigenvalue, through
  `xᵀ Ã x ≤ (∑ x)² / n + L (‖x‖² - (∑ x)² / n)`.
* **The lift** (`BHSV25.Alg.lift`): `z ↦ (x ↦ z_{χ x} / √|V_{χ x}|)`, an isometry from `ℝ^ι` onto
  the vectors constant on the parts when no part is empty, which carries the symmetrized model
  `S_ab = ∑_{x ∈ V_a} D_x(b) / √(|V_a| |V_b|)` (`BHSV25.Alg.symModel`) to `Ã`:
  `⟨lift z, Ã lift z'⟩ = ⟨z, S z'⟩`. The paper writes `W = Z M B⁻¹ Zᵀ`; `S` is `B^{1/2} M B^{-1/2}`.
* **Lemma 7.4** (`BHSV25.Alg.dist_lift_single`): `‖Ã lift e_c - lift (S e_c)‖²` is the sum of the
  dispersions `∑_a ∑_{x ∈ V_a} (D_x(c) - M_ac)²` divided by `|V_c|`.
* **Few edges inside the parts**: if every edge inside a part has an endpoint in a set `S`, the
  weight inside the parts is at most `2 |S|` (`BHSV25.Alg.intWt_le_of_cover`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Matrix Finset

variable (G : Graph) {ι : Type*} [DecidableEq ι]

/-! ### Partitions -/

/-- The part `a` of a partition `χ`: the vertices `x` with `χ x = a`. -/
def part (χ : Fin G.1 → ι) (a : ι) : Finset (Fin G.1) := univ.filter (χ · = a)

/-- The weight `D_x(a) = ∑_{y ∈ V_a} Ã_xy` from the vertex `x` to the part `a`. -/
noncomputable def wt (χ : Fin G.1 → ι) (x : Fin G.1) (a : ι) : ℝ :=
  ∑ y ∈ part G χ a, G.normAdj x y

/-- The weight `∑_{χ x = χ y} Ã_xy` of the edges inside the parts. -/
noncomputable def intWt (χ : Fin G.1 → ι) : ℝ := ∑ x, wt G χ x (χ x)

/-- The model of `χ`: `M_ab = 𝔼_{x ∈ V_a} D_x(b)` (`0` if `V_a` is empty). -/
noncomputable def pmodel (χ : Fin G.1 → ι) (a b : ι) : ℝ :=
  (∑ x ∈ part G χ a, wt G χ x b) / (part G χ a).card

/-- The dispersion `∑_{x ∈ V_a} (D_x(b) - M_ab)²` of the weights to the part `b` over the part
`a`. -/
noncomputable def disp (χ : Fin G.1 → ι) (a b : ι) : ℝ :=
  ∑ x ∈ part G χ a, (wt G χ x b - pmodel G χ a b) ^ 2

/-- The lift `z ↦ (x ↦ z_{χ x} / √|V_{χ x}|)` of vectors indexed by the parts. -/
noncomputable def lift (χ : Fin G.1 → ι) (z : ι → ℝ) : Fin G.1 → ℝ :=
  fun x ↦ z (χ x) / Real.sqrt (part G χ (χ x)).card

/-- The symmetrized model `S_ab = ∑_{x ∈ V_a} D_x(b) / √(|V_a| |V_b|)`. -/
noncomputable def symModel (χ : Fin G.1 → ι) : Matrix ι ι ℝ :=
  fun a b ↦ (∑ x ∈ part G χ a, wt G χ x b) /
    Real.sqrt ((part G χ a).card * (part G χ b).card)

theorem model_eq_pmodel {k : ℕ} (χ : Fin G.1 → Fin k) : G.model χ = pmodel G χ := rfl

variable {G}

theorem mem_part {χ : Fin G.1 → ι} {a : ι} {x : Fin G.1} : x ∈ part G χ a ↔ χ x = a := by
  rw [part, mem_filter, and_iff_right (mem_univ _)]

theorem mem_part_self (χ : Fin G.1 → ι) (x : Fin G.1) : x ∈ part G χ (χ x) := mem_part.2 rfl

theorem card_part_pos (χ : Fin G.1 → ι) (x : Fin G.1) : 0 < (part G χ (χ x)).card :=
  card_pos.2 ⟨x, mem_part_self χ x⟩

/-- A sum over the vertices, grouped by parts. -/
theorem sum_part [Fintype ι] {M : Type*} [AddCommMonoid M] (χ : Fin G.1 → ι) (f : Fin G.1 → M) :
    ∑ a, ∑ x ∈ part G χ a, f x = ∑ x, f x :=
  Finset.sum_fiberwise univ χ f

theorem sum_card_part [Fintype ι] (χ : Fin G.1 → ι) : ∑ a, ((part G χ a).card : ℝ) = G.1 := by
  have := sum_part (G := G) χ (fun _ ↦ (1 : ℝ))
  simpa using this

theorem normAdj_symm (x y : Fin G.1) : G.normAdj x y = G.normAdj y x := by
  have := G.normAdj_isHermitian.apply x y
  simpa using this.symm

open Classical in
theorem sum_normAdj {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) (x : Fin G.1) :
    ∑ y, G.normAdj x y = 1 := by
  have := congrFun (G.normAdj_mulVec_one h hd) x
  simpa [mulVec, dotProduct] using this

theorem wt_nonneg (χ : Fin G.1 → ι) (x : Fin G.1) (a : ι) : 0 ≤ wt G χ x a :=
  sum_nonneg fun y _ ↦ G.normAdj_nonneg x y

open Classical in
theorem sum_wt [Fintype ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) (χ : Fin G.1 → ι)
    (x : Fin G.1) : ∑ a, wt G χ x a = 1 := by
  rw [← sum_normAdj h hd x]
  exact sum_part χ _

open Classical in
theorem wt_le_one [Finite ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) (x : Fin G.1) (a : ι) : wt G χ x a ≤ 1 := by
  have := Fintype.ofFinite ι
  rw [← sum_wt h hd χ x]
  exact single_le_sum (fun b _ ↦ wt_nonneg χ x b) (mem_univ a)

theorem pmodel_nonneg (χ : Fin G.1 → ι) (a b : ι) : 0 ≤ pmodel G χ a b :=
  div_nonneg (sum_nonneg fun x _ ↦ wt_nonneg χ x b) (Nat.cast_nonneg _)

open Classical in
theorem pmodel_le_one [Finite ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) (a b : ι) : pmodel G χ a b ≤ 1 := by
  rcases Nat.eq_zero_or_pos (part G χ a).card with h0 | hpos
  · simp [pmodel, h0]
  · rw [pmodel, div_le_one (by exact_mod_cast hpos)]
    calc ∑ x ∈ part G χ a, wt G χ x b ≤ ∑ _x ∈ part G χ a, (1 : ℝ) :=
          sum_le_sum fun x _ ↦ wt_le_one h hd χ x b
      _ = (part G χ a).card := by simp

/-- The weight between two parts, seen from either side. -/
theorem sum_wt_comm (χ : Fin G.1 → ι) (a b : ι) :
    ∑ x ∈ part G χ a, wt G χ x b = ∑ y ∈ part G χ b, wt G χ y a :=
  calc ∑ x ∈ part G χ a, wt G χ x b
      = ∑ x ∈ part G χ a, ∑ y ∈ part G χ b, G.normAdj y x :=
        sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ normAdj_symm x y
    _ = ∑ y ∈ part G χ b, ∑ x ∈ part G χ a, G.normAdj y x := Finset.sum_comm

theorem card_mul_pmodel (χ : Fin G.1 → ι) (a b : ι) :
    (part G χ a).card * pmodel G χ a b = ∑ x ∈ part G χ a, wt G χ x b := by
  rcases Nat.eq_zero_or_pos (part G χ a).card with h0 | hpos
  · rw [card_eq_zero.1 h0]
    simp
  · rw [pmodel, mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')]

open Classical in
/-- The weights to a part sum to its size: `∑_a |V_a| M_ab = |V_b|`. -/
theorem sum_card_mul_pmodel [Fintype ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (χ : Fin G.1 → ι) (b : ι) :
    ∑ a, (part G χ a).card * pmodel G χ a b = (part G χ b).card := by
  simp_rw [card_mul_pmodel]
  rw [sum_part χ (fun x ↦ wt G χ x b)]
  calc ∑ x, wt G χ x b = ∑ x, ∑ y ∈ part G χ b, G.normAdj y x :=
        sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ normAdj_symm x y
    _ = ∑ y ∈ part G χ b, ∑ x, G.normAdj y x := Finset.sum_comm
    _ = (part G χ b).card := by simp [sum_normAdj h hd]

open Classical in
/-- The rows of the model sum to `1`. -/
theorem sum_pmodel [Fintype ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) (χ : Fin G.1 → ι)
    (a : ι) (ha : (part G χ a).Nonempty) : ∑ b, pmodel G χ a b = 1 := by
  have hpos : (0 : ℝ) < (part G χ a).card := by exact_mod_cast ha.card_pos
  simp only [pmodel, ← sum_div]
  rw [sum_comm, div_eq_one_iff_eq hpos.ne']
  simp [sum_wt h hd]

/-! ### Lemma 6.1 -/

/-- The weight inside a part is at most the weight inside all parts. -/
theorem sum_wt_self_le_intWt (χ : Fin G.1 → ι) (a : ι) :
    ∑ x ∈ part G χ a, wt G χ x a ≤ intWt G χ := by
  rw [intWt]
  calc ∑ x ∈ part G χ a, wt G χ x a = ∑ x ∈ part G χ a, wt G χ x (χ x) :=
        sum_congr rfl fun x hx ↦ by rw [mem_part.1 hx]
    _ ≤ ∑ x, wt G χ x (χ x) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ ↦ wt_nonneg χ x _

theorem intWt_nonneg (χ : Fin G.1 → ι) : 0 ≤ intWt G χ :=
  sum_nonneg fun x _ ↦ wt_nonneg χ x _

/-- The weights to `b` minus their mean over the part `a` sum to `0`. -/
theorem sum_wt_sub_pmodel (χ : Fin G.1 → ι) (a b : ι) :
    ∑ x ∈ part G χ a, (wt G χ x b - pmodel G χ a b) = 0 := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_mul_pmodel, sub_self]

/-- The dispersion is at most the second moment. -/
theorem disp_le_sum_sq (χ : Fin G.1 → ι) (a b : ι) :
    disp G χ a b ≤ ∑ x ∈ part G χ a, wt G χ x b ^ 2 := by
  have h : ∀ x ∈ part G χ a, (wt G χ x b - pmodel G χ a b) ^ 2 =
      wt G χ x b ^ 2 - pmodel G χ a b * (wt G χ x b - pmodel G χ a b) -
        pmodel G χ a b * wt G χ x b := fun x _ ↦ by ring
  rw [disp, sum_congr rfl h, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
    sum_wt_sub_pmodel, mul_zero, sub_zero, ← mul_sum]
  have := mul_nonneg (pmodel_nonneg χ a b) (sum_nonneg fun x (_ : x ∈ part G χ a) ↦
    wt_nonneg (G := G) χ x b)
  linarith

/-- The indicator of a part. -/
noncomputable def ind (χ : Fin G.1 → ι) (b : ι) : Fin G.1 → ℝ := fun x ↦ if χ x = b then 1 else 0

/-- The weights to `b` minus their mean, on the part `a`, and `0` elsewhere. -/
noncomputable def dev (χ : Fin G.1 → ι) (a b : ι) : Fin G.1 → ℝ :=
  fun x ↦ if χ x = a then wt G χ x b - pmodel G χ a b else 0

theorem mulVec_ind (χ : Fin G.1 → ι) (b : ι) (x : Fin G.1) :
    (G.normAdj *ᵥ ind χ b) x = wt G χ x b := by
  simp only [mulVec, dotProduct, ind, mul_ite, mul_one, mul_zero, wt, part]
  rw [sum_filter]

theorem sum_ite_part {M : Type*} [AddCommMonoid M] (χ : Fin G.1 → ι) (a : ι) (f : Fin G.1 → M) :
    ∑ x, (if χ x = a then f x else 0) = ∑ x ∈ part G χ a, f x := by
  rw [part, sum_filter]

theorem dotProduct_symm_mulVec (u v : Fin G.1 → ℝ) :
    u ⬝ᵥ (G.normAdj *ᵥ v) = v ⬝ᵥ (G.normAdj *ᵥ u) := by
  simp only [dotProduct, mulVec, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by rw [normAdj_symm y x]; ring

open Classical in
/-- **[BHSV25, Lemma 6.1]** (variance of colorings in expanders), with an upper bound `L` on the
second eigenvalue: `∑_{x ∈ V_a} (D_x(b) - M_ab)² ≤ I / L + L n`, where `I` is the weight inside
the parts. -/
theorem disp_le [Finite ι] {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) {L : ℝ}
    (hL0 : 0 < L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1) (χ : Fin G.1 → ι) (a b : ι) :
    disp G χ a b ≤ intWt G χ / L + L * G.1 := by
  have hI := intWt_nonneg (G := G) χ
  have hIL : intWt G χ ≤ intWt G χ / L := by
    rw [le_div_iff₀ hL0]
    nlinarith
  have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have hLn : 0 ≤ L * G.1 := mul_nonneg hL0.le hn
  by_cases hab : a = b
  · subst hab
    calc disp G χ a a ≤ ∑ x ∈ part G χ a, wt G χ x a ^ 2 := disp_le_sum_sq χ a a
      _ ≤ ∑ x ∈ part G χ a, wt G χ x a := sum_le_sum fun x _ ↦ by
          have h0 := wt_nonneg χ x a
          have h1 := wt_le_one h hd χ x a
          nlinarith
      _ ≤ intWt G χ := sum_wt_self_le_intWt χ a
      _ ≤ intWt G χ / L + L * G.1 := by linarith
  -- the test vector `v = f + L g`
  set f := dev (G := G) χ a b with hf
  set g := ind (G := G) χ b with hg
  set D := disp G χ a b with hD
  set sb : ℝ := ((part G χ b).card : ℝ) with hsb
  set Ia := ∑ x ∈ part G χ a, wt G χ x a with hIa
  have hsbn : sb ≤ G.1 := by
    rw [hsb]
    exact_mod_cast (card_le_univ _).trans (by simp)
  have hsb0 : 0 ≤ sb := Nat.cast_nonneg _
  -- the needed facts
  have hsumf : ∑ x, f x = 0 := by
    rw [hf]
    simp only [dev]
    rw [sum_ite_part, sum_wt_sub_pmodel]
  have hsumg : ∑ x, g x = sb := by
    simp only [hg, ind, Finset.sum_boole]
    rfl
  have hff : f ⬝ᵥ f = D := by
    have e : ∀ x, f x * f x = if χ x = a then (wt G χ x b - pmodel G χ a b) ^ 2 else 0 := by
      intro x
      simp only [hf, dev]
      split_ifs <;> ring
    simp only [dotProduct, e]
    exact sum_ite_part χ a _
  have hfg : f ⬝ᵥ g = 0 := by
    refine sum_eq_zero fun x _ ↦ ?_
    simp only [hf, hg, dev, ind]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hab
    · ring
    · ring
    · ring
  have hgg : g ⬝ᵥ g = sb := by
    have e : ∀ x, g x * g x = if χ x = b then 1 else 0 := by
      intro x
      simp only [hg, ind]
      split_ifs <;> ring
    simp only [dotProduct, e, Finset.sum_boole]
    rfl
  have hfAg : f ⬝ᵥ (G.normAdj *ᵥ g) = D := by
    simp only [dotProduct, hg, mulVec_ind, hf, dev, ite_mul, zero_mul]
    rw [sum_ite_part, hD, disp]
    have h2 : ∀ x ∈ part G χ a, (wt G χ x b - pmodel G χ a b) * wt G χ x b =
        (wt G χ x b - pmodel G χ a b) ^ 2 + pmodel G χ a b * (wt G χ x b - pmodel G χ a b) :=
      fun x _ ↦ by ring
    rw [sum_congr rfl h2, sum_add_distrib, ← mul_sum, sum_wt_sub_pmodel, mul_zero, add_zero]
  have hgAg : 0 ≤ g ⬝ᵥ (G.normAdj *ᵥ g) := by
    refine sum_nonneg fun x _ ↦ mul_nonneg ?_ ?_
    · simp only [hg, ind]
      split_ifs <;> norm_num
    · rw [hg, mulVec_ind]
      exact wt_nonneg χ x b
  have hfAf : -Ia ≤ f ⬝ᵥ (G.normAdj *ᵥ f) := by
    have hterm : ∀ x y, -(if χ x = a then (if χ y = a then G.normAdj x y else 0) else 0) ≤
        f x * (G.normAdj x y * f y) := by
      intro x y
      have hA := G.normAdj_nonneg x y
      simp only [hf, dev]
      split_ifs with h1 h2 h2
      · have e1 := abs_sub_le_of_nonneg_of_le (wt_nonneg χ x b) (wt_le_one h hd χ x b)
          (pmodel_nonneg χ a b) (pmodel_le_one h hd χ a b)
        have e2 := abs_sub_le_of_nonneg_of_le (wt_nonneg χ y b) (wt_le_one h hd χ y b)
          (pmodel_nonneg χ a b) (pmodel_le_one h hd χ a b)
        have e3 : -1 ≤ (wt G χ x b - pmodel G χ a b) * (wt G χ y b - pmodel G χ a b) := by
          have := abs_mul (wt G χ x b - pmodel G χ a b) (wt G χ y b - pmodel G χ a b)
          have := neg_abs_le ((wt G χ x b - pmodel G χ a b) * (wt G χ y b - pmodel G χ a b))
          have : |wt G χ x b - pmodel G χ a b| * |wt G χ y b - pmodel G χ a b| ≤ 1 * 1 :=
            mul_le_mul e1 e2 (abs_nonneg _) zero_le_one
          linarith
        nlinarith
      · simp
      · simp
      · simp
    have hsum : ∑ x, ∑ y, (if χ x = a then (if χ y = a then G.normAdj x y else 0) else 0) =
        Ia := by
      have e : ∀ x, ∑ y, (if χ x = a then (if χ y = a then G.normAdj x y else 0) else 0) =
          if χ x = a then wt G χ x a else 0 := fun x ↦ by
        split_ifs
        · exact sum_ite_part χ a (fun y ↦ G.normAdj x y)
        · simp
      exact (sum_congr rfl fun x _ ↦ e x).trans (sum_ite_part χ a _)
    simp only [dotProduct, mulVec, mul_sum]
    rw [← hsum, ← sum_neg_distrib]
    exact sum_le_sum fun x _ ↦ by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun y _ ↦ hterm x y
  have hIaI : Ia ≤ intWt G χ := sum_wt_self_le_intWt χ a
  -- the quadratic form of `v`
  set v := f + L • g with hv
  have hquad : v ⬝ᵥ (G.normAdj *ᵥ v) = f ⬝ᵥ (G.normAdj *ᵥ f) + 2 * L * D +
      L ^ 2 * (g ⬝ᵥ (G.normAdj *ᵥ g)) := by
    have hsym : g ⬝ᵥ (G.normAdj *ᵥ f) = f ⬝ᵥ (G.normAdj *ᵥ g) := dotProduct_symm_mulVec g f
    rw [hv, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hsym, hfAg]
    simp only [smul_eq_mul]
    ring
  have hsumv : ∑ x, v x = L * sb := by
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hsumf,
      hsumg, zero_add]
  have hvv : v ⬝ᵥ v = D + L ^ 2 * sb := by
    rw [hv, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, hff, hfg, dotProduct_comm g f, hfg, hgg]
    simp only [smul_eq_mul]
    ring
  have hup := G.quad_le_of_numEigGT_le_one h hd hL0.le hL1 hexp v
  rw [hquad, hsumv, hvv] at hup
  -- `(L sb)² / n ≤ L² sb`
  have hfrac : (L * sb) ^ 2 / G.1 ≤ L ^ 2 * sb := by
    rcases hn.lt_or_eq with hpos | h0
    · rw [div_le_iff₀ hpos]
      have : sb * sb ≤ sb * G.1 := mul_le_mul_of_nonneg_left hsbn hsb0
      nlinarith [sq_nonneg L]
    · rw [← h0, div_zero]
      positivity
  have hfrac0 : 0 ≤ (L * sb) ^ 2 / G.1 := by positivity
  have key : L * D ≤ Ia + L ^ 2 * sb := by
    have h1 : (1 - L) * ((L * sb) ^ 2 / G.1) ≤ (1 - L) * (L ^ 2 * sb) :=
      mul_le_mul_of_nonneg_left hfrac (by linarith)
    nlinarith
  have hD' : D ≤ Ia / L + L * sb := by
    rw [div_add' _ _ _ hL0.ne', le_div_iff₀ hL0]
    nlinarith
  have : Ia / L ≤ intWt G χ / L := div_le_div_of_nonneg_right hIaI hL0.le
  have : L * sb ≤ L * G.1 := mul_le_mul_of_nonneg_left hsbn hL0.le
  linarith

/-! ### Few edges inside the parts -/

open Classical in
/-- If every edge inside a part has an endpoint in `S`, the weight inside the parts is at most
`2 |S|`. -/
theorem intWt_le_of_cover {d : ℕ} (h : G.2.IsRegularOfDegree d) (χ : Fin G.1 → ι)
    (S : Finset (Fin G.1)) (hS : ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ S ∨ v ∈ S) :
    intWt G χ ≤ 2 * S.card := by
  rcases eq_or_ne d 0 with hd | hd
  · have h0 : ∀ x y, G.normAdj x y = 0 := fun x y ↦ by
      rw [G.normAdj_of_isRegularOfDegree h]
      subst hd
      split_ifs <;> simp
    have : intWt G χ = 0 := by simp [intWt, wt, h0]
    rw [this]
    positivity
  have hterm : ∀ x y, (if χ y = χ x then G.normAdj x y else 0) ≤
      (if x ∈ S then G.normAdj x y else 0) + (if y ∈ S then G.normAdj x y else 0) := by
    intro x y
    have hA := G.normAdj_nonneg x y
    by_cases hadj : G.2.Adj x y
    · split_ifs with h1 h2 h3 h3 <;> try linarith
      rcases hS x y hadj h1.symm with h4 | h4
      · exact absurd h4 h2
      · exact absurd h4 h3
    · rw [G.normAdj_of_isRegularOfDegree h, ite_eq_right hadj]
      split_ifs <;> simp
  have hrow : ∀ x, ∑ y, G.normAdj x y = 1 := sum_normAdj h hd
  calc intWt G χ = ∑ x, ∑ y, (if χ y = χ x then G.normAdj x y else 0) := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [wt, sum_ite_part]
    _ ≤ ∑ x, ∑ y, ((if x ∈ S then G.normAdj x y else 0) +
          (if y ∈ S then G.normAdj x y else 0)) :=
        sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ hterm x y
    _ = 2 * S.card := by
        have e1 : ∀ x, ∑ y, (if x ∈ S then G.normAdj x y else 0) = if x ∈ S then 1 else 0 :=
          fun x ↦ by split_ifs <;> simp [hrow]
        have e2 : ∀ y, ∑ x, (if y ∈ S then G.normAdj x y else 0) = if y ∈ S then 1 else 0 := by
          intro y
          split_ifs
          · simp_rw [normAdj_symm _ y]
            exact hrow y
          · simp
        rw [sum_congr rfl fun x _ ↦ sum_add_distrib, sum_add_distrib, sum_congr rfl fun x _ ↦ e1 x,
          sum_comm, sum_congr rfl fun y _ ↦ e2 y, sum_boole]
        simp only [filter_mem_eq_inter, univ_inter]
        ring

/-! ### The lift -/

theorem lift_apply (χ : Fin G.1 → ι) (z : ι → ℝ) (x : Fin G.1) :
    lift G χ z x = z (χ x) / Real.sqrt (part G χ (χ x)).card := rfl

theorem lift_add (χ : Fin G.1 → ι) (z z' : ι → ℝ) : lift G χ (z + z') = lift G χ z + lift G χ z' :=
  funext fun x ↦ by simp [lift, add_div]

theorem lift_sub (χ : Fin G.1 → ι) (z z' : ι → ℝ) : lift G χ (z - z') = lift G χ z - lift G χ z' :=
  funext fun x ↦ by simp [lift, sub_div]

theorem lift_smul (χ : Fin G.1 → ι) (c : ℝ) (z : ι → ℝ) : lift G χ (c • z) = c • lift G χ z :=
  funext fun x ↦ by simp [lift, mul_div_assoc]

theorem lift_sum {κ : Type*} (χ : Fin G.1 → ι) (s : Finset κ) (z : κ → ι → ℝ) :
    lift G χ (∑ j ∈ s, z j) = ∑ j ∈ s, lift G χ (z j) :=
  funext fun x ↦ by simp [lift, sum_div]

theorem sqrt_card_part_mul_self (χ : Fin G.1 → ι) (x : Fin G.1) :
    Real.sqrt (part G χ (χ x)).card * Real.sqrt (part G χ (χ x)).card =
      (part G χ (χ x)).card :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

theorem sqrt_card_part_pos (χ : Fin G.1 → ι) (x : Fin G.1) :
    0 < Real.sqrt (part G χ (χ x)).card :=
  Real.sqrt_pos.2 (by exact_mod_cast card_part_pos χ x)

/-- **The lift is an isometry** when no part is empty. -/
theorem lift_dotProduct_lift [Fintype ι] (χ : Fin G.1 → ι) (hne : ∀ a, (part G χ a).Nonempty)
    (z z' : ι → ℝ) : lift G χ z ⬝ᵥ lift G χ z' = z ⬝ᵥ z' := by
  simp only [dotProduct, lift_apply]
  rw [← sum_part χ]
  refine sum_congr rfl fun a _ ↦ ?_
  have hpos : (0 : ℝ) < (part G χ a).card := by exact_mod_cast (hne a).card_pos
  have hs := Real.mul_self_sqrt hpos.le
  have hs0 := Real.sqrt_pos.2 hpos
  calc ∑ x ∈ part G χ a, z (χ x) / Real.sqrt (part G χ (χ x)).card *
        (z' (χ x) / Real.sqrt (part G χ (χ x)).card)
      = ∑ _x ∈ part G χ a, z a * z' a / (part G χ a).card := by
        refine sum_congr rfl fun x hx ↦ ?_
        rw [mem_part.1 hx, div_mul_div_comm, hs]
    _ = z a * z' a := by
        rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']

theorem sqrt_mul_card (χ : Fin G.1 → ι) (a b : ι) :
    Real.sqrt ((part G χ a).card * (part G χ b).card) =
      Real.sqrt (part G χ a).card * Real.sqrt (part G χ b).card :=
  Real.sqrt_mul (Nat.cast_nonneg _) _

/-- A double sum over the vertices, grouped by parts. -/
theorem sum_sum_part [Fintype ι] (χ : Fin G.1 → ι) (F : Fin G.1 → Fin G.1 → ℝ) :
    ∑ x, ∑ y, F x y = ∑ a, ∑ b, ∑ x ∈ part G χ a, ∑ y ∈ part G χ b, F x y := by
  rw [← sum_part χ]
  refine sum_congr rfl fun a _ ↦ ?_
  calc ∑ x ∈ part G χ a, ∑ y, F x y = ∑ x ∈ part G χ a, ∑ b, ∑ y ∈ part G χ b, F x y :=
        sum_congr rfl fun x _ ↦ (sum_part χ (F x)).symm
    _ = ∑ b, ∑ x ∈ part G χ a, ∑ y ∈ part G χ b, F x y := Finset.sum_comm

/-- **The lift carries the symmetrized model to `Ã`**: `⟨lift z, Ã lift z'⟩ = ⟨z, S z'⟩`. -/
theorem lift_dotProduct_mulVec_lift [Fintype ι] (χ : Fin G.1 → ι) (z z' : ι → ℝ) :
    lift G χ z ⬝ᵥ (G.normAdj *ᵥ lift G χ z') = z ⬝ᵥ (symModel G χ *ᵥ z') := by
  have hL : lift G χ z ⬝ᵥ (G.normAdj *ᵥ lift G χ z') =
      ∑ x, ∑ y, lift G χ z x * (G.normAdj x y * lift G χ z' y) := by
    simp only [dotProduct, mulVec, mul_sum]
  rw [hL, sum_sum_part χ]
  simp only [dotProduct, mulVec, mul_sum]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
  have hR : ∀ x ∈ part G χ a, ∀ y ∈ part G χ b,
      lift G χ z x * (G.normAdj x y * lift G χ z' y) =
      z a * z' b / Real.sqrt ((part G χ a).card * (part G χ b).card) * G.normAdj x y := by
    intro x hx y hy
    rw [lift_apply, lift_apply, mem_part.1 hx, mem_part.1 hy, sqrt_mul_card]
    field_simp
  rw [sum_congr rfl fun x hx ↦ sum_congr rfl (hR x hx)]
  simp only [← mul_sum]
  rw [symModel]
  simp only [wt]
  ring

theorem symModel_isHermitian (χ : Fin G.1 → ι) : (symModel G χ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b ↦ ?_
  simp only [symModel, star_trivial]
  rw [sum_wt_comm χ b a, mul_comm ((part G χ b).card : ℝ)]

theorem lift_single (χ : Fin G.1 → ι) (c : ι) (y : Fin G.1) :
    lift G χ (Pi.single c 1) y = if χ y = c then 1 / Real.sqrt (part G χ c).card else 0 := by
  rw [lift_apply]
  by_cases hy : χ y = c
  · rw [hy, Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne hy, ite_eq_right hy, zero_div]

theorem mulVec_lift_single (χ : Fin G.1 → ι) (c : ι) (x : Fin G.1) :
    (G.normAdj *ᵥ lift G χ (Pi.single c 1)) x = wt G χ x c / Real.sqrt (part G χ c).card := by
  simp only [mulVec, dotProduct, lift_single, mul_ite, mul_zero, wt, sum_div]
  rw [sum_ite_part]
  exact sum_congr rfl fun y _ ↦ by ring

theorem lift_symModel_single [Fintype ι] (χ : Fin G.1 → ι) (c : ι) (x : Fin G.1) :
    lift G χ (symModel G χ *ᵥ Pi.single c 1) x =
      pmodel G χ (χ x) c / Real.sqrt (part G χ c).card := by
  have hpos' : (0 : ℝ) < (part G χ (χ x)).card := by exact_mod_cast card_part_pos χ x
  have hs := sqrt_card_part_mul_self χ x
  have hs0 := sqrt_card_part_pos χ x
  rw [lift_apply, mulVec_single_one, Matrix.col_apply, symModel, sqrt_mul_card, pmodel]
  rcases Nat.eq_zero_or_pos (part G χ c).card with h0 | hc
  · simp [h0]
  have hc' : (0 : ℝ) < Real.sqrt (part G χ c).card := Real.sqrt_pos.2 (by exact_mod_cast hc)
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- **[BHSV25, Lemma 7.4]** (small variance implies close indicators):
`‖Ã lift e_c - lift (S e_c)‖² = (∑_a ∑_{x ∈ V_a} (D_x(c) - M_ac)²) / |V_c|`. -/
theorem dist_lift_single [Fintype ι] (χ : Fin G.1 → ι) (c : ι) :
    (G.normAdj *ᵥ lift G χ (Pi.single c 1) - lift G χ (symModel G χ *ᵥ Pi.single c 1)) ⬝ᵥ
      (G.normAdj *ᵥ lift G χ (Pi.single c 1) - lift G χ (symModel G χ *ᵥ Pi.single c 1)) =
    (∑ a, disp G χ a c) / (part G χ c).card := by
  have hval : ∀ x, (G.normAdj *ᵥ lift G χ (Pi.single c 1) -
      lift G χ (symModel G χ *ᵥ Pi.single c 1)) x =
      (wt G χ x c - pmodel G χ (χ x) c) / Real.sqrt (part G χ c).card := by
    intro x
    rw [Pi.sub_apply, mulVec_lift_single, lift_symModel_single, sub_div]
  simp only [dotProduct, hval]
  rw [← sum_part χ, sum_div]
  refine sum_congr rfl fun a _ ↦ ?_
  rcases Nat.eq_zero_or_pos (part G χ c).card with h0 | hpos
  · simp [h0]
  have hpos' : (0 : ℝ) < (part G χ c).card := by exact_mod_cast hpos
  have hs := Real.mul_self_sqrt hpos'.le
  rw [disp, sum_div]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mem_part.1 hx, div_mul_div_comm, hs, sq]

end Alg

end BHSV25
