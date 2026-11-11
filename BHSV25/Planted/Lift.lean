module

public import BHSV25.Alg.PartitionSpectral
public import BHSV25.Spectral.Basic

/-!
# Partitions and the lift, for a symmetric matrix

The objects of [BHSV25, Theorem 5.1 and Lemma 7.4] for a partition `χ` of `0, …, n - 1` into parts
indexed by a finite type `ι` and a symmetric matrix `Q` in place of the normalized adjacency
matrix of a regular graph (`BHSV25/Alg/Variance.lean`). The random planting theorems take for `Q`
the adjacency matrix of the planted graph divided by the degree of the host, as the paper's
Theorem 7.12 does ([BHSV25, Section 5]: "for technical reasons we take `M = A / d'`").

* **Partitions** (`BHSV25.Planted.part`, `BHSV25.Planted.wt`, `BHSV25.Planted.pmodel`,
  `BHSV25.Planted.disp`): the parts `V_a`, the weights `D_x(a) = ∑_{y ∈ V_a} Q_xy`, the model
  `M_ab = 𝔼_{x ∈ V_a} D_x(b)` and the dispersion `∑_{x ∈ V_a} (D_x(b) - M_ab)²`.
* **The lift** (`BHSV25.Planted.lift`): `z ↦ (x ↦ z_{χ x} / √|V_{χ x}|)`, an isometry when no part
  is empty, which carries the symmetrized model `S_ab = ∑_{x ∈ V_a} D_x(b) / √(|V_a| |V_b|)`
  (`BHSV25.Planted.symModel`) to `Q`: `⟨lift z, Q lift z'⟩ = ⟨z, S z'⟩`.
* **Lemma 7.4** (`BHSV25.Planted.dist_lift_single`): `‖Q lift e_c - lift (S e_c)‖²` is the sum of
  the dispersions `∑_a disp(a, c)` divided by `|V_c|`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset

variable {n : ℕ} {ι : Type*} [DecidableEq ι]

/-! ### Partitions -/

/-- The part `a` of a partition `χ`: the points `x` with `χ x = a`. -/
def part (χ : Fin n → ι) (a : ι) : Finset (Fin n) := univ.filter (χ · = a)

/-- The weight `D_x(a) = ∑_{y ∈ V_a} Q_xy` from `x` to the part `a`. -/
noncomputable def wt (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (x : Fin n) (a : ι) : ℝ :=
  ∑ y ∈ part χ a, Q x y

/-- The model of `χ`: `M_ab = 𝔼_{x ∈ V_a} D_x(b)` (`0` if `V_a` is empty). -/
noncomputable def pmodel (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (a b : ι) : ℝ :=
  (∑ x ∈ part χ a, wt Q χ x b) / (part χ a).card

/-- The dispersion `∑_{x ∈ V_a} (D_x(b) - M_ab)²`. -/
noncomputable def disp (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (a b : ι) : ℝ :=
  ∑ x ∈ part χ a, (wt Q χ x b - pmodel Q χ a b) ^ 2

/-- The lift `z ↦ (x ↦ z_{χ x} / √|V_{χ x}|)` of vectors indexed by the parts. -/
noncomputable def lift (χ : Fin n → ι) (z : ι → ℝ) : Fin n → ℝ :=
  fun x ↦ z (χ x) / Real.sqrt (part χ (χ x)).card

/-- The symmetrized model `S_ab = ∑_{x ∈ V_a} D_x(b) / √(|V_a| |V_b|)`. -/
noncomputable def symModel (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) : Matrix ι ι ℝ :=
  fun a b ↦ (∑ x ∈ part χ a, wt Q χ x b) / Real.sqrt ((part χ a).card * (part χ b).card)

theorem mem_part {χ : Fin n → ι} {a : ι} {x : Fin n} : x ∈ part χ a ↔ χ x = a := by
  rw [part, mem_filter, and_iff_right (mem_univ _)]

theorem mem_part_self (χ : Fin n → ι) (x : Fin n) : x ∈ part χ (χ x) := mem_part.2 rfl

theorem card_part_pos (χ : Fin n → ι) (x : Fin n) : 0 < (part χ (χ x)).card :=
  card_pos.2 ⟨x, mem_part_self χ x⟩

/-- A sum over the points, grouped by parts. -/
theorem sum_part [Fintype ι] {M : Type*} [AddCommMonoid M] (χ : Fin n → ι) (f : Fin n → M) :
    ∑ a, ∑ x ∈ part χ a, f x = ∑ x, f x :=
  Finset.sum_fiberwise univ χ f

theorem sum_card_part [Fintype ι] (χ : Fin n → ι) : ∑ a, ((part χ a).card : ℝ) = n := by
  have := sum_part χ (fun _ ↦ (1 : ℝ))
  simpa using this

theorem sum_ite_part {M : Type*} [AddCommMonoid M] (χ : Fin n → ι) (a : ι) (f : Fin n → M) :
    ∑ x, (if χ x = a then f x else 0) = ∑ x ∈ part χ a, f x := by
  rw [part, sum_filter]

section Symm

variable {Q : Matrix (Fin n) (Fin n) ℝ}

theorem symm_apply (hQ : Q.IsHermitian) (x y : Fin n) : Q x y = Q y x := by
  have := hQ.apply x y
  simpa using this.symm

/-- The weight between two parts, seen from either side. -/
theorem sum_wt_comm (hQ : Q.IsHermitian) (χ : Fin n → ι) (a b : ι) :
    ∑ x ∈ part χ a, wt Q χ x b = ∑ y ∈ part χ b, wt Q χ y a :=
  calc ∑ x ∈ part χ a, wt Q χ x b
      = ∑ x ∈ part χ a, ∑ y ∈ part χ b, Q y x :=
        sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ symm_apply hQ x y
    _ = ∑ y ∈ part χ b, ∑ x ∈ part χ a, Q y x := Finset.sum_comm

end Symm

theorem card_mul_pmodel (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (a b : ι) :
    (part χ a).card * pmodel Q χ a b = ∑ x ∈ part χ a, wt Q χ x b := by
  rcases Nat.eq_zero_or_pos (part χ a).card with h0 | hpos
  · rw [card_eq_zero.1 h0]
    simp
  · rw [pmodel, mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')]

/-- The mean minimizes the sum of squares: `disp(a, b) ≤ ∑_{x ∈ V_a} (D_x(b) - p)²` for every
`p`. -/
theorem disp_le_sum_sq (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (a b : ι) (p : ℝ) :
    disp Q χ a b ≤ ∑ x ∈ part χ a, (wt Q χ x b - p) ^ 2 := by
  set μ := pmodel Q χ a b
  have hsum : ∑ x ∈ part χ a, (wt Q χ x b - μ) = 0 := by
    rw [sum_sub_distrib, ← card_mul_pmodel, sum_const, nsmul_eq_mul, sub_self]
  have e : ∀ x, (wt Q χ x b - p) ^ 2 =
      (wt Q χ x b - μ) ^ 2 + 2 * (μ - p) * (wt Q χ x b - μ) + (μ - p) ^ 2 := fun x ↦ by ring
  rw [disp, sum_congr rfl fun x _ ↦ e x, sum_add_distrib, sum_add_distrib, ← mul_sum, hsum,
    mul_zero, add_zero]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sq_nonneg _)

/-! ### The lift -/

theorem lift_apply (χ : Fin n → ι) (z : ι → ℝ) (x : Fin n) :
    lift χ z x = z (χ x) / Real.sqrt (part χ (χ x)).card := rfl

theorem lift_smul (χ : Fin n → ι) (c : ℝ) (z : ι → ℝ) : lift χ (c • z) = c • lift χ z :=
  funext fun x ↦ by simp [lift, mul_div_assoc]

theorem lift_sum {κ : Type*} (χ : Fin n → ι) (s : Finset κ) (z : κ → ι → ℝ) :
    lift χ (∑ j ∈ s, z j) = ∑ j ∈ s, lift χ (z j) :=
  funext fun x ↦ by simp [lift, sum_div]

theorem sqrt_card_part_mul_self (χ : Fin n → ι) (x : Fin n) :
    Real.sqrt (part χ (χ x)).card * Real.sqrt (part χ (χ x)).card = (part χ (χ x)).card :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

theorem sqrt_card_part_pos (χ : Fin n → ι) (x : Fin n) :
    0 < Real.sqrt (part χ (χ x)).card :=
  Real.sqrt_pos.2 (by exact_mod_cast card_part_pos χ x)

/-- **The lift is an isometry** when no part is empty. -/
theorem lift_dotProduct_lift [Fintype ι] (χ : Fin n → ι) (hne : ∀ a, (part χ a).Nonempty)
    (z z' : ι → ℝ) : lift χ z ⬝ᵥ lift χ z' = z ⬝ᵥ z' := by
  simp only [dotProduct, lift_apply]
  rw [← sum_part χ]
  refine sum_congr rfl fun a _ ↦ ?_
  have hpos : (0 : ℝ) < (part χ a).card := by exact_mod_cast (hne a).card_pos
  have hs := Real.mul_self_sqrt hpos.le
  calc ∑ x ∈ part χ a, z (χ x) / Real.sqrt (part χ (χ x)).card *
        (z' (χ x) / Real.sqrt (part χ (χ x)).card)
      = ∑ _x ∈ part χ a, z a * z' a / (part χ a).card := by
        refine sum_congr rfl fun x hx ↦ ?_
        rw [mem_part.1 hx, div_mul_div_comm, hs]
    _ = z a * z' a := by
        rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']

theorem sqrt_mul_card (χ : Fin n → ι) (a b : ι) :
    Real.sqrt ((part χ a).card * (part χ b).card) =
      Real.sqrt (part χ a).card * Real.sqrt (part χ b).card :=
  Real.sqrt_mul (Nat.cast_nonneg _) _

/-- A double sum over the points, grouped by parts. -/
theorem sum_sum_part [Fintype ι] (χ : Fin n → ι) (F : Fin n → Fin n → ℝ) :
    ∑ x, ∑ y, F x y = ∑ a, ∑ b, ∑ x ∈ part χ a, ∑ y ∈ part χ b, F x y := by
  rw [← sum_part χ]
  refine sum_congr rfl fun a _ ↦ ?_
  calc ∑ x ∈ part χ a, ∑ y, F x y = ∑ x ∈ part χ a, ∑ b, ∑ y ∈ part χ b, F x y :=
        sum_congr rfl fun x _ ↦ (sum_part χ (F x)).symm
    _ = ∑ b, ∑ x ∈ part χ a, ∑ y ∈ part χ b, F x y := Finset.sum_comm

/-- **The lift carries the symmetrized model to `Q`**: `⟨lift z, Q lift z'⟩ = ⟨z, S z'⟩`. -/
theorem lift_dotProduct_mulVec_lift [Fintype ι] (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι)
    (z z' : ι → ℝ) : lift χ z ⬝ᵥ (Q *ᵥ lift χ z') = z ⬝ᵥ (symModel Q χ *ᵥ z') := by
  have hL : lift χ z ⬝ᵥ (Q *ᵥ lift χ z') = ∑ x, ∑ y, lift χ z x * (Q x y * lift χ z' y) := by
    simp only [dotProduct, mulVec, mul_sum]
  rw [hL, sum_sum_part χ]
  simp only [dotProduct, mulVec, mul_sum]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
  have hR : ∀ x ∈ part χ a, ∀ y ∈ part χ b, lift χ z x * (Q x y * lift χ z' y) =
      z a * z' b / Real.sqrt ((part χ a).card * (part χ b).card) * Q x y := by
    intro x hx y hy
    rw [lift_apply, lift_apply, mem_part.1 hx, mem_part.1 hy, sqrt_mul_card]
    field_simp
  rw [sum_congr rfl fun x hx ↦ sum_congr rfl (hR x hx)]
  simp only [← mul_sum]
  rw [symModel]
  simp only [wt]
  ring

theorem symModel_isHermitian {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.IsHermitian)
    (χ : Fin n → ι) : (symModel Q χ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b ↦ ?_
  simp only [symModel, star_trivial]
  rw [sum_wt_comm hQ χ b a, mul_comm ((part χ b).card : ℝ)]

theorem lift_single (χ : Fin n → ι) (c : ι) (y : Fin n) :
    lift χ (Pi.single c 1) y = if χ y = c then 1 / Real.sqrt (part χ c).card else 0 := by
  rw [lift_apply]
  by_cases hy : χ y = c
  · rw [hy, Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne hy, ite_eq_right hy, zero_div]

theorem mulVec_lift_single (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (c : ι) (x : Fin n) :
    (Q *ᵥ lift χ (Pi.single c 1)) x = wt Q χ x c / Real.sqrt (part χ c).card := by
  simp only [mulVec, dotProduct, lift_single, mul_ite, mul_zero, wt, sum_div]
  rw [sum_ite_part]
  exact sum_congr rfl fun y _ ↦ by ring

theorem lift_symModel_single [Fintype ι] (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (c : ι)
    (x : Fin n) :
    lift χ (symModel Q χ *ᵥ Pi.single c 1) x = pmodel Q χ (χ x) c / Real.sqrt (part χ c).card := by
  have hpos' : (0 : ℝ) < (part χ (χ x)).card := by exact_mod_cast card_part_pos χ x
  have hs0 := sqrt_card_part_pos χ x
  rw [lift_apply, mulVec_single_one, Matrix.col_apply, symModel, sqrt_mul_card, pmodel]
  rcases Nat.eq_zero_or_pos (part χ c).card with h0 | hc
  · simp [h0]
  have hc' : (0 : ℝ) < Real.sqrt (part χ c).card := Real.sqrt_pos.2 (by exact_mod_cast hc)
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- **[BHSV25, Lemma 7.4]** (small variance implies close indicators):
`‖Q lift e_c - lift (S e_c)‖² = (∑_a disp(a, c)) / |V_c|`. -/
theorem dist_lift_single [Fintype ι] (Q : Matrix (Fin n) (Fin n) ℝ) (χ : Fin n → ι) (c : ι) :
    (Q *ᵥ lift χ (Pi.single c 1) - lift χ (symModel Q χ *ᵥ Pi.single c 1)) ⬝ᵥ
      (Q *ᵥ lift χ (Pi.single c 1) - lift χ (symModel Q χ *ᵥ Pi.single c 1)) =
    (∑ a, disp Q χ a c) / (part χ c).card := by
  have hval : ∀ x, (Q *ᵥ lift χ (Pi.single c 1) - lift χ (symModel Q χ *ᵥ Pi.single c 1)) x =
      (wt Q χ x c - pmodel Q χ (χ x) c) / Real.sqrt (part χ c).card := by
    intro x
    rw [Pi.sub_apply, mulVec_lift_single, lift_symModel_single, sub_div]
  simp only [dotProduct, hval]
  rw [← sum_part χ, sum_div]
  refine sum_congr rfl fun a _ ↦ ?_
  rcases Nat.eq_zero_or_pos (part χ c).card with h0 | hpos
  · simp [h0]
  have hpos' : (0 : ℝ) < (part χ c).card := by exact_mod_cast hpos
  have hs := Real.mul_self_sqrt hpos'.le
  rw [disp, sum_div]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mem_part.1 hx, div_mul_div_comm, hs, sq]

end Planted

end BHSV25
