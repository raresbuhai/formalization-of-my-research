module

public import BGHKLMM26.Hardness.Defs
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Fourier facts for the KKMO reduction

Auxiliary facts on the cube for `BGHKLMM26/Hardness/KKMO.lean`, in the namespace
`BGHKLMM26.Hard.KKMOAux`: the coefficients are linear; the degree-`K` influences are convex
(`cutoffInfluence_listAvg_le`), move with a permutation of the coordinates
(`cutoffInfluence_comp_perm`), and sum to at most `K` for a `[-1,1]`-valued table, so that at most
`K/τ` coordinates have influence `τ` (`card_influential_mul_le`); a dictator cuts `(1 - ρ)/2` of
the `ρ`-correlated pairs (`corrAverage_dictator`); and the stability is Lipschitz in the
correlation (`abs_stability_sub_le`).
-/
@[expose] public section

namespace BGHKLMM26.Hard.KKMOAux

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

section Fourier

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ### Linearity of the coefficients -/

theorem coefficient_add' (f g : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ f x + g x) s = coefficient f s + coefficient g s := by
  unfold coefficient
  rw [← Finset.expect_add_distrib]
  exact Finset.expect_congr rfl fun x _ ↦ by ring

theorem coefficient_const_mul (a : ℝ) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ a * f x) s = a * coefficient f s := by
  unfold coefficient
  rw [Finset.mul_expect]
  exact Finset.expect_congr rfl fun x _ ↦ by ring

theorem coefficient_div_const (a : ℝ) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ f x / a) s = coefficient f s / a := by
  unfold coefficient
  rw [Finset.expect_div]
  exact Finset.expect_congr rfl fun x _ ↦ by ring

theorem coefficient_finsetSum {ι : Type*} (S : Finset ι) (h : ι → Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ ∑ k ∈ S, h k x) s = ∑ k ∈ S, coefficient (h k) s := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

/-! ### Bounds -/

theorem cutoffInfluence_nonneg (K : ℕ) (i : I) (h : Cube I → ℝ) : 0 ≤ cutoffInfluence K i h :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem cutoffInfluence_le_energy (K : ℕ) (i : I) (h : Cube I → ℝ) :
    cutoffInfluence K i h ≤ ∑ s, coefficient h s ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ ↦ sq_nonneg _

theorem cutoffInfluence_le_one (K : ℕ) (i : I) {h : Cube I → ℝ}
    (hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1) : cutoffInfluence K i h ≤ 1 :=
  (cutoffInfluence_le_energy K i h).trans (spectral_energy_le_one h hh)

/-- The total degree-`K` influence is at most `K` times the energy. -/
theorem sum_cutoffInfluence_le (K : ℕ) (h : Cube I → ℝ) :
    ∑ i, cutoffInfluence K i h ≤ K * ∑ s, coefficient h s ^ 2 := by
  unfold cutoffInfluence
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  by_cases hd : OAI.OptimalMaxCut.Analytic.degree s ≤ K
  · simp only [hd, and_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : ((univ.filter fun i ↦ s i = true).card : ℝ) = OAI.OptimalMaxCut.Analytic.degree s := rfl
    rw [this]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (sq_nonneg _)
  · simp only [hd, and_false, ↓reduceIte, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- At most `K / τ` coordinates have degree-`K` influence at least `τ`, for `|h| ≤ 1`. -/
theorem card_influential_mul_le (K : ℕ) {τ : ℝ} {h : Cube I → ℝ}
    (hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1) :
    ((univ.filter fun i ↦ τ ≤ cutoffInfluence K i h).card : ℝ) * τ ≤ K := by
  calc ((univ.filter fun i ↦ τ ≤ cutoffInfluence K i h).card : ℝ) * τ
      = ∑ i ∈ univ.filter fun i ↦ τ ≤ cutoffInfluence K i h, τ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ univ.filter fun i ↦ τ ≤ cutoffInfluence K i h, cutoffInfluence K i h :=
        Finset.sum_le_sum fun i hi ↦ (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, cutoffInfluence K i h :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ ↦ cutoffInfluence_nonneg K i h
    _ ≤ K * ∑ s, coefficient h s ^ 2 := sum_cutoffInfluence_le K h
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one h hh) (Nat.cast_nonneg _)
    _ = K := mul_one _

/-! ### Averages -/

/-- Influences are convex: the degree-`K` influence of an average is at most the average of the
influences. -/
theorem cutoffInfluence_avg_le {N : ℕ} (hN : 0 < N) (K : ℕ) (i : I)
    (h : Fin N → Cube I → ℝ) :
    cutoffInfluence K i (fun x ↦ (∑ k, h k x) / N) ≤ (∑ k, cutoffInfluence K i (h k)) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cutoffInfluence
  simp_rw [coefficient_div_const, coefficient_finsetSum]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin N)))
    (f := fun k ↦ coefficient (h k) s)
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  rw [div_pow, div_le_div_iff₀ (by positivity) hN']
  calc (∑ k, coefficient (h k) s) ^ 2 * N ≤ (N * ∑ k, coefficient (h k) s ^ 2) * N :=
        mul_le_mul_of_nonneg_right hcs hN'.le
    _ = (∑ k, coefficient (h k) s ^ 2) * N ^ 2 := by ring

/-- The list form of `cutoffInfluence_avg_le`. -/
theorem cutoffInfluence_listAvg_le {α : Type*} (K : ℕ) (i : I) {l : List α} (hl : l ≠ [])
    (h : α → Cube I → ℝ) :
    cutoffInfluence K i (fun x ↦ (l.map fun a ↦ h a x).sum / l.length) ≤
      (l.map fun a ↦ cutoffInfluence K i (h a)).sum / l.length := by
  have e1 : (fun x ↦ (l.map fun a ↦ h a x).sum / l.length) =
      fun x ↦ (∑ k : Fin l.length, h l[k.1] x) / l.length := by
    funext x; rw [Fin.sum_univ_fun_getElem l (fun a ↦ h a x)]
  rw [e1, ← Fin.sum_univ_fun_getElem l (fun a ↦ cutoffInfluence K i (h a))]
  exact cutoffInfluence_avg_le (List.length_pos_iff.mpr hl) K i (fun k ↦ h l[k.1])

/-! ### Permutations of the coordinates -/

/-- The permutation of the cube induced by a permutation `e` of the coordinates. -/
def cubePerm (e : I ≃ I) : Cube I ≃ Cube I where
  toFun x j := x (e j)
  invFun y k := y (e.symm k)
  left_inv x := by funext k; simp
  right_inv y := by funext j; simp

theorem walsh_cubePerm_symm (e : I ≃ I) (s y : Cube I) :
    walsh s (fun k ↦ y (e.symm k)) = walsh (fun j ↦ s (e j)) y := by
  unfold walsh
  exact (Equiv.prod_comp e (fun k ↦ bitSign (s k && y (e.symm k)))).symm.trans
    (Finset.prod_congr rfl fun j _ ↦ by simp)

theorem coefficient_comp_perm (e : I ≃ I) (h : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ h (fun j ↦ x (e j))) s = coefficient h (fun j ↦ s (e j)) := by
  unfold coefficient
  refine Fintype.expect_equiv (cubePerm e) _ _ fun x ↦ ?_
  have : x = fun k ↦ (cubePerm e x) (e.symm k) := by funext k; simp [cubePerm]
  conv_lhs => rw [this]
  rw [walsh_cubePerm_symm]
  simp [cubePerm]

omit [DecidableEq I] in
theorem degree_comp_perm (e : I ≃ I) (s : Cube I) :
    OAI.OptimalMaxCut.Analytic.degree (fun j ↦ s (e j)) = OAI.OptimalMaxCut.Analytic.degree s := by
  unfold OAI.OptimalMaxCut.Analytic.degree
  exact Finset.card_bij (fun j _ ↦ e j) (by simp) (fun _ _ _ _ h ↦ e.injective h)
    (fun k hk ↦ ⟨e.symm k, by simpa using hk, by simp⟩)

/-- Reading `h` through a permutation `e` of the coordinates moves the influences by `e⁻¹`. -/
theorem cutoffInfluence_comp_perm (K : ℕ) (e : I ≃ I) (i : I) (h : Cube I → ℝ) :
    cutoffInfluence K i (fun x ↦ h (fun j ↦ x (e j))) = cutoffInfluence K (e.symm i) h := by
  unfold cutoffInfluence
  simp_rw [coefficient_comp_perm, Finset.sum_filter]
  refine Fintype.sum_equiv (cubePerm e) _ _ fun s ↦ ?_
  simp only [cubePerm, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  rw [degree_comp_perm]

end Fourier

/-! ### The cut of a dictator -/

theorem bitVal_bne (a b : Bool) : bitVal (a != b) = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [bitVal, bitSign]

theorem walsh_single {n : ℕ} (i : Fin n) (x : Cube (Fin n)) :
    walsh (fun k ↦ decide (k = i)) x = bitSign (x i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hk; simp [hk, bitSign]
  · simp

theorem degree_single {n : ℕ} (i : Fin n) :
    OAI.OptimalMaxCut.Analytic.degree (fun k : Fin n ↦ decide (k = i)) = 1 := by
  unfold OAI.OptimalMaxCut.Analytic.degree
  rw [Finset.card_eq_one]
  exact ⟨i, by ext k; simp⟩

theorem corrAverage_one (ρ : ℝ) (n : ℕ) :
    corrAverage ρ n (fun (_ : BitCube n) (_ : BitCube n) ↦ (1 : ℝ)) = 1 := by
  have := corrAverage_fst ρ n (fun _ ↦ (1 : ℝ))
  rw [Fintype.expect_const] at this
  exact this

/-- A dictator cuts a `(1 - ρ)/2` fraction of the `ρ`-correlated pairs. -/
theorem corrAverage_dictator (ρ : ℝ) {n : ℕ} (i : Fin n) :
    corrAverage ρ n (fun x y ↦ bitVal (x i != y i)) = (1 - ρ) / 2 := by
  have e : (fun x y : BitCube n ↦ bitVal (x i != y i)) = fun x y ↦
      (1 / 2 : ℝ) * 1 + (-(1 / 2) * (walsh (fun k ↦ decide (k = i)) x *
        walsh (fun k ↦ decide (k = i)) y)) := by
    funext x y; rw [walsh_single, walsh_single, bitVal_bne]; ring
  rw [e, corrAverage_add, corrAverage_const_mul, corrAverage_const_mul, corrAverage_one,
    OAI.OptimalMaxCut.MISProof.corrAverage_walsh]
  simp only [↓reduceIte, degree_single]
  ring

/-! ### Stability is Lipschitz in the correlation -/

theorem pow_lipschitz {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {a b : ℝ} (ha : |a| ≤ r) (hb : |b| ≤ r)
    (d : ℕ) : |a ^ d - b ^ d| ≤ 2 / (1 - r) * |a - b| := by
  have h1 : 0 < 1 - r := by linarith
  rcases d with _ | j
  · simp only [pow_zero, sub_self, abs_zero]; positivity
  refine (abs_pow_sub_pow_le a b (j + 1)).trans ?_
  rw [Nat.add_sub_cancel]
  have hm : max |a| |b| ^ j ≤ r ^ j :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) (max_le ha hb) j
  have hj := nat_mul_pow_mul_one_sub_le_one r hr0 hr1.le j
  have hrj : r ^ j * (1 - r) ≤ 1 := by
    have : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1.le
    nlinarith
  have key : ((j + 1 : ℕ) : ℝ) * r ^ j ≤ 2 / (1 - r) := by
    rw [le_div_iff₀ h1]; push_cast; linarith
  calc |a - b| * ((j + 1 : ℕ) : ℝ) * max |a| |b| ^ j
      ≤ |a - b| * ((j + 1 : ℕ) : ℝ) * r ^ j :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = |a - b| * (((j + 1 : ℕ) : ℝ) * r ^ j) := by ring
    _ ≤ |a - b| * (2 / (1 - r)) := mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = 2 / (1 - r) * |a - b| := by ring

theorem abs_stability_sub_le {I : Type*} [Fintype I] [DecidableEq I] {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) {ρ ρ' : ℝ} (hρ : |ρ| ≤ r) (hρ' : |ρ'| ≤ r) {h : Cube I → ℝ}
    (hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1) :
    |stability ρ' h - stability ρ h| ≤ 2 / (1 - r) * |ρ' - ρ| := by
  unfold stability
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ s, |ρ' ^ OAI.OptimalMaxCut.Analytic.degree s * coefficient h s ^ 2 -
        ρ ^ OAI.OptimalMaxCut.Analytic.degree s * coefficient h s ^ 2|
      ≤ ∑ s, 2 / (1 - r) * |ρ' - ρ| * coefficient h s ^ 2 := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (coefficient h s))]
        exact mul_le_mul_of_nonneg_right (pow_lipschitz hr0 hr1 hρ' hρ _) (sq_nonneg _)
    _ = 2 / (1 - r) * |ρ' - ρ| * ∑ s, coefficient h s ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 / (1 - r) * |ρ' - ρ| * 1 := by
        refine mul_le_mul_of_nonneg_left (spectral_energy_le_one h hh) ?_
        have : 0 < 1 - r := by linarith
        positivity
    _ = 2 / (1 - r) * |ρ' - ρ| := mul_one _

end BGHKLMM26.Hard.KKMOAux
