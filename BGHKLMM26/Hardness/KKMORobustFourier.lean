module

public import BGHKLMM26.Hardness.Defs

/-!
# Smoothing an averaged long code

Fourier facts for the robust inverse of soundness (`BGHKLMM26.Hard.kkmo_robust`), about the noise
operator `T_u` (OpenAI's `noise u`, the Fourier multiplier `u^|s|`), for `u ∈ [0,1]`:

* linearity: `T_u` commutes with affine maps and finite averages (`noise_two_mul_sub_one`,
  `noise_list_avg`), and maps `[0,1]`-valued tables to `[0,1]`-valued tables (`noise_mem'`);
* influences: the influences of `T_u g` are at most a quarter of the degree-`K` influences of
  `2g - 1` plus `u^(2(K+1))` (`influence_noise_le'`), and `T_u` does not increase low-degree
  influences (`cutoffInfluence_noise_le`);
* the cut value: `Cut_ρ(T_u g) ≥ Cut_ρ(g) - (1 - u)/(1 - |ρ|)` (`cutValue_noise_ge`), and
  `Cut_ρ(g) ≤ 1` (`cutValue_le_one`).
-/

@[expose] public section

namespace BGHKLMM26.Hard.KKMORobust

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

section Linear

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem coefficient_add' (f g : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ f x + g x) s = coefficient f s + coefficient g s := by
  unfold coefficient
  rw [← Finset.expect_add_distrib]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  ring

theorem coefficient_const_mul' (a : ℝ) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (fun x ↦ a * f x) s = a * coefficient f s := by
  unfold coefficient
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  ring

theorem noise_add' (u : ℝ) (f g : Cube I → ℝ) :
    noise u (fun x ↦ f x + g x) = fun x ↦ noise u f x + noise u g x := by
  funext x
  unfold noise
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [coefficient_add']
  ring

theorem noise_const_mul' (u a : ℝ) (f : Cube I → ℝ) :
    noise u (fun x ↦ a * f x) = fun x ↦ a * noise u f x := by
  funext x
  unfold noise
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [coefficient_const_mul']
  ring

theorem noise_zero' (u : ℝ) : noise u (fun _ : Cube I ↦ (0 : ℝ)) = fun _ ↦ 0 := by
  have h := noise_const_mul' u 0 (fun _ : Cube I ↦ (0 : ℝ))
  simp only [zero_mul] at h
  exact h

theorem noise_const' (u c : ℝ) : noise u (fun _ : Cube I ↦ c) = fun _ ↦ c := by
  have h := noise_const_mul' u c (fun _ : Cube I ↦ (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  funext x
  rw [noise_one, mul_one]

/-- The noise of `2g - 1`. -/
theorem noise_two_mul_sub_one (u : ℝ) (g : Cube I → ℝ) :
    noise u (fun x ↦ 2 * g x - 1) = fun x ↦ 2 * noise u g x - 1 := by
  have e : (fun x ↦ 2 * g x - 1) = fun x ↦ (fun y ↦ 2 * g y) x + (fun _ ↦ (-1 : ℝ)) x := by
    funext x; ring
  rw [e, noise_add', noise_const_mul', noise_const']
  funext x; ring

/-- The noise of a finite average is the average of the noises. -/
theorem noise_list_sum {ι : Type*} (u : ℝ) (l : List ι) (h : ι → Cube I → ℝ) :
    noise u (fun x ↦ (l.map fun j ↦ h j x).sum) = fun x ↦ (l.map fun j ↦ noise u (h j) x).sum := by
  induction l with
  | nil => simpa using noise_zero' (I := I) u
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [noise_add' u (h a) (fun x ↦ (l.map fun j ↦ h j x).sum), ih]

theorem noise_list_avg {ι : Type*} (u : ℝ) (l : List ι) (h : ι → Cube I → ℝ) :
    noise u (fun x ↦ (l.map fun j ↦ h j x).sum / l.length) =
      fun x ↦ (l.map fun j ↦ noise u (h j) x).sum / l.length := by
  have e : (fun x ↦ (l.map fun j ↦ h j x).sum / l.length) =
      fun x ↦ (l.length : ℝ)⁻¹ * (fun y ↦ (l.map fun j ↦ h j y).sum) x := by
    funext x; rw [div_eq_inv_mul]
  rw [e, noise_const_mul', noise_list_sum]
  funext x; rw [div_eq_inv_mul]

/-- The coefficients of an affine image. -/
theorem coefficient_two_mul_sub_one (g : Cube I → ℝ) (s : Cube I) (hs : s ≠ fun _ ↦ false) :
    coefficient (fun x ↦ 2 * g x - 1) s = 2 * coefficient g s := by
  have e : (fun x ↦ 2 * g x - 1) = fun x ↦ (fun y ↦ 2 * g y) x + (fun _ ↦ (-1 : ℝ)) x := by
    funext x; ring
  rw [e, coefficient_add', coefficient_const_mul']
  have h1 := coefficient_const_mul' (-1 : ℝ) (fun _ : Cube I ↦ (1 : ℝ)) s
  simp only [mul_one] at h1
  rw [h1, coefficient_one, ite_eq_right_iff.mpr (fun h ↦ absurd h hs)]
  ring

theorem influence_two_mul_sub_one (i : I) (g : Cube I → ℝ) :
    influence i (fun x ↦ 2 * g x - 1) = 4 * influence i g := by
  unfold influence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs' : s ≠ fun _ ↦ false := by
    intro h
    simp only [Finset.mem_filter] at hs
    have := hs.2
    rw [h] at this
    simp at this
  rw [coefficient_two_mul_sub_one g s hs']
  ring

theorem cutoffInfluence_noise_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K : ℕ) (i : I)
    (f : Cube I → ℝ) : cutoffInfluence K i (noise u f) ≤ cutoffInfluence K i f := by
  unfold cutoffInfluence
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [coefficient_noise, mul_pow]
  have hp : (u ^ OAI.OptimalMaxCut.Analytic.degree s) ^ 2 ≤ 1 :=
    pow_le_one₀ (pow_nonneg hu0 _) (pow_le_one₀ hu0 hu1)
  exact mul_le_of_le_one_left (sq_nonneg _) hp

theorem cutoffInfluence_mono {K K' : ℕ} (hK : K ≤ K') (i : I) (f : Cube I → ℝ) :
    cutoffInfluence K i f ≤ cutoffInfluence K' i f := by
  unfold cutoffInfluence
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s _ _ ↦ sq_nonneg _
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact ⟨hs.1, hs.2.trans hK⟩

end Linear

variable {R : ℕ}

theorem noise_mem' {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {g : Cube (Fin R) → ℝ}
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (x : Cube (Fin R)) : 0 ≤ noise u g x ∧ noise u g x ≤ 1 := by
  have hh : ∀ x, -1 ≤ 2 * g x - 1 ∧ 2 * g x - 1 ≤ 1 := fun x ↦ by
    have := hg x; constructor <;> linarith [this.1, this.2]
  have := noise_bounded u hu0 hu1 _ hh x
  rw [noise_two_mul_sub_one] at this
  constructor <;> linarith [this.1, this.2]

/-- The influences of `T_u g` are small when the low-degree influences of `2g - 1` are. -/
theorem influence_noise_le' {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K : ℕ) (i : Fin R)
    {g : Cube (Fin R) → ℝ} (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    influence i (noise u g) ≤
      (cutoffInfluence K i (fun x ↦ 2 * g x - 1) + u ^ (2 * (K + 1))) / 4 := by
  have hh : ∀ x, -1 ≤ 2 * g x - 1 ∧ 2 * g x - 1 ≤ 1 := fun x ↦ by
    have := hg x; constructor <;> linarith [this.1, this.2]
  have h1 := influence_noise_le_of_bounded u hu0 hu1 K i _ hh
  rw [noise_two_mul_sub_one, influence_two_mul_sub_one] at h1
  linarith

theorem stability_ge_neg_one {t : ℝ} (ht : |t| ≤ 1) {h : Cube (Fin R) → ℝ}
    (hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1) : -1 ≤ stability t h := by
  have he := spectral_energy_le_one h hh
  have : -(∑ s, coefficient h s ^ 2) ≤ stability t h := by
    unfold stability
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ ↦ ?_
    have h1 : -1 ≤ t ^ OAI.OptimalMaxCut.Analytic.degree s := by
      have := abs_le.mp (show |t ^ OAI.OptimalMaxCut.Analytic.degree s| ≤ 1 by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht)
      exact this.1
    have h2 := sq_nonneg (coefficient h s)
    nlinarith
  linarith

theorem cutValue_le_one {ρ : ℝ} (hρ : |ρ| ≤ 1) {g : Cube (Fin R) → ℝ}
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) : cutValue ρ g ≤ 1 := by
  have hh : ∀ x, -1 ≤ 2 * g x - 1 ∧ 2 * g x - 1 ≤ 1 := fun x ↦ by
    have := hg x; constructor <;> linarith [this.1, this.2]
  unfold cutValue
  rw [corrAverage_cut]
  have := stability_ge_neg_one hρ hh
  linarith

/-- **Smoothing loses little of the cut**: `Cut_ρ(T_u g) ≥ Cut_ρ(g) - (1 - u)/(1 - |ρ|)`. -/
theorem cutValue_noise_ge {ρ : ℝ} (hρ : |ρ| < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g : Cube (Fin R) → ℝ} (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    cutValue ρ g - (1 - u) / (1 - |ρ|) ≤ cutValue ρ (noise u g) := by
  have hh : ∀ x, -1 ≤ 2 * g x - 1 ∧ 2 * g x - 1 ≤ 1 := fun x ↦ by
    have := hg x; constructor <;> linarith [this.1, this.2]
  set h : Cube (Fin R) → ℝ := fun x ↦ 2 * g x - 1 with hhdef
  have hd := stability_sub_noise ρ u h
  have hE := spectral_energy_le_one h hh
  have hM : 0 ≤ 2 * (1 - u) / (1 - |ρ|) :=
    div_nonneg (by linarith) (by linarith)
  have key : -(2 * (1 - u) / (1 - |ρ|)) ≤ stability ρ h - stability ρ (noise u h) := by
    rw [hd]
    calc -(2 * (1 - u) / (1 - |ρ|)) ≤ -(2 * (1 - u) / (1 - |ρ|)) * ∑ s, coefficient h s ^ 2 := by
          nlinarith [Finset.sum_nonneg fun s (_ : s ∈ (Finset.univ : Finset (Cube (Fin R)))) ↦
            sq_nonneg (coefficient h s)]
      _ = ∑ s, -(2 * (1 - u) / (1 - |ρ|)) * coefficient h s ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have hm := multiplier_le |ρ| u (abs_nonneg ρ) hρ hu0 hu1
            (OAI.OptimalMaxCut.Analytic.degree s)
          have hp : 0 ≤ 1 - u ^ (2 * OAI.OptimalMaxCut.Analytic.degree s) := by
            have := pow_le_one₀ hu0 hu1 (n := 2 * OAI.OptimalMaxCut.Analytic.degree s); linarith
          have hr : -(|ρ| ^ OAI.OptimalMaxCut.Analytic.degree s) ≤
              ρ ^ OAI.OptimalMaxCut.Analytic.degree s := by
            rw [← abs_pow]; exact neg_abs_le _
          nlinarith
  unfold cutValue
  rw [corrAverage_cut, corrAverage_cut]
  have e : (fun x ↦ 2 * noise u g x - 1) = noise u h := by
    rw [hhdef, noise_two_mul_sub_one]
  rw [e]
  have e2 : (1 - u) / (1 - |ρ|) = (2 * (1 - u) / (1 - |ρ|)) / 2 := by ring
  rw [e2]
  linarith

end BGHKLMM26.Hard.KKMORobust
