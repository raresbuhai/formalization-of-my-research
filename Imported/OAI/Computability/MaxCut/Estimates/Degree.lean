/-
Copied from OpenAI's `openai/math` (Apache-2.0, see `Imported/OAI/LICENSE`), commit `4eaee87548250b2682affda7d05d947c05554bae`,
file `lean/OAI/Computability/MaxCut/Estimates/Degree.lean`.
Changes: the section on the Goemans–Williamson ratio (`OAI.OptimalMaxCut.gwRatio`, `alphaGW`, ...),
which Majority is Stablest does not use, is removed.
-/
module

public import OAI.Computability.MaxCut.Walsh

@[expose] public section

namespace OAI

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace OptimalMaxCut.Analytic

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

/-- Frequency degree: cardinality of the set of selected Boolean coordinates. -/
def degree {I : Type*} [Fintype I] (s : Cube I) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card

noncomputable def stability {I : Type*} [Fintype I] [DecidableEq I]
    (t : ℝ) (f : Cube I → ℝ) : ℝ :=
  ∑ s, t ^ degree s * coefficient f s ^ 2

/-- Full influence, with the same probability normalization. -/
noncomputable def influence {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (f : Cube I → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Cube I => s i = true), coefficient f s ^ 2

noncomputable def cutoffInfluence {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (i : I) (f : Cube I → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Cube I => s i = true ∧ degree s ≤ K),
    coefficient f s ^ 2

/-- Ordinary Boolean noise in its exact Walsh multiplier representation.
Range/mean preservation must be proved, not imposed as assumptions. -/
noncomputable def noise {I : Type*} [Fintype I] [DecidableEq I]
    (u : ℝ) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  ∑ s, (u ^ degree s * coefficient f s) * walsh s x

def MajorityIsStablest : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ ξ : ℝ, 0 < ξ →
    ∃ K : ℕ, 1 ≤ K ∧ ∃ τ : ℝ, 0 < τ ∧
      ∀ (n : ℕ) (h : Cube (Fin n) → ℝ),
        (∀ x, -1 ≤ h x ∧ h x ≤ 1) → (𝔼 x, h x) = 0 →
        (∀ i, cutoffInfluence K i h < τ) →
        stability t h ≤ 2 / Real.pi * Real.arcsin t + ξ

def UntruncatedMajorityIsStablest : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ ξ : ℝ, 0 < ξ →
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (n : ℕ) (h : Cube (Fin n) → ℝ),
        (∀ x, -1 ≤ h x ∧ h x ≤ 1) → (𝔼 x, h x) = 0 →
        (∀ i, influence i h < τ) →
        stability t h ≤ 2 / Real.pi * Real.arcsin t + ξ

section NoiseIdentities

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact diagonalization of ordinary bit noise. -/
theorem coefficient_noise (u : ℝ) (f : Cube I → ℝ) (a : Cube I) :
    coefficient (noise u f) a = u ^ degree a * coefficient f a := by
  classical
  unfold coefficient noise
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp [coefficient]

/-- The finite energy bound used for the dimension-independent cutoff step. -/
theorem spectral_energy_le_one (f : Cube I → ℝ)
    (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    (∑ s, coefficient f s ^ 2) ≤ 1 := by
  rw [walsh_parseval]
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  obtain ⟨hl, hu⟩ := hf x
  nlinarith

theorem stability_noise (t u : ℝ) (f : Cube I → ℝ) :
    stability t (noise u f) =
      ∑ s, t ^ degree s * u ^ (2 * degree s) * coefficient f s ^ 2 := by
  classical
  unfold stability
  simp_rw [coefficient_noise, mul_pow, pow_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Noise only decreases nonnegative stability (`lem:mis`, first inequality). -/
theorem stability_noise_le (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (f : Cube I → ℝ) : stability t (noise u f) ≤ stability t f := by
  classical
  rw [stability_noise, stability]
  apply Finset.sum_le_sum
  intro s _
  have hp : u ^ (2 * degree s) ≤ 1 := pow_le_one₀ hu hu1
  have hn : 0 ≤ t ^ degree s * coefficient f s ^ 2 := by positivity
  nlinarith

/-- The exact error integrand, before replacing it by any uniform bound. -/
theorem stability_sub_noise (t u : ℝ) (f : Cube I → ℝ) :
    stability t f - stability t (noise u f) =
      ∑ s, (t ^ degree s * (1 - u ^ (2 * degree s))) * coefficient f s ^ 2 := by
  classical
  rw [stability_noise, stability, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A uniform multiplier bound gives a dimension-independent stability error. -/
theorem stability_sub_noise_le (t u η : ℝ) (f : Cube I → ℝ)
    (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) (hη : 0 ≤ η)
    (h : ∀ j : ℕ, t ^ j * (1 - u ^ (2 * j)) ≤ η) :
    stability t f - stability t (noise u f) ≤ η := by
  rw [stability_sub_noise]
  calc
    _ ≤ ∑ s, η * coefficient f s ^ 2 :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (h _) (sq_nonneg _)
    _ = η * ∑ s, coefficient f s ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one f hf) hη
    _ = η := mul_one _

@[simp] theorem walsh_zero (x : Cube I) : walsh (fun _ => false) x = 1 := by
  simp [walsh, bitSign]

omit [DecidableEq I] in
@[simp] theorem degree_zero : degree (fun _ : I => false) = 0 := by
  simp [degree]

@[simp] theorem coefficient_one (a : Cube I) :
    coefficient (fun _ : Cube I => (1 : ℝ)) a =
      if a = (fun _ => false) then 1 else 0 := by
  simpa [coefficient] using walsh_orthogonality a (fun _ => false)

@[simp] theorem noise_one (u : ℝ) (x : Cube I) :
    noise u (fun _ => (1 : ℝ)) x = 1 := by
  classical
  simp [noise]

/-- Exactly preservation of the probability-normalized mean. -/
theorem noise_mean (u : ℝ) (f : Cube I → ℝ) :
    (𝔼 x, noise u f x) = 𝔼 x, f x := by
  simpa [coefficient] using coefficient_noise u f (fun _ => false)

omit [DecidableEq I] in
lemma pow_degree (u : ℝ) (s : Cube I) :
    u ^ degree s = ∏ i, if s i = true then u else 1 := by
  classical
  simp [Finset.prod_ite, degree]

/-- The product kernel of independent bit noise, not an assumed operator. -/
theorem walsh_noise_kernel (u : ℝ) (x y : Cube I) :
    (∑ s, u ^ degree s * walsh s x * walsh s y) =
      ∏ i, (1 + u * bitSign (x i) * bitSign (y i)) := by
  classical
  have hs (s : Cube I) : u ^ degree s * walsh s x * walsh s y =
      ∏ i, if s i = true then u * bitSign (x i) * bitSign (y i) else 1 := by
    rw [pow_degree, walsh, walsh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases h : s i <;> simp [bitSign]
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    if b = true then u * bitSign (x i) * bitSign (y i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

theorem noise_kernel (u : ℝ) (f : Cube I → ℝ) (x : Cube I) :
    noise u f x =
      𝔼 y, f y * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
  classical
  unfold noise coefficient
  simp_rw [Finset.mul_expect, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro y _
  calc
    _ = f y * (∑ s, u ^ degree s * walsh s y * walsh s x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [walsh_noise_kernel]

/-- Normalization of the actual bit-noise kernel, for every real multiplier. -/
theorem noise_kernel_mass (u : ℝ) (x : Cube I) :
    (𝔼 y : Cube I, ∏ i, (1 + u * bitSign (y i) * bitSign (x i))) = 1 := by
  have h := noise_kernel u (fun _ : Cube I => (1 : ℝ)) x
  simpa using h.symm

omit [DecidableEq I] in
/-- The positivity restriction needed to make the kernel a probability law. -/
theorem noise_kernel_nonneg (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : Cube I) : 0 ≤ ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
  apply Finset.prod_nonneg
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [bitSign] <;> linarith

theorem noise_bounded (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (f : Cube I → ℝ) (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    ∀ x, -1 ≤ noise u f x ∧ noise u f x ≤ 1 := by
  intro x
  rw [noise_kernel]
  have hmass := noise_kernel_mass u x
  constructor
  · calc
      -1 = 𝔼 y, (-1 : ℝ) * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
        rw [← Finset.mul_expect, hmass, mul_one]
      _ ≤ _ := Finset.expect_le_expect fun y _ =>
        mul_le_mul_of_nonneg_right (hf y).1 (noise_kernel_nonneg u hu hu1 x y)
  · calc
      _ ≤ 𝔼 y, (1 : ℝ) * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) :=
        Finset.expect_le_expect fun y _ =>
          mul_le_mul_of_nonneg_right (hf y).2 (noise_kernel_nonneg u hu hu1 x y)
      _ = 1 := by simpa using hmass

theorem influence_noise_le (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (K : ℕ) (i : I) (f : Cube I → ℝ) :
    influence i (noise u f) ≤ cutoffInfluence K i f +
      u ^ (2 * (K + 1)) * (∑ s, coefficient f s ^ 2) := by
  classical
  simp only [influence, cutoffInfluence, Finset.sum_filter, coefficient_noise,
    mul_pow, ← pow_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hi : s i = true
  · simp only [hi, true_and, ite_true]
    by_cases hd : degree s ≤ K
    · rw [ite_eq_left hd]
      have hp : u ^ (degree s * 2) ≤ 1 := pow_le_one₀ hu hu1
      have hb : 0 ≤ u ^ (2 * (K + 1)) * coefficient f s ^ 2 := by positivity
      have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (coefficient f s))
      nlinarith
    · rw [ite_eq_right hd]
      have hkd : 2 * (K + 1) ≤ degree s * 2 := by omega
      have hp := pow_le_pow_of_le_one hu hu1 hkd
      simpa using mul_le_mul_of_nonneg_right hp (sq_nonneg (coefficient f s))
  · simp only [hi]
    positivity

/-- The normalized form actually used in `lem:mis`. -/
theorem influence_noise_le_of_bounded (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (K : ℕ) (i : I) (f : Cube I → ℝ) (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    influence i (noise u f) ≤ cutoffInfluence K i f + u ^ (2 * (K + 1)) := by
  calc
    _ ≤ cutoffInfluence K i f + u ^ (2 * (K + 1)) * (∑ s, coefficient f s ^ 2) :=
      influence_noise_le u hu hu1 K i f
    _ ≤ cutoffInfluence K i f + u ^ (2 * (K + 1)) * 1 :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (spectral_energy_le_one f hf)
        (pow_nonneg hu _))
    _ = _ := by rw [mul_one]

end NoiseIdentities

theorem nat_mul_pow_mul_one_sub_le_one (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) : (j : ℝ) * t ^ j * (1 - t) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp : t ^ (j + 1) ≤ 1 := pow_le_one₀ ht ht1
    calc
      ((j + 1 : ℕ) : ℝ) * t ^ (j + 1) * (1 - t) =
          t * ((j : ℝ) * t ^ j * (1 - t)) + t ^ (j + 1) * (1 - t) := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ t * 1 + 1 * (1 - t) := add_le_add
        (mul_le_mul_of_nonneg_left ih ht)
        (mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr ht1))
      _ = 1 := by ring

/-- Explicit control of the entire noise-stability multiplier sequence. -/
theorem multiplier_le (t u : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (j : ℕ) :
    t ^ j * (1 - u ^ (2 * j)) ≤ 2 * (1 - u) / (1 - t) := by
  have hber := one_add_mul_sub_le_pow (show -1 ≤ u by linarith) (2 * j)
  have hbern : 1 - u ^ (2 * j) ≤ (2 * (j : ℝ)) * (1 - u) := by
    push_cast at hber
    nlinarith
  have htp : 0 ≤ t ^ j := pow_nonneg ht j
  have hju := nat_mul_pow_mul_one_sub_le_one t ht ht1.le j
  have htm : 0 < 1 - t := sub_pos.mpr ht1
  apply (le_div_iff₀ htm).mpr
  calc
    t ^ j * (1 - u ^ (2 * j)) * (1 - t) ≤
        t ^ j * (2 * (j : ℝ) * (1 - u)) * (1 - t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbern htp) htm.le
    _ = (2 * (1 - u)) * ((j : ℝ) * t ^ j * (1 - t)) := by ring
    _ ≤ (2 * (1 - u)) * 1 := mul_le_mul_of_nonneg_left hju (by linarith)
    _ = 2 * (1 - u) := by ring

theorem exists_uniform_noise_error (t ξ : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hξ : 0 < ξ) : ∃ u : ℝ, 0 < u ∧ u < 1 ∧
      ∀ j : ℕ, t ^ j * (1 - u ^ (2 * j)) ≤ ξ / 2 := by
  let e : ℝ := min (1 / 2) (ξ * (1 - t) / 4)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have hehalf : e ≤ 1 / 2 := min_le_left _ _
  have heξ : e ≤ ξ * (1 - t) / 4 := min_le_right _ _
  refine ⟨1 - e, by linarith, by linarith, ?_⟩
  intro j
  calc
    _ ≤ 2 * (1 - (1 - e)) / (1 - t) :=
      multiplier_le t (1 - e) ht ht1 (by linarith) (by linarith) j
    _ ≤ ξ / 2 := by
      apply (div_le_iff₀ (sub_pos.mpr ht1)).mpr
      linarith

/-- Degree cutoff for the influence tail, with no dimension dependence. -/
theorem exists_influence_tail_cutoff (u δ : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : 0 < δ) : ∃ K : ℕ, 1 ≤ K ∧ u ^ (2 * (K + 1)) ≤ δ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity) hu1
  refine ⟨N + 1, by omega, ?_⟩
  exact le_trans (pow_le_pow_of_le_one hu hu1.le (by omega : N ≤ 2 * (N + 1 + 1)))
    hN.le

/-- All of the uniform smoothing preparation in `lem:mis`, independently of
(the still unproved) Majority Is Stablest inequality. Both K and u precede
n, and the range and centered-mean conclusions are proved from the kernel. -/
theorem uniform_noise_preparation (t ξ : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hξ : 0 < ξ) : ∃ u : ℝ, 0 < u ∧ u < 1 ∧
      (∀ (n : ℕ) (f : Cube (Fin n) → ℝ),
        (∀ x, -1 ≤ f x ∧ f x ≤ 1) → (𝔼 x, f x) = 0 →
        (∀ x, -1 ≤ noise u f x ∧ noise u f x ≤ 1) ∧
        (𝔼 x, noise u f x) = 0 ∧
        0 ≤ stability t f - stability t (noise u f) ∧
        stability t f - stability t (noise u f) ≤ ξ / 2) ∧
      (∀ δ : ℝ, 0 < δ → ∃ K : ℕ, 1 ≤ K ∧
        ∀ (n : ℕ) (f : Cube (Fin n) → ℝ),
          (∀ x, -1 ≤ f x ∧ f x ≤ 1) →
          (∀ i, cutoffInfluence K i f < δ / 2) →
          ∀ i, influence i (noise u f) < δ) := by
  obtain ⟨u, hu, hu1, herr⟩ := exists_uniform_noise_error t ξ ht ht1 hξ
  refine ⟨u, hu, hu1, ?_, ?_⟩
  · intro n f hf hm
    refine ⟨noise_bounded u hu.le hu1.le f hf, ?_, ?_, ?_⟩
    · rw [noise_mean, hm]
    · exact sub_nonneg.mpr (stability_noise_le t u ht hu.le hu1.le f)
    · exact stability_sub_noise_le t u (ξ / 2) f hf (by positivity) herr
  · intro δ hδ
    obtain ⟨K, hK, htail⟩ := exists_influence_tail_cutoff u δ hu.le hu1 hδ
    refine ⟨K, hK, ?_⟩
    intro n f hf hi i
    have hbound := influence_noise_le_of_bounded u hu.le hu1.le K i f hf
    have hsmall := hi i
    linarith

end OptimalMaxCut.Analytic


end -- noncomputable Walsh/analytic section

end OAI
