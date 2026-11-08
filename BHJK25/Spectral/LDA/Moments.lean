module

public import BHJK25.Spectral.Basic
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Moments of polynomials in the spectral model

A polynomial `f` in the entries of `U diag(λ) Uᵀ` (`BHJK25.Spectral.LDAAux.phi`) has finite
moments of every order when the coordinates of `λ` and of `U` do: sums and products of functions
with finite moments of every order have finite moments of every order (the products by Hölder's
inequality). This applies when `λ` is drawn from a product of distributions with bounded support
(as `μ_γ` and point masses), possibly with one coordinate fixed, and `U` is the Gaussian matrix.
-/

@[expose] public section

namespace BHJK25.Spectral.LDAAux

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The polynomial `f` in the entries of `U diag(λ) Uᵀ`, as a function of `(λ, U)`. -/
noncomputable def phi {n m : ℕ} (f : MvPolynomial (Fin n × Fin n) ℝ)
    (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) : ℝ :=
  MvPolynomial.eval (entries (specMap n m p)) f

theorem continuous_entries {n : ℕ} : Continuous (entries : Matrix (Fin n) (Fin n) ℝ → _) := by
  unfold entries
  fun_prop

theorem continuous_specMap {n m : ℕ} : Continuous (specMap n m) := by
  unfold specMap
  fun_prop

theorem continuous_phi {n m : ℕ} (f : MvPolynomial (Fin n × Fin n) ℝ) :
    Continuous (phi (m := m) f) :=
  (MvPolynomial.continuous_eval f).comp (continuous_entries.comp continuous_specMap)

variable {X : Type*} [MeasurableSpace X]

/-- `g` has finite moments of every order under `M`. -/
def AllMoments (M : Measure X) (g : X → ℝ) : Prop := ∀ p : ℝ≥0, MemLp g p M

variable {M : Measure X}

theorem allMoments_const [IsFiniteMeasure M] (c : ℝ) : AllMoments M fun _ ↦ c :=
  fun _ ↦ memLp_const c

theorem AllMoments.add {f g : X → ℝ} (hf : AllMoments M f) (hg : AllMoments M g) :
    AllMoments M fun x ↦ f x + g x := fun p ↦ (hf p).add (hg p)

theorem holderTriple_two_mul (p : ℝ≥0∞) : ENNReal.HolderTriple (2 * p) (2 * p) p := by
  constructor
  rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul]

theorem AllMoments.mul {f g : X → ℝ} (hf : AllMoments M f) (hg : AllMoments M g) :
    AllMoments M fun x ↦ f x * g x := by
  intro p
  have := holderTriple_two_mul (p : ℝ≥0∞)
  have h1 : MemLp f (2 * (p : ℝ≥0∞)) M := by exact_mod_cast hf (2 * p)
  have h2 : MemLp g (2 * (p : ℝ≥0∞)) M := by exact_mod_cast hg (2 * p)
  exact h1.fun_mul h2

theorem AllMoments.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, AllMoments M (f i)) : AllMoments M fun x ↦ ∑ i ∈ s, f i x :=
  fun p ↦ memLp_finsetSum s fun i hi ↦ hf i hi p

theorem AllMoments.comp_measurePreserving {Y : Type*} [MeasurableSpace Y] {N : Measure Y}
    {g : Y → ℝ} (hg : AllMoments N g) {T : X → Y} (hT : MeasurePreserving T M N) :
    AllMoments M fun x ↦ g (T x) :=
  fun p ↦ (hg p).comp_measurePreserving hT

theorem AllMoments.integrable {g : X → ℝ} (hg : AllMoments M g) : Integrable g M :=
  memLp_one_iff_integrable.1 (by exact_mod_cast hg 1)

/-- A polynomial in functions with finite moments of every order has finite moments of every
order. -/
theorem allMoments_eval [IsFiniteMeasure M] {σ : Type*} (y : X → σ → ℝ)
    (hy : ∀ s, AllMoments M fun x ↦ y x s) (f : MvPolynomial σ ℝ) :
    AllMoments M fun x ↦ MvPolynomial.eval (y x) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using allMoments_const (M := M) a
  | add p q hp hq => simpa using hp.add hq
  | mul_X p s hp => simpa using hp.mul (hy s)

/-- A polynomial in the entries of `U diag(λ) Uᵀ` has finite moments of every order when the
coordinates of `λ` and `U` do. -/
theorem allMoments_specMap [IsFiniteMeasure M] {n m : ℕ} (Λ : X → Fin m → ℝ)
    (W : X → Fin n → Fin m → ℝ) (hΛ : ∀ k, AllMoments M fun x ↦ Λ x k)
    (hW : ∀ a k, AllMoments M fun x ↦ W x a k) (f : MvPolynomial (Fin n × Fin n) ℝ) :
    AllMoments M fun x ↦ phi f (Λ x, W x) := by
  apply allMoments_eval
  rintro ⟨a, b⟩
  have h : (fun x ↦ entries (specMap n m (Λ x, W x)) (a, b)) =
      fun x ↦ ∑ k, W x a k * Λ x k * W x b k := by
    funext x
    simp only [entries, specMap_apply]
  rw [h]
  exact AllMoments.sum _ fun k _ ↦ ((hW a k).mul (hΛ k)).mul (hW b k)

/-! ### The coordinates -/

theorem allMoments_gaussianReal : AllMoments (gaussianReal 0 1) fun x ↦ x :=
  fun p ↦ memLp_id_gaussianReal p

theorem allMoments_dirac (s : ℝ) : AllMoments (Measure.dirac s) fun x ↦ x := by
  intro p
  refine MemLp.of_bound measurable_id.aestronglyMeasurable |s| ?_
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.2 (Real.norm_eq_abs s).le

theorem allMoments_eigLaw (γ : ℝ) [IsFiniteMeasure (eigLaw γ)] :
    AllMoments (eigLaw γ) fun x ↦ x :=
  fun p ↦ memLp_of_bounded (ae_eigLaw_mem γ) measurable_id.aestronglyMeasurable p

theorem allMoments_gaussMat {n m : ℕ} (a : Fin n) (k : Fin m) :
    AllMoments (gaussMat n m) fun U ↦ U a k := by
  have h1 : MeasurePreserving (fun U : Fin n → Fin m → ℝ ↦ U a) (gaussMat n m)
      (Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) := measurePreserving_eval _ a
  have h2 : MeasurePreserving (fun v : Fin m → ℝ ↦ v k)
      (Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
    measurePreserving_eval _ k
  exact (allMoments_gaussianReal.comp_measurePreserving h2).comp_measurePreserving h1

variable {n m : ℕ} {μs : Fin m → Measure ℝ} [∀ k, IsProbabilityMeasure (μs k)]

theorem allMoments_fst (hμ : ∀ k, AllMoments (μs k) fun x ↦ x) (k : Fin m) :
    AllMoments ((Measure.pi μs).prod (gaussMat n m)) fun p ↦ p.1 k :=
  ((hμ k).comp_measurePreserving (measurePreserving_eval μs k)).comp_measurePreserving
    measurePreserving_fst

theorem allMoments_snd (a : Fin n) (k : Fin m) :
    AllMoments ((Measure.pi μs).prod (gaussMat n m)) fun p ↦ p.2 a k :=
  (allMoments_gaussMat a k).comp_measurePreserving measurePreserving_snd

/-- `f(U diag(λ) Uᵀ)` has finite moments of every order when `λ` has independent coordinates with
finite moments of every order and `U` is Gaussian. -/
theorem allMoments_phi (hμ : ∀ k, AllMoments (μs k) fun x ↦ x)
    (f : MvPolynomial (Fin n × Fin n) ℝ) :
    AllMoments ((Measure.pi μs).prod (gaussMat n m)) (phi f) := by
  have h := allMoments_specMap (M := (Measure.pi μs).prod (gaussMat n m)) (fun p ↦ p.1)
    (fun p ↦ p.2) (allMoments_fst hμ) allMoments_snd f
  exact h

/-- The same with the coordinate `i` of `λ` replaced by `c`. -/
theorem allMoments_phi_update (hμ : ∀ k, AllMoments (μs k) fun x ↦ x)
    (f : MvPolynomial (Fin n × Fin n) ℝ) (i : Fin m) (c : ℝ) :
    AllMoments ((Measure.pi μs).prod (gaussMat n m))
      fun p ↦ phi f (Function.update p.1 i c, p.2) := by
  refine allMoments_specMap (M := (Measure.pi μs).prod (gaussMat n m))
    (fun p ↦ Function.update p.1 i c) (fun p ↦ p.2) (fun k ↦ ?_) allMoments_snd f
  by_cases hk : k = i
  · subst hk
    have h : (fun p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) ↦ Function.update p.1 k c k) =
        fun _ ↦ c := by
      funext p
      exact Function.update_self k c p.1
    rw [h]
    exact allMoments_const c
  · have h : (fun p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) ↦ Function.update p.1 i c k) =
        fun p ↦ p.1 k := by
      funext p
      exact Function.update_of_ne hk c p.1
    rw [h]
    exact allMoments_fst hμ k

end BHJK25.Spectral.LDAAux
