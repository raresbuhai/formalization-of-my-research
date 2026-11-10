module

public import ABBKS26.Tree.SoundAux
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Rounded reference resilience for refinement

The polynomial and affine estimates are copied from the learner helpers, in an independent
namespace, so the tree does not import its downstream selection layer.
-/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix MvPolynomial Finset SoS _root_.ABBKS26.Tree
open scoped BigOperators Nat MatrixOrder

variable {n k d : ℕ} {σ : Type*} {K : Type} [CommRing K]

/-- Rounding the clean points in their population coordinates. -/
def standardizedRounded (M : Mixture k d) (ω : Fin n → Triple k d)
    (r : Rounding k d) (l : Fin n) : Vec d :=
  fun i ↦ stdPt M (ω l).1 (WithLp.toLp 2 fun a ↦ (r ((ω l).1, (ω l).2.1) a : ℝ)) i

theorem standardizedRounded_error (M : Mixture k d) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hr : IsRounding M (1 / n) r)
    (l : Fin n) (i : Fin d) :
    |standardizedRounded M ω r l i - stdClean M ω l i| ≤ 1 / n := by
  exact (PiLp.norm_apply_le
    (stdPt M (ω l).1 (WithLp.toLp 2 fun a ↦ (r ((ω l).1, (ω l).2.1) a : ℝ)) -
      stdClean M ω l) i).trans
    (norm_stdPt_sub_le_of_isRounding hM (by positivity) hr _ _)


namespace Resilience

lemma factorial_two_mul_eq (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * (2 * n - 1).doubleFactorial := by
  rcases n with _ | n
  · simp
  · have h : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h, Nat.factorial_eq_mul_doubleFactorial, ← h, Nat.doubleFactorial_two_mul,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

/-- `(2r; 2β) ∏ᵢ (2βᵢ-1)‼ = (2r-1)‼ (r; β)` for `r = ∑ᵢ βᵢ`. -/
lemma multinomial_two_mul_mul_prod {ι : Type*} (s : Finset ι) (β : ι → ℕ) :
    Nat.multinomial s (fun i ↦ 2 * β i) * ∏ i ∈ s, (2 * β i - 1).doubleFactorial =
      (2 * ∑ i ∈ s, β i - 1).doubleFactorial * Nat.multinomial s β := by
  have h1 := Nat.multinomial_spec s (fun i ↦ 2 * β i)
  have h2 := Nat.multinomial_spec s β
  have hP : ∏ i ∈ s, (2 * β i).factorial =
      2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
        ∏ i ∈ s, (2 * β i - 1).doubleFactorial := by
    simp_rw [factorial_two_mul_eq, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpos : 0 < 2 ^ (∑ i ∈ s, β i) * ∏ i ∈ s, (β i).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc 2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
          (Nat.multinomial s (fun i ↦ 2 * β i) * ∏ i ∈ s, (2 * β i - 1).doubleFactorial)
        = (∏ i ∈ s, (2 * β i).factorial) * Nat.multinomial s (fun i ↦ 2 * β i) := by
          rw [hP]; ring
      _ = (2 * ∑ i ∈ s, β i).factorial := by rw [h1, Finset.mul_sum]
      _ = 2 ^ (∑ i ∈ s, β i) * (∏ i ∈ s, (β i).factorial) *
            ((2 * ∑ i ∈ s, β i - 1).doubleFactorial * Nat.multinomial s β) := by
          rw [factorial_two_mul_eq, ← h2]; ring

/-! ### Gaussian moments of a linear form -/

lemma gaussMom_two_mul (r : ℕ) : gaussMom (2 * r) = (2 * r - 1).doubleFactorial := by
  simp [gaussMom]

lemma gaussMomMulti_eq_zero {α : Fin d → ℕ} (h : ∃ i, ¬ Even (α i)) : gaussMomMulti α = 0 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])

/-- **Gaussian moments of a linear form**, written out with the multinomial theorem:
`∑_{|α| = p} (p; α) b^α E[G^α] = E[Z^p] ‖b‖^p`, i.e. `E ⟨b, G⟩^p = E Z^p ‖b‖^p` for a standard
Gaussian vector `G` (proved combinatorially). -/
theorem sum_multinomial_gaussMomMulti (b : Fin d → ℝ) (p : ℕ) :
    ∑ α ∈ (univ : Finset (Fin d)).piAntidiag p,
        (Nat.multinomial univ α : ℝ) * (∏ i, b i ^ α i) * (gaussMomMulti α : ℝ) =
      (gaussMom p : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ p := by
  by_cases hp : Even p
  · obtain ⟨r, rfl⟩ := hp
    rw [← two_mul]
    have hq : 0 ≤ ∑ i, b i ^ 2 := by positivity
    rw [pow_mul, Real.sq_sqrt hq, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    symm
    refine Finset.sum_of_injOn (fun β i ↦ 2 * β i) ?_ ?_ ?_ ?_
    · intro β _ β' _ h
      funext i
      have := congrFun h i
      simp only at this
      omega
    · intro β hβ
      simp only [mem_univ, implies_true, and_true,
        Finset.mem_coe, mem_piAntidiag] at hβ ⊢
      rw [← Finset.mul_sum, hβ]
    · intro α hα hnot
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hα
      have : ∃ i, ¬ Even (α i) := by
        by_contra hall
        push Not at hall
        apply hnot
        refine ⟨fun i ↦ α i / 2, ?_, ?_⟩
        · simp only [Finset.mem_coe, mem_piAntidiag, mem_univ, implies_true, and_true]
          have hα2 : ∀ i, α i = 2 * (α i / 2) := fun i ↦ (Nat.two_mul_div_two_of_even (hall i)).symm
          have : ∑ i, α i = 2 * ∑ i, α i / 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ hα2 i
          have hα' : ∑ i, α i = 2 * r := hα
          omega
        · funext i
          exact Nat.two_mul_div_two_of_even (hall i)
      simp [gaussMomMulti_eq_zero this]
    · intro β hβ
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hβ
      have hm := multinomial_two_mul_mul_prod univ β
      rw [hβ] at hm
      simp only [gaussMomMulti, gaussMom_two_mul]
      have hm' : ((Nat.multinomial univ fun i ↦ 2 * β i : ℕ) : ℝ) *
          ∏ i, ((2 * β i - 1).doubleFactorial : ℝ) =
          ((2 * r - 1).doubleFactorial : ℝ) * (Nat.multinomial univ β : ℝ) := by
        exact_mod_cast hm
      push_cast
      simp_rw [pow_mul]
      linear_combination (∏ i, (b i ^ 2) ^ β i) * hm'.symm
  · rw [show gaussMom p = 0 by simp [gaussMom, hp]]
    simp only [Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hα
    have : ∃ i, ¬ Even (α i) := by
      by_contra hall
      push Not at hall
      exact hp (hα ▸ Finset.even_sum _ fun i _ ↦ hall i)
    simp [gaussMomMulti_eq_zero this]


/-- The empirical `r`-th moment polynomial `|S|⁻¹ ∑_{j ∈ S} ⟨aⱼ, X⟩^r` of the points `aⱼ`,
`j ∈ S`. -/
noncomputable def empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    MvPolynomial (Fin d) ℝ :=
  (S.card : ℝ)⁻¹ • ∑ j ∈ S, lin (a j) ^ r

/-- The Gaussian `r`-th moment polynomial `E ⟨G, X⟩^r = E Z^r ‖X‖^r`, that is
`gaussMom r · (∑ᵢ Xᵢ²)^(r/2)` (`gaussMom r = 0` for odd `r`). -/
noncomputable def gaussPoly (r : ℕ) : MvPolynomial (Fin d) ℝ :=
  (gaussMom r : ℝ) • (∑ i, X i ^ 2) ^ (r / 2)

@[simp] lemma eval_lin (a b : Fin d → ℝ) : eval b (lin a) = ∑ i, a i * b i := by
  simp [lin]

lemma eval_empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) (b : Fin d → ℝ) :
    eval b (empMom S a r) = (S.card : ℝ)⁻¹ * ∑ j ∈ S, (∑ i, a j i * b i) ^ r := by
  simp [empMom, smul_eval]

lemma eval_gaussPoly (r : ℕ) (b : Fin d → ℝ) :
    eval b (gaussPoly r) = (gaussMom r : ℝ) * (∑ i, b i ^ 2) ^ (r / 2) := by
  simp [gaussPoly, smul_eval]

lemma gaussMom_eq_zero_of_not_even {r : ℕ} (hr : ¬ Even r) : gaussMom r = 0 := by
  simp [gaussMom, hr]

/-- `gaussMom r · (∑ bᵢ²)^(r/2) = gaussMom r · ‖b‖^r`: both vanish for odd `r`. -/
lemma gaussMom_mul_pow_div_two (r : ℕ) (b : Fin d → ℝ) :
    (gaussMom r : ℝ) * (∑ i, b i ^ 2) ^ (r / 2) =
      (gaussMom r : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ r := by
  by_cases hr : Even r
  · obtain ⟨s, rfl⟩ := hr
    rw [← two_mul, Nat.mul_div_cancel_left _ two_pos, pow_mul,
      Real.sq_sqrt (by positivity)]
  · simp [gaussMom_eq_zero_of_not_even hr]

lemma eval_gaussPoly' (r : ℕ) (b : Fin d → ℝ) :
    eval b (gaussPoly r) = (gaussMom r : ℝ) * Real.sqrt (∑ i, b i ^ 2) ^ r := by
  rw [eval_gaussPoly, gaussMom_mul_pow_div_two]

/-! ### The multinomial expansion -/

/-- The empirical moments minus the Gaussian ones, monomial by monomial:
`∑_{|α| = r} (r; α) (|S|⁻¹ ∑_{j ∈ S} aⱼ^α - m_α) X^α`. -/
lemma empMom_sub_gaussPoly_eq (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    empMom S a r - gaussPoly r = ∑ α ∈ (univ : Finset (Fin d)).piAntidiag r,
      ((Nat.multinomial univ α : ℝ) *
        ((S.card : ℝ)⁻¹ * ∑ j ∈ S, ∏ i, a j i ^ α i - (gaussMomMulti α : ℝ))) •
        ∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i := by
  apply MvPolynomial.funext
  intro b
  rw [map_sub, eval_empMom, eval_gaussPoly', ← sum_multinomial_gaussMomMulti, map_sum]
  simp only [smul_eval, map_prod, map_pow, eval_X]
  simp_rw [sum_pow_eq_sum_piAntidiag, mul_pow, prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have h : ∑ j ∈ S, (Nat.multinomial univ α : ℝ) * ((∏ i, a j i ^ α i) * ∏ i, b i ^ α i) =
      (Nat.multinomial univ α : ℝ) * (∏ i, b i ^ α i) * ∑ j ∈ S, ∏ i, a j i ^ α i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h]
  ring


lemma coeffNorm1_prod_X_pow_le (α : Fin d → ℕ) :
    coeffNorm1 (∏ i, (X i : MvPolynomial (Fin d) ℝ) ^ α i) ≤ 1 :=
  (coeffNorm1_prod_le _ _).trans (Finset.prod_le_one₀ (fun _ _ ↦ coeffNorm1_nonneg _)
    fun i _ ↦ (coeffNorm1_pow_le _ _).trans (by rw [coeffNorm1_X, one_pow]))

lemma coeffNorm1_lin_le (a : Fin d → ℝ) : coeffNorm1 (lin a) ≤ ∑ i, |a i| :=
  (coeffNorm1_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ by rw [coeffNorm1_C_mul, coeffNorm1_X, mul_one])


lemma lin_add (a b : Fin d → ℝ) : lin (a + b) = lin a + lin b := by
  simp [lin, add_mul, Finset.sum_add_distrib]


lemma lin_sub (a b : Fin d → ℝ) : lin (a - b) = lin a - lin b := by
  simp [lin, sub_mul, Finset.sum_sub_distrib]


/-- `‖(A + E)^(r+1) - A^(r+1)‖₁ ≤ (r + 1) e (a + e)^r` if `‖A‖₁ ≤ a` and `‖E‖₁ ≤ e`. -/
lemma coeffNorm1_add_pow_succ_sub_le {σ : Type*} (A E : MvPolynomial σ ℝ) {a e : ℝ}
    (ha : coeffNorm1 A ≤ a) (he : coeffNorm1 E ≤ e) (r : ℕ) :
    coeffNorm1 ((A + E) ^ (r + 1) - A ^ (r + 1)) ≤ (r + 1) * e * (a + e) ^ r := by
  have ha0 : 0 ≤ a := (coeffNorm1_nonneg A).trans ha
  have he0 : 0 ≤ e := (coeffNorm1_nonneg E).trans he
  have hAE : coeffNorm1 (A + E) ≤ a + e := (coeffNorm1_add_le _ _).trans (add_le_add ha he)
  induction r with
  | zero => simpa using he
  | succ r ih =>
    have heq : (A + E) ^ (r + 1 + 1) - A ^ (r + 1 + 1) =
        (A + E) * ((A + E) ^ (r + 1) - A ^ (r + 1)) + E * A ^ (r + 1) := by ring
    have hApow : coeffNorm1 (A ^ (r + 1)) ≤ (a + e) ^ (r + 1) :=
      (coeffNorm1_pow_le _ _).trans
        (pow_le_pow_left₀ (coeffNorm1_nonneg _) (ha.trans (by linarith)) _)
    rw [heq]
    calc coeffNorm1 ((A + E) * ((A + E) ^ (r + 1) - A ^ (r + 1)) + E * A ^ (r + 1))
        ≤ coeffNorm1 (A + E) * coeffNorm1 ((A + E) ^ (r + 1) - A ^ (r + 1)) +
            coeffNorm1 E * coeffNorm1 (A ^ (r + 1)) :=
          (coeffNorm1_add_le _ _).trans (add_le_add (coeffNorm1_mul_le _ _) (coeffNorm1_mul_le _ _))
      _ ≤ (a + e) * ((r + 1) * e * (a + e) ^ r) + e * (a + e) ^ (r + 1) :=
          add_le_add (mul_le_mul hAE ih (coeffNorm1_nonneg _) (by positivity))
            (mul_le_mul he hApow (coeffNorm1_nonneg _) he0)
      _ = ((r + 1 : ℕ) + 1 : ℝ) * e * (a + e) ^ (r + 1) := by push_cast; ring

/-- `‖(A + E)^r - A^r‖₁ ≤ r e (a + e)^(r-1)` if `‖A‖₁ ≤ a` and `‖E‖₁ ≤ e`. -/
lemma coeffNorm1_add_pow_sub_le {σ : Type*} (A E : MvPolynomial σ ℝ) {a e : ℝ}
    (ha : coeffNorm1 A ≤ a) (he : coeffNorm1 E ≤ e) (r : ℕ) :
    coeffNorm1 ((A + E) ^ r - A ^ r) ≤ r * e * (a + e) ^ (r - 1) := by
  rcases r with _ | r
  · simp
  · simpa using coeffNorm1_add_pow_succ_sub_le A E ha he r

/-- `(G + 1)^p ≤ 2^p (1 + G^q)` for `G ≥ 0` and `p ≤ q`. -/
lemma add_one_pow_le_two_pow_mul {G : ℝ} (hG : 0 ≤ G) {p q : ℕ} (hpq : p ≤ q) :
    (G + 1) ^ p ≤ 2 ^ p * (1 + G ^ q) := by
  have hM : 1 ≤ max G 1 := le_max_right _ _
  calc (G + 1) ^ p ≤ (2 * max G 1) ^ p :=
        pow_le_pow_left₀ (by positivity) (by linarith [le_max_left G 1, le_max_right G 1]) p
    _ = 2 ^ p * max G 1 ^ p := mul_pow _ _ _
    _ ≤ 2 ^ p * max G 1 ^ q := by gcongr
    _ ≤ 2 ^ p * (1 + G ^ q) := by
        gcongr
        rcases le_total G 1 with hG1 | hG1
        · rw [max_eq_right hG1, one_pow]; linarith [pow_nonneg hG q]
        · rw [max_eq_left hG1]; linarith

/-! ### Homogeneity -/

lemma isHomogeneous_lin (a : Fin d → ℝ) : (lin a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

lemma isHomogeneous_empMom (S : Finset (Fin n)) (a : Fin n → Fin d → ℝ) (r : ℕ) :
    (empMom S a r).IsHomogeneous r := by
  rw [empMom, smul_eq_C_mul]
  refine IsHomogeneous.C_mul (IsHomogeneous.sum _ _ _ fun j _ ↦ ?_) _
  simpa using (isHomogeneous_lin (a j)).pow r

lemma isHomogeneous_gaussPoly (r : ℕ) : (gaussPoly (d := d) r).IsHomogeneous r := by
  by_cases hr : Even r
  · obtain ⟨s, rfl⟩ := hr
    rw [gaussPoly, smul_eq_C_mul]
    refine IsHomogeneous.C_mul ?_ _
    have h2 : (∑ i, (X i : MvPolynomial (Fin d) ℝ) ^ 2).IsHomogeneous 2 :=
      IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow _ _
    have := h2.pow ((s + s) / 2)
    rwa [show 2 * ((s + s) / 2) = s + s by omega] at this
  · simp only [gaussPoly, gaussMom_eq_zero_of_not_even hr, Nat.cast_zero, zero_smul]
    exact isHomogeneous_zero _ _ _


/-- Substitution: `‖p(forms)‖₁ ≤ ∑_m |p_m| β^|m|` if every `‖formsᵢ‖₁ ≤ β`. -/
lemma coeffNorm1_aeval_le_sum {σ τ : Type*} [Finite σ] (forms : σ → MvPolynomial τ ℝ) {β : ℝ}
    (hforms : ∀ i, coeffNorm1 (forms i) ≤ β) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (aeval forms p) ≤ ∑ m ∈ p.support, |p.coeff m| * β ^ m.degree := by
  have := Fintype.ofFinite σ
  rw [aeval_def, eval₂_eq']
  refine (coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [algebraMap_eq, coeffNorm1_C_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc coeffNorm1 (∏ i, forms i ^ m i) ≤ ∏ i, coeffNorm1 (forms i ^ m i) := coeffNorm1_prod_le _ _
    _ ≤ ∏ i, β ^ m i :=
        Finset.prod_le_prod₀ (fun _ _ ↦ coeffNorm1_nonneg _) fun i _ ↦
          (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hforms i) _)
    _ = β ^ m.degree := by rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]

/-- Substitution into a homogeneous polynomial of degree `r`: `‖p(forms)‖₁ ≤ ‖p‖₁ β^r` if every
`‖formsᵢ‖₁ ≤ β`. -/
lemma coeffNorm1_aeval_le_of_isHomogeneous {σ τ : Type*} [Finite σ] (forms : σ → MvPolynomial τ ℝ)
    {β : ℝ} (hforms : ∀ i, coeffNorm1 (forms i) ≤ β) {p : MvPolynomial σ ℝ} {r : ℕ}
    (hp : p.IsHomogeneous r) : coeffNorm1 (aeval forms p) ≤ coeffNorm1 p * β ^ r := by
  refine (coeffNorm1_aeval_le_sum forms hforms p).trans_eq ?_
  rw [coeffNorm1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [hp.degree_eq_sum_deg_support hm, ← Finsupp.degree_apply]


lemma aeval_lin {τ : Type*} (forms : Fin d → MvPolynomial τ ℝ) (a : Fin d → ℝ) :
    aeval forms (lin a) = ∑ i, C (a i) * forms i := by
  simp [lin, algebraMap_eq]


lemma aeval_gaussPoly {τ : Type*} (forms : Fin d → MvPolynomial τ ℝ) (r : ℕ) :
    aeval forms (gaussPoly r) = (gaussMom r : ℝ) • (∑ i, forms i ^ 2) ^ (r / 2) := by
  simp [gaussPoly, map_smul]


/-- `IdCov.hmom r a v = ∑_q C(r, q) a^(r-q) E Z^q v^(q/2)`: the binomial expansion of
`E (a + √v Z)^r`, written without the square root. -/
theorem hmom_eq_sum_choose (r : ℕ) (a v : K) :
    IdCov.hmom r a v = ∑ q ∈ range (r + 1),
      (r.choose q : K) * a ^ (r - q) * (gaussMom q : K) * v ^ (q / 2) := by
  have hsub : (range (r / 2 + 1)).image (fun i ↦ 2 * i) ⊆ range (r + 1) := by
    intro p hp
    simp only [mem_image, mem_range] at hp ⊢
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · rw [IdCov.hmom]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [IdCov.hermCoeff, gaussMom, even_two_mul, ite_true, Nat.cast_mul,
      Nat.mul_div_cancel_left _ two_pos]
    ring
  · intro i _ j _ h
    simpa using h
  · intro p hp hp'
    have hodd : ¬ Even p := by
      rintro ⟨i, rfl⟩
      apply hp'
      simp only [mem_image, mem_range] at hp ⊢
      exact ⟨i, by omega, by omega⟩
    simp [gaussMom, hodd]


/-- `∑_{j ∈ s} (A + Z_j)^r = ∑_q C(r, q) A^(r-q) ∑_{j ∈ s} Z_j^q`. -/
theorem sum_add_pow_eq {ι : Type*} (s : Finset ι) (A : MvPolynomial σ ℝ)
    (Z : ι → MvPolynomial σ ℝ) (r : ℕ) :
    ∑ j ∈ s, (A + Z j) ^ r =
      ∑ q ∈ range (r + 1), (r.choose q : MvPolynomial σ ℝ) * (A ^ (r - q) * ∑ j ∈ s, Z j ^ q) := by
  simp_rw [add_comm A, add_pow]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring


/-- A monomial error bound controls the entire homogeneous moment polynomial. -/
theorem monomial_error (S : Finset (Fin n)) (g : Fin n → Vec d) (δ : ℝ)
    (hδ : 0 ≤ δ) (r : ℕ)
    (hm : ∀ α : Fin d → ℕ, (∑ i, α i) ≤ r →
      |(S.card : ℝ)⁻¹ * ∑ l ∈ S, ∏ i, g l i ^ α i - gaussMomMulti α| ≤ δ) :
    coeffNorm1 (empMom S g r - gaussPoly r) ≤ δ * (d : ℝ) ^ r := by
  rw [empMom_sub_gaussPoly_eq]
  refine (coeffNorm1_sum_le _ _).trans ?_
  have hsum : ∑ α ∈ (univ : Finset (Fin d)).piAntidiag r,
      (Nat.multinomial univ α : ℝ) = (d : ℝ) ^ r := by
    have := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin d)) (fun _ ↦ (1 : ℝ)) r
    simpa using this.symm
  rw [← hsum, Finset.mul_sum]
  refine sum_le_sum fun α hα ↦ ?_
  rw [coeffNorm1_smul, abs_mul, Nat.abs_cast]
  have hαr : ∑ i, α i ≤ r := le_of_eq (mem_piAntidiag.mp hα).1
  calc
    _ ≤ (Nat.multinomial univ α : ℝ) * δ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hm α hαr) (Nat.cast_nonneg _))
        (coeffNorm1_prod_X_pow_le α) (coeffNorm1_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hδ)
    _ = _ := by ring

/-- The sample schedule retains a factor of `η` in the inverse sample bound. -/
theorem inverse_sample_relative
    (M : Mixture k d) (w η : ℝ) (D : ℕ) (hM : M.Valid)
    (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j) (hη : 0 < η) (hη100 : η ≤ 1 / 100)
    (hD : 8 ≤ D) (hn : sampleNeed w η (1 / 2) k d D ≤ n) (j : Fin k) :
    1 / (n : ℝ) ≤ η / (10 ^ 12 * (d + 1 : ℝ) ^ 20) := by
  have hw1 : w ≤ 1 := (hwj j).trans (hM.sum_w ▸
    single_le_sum (fun i _ ↦ hM.nonneg_w i) (mem_univ j))
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast j.pos
  have hD8 : (8 : ℝ) ≤ D := by exact_mod_cast hD
  let K : ℝ := (64 * D / w) ^ (4 * D)
  have hbase : (512 : ℝ) ≤ 64 * D / w := by
    rw [le_div_iff₀ hw]
    nlinarith only [hD8, hw1]
  have hK : (10 : ℝ) ^ 12 ≤ K := by
    calc
      _ ≤ (512 : ℝ) ^ 32 := by norm_num
      _ ≤ (64 * D / w) ^ 32 := pow_le_pow_left₀ (by norm_num) hbase 32
      _ ≤ K := pow_le_pow_right₀ (by linarith only [hbase]) (by omega)
  have hK1 : 1 ≤ K := (by norm_num : (1 : ℝ) ≤ 10 ^ 12).trans hK
  have hKsq : K ≤ K ^ 2 := by nlinarith only [hK1]
  have hpow : (1 : ℝ) ≤ (2 * D : ℝ) ^ D :=
    one_le_pow₀ (by linarith only [hD8])
  have hcoef : K ≤ 32 * k * K ^ 2 * (2 * D : ℝ) ^ D := by
    calc
      K = 1 * 1 * K * 1 := by ring
      _ ≤ 32 * k * K ^ 2 * (2 * D : ℝ) ^ D := by gcongr; norm_num
  have hden : 0 < w * η ^ 2 * (1 / 2) := by positivity
  have hdenη : w * η ^ 2 * (1 / 2) ≤ η := by
    have hh := mul_le_mul_of_nonneg_right hw1 (sq_nonneg η)
    nlinarith only [hh, hη, hη100]
  have hlast : 32 * k * K ^ 2 * (2 * D : ℝ) ^ D *
      (d + 1 : ℝ) ^ (9 * D) / (w * η ^ 2 * (1 / 2)) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hn))
  have ht : (1 : ℝ) ≤ d + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) d]
  have ht20 : (d + 1 : ℝ) ^ 20 ≤ (d + 1 : ℝ) ^ (9 * D) :=
    pow_le_pow_right₀ ht (by omega)
  have hsize : 10 ^ 12 * (d + 1 : ℝ) ^ 20 ≤ (n : ℝ) * η := by
    calc
      _ ≤ K * (d + 1 : ℝ) ^ (9 * D) :=
        mul_le_mul hK ht20 (by positivity) (by positivity)
      _ ≤ 32 * k * K ^ 2 * (2 * D : ℝ) ^ D * (d + 1 : ℝ) ^ (9 * D) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (n : ℝ) * (w * η ^ 2 * (1 / 2)) := (div_le_iff₀ hden).mp hlast
      _ ≤ (n : ℝ) * η := mul_le_mul_of_nonneg_left hdenη (Nat.cast_nonneg n)
  have hn0 : (0 : ℝ) < n := by
    have hh : 0 < (n : ℝ) * η := lt_of_lt_of_le (by positivity) hsize
    rcases mul_pos_iff.mp hh with hh | hh
    · exact hh.1
    · exact False.elim (not_lt_of_ge hη.le hh.2)
  rw [div_le_div_iff₀ hn0 (by positivity)]
  simpa only [one_mul, mul_comm] using hsize

lemma lin_mulVec (H : Mat d) (g : Vec d) :
    lin (H *ᵥ g) = ∑ i, C (g i) * lin (fun l ↦ H l i) := by
  simp only [lin, mulVec, dotProduct, map_sum, map_mul, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun l _ ↦ by ring

lemma eval_lin_eq (v x : Vec d) : eval x (lin v) = v ⬝ᵥ x := by
  simp [lin, dotProduct]

lemma eval_quad_eq (A : Mat d) (x : Vec d) : eval x (quad A) = qform A x := by
  simp only [quad, map_sum, map_mul, eval_C, eval_X, qform, mulVec, dotProduct,
    mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

lemma quad_mul_transpose (H : Mat d) :
    quad (H * Hᵀ) = ∑ i, lin (fun l ↦ H l i) ^ 2 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_quad_eq]
  simp only [map_sum, map_pow, eval_lin_eq]
  rw [qform, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec, transpose_apply, pow_two]

lemma empMom_affine (S : Finset (Fin n)) (g : Fin n → Vec d) (H : Mat d)
    (b : Vec d) (r : ℕ) :
    empMom S (fun l ↦ b + H *ᵥ g l) r =
      ∑ q ∈ range (r + 1), (r.choose q : RPoly d) *
        (lin b ^ (r - q) * aeval (fun i ↦ lin (fun l ↦ H l i)) (empMom S g q)) := by
  simp only [empMom, lin_add, lin_mulVec]
  rw [sum_add_pow_eq, smul_sum]
  apply sum_congr rfl
  intro q _
  simp only [map_smul, map_sum, map_pow, aeval_lin]
  simp only [smul_eq_C_mul]
  ring

lemma hmom_affine (H : Mat d) (b : Vec d) (r : ℕ) :
    IdCov.hmom r (lin b) (quad (H * Hᵀ)) =
      ∑ q ∈ range (r + 1), (r.choose q : RPoly d) *
        (lin b ^ (r - q) * aeval (fun i ↦ lin (fun l ↦ H l i)) (gaussPoly q)) := by
  rw [quad_mul_transpose, hmom_eq_sum_choose]
  apply sum_congr rfl
  intro q _
  rw [aeval_gaussPoly, smul_eq_C_mul, C_eq_natCast]
  ring

lemma coeffNorm1_natCast_mul (c : ℕ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 ((c : MvPolynomial σ ℝ) * p) = c * coeffNorm1 p := by
  rw [← map_natCast (C : ℝ →+* MvPolynomial σ ℝ) c, coeffNorm1_C_mul, Nat.abs_cast]

/-- Homogeneous substitution and the binomial theorem give a bound in every affine frame. -/
theorem affine_error (S : Finset (Fin n)) (g : Fin n → Vec d) (H : Mat d)
    (b : Vec d) (r : ℕ) (δ β : ℝ) (hβ : 0 ≤ β)
    (hcols : ∀ i, coeffNorm1 (lin (fun l ↦ H l i)) ≤ β)
    (hm : ∀ q ≤ r, coeffNorm1 (empMom S g q - gaussPoly q) ≤ δ) :
    coeffNorm1 (empMom S (fun l ↦ b + H *ᵥ g l) r -
      IdCov.hmom r (lin b) (quad (H * Hᵀ))) ≤ δ * (coeffNorm1 (lin b) + β) ^ r := by
  let forms (i : Fin d) := lin (fun l ↦ H l i)
  have hsub (q : ℕ) (hq : q ≤ r) :
      coeffNorm1 (aeval forms (empMom S g q - gaussPoly q)) ≤ δ * β ^ q := by
    exact (coeffNorm1_aeval_le_of_isHomogeneous forms hcols
      ((isHomogeneous_empMom S g q).sub (isHomogeneous_gaussPoly q))).trans
        (mul_le_mul_of_nonneg_right (hm q hq) (pow_nonneg hβ q))
  rw [empMom_affine, hmom_affine, ← sum_sub_distrib]
  simp only [← mul_sub, ← map_sub]
  apply (coeffNorm1_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ range (r + 1), (r.choose q : ℝ) *
        (coeffNorm1 (lin b) ^ (r - q) * (δ * β ^ q)) := by
      apply sum_le_sum
      intro q hq
      rw [coeffNorm1_natCast_mul]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact (coeffNorm1_mul_le _ _).trans
        (mul_le_mul (coeffNorm1_pow_le _ _) (hsub q (by simpa using hq))
          (coeffNorm1_nonneg _) (pow_nonneg (coeffNorm1_nonneg _) _))
    _ = δ * (coeffNorm1 (lin b) + β) ^ r := by
      rw [add_comm (coeffNorm1 (lin b)), add_pow, mul_sum]
      exact sum_congr rfl fun q _ ↦ by ring

/-- The population quadratic controls every entry of a factor, including singular factors. -/
lemma factor_entry_bound (H : Mat d) (i a : Fin d) :
    |H i a| ≤ 1 + coeffNorm1 (quad (H * Hᵀ)) := by
  let Q := coeffNorm1 (quad (H * Hᵀ))
  have hQ : 0 ≤ Q := coeffNorm1_nonneg _
  have hx : ∀ b : Fin d, |(Pi.single i 1 : Vec d) b| ≤ 1 := by
    intro b
    by_cases hb : i = b <;> simp [hb]
  have heval := SoS.abs_eval_le (p := quad (H * Hᵀ)) (by norm_num : (1 : ℝ) ≤ 1) hx
  simp only [one_pow, mul_one, eval_quad_eq, qform] at heval
  have he : (Pi.single i 1 : Vec d) ⬝ᵥ ((H * Hᵀ) *ᵥ Pi.single i 1) =
      ∑ b, H i b ^ 2 := by
    rw [single_dotProduct, one_mul, mulVec_single_one]
    change (H * Hᵀ) i i = ∑ b, H i b ^ 2
    simp only [Matrix.mul_apply, transpose_apply, pow_two]
  rw [he] at heval
  have hi : H i a ^ 2 ≤ Q :=
    (single_le_sum (fun b _ ↦ sq_nonneg (H i b)) (mem_univ a)).trans
      ((le_abs_self _).trans heval)
  have habs : |H i a| ≤ Real.sqrt Q := Real.abs_le_sqrt hi
  have hroot : Real.sqrt Q ≤ 1 + Q := by
    have := Real.sq_sqrt hQ
    nlinarith only [this, sq_nonneg (Real.sqrt Q - 1 / 2)]
  exact habs.trans hroot

lemma factor_column_bound (H : Mat d) (a : Fin d) :
    coeffNorm1 (lin (fun l ↦ H l a)) ≤
      (d + 1 : ℝ) * (1 + coeffNorm1 (quad (H * Hᵀ))) := by
  calc
    _ ≤ ∑ i, |H i a| := coeffNorm1_lin_le _
    _ ≤ ∑ _i : Fin d, (1 + coeffNorm1 (quad (H * Hᵀ))) :=
      sum_le_sum fun i _ ↦ factor_entry_bound H i a
    _ = (d : ℝ) * (1 + coeffNorm1 (quad (H * Hᵀ))) := by simp; ring
    _ ≤ _ := by nlinarith only [coeffNorm1_nonneg (quad (H * Hᵀ))]


/-- Even coordinate moments control the corresponding power of the coordinate sum. -/
theorem average_l1_even (S : Finset (Fin n)) (g : Fin n → Vec d)
    (s : ℕ) (hs : 0 < s) (heven : Even s) (B : ℝ) (_hB : 0 ≤ B)
    (hm : ∀ i, Robust.FilterAux.average S (fun l ↦ g l i ^ s) ≤ B) :
    Robust.FilterAux.average S (fun l ↦ (∑ i, |g l i|) ^ s) ≤ B * (d : ℝ) ^ s := by
  have hs' : s - 1 + 1 = s := by omega
  have hpoint (l : Fin n) :
      (∑ i, |g l i|) ^ s ≤ (d : ℝ) ^ (s - 1) * ∑ i, g l i ^ s := by
    simpa only [hs', card_univ, Fintype.card_fin, heven.pow_abs] using
      pow_sum_le_card_mul_sum_pow (s := univ) (f := fun i ↦ |g l i|)
        (fun _ _ ↦ abs_nonneg _) (s - 1)
  have hh := Robust.FilterAux.average_mono S _ _ (fun l _ ↦ hpoint l)
  have he : (fun l ↦ (d : ℝ) ^ (s - 1) * ∑ i, g l i ^ s) =
      (d : ℝ) ^ (s - 1) • ∑ i, (fun l ↦ g l i ^ s) := by ext; simp
  rw [he, map_smul, map_sum] at hh
  change _ ≤ (d : ℝ) ^ (s - 1) * ∑ i,
    Robust.FilterAux.average S (fun l ↦ g l i ^ s) at hh
  calc
    _ ≤ (d : ℝ) ^ (s - 1) * ∑ i,
        Robust.FilterAux.average S (fun l ↦ g l i ^ s) := hh
    _ ≤ (d : ℝ) ^ (s - 1) * ∑ _i : Fin d, B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun i _ ↦ hm i
    _ = B * (d : ℝ) ^ s := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        _ = B * ((d : ℝ) ^ (s - 1) * d) := by ring
        _ = _ := by rw [← pow_succ, hs']

/-- The rounding estimate works at any positive even degree, including the IdCov budget. -/
theorem rounding_error_even (S : Finset (Fin n)) (hS : S.Nonempty)
    (g h : Fin n → Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : (d : ℝ) * τ ≤ 1)
    (herr : ∀ l, ∀ i, |h l i - g l i| ≤ τ)
    (s : ℕ) (hs : 0 < s) (heven : Even s) (B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ i, Robust.FilterAux.average S (fun l ↦ g l i ^ s) ≤ B)
    (r : ℕ) (hr : r ≤ s) :
    coeffNorm1 (empMom S h r - empMom S g r) ≤
      τ * (s * 2 ^ s * (1 + B)) * (d + 1 : ℝ) ^ (s + 1) := by
  let e := (d : ℝ) * τ
  let G (l : Fin n) := ∑ i, |g l i|
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hlin (l : Fin n) : coeffNorm1 (lin (h l - g l)) ≤ e := by
    apply (coeffNorm1_lin_le _).trans
    calc
      _ ≤ ∑ _i : Fin d, τ := sum_le_sum fun i _ ↦ herr l i
      _ = e := by simp [e]
  have hterm (l : Fin n) :
      coeffNorm1 (lin (h l) ^ r - lin (g l) ^ r) ≤
        (s : ℝ) * 2 ^ s * e * (1 + G l ^ s) := by
    have heq : lin (h l) = lin (g l) + lin (h l - g l) := by rw [lin_sub]; ring
    rw [heq]
    apply (coeffNorm1_add_pow_sub_le _ _ (coeffNorm1_lin_le _) (hlin l) r).trans
    have hG : 0 ≤ G l := by dsimp only [G]; positivity
    have hpow := add_one_pow_le_two_pow_mul hG (show r - 1 ≤ s by omega)
    have hcoef : (r : ℝ) * 2 ^ (r - 1) ≤ (s : ℝ) * 2 ^ s :=
      mul_le_mul (by exact_mod_cast hr) (pow_le_pow_right₀ (by norm_num) (by omega))
        (by positivity) (Nat.cast_nonneg s)
    calc
      _ ≤ (r : ℝ) * e * (G l + 1) ^ (r - 1) := by gcongr
      _ ≤ (r : ℝ) * e * (2 ^ (r - 1) * (1 + G l ^ s)) := by gcongr
      _ = ((r : ℝ) * 2 ^ (r - 1)) * (e * (1 + G l ^ s)) := by ring
      _ ≤ ((s : ℝ) * 2 ^ s) * (e * (1 + G l ^ s)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  have hdiff : empMom S h r - empMom S g r =
      (S.card : ℝ)⁻¹ • ∑ l ∈ S, (lin (h l) ^ r - lin (g l) ^ r) := by
    simp only [empMom, ← smul_sub, ← sum_sub_distrib]
  have hbound : coeffNorm1 (empMom S h r - empMom S g r) ≤
      (s : ℝ) * 2 ^ s * e * (1 + B * (d : ℝ) ^ s) := by
    rw [hdiff, coeffNorm1_smul, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (S.card : ℝ)⁻¹ * ∑ l ∈ S,
          ((s : ℝ) * 2 ^ s * e * (1 + G l ^ s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (coeffNorm1_sum_le _ _).trans (sum_le_sum fun l _ ↦ hterm l)
      _ = (s : ℝ) * 2 ^ s * e *
          (1 + Robust.FilterAux.average S (fun l ↦ G l ^ s)) := by
        have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ne_zero.mpr hS)
        simp only [Robust.FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk,
          mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add_right (average_l1_even S g s hs heven B hB hm) 1) (by positivity)
  apply hbound.trans
  have ht : (1 : ℝ) ≤ d + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hd : (d : ℝ) ≤ d + 1 := by linarith
  have hp : (d : ℝ) ^ s ≤ (d + 1 : ℝ) ^ s :=
    pow_le_pow_left₀ (by positivity) hd s
  have hp1 : (1 : ℝ) ≤ (d + 1 : ℝ) ^ s := one_le_pow₀ ht
  have hb : 1 + B * (d : ℝ) ^ s ≤ (1 + B) * (d + 1 : ℝ) ^ s := by
    nlinarith only [mul_le_mul_of_nonneg_left hp hB, hp1]
  calc
    _ ≤ (s : ℝ) * 2 ^ s * ((d + 1 : ℝ) * τ) * ((1 + B) * (d + 1 : ℝ) ^ s) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd hτ)
          (by positivity)
      · exact hb
      · positivity
      · positivity
    _ = _ := by rw [pow_succ]; ring

/-- Monomial control bounds every even coordinate moment. -/
theorem coordinate_even (S : Finset (Fin n)) (g : Fin n → Vec d) (δ : ℝ) (s : ℕ)
    (hm : ∀ α : Fin d → ℕ, (∑ i, α i) ≤ s →
      |(S.card : ℝ)⁻¹ * ∑ l ∈ S, ∏ i, g l i ^ α i - gaussMomMulti α| ≤ δ)
    (i : Fin d) : Robust.FilterAux.average S (fun l ↦ g l i ^ s) ≤ gaussMom s + δ := by
  have h := hm (Pi.single i s) (by simp)
  have he (l : Fin n) : ∏ a, g l a ^ (Pi.single i s : Fin d → ℕ) a = g l i ^ s := by
    rw [Fintype.prod_eq_single i (fun a ha ↦ by simp [ha])]
    simp
  have hg : gaussMomMulti (Pi.single i s : Fin d → ℕ) = gaussMom s := by
    rw [gaussMomMulti, Fintype.prod_eq_single i (fun a ha ↦ by simp [ha, gaussMom])]
    simp
  simp only [he, hg] at h
  change (S.card : ℝ)⁻¹ * ∑ l ∈ S, g l i ^ s ≤ gaussMom s + δ
  linarith only [(abs_le.mp h).2]

/-- Rounded moment bounds at arbitrary even degree, with the numerical budget explicit. -/
theorem rounded_moments_even (S : Finset (Fin n)) (hS : S.Nonempty)
    (g h : Fin n → Vec d) (s : ℕ) (hs : 0 < s) (heven : Even s)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hsmall : (d : ℝ) * τ ≤ 1)
    (hm : ∀ α : Fin d → ℕ, (∑ i, α i) ≤ s →
      |(S.card : ℝ)⁻¹ * ∑ l ∈ S, ∏ i, g l i ^ α i - gaussMomMulti α| ≤ δ)
    (herr : ∀ l i, |h l i - g l i| ≤ τ) (q : ℕ) (hq : q ≤ s) :
    coeffNorm1 (empMom S h q - gaussPoly q) ≤
      δ * (d : ℝ) ^ q + τ * (s * 2 ^ s * (1 + (gaussMom s : ℝ) + δ)) *
        (d + 1 : ℝ) ^ (s + 1) := by
  have hc := monomial_error S g δ hδ q (fun α hα ↦ hm α (hα.trans hq))
  have he := rounding_error_even S hS g h τ hτ hsmall herr s hs heven
    (gaussMom s + δ) (by positivity) (coordinate_even S g δ s hm) q hq
  have heq : empMom S h q - gaussPoly q =
      (empMom S h q - empMom S g q) + (empMom S g q - gaussPoly q) := by ring
  rw [heq]
  apply (coeffNorm1_add_le _ _).trans ((add_le_add he hc).trans_eq ?_)
  ring

/-- A uniform coefficient bound transfers to every affine frame at the same degree. -/
theorem affine_moments (S : Finset (Fin n)) (g : Fin n → Vec d) (s : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ)
    (hm : ∀ q ≤ s, coeffNorm1 (empMom S g q - gaussPoly q) ≤
      θ / (d + 1 : ℝ) ^ (3 * s))
    (H : Mat d) (b : Vec d) (q : ℕ) (hq : q ≤ s) :
    coeffNorm1 (empMom S (fun l ↦ b + H *ᵥ g l) q -
      IdCov.hmom q (lin b) (quad (H * Hᵀ))) ≤
      (θ / (d + 1 : ℝ) ^ (2 * s)) *
        (1 + coeffNorm1 (lin b) + coeffNorm1 (quad (H * Hᵀ))) ^ q := by
  let t : ℝ := d + 1
  let A := coeffNorm1 (lin b)
  let Q := coeffNorm1 (quad (H * Hᵀ))
  let δ := θ / t ^ (3 * s)
  let β := t * (1 + Q)
  have ht : 1 ≤ t := by dsimp only [t]; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hA : 0 ≤ A := coeffNorm1_nonneg _
  have hQ : 0 ≤ Q := coeffNorm1_nonneg _
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hb := affine_error S g H b q δ β (by dsimp only [β]; positivity)
    (factor_column_bound H) (fun a ha ↦ hm a (ha.trans hq))
  have hbase : A + β ≤ t * (1 + A + Q) := by
    have hh := mul_nonneg (sub_nonneg.mpr ht) hA
    dsimp only [β]
    nlinarith only [hh]
  have hscale : δ * t ^ q ≤ θ / t ^ (2 * s) := by
    calc
      _ ≤ δ * t ^ s := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hq) hδ
      _ = θ / t ^ (2 * s) := by
        dsimp only [δ]
        rw [show 3 * s = 2 * s + s by omega, pow_add]
        field_simp
  apply hb.trans
  calc
    _ ≤ δ * (t * (1 + A + Q)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase q) hδ
    _ = (δ * t ^ q) * (1 + A + Q) ^ q := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)

/-- The standardized rounded estimates imply resilience of any matching reference.
The matching conditions also cover a relabelled subset of mixture components. -/
theorem rounded_reference_resilient {m : ℕ}
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (hM : M.Valid) (R : Robust.Reference n m d) (component : Fin m → Fin k)
    (hmean : ∀ j, R.model.mean j = M.μ (component j))
    (hcov : ∀ j, R.model.cov j = M.S (component j))
    (hcluster : ∀ j, R.reference.filter (fun l ↦ R.label l = j) =
      cluster (labels ω) (component j))
    (hclean : ∀ l, R.clean l = fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ))
    (s : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hm : ∀ j q, q ≤ s →
      coeffNorm1 (empMom (cluster (labels ω) (component j))
        (standardizedRounded M ω r) q - gaussPoly q) ≤
        θ / (d + 1 : ℝ) ^ (3 * s)) : R.Resilient s θ := by
  intro T a j q hq
  let B := CFC.sqrt (M.S (component j))
  let H := T * B
  let b := T *ᵥ (M.μ (component j) - a)
  let g := standardizedRounded M ω r
  have hBsym : Bᵀ = B := (Robust.RBAux.sqrt_properties _ (hM.posDef _)).1
  have hBunit : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr (Robust.RBAux.sqrt_properties _ (hM.posDef _)).2.1
  have hH : H * Hᵀ = T * M.S (component j) * Tᵀ := by
    calc
      _ = T * (B * B) * Tᵀ := by simp only [H, transpose_mul, hBsym, mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ (hM.posDef _).posSemidef.nonneg]
  have hpoint (l : Fin n) (hl : l ∈ cluster (labels ω) (component j)) :
      b + H *ᵥ g l = T *ᵥ (R.clean l - a) := by
    have hj : (ω l).1 = component j := (mem_filter.mp hl).2
    have hg : g l = B⁻¹ *ᵥ (R.clean l - M.μ (component j)) := by
      ext i
      simp only [g, standardizedRounded, stdPt_apply, hj, hclean]
      rfl
    have hrec : B *ᵥ g l = R.clean l - M.μ (component j) := by
      rw [hg, mulVec_mulVec, mul_nonsing_inv _ hBunit, one_mulVec]
    change T *ᵥ (M.μ (component j) - a) + (T * B) *ᵥ g l = _
    rw [← mulVec_mulVec, hrec, ← mulVec_add]
    congr 1
    abel
  have he : empMom (cluster (labels ω) (component j)) (fun l ↦ b + H *ᵥ g l) q =
      C ((cluster (labels ω) (component j)).card : ℝ)⁻¹ *
        ∑ l ∈ cluster (labels ω) (component j), lin (T *ᵥ (R.clean l - a)) ^ q := by
    rw [empMom, smul_eq_C_mul]
    congr 1
    exact sum_congr rfl fun l hl ↦ by rw [hpoint l hl]
  have hh := affine_moments (cluster (labels ω) (component j)) g s θ hθ
    (hm j) H b q hq
  rw [he, hH] at hh
  simpa only [Robust.Reference.Resilient, hcluster, hmean, hcov, b] using hh

end Resilience

end

end ABBKS26.RefineAux
