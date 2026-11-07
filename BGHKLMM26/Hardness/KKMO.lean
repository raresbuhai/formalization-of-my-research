module

public import BGHKLMM26.Hardness.KKMOFourier
import Mathlib.Data.List.GetD

/-!
# The dense graph of the KKMO reduction: completeness and soundness

[BGHKLMM26, Lemmas 5.1 and 5.2] (from Khot, Kindler, Mossel and O'Donnell), for the reduction of
Figure 5.1 without the noise `μ`: the soundness uses Majority is Stablest with low-degree
influences (`BGHKLMM26.Hard.cut_le_of_lowInfluence`), so the decoding of labels needs no noise.

* `BGHKLMM26.Hard.kkmoCut_eq`: the cut value is the average over left vertices `u` of
  `Cut_ρ(g_u)`, for the averaged long code `g_u(x) = E_{v ∼ u} f_v(π_{uv} x)` (bilinearity of
  `Cut`, left-regularity).
* `BGHKLMM26.Hard.kkmo_complete`: from a labeling satisfying `1 - ε` of the constraints, the
  dictators cut `(1 - ρ)/2 - 2ε` (a pair of constraints at `u` that are both satisfied is cut with
  probability `(1 - ρ)/2`, and both are satisfied with probability at least `1 - 2ε`).
* `BGHKLMM26.Hard.kkmo_few_bad`: the decoding [BGHKLMM26, Lemma 5.4], with low-degree influences.
  If `i` has degree-`K` influence at least `τ` in `2 g_u - 1`, then (convexity of the influences,
  and `π` moving the influences) at least a `τ/2` fraction of the constraints `(u, v, π)` at `u`
  have `π⁻¹(i)` of influence at least `τ/2` in `2 f_v - 1`, a set of at most `2K/τ` candidates;
  labeling the bad `u` by `i` and each `v` by its most popular candidate satisfies a
  `τ²/(4(K+1))` fraction of the constraints at the bad vertices.
* `BGHKLMM26.Hard.kkmo_sound`: if the value is at most `ε`, every cut is at most
  `arccos ρ / π + ξ` (for `ε` small depending on `ρ, ξ`, but not on `R`): by `kkmo_few_bad`, all
  but a `ξ/2` fraction of the `g_u` have small low-degree influences.
* `BGHKLMM26.Hard.kkmoCut_lipschitz`: the cut value is Lipschitz in `ρ`, uniformly in the
  instance and the cut (with constant `2/(1 - r)` on `[-r, r]`).

The auxiliary lemmas are in the namespace `BGHKLMM26.Hard.KKMOAux` (the Fourier facts in
`BGHKLMM26/Hardness/KKMOFourier.lean`).
-/
@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

/-- The instances of the gap problem with `R` labels: valid, simple, bi-regular. -/
def Good (R : ℕ) (G : UGInstance) : Prop :=
  UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧ BiRegular G

/-- The averaged long code `g_u(x) = E_{(u,v) ∈ cs} f_v(π_{uv} x)` of the left vertex `u`. -/
noncomputable def avgTable {R : ℕ} (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool) (u : ℕ)
    (x : Cube (Fin R)) : ℝ :=
  ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum / (nbrs cs u).length

namespace KKMOAux

/-! ### Sums over lists -/

/-- A sum over a list, grouped by a key below `m`. -/
theorem list_sum_group {α : Type*} (l : List α) (key : α → ℕ) {m : ℕ} (hl : ∀ a ∈ l, key a < m)
    (φ : α → ℝ) :
    (l.map φ).sum = ∑ u ∈ range m, ((l.filter fun a ↦ key a = u).map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)]
    have e : ∀ u, (((a :: l).filter fun b ↦ key b = u).map φ).sum =
        (if key a = u then φ a else 0) + ((l.filter fun b ↦ key b = u).map φ).sum := by
      intro u
      by_cases h : key a = u <;> simp [h]
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range]
    simp only [hl a List.mem_cons_self, ↓reduceIte]

theorem list_sum_const_one {α : Type*} (l : List α) : (l.map fun _ ↦ (1 : ℝ)).sum = l.length := by
  simp

theorem list_sum_div {α : Type*} (l : List α) (φ : α → ℝ) (a : ℝ) :
    (l.map fun x ↦ φ x / a).sum = (l.map φ).sum / a := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, ih, add_div]

/-- The constraints of a valid instance are grouped by their left vertex. -/
theorem sum_nbrs {G : UGInstance} (hv : UGValid G) (φ : UGConstraint → ℝ) :
    (G.2.2.2.map φ).sum = ∑ u ∈ range G.1, ((nbrs G.2.2.2 u).map φ).sum :=
  list_sum_group _ (fun c ↦ c.1.1) (fun c hc ↦ (hv c hc).1) φ

/-- The left degree of a good instance with constraints. -/
theorem exists_leftDeg {R : ℕ} {G : UGInstance} (hG : Good R G) (hcs : G.2.2.2 ≠ []) :
    ∃ D : ℕ, 0 < D ∧ 0 < G.1 ∧ (∀ u < G.1, (nbrs G.2.2.2 u).length = D) ∧
      G.2.2.2.length = G.1 * D := by
  obtain ⟨D, hD⟩ := hG.2.2.2.1
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hcs
  have hu := (hG.1 c hc).1
  have hlen : ∀ u < G.1, (nbrs G.2.2.2 u).length = D := hD
  refine ⟨D, ?_, by omega, hlen, ?_⟩
  · rw [← hlen _ hu]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hc, by simp⟩)
  · have := sum_nbrs hG.1 (fun _ ↦ (1 : ℝ))
    simp only [list_sum_const_one] at this
    rw [Finset.sum_congr rfl fun u hu ↦ by rw [hlen u (Finset.mem_range.mp hu)]] at this
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact_mod_cast this

/-! ### The cut value of an average -/

theorem bitVal_bne' (a b : Bool) :
    bitVal (a != b) = bitVal a + bitVal b - 2 * bitVal a * bitVal b := by
  cases a <;> cases b <;> norm_num [bitVal]

/-- `Cut_ρ` of an average of `0/1` tables is the average of the pairwise cuts. -/
theorem cutValue_listAvg {α : Type*} (ρ : ℝ) {R : ℕ} {l : List α} (hl : l ≠ [])
    (F : α → Cube (Fin R) → Bool) :
    cutValue ρ (fun x ↦ (l.map fun a ↦ bitVal (F a x)).sum / l.length) =
      (l.map fun a ↦ (l.map fun b ↦
        corrAverage ρ R fun x y ↦ bitVal (F a x != F b y)).sum).sum / (l.length : ℝ) ^ 2 := by
  have hN : (l.length : ℝ) ≠ 0 := by
    have := List.length_pos_iff.mpr hl
    positivity
  simp only [← Fin.sum_univ_fun_getElem l]
  unfold cutValue
  have e : (fun x y : Cube (Fin R) ↦
      (∑ k : Fin l.length, bitVal (F l[k.1] x)) / l.length +
        (∑ k : Fin l.length, bitVal (F l[k.1] y)) / l.length -
        2 * ((∑ k : Fin l.length, bitVal (F l[k.1] x)) / l.length) *
          ((∑ k : Fin l.length, bitVal (F l[k.1] y)) / l.length)) =
      fun x y ↦ ∑ k₁ : Fin l.length, ∑ k₂ : Fin l.length,
        (1 / (l.length : ℝ) ^ 2) * bitVal (F l[k₁.1] x != F l[k₂.1] y) := by
    funext x y
    simp only [bitVal_bne', ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
    field_simp
  rw [e]
  simp only [OAI.OptimalMaxCut.MISProof.corrAverage_sum, corrAverage_const_mul, ← Finset.mul_sum]
  field_simp

end KKMOAux

open KKMOAux

/-- **The cut value through the averaged long codes**: `E_u Cut_ρ(g_u)`. -/
theorem kkmoCut_eq (ρ : ℝ) {R : ℕ} {G : UGInstance} (hG : Good R G) (hcs : G.2.2.2 ≠ [])
    (f : ℕ → Cube (Fin R) → Bool) :
    kkmoCut ρ R G.2.2.2 f = (∑ u ∈ range G.1, cutValue ρ (avgTable G.2.2.2 f u)) / G.1 := by
  obtain ⟨D, hD, hm, hlen, hcard⟩ := exists_leftDeg hG hcs
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have hm' : (G.1 : ℝ) ≠ 0 := by positivity
  unfold kkmoCut
  rw [sum_nbrs hG.1, hcard]
  have key : ∀ u ∈ range G.1, ((nbrs G.2.2.2 u).map fun c₁ ↦ ((nbrs G.2.2.2 c₁.1.1).map
      fun c₂ ↦ corrAverage ρ R fun x y ↦
        bitVal (f c₁.1.2 (permCube c₁.2 x) != f c₂.1.2 (permCube c₂.2 y))).sum /
      (nbrs G.2.2.2 c₁.1.1).length).sum = D * cutValue ρ (avgTable G.2.2.2 f u) := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have hne : nbrs G.2.2.2 u ≠ [] := by
      rw [← List.length_pos_iff, hlen u hu']; exact hD
    rw [List.map_congr_left (fun c₁ hc₁ ↦ by
      rw [show c₁.1.1 = u from of_decide_eq_true (List.mem_filter.mp hc₁).2])]
    rw [list_sum_div]
    unfold avgTable
    rw [cutValue_listAvg ρ hne (fun c x ↦ f c.1.2 (permCube c.2 x)), hlen u hu']
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  push_cast
  field_simp


namespace KKMOAux

/-! ### Bounds on the cut values -/

theorem bitVal_nonneg (b : Bool) : 0 ≤ bitVal b := by cases b <;> norm_num [bitVal]

theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by cases b <;> norm_num [bitVal]

theorem corrAverage_zero (ρ : ℝ) (n : ℕ) :
    corrAverage ρ n (fun (_ : BitCube n) (_ : BitCube n) ↦ (0 : ℝ)) = 0 := by
  have := corrAverage_fst ρ n (fun _ ↦ (0 : ℝ))
  rw [Finset.expect_const_zero] at this
  exact this

theorem corrAverage_nonneg {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) {n : ℕ}
    {F : BitCube n → BitCube n → ℝ} (hF : ∀ x y, 0 ≤ F x y) : 0 ≤ corrAverage ρ n F := by
  have := corrAverage_mono ⟨hρ0, hρ1⟩ n (F := fun _ _ ↦ (0 : ℝ)) hF
  rwa [corrAverage_zero] at this

theorem kkmoCut_nil (ρ : ℝ) (R : ℕ) (f : ℕ → Cube (Fin R) → Bool) : kkmoCut ρ R [] f = 0 := by
  simp [kkmoCut]

theorem kkmoCut_nonneg {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) (R : ℕ) (cs : List UGConstraint)
    (f : ℕ → Cube (Fin R) → Bool) : 0 ≤ kkmoCut ρ R cs f := by
  unfold kkmoCut
  refine div_nonneg (List.sum_nonneg fun a ha ↦ ?_) (Nat.cast_nonneg _)
  obtain ⟨c₁, _, rfl⟩ := List.mem_map.mp ha
  refine div_nonneg (List.sum_nonneg fun b hb ↦ ?_) (Nat.cast_nonneg _)
  obtain ⟨c₂, _, rfl⟩ := List.mem_map.mp hb
  exact corrAverage_nonneg hρ0 hρ1 fun x y ↦ bitVal_nonneg _

theorem avgTable_mem {R : ℕ} (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool) (u : ℕ)
    (x : Cube (Fin R)) : 0 ≤ avgTable cs f u x ∧ avgTable cs f u x ≤ 1 := by
  unfold avgTable
  have h0 : 0 ≤ ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum :=
    List.sum_nonneg fun a ha ↦ by
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
      exact bitVal_nonneg _
  have h1 : ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum ≤
      (nbrs cs u).length := by
    rw [← list_sum_const_one]
    exact List.sum_le_sum fun c _ ↦ bitVal_le_one _
  refine ⟨div_nonneg h0 (Nat.cast_nonneg _), div_le_one_of_le₀ h1 (Nat.cast_nonneg _)⟩

theorem cutValue_le_one {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) {R : ℕ} {g : Cube (Fin R) → ℝ}
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) : cutValue ρ g ≤ 1 := by
  unfold cutValue
  have := corrAverage_mono ⟨hρ0, hρ1⟩ R (F := fun x y ↦ g x + g y - 2 * g x * g y)
    (G := fun _ _ ↦ (1 : ℝ)) fun x y ↦ by
      have hx := hg x; have hy := hg y
      nlinarith [mul_nonneg hx.1 hy.1, mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)]
  rwa [corrAverage_one] at this

/-! ### Labelings and indicators -/

/-- A labeling of `0, …, k - 1` read as a function on `ℕ` (`0` outside), as in `ugValue`. -/
def lab {k R : ℕ} (σ : Fin k → Fin R) (u : ℕ) : ℕ := if h : u < k then σ ⟨u, h⟩ else 0

theorem lab_of_lt {k R : ℕ} (σ : Fin k → Fin R) {u : ℕ} (h : u < k) : lab σ u = σ ⟨u, h⟩ := by
  simp [lab, h]

/-- The `0/1` indicator of a proposition. -/
noncomputable def ind (p : Prop) : ℝ := by classical exact if p then 1 else 0

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]

theorem ind_of_not {p : Prop} (h : ¬p) : ind p = 0 := by simp [ind, h]

@[simp] theorem ind_true : ind True = 1 := ind_of trivial

@[simp] theorem ind_false : ind False = 0 := ind_of_not not_false

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  by_cases h : p
  · rw [ind_of h]; norm_num
  · rw [ind_of_not h]

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · rw [ind_of h]
  · rw [ind_of_not h]; norm_num

theorem ind_le_ind {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_of hp, ind_of (h hp)]
  · rw [ind_of_not hp]; exact ind_nonneg q

theorem length_filter_eq {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    ((l.filter fun a ↦ p a).length : ℝ) = (l.map fun a ↦ ind (p a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih, add_comm]
    · simp [h, ih]

theorem le_ugValue (G : UGInstance) (σ : Fin G.1 → Fin G.2.2.1) (τ : Fin G.2.1 → Fin G.2.2.1) :
    (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length ≤ ugValue G := by
  unfold ugValue
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove σ)
  exact le_ciSup (f := fun τ : Fin G.2.1 → Fin G.2.2.1 ↦
    (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length) (Set.finite_range _).bddAbove τ

/-! ### Completeness -/

theorem ugValue_eq (G : UGInstance) : ugValue G =
    ⨆ (σ : Fin G.1 → Fin G.2.2.1) (τ : Fin G.2.1 → Fin G.2.2.1),
      (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length := rfl

theorem ugValue_le_one (G : UGInstance) : ugValue G ≤ 1 := by
  rw [ugValue_eq]
  refine Real.iSup_le (fun σ ↦ Real.iSup_le (fun τ ↦ ?_) zero_le_one) zero_le_one
  exact div_le_one_of_le₀ (by exact_mod_cast List.length_filter_le _ _) (Nat.cast_nonneg _)

/-- A labeling attaining the value, if the value is positive. -/
theorem exists_opt_labeling (G : UGInstance) (h : 0 < ugValue G) :
    ∃ (σ : Fin G.1 → Fin G.2.2.1) (τ : Fin G.2.1 → Fin G.2.2.1),
      ugValue G = (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length := by
  rw [ugValue_eq] at h ⊢
  have hne1 : Nonempty (Fin G.1 → Fin G.2.2.1) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    rw [Real.iSup_of_isEmpty] at h
    exact lt_irrefl _ h
  have hne2 : Nonempty (Fin G.2.1 → Fin G.2.2.1) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp only [Real.iSup_of_isEmpty, Real.iSup_const_zero] at h
    exact lt_irrefl _ h
  obtain ⟨σ, hσ⟩ := exists_eq_ciSup_of_finite (f := fun σ : Fin G.1 → Fin G.2.2.1 ↦
    ⨆ τ : Fin G.2.1 → Fin G.2.2.1, (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length)
  obtain ⟨τ, hτ⟩ := exists_eq_ciSup_of_finite (f := fun τ : Fin G.2.1 → Fin G.2.2.1 ↦
    (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length)
  exact ⟨σ, τ, by rw [← hσ, ← hτ]⟩

/-- If every pair `c₁, c₂` of `l` has weight at least `a (s c₁ + s c₂ - 1)`, the average weight of
the pairs is at least `a (2 E s - 1)`. -/
theorem pair_avg_ge {α : Type*} {l : List α} (hl : l ≠ []) (s : α → ℝ) (X : α → α → ℝ) {a : ℝ}
    (h : ∀ c₁ ∈ l, ∀ c₂ ∈ l, a * (s c₁ + s c₂ - 1) ≤ X c₁ c₂) :
    a * (2 * (l.map s).sum / l.length - 1) ≤
      (l.map fun c₁ ↦ (l.map fun c₂ ↦ X c₁ c₂).sum).sum / (l.length : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.mpr hl
  simp only [← Fin.sum_univ_fun_getElem l]
  rw [le_div_iff₀ (by positivity)]
  calc a * (2 * (∑ k : Fin l.length, s l[k.1]) / l.length - 1) * (l.length : ℝ) ^ 2
      = ∑ k₁ : Fin l.length, ∑ k₂ : Fin l.length, a * (s l[k₁.1] + s l[k₂.1] - 1) := by
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring
    _ ≤ ∑ k₁ : Fin l.length, ∑ k₂ : Fin l.length, X l[k₁.1] l[k₂.1] :=
        Finset.sum_le_sum fun k₁ _ ↦ Finset.sum_le_sum fun k₂ _ ↦
          h _ (List.getElem_mem _) _ (List.getElem_mem _)

end KKMOAux

/-- **Completeness** [BGHKLMM26, Lemma 5.1] with `μ = 0`. -/
theorem kkmo_complete {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) {R : ℕ} {G : UGInstance}
    (hG : Good R G) {ε : ℝ} (hval : 1 - ε ≤ ugValue G) :
    ∃ f : ℕ → Cube (Fin R) → Bool, (1 - ρ) / 2 - 2 * ε ≤ kkmoCut ρ R G.2.2.2 f := by
  by_cases hε : 1 / 2 ≤ ε
  · exact ⟨fun _ _ ↦ false, by linarith [kkmoCut_nonneg hρ0 hρ1 R G.2.2.2 (fun _ _ ↦ false)]⟩
  rw [not_le] at hε
  have hε0 : 0 ≤ ε := by linarith [ugValue_le_one G]
  have hpos : 0 < ugValue G := by linarith
  obtain ⟨m, n, R', cs⟩ := G
  obtain ⟨hv, hR, -, -⟩ := id hG
  dsimp only at hR
  subst hR
  obtain ⟨σ, τ, hστ⟩ := exists_opt_labeling _ hpos
  dsimp only at σ τ hστ ⊢
  have hcs : cs ≠ [] := by
    intro h; rw [hστ, h] at hpos; simp at hpos
  obtain ⟨D, hD, hm, hlen, hcard⟩ := exists_leftDeg hG hcs
  have hR0 : 0 < R' := lt_of_le_of_lt (Nat.zero_le _) (σ ⟨0, hm⟩).2
  -- the dictators of the labels of the right vertices
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Cube (Fin R') → Bool,
      f = fun v x ↦ if h : lab τ v < R' then x ⟨lab τ v, h⟩ else false := ⟨_, rfl⟩
  obtain ⟨sL, hsL⟩ : ∃ sL : ℕ → Fin R',
      sL = fun u ↦ if h : u < m then σ ⟨u, h⟩ else ⟨0, hR0⟩ := ⟨_, rfl⟩
  have hdict : ∀ c ∈ cs, lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0 →
      ∀ x, f c.1.2 (permCube c.2 x) = x (sL c.1.1) := by
    intro c hc hsat x
    have hc' := hv c hc
    have hτv : lab τ c.1.2 < R' := by rw [lab_of_lt τ hc'.2.1]; exact (τ _).2
    have hσu : lab σ c.1.1 < R' := by rw [lab_of_lt σ hc'.1]; exact (σ _).2
    have hgd : c.2.getD (lab τ c.1.2) 0 < R' := hsat ▸ hσu
    rw [hf, hsL]
    simp only [hτv, permCube, hgd, hc'.1, ↓reduceDIte]
    congr 1
    ext
    simp only
    rw [← hsat, lab_of_lt σ hc'.1]
  refine ⟨f, ?_⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [kkmoCut_eq ρ hG hcs f]
  dsimp only
  -- the bound at each left vertex
  have hu : ∀ u ∈ range m, (1 - ρ) / D * ((nbrs cs u).map fun c ↦
      ind (lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0)).sum - (1 - ρ) / 2 ≤
      cutValue ρ (avgTable cs f u) := by
    intro u hu
    have hum := Finset.mem_range.mp hu
    have hne : nbrs cs u ≠ [] := by rw [← List.length_pos_iff, hlen u hum]; exact hD
    unfold avgTable
    rw [cutValue_listAvg ρ hne (fun c x ↦ f c.1.2 (permCube c.2 x))]
    have key := pair_avg_ge hne (fun c ↦ ind (lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0))
      (fun c₁ c₂ ↦ corrAverage ρ R' fun x y ↦
        bitVal (f c₁.1.2 (permCube c₁.2 x) != f c₂.1.2 (permCube c₂.2 y)))
      (a := (1 - ρ) / 2) (fun c₁ hc₁ c₂ hc₂ ↦ by
        have hc₁' := List.mem_filter.mp hc₁
        have hc₂' := List.mem_filter.mp hc₂
        have hu₁ : c₁.1.1 = u := of_decide_eq_true hc₁'.2
        have hu₂ : c₂.1.1 = u := of_decide_eq_true hc₂'.2
        have hX : 0 ≤ corrAverage ρ R' fun x y ↦
            bitVal (f c₁.1.2 (permCube c₁.2 x) != f c₂.1.2 (permCube c₂.2 y)) :=
          corrAverage_nonneg hρ0 hρ1 fun x y ↦ bitVal_nonneg _
        have hρ' : 0 ≤ (1 - ρ) / 2 := by linarith
        by_cases h1 : lab σ c₁.1.1 = c₁.2.getD (lab τ c₁.1.2) 0
        · by_cases h2 : lab σ c₂.1.1 = c₂.2.getD (lab τ c₂.1.2) 0
          · have e : (fun x y : Cube (Fin R') ↦
                bitVal (f c₁.1.2 (permCube c₁.2 x) != f c₂.1.2 (permCube c₂.2 y))) =
                fun x y ↦ bitVal (x (sL u) != y (sL u)) := by
              funext x y
              rw [hdict c₁ hc₁'.1 h1 x, hdict c₂ hc₂'.1 h2 y, hu₁, hu₂]
            rw [ind_of h1, ind_of h2, e, corrAverage_dictator]
            ring_nf
            rfl
          · rw [ind_of h1, ind_of_not h2]
            nlinarith
        · rw [ind_of_not h1]
          have := ind_le_one (lab σ c₂.1.1 = c₂.2.getD (lab τ c₂.1.2) 0)
          nlinarith)
    rw [hlen u hum] at key ⊢
    calc (1 - ρ) / D * ((nbrs cs u).map fun c ↦
          ind (lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0)).sum - (1 - ρ) / 2
        = (1 - ρ) / 2 * (2 * ((nbrs cs u).map fun c ↦
          ind (lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0)).sum / D - 1) := by
          field_simp
      _ ≤ _ := key
  -- summing over the left vertices
  have hS : ∑ u ∈ range m, ((nbrs cs u).map fun c ↦
      ind (lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0)).sum =
      (ugSatisfied (m, n, R', cs) (lab σ) (lab τ) : ℝ) := by
    rw [← sum_nbrs hv]
    unfold ugSatisfied
    rw [length_filter_eq]
  have hsum := Finset.sum_le_sum hu
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  rw [hστ, hcard] at hval
  push_cast at hval
  rw [le_div_iff₀ (by positivity)] at hval
  rw [le_div_iff₀ hm']
  have h1 : (1 - ρ) * ((1 - ε) * (m * D)) ≤
      (1 - ρ) * (ugSatisfied (m, n, R', cs) (lab σ) (lab τ) : ℝ) :=
    mul_le_mul_of_nonneg_left hval (by linarith)
  have h2 : (1 + ρ) * ε * m ≥ 0 := by
    have : 0 ≤ 1 + ρ := by linarith
    positivity
  have h3 : (1 - ρ) / D * (ugSatisfied (m, n, R', cs) (lab σ) (lab τ) : ℝ) ≥
      (1 - ρ) * ((1 - ε) * m) := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hD']
    linarith
  nlinarith


namespace KKMOAux

/-! ### Permutation tables -/

/-- The degree-`K` influence of the coordinate `j`, and `0` if `j ≥ R`. -/
noncomputable def inflAt {R : ℕ} (K j : ℕ) (h : Cube (Fin R) → ℝ) : ℝ :=
  if hj : j < R then cutoffInfluence K ⟨j, hj⟩ h else 0

/-- The `±1` table `2 f_v - 1`. -/
noncomputable def pmTable {R : ℕ} (f : ℕ → Cube (Fin R) → Bool) (v : ℕ) (y : Cube (Fin R)) : ℝ :=
  2 * bitVal (f v y) - 1

theorem pmTable_mem {R : ℕ} (f : ℕ → Cube (Fin R) → Bool) (v : ℕ) (y : Cube (Fin R)) :
    -1 ≤ pmTable f v y ∧ pmTable f v y ≤ 1 := by
  unfold pmTable bitVal; split_ifs <;> norm_num

theorem inflAt_le_one {R : ℕ} (K j : ℕ) (f : ℕ → Cube (Fin R) → Bool) (v : ℕ) :
    inflAt K j (pmTable f v) ≤ 1 := by
  unfold inflAt
  split_ifs
  · exact cutoffInfluence_le_one K _ (pmTable_mem f v)
  · norm_num

/-- A valid table `π` is a permutation: every label is listed, and reading a table through `π`
moves the influence of `i` to the position of `i` in `π`. -/
theorem perm_table {R : ℕ} {π : List ℕ} (hlen : π.length = R) (hnd : π.Nodup)
    (hlt : ∀ a ∈ π, a < R) (i : Fin R) :
    π.idxOf i.1 < R ∧ π.getD (π.idxOf i.1) 0 = i.1 ∧
      ∀ (K : ℕ) (h : Cube (Fin R) → ℝ),
        cutoffInfluence K i (fun x ↦ h (permCube π x)) = inflAt K (π.idxOf i.1) h := by
  have hmem : i.1 ∈ π := by
    have hsub : π.toFinset ⊆ range R := fun a ha ↦
      Finset.mem_range.mpr (hlt a (List.mem_toFinset.mp ha))
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_range])
    have : i.1 ∈ range R := Finset.mem_range.mpr i.2
    rw [← heq] at this
    exact List.mem_toFinset.mp this
  have hidx : π.idxOf i.1 < π.length := List.idxOf_lt_length_iff.mpr hmem
  have hget : π[π.idxOf i.1] = i.1 := List.getElem_idxOf hidx
  refine ⟨hlen ▸ hidx, by rw [List.getD_eq_getElem _ _ hidx, hget], fun K h ↦ ?_⟩
  let e₀ : Fin R → Fin R := fun j ↦ ⟨π[j.1]'(hlen ▸ j.2), hlt _ (List.getElem_mem _)⟩
  have hinj : Function.Injective e₀ := fun j k hjk ↦ by
    have : π[j.1]'(hlen ▸ j.2) = π[k.1]'(hlen ▸ k.2) := congrArg Fin.val hjk
    exact Fin.ext ((hnd.getElem_inj_iff).mp this)
  let e : Fin R ≃ Fin R := Equiv.ofBijective e₀ (Finite.injective_iff_bijective.mp hinj)
  have hperm : ∀ x : Cube (Fin R), permCube π x = fun j ↦ x (e j) := by
    intro x
    funext j
    have hj : j.1 < π.length := hlen ▸ j.2
    simp only [permCube, List.getD_eq_getElem _ _ hj, e, Equiv.ofBijective_apply, e₀,
      hlt _ (List.getElem_mem hj), ↓reduceDIte]
  have hsymm : e.symm i = ⟨π.idxOf i.1, hlen ▸ hidx⟩ := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simp [e, e₀, hget])
  simp only [hperm]
  rw [cutoffInfluence_comp_perm, hsymm]
  simp [inflAt, hlen ▸ hidx]

/-! ### Many constraints at a bad vertex decode -/

theorem two_avgTable_sub_one {R : ℕ} (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool)
    {u : ℕ} (hne : nbrs cs u ≠ []) (x : Cube (Fin R)) :
    2 * avgTable cs f u x - 1 =
      ((nbrs cs u).map fun c ↦ pmTable f c.1.2 (permCube c.2 x)).sum / (nbrs cs u).length := by
  have hN : ((nbrs cs u).length : ℝ) ≠ 0 := by
    have := List.length_pos_iff.mpr hne
    positivity
  unfold avgTable pmTable
  simp only [← Fin.sum_univ_fun_getElem (nbrs cs u)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem cutoffInfluence_const {R : ℕ} (K : ℕ) (i : Fin R) (a : ℝ) :
    cutoffInfluence K i (fun _ : Cube (Fin R) ↦ a) = 0 := by
  unfold cutoffInfluence
  refine Finset.sum_eq_zero fun s hs ↦ ?_
  have hs0 : s ≠ fun _ ↦ false := by
    intro h
    have := (Finset.mem_filter.mp hs).2.1
    rw [h] at this
    exact Bool.false_ne_true this
  have hw : ∀ x : Cube (Fin R), walsh (fun _ ↦ false) x = 1 := by
    intro x; simp [walsh, bitSign]
  have := walsh_orthogonality s (fun _ ↦ false)
  simp only [hw, mul_one, hs0, ↓reduceIte] at this
  unfold coefficient
  rw [← Finset.mul_expect, this, mul_zero]
  ring

theorem list_sum_add_const {α : Type*} (l : List α) (φ : α → ℝ) (b : ℝ) :
    (l.map fun a ↦ φ a + b).sum = (l.map φ).sum + l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- The constraint `c = ((u, v), π)` **decodes** under the left labeling `σ'`: the coordinate
`π⁻¹(σ'(u))` has degree-`K` influence at least `τ/2` in `2 f_v - 1`. -/
def Decodes {R : ℕ} (K : ℕ) (τ : ℝ) (f : ℕ → Cube (Fin R) → Bool) (σ' : ℕ → ℕ)
    (c : UGConstraint) : Prop :=
  τ / 2 ≤ inflAt K (c.2.idxOf (σ' c.1.1)) (pmTable f c.1.2)

/-- At a vertex `u` where the label `σ'(u)` has degree-`K` influence at least `τ` in `2 g_u - 1`,
at least a `τ/2` fraction of the constraints at `u` decode. -/
theorem many_decode {R K : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) {G : UGInstance} (hv : UGValid G)
    (hR : G.2.2.1 = R) (f : ℕ → Cube (Fin R) → Bool) (σ' : ℕ → ℕ) (u : ℕ) (i : Fin R)
    (hσ : σ' u = i.1)
    (hi : τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)) :
    τ / 2 * (nbrs G.2.2.2 u).length ≤
      ((nbrs G.2.2.2 u).map fun c ↦ ind (Decodes K τ f σ' c)).sum := by
  by_cases hne : nbrs G.2.2.2 u = []
  · rw [hne]; simp
  have hN : (0 : ℝ) < (nbrs G.2.2.2 u).length := by
    exact_mod_cast List.length_pos_iff.mpr hne
  have e1 : (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1) = fun x ↦
      ((nbrs G.2.2.2 u).map fun c ↦ pmTable f c.1.2 (permCube c.2 x)).sum /
        (nbrs G.2.2.2 u).length :=
    funext (two_avgTable_sub_one _ f hne)
  rw [e1] at hi
  have hJ := cutoffInfluence_listAvg_le K i hne (fun c x ↦ pmTable f c.1.2 (permCube c.2 x))
  have e2 : ((nbrs G.2.2.2 u).map fun c ↦
      cutoffInfluence K i (fun x ↦ pmTable f c.1.2 (permCube c.2 x))) =
      (nbrs G.2.2.2 u).map fun c ↦ inflAt K (c.2.idxOf (σ' c.1.1)) (pmTable f c.1.2) := by
    refine List.map_congr_left fun c hc ↦ ?_
    have hcu : c.1.1 = u := of_decide_eq_true (List.mem_filter.mp hc).2
    have hc' := hv c (List.mem_filter.mp hc).1
    rw [hcu, hσ]
    exact (perm_table (hR ▸ hc'.2.2.1) hc'.2.2.2.1 (hR ▸ hc'.2.2.2.2) i).2.2 K _
  rw [e2] at hJ
  have hle : ((nbrs G.2.2.2 u).map fun c ↦ inflAt K (c.2.idxOf (σ' c.1.1)) (pmTable f c.1.2)).sum
      ≤ ((nbrs G.2.2.2 u).map fun c ↦ ind (Decodes K τ f σ' c) + τ / 2).sum := by
    refine List.sum_le_sum fun c _ ↦ ?_
    by_cases h : Decodes K τ f σ' c
    · rw [ind_of h]
      have := inflAt_le_one K (c.2.idxOf (σ' c.1.1)) f c.1.2
      linarith
    · rw [ind_of_not h]
      unfold Decodes at h
      linarith [not_le.mp h]
  rw [list_sum_add_const] at hle
  have h3 := (le_div_iff₀ hN).mp (hi.trans hJ)
  nlinarith

/-- **Pigeonhole**: if the good elements of `l` have their label `j` in `L`, some label in `L` (or
`t₀`, if `L` is empty) is the label of at least a `1/|L|` fraction of the good elements. -/
theorem exists_label {α : Type*} (l : List α) (good : α → Prop) (j : α → ℕ) (L : Finset ℕ)
    (hL : ∀ a ∈ l, good a → j a ∈ L) (t₀ : ℕ) :
    ∃ t, (t ∈ L ∨ t = t₀) ∧
      (l.map fun a ↦ ind (good a)).sum ≤ L.card * (l.map fun a ↦ ind (good a ∧ j a = t)).sum := by
  classical
  by_cases hne : L.Nonempty
  · have hsum : ∑ t ∈ L, (l.map fun a ↦ ind (good a ∧ j a = t)).sum =
        (l.map fun a ↦ ind (good a)).sum := by
      simp only [← Fin.sum_univ_fun_getElem l]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      by_cases hg : good l[k.1]
      · have hj := hL _ (List.getElem_mem _) hg
        rw [ind_of hg, Finset.sum_eq_single_of_mem (j l[k.1]) hj]
        · exact ind_of ⟨hg, rfl⟩
        · intro t _ ht
          exact ind_of_not fun h ↦ ht h.2.symm
      · rw [ind_of_not hg]
        exact Finset.sum_eq_zero fun t _ ↦ ind_of_not fun h ↦ hg h.1
    have hc : (0 : ℝ) < L.card := by exact_mod_cast hne.card_pos
    obtain ⟨t, ht, hle⟩ := Finset.exists_le_of_sum_le hne
      (f := fun _ ↦ (l.map fun a ↦ ind (good a)).sum / L.card)
      (g := fun t ↦ (l.map fun a ↦ ind (good a ∧ j a = t)).sum) (by
        rw [hsum, Finset.sum_const, nsmul_eq_mul]
        field_simp
        rfl)
    refine ⟨t, Or.inl ht, ?_⟩
    rw [div_le_iff₀ hc] at hle
    linarith
  · refine ⟨t₀, Or.inr rfl, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have : (l.map fun a ↦ ind (good a)).sum ≤ (l.map fun _ ↦ (0 : ℝ)).sum :=
      List.sum_le_sum fun a ha ↦ by
        rw [ind_of_not fun hg ↦ Finset.notMem_empty _ (hL a ha hg)]
    simpa using this

/-- The candidate labels of `v`: the coordinates of degree-`K` influence at least `τ/2` in
`2 f_v - 1`. -/
noncomputable def cands {R : ℕ} (K : ℕ) (τ : ℝ) (f : ℕ → Cube (Fin R) → Bool) (v : ℕ) :
    Finset ℕ :=
  (univ.filter fun k : Fin R ↦ τ / 2 ≤ cutoffInfluence K k (pmTable f v)).map Fin.valEmbedding

theorem card_cands_le {R : ℕ} (K : ℕ) {τ : ℝ} (hτ : 0 < τ) (f : ℕ → Cube (Fin R) → Bool)
    (v : ℕ) : ((cands K τ f v).card : ℝ) ≤ 2 * (K + 1) / τ := by
  unfold cands
  rw [Finset.card_map, le_div_iff₀ hτ]
  have := card_influential_mul_le K (τ := τ / 2) (pmTable_mem f v)
  linarith

theorem mem_cands {R : ℕ} {K : ℕ} {τ : ℝ} (hτ : 0 < τ) {f : ℕ → Cube (Fin R) → Bool} {v j : ℕ}
    (h : τ / 2 ≤ inflAt K j (pmTable f v)) : j ∈ cands K τ f v := by
  unfold inflAt at h
  split_ifs at h with hj
  · exact Finset.mem_map.mpr ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  · linarith

theorem lt_of_mem_cands {R : ℕ} {K : ℕ} {τ : ℝ} {f : ℕ → Cube (Fin R) → Bool} {v j : ℕ}
    (h : j ∈ cands K τ f v) : j < R := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp h
  exact k.2

/-- **Decoding the right labels**: for any left labeling `σ`, some right labeling satisfies at
least a `τ / (2(K+1))` fraction of the decoding constraints. -/
theorem exists_right_labels {m n R : ℕ} (K : ℕ) {cs : List UGConstraint} (hR : 0 < R)
    (hv : UGValid (m, n, R, cs)) {τ : ℝ} (hτ : 0 < τ) (f : ℕ → Cube (Fin R) → Bool)
    (σ : Fin m → Fin R) :
    ∃ τf : Fin n → Fin R,
      τ / (2 * (K + 1)) * (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum ≤
        ugSatisfied (m, n, R, cs) (lab σ) (lab τf) := by
  have hex : ∀ v : Fin n, ∃ t : Fin R,
      ((cs.filter fun c ↦ c.1.2 = v.1).map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum ≤
        (cands K τ f v.1).card * ((cs.filter fun c ↦ c.1.2 = v.1).map fun c ↦
          ind (Decodes K τ f (lab σ) c ∧ c.2.idxOf (lab σ c.1.1) = t.1)).sum := by
    intro v
    obtain ⟨t, ht, hle⟩ := exists_label (cs.filter fun c ↦ c.1.2 = v.1)
      (Decodes K τ f (lab σ)) (fun c ↦ c.2.idxOf (lab σ c.1.1)) (cands K τ f v.1)
      (fun c hc hd ↦ by
        have hcv : c.1.2 = v.1 := of_decide_eq_true (List.mem_filter.mp hc).2
        unfold Decodes at hd
        rw [hcv] at hd
        exact mem_cands hτ hd) 0
    have htR : t < R := by
      rcases ht with ht | rfl
      · exact lt_of_mem_cands ht
      · exact hR
    exact ⟨⟨t, htR⟩, hle⟩
  choose τf hτf using hex
  refine ⟨τf, ?_⟩
  -- the satisfied constraints
  have hsat : (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
      c.2.idxOf (lab σ c.1.1) = lab τf c.1.2)).sum ≤
        ugSatisfied (m, n, R, cs) (lab σ) (lab τf) := by
    unfold ugSatisfied
    rw [length_filter_eq]
    refine List.sum_le_sum fun c hc ↦ ind_le_ind fun h ↦ ?_
    have hc' := hv c hc
    have hu : lab σ c.1.1 = σ ⟨c.1.1, hc'.1⟩ := lab_of_lt σ hc'.1
    have hp := (perm_table hc'.2.2.1 hc'.2.2.2.1 hc'.2.2.2.2 (σ ⟨c.1.1, hc'.1⟩)).2.1
    change lab σ c.1.1 = c.2.getD (lab τf c.1.2) 0
    rw [← h.2, hu, hp]
  -- grouped by right vertex
  have hgroup : ∀ φ : UGConstraint → ℝ, (cs.map φ).sum =
      ∑ v ∈ range n, ((cs.filter fun c ↦ c.1.2 = v).map φ).sum :=
    fun φ ↦ list_sum_group _ (fun c ↦ c.1.2) (fun c hc ↦ (hv c hc).2.1) φ
  have hτK : (0 : ℝ) < 2 * (K + 1) / τ := by positivity
  have hmain : (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum ≤ 2 * (K + 1) / τ *
      (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
        c.2.idxOf (lab σ c.1.1) = lab τf c.1.2)).sum := by
    rw [hgroup, hgroup, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv' ↦ ?_
    have hvn := Finset.mem_range.mp hv'
    have e : ((cs.filter fun c ↦ c.1.2 = v).map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
        c.2.idxOf (lab σ c.1.1) = lab τf c.1.2)) =
        (cs.filter fun c ↦ c.1.2 = v).map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
          c.2.idxOf (lab σ c.1.1) = (τf ⟨v, hvn⟩).1) := by
      refine List.map_congr_left fun c hc ↦ ?_
      have hcv : c.1.2 = v := of_decide_eq_true (List.mem_filter.mp hc).2
      rw [hcv, lab_of_lt τf hvn]
    rw [e]
    refine (hτf ⟨v, hvn⟩).trans (mul_le_mul_of_nonneg_right (card_cands_le K hτ f v) ?_)
    exact List.sum_nonneg fun x hx ↦ by
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact ind_nonneg _
  calc τ / (2 * (K + 1)) * (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum
      ≤ τ / (2 * (K + 1)) * (2 * (K + 1) / τ * (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
        c.2.idxOf (lab σ c.1.1) = lab τf c.1.2)).sum) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c ∧
        c.2.idxOf (lab σ c.1.1) = lab τf c.1.2)).sum := by
        field_simp
    _ ≤ _ := hsat

/-- The decoding constraints are many: a `τ/2` fraction of those at each bad left vertex. -/
theorem many_decode_total {m n R K : ℕ} {cs : List UGConstraint} (hv : UGValid (m, n, R, cs))
    {τ : ℝ} (hτ : 0 ≤ τ) (f : ℕ → Cube (Fin R) → Bool) (σ : Fin m → Fin R) {D : ℕ}
    (hlen : ∀ u < m, (nbrs cs u).length = D) (B : Finset ℕ) (hB : B ⊆ range m)
    (hσ : ∀ u : Fin m, u.1 ∈ B →
      τ ≤ cutoffInfluence K (σ u) (fun x ↦ 2 * avgTable cs f u.1 x - 1)) :
    B.card * (τ / 2 * D) ≤ (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum := by
  rw [sum_nbrs hv]
  calc (B.card : ℝ) * (τ / 2 * D) = ∑ u ∈ B, τ / 2 * D := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ B, ((nbrs cs u).map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum := by
        refine Finset.sum_le_sum fun u hu ↦ ?_
        have hum : u < m := Finset.mem_range.mp (hB hu)
        have := many_decode hτ (G := (m, n, R, cs)) hv rfl f (lab σ) u (σ ⟨u, hum⟩)
          (lab_of_lt σ hum) (hσ ⟨u, hum⟩ hu)
        rwa [hlen u hum] at this
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hB fun u _ _ ↦
        List.sum_nonneg fun x hx ↦ by
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
          exact ind_nonneg _

end KKMOAux

/-- **Few left vertices have an influential coordinate** [BGHKLMM26, Lemma 5.4], with low-degree
influences: on instances of small value, at most a `ν` fraction of the left vertices `u` have a
coordinate of degree-`K` influence at least `τ` in `2 g_u - 1`. (Decoding: such a coordinate is
influential in many of the tables `f_v`, through `π_{uv}`, and the influential coordinates give a
labeling satisfying many constraints.) -/
theorem kkmo_few_bad (K : ℕ) {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ (R : ℕ) (G : UGInstance), Good R G →
      ugValue G ≤ ε → ∀ f : ℕ → Cube (Fin R) → Bool,
        (((range G.1).filter fun u ↦
            ∃ i, τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)).card : ℝ) ≤
          ν * G.1 := by
  refine ⟨ν * τ ^ 2 / (4 * (K + 1)), by positivity, fun ε _ hε₁ R G hG hval f ↦ ?_⟩
  obtain ⟨m, n, R', cs⟩ := G
  obtain ⟨hv, hR, -, -⟩ := id hG
  dsimp only at hR
  subst hR
  dsimp only
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨B, hBdef⟩ : ∃ B : Finset ℕ, B = (range m).filter fun u ↦
      ∃ i, τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable cs f u x - 1) := ⟨_, rfl⟩
  rw [← hBdef] at hlt
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < B.card := lt_of_le_of_lt (by positivity) hlt
    exact_mod_cast this
  obtain ⟨u₀, hu₀⟩ := hBne
  rw [hBdef, Finset.mem_filter] at hu₀
  obtain ⟨-, i₀, hi₀⟩ := hu₀
  have hR0 : 0 < R' := lt_of_le_of_lt (Nat.zero_le _) i₀.2
  have hne : nbrs cs u₀ ≠ [] := by
    intro h
    have e : (fun x ↦ 2 * avgTable cs f u₀ x - 1) = fun _ ↦ (-1 : ℝ) := by
      funext x; simp [avgTable, h]
    rw [e, cutoffInfluence_const] at hi₀
    linarith
  have hcs : cs ≠ [] := fun h ↦ hne (by simp [nbrs, h])
  obtain ⟨D, hD, hm, hlen, hcard⟩ := exists_leftDeg hG hcs
  have hσ : ∀ u : Fin m, ∃ i : Fin R', u.1 ∈ B →
      τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable cs f u.1 x - 1) := by
    intro u
    by_cases hu : u.1 ∈ B
    · rw [hBdef, Finset.mem_filter] at hu
      obtain ⟨i, hi⟩ := hu.2
      exact ⟨i, fun _ ↦ hi⟩
    · exact ⟨⟨0, hR0⟩, fun h ↦ absurd h hu⟩
  choose σ hσ using hσ
  obtain ⟨τf, hτf⟩ := exists_right_labels K hR0 hv hτ f σ
  have hcount := many_decode_total hv hτ.le f σ hlen B (hBdef ▸ Finset.filter_subset _ _) hσ
  have hval' := (le_ugValue (m, n, R', cs) σ τf).trans hval
  dsimp only at hval' hcard
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ugSatisfied (m, n, R', cs) (lab σ) (lab τf) := ⟨_, rfl⟩
  rw [← hS] at hτf hval'
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcsR : (0 : ℝ) < cs.length := by rw [hcard]; push_cast; positivity
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : τ ^ 2 * D / (4 * (K + 1)) * B.card ≤ S := by
    calc τ ^ 2 * D / (4 * (K + 1)) * B.card = τ / (2 * (K + 1)) * (B.card * (τ / 2 * D)) := by
          field_simp; ring
      _ ≤ τ / (2 * (K + 1)) * (cs.map fun c ↦ ind (Decodes K τ f (lab σ) c)).sum :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ ≤ S := hτf
  have h2 : S ≤ τ ^ 2 * D / (4 * (K + 1)) * (ν * m) := by
    rw [div_le_iff₀ hcsR] at hval'
    rw [hcard] at hval'
    push_cast at hval'
    calc S ≤ ε * (m * D) := hval'
      _ ≤ ν * τ ^ 2 / (4 * (K + 1)) * (m * D) :=
          mul_le_mul_of_nonneg_right hε₁ (by positivity)
      _ = τ ^ 2 * D / (4 * (K + 1)) * (ν * m) := by ring
  have hpos : 0 < τ ^ 2 * D / (4 * (K + 1)) := by positivity
  exact absurd (le_of_mul_le_mul_left (h1.trans h2) hpos) (not_le.mpr hlt)


/-- **Soundness** [BGHKLMM26, Lemma 5.2]: for `ρ ∈ (-1, 0)` and `ξ > 0` there is `ε₁ > 0` such
that on instances of value at most `ε ≤ ε₁` (with any number of labels) every cut is at most
`arccos ρ / π + ξ`. -/
theorem kkmo_sound {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ (R : ℕ) (G : UGInstance), Good R G →
      ugValue G ≤ ε → ∀ f : ℕ → Cube (Fin R) → Bool,
        kkmoCut ρ R G.2.2.2 f ≤ Real.arccos ρ / Real.pi + ξ := by
  obtain ⟨K, -, τ, hτ, hmis⟩ := cut_le_of_lowInfluence hρ1 hρ0 (half_pos hξ)
  obtain ⟨ε₁, hε₁, hfew⟩ := kkmo_few_bad K hτ (half_pos hξ)
  refine ⟨ε₁, hε₁, fun ε hε hεε R G hG hval f ↦ ?_⟩
  have hA : 0 ≤ Real.arccos ρ / Real.pi := div_nonneg (Real.arccos_nonneg ρ) Real.pi_pos.le
  by_cases hcs : G.2.2.2 = []
  · rw [hcs, kkmoCut_nil]; linarith
  obtain ⟨D, -, hm, -, -⟩ := exists_leftDeg hG hcs
  have hm' : (0 : ℝ) < G.1 := by exact_mod_cast hm
  rw [kkmoCut_eq ρ hG hcs f, div_le_iff₀ hm']
  have hB := hfew ε hε hεε R G hG hval f
  have hpt : ∀ u ∈ range G.1, cutValue ρ (avgTable G.2.2.2 f u) ≤
      (Real.arccos ρ / Real.pi + ξ / 2) + (if ∃ i, τ ≤ cutoffInfluence K i
        (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1) then 1 else 0) := by
    intro u _
    split_ifs with h
    · have hρ1' : ρ ≤ 1 := by linarith
      linarith [cutValue_le_one hρ1.le hρ1' (avgTable_mem G.2.2.2 f u)]
    · push Not at h
      have := hmis R (avgTable G.2.2.2 f u) (avgTable_mem G.2.2.2 f u) h
      unfold cutValue
      linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_boole]
  linarith

/-- **The cut value is Lipschitz in `ρ`** on `[-r, r]`, `r < 1`, uniformly in the instance and the
cut. -/
theorem kkmoCut_lipschitz {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ ρ ρ' : ℝ, |ρ| ≤ r → |ρ'| ≤ r → ∀ (R : ℕ) (G : UGInstance), Good R G →
      ∀ f : ℕ → Cube (Fin R) → Bool,
        |kkmoCut ρ' R G.2.2.2 f - kkmoCut ρ R G.2.2.2 f| ≤ M * |ρ' - ρ| := by
  have hr : 0 < 1 - r := by linarith
  refine ⟨2 / (1 - r), by positivity, fun ρ ρ' hρ hρ' R G hG f ↦ ?_⟩
  by_cases hcs : G.2.2.2 = []
  · rw [hcs, kkmoCut_nil, kkmoCut_nil, sub_self, abs_zero]; positivity
  obtain ⟨D, -, hm, -, -⟩ := exists_leftDeg hG hcs
  have hm' : (0 : ℝ) < G.1 := by exact_mod_cast hm
  rw [kkmoCut_eq ρ' hG hcs f, kkmoCut_eq ρ hG hcs f, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div, abs_of_pos hm', div_le_iff₀ hm']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ u ∈ range G.1, |cutValue ρ' (avgTable G.2.2.2 f u) -
      cutValue ρ (avgTable G.2.2.2 f u)| ≤ 2 / (1 - r) * |ρ' - ρ| := by
    intro u _
    unfold cutValue
    rw [corrAverage_cut, corrAverage_cut]
    have hh : ∀ x, -1 ≤ 2 * avgTable G.2.2.2 f u x - 1 ∧ 2 * avgTable G.2.2.2 f u x - 1 ≤ 1 :=
      fun x ↦ by
        have := avgTable_mem G.2.2.2 f u x
        constructor <;> linarith [this.1, this.2]
    have hs := abs_stability_sub_le hr0 hr1 hρ hρ' hh
    have e : (1 - stability ρ' (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)) / 2 -
        (1 - stability ρ (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)) / 2 =
        -((stability ρ' (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1) -
          stability ρ (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)) / 2) := by ring
    rw [e, abs_neg, abs_div, abs_two]
    have : 0 ≤ 2 / (1 - r) * |ρ' - ρ| := by positivity
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

end BGHKLMM26.Hard
