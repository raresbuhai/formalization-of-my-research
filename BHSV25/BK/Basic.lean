module

public import BHSV25.Model
public import OAI.Computability.MaxCut.Estimates.Degree
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.GetD

/-!
# Long codes, influences and the decoding of labels

Infrastructure for the proof of Bansal and Khot's theorem (`BHSV25/BK/`), copied from
`BGHKLMM26/Hardness/{Defs,KKMOFourier,KKMO}.lean` (papers do not import each other), with the
namespace changed to `BHSV25.BK` and the unused parts left out.

* Tables on the cube `{0,1}^R` (OpenAI's `Cube (Fin R)`), read through a permutation table `π`
  (`BHSV25.BK.permCube`, `(π x)ⱼ = x_{π(j)}`); the constraints at a left vertex
  (`BHSV25.BK.nbrs`); the averaged long code `g_u(x) = E_{(u,v,π)} f_v(π x)`
  (`BHSV25.BK.avgTable`).
* Fourier facts: degree-`K` influences (OpenAI's `cutoffInfluence`) are convex, move with a
  permutation of the coordinates, and sum to at most `K` for `[-1,1]`-valued tables.
* **Decoding** (`BHSV25.BK.few_bad`, BGHKLMM26's `kkmo_few_bad`, after Khot, Kindler, Mossel and
  O'Donnell): on simple bi-regular Unique Games instances of small value, few left vertices `u`
  have a coordinate of large degree-`K` influence in `2 g_u - 1`.
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

/-! ### Tables on the cube -/

/-- The `0/1` value of a bit. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- The table `π = [π(0), …, π(R-1)]` acting on the cube: `(π x)ⱼ = x_{π(j)}`, so that the
dictator of `σ(v)` at `v`, read through `π`, is the dictator of `π(σ(v))`. -/
def permCube {R : ℕ} (π : List ℕ) (x : Cube (Fin R)) : Cube (Fin R) :=
  fun j ↦ if h : π.getD j 0 < R then x ⟨π.getD j 0, h⟩ else false

/-- The constraints at the left vertex `u`. -/
def nbrs (cs : List UGConstraint) (u : ℕ) : List UGConstraint := cs.filter fun c ↦ c.1.1 = u

/-- The instances of the gap problem with `R` labels: valid, simple, bi-regular. -/
def Good (R : ℕ) (G : UGInstance) : Prop :=
  UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧ BiRegular G

/-- The averaged long code `g_u(x) = E_{(u,v) ∈ cs} f_v(π_{uv} x)` of the left vertex `u`. -/
noncomputable def avgTable {R : ℕ} (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool) (u : ℕ)
    (x : Cube (Fin R)) : ℝ :=
  ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum / (nbrs cs u).length

section Fourier

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ### Linearity of the coefficients -/

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

theorem bitVal_nonneg (b : Bool) : 0 ≤ bitVal b := by cases b <;> norm_num [bitVal]

theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by cases b <;> norm_num [bitVal]

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

/-- **Few left vertices have an influential coordinate** [BGHKLMM26, Lemma 5.4], with low-degree
influences: on instances of small value, at most a `ν` fraction of the left vertices `u` have a
coordinate of degree-`K` influence at least `τ` in `2 g_u - 1`. (Decoding: such a coordinate is
influential in many of the tables `f_v`, through `π_{uv}`, and the influential coordinates give a
labeling satisfying many constraints.) -/
theorem few_bad (K : ℕ) {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) :
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

end BHSV25.BK
