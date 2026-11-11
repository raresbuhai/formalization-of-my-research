module

public import BHSV25.BK.Basic
import Mathlib.Data.List.GetD

/-!
# Values of Unique Games instances through labelings of `ℕ`

The values `UniqueGames.ugValue` and `UniqueGames.ugGraphValue` are suprema over labelings of
`Fin n`. Here they are bounded through labelings of `ℕ` with labels below `R` on the vertices and
`0` past them (`BHSV25.UG.IsLab`), which is how the reductions of `BHSV25/UG/` build and read
labelings, as in `BGHKLMM26/Hardness/Enlarge.lean`.
-/

@[expose] public section

namespace BHSV25.UG

open Finset UniqueGames BK

/-- A labeling of `ℕ` with labels below `R` on the vertices `u < k` and `0` past them. -/
def IsLab (k R : ℕ) (σ : ℕ → ℕ) : Prop := (∀ u < k, σ u < R) ∧ ∀ u, k ≤ u → σ u = 0

theorem lab_isLab {k R : ℕ} (σ : Fin k → Fin R) : IsLab k R (lab σ) :=
  ⟨fun u hu ↦ by simp [lab, hu], fun u hu ↦ by simp [lab, not_lt.2 hu]⟩

theorem eq_lab {k R : ℕ} {σ : ℕ → ℕ} (h : IsLab k R σ) :
    lab (fun u : Fin k ↦ (⟨σ u, h.1 u u.isLt⟩ : Fin R)) = σ := by
  funext u
  unfold lab
  split_ifs with hu
  · rfl
  · exact (h.2 u (not_lt.1 hu)).symm

/-! ### Bipartite instances -/

theorem ugValue_nonneg (G : UGInstance) : 0 ≤ ugValue G :=
  Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun _ ↦
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Lower bound on the value** by a labeling of `ℕ`. -/
theorem le_ugValue' (G : UGInstance) {σ τ : ℕ → ℕ} (hσ : IsLab G.1 G.2.2.1 σ)
    (hτ : IsLab G.2.1 G.2.2.1 τ) :
    (ugSatisfied G σ τ : ℝ) / G.2.2.2.length ≤ ugValue G := by
  have h := le_ugValue G (fun u ↦ ⟨σ u, hσ.1 u u.isLt⟩) (fun v ↦ ⟨τ v, hτ.1 v v.isLt⟩)
  rwa [eq_lab hσ, eq_lab hτ] at h

/-- **Upper bound on the value** by a bound on every labeling of `ℕ`. -/
theorem ugValue_le' {G : UGInstance} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ τ, IsLab G.1 G.2.2.1 σ → IsLab G.2.1 G.2.2.1 τ →
      (ugSatisfied G σ τ : ℝ) / G.2.2.2.length ≤ c) :
    ugValue G ≤ c :=
  Real.iSup_le (fun σ ↦ Real.iSup_le (fun τ ↦ h _ _ (lab_isLab σ) (lab_isLab τ)) hc) hc

/-! ### Instances on graphs -/

theorem ugGraphValue_nonneg (G : UGGraphInstance) : 0 ≤ ugGraphValue G :=
  Real.iSup_nonneg fun _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Lower bound on the value** of an instance on a graph by a labeling of `ℕ`. -/
theorem le_ugGraphValue (G : UGGraphInstance) {σ : ℕ → ℕ} (hσ : IsLab G.1 G.2.1 σ) :
    (ugGraphSatisfied G σ : ℝ) / G.2.2.length ≤ ugGraphValue G := by
  have h : (ugGraphSatisfied G (lab fun u : Fin G.1 ↦ (⟨σ u, hσ.1 u u.isLt⟩ : Fin G.2.1)) : ℝ) /
      G.2.2.length ≤ ugGraphValue G :=
    le_ciSup (f := fun σ : Fin G.1 → Fin G.2.1 ↦
      (ugGraphSatisfied G (lab σ) : ℝ) / G.2.2.length) (Set.finite_range _).bddAbove _
  rwa [eq_lab hσ] at h

/-- **Upper bound on the value** of an instance on a graph by a bound on every labeling of `ℕ`. -/
theorem ugGraphValue_le' {G : UGGraphInstance} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ, IsLab G.1 G.2.1 σ → (ugGraphSatisfied G σ : ℝ) / G.2.2.length ≤ c) :
    ugGraphValue G ≤ c :=
  Real.iSup_le (fun σ ↦ h _ (lab_isLab σ)) hc

/-! ### Sums over lists -/

/-- A sum over the positions of a list is the sum over its elements. -/
theorem sum_range_getD {α : Type*} (l : List α) (d : α) (f : α → ℝ) :
    ∑ j ∈ range l.length, f (l.getD j d) = (l.map f).sum := by
  rw [Finset.sum_range (fun j ↦ f (l.getD j d))]
  have h : ∀ i : Fin l.length, l.getD i d = l[i] := fun i ↦ List.getD_eq_getElem _ _ i.2
  simp_rw [h]
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_getElem (by simp) fun i h1 h2 ↦ by simp

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (φ : β → ℝ) :
    ((l.flatMap f).map φ).sum = (l.map fun a ↦ ((f a).map φ).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_list_comm {ι α : Type*} (s : Finset ι) (l : List α) (φ : ι → α → ℝ) :
    ∑ i ∈ s, (l.map (φ i)).sum = (l.map fun a ↦ ∑ i ∈ s, φ i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- The number of satisfied constraints as a sum of indicators. -/
theorem ugSatisfied_eq_sum (G : UGInstance) (σ τ : ℕ → ℕ) :
    (ugSatisfied G σ τ : ℝ) = (G.2.2.2.map fun c ↦ ind (σ c.1.1 = c.2.getD (τ c.1.2) 0)).sum := by
  unfold ugSatisfied
  exact length_filter_eq _ fun c : UGConstraint ↦ σ c.1.1 = c.2.getD (τ c.1.2) 0

theorem ugGraphSatisfied_eq_sum (G : UGGraphInstance) (σ : ℕ → ℕ) :
    (ugGraphSatisfied G σ : ℝ) = (G.2.2.map fun c ↦ ind (σ c.1.1 = c.2.getD (σ c.1.2) 0)).sum := by
  unfold ugGraphSatisfied
  exact length_filter_eq _ fun c : UGConstraint ↦ σ c.1.1 = c.2.getD (σ c.1.2) 0

end BHSV25.UG
