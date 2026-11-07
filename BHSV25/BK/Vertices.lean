module

public import BHSV25.BK.Graph

/-!
# The vertices of the reduction graph as data

The vertex numbered `x` of one copy is the tuple `(a, z, k, u)` (`BHSV25.BK.Prm.vEquiv`, built
from Mathlib's `finProdFinEquiv` and `finFunctionFinEquiv`), and its digits `BHSV25.BK.Prm.rv`
are those of the tuple (`BHSV25.BK.Prm.rv_eq`). Sums over the vertices are sums over the tuples,
and sums over `Fin n → α` of a function of one coordinate factor (`BHSV25.BK.sum_pi_apply`).

The demands are read as subcubes (`BHSV25.BK.inSub`): two demands at the same right vertex are
incompatible exactly when a point of one has its negation in the other
(`BHSV25.BK.clash_iff`).
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames OAI.MaxCutGames.Foundations.Hastad

namespace Prm

variable (P : Prm)

/-- The vertices of one copy, as tuples `(a, z, k, u)`. -/
abbrev Vtx (m L : ℕ) := (((Fin P.R → Fin P.M) × Cube (Fin P.R)) × (Fin P.t → Fin L)) × Fin m

/-- The numbering of the vertices. -/
def vEquiv (m L : ℕ) : Fin (P.nV m L) ≃ P.Vtx m L :=
  finProdFinEquiv.symm.trans <| Equiv.prodCongr
    (finProdFinEquiv.symm.trans <| Equiv.prodCongr
      (finProdFinEquiv.symm.trans <| Equiv.prodCongr finFunctionFinEquiv.symm
        (finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv)))
      finFunctionFinEquiv.symm)
    (Equiv.refl _)

/-- The digits of a tuple. -/
def rvS {m L : ℕ} (v : P.Vtx m L) : RV :=
  ((v.2 : ℕ), List.ofFn (fun p ↦ (v.1.2 p : ℕ)), List.ofFn v.1.1.2,
    List.ofFn (fun j ↦ (v.1.1.1 j : ℕ)))

theorem ofFn_eq_range_map {n : ℕ} {β : Type*} (f : ℕ → β) :
    List.ofFn (fun i : Fin n ↦ f i) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

theorem vEquiv_u (m L : ℕ) (x : Fin (P.nV m L)) : ((P.vEquiv m L x).2 : ℕ) = x % m := rfl

theorem vEquiv_k (m L : ℕ) (x : Fin (P.nV m L)) (p : Fin P.t) :
    ((P.vEquiv m L x).1.2 p : ℕ) = x / m % L ^ P.t / L ^ (p : ℕ) % L := rfl

theorem vEquiv_a (m L : ℕ) (x : Fin (P.nV m L)) (j : Fin P.R) :
    ((P.vEquiv m L x).1.1.1 j : ℕ) = x / m / L ^ P.t / 2 ^ P.R / P.M ^ (j : ℕ) % P.M := rfl

theorem vEquiv_z (m L : ℕ) (x : Fin (P.nV m L)) (j : Fin P.R) :
    (P.vEquiv m L x).1.1.2 j = decide (x / m / L ^ P.t % 2 ^ P.R / 2 ^ (j : ℕ) % 2 = 1) := by
  have key : ∀ (d : ℕ) (h : d < 2), ((⟨d, h⟩ : Fin 2) == 1) = decide (d = 1) := by
    intro d h
    interval_cases d <;> rfl
  exact key _ _

/-- **The digits of the vertex numbered `x`** are those of its tuple. -/
theorem rv_eq (m L : ℕ) (x : Fin (P.nV m L)) : P.rv m L x = P.rvS (P.vEquiv m L x) := by
  unfold rv rvS
  refine Prod.ext (P.vEquiv_u m L x).symm (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only
    rw [← ofFn_eq_range_map]
    congr 1
  · simp only
    rw [← ofFn_eq_range_map (fun j ↦ decide (↑x / m / L ^ P.t % 2 ^ P.R / 2 ^ j % 2 = 1))]
    congr 1
  · simp only
    rw [← ofFn_eq_range_map]
    congr 1

theorem getD_ofFn {n : ℕ} {β : Type*} (f : Fin n → β) (d : β) (i : Fin n) :
    (List.ofFn f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem rvS_ks {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) : (P.rvS v).2.1.getD p 0 = v.1.2 p :=
  getD_ofFn _ _ p

theorem rvS_z {m L : ℕ} (v : P.Vtx m L) (j : Fin P.R) : (P.rvS v).2.2.1.getD j false = v.1.1.2 j :=
  getD_ofFn _ _ j

theorem rvS_a {m L : ℕ} (v : P.Vtx m L) (j : Fin P.R) : (P.rvS v).2.2.2.getD j 0 = v.1.1.1 j :=
  getD_ofFn _ _ j

end Prm

/-! ### Sums over functions -/

/-- A sum over `Fin n → α` of a function of the coordinate `j`. -/
theorem sum_pi_apply {n : ℕ} {α : Type*} [Fintype α] (j : Fin n) (φ : α → ℝ) :
    ∑ f : Fin n → α, φ (f j) = (Fintype.card α : ℝ) ^ (n - 1) * ∑ x, φ x := by
  rw [← (Equiv.piSplitAt j (fun _ ↦ α)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.piSplitAt_symm_apply, dite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.card_fun]
  have : Fintype.card {i // i ≠ j} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  rw [this]
  push_cast
  ring

/-- A sum over `Fin t → α` of a product of a function of each coordinate. -/
theorem sum_prod_apply {t : ℕ} {α : Type*} [Fintype α] (ψ : α → ℝ) :
    ∑ f : Fin t → α, ∏ p, ψ (f p) = (∑ x, ψ x) ^ t := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]

/-! ### Demands as subcubes -/

/-- The point `w` of the cube of the right end of the `p`-th constraint lies in the `p`-th
demand of `r`: `w_i = z_{π_p(i)}` at every fixed coordinate `i`. -/
def inSub {R : ℕ} (cs : List UGConstraint) (r : RV) (p : ℕ) (w : Cube (Fin R)) : Prop :=
  ∀ i : Fin R, fixedAt cs r p i = true → w i = zAt cs r p i

/-- **Incompatible demands**: two demands at the same right vertex clash exactly when a point of
the first has its negation in the second. -/
theorem clash_iff (P : Prm) (cs : List UGConstraint) (r r' : RV) (p q : ℕ) :
    P.clash cs r r' p q = true ↔ (conAt cs r p).1.2 = (conAt cs r' q).1.2 ∧
      ∃ w : Cube (Fin P.R), inSub cs r p w ∧ inSub cs r' q (fun i ↦ !w i) := by
  unfold Prm.clash inSub
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, bne_iff_ne, ne_eq]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun ⟨w, hw, hw'⟩ i hi ↦ ?_⟩
  · refine ⟨fun i ↦ if fixedAt cs r p i then zAt cs r p i else !zAt cs r' q i, ?_, ?_⟩
    · intro i hi
      simp [hi]
    · intro i hi
      by_cases h1 : fixedAt cs r p i = true
      · rcases h ↑i i.2 with (h2 | h2) | h2
        · rw [h1] at h2; exact absurd h2 (by decide)
        · rw [hi] at h2; exact absurd h2 (by decide)
        · simp only [h1, ite_true]
          cases hz : zAt cs r p i <;> cases hz' : zAt cs r' q i <;> simp_all
      · simp [h1]
  · by_cases h1 : fixedAt cs r p i = true
    · by_cases h2 : fixedAt cs r' q i = true
      · right
        have e1 := hw ⟨i, hi⟩ h1
        have e2 := hw' ⟨i, hi⟩ h2
        simp only at e1 e2
        rw [← e1, ← e2]
        cases w ⟨i, hi⟩ <;> simp
      · left; right; simpa using h2
    · left; left; simpa using h1

end BHSV25.BK
