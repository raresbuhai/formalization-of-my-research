module

public import BHSV25.BK.Graph

/-!
# Disjoint copies

`k` disjoint copies of a graph `H` on `n` vertices (`BHSV25.BK.copies`) have maximum degree below
`n`, so at most `η k n` once `η k ≥ 1` (`BHSV25.BK.copies_maxDeg`); two disjoint independent sets
of `H` give two of `k` times the size (`BHSV25.BK.copies_yes`); and an independent set of the
copies is at most `k` times one of `H` (`BHSV25.BK.copies_indep`). A clique has no independent
set of two vertices (`BHSV25.BK.clique_indep`).
-/

@[expose] public section

namespace BHSV25.BK

open Finset

theorem fin_eq_of_divNat_modNat {k n : ℕ} {i j : Fin (k * n)} (h1 : i.divNat = j.divNat)
    (h2 : i.modNat = j.modNat) : i = j := by
  have hi := finProdFinEquiv.apply_symm_apply i
  have hj := finProdFinEquiv.apply_symm_apply j
  rw [finProdFinEquiv_symm_apply] at hi hj
  rw [← hi, ← hj, h1, h2]

theorem copies_degree_le (H : Graph) (k : ℕ) (i : Fin (copies H k).1)
    (inst : Fintype ((copies H k).2.neighborSet i)) : (copies H k).2.degree i ≤ H.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((copies H k).2.neighborFinset i).card ≤ (univ : Finset (Fin H.1)).card := by
        refine Finset.card_le_card_of_injOn (fun j ↦ j.modNat) (fun _ _ ↦ mem_univ _) ?_
        intro a ha b hb hab
        rw [mem_coe, SimpleGraph.mem_neighborFinset] at ha hb
        exact fin_eq_of_divNat_modNat (ha.1.symm.trans hb.1) hab
    _ = H.1 := by simp

/-- **The copies have small degree**: every vertex has fewer than `n` neighbours. -/
theorem copies_maxDeg (H : Graph) {k : ℕ} {η : ℝ} (hk : 1 ≤ η * k) : MaxDegLE (copies H k) η := by
  intro i
  have hn : (0 : ℝ) ≤ H.1 := Nat.cast_nonneg _
  refine le_trans (Nat.cast_le.mpr (copies_degree_le H k i _)) ?_
  calc (H.1 : ℝ) = 1 * H.1 := (one_mul _).symm
    _ ≤ η * k * H.1 := mul_le_mul_of_nonneg_right hk hn
    _ = η * (copies H k).1 := by push_cast; ring

/-- The vertices of all copies over a set of vertices of `H`. -/
def lift (H : Graph) (k : ℕ) (I : Finset (Fin H.1)) : Finset (Fin (k * H.1)) :=
  (univ ×ˢ I).map finProdFinEquiv.toEmbedding

theorem mem_lift {H : Graph} {k : ℕ} {I : Finset (Fin H.1)} {i : Fin (k * H.1)} :
    i ∈ lift H k I ↔ i.modNat ∈ I := by
  unfold lift
  rw [Finset.mem_map_equiv, mem_product, finProdFinEquiv_symm_apply]
  simp

theorem card_lift (H : Graph) (k : ℕ) (I : Finset (Fin H.1)) : (lift H k I).card = k * I.card := by
  unfold lift
  rw [card_map, card_product, card_univ, Fintype.card_fin]

theorem lift_indep {H : Graph} {k : ℕ} {I : Finset (Fin H.1)}
    (hI : H.2.IsIndepSet (I : Set (Fin H.1))) :
    (copies H k).2.IsIndepSet (lift H k I : Set (Fin (copies H k).1)) := by
  intro i hi j hj _ hij
  have hi' := mem_lift.mp hi
  have hj' := mem_lift.mp hj
  exact hI hi' hj' (H.2.ne_of_adj hij.2) hij.2

/-- **Two disjoint independent sets** of `H` give two of the copies, `k` times larger. -/
theorem copies_yes (H : Graph) (k : ℕ) {I J : Finset (Fin H.1)} (hd : Disjoint I J)
    (hI : H.2.IsIndepSet (I : Set (Fin H.1))) (hJ : H.2.IsIndepSet (J : Set (Fin H.1))) :
    ∃ I' J' : Finset (Fin (copies H k).1), Disjoint I' J' ∧
      (copies H k).2.IsIndepSet (I' : Set (Fin (copies H k).1)) ∧
      (copies H k).2.IsIndepSet (J' : Set (Fin (copies H k).1)) ∧
      I'.card = k * I.card ∧ J'.card = k * J.card := by
  refine ⟨lift H k I, lift H k J, ?_, lift_indep hI, lift_indep hJ, card_lift _ _ _,
    card_lift _ _ _⟩
  rw [Finset.disjoint_left]
  intro i hi hj
  exact Finset.disjoint_left.mp hd (mem_lift.mp hi) (mem_lift.mp hj)

/-- **An independent set of the copies** is at most `k` times one of `H`. -/
theorem copies_indep (H : Graph) {k : ℕ} (hk : 0 < k) (I : Finset (Fin (copies H k).1))
    (hI : (copies H k).2.IsIndepSet (I : Set (Fin (copies H k).1))) :
    ∃ S : Finset (Fin H.1), H.2.IsIndepSet (S : Set (Fin H.1)) ∧ I.card ≤ k * S.card := by
  classical
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image univ
    (fun c : Fin k ↦ (I.filter fun i : Fin (k * H.1) ↦ i.divNat = c).card) hne
  refine ⟨(I.filter fun i : Fin (k * H.1) ↦ i.divNat = c).image fun i ↦ i.modNat, ?_, ?_⟩
  · intro x hx y hy hxy hadj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    rw [mem_filter] at hi hj
    exact hI hi.1 hj.1 (fun h ↦ hxy (by rw [h])) ⟨hi.2.trans hj.2.symm, hadj⟩
  · rw [Finset.card_image_of_injOn]
    · calc I.card = ∑ c' : Fin k, (I.filter fun i : Fin (k * H.1) ↦ i.divNat = c').card :=
            Finset.card_eq_sum_card_fiberwise (fun i _ ↦ mem_univ _)
        _ ≤ ∑ _c' : Fin k, (I.filter fun i : Fin (k * H.1) ↦ i.divNat = c).card :=
            Finset.sum_le_sum fun c' _ ↦ hc c' (mem_univ _)
        _ = k * _ := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    · intro i hi j hj hij
      rw [mem_coe, mem_filter] at hi hj
      exact fin_eq_of_divNat_modNat (hi.2.trans hj.2.symm) hij

/-- A clique has no independent set of two vertices. -/
theorem clique_indep {s : ℕ} (S : Finset (Fin (clique s).1))
    (hS : (clique s).2.IsIndepSet (S : Set (Fin (clique s).1))) : S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  exact hS ha hb hab ((SimpleGraph.top_adj a b).mpr hab)

end BHSV25.BK
