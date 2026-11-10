module

public import BHSV25.Net.Approx
public import BHSV25.Net.Machine
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The filters on the input of a graph

On the input of a graph, the operations of `BHSV25/Net/Machine.lean` compute what they should:

* **the input of a graph** (`BHSV25.Net.numV_graph`, `BHSV25.Net.adjB_graph`,
  `BHSV25.Net.deg_graph`): the table gives the adjacency relation, and the degree of vertex `0` is
  the degree of the graph (the proof of `BHSV25.Net.adjB_graph` is adapted from
  `BHSV25.Alg.adjBit_adjTable` in `BHSV25/Alg/GraphMachine.lean`);
* **the two filters** (`BHSV25.Net.bottom_base`, `BHSV25.Net.abs_base`): `M / D` is
  `(I - Ã) / 2` for the bottom eigenspace and `Ã` for the absolute one, and it is symmetric
  (`BHSV25.Net.toMat_baseMat_symm`);
* **graphs without edges** have only the eigenvalue `0` (`BHSV25.Net.eig_eq_zero_of_deg_zero`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral

/-! ### The input of a graph -/

theorem numV_graph (G : Graph) : numV (G.1, adjTable G) = G.1 := by
  have h : (adjTable G).length = G.1 * G.1 := by rw [adjTable, List.length_ofFn]
  rw [numV, h]
  refine min_eq_right ?_
  rcases Nat.eq_zero_or_pos G.1 with h0 | h0
  · omega
  · exact Nat.le_mul_of_pos_left _ h0

open Classical in
theorem adjB_graph (G : Graph) (u v : Fin G.1) :
    adjB G.1 (adjTable G) u v = decide (G.2.Adj u v) := by
  have hlt : (u : ℕ) * G.1 + v < G.1 * G.1 := by
    have := u.2
    have := v.2
    nlinarith
  have hlen : (adjTable G).length = G.1 * G.1 := by rw [adjTable, List.length_ofFn]
  have hk : (⟨(u : ℕ) * G.1 + v, hlt⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) :=
    Fin.ext (by rw [finProdFinEquiv_apply_val]; ring)
  rw [adjB, List.getD_eq_getElem _ _ (by rw [hlen]; exact hlt)]
  simp only [adjTable, List.getElem_ofFn]
  rw [show (⟨(u : ℕ) * G.1 + v, _⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) from hk,
    Equiv.symm_apply_apply]

theorem countP_range (n : ℕ) (q : ℕ → Bool) :
    (List.range n).countP q = ∑ v : Fin n, if q v then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Fin.sum_univ_castSucc]
    simp [List.countP_cons]

open Classical in
theorem deg_graph (G : Graph) (h0 : 0 < G.1) : deg G.1 (adjTable G) = G.2.degree ⟨0, h0⟩ := by
  rw [deg, countP_range, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have h : (adjTable G).getD v false = adjB G.1 (adjTable G) (⟨0, h0⟩ : Fin G.1) v := by
    simp [adjB]
  rw [h, adjB_graph]
  simp

/-! ### The filter -/

theorem map_castRingHom_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (e : ℕ) :
    (M ^ e).map (Int.castRingHom ℝ) = (M.map (Int.castRingHom ℝ)) ^ e := by
  induction e with
  | zero => simp [Matrix.map_one]
  | succ e ih => rw [pow_succ, pow_succ, Matrix.map_mul, ih]

theorem toMat_baseMat_symm (p : Params) (G : Graph) (d : ℕ) :
    (toMat G.1 (baseMat p.bottom G.1 d (adjTable G)))ᵀ =
      toMat G.1 (baseMat p.bottom G.1 d (adjTable G)) := by
  classical
  ext u v
  rw [transpose_apply, toMat_baseMat]
  simp only [entry, adjB_graph, G.2.adj_comm u v]
  by_cases h : u = v
  · subst h; rfl
  · have h1 : (v : ℕ) ≠ u := fun h' ↦ h (Fin.ext h'.symm)
    have h2 : (u : ℕ) ≠ v := fun h' ↦ h (Fin.ext h')
    simp [h1, h2]

/-! ### Candidates -/

/-! ### The constants -/

/-! ### Degenerate inputs -/

open Classical in
/-- A regular graph of degree `0` has only the eigenvalue `0`. -/
theorem eig_eq_zero_of_deg_zero (G : Graph) (h : G.2.IsRegularOfDegree 0) (i : Fin G.1) :
    G.eig i = 0 := by
  classical
  have h0 : ∀ u v, G.normAdj u v = 0 := fun u v ↦ by
    rw [G.normAdj_of_isRegularOfDegree h]
    simp
  have h1 := coeff_mulVec G.normAdj_isHermitian i ⇑(G.normAdj_isHermitian.eigenvectorBasis i)
  rw [coeff_eigenvector] at h1
  have h2 : G.normAdj *ᵥ ⇑(G.normAdj_isHermitian.eigenvectorBasis i) = 0 := by
    ext u
    simp only [mulVec, dotProduct, h0, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  rw [h2] at h1
  simp only [coeff, dotProduct_zero] at h1
  simp only [ite_true, mul_one] at h1
  exact h1.symm

theorem eq_zero_of_inEigSpan (G : Graph) {S : ℝ → Prop} {w : Fin G.1 → ℝ}
    (hw : G.InEigSpan S w) (hS : ∀ i, ¬ S (G.eig i)) : w = 0 :=
  eq_of_coeff_eq G.normAdj_isHermitian fun i ↦ by
    rw [hw i (hS i)]
    simp [coeff]

/-! ### The two filters -/

theorem coeff_halfSub (G : Graph) (i : Fin G.1) (x : Fin G.1 → ℝ) :
    coeff G.normAdj_isHermitian i (((1 / 2 : ℝ) • (1 - G.normAdj)) *ᵥ x) =
      ((1 - G.eig i) / 2) * coeff G.normAdj_isHermitian i x := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, coeff_smul, coeff_sub,
    coeff_mulVec]
  unfold Graph.eig
  ring

open Classical in
/-- For the bottom eigenspace, `M / D = (I - Ã) / 2`. -/
theorem bottom_base (p : Params) (hp : p.bottom = true) (G : Graph) {d : ℕ}
    (hreg : G.2.IsRegularOfDegree d) (hd : 0 < d) :
    (denBase p d : ℝ)⁻¹ • (toMat G.1 (baseMat p.bottom G.1 d (adjTable G))).map
      (Int.castRingHom ℝ) = (1 / 2 : ℝ) • (1 - G.normAdj) := by
  classical
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext u v
  rw [Matrix.smul_apply, Matrix.map_apply, toMat_baseMat, Matrix.smul_apply, Matrix.sub_apply,
    G.normAdj_of_isRegularOfDegree hreg u v, Matrix.one_apply]
  simp only [entry, hp, ite_true, adjB_graph, denBase, smul_eq_mul, Int.coe_castRingHom]
  by_cases huv : u = v
  · subst huv
    simp only [ite_true, G.2.irrefl, decide_false, Bool.false_eq_true, ite_false]
    push_cast
    field_simp
    ring
  · have h' : (u : ℕ) ≠ v := fun h ↦ huv (Fin.ext h)
    by_cases ha : G.2.Adj u v
    · simp only [h', huv, ha, ite_false, ite_true, decide_true]
      push_cast
      field_simp
      ring
    · simp only [h', huv, ha, ite_false, decide_false, Bool.false_eq_true]
      simp

open Classical in
/-- For the absolute eigenspace, `M / D = Ã`. -/
theorem abs_base (p : Params) (hp : p.bottom = false) (G : Graph) {d : ℕ}
    (hreg : G.2.IsRegularOfDegree d) :
    (denBase p d : ℝ)⁻¹ • (toMat G.1 (baseMat p.bottom G.1 d (adjTable G))).map
      (Int.castRingHom ℝ) = G.normAdj := by
  classical
  ext u v
  rw [Matrix.smul_apply, Matrix.map_apply, toMat_baseMat, G.normAdj_of_isRegularOfDegree hreg u v]
  simp only [entry, hp, Bool.false_eq_true, ite_false, adjB_graph, denBase, smul_eq_mul,
    Int.coe_castRingHom, one_mul]
  by_cases ha : G.2.Adj u v
  · simp [ha]
  · simp [ha]

/-! ### The two nets -/

end Net

end BHSV25
