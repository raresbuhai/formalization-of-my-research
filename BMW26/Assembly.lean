module

public import BMW26.Spec.Main
public import BMW26.SoS.Main
public import BMW26.Round.Correct
public import BMW26.Alg.PolyTime
public import BMW26.Prob.Percolation
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Assembly

The proof of [BMW26, Theorem 1.2] from its parts.

* `BMW26.success_of_good`: on a good sample (`BMW26.Good` with `ε = 1/100` and `ξ, τ₀ ≤ d^-(c+8)`),
  for every renaming, the algorithm recovers the hidden vectors of all but `2^d / d^c` vertices.
  The chain: the coordinate cuts make the program valid (`BMW26.Alg.valid_of_feasible`); the
  solver's pseudo-expectation (`BMW26.Alg.alg_spec`), renamed to the hypercube's variables,
  satisfies the program approximately (`BMW26.Asm.approxSatisfies_rename`, with the cut constraint
  renamed to `BMW26.cutPolyCube` by `BMW26.Asm.rename_cutPolyFin`), so the certificate
  `BMW26.level_one_mass` gives its level-one mass (`SoS.DerivesN.approx_ge`, with every constraint
  of norm `‖f‖₂ < 16 n³`, `BMW26.Asm.one_add_coeffNorm_le`: the error `η ∏ (1 + ‖f‖₂)` is then
  `2^-(n² + 10) 2^O(n log n)`, negligible); the mixture of the coordinate cuts
  (`BMW26.cutMixture`) bounds its objective; `BMW26.frobenius_bound` and `BMW26.roundOut_recovers`
  conclude (`BMW26.Asm.mass_bound`, `BMW26.Asm.success_aux`).
* `BMW26.good_whp`: a sample of `Q_d(p)` is good with probability at least `1 - 4/d`:
  `BMW26.spectral_whp` for `Q_d` and for its `2d` half-cubes (`BMW26.halfCoins`,
  `BMW26.specClose_halfW`), and `BMW26.count_whp`, with a union bound (`BMW26.Asm.good_aux`).
* `BMW26.hypercube_recovery_of_parts`: the theorem of `Challenge.lean`.
-/

@[expose] public section

namespace BMW26

open MeasureTheory Filter Topology

/-! ### Renaming the variables of a pseudo-expectation -/

namespace Asm

open MvPolynomial SoS

section Rename

variable {σ τ : Type*}

theorem rename_symm_rename (e : σ ≃ τ) (p : MvPolynomial σ ℝ) : rename e.symm (rename e p) = p := by
  rw [rename_rename, e.symm_comp_self, rename_id_apply]

theorem totalDegree_rename_equiv (e : σ ≃ τ) (p : MvPolynomial σ ℝ) :
    (rename e p).totalDegree = p.totalDegree := by
  refine le_antisymm (totalDegree_rename_le _ _) ?_
  have := totalDegree_rename_le e.symm (rename e p)
  rwa [rename_symm_rename] at this

/-- Renaming the variables by a bijection preserves the coefficient norm. -/
theorem coeffNorm_rename (e : σ ≃ τ) (p : MvPolynomial σ ℝ) :
    coeffNorm (rename e p) = coeffNorm p := by
  classical
  unfold coeffNorm
  congr 1
  rw [support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h ↦ Finsupp.mapDomain_injective e.injective h]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [coeff_rename_mapDomain _ e.injective]

/-- A pseudo-expectation with its variables renamed by a bijection `e`:
`q ↦ Ẽ (q ∘ e)`. -/
noncomputable def peRename {ℓ : ℕ} (e : σ ≃ τ) (E : PseudoExpectation σ ℓ) :
    PseudoExpectation τ ℓ where
  toLinearMap := E.toLinearMap ∘ₗ (rename e.symm : MvPolynomial τ ℝ →ₐ[ℝ] _).toLinearMap
  map_one' := by simp
  map_mul_self_nonneg' f hf := by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
    exact E.map_mul_self_nonneg' _ ((Nat.mul_le_mul_left 2 (totalDegree_rename_le _ _)).trans hf)

theorem peRename_apply {ℓ : ℕ} (e : σ ≃ τ) (E : PseudoExpectation σ ℓ) (q : MvPolynomial τ ℝ) :
    peRename e E q = E (rename e.symm q) := rfl

/-- **Transport of approximate satisfaction** along a bijection of the variables. -/
theorem approxSatisfies_rename {ℓ : ℕ} (e : σ ≃ τ) {E : PseudoExpectation σ ℓ}
    {A : System σ ℝ} {η : ℝ} {r : ℕ} (hA : E.ApproxSatisfies A η r) :
    (peRename e E).ApproxSatisfies (A.map (rename e)) η r := by
  classical
  intro S h hh hdeg
  set f : Fin (A.map (rename e)).length ≃ Fin A.length := finCongr (List.length_map _)
  have hget : ∀ i, (A.map (rename e)).get i = rename e (A.get (f i)) := fun i ↦ by
    simp [f, List.get_eq_getElem]
  have h1 := hA (S.map f.toEmbedding) (rename e.symm h) (isSumSq_map _ hh) (by
    rw [Finset.sum_map]
    refine le_trans (add_le_add (totalDegree_rename_le _ _) le_rfl) (le_trans ?_ hdeg)
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [hget, totalDegree_rename_equiv]
    rfl)
  simp only [System.prod, Finset.prod_map, toReal_real, coeffNorm_rename] at h1 ⊢
  rw [peRename_apply, map_mul, map_prod]
  simp only [hget, rename_symm_rename, coeffNorm_rename]
  exact h1

end Rename

/-! ### Edges of subgraphs of the hypercube -/

section Edges

variable {d : ℕ}

theorem flip_inj_left (x : Cube d) : Function.Injective fun j : Fin d ↦ flip x j := by
  intro j k h
  by_contra hjk
  have h' := congrFun h j
  simp only at h'
  rw [flip_apply_self, flip_apply_ne x hjk] at h'
  cases hx : x j <;> simp [hx] at h'

/-- The neighbours of `x` in a subgraph of `Q_d` are flips of `x`. -/
theorem sum_adj_eq_sum_flip {H : SimpleGraph (Cube d)} [DecidableRel H.Adj] (hH : H ≤ cube d)
    (g : Cube d → Cube d → ℝ) :
    ∑ x, ∑ y, (if H.Adj x y then g x y else 0) =
      ∑ j, ∑ x, (if H.Adj x (flip x j) then g x (flip x j) else 0) := by
  rw [Finset.sum_comm (f := fun j x ↦ if H.Adj x (flip x j) then g x (flip x j) else 0)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  symm
  refine Fintype.sum_of_injective (fun j ↦ flip x j) (flip_inj_left x) _ _ ?_ fun j ↦ rfl
  intro y hy
  rw [ite_eq_right_iff]
  intro hadj
  obtain ⟨i, rfl⟩ := cube_adj_iff.1 (hH hadj)
  exact absurd ⟨i, rfl⟩ hy

/-- A function invariant under flipping coordinate `j` sums to twice its sum over `xⱼ = false`. -/
theorem sum_eq_two_mul_sum_low (j : Fin d) (F : Cube d → ℝ) (hF : ∀ x, F (flip x j) = F x) :
    ∑ x, F x = 2 * ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x j = false), F x := by
  rw [Finset.sum_filter]
  have e1 : ∑ x, F x = ∑ x, (if x j = false then F x else 0) +
      ∑ x, (if x j = false then 0 else F x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  have e2 : ∑ x, (if x j = false then 0 else F x) = ∑ x, (if x j = false then F x else 0) := by
    let σ : Cube d ≃ Cube d :=
      ⟨fun x ↦ flip x j, fun x ↦ flip x j, fun x ↦ flip_flip x j, fun x ↦ flip_flip x j⟩
    refine Fintype.sum_equiv σ _ _ fun x ↦ ?_
    simp only [σ, Equiv.coe_fn_mk, flip_apply_self, hF]
    cases x j <;> simp
  rw [e1, e2, two_mul]

theorem sum_adj_eq_two_mul_sum_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin n → Fin n → ℝ) (hf : ∀ u v, f u v = f v u) :
    ∑ u, ∑ v, (if G.Adj u v then f u v else 0) =
      2 * ∑ u, ∑ v, (if u < v ∧ G.Adj u v then f u v else 0) := by
  have h1 : ∀ u v, (if G.Adj u v then f u v else 0) = (if u < v ∧ G.Adj u v then f u v else 0) +
      (if v < u ∧ G.Adj v u then f v u else 0) := by
    intro u v
    by_cases h : G.Adj u v
    · have h' : G.Adj v u := h.symm
      rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | huv
      · simp [h, h', huv, not_lt.2 huv.le]
      · simp [h, h', huv, not_lt.2 huv.le, hf u v]
    · have h' : ¬ G.Adj v u := fun h'' ↦ h (h''.symm)
      simp [h, h']
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v ↦ if v < u ∧ G.Adj v u then f v u else 0)]
  ring

theorem sum_comap_adj {n : ℕ} (z : Fin n ≃ Cube d) {H : SimpleGraph (Cube d)} (hH : H ≤ cube d)
    [DecidableRel H.Adj] [DecidableRel (H.comap z).Adj] (g : Cube d → Cube d → ℝ)
    (hg : ∀ x y, g x y = g y x) :
    ∑ u, ∑ v, (if (H.comap z).Adj u v then g (z u) (z v) else 0) =
      2 * ∑ j, ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x j = false),
        (if H.Adj x (flip x j) then g x (flip x j) else 0) := by
  have hR : ∑ u, ∑ v, (if (H.comap z).Adj u v then g (z u) (z v) else 0) =
      ∑ x, ∑ y, (if H.Adj x y then g x y else 0) := by
    rw [← Equiv.sum_comp z (fun x ↦ ∑ y, if H.Adj x y then g x y else 0)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← Equiv.sum_comp z (fun y ↦ if H.Adj (z u) y then g (z u) y else 0)]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases h : H.Adj (z u) (z v) <;> simp [h]
  rw [hR, sum_adj_eq_sum_flip hH, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ sum_eq_two_mul_sum_low j _ fun x ↦ ?_
  rw [flip_flip]
  by_cases h : H.Adj x (flip x j)
  · simp [h, h.symm, hg x]
  · have h' : ¬ H.Adj (flip x j) x := fun h'' ↦ h (h''.symm)
    simp [h, h']

/-- Each edge of the renamed graph, listed once as `u < v`, is an edge of `H` listed once at its
lower endpoint. -/
theorem sum_lt_comap {n : ℕ} (z : Fin n ≃ Cube d) {H : SimpleGraph (Cube d)} (hH : H ≤ cube d)
    [DecidableRel H.Adj] [DecidableRel (H.comap z).Adj] (g : Cube d → Cube d → ℝ)
    (hg : ∀ x y, g x y = g y x) :
    ∑ u, ∑ v, (if u < v ∧ (H.comap z).Adj u v then g (z u) (z v) else 0) =
      ∑ j, ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x j = false),
        (if H.Adj x (flip x j) then g x (flip x j) else 0) := by
  have h1 := sum_adj_eq_two_mul_sum_lt (H.comap z) (fun u v ↦ g (z u) (z v)) fun u v ↦ hg _ _
  have h2 := sum_comap_adj z hH g hg
  linarith

theorem dirCount_eq_sum (H : SimpleGraph (Cube d)) [DecidableRel H.Adj] (j : Fin d) :
    (dirCount H j : ℝ) = ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x j = false),
      (if H.Adj x (flip x j) then 1 else 0) := by
  simp only [dirCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h1 : x j = false <;> by_cases h2 : H.Adj x (flip x j) <;> simp [h1, h2]

theorem card_edgeFinset_comap {n : ℕ} (z : Fin n ≃ Cube d) {H : SimpleGraph (Cube d)}
    (hH : H ≤ cube d) {_ : Fintype (H.comap z).edgeSet} :
    ((H.comap z).edgeFinset.card : ℝ) = ∑ j, (dirCount H j : ℝ) := by
  classical
  have h2 : 2 * (H.comap z).edgeFinset.card =
      (Finset.univ.filter fun q : Fin n × Fin n ↦ (H.comap z).Adj q.1 q.2).card := by
    convert (H.comap z).two_mul_card_edgeFinset
  have h3 : ((Finset.univ.filter fun q : Fin n × Fin n ↦ (H.comap z).Adj q.1 q.2).card : ℝ) =
      ∑ u, ∑ v, (if (H.comap z).Adj u v then (fun _ _ ↦ (1 : ℝ)) (z u) (z v) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.univ_product_univ, Finset.sum_product]
    push_cast
    rfl
  have h4 := sum_comap_adj z hH (fun _ _ ↦ (1 : ℝ)) fun _ _ ↦ rfl
  simp only [← dirCount_eq_sum] at h4
  have h5 : (2 * (H.comap z).edgeFinset.card : ℝ) =
      ((Finset.univ.filter fun q : Fin n × Fin n ↦ (H.comap z).Adj q.1 q.2).card : ℝ) := by
    exact_mod_cast h2
  rw [h3] at h5
  simp only at h5
  rw [h4] at h5
  linarith

end Edges

/-! ### The cut constraint on the hypercube -/

section Cut

variable {d : ℕ}

theorem eval_energyP (w : Fin d → Cube d → ℝ) (y : Cube d → ℝ) :
    eval y (energyP w) = energy w y := by
  simp [energyP, energy, map_sum]

theorem graphW_eq (H : SimpleGraph (Cube d)) [DecidableRel H.Adj] (j : Fin d) (x : Cube d) :
    graphW H j x = if H.Adj x (flip x j) then 1 else 0 := by
  unfold graphW
  by_cases h : H.Adj x (flip x j) <;> simp [h]

/-- The cut constraint of the program, renamed to the hypercube's variables, is
`BMW26.cutPolyCube`. -/
theorem rename_cutPolyFin {n : ℕ} (z : Fin n ≃ Cube d) {H : SimpleGraph (Cube d)}
    (hH : H ≤ cube d) (δ : ℚ) :
    rename z (toReal (Alg.cutPolyFin (H.comap z) d δ)) = cutPolyCube H (δ : ℝ) := by
  classical
  refine MvPolynomial.funext fun y ↦ ?_
  rw [eval_rename]
  simp only [toReal, Alg.cutPolyFin, map_natCast, SimpleGraph.comap_adj, map_sub, map_mul, map_add,
    map_C, eq_ratCast, Rat.cast_ofNat, map_sum, apply_ite, map_pow, map_X, map_zero, eval_C, eval_X,
    Function.comp_apply, cutPolyCube, eval_energyP, energy]
  rw [card_edgeFinset_comap z hH]
  have key := sum_lt_comap z hH (fun a b ↦ (y a - y b) ^ 2) (fun a b ↦ by ring)
  simp only [SimpleGraph.comap_adj] at key
  have key2 : ∀ i, ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x i = false),
      graphW H i x * (y x - y (flip x i)) ^ 2 =
      ∑ x ∈ Finset.univ.filter (fun x : Cube d ↦ x i = false),
        (if H.Adj x (flip x i) then (y x - y (flip x i)) ^ 2 else 0) := by
    intro i
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [graphW_eq]
    split_ifs <;> simp
  simp only [key2]
  congr 2

theorem energy_graphW_cut (H : SimpleGraph (Cube d)) (i : Fin d) :
    energy (graphW H) (fun x ↦ sgn (x i)) = 4 * dirCount H i := by
  classical
  unfold energy
  rw [Finset.sum_eq_single i]
  · rw [dirCount_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only
    rw [graphW_eq, flip_apply_self, sgn_not]
    have := sgn_sq (x i)
    split_ifs <;> nlinarith
  · intro j _ hji
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp only
    rw [flip_apply_ne x (Ne.symm hji)]
    ring
  · simp

theorem eval_cutPolyCube_cut (H : SimpleGraph (Cube d)) (δ : ℝ) (i : Fin d) :
    eval (fun x ↦ sgn (x i)) (cutPolyCube H δ) =
      (2 + δ) * 2 * ∑ j, (dirCount H j : ℝ) - d * (4 * dirCount H i) := by
  simp [cutPolyCube, eval_energyP, energy_graphW_cut]

/-- A coordinate cut satisfies the cut constraint when the directions have about the same number
of edges. -/
theorem cut_nonneg {H : SimpleGraph (Cube d)} {p τ₀ δ : ℝ} (hp : 0 ≤ p) (hτ₀ : 0 ≤ τ₀)
    (hδ1 : δ ≤ 1) (h5 : 5 * τ₀ ≤ δ)
    (hcount : ∀ i, |(dirCount H i : ℝ) - p * 2 ^ d / 2| ≤ τ₀ * (p * 2 ^ d / 2)) (i : Fin d) :
    0 ≤ (2 + δ) * 2 * ∑ j, (dirCount H j : ℝ) - d * (4 * dirCount H i) := by
  set P : ℝ := p * 2 ^ d / 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have h1 : (d : ℝ) * ((1 - τ₀) * P) ≤ ∑ j, (dirCount H j : ℝ) := by
    have : ∑ _j : Fin d, (1 - τ₀) * P ≤ ∑ j, (dirCount H j : ℝ) :=
      Finset.sum_le_sum fun j _ ↦ by have := (abs_le.1 (hcount j)).1; linarith
    simpa using this
  have h2 : (dirCount H i : ℝ) ≤ (1 + τ₀) * P := by
    have := (abs_le.1 (hcount i)).2; linarith
  have h3 : 0 ≤ δ - δ * τ₀ - 4 * τ₀ := by nlinarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h4 : 0 ≤ 2 * d * P * (δ - δ * τ₀ - 4 * τ₀) := by positivity
  have h5' : 0 ≤ 2 + δ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 + δ) * 2),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * d)]

theorem sum_sgn_eq_zero (i : Fin d) : ∑ x : Cube d, sgn (x i) = 0 := by
  let σ : Cube d ≃ Cube d :=
    ⟨fun x ↦ flip x i, fun x ↦ flip x i, fun x ↦ flip_flip x i, fun x ↦ flip_flip x i⟩
  have h : ∑ x : Cube d, sgn (x i) = ∑ x : Cube d, -sgn (x i) :=
    Fintype.sum_equiv σ _ _ fun x ↦ by simp [σ, flip_apply_self, sgn_not]
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- **The coordinate cuts satisfy the program**, when the directions have about the same number
of edges and the slack is large enough. -/
theorem eval_cutPt_nonneg {n : ℕ} (z : Fin n ≃ Cube d) {H : SimpleGraph (Cube d)}
    (hH : H ≤ cube d) {p τ₀ : ℝ} (δ : ℚ) (hp : 0 ≤ p) (hτ₀ : 0 ≤ τ₀) (hδ1 : (δ : ℝ) ≤ 1)
    (h5 : 5 * τ₀ ≤ δ)
    (hcount : ∀ i, |(dirCount H i : ℝ) - p * 2 ^ d / 2| ≤ τ₀ * (p * 2 ^ d / 2)) :
    ∀ f ∈ (Alg.problemOf n d δ (Alg.edgeList n (adjTable ⟨n, H.comap z⟩))).system, ∀ i,
      0 ≤ eval (cutPt z i) (toReal f) := by
  intro f hf i
  rcases (Alg.mem_system_iff δ (H.comap z) f).1 hf with rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl | rfl
  · simp [toReal, cutPt, sgn_sq]
  · simp [toReal, cutPt, sgn_sq]
  · simp [toReal, cutPt, sgn_sq]
  · have := sum_sgn_eq_zero i
    rw [← Equiv.sum_comp z (fun x ↦ sgn (x i))] at this
    simp [toReal, cutPt, this]
  · have := sum_sgn_eq_zero i
    rw [← Equiv.sum_comp z (fun x ↦ sgn (x i))] at this
    simp [toReal, cutPt, this]
  · rw [show cutPt z i = (fun x ↦ sgn (x i)) ∘ z from rfl, ← eval_rename, rename_cutPolyFin z hH,
      eval_cutPolyCube_cut]
    exact cut_nonneg hp hτ₀ hδ1 h5 hcount i

end Cut

/-! ### The norms of the constraints -/

section Norms

theorem coeffNorm1_X_sq_le {σ : Type*} (v : σ) : coeffNorm1 (X v ^ 2 : MvPolynomial σ ℝ) ≤ 1 := by
  have := coeffNorm1_pow_le (X v : MvPolynomial σ ℝ) 2
  rw [coeffNorm1_X] at this
  simpa using this

theorem coeffNorm1_sum_X_sq_le (n : ℕ) :
    coeffNorm1 (∑ v : Fin n, X v ^ 2 : MvPolynomial (Fin n) ℝ) ≤ n := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ v : Fin n, coeffNorm1 (X v ^ 2 : MvPolynomial (Fin n) ℝ) ≤ ∑ _v : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun v _ ↦ coeffNorm1_X_sq_le v
    _ = n := by simp

theorem coeffNorm1_sum_X_le (n : ℕ) :
    coeffNorm1 (∑ v : Fin n, X v : MvPolynomial (Fin n) ℝ) ≤ n := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ v : Fin n, coeffNorm1 (X v : MvPolynomial (Fin n) ℝ) ≤ ∑ _v : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun v _ ↦ (coeffNorm1_X v).le
    _ = n := by simp

theorem card_edgeFinset_le_sq {n : ℕ} (G : SimpleGraph (Fin n)) {_ : Fintype G.edgeSet} :
    (G.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 := G.card_edgeFinset_le_card_choose_two
  have h2 : n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  rw [Fintype.card_fin] at h1
  exact_mod_cast h1.trans h2

theorem coeffNorm1_cut_le {n d : ℕ} (G : SimpleGraph (Fin n)) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    coeffNorm1 (toReal (Alg.cutPolyFin G d δ)) ≤ 6 * (n : ℝ) ^ 2 + 4 * d * (n : ℝ) ^ 2 := by
  classical
  have hsum : ∀ f : Fin n → Fin n → MvPolynomial (Fin n) ℝ, (∀ u v, coeffNorm1 (f u v) ≤ 4) →
      coeffNorm1 (∑ u, ∑ v, f u v) ≤ 4 * (n : ℝ) ^ 2 := by
    intro f hf
    refine (coeffNorm1_sum_le _ _).trans ?_
    calc ∑ u, coeffNorm1 (∑ v, f u v) ≤ ∑ _u : Fin n, ∑ _v : Fin n, (4 : ℝ) :=
          Finset.sum_le_sum fun u _ ↦ (coeffNorm1_sum_le _ _).trans
            (Finset.sum_le_sum fun v _ ↦ hf u v)
      _ = 4 * (n : ℝ) ^ 2 := by simp; ring
  have hsq : ∀ u v : Fin n, coeffNorm1 ((X u - X v) ^ 2 : MvPolynomial (Fin n) ℝ) ≤ 4 := by
    intro u v
    refine (coeffNorm1_pow_le _ 2).trans ?_
    have := coeffNorm1_sub_le (X u : MvPolynomial (Fin n) ℝ) (X v)
    rw [coeffNorm1_X, coeffNorm1_X] at this
    nlinarith [coeffNorm1_nonneg (X u - X v : MvPolynomial (Fin n) ℝ)]
  have hE : (G.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := card_edgeFinset_le_sq G
  unfold Alg.cutPolyFin
  simp only [toReal, map_sub]
  rw [MvPolynomial.map_C, map_mul (MvPolynomial.map (algebraMap ℚ ℝ)), MvPolynomial.map_C,
    map_sum]
  simp only [map_sum]
  refine (coeffNorm1_sub_le _ _).trans ?_
  rw [coeffNorm1_C, coeffNorm1_C_mul]
  have hδ0' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  refine le_trans (add_le_add (b := 6 * (n : ℝ) ^ 2) ?_
    (mul_le_mul_of_nonneg_left (c := 4 * (n : ℝ) ^ 2) (hsum _ fun u v ↦ ?_) (abs_nonneg _))) ?_
  · simp only [map_mul, map_add, map_ofNat, map_natCast, eq_ratCast]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · split_ifs
    · simpa using hsq u v
    · simp
  · simp only [map_natCast, Nat.abs_cast]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- Every constraint of the program has `1 + ‖f‖₂ ≤ 16 n³`. -/
theorem one_add_coeffNorm_le {n d : ℕ} (hn : 1 ≤ n) (hdn : d ≤ n) (G : SimpleGraph (Fin n))
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ f : MvPolynomial (Fin n) ℚ,
      f ∈ (Alg.problemOf n d δ (Alg.edgeList n (adjTable ⟨n, G⟩))).system →
        1 + coeffNorm (toReal f) ≤ 16 * (n : ℝ) ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
  intro f hf
  refine le_trans (add_le_add_right (coeffNorm_le_coeffNorm1 _) 1) ?_
  rcases (Alg.mem_system_iff δ G f).1 hf with rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl | rfl
  · have e : toReal (C (n : ℚ) - ∑ v, X v ^ 2 : MvPolynomial (Fin n) ℚ) =
        C (n : ℝ) - ∑ v, X v ^ 2 := by simp [toReal]
    rw [e]
    have h1 := coeffNorm1_sub_le (C (n : ℝ) : MvPolynomial (Fin n) ℝ) (∑ v, X v ^ 2)
    rw [coeffNorm1_C, abs_of_nonneg (Nat.cast_nonneg n)] at h1
    have h2 := coeffNorm1_sum_X_sq_le n
    nlinarith
  · have e : toReal (X v ^ 2 - 1 : MvPolynomial (Fin n) ℚ) = X v ^ 2 - 1 := by simp [toReal]
    rw [e]
    have h1 := coeffNorm1_sub_le (X v ^ 2 : MvPolynomial (Fin n) ℝ) 1
    rw [coeffNorm1_one] at h1
    have h2 := coeffNorm1_X_sq_le (σ := Fin n) v
    nlinarith
  · have e : toReal (1 - X v ^ 2 : MvPolynomial (Fin n) ℚ) = 1 - X v ^ 2 := by simp [toReal]
    rw [e]
    have h1 := coeffNorm1_sub_le (1 : MvPolynomial (Fin n) ℝ) (X v ^ 2)
    rw [coeffNorm1_one] at h1
    have h2 := coeffNorm1_X_sq_le (σ := Fin n) v
    nlinarith
  · have e : toReal (∑ v, X v : MvPolynomial (Fin n) ℚ) = ∑ v, X v := by simp [toReal]
    rw [e]
    have h2 := coeffNorm1_sum_X_le n
    nlinarith
  · have e : toReal (-∑ v, X v : MvPolynomial (Fin n) ℚ) = -∑ v, X v := by simp [toReal]
    rw [e, coeffNorm1_neg]
    have h2 := coeffNorm1_sum_X_le n
    nlinarith
  · have h2 := coeffNorm1_cut_le (d := d) G hδ0 hδ1
    nlinarith

theorem prod_one_add_le {τ : Type*} (A : System τ ℝ) {B : ℝ}
    (hA : ∀ f ∈ A, 1 + coeffNorm f ≤ B) :
    ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) ≤ B ^ A.length := by
  calc ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) ≤ ∏ _i : Fin A.length, B :=
        Finset.prod_le_prod₀ (fun i _ ↦ add_nonneg zero_le_one (coeffNorm_nonneg _))
          (fun i _ ↦ hA _ (List.get_mem A i))
    _ = B ^ A.length := by simp

end Norms

/-! ### Numerics -/

section Numeric

theorem sq_le_two_pow {d : ℕ} (hd : 4 ≤ d) : d ^ 2 ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem exp_ineq {c d : ℕ} (hd : c + 1100 ≤ d) :
    1 + 200 * (d + 4) + (3 * d + 4) * (2 * 2 ^ d + 4) + d * (c + 8) ≤ (2 ^ d) ^ 2 + 10 := by
  have h1 := sq_le_two_pow (d := d) (by omega)
  have h2 : 7 * d + 1000 ≤ 2 ^ d := by nlinarith
  have h3 : c + 220 ≤ 2 ^ d := by omega
  have h4 := Nat.mul_le_mul_left (2 ^ d) h2
  have h5 := Nat.mul_le_mul_left d h3
  nlinarith

theorem natCast_le_two_pow (d : ℕ) : (d : ℝ) ≤ 2 ^ d := by
  exact_mod_cast (Nat.lt_two_pow_self).le

theorem acc_le {c d : ℕ} (hd : c + 1100 ≤ d) :
    ((Alg.acc (2 ^ d) : ℚ) : ℝ) ≤ 1 / (d : ℝ) ^ (c + 8) := by
  have hM := exp_ineq hd
  have hacc : ((Alg.acc (2 ^ d) : ℚ) : ℝ) = 1 / 2 ^ ((2 ^ d) ^ 2 + 10) := by simp [Alg.acc]
  rw [hacc]
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  calc (1 : ℝ) / 2 ^ ((2 ^ d) ^ 2 + 10) ≤ 1 / 2 ^ (d * (c + 8)) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    _ = 1 / ((2 : ℝ) ^ d) ^ (c + 8) := by rw [← pow_mul]
    _ ≤ 1 / (d : ℝ) ^ (c + 8) :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ hd0.le (natCast_le_two_pow d) _)

theorem err_le {c d : ℕ} (hd : c + 1100 ≤ d) :
    2 * ((Alg.acc (2 ^ d) : ℚ) : ℝ) * (2 : ℝ) ^ (200 * (d + 4)) *
      (16 * ((2 ^ d : ℕ) : ℝ) ^ 3) ^ (2 * 2 ^ d + 4) ≤ 1 / (d : ℝ) ^ (c + 8) := by
  have hM := exp_ineq hd
  have hacc : ((Alg.acc (2 ^ d) : ℚ) : ℝ) = 1 / 2 ^ ((2 ^ d) ^ 2 + 10) := by simp [Alg.acc]
  have h16 : 16 * ((2 ^ d : ℕ) : ℝ) ^ 3 = 2 ^ (3 * d + 4) := by
    push_cast
    rw [← pow_mul, pow_add, mul_comm d 3]
    norm_num
    ring
  rw [hacc, h16, ← pow_mul (2 : ℝ) (3 * d + 4)]
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  set K := 1 + 200 * (d + 4) + (3 * d + 4) * (2 * 2 ^ d + 4) with hK
  have hK' : 2 * (2 : ℝ) ^ (200 * (d + 4)) * 2 ^ ((3 * d + 4) * (2 * 2 ^ d + 4)) = 2 ^ K := by
    rw [hK, pow_add, pow_add, pow_one]
  clear_value K
  rw [show ∀ x y w : ℝ, 2 * (1 / w) * x * y = 2 * x * y / w from fun x y w ↦ by ring, hK']
  calc (2 : ℝ) ^ K / 2 ^ ((2 ^ d) ^ 2 + 10) ≤ 2 ^ K / 2 ^ (K + d * (c + 8)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hM)
    _ = 1 / ((2 : ℝ) ^ d) ^ (c + 8) := by
        rw [pow_add (2 : ℝ) K, pow_mul]
        field_simp
    _ ≤ 1 / (d : ℝ) ^ (c + 8) :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ hd0.le (natCast_le_two_pow d) _)

/-- The final comparison of the Frobenius error with what the rounding needs. -/
theorem final_bound {c : ℕ} {D N p δ τ₀ ξ err a t : ℝ} (hD : 1100 ≤ D) (hN : 1 ≤ N)
    (ht0 : 0 ≤ t) (htD : t * D ^ (c + 8) = 1) (hδ : δ = D * t) (hτ : τ₀ ≤ t) (hξ : ξ ≤ t)
    (herr : err ≤ t) (ha : a ≤ t) (hp : 1 / D ≤ p) :
    2 * N * (4 * (δ + 5 * τ₀ + 3 * ξ) + err) / D + a ≤ p * N / (64 * D ^ (c + 5)) := by
  have hD0 : 0 < D := by linarith
  have h1 : 2 * N * (4 * (δ + 5 * τ₀ + 3 * ξ) + err) / D ≤ 10 * N * t := by
    rw [div_le_iff₀ hD0]
    have : 4 * (δ + 5 * τ₀ + 3 * ξ) + err ≤ 5 * D * t := by rw [hδ]; nlinarith
    nlinarith
  have h2 : a ≤ N * t := by nlinarith
  have h3 : N * D ^ 2 * t / 64 ≤ p * N / (64 * D ^ (c + 5)) := by
    have e : N * D ^ 2 * t / 64 = (1 / D) * N / (64 * D ^ (c + 5)) := by
      field_simp
      rw [← htD]
      ring
    rw [e]
    gcongr
  have h4 : 11 * (N * t) ≤ N * D ^ 2 * t / 64 := by
    have hNt : 0 ≤ N * t := by positivity
    have hD2 : 704 ≤ D ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hD2 hNt]
  linarith

end Numeric

/-! ### The level-one mass of the solver's pseudo-expectation -/

section Level

variable {n d : ℕ}

theorem rename_aP (z : Fin n ≃ Cube d) (i : Fin d) :
    rename z.symm (aP {i}) = C (1 / 2 ^ d) * ∑ v, C (sgn (z v i)) * X v := by
  simp only [aP, fcP, map_mul, rename_C, map_sum, rename_X, chi_singleton]
  congr 1
  exact (Equiv.sum_comp z (fun x ↦ C (sgn (x i)) * X (z.symm x))).symm.trans (by simp)

theorem peRename_aP_sq {ℓ : ℕ} (z : Fin n ≃ Cube d) (E : PseudoExpectation (Fin n) ℓ)
    (i : Fin d) :
    peRename z E (aP {i} ^ 2) = (1 / 2 ^ d) ^ 2 * E ((∑ v, C (sgn (z v i)) * X v) ^ 2) := by
  rw [peRename_apply, map_pow, rename_aP, mul_pow, ← C_pow, E.map_C_mul]

theorem mem_renamed (z : Fin n ≃ Cube d) {sys : System (Fin n) ℚ} {b : MvPolynomial (Fin n) ℚ}
    (hb : b ∈ sys) {f : MvPolynomial (Cube d) ℝ} (hf : rename z (toReal b) = f) :
    f ∈ (sys.map toReal).map (rename z) :=
  List.mem_map.2 ⟨toReal b, List.mem_map.2 ⟨b, hb, rfl⟩, hf⟩

theorem slack_cast (c d : ℕ) : ((Alg.slack c d : ℚ) : ℝ) = 1 / (d : ℝ) ^ (c + 7) := by
  simp [Alg.slack]

/-- **The level-one mass** of a pseudo-expectation that satisfies the program approximately:
`∑ᵢ Ẽ[(∑ᵥ χ̂ᵢ(v) f_v)²] ≥ (1 - 4 (δ + 5τ₀ + 3ξ) - d^-(c+8)) n²`. -/
theorem mass_bound (c : ℕ) (hdc : c + 1100 ≤ d) {H : SimpleGraph (Cube d)} {p ξ τ₀ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hτ : 0 ≤ τ₀) (hτ1 : τ₀ ≤ 1 / 4)
    (good : Good H p (1 / 100) ξ τ₀) (z : Fin (2 ^ d) ≃ Cube d)
    (E : PseudoExpectation (Fin (2 ^ d)) 4)
    (hE : E.ApproxSatisfies (Alg.problemOf (2 ^ d) d (Alg.slack c d)
      (Alg.edgeList (2 ^ d) (adjTable ⟨2 ^ d, H.comap z⟩))).system (2 * (Alg.acc (2 ^ d) : ℝ)) 0) :
    (1 - (4 * ((Alg.slack c d : ℝ) + 5 * τ₀ + 3 * ξ) + 1 / (d : ℝ) ^ (c + 8))) *
        ((2 ^ d : ℕ) : ℝ) ^ 2 ≤ ∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2) := by
  set sys : System (Fin (2 ^ d)) ℚ := (Alg.problemOf (2 ^ d) d (Alg.slack c d)
    (Alg.edgeList (2 ^ d) (adjTable ⟨2 ^ d, H.comap z⟩))).system with hsys
  have hd1 : 1 ≤ d := by omega
  have hD1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ0 : 0 ≤ Alg.slack c d := by unfold Alg.slack; positivity
  have hδ1 : Alg.slack c d ≤ 1 := by
    unfold Alg.slack
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by exact_mod_cast hd1)
  have hδ0' : (0 : ℝ) ≤ (Alg.slack c d : ℝ) := by exact_mod_cast hδ0
  have hδ1' : ((Alg.slack c d : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hδ1
  -- The renamed system and its constraints.
  set A' : System (Cube d) ℝ := (sys.map toReal).map (rename z) with hA'
  have hE' : (peRename z E).ApproxSatisfies A' (2 * (Alg.acc (2 ^ d) : ℝ)) 0 :=
    approxSatisfies_rename z hE.map_toReal
  have hmem := fun f ↦ (Alg.mem_system_iff (d := d) (Alg.slack c d) (H.comap z) f).2
  have hbool : ∀ x, X x ^ 2 - 1 ∈ A' ∧ 1 - X x ^ 2 ∈ A' := fun x ↦
    ⟨mem_renamed z (hmem _ (Or.inr (Or.inl ⟨z.symm x, rfl⟩))) (by simp [toReal]),
      mem_renamed z (hmem _ (Or.inr (Or.inr (Or.inl ⟨z.symm x, rfl⟩)))) (by simp [toReal])⟩
  have hsumX : rename z (toReal (∑ v : Fin (2 ^ d), X v : MvPolynomial (Fin (2 ^ d)) ℚ)) =
      ∑ x, X x := by
    simp only [toReal, map_sum, MvPolynomial.map_X, rename_X]
    exact Equiv.sum_comp z (fun x ↦ (X x : MvPolynomial (Cube d) ℝ))
  have hbal : ∑ x, X x ∈ A' ∧ -∑ x, X x ∈ A' :=
    ⟨mem_renamed z (hmem _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hsumX,
      mem_renamed z (hmem _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (by
          rw [show toReal (-∑ v, X v : MvPolynomial (Fin (2 ^ d)) ℚ) =
            -toReal (∑ v, X v : MvPolynomial (Fin (2 ^ d)) ℚ) from map_neg _ _, map_neg, hsumX])⟩
  have hcut : cutPolyCube H (Alg.slack c d : ℝ) ∈ A' :=
    mem_renamed z (hmem _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      (rename_cutPolyFin z good.le_cube _)
  -- The certificate and approximate soundness.
  have hlev := level_one_mass (m := d) (by omega) hp0 hp1 (by norm_num) le_rfl hξ hξ1 hτ hτ1 hδ0'
    hδ1' good A' hbool hbal hcut
  have hacc0 : (0 : ℝ) ≤ (Alg.acc (2 ^ d) : ℝ) := by
    have : (0 : ℚ) ≤ Alg.acc (2 ^ d) := by unfold Alg.acc; positivity
    exact_mod_cast this
  have happ := hlev.approx_ge (mul_nonneg zero_le_two hacc0) hE' le_rfl
  -- The norms of the constraints.
  have hprod : ∏ i : Fin A'.length, (1 + coeffNorm (A'.get i)) ≤
      (16 * ((2 ^ d : ℕ) : ℝ) ^ 3) ^ (2 * 2 ^ d + 4) := by
    have hlen : A'.length = 2 * 2 ^ d + 4 := by
      simp only [hA', List.length_map]
      exact Alg.length_system _ _
    rw [← hlen]
    refine prod_one_add_le A' fun f hf ↦ ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hf
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [coeffNorm_rename]
    exact one_add_coeffNorm_le (Nat.one_le_two_pow) (Nat.lt_two_pow_self).le _ hδ0 hδ1 b hb
  have herr := err_le hdc
  have hbig : 2 * (Alg.acc (2 ^ d) : ℝ) * (2 : ℝ) ^ (200 * (d + 4)) *
      ∏ i : Fin A'.length, (1 + coeffNorm (A'.get i)) ≤ 1 / (d : ℝ) ^ (c + 8) :=
    le_trans (mul_le_mul_of_nonneg_left hprod (by positivity)) herr
  -- The pseudo-expectation of the certificate's conclusion.
  have hval : peRename z E (∑ i, aP {i} ^ 2 - C (1 - 4 * ((Alg.slack c d : ℝ) + 5 * τ₀ + 3 * ξ))) =
      (1 / 2 ^ d) ^ 2 * ∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2) -
        (1 - 4 * ((Alg.slack c d : ℝ) + 5 * τ₀ + 3 * ξ)) := by
    rw [PseudoExpectation.map_sub, PseudoExpectation.map_sum, PseudoExpectation.map_C,
      Finset.mul_sum]
    simp only [peRename_aP_sq]
  rw [hval] at happ
  generalize 2 * (Alg.acc (2 ^ d) : ℝ) * (2 : ℝ) ^ (200 * (d + 4)) *
    ∏ i : Fin A'.length, (1 + coeffNorm (A'.get i)) = Err at happ hbig
  have hN : ((2 ^ d : ℕ) : ℝ) ^ 2 * (1 / 2 ^ d) ^ 2 = 1 := by
    push_cast
    field_simp
  have hN0 : (0 : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ 2 := by positivity
  set S := ∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2)
  set ε₀ := 4 * ((Alg.slack c d : ℝ) + 5 * τ₀ + 3 * ξ)
  have h1 : 1 - ε₀ - 1 / (d : ℝ) ^ (c + 8) ≤ (1 / 2 ^ d) ^ 2 * S := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hN0
  rw [← mul_assoc, hN, one_mul] at h2
  linarith

/-- The chain of `BMW26.success_of_good` for one sample, given the rounding's guarantee. -/
theorem success_aux (c : ℕ) {d : ℕ} (hdc : c + 1100 ≤ d) {H : SimpleGraph (Cube d)}
    {p ξ τ₀ : ℝ} (hp : 1 / (d : ℝ) ≤ p) (hp1 : p ≤ 1) (hξ : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / (d : ℝ) ^ (c + 8)) (hτ : 0 ≤ τ₀) (hτ1 : τ₀ ≤ 1 / (d : ℝ) ^ (c + 8))
    (good : Good H p (1 / 100) ξ τ₀) (z : Renaming d) (r : List Bool)
    (hround : ∀ Mt : List (List ℚ),
      ∑ u : Fin (2 ^ d), ∑ v : Fin (2 ^ d), ((Round.entry Mt u v : ℝ) - targetM z u v) ^ 2 ≤
          p * 4 ^ d / (64 * (d : ℝ) ^ (c + 5)) →
        Recovers z (2 ^ d / (d : ℝ) ^ c)
          (Round.roundOut (2 ^ d) d c Mt (Alg.edgeList (2 ^ d) (adjTable (observed H z))))) :
    Recovers z (2 ^ d / (d : ℝ) ^ c) (Alg.alg c (observed H z, r)) := by
  have hd0 : 0 < d := by omega
  have hD : (1100 : ℝ) ≤ d := by exact_mod_cast (by omega : 1100 ≤ d)
  have hDpos : (0 : ℝ) < d := by linarith
  set t : ℝ := 1 / (d : ℝ) ^ (c + 8) with ht
  have ht0 : 0 ≤ t := by positivity
  have htD : t * (d : ℝ) ^ (c + 8) = 1 := by rw [ht]; field_simp
  have hδR := slack_cast c d
  have hδt : ((Alg.slack c d : ℚ) : ℝ) = d * t := by
    rw [hδR, ht]
    field_simp
    ring
  have hδ1' : ((Alg.slack c d : ℚ) : ℝ) ≤ 1 := by
    rw [hδR]
    exact div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)
  have h5 : 5 * τ₀ ≤ (Alg.slack c d : ℝ) := by rw [hδt]; nlinarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hτ14 : τ₀ ≤ 1 / 4 := by
    have : t ≤ 1 / 4 := by
      rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (d : ℝ) ≤ (d : ℝ) ^ (c + 8) := le_self_pow₀ (by linarith) (by omega)
      linarith
    linarith
  -- (1) The program is valid: the coordinate cuts satisfy it.
  have hfeas := eval_cutPt_nonneg z good.le_cube (Alg.slack c d) hp0.le hτ hδ1' h5 good.count
  have hdim : Alg.dimOf (2 ^ d) = d := Nat.log_pow (by norm_num) d
  have hvalid : (Alg.problemOf (2 ^ d) (Alg.dimOf (2 ^ d)) (Alg.slack c (Alg.dimOf (2 ^ d)))
      (Alg.edgeList (2 ^ d) (adjTable ⟨2 ^ d, H.comap z⟩))).Valid := by
    rw [hdim]
    exact Alg.valid_of_feasible _ _ (cutPt z ⟨0, hd0⟩) fun f hf ↦ hfeas f hf _
  -- (2) The solver's output.
  obtain ⟨E, Mt, hE, hopt, hMt, halg⟩ := Alg.alg_spec c (H.comap z) r hvalid
  rw [hdim] at hE hopt halg
  -- (5) The mixture of the coordinate cuts bounds the objective.
  have hacc0 : (0 : ℝ) ≤ (Alg.acc (2 ^ d) : ℝ) := by
    have : (0 : ℚ) ≤ Alg.acc (2 ^ d) := by unfold Alg.acc; positivity
    exact_mod_cast this
  have hcomp := cutMixture_approxSatisfies hd0 z 4 _ hfeas hacc0
  have hobj : ∑ u, ∑ v, E (X u * X v) ^ 2 ≤
      ((2 ^ d : ℕ) : ℝ) ^ 2 / d + (Alg.acc (2 ^ d) : ℝ) := by
    have := hopt _ hcomp
    rwa [cutMixture_objective] at this
  -- (3), (4) The level-one mass.
  have hξ1' : ξ ≤ 1 := hξ1.trans ((div_le_one (by positivity)).2
    (one_le_pow₀ (by exact_mod_cast (show 1 ≤ d by omega))))
  have hmass := mass_bound c hdc hp0 hp1 hξ hξ1' hτ hτ14 good z E hE
  -- (6) The second moments are close to those of the mixture, and the rounding recovers.
  have hfrob := frobenius_bound hd0 z E hmass hobj
  change Recovers z _ (Alg.alg c (⟨2 ^ d, H.comap z⟩, r))
  rw [halg]
  refine hround Mt ?_
  simp only [hMt]
  refine hfrob.trans ?_
  have hN : ((2 ^ d : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ d := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hN]
  exact final_bound hD (one_le_pow₀ (by norm_num)) ht0 htD hδt hτ1 hξ1 le_rfl (acc_le hdc) hp

end Level






/-! ### Good samples are likely -/

section Whp

theorem real_inter_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hmeas : ∀ s : Set Ω, MeasurableSet s) (s t : Set Ω) :
    μ.real s + μ.real t - 1 ≤ μ.real (s ∩ t) := by
  have h1 := measureReal_union_add_inter (μ := μ) (s := s) (hmeas t)
  have h2 : μ.real (s ∪ t) ≤ 1 := measureReal_le_one
  linarith

theorem real_iInter_ge {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hmeas : ∀ s : Set Ω, MeasurableSet s) (s : ι → Set Ω) :
    1 - ∑ i, (1 - μ.real (s i)) ≤ μ.real (⋂ i, s i) := by
  have h1 : μ.real (⋂ i, s i)ᶜ ≤ ∑ i, μ.real (s i)ᶜ := by
    rw [Set.compl_iInter]
    exact measureReal_iUnion_fintype_le _
  rw [probReal_compl_eq_one_sub (hmeas _)] at h1
  simp only [probReal_compl_eq_one_sub (hmeas _)] at h1
  linarith

theorem energy_congr {m : ℕ} {w w' : Fin m → Cube m → ℝ}
    (h : ∀ i x, x i = false → w i x = w' i x) (g : Cube m → ℝ) : energy w g = energy w' g := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x hx ↦ ?_
  rw [h i x (Finset.mem_filter.1 hx).2]

theorem sum_half {d : ℕ} (i : Fin (d + 1)) (D₀ D₁ : Cube d → ℝ) :
    ∑ x : Cube (d + 1), (if x i then D₁ (Fin.removeNth i x) else D₀ (Fin.removeNth i x)) =
      ∑ y, D₀ y + ∑ y, D₁ y := by
  rw [← (Fin.insertNthEquiv (fun _ ↦ Bool) i).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  ring

/-- `d^k 2^(-d/3) ≤ 1/2` for large `d`. -/
theorem eventually_pow_mul_le (k : ℕ) :
    ∀ᶠ d : ℕ in atTop, (d : ℝ) ^ k * (2 : ℝ) ^ (-(d : ℝ) / 3) ≤ 1 / 2 := by
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 3) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := r)
    (by rw [abs_of_pos hr0]; exact hr1)
  filter_upwards [ht (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with d hd
  have e : (2 : ℝ) ^ (-(d : ℝ) / 3) = r ^ d := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [e]
  exact hd

theorem half_pow_le {c d : ℕ} (hd1 : 1 ≤ d) (hdc : 2 ^ (c + 8) ≤ d) :
    ((d + 1 : ℕ) : ℝ) ^ (c + 8) ≤ (d : ℝ) ^ (c + 9) := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have h1 : ((d + 1 : ℕ) : ℝ) ≤ 2 * d := by push_cast; linarith
  have h2 : (2 : ℝ) ^ (c + 8) ≤ d := by exact_mod_cast hdc
  calc ((d + 1 : ℕ) : ℝ) ^ (c + 8) ≤ (2 * d) ^ (c + 8) := pow_le_pow_left₀ (by positivity) h1 _
    _ = 2 ^ (c + 8) * (d : ℝ) ^ (c + 8) := mul_pow _ _ _
    _ ≤ d * (d : ℝ) ^ (c + 8) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (d : ℝ) ^ (c + 9) := by ring

theorem prob_arith {D r : ℝ} (hD : 20 ≤ D) (h : 2 * (D + 1) ^ 2 * r ≤ 1 / (D + 1)) :
    1 - 4 / (D + 1) ≤
      (1 - 1 / (D + 1) ^ 2) + (1 - 2 * (D + 1) * (1 / D ^ 2)) + (1 - 2 * (D + 1) ^ 2 * r) - 2 := by
  have h1 : 1 / (D + 1) ^ 2 ≤ (1 / 10) / (D + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 2 * (D + 1) * (1 / D ^ 2) ≤ (29 / 10) / (D + 1) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 : (1 / 10) / (D + 1) + (29 / 10) / (D + 1) + 1 / (D + 1) = 4 / (D + 1) := by ring
  linarith

/-- **Good samples are likely**, for the dimension `d + 1`, given the spectral concentration. -/
theorem good_aux (c : ℕ) {C₁ : ℝ} {m₀ : ℕ}
    (hspec : ∀ m ≥ m₀, ∀ p : ℝ, C₁ * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 2 ≤ μ.real {ω | ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧
          ∑ x, D x ≤ p * 2 ^ m / (m : ℝ) ^ (c + 9) ∧ SpecClose (coinW a ω) 1 p (1 / 100) D})
    {d : ℕ} (hdm : m₀ ≤ d) (hd20 : 20 ≤ d) (hdc : 2 ^ (c + 8) ≤ d)
    (hexp : ((d + 1 : ℕ) : ℝ) ^ (c + 8) * (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ) / 3) ≤ 1 / 2)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hpd : 1 / ((d + 1 : ℕ) : ℝ) ≤ p)
    (hC₀ : C₁ * Real.log ((d + 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ) ≤ p)
    (hC₁ : C₁ * Real.log (d : ℝ) / (d : ℝ) ≤ p) :
    1 - 4 / ((d + 1 : ℕ) : ℝ) ≤ (coinMeasure (d + 1) p hp0 hp1).real
      {ω | Good (coinGraph ω) p (1 / 100) (1 / ((d + 1 : ℕ) : ℝ) ^ (c + 8))
        (1 / ((d + 1 : ℕ) : ℝ) ^ (c + 8))} := by
  set μ := coinMeasure (d + 1) p hp0 hp1 with hμ
  have hcoins := isCoins_coinMeasure (d + 1) hp0 hp1
  have := hcoins.isProb
  have hmeas : ∀ s : Set (CoinSpace (d + 1)), MeasurableSet s :=
    fun s ↦ hcoins.measurableSet_preimage s
  set D1 : ℝ := ((d + 1 : ℕ) : ℝ) with hD1
  set ξ : ℝ := 1 / D1 ^ (c + 8) with hξ
  set r : ℝ := (2 : ℝ) ^ (-D1 / 3) with hr
  have hD : (20 : ℝ) ≤ d := by exact_mod_cast hd20
  have hD1e : D1 = d + 1 := by rw [hD1]; push_cast; ring
  have hD1pos : 0 < D1 := by rw [hD1e]; linarith
  have hr0 : 0 ≤ r := by positivity
  -- The events.
  let F : Set (CoinSpace (d + 1)) := {ω | ∃ D : Cube (d + 1) → ℝ, (∀ x, 0 ≤ D x) ∧
    ∑ x, D x ≤ p * 2 ^ (d + 1) / D1 ^ (c + 9) ∧
      SpecClose (coinW (fun e ω ↦ ω e) ω) 1 p (1 / 100) D}
  let Fh : Fin (d + 1) × Bool → Set (CoinSpace (d + 1)) := fun j ↦ {ω | ∃ D : Cube d → ℝ,
    (∀ x, 0 ≤ D x) ∧ ∑ x, D x ≤ p * 2 ^ d / (d : ℝ) ^ (c + 9) ∧
      SpecClose (coinW (halfCoins j.1 j.2 fun e ω ↦ ω e) ω) 1 p (1 / 100) D}
  let Cnt : Set (CoinSpace (d + 1)) := {ω | ∀ i, |(dirCount (coinGraph ω) i : ℝ) -
    p * 2 ^ (d + 1) / 2| ≤ r * (p * 2 ^ (d + 1) / 2)}
  have hF : 1 - 1 / D1 ^ 2 ≤ μ.real F := hspec (d + 1) (by omega) p hC₀ hp1 μ _ hcoins
  have hFh : ∀ j, 1 - 1 / (d : ℝ) ^ 2 ≤ μ.real (Fh j) := fun j ↦
    hspec d hdm p hC₁ hp1 μ _ (isCoins_halfCoins hcoins j.1 j.2)
  have hCnt : 1 - 2 * D1 ^ 2 * r ≤ μ.real Cnt := count_whp (d + 1) hpd hp1
  -- The numerics.
  have hD1c : D1 ^ (c + 8) ≤ (d : ℝ) ^ (c + 9) := half_pow_le (by omega) hdc
  have hrξ : r ≤ ξ := by
    rw [hξ, le_div_iff₀ (by positivity)]
    linarith
  have hr3 : 2 * D1 ^ 2 * r ≤ 1 / D1 := by
    rw [le_div_iff₀ hD1pos]
    have : D1 ^ 3 ≤ D1 ^ (c + 8) := pow_le_pow_right₀ (by rw [hD1e]; linarith) (by omega)
    nlinarith
  have hP0 : 0 ≤ p * 2 ^ (d + 1) / 2 := by positivity
  -- Every sample in all the events is good.
  have hsub : F ∩ (⋂ j, Fh j) ∩ Cnt ⊆ {ω | Good (coinGraph ω) p (1 / 100) ξ ξ} := by
    rintro ω ⟨⟨⟨D, hD0, hDs, hDsc⟩, hH⟩, hC⟩
    rw [Set.mem_iInter] at hH
    refine ⟨coinGraph_le ω, ⟨D, hD0, ?_, fun g ↦ ?_⟩, fun i ↦ ?_, fun i ↦ ?_⟩
    · refine hDs.trans ?_
      rw [hξ, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by rw [hD1e]; linarith) (by omega))
    · rw [energy_congr (fun i x hx ↦ graphW_coinGraph ω i hx)]
      exact hDsc g
    · obtain ⟨D₀, h00, h0s, h0c⟩ := hH (i, false)
      obtain ⟨D₁, h10, h1s, h1c⟩ := hH (i, true)
      refine ⟨_, fun x ↦ ?_, ?_, specClose_halfW ω i h0c h1c⟩
      · split_ifs
        · exact h10 _
        · exact h00 _
      · rw [sum_half]
        have e : ξ * p * 2 ^ (d + 1) = 2 * (p * 2 ^ d / D1 ^ (c + 8)) := by
          rw [hξ]; ring
        rw [e]
        have : p * 2 ^ d / (d : ℝ) ^ (c + 9) ≤ p * 2 ^ d / D1 ^ (c + 8) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hD1c
        linarith
    · exact (hC i).trans (mul_le_mul_of_nonneg_right hrξ hP0)
  -- The union bound.
  have hall := real_iInter_ge μ hmeas Fh
  have hsumFh : ∑ j, (1 - μ.real (Fh j)) ≤ 2 * D1 * (1 / (d : ℝ) ^ 2) := by
    calc ∑ j, (1 - μ.real (Fh j)) ≤ ∑ _j : Fin (d + 1) × Bool, 1 / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ by linarith [hFh j]
      _ = 2 * D1 * (1 / (d : ℝ) ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul, hD1]
          push_cast
          ring
  have h1 := real_inter_ge μ hmeas F (⋂ j, Fh j)
  have h2 := real_inter_ge μ hmeas (F ∩ ⋂ j, Fh j) Cnt
  have h3 := measureReal_mono (μ := μ) hsub
  have h4 := prob_arith hD (r := r) (by rw [← hD1e]; exact hr3)
  rw [← hD1e] at h4
  linarith

theorem coinProb_eq_one {m : ℕ} {P : List Bool → Prop} (h : ∀ r, P r) : coinProb m P = 1 := by
  classical
  unfold coinProb
  rw [Finset.filter_true_of_mem (fun r _ ↦ h _), Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  push_cast
  exact div_self (by positivity)

theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb
  positivity

theorem percolationProb_nonneg {d : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (H : SimpleGraph (Cube d)) : 0 ≤ percolationProb p H := by
  unfold percolationProb
  split_ifs
  · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.2 hp1) _)
  · exact le_rfl

end Whp

end Asm


/-- **Success on good samples**, for every renaming and every coin string. -/
theorem success_of_good (c : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (H : SimpleGraph (Cube d)) (p ξ τ₀ : ℝ), 1 / (d : ℝ) ≤ p → p ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 / (d : ℝ) ^ (c + 8) → 0 ≤ τ₀ → τ₀ ≤ 1 / (d : ℝ) ^ (c + 8) →
      Good H p (1 / 100) ξ τ₀ → ∀ (z : Renaming d) (r : List Bool),
        Recovers z (2 ^ d / (d : ℝ) ^ c) (Alg.alg c (observed H z, r)) := by
  obtain ⟨d₁, hd₁⟩ := roundOut_recovers c
  refine ⟨max d₁ (c + 1100), fun d hd H p ξ τ₀ hp hp1 hξ hξ1 hτ hτ1 good z r ↦ ?_⟩
  have hdc : c + 1100 ≤ d := le_of_max_le_right hd
  have hτ14 : τ₀ ≤ 1 / 4 := by
    have hD : (1100 : ℝ) ≤ d := by exact_mod_cast (by omega : 1100 ≤ d)
    have : (d : ℝ) ≤ (d : ℝ) ^ (c + 8) := le_self_pow₀ (by linarith) (by omega)
    have : 1 / (d : ℝ) ^ (c + 8) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  exact Asm.success_aux c hdc hp hp1 hξ hξ1 hτ hτ1 good z r
    (hd₁ d (le_of_max_le_left hd) z H good.le_cube p τ₀ hp hp1 hτ hτ14 good.count)

/-- **Good samples are likely.** -/
theorem good_whp (c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ p : ℝ, ∀ _hCp : C * Real.log d / d ≤ p, ∀ hp1 : p ≤ 1,
      ∃ hp0 : 0 ≤ p, 1 - 4 / (d : ℝ) ≤ (coinMeasure d p hp0 hp1).real
        {ω | Good (coinGraph ω) p (1 / 100) (1 / (d : ℝ) ^ (c + 8)) (1 / (d : ℝ) ^ (c + 8))} := by
  obtain ⟨C₁, hC₁, m₀, hm₀⟩ := spectral_whp (ε := 1 / 100) (by norm_num) (by norm_num) (c + 9)
  obtain ⟨d₂, hd₂⟩ := Filter.eventually_atTop.1 (Asm.eventually_pow_mul_le (c + 8))
  refine ⟨2 * C₁ + 1, by positivity, max (max (m₀ + 1) (2 ^ (c + 8) + 1)) (max 21 d₂),
    fun d hd p hCp hp1 ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hd
  obtain ⟨⟨hdm, hdc⟩, hd21, hdd₂⟩ := hd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hD1 : (21 : ℝ) ≤ ((d' + 1 : ℕ) : ℝ) := by exact_mod_cast hd21
  have hD1pos : (0 : ℝ) < ((d' + 1 : ℕ) : ℝ) := by linarith
  have hD : (1 : ℝ) ≤ d' := by
    have : 1 ≤ d' := by omega
    exact_mod_cast this
  have hD1e : ((d' + 1 : ℕ) : ℝ) = d' + 1 := by push_cast; ring
  have hlog : 1 ≤ Real.log ((d' + 1 : ℕ) : ℝ) := by
    have h4 : 1 - (4 : ℝ)⁻¹ ≤ Real.log 4 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h16 : Real.log 16 = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have : Real.log 16 ≤ Real.log ((d' + 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h4
    linarith
  have hlog' : Real.log (d' : ℝ) ≤ Real.log ((d' + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by rw [hD1e]; linarith)
  have hlog0 : 0 ≤ Real.log (d' : ℝ) := Real.log_nonneg hD
  have hpd : 1 / ((d' + 1 : ℕ) : ℝ) ≤ p := by
    refine le_trans ?_ hCp
    exact div_le_div_of_nonneg_right (by nlinarith) hD1pos.le
  have hp0 : 0 ≤ p := le_trans (by positivity) hpd
  refine ⟨hp0, ?_⟩
  have hC₀ : C₁ * Real.log ((d' + 1 : ℕ) : ℝ) / ((d' + 1 : ℕ) : ℝ) ≤ p :=
    le_trans (div_le_div_of_nonneg_right (by nlinarith) hD1pos.le) hCp
  have hC₁' : C₁ * Real.log (d' : ℝ) / (d' : ℝ) ≤ p := by
    refine le_trans ?_ hCp
    rw [div_le_div_iff₀ (by linarith) hD1pos]
    have h1 : C₁ * Real.log (d' : ℝ) ≤ C₁ * Real.log ((d' + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlog' hC₁.le
    have h2 : 0 ≤ C₁ * Real.log ((d' + 1 : ℕ) : ℝ) := by positivity
    have h3 : ((d' + 1 : ℕ) : ℝ) ≤ 2 * d' := by rw [hD1e]; linarith
    have h4 : 0 ≤ Real.log ((d' + 1 : ℕ) : ℝ) * d' := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hD1pos.le, mul_le_mul_of_nonneg_left h3 h2]
  exact Asm.good_aux c hm₀ (by omega) (by omega) (by omega) (hd₂ _ hdd₂) hp0 hp1 hpd hC₀ hC₁'

/-- **[BMW26, Theorem 1.2]**, the statement of `Challenge.lean`. -/
theorem hypercube_recovery_of_parts :
    ∀ c : ℕ, ∃ (A : Graph × List Bool → Output) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ d : ℕ in atTop, ∀ p : ℝ, C * Real.log d / d ≤ p → p ≤ 1 →
          ∀ ren : SimpleGraph (Cube d) → Renaming d,
            1 - δ d ≤ successProb d p ren A (fun N ↦ (N + 2) ^ k) (2 ^ d / (d : ℝ) ^ c) := by
  intro c
  obtain ⟨k, hk⟩ := Alg.alg_runsInTime c
  obtain ⟨C, hC, d₁, hd₁⟩ := good_whp c
  obtain ⟨d₂, hd₂⟩ := success_of_good c
  refine ⟨Alg.alg c, k, hk, C, hC, fun d ↦ 4 / d, tendsto_const_div_atTop_nhds_zero_nat 4, ?_⟩
  have hlog : ∀ᶠ d : ℕ in atTop, 1 / C ≤ Real.log d :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / C)
  filter_upwards [eventually_ge_atTop (max (max d₁ d₂) 1), hlog] with d hd hlogd p hCp hp1 ren
  simp only [max_le_iff] at hd
  obtain ⟨⟨hdd₁, hdd₂⟩, hd1⟩ := hd
  have hD : (0 : ℝ) < d := by exact_mod_cast hd1
  have hpd : 1 / (d : ℝ) ≤ p := by
    refine le_trans (div_le_div_of_nonneg_right ?_ hD.le) hCp
    rw [div_le_iff₀ hC] at hlogd
    linarith
  obtain ⟨hp0, hgood⟩ := hd₁ d hdd₁ p hCp hp1
  set ξ : ℝ := 1 / (d : ℝ) ^ (c + 8) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  rw [show (coinMeasure d p hp0 hp1).real {ω | Good (coinGraph ω) p (1 / 100) ξ ξ} =
      (coinMeasure d p hp0 hp1).real {ω | coinGraph ω ∈ {H | Good H p (1 / 100) ξ ξ}} from rfl,
    ← sum_percolationProb_eq d hp0 hp1] at hgood
  refine hgood.trans (Finset.sum_le_sum fun H _ ↦ ?_)
  split_ifs with hH
  · rw [Asm.coinProb_eq_one fun r ↦ hd₂ d hdd₂ H p ξ ξ hpd hp1 hξ0 le_rfl hξ0 le_rfl hH (ren H) r,
      mul_one]
  · exact mul_nonneg (Asm.percolationProb_nonneg hp0 hp1 H) (Asm.coinProb_nonneg _ _)

end BMW26
