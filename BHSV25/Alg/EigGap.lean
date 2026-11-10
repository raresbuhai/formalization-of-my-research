module

public import BHSV25.Net.Correct
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# No eigenvalue just above `-1`

On a regular graph with `n` vertices, every eigenvalue of the normalized adjacency matrix is `-1`
or at least `-1 + 1 / (2 n⁴)` (`BHSV25.Alg.eig_eq_neg_one_or_ge`). This lets the bottom filter of
Theorem 7.20 separate the eigenvalues at most `-λ` from the others with a power polynomial in `n`
for every `λ < 1`: if `λ > 1 - 1/(4 n⁴)`, the eigenvalues at most `-λ` are exactly those equal to
`-1`.

**The proof.** Let `x` be a unit eigenvector with eigenvalue `μ ≠ -1` of a `d`-regular graph,
`d ≥ 1`. Then `∑_(a ~ b) (x_a + x_b)² = 2 d (1 + μ)`, so `|x_a + x_b| ≤ ε = √(2 d (1 + μ))` on every
edge, and along a walk of length `L` from `u` to `v`, `|x_v - (-1)^L x_u| ≤ L ε`
(`BHSV25.Alg.abs_sub_neg_one_pow_le`). Take `r` with `x_r² ≥ 1 / n`, and the distances `dist(r, v)`
in its component, all below `n`:

* if some edge `ab` of the component has `dist(r, a) ≡ dist(r, b) (mod 2)`, the walks to `b`
  through `a` and directly have lengths of different parities, so `2 |x_r| ≤ 2 n ε`;
* otherwise `y_v = (-1)^dist(r, v)` on the component (and `0` elsewhere) is an eigenvector with
  eigenvalue `-1`, orthogonal to `x`, while `(-1)^dist(r, v) x_v ≥ x_r - n ε` on the component,
  so again `|x_r| ≤ n ε`.

So `1 / n ≤ x_r² ≤ n² ε² = 2 d n² (1 + μ)`, and `d < n`.
-/

@[expose] public section

namespace BHSV25.Alg

open Matrix

/-- **Along a walk**, a vector whose sums `x_a + x_b` over the edges are at most `ε` in absolute
value changes by at most `ε` per step, up to the sign `(-1)^L`. -/
theorem abs_sub_neg_one_pow_le {V : Type*} {H : SimpleGraph V} (x : V → ℝ) {ε : ℝ}
    (hε : ∀ a b, H.Adj a b → |x a + x b| ≤ ε) {u v : V} (p : H.Walk u v) :
    |x v - (-1) ^ p.length * x u| ≤ p.length * ε := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have e : x v - (-1) ^ (p.length + 1) * x u =
        (x v - (-1) ^ p.length * x w) + (-1) ^ p.length * (x w + x u) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have := hε w u h.symm
    push_cast
    linarith

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

open Classical in
/-- **The spectral gap at `-1`**: on a regular graph with `n` vertices, every eigenvalue of the
normalized adjacency matrix is `-1` or at least `-1 + 1 / (2 n⁴)`. -/
theorem eig_eq_neg_one_or_ge (G : Graph) (hreg : G.IsRegular) (i : Fin G.1) :
    G.eig i = -1 ∨ -1 + 1 / (2 * (G.1 : ℝ) ^ 4) ≤ G.eig i := by
  obtain ⟨d, hd⟩ := hreg
  have hn : 0 < G.1 := Fin.pos i
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- no edges: all eigenvalues are `0`
    subst hd0
    right
    rw [Net.eig_eq_zero_of_deg_zero G hd i]
    have : 1 / (2 * (G.1 : ℝ) ^ 4) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (G.1 : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hn)
      linarith
    linarith
  by_cases hμ : G.eig i = -1
  · exact Or.inl hμ
  right
  set hA := G.normAdj_isHermitian
  set μ := G.eig i with hμdef
  set x : Fin G.1 → ℝ := ⇑(hA.eigenvectorBasis i) with hx
  have hd' : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdlt : d < G.1 := by
    have := G.2.degree_lt_card_verts i
    rw [hd i, Fintype.card_fin] at this
    exact this
  -- the eigenvector
  have hcx : ∀ j, Spectral.coeff hA j x = if j = i then 1 else 0 := fun j ↦
    Net.coeff_eigenvector hA j i
  have hxx : x ⬝ᵥ x = 1 := by
    rw [← Spectral.sum_coeff_sq hA x]
    simp [hcx]
  have hxAx : x ⬝ᵥ (G.normAdj *ᵥ x) = μ := by
    rw [Spectral.quad_eq hA x]
    simp [hcx, hμdef, Graph.eig]
  have hμ1 : -1 ≤ μ := (abs_le.1 (G.abs_eig_le_one i)).1
  -- the degrees
  have hA_entry : ∀ a b, G.normAdj a b = if G.2.Adj a b then (d : ℝ)⁻¹ else 0 :=
    G.normAdj_of_isRegularOfDegree hd
  have hdeg : ∀ a, ∑ b, (if G.2.Adj a b then (1 : ℝ) else 0) = d := by
    intro a
    rw [Finset.sum_boole]
    have h1 : (Finset.univ.filter fun b ↦ G.2.Adj a b) = G.2.neighborFinset a := by
      rw [SimpleGraph.neighborFinset_eq_filter]
    rw [h1, SimpleGraph.card_neighborFinset_eq_degree, hd a]
  -- the sum over the edges
  have hsum : ∑ a, ∑ b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0) = 2 * d * (1 + μ) := by
    have hpt : ∀ a b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0) =
        (if G.2.Adj a b then (1 : ℝ) else 0) * x a ^ 2 +
          (if G.2.Adj a b then (1 : ℝ) else 0) * x b ^ 2 +
          2 * d * (x a * (G.normAdj a b * x b)) := by
      intro a b
      rw [hA_entry]
      split_ifs
      · field_simp
        ring
      · ring
    simp only [hpt, Finset.sum_add_distrib]
    have h1 : ∑ a, ∑ b, (if G.2.Adj a b then (1 : ℝ) else 0) * x a ^ 2 = d := by
      simp_rw [← Finset.sum_mul, hdeg]
      rw [← Finset.mul_sum]
      have : ∑ a, x a ^ 2 = 1 := by rw [← hxx, dotProduct]; simp [sq]
      rw [this, mul_one]
    have h2 : ∑ a, ∑ b, (if G.2.Adj a b then (1 : ℝ) else 0) * x b ^ 2 = d := by
      rw [Finset.sum_comm]
      have hsym : ∀ b, ∑ a, (if G.2.Adj a b then (1 : ℝ) else 0) * x b ^ 2 =
          (∑ a, if G.2.Adj b a then (1 : ℝ) else 0) * x b ^ 2 := by
        intro b
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [G.2.adj_comm]
      simp_rw [hsym, hdeg]
      rw [← Finset.mul_sum]
      have : ∑ a, x a ^ 2 = 1 := by rw [← hxx, dotProduct]; simp [sq]
      rw [this, mul_one]
    have h3 : ∑ a, ∑ b, 2 * d * (x a * (G.normAdj a b * x b)) = 2 * d * μ := by
      rw [← hxAx]
      simp only [dotProduct, mulVec, Finset.mul_sum]
    rw [h1, h2, h3]
    ring
  -- every edge
  set ε := Real.sqrt (2 * d * (1 + μ)) with hε
  have hedge : ∀ a b, G.2.Adj a b → |x a + x b| ≤ ε := by
    intro a b hab
    have hterm : ∀ a b, 0 ≤ (if G.2.Adj a b then (x a + x b) ^ 2 else 0) := fun a b ↦ by
      split_ifs <;> positivity
    have h1 : (if G.2.Adj a b then (x a + x b) ^ 2 else 0) ≤
        ∑ b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0) :=
      Finset.single_le_sum (fun b _ ↦ hterm a b) (Finset.mem_univ b)
    have h2 : ∑ b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0) ≤
        ∑ a, ∑ b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0) :=
      Finset.single_le_sum (f := fun a ↦ ∑ b, (if G.2.Adj a b then (x a + x b) ^ 2 else 0))
        (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hterm a b) (Finset.mem_univ a)
    simp only [hab, ↓reduceIte] at h1
    rw [hsum] at h2
    rw [hε, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (h1.trans h2)
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  -- the vertex of largest weight
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image Finset.univ (fun v ↦ x v ^ 2)
    ⟨i, Finset.mem_univ i⟩
  have hr2 : 1 / (G.1 : ℝ) ≤ x r ^ 2 := by
    have h1 : ∑ v, x v ^ 2 ≤ ∑ _v : Fin G.1, x r ^ 2 := Finset.sum_le_sum fun v hv ↦ hr v hv
    have h2 : ∑ v, x v ^ 2 = 1 := by rw [← hxx, dotProduct]; simp [sq]
    rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [div_le_iff₀ hn']
    linarith
  -- walks from `r`
  have hwalk : ∀ v, G.2.Reachable r v →
      |x v - (-1) ^ G.2.dist r v * x r| ≤ (G.1 - 1 : ℝ) * ε := by
    intro v hv
    obtain ⟨p, hp, hlen⟩ := hv.exists_path_of_dist
    have h1 := abs_sub_neg_one_pow_le x hedge p
    rw [hlen] at h1
    have h2 : G.2.dist r v < G.1 := by
      have := hp.length_lt
      rw [Fintype.card_fin, hlen] at this
      exact this
    have h3 : (G.2.dist r v : ℝ) ≤ G.1 - 1 := by
      have : G.2.dist r v + 1 ≤ G.1 := h2
      have : ((G.2.dist r v + 1 : ℕ) : ℝ) ≤ G.1 := by exact_mod_cast this
      push_cast at this
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right h3 hε0)
  have hxr : |x r| ≤ G.1 * ε := by
    by_cases hodd : ∃ a b, G.2.Adj a b ∧ G.2.Reachable r a ∧
        G.2.dist r a % 2 = G.2.dist r b % 2
    · -- an odd cycle: two walks of different parities
      obtain ⟨a, b, hab, hra, hpar⟩ := hodd
      obtain ⟨p, hp, hlen⟩ := hra.exists_path_of_dist
      have hrb : G.2.Reachable r b := hra.trans hab.reachable
      have h1 := abs_sub_neg_one_pow_le x hedge (p.concat hab)
      rw [SimpleGraph.Walk.length_concat, hlen] at h1
      have h2 := hwalk b hrb
      have hda : (G.2.dist r a : ℝ) ≤ G.1 - 1 := by
        have := hp.length_lt
        rw [Fintype.card_fin, hlen] at this
        have : ((G.2.dist r a + 1 : ℕ) : ℝ) ≤ G.1 := by exact_mod_cast this
        push_cast at this
        linarith
      have hsign : ((-1 : ℝ) ^ (G.2.dist r a + 1)) = -(-1) ^ G.2.dist r b := by
        rw [pow_succ, neg_one_pow_eq_pow_mod_two (G.2.dist r a), hpar,
          ← neg_one_pow_eq_pow_mod_two]
        ring
      rw [hsign] at h1
      have h3 : |2 * ((-1) ^ G.2.dist r b * x r)| ≤
          ((G.2.dist r a + 1 : ℕ) : ℝ) * ε + (G.1 - 1) * ε := by
        have e : 2 * ((-1 : ℝ) ^ G.2.dist r b * x r) =
            (x b - -(-1) ^ G.2.dist r b * x r) - (x b - (-1) ^ G.2.dist r b * x r) := by ring
        rw [e]
        exact (abs_sub _ _).trans (add_le_add h1 h2)
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_two] at h3
      push_cast at h3
      nlinarith
    · -- bipartite component: the sign vector is an eigenvector with eigenvalue `-1`
      push Not at hodd
      set y : Fin G.1 → ℝ := fun v ↦ if G.2.Reachable r v then (-1) ^ G.2.dist r v else 0
        with hy
      have hAy : G.normAdj *ᵥ y = -y := by
        funext v
        simp only [mulVec, dotProduct, hA_entry, Pi.neg_apply]
        by_cases hv : G.2.Reachable r v
        · have hnb : ∀ w, (if G.2.Adj v w then (d : ℝ)⁻¹ else 0) * y w =
              (if G.2.Adj v w then (d : ℝ)⁻¹ else 0) * (-y v) := by
            intro w
            by_cases hvw : G.2.Adj v w
            · have hw : G.2.Reachable r w := hv.trans hvw.reachable
              have hp := hodd v w hvw hv
              simp only [hvw, ↓reduceIte, hy, hw, hv]
              congr 1
              rw [neg_one_pow_eq_pow_mod_two (G.2.dist r w),
                neg_one_pow_eq_pow_mod_two (G.2.dist r v)]
              have h2 : G.2.dist r v % 2 < 2 := Nat.mod_lt _ (by norm_num)
              have h3 : G.2.dist r w % 2 < 2 := Nat.mod_lt _ (by norm_num)
              interval_cases (G.2.dist r v % 2) <;> interval_cases (G.2.dist r w % 2) <;>
                simp_all
            · simp [hvw]
          simp_rw [hnb, ← Finset.sum_mul]
          have : ∑ w, (if G.2.Adj v w then (d : ℝ)⁻¹ else 0) = 1 := by
            have h1 : ∀ w, (if G.2.Adj v w then (d : ℝ)⁻¹ else 0) =
                (d : ℝ)⁻¹ * (if G.2.Adj v w then (1 : ℝ) else 0) := fun w ↦ by
              split_ifs <;> simp
            simp_rw [h1]
            rw [← Finset.mul_sum, hdeg, inv_mul_cancel₀ hd'.ne']
          rw [this, one_mul]
        · have hnb : ∀ w, (if G.2.Adj v w then (d : ℝ)⁻¹ else 0) * y w = 0 := by
            intro w
            by_cases hvw : G.2.Adj v w
            · have hw : ¬ G.2.Reachable r w := fun hw ↦ hv (hw.trans hvw.symm.reachable)
              simp [hy, hw]
            · simp [hvw]
          have hyv : y v = 0 := by simp [hy, hv]
          rw [hyv, neg_zero]
          exact Finset.sum_eq_zero fun w _ ↦ hnb w
      -- `x` is orthogonal to `y`
      have hxy : x ⬝ᵥ y = 0 := by
        have h1 := Spectral.coeff_mulVec hA i y
        rw [hAy] at h1
        have h2 : Spectral.coeff hA i (-y) = -Spectral.coeff hA i y := by
          simp only [Spectral.coeff, dotProduct_neg]
        rw [h2] at h1
        have h3 : (μ + 1) * Spectral.coeff hA i y = 0 := by
          have : hA.eigenvalues i = μ := rfl
          rw [this] at h1
          linarith
        have h4 : μ + 1 ≠ 0 := fun h ↦ hμ (by linarith)
        exact (mul_eq_zero.1 h3).resolve_left h4
      -- the component
      set C := Finset.univ.filter fun v ↦ G.2.Reachable r v with hC
      have hrC : r ∈ C := Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl r⟩
      have hCpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.2 ⟨r, hrC⟩
      have hxy' : ∑ v ∈ C, (-1) ^ G.2.dist r v * x v = 0 := by
        rw [← hxy, dotProduct, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun v ↦ G.2.Reachable r v)]
        have h0 : ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ G.2.Reachable r v), x v * y v = 0 :=
          Finset.sum_eq_zero fun v hv ↦ by
            simp [hy, (Finset.mem_filter.1 hv).2]
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun v hv ↦ ?_
        simp [hy, (Finset.mem_filter.1 hv).2, mul_comm]
      have hbd : ∀ v ∈ C, |(-1) ^ G.2.dist r v * x v - x r| ≤ (G.1 - 1 : ℝ) * ε := by
        intro v hv
        have h1 := hwalk v (Finset.mem_filter.1 hv).2
        have e : (-1 : ℝ) ^ G.2.dist r v * x v - x r =
            (-1) ^ G.2.dist r v * (x v - (-1) ^ G.2.dist r v * x r) := by
          rw [mul_sub, ← mul_assoc, neg_one_pow_mul_self, one_mul]
        rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact h1
      have hup : (C.card : ℝ) * (x r - (G.1 - 1) * ε) ≤ 0 := by
        have h := Finset.card_nsmul_le_sum C (fun v ↦ (-1 : ℝ) ^ G.2.dist r v * x v)
          (x r - (G.1 - 1) * ε) (fun v hv ↦ by linarith [(abs_le.1 (hbd v hv)).1])
        rw [nsmul_eq_mul, hxy'] at h
        exact h
      have hlo : 0 ≤ (C.card : ℝ) * (x r + (G.1 - 1) * ε) := by
        have h := Finset.sum_le_card_nsmul C (fun v ↦ (-1 : ℝ) ^ G.2.dist r v * x v)
          (x r + (G.1 - 1) * ε) (fun v hv ↦ by linarith [(abs_le.1 (hbd v hv)).2])
        rw [nsmul_eq_mul, hxy'] at h
        exact h
      have h1 : x r - (G.1 - 1) * ε ≤ 0 := by
        by_contra h
        exact absurd hup (not_le.2 (mul_pos hCpos (lt_of_not_ge h)))
      have h2 : 0 ≤ x r + (G.1 - 1) * ε := by
        by_contra h
        exact absurd hlo (not_le.2 (mul_neg_of_pos_of_neg hCpos (lt_of_not_ge h)))
      rw [abs_le]
      constructor <;> nlinarith
  -- the bound
  have hsq : x r ^ 2 ≤ (G.1 : ℝ) ^ 2 * (2 * d * (1 + μ)) := by
    have h1 : x r ^ 2 ≤ ((G.1 : ℝ) * ε) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxr 2
    have h2 : ε ^ 2 = 2 * d * (1 + μ) := Real.sq_sqrt (by nlinarith)
    rw [mul_pow, h2] at h1
    exact h1
  have hdn : (d : ℝ) ≤ G.1 := by exact_mod_cast hdlt.le
  have h3 : 1 / (G.1 : ℝ) ≤ (G.1 : ℝ) ^ 2 * (2 * G.1 * (1 + μ)) := by
    refine (hr2.trans hsq).trans ?_
    have : 0 ≤ 1 + μ := by linarith
    gcongr
  have h4 : 1 / (2 * (G.1 : ℝ) ^ 4) ≤ 1 + μ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hn'] at h3
    nlinarith
  linarith

end BHSV25.Alg
