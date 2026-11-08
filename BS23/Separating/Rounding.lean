module

public import BS23.Model

/-!
# A separating bipartition from a pivot

The last step of the algorithm of [BS23, Theorem 1.1] is combinatorial. It has a "distance"
`Q i j ≥ 0` between sample points (later `Q i j = q(xᵢ - xⱼ)` for a polynomial `q` read off a
pseudo-expectation) and picks a pivot `p`: the points within `τ` of `p` form one side `C₁`, the
others the other side `C₂` (`List.ofFn fun j ↦ if Q p j ≤ τ then 0 else 1`).

Suppose `Q` is symmetric and satisfies a weak triangle inequality `Q i j ≤ K (Q i p + Q p j)`
with `2 K τ < T`, that at most a `δ ≤ 10⁻⁴` fraction of the pairs inside each cluster are farther
than `τ`, and that at most a `δ` fraction of the pairs between two nonempty clusters `S_a`, `S_b`
are closer than `T`. Then all pivots outside a set of at most `100 δ n` points give a separating
bipartition (`BS23.Separating.isSeparatingBipartition_ofFn`).

* **First side**, for good pivots: the bad pivots of a cluster `S_c` are its points that are
  farther than `τ` from more than `|S_c|/100` of its points (`BS23.Separating.badIn`); there are
  at most `100 δ |S_c|` of them (`BS23.Separating.card_badIn_le`). A pivot `p` that is not bad for
  its own cluster puts `99%` of it in `C₁` (`BS23.Separating.containsMostOfSome_near`).
* **Second side**, for every pivot: two points of `C₁` are within `2 K τ < T` of each other, so
  `|C₁ ∩ S_a| |C₁ ∩ S_b| ≤ δ |S_a| |S_b|`, and `C₁` has at most `1%` of `S_a` or of `S_b`
  (`BS23.Separating.containsMostOfSome_far`).
-/

@[expose] public section

namespace BS23.Separating

open Finset

variable {n k : ℕ}

/-! ### The output of a pivot -/

theorem outCluster_ofFn (f : Fin n → ℕ) (j : Fin n) : outCluster (List.ofFn f) j = f j := by
  simp [outCluster]

theorem filter_outCluster_eq_zero (Q : Fin n → Fin n → ℝ) (τ : ℝ) (p : Fin n) :
    (univ.filter fun j : Fin n ↦
        outCluster (List.ofFn fun j ↦ if Q p j ≤ τ then 0 else 1) j = 0) =
      univ.filter fun j ↦ Q p j ≤ τ := by
  ext j
  simp [outCluster_ofFn]

theorem filter_outCluster_ne_zero (Q : Fin n → Fin n → ℝ) (τ : ℝ) (p : Fin n) :
    (univ.filter fun j : Fin n ↦
        outCluster (List.ofFn fun j ↦ if Q p j ≤ τ then 0 else 1) j ≠ 0) =
      univ.filter fun j ↦ ¬ Q p j ≤ τ := by
  ext j
  simp [outCluster_ofFn]

/-! ### Counting pairs -/

/-- The pairs of `S × T` with a property, counted by their first point. -/
theorem card_filter_product_eq_sum (S T : Finset (Fin n)) (R : Fin n → Fin n → Prop)
    [∀ i j, Decidable (R i j)] :
    ((S ×ˢ T).filter fun ij ↦ R ij.1 ij.2).card = ∑ i ∈ S, (T.filter fun j ↦ R i j).card := by
  rw [card_filter, sum_product]
  simp_rw [card_filter]

/-- The points of `S` on each side of a pivot. -/
theorem card_inter_add_card_filter (Q : Fin n → Fin n → ℝ) (τ : ℝ) (p : Fin n)
    (S : Finset (Fin n)) :
    ((univ.filter fun j ↦ Q p j ≤ τ) ∩ S).card + (S.filter fun j ↦ τ < Q p j).card = S.card := by
  rw [filter_inter, univ_inter]
  simp_rw [← not_le]
  exact card_filter_add_card_filter_not _

/-! ### Bad pivots -/

/-- The **bad pivots** of a set `S`: its points `p` that are farther than `τ` from more than a
`1/100` fraction of `S`. -/
noncomputable def badIn (Q : Fin n → Fin n → ℝ) (τ : ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun p ↦ (S.card : ℝ) < 100 * (S.filter fun j ↦ τ < Q p j).card

/-- The **bad pivots**: the points that are bad pivots of their own cluster. -/
noncomputable def badPivots (ℓ : Fin n → Fin k) (Q : Fin n → Fin n → ℝ) (τ : ℝ) :
    Finset (Fin n) :=
  univ.biUnion fun c ↦ badIn Q τ (cluster ℓ c)

/-- **Few bad pivots** (Markov): if at most `δ |S|²` pairs of `S` are farther than `τ`, then `S`
has at most `100 δ |S|` bad pivots. -/
theorem card_badIn_le (Q : Fin n → Fin n → ℝ) {τ δ : ℝ} (S : Finset (Fin n))
    (hS : (((S ×ˢ S).filter fun ij ↦ τ < Q ij.1 ij.2).card : ℝ) ≤ δ * S.card ^ 2) :
    ((badIn Q τ S).card : ℝ) ≤ 100 * δ * S.card := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have hS0 : S = ∅ := card_eq_zero.1 h0
    simp [badIn, hS0]
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  have key : ((badIn Q τ S).card : ℝ) * S.card ≤ 100 * δ * S.card * S.card := by
    calc ((badIn Q τ S).card : ℝ) * S.card = ∑ _p ∈ badIn Q τ S, (S.card : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ badIn Q τ S, 100 * ((S.filter fun j ↦ τ < Q p j).card : ℝ) :=
          sum_le_sum fun p hp ↦ (mem_filter.1 hp).2.le
      _ ≤ ∑ p ∈ S, 100 * ((S.filter fun j ↦ τ < Q p j).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity
      _ = 100 * (((S ×ˢ S).filter fun ij ↦ τ < Q ij.1 ij.2).card : ℝ) := by
          rw [← mul_sum, card_filter_product_eq_sum S S fun i j ↦ τ < Q i j]
          push_cast
          rfl
      _ ≤ 100 * (δ * S.card ^ 2) := by linarith
      _ = 100 * δ * S.card * S.card := by ring
  exact le_of_mul_le_mul_right key hSpos

/-- At most `100 δ n` bad pivots, if at most `δ |S_c|²` pairs of each cluster `S_c` are farther
than `τ`. -/
theorem card_badPivots_le (ℓ : Fin n → Fin k) (Q : Fin n → Fin n → ℝ) {τ δ : ℝ}
    (hsame : ∀ c, (((cluster ℓ c ×ˢ cluster ℓ c).filter fun ij ↦ τ < Q ij.1 ij.2).card : ℝ) ≤
      δ * (cluster ℓ c).card ^ 2) :
    ((badPivots ℓ Q τ).card : ℝ) ≤ 100 * δ * n := by
  have hn : ∑ c, ((cluster ℓ c).card : ℝ) = n := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := ℓ)
      fun _ _ ↦ mem_univ _
    rw [card_univ, Fintype.card_fin] at h
    have h' : ∑ c, (cluster ℓ c).card = n := h.symm
    exact_mod_cast h'
  calc ((badPivots ℓ Q τ).card : ℝ) ≤ ∑ c, ((badIn Q τ (cluster ℓ c)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ c, 100 * δ * ((cluster ℓ c).card : ℝ) :=
        sum_le_sum fun c _ ↦ card_badIn_le Q _ (hsame c)
    _ = 100 * δ * n := by rw [← mul_sum, hn]

/-! ### The two sides -/

/-- **First side**: a pivot that is not bad for its own cluster has `99%` of it within `τ`. -/
theorem containsMostOfSome_near (ℓ : Fin n → Fin k) (Q : Fin n → Fin n → ℝ) (τ : ℝ) {p : Fin n}
    (hp : p ∉ badPivots ℓ Q τ) : ContainsMostOfSome ℓ (univ.filter fun j ↦ Q p j ≤ τ) := by
  have hpS : p ∈ cluster ℓ (ℓ p) := by simp [cluster]
  refine ⟨ℓ p, ⟨p, hpS⟩, ?_⟩
  have hnb : p ∉ badIn Q τ (cluster ℓ (ℓ p)) := fun h ↦ hp (mem_biUnion.2 ⟨ℓ p, mem_univ _, h⟩)
  have hle : 100 * (((cluster ℓ (ℓ p)).filter fun j ↦ τ < Q p j).card : ℝ) ≤
      (cluster ℓ (ℓ p)).card := by
    simp only [badIn, mem_filter, not_and, not_lt] at hnb
    exact hnb hpS
  have hsplit := card_inter_add_card_filter Q τ p (cluster ℓ (ℓ p))
  have hsplit' : (((univ.filter fun j ↦ Q p j ≤ τ) ∩ cluster ℓ (ℓ p)).card : ℝ) +
      ((cluster ℓ (ℓ p)).filter fun j ↦ τ < Q p j).card = (cluster ℓ (ℓ p)).card := by
    exact_mod_cast hsplit
  linarith

/-- **Second side**: if at most a `δ ≤ 10⁻⁴` fraction of the pairs between two nonempty clusters
are closer than `T > 2 K τ`, then every pivot has `99%` of one of them farther than `τ`. -/
theorem containsMostOfSome_far (ℓ : Fin n → Fin k) (Q : Fin n → Fin n → ℝ) {K τ T δ : ℝ}
    (hK : 0 ≤ K) (hsymm : ∀ i j, Q i j = Q j i) (htri : ∀ i j p, Q i j ≤ K * (Q i p + Q p j))
    (hτT : 2 * K * τ < T) (hδ : δ ≤ 1 / 10000) {a b : Fin k} (ha : (cluster ℓ a).Nonempty)
    (hb : (cluster ℓ b).Nonempty)
    (hfar : (((cluster ℓ a ×ˢ cluster ℓ b).filter fun ij ↦ Q ij.1 ij.2 < T).card : ℝ) ≤
      δ * (cluster ℓ a).card * (cluster ℓ b).card) (p : Fin n) :
    ContainsMostOfSome ℓ (univ.filter fun j ↦ ¬ Q p j ≤ τ) := by
  set C := univ.filter fun j ↦ Q p j ≤ τ with hC
  have hsub : (C ∩ cluster ℓ a) ×ˢ (C ∩ cluster ℓ b) ⊆
      (cluster ℓ a ×ˢ cluster ℓ b).filter fun ij ↦ Q ij.1 ij.2 < T := by
    intro ij hij
    simp only [hC, mem_product, mem_inter, mem_filter, mem_univ, true_and] at hij ⊢
    refine ⟨⟨hij.1.2, hij.2.2⟩, ?_⟩
    calc Q ij.1 ij.2 ≤ K * (Q ij.1 p + Q p ij.2) := htri _ _ _
      _ ≤ K * (τ + τ) := by
          rw [hsymm ij.1 p]
          exact mul_le_mul_of_nonneg_left (add_le_add hij.1.1 hij.2.1) hK
      _ = 2 * K * τ := by ring
      _ < T := hτT
  have hprod : ((C ∩ cluster ℓ a).card : ℝ) * (C ∩ cluster ℓ b).card ≤
      δ * (cluster ℓ a).card * (cluster ℓ b).card := by
    have h := card_le_card hsub
    rw [card_product] at h
    have h' : ((C ∩ cluster ℓ a).card : ℝ) * (C ∩ cluster ℓ b).card ≤
        (((cluster ℓ a ×ˢ cluster ℓ b).filter fun ij ↦ Q ij.1 ij.2 < T).card : ℝ) := by
      exact_mod_cast h
    linarith
  -- A cluster with at most `1%` in `C` has `99%` on the other side.
  have hside : ∀ c, (cluster ℓ c).Nonempty →
      ((C ∩ cluster ℓ c).card : ℝ) ≤ (cluster ℓ c).card / 100 →
      ContainsMostOfSome ℓ (univ.filter fun j ↦ ¬ Q p j ≤ τ) := by
    intro c hc hsmall
    refine ⟨c, hc, ?_⟩
    have hsplit : (C ∩ cluster ℓ c).card + ((univ.filter fun j ↦ ¬ Q p j ≤ τ) ∩ cluster ℓ c).card
        = (cluster ℓ c).card := by
      rw [hC, filter_inter, filter_inter, univ_inter]
      exact card_filter_add_card_filter_not _
    have hsplit' : ((C ∩ cluster ℓ c).card : ℝ) +
        ((univ.filter fun j ↦ ¬ Q p j ≤ τ) ∩ cluster ℓ c).card = (cluster ℓ c).card := by
      exact_mod_cast hsplit
    linarith
  by_cases hA : ((C ∩ cluster ℓ a).card : ℝ) ≤ (cluster ℓ a).card / 100
  · exact hside a ha hA
  refine hside b hb ?_
  by_contra hB
  push Not at hA hB
  have hApos : (0 : ℝ) < (cluster ℓ a).card := by exact_mod_cast ha.card_pos
  have hBpos : (0 : ℝ) < (cluster ℓ b).card := by exact_mod_cast hb.card_pos
  have h1 : ((cluster ℓ a).card : ℝ) / 100 * ((cluster ℓ b).card / 100) <
      ((C ∩ cluster ℓ a).card : ℝ) * (C ∩ cluster ℓ b).card :=
    mul_lt_mul'' hA hB (by positivity) (by positivity)
  have h2 : δ * (cluster ℓ a).card * (cluster ℓ b).card ≤
      ((cluster ℓ a).card : ℝ) / 100 * ((cluster ℓ b).card / 100) := by
    have hAB : (0 : ℝ) ≤ (cluster ℓ a).card * (cluster ℓ b).card := by positivity
    nlinarith
  linarith

/-! ### The bipartition -/

/-- **A separating bipartition from a pivot** [BS23, proof of Theorem 4.1]. Let `Q` be symmetric
with `Q i j ≤ K (Q i p + Q p j)`, `K ≥ 0`, and `2 K τ < T`. Suppose at most `δ |S_c|²` pairs of
each cluster `S_c` are farther than `τ`, and at most `δ |S_a| |S_b|` pairs between two nonempty
clusters `S_a`, `S_b` are closer than `T`, with `δ ≤ 10⁻⁴`. Then outside a set of at most
`100 δ n` pivots `p`, putting the points within `τ` of `p` in cluster `0` and the others in cluster
`1` is a separating bipartition. -/
theorem isSeparatingBipartition_ofFn (ℓ : Fin n → Fin k) (Q : Fin n → Fin n → ℝ) {K τ T δ : ℝ}
    (hK : 0 ≤ K) (hsymm : ∀ i j, Q i j = Q j i) (htri : ∀ i j p, Q i j ≤ K * (Q i p + Q p j))
    (hτT : 2 * K * τ < T) (hδ : δ ≤ 1 / 10000)
    (hsame : ∀ c, (((cluster ℓ c ×ˢ cluster ℓ c).filter fun ij ↦ τ < Q ij.1 ij.2).card : ℝ) ≤
      δ * (cluster ℓ c).card ^ 2)
    {a b : Fin k} (ha : (cluster ℓ a).Nonempty) (hb : (cluster ℓ b).Nonempty)
    (hfar : (((cluster ℓ a ×ˢ cluster ℓ b).filter fun ij ↦ Q ij.1 ij.2 < T).card : ℝ) ≤
      δ * (cluster ℓ a).card * (cluster ℓ b).card) :
    ∃ Bad : Finset (Fin n), (Bad.card : ℝ) ≤ 100 * δ * n ∧
      ∀ p ∉ Bad, IsSeparatingBipartition ℓ (List.ofFn fun j ↦ if Q p j ≤ τ then 0 else 1) := by
  refine ⟨badPivots ℓ Q τ, card_badPivots_le ℓ Q hsame, fun p hp ↦ ?_⟩
  unfold IsSeparatingBipartition
  rw [filter_outCluster_eq_zero, filter_outCluster_ne_zero]
  exact ⟨List.length_ofFn, containsMostOfSome_near ℓ Q τ hp,
    containsMostOfSome_far ℓ Q hK hsymm htri hτT hδ ha hb hfar p⟩

end BS23.Separating
