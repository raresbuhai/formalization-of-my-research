module

public import BHSV25.Planted.Partial
public import BHSV25.Planted.Comp
public import BHSV25.Planted.StatBad

/-!
# Theorem 7.17 on one good coloring

The deterministic part of [BHSV25, Theorem 7.17] (`BHSV25.Planted.isColoring_full`): for `k ≥ 3`,
a `d`-regular host with `d ≥ d₀` and at most one eigenvalue above `λ₀ = 1 / (16384 k⁶)`, and a
coloring `χ` of `n ≥ (k (4k + 1))⁴` vertices that is good (`BHSV25.Planted.Good`), makes at most
`α n` vertices statistically bad, `α = 1 / (1024 k¹²)`, and leaves no connected set of at most
`β n = 4 α n` vertices with `k^|S| > n²` stuck, the algorithm `BHSV25.Planted.fullAlg` outputs a
proper `k`-coloring of the planted graph.

The proof follows the paper's:
1. **The list** (Theorem B.1): some candidate `q` of the list differs from `χ` on a set `B` of at
   most `α n` vertices (`BHSV25.Planted.exists_good_candidate`, with the precision of the net
   `4 / K`, `K = 8192 k⁸`, and `d₀` large enough).
2. **Uncoloring** (Lemma B.20, with `d' = d` among the degrees tried): Lemma B.19 for the `2 α n`
   vertices of `B ∪ SB` gives `T ⊇ B ∪ SB` with `|T| ≤ 4 α n` such that every other vertex has at
   most `(4α + 2λ₀) d` neighbors in `T`; the vertices outside `T` keep `d / (2k) - (4α + 2λ₀) d ≥
   d / (6k)` neighbors of every other color outside `T`, so they stay colored; and the edge
   density bound (Lemma 7.18) excludes a nonempty set of wrongly colored vertices with
   `d / (6k)` neighbors each in the set, as `α + λ₀ < 1 / (6k)`.
3. **Safe recoloring** (Lemma B.21): the components of the uncolored vertices are stuck, connected
   and of at most `|T| ≤ β n` vertices, so `k^|C| ≤ n²`.
4. **Brute force** colors them, and the rounding and selection keep a proper coloring of all
   vertices.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {k : ℕ}

/-! ### The constants -/

/-- The threshold `λ₀ = 1 / (16384 k⁶)` of Theorem 7.17. -/
noncomputable def lamF (k : ℕ) : ℝ := 1 / (16384 * (k : ℝ) ^ 6)

/-- The fraction `α = 1 / (1024 k¹²)` of wrongly colored and of statistically bad vertices. -/
noncomputable def alphaF (k : ℕ) : ℝ := 1 / (1024 * (k : ℝ) ^ 12)

/-- The fraction `β = 4 α = 1 / (256 k¹²)` of uncolored vertices. -/
noncomputable def betaF (k : ℕ) : ℝ := 1 / (256 * (k : ℝ) ^ 12)

/-- The precision `4 / K` of the net, `K = 8192 k⁸`. -/
def fullK (k : ℕ) : ℕ := 8192 * k ^ 8

/-- The degree from which the list contains a candidate within `α n` of the planted coloring. -/
def fullD (k : ℕ) : ℕ := (5 * 2 ^ 31 * k ^ 23) ^ 4

/-- The parameters of the algorithm of Theorem 7.17. -/
def fullParams (k : ℕ) : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) := planParams k (fullK k) 1

theorem lamF_pos (hk : 0 < k) : 0 < lamF k := by unfold lamF; positivity

theorem lamF_lt_lamP (hk : 0 < k) : lamF k < lamP k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold lamF lamP
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_le_pow_left₀ zero_le_one hk1 4, pow_le_pow_left₀ zero_le_one hk1 6,
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 2]

/-! ### The list -/

theorem mem_clusterList (n m S K B : ℕ) (U : List (List ℚ)) (us : Fin m → List ℚ)
    (hus : ∀ j, us j ∈ U) (ts : Fin (m * m) → Fin (2 * K + 1)) (hB1 : U.length ^ m ≤ B)
    (hB2 : (2 * K + 1) ^ (m * m) ≤ B) :
    Alg.clustersC n (List.ofFn us) (Alg.gridCenters m S K (Nat.sqrt n)
        (List.ofFn fun j ↦ (ts j : ℕ))) ∈ clusterList n m S K B U := by
  rw [clusterList, List.mem_flatMap]
  have hU : ∀ j, U.idxOf (us j) < U.length := fun j ↦ List.idxOf_lt_length_of_mem (hus j)
  refine ⟨List.ofFn fun j ↦ ((⟨U.idxOf (us j), hU j⟩ : Fin U.length) : ℕ),
    Tuples.ofFn_mem_tuples hB1 _, List.mem_map.2 ⟨_, Tuples.ofFn_mem_tuples hB2 ts, ?_⟩⟩
  congr 2
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (hU j), List.getElem_idxOf]

/-! ### The final rounding -/

theorem getD_clampK {n : ℕ} (c : List ℕ) {y : ℕ} (hy : y < n) :
    (clampK n k c).getD y k = if c.getD y k < k then c.getD y k else 0 :=
  Net.getD_map_range n _ k hy

open Classical in
/-- A proper coloring of all vertices survives the rounding. -/
theorem numColored_pipeline {G : Graph} (b : List ℕ)
    (hb : ∀ y : Fin G.1, b.getD y k < k)
    (hprop : ∀ u v : Fin G.1, G.2.Adj u v → b.getD u k ≠ b.getD v k) :
    G.IsPartialColoring k (Alg.colorOf G.1 k k (adjTable G) (clampK G.1 k b)) ∧
      G.1 ≤ G.numColored k (Alg.colorOf G.1 k k (adjTable G) (clampK G.1 k b)) := by
  set p := clampK G.1 k b
  have hp : ∀ v : Fin G.1, p.getD v k = b.getD v k := fun v ↦ by
    rw [getD_clampK _ v.2, ite_eq_left (hb v)]
  have hp' : ∀ v : Fin G.1, p.getD v k < k := fun v ↦ by rw [hp]; exact hb v
  refine ⟨Alg.isPartialColoring_colorOf G le_rfl p hp', ?_⟩
  set I : ℕ → Finset (Fin G.1) := fun a ↦ Alg.classSet G k p a
  have hI : ∀ a, G.2.IsIndepSet (I a : Set (Fin G.1)) := by
    intro a u hu v hv _ huv
    simp only [I, Alg.classSet, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hu hv
    exact hprop u v huv (by rw [← hp, ← hp, hu, hv])
  have h := Alg.sum_card_inter_le G le_rfl p hp' I hI
  simp only [I, inter_self, sdiff_self, bot_eq_empty, card_empty, Nat.cast_zero, sub_zero] at h
  have hsum : ∑ a ∈ range k, ((Alg.classSet G k p a).card : ℝ) = G.1 := by
    have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin G.1))) (t := range k)
      (f := fun v : Fin G.1 ↦ p.getD v k) (fun v _ ↦ mem_range.2 (hp' v))
    rw [card_univ, Fintype.card_fin] at this
    have h' : ((G.1 : ℕ) : ℝ) = ∑ a ∈ range k,
        (((univ : Finset (Fin G.1)).filter fun v : Fin G.1 ↦ p.getD v k = a).card : ℝ) := by
      exact_mod_cast this
    exact h'.symm
  have h2 : ∑ a ∈ range k, max 0 ((Alg.classSet G k p a).card : ℝ) =
      ∑ a ∈ range k, ((Alg.classSet G k p a).card : ℝ) :=
    sum_congr rfl fun a _ ↦ max_eq_right (Nat.cast_nonneg _)
  rw [h2, hsum] at h
  exact_mod_cast h

open Classical in
/-- The output of the algorithm is a partial coloring, and colors at least as many vertices as
each result of the steps. -/
theorem fullAlg_spec (hk : 0 < k) (G : Graph) {K t : ℕ} (q : List ℕ) (d : ℕ)
    (hq : q ∈ clusterList G.1 k (gridS k) (gridK k)
      (((3 + 12 * K) ^ numT k t + 1) ^ k + (2 * gridK k + 1) ^ (k * k))
      (Alg.expNet (planParams k K t).2 (G.1, adjTable G)))
    (hd : d ≤ G.1) :
    G.IsPartialColoring k (fullAlg (planParams k K t) (G.1, adjTable G)) ∧
      G.numColored k (pipeline G.1 k d (adjTable G) q) ≤
        G.numColored k (fullAlg (planParams k K t) (G.1, adjTable G)) := by
  set L := (clusterList G.1 k (gridS k) (gridK k)
      (((3 + 12 * K) ^ numT k t + 1) ^ k + (2 * gridK k + 1) ^ (k * k))
      (Alg.expNet (planParams k K t).2 (G.1, adjTable G))).flatMap
      fun q ↦ (List.range (G.1 + 1)).map fun d ↦ pipeline G.1 k d (adjTable G) q with hL
  have hrun : fullAlg (planParams k K t) (G.1, adjTable G) = Alg.bestColoring G.1 k L := by
    rw [fullAlg, Alg.numV_graph]
    rfl
  rw [hrun]
  obtain ⟨hmem, hbest⟩ := Alg.bestColoring_spec G.1 k L
  have hpipe : ∀ c ∈ L, G.IsPartialColoring k c := by
    intro c hc
    rw [hL, List.mem_flatMap] at hc
    obtain ⟨q', -, hc⟩ := hc
    obtain ⟨d', -, rfl⟩ := List.mem_map.1 hc
    refine Alg.isPartialColoring_colorOf G le_rfl _ fun v ↦ ?_
    rw [getD_clampK _ v.2]
    split_ifs with h
    · exact h
    · exact hk
  refine ⟨?_, ?_⟩
  · rcases hmem with h | h
    · exact hpipe _ h
    · rw [h]; intro u v _ hu; simp [Graph.color] at hu
  · have hr : pipeline G.1 k d (adjTable G) q ∈ L := by
      rw [hL, List.mem_flatMap]
      exact ⟨q, hq, List.mem_map.2 ⟨d, List.mem_range.2 (by omega), rfl⟩⟩
    have := hbest _ hr
    rw [Alg.numColored_eq_numCol G, Alg.numColored_eq_numCol G]
    exact this

/-! ### The arithmetic -/

theorem errB_div_le_alphaF (hk : 0 < k) {d : ℕ} (hd : fullD k ≤ d) :
    errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ alphaF k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set x : ℝ := 5 * 2 ^ 31 * (k : ℝ) ^ 23 with hx
  have hx0 : 0 < x := by positivity
  have h1 : x ^ 4 ≤ (d : ℝ) + 1 := by
    have : ((fullD k : ℕ) : ℝ) = x ^ 4 := by rw [fullD, hx]; push_cast; ring
    have h2 : ((fullD k : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2 : x ≤ ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    have h3 : (x ^ 4) ^ ((1 : ℝ) / 4) = x := by
      rw [show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hx0.le (by norm_num)
    rw [← h3]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  calc errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ errB k / x :=
        div_le_div_of_nonneg_left (by unfold errB; positivity) hx0 h2
    _ = alphaF k := by
        rw [errB, alphaF, hx]
        field_simp
        ring

theorem K_term_eq (hk : 0 < k) :
    65536 * (k : ℝ) ^ 4 / ((fullK k : ℕ) : ℝ) ^ 2 = alphaF k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [fullK, alphaF]
  push_cast
  field_simp
  ring

/-! ### The constants of the analysis -/

theorem alphaF_pos (hk : 0 < k) : 0 < alphaF k := by unfold alphaF; positivity

theorem lamF_lt_one (hk : 0 < k) : lamF k < 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [lamF, div_lt_one (by positivity)]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 6]

theorem alphaF_add_lamF_lt (hk : 3 ≤ k) : alphaF k + lamF k < 1 / (6 * k) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by linarith
  rw [alphaF, lamF]
  have h1 : 1 / (1024 * (k : ℝ) ^ 12) ≤ 1 / (1024 * k) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 11]
  have h2 : 1 / (16384 * (k : ℝ) ^ 6) ≤ 1 / (16384 * k) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 5]
  have h3 : 1 / (1024 * (k : ℝ)) + 1 / (16384 * k) < 1 / (6 * k) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  linarith

theorem eps_le (hk : 3 ≤ k) : 4 * alphaF k + 2 * lamF k ≤ 1 / (3 * k) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by linarith
  rw [alphaF, lamF]
  have h1 : 4 * (1 / (1024 * (k : ℝ) ^ 12)) ≤ 1 / (256 * k) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 11]
  have h2 : 2 * (1 / (16384 * (k : ℝ) ^ 6)) ≤ 1 / (8192 * k) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 5]
  have h3 : 1 / (256 * (k : ℝ)) + 1 / (8192 * k) ≤ 1 / (3 * k) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  linarith

theorem betaF_eq : betaF k = 4 * alphaF k := by
  unfold betaF alphaF
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · have : (k : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp; ring

/-! ### The host: the set `T` -/

open Classical in
/-- **Lemma B.19 for the uncoloring**: the wrongly colored and the statistically bad vertices lie
in a set `T` of at most `β n` vertices outside of which every vertex keeps at least `d / (6k)`
neighbors of every other color. -/
theorem exists_T (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (hexp : H.numEigGT (lamF k) ≤ 1) (χ : Fin H.1 → Fin k) (B : Finset (Fin H.1))
    (hB : (B.card : ℝ) ≤ alphaF k * H.1) (hbad : ((badSet H d χ).card : ℝ) ≤ alphaF k * H.1) :
    ∃ T : Finset (Fin H.1), B ⊆ T ∧ (T.card : ℝ) ≤ betaF k * H.1 ∧
      ∀ y ∉ T, ∀ a : Fin k, a ≠ χ y →
        d ≤ 6 * k * (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a).card := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  set c := lamF k
  set α := alphaF k
  have hc0 : 0 < c := lamF_pos hk0
  set S := B ∪ badSet H d χ
  have hS : (S.card : ℝ) ≤ 2 * α * H.1 := by
    have h' : (S.card : ℝ) ≤ B.card + (badSet H d χ).card := by
      exact_mod_cast card_union_le B (badSet H d χ)
    linarith
  obtain ⟨T, hST, hTc, hTdeg⟩ := exists_closed_superset hreg hd hc0.le (lamF_lt_one hk0) hexp S
    (γ := 2 * α) (ε := 4 * α + 2 * c) (by have := alphaF_pos hk0; positivity) hS (by linarith)
  refine ⟨T, subset_union_left.trans hST, ?_, fun y hy a ha ↦ ?_⟩
  · have h1 : (T.card : ℝ) ≤ 2 * S.card := by exact_mod_cast hTc
    rw [betaF_eq]; linarith
  have hySB : y ∉ badSet H d χ := fun h ↦ hy (hST (mem_union_right _ h))
  have hnb : d ≤ 2 * k * nbrCol H χ y a := by
    by_contra hlt
    push Not at hlt
    exact hySB (mem_filter.2 ⟨mem_univ _, a, ha, hlt⟩)
  have hsub : (univ.filter fun z : Fin H.1 ↦ H.2.Adj y z ∧ χ z = a) ⊆
      (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a) ∪ T.filter (H.2.Adj y) := by
    intro z hz
    rw [mem_filter] at hz
    by_cases hzT : z ∈ T
    · exact mem_union_right _ (mem_filter.2 ⟨hzT, hz.2.1⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hzT, hz.2⟩)
  have h1 : (nbrCol H χ y a : ℝ) ≤ (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a).card +
      (T.filter (H.2.Adj y)).card := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    exact_mod_cast this
  have h2 := hTdeg y hy
  have h3 : (d : ℝ) ≤ 2 * k * nbrCol H χ y a := by exact_mod_cast hnb
  have h5 : 6 * (k : ℝ) * ((4 * α + 2 * c) * d) ≤ 2 * d := by
    have := mul_le_mul_of_nonneg_left (eps_le hk) (by positivity : (0 : ℝ) ≤ 6 * k * d)
    have e : 6 * (k : ℝ) * d * (1 / (3 * k)) = 2 * d := by field_simp; ring
    nlinarith
  have h4 : (d : ℝ) ≤ 6 * k * (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a).card := by
    nlinarith
  exact_mod_cast h4

open Classical in
/-- **No dense set of wrong colors** (Lemma 7.18 in the proof of Lemma B.20): a nonempty set of at
most `α n` vertices does not give each of its vertices `d / (6k)` neighbors in itself. -/
theorem not_dense (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (hexp : H.numEigGT (lamF k) ≤ 1) (W : Finset (Fin H.1)) (hW : W.Nonempty)
    (hWc : (W.card : ℝ) ≤ alphaF k * H.1) :
    ¬ ∀ y ∈ W, d ≤ 6 * k * (W.filter (H.2.Adj y)).card := by
  intro hWd
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hn : 0 < H.1 := by
    obtain ⟨y, -⟩ := hW; exact Fin.pos y
  have hnR : (0 : ℝ) < H.1 := by exact_mod_cast hn
  have hpairs : (W.card : ℝ) * d ≤ 6 * k * pairs H W := by
    have h1 : W.card * d ≤ 6 * k * pairs H W := by
      rw [pairs, mul_sum]
      calc W.card * d = ∑ _y ∈ W, d := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ y ∈ W, 6 * k * (W.filter (H.2.Adj y)).card := sum_le_sum hWd
    exact_mod_cast h1
  have hdens := pairs_le hreg hd (lamF_pos hk0).le (lamF_lt_one hk0) hexp W
  have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have h1 : (W.card : ℝ) * d ≤ 6 * k * (d * ((W.card : ℝ) ^ 2 / H.1 + lamF k * W.card)) :=
    hpairs.trans (mul_le_mul_of_nonneg_left hdens (by positivity))
  have h2 : (1 : ℝ) ≤ 6 * k * ((W.card : ℝ) / H.1 + lamF k) := by
    have e : 6 * (k : ℝ) * (d * ((W.card : ℝ) ^ 2 / H.1 + lamF k * W.card)) =
        (W.card * d) * (6 * k * ((W.card : ℝ) / H.1 + lamF k)) := by ring
    rw [e] at h1
    have h1' : (W.card * d : ℝ) * 1 ≤ (W.card * d) * (6 * k * ((W.card : ℝ) / H.1 + lamF k)) := by
      rw [mul_one]; exact h1
    exact le_of_mul_le_mul_left h1' (by positivity)
  have h3 : (W.card : ℝ) / H.1 ≤ alphaF k := by rw [div_le_iff₀ hnR]; exact hWc
  have h5 := alphaF_add_lamF_lt hk
  rw [lt_div_iff₀ (by positivity)] at h5
  have h6 := mul_le_mul_of_nonneg_left (add_le_add_right h3 (lamF k)) (by positivity :
    (0 : ℝ) ≤ 6 * k)
  nlinarith

/-! ### The steps on the planted graph -/

/-- The planted graph with the vertices of the host: definitionally `H.plant χ`. -/
abbrev plantG (H : Graph) (χ : Fin H.1 → Fin k) : Graph := ⟨H.1, (H.plant χ).2⟩

open Classical in
/-- **Uncoloring, safe recoloring and brute force** color the planted graph properly from a
candidate that agrees with `χ` outside `T`. -/
theorem pipeline_good (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (hd : d ≠ 0) (hexp : H.numEigGT (lamF k) ≤ 1) (χ : Fin H.1 → Fin k) (q : List ℕ)
    (hqk : ∀ y : Fin H.1, q.getD y k < k) (T : Finset (Fin H.1))
    (hqB : (univ.filter fun y : Fin H.1 ↦ q.getD y k ≠ χ y) ⊆ T)
    (hBc : ((univ.filter fun y : Fin H.1 ↦ q.getD y k ≠ χ y).card : ℝ) ≤ alphaF k * H.1)
    (hT : (T.card : ℝ) ≤ betaF k * H.1)
    (hTdeg : ∀ y ∉ T, ∀ a : Fin k, a ≠ χ y →
      d ≤ 6 * k * (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a).card)
    (hstuck : ∀ S : Finset (Fin H.1), S.Nonempty → ConnSet H.2 S →
      (S.card : ℝ) ≤ betaF k * H.1 → H.1 ^ 2 < k ^ S.card → ¬ Stuck H S χ) :
    H.1 ≤ (plantG H χ).numColored k
      (pipeline H.1 k d (adjTable (plantG H χ)) q) := by
  set G := plantG H χ with hG
  have hk0 : 0 < k := by omega
  have hproper : ∀ u v : Fin G.1, G.2.Adj u v → χ u ≠ χ v := fun u v h ↦ h.2
  set R : Finset (Fin H.1) := univ \ T with hRdef
  have hR : ∀ y ∈ R, q.getD y k = χ y := by
    intro y hy
    rw [hRdef, mem_sdiff] at hy
    by_contra hne
    exact hy.2 (hqB (mem_filter.2 ⟨mem_univ _, hne⟩))
  have hRdeg : ∀ y ∈ R, ∀ a : Fin k, a ≠ χ y →
      d ≤ 6 * k * (R.filter fun z ↦ G.2.Adj y z ∧ χ z = a).card := by
    intro y hy a ha
    rw [hRdef, mem_sdiff] at hy
    have h := hTdeg y hy.2 a ha
    have heq : (univ.filter fun z ↦ z ∉ T ∧ H.2.Adj y z ∧ χ z = a) =
        R.filter fun z ↦ G.2.Adj y z ∧ χ z = a := by
      ext z
      simp only [mem_filter, mem_univ, true_and, hRdef, mem_sdiff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, ⟨h2, by rw [h3]; exact Ne.symm ha⟩, h3⟩
      · rintro ⟨h1, ⟨h2, -⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [heq] at h
    exact h
  have hW : ∀ W : Finset (Fin G.1), (∀ y ∈ W, q.getD y k < k ∧ q.getD y k ≠ χ y) →
      (∀ y ∈ W, d ≤ 6 * k * (W.filter (G.2.Adj y)).card) → W = ∅ := by
    intro W hWB hWd
    by_contra hne
    have hWne : W.Nonempty := nonempty_iff_ne_empty.2 hne
    have hWsub : W ⊆ univ.filter fun y : Fin H.1 ↦ q.getD y k ≠ χ y :=
      fun y hy ↦ mem_filter.2 ⟨mem_univ _, (hWB y hy).2⟩
    refine not_dense hk H hreg hd hexp W hWne
      (le_trans (by exact_mod_cast card_le_card hWsub) hBc) fun y hy ↦ ?_
    refine (hWd y hy).trans (Nat.mul_le_mul_left _ (card_le_card fun z hz ↦ ?_))
    rw [mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.1⟩
  -- uncoloring
  obtain ⟨hu1, hu2, hu3⟩ := uncolor_spec (G := G) χ hproper d q R hR hRdeg hW
  set c₁ := uncolor G.1 k d (adjTable G) q with hc₁
  have hc1k : ∀ y : Fin G.1, c₁.getD y k ≤ k := fun y ↦
    (hu3 y).elim (fun h ↦ h ▸ (hqk y).le) (fun h ↦ h.le)
  -- safe recoloring
  obtain ⟨hr1, hr2, hr3, hr4⟩ := recolor_spec (G := G) χ hproper c₁ hu1 hc1k
  set c₂ := recolor G.1 k (adjTable G) c₁ with hc₂
  have hU2 : ∀ y : Fin G.1, c₂.getD y k = k → y ∈ T := by
    intro y hy
    by_contra hyT
    have hyR : y ∈ R := mem_sdiff.2 ⟨mem_univ _, hyT⟩
    have h1 := hu2 y hyR
    have h2 := hr2 y (by rw [h1]; exact (χ y).2)
    rw [h2, h1] at hy
    exact absurd hy (ne_of_lt (χ y).2)
  have hsmall : ∀ C : Finset (Fin G.1), (∀ y ∈ C, c₂.getD y k = k) → C.Nonempty →
      ConnSet G.2 C → (∀ x ∈ C, ∀ y : Fin G.1, G.2.Adj x y → c₂.getD y k = k → y ∈ C) →
      k ^ C.card ≤ G.1 * G.1 := by
    intro C hCU hCne hCconn hCcl
    by_contra hbig
    push Not at hbig
    have hbig' : H.1 ^ 2 < k ^ C.card := by rw [sq]; exact hbig
    have hCT : C ⊆ T := fun y hy ↦ hU2 y (hCU y hy)
    have hCβ : (C.card : ℝ) ≤ betaF k * H.1 :=
      le_trans (by exact_mod_cast card_le_card hCT) hT
    refine hstuck C hCne (hCconn.mono fun u v h ↦ h.1) hCβ hbig' fun v hv ↦ ?_
    obtain ⟨a, hav, hmiss⟩ := hr4 v (hCU v hv)
    refine ⟨a, hav, fun y hvy hyC hya ↦ ?_⟩
    have hGa : G.2.Adj v y := ⟨hvy, by rw [hya]; exact Ne.symm hav⟩
    have hyU : c₂.getD y k ≠ k := fun h ↦ hyC (hCcl v hv y hGa h)
    have hylt := lt_of_le_of_ne (hr3 y) hyU
    have := hr1 y hylt
    exact hmiss y hGa (by rw [this, hya])
  -- brute force and the rounding
  obtain ⟨hb1, hb2⟩ := brute_spec (G := G) χ hproper c₂ hr1 hr3 hsmall
  exact (numColored_pipeline (G := G) _ hb1 hb2).2

/-! ### Theorem 7.17 on one good coloring -/

open Classical in
/-- **Theorem 7.17 on one good coloring.** -/
theorem isColoring_full (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (hd : fullD k ≤ d) (hexp : H.numEigGT (lamF k) ≤ 1) (χ : Fin H.1 → Fin k)
    (hn : minN k ≤ H.1) (hgood : Good (fun x y ↦ H.normAdj x y) χ)
    (hbad : ((badSet H d χ).card : ℝ) ≤ alphaF k * H.1)
    (hstuck : ∀ S : Finset (Fin H.1), S.Nonempty → ConnSet H.2 S →
      (S.card : ℝ) ≤ betaF k * H.1 → H.1 ^ 2 < k ^ S.card → ¬ Stuck H S χ) :
    (H.plant χ).IsColoring k 0
      (fullAlg (fullParams k) ((H.plant χ).1, adjTable (H.plant χ))) := by
  have hk0 : 0 < k := by omega
  have hfullD : 1 ≤ fullD k := Nat.one_le_pow _ _ (by positivity)
  have hd1 : 1 ≤ d := le_trans hfullD hd
  have hd0 : d ≠ 0 := by omega
  have hmin : 1 ≤ minN k := Nat.one_le_pow _ _ (by positivity)
  have hn0 : 0 < H.1 := by omega
  have hnR : (0 : ℝ) < H.1 := by exact_mod_cast hn0
  have hdn : d ≤ H.1 := by
    have := H.2.degree_lt_card_verts ⟨0, hn0⟩
    rw [hreg, Fintype.card_fin] at this
    exact this.le
  have hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ 1 := by
    refine le_trans (card_le_card fun i hi ↦ ?_) hexp
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_lt_of_le (lamF_lt_lamP hk0) hi.2⟩
  -- the candidate of the list
  have hK : 0 < fullK k := by unfold fullK; positivity
  obtain ⟨us, hus0, ts, h2E0⟩ := exists_good_candidate hk hK 1 H hreg hd1 hrank χ hn hgood
  set G := plantG H χ with hG
  have hus : ∀ j, us j ∈ Alg.expNet (planParams k (fullK k) 1).2 (G.1, adjTable G) := hus0
  set cs := Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt H.1) (List.ofFn fun j ↦ (ts j : ℕ))
    with hcs
  set q := Alg.clustersC H.1 (List.ofFn us) cs with hq
  have hqv : ∀ y : Fin H.1, q.getD y k = Alg.clusterIdxC (List.ofFn us) cs y :=
    fun y ↦ Alg.getD_clustersC _ _ y.2 k
  have hqk : ∀ y : Fin H.1, q.getD y k < k := fun y ↦ by
    rw [hqv]
    have := Alg.clusterIdxC_lt (List.ofFn us) cs (by rw [hcs, Alg.length_gridCenters]; exact hk0) y
    rwa [hcs, Alg.length_gridCenters] at this
  set B : Finset (Fin H.1) := univ.filter fun y : Fin H.1 ↦ q.getD y k ≠ χ y with hBdef
  have hBcard : B.card = (univ.filter fun y : Fin (H.plant χ).1 ↦ Alg.clusterIdxC (List.ofFn us)
      (Alg.gridCenters k (gridS k) (gridK k) (Nat.sqrt (H.plant χ).1)
        (List.ofFn fun j ↦ (ts j : ℕ))) y ≠ (χ y : ℕ)).card := by
    refine card_bij (fun y _ ↦ y) (fun y hy ↦ ?_) (fun _ _ _ _ h ↦ h) (fun y hy ↦ ⟨y, ?_, rfl⟩)
    · have := (mem_filter.1 hy).2
      rw [hqv] at this
      exact mem_filter.2 ⟨mem_univ _, this⟩
    · have := (mem_filter.1 hy).2
      exact mem_filter.2 ⟨mem_univ _, fun h ↦ this ((hqv y).symm.trans h)⟩
  have hB : (B.card : ℝ) ≤ alphaF k * H.1 := by
    have h1 : 2 * (B.card : ℝ) ≤ (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) +
        65536 * (k : ℝ) ^ 4 / ((fullK k : ℕ) : ℝ) ^ 2) * H.1 := by
      rw [hBcard]; exact h2E0
    rw [K_term_eq hk0] at h1
    have h2 := errB_div_le_alphaF hk0 hd
    have h4 : (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + alphaF k) * H.1 ≤
        (alphaF k + alphaF k) * H.1 := mul_le_mul_of_nonneg_right (by linarith) hnR.le
    linarith
  -- the set `T`, and the steps
  obtain ⟨T, hBT, hT, hTdeg⟩ := exists_T hk H hreg hd0 hexp χ B hB hbad
  have hpipe := pipeline_good hk H hreg hd0 hexp χ q hqk T hBT hB hT hTdeg hstuck
  -- the list and the selection
  have hB1 : (Alg.expNet (planParams k (fullK k) 1).2 (G.1, adjTable G)).length ^ k ≤
      ((3 + 12 * fullK k) ^ numT k 1 + 1) ^ k + (2 * gridK k + 1) ^ (k * k) :=
    (Nat.pow_le_pow_left (Alg.length_expNet_le _ _) k).trans (Nat.le_add_right _ _)
  have hqmem := mem_clusterList G.1 k (gridS k) (gridK k) _ _ us hus ts hB1 (Nat.le_add_left _ _)
  obtain ⟨hpart, hnum⟩ := fullAlg_spec hk0 G q d hqmem hdn
  have hres : G.IsColoring k 0 (fullAlg (planParams k (fullK k) 1) (G.1, adjTable G)) := by
    refine ⟨hpart, ?_⟩
    rw [sub_zero, one_mul]
    exact_mod_cast hpipe.trans hnum
  exact hres

end Planted

end BHSV25
