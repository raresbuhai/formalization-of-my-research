module

public import BHSV25.Alg.Partition
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Theorem 1.3: the analysis of the clustering algorithm

The analysis of [BHSV25, Theorem 7.9] for `3` colors, in the qualitative form of Theorem 1.3:
for every `λ > 0` there is a polynomial-time net (`BHSV25.Net.exists_absNet`) for which the
clustering algorithm with `3` clusters (`BHSV25.Alg.clusterAlg 3 3`) colors all but
`f λ · n = 32 λ^{1/16} n` vertices of every regular `λ`-one-sided expander that has a
`(3, λ)`-coloring whose classes have at most `(1/2 - f λ) n` vertices each
(`BHSV25.Alg.three_exists_net`). The loss is `BHSV25.Alg.threeLoss`.

Write `λ = s³²`, `g = 32 s²` (the loss), and let `χ` put every vertex in its color class, and the
uncolored ones (at most `λ n`) in the class `0`.

* **Few edges inside the parts**: the uncolored vertices cover them, so the weight inside the
  parts is at most `2 λ n` (`BHSV25.Alg.intWt_le_of_cover`).
* **Large parts**: every part has at most `(1/2 - g + λ) n` vertices, hence at least
  `(2 g - 2 λ) n ≥ g n` (`BHSV25.Alg.three_card_part_ge`).
* **Separated rows** (the claim in the proof of Theorem 7.9): the computation of Lemmas 7.7 and
  7.8, done directly on the model `M`, whose diagonal is small rather than `0`. With
  `E_ab = |V_a| M_ab`, which is symmetric with row sums `|V_a|`, the three parts `a, b, c` satisfy
  `2 E_ab = |V_a| + |V_b| - |V_c| - E_aa - E_bb + E_cc`, so `M_ab ≥ g - 2 λ` for `a ≠ b`, while
  `M_bb ≤ 2 λ / g`; hence `‖M_a - M_b‖ ≥ g / 2` (`BHSV25.Alg.three_rowSep`).
* **Recovering the partition** (Theorem 5.1, `BHSV25.Alg.exists_good_candidate`) with
  `L = s¹⁶ = √λ` as the upper bound on the second eigenvalue, `ε₀ = 2 λ`, `c = g`, `α = g / 2`,
  a rational `θ ∈ (s³, 2 s³)` and `τ = 2 θ`: some candidate of the algorithm agrees with `χ` on all
  but `16 s⁴ n` vertices. The net (of precision `κ / n` for a rational `κ ∈ (0, s² / 128)`) covers
  the span of the eigenvectors with `|μ| ≥ θ`, since there are at most `1 + 4 / (θ/2)⁴`
  eigenvalues with `|μ| ≥ θ / 2` (`BHSV25.Alg.card_abs_eig_ge_le`).
* **Rounding** (`BHSV25.Alg.clusterAlg_spec`, Lemma 7.24, with the color classes as the
  independent sets): every vertex that is colored and correctly clustered counts, and every other
  one costs at most `2` (`BHSV25.Alg.three_sub_le_sum_max`), so all but
  `2 (16 s⁴ + λ) n ≤ g n` vertices are colored.

Regular graphs of degree `0` have no edges, and any candidate colors all vertices
(`BHSV25.Alg.three_numColored_of_degree_zero`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Filter Topology Turing.MultiTapeTM Matrix

/-! ### Counting the colored vertices -/

section Counting

variable (G : Graph)

/-- **Accounting with a set of exceptions**: if every vertex outside `S` lies in the independent
set `I_a` of its part `a`, then `∑_a max(0, |R_a ∩ I_a| - |R_a \ I_a|) ≥ n - 2 |S|`. -/
theorem three_sub_le_sum_max {m : ℕ} (p : List ℕ) (hp : ∀ v : Fin G.1, p.getD v m < m)
    (I : ℕ → Finset (Fin G.1)) (S : Finset (Fin G.1)) (hS : ∀ v, v ∉ S → v ∈ I (p.getD v m)) :
    (G.1 : ℝ) - 2 * S.card ≤ ∑ a ∈ range m, max 0
      (((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card) := by
  have hdisj : (↑(range m) : Set ℕ).PairwiseDisjoint (classSet G m p) := by
    intro a _ b _ hab
    refine disjoint_left.2 fun v hva hvb ↦ hab ?_
    rw [classSet, mem_filter] at hva hvb
    exact hva.2.symm.trans hvb.2
  have hdisj' : (↑(range m) : Set ℕ).PairwiseDisjoint (fun a ↦ classSet G m p a \ I a) :=
    hdisj.mono fun a ↦ sdiff_subset
  have hR : ∑ a ∈ range m, ((classSet G m p a).card : ℝ) = G.1 := by
    rw [← Nat.cast_sum, ← card_biUnion hdisj]
    have : (range m).biUnion (classSet G m p) = univ := by
      ext v
      simp only [mem_biUnion, mem_range, classSet, mem_filter, mem_univ, true_and, iff_true]
      exact ⟨_, hp v, rfl⟩
    rw [this, card_univ, Fintype.card_fin]
  have hD : ∑ a ∈ range m, ((classSet G m p a \ I a).card : ℝ) ≤ S.card := by
    rw [← Nat.cast_sum, ← card_biUnion hdisj']
    refine Nat.cast_le.2 (card_le_card fun v hv ↦ ?_)
    rw [mem_biUnion] at hv
    obtain ⟨a, -, hv⟩ := hv
    obtain ⟨hv1, hv2⟩ := mem_sdiff.1 hv
    rw [classSet, mem_filter] at hv1
    by_contra hvS
    have := hS v hvS
    rw [hv1.2] at this
    exact hv2 this
  have hsplit : ∀ a, ((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card =
      (classSet G m p a).card - 2 * (classSet G m p a \ I a).card := by
    intro a
    have h' : ((classSet G m p a ∩ I a).card : ℝ) + (classSet G m p a \ I a).card =
        (classSet G m p a).card := by exact_mod_cast card_inter_add_card_sdiff _ _
    linarith only [h']
  calc (G.1 : ℝ) - 2 * S.card ≤ ∑ a ∈ range m, (((classSet G m p a).card : ℝ) -
        2 * (classSet G m p a \ I a).card) := by
        rw [sum_sub_distrib, ← mul_sum, hR]
        linarith only [hD]
    _ = ∑ a ∈ range m, (((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card) :=
        sum_congr rfl fun a _ ↦ (hsplit a).symm
    _ ≤ _ := sum_le_sum fun a _ ↦ le_max_right _ _

end Counting

/-! ### Partitions into three parts -/

section Three

variable {G : Graph}

/-- For two of the three parts, the third one. -/
theorem three_exists_third {a b : Fin 3} (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ ∀ f : Fin 3 → ℝ, ∑ j, f j = f a + f b + f c := by
  have key : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b := by decide
  have hcov : ∀ a b c x : Fin 3, a ≠ b → c ≠ a → c ≠ b → x = a ∨ x = b ∨ x = c := by decide
  obtain ⟨c, hca, hcb⟩ := key a b hab
  refine ⟨c, hca, hcb, fun f ↦ ?_⟩
  have huniv : (univ : Finset (Fin 3)) = {a, b, c} := by
    ext x
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact hcov a b c x hab hca hcb
  rw [huniv, sum_insert (by simp [hab, hca.symm]), sum_insert (by simp [hcb.symm]),
    sum_singleton, add_assoc]

/-- If every part has at most `B` vertices, every part has at least `n - 2 B`. -/
theorem three_card_part_ge (χ : Fin G.1 → Fin 3) {B : ℝ}
    (hup : ∀ a, ((part G χ a).card : ℝ) ≤ B) (a : Fin 3) :
    G.1 - 2 * B ≤ (part G χ a).card := by
  have h1 := sum_card_part (G := G) χ
  rw [← add_sum_erase _ _ (mem_univ a)] at h1
  have h2 : ∑ x ∈ univ.erase a, ((part G χ x).card : ℝ) ≤ ∑ _x ∈ univ.erase a, B :=
    sum_le_sum fun x _ ↦ hup x
  rw [sum_const, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h2
  have h3 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h3] at h2
  linarith only [h1, h2]

open Classical in
/-- **Separated rows** (the claim in the proof of [BHSV25, Theorem 7.9]): if the three parts have
between `g n` and `(1/2 - g + λ) n` vertices and weight at most `2 λ n` inside them, then the rows
of the model are `g / 2`-separated, provided `2 λ + 2 λ / g ≤ g / 2`. -/
theorem three_rowSep {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) (hn : 0 < G.1)
    (χ : Fin G.1 → Fin 3) {g lam : ℝ} (hg : 0 < g) (hlam0 : 0 ≤ lam) (hgl : 2 * lam ≤ g)
    (hup : ∀ a, ((part G χ a).card : ℝ) ≤ (1 / 2 - g + lam) * G.1)
    (hlow : ∀ a, g * G.1 ≤ (part G χ a).card)
    (hint : intWt G χ ≤ 2 * lam * G.1) (hcond : 2 * lam + 2 * lam / g ≤ g / 2) (a b : Fin 3)
    (hab : a ≠ b) : (g / 2) ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 := by
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  obtain ⟨c, -, -, hsum⟩ := three_exists_third hab
  set E : Fin 3 → Fin 3 → ℝ := fun x y ↦ ∑ v ∈ part G χ x, wt G χ v y with hE
  have hrow : ∀ x, ∑ y, E x y = (part G χ x).card := by
    intro x
    simp only [hE]
    rw [sum_comm]
    simp [sum_wt h hd χ]
  have hsym : ∀ x y, E x y = E y x := fun x y ↦ sum_wt_comm χ x y
  have hdiag : ∑ x, E x x = intWt G χ := by
    rw [intWt, ← sum_part χ]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun v hv ↦ ?_
    rw [mem_part.1 hv]
  have hnn : ∀ x y, 0 ≤ E x y := fun x y ↦ sum_nonneg fun v _ ↦ wt_nonneg χ v y
  have hcard := sum_card_part (G := G) χ
  have hRa := hrow a
  have hRb := hrow b
  have hRc := hrow c
  rw [hsum] at hRa hRb hRc hdiag hcard
  have hsab := hsym a b
  have hsac := hsym a c
  have hsbc := hsym b c
  have hupc := hup c
  have hcc := hnn c c
  have haa := hnn a a
  -- the weight between `a` and `b`
  have hEab : (g - 2 * lam) * G.1 ≤ E a b := by
    linarith only [hRa, hRb, hRc, hdiag, hcard, hsab, hsac, hsbc, hupc, hcc, hint]
  -- the entries of the model
  have hpa : (0 : ℝ) < (part G χ a).card := lt_of_lt_of_le (mul_pos hg hnR) (hlow a)
  have hpb : (0 : ℝ) < (part G χ b).card := lt_of_lt_of_le (mul_pos hg hnR) (hlow b)
  have hpan : ((part G χ a).card : ℝ) ≤ G.1 := by
    have h1 := Nat.cast_nonneg (α := ℝ) (part G χ b).card
    have h2 := Nat.cast_nonneg (α := ℝ) (part G χ c).card
    linarith only [hcard, h1, h2]
  have hMab : g - 2 * lam ≤ pmodel G χ a b := by
    change g - 2 * lam ≤ E a b / (part G χ a).card
    rw [le_div_iff₀ hpa]
    have := mul_le_mul_of_nonneg_left hpan (by linarith only [hgl] : (0 : ℝ) ≤ g - 2 * lam)
    linarith only [this, hEab]
  have hMbb : pmodel G χ b b ≤ 2 * lam / g := by
    change E b b / (part G χ b).card ≤ 2 * lam / g
    rw [div_le_iff₀ hpb]
    have hEbb : E b b ≤ 2 * lam * G.1 := by
      have := hnn b b
      linarith only [hdiag, haa, hcc, hint]
    have hlam : 0 ≤ 2 * lam / g := by positivity
    have h1 := mul_le_mul_of_nonneg_left (hlow b) hlam
    have h2 : 2 * lam / g * (g * G.1) = 2 * lam * G.1 := by field_simp
    linarith only [h1, h2, hEbb]
  have hdiff : g / 2 ≤ pmodel G χ a b - pmodel G χ b b := by linarith only [hMab, hMbb, hcond]
  calc (g / 2) ^ 2 ≤ (pmodel G χ a b - pmodel G χ b b) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdiff 2
    _ ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 :=
        single_le_sum (f := fun j ↦ (pmodel G χ a j - pmodel G χ b j) ^ 2)
          (fun j _ ↦ sq_nonneg _) (mem_univ b)

end Three

/-! ### The clustering algorithm on balanced `3`-colorable expanders -/

section Main

variable (G : Graph)

/-- The class `a` of a partial `3`-coloring `c` (empty for `a ≥ 3`). -/
def threeClass (c : List ℕ) (a : ℕ) : Finset (Fin G.1) :=
  univ.filter fun v ↦ G.color 3 c v = a ∧ G.color 3 c v < 3

theorem isIndepSet_threeClass {c : List ℕ} (hc : G.IsPartialColoring 3 c) (a : ℕ) :
    G.2.IsIndepSet (threeClass G c a : Set (Fin G.1)) := by
  intro u hu v hv _ huv
  rw [mem_coe, threeClass, mem_filter] at hu hv
  exact hc u v huv hu.2.2 (hu.2.1.trans hv.2.1.symm)

theorem card_threeClass (c : List ℕ) {a : ℕ} (ha : a < 3) :
    (threeClass G c a).card = G.classSize 3 c a := by
  rw [threeClass, Graph.classSize]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨And.left, fun h ↦ ⟨h, h ▸ ha⟩⟩

open Classical in
/-- **Without edges**, the algorithm colors all vertices: every candidate does, with the
independent sets `I_a` of all vertices. -/
theorem three_numColored_of_degree_zero (hd : G.2.IsRegularOfDegree 0) (hn : 0 < G.1)
    (net : ℕ × List Bool → List (List ℚ)) {u : List ℚ} (hu : u ∈ net (G.1, adjTable G)) :
    (G.1 : ℝ) ≤ G.numColored 3 (clusterAlg 3 3 net (G.1, adjTable G)) := by
  have hI : ∀ _a : ℕ, G.2.IsIndepSet ((univ : Finset (Fin G.1)) : Set (Fin G.1)) := by
    intro _ v _ w _ _ hadj
    have h := hd v
    rw [SimpleGraph.degree, Finset.card_eq_zero] at h
    have hw : w ∈ G.2.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
    rw [h] at hw
    exact Finset.notMem_empty w hw
  have hspec := (clusterAlg_spec G (m := 3) (K := 3) (by norm_num) le_rfl net).2
    (fun _ ↦ u) (fun _ ↦ hu) (fun _ ↦ ⟨0, hn⟩) (fun _ ↦ univ) hI
  have hp : ∀ v : Fin G.1, (clusters G.1 (List.ofFn fun _ : Fin 3 ↦ u)
      (List.ofFn fun _ : Fin 3 ↦ ((⟨0, hn⟩ : Fin G.1) : ℕ))).getD v 3 < 3 := by
    intro v
    rw [getD_clusters _ _ v.2]
    simpa using clusterIdx_lt (List.ofFn fun _ : Fin 3 ↦ u)
      (xs := List.ofFn fun _ : Fin 3 ↦ ((⟨0, hn⟩ : Fin G.1) : ℕ)) (by simp) v
  have hcount := three_sub_le_sum_max G _ hp (fun _ ↦ univ) ∅ fun v _ ↦ mem_univ v
  rw [card_empty, Nat.cast_zero, mul_zero, sub_zero] at hcount
  exact hcount.trans hspec

open Classical in
/-- **The analysis for graphs with edges**, for `λ = s³²`, with a rational `θ ∈ (s³, 2 s³)` and a
rational `κ ∈ (0, s² / 128)`, given that the net covers the span of the eigenvectors with
`|μ| ≥ θ` within `κ / n`. -/
theorem three_numColored_ge_of_pos {d : ℕ} (hreg : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    (hn : 0 < G.1) {s : ℝ} (hs0 : 0 < s) (hs1 : 32 * s ^ 2 < 1)
    (hexp : G.numEigGT (s ^ 32) ≤ 1) {θ κ : ℚ} (hθ1 : s ^ 3 < θ) (hθ2 : (θ : ℝ) < 2 * s ^ 3)
    (hκ1 : (0 : ℝ) < κ) (hκ2 : (κ : ℝ) < s ^ 2 / 128) (net : ℕ × List Bool → List (List ℚ))
    (hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ (θ : ℝ) ≤ |μ|) w →
      ∃ u ∈ net (G.1, adjTable G),
        (Net.vecOf G.1 u - w) ⬝ᵥ (Net.vecOf G.1 u - w) ≤ (κ / G.1) ^ 2)
    (c₀ : List ℕ) (hc₀ : G.IsColoring 3 (s ^ 32) c₀)
    (hsize : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - 32 * s ^ 2) * G.1) :
    (1 - 32 * s ^ 2) * G.1 ≤ G.numColored 3 (clusterAlg 3 3 net (G.1, adjTable G)) := by
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  -- facts about `s`
  have hs2 : s ^ 2 < 1 / 32 := by linarith only [hs1]
  have hslt : s < 1 := by nlinarith only [hs2, hs0]
  have hpow : ∀ {i j : ℕ}, i ≤ j → s ^ j ≤ s ^ i := fun h ↦
    pow_le_pow_of_le_one hs0.le hslt.le h
  have hs3 : 0 < s ^ 3 := pow_pos hs0 3
  have hθ0 : (0 : ℝ) < θ := hs3.trans hθ1
  -- the uncolored vertices
  set U₀ := univ.filter fun v : Fin G.1 ↦ ¬ G.color 3 c₀ v < 3 with hU₀
  have hU₀card : (U₀.card : ℝ) ≤ s ^ 32 * G.1 := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin G.1)))
      (fun v ↦ G.color 3 c₀ v < 3)
    rw [card_univ, Fintype.card_fin] at h1
    have h2 := hc₀.2
    rw [Graph.numColored] at h2
    have h1' : ((univ.filter fun v ↦ G.color 3 c₀ v < 3).card : ℝ) + U₀.card = G.1 := by
      exact_mod_cast h1
    linarith only [h1', h2]
  -- the partition into the color classes, the uncolored vertices in the class `0`
  set χ : Fin G.1 → Fin 3 := fun v ↦ if h : G.color 3 c₀ v < 3 then ⟨_, h⟩ else 0 with hχ
  have hχval : ∀ v, G.color 3 c₀ v < 3 → (χ v : ℕ) = G.color 3 c₀ v := by
    intro v h
    simp [hχ, h]
  have hcover : ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ U₀ ∨ v ∈ U₀ := by
    intro u v huv he
    by_cases hu : G.color 3 c₀ u < 3
    · by_cases hv : G.color 3 c₀ v < 3
      · exact (hc₀.1 u v huv hu (by rw [← hχval u hu, ← hχval v hv, he])).elim
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, hv⟩)
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, hu⟩)
  have hint : intWt G χ ≤ 2 * s ^ 32 * G.1 := by
    have := intWt_le_of_cover hreg χ U₀ hcover
    linarith only [this, hU₀card]
  -- the sizes of the parts
  have hup : ∀ a, ((part G χ a).card : ℝ) ≤ (1 / 2 - 32 * s ^ 2 + s ^ 32) * G.1 := by
    intro a
    have hsub : part G χ a ⊆ (univ.filter fun v ↦ G.color 3 c₀ v = a) ∪ U₀ := by
      intro v hv
      rw [mem_part] at hv
      rw [mem_union]
      by_cases h : G.color 3 c₀ v < 3
      · exact Or.inl (mem_filter.2 ⟨mem_univ _, by rw [← hχval v h, hv]⟩)
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, h⟩)
    have h1 : ((part G χ a).card : ℝ) ≤
        (univ.filter fun v ↦ G.color 3 c₀ v = a).card + U₀.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have h2 := hsize a a.2
    rw [Graph.classSize] at h2
    linarith only [h1, h2, hU₀card]
  have hgl : 2 * s ^ 32 ≤ 32 * s ^ 2 := by
    have := hpow (show 2 ≤ 32 by norm_num)
    linarith only [this, pow_pos hs0 2]
  have hlow : ∀ a, 32 * s ^ 2 * G.1 ≤ (part G χ a).card := by
    intro a
    have h1 := three_card_part_ge χ hup a
    have h2 : 0 ≤ (32 * s ^ 2 - 2 * s ^ 32) * G.1 := mul_nonneg (by linarith only [hgl]) hnR.le
    linarith only [h1, h2]
  -- separated rows
  have hcond : 2 * s ^ 32 + 2 * s ^ 32 / (32 * s ^ 2) ≤ 32 * s ^ 2 / 2 := by
    have e : 2 * s ^ 32 / (32 * s ^ 2) = s ^ 30 / 16 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      ring
    rw [e]
    have h1 := hpow (show 2 ≤ 30 by norm_num)
    have h2 := hpow (show 2 ≤ 32 by norm_num)
    linarith only [h1, h2, pow_pos hs0 2]
  have hsep : ∀ a b, a ≠ b →
      (32 * s ^ 2 / 2) ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 :=
    fun a b hab ↦ three_rowSep hreg hd hn χ (by positivity) (by positivity) hgl hup hlow hint
      hcond a b hab
  -- the spectrum
  have hL0 : 0 < s ^ 16 := pow_pos hs0 16
  have hL1 : s ^ 16 < 1 := pow_lt_one₀ hs0.le hslt (by norm_num)
  have hexpL : G.numEigGT (s ^ 16) ≤ 1 := by
    unfold Graph.numEigGT at hexp ⊢
    refine le_trans (card_le_card fun i hi ↦ ?_) hexp
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_le_of_lt (hpow (show 16 ≤ 32 by norm_num)) hi.2⟩
  -- the parameters
  have hθsq1 : s ^ 6 < (θ : ℝ) ^ 2 := by
    have := pow_lt_pow_left₀ hθ1 hs3.le two_ne_zero
    rwa [← pow_mul] at this
  have hθsq2 : (θ : ℝ) ^ 2 < 4 * s ^ 6 := by
    have := pow_lt_pow_left₀ hθ2 hθ0.le two_ne_zero
    have e : (2 * s ^ 3) ^ 2 = 4 * s ^ 6 := by ring
    rwa [e] at this
  have hτ : (2 * (θ : ℝ)) ^ 2 * (2 / (32 * s ^ 2)) ≤ (32 * s ^ 2 / 2) ^ 2 / 2 := by
    have e1 : (2 * (θ : ℝ)) ^ 2 * (2 / (32 * s ^ 2)) = θ ^ 2 / (4 * s ^ 2) := by
      rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
      ring
    have e2 : (32 * s ^ 2 / 2) ^ 2 / 2 = 128 * s ^ 4 := by ring
    rw [e1, e2, div_le_iff₀ (by positivity)]
    have e3 : 128 * s ^ 4 * (4 * s ^ 2) = 512 * s ^ 6 := by ring
    rw [e3]
    linarith only [hθsq2, pow_pos hs0 6]
  have hκ : 512 * ((3 : ℕ) : ℝ) ^ 2 * (κ : ℝ) ^ 2 < (32 * s ^ 2 / 2) ^ 2 := by
    have h1 : (κ : ℝ) ^ 2 < (s ^ 2 / 128) ^ 2 := pow_lt_pow_left₀ hκ2 hκ1.le two_ne_zero
    have e1 : (s ^ 2 / 128) ^ 2 = s ^ 4 / 16384 := by ring
    have e2 : (32 * s ^ 2 / 2) ^ 2 = 256 * s ^ 4 := by ring
    rw [e1] at h1
    rw [e2]
    push_cast
    linarith only [h1, pow_pos hs0 4]
  have hEval : 512 * ((3 : ℕ) : ℝ) ^ 4 * (2 * s ^ 32 / s ^ 16 + s ^ 16) /
      (32 * s ^ 2 * (2 * (θ : ℝ) - θ) ^ 2 * (32 * s ^ 2 / 2) ^ 2) ≤ 16 * s ^ 4 := by
    have e1 : 2 * s ^ 32 / s ^ 16 = 2 * s ^ 16 := by
      rw [div_eq_iff (by positivity)]
      ring
    have e2 : 32 * s ^ 2 * (2 * (θ : ℝ) - θ) ^ 2 * (32 * s ^ 2 / 2) ^ 2 =
        8192 * s ^ 6 * θ ^ 2 := by ring
    rw [e1, e2, div_le_iff₀ (by positivity)]
    have h1 : s ^ 10 * s ^ 6 ≤ s ^ 10 * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hθsq1.le (by positivity)
    have e3 : 512 * ((3 : ℕ) : ℝ) ^ 4 * (2 * s ^ 16 + s ^ 16) = 124416 * (s ^ 10 * s ^ 6) := by
      push_cast
      ring
    have e4 : 16 * s ^ 4 * (8192 * s ^ 6 * θ ^ 2) = 131072 * (s ^ 10 * θ ^ 2) := by ring
    rw [e3, e4]
    have h2 : 0 ≤ s ^ 10 * s ^ 6 := by positivity
    linarith only [h1, h2]
  have hE : 512 * ((3 : ℕ) : ℝ) ^ 4 * (2 * s ^ 32 / s ^ 16 + s ^ 16) /
      (32 * s ^ 2 * (2 * (θ : ℝ) - θ) ^ 2 * (32 * s ^ 2 / 2) ^ 2) < 32 * s ^ 2 := by
    refine lt_of_le_of_lt hEval ?_
    have := hpow (show 2 ≤ 4 by norm_num)
    linarith only [this, pow_pos hs0 2]
  -- Theorem 5.1: a good candidate
  obtain ⟨us, hus, xs, hB⟩ := exists_good_candidate hreg hd χ (Equiv.refl (Fin 3)) hn
    (by positivity) hlow (by positivity) hsep hL0 hL1 hexpL hint
    (by linarith only [hθ0] : (θ : ℝ) < 2 * θ) hτ (net (G.1, adjTable G)) hnet hκ hE
  obtain ⟨B, hBcard, hBmem⟩ : ∃ B : Finset (Fin G.1), (B.card : ℝ) ≤ 16 * s ^ 4 * G.1 ∧
      ∀ v, v ∉ B → clusterIdx (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ)) v = (χ v : ℕ) :=
    ⟨_, hB.trans (mul_le_mul_of_nonneg_right hEval hnR.le), fun v hv ↦ by simpa using hv⟩
  -- the rounding
  have hp : ∀ v : Fin G.1,
      (clusters G.1 (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ))).getD v 3 < 3 := by
    intro v
    rw [getD_clusters _ _ v.2]
    simpa using clusterIdx_lt (List.ofFn us) (xs := List.ofFn fun j ↦ (xs j : ℕ)) (by simp) v
  have hS : ∀ v, v ∉ B ∪ U₀ → v ∈ threeClass G c₀
      ((clusters G.1 (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ))).getD v 3) := by
    intro v hv
    rw [mem_union, not_or] at hv
    have h1 : G.color 3 c₀ v < 3 := by
      by_contra h
      exact hv.2 (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [getD_clusters _ _ v.2, hBmem v hv.1, hχval v h1]
    exact mem_filter.2 ⟨mem_univ _, rfl, h1⟩
  have hspec := (clusterAlg_spec G (m := 3) (K := 3) (by norm_num) le_rfl net).2 us hus xs
    (threeClass G c₀) (isIndepSet_threeClass G hc₀.1)
  have hcount := three_sub_le_sum_max G _ hp (threeClass G c₀) (B ∪ U₀) hS
  have hunion : ((B ∪ U₀).card : ℝ) ≤ B.card + U₀.card := by
    exact_mod_cast card_union_le _ _
  have hcoef : 32 * s ^ 4 + 2 * s ^ 32 ≤ 32 * s ^ 2 := by
    have h1 := hpow (show 4 ≤ 32 by norm_num)
    have h2 : s ^ 4 ≤ s ^ 2 * (1 / 32) := by
      have e : s ^ 4 = s ^ 2 * s ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hs2.le (by positivity)
    linarith only [h1, h2, pow_pos hs0 2]
  have hfin := mul_le_mul_of_nonneg_right hcoef hnR.le
  linarith only [hspec, hcount, hunion, hBcard, hU₀card, hfin]

open Classical in
/-- **The analysis** (all regular graphs), for `λ = s³²` with `32 s² < 1`. -/
theorem three_numColored_ge {d : ℕ} (hreg : G.2.IsRegularOfDegree d) {s : ℝ} (hs0 : 0 < s)
    (hs1 : 32 * s ^ 2 < 1) (hexp : G.numEigGT (s ^ 32) ≤ 1) {θ κ : ℚ} (hθ1 : s ^ 3 < θ)
    (hθ2 : (θ : ℝ) < 2 * s ^ 3) (hκ1 : (0 : ℝ) < κ) (hκ2 : (κ : ℝ) < s ^ 2 / 128)
    (net : ℕ × List Bool → List (List ℚ))
    (hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ (θ : ℝ) ≤ |μ|) w →
      ∃ u ∈ net (G.1, adjTable G),
        (Net.vecOf G.1 u - w) ⬝ᵥ (Net.vecOf G.1 u - w) ≤ (κ / G.1) ^ 2)
    (c₀ : List ℕ) (hc₀ : G.IsColoring 3 (s ^ 32) c₀)
    (hsize : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - 32 * s ^ 2) * G.1) :
    (1 - 32 * s ^ 2) * G.1 ≤ G.numColored 3 (clusterAlg 3 3 net (G.1, adjTable G)) := by
  rcases Nat.eq_zero_or_pos G.1 with hn | hn
  · have h0 : (G.1 : ℝ) = 0 := by exact_mod_cast hn
    rw [h0, mul_zero]
    exact Nat.cast_nonneg _
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    obtain ⟨u, hu, -⟩ := hnet 0 (by simp) (by intro i _; simp [Spectral.coeff])
    have h := three_numColored_of_degree_zero G hreg hn net hu
    have h2 : 0 ≤ 32 * s ^ 2 * (G.1 : ℝ) := by positivity
    linarith only [h, h2]
  · exact three_numColored_ge_of_pos G hreg hd hn hs0 hs1 hexp hθ1 hθ2 hκ1 hκ2 net hnet c₀ hc₀
      hsize

end Main

/-! ### The parameters -/

/-- `λ^{1/32}`. -/
noncomputable def threeRoot (lam : ℝ) : ℝ := lam ^ ((32 : ℕ) : ℝ)⁻¹

/-- **The loss of Theorem 1.3**: `32 λ^{1/16}`. -/
noncomputable def threeLoss (lam : ℝ) : ℝ := 32 * threeRoot lam ^ 2

theorem threeLoss_nonneg (lam : ℝ) : 0 ≤ threeLoss lam := by
  unfold threeLoss
  positivity

theorem tendsto_threeLoss : Tendsto threeLoss (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto threeRoot (𝓝 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 ((32 : ℕ) : ℝ)⁻¹ (Or.inr (by positivity))
    rw [ContinuousAt, Real.zero_rpow (by positivity)] at this
    exact this
  have h2 : Tendsto threeLoss (𝓝 0) (𝓝 0) := by
    have := (h.pow 2).const_mul 32
    rw [zero_pow two_ne_zero, mul_zero] at this
    exact this
  exact h2.mono_left nhdsWithin_le_nhds

/-- **The guarantee of the clustering algorithm with `3` clusters** [BHSV25, Theorem 7.9]: for
every `λ > 0`, a polynomial-time net for which the algorithm colors all but `32 λ^{1/16} n`
vertices of every regular `λ`-one-sided expander with a `(3, λ)`-coloring whose classes have at
most `(1/2 - 32 λ^{1/16}) n` vertices each. (Its output is always a partial `3`-coloring,
`BHSV25.Alg.clusterAlg_spec`.) -/
theorem three_exists_net {lam : ℝ} (h0 : 0 < lam) :
    ∃ net : ℕ × List Bool → List (List ℚ),
      ComputableInPolyTime net (Encoding.encPair Encoding.encNat Encoding.encBits)
        (Encoding.encList (Encoding.encList Encoding.encRat)) ∧
      ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → ∀ c₀ : List ℕ,
        G.IsColoring 3 lam c₀ →
        (∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - threeLoss lam) * G.1) →
        (1 - threeLoss lam) * G.1 ≤ G.numColored 3 (clusterAlg 3 3 net (G.1, adjTable G)) := by
  have hs0 : 0 < threeRoot lam := Real.rpow_pos_of_pos h0 _
  have hs32 : threeRoot lam ^ 32 = lam := Real.rpow_inv_natCast_pow h0.le (by norm_num)
  have hloss : threeLoss lam = 32 * threeRoot lam ^ 2 := rfl
  generalize threeRoot lam = s at hs0 hs32 hloss
  subst hs32
  rw [hloss]
  by_cases hsmall : 32 * s ^ 2 < 1
  · have hs3 : 0 < s ^ 3 := pow_pos hs0 3
    have hslt : s < 1 := by nlinarith only [hsmall, hs0]
    obtain ⟨θ, hθ1, hθ2⟩ := exists_rat_btwn (by linarith only [hs3] : s ^ 3 < 2 * s ^ 3)
    obtain ⟨κ, hκ1, hκ2⟩ := exists_rat_btwn (by positivity : (0 : ℝ) < s ^ 2 / 128)
    have hθ0 : (0 : ℝ) < θ := hs3.trans hθ1
    have hθle : (θ : ℝ) ≤ 1 := by
      have : s ^ 3 ≤ s ^ 2 := pow_le_pow_of_le_one hs0.le hslt.le (by norm_num)
      linarith only [hθ2, this, hsmall]
    have hθq : (0 : ℚ) < θ := by exact_mod_cast hθ0
    have hθq0 : (0 : ℚ) < θ / 2 := by positivity
    have hθq1 : θ / 2 < θ := by linarith only [hθq]
    have hθq2 : θ ≤ 1 := by exact_mod_cast hθle
    have hκq : (0 : ℚ) < κ := by exact_mod_cast hκ1
    obtain ⟨net, hnetp, hcov⟩ := Net.exists_absNet (θ / 2) θ κ hθq0 hθq1 hθq2 hκq
      ⌊1 + 4 / ((θ / 2 : ℚ) : ℝ) ^ 4⌋₊
    refine ⟨net, hnetp, fun G hreg hexp c₀ hc₀ hsize ↦ ?_⟩
    obtain ⟨d, hd⟩ := hreg
    have hθ'0 : (0 : ℝ) < ((θ / 2 : ℚ) : ℝ) := by exact_mod_cast hθq0
    have hθ'1 : ((θ / 2 : ℚ) : ℝ) < 1 := by
      push_cast
      linarith only [hθle, hθ0]
    have hδ : s ^ 32 < ((θ / 2 : ℚ) : ℝ) ^ 2 / 2 := by
      have hθsq : s ^ 6 < (θ : ℝ) ^ 2 := by
        have := pow_lt_pow_left₀ hθ1 hs3.le two_ne_zero
        rwa [← pow_mul] at this
      have h1 : s ^ 32 ≤ s ^ 8 := pow_le_pow_of_le_one hs0.le hslt.le (by norm_num)
      have h2 : s ^ 8 = s ^ 6 * s ^ 2 := by ring
      have h3 : s ^ 6 * s ^ 2 ≤ s ^ 6 * (1 / 32) :=
        mul_le_mul_of_nonneg_left (by linarith only [hsmall]) (by positivity)
      have e : ((θ / 2 : ℚ) : ℝ) ^ 2 / 2 = (θ : ℝ) ^ 2 / 8 := by
        push_cast
        ring
      rw [e]
      linarith only [h1, h2, h3, hθsq, pow_pos hs0 6]
    have hT := Nat.le_floor (card_abs_eig_ge_le G hθ'0 hθ'1 hδ hexp)
    exact three_numColored_ge G hd hs0 hsmall hexp hθ1 hθ2 hκ1 hκ2 net (hcov G ⟨d, hd⟩ hT) c₀
      hc₀ hsize
  · refine ⟨fun _ ↦ [], ComputableInPolyTime.const _, fun G _ _ c₀ _ _ ↦ ?_⟩
    have h1 : (1 - 32 * s ^ 2) * (G.1 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [not_lt.1 hsmall]) (Nat.cast_nonneg _)
    exact h1.trans (Nat.cast_nonneg _)

end Alg

end BHSV25
