module

public import BHSV25.Alg.ColoringAnalysis
public import BHSV25.Alg.ColoringPolyTime

/-!
# Algorithms for 3-colorable one-sided expanders

[BHSV25, Theorem 1.3] (Theorem 7.9) and [BHSV25, Corollary 1.4].

* **Theorem 1.3** (`BHSV25.Alg.threeColoring_balanced`): the clustering algorithm with `3`
  clusters (`BHSV25.Alg.clusterAlg 3 3`), with a net of the eigenvectors with `|μ| ≥ θ` for a
  suitable `θ`, colors all but `g λ · n` vertices, for `g λ = 32 λ^{1/16}`
  (`BHSV25.Alg.threeLoss`). The analysis is in `BHSV25/Alg/ColoringAnalysis.lean`
  (`BHSV25.Alg.three_exists_net`); the output is always a partial `3`-coloring.
* **Corollary 1.4** (`BHSV25.Alg.threeColoring_independentSet_or_coloring`): the algorithm of
  `BHSV25/Alg/ColoringPolyTime.lean` (`BHSV25.Alg.threeAlg`) runs the clustering algorithm,
  giving a partial `3`-coloring `c`, and the algorithm of Theorem 1.1 (`BHSV25.Alg.indepAlg`),
  giving an independent set `b`, and outputs `c` if `c` colors at least `2 |b|` vertices, and the
  coloring of `b` alone otherwise (`BHSV25.Alg.threeAlg_spec`). Let `h` be the loss of
  Theorem 1.1 (`BHSV25.Alg.indepLoss`). If every class of the promised `(3, λ)`-coloring has at
  most `(1/2 - g) n` vertices, `c` colors at least `(1 - g) n` vertices, so either `c` is output,
  or `|b| > (1 - g) n / 2`. Otherwise some class is an independent set of more than
  `(1/2 - g) n` vertices, so `|b| ≥ (1/2 - (5 + h) g) n` by Theorem 1.1, and either `b` is output,
  or `c` colors at least `2 |b| ≥ (1 - (10 + 2 h) g) n` vertices. So the loss of Corollary 1.4 is
  `(11 + 2 h λ) g λ` for `λ < 1`. For `λ ≥ 1` it is `1`, so that only the output being a partial
  `3`-coloring matters, and the algorithm is the clustering algorithm alone (Theorem 1.1 is
  stated for `λ < 1`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Filter Topology Turing.MultiTapeTM Finset

/-- **Theorem 1.3** of [BHSV25] (Theorem 7.9): for every `λ > 0`, a polynomial-time algorithm that,
on regular `λ`-one-sided expanders with `3` independent sets of at most `(1/2 - f λ) n` vertices
each that cover all but `λ n` vertices, outputs `3` independent sets covering all but `f λ · n`
vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_balanced :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ c, G.IsColoring 3 lam c ∧
              ∀ a < 3, (G.classSize 3 c a : ℝ) ≤ (1 / 2 - f lam) * G.1) →
            G.IsColoring 3 (f lam) (A G) := by
  refine ⟨threeLoss, tendsto_threeLoss, fun lam h0 ↦ ?_⟩
  obtain ⟨net, hnet, hcorr⟩ := three_exists_net h0
  refine ⟨fun G ↦ clusterAlg 3 3 net (G.1, adjTable G), clusterAlg_graph_polytime 3 3 hnet, ?_⟩
  rintro G hreg hexp ⟨c₀, hc₀, hsize⟩
  exact ⟨(clusterAlg_spec G (by norm_num) le_rfl net).1, hcorr G hreg hexp c₀ hc₀ hsize⟩

/-! ### Corollary 1.4 -/

section Corollary

variable (G : Graph)

theorem color_threeIndepColoring (b : List Bool) (v : Fin G.1) :
    G.color 3 (threeIndepColoring G.1 b) v = if b.getD v false then 0 else 3 := by
  rw [Graph.color, threeIndepColoring, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The coloring of an independent set is a partial `3`-coloring. -/
theorem isPartialColoring_threeIndepColoring {b : List Bool}
    (hb : G.2.IsIndepSet (G.vertexSet b : Set (Fin G.1))) :
    G.IsPartialColoring 3 (threeIndepColoring G.1 b) := by
  intro u v huv hu heq
  rw [color_threeIndepColoring] at hu heq
  rw [color_threeIndepColoring] at heq
  by_cases hbu : b.getD u false = true
  · by_cases hbv : b.getD v false = true
    · have hu' : u ∈ (G.vertexSet b : Set (Fin G.1)) := by
        rw [mem_coe, Graph.vertexSet, mem_filter]
        exact ⟨mem_univ _, hbu⟩
      have hv' : v ∈ (G.vertexSet b : Set (Fin G.1)) := by
        rw [mem_coe, Graph.vertexSet, mem_filter]
        exact ⟨mem_univ _, hbv⟩
      exact hb hu' hv' huv.ne huv
    · rw [ite_eq_left hbu, ite_eq_right hbv] at heq
      exact absurd heq (by norm_num)
  · rw [ite_eq_right hbu] at hu
    exact absurd hu (by norm_num)

/-- The class `0` of the coloring of `b` is `b`. -/
theorem classSize_threeIndepColoring (b : List Bool) :
    G.classSize 3 (threeIndepColoring G.1 b) 0 = numTrue G.1 b := by
  rw [← card_vertexSet, Graph.classSize]
  congr 1
  ext v
  rw [mem_filter, color_threeIndepColoring, Graph.vertexSet, mem_filter]
  by_cases h : b.getD v false = true
  · rw [ite_eq_left h]
    exact ⟨fun _ ↦ ⟨mem_univ _, h⟩, fun _ ↦ ⟨mem_univ _, rfl⟩⟩
  · rw [ite_eq_right h]
    exact ⟨fun h' ↦ absurd h'.2 (by norm_num), fun h' ↦ absurd h'.2 h⟩

/-- **The guarantee of the combined algorithm** for `λ ∈ (0, 1)`, given the guarantees of the
clustering algorithm (loss `g`) and of the independent-set algorithm (loss `h`): a partial
`3`-coloring with a class of `(1/2 - (11 + 2 h) g) n` vertices or covering all but
`(11 + 2 h) g · n` vertices. -/
theorem threeAlg_spec {lam g h : ℝ} (hg0 : 0 ≤ g) (hh0 : 0 ≤ h)
    {net₁ net₂ : ℕ × List Bool → List (List ℚ)}
    (hcorr₁ : ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → ∀ c₀ : List ℕ,
      G.IsColoring 3 lam c₀ → (∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1) →
      (1 - g) * G.1 ≤ G.numColored 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)))
    (hcorr₂ : ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ 1 →
      ∀ γ : ℝ, 0 ≤ γ → G.HasIndepSet ((1 / 2 - γ) * G.1) →
        (1 / 2 - (5 + h) * γ) * G.1 ≤ (G.vertexSet (indepAlg net₂ (G.1, adjTable G))).card)
    (hreg : G.IsRegular) (hexp : G.IsOneSidedExpander lam) (hcol : G.HasColoring 3 lam) :
    G.IsPartialColoring 3 (threeAlg net₁ net₂ (G.1, adjTable G)) ∧
      ((∃ a < 3, (1 / 2 - (11 + 2 * h) * g) * G.1 ≤
          G.classSize 3 (threeAlg net₁ net₂ (G.1, adjTable G)) a) ∨
        (1 - (11 + 2 * h) * g) * G.1 ≤ G.numColored 3 (threeAlg net₁ net₂ (G.1, adjTable G))) := by
  obtain ⟨c₀, hc₀⟩ := hcol
  have hnR : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have hrun : threeAlg net₁ net₂ (G.1, adjTable G) = threeCombine G.1
      (clusterAlg 3 3 net₁ (G.1, adjTable G)) (indepAlg net₂ (G.1, adjTable G)) := by
    rw [threeAlg, numV_graph]
  -- the two candidates
  have hpc₁ : G.IsPartialColoring 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) :=
    (clusterAlg_spec G (by norm_num) le_rfl net₁).1
  have hpc₂ := isPartialColoring_threeIndepColoring G (isIndepSet_indepAlg net₂ G)
  have hsize₂ : (G.classSize 3 (threeIndepColoring G.1 (indepAlg net₂ (G.1, adjTable G))) 0 : ℝ) =
      numTrue G.1 (indepAlg net₂ (G.1, adjTable G)) := by
    rw [classSize_threeIndepColoring]
  have hnum₁ : (G.numColored 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) : ℝ) =
      numCol G.1 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) := by
    rw [numColored_eq_numCol]
  have hcardb : ((G.vertexSet (indepAlg net₂ (G.1, adjTable G))).card : ℝ) =
      numTrue G.1 (indepAlg net₂ (G.1, adjTable G)) := by
    rw [card_vertexSet]
  -- the losses
  have hF1 : g * G.1 ≤ (11 + 2 * h) * g * G.1 := by
    have := mul_nonneg (mul_nonneg (by linarith only [hh0] : (0 : ℝ) ≤ 10 + 2 * h) hg0) hnR
    linarith only [this]
  have hF5 : (5 + h) * g * G.1 ≤ (11 + 2 * h) * g * G.1 := by
    have := mul_nonneg (mul_nonneg (by linarith only [hh0] : (0 : ℝ) ≤ 6 + h) hg0) hnR
    linarith only [this]
  have hgn : 0 ≤ g * G.1 := mul_nonneg hg0 hnR
  -- the case of a large class: Theorem 1.1
  have hlarge : (¬ ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1) →
      (1 / 2 - (5 + h) * g) * G.1 ≤ numTrue G.1 (indepAlg net₂ (G.1, adjTable G)) := by
    intro hbal
    push Not at hbal
    obtain ⟨a, ha, hbig⟩ := hbal
    have hI : G.HasIndepSet ((1 / 2 - g) * G.1) := by
      refine ⟨threeClass G c₀ a, isIndepSet_threeClass G hc₀.1 a, ?_⟩
      rw [card_threeClass G c₀ ha]
      exact hbig.le
    have := hcorr₂ G hreg hexp g hg0 hI
    rw [hcardb] at this
    exact this
  rw [hrun, threeCombine]
  by_cases hcmp : numCol G.1 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) <
    2 * numTrue G.1 (indepAlg net₂ (G.1, adjTable G))
  · -- the coloring of the independent set
    rw [ite_eq_left hcmp]
    refine ⟨hpc₂, Or.inl ⟨0, by norm_num, ?_⟩⟩
    rw [hsize₂]
    have hcmp' : (numCol G.1 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) : ℝ) <
        2 * (numTrue G.1 (indepAlg net₂ (G.1, adjTable G)) : ℝ) := by exact_mod_cast hcmp
    by_cases hbal : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1
    · have h1 := hcorr₁ G hreg hexp c₀ hc₀ hbal
      linarith only [h1, hnum₁, hcmp', hF1, hgn]
    · have h3 := hlarge hbal
      linarith only [h3, hF5]
  · -- the coloring of the clustering algorithm
    rw [ite_eq_right hcmp]
    refine ⟨hpc₁, Or.inr ?_⟩
    have hcmp' : 2 * (numTrue G.1 (indepAlg net₂ (G.1, adjTable G)) : ℝ) ≤
        (numCol G.1 3 (clusterAlg 3 3 net₁ (G.1, adjTable G)) : ℝ) := by
      exact_mod_cast not_lt.1 hcmp
    by_cases hbal : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1
    · have h1 := hcorr₁ G hreg hexp c₀ hc₀ hbal
      linarith only [h1, hF1]
    · have h3 := hlarge hbal
      linarith only [h3, hF5, hcmp', hnum₁, hF1, hgn]

end Corollary

/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, a polynomial-time algorithm that, on regular
`λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices, outputs `3`
independent sets of which one has at least `(1/2 - f λ) n` vertices or which cover all but
`f λ · n` vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 lam →
            G.IsPartialColoring 3 (A G) ∧
            ((∃ a < 3, (1 / 2 - f lam) * G.1 ≤ G.classSize 3 (A G) a) ∨
              (1 - f lam) * G.1 ≤ G.numColored 3 (A G)) := by
  refine ⟨fun lam ↦ if lam < 1 then (11 + 2 * indepLoss lam) * threeLoss lam else 1, ?_,
    fun lam h0 ↦ ?_⟩
  · have hlim : Tendsto (fun lam ↦ (11 + 2 * indepLoss lam) * threeLoss lam) (𝓝[>] 0)
        (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (11 : ℝ))).add
        (tendsto_indepLoss.const_mul 2)).mul tendsto_threeLoss
      rw [mul_zero] at this
      exact this
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    rw [ite_eq_left hlam.2]
  obtain ⟨net₁, hnet₁, hcorr₁⟩ := three_exists_net h0
  by_cases h1 : lam < 1
  · obtain ⟨net₂, hnet₂, hcorr₂⟩ := exists_indepAlg h0 h1 1
    refine ⟨fun G ↦ threeAlg net₁ net₂ (G.1, adjTable G), threeAlg_graph_polytime hnet₁ hnet₂,
      fun G hreg hexp hcol ↦ ?_⟩
    simp only [ite_eq_left h1]
    exact threeAlg_spec G (threeLoss_nonneg lam) (indepLoss_nonneg h0 h1) hcorr₁ hcorr₂ hreg hexp
      hcol
  · refine ⟨fun G ↦ clusterAlg 3 3 net₁ (G.1, adjTable G), clusterAlg_graph_polytime 3 3 hnet₁,
      fun G _ _ _ ↦ ⟨(clusterAlg_spec G (by norm_num) le_rfl net₁).1, Or.inr ?_⟩⟩
    beta_reduce
    rw [ite_eq_right h1, sub_self, zero_mul]
    exact Nat.cast_nonneg _

end Alg

end BHSV25
