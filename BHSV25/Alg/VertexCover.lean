module

public import BHSV25.Alg.IndepSet

/-!
# Corollary 1.2: vertex cover in one-sided expanders

[BHSV25, Corollary 1.2] (`BHSV25.Alg.vertexCover_approximation`): for every `ε > 0` there are
`λ₀ > 0` and a polynomial-time algorithm that, on every regular `λ₀`-one-sided expander, outputs a
vertex cover of size at most `(5/3 + ε)` times the minimum.

The algorithm (`BHSV25.Alg.vcAlg`) outputs the complement of the independent set of Theorem 1.1
(`BHSV25.Alg.indepAlg`, with `t = 1`), a vertex cover. Let `τ = (1/2 + γ) n` be the vertex cover
number, so that the complement of a minimum vertex cover is an independent set of `(1/2 - γ) n`
vertices. In a `d`-regular graph with `d ≥ 1`, `γ ≥ 0`.
* If `γ ≤ 1/10`, Theorem 1.1 bounds the output by `(1/2 + (5 + f λ₀) γ) n`, at most
  `(5/3 + ε) τ` when `f λ₀ ≤ ε`: the ratio `(1/2 + 5γ) / (1/2 + γ)` is `5/3` at `γ = 1/10`.
* If `γ > 1/10`, the output has at most `n < (5/3) τ` vertices.

Without edges, Theorem 1.1's algorithm outputs all vertices, so the cover is empty, as is the
minimum one.
-/

@[expose] public section

namespace BHSV25.Alg

open Filter Topology Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-! ### Complements -/

/-- The complement of a set of vertices `v < n` given by bits. -/
def compBits (n : ℕ) (b : List Bool) : List Bool := (List.range n).map fun v ↦ !b.getD v false

theorem mem_vertexSet_compBits (G : Graph) (b : List Bool) (v : Fin G.1) :
    v ∈ G.vertexSet (compBits G.1 b) ↔ v ∉ G.vertexSet b := by
  rw [Graph.vertexSet, Graph.vertexSet, Finset.mem_filter, Finset.mem_filter,
    List.getD_eq_getElem _ _ (by rw [compBits, List.length_map, List.length_range]; exact v.2)]
  simp [compBits]

theorem vertexSet_compBits (G : Graph) (b : List Bool) :
    G.vertexSet (compBits G.1 b) = Finset.univ \ G.vertexSet b := by
  ext v
  rw [mem_vertexSet_compBits, Finset.mem_sdiff]
  exact ⟨fun h ↦ ⟨Finset.mem_univ _, h⟩, fun h ↦ h.2⟩

theorem compBits_polytime : ComputableInPolyTime (fun x : ℕ × List Bool ↦ compBits x.1 x.2)
    (encPair encUnary encBits) encBits := by
  unfold compBits
  have h : ComputableInPolyTime
      (fun x : ℕ × List Bool ↦ (List.range x.1).map fun v ↦ !x.2.getD v false)
      (encPair encUnary encBits) (encList encBool) :=
    mapWithInput (by fun_prop) (bool_not.comp (bitsGetDWithInput (by fun_prop) (by fun_prop) false))
  exact (bits_encList_polyTime encBool).2.comp h

@[fun_prop]
theorem compBits' {n : α → ℕ} {b : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x ↦ compBits (n x) (b x)) input encBits :=
  compBits_polytime.comp (g := fun x ↦ (n x, b x)) (hn.prod hb)

/-! ### The algorithm -/

/-- **The algorithm** of [BHSV25, Corollary 1.2]: the complement of the independent set of
Theorem 1.1. -/
def vcAlg (net : ℕ × List Bool → List (List ℚ)) (x : ℕ × List Bool) : List Bool :=
  compBits (numV x) (indepAlg net x)

theorem vcAlg_polytime {net : ℕ × List Bool → List (List ℚ)}
    (hnet : ComputableInPolyTime net (encPair encNat encBits)
      (encList (encList Encoding.encRat))) :
    ComputableInPolyTime (vcAlg net) (encPair encNat encBits) encBits := by
  unfold vcAlg
  exact compBits' numV_polytime (indepAlg_polytime hnet)

theorem vertexSet_vcAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    G.vertexSet (vcAlg net (G.1, adjTable G)) =
      Finset.univ \ G.vertexSet (indepAlg net (G.1, adjTable G)) := by
  rw [vcAlg, numV_graph, vertexSet_compBits]

theorem isVertexCover_vcAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    G.IsVertexCover (G.vertexSet (vcAlg net (G.1, adjTable G))) := by
  intro u v hadj
  rw [vertexSet_vcAlg, Finset.mem_sdiff, Finset.mem_sdiff]
  by_contra h
  rw [not_or] at h
  have hu := not_not.1 fun hu ↦ h.1 ⟨Finset.mem_univ u, hu⟩
  have hv := not_not.1 fun hv ↦ h.2 ⟨Finset.mem_univ v, hv⟩
  exact isIndepSet_indepAlg net G (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hadj.ne hadj

/-! ### Vertex covers and independent sets -/

/-- A minimum vertex cover exists. -/
theorem exists_vertexCover_card (G : Graph) :
    ∃ S : Finset (Fin G.1), G.IsVertexCover S ∧ S.card = G.vertexCoverNumber :=
  Nat.sInf_mem (s := {m | ∃ S : Finset (Fin G.1), G.IsVertexCover S ∧ S.card = m})
    ⟨_, Finset.univ, fun u _ _ ↦ Or.inl (Finset.mem_univ u), rfl⟩

theorem isIndepSet_compl_of_isVertexCover (G : Graph) {S : Finset (Fin G.1)}
    (hS : G.IsVertexCover S) : G.2.IsIndepSet ((Finset.univ \ S : Finset (Fin G.1)) : Set (Fin G.1))
    := by
  intro u hu v hv _ hadj
  rw [Finset.mem_coe, Finset.mem_sdiff] at hu hv
  rcases hS u v hadj with h | h
  · exact hu.2 h
  · exact hv.2 h

/-! ### Corollary 1.2 -/

/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a polynomial-time `(5/3 + ε)`-approximation
algorithm for vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`. -/
theorem vertexCover_approximation :
    ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber := by
  classical
  intro ε hε
  -- `λ₀` with `f λ₀ < ε`
  obtain ⟨lam, ⟨hl0, hl1⟩, hfε⟩ : ∃ lam : ℝ, (0 < lam ∧ lam < 1) ∧ indepLoss lam < ε := by
    have h1 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), indepLoss lam < ε := tendsto_indepLoss (Iio_mem_nhds hε)
    have h2 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Set.Ioo 0 1 := Ioo_mem_nhdsGT (by norm_num)
    exact (h2.and h1).exists
  obtain ⟨net, hnet, hcorr⟩ := exists_indepAlg hl0 hl1 1
  refine ⟨lam, hl0, fun G ↦ vcAlg net (G.1, adjTable G),
    (vcAlg_polytime hnet).comp (of_eq fun _ ↦ rfl), fun G hreg hexp ↦
      ⟨isVertexCover_vcAlg net G, ?_⟩⟩
  have hf0 := indepLoss_nonneg hl0 hl1
  set f := indepLoss lam with hf
  set m := (G.vertexSet (indepAlg net (G.1, adjTable G))).card with hm
  have hout : (G.vertexSet (vcAlg net (G.1, adjTable G))).card = G.1 - m := by
    rw [vertexSet_vcAlg, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hmn : m ≤ G.1 := by
    have := (G.vertexSet (indepAlg net (G.1, adjTable G))).card_le_univ
    rwa [Fintype.card_fin] at this
  have hout' : ((G.vertexSet (vcAlg net (G.1, adjTable G))).card : ℝ) = G.1 - m := by
    rw [hout, Nat.cast_sub hmn]
  rw [hout']
  -- a minimum vertex cover and its complement
  obtain ⟨S, hS, hScard⟩ := exists_vertexCover_card G
  rw [← hScard]
  have hτ0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hε' : (0 : ℝ) ≤ (5 / 3 + ε) * S.card := mul_nonneg (by linarith only [hε]) hτ0
  obtain ⟨d, hd⟩ := hreg
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith only [this, hm0, hε']
  by_cases hd0 : d = 0
  · subst hd0
    have h := card_indepAlg_of_degree_zero net G hd
    have h' : (G.1 : ℝ) ≤ m := by exact_mod_cast h
    linarith only [h', hε']
  set I := Finset.univ \ S with hI
  have hIind := isIndepSet_compl_of_isVertexCover G hS
  have hIcard : (I.card : ℝ) = G.1 - S.card := by
    rw [hI, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by simpa using S.card_le_univ)]
  have h2I : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hIind
  have hn' : (0 : ℝ) < G.1 := Nat.cast_pos.2 hn
  set g : ℝ := G.1 / 2 - I.card with hg
  have hg0 : 0 ≤ g := by linarith only [h2I, hg]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rcases le_or_gt g (G.1 / 10) with hg10 | hg10
  · -- `γ = g / n ≤ 1/10`: Theorem 1.1
    have hγ : (1 / 2 - g / G.1) * G.1 = I.card := by
      rw [hg]
      field_simp
      ring
    have h := hcorr G ⟨d, hd⟩ hexp (g / G.1) (div_nonneg hg0 hn'.le)
      ⟨I, hIind, hγ.le⟩
    have e : (1 / 2 - (5 + f) * (g / G.1)) * G.1 = G.1 / 2 - (5 + f) * g := by
      field_simp
    rw [e, ← hm] at h
    have hSg : (S.card : ℝ) = G.1 / 2 + g := by linarith only [hIcard, hg]
    have hεS : ε * S.card = ε * (G.1 / 2) + ε * g := by rw [hSg]; ring
    have hfg : f * g ≤ ε * (G.1 / 10) :=
      mul_le_mul hfε.le hg10 hg0 hε.le
    have hεg : 0 ≤ ε * g := mul_nonneg hε.le hg0
    have hεn : 0 ≤ ε * G.1 := mul_nonneg hε.le hn'.le
    linarith only [h, hfg, hεg, hεn, hSg, hεS, hg10]
  · -- `γ > 1/10`: the cover has at most `n` vertices
    have hεS : 0 ≤ ε * S.card := mul_nonneg hε.le hτ0
    linarith only [hm0, hg10, hIcard, hg, hεS]

end BHSV25.Alg
