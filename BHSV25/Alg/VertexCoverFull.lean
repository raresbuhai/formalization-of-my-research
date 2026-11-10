module

public import BHSV25.Alg.VertexCover
public import BHSV25.Alg.IndepSetFull

/-!
# Corollary 1.2

[BHSV25, Corollary 1.2] (`BHSV25.Alg.vertexCover_approximation`): for every `ε > 0` there are
`λ₀ > 0` and an algorithm running in time `K · m^C`, with `C` independent of `ε`, that outputs a
vertex cover of size at most `(5/3 + ε)` times the minimum on every regular `λ₀`-one-sided
expander.

**The algorithm** (`BHSV25.Alg.vcAlgGS`) runs the algorithm of Corollary 7.21
(`BHSV25.Alg.indepAlgGS`) for each of finitely many parameters, here those of `γ = j s`,
`j = 1, …, ⌈1 / (10 s)⌉`, keeps the largest independent set and outputs its complement. It is one
machine reading the list of parameters with the graph (`BHSV25.Alg.vcAlgGS_polytime`).

**The analysis**, for `e = min(ε, 1)`, `c = e/4`, `√(2λ₀) = e / (16 + 2e)` (so that
`(4 + c) / (1 - √(2λ₀)) = 4 + e/2`) and `s = e / 12`: the vertex cover number is `(1/2 + γ*) n`
with `γ* ≥ 0`, and the complement of a minimum cover is an independent set of `(1/2 - γ*) n`
vertices.

* If `γ* ≤ 1/10`, the grid has `γ_j ∈ [γ*, γ* + s]` (`BHSV25.Alg.exists_grid_index`), and
  Corollary 7.21 for `γ_j` bounds the cover by `(1/2 + (5 + e/2) γ_j) n`, at most
  `(5/3 + ε) (1/2 + γ*) n` (`BHSV25.Alg.vc_ratio`).
* If `γ* > 1/10`, the cover has at most `n < (5/3) (1/2 + γ*) n` vertices.

Without edges, each run outputs all vertices, so the cover is empty.
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### The algorithm -/

/-- **The algorithm** of Corollary 1.2, for a list `q` of parameters of
`BHSV25.Alg.indepAlgGS`: the complement of the largest of their independent sets. -/
def vcAlgGS (q : List (ℕ × ℕ × ℕ × ℕ)) (x : ℕ × List Bool) : List Bool :=
  compBits (numV x) (bestOf (numV x) [] (q.map fun p ↦ indepAlgGS p x))

/-- The input of the machine: the list of parameters with the graph. -/
abbrev encVCIn : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↪ List Bool :=
  encPair (encList Net.encGSPar) (encPair encNat encBits)

theorem vcAlgGS_polytime : ComputableInPolyTime
    (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ vcAlgGS z.1 z.2) encVCIn encBits := by
  have hq : ComputableInPolyTime (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.1)
      encVCIn (encList Net.encGSPar) := fst _ _
  have hx : ComputableInPolyTime (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2)
      encVCIn (encPair encNat encBits) := snd _ _
  have hn := numV_polytime.comp hx
  have hw1 : ComputableInPolyTime
      (fun w : (List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool)) × (ℕ × ℕ × ℕ × ℕ) ↦ w.2)
      (encPair encVCIn Net.encGSPar) Net.encGSPar := snd _ _
  have hw2 : ComputableInPolyTime
      (fun w : (List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool)) × (ℕ × ℕ × ℕ × ℕ) ↦ w.1.2)
      (encPair encVCIn Net.encGSPar) (encPair encNat encBits) := hx.comp (fst _ _)
  have hw := hw1.prod hw2
  have hf0 := indepAlgGS_polytime.comp hw
  have hf : ComputableInPolyTime
      (fun w : (List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool)) × (ℕ × ℕ × ℕ × ℕ) ↦ indepAlgGS w.2 w.1.2)
      (encPair encVCIn Net.encGSPar) encBits := hf0
  have hL : ComputableInPolyTime (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      z.1.map fun p ↦ indepAlgGS p z.2) encVCIn (encList encBits) := mapWithInput hq hf
  have hinit : ComputableInPolyTime (fun _ : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      ([] : List Bool)) encVCIn encBits := const _
  have hbest : ComputableInPolyTime (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      bestOf (numV z.2) [] (z.1.map fun p ↦ indepAlgGS p z.2)) encVCIn encBits :=
    bestOf' hn hinit hL
  have key : ComputableInPolyTime (fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      compBits (numV z.2) (bestOf (numV z.2) [] (z.1.map fun p ↦ indepAlgGS p z.2)))
      encVCIn encBits := compBits' hn hbest
  unfold vcAlgGS
  exact key

theorem vertexSet_nil (G : Graph) : G.vertexSet [] = ∅ := by
  ext v
  simp [Graph.vertexSet]

/-- The largest independent set is independent. -/
theorem isIndepSet_best (q : List (ℕ × ℕ × ℕ × ℕ)) (G : Graph) :
    G.2.IsIndepSet (G.vertexSet (bestOf G.1 []
      (q.map fun p ↦ indepAlgGS p (G.1, adjTable G))) : Set (Fin G.1)) := by
  rcases bestOf_mem G.1 [] (q.map fun p ↦ indepAlgGS p (G.1, adjTable G)) with h | h
  · rw [h, vertexSet_nil]
    simp
  · obtain ⟨p, -, hp⟩ := List.mem_map.1 h
    rw [← hp]
    exact isIndepSet_indepAlg _ G

theorem vertexSet_vcAlgGS (q : List (ℕ × ℕ × ℕ × ℕ)) (G : Graph) :
    G.vertexSet (vcAlgGS q (G.1, adjTable G)) = Finset.univ \
      G.vertexSet (bestOf G.1 [] (q.map fun p ↦ indepAlgGS p (G.1, adjTable G))) := by
  rw [vcAlgGS, numV_graph, vertexSet_compBits]

theorem isVertexCover_vcAlgGS (q : List (ℕ × ℕ × ℕ × ℕ)) (G : Graph) :
    G.IsVertexCover (G.vertexSet (vcAlgGS q (G.1, adjTable G))) := by
  intro u v hadj
  rw [vertexSet_vcAlgGS, Finset.mem_sdiff, Finset.mem_sdiff]
  by_contra h
  rw [not_or] at h
  have hu := not_not.1 fun hu ↦ h.1 ⟨Finset.mem_univ u, hu⟩
  have hv := not_not.1 fun hv ↦ h.2 ⟨Finset.mem_univ v, hv⟩
  exact isIndepSet_best q G (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hadj.ne hadj

/-- Every run is at most the largest. -/
theorem card_le_best {q : List (ℕ × ℕ × ℕ × ℕ)} {p : ℕ × ℕ × ℕ × ℕ} (hp : p ∈ q) (G : Graph) :
    (G.vertexSet (indepAlgGS p (G.1, adjTable G))).card ≤
      (G.vertexSet (bestOf G.1 [] (q.map fun p ↦ indepAlgGS p (G.1, adjTable G)))).card := by
  rw [card_vertexSet, card_vertexSet]
  exact le_numTrue_bestOf (List.mem_map.2 ⟨p, hp, rfl⟩)

/-! ### The arithmetic -/

/-- **The grid**: for `γ ∈ [0, 1/10]` and `s > 0`, some `j < ⌈1 / (10 s)⌉` has
`γ ≤ (j + 1) s ≤ γ + s`. -/
theorem exists_grid_index {γ s : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 10) (hs : 0 < s) :
    ∃ j < ⌈1 / 10 / s⌉₊, γ ≤ (j + 1 : ℝ) * s ∧ (j + 1 : ℝ) * s ≤ γ + s := by
  have hJ : 1 ≤ ⌈1 / 10 / s⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]
    positivity)
  rcases Nat.eq_zero_or_pos ⌈γ / s⌉₊ with h0 | hpos
  · have h1 : γ / s ≤ 0 := Nat.ceil_eq_zero.1 h0
    have h2 : γ ≤ 0 := by
      by_contra h
      have : 0 < γ / s := div_pos (lt_of_not_ge h) hs
      linarith
    have hγ : γ = 0 := le_antisymm h2 hγ0
    refine ⟨0, hJ, ?_, ?_⟩ <;> simp [hγ, hs.le]
  · refine ⟨⌈γ / s⌉₊ - 1, ?_, ?_, ?_⟩
    · have := Nat.ceil_mono (div_le_div_of_nonneg_right hγ1 hs.le)
      omega
    · have e : ((⌈γ / s⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈γ / s⌉₊ := by
        rw [Nat.cast_sub hpos]
        ring
      rw [e]
      have := Nat.le_ceil (γ / s)
      rwa [div_le_iff₀ hs] at this
    · have e : ((⌈γ / s⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈γ / s⌉₊ := by
        rw [Nat.cast_sub hpos]
        ring
      rw [e]
      have := Nat.ceil_lt_add_one (div_nonneg hγ0 hs.le)
      have h2 : (⌈γ / s⌉₊ : ℝ) * s < (γ / s + 1) * s := mul_lt_mul_of_pos_right this hs
      rw [add_mul, div_mul_cancel₀ _ hs.ne', one_mul] at h2
      exact h2.le

/-- **The ratio**: for `γ ≤ 1/10`, `γ_j ≤ γ + e/12` and an output of
`(1/2 - (5 + e/2) γ_j) n` vertices, the cover has at most `(5/3 + ε) (1/2 + γ) n` vertices. -/
theorem vc_ratio {ε e n γ γj out : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heε : e ≤ ε) (hn : 0 ≤ n)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 10) (hj2 : γj ≤ γ + e / 12)
    (hout : (1 / 2 - (5 + e / 2) * γj) * n ≤ out) :
    n - out ≤ (5 / 3 + ε) * ((1 / 2 + γ) * n) := by
  have h1 : (1 / 2 + (5 + e / 2) * (γ + e / 12)) ≤ (5 / 3 + ε) * (1 / 2 + γ) := by
    have h2 : e / 12 * (5 + e / 2) ≤ e / 2 := by nlinarith
    nlinarith
  have h3 : (5 + e / 2) * γj ≤ (5 + e / 2) * (γ + e / 12) :=
    mul_le_mul_of_nonneg_left hj2 (by positivity)
  have h4 := mul_le_mul_of_nonneg_right h1 hn
  nlinarith

/-! ### Corollary 1.2 -/

open Classical in
/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a `(5/3 + ε)`-approximation algorithm for
vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`, running in time `K · m^C`
with `C` independent of `ε`. -/
theorem vertexCover_approximation :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ K : ℝ,
      ∃ A : Graph → List Bool, RunsInTime A encGraph Encoding.encBits K C ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber := by
  obtain ⟨C, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : List (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ vcAlgGS z.1 z.2) vcAlgGS_polytime
  refine ⟨C, fun ε hε ↦ ?_⟩
  -- the constants
  obtain ⟨e, he⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ lt_min hε one_pos
  have he1 : e ≤ 1 := he ▸ min_le_right _ _
  have heε : e ≤ ε := he ▸ min_le_left _ _
  obtain ⟨r, hr⟩ : ∃ x : ℝ, x = e / (16 + 2 * e) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have hl0 : 0 < r ^ 2 / 2 := by positivity
  have hl1 : r ^ 2 / 2 < 1 / 2 := by nlinarith
  have hsq : Real.sqrt (2 * (r ^ 2 / 2)) = r := by
    rw [show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hr0.le]
  have hcoef : (4 + e / 4) / (1 - r) = 4 + e / 2 := by
    rw [hr, div_eq_iff (by rw [← hr]; linarith)]
    field_simp
    ring
  have hs : 0 < e / 12 := by positivity
  -- the runs of Corollary 7.21
  choose P hP using fun j : ℕ ↦ exists_indep_params_top (c := e / 4) (by positivity) hl0 hl1 1
    (γ := (j + 1 : ℝ) * (e / 12)) (by positivity)
  set q := (List.range ⌈1 / 10 / (e / 12)⌉₊).map P with hq
  obtain ⟨K, hK⟩ := hrun q
  refine ⟨r ^ 2 / 2, hl0, K, _, hK, fun G hreg hexp ↦ ⟨isVertexCover_vcAlgGS q G, ?_⟩⟩
  -- the size of the output
  set best := G.vertexSet (bestOf G.1 [] (q.map fun p ↦ indepAlgGS p (G.1, adjTable G)))
    with hbest
  have hout : ((G.vertexSet (vcAlgGS q (G.1, adjTable G))).card : ℝ) = G.1 - best.card := by
    rw [vertexSet_vcAlgGS, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by simpa using best.card_le_univ)]
  rw [hout]
  obtain ⟨S, hS, hScard⟩ := exists_vertexCover_card G
  rw [← hScard]
  have hε' : (0 : ℝ) ≤ (5 / 3 + ε) * S.card := by positivity
  have hbest0 : (0 : ℝ) ≤ best.card := Nat.cast_nonneg _
  obtain ⟨d, hd⟩ := hreg
  have hJ : 0 < ⌈1 / 10 / (e / 12)⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hP0 : P 0 ∈ q := List.mem_map.2 ⟨0, List.mem_range.2 hJ, rfl⟩
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    linarith
  by_cases hd0 : d = 0
  · -- no edges: all vertices are independent
    subst hd0
    have h := (card_indepAlg_of_degree_zero (indepNet (P 0)) G hd).trans (card_le_best hP0 G)
    have h' : (G.1 : ℝ) ≤ best.card := by exact_mod_cast h
    linarith
  -- the complement of a minimum cover
  set I := Finset.univ \ S with hI
  have hIind := isIndepSet_compl_of_isVertexCover G hS
  have hIcard : (I.card : ℝ) = G.1 - S.card := by
    rw [hI, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by simpa using S.card_le_univ)]
  have h2I : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hIind
  have hn' : (0 : ℝ) < G.1 := Nat.cast_pos.2 hn
  set γ := (S.card : ℝ) / G.1 - 1 / 2 with hγ
  have hSγ : (S.card : ℝ) = (1 / 2 + γ) * G.1 := by rw [hγ]; field_simp; ring
  have hγ0 : 0 ≤ γ := by
    rw [hγ, sub_nonneg, le_div_iff₀ hn']
    linarith
  rw [hSγ]
  rcases le_or_gt γ (1 / 10) with hγ10 | hγ10
  · -- `γ ≤ 1/10`: the run for the grid point above `γ`
    obtain ⟨j, hj, hj1, hj2⟩ := exists_grid_index hγ0 hγ10 hs
    have hInd : G.HasIndepSet ((1 / 2 - (j + 1 : ℝ) * (e / 12)) * G.1) := by
      refine ⟨I, hIind, ?_⟩
      rw [hIcard, hSγ]
      nlinarith
    have h1 := hP j G ⟨d, hd⟩ hexp hInd
    rw [hsq] at h1
    have h2 : ((G.vertexSet (indepAlgGS (P j) (G.1, adjTable G))).card : ℝ) ≤ best.card := by
      exact_mod_cast card_le_best (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩) G
    have e1 : (1 / 2 - (j + 1 : ℝ) * (e / 12) - (4 + e / 2) * ((j + 1 : ℝ) * (e / 12))) * G.1 =
        (1 / 2 - (5 + e / 2) * ((j + 1 : ℝ) * (e / 12))) * G.1 := by ring
    have h3 : ((4 + e / 4) * ((j + 1 : ℝ) * (e / 12)) / (1 - r)) =
        (4 + e / 2) * ((j + 1 : ℝ) * (e / 12)) := by
      rw [mul_comm (4 + e / 4), mul_div_assoc, hcoef, mul_comm]
    rw [h3, e1] at h1
    exact vc_ratio he0 he1 heε hn'.le hγ0 hγ10 hj2 (h1.trans h2)
  · -- `γ > 1/10`: the cover has at most `n` vertices
    nlinarith

end BHSV25.Alg
