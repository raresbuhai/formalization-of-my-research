module

public import BHSV25.Alg.ExpanderFull
public import BHSV25.Alg.ColoringAnalysis

/-!
# Theorem 7.9 (Theorem 1.3)

[BHSV25, Theorem 7.9] (`BHSV25.Alg.threeColoring_balanced`): there are constants `B` and `c₀`
such that for `δ ∈ [0, c₀)` and `γ, λ ∈ (0, c₀)` an algorithm running in time `K · m^C`, with `C`
independent of `δ`, `γ` and `λ`, outputs `3` independent sets covering all but
`B (λ + δ/λ) / γ⁸ · n` vertices of every regular graph with at most one eigenvalue above `λ` and a
partition into `3` parts of at most `(1/2 - γ) n` vertices whose inside edges are covered by
`δ n` vertices.

**The algorithm** is that of Theorem 7.1 (`BHSV25.Alg.expAlg`) with `3` clusters: the greedy net
of the eigenvectors with `|μ| ≥ θ`, `θ = γ^{3/2} / 8`, and the grid clustering.

**The analysis** (`BHSV25.Alg.three_numColored_grid`), as in the paper:

* the parts have at least `2 γ n ≥ γ n` vertices (`BHSV25.Alg.three_card_part_ge`), the weight
  inside them is at most `2 δ n`, and for `8 δ ≤ γ²` the rows of the model are `γ/2`-separated
  (the claim in the proof of Theorem 7.9, `BHSV25.Alg.three_rowSep`);
* Theorem 5.1 with the grid of centers (`BHSV25.Alg.exists_good_grid`), with `c = γ`,
  `α = γ/2`, the upper bound `L = λ` on the second eigenvalue and `τ = 2 θ`, misclusters at most
  `(512 · 3⁴ (2δ/λ + λ) / (γ θ² (γ/2)²) + F) n = (2¹⁷ · 3⁴ (2δ/λ + λ) / γ⁶ + F) n` vertices, where
  `F ≤ λ` is the cost of the net; the net covers the span of the eigenvectors with `|μ| ≥ θ` when
  `λ < θ²/8 = γ³/512` (Corollary 4.2);
* rounding each cluster against the part minus the cover colors all but twice the misclustered
  and covering vertices (`BHSV25.Alg.three_sub_le_sum_max`).

When `8 δ > γ²` or `λ ≥ γ³/512` the bound `B (λ + δ/λ) / γ⁸` is at least `1` for `B ≥ 512`, and
every partial coloring satisfies it, as the paper notes ("the guarantees are vacuous otherwise").
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix Turing.MultiTapeTM

open Classical in
/-- **The analysis for the 3-coloring**, on a regular graph with at most one eigenvalue above `λ`
and a partition `χ` into `3` parts of at most `(1/2 - γ) n` vertices whose inside edges are covered
by `δ n` vertices, when `8 δ ≤ γ²` and `λ < (θ/2)²/2`: the algorithm colors all but
`(2 (E + F) + 2 δ) n` vertices, for bounds `E` and `F` on the error of Theorem 5.1 and on the
cost of the net. -/
theorem three_numColored_grid (G : Graph) (hreg : G.IsRegular) {δ γ lam : ℝ} (hδ0 : 0 ≤ δ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (h8 : 8 * δ ≤ γ ^ 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2) (hθγ : (2 * θ) ^ 2 * (2 / γ) ≤ (γ / 2) ^ 2 / 2)
    (hlθ : lam < (θ / 2) ^ 2 / 2)
    {K a Sg Kg Bg : ℕ} (hK : 0 < K) (ha : ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 2 + K ≤ a)
    (hSg : 128 * ((3 : ℕ) : ℝ) ^ 2 ≤ (γ / 2) ^ 2 * (Sg : ℝ) ^ 2) (hK1 : 1 ≤ Kg)
    (hKg : (Sg : ℝ) ^ 2 ≤ γ * ((Kg : ℝ) - 1) ^ 2)
    (hBg1 : ((3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) ^ 3 ≤ Bg)
    (hBg2 : (2 * Kg + 1) ^ (3 * 3) ≤ Bg) {E F : ℝ}
    (hE : 512 * ((3 : ℕ) : ℝ) ^ 4 * (2 * δ / lam + lam) / (γ * (2 * θ - θ) ^ 2 * (γ / 2) ^ 2) ≤ E)
    (hF : 512 * ((3 : ℕ) : ℝ) ^ 2 * (4 / K) ^ 2 / (γ / 2) ^ 2 ≤ F)
    (hexp : G.numEigGT lam ≤ 1) (χ : Fin G.1 → Fin 3) (hχ : G.IsAlmostProper χ δ)
    (hsize : ∀ a, ((univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - γ) * G.1) :
    (1 - (2 * (E + F) + 2 * δ)) * G.1 ≤
      G.numColored 3 (expAlg ((3, 3, Sg, Kg, Bg),
        (a, ⌊1 + 4 / (θ / 2) ^ 4⌋₊, (Nat.sqrt ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) * K,
          (3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊)) (G.1, adjTable G)) := by
  obtain ⟨d, hd⟩ := hreg
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have hF0 : 0 ≤ F := le_trans (by positivity) hF
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  set U := expNet (a, ⌊1 + 4 / (θ / 2) ^ 4⌋₊, (Nat.sqrt ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) * K,
    (3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊) (G.1, adjTable G) with hU
  have hB1 : U.length ^ 3 ≤ Bg := (Nat.pow_le_pow_left (length_expNet_le _ _) 3).trans hBg1
  have hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ (4 / K) ^ 2 :=
    fun w hw1 hw ↦ expNet_cover G ⟨d, hd⟩ hθ0 hθ1 hlθ hexp hK ha w hw1 hw
  have hspec := (gridAlg_spec G (m := 3) (K₀ := 3) (by norm_num) le_rfl Sg Kg Bg U hB1 hBg2).2
  change (1 - (2 * (E + F) + 2 * δ)) * G.1 ≤
    G.numColored 3 (gridAlg 3 3 Sg Kg Bg U (G.1, adjTable G))
  have hp : ∀ (us : Fin 3 → List ℚ) (ts : Fin (3 * 3) → Fin (2 * Kg + 1)) (v : Fin G.1),
      (clustersC G.1 (List.ofFn us)
        (gridCenters 3 Sg Kg (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))).getD v 3 < 3 := by
    intro us ts v
    rw [getD_clustersC _ _ v.2]
    have h := clusterIdxC_lt (List.ofFn us)
      (gridCenters 3 Sg Kg (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))
      (by rw [length_gridCenters]; norm_num) v
    rwa [length_gridCenters] at h
  by_cases hd0 : d = 0
  · -- no edges: every candidate colors all vertices
    subst hd0
    obtain ⟨u, hu, -⟩ := hnet 0 (by simp) (by intro i _; simp [Spectral.coeff])
    have hI : ∀ _j : ℕ, G.2.IsIndepSet ((univ : Finset (Fin G.1)) : Set (Fin G.1)) := by
      intro _ v _ w _ _ hadj
      have h := hd v
      rw [SimpleGraph.degree, Finset.card_eq_zero] at h
      have hw : w ∈ G.2.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
      rw [h] at hw
      exact Finset.notMem_empty w hw
    have h1 := hspec (fun _ ↦ u) (fun _ ↦ hu) (fun _ ↦ 0) (fun _ ↦ univ) hI
    have h2 := three_sub_le_sum_max G _ (hp (fun _ ↦ u) (fun _ ↦ 0)) (fun _ ↦ univ) ∅
      fun v _ ↦ mem_univ v
    rw [card_empty, Nat.cast_zero, mul_zero, sub_zero] at h2
    have h3 : 0 ≤ (2 * (E + F) + 2 * δ) * G.1 := by positivity
    nlinarith
  -- the parts
  obtain ⟨S, hScard, hS⟩ := hχ
  have hint : intWt G χ ≤ 2 * δ * G.1 := by
    have := intWt_le_of_cover hd χ S hS
    linarith
  have hup' : ∀ a, ((part G χ a).card : ℝ) ≤ (1 / 2 - γ) * G.1 := hsize
  have hup : ∀ a, ((part G χ a).card : ℝ) ≤ (1 / 2 - γ + δ) * G.1 := fun a ↦ by
    have := mul_nonneg hδ0 hnR.le
    nlinarith [hup' a]
  have hlow : ∀ a, γ * G.1 ≤ (part G χ a).card := by
    intro a
    have h1 := three_card_part_ge χ hup' a
    nlinarith
  have hgl : 2 * δ ≤ γ := by nlinarith
  have hcond : 2 * δ + 2 * δ / γ ≤ γ / 2 := by
    have h1 : 2 * δ ≤ 2 * δ / γ := by
      rw [le_div_iff₀ hγ0]
      nlinarith
    have h2 : 2 * δ / γ ≤ γ / 4 := by
      rw [div_le_iff₀ hγ0]
      nlinarith
    linarith
  have hsep := three_rowSep hd hd0 hn χ hγ0 hδ0 hgl hup hlow hint hcond
  -- Theorem 5.1 with the grid of centers
  obtain ⟨us, hus, ts, hcount⟩ := exists_good_grid hd hd0 χ (Equiv.refl (Fin 3)) hn hγ0 hlow
    (by positivity : 0 < γ / 2) hsep hl0 hl1 hexp hint (by linarith : θ < 2 * θ) hθγ U hnet
    hSg hK1 hKg
  set B := univ.filter fun y : Fin G.1 ↦ clusterIdxC (List.ofFn us)
    (gridCenters 3 Sg Kg (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ))) y ≠
      (Equiv.refl (Fin 3)) (χ y) with hB
  have hBcard : (B.card : ℝ) ≤ (E + F) * G.1 :=
    hcount.trans (mul_le_mul_of_nonneg_right (add_le_add hE hF) hnR.le)
  -- the rounding
  set I : ℕ → Finset (Fin G.1) := fun j ↦ if h : j < 3 then part G χ ⟨j, h⟩ \ S else ∅ with hI
  have hIind : ∀ j, G.2.IsIndepSet (I j : Set (Fin G.1)) := by
    intro j
    simp only [hI]
    split_ifs
    · exact isIndepSet_part_sdiff χ S hS _
    · simp
  have hS' : ∀ v, v ∉ B ∪ S → v ∈ I ((clustersC G.1 (List.ofFn us)
      (gridCenters 3 Sg Kg (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))).getD v 3) := by
    intro v hv
    rw [mem_union, not_or] at hv
    have hvB : clusterIdxC (List.ofFn us)
        (gridCenters 3 Sg Kg (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ))) v = (χ v : ℕ) := by
      by_contra h
      exact hv.1 (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [getD_clustersC _ _ v.2, hvB, hI]
    simp only [(χ v).2, ↓reduceDIte, Fin.eta]
    exact mem_sdiff.2 ⟨mem_part_self χ v, hv.2⟩
  have h1 := hspec us hus ts I hIind
  have h2 := three_sub_le_sum_max G _ (hp us ts) I (B ∪ S) hS'
  have hunion : ((B ∪ S).card : ℝ) ≤ B.card + S.card := by exact_mod_cast card_union_le _ _
  have hS2 : (S.card : ℝ) ≤ δ * G.1 := hScard
  nlinarith

/-! ### The parameters and the theorem -/

/-- The threshold `θ = γ^{3/2} / 8`: `(2θ)² (2/γ) ≤ (γ/2)²/2`, `(θ/2)²/2 = γ³/512` and
`θ² = γ³/64`. -/
theorem three_theta {γ : ℝ} (hγ0 : 0 < γ) :
    (2 * (γ * Real.sqrt γ / 8)) ^ 2 * (2 / γ) ≤ (γ / 2) ^ 2 / 2 ∧
      ((γ * Real.sqrt γ / 8) / 2) ^ 2 / 2 = γ ^ 3 / 512 ∧
      (2 * (γ * Real.sqrt γ / 8) - γ * Real.sqrt γ / 8) ^ 2 = γ ^ 3 / 64 := by
  have hs : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ0.le
  refine ⟨le_of_eq ?_, ?_, ?_⟩
  · have e : (2 * (γ * Real.sqrt γ / 8)) ^ 2 = γ ^ 2 * Real.sqrt γ ^ 2 / 16 := by ring
    rw [e, hs]
    field_simp
    ring
  · have e : ((γ * Real.sqrt γ / 8) / 2) ^ 2 / 2 = γ ^ 2 * Real.sqrt γ ^ 2 / 512 := by ring
    rw [e, hs]
    ring
  · have e : (2 * (γ * Real.sqrt γ / 8) - γ * Real.sqrt γ / 8) ^ 2 =
        γ ^ 2 * Real.sqrt γ ^ 2 / 64 := by ring
    rw [e, hs]
    ring

/-- The error of Theorem 5.1 for `θ = γ^{3/2}/8`: `2¹⁷ · 3⁴ (2δ/λ + λ) / γ⁶`. -/
theorem three_error_eq {δ γ lam : ℝ} (hγ0 : 0 < γ) :
    512 * ((3 : ℕ) : ℝ) ^ 4 * (2 * δ / lam + lam) /
        (γ * (2 * (γ * Real.sqrt γ / 8) - γ * Real.sqrt γ / 8) ^ 2 * (γ / 2) ^ 2) =
      10616832 * (2 * δ / lam + lam) / γ ^ 6 := by
  rw [(three_theta hγ0).2.2]
  push_cast
  field_simp
  ring

/-- **The error is at most `B (λ + δ/λ) / γ⁸`**, for `B = 42467332`. -/
theorem three_uncovered_le {δ γ lam F : ℝ} (hδ0 : 0 ≤ δ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hF : F ≤ lam) :
    2 * (10616832 * (2 * δ / lam + lam) / γ ^ 6 + F) + 2 * δ ≤
      42467332 * (lam + δ / lam) / γ ^ 8 := by
  have hg8 : γ ^ 8 ≤ γ ^ 6 := pow_le_pow_of_le_one hγ0.le hγ1 (by norm_num)
  have hg81 : γ ^ 8 ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have hg8p : 0 < γ ^ 8 := by positivity
  have hq0 : 0 ≤ δ / lam := div_nonneg hδ0 hl0.le
  have hδq : δ ≤ δ / lam := by
    rw [le_div_iff₀ hl0]
    nlinarith
  set X := (lam + δ / lam) / γ ^ 8 with hX
  have hX0 : 0 ≤ X := by positivity
  have e : 2 * δ / lam = 2 * (δ / lam) := by ring
  rw [e]
  have h1 : 10616832 * (2 * (δ / lam) + lam) / γ ^ 6 ≤
      10616832 * (2 * (δ / lam) + lam) / γ ^ 8 :=
    div_le_div_of_nonneg_left (by positivity) hg8p hg8
  have h1' : 10616832 * (2 * (δ / lam) + lam) / γ ^ 8 ≤ 21233664 * X := by
    have h : 10616832 * (2 * (δ / lam) + lam) ≤ 21233664 * (lam + δ / lam) := by nlinarith
    have := div_le_div_of_nonneg_right h hg8p.le
    simpa only [hX, mul_div_assoc] using this
  have h2 : F + δ ≤ X := by
    rw [hX, le_div_iff₀ hg8p]
    nlinarith
  have e2 : 42467332 * (lam + δ / lam) / γ ^ 8 = 42467332 * X := by rw [hX, mul_div_assoc]
  rw [e2]
  linarith

/-- **Outside the regime of the analysis** (`8 δ > γ²` or `λ ≥ γ³/512`), the bound is at
least `1`. -/
theorem three_trivial_bound {δ γ lam : ℝ} (hδ0 : 0 ≤ δ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hbad : ¬(8 * δ ≤ γ ^ 2 ∧ lam < γ ^ 3 / 512)) :
    1 ≤ 42467332 * (lam + δ / lam) / γ ^ 8 := by
  have hg8p : 0 < γ ^ 8 := by positivity
  rw [le_div_iff₀ hg8p, one_mul]
  have hq0 : 0 ≤ δ / lam := div_nonneg hδ0 hl0.le
  rcases not_and_or.1 hbad with h | h
  · have h1 : δ ≤ δ / lam := by rw [le_div_iff₀ hl0]; nlinarith
    have h2 : γ ^ 8 ≤ γ ^ 2 := pow_le_pow_of_le_one hγ0.le hγ1 (by norm_num)
    push Not at h
    linarith
  · have h2 : γ ^ 8 ≤ γ ^ 3 := pow_le_pow_of_le_one hγ0.le hγ1 (by norm_num)
    push Not at h
    linarith

open Classical in
/-- **The parameters of Theorem 7.9** for `δ ≥ 0` and `γ, λ ∈ (0, 1/2)`: the algorithm
`BHSV25.Alg.expAlg p` has the guarantee of Theorem 7.9, with `B = 42467332`. -/
theorem exists_three_params {δ γ lam : ℝ} (hδ0 : 0 ≤ δ) (hγ0 : 0 < γ) (hγc : γ < 1 / 2)
    (hl0 : 0 < lam) (hlc : lam < 1 / 2) :
    ∃ p, (∀ G : Graph, G.IsPartialColoring 3 (expAlg p (G.1, adjTable G))) ∧
      ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
      (∃ χ : Fin G.1 → Fin 3, G.IsAlmostProper χ δ ∧
        ∀ a, ((Finset.univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - γ) * G.1) →
      G.IsColoring 3 (42467332 * (lam + δ / lam) / γ ^ 8) (expAlg p (G.1, adjTable G)) := by
  have hγ1 : γ ≤ 1 := by linarith
  have hl1 : lam < 1 := by linarith
  -- the parameters
  obtain ⟨θ, hθ⟩ : ∃ x : ℝ, x = γ * Real.sqrt γ / 8 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; have := Real.sqrt_pos.2 hγ0; positivity
  have hθ1 : θ < 2 := by
    rw [hθ]
    have : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.2 hγ1
    nlinarith [Real.sqrt_nonneg γ]
  obtain ⟨hθγ, hθl, -⟩ := three_theta hγ0
  rw [← hθ] at hθγ hθl
  obtain ⟨Sg, Kg, hSg, hK1, hKg⟩ := exists_grid_params 3 hγ0 hγ0
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈32768 * ((3 : ℕ) : ℝ) ^ 2 / (γ ^ 2 * lam)⌉₊ + 1 := ⟨_, rfl⟩
  have hKge : 32768 * ((3 : ℕ) : ℝ) ^ 2 / (γ ^ 2 * lam) + 1 ≤ K := by
    rw [hK]
    push_cast
    linarith [Nat.le_ceil (32768 * ((3 : ℕ) : ℝ) ^ 2 / (γ ^ 2 * lam))]
  have hKpos : 0 < K := by rw [hK]; omega
  set T := ⌊1 + 4 / (θ / 2) ^ 4⌋₊ with hT
  set p : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
    ((3, 3, Sg, Kg, ((3 + 12 * K) ^ T + 1) ^ 3 + (2 * Kg + 1) ^ (3 * 3)),
      (T + 2 + K, T, (Nat.sqrt T + 1) * K, (3 + 12 * K) ^ T)) with hp
  refine ⟨p, fun G ↦ isPartialColoring_gridAlg G (by norm_num) le_rfl _ _ _ _,
    fun G hreg hexp ⟨χ, hχ, hsize⟩ ↦ ?_⟩
  have hU : (expNet p.2 (G.1, adjTable G)).length ^ 3 ≤
      ((3 + 12 * K) ^ T + 1) ^ 3 + (2 * Kg + 1) ^ (3 * 3) :=
    (Nat.pow_le_pow_left (length_expNet_le _ _) 3).trans (Nat.le_add_right _ _)
  have hpart : G.IsPartialColoring 3 (expAlg p (G.1, adjTable G)) :=
    (gridAlg_spec G (m := 3) (K₀ := 3) (by norm_num) le_rfl Sg Kg _ _ hU
      (Nat.le_add_left _ _)).1
  refine ⟨hpart, ?_⟩
  by_cases hgood : 8 * δ ≤ γ ^ 2 ∧ lam < γ ^ 3 / 512
  · -- the analysis
    obtain ⟨h8, hlγ⟩ := hgood
    have hF := net_cost_le (m := 3) hγ0 hl0 hKge
    have hmain := three_numColored_grid (E := 10616832 * (2 * δ / lam + lam) / γ ^ 6)
      G hreg hδ0 hγ0 hγ1 h8 hl0 hl1 hθ0 hθ1 hθγ
      (by rw [hθl]; exact hlγ) hKpos le_rfl hSg hK1 hKg (Nat.le_add_right _ _)
      (Nat.le_add_left _ _) (le_of_eq (by rw [hθ]; exact three_error_eq hγ0)) hF hexp χ hχ hsize
    have hbound := three_uncovered_le (F := lam) hδ0 hγ0 hγ1 hl0 hl1.le le_rfl
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hmain
    linarith
  · -- the bound is at least `1`
    have hbig := three_trivial_bound hδ0 hγ0 hγ1 hl0 hl1.le hgood
    have : (1 - 42467332 * (lam + δ / lam) / γ ^ 8) * G.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    exact this.trans (Nat.cast_nonneg _)

open Classical in
/-- **Theorem 1.3** of [BHSV25], full version (Theorem 7.9). -/
theorem threeColoring_balanced :
    ∃ C : ℕ, ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ γ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < γ → γ < c₀ →
      0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ χ : Fin G.1 → Fin 3, G.IsAlmostProper χ δ ∧
              ∀ a, ((Finset.univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - γ) * G.1) →
            G.IsColoring 3 (B * (lam + δ / lam) / γ ^ 8) (A G) := by
  obtain ⟨C, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ expAlg z.1 z.2)
    expAlg_polytime
  refine ⟨C, 42467332, 1 / 2, by norm_num, fun δ γ lam hδ0 _ hγ0 hγc hl0 hlc ↦ ?_⟩
  obtain ⟨p, hp⟩ := exists_three_params hδ0 hγ0 hγc hl0 hlc
  obtain ⟨Kt, hKt⟩ := hrun p
  exact ⟨Kt, _, hKt, hp.2⟩

end Alg

end BHSV25
