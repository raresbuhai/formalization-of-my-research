module

public import BHSV25.Alg.IndepSetSpectral
public import BHSV25.Alg.IndepSetParams
public import Background.PolyTime.Rat

/-!
# Theorem 1.1: independent sets in one-sided expanders

[BHSV25, Theorem 1.1] in the form of Corollary 7.21 (`BHSV25.Alg.independentSet_approximation`):
for every `λ ∈ (0, 1)` and every `t`, a polynomial-time algorithm that, on regular graphs with at
most `t` eigenvalues larger than `λ` and an independent set of `(1/2 - γ) n` vertices,
`γ ∈ [0, 1/10]`, outputs an independent set of at least `(1/2 - (5 + f λ) γ) n` vertices, where
`f = BHSV25.Alg.indepLoss` tends to `0` as `λ → 0`.

## The algorithm (`BHSV25.Alg.indepAlg`)

For rational thresholds `θ₀ < θ' < θ < θ₁` and a precision `κ < θ₁ / 2` (the parameters of
`BHSV25/Alg/IndepSetParams.lean`), the net of `BHSV25.Net.exists_bottomNet` lists vectors containing
one within `κ / n` of every vector of norm at most `1` in the span of the eigenvectors with
eigenvalue at most `-θ`. Each vector `c` gives the candidate set `{x : c_x ≥ 0}`
(`BHSV25.Alg.thrBits`), rounded to an independent set by removing a greedy maximal matching
(`BHSV25.Alg.roundIndep`); so does the set of all vertices. The algorithm outputs the largest
result (`BHSV25.Alg.bestOf`).

## Why it works

By [BHSV25, Corollary 4.2] the graph has few eigenvalues at most `-θ'`, so the net applies. One
algorithm serves every `γ`: the net's precision `κ / n` is absorbed by the loss whenever
`|I| < n / 2`, and recovers `I` exactly when `|I| = n / 2`
(`BHSV25.Alg.card_roundIndep_thrBits_ge`). Graphs without edges (degree `0`) are handled by the
candidate of all vertices, and the empty graph trivially.

`BHSV25.Alg.exists_indepAlg` states the guarantee of the concrete algorithm, which Corollary 1.2
also uses (`BHSV25/Alg/VertexCover.lean`).
-/

@[expose] public section

namespace BHSV25.Alg

open Filter Topology Turing.MultiTapeTM ComputableInPolyTime Matrix
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The largest candidate -/

/-- Keep the larger of `acc` and `r`, by their numbers of members among the first `n`. -/
def bestStep (n : ℕ) (acc r : List Bool) : List Bool :=
  if numTrue n acc < numTrue n r then r else acc

/-- The candidate with the most members, among `init` and the list `L`. -/
def bestOf (n : ℕ) (init : List Bool) (L : List (List Bool)) : List Bool :=
  L.foldl (bestStep n) init

theorem le_numTrue_bestStep_left (n : ℕ) (acc r : List Bool) :
    numTrue n acc ≤ numTrue n (bestStep n acc r) := by
  unfold bestStep
  split_ifs with h
  · exact h.le
  · exact le_rfl

theorem le_numTrue_bestStep_right (n : ℕ) (acc r : List Bool) :
    numTrue n r ≤ numTrue n (bestStep n acc r) := by
  unfold bestStep
  split_ifs with h
  · exact le_rfl
  · exact not_lt.1 h

theorem bestOf_mem (n : ℕ) (init : List Bool) (L : List (List Bool)) :
    bestOf n init L = init ∨ bestOf n init L ∈ L := by
  induction L generalizing init with
  | nil => exact Or.inl rfl
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    rcases ih (bestStep n init e) with h | h
    · unfold bestOf at h
      rw [h]
      unfold bestStep
      split_ifs
      · exact Or.inr List.mem_cons_self
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem le_numTrue_bestOf_init (n : ℕ) (init : List Bool) (L : List (List Bool)) :
    numTrue n init ≤ numTrue n (bestOf n init L) := by
  induction L generalizing init with
  | nil => exact le_rfl
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    exact (le_numTrue_bestStep_left n init e).trans (ih _)

theorem le_numTrue_bestOf {n : ℕ} {init r : List Bool} {L : List (List Bool)} (hr : r ∈ L) :
    numTrue n r ≤ numTrue n (bestOf n init L) := by
  induction L generalizing init with
  | nil => simp at hr
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hr with rfl | hr
    · exact (le_numTrue_bestStep_right n init r).trans (le_numTrue_bestOf_init n _ L)
    · exact ih hr

/-! ### The algorithm -/

/-- **The algorithm** of [BHSV25, Theorem 7.20], for a net `net`: the largest of the roundings of
all vertices and of the sets `{x : c_x ≥ 0}` for the vectors `c` of the net. -/
def indepAlg (net : ℕ × List Bool → List (List ℚ)) (x : ℕ × List Bool) : List Bool :=
  bestOf (numV x) (roundIndep (numV x) x.2 (List.replicate (numV x) true))
    ((net x).map fun c ↦ roundIndep (numV x) x.2 (thrBits (numV x) c))

theorem isIndepSet_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    G.2.IsIndepSet (G.vertexSet (indepAlg net (G.1, adjTable G)) : Set (Fin G.1)) := by
  unfold indepAlg
  rw [numV_graph]
  rcases bestOf_mem G.1 (roundIndep G.1 (adjTable G) (List.replicate G.1 true))
    ((net (G.1, adjTable G)).map fun c ↦ roundIndep G.1 (adjTable G) (thrBits G.1 c)) with h | h
  · rw [h]
    exact isIndepSet_roundIndep G _
  · obtain ⟨c, -, hc⟩ := List.mem_map.1 h
    rw [← hc]
    exact isIndepSet_roundIndep G _

theorem card_init_le_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    (G.vertexSet (roundIndep G.1 (adjTable G) (List.replicate G.1 true))).card ≤
      (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  unfold indepAlg
  rw [numV_graph, card_vertexSet, card_vertexSet]
  exact le_numTrue_bestOf_init _ _ _

theorem card_cand_le_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) {c : List ℚ}
    (hc : c ∈ net (G.1, adjTable G)) :
    (G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card ≤
      (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  unfold indepAlg
  rw [numV_graph, card_vertexSet, card_vertexSet]
  exact le_numTrue_bestOf (List.mem_map.2 ⟨c, hc, rfl⟩)

/-! ### Polynomial time -/

theorem thrBits_polytime : ComputableInPolyTime (fun x : ℕ × List ℚ ↦ thrBits x.1 x.2)
    (encPair encUnary (encList encRat)) encBits := by
  unfold thrBits
  have h : ComputableInPolyTime
      (fun x : ℕ × List ℚ ↦ (List.range x.1).map fun i ↦ decide (0 ≤ x.2.getD i 0))
      (encPair encUnary (encList encRat)) (encList encBool) :=
    mapWithInput (by fun_prop)
      (rat_le' (const 0) (listGetDWithInput (by fun_prop) (by fun_prop) 0))
  exact (bits_encList_polyTime encBool).2.comp h

@[fun_prop]
theorem thrBits' {n : α → ℕ} {c : α → List ℚ} (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime c input (encList encRat)) :
    ComputableInPolyTime (fun x ↦ thrBits (n x) (c x)) input encBits :=
  thrBits_polytime.comp (g := fun x ↦ (n x, c x)) (hn.prod hc)

theorem bestStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × List Bool) × List Bool ↦ bestStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encBits) encBits) encBits := by
  unfold bestStep
  exact ite_decide (unary_lt' (numTrue' ((fst _ _).comp (fst _ _)) ((snd _ _).comp (fst _ _)))
    (numTrue' ((fst _ _).comp (fst _ _)) (snd _ _))) (snd _ _) ((snd _ _).comp (fst _ _))

theorem bestOf' {n : α → ℕ} {init : α → List Bool} {L : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary) (hinit : ComputableInPolyTime init input encBits)
    (hL : ComputableInPolyTime L input (encList encBits)) :
    ComputableInPolyTime (fun x ↦ bestOf (n x) (init x) (L x)) input encBits := by
  unfold bestOf
  refine foldlWith_of_bounded_growth (par := n) (list := L) (init := init) (step := bestStep)
    hn hL hinit bestStep_polytime (growth := fun x ↦ (encList encBits (L x)).length)
    hL.polyBounded_length ?_
  intro x acc r hr
  have h := SizedListEncoding.length_elem_le (encA := encBits) (encL := encList encBits) _ _ hr
  unfold bestStep
  split_ifs <;> omega

/-- **The algorithm runs in polynomial time**, given a polynomial-time net. -/
theorem indepAlg_polytime {net : ℕ × List Bool → List (List ℚ)}
    (hnet : ComputableInPolyTime net (encPair encNat encBits) (encList (encList encRat))) :
    ComputableInPolyTime (indepAlg net) (encPair encNat encBits) encBits := by
  unfold indepAlg
  have hn : ComputableInPolyTime numV (encPair encNat encBits) encUnary := numV_polytime
  have hrep : ComputableInPolyTime (fun x : ℕ × List Bool ↦ List.replicate (numV x) true)
      (encPair encNat encBits) encBits :=
    (bits_encList_polyTime encBool).2.comp (replicate hn (const true))
  have hL : ComputableInPolyTime
      (fun x : ℕ × List Bool ↦ (net x).map fun c ↦ roundIndep (numV x) x.2 (thrBits (numV x) c))
      (encPair encNat encBits) (encList encBits) :=
    mapWithInput hnet (roundIndep' (hn.comp (fst _ _)) ((snd _ _).comp (fst _ _))
      (thrBits' (hn.comp (fst _ _)) (snd _ _)))
  exact bestOf' hn (roundIndep' hn (snd _ _) hrep) hL

/-! ### The size of the output -/

theorem vertexSet_replicate (G : Graph) : G.vertexSet (List.replicate G.1 true) = Finset.univ := by
  ext v
  simp [Graph.vertexSet, List.getD_eq_getElem?_getD]

open Classical in
/-- Without edges, the algorithm outputs all vertices. -/
theorem card_indepAlg_of_degree_zero (net : ℕ × List Bool → List (List ℚ)) (G : Graph)
    (hd : G.2.IsRegularOfDegree 0) : G.1 ≤ (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  have hI : G.2.IsIndepSet ((Finset.univ : Finset (Fin G.1)) : Set (Fin G.1)) := by
    intro u _ v _ _ hadj
    have h := hd u
    rw [SimpleGraph.degree, Finset.card_eq_zero] at h
    have hv : v ∈ G.2.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
    rw [h] at hv
    exact Finset.notMem_empty v hv
  have h := card_inter_le_card_roundIndep G (List.replicate G.1 true) hI
  rw [vertexSet_replicate, Finset.inter_self, Finset.sdiff_self, Finset.card_empty, add_zero,
    Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (card_init_le_indepAlg net G)

/-! ### Theorem 1.1 -/

/-- **The guarantee of the algorithm** [BHSV25, Corollary 7.21]: for `λ ∈ (0, 1)` and `t`, a
polynomial-time net for which the algorithm, on regular graphs with at most `t` eigenvalues larger
than `λ` and an independent set of `(1/2 - γ) n` vertices, `γ ≥ 0`, outputs at least
`(1/2 - (5 + f λ) γ) n` vertices. (It always outputs an independent set,
`BHSV25.Alg.isIndepSet_indepAlg`, and all vertices on graphs without edges,
`BHSV25.Alg.card_indepAlg_of_degree_zero`.) -/
theorem exists_indepAlg {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (t : ℕ) :
    ∃ net : ℕ × List Bool → List (List ℚ),
      ComputableInPolyTime net (encPair encNat encBits) (encList (encList encRat)) ∧
      ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
        ∀ γ : ℝ, 0 ≤ γ → G.HasIndepSet ((1 / 2 - γ) * G.1) →
          (1 / 2 - (5 + indepLoss lam) * γ) * G.1 ≤
            (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  classical
  -- the rational parameters
  obtain ⟨θ', hθ'1, hθ'2⟩ := exists_rat_btwn (thetaLow_lt_thetaUp h0 h1)
  obtain ⟨θ, hθ1, hθ2⟩ := exists_rat_btwn hθ'2
  obtain ⟨κ, hκ1, hκ2⟩ := exists_rat_btwn (half_pos (thetaUp_pos h0 h1))
  have hθ'pos : (0 : ℚ) < θ' := by exact_mod_cast (thetaLow_pos h0 h1).trans hθ'1
  have hθθ' : θ' < θ := by exact_mod_cast hθ1
  have hθlt : (θ : ℝ) < 1 := hθ2.trans (thetaUp_lt_one h0 h1)
  have hθlt1 : θ < 1 := by exact_mod_cast hθlt
  have hκpos : (0 : ℚ) < κ := by exact_mod_cast hκ1
  obtain ⟨net, hnet, hcorr⟩ :=
    Net.exists_bottomNet θ' θ κ hθ'pos hθθ' hθlt1 hκpos ⌊(t : ℝ) / tauOf lam ^ 2⌋₊
  have hK := const_le_indepLoss h0 h1 hθ2 hκ1 hκ2
  have hf0 := indepLoss_nonneg h0 h1
  refine ⟨net, hnet, fun G hreg ht ↦ ?_⟩
  rintro γ hγ0 ⟨I, hI, hIcard⟩
  set f := indepLoss lam with hf
  set out := (G.vertexSet (indepAlg net (G.1, adjTable G))).card with hout
  have h5f : 0 ≤ (5 + f) * γ := mul_nonneg (by linarith only [hf0]) hγ0
  have hhalf : (1 / 2 - (5 + f) * γ) * G.1 ≤ G.1 / 2 := by
    have := mul_nonneg h5f (Nat.cast_nonneg G.1 : (0 : ℝ) ≤ G.1)
    linarith only [this]
  obtain ⟨d, hd⟩ := hreg
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · -- no vertices
    have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  by_cases hd0 : d = 0
  · -- no edges
    subst hd0
    have h := card_indepAlg_of_degree_zero net G hd
    have h' : (G.1 : ℝ) ≤ out := by exact_mod_cast h
    have hn' : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    linarith only [hhalf, h', hn']
  -- the net applies
  have hT : (Finset.univ.filter fun i ↦ G.eig i ≤ -((θ' : ℚ) : ℝ)).card ≤
      ⌊(t : ℝ) / tauOf lam ^ 2⌋₊ := by
    refine (Finset.card_le_card fun i hi ↦ ?_).trans (card_eig_le_neg_thetaLow_le G h0 h1 ht)
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans (neg_le_neg hθ'1.le)⟩
  set w := Spectral.proj G.normAdj_isHermitian (· ≤ -(θ : ℝ)) (signVec I) with hw
  have hw1 : w ⬝ᵥ w ≤ 1 :=
    (proj_dot_self_le _ _ _).trans (signVec_dot_self hn I).le
  have hw2 : G.InEigSpan (· ≤ -(θ : ℝ)) w := Spectral.inEigSpan_proj _ _ _
  obtain ⟨c, hc, hcw⟩ := hcorr G ⟨d, hd⟩ hT w hw1 hw2
  have hcand := card_roundIndep_thrBits_ge G hd hd0 hn hI hθlt (thetaUp_pos h0 h1) hK.2 c hcw
  have hle : ((G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card : ℝ) ≤ out := by
    exact_mod_cast card_cand_le_indepAlg net G hc
  -- the arithmetic
  set g : ℝ := G.1 / 2 - I.card with hg
  have hg0 : 0 ≤ g := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith only [this, hg]
  have hgγ : g ≤ γ * G.1 := by linarith only [hIcard, hg]
  have hA1 := mul_le_mul_of_nonneg_right hK.1 hg0
  have hA2 := mul_le_mul_of_nonneg_left hgγ (by linarith only [hf0] : (0 : ℝ) ≤ 5 + f)
  linarith only [hcand, hle, hA1, hA2, hg]

/-- **Theorem 1.1** of [BHSV25] (Corollary 7.21): for every `λ ∈ (0, 1)` and every `t`, a
polynomial-time algorithm that, on regular graphs with at most `t` eigenvalues larger than `λ`
(`λ`-one-sided expanders for `t = 1`) and an independent set of `(1/2 - γ) n` vertices for some
`γ ∈ [0, 1/10]`, outputs an independent set of at least `(1/2 - (5 + f λ) γ) n` vertices, where
`f λ → 0` as `λ → 0`. -/
theorem independentSet_approximation :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
        ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 10 → G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - (5 + f lam) * γ) * G.1 ≤ (G.vertexSet (A G)).card := by
  refine ⟨indepLoss, tendsto_indepLoss, fun lam h0 h1 t ↦ ?_⟩
  obtain ⟨net, hnet, hcorr⟩ := exists_indepAlg h0 h1 t
  refine ⟨fun G ↦ indepAlg net (G.1, adjTable G), (indepAlg_polytime hnet).comp (of_eq fun _ ↦ rfl),
    fun G hreg ht ↦ ⟨isIndepSet_indepAlg net G, fun γ hγ0 _ hγ ↦ hcorr G hreg ht γ hγ0 hγ⟩⟩

end BHSV25.Alg
