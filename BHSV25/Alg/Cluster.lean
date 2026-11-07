module

public import BHSV25.Alg.Rounding
public import Background.Tuples

/-!
# The clustering algorithm

The algorithm of [BHSV25, Theorems 5.1, 7.1 and 7.9] as a function on the input of a graph
(`BHSV25.Alg.clusterAlg`), given a map `net` from the input to a list of rational vectors (the
net of an eigenspace of `BHSV25/Net/Spec.lean`), a number `m` of clusters and the color `K ≥ m`
that marks uncolored vertices:

1. **Candidates.** For every `m`-tuple of vectors `u₀, …, u_{m-1}` of the net and every `m`-tuple
   of vertices `x₀, …, x_{m-1}`, put each vertex `y` in the cluster `a` of the representative
   `x_a` nearest to it in the coordinates of the `u_j`: `a` minimizes
   `∑_j (u_j[y] - u_j[x_a])²` (`BHSV25.Alg.clusters`, the first minimizer).
2. **Rounding** [BHSV25, Lemma 7.23]: round each cluster to an independent set
   (`BHSV25.Alg.roundIndep`); a vertex keeps the color of its cluster if it survives, and gets `K`
   otherwise (`BHSV25.Alg.colorOf`).
3. **Selection**: output the candidate with the most colored vertices
   (`BHSV25.Alg.bestColoring`).

The paper's Algorithm 3 guesses the centers of the clusters on a grid of resolution
`Θ(1/√n)`; guessing a vertex of each cluster as its center (`n^m` guesses) does the same without
a grid.

The correctness facts here are combinatorial (`BHSV25.Alg.clusterAlg_spec`): the output is a
partial `K`-coloring, and for every candidate partition `R₀, …, R_{m-1}` and independent sets
`I₀, …, I_{m-1}`, it colors at least `∑_a (|R_a ∩ I_a| - |R_a \ I_a|)` vertices. Which candidate
is good is the analysis of `BHSV25/Alg/Partition.lean`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset

/-! ### Clustering -/

/-- The squared distance `∑_j (u_j[y] - u_j[x])²` between the vertices `y` and `x` in the
coordinates given by the vectors `us`. -/
def sqDist (us : List (List ℚ)) (y x : ℕ) : ℚ :=
  (us.map fun u ↦ (u.getD y 0 - u.getD x 0) ^ 2).sum

/-- One step of the search for a minimizer: `a` replaces the current `best` if it is strictly
better. -/
def argminStep (f : ℕ → ℚ) (best a : ℕ) : ℕ := if f a < f best then a else best

/-- The first `a < m` minimizing `f` (`0` if `m = 0`). -/
def argminBelow (f : ℕ → ℚ) (m : ℕ) : ℕ := (List.range m).foldl (argminStep f) 0

/-- The cluster of the vertex `y`: the index of the representative in `xs` nearest to it. -/
def clusterIdx (us : List (List ℚ)) (xs : List ℕ) (y : ℕ) : ℕ :=
  argminBelow (fun a ↦ sqDist us y (xs.getD a 0)) xs.length

/-- The clusters of the vertices `0, …, n - 1`. -/
def clusters (n : ℕ) (us : List (List ℚ)) (xs : List ℕ) : List ℕ :=
  (List.range n).map (clusterIdx us xs)

/-! ### Rounding the clusters -/

/-- The membership bits of the part `a` of a partition `p` of the vertices `0, …, n - 1` into
`m` parts. -/
def classBits (n m : ℕ) (p : List ℕ) (a : ℕ) : List Bool :=
  (List.range n).map fun y ↦ decide (p.getD y m = a)

/-- The parts of `p`, each rounded to an independent set. -/
def roundedClasses (n m : ℕ) (adj : List Bool) (p : List ℕ) : List (List Bool) :=
  (List.range m).map fun a ↦ roundIndep n adj (classBits n m p a)

/-- The coloring given by rounded parts `rs` of a partition `p`: a vertex keeps its part if it is
in the rounded part, and gets `K` otherwise. -/
def colorWith (n m K : ℕ) (rs : List (List Bool)) (p : List ℕ) : List ℕ :=
  (List.range n).map fun y ↦ if (rs.getD (p.getD y m) []).getD y false then p.getD y m else K

/-- The coloring obtained by rounding every part of `p`. -/
def colorOf (n m K : ℕ) (adj : List Bool) (p : List ℕ) : List ℕ :=
  colorWith n m K (roundedClasses n m adj p) p

/-! ### Choosing the best coloring -/

/-- The number of vertices `y < n` with a color `< K`. -/
def numCol (n K : ℕ) (c : List ℕ) : ℕ :=
  ((List.range n).filter fun y ↦ decide (c.getD y K < K)).length

/-- One step of the selection: keep the coloring with more colored vertices. -/
def bestColorStep (n K : ℕ) (b c : List ℕ) : List ℕ :=
  if numCol n K b < numCol n K c then c else b

/-- The coloring with the most colored vertices (the first one, or `[]` if there is none). -/
def bestColoring (n K : ℕ) (cs : List (List ℕ)) : List ℕ :=
  cs.foldl (bestColorStep n K) []

/-! ### The algorithm -/

/-- The number of tuples to try: `(n + N + 1)^m`, more than `n^m` and `N^m`. -/
def clusterBudget (n N m : ℕ) : ℕ := (n + N + 1) ^ m

/-- **The candidates**: for every `m`-tuple of vectors of `U` and every `m`-tuple of vertices,
the rounded clusters. -/
def candidates (n m K : ℕ) (adj : List Bool) (U : List (List ℚ)) : List (List ℕ) :=
  (Tuples.tuples (clusterBudget n U.length m) U.length m).flatMap fun is ↦
    (Tuples.tuples (clusterBudget n U.length m) n m).map fun xs ↦
      colorOf n m K adj (clusters n (is.map fun i ↦ U.getD i []) xs)

/-- **The clustering algorithm** with `m` clusters, uncolored vertices marked `K`, and the net
`net`: the best candidate. -/
def clusterAlg (m K : ℕ) (net : ℕ × List Bool → List (List ℚ)) (x : ℕ × List Bool) :
    List ℕ :=
  bestColoring (numV x) K (candidates (numV x) m K x.2 (net x))

/-! ### The search for a minimizer -/

theorem argminBelow_spec (f : ℕ → ℚ) (i : ℕ) :
    (argminBelow f i = 0 ∨ argminBelow f i < i) ∧ ∀ j < i, f (argminBelow f i) ≤ f j := by
  induction i with
  | zero => simp [argminBelow]
  | succ i ih =>
    have hstep : argminBelow f (i + 1) = argminStep f (argminBelow f i) i := by
      rw [argminBelow, List.range_succ, List.foldl_append]
      rfl
    rw [hstep, argminStep]
    obtain ⟨h1, h2⟩ := ih
    split_ifs with h
    · refine ⟨Or.inr (Nat.lt_succ_self i), fun j hj ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h.le.trans (h2 j hj)
      · exact le_rfl
    · refine ⟨h1.imp_right fun h' ↦ h'.trans (Nat.lt_succ_self i), fun j hj ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 j hj
      · exact not_lt.1 h

theorem argminBelow_lt (f : ℕ → ℚ) {m : ℕ} (hm : 0 < m) : argminBelow f m < m := by
  rcases (argminBelow_spec f m).1 with h | h
  · rw [h]
    exact hm
  · exact h

/-- The strict minimizer is found. -/
theorem argminBelow_eq (f : ℕ → ℚ) {m a : ℕ} (ha : a < m) (h : ∀ b < m, b ≠ a → f a < f b) :
    argminBelow f m = a := by
  by_contra hne
  have hlt := argminBelow_lt f (lt_of_le_of_lt (Nat.zero_le a) ha)
  have h1 := (argminBelow_spec f m).2 a ha
  have h2 := h _ hlt hne
  exact absurd h1 (not_le.2 h2)

theorem clusterIdx_lt (us : List (List ℚ)) {xs : List ℕ} (hxs : 0 < xs.length) (y : ℕ) :
    clusterIdx us xs y < xs.length :=
  argminBelow_lt _ hxs

/-- A vertex strictly nearest to the representative `x_a` is put in the cluster `a`. -/
theorem clusterIdx_eq (us : List (List ℚ)) (xs : List ℕ) (y : ℕ) {a : ℕ} (ha : a < xs.length)
    (h : ∀ b < xs.length, b ≠ a → sqDist us y (xs.getD a 0) < sqDist us y (xs.getD b 0)) :
    clusterIdx us xs y = a :=
  argminBelow_eq _ ha h

theorem getD_clusters {n : ℕ} (us : List (List ℚ)) (xs : List ℕ) {y : ℕ} (hy : y < n) (d : ℕ) :
    (clusters n us xs).getD y d = clusterIdx us xs y := by
  rw [List.getD_eq_getElem _ _ (by simp [clusters, hy])]
  simp [clusters]

/-! ### The rounded coloring -/

variable (G : Graph)

/-- The part `a` of a partition `p`, as a set of vertices. -/
def classSet (m : ℕ) (p : List ℕ) (a : ℕ) : Finset (Fin G.1) :=
  univ.filter fun v ↦ p.getD v m = a

/-- The part `a` of `p`, rounded. -/
noncomputable def roundedSet (m : ℕ) (p : List ℕ) (a : ℕ) : Finset (Fin G.1) :=
  G.vertexSet (roundIndep G.1 (adjTable G) (classBits G.1 m p a))

theorem vertexSet_classBits (m : ℕ) (p : List ℕ) (a : ℕ) :
    G.vertexSet (classBits G.1 m p a) = classSet G m p a := by
  ext v
  rw [Graph.vertexSet, classSet, mem_filter, mem_filter,
    List.getD_eq_getElem _ _ (by simp [classBits])]
  simp [classBits]

theorem roundedSet_subset (m : ℕ) (p : List ℕ) (a : ℕ) :
    roundedSet G m p a ⊆ classSet G m p a := by
  rw [← vertexSet_classBits]
  exact vertexSet_roundIndep_subset G _

theorem getD_roundedClasses (m : ℕ) (p : List ℕ) {a : ℕ} (ha : a < m) :
    (roundedClasses G.1 m (adjTable G) p).getD a [] =
      roundIndep G.1 (adjTable G) (classBits G.1 m p a) := by
  rw [List.getD_eq_getElem _ _ (by simp [roundedClasses, ha])]
  simp [roundedClasses]

theorem color_colorOf (m K : ℕ) (p : List ℕ) (hp : ∀ v : Fin G.1, p.getD v m < m)
    (v : Fin G.1) :
    G.color K (colorOf G.1 m K (adjTable G) p) v =
      if v ∈ roundedSet G m p (p.getD v m) then p.getD v m else K := by
  rw [Graph.color, colorOf, colorWith, List.getD_eq_getElem _ _ (by simp),
    List.getElem_map, List.getElem_range, getD_roundedClasses G m p (hp v)]
  simp only [roundedSet, Graph.vertexSet, mem_filter, mem_univ, true_and]

/-- The rounded coloring is a partial `K`-coloring. -/
theorem isPartialColoring_colorOf {m K : ℕ} (_hmK : m ≤ K) (p : List ℕ)
    (hp : ∀ v : Fin G.1, p.getD v m < m) :
    G.IsPartialColoring K (colorOf G.1 m K (adjTable G) p) := by
  intro u v huv hu heq
  rw [color_colorOf G m K p hp u] at hu heq
  rw [color_colorOf G m K p hp v] at heq
  split_ifs at hu heq with h1 h2 h2
  · -- both rounded, same part
    rw [heq] at h1
    exact (isIndepSet_roundIndep G (classBits G.1 m p (p.getD v m))) h1 h2 huv.ne huv
  · exact absurd heq (by have := hp u; omega)
  · omega
  · omega

/-- The rounded coloring colors the vertices of the rounded parts. -/
theorem numColored_colorOf {m K : ℕ} (hmK : m ≤ K) (p : List ℕ)
    (hp : ∀ v : Fin G.1, p.getD v m < m) :
    G.numColored K (colorOf G.1 m K (adjTable G) p) = ∑ a ∈ range m, (roundedSet G m p a).card := by
  have hdisj : (↑(range m) : Set ℕ).PairwiseDisjoint (roundedSet G m p) := by
    intro a _ b _ hab
    refine disjoint_left.2 fun v hva hvb ↦ hab ?_
    have h1 := roundedSet_subset G m p a hva
    have h2 := roundedSet_subset G m p b hvb
    rw [classSet, mem_filter] at h1 h2
    exact h1.2.symm.trans h2.2
  rw [← card_biUnion hdisj, Graph.numColored]
  congr 1
  ext v
  rw [mem_filter, mem_biUnion, color_colorOf G m K p hp v]
  simp only [mem_univ, true_and, mem_range]
  constructor
  · intro h
    split_ifs at h with h1
    · exact ⟨_, hp v, h1⟩
    · omega
  · rintro ⟨a, ha, hv⟩
    have h1 := roundedSet_subset G m p a hv
    rw [classSet, mem_filter] at h1
    rw [h1.2, ite_eq_left hv]
    omega

/-- **Accounting of the rounding** [BHSV25, Lemma 7.24]: for independent sets `I_a`, the rounded
coloring colors at least `∑_a max(0, |R_a ∩ I_a| - |R_a \ I_a|)` vertices. -/
theorem sum_card_inter_le {m K : ℕ} (hmK : m ≤ K) (p : List ℕ)
    (hp : ∀ v : Fin G.1, p.getD v m < m) (I : ℕ → Finset (Fin G.1))
    (hI : ∀ a, G.2.IsIndepSet (I a : Set (Fin G.1))) :
    ∑ a ∈ range m, max 0 (((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card) ≤
      G.numColored K (colorOf G.1 m K (adjTable G) p) := by
  rw [numColored_colorOf G hmK p hp, Nat.cast_sum]
  refine sum_le_sum fun a _ ↦ max_le (Nat.cast_nonneg _) ?_
  have h := card_inter_le_card_roundIndep G (classBits G.1 m p a) (hI a)
  rw [vertexSet_classBits] at h
  have h' : ((classSet G m p a ∩ I a).card : ℝ) ≤
      (roundedSet G m p a).card + (classSet G m p a \ I a).card := by exact_mod_cast h
  linarith

/-! ### The selection -/

theorem numColored_eq_numCol (K : ℕ) (c : List ℕ) : G.numColored K c = numCol G.1 K c := by
  rw [Graph.numColored, numCol, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  refine card_bij (fun v _ ↦ (v : ℕ)) (fun v hv ↦ ?_) (fun _ _ _ _ h ↦ Fin.ext h)
    (fun y hy ↦ ?_)
  · rw [mem_filter] at hv
    simpa [Graph.color] using And.intro v.2 hv.2
  · simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
    exact ⟨⟨y, hy.1⟩, by simpa [Graph.color] using hy.2, rfl⟩

theorem bestColoring_spec (n K : ℕ) (cs : List (List ℕ)) :
    (bestColoring n K cs ∈ cs ∨ bestColoring n K cs = []) ∧
      ∀ c ∈ cs, numCol n K c ≤ numCol n K (bestColoring n K cs) := by
  suffices ∀ (cs : List (List ℕ)) (b : List ℕ),
      (cs.foldl (bestColorStep n K) b ∈ cs ∨ cs.foldl (bestColorStep n K) b = b) ∧
        numCol n K b ≤ numCol n K (cs.foldl (bestColorStep n K) b) ∧
        ∀ c ∈ cs, numCol n K c ≤ numCol n K (cs.foldl (bestColorStep n K) b) by
    obtain ⟨h1, -, h3⟩ := this cs []
    exact ⟨h1, h3⟩
  intro cs
  induction cs with
  | nil => simp
  | cons c cs ih =>
    intro b
    obtain ⟨h1, h2, h3⟩ := ih (bestColorStep n K b c)
    simp only [List.foldl_cons, List.mem_cons]
    have hb : numCol n K b ≤ numCol n K (bestColorStep n K b c) ∧
        numCol n K c ≤ numCol n K (bestColorStep n K b c) := by
      unfold bestColorStep
      split_ifs with h <;> omega
    refine ⟨?_, hb.1.trans h2, ?_⟩
    · rcases h1 with h | h
      · exact Or.inl (Or.inr h)
      · rw [h, bestColorStep]
        split_ifs
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr rfl
    · rintro c' (rfl | hc')
      · exact hb.2.trans h2
      · exact h3 c' hc'

/-! ### The candidates -/

theorem colorOf_mem_candidates (n m K : ℕ) (adj : List Bool) (U : List (List ℚ))
    (us : Fin m → List ℚ) (hus : ∀ j, us j ∈ U) (xs : Fin m → Fin n) :
    colorOf n m K adj (clusters n (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ))) ∈
      candidates n m K adj U := by
  rw [candidates, List.mem_flatMap]
  have hU : ∀ j, U.idxOf (us j) < U.length := fun j ↦ List.idxOf_lt_length_of_mem (hus j)
  have hle1 : U.length ^ m ≤ clusterBudget n U.length m :=
    Nat.pow_le_pow_left (by omega) m
  have hle2 : n ^ m ≤ clusterBudget n U.length m := Nat.pow_le_pow_left (by omega) m
  refine ⟨List.ofFn fun j ↦ ((⟨U.idxOf (us j), hU j⟩ : Fin U.length) : ℕ),
    Tuples.ofFn_mem_tuples hle1 _, List.mem_map.2 ⟨_, Tuples.ofFn_mem_tuples hle2 xs, ?_⟩⟩
  congr 3
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (hU j), List.getElem_idxOf]

/-! ### The algorithm on a graph -/

/-- **What the algorithm guarantees**, for `1 ≤ m ≤ K`: a partial `K`-coloring that, for every
candidate (vectors `us` of the net and representatives `xs`) and all independent sets `I_a`, colors
at least `∑_a max(0, |R_a ∩ I_a| - |R_a \ I_a|)` vertices, where `R_a` are the clusters. -/
theorem clusterAlg_spec {m K : ℕ} (hm : 0 < m) (hmK : m ≤ K)
    (net : ℕ × List Bool → List (List ℚ)) :
    G.IsPartialColoring K (clusterAlg m K net (G.1, adjTable G)) ∧
      ∀ (us : Fin m → List ℚ), (∀ j, us j ∈ net (G.1, adjTable G)) →
      ∀ (xs : Fin m → Fin G.1) (I : ℕ → Finset (Fin G.1)),
        (∀ a, G.2.IsIndepSet (I a : Set (Fin G.1))) →
        ∑ a ∈ range m, max 0
          (((classSet G m (clusters G.1 (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ))) a ∩
            I a).card : ℝ) -
          (classSet G m (clusters G.1 (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ))) a \
            I a).card) ≤
          G.numColored K (clusterAlg m K net (G.1, adjTable G)) := by
  have hp : ∀ (us : List (List ℚ)) (xs : Fin m → Fin G.1) (v : Fin G.1),
      (clusters G.1 us (List.ofFn fun j ↦ (xs j : ℕ))).getD v m < m := by
    intro us xs v
    rw [getD_clusters _ _ v.2]
    have := clusterIdx_lt us (xs := List.ofFn fun j ↦ (xs j : ℕ)) (by simpa using hm) v
    simpa using this
  have hrun : clusterAlg m K net (G.1, adjTable G) =
      bestColoring G.1 K (candidates G.1 m K (adjTable G) (net (G.1, adjTable G))) := by
    rw [clusterAlg, numV_graph]
  obtain ⟨hmem, hbest⟩ :=
    bestColoring_spec G.1 K (candidates G.1 m K (adjTable G) (net (G.1, adjTable G)))
  rw [hrun]
  refine ⟨?_, fun us hus xs I hI ↦ ?_⟩
  · rcases hmem with h | h
    · generalize bestColoring G.1 K (candidates G.1 m K (adjTable G) (net (G.1, adjTable G))) = b
        at h ⊢
      rw [candidates, List.mem_flatMap] at h
      obtain ⟨is, -, h⟩ := h
      obtain ⟨xs', hxs', hc⟩ := List.mem_map.1 h
      obtain ⟨hlen, -⟩ := Tuples.mem_tuples_le hxs'
      rw [← hc]
      refine isPartialColoring_colorOf G hmK _ fun v ↦ ?_
      rw [getD_clusters _ _ v.2]
      exact hlen ▸ clusterIdx_lt _ (by omega) v
    · rw [h]
      intro u v _ hu
      simp [Graph.color] at hu
  · have hc := colorOf_mem_candidates G.1 m K (adjTable G) _ us hus xs
    have h1 := sum_card_inter_le G hmK _ (hp (List.ofFn us) xs) I hI
    have h2 := hbest _ hc
    rw [← numColored_eq_numCol, ← numColored_eq_numCol] at h2
    have h2' : (G.numColored K (colorOf G.1 m K (adjTable G)
        (clusters G.1 (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ)))) : ℝ) ≤
        G.numColored K
          (bestColoring G.1 K (candidates G.1 m K (adjTable G) (net (G.1, adjTable G)))) := by
      exact_mod_cast h2
    linarith

end Alg

end BHSV25
