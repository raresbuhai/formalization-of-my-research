module

public import BHSV25.Alg.GraphMachine

/-!
# Rounding an approximate independent set

[BHSV25, Lemma 7.24] (rounding an approximate independent set): from a set `S` of vertices,
remove both endpoints of every edge of a maximal matching inside `S`. What remains is an
independent set, and for every independent set `I`, each edge of the matching has an endpoint in
`S \ I`, so at most `2 |S \ I|` vertices are removed: what remains has at least
`|S ∩ I| - |S \ I|` vertices. (The paper removes a `2`-approximate vertex cover of the graph
induced by `S`; the endpoints of a maximal matching are the standard one.)

The matching is greedy: the pairs `(u, v)` of vertices are scanned in order, and both endpoints
of an edge are removed when both are still present (`BHSV25.Alg.removeMatching`, on lists of
vertex numbers).

## The interface

The input is a graph as the pair `(n, a)` of its number of vertices and its adjacency table, and a
set of vertices as membership bits, one per vertex (as `BHSV25.Graph.vertexSet` reads them; bits
past `n` are ignored). The output is the membership bits of the result, `n` of them.

* `BHSV25.Alg.roundIndep n a b`: the rounding.
* `BHSV25.Alg.isIndepSet_roundIndep`: the result is independent in `G`.
* `BHSV25.Alg.vertexSet_roundIndep_subset`: it is contained in the input set.
* `BHSV25.Alg.card_inter_le_card_roundIndep`: for every independent set `I` of `G`,
  `|S ∩ I| ≤ |result| + |S \ I|` (and `BHSV25.Alg.card_le_card_roundIndep_of_subset`, the paper's
  form, for `I ⊆ S`).
* `BHSV25.Alg.roundIndep_polytime` and `BHSV25.Alg.roundIndep'` (for `fun_prop`): polynomial time,
  with `n` in unary (`BHSV25.Alg.numV` computes it from the input of a graph).
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-! ### The algorithm -/

/-- One step of the greedy matching: if `u v` is an edge and both `u` and `v` are still in `s`,
remove them. -/
def matchStep (n : ℕ) (a : List Bool) (s : List ℕ) (e : ℕ × ℕ) : List ℕ :=
  if adjBit n a e.1 e.2 && decide (e.1 ∈ s) && decide (e.2 ∈ s) then
    s.filter fun w ↦ !decide (w = e.1) && !decide (w = e.2)
  else s

/-- All ordered pairs `(u, v)` of vertices `u, v < n`. -/
def vertexPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun u ↦ (List.range n).map fun v ↦ (u, v)

/-- **Removing a greedy maximal matching** from a list `s` of vertices. -/
def removeMatching (n : ℕ) (a : List Bool) (s : List ℕ) : List ℕ :=
  (vertexPairs n).foldl (matchStep n a) s

/-- **The rounding** [BHSV25, Lemma 7.24]: the set given by the bits `b`, minus both endpoints of
a greedy maximal matching inside it, as membership bits. -/
def roundIndep (n : ℕ) (a b : List Bool) : List Bool :=
  listToBits n (removeMatching n a (bitsToList n b))

theorem length_roundIndep (n : ℕ) (a b : List Bool) : (roundIndep n a b).length = n :=
  length_listToBits _ _

/-! ### The greedy matching on lists -/

theorem matchStep_sublist (n : ℕ) (a : List Bool) (s : List ℕ) (e : ℕ × ℕ) :
    List.Sublist (matchStep n a s e) s := by
  unfold matchStep
  split_ifs
  · exact List.filter_sublist
  · exact List.Sublist.refl _

theorem foldl_matchStep_sublist (n : ℕ) (a : List Bool) (L : List (ℕ × ℕ)) (s : List ℕ) :
    List.Sublist (L.foldl (matchStep n a) s) s := by
  induction L generalizing s with
  | nil => exact List.Sublist.refl _
  | cons e L ih => exact (ih _).trans (matchStep_sublist n a s e)

theorem removeMatching_sublist (n : ℕ) (a : List Bool) (s : List ℕ) :
    List.Sublist (removeMatching n a s) s :=
  foldl_matchStep_sublist n a _ s

/-- After the step of an edge, its endpoints are not both present. -/
theorem not_mem_and_mem_matchStep {n : ℕ} {a : List Bool} {s : List ℕ} {e : ℕ × ℕ}
    (h : adjBit n a e.1 e.2 = true) :
    ¬(e.1 ∈ matchStep n a s e ∧ e.2 ∈ matchStep n a s e) := by
  rintro ⟨h1, h2⟩
  unfold matchStep at h1 h2
  by_cases hc : (adjBit n a e.1 e.2 && decide (e.1 ∈ s) && decide (e.2 ∈ s)) = true
  · rw [ite_eq_left hc] at h1
    simp at h1
  · rw [ite_eq_right hc] at h1 h2
    simp [h, h1, h2] at hc

/-- After the scan, the endpoints of a scanned edge are not both present. -/
theorem foldl_matchStep_not_both {n : ℕ} {a : List Bool} (L : List (ℕ × ℕ)) (s : List ℕ) :
    ∀ e ∈ L, adjBit n a e.1 e.2 = true →
      ¬(e.1 ∈ L.foldl (matchStep n a) s ∧ e.2 ∈ L.foldl (matchStep n a) s) := by
  induction L generalizing s with
  | nil => intro e he; simp at he
  | cons e' L ih =>
    intro e he hadj
    rw [List.foldl_cons]
    rcases List.mem_cons.1 he with rfl | he
    · rintro ⟨h1, h2⟩
      have hsub := foldl_matchStep_sublist n a L (matchStep n a s e)
      exact not_mem_and_mem_matchStep hadj ⟨hsub.subset h1, hsub.subset h2⟩
    · exact ih _ e he hadj

theorem toFinset_matchStep (n : ℕ) (a : List Bool) (s : List ℕ) (e : ℕ × ℕ) :
    (matchStep n a s e).toFinset =
      if (adjBit n a e.1 e.2 && decide (e.1 ∈ s) && decide (e.2 ∈ s)) = true then
        s.toFinset \ {e.1, e.2}
      else s.toFinset := by
  unfold matchStep
  split_ifs
  · ext w
    simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · rfl

/-- The potential of a set of numbers with respect to a property `p`: its members with `p` minus
those without. -/
def potential (p : ℕ → Prop) [DecidablePred p] (S : Finset ℕ) : ℤ :=
  ((S.filter p).card : ℤ) - (S.filter fun w ↦ ¬p w).card

/-- Removing two members `u, v` of `S`, not both with `p`, does not decrease the potential. -/
theorem potential_le_sdiff (p : ℕ → Prop) [DecidablePred p] {S : Finset ℕ} {u v : ℕ}
    (hu : u ∈ S) (hv : v ∈ S) (h : ¬(p u ∧ p v)) : potential p S ≤ potential p (S \ {u, v}) := by
  have hT : ({u, v} : Finset ℕ) ⊆ S := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hu
    · rw [Finset.mem_singleton.1 hw]
      exact hv
  have key : ∀ (q : ℕ → Prop) [DecidablePred q],
      ((S \ {u, v}).filter q).card + (({u, v} : Finset ℕ).filter q).card = (S.filter q).card := by
    intro q _
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.sdiff_disjoint),
      ← Finset.filter_union, Finset.sdiff_union_of_subset hT]
  have h1 := key p
  have h2 := key fun w ↦ ¬p w
  have h3 : (({u, v} : Finset ℕ).filter p).card ≤
      (({u, v} : Finset ℕ).filter fun w ↦ ¬p w).card := by
    by_cases hpu : p u <;> by_cases hpv : p v
    · exact absurd ⟨hpu, hpv⟩ h
    · simp [Finset.filter_insert, Finset.filter_singleton, hpu, hpv]
    · simp [Finset.filter_insert, Finset.filter_singleton, hpu, hpv]
    · simp [Finset.filter_insert, Finset.filter_singleton, hpu, hpv]
  unfold potential
  omega

/-- **The potential does not decrease** along the scan, if no scanned edge has both endpoints
with `p`. -/
theorem potential_le_foldl_matchStep (p : ℕ → Prop) [DecidablePred p] {n : ℕ} {a : List Bool}
    (L : List (ℕ × ℕ)) (s : List ℕ)
    (hL : ∀ e ∈ L, adjBit n a e.1 e.2 = true → ¬(p e.1 ∧ p e.2)) :
    potential p s.toFinset ≤ potential p (L.foldl (matchStep n a) s).toFinset := by
  induction L generalizing s with
  | nil => exact le_rfl
  | cons e L ih =>
    rw [List.foldl_cons]
    refine le_trans ?_ (ih _ fun e' he' ↦ hL e' (List.mem_cons_of_mem _ he'))
    rw [toFinset_matchStep]
    split_ifs with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact potential_le_sdiff p (List.mem_toFinset.2 hc.1.2) (List.mem_toFinset.2 hc.2)
        (hL e List.mem_cons_self hc.1.1)
    · exact le_rfl

theorem mem_vertexPairs {n u v : ℕ} : (u, v) ∈ vertexPairs n ↔ u < n ∧ v < n := by
  simp [vertexPairs]

/-! ### Correctness -/

theorem mem_vertexSet_roundIndep (G : Graph) (b : List Bool) (v : Fin G.1) :
    v ∈ G.vertexSet (roundIndep G.1 (adjTable G) b) ↔
      (v : ℕ) ∈ removeMatching G.1 (adjTable G) (bitsToList G.1 b) :=
  mem_vertexSet_listToBits _ _ _

/-- The result is an independent set. -/
theorem isIndepSet_roundIndep (G : Graph) (b : List Bool) :
    G.2.IsIndepSet (G.vertexSet (roundIndep G.1 (adjTable G) b) : Set (Fin G.1)) := by
  intro u hu v hv _ hadj
  rw [Finset.mem_coe, mem_vertexSet_roundIndep] at hu hv
  refine foldl_matchStep_not_both _ _ ((u : ℕ), (v : ℕ)) (mem_vertexPairs.2 ⟨u.2, v.2⟩) ?_
    ⟨hu, hv⟩
  classical
  rw [adjBit_adjTable]
  exact decide_eq_true hadj

/-- The result is contained in the input set. -/
theorem vertexSet_roundIndep_subset (G : Graph) (b : List Bool) :
    G.vertexSet (roundIndep G.1 (adjTable G) b) ⊆ G.vertexSet b := by
  intro v hv
  rw [mem_vertexSet_roundIndep] at hv
  rw [mem_vertexSet_iff]
  exact (removeMatching_sublist _ _ _).subset hv

/-- **[BHSV25, Lemma 7.24]**: for every independent set `I`, the result has at least
`|S ∩ I| - |S \ I|` vertices, where `S` is the input set. -/
theorem card_inter_le_card_roundIndep (G : Graph) (b : List Bool) {I : Finset (Fin G.1)}
    (hI : G.2.IsIndepSet (I : Set (Fin G.1))) :
    (G.vertexSet b ∩ I).card ≤
      (G.vertexSet (roundIndep G.1 (adjTable G) b)).card + (G.vertexSet b \ I).card := by
  classical
  set J := I.map Fin.valEmbedding with hJ
  set R := removeMatching G.1 (adjTable G) (bitsToList G.1 b) with hR
  have hL : ∀ e ∈ vertexPairs G.1, adjBit G.1 (adjTable G) e.1 e.2 = true →
      ¬(e.1 ∈ J ∧ e.2 ∈ J) := by
    rintro ⟨x, y⟩ he hadj ⟨hx, hy⟩
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    have hadj' : G.2.Adj x' y' := by
      have h' : adjBit G.1 (adjTable G) x' y' = true := hadj
      exact of_decide_eq_true ((adjBit_adjTable G x' y').symm.trans h')
    exact hI (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hy') hadj'.ne hadj'
  have hpot := potential_le_foldl_matchStep (· ∈ J) _ (bitsToList G.1 b) hL
  have hS : (bitsToList G.1 b).toFinset = (G.vertexSet b).map Fin.valEmbedding :=
    (map_vertexSet G b).symm
  have hRmap : R.toFinset = (G.vertexSet (roundIndep G.1 (adjTable G) b)).map Fin.valEmbedding := by
    ext w
    rw [List.mem_toFinset, Finset.mem_map]
    constructor
    · intro hw
      have hlt : w < G.1 :=
        (mem_bitsToList.1 ((removeMatching_sublist _ _ _).subset hw)).1
      exact ⟨⟨w, hlt⟩, (mem_vertexSet_roundIndep G b ⟨w, hlt⟩).2 hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (mem_vertexSet_roundIndep G b v).1 hv
  have e1 : ((bitsToList G.1 b).toFinset.filter (· ∈ J)).card = (G.vertexSet b ∩ I).card := by
    rw [hS, Finset.filter_mem_eq_inter, ← Finset.map_inter, Finset.card_map]
  have e2 : ((bitsToList G.1 b).toFinset.filter fun w ↦ ¬w ∈ J).card =
      (G.vertexSet b \ I).card := by
    rw [hS, Finset.filter_notMem_eq_sdiff, ← Finset.map_sdiff, Finset.card_map]
  have e3 : (R.toFinset.filter (· ∈ J)).card + (R.toFinset.filter fun w ↦ ¬w ∈ J).card =
      (G.vertexSet (roundIndep G.1 (adjTable G) b)).card := by
    rw [Finset.card_filter_add_card_filter_not, hRmap, Finset.card_map]
  unfold potential at hpot
  rw [e1, e2] at hpot
  change _ ≤ ((R.toFinset.filter (· ∈ J)).card : ℤ) - (R.toFinset.filter fun w ↦ ¬w ∈ J).card
    at hpot
  omega

/-- **[BHSV25, Lemma 7.24]**, in the paper's form: for an independent set `I` contained in the
input set `S`, the result has at least `|I| - |S \ I|` vertices. -/
theorem card_le_card_roundIndep_of_subset (G : Graph) (b : List Bool) {I : Finset (Fin G.1)}
    (hI : G.2.IsIndepSet (I : Set (Fin G.1))) (hIS : I ⊆ G.vertexSet b) :
    I.card ≤ (G.vertexSet (roundIndep G.1 (adjTable G) b)).card + (G.vertexSet b \ I).card := by
  have h := card_inter_le_card_roundIndep G b hI
  rwa [Finset.inter_eq_right.2 hIS] at h

/-! ### Polynomial time -/

theorem length_encList_le_of_sublist {β : Type} (enc : β ↪ List Bool) {l l' : List β}
    (h : List.Sublist l l') : (encList enc l).length ≤ (encList enc l').length := by
  rw [length_encList, length_encList]
  exact (h.map _).sum_le_sum fun _ _ ↦ Nat.zero_le _

theorem vertexPairs_polytime :
    ComputableInPolyTime vertexPairs encUnary (encList (encPair encUnary encUnary)) := by
  unfold vertexPairs
  exact flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

theorem matchStep_polytime : ComputableInPolyTime
    (fun p : ((ℕ × List Bool) × List ℕ) × (ℕ × ℕ) ↦ matchStep p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encBits) (encList encUnary)) (encPair encUnary encUnary))
    (encList encUnary) := by
  unfold matchStep
  refine ite' (bool_and' (bool_and' (adjBit' (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)) (decide_mem (by fun_prop) (by fun_prop)))
    (decide_mem (by fun_prop) (by fun_prop))) ?_ (by fun_prop)
  exact filterWithInput (by fun_prop)
    (bool_and' (bool_not.comp (unary_eq' (by fun_prop) (by fun_prop)))
      (bool_not.comp (unary_eq' (by fun_prop) (by fun_prop))))

theorem removeMatching_polytime : ComputableInPolyTime
    (fun x : (ℕ × List Bool) × List ℕ ↦ removeMatching x.1.1 x.1.2 x.2)
    (encPair (encPair encUnary encBits) (encList encUnary)) (encList encUnary) := by
  unfold removeMatching
  refine foldlWith_of_bounded_growth (par := fun x : (ℕ × List Bool) × List ℕ ↦ x.1)
    (list := fun x ↦ vertexPairs x.1.1) (init := fun x ↦ x.2)
    (step := fun p s e ↦ matchStep p.1 p.2 s e) (fst _ _)
    (vertexPairs_polytime.comp (by fun_prop)) (snd _ _) matchStep_polytime
    (growth := fun _ ↦ 0) (PolyBounded.const 0) ?_
  intro x s e _
  exact (length_encList_le_of_sublist _ (matchStep_sublist _ _ s e)).trans (Nat.le_add_right _ _)

@[fun_prop]
theorem removeMatching' {n : α → ℕ} {a : α → List Bool} {s : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (ha : ComputableInPolyTime a input encBits)
    (hs : ComputableInPolyTime s input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ removeMatching (n x) (a x) (s x)) input (encList encUnary) :=
  removeMatching_polytime.comp (g := fun x ↦ ((n x, a x), s x)) ((hn.prod ha).prod hs)

/-- The rounding runs in polynomial time, with the number of vertices in unary. -/
theorem roundIndep_polytime : ComputableInPolyTime
    (fun x : (ℕ × List Bool) × List Bool ↦ roundIndep x.1.1 x.1.2 x.2)
    (encPair (encPair encUnary encBits) encBits) encBits := by
  unfold roundIndep
  exact listToBits' (by fun_prop) (removeMatching' (by fun_prop) (by fun_prop)
    (bitsToList' (by fun_prop) (by fun_prop)))

@[fun_prop]
theorem roundIndep' {n : α → ℕ} {a b : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (ha : ComputableInPolyTime a input encBits) (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x ↦ roundIndep (n x) (a x) (b x)) input encBits :=
  roundIndep_polytime.comp (g := fun x ↦ ((n x, a x), b x)) ((hn.prod ha).prod hb)

end BHSV25.Alg
