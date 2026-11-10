module

public import BHSV25.Alg.IndepSet

/-!
# Vertex covers and complements

The complement of a set of vertices given by bits (`BHSV25.Alg.compBits`), in polynomial time; the
complement of a vertex cover is an independent set (`BHSV25.Alg.isIndepSet_compl_of_isVertexCover`),
and a minimum vertex cover exists (`BHSV25.Alg.exists_vertexCover_card`). Corollary 1.2 outputs
the complement of an independent set (`BHSV25/Alg/VertexCoverFull.lean`).
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

end BHSV25.Alg
