module

public import BHSV25.Model
public import Background.PolyTime.Lists
public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
public import Mathlib.Data.List.GetD

/-!
# Graphs as inputs of machines

The algorithms of [BHSV25] read a graph as the pair `(n, a)` of its number of vertices, in binary,
and its adjacency table `a` (`BHSV25.encGraph`). This file provides what they share to read such
inputs and to handle sets of vertices, with polynomial-time certificates in the style of
complexitylib (`Turing.MultiTapeTM.ComputableInPolyTime`, registered with `fun_prop`).

* **The number of vertices in unary** (`BHSV25.Alg.numV`): `n`, capped at `|a| + 1`, so that a
  machine may loop over the vertices on every input, also on pairs `(n, a)` that are not graphs.
  On the input of a graph it is `n` (`BHSV25.Alg.numV_graph`).
* **Adjacency** (`BHSV25.Alg.adjBit`): the bit `a[u n + v]`, which is `[u ~ v]` on the table of a
  graph (`BHSV25.Alg.adjBit_adjTable`).
* **Sets of vertices** as membership bits, one per vertex (as `BHSV25.Graph.vertexSet` reads
  them), or as lists of vertex numbers in unary: `BHSV25.Alg.bitsToList` and
  `BHSV25.Alg.listToBits` convert between them, and `BHSV25.Alg.numTrue` counts the members of a
  set given by bits (`BHSV25.Alg.card_vertexSet`).
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-! ### The number of vertices -/

/-- The number of vertices of an input `(n, a)`, capped at `|a| + 1`; on the input of a graph,
whose table has `n²` bits, it is `n`. -/
def numV (x : ℕ × List Bool) : ℕ := min (x.2.length + 1) x.1

theorem length_adjTable (G : Graph) : (adjTable G).length = G.1 * G.1 := by
  rw [adjTable, List.length_ofFn]

theorem numV_graph (G : Graph) : numV (G.1, adjTable G) = G.1 := by
  rw [numV, length_adjTable]
  refine min_eq_right ?_
  rcases Nat.eq_zero_or_pos G.1 with h | h
  · omega
  · exact (Nat.le_mul_of_pos_left _ h).trans (Nat.le_succ _)

theorem numV_polytime : ComputableInPolyTime numV (encPair encNat encBits) encUnary :=
  binary_min_unary' (unary_add' (length_bits_comp (snd _ _)) (const 1)) (fst _ _)

/-! ### Adjacency -/

/-- The adjacency bit of `u` and `v` in the table `a` of a graph on `n` vertices: `a[u n + v]`
(`false` past the end of `a`). -/
def adjBit (n : ℕ) (a : List Bool) (u v : ℕ) : Bool := a.getD (u * n + v) false

open Classical in
theorem adjBit_adjTable (G : Graph) (u v : Fin G.1) :
    adjBit G.1 (adjTable G) u v = decide (G.2.Adj u v) := by
  have hlt : (u : ℕ) * G.1 + v < G.1 * G.1 :=
    calc (u : ℕ) * G.1 + v < u * G.1 + G.1 := Nat.add_lt_add_left v.2 _
      _ = (u + 1) * G.1 := (Nat.succ_mul _ _).symm
      _ ≤ G.1 * G.1 := Nat.mul_le_mul_right _ u.2
  have hk : (⟨(u : ℕ) * G.1 + v, hlt⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) :=
    Fin.ext (by rw [finProdFinEquiv_apply_val]; ring)
  rw [adjBit, List.getD_eq_getElem _ _ (by rw [length_adjTable]; exact hlt)]
  simp only [adjTable, List.getElem_ofFn]
  rw [show (⟨(u : ℕ) * G.1 + v, _⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) from hk,
    Equiv.symm_apply_apply]

theorem adjBit_polytime : ComputableInPolyTime
    (fun x : (ℕ × List Bool) × ℕ × ℕ ↦ adjBit x.1.1 x.1.2 x.2.1 x.2.2)
    (encPair (encPair encUnary encBits) (encPair encUnary encUnary)) encBool := by
  unfold adjBit
  exact bitsGetDWithInput (by fun_prop)
    (unary_add' (unary_mul' (by fun_prop) (by fun_prop)) (by fun_prop)) false

@[fun_prop]
theorem adjBit' {n u v : α → ℕ} {a : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (ha : ComputableInPolyTime a input encBits)
    (hu : ComputableInPolyTime u input encUnary) (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun x ↦ adjBit (n x) (a x) (u x) (v x)) input encBool :=
  adjBit_polytime.comp (g := fun x ↦ ((n x, a x), u x, v x)) ((hn.prod ha).prod (hu.prod hv))

/-! ### Sets of vertices -/

/-- The vertices `v < n` whose bit in `b` is set, in increasing order. -/
def bitsToList (n : ℕ) (b : List Bool) : List ℕ := (List.range n).filter fun v ↦ b.getD v false

/-- The membership bits, one per vertex `v < n`, of a list of vertices. -/
def listToBits (n : ℕ) (s : List ℕ) : List Bool := (List.range n).map fun v ↦ decide (v ∈ s)

/-- The number of vertices `v < n` whose bit in `b` is set. -/
def numTrue (n : ℕ) (b : List Bool) : ℕ := (bitsToList n b).length

theorem mem_bitsToList {n v : ℕ} {b : List Bool} :
    v ∈ bitsToList n b ↔ v < n ∧ b.getD v false = true := by
  rw [bitsToList, List.mem_filter, List.mem_range]

theorem nodup_bitsToList (n : ℕ) (b : List Bool) : (bitsToList n b).Nodup :=
  (List.nodup_range).filter _

theorem length_listToBits (n : ℕ) (s : List ℕ) : (listToBits n s).length = n := by
  rw [listToBits, List.length_map, List.length_range]

theorem getD_listToBits {n v : ℕ} (s : List ℕ) (hv : v < n) :
    (listToBits n s).getD v false = decide (v ∈ s) := by
  rw [List.getD_eq_getElem _ _ (by rw [length_listToBits]; exact hv)]
  simp [listToBits]

theorem mem_vertexSet_listToBits (G : Graph) (s : List ℕ) (v : Fin G.1) :
    v ∈ G.vertexSet (listToBits G.1 s) ↔ (v : ℕ) ∈ s := by
  rw [Graph.vertexSet, Finset.mem_filter, getD_listToBits s v.2, decide_eq_true_iff]
  exact and_iff_right (Finset.mem_univ _)

theorem mem_vertexSet_iff (G : Graph) (b : List Bool) (v : Fin G.1) :
    v ∈ G.vertexSet b ↔ (v : ℕ) ∈ bitsToList G.1 b := by
  rw [Graph.vertexSet, Finset.mem_filter, mem_bitsToList]
  exact ⟨fun h ↦ ⟨v.2, h.2⟩, fun h ↦ ⟨Finset.mem_univ _, h.2⟩⟩

/-- The set given by bits, as a set of numbers: the image of `G.vertexSet b`. -/
theorem map_vertexSet (G : Graph) (b : List Bool) :
    (G.vertexSet b).map Fin.valEmbedding = (bitsToList G.1 b).toFinset := by
  ext v
  rw [Finset.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_vertexSet_iff G b w).1 hw
  · intro hv
    have hlt := (mem_bitsToList.1 hv).1
    exact ⟨⟨v, hlt⟩, (mem_vertexSet_iff G b ⟨v, hlt⟩).2 hv, rfl⟩

theorem card_vertexSet (G : Graph) (b : List Bool) : (G.vertexSet b).card = numTrue G.1 b := by
  rw [numTrue, ← List.toFinset_card_of_nodup (nodup_bitsToList _ _), ← map_vertexSet,
    Finset.card_map]

/-! ### Certificates -/

theorem bitsToList_polytime : ComputableInPolyTime (fun x : ℕ × List Bool ↦ bitsToList x.1 x.2)
    (encPair encUnary encBits) (encList encUnary) := by
  unfold bitsToList
  exact filterWithInput (by fun_prop) (bitsGetDWithInput (by fun_prop) (by fun_prop) false)

@[fun_prop]
theorem bitsToList' {n : α → ℕ} {b : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x ↦ bitsToList (n x) (b x)) input (encList encUnary) :=
  bitsToList_polytime.comp (g := fun x ↦ (n x, b x)) (hn.prod hb)

theorem listToBits_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ ↦ listToBits x.1 x.2)
    (encPair encUnary (encList encUnary)) encBits := by
  unfold listToBits
  have h : ComputableInPolyTime (fun x : ℕ × List ℕ ↦ (List.range x.1).map fun v ↦ decide (v ∈ x.2))
      (encPair encUnary (encList encUnary)) (encList encBool) :=
    mapWithInput (by fun_prop) (decide_mem (by fun_prop) (by fun_prop))
  exact (bits_encList_polyTime encBool).2.comp h

@[fun_prop]
theorem listToBits' {n : α → ℕ} {s : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ listToBits (n x) (s x)) input encBits :=
  listToBits_polytime.comp (g := fun x ↦ (n x, s x)) (hn.prod hs)

@[fun_prop]
theorem numTrue' {n : α → ℕ} {b : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x ↦ numTrue (n x) (b x)) input encUnary := by
  unfold numTrue
  exact (length_list encUnary).comp (bitsToList' hn hb)

end BHSV25.Alg
