module

public import BHSV25.BK.AintOver

/-!
# The reduction from Unique Games to almost-bipartite independent set

The graph of Bansal and Khot's reduction (`BHSV25/BK/README.md`, Section 1), its disjoint copies,
and the gap problem it reduces to.

* **Vertices** of one copy (`BHSV25.BK.Prm.nV`): `r = (u, k, z, a)` with a left vertex `u < m`,
  indices `k : [t] → [L]` of `t` constraints at `u` (`L` the left degree), a point `z ∈ {0,1}^R`
  and `a : [R] → [M]`; the coordinates `j` with `a_j = 0` are free. A vertex is numbered
  `u + m (K + L^t (Z + 2^R A))` with `K, Z, A` the numbers of `k, z, a` in bases `L, 2, M`
  (`BHSV25.BK.Prm.rv` reads the digits back).
* **Demands**: `r` asks the long code of the right end `v_p` of its `p`-th constraint
  `((u, v_p), π_p)` to be `1` at every point `w` of `v_p`'s cube with `w_i = z_{π_p(i)}` for the
  coordinates `i` whose `π_p(i)` is not free.
* **Edges** (`BHSV25.BK.Prm.conflict`): two vertices are adjacent when some demands at the same
  right vertex are incompatible for a folded long code, that is, `z_{π_p(i)} ≠ z'_{π'_{p'}(i)}` at
  every coordinate `i` fixed in both.
* **Copies** (`BHSV25.BK.copies`): disjoint copies bring the maximum degree below `η n`.
* **The reduction** (`BHSV25.BK.Prm.reduce`): `k₀` copies of this graph, or of a clique on
  degenerate instances (no constraint at `u = 0`).

The gap problem of Bansal and Khot is restated here (`BHSV25.BK.bkGap'`), identical to
`BHSV25.bkGap` of `BHSV25/BansalKhot.lean`, which this file cannot import.
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames Cslib.Complexity

/-! ### The gap problem -/

open Classical in
/-- Every vertex has at most `η n` neighbours (`BHSV25.Graph.MaxDegreeLE`). -/
def MaxDegLE (G : Graph) (η : ℝ) : Prop := ∀ v, (G.2.degree v : ℝ) ≤ η * G.1

/-- The gap problem of Bansal and Khot (`BHSV25.bkGap`). -/
noncomputable def bkGap' (ε γ η : ℝ) : PromiseProblem Graph where
  yes := {G | MaxDegLE G η ∧ ∃ I J : Finset (Fin G.1), Disjoint I J ∧
    G.2.IsIndepSet (I : Set (Fin G.1)) ∧ G.2.IsIndepSet (J : Set (Fin G.1)) ∧
    (1 / 2 - ε) * G.1 ≤ I.card ∧ (1 / 2 - ε) * G.1 ≤ J.card}
  no := {G | MaxDegLE G η ∧ γ ≤ 1 / 2 - ε ∧
    ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < γ * G.1}
  disjoint := Set.disjoint_left.2 fun G hyes hno ↦ by
    obtain ⟨-, I, -, -, hI, -, hIc, -⟩ := hyes
    obtain ⟨-, hγ, hno⟩ := hno
    have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    linarith [hno I hI, mul_le_mul_of_nonneg_right hγ hn]

/-- [BHSV25, Fact 8.1] (`BHSV25.BansalKhot`). -/
def BansalKhot' : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε γ η : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ ≤ ε₀ → 0 < η →
    PromiseProblem.NPHard encGraph (bkGap' ε γ η)

/-! ### Copies -/

/-- `k` disjoint copies of `H`: the vertex `i` is the vertex `i mod n` of the copy `⌊i / n⌋`. -/
abbrev copies (H : Graph) (k : ℕ) : Graph :=
  ⟨k * H.1, {
    Adj := fun i j ↦ i.divNat = j.divNat ∧ H.2.Adj i.modNat j.modNat
    symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h ↦ H.2.loopless.irrefl _ h.2⟩ }⟩

/-- The clique on `s` vertices. -/
def clique (s : ℕ) : Graph := ⟨s, ⊤⟩

/-! ### The reduction -/

/-- A vertex given by its digits: the left vertex `u`, the indices `k_p` of its constraints, the
point `z` and the numbers `a_j`. -/
abbrev RV := ℕ × List ℕ × List Bool × List ℕ

/-- The `p`-th constraint of a vertex. -/
def conAt (cs : List UGConstraint) (r : RV) (p : ℕ) : UGConstraint :=
  (nbrs cs r.1).getD (r.2.1.getD p 0) default

/-- The coordinate `π_p(i)` of `z` read at the coordinate `i` of the `p`-th demand. -/
def jAt (cs : List UGConstraint) (r : RV) (p i : ℕ) : ℕ := (conAt cs r p).2.getD i 0

/-- The coordinate `i` of the `p`-th demand is fixed: `π_p(i)` is not free. -/
def fixedAt (cs : List UGConstraint) (r : RV) (p i : ℕ) : Bool :=
  r.2.2.2.getD (jAt cs r p i) 0 != 0

/-- The value `z_{π_p(i)}` asked at the coordinate `i` of the `p`-th demand. -/
def zAt (cs : List UGConstraint) (r : RV) (p i : ℕ) : Bool := r.2.2.1.getD (jAt cs r p i) false

/-- The parameters: `R` labels, `t` queries, free coordinates of density `1/M`, `k₀` copies, and
cliques of size `s` for degenerate instances. -/
structure Prm where
  R : ℕ
  t : ℕ
  M : ℕ
  k₀ : ℕ
  s : ℕ

namespace Prm

variable (P : Prm)

/-- The left degree: the number of constraints at `u = 0`. -/
def ldeg (cs : List UGConstraint) : ℕ := (nbrs cs 0).length

/-- The number of vertices of one copy, `m L^t 2^R M^R`. -/
def nV (m L : ℕ) : ℕ := ((P.M ^ P.R * 2 ^ P.R) * L ^ P.t) * m

/-- The digits of the vertex numbered `x`. -/
def rv (m L x : ℕ) : RV :=
  (x % m, (List.range P.t).map (fun p ↦ x / m % L ^ P.t / L ^ p % L),
    (List.range P.R).map (fun j ↦ decide (x / m / L ^ P.t % 2 ^ P.R / 2 ^ j % 2 = 1)),
    (List.range P.R).map (fun j ↦ x / m / L ^ P.t / 2 ^ P.R / P.M ^ j % P.M))

/-- Two demands at the same right vertex are **incompatible** for folded long codes: they differ
at every coordinate fixed in both. -/
def clash (cs : List UGConstraint) (r r' : RV) (p q : ℕ) : Bool :=
  decide ((conAt cs r p).1.2 = (conAt cs r' q).1.2) &&
    (List.range P.R).all fun i ↦
      !(fixedAt cs r p i && fixedAt cs r' q i) || (zAt cs r p i != zAt cs r' q i)

/-- Two vertices **conflict**: some of their demands are incompatible. -/
def conflict (cs : List UGConstraint) (r r' : RV) : Bool :=
  (List.range P.t).any fun p ↦ (List.range P.t).any fun q ↦ P.clash cs r r' p q

/-- One copy of the graph of the reduction, on an instance with `m` left vertices, left degree
`L` and constraints `cs`. -/
abbrev baseGraph (cs : List UGConstraint) (m L : ℕ) : Graph :=
  ⟨P.nV m L, SimpleGraph.fromRel fun x y : Fin (P.nV m L) ↦
    P.conflict cs (P.rv m L x) (P.rv m L y) = true⟩

/-- **The reduction**: `k₀` copies of the graph of the instance, or of the clique `K_s` if there
is no constraint at `u = 0`. (The number of left vertices is capped by the number of constraints,
which it does not exceed on bi-regular instances with constraints, so that the output has
polynomial size on every input.) -/
def reduce (G : UGInstance) : Graph :=
  if ldeg G.2.2.2 = 0 then copies (clique P.s) P.k₀
  else copies (P.baseGraph G.2.2.2 (min G.1 G.2.2.2.length) (ldeg G.2.2.2)) P.k₀

end Prm

end BHSV25.BK
