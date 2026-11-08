module

public import BGHKLMM26.Model
public import BGHKLMM26.Stablest

/-!
# The reduction from Unique Games to bounded-degree Max-Cut: definitions

The objects of the proof of [BGHKLMM26, Theorem 1.2], shared by the files of `BGHKLMM26/Hardness/`.

* **LTFs** (`BGHKLMM26.Hard.IsLTF`, `BGHKLMM26.Hard.ltfDist`): linear threshold functions on the
  cube and the `L¹` distance to the nearest one; the cut value `Cut_ρ(g)`
  (`BGHKLMM26.Hard.cutValue`); and the robust Majority is Stablest theorem as a statement,
  `BGHKLMM26.Hard.RobustMIS` ([BGHKLMM26, Theorem 7.1], with the error `C √η` of Lemma 7.4).
* **The dense graph** of the KKMO reduction (Figure 5.1), without the noise `μ`: the cut value
  `BGHKLMM26.Hard.kkmoCut` of a cut of `V × {0,1}^R`, for a correlation `ρ`.
* **The machine**: the decoder of one sampled edge from a block of coins
  (`BGHKLMM26.Hard.edgeOfBlock`), the greedy simplification with a degree cap
  (`BGHKLMM26.Hard.keptEdges`), and the reduction `BGHKLMM26.Hard.reduce` from an instance and its
  coins to a graph.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

/-! ### Linear threshold functions and the robust Majority is Stablest theorem -/

/-- The `0/1` value of a bit. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- A **linear threshold function** on the cube: `L x = [θ ≤ ∑ᵢ wᵢ σ(xᵢ)]` with `σ = bitSign`
(`σ(false) = 1`, `σ(true) = -1`). The constants are LTFs (`w = 0`). -/
def IsLTF {R : ℕ} (L : Cube (Fin R) → Bool) : Prop :=
  ∃ (w : Fin R → ℝ) (θ : ℝ), ∀ x, L x = decide (θ ≤ ∑ i, w i * bitSign (x i))

/-- `dist(g, ℒ_R)`: the `L¹` distance from `g` to the nearest LTF, under the uniform measure. -/
noncomputable def ltfDist {R : ℕ} (g : Cube (Fin R) → ℝ) : ℝ :=
  ⨅ L : {L : Cube (Fin R) → Bool // IsLTF L}, 𝔼 x, |g x - bitVal (L.1 x)|

/-- `Cut_ρ(g) = E[Cut(g(x), g(y))]` over `ρ`-correlated `x, y`, with `Cut(a, b) = a + b - 2ab`. -/
noncomputable def cutValue (ρ : ℝ) {R : ℕ} (g : Cube (Fin R) → ℝ) : ℝ :=
  corrAverage ρ R (fun x y ↦ g x + g y - 2 * g x * g y)

/-- **Robust Majority is Stablest** [BGHKLMM26, Theorem 7.1]: for `ρ ∈ (-1, 0)` there are `C` and
`η₀` such that for every `ξ > 0` there is `τ > 0` for which a table `g : {0,1}^R → [0,1]` with
influences at most `τ` that cuts at least `arccos ρ / π - η` of the `ρ`-correlated pairs,
`0 ≤ η ≤ η₀`, is within `C √η + ξ` of an LTF. (The paper's `h_ρ(τ) → 0` is the `ξ` here.) -/
def RobustMIS : Prop :=
  ∀ ρ : ℝ, -1 < ρ → ρ < 0 → ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧
    ∀ ξ : ℝ, 0 < ξ → ∃ τ : ℝ, 0 < τ ∧
      ∀ (R : ℕ) (g : Cube (Fin R) → ℝ), (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ i, influence i g ≤ τ) →
        ∀ η : ℝ, 0 ≤ η → η ≤ η₀ → Real.arccos ρ / Real.pi - η ≤ cutValue ρ g →
          ltfDist g ≤ C * Real.sqrt η + ξ

/-! ### Points of the cube as numbers -/

/-- The value of a bit string, least significant bit first. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsVal l

/-- The index of a point of the cube, in `[0, 2^R)`. -/
def cubeIdx {R : ℕ} (x : Cube (Fin R)) : ℕ := bitsVal (List.ofFn x)

/-- The vertex `(v, x)` of the reduction graph, numbered `v · 2^R + idx(x)`. -/
def vtx {R : ℕ} (v : ℕ) (x : Cube (Fin R)) : ℕ := v * 2 ^ R + cubeIdx x

/-! ### The dense graph of the KKMO reduction -/

/-- The table `π = [π(0), …, π(R-1)]` acting on the cube: `(π x)ⱼ = x_{π(j)}`, so that the
dictator of `σ(v)` at `v`, read through `π`, is the dictator of `π(σ(v))`. -/
def permCube {R : ℕ} (π : List ℕ) (x : Cube (Fin R)) : Cube (Fin R) :=
  fun j ↦ if h : π.getD j 0 < R then x ⟨π.getD j 0, h⟩ else false

/-- The constraints at the left vertex `u`. -/
def nbrs (cs : List UGConstraint) (u : ℕ) : List UGConstraint := cs.filter fun c ↦ c.1.1 = u

/-- The weight of the edges cut by `f : V × {0,1}^R → {0,1}` in the KKMO graph (Figure 5.1,
without noise): a uniformly random constraint `(u, v₁)`, a uniformly random constraint `(u, v₂)` at
the same left vertex, a uniform `x` and a `ρ`-correlated `y`, and the edge between `(v₁, π₁ x)` and
`(v₂, π₂ y)`. For an instance with `R` labels; `0` if there are no constraints. -/
noncomputable def kkmoCut (ρ : ℝ) (R : ℕ) (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool) :
    ℝ :=
  (cs.map fun c₁ ↦ ((nbrs cs c₁.1.1).map fun c₂ ↦
      corrAverage ρ R fun x y ↦
        bitVal (f c₁.1.2 (permCube c₁.2 x) != f c₂.1.2 (permCube c₂.2 y))).sum /
    (nbrs cs c₁.1.1).length).sum / cs.length

/-! ### The machine -/

/-- The parameters of the reduction, fixed for given `d` and `ρ`: the number `R` of labels, the
probability `q / 2^b` that a coordinate of `y` differs from that of `x` (so `ρ = 1 - 2q/2^b`), the
number `D` of sampled edges per vertex, and the degree cap `Δ`. -/
structure Prm where
  R : ℕ
  b : ℕ
  q : ℕ
  D : ℕ
  Δ : ℕ

namespace Prm

variable (P : Prm) (G : UGInstance)

/-- The bits for a uniform index: `2|cs| + R + Δ`, so that an index read modulo `M ≤ |cs|` is
within `|cs| / 2^t ≤ 2^-Δ / (|cs| 2^R)` of uniform in total variation, small next to `1/n`. -/
def tBits : ℕ := 2 * G.2.2.2.length + P.R + P.Δ

/-- The coins of one sampled edge: two indices, `x`, and `b` bits per coordinate for `y`. -/
def blockLen : ℕ := 2 * P.tBits G + P.R + P.R * P.b

/-- The number of vertices, `|V| · 2^R`. (`|V|` is capped by the number of constraints, which it
does not exceed on the instances that matter, so that the machine runs in polynomial time on every
input.) -/
def nVert : ℕ := min G.2.1 G.2.2.2.length * 2 ^ P.R

/-- The number of sampled edges, `D` per vertex. -/
def samples : ℕ := P.nVert G * P.D

/-- The instance has `R` labels, some constraints, and no more vertices on either side than
constraints (true of every bi-regular instance with constraints); otherwise the reduction outputs
a fixed graph. -/
def ok : Bool :=
  decide (G.2.2.1 = P.R) && decide (0 < G.2.2.2.length) && decide (G.1 ≤ G.2.2.2.length) &&
    decide (G.2.1 ≤ G.2.2.2.length)

/-- The number of coins read. -/
def coinCount : ℕ := if P.ok G then P.samples G * P.blockLen G else 0

end Prm

/-- The edge decoded from indices `r₁, r₂`, a point `x` and the numbers `z` of the coordinates:
the constraint `c₁ = cs[r₁ mod |cs|]`, the constraint `c₂` of index `r₂` modulo the degree among
those at the left vertex of `c₁`, `y = x` with coordinate `i` flipped when `zᵢ < q`, and the
edge between `(v₁, π₁ x)` and `(v₂, π₂ y)`. -/
def edgeOf (cs : List UGConstraint) (R q : ℕ) (r₁ r₂ : ℕ) (x : Cube (Fin R)) (z : Fin R → ℕ) :
    ℕ × ℕ :=
  let c₁ := cs.getD (r₁ % cs.length) default
  let N := nbrs cs c₁.1.1
  let c₂ := N.getD (r₂ % N.length) default
  let y : Cube (Fin R) := fun i ↦ xor (x i) (decide (z i < q))
  (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y))

/-- The edge decoded from a block of coins: `t` bits for `r₁`, `t` for `r₂`, `R` for `x`, and `b`
for each `zᵢ`. -/
def edgeOfBlock (P : Prm) (G : UGInstance) (blk : List Bool) : ℕ × ℕ :=
  let t := P.tBits G
  edgeOf G.2.2.2 P.R P.q (bitsVal (blk.take t)) (bitsVal ((blk.drop t).take t))
    (fun i ↦ blk.getD (2 * t + i) false)
    (fun i ↦ bitsVal (((blk.drop (2 * t + P.R)).drop (i * P.b)).take P.b))

/-- The number of kept edges at `a`. -/
def degIn (kept : List (ℕ × ℕ)) (a : ℕ) : ℕ := (kept.filter fun p ↦ p.1 = a ∨ p.2 = a).length

/-- An edge is kept if it is not a loop, not already kept (in either direction), and both ends
have fewer than `Δ` kept edges. -/
def keepOK (Δ : ℕ) (kept : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ≠ e.2) && !(kept.contains e) && !(kept.contains (e.2, e.1)) &&
    decide (degIn kept e.1 < Δ) && decide (degIn kept e.2 < Δ)

/-- One step of the greedy simplification. -/
def keepStep (Δ : ℕ) (kept : List (ℕ × ℕ)) (e : ℕ × ℕ) : List (ℕ × ℕ) :=
  if keepOK Δ kept e then kept ++ [e] else kept

/-- The sampled edges, made simple with maximum degree at most `Δ` greedily (steps (R1), (R2) of
Section 6). -/
def keptEdges (Δ : ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) := es.foldl (keepStep Δ) []

/-- The graph on `0, …, n - 1` with the given edges. -/
def graphOf (n : ℕ) (kept : List (ℕ × ℕ)) : Graph :=
  ⟨n, SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept⟩

/-- A single vertex, output on instances that fail the check (on good instances, those with no
constraints, whose value is `0`). Its Max-Cut value is `0` by convention, since it has no edges. -/
def pointGraph : Graph := ⟨1, ⊥⟩

/-- **The reduction**: `nVert · D` edges decoded from consecutive blocks of the coins, made simple
with degree at most `Δ`. -/
def reduce (P : Prm) (Gr : UGInstance × List Bool) : Graph :=
  if P.ok Gr.1 then
    graphOf (P.nVert Gr.1) (keptEdges P.Δ ((List.range (P.samples Gr.1)).map fun i ↦
      edgeOfBlock P Gr.1 ((Gr.2.drop (i * P.blockLen Gr.1)).take (P.blockLen Gr.1))))
  else pointGraph

end BGHKLMM26.Hard
