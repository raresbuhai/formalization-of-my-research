module

public import Complexity.Computability.PolyTime.GaloisRingArithmetic
public import Complexity.Foundations.Data.List.EraseDupsBy

/-!
# The per-guess decoder: the list program

The list program behind `BHJK25.RS.decodeL`. A field element is a coefficient list (`List ℕ`),
with complexitylib's arithmetic modulo `2` and the monic polynomial with lower coefficients `fl`
(`Cslib.GaloisRingArith`); a vector is a list of field elements, read with `getD` (missing entries
are `[]`, which is zero). Every list is built by `List.range` maps of fixed lengths, so all sizes
are bounded by the parameters `m`, `W` and the length of `fl`.

* **Interpolation** (`BHJK25.RS.DecodeAux.interp`). Column `k < K = (W + 1)²` stands for the
  monomial `X^a Y^b`, `a = k % (W + 1)`, `b = k / (W + 1)`, allowed when `a + (m - 1) b ≤ W`
  (`BHJK25.RS.DecodeAux.low`). Each point `(x, y)` gives the row `(x^a y^b)_k`
  (`BHJK25.RS.DecodeAux.row`). A nonzero kernel vector supported on the allowed columns is found
  by fraction-free elimination (`BHJK25.RS.DecodeAux.kernelVec`): a family of `K` vectors,
  initially the allowed unit vectors, spans the allowed vectors killed by the rows seen so far;
  a row `a` with values `bᵢ = a · Nᵢ` and a pivot `bⱼ ≠ 0` replaces `Nᵢ` by `bⱼ Nᵢ - bᵢ Nⱼ`
  (`BHJK25.RS.DecodeAux.elimStep`). The interpolant `Q(X, Y)` is stored as the list over `b` of
  the lists over `a` of its coefficients.
* **Roth–Ruckenstein** (`BHJK25.RS.DecodeAux.rrRoots`). Bivariate polynomials are kept in the
  window `b < BY = W + 1`, `a < L = (m + 1)(W + 1)`. A node `(Q, p)` has a polynomial `Q` with
  `Q(0, Y) ≠ 0` and the coefficients `p` found so far. Its children are, for each element `c` of
  `elts` with `Q(0, c) = 0` (`BHJK25.RS.DecodeAux.eval0`), the node `(Q', p ++ [c])` where `Q'` is
  `Q(X, c + X Y)` (the Taylor shift `BHJK25.RS.DecodeAux.taylorL` by Horner's rule, then
  `BHJK25.RS.DecodeAux.shiftL`) divided by the largest power of `X` dividing it
  (`BHJK25.RS.DecodeAux.stripL`). Each level keeps at most `W + 1` nodes
  (`BHJK25.RS.DecodeAux.level`), which never drops one, and there are `m` levels.
* **Agreement** (`BHJK25.RS.DecodeAux.agree`): the number of distinct `x` among the points
  `(x, y)` with `p(x) = y`.
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

open Cslib

/-! ### Field elements -/

/-- Sum of field elements. -/
def fadd (fl a b : List ℕ) : List ℕ := GaloisRingArith.add 1 fl a b

/-- Difference of field elements. -/
def fsub (fl a b : List ℕ) : List ℕ := GaloisRingArith.sub 1 fl a b

/-- Product of field elements. -/
def fmul (fl a b : List ℕ) : List ℕ := GaloisRingArith.mul 1 fl a b

/-- Power of a field element, with the exponent in unary. -/
def fpow (fl a : List ℕ) (k : ℕ) : List ℕ := GaloisRingArith.pow 1 fl a k

/-- The field element zero. -/
def fzero (fl : List ℕ) : List ℕ := GaloisRingArith.zero fl

/-- The field element one. -/
def fone (fl : List ℕ) : List ℕ := GaloisRingArith.one fl

/-- The sum of a list of field elements. -/
def fsum (fl : List ℕ) (l : List (List ℕ)) : List ℕ := l.foldl (fadd fl) (fzero fl)

/-- The zero test: the first `r` coordinates are even. -/
def isZ (fl c : List ℕ) : Bool := (List.range fl.length).all fun i ↦ c.getD i 0 % 2 == 0

/-! ### Interpolation -/

/-- Column `k` stands for the monomial `X^(k % (W + 1)) Y^(k / (W + 1))`; it is allowed when its
`(1, m - 1)`-weighted degree is at most `W`. -/
def low (m W k : ℕ) : Bool := decide (k % (W + 1) + (m - 1) * (k / (W + 1)) ≤ W)

/-- The dot product of two vectors of length `K`. -/
def dot (fl : List ℕ) (K : ℕ) (a v : List (List ℕ)) : List ℕ :=
  fsum fl ((List.range K).map fun k ↦ fmul fl (a.getD k []) (v.getD k []))

/-- The initial family: the unit vectors of the allowed columns, and zero for the others. -/
def initFam (fl : List ℕ) (m W : ℕ) : List (List (List ℕ)) :=
  (List.range ((W + 1) * (W + 1))).map fun i ↦ (List.range ((W + 1) * (W + 1))).map fun k ↦
    if i == k && low m W k then fone fl else fzero fl

/-- One step of fraction-free elimination: with the row values `bᵢ = a · Nᵢ` and the first
pivot `bⱼ ≠ 0`, replace `Nᵢ` by `bⱼ Nᵢ - bᵢ Nⱼ`; keep the family when all row values vanish. -/
def elimStep (fl : List ℕ) (K : ℕ) (N : List (List (List ℕ))) (a : List (List ℕ)) :
    List (List (List ℕ)) :=
  let bs := (List.range K).map fun i ↦ dot fl K a (N.getD i [])
  let j := ((List.range K).find? fun i ↦ !isZ fl (bs.getD i [])).getD 0
  if isZ fl (bs.getD j []) then N else
    (List.range K).map fun i ↦ (List.range K).map fun k ↦
      fsub fl (fmul fl (bs.getD j []) ((N.getD i []).getD k []))
        (fmul fl (bs.getD i []) ((N.getD j []).getD k []))

/-- A kernel vector: process all rows, then take the first nonzero member of the family. -/
def kernelVec (fl : List ℕ) (K : ℕ) (N₀ : List (List (List ℕ)))
    (rows : List (List (List ℕ))) : List (List ℕ) :=
  let N := rows.foldl (elimStep fl K) N₀
  N.getD (((List.range K).find? fun i ↦
    (List.range K).any fun k ↦ !isZ fl ((N.getD i []).getD k [])).getD 0) []

/-- The row of the point `(x, y)`: the values `x^a y^b` of the monomials. -/
def row (fl : List ℕ) (W : ℕ) (xy : List ℕ × List ℕ) : List (List ℕ) :=
  (List.range ((W + 1) * (W + 1))).map fun k ↦
    fmul fl (fpow fl xy.1 (k % (W + 1))) (fpow fl xy.2 (k / (W + 1)))

/-- **The interpolant** `Q(X, Y)`, as the list over `b` of the coefficients of `Y^b`, each the
list over `a` of the coefficients of `X^a`. -/
def interp (fl : List ℕ) (m W : ℕ) (pts : List (List ℕ × List ℕ)) : List (List (List ℕ)) :=
  let c := kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) (pts.map (row fl W))
  (List.range (W + 1)).map fun b ↦ (List.range (W + 1)).map fun a ↦ c.getD (b * (W + 1) + a) []

/-! ### Roth–Ruckenstein -/

/-- `Q(0, c) = Σ_b Q_{b,0} c^b`. -/
def eval0 (fl : List ℕ) (BY : ℕ) (Q : List (List (List ℕ))) (c : List ℕ) : List ℕ :=
  fsum fl ((List.range BY).map fun b ↦ fmul fl ((Q.getD b []).getD 0 []) (fpow fl c b))

/-- One step of Horner's rule for the Taylor shift: `C(q) + (Y + c) acc`, in the window. -/
def taylorStep (fl : List ℕ) (BY L : ℕ) (c : List ℕ) (acc : List (List (List ℕ)))
    (q : List (List ℕ)) : List (List (List ℕ)) :=
  (List.range BY).map fun j ↦ (List.range L).map fun i ↦
    fadd fl (fmul fl c ((acc.getD j []).getD i []))
      (if j = 0 then q.getD i [] else (acc.getD (j - 1) []).getD i [])

/-- The Taylor shift `Q(X, Y + c) = Σ_b Q_b (Y + c)^b`, by Horner's rule. -/
def taylorL (fl : List ℕ) (BY L : ℕ) (Q : List (List (List ℕ))) (c : List ℕ) :
    List (List (List ℕ)) :=
  (List.range BY).reverse.foldl (fun acc b ↦ taylorStep fl BY L c acc (Q.getD b [])) []

/-- `H(X, X Y)`: multiply the coefficient of `Y^j` by `X^j`, in the window. -/
def shiftL (fl : List ℕ) (BY L : ℕ) (H : List (List (List ℕ))) : List (List (List ℕ)) :=
  (List.range BY).map fun j ↦ (List.range L).map fun i ↦
    if j ≤ i then (H.getD j []).getD (i - j) [] else fzero fl

/-- Divide by the largest power `X^v` dividing `Q`: `v` is the first `X`-degree at which some
coefficient is nonzero. The entries are reduced (`e + 0`), so that the output has a size bounded
in terms of the parameters. -/
def stripL (fl : List ℕ) (BY L : ℕ) (Q : List (List (List ℕ))) : List (List (List ℕ)) :=
  let v := ((List.range L).find? fun i ↦
    (List.range BY).any fun j ↦ !isZ fl ((Q.getD j []).getD i [])).getD 0
  (List.range BY).map fun j ↦ (List.range L).map fun i ↦
    if i + v < L then fadd fl ((Q.getD j []).getD (i + v) []) (fzero fl) else fzero fl

/-- The children of a node `(Q, p)`: for each root `c ∈ elts` of `Q(0, Y)`, the node
`(Q(X, c + X Y) / X^v, p ++ [c])`. The coefficients are reduced (`c + 0`) and at most `m` are
kept, so that every node has a size bounded in terms of the parameters (on the runs of the
decoder, `p` has fewer than `m` coefficients and nothing is dropped). -/
def children (fl : List ℕ) (elts : List (List ℕ)) (m BY L : ℕ)
    (nd : List (List (List ℕ)) × List (List ℕ)) :
    List (List (List (List ℕ)) × List (List ℕ)) :=
  (elts.filter fun c ↦ isZ fl (eval0 fl BY nd.1 c)).map fun c ↦
    (stripL fl BY L (shiftL fl BY L (taylorL fl BY L nd.1 c)),
      ((nd.2 ++ [c]).map fun e ↦ fadd fl e (fzero fl)).take m)

/-- One level of Roth–Ruckenstein: all children, keeping the first `cap` of them. -/
def level (fl : List ℕ) (elts : List (List ℕ)) (m BY L cap : ℕ)
    (fr : List (List (List (List ℕ)) × List (List ℕ))) :
    List (List (List (List ℕ)) × List (List ℕ)) :=
  (fr.flatMap (children fl elts m BY L)).take cap

/-- **The candidate polynomials**: the coefficient lists of the nodes after `m` levels. -/
def rrRoots (fl : List ℕ) (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  ((List.range m).foldl (fun fr _ ↦ level fl elts m (W + 1) ((m + 1) * (W + 1)) (W + 1) fr)
    [(stripL fl (W + 1) ((m + 1) * (W + 1)) Q, [])]).map Prod.snd

/-! ### Agreement -/

/-- The value `p(x) = Σ_i p_i x^i`. -/
def evalPoly (fl : List ℕ) (p : List (List ℕ)) (x : List ℕ) : List ℕ :=
  fsum fl ((List.range p.length).map fun i ↦ fmul fl (p.getD i []) (fpow fl x i))

/-- The number of distinct `x` among the points `(x, y)` with `p(x) = y`. -/
def agree (fl : List ℕ) (pts : List (List ℕ × List ℕ)) (p : List (List ℕ)) : ℕ :=
  (((pts.filter fun xy ↦ isZ fl (fsub fl (evalPoly fl p xy.1) xy.2)).map Prod.fst).eraseDupsBy
    fun x y ↦ decide (x = y)).length

/-- **The decoder**: some candidate polynomial agrees with the points at `W + 1` distinct
values. -/
def decode (fl : List ℕ) (elts : List (List ℕ)) (m W : ℕ) (pts : List (List ℕ × List ℕ)) :
    Bool :=
  (rrRoots fl elts m W (interp fl m W pts)).any fun p ↦ decide (W + 1 ≤ agree fl pts p)

end BHJK25.RS.DecodeAux
