module

public import BHJK25.RS.Decode

/-!
# The algorithm of Theorem 2.1, on lists

The algorithm `BHJK25.RS.rsAlg` as a program on lists of numbers and bits, which is how a Turing
machine runs it.

From the input `⟨n, M⟩`, read as `n` and the table `w` of `M` (`BHJK25.table`), the data of a run
is computed once (`BHJK25.RS.AlgAux.mkDat`): the parameters `ℓ`, `r`, `L = 2 (k - 1) ℓ`, `m`,
`W`, the modulus `fl` of the field and the list `elts` of its elements. Then every index
`idx < n^L` is a guess: its digits `g_j = idx / n^j % n` in base `n` (`BHJK25.RS.AlgAux.digits`),
the vertex at side `s`, block `b`, position `t` being digit `(s (k - 1) + b) ℓ + t`
(`BHJK25.RS.AlgAux.pos`). If the digits are distinct (`BHJK25.RS.AlgAux.nodupB`), the pairs
`(α_v, β_v)` of the columns `v` are read as lists of `r` bits (`BHJK25.RS.AlgAux.points`): bit `i`
of side `s` is the entry of the table at the tuple
`(g_{s,0,digit₀(i)}, …, g_{s,k-2,digit_{k-2}(i)}, v)`, whose index in the table is
`Σ_j tupleⱼ n^j` (`BHJK25.RS.AlgAux.tabIdx`). The pairs are decoded by `BHJK25.RS.decodeL`, or,
when the polynomials are constants (`m = 1`, which happens for `T = 1`), by trying the value of
every point (`BHJK25.RS.AlgAux.constCheck`). The input is accepted when some guess is
(`BHJK25.RS.AlgAux.run`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

/-- The data of a run, computed once from the input: the dimension `n`, the table `w` of the
tensor, the side `ℓ` (`l`) of the grid of a field element, the number `r` of bits of a field
element, the number `L = 2 (k - 1) ℓ` of guessed vertices, the number `m` of coefficients of the
polynomials, Sudan's weighted degree `W`, the lower coefficients `fl` of the modulus of the field,
and the list `elts` of all field elements. -/
structure Dat where
  /-- The dimension. -/
  n : ℕ
  /-- The table of the tensor. -/
  w : List Bool
  /-- The side of the grid of a field element. -/
  l : ℕ
  /-- The number of bits of a field element. -/
  r : ℕ
  /-- The number of guessed vertices. -/
  L : ℕ
  /-- The number of coefficients of the polynomials. -/
  m : ℕ
  /-- Sudan's weighted degree. -/
  W : ℕ
  /-- The lower coefficients of the modulus of the field. -/
  fl : List ℕ
  /-- The field elements. -/
  elts : List (List ℕ)

/-- The data of a run on the dimension `n` and the table `w`. -/
def mkDat (k T n : ℕ) (w : List Bool) : Dat where
  n := n
  w := w
  l := ell k T n
  r := rbits T n
  L := 2 * (k - 1) * ell k T n
  m := mdeg T n
  W := wdeg T n
  fl := irrPoly (rbits T n)
  elts := (List.range (2 ^ rbits T n)).map (bitsOf (rbits T n))

/-- Digit `j` of `idx` in base `n`. -/
def dig (n idx j : ℕ) : ℕ := idx / n ^ j % n

/-- The digit carrying the vertex at side `s`, block `b` and position `t`. -/
def pos (k l s b t : ℕ) : ℕ := (s * (k - 1) + b) * l + t

/-- The index in the table of the cell carrying bit `i` of side `s` of the column `v`, for the
guess with index `idx`: `Σ_{b < k - 1} g_{s,b,digit_b(i)} n^b + v n^(k-1)`. -/
def tabIdx (k : ℕ) (d : Dat) (idx s v i : ℕ) : ℕ :=
  ((List.range (k - 1)).map fun b ↦ dig d.n idx (pos k d.l s b (i / d.l ^ b % d.l)) * d.n ^ b).sum +
    v * d.n ^ (k - 1)

/-- The `r` bits of side `s` of the column `v`, as `0`s and `1`s. -/
def bitList (k : ℕ) (d : Dat) (idx s v : ℕ) : List ℕ :=
  (List.range d.r).map fun i ↦ (d.w.getD (tabIdx k d idx s v i) false).toNat

/-- The guessed vertices of the index `idx`: its `L` digits in base `n`. -/
def digits (d : Dat) (idx : ℕ) : List ℕ := (List.range d.L).map (dig d.n idx)

/-- The pairs `(α_v, β_v)` of the columns `v` of the guess with index `idx`, in increasing order
of `v`, as bit lists. -/
def points (k : ℕ) (d : Dat) (idx : ℕ) : List (List ℕ × List ℕ) :=
  ((List.range d.n).filter fun v ↦ !decide (v ∈ digits d idx)).map fun v ↦
    (bitList k d idx 0 v, bitList k d idx 1 v)

/-- The numbers of a list are distinct. -/
def nodupB (l : List ℕ) : Bool := l.dedup.length == l.length

/-- Some constant agrees with the points at `t` distinct first coordinates: the decoder for
`m = 1`, trying the value of every point. -/
def constCheck (t : ℕ) (pts : List (List ℕ × List ℕ)) : Bool :=
  pts.any fun q ↦ decide (t ≤ ((pts.filter fun xy ↦ xy.2 == q.2).map Prod.fst).dedup.length)

/-- Some polynomial with `m` coefficients agrees with the points at `W + 1` distinct first
coordinates. -/
def decidePts (d : Dat) (pts : List (List ℕ × List ℕ)) : Bool :=
  if 2 ≤ d.m then decodeL d.fl d.elts d.m d.W pts else constCheck (d.W + 1) pts

/-- The guess with index `idx` is accepted. -/
def guessOK (k : ℕ) (d : Dat) (idx : ℕ) : Bool :=
  nodupB (digits d idx) && decidePts d (points k d idx)

/-- **The algorithm**: some index below `n^L` is an accepted guess. -/
noncomputable def run (k T : ℕ) (x : TensorInput k) : Bool :=
  (List.range (x.1 ^ (mkDat k T x.1 (table x.2)).L)).any (guessOK k (mkDat k T x.1 (table x.2)))

end BHJK25.RS.AlgAux
