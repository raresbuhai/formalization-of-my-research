module

public import BS23.Common.Hermite
public import BS23.Colinear.OneDim
public import BS23.Model
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Log

/-!
# The colinear-means algorithm

The algorithm for [BS23, Theorem 1.2] as a function on a list of points, over any linearly
ordered field with a floor (rationals for the machine, reals for the analysis). It uses no
sum-of-squares and runs in polynomial time.

1. The empirical mean `ȳ` and covariance `Ĉ` (`BS23.Colinear.mean`, `BS23.Colinear.empCov`).
2. A `Ĉ`-orthogonal basis `λ₁, …, λ_d` (`BS23.Colinear.basisVec`): `λᵢ` is column `i` of the
   adjugate of the leading `(i+1) × (i+1)` block of `Ĉ`, extended by zeros, so that
   `Ĉ_{[i]} λᵢ = det Ĉ_{[i]} eᵢ`.
3. For every degree `3 ≤ m ≤ M` and basis vector, the empirical Hermite moment
   `P̂_m(λ) = (1/n) ∑_j He_m(⟨λ, y_j - ȳ⟩; λᵀĈλ)` (`BS23.Colinear.phat`) and the scale-free score
   `P̂_m(λ)² / (λᵀĈλ)^m`; the best pair `(m, i)` (the first maximal one,
   `BS23.Colinear.selectBest`).
4. The gradient `g = ∇P̂_m(λᵢ)` (`BS23.Colinear.gradPhat`) and the direction
   `a = Ĉ⁻¹ g = ∑ᵢ (⟨λᵢ, g⟩ / λᵢᵀĈλᵢ) λᵢ` (`BS23.Colinear.direction`).
5. The projections `zⱼ = ⟨a, yⱼ⟩`, clustered on the line (`BS23.OneDim.cluster`) at scales
   `H / 2^ℓ`, `ℓ ≤ log₂ n + 8`, with `H = 4^e`-root: `H = 2^e` for the least integer `e` with
   `2 A² aᵀĈa ≤ 4^e`.

The parameters (`BS23.Colinear.Params`): the largest Hermite degree `M`, and the heavy-cell
threshold `θ`, coverage slack `ε` and range factor `A` of the line clustering.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
variable {n d : ℕ}

/-- The empirical mean. -/
def mean (Y : Fin n → Fin d → K) : Fin d → K := fun a ↦ (∑ j, Y j a) / n

/-- The empirical covariance. -/
def empCov (Y : Fin n → Fin d → K) : Matrix (Fin d) (Fin d) K :=
  fun a b ↦ (∑ j, (Y j a - mean Y a) * (Y j b - mean Y b)) / n

/-- The quadratic form `λᵀ C λ`. -/
def quad (C : Matrix (Fin d) (Fin d) K) (v : Fin d → K) : K := v ⬝ᵥ (C *ᵥ v)

/-- The leading `(i+1) × (i+1)` block of `C`. -/
def lead (C : Matrix (Fin d) (Fin d) K) (i : Fin d) : Matrix (Fin (i + 1)) (Fin (i + 1)) K :=
  C.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)

/-- The `i`-th vector of the `C`-orthogonal basis: column `i` of the adjugate of the leading
`(i+1) × (i+1)` block of `C`, extended by zeros. -/
def basisVec (C : Matrix (Fin d) (Fin d) K) (i : Fin d) : Fin d → K := fun j ↦
  if h : j.val ≤ i.val then (lead C i).adjugate ⟨j.val, Nat.lt_succ_of_le h⟩ (Fin.last i)
  else 0

/-- The empirical Hermite moment `P̂_m(λ) = (1/n) ∑_j He_m(⟨λ, y_j - ȳ⟩; λᵀĈλ)`. -/
def phat (m : ℕ) (Y : Fin n → Fin d → K) (v : Fin d → K) : K :=
  (∑ j, hermite m ((Y j - mean Y) ⬝ᵥ v) (quad (empCov Y) v)) / n

/-- The gradient of `phat m Y` at `v`:
`(1/n) ∑_j (m He_{m-1}(x_j; q) (y_j - ȳ) - m (m-1) He_{m-2}(x_j; q) Ĉ v)`. -/
def gradPhat (m : ℕ) (Y : Fin n → Fin d → K) (v : Fin d → K) : Fin d → K := fun a ↦
  (∑ j, ((m : K) * hermite (m - 1) ((Y j - mean Y) ⬝ᵥ v) (quad (empCov Y) v) * (Y j a - mean Y a) -
      ((m : K) * ((m : K) - 1)) * hermite (m - 2) ((Y j - mean Y) ⬝ᵥ v) (quad (empCov Y) v) *
        (empCov Y *ᵥ v) a)) / n

/-- The score of the pair `(m, i)`: `P̂_m(λᵢ)² / (λᵢᵀĈλᵢ)^m`. -/
def score (Y : Fin n → Fin d → K) (p : ℕ × Fin d) : K :=
  phat p.1 Y (basisVec (empCov Y) p.2) ^ 2 / quad (empCov Y) (basisVec (empCov Y) p.2) ^ p.1

/-- The candidate pairs `(m, i)`, `3 ≤ m ≤ M`, in lexicographic order. -/
def candidates (M d : ℕ) : List (ℕ × Fin d) :=
  (List.range' 3 (M - 2)).flatMap fun m ↦ (List.finRange d).map fun i ↦ (m, i)

/-- The first element of a list with the largest value of `f`, after the default `b`. -/
def argmaxFrom {α : Type*} (f : α → K) : List α → α → α
  | [], b => b
  | a :: l, b => argmaxFrom f l (if f b < f a then a else b)

/-- The first candidate with the largest score, if there is a candidate. -/
def selectBest (M : ℕ) (Y : Fin n → Fin d → K) : Option (ℕ × Fin d) :=
  match candidates M d with
  | [] => none
  | p :: l => some (argmaxFrom (score Y) l p)

/-- The direction `Ĉ⁻¹ g = ∑ᵢ (⟨λᵢ, g⟩ / λᵢᵀĈλᵢ) λᵢ`. -/
def direction (C : Matrix (Fin d) (Fin d) K) (g : Fin d → K) : Fin d → K :=
  ∑ i, ((basisVec C i ⬝ᵥ g) / quad C (basisVec C i)) • basisVec C i

/-- The parameters of the algorithm: the largest Hermite degree, and the threshold, slack and
range factor of the clustering on the line. -/
structure Params (K : Type*) where
  /-- The largest Hermite degree. -/
  M : ℕ
  /-- The heavy-cell threshold. -/
  θ : K
  /-- The coverage slack. -/
  ε : K
  /-- The range factor of the scales. -/
  A : K

/-- The largest scale `2^e`, `e` the least integer with `2 A² v ≤ 4^e`. -/
def topScale (A v : K) : K := (2 : K) ^ Int.clog 4 (2 * A ^ 2 * v)

/-- **The colinear-means algorithm** on the points `Y`, with `k` components. -/
def alg (P : Params K) (k : ℕ) (Y : Fin n → Fin d → K) : Fin n → ℕ :=
  if k ≤ 1 then fun _ ↦ 0 else
  match selectBest P.M Y with
  | none => fun _ ↦ 0
  | some p =>
    let a := direction (empCov Y) (gradPhat p.1 Y (basisVec (empCov Y) p.2))
    OneDim.cluster k P.θ P.ε (topScale P.A (quad (empCov Y) a)) (Nat.clog 2 n + 8)
      (fun j ↦ a ⬝ᵥ Y j)

/-- The points of a list of rational vectors, as a function (missing entries are `0`). -/
def pointsFun (pts : Points) : Fin pts.length → Fin (dim pts) → ℚ :=
  fun j a ↦ (pts.getD j []).getD a 0

/-- The algorithm on an input: its output lists the label of every point. -/
def algInput (P : Params ℚ) (x : ColinearInput) : Output :=
  List.ofFn (alg P x.k (pointsFun x.points))

/-- The parameters used for Theorem 1.2, from the weight bound `wmin`, with `L = logInv wmin`:
Hermite degrees up to `M = 40 (L + 1)`, heavy-cell threshold `θ = wmin² / 100`, coverage slack
`ε = wmin / 4`, and range factor `A = ⌊√(64 (L + 1))⌋ + 1`. -/
def params (wmin : ℚ) : Params ℚ where
  M := 40 * (logInv wmin + 1)
  θ := wmin ^ 2 / 100
  ε := wmin / 4
  A := ((Nat.sqrt (64 * (logInv wmin + 1)) + 1 : ℕ) : ℚ)

/-- **The algorithm of Theorem 1.2**: the colinear-means algorithm with the parameters
`BS23.Colinear.params` of the input's weight bound. It ignores its coins. -/
def colinearAlg (x : ColinearInput) : Output := algInput (params x.wmin) x

end BS23.Colinear
