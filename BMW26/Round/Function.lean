module

public import BMW26.Model

/-!
# The rounding, as a function on lists

The last step of the algorithm (`BMW26.Round.roundOut`): from the second moments
`M u v = Ẽ[f_u f_v]` of the pseudo-distribution (a table of rows, `BMW26.Round.entry`) and the
edges `(u, u')` of the observed graph, it outputs a vector of `d` bits for each vertex.

* For an edge `e = (u, u')` in direction `i`, the row difference `(d/2)(M_u - M_{u'})` is close
  to `±χ̂ᵢ`; its sign vector `BMW26.Round.edgeVec` (bit `v` is `true` when `M u v < M u' v`) is
  close to a coordinate cut.
* **Greedy clustering** (`BMW26.Round.greedy`): going through the edges in order, keep the sign
  vector of an edge if it is *heavy* (at least `mth` sign vectors are within `2T` of it up to
  sign, `BMW26.Round.heavy`) and far (more than `n/4` up to sign) from those kept so far.
* The output lists, for each vertex `v`, bit `v` of the first `d` kept vectors.

The thresholds are `T = n / d^(c+2)` (the error allowed per cut) and `mth = |E| / (4d)` (a quarter
of the number of edges per direction).
-/

@[expose] public section

namespace BMW26.Round

/-- The number of positions where two bit lists differ (on their common length). -/
def hamm (a b : List Bool) : ℕ := (List.zipWith (fun x y ↦ x != y) a b).count true

/-- The distance up to sign between two vectors of `n` bits. -/
def hammPM (n : ℕ) (a b : List Bool) : ℕ := min (hamm a b) (n - hamm a b)

/-- Entry `(u, v)` of a table of rows (`0` when missing). -/
def entry (Mt : List (List ℚ)) (u v : ℕ) : ℚ := (Mt.getD u []).getD v 0

/-- The sign vector of the edge `e = (u, u')`: bit `v` is `true` when `M u v < M u' v`. -/
def edgeVec (n : ℕ) (Mt : List (List ℚ)) (e : ℕ × ℕ) : List Bool :=
  (List.range n).map fun v ↦ decide (entry Mt e.1 v < entry Mt e.2 v)

/-- `a` is heavy: at least `mth` of the vectors `vs` are within `2T` of `a` up to sign. -/
def heavy (n T mth : ℕ) (vs : List (List Bool)) (a : List Bool) : Bool :=
  decide (mth ≤ (vs.filter fun b ↦ decide (hammPM n a b ≤ 2 * T)).length)

/-- One step of the greedy clustering: keep `a` if it is heavy and far from the kept vectors. -/
def greedyStep (n T mth : ℕ) (vs : List (List Bool)) (kept : List (List Bool))
    (a : List Bool) : List (List Bool) :=
  if heavy n T mth vs a && kept.all (fun b ↦ decide (n / 4 < hammPM n a b)) then kept ++ [a]
  else kept

/-- **Greedy clustering** of the vectors `vs`. -/
def greedy (n T mth : ℕ) (vs : List (List Bool)) : List (List Bool) :=
  vs.foldl (greedyStep n T mth vs) []

/-- **The rounding**: the output vectors of the `n` vertices, from the moment table `Mt` and the
edge list. -/
def roundOut (n d c : ℕ) (Mt : List (List ℚ)) (edges : List (ℕ × ℕ)) : List (List Bool) :=
  let vs := edges.map (edgeVec n Mt)
  let kept := (greedy n (n / d ^ (c + 2)) (edges.length / (4 * d)) vs).take d
  (List.range n).map fun v ↦ kept.map fun a ↦ a.getD v false

end BMW26.Round
