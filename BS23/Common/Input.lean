module

public import BS23.Colinear.Cast

/-!
# From a sample to the algorithm's input

The algorithms read the rounded sample `BS23.roundedSample r ω` as a list of lists of rationals,
and turn it into a function `BS23.Colinear.pointsFun` indexed by `Fin (length)` and
`Fin (dim)`. For a sample `ω` of `n` points in `ℝ^d` that list has length `n`
(`BS23.length_roundedSample`) and, when `n > 0`, dimension `d` (`BS23.dim_roundedSample`), and its
entries are the rounded coordinates `r (ω j) a` (`BS23.pointsFun_roundedSample`).

The dependent-type transport along these two equalities is done once, for any function `G` that
takes points `Fin n' → Fin d' → ℚ` to one value per point (`BS23.apply_pointsFun_cast`): the
output list of `G` on the input is the output list of `G` on the function
`fun j a ↦ r (ω j) a` (`BS23.ofFn_pointsFun_roundedSample`, with no hypothesis on `n`, since for
`n = 0` both lists are empty). Since `BS23.ClustersWithin` and `BS23.IsSeparatingBipartition`
only read the length of the output and the labels of the sample points
(`BS23.clustersWithin_congr`, `BS23.isSeparatingBipartition_congr`), this is all an analysis
needs.

For the colinear-means algorithm, its output on the rounded sample is the output of the real
algorithm on the rounded points cast to the reals (`BS23.Colinear.algInput_roundedSample`).
-/

@[expose] public section

namespace BS23

open Colinear

variable {k d n : ℕ}

/-! ### The rounded sample as a list -/

/-- The rounded sample has one point per sample point. -/
@[simp] theorem length_roundedSample (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : (roundedSample r ω).length = n := by
  simp [roundedSample]

/-- The rounded sample of an empty sample is empty. -/
theorem roundedSample_of_eq_zero (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : n = 0) : roundedSample r ω = [] := by
  rw [← List.length_eq_zero_iff, length_roundedSample, hn]

/-- The `j`-th point of the rounded sample is the rounding of the `j`-th sample point. -/
theorem getD_roundedSample (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d))
    (j : Fin n) : (roundedSample r ω).getD j [] = List.ofFn (r (ω j)) := by
  simp [roundedSample, List.getD_eq_getElem?_getD]

/-- The points of a nonempty rounded sample have dimension `d`. -/
theorem dim_roundedSample (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d))
    (hn : 0 < n) : dim (roundedSample r ω) = d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  simp [dim, roundedSample, List.ofFn_succ]

/-- The coordinates of the rounded sample, as read by the algorithm: coordinate `a` of point `j`
is `r (ω j) a`. -/
theorem pointsFun_roundedSample (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) (a : Fin d) :
    pointsFun (roundedSample r ω) (Fin.cast (length_roundedSample r ω).symm j)
        (Fin.cast (dim_roundedSample r ω j.pos).symm a) = r (ω j) a := by
  rw [pointsFun, Fin.val_cast, getD_roundedSample, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp

/-! ### Transport -/

/-- **Transport along the length and the dimension.** If a list of points has length `n` and
dimension `d`, a function `G` of the points, with one value per point, gives on `pointsFun L` the
values it gives on the same points indexed by `Fin n` and `Fin d`. -/
theorem apply_pointsFun_cast {α : Type*} (G : (n' d' : ℕ) → (Fin n' → Fin d' → ℚ) → Fin n' → α)
    (L : Points) (hn : L.length = n) (hd : dim L = d) (j : Fin n) :
    G _ _ (pointsFun L) (Fin.cast hn.symm j) =
      G n d (fun j a ↦ pointsFun L (Fin.cast hn.symm j) (Fin.cast hd.symm a)) j := by
  subst hn hd
  rfl

/-- `BS23.apply_pointsFun_cast` for the rounded sample: a function `G` of the points, with one
value per point, gives on the rounded sample the values it gives on the rounded points
`fun j a ↦ r (ω j) a`. -/
theorem apply_pointsFun_roundedSample {α : Type*}
    (G : (n' d' : ℕ) → (Fin n' → Fin d' → ℚ) → Fin n' → α) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    G _ _ (pointsFun (roundedSample r ω)) (Fin.cast (length_roundedSample r ω).symm j) =
      G n d (fun j a ↦ r (ω j) a) j := by
  rw [apply_pointsFun_cast G _ (length_roundedSample r ω) (dim_roundedSample r ω j.pos)]
  simp only [pointsFun_roundedSample]

/-- The list of values of a function `G` of the points on the rounded sample is its list of
values on the rounded points `fun j a ↦ r (ω j) a`. -/
theorem ofFn_pointsFun_roundedSample {α : Type*}
    (G : (n' d' : ℕ) → (Fin n' → Fin d' → ℚ) → Fin n' → α) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    List.ofFn (G _ _ (pointsFun (roundedSample r ω))) = List.ofFn (G n d fun j a ↦ r (ω j) a) := by
  rw [List.ofFn_congr (length_roundedSample r ω)]
  congr 1
  funext j
  exact apply_pointsFun_roundedSample G r ω j

/-! ### Outputs -/

/-- The cluster of point `j` in the output listing `f`. -/
@[simp] theorem outCluster_ofFn (f : Fin n → ℕ) (j : Fin n) : outCluster (List.ofFn f) j = f j := by
  simp [outCluster, List.getD_eq_getElem?_getD]

/-- The cluster that a function `G` of the points puts sample point `j` in, on the rounded
sample, is its label of `j` on the rounded points. -/
theorem outCluster_ofFn_pointsFun_roundedSample
    (G : (n' d' : ℕ) → (Fin n' → Fin d' → ℚ) → Fin n' → ℕ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    outCluster (List.ofFn (G _ _ (pointsFun (roundedSample r ω)))) j =
      G n d (fun j a ↦ r (ω j) a) j := by
  rw [ofFn_pointsFun_roundedSample, outCluster_ofFn]

/-- `BS23.ClustersWithin` only depends on the clusters of the sample points. -/
theorem clustersWithin_congr {ε : ℝ} {ℓ : Fin n → Fin k} {out out' : Output}
    (hl : out.length = out'.length) (h : ∀ j : Fin n, outCluster out j = outCluster out' j) :
    ClustersWithin ε ℓ out ↔ ClustersWithin ε ℓ out' := by
  simp only [ClustersWithin, h, hl]

/-- `BS23.IsSeparatingBipartition` only depends on the clusters of the sample points. -/
theorem isSeparatingBipartition_congr {ℓ : Fin n → Fin k} {out out' : Output}
    (hl : out.length = out'.length) (h : ∀ j : Fin n, outCluster out j = outCluster out' j) :
    IsSeparatingBipartition ℓ out ↔ IsSeparatingBipartition ℓ out' := by
  simp only [IsSeparatingBipartition, h, hl]

/-! ### The colinear-means algorithm on a rounded sample -/

/-- **The colinear-means algorithm on a rounded sample** is the real algorithm on the rounded
points cast to the reals. -/
theorem Colinear.algInput_roundedSample (P : Params ℚ) (k' : ℕ) (wmin : ℚ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    algInput P ⟨k', wmin, roundedSample r ω⟩ =
      List.ofFn (alg P.cast k' fun j a ↦ (r (ω j) a : ℝ)) := by
  rw [algInput, ofFn_pointsFun_roundedSample (fun _ _ Y ↦ alg P k' Y), alg_cast]

/-- The label that the colinear-means algorithm gives to sample point `j` of a rounded sample. -/
theorem Colinear.outCluster_algInput_roundedSample (P : Params ℚ) (k' : ℕ) (wmin : ℚ)
    (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    outCluster (algInput P ⟨k', wmin, roundedSample r ω⟩) j =
      alg P.cast k' (fun j a ↦ (r (ω j) a : ℝ)) j := by
  rw [algInput_roundedSample, outCluster_ofFn]

/-- The colinear-means algorithm clusters a rounded sample within `ε` iff the real algorithm does
on the rounded points cast to the reals. -/
theorem Colinear.clustersWithin_algInput_roundedSample (P : Params ℚ) (k' : ℕ) (wmin : ℚ)
    (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (ℓ : Fin n → Fin k) :
    ClustersWithin ε ℓ (algInput P ⟨k', wmin, roundedSample r ω⟩) ↔
      ClustersWithin ε ℓ (List.ofFn (alg P.cast k' fun j a ↦ (r (ω j) a : ℝ))) := by
  rw [algInput_roundedSample]

end BS23
