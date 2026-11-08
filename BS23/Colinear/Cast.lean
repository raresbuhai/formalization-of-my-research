module

public import BS23.Colinear.Alg
public import Mathlib.Data.Rat.Floor

/-!
# The colinear-means algorithm commutes with casting to the reals

The machine runs `BS23.Colinear.alg` over `ℚ`, the analysis studies it over `ℝ`. Every step of
the algorithm is made of field operations, comparisons, floors and `Int.clog`, all of which commute
with the order-embedding `ℚ → ℝ`; hence the labels the algorithm gives to rational points are the
labels it gives to the same points seen as real points (`BS23.Colinear.alg_cast`), with the
parameters cast to the reals (`BS23.Colinear.Params.cast`). For an input, the `j`-th output label
is the real algorithm's label of the `j`-th point (`BS23.Colinear.outCluster_algInput`).

Each piece has its cast lemma, stated as "the real function on cast arguments is the cast of the
rational function": `BS23.hermite_cast`, `BS23.clog_ratCast`, `BS23.Colinear.mean_cast`,
`BS23.Colinear.empCov_cast`, `BS23.Colinear.quad_cast`, `BS23.Colinear.basisVec_cast`,
`BS23.Colinear.phat_cast`, `BS23.Colinear.gradPhat_cast`, `BS23.Colinear.score_cast`,
`BS23.Colinear.argmaxFrom_cast`, `BS23.Colinear.selectBest_cast`,
`BS23.Colinear.direction_cast`, `BS23.Colinear.topScale_cast`, and for the clustering on the line
`BS23.OneDim.cell_cast`, `BS23.OneDim.cellCount_cast`, `BS23.OneDim.heavy_cast`,
`BS23.OneDim.coverage_cast`, `BS23.OneDim.scale_cast`, `BS23.OneDim.level_cast` and
`BS23.OneDim.cluster_cast`.
-/

@[expose] public section

namespace BS23

open Matrix

/-- The Hermite polynomial commutes with casting. -/
theorem hermite_cast (m : ℕ) (x q : ℚ) :
    hermite m (x : ℝ) (q : ℝ) = ((hermite m x q : ℚ) : ℝ) := by
  simp [hermite]

/-- `Int.clog` of a rational is the same over `ℚ` and over `ℝ`. -/
theorem clog_ratCast (b : ℕ) (x : ℚ) : Int.clog b (x : ℝ) = Int.clog b x := by
  by_cases hx : 1 ≤ x
  · have hceil : ⌈(x : ℝ)⌉₊ = ⌈x⌉₊ := by
      rw [← Int.ceil_toNat, Rat.ceil_cast, Int.ceil_toNat]
    rw [Int.clog_of_one_le_right _ hx, Int.clog_of_one_le_right _ (by exact_mod_cast hx), hceil]
  · have hx' : x ≤ 1 := (lt_of_not_ge hx).le
    have hfloor : ⌊(x : ℝ)⁻¹⌋₊ = ⌊x⁻¹⌋₊ := by
      rw [← Rat.cast_inv, ← Int.floor_toNat, Rat.floor_cast, Int.floor_toNat]
    rw [Int.clog_of_right_le_one _ hx', Int.clog_of_right_le_one _ (by exact_mod_cast hx'),
      hfloor]

namespace OneDim

variable {n : ℕ}

theorem cell_cast (h z : ℚ) : cell (h : ℝ) (z : ℝ) = cell h z := by
  rw [cell, cell, ← Rat.cast_div, Rat.floor_cast]

theorem cellCount_cast (h : ℚ) (z : Fin n → ℚ) (p : ℤ) :
    cellCount (h : ℝ) (fun j ↦ (z j : ℝ)) p = cellCount h z p := by
  simp only [cellCount, cell_cast]

theorem heavy_cast (θ h : ℚ) (z : Fin n → ℚ) :
    heavy (θ : ℝ) (h : ℝ) (fun j ↦ (z j : ℝ)) = heavy θ h z := by
  simp only [heavy, cell_cast, cellCount_cast]
  refine Finset.filter_congr fun p _ ↦ ?_
  constructor <;> intro hp <;> exact_mod_cast hp

theorem coverage_cast (θ h : ℚ) (z : Fin n → ℚ) :
    coverage (θ : ℝ) (h : ℝ) (fun j ↦ (z j : ℝ)) = ((coverage θ h z : ℚ) : ℝ) := by
  simp only [coverage, cell_cast, heavy_cast]
  push_cast
  rfl

theorem scale_cast (H : ℚ) (ℓ : ℕ) : scale (H : ℝ) ℓ = ((scale H ℓ : ℚ) : ℝ) := by
  simp [scale]

theorem level_cast (θ ε H : ℚ) (ℓmax : ℕ) (z : Fin n → ℚ) :
    level (θ : ℝ) (ε : ℝ) (H : ℝ) ℓmax (fun j ↦ (z j : ℝ)) = level θ ε H ℓmax z := by
  unfold level
  congr 1
  refine Finset.filter_congr fun ℓ _ ↦ ?_
  rw [scale_cast, coverage_cast]
  constructor <;> intro hℓ <;> exact_mod_cast hℓ

theorem cluster_cast (k : ℕ) (θ ε H : ℚ) (ℓmax : ℕ) (z : Fin n → ℚ) :
    cluster k (θ : ℝ) (ε : ℝ) (H : ℝ) ℓmax (fun j ↦ (z j : ℝ)) = cluster k θ ε H ℓmax z := by
  funext j
  simp only [cluster, level_cast, scale_cast, heavy_cast, cell_cast]

end OneDim

namespace Colinear

variable {n d : ℕ}

theorem dotProduct_cast (v w : Fin d → ℚ) :
    (fun a ↦ (v a : ℝ)) ⬝ᵥ (fun a ↦ (w a : ℝ)) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  simp [dotProduct]

theorem mulVec_cast (C : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    C.map ((↑) : ℚ → ℝ) *ᵥ (fun a ↦ (v a : ℝ)) = fun a ↦ ((C *ᵥ v) a : ℝ) := by
  funext a
  simp [mulVec, dotProduct]

theorem sub_cast (v w : Fin d → ℚ) :
    (fun a ↦ (v a : ℝ)) - (fun a ↦ (w a : ℝ)) = fun a ↦ ((v - w) a : ℝ) := by
  funext a
  simp

theorem mean_cast (Y : Fin n → Fin d → ℚ) :
    mean (fun j a ↦ (Y j a : ℝ)) = fun a ↦ ((mean Y a : ℚ) : ℝ) := by
  funext a
  simp [mean]

theorem empCov_cast (Y : Fin n → Fin d → ℚ) :
    empCov (fun j a ↦ (Y j a : ℝ)) = (empCov Y).map ((↑) : ℚ → ℝ) := by
  ext a b
  simp [empCov, mean_cast]

theorem quad_cast (C : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    quad (C.map ((↑) : ℚ → ℝ)) (fun a ↦ (v a : ℝ)) = ((quad C v : ℚ) : ℝ) := by
  rw [quad, quad, mulVec_cast, dotProduct_cast]

theorem lead_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    lead (C.map ((↑) : ℚ → ℝ)) i = (lead C i).map ((↑) : ℚ → ℝ) :=
  rfl

theorem basisVec_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    basisVec (C.map ((↑) : ℚ → ℝ)) i = fun j ↦ ((basisVec C i j : ℚ) : ℝ) := by
  have hadj : (lead (C.map ((↑) : ℚ → ℝ)) i).adjugate =
      (lead C i).adjugate.map ((↑) : ℚ → ℝ) := by
    rw [lead_cast]
    exact ((Rat.castHom ℝ).map_adjugate (lead C i)).symm
  funext j
  unfold basisVec
  split_ifs <;> simp [hadj]

theorem phat_cast (m : ℕ) (Y : Fin n → Fin d → ℚ) (v : Fin d → ℚ) :
    phat m (fun j a ↦ (Y j a : ℝ)) (fun a ↦ (v a : ℝ)) = ((phat m Y v : ℚ) : ℝ) := by
  simp only [phat, mean_cast, sub_cast, dotProduct_cast, empCov_cast, quad_cast, hermite_cast]
  push_cast
  rfl

theorem gradPhat_cast (m : ℕ) (Y : Fin n → Fin d → ℚ) (v : Fin d → ℚ) :
    gradPhat m (fun j a ↦ (Y j a : ℝ)) (fun a ↦ (v a : ℝ)) =
      fun a ↦ ((gradPhat m Y v a : ℚ) : ℝ) := by
  funext a
  simp only [gradPhat, mean_cast, sub_cast, dotProduct_cast, empCov_cast, quad_cast,
    hermite_cast, mulVec_cast]
  push_cast
  rfl

theorem score_cast (Y : Fin n → Fin d → ℚ) (p : ℕ × Fin d) :
    score (fun j a ↦ (Y j a : ℝ)) p = ((score Y p : ℚ) : ℝ) := by
  simp only [score, empCov_cast, basisVec_cast, phat_cast, quad_cast]
  push_cast
  rfl

theorem argmaxFrom_cast {α : Type*} (f : α → ℚ) (l : List α) (b : α) :
    argmaxFrom (fun a ↦ (f a : ℝ)) l b = argmaxFrom f l b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [argmaxFrom, Rat.cast_lt, ih]

theorem selectBest_cast (M : ℕ) (Y : Fin n → Fin d → ℚ) :
    selectBest M (fun j a ↦ (Y j a : ℝ)) = selectBest M Y := by
  have hs : score (fun j a ↦ (Y j a : ℝ)) = fun p ↦ ((score Y p : ℚ) : ℝ) := funext (score_cast Y)
  unfold selectBest
  rw [hs]
  generalize candidates M d = L
  cases L <;> simp [argmaxFrom_cast]

theorem direction_cast (C : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) :
    direction (C.map ((↑) : ℚ → ℝ)) (fun a ↦ (g a : ℝ)) = fun a ↦ ((direction C g a : ℚ) : ℝ) := by
  funext a
  simp only [direction, basisVec_cast, dotProduct_cast, quad_cast, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

theorem topScale_cast (A v : ℚ) : topScale (A : ℝ) (v : ℝ) = ((topScale A v : ℚ) : ℝ) := by
  have h : (2 : ℝ) * (A : ℝ) ^ 2 * (v : ℝ) = ((2 * A ^ 2 * v : ℚ) : ℝ) := by push_cast; ring
  rw [topScale, topScale, h, clog_ratCast, Rat.cast_zpow, Rat.cast_ofNat]

/-- The parameters, cast to the reals. -/
def Params.cast (P : Params ℚ) : Params ℝ := ⟨P.M, P.θ, P.ε, P.A⟩

/-- **The algorithm commutes with casting**: on rational points, the colinear-means algorithm
gives the same labels over `ℚ` and over `ℝ`. -/
theorem alg_cast (P : Params ℚ) (k : ℕ) (Y : Fin n → Fin d → ℚ) :
    alg P k Y = alg P.cast k (fun j a ↦ (Y j a : ℝ)) := by
  unfold alg
  split_ifs with hk
  · rfl
  · simp only [Params.cast, selectBest_cast]
    cases selectBest P.M Y with
    | none => rfl
    | some p =>
      simp only [empCov_cast, basisVec_cast, gradPhat_cast, direction_cast, quad_cast,
        topScale_cast, dotProduct_cast, OneDim.cluster_cast]

/-- The output of the algorithm on an input lists a label for every point. -/
theorem length_algInput (P : Params ℚ) (x : ColinearInput) :
    (algInput P x).length = x.points.length := by
  simp [algInput]

/-- The label the algorithm gives to the `j`-th point of an input is the label the real
algorithm gives to it, on the input's points cast to the reals. -/
theorem outCluster_algInput (P : Params ℚ) (x : ColinearInput) {j : ℕ}
    (hj : j < x.points.length) :
    outCluster (algInput P x) j =
      alg P.cast x.k (fun j a ↦ ((pointsFun x.points j a : ℚ) : ℝ)) ⟨j, hj⟩ := by
  rw [outCluster, algInput, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hj, alg_cast]

/-- `BS23.Colinear.outCluster_algInput`, for points indexed by `Fin`. -/
theorem outCluster_algInput_fin (P : Params ℚ) (x : ColinearInput) (j : Fin x.points.length) :
    outCluster (algInput P x) j =
      alg P.cast x.k (fun j a ↦ ((pointsFun x.points j a : ℚ) : ℝ)) j :=
  outCluster_algInput P x j.isLt

end Colinear

end BS23
