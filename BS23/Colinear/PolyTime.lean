module

public import BS23.Colinear.PolyTimeScore
public import BS23.Colinear.PolyTimeOneDim
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO

/-!
# The colinear algorithm runs in polynomial time

`BS23.Colinear.colinearAlg_runsInTime`: the algorithm of [BS23, Theorem 1.2]
(`BS23.Colinear.colinearAlg`) runs in time `BS23.colinearTime C` for some `C`, in the sense of
`BS23.RunsInTime`. It even runs in polynomial time: `colinearTime C x ≥ (|x| + 2)^C`.

* **A list program.** `BS23.Colinear.PT.algL` computes the algorithm on the input
  `(k, wmin, points)` (`BS23.Colinear.PT.algL_eq`) with lists of rationals for vectors, lists of
  rows for matrices, numbers for the basis indices, and the list programs of
  `BS23/Colinear/PolyTimeLinAlg.lean`, `BS23/Colinear/PolyTimeScore.lean` and
  `BS23/Colinear/PolyTimeOneDim.lean`.
* **Polynomial time.** Every step of the list program has a certificate
  (`Turing.MultiTapeTM.ComputableInPolyTime`, complexitylib's `fun_prop` calculus), so the whole
  program runs in polynomial time (`BS23.Colinear.PT.algL_polytime`). The Hermite degrees are at
  most `M = 40 (logInv wmin + 1)`, in unary, which is linear in the length of the encoding of
  `wmin`; every rational the program computes has polynomial size, since it is a closed-form
  expression (sums over the points, determinants, Hermite polynomials of degree at most `M`),
  never an iterated update.
* **The coins.** The algorithm ignores its coins: reading the input from the input with the coins
  takes linear time, so the algorithm runs within `O(|x|^C + |(x, r)|)` steps and cells.
-/

@[expose] public section

namespace BS23.Colinear.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Matrix

variable {α : Type} {input : α ↪ List Bool}

/-! ### The list program -/

/-- The centered points. -/
def csOf (pts : Points) : List (List ℚ) :=
  centL pts.length (dim pts) pts (meanL pts.length (dim pts) pts)

/-- The empirical covariance. -/
def covOf (pts : Points) : List (List ℚ) := covL pts.length (dim pts) (csOf pts)

/-- The basis. -/
def basOf (pts : Points) : List (List ℚ) := basisL (dim pts) (covOf pts)

/-- The direction for the candidate `p = (m, i)`. -/
def dirOf (pts : Points) (p : ℕ × ℕ) : List ℚ :=
  dirL (dim pts) (covOf pts) (basOf pts)
    (gradL p.1 pts.length (dim pts) (csOf pts) (covOf pts) ((basOf pts).getD p.2 []))

/-- The range factor `A = ⌊√(64 (L + 1))⌋ + 1`. -/
def rangeA (w : ℚ) : ℚ := ((Nat.sqrt (64 * (logInv w + 1)) + 1 : ℕ) : ℚ)

/-- The output for the selected candidate `p`: the clustering on the line of the projections. -/
def branchL (k : ℕ) (w : ℚ) (pts : Points) (p : ℕ × ℕ) : Output :=
  clusterL k (w ^ 2 / 100) (w / 4)
    (topScaleL (rangeA w) (quadL (dim pts) (covOf pts) (dirOf pts p))) (Nat.clog 2 pts.length + 8)
    (projL pts.length (dim pts) pts (dirOf pts p))

/-- **The algorithm as a list program**, on the input `(k, wmin, points)`. -/
def algL (x : ℕ × ℚ × Points) : Output :=
  if x.1 ≤ 1 then List.replicate x.2.2.length 0
  else (selectBestL (40 * (logInv x.2.1 + 1)) x.2.2.length (dim x.2.2) (csOf x.2.2) (covOf x.2.2)
    (basOf x.2.2)).elim (List.replicate x.2.2.length 0) (branchL x.1 x.2.1 x.2.2)

/-- **The list program computes the algorithm.** -/
theorem algL_eq (x : ColinearInput) : algL (x.k, x.wmin, x.points) = colinearAlg x := by
  have hP : RepT x.points (pointsFun x.points) := ent_pointsFun x.points
  have hc : RepT (csOf x.points) fun j ↦ pointsFun x.points j - mean (pointsFun x.points) :=
    centL_rep hP (meanL_rep hP)
  have hC : RepT (covOf x.points) (empCov (pointsFun x.points)) := covL_rep hc
  have hB : RepT (basOf x.points) fun i ↦ basisVec (empCov (pointsFun x.points)) i :=
    basisL_rep hC
  have hsel := selectBestL_eq (params x.wmin).M hc hC hB
  rw [colinearAlg, algInput, alg, algL]
  by_cases hk : x.k ≤ 1
  · simp only [hk, ite_true, List.ofFn_const]
  · simp only [hk, ite_false]
    rw [show 40 * (logInv x.wmin + 1) = (params x.wmin).M from rfl, ← hsel]
    cases selectBest (params x.wmin).M (pointsFun x.points) with
    | none => simp only [Option.map_none, Option.elim_none, List.ofFn_const]
    | some p =>
      simp only [Option.map_some, Option.elim_some]
      have hg := gradL_rep p.1 hc hC (hB.row p.2)
      have ha : RepV (dirOf x.points (p.1, p.2.val))
          (direction (empCov (pointsFun x.points))
            (gradPhat p.1 (pointsFun x.points) (basisVec (empCov (pointsFun x.points)) p.2))) :=
        dirL_rep hC hB hg
      rw [branchL, projL_eq hP ha, quadL_eq hC ha, topScaleL_eq, ← clusterL_eq]
      rfl

/-! ### Polynomial time -/

/-- The input `(k, wmin, points)`, as in `BS23.encColinearInput`. -/
abbrev encX : ℕ × ℚ × Points ↪ List Bool := encPair encNat (encPair encRat encM)

theorem dim_polytime : ComputableInPolyTime dim encM encUnary := by
  unfold dim
  exact (length_list encRat).comp (headD (encA := encList encRat) [])

@[fun_prop]
theorem dim' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ dim (P a)) input encUnary :=
  dim_polytime.comp hP

theorem len' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ (P a).length) input encUnary :=
  (length_list (encList encRat)).comp hP

@[fun_prop]
theorem csOf' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ csOf (P a)) input encM := by
  unfold csOf
  exact centL' (len' hP) (dim' hP) hP (meanL' (len' hP) (dim' hP) hP)

@[fun_prop]
theorem covOf' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ covOf (P a)) input encM := by
  unfold covOf
  exact covL' (len' hP) (dim' hP) (csOf' hP)

@[fun_prop]
theorem basOf' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ basOf (P a)) input encM := by
  unfold basOf
  exact basisL' (dim' hP) (covOf' hP)

@[fun_prop]
theorem dirOf' {P : α → Points} {p : α → ℕ × ℕ} (hP : ComputableInPolyTime P input encM)
    (hp : ComputableInPolyTime p input (encPair encUnary encUnary)) :
    ComputableInPolyTime (fun a ↦ dirOf (P a) (p a)) input encV := by
  unfold dirOf
  exact dirL' (dim' hP) (covOf' hP) (basOf' hP) (gradL' ((fst _ _).comp hp) (len' hP) (dim' hP)
    (csOf' hP) (covOf' hP) (row' (basOf' hP) ((snd _ _).comp hp)))

@[fun_prop]
theorem rangeA' {w : α → ℚ} (hw : ComputableInPolyTime w input encRat) :
    ComputableInPolyTime (fun a ↦ rangeA (w a)) input encRat := by
  unfold rangeA
  exact rat_natCast' (binAdd' (binary_sqrt' (toBinary' (unary_mul' (const 64)
    (unary_add' (logInv' hw) (const 1))))) (const 1))

/-- Unary numbers converted to binary, in a list. -/
theorem unaryList_to_binary : ComputableInPolyTime (fun l : List ℕ ↦ l) (encList encUnary)
    (encList encNat) := by
  have h : ComputableInPolyTime (fun l : List ℕ ↦ l.map fun a ↦ a) (encList encUnary)
      (encList encNat) := mapWithInput id' (toBinary' (snd _ _))
  simpa only [List.map_id'] using h

theorem branchL_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℚ × Points) × (ℕ × ℕ) ↦ branchL q.1.1 q.1.2.1 q.1.2.2 q.2)
    (encPair encX (encPair encUnary encUnary)) (encList encNat) := by
  unfold branchL
  have hk : ComputableInPolyTime (fun q : (ℕ × ℚ × Points) × (ℕ × ℕ) ↦ q.1.1)
      (encPair encX (encPair encUnary encUnary)) encNat := (fst _ _).comp (fst _ _)
  have hw : ComputableInPolyTime (fun q : (ℕ × ℚ × Points) × (ℕ × ℕ) ↦ q.1.2.1)
      (encPair encX (encPair encUnary encUnary)) encRat := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hP : ComputableInPolyTime (fun q : (ℕ × ℚ × Points) × (ℕ × ℕ) ↦ q.1.2.2)
      (encPair encX (encPair encUnary encUnary)) encM := (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hp : ComputableInPolyTime (fun q : (ℕ × ℚ × Points) × (ℕ × ℕ) ↦ q.2)
      (encPair encX (encPair encUnary encUnary)) (encPair encUnary encUnary) := snd _ _
  have ha := dirOf' hP hp
  exact unaryList_to_binary.comp (clusterL' hk (rat_div' (rat_sq' hw) (const 100))
    (rat_div' hw (const 4)) (topScaleL' (rangeA' hw) (quadL' (dim' hP) (covOf' hP) ha))
    (unary_add' (binary_clog_two.comp (toBinary' (len' hP))) (const 8))
    (projL' (len' hP) (dim' hP) hP ha))

/-- **The list program runs in polynomial time.** -/
theorem algL_polytime : ComputableInPolyTime algL encX encOutput := by
  unfold algL
  have hk : ComputableInPolyTime (fun x : ℕ × ℚ × Points ↦ x.1) encX encNat := fst _ _
  have hw : ComputableInPolyTime (fun x : ℕ × ℚ × Points ↦ x.2.1) encX encRat :=
    (fst _ _).comp (snd _ _)
  have hP : ComputableInPolyTime (fun x : ℕ × ℚ × Points ↦ x.2.2) encX encM :=
    (snd _ _).comp (snd _ _)
  have hz : ComputableInPolyTime (fun x : ℕ × ℚ × Points ↦ List.replicate x.2.2.length 0) encX
      (encList encNat) := replicate (len' hP) (const 0)
  exact ite_prop (binary_le' hk (const 1)) hz
    (optionElimWithInput (selectBestL' (unary_mul' (const 40) (unary_add' (logInv' hw) (const 1)))
      (len' hP) (dim' hP) (csOf' hP) (covOf' hP) (basOf' hP)) hz branchL_polytime)

end BS23.Colinear.PT

namespace BS23.Colinear

open Turing.MultiTapeTM

/-- **The algorithm of Theorem 1.2 runs in time `colinearTime C`** for some `C`: it runs in
polynomial time and ignores its coins. -/
theorem colinearAlg_runsInTime : ∃ C : ℕ, RunsInTime encColinearInput encOutput
    (fun xr : ColinearInput × List Bool ↦ colinearAlg xr.1) (colinearTime C) := by
  obtain ⟨d, e, hd⟩ := PT.algL_polytime.tidy.exists_degree
  -- Reading `(k, wmin, points)` from the input with the coins: it is the first frame.
  have h1 : ComputableTidilyInO (fun xr : ColinearInput × List Bool ↦
      (xr.1.k, xr.1.wmin, xr.1.points)) (encPair encColinearInput encBits) PT.encX
      (fun xr ↦ (encPair encColinearInput encBits xr).length)
      (fun xr ↦ (encPair encColinearInput encBits xr).length) :=
    (ComputableTidilyInO.fst encColinearInput encBits).of_enc_eq fun _ ↦ rfl
  obtain ⟨c, hc, -⟩ := (hd.inO.comp h1).computableInO
  have heq : (fun xr : ColinearInput × List Bool ↦ colinearAlg xr.1) =
      PT.algL ∘ fun xr : ColinearInput × List Bool ↦ (xr.1.k, xr.1.wmin, xr.1.points) :=
    funext fun xr ↦ (PT.algL_eq xr.1).symm
  refine ⟨d, c, ?_⟩
  rw [heq]
  refine hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)
  all_goals
    refine Nat.mul_le_mul_left c ?_
    have h : (PT.encX (xr.1.k, xr.1.wmin, xr.1.points)).length + 1 ≤
        (encColinearInput xr.1).length + 2 := by
      have : (PT.encX (xr.1.k, xr.1.wmin, xr.1.points)).length =
          (encColinearInput xr.1).length := rfl
      omega
    have h2 := Nat.pow_le_pow_left h d
    have h3 : ((encColinearInput xr.1).length + 2) ^ d ≤ colinearTime d xr.1 :=
      Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right d (Nat.succ_pos _))
    have hk : (Encoding.encPair encColinearInput Encoding.encBits xr).length =
        (encPair encColinearInput encBits xr).length := rfl
    beta_reduce
    omega

end BS23.Colinear
