module

public import BS23.Separating.Alg
public import BS23.Colinear.PolyTime
public import Background.SumOfSquares.Algorithm.PolyTime

/-!
# The separating algorithm as a list program in polynomial time

`BS23.Separating.PT.runL r Kc` computes the algorithm `BS23.Separating.run r Kc` of [BS23,
Theorem 1.1] on the input `((wmin, points), c, Lb)`, with the coins `c` and the budget `Lb` in
unary (`BS23.Separating.PT.runL_eq`), and it runs in polynomial time in the length of that input
with `r` and `Kc` in unary (`BS23.Separating.PT.runL_polytime`).

* **The list program.** Vectors are lists of rationals and point sets lists of rows, as in
  `BS23/Colinear/PolyTime.lean`, whose list programs for the mean, the centered points, the
  empirical covariance and its orthogonal basis (by determinants) are reused. The whitened points
  are `BS23.Separating.PT.whitenL`, the raw polynomials of the program are built over `List.range`
  instead of `List.finRange` (`BS23.Separating.PT.linRawL`, `BS23.Separating.PT.pairRawL`,
  `BS23.Separating.PT.ballRawL`), and the problem is `BS23.Separating.PT.probL`.
* **Every object of size `d^O(t)` is cut at the budget.** The powers `⟨u, v⟩^p` are the budgeted
  products `SoS.Poly.prodRaw d Lb` (at most `Lb` terms, `SoS.Poly.prodRaw_polytime`), so the
  program and the evaluations of `q` have size polynomial in `Lb` and the input, and the solver
  `SoS.Core.core` is polynomial-time in its input and its unary budget `Lb (|P| + 2)³`
  (`SoS.PolyTime.core_polytime'`). Nothing else is large: the degrees `2s`, `2t = 2 r s` are
  linear in the length of the encoding of `wmin` and in `r`, and the pivot reads `⌈log₂ n⌉ + Kc`
  coins.
* **The parameters are part of the input.** The ratio `r` and the number `Kc` of extra coin bits
  are given in unary, so one machine serves all of them, and the degree of its polynomial does not
  depend on them.
-/

@[expose] public section

namespace BS23.Separating.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS.Solver SoS.Poly
open BS23.Colinear BS23.Colinear.PT

variable {α : Type} {input : α ↪ List Bool}

/-! ### The list program -/

/-- The whitened points as a table: entry `(j, i)` is `⟨λᵢ, yⱼ - ȳ⟩ / scaleOf (λᵢᵀĈλᵢ)`. -/
def whitenL (pts : Points) : List (List ℚ) :=
  (List.range pts.length).map fun j ↦ (List.range (dim pts)).map fun i ↦
    (topScaleL (1 / 2) (quadL (dim pts) (covOf pts) ((basOf pts).getD i [])))⁻¹ *
      dotL (dim pts) ((basOf pts).getD i []) ((csOf pts).getD j [])

/-- The difference of the first `d` entries. -/
def subL (d : ℕ) (u v : List ℚ) : List ℚ := (List.range d).map fun k ↦ u.getD k 0 - v.getD k 0

/-- The linear form `⟨u, v⟩`, as `BS23.Separating.linRaw`. -/
def linRawL (d : ℕ) (u : List ℚ) : RawPoly :=
  ([], 0) :: (List.range d).map fun k ↦ (expAt d k 1, u.getD k 0)

/-- `⟨u, v⟩^p`, as `BS23.Separating.powRaw`. -/
def powRawL (d Lb p : ℕ) (u : List ℚ) : RawPoly := prodRaw d Lb (List.replicate p (linRawL d u))

/-- The pair moment polynomial, as `BS23.Separating.pairRaw`, for a table of `n` points. -/
def pairRawL (n d Lb p : ℕ) (Z : List (List ℚ)) : RawPoly :=
  (List.range n).flatMap fun i ↦ (List.range n).flatMap fun j ↦
    scaleRaw ((n : ℚ) ^ 2)⁻¹ (powRawL d Lb p (subL d (Z.getD i []) (Z.getD j [])))

/-- The ball constraint, as `BS23.Separating.ballRaw`. -/
def ballRawL (d : ℕ) : RawPoly := ([], 256) :: (List.range d).map fun k ↦ (expAt d k 2, -1)

/-- The problem, as `BS23.Separating.prob`, for a table of `n` points in dimension `d`. -/
def probT (n d Lb s t : ℕ) (Z : List (List ℚ)) : Problem :=
  (d, 2 * t, [ballRawL d, pairRawL n d Lb (2 * s) Z ++ [([], -1)],
    ([], 1024 ^ t) :: scaleRaw (-1) (pairRawL n d Lb (2 * t) Z)], ([], []))

/-- The problem on the whitened points. -/
def probL (Lb s t : ℕ) (pts : Points) : Problem :=
  probT pts.length (dim pts) Lb s t (whitenL pts)

/-- `q(u)`, as `BS23.Separating.qvOf`. -/
def qvOfL (d Lb p : ℕ) (out : RawPoly) (u : List ℚ) : ℚ :=
  ((powRawL d Lb p u).map fun t ↦ t.2 * SoS.Poly.coeff d out (expo d t.1)).sum

/-- The solver output for the weight bound `w`, the points and the budget. -/
def outL (r : ℕ) (w : ℚ) (pts : Points) (Lb : ℕ) : RawPoly :=
  solve Lb (probL Lb (logInv w + 1) (r * (logInv w + 1)) pts)

/-- The label of point `j` for the pivot `p`. -/
def labelL (r : ℕ) (w : ℚ) (pts : Points) (Lb p j : ℕ) : ℕ :=
  if qvOfL (dim pts) Lb (2 * (logInv w + 1)) (outL r w pts Lb)
      (subL (dim pts) ((whitenL pts).getD p []) ((whitenL pts).getD j [])) ≤ tau (logInv w + 1)
  then 0 else 1

/-- **The algorithm as a list program**, on `((wmin, points), coins, budget)`. -/
def runL (r Kc : ℕ) (y : (ℚ × Points) × List Bool × ℕ) : BS23.Output :=
  (List.range y.1.2.length).map (labelL r y.1.1 y.1.2 y.2.2 (pivot y.1.2.length Kc y.2.1))

/-! ### It computes the algorithm -/

variable {n d : ℕ}

theorem map_finRange_eq {β : Type*} (f : Fin n → β) (g : ℕ → β) (h : ∀ k : Fin n, g k = f k) :
    (List.finRange n).map f = (List.range n).map g := by
  rw [← List.ofFn_eq_map]
  exact ofFn_eq_map_range f g h

theorem flatMap_finRange_eq {β : Type*} (f : Fin n → List β) (g : ℕ → List β)
    (h : ∀ k : Fin n, g k = f k) :
    (List.finRange n).flatMap f = (List.range n).flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, map_finRange_eq f g h]

/-- The whitened points. -/
theorem whitenL_rep (x : BipartitionInput) : RepT (whitenL x.points) (whitened x) := by
  have hP : RepT x.points (pointsFun x.points) := ent_pointsFun x.points
  have hc : RepT (csOf x.points) fun j ↦ pointsFun x.points j - mean (pointsFun x.points) :=
    centL_rep hP (meanL_rep hP)
  have hC : RepT (covOf x.points) (empCov (pointsFun x.points)) := covL_rep hc
  have hB : RepT (basOf x.points) fun i ↦ basisVec (empCov (pointsFun x.points)) i :=
    basisL_rep hC
  refine repT_map_range _ _ fun j i ↦ ?_
  rw [whitened, whiten, wRow_dotProduct, quadL_eq hC (hB.row i), topScaleL_eq,
    dotL_eq (hB.row i) (hc.row j)]
  rfl

theorem subL_rep {u v : List ℚ} {u' v' : Fin d → ℚ} (hu : RepV u u') (hv : RepV v v') :
    RepV (subL d u v) (u' - v') :=
  repV_map_range _ _ fun a ↦ by rw [hu a, hv a, Pi.sub_apply]

theorem linRawL_eq {u : List ℚ} {u' : Fin d → ℚ} (hu : RepV u u') : linRawL d u = linRaw u' := by
  unfold linRawL linRaw
  congr 1
  exact (map_finRange_eq _ _ fun k ↦ by rw [hu k]).symm

theorem powRawL_eq (Lb p : ℕ) {u : List ℚ} {u' : Fin d → ℚ} (hu : RepV u u') :
    powRawL d Lb p u = powRaw Lb p u' := by
  rw [powRawL, powRaw, linRawL_eq hu]

theorem pairRawL_eq (Lb p : ℕ) {Z : List (List ℚ)} {Z' : Fin n → Fin d → ℚ} (hZ : RepT Z Z') :
    pairRawL n d Lb p Z = pairRaw Lb p Z' := by
  unfold pairRawL pairRaw
  refine (flatMap_finRange_eq _ _ fun i ↦ ?_).symm
  refine (flatMap_finRange_eq _ _ fun j ↦ ?_).symm
  rw [powRawL_eq Lb p (subL_rep (hZ.row i) (hZ.row j))]

theorem ballRawL_eq (d : ℕ) : ballRawL d = ballRaw d := by
  unfold ballRawL ballRaw
  congr 1
  exact (map_finRange_eq _ _ fun _ ↦ rfl).symm

theorem probL_eq (r : ℕ) (x : BipartitionInput) (Lb : ℕ) :
    probL Lb (logInv x.wmin + 1) (r * (logInv x.wmin + 1)) x.points = progOf r x Lb := by
  unfold probL probT progOf prob lowRaw highRaw
  rw [ballRawL_eq, pairRawL_eq Lb _ (whitenL_rep x), pairRawL_eq Lb _ (whitenL_rep x)]
  rfl

theorem qvOfL_eq (Lb p : ℕ) (out : RawPoly) {u : List ℚ} {u' : Fin d → ℚ} (hu : RepV u u') :
    qvOfL d Lb p out u = qvOf d Lb p out u' := by
  rw [qvOfL, qvOf, powRawL_eq Lb p hu]

/-- **The list program computes the algorithm.** -/
theorem runL_eq (r Kc : ℕ) (x : BipartitionInput) (c : List Bool) (Lb : ℕ) :
    runL r Kc ((x.wmin, x.points), c, Lb) = run r Kc x c Lb := by
  unfold run
  dsimp only
  rw [runL]
  refine (ofFn_eq_map_range _ _ fun j ↦ ?_).symm
  have hZ := whitenL_rep x
  have hp : pivot x.points.length Kc c < x.points.length := coinIdx_lt j.pos _ _
  have hrow : RepV ((whitenL x.points).getD (pivot x.points.length Kc c) [])
      (whitened x ⟨_, hp⟩) := hZ.row ⟨_, hp⟩
  rw [labelL, outL, probL_eq, qvOfL_eq _ _ _ (subL_rep hrow (hZ.row j))]
  rfl

/-! ### Polynomial time -/

/-- The inputs `((wmin, points), coins, budget)`, with the budget in unary. -/
abbrev encY : (ℚ × Points) × List Bool × ℕ ↪ List Bool :=
  encPair (encPair encRat encM) (encPair encBits encUnary)

theorem whitenL_polytime : ComputableInPolyTime whitenL encM encM := by
  unfold whitenL
  have hP : ComputableInPolyTime (fun p : (Points × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair encM encUnary) encUnary) encM := (fst _ _).comp (fst _ _)
  have hrow := row' (basOf' hP) (snd _ _)
  exact mapWithInput (range.comp (len' id')) (mapWithInput (range.comp (dim' (fst _ _)))
    (rat_mul' (rat_inv' (topScaleL' (const (1 / 2)) (quadL' (dim' hP) (covOf' hP) hrow)))
      (dotL' (dim' hP) hrow (row' (csOf' hP) ((snd _ _).comp (fst _ _))))))

theorem expAt_polytime : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ ↦ expAt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encNat)) (encList encNat) := by
  unfold expAt
  set E := encPair encUnary (encPair encUnary encNat)
  have hk : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.1.2.1) (encPair E encUnary)
      encUnary := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have he : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.1.2.2) (encPair E encUnary)
      encNat := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact mapWithInput (range.comp (fst _ _)) (ite_prop (decide_eq' (snd _ _) hk) he (const 0))

@[fun_prop]
theorem expAt' {d k e : α → ℕ} (hd : ComputableInPolyTime d input encUnary)
    (hk : ComputableInPolyTime k input encUnary) (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a ↦ expAt (d a) (k a) (e a)) input (encList encNat) :=
  expAt_polytime.comp (g := fun a ↦ (d a, k a, e a)) (hd.prod (hk.prod he))

theorem subL_polytime : ComputableInPolyTime (fun p : ℕ × List ℚ × List ℚ ↦ subL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encV encV)) encV := by
  unfold subL
  set E := encPair encUnary (encPair encV encV)
  have hu : ComputableInPolyTime (fun q : (ℕ × List ℚ × List ℚ) × ℕ ↦ q.1.2.1)
      (encPair E encUnary) encV := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hv : ComputableInPolyTime (fun q : (ℕ × List ℚ × List ℚ) × ℕ ↦ q.1.2.2)
      (encPair E encUnary) encV := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact mapWithInput (range.comp (fst _ _)) (rat_sub' (vget' hu (snd _ _)) (vget' hv (snd _ _)))

@[fun_prop]
theorem subL' {d : α → ℕ} {u v : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hu : ComputableInPolyTime u input encV) (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun a ↦ subL (d a) (u a) (v a)) input encV :=
  subL_polytime.comp (g := fun a ↦ (d a, u a, v a)) (hd.prod (hu.prod hv))

theorem linRawL_polytime : ComputableInPolyTime (fun p : ℕ × List ℚ ↦ linRawL p.1 p.2)
    (encPair encUnary encV) encRaw := by
  unfold linRawL
  set E := encPair encUnary encV
  have hd : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.1) (encPair E encUnary)
      encUnary := (fst _ _).comp (fst _ _)
  have hu : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.2) (encPair E encUnary)
      encV := (snd _ _).comp (fst _ _)
  exact cons' (const ([], 0)) (mapWithInput (range.comp (fst _ _))
    ((expAt' hd (snd _ _) (const 1)).prod (vget' hu (snd _ _))))

@[fun_prop]
theorem powRawL' {d Lb p : α → ℕ} {u : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hLb : ComputableInPolyTime Lb input encUnary) (hp : ComputableInPolyTime p input encUnary)
    (hu : ComputableInPolyTime u input encV) :
    ComputableInPolyTime (fun a ↦ powRawL (d a) (Lb a) (p a) (u a)) input encRaw := by
  unfold powRawL
  exact prodRaw' hd hLb (replicate hp (linRawL_polytime.comp (g := fun a ↦ (d a, u a))
    (hd.prod hu)))

theorem scaleRaw_polytime : ComputableInPolyTime (fun p : ℚ × RawPoly ↦ scaleRaw p.1 p.2)
    (encPair encRat encRaw) encRaw := by
  unfold scaleRaw
  exact mapWithInput (snd _ _) (((fst _ _).comp (snd _ _)).prod
    (rat_mul' ((fst _ _).comp (fst _ _)) ((snd _ _).comp (snd _ _))))

@[fun_prop]
theorem scaleRaw' {c : α → ℚ} {f : α → RawPoly} (hc : ComputableInPolyTime c input encRat)
    (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ scaleRaw (c a) (f a)) input encRaw :=
  scaleRaw_polytime.comp (g := fun a ↦ (c a, f a)) (hc.prod hf)

/-- The inputs `(n, d, Lb, p, Z)` of `BS23.Separating.PT.pairRawL`. -/
abbrev encPR : ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encM)))

theorem pairRawL_polytime : ComputableInPolyTime
    (fun q : ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ pairRawL q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    encPR encRaw := by
  unfold pairRawL
  set E := encPair (encPair encPR encUnary) encUnary
  have hn : ComputableInPolyTime (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.1.1)
      E encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hd : ComputableInPolyTime (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.1.2.1)
      E encUnary := (fst _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hLb : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.1.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _))))
  have hp : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.1.2.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))))
  have hZ : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.1.2.2.2.2) E encM :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))))
  have hi : ComputableInPolyTime (fun z : ((ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ z.1.2)
      E encUnary := (snd _ _).comp (fst _ _)
  exact flatMapWithInput (range.comp (fst _ _)) (flatMapWithInput (range.comp ((fst _ _).comp
    (fst _ _))) (scaleRaw' (rat_inv' (rat_sq' (rat_ofUnary hn)))
      (powRawL' hd hLb hp (subL' hd (row' hZ hi) (row' hZ (snd _ _))))))

@[fun_prop]
theorem pairRawL' {n d Lb p : α → ℕ} {Z : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hLb : ComputableInPolyTime Lb input encUnary) (hp : ComputableInPolyTime p input encUnary)
    (hZ : ComputableInPolyTime Z input encM) :
    ComputableInPolyTime (fun a ↦ pairRawL (n a) (d a) (Lb a) (p a) (Z a)) input encRaw :=
  pairRawL_polytime.comp (g := fun a ↦ (n a, d a, Lb a, p a, Z a))
    (hn.prod (hd.prod (hLb.prod (hp.prod hZ))))

theorem ballRawL_polytime : ComputableInPolyTime ballRawL encUnary encRaw := by
  unfold ballRawL
  exact cons' (const ([], 256)) (mapWithInput range
    ((expAt' (fst _ _) (snd _ _) (const 2)).prod (const (-1))))

/-- The inputs `(n, d, Lb, s, t, Z)` of `BS23.Separating.PT.probT`. -/
abbrev encPT : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encM))))

theorem probT_polytime : ComputableInPolyTime
    (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦
      probT q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
    encPT SoS.PolyTime.encProblemM := by
  unfold probT
  have hn : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.1) encPT
      encUnary := fst _ _
  have hd : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.2.1) encPT
      encUnary := (fst _ _).comp (snd _ _)
  have hLb : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.2.2.1) encPT
      encUnary := (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hs : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.2.2.2.1) encPT
      encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have ht : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.2.2.2.2.1)
      encPT encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hZ : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦ q.2.2.2.2.2)
      encPT encM := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hs2 := unary_mul' (const 2) hs
  have ht2 := unary_mul' (const 2) ht
  have hlow : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦
      pairRawL q.1 q.2.1 q.2.2.1 (2 * q.2.2.2.1) q.2.2.2.2.2 ++ [([], -1)]) encPT encRaw :=
    listAppend' (pairRawL' hn hd hLb hs2 hZ) (const _)
  have hhigh : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦
      (([] : List ℕ), (1024 : ℚ) ^ q.2.2.2.2.1) ::
        scaleRaw (-1) (pairRawL q.1 q.2.1 q.2.2.1 (2 * q.2.2.2.2.1) q.2.2.2.2.2)) encPT encRaw :=
    cons' ((const _).prod (rat_pow' (const 1024) ht)) (scaleRaw' (const (-1))
      (pairRawL' hn hd hLb ht2 hZ))
  exact (toBinary' hd).prod ((toBinary' ht2).prod ((cons' (ballRawL_polytime.comp hd)
    (cons' hlow (cons' hhigh (const [])))).prod (const _)))

@[fun_prop]
theorem probL' {Lb s t : α → ℕ} {P : α → Points} (hLb : ComputableInPolyTime Lb input encUnary)
    (hs : ComputableInPolyTime s input encUnary) (ht : ComputableInPolyTime t input encUnary)
    (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ probL (Lb a) (s a) (t a) (P a)) input
      SoS.PolyTime.encProblemM :=
  probT_polytime.comp (g := fun a ↦ ((P a).length, dim (P a), Lb a, s a, t a, whitenL (P a)))
    ((len' hP).prod ((dim' hP).prod (hLb.prod (hs.prod (ht.prod (whitenL_polytime.comp hP))))))

/-- The solver `SoS.Core.core` on a computed input and a computed unary budget. -/
theorem sosCore' {f : α → SoS.Solver.Input} {g : α → ℕ}
    (hf : ComputableInPolyTime f input SoS.PolyTime.encInputM)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ SoS.Core.core (f a, g a)) input encRaw :=
  SoS.PolyTime.core_polytime'.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem encProblem_eq (P : Problem) : encProblem P = SoS.PolyTime.encProblemM P := rfl

/-- **The solver call** in polynomial time, in the budget `Lb` (in unary) and the problem. -/
@[fun_prop]
theorem solve' {Lb : α → ℕ} {P : α → Problem} (hLb : ComputableInPolyTime Lb input encUnary)
    (hP : ComputableInPolyTime P input SoS.PolyTime.encProblemM) :
    ComputableInPolyTime (fun a ↦ solve (Lb a) (P a)) input encRaw := by
  have hlen : ComputableInPolyTime (fun a ↦ (encProblem (P a)).length) input encUnary := by
    simp only [encProblem_eq]
    exact (encoding_length SoS.PolyTime.encProblemM).comp hP
  have hl2 := unary_add' hlen (const 2)
  have hacc : ComputableInPolyTime (fun a ↦ acc (P a)) input encRat := by
    unfold acc
    exact rat_div' (const 1) (rat_two_pow' hl2)
  have hcube : ComputableInPolyTime (fun a ↦ ((encProblem (P a)).length + 2) ^ 3) input
      encUnary := by
    have e : (fun a ↦ ((encProblem (P a)).length + 2) ^ 3) = fun a ↦
        ((encProblem (P a)).length + 2) * ((encProblem (P a)).length + 2) *
          ((encProblem (P a)).length + 2) := funext fun _ ↦ pow_three' _
    rw [e]
    exact unary_mul' (unary_mul' hl2 hl2) hl2
  have hbud : ComputableInPolyTime (fun a ↦ solverBudget (Lb a) (P a)) input encUnary :=
    unary_mul' hLb hcube
  exact sosCore' (f := fun a ↦ (P a, acc (P a), acc (P a))) (hP.prod (hacc.prod hacc)) hbud

theorem qvOfL_polytime : ComputableInPolyTime
    (fun q : ℕ × ℕ × ℕ × RawPoly × List ℚ ↦ qvOfL q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair encRaw encV)))) encRat := by
  unfold qvOfL
  set E := encPair encUnary (encPair encUnary (encPair encUnary (encPair encRaw encV)))
  have hd : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × RawPoly × List ℚ ↦ q.1) E encUnary :=
    fst _ _
  have hLb : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × RawPoly × List ℚ ↦ q.2.1) E encUnary :=
    (fst _ _).comp (snd _ _)
  have hp : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × RawPoly × List ℚ ↦ q.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hu : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ × RawPoly × List ℚ ↦ q.2.2.2.2) E encV :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hd' : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × RawPoly × List ℚ) × (List ℕ × ℚ) ↦ z.1.1)
      (encPair E encTerm) encUnary := (fst _ _).comp (fst _ _)
  have hout : ComputableInPolyTime
      (fun z : (ℕ × ℕ × ℕ × RawPoly × List ℚ) × (List ℕ × ℚ) ↦ z.1.2.2.2.1)
      (encPair E encTerm) encRaw :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _))))
  have he : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × RawPoly × List ℚ) × (List ℕ × ℚ) ↦ z.2.1)
      (encPair E encTerm) (encList encNat) := (fst _ _).comp (snd _ _)
  have hc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × RawPoly × List ℚ) × (List ℕ × ℚ) ↦ z.2.2)
      (encPair E encTerm) encRat := (snd _ _).comp (snd _ _)
  exact rat_sum' (mapWithInput (powRawL' hd hLb hp hu)
    (rat_mul' hc (SoS.Poly.coeff' hd' hout (SoS.Poly.expo' hd' he))))

@[fun_prop]
theorem qvOfL' {d Lb p : α → ℕ} {out : α → RawPoly} {u : α → List ℚ}
    (hd : ComputableInPolyTime d input encUnary) (hLb : ComputableInPolyTime Lb input encUnary)
    (hp : ComputableInPolyTime p input encUnary) (hout : ComputableInPolyTime out input encRaw)
    (hu : ComputableInPolyTime u input encV) :
    ComputableInPolyTime (fun a ↦ qvOfL (d a) (Lb a) (p a) (out a) (u a)) input encRat :=
  qvOfL_polytime.comp (g := fun a ↦ (d a, Lb a, p a, out a, u a))
    (hd.prod (hLb.prod (hp.prod (hout.prod hu))))

/-! ### The pivot and the algorithm -/

theorem chunkVal_zero (b : ℕ) (l : List Bool) :
    Sampling.chunkVal b l 0 =
      ((List.range b).map fun t ↦ if l.getD t false then 2 ^ t else 0).sum := by
  rw [Sampling.chunkVal, sum_range_eq_list]
  simp only [zero_mul, zero_add]

/-- **The pivot**: the first `⌈log₂ n⌉ + Kc` coins as a number, modulo `n`, in binary. -/
@[fun_prop]
theorem pivot' {Kc n : α → ℕ} {c : α → List Bool} (hKc : ComputableInPolyTime Kc input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hc : ComputableInPolyTime c input encBits) :
    ComputableInPolyTime (fun a ↦ pivot (n a) (Kc a) (c a)) input encNat := by
  have e : (fun a ↦ pivot (n a) (Kc a) (c a)) = fun a ↦
      ((List.range (Nat.clog 2 (n a) + Kc a)).map fun t ↦
        if (c a).getD t false then 2 ^ t else 0).sum % n a := by
    funext a
    rw [pivot, coinIdx, coinBits, chunkVal_zero]
  rw [e]
  have hb : ComputableInPolyTime (fun a ↦ Nat.clog 2 (n a) + Kc a) input encUnary :=
    unary_add' (binary_clog_two.comp (toBinary' hn)) hKc
  have hmap : ComputableInPolyTime (fun a ↦
      (List.range (Nat.clog 2 (n a) + Kc a)).map fun t ↦ if (c a).getD t false then 2 ^ t else 0)
      input (encList encNat) :=
    mapWithInput (range.comp hb) (ite' (bitsGetDWithInput (hc.comp (fst _ _)) (snd _ _) false)
      (binary_two_pow.comp (snd _ _)) (const 0))
  have hsum : ComputableInPolyTime (fun a ↦
      ((List.range (Nat.clog 2 (n a) + Kc a)).map fun t ↦
        if (c a).getD t false then 2 ^ t else 0).sum) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp hmap.tidy)
  exact binary_mod.comp (g := fun a ↦ (((List.range (Nat.clog 2 (n a) + Kc a)).map
    fun t ↦ if (c a).getD t false then 2 ^ t else 0).sum, n a)) (hsum.prod (toBinary' hn))

@[fun_prop]
theorem whitenL' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ whitenL (P a)) input encM :=
  whitenL_polytime.comp hP

/-- The inputs `((r, Kc), ((wmin, points), c, Lb))` of the list program with its parameters, all
in unary but the weight bound, the points and the coins. -/
abbrev encRY : (ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ ↪ List Bool :=
  encPair (encPair encUnary encUnary) encY

/-- **The list program runs in polynomial time** in the length of `((r, Kc), ((wmin, points), c,
Lb))`: the parameters `r` and `Kc` are part of the input, in unary. -/
theorem runL_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ ↦ runL q.1.1 q.1.2 q.2) encRY
    BS23.encOutput := by
  unfold runL labelL outL
  set E := encPair encRY encUnary
  have hr : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.1.1) E encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hKc : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.1.2) E encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hw : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.2.1.1) E encRat := (fst _ _).comp ((fst _ _).comp ((snd _ _).comp (fst _ _)))
  have hP : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.2.1.2) E encM := (snd _ _).comp ((fst _ _).comp ((snd _ _).comp (fst _ _)))
  have hc : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.2.2.1) E encBits := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))
  have hLb : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      z.1.2.2.2) E encUnary := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))
  have hpiv : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      pivot z.1.2.1.2.length z.1.1.2 z.1.2.2.1) E encNat := pivot' hKc (len' hP) hc
  have hs : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      logInv z.1.2.1.1 + 1) E encUnary := unary_add' (logInv' hw) (const 1)
  have hout := solve' hLb (probL' hLb hs (unary_mul' hr hs) hP)
  have hZ : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      whitenL z.1.2.1.2) E encM := whitenL' hP
  have hZp : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      (whitenL z.1.2.1.2).getD (pivot z.1.2.1.2.length z.1.1.2 z.1.2.2.1) []) E encV :=
    .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := encV) (encL := encM) []
      hZ.tidy hpiv.tidy)
  have hq := qvOfL' (dim' hP) hLb (unary_mul' (const 2) hs) hout
    (subL' (dim' hP) hZp (row' hZ (snd _ _)))
  have htau : ComputableInPolyTime (fun z : ((ℕ × ℕ) × (ℚ × Points) × List Bool × ℕ) × ℕ ↦
      tau (logInv z.1.2.1.1 + 1)) E encRat := by
    unfold tau
    exact rat_div' (const 1) (rat_mul' (const 4) (rat_pow' (const 64) hs))
  exact mapWithInput (range.comp (len' ((snd _ _).comp ((fst _ _).comp (snd _ _)))))
    (ite_prop (rat_le' hq htau) (const 0) (const 1))

end BS23.Separating.PT
