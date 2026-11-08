module

public import BS23.ColinearSoS.Alg
public import BS23.Separating.PolyTime

/-!
# The sum-of-squares colinear algorithm as a list program in polynomial time

`BS23.ColinearSoS.PTc.colL` computes the algorithm `BS23.ColinearSoS.colSoS` of [BS23, Theorem
1.2] on the input `((k, wmin, points), Lb)`, with the budget `Lb` in unary
(`BS23.ColinearSoS.PTc.colL_eq`), and it runs in polynomial time in the length of that input
(`BS23.ColinearSoS.PTc.colL_polytime`).

* **The list program.** Vectors are lists of rationals and point sets lists of rows, as in
  `BS23/Colinear/PolyTime.lean` and `BS23/Separating/PolyTime.lean`, whose list programs for the
  empirical covariance, its orthogonal basis, the whitened points
  (`BS23.Separating.PT.whitenL`), the budgeted powers `⟨u, v⟩^p`, the solver call and the
  evaluations `BS23.Separating.qvOf` are reused. New are the weights `κ`
  (`BS23.ColinearSoS.PTc.kappaL`), the constraints `vᵀ diag(κ) v ≷ 1`, the moment polynomials
  `c ∑ⱼ ⟨Xⱼ, v⟩^r` and the two programs (`BS23.ColinearSoS.PTc.progUL`,
  `BS23.ColinearSoS.PTc.progLL`), the test on `OPT_U` (`BS23.ColinearSoS.PTc.outCL`), the
  rounding `â = M e_{j*}` and the direction `Wᵀ â` (`BS23.ColinearSoS.PTc.aL`); the last step is
  the line clustering `BS23.Colinear.PT.clusterL`.
* **Polynomial time.** The degrees `2s`, `2t = 512 s` with `s = logInv wmin + 1` are computed in
  unary from `wmin` in polynomial time, and every object of size `d^O(t)` is cut at the budget: the
  powers are the budgeted products `SoS.Poly.prodRaw d Lb` (at most `Lb` terms), and the solver
  `SoS.Core.core` runs in polynomial time in its input and its unary budget `Lb (|P| + 2)³`
  (`BS23.Separating.PT.solve'`). So the program runs in polynomial time in `|x| + Lb`, with a
  degree that depends on nothing.
-/

@[expose] public section

namespace BS23.ColinearSoS.PTc

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS.Solver SoS.Poly Matrix
open BS23.Colinear BS23.Colinear.PT
open BS23.Separating (expAt scaleRaw ballRaw solve qvOf whiten W wRow kappa scaleOf)
open BS23.Separating.PT (whitenL whitenL' whitenL_rep powRawL powRawL' powRawL_eq ballRawL
  ballRawL_eq ballRawL_polytime qvOfL qvOfL' qvOfL_eq expAt' scaleRaw' solve' map_finRange_eq
  flatMap_finRange_eq)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The list program -/

/-- The weights `κ` as a list: entry `i` is `λᵢᵀĈλᵢ / (scaleOf (λᵢᵀĈλᵢ))²`, as
`BS23.Separating.kappa`. -/
def kappaL (pts : Points) : List ℚ :=
  (List.range (dim pts)).map fun i ↦
    quadL (dim pts) (covOf pts) ((basOf pts).getD i []) /
      topScaleL (1 / 2) (quadL (dim pts) (covOf pts) ((basOf pts).getD i [])) ^ 2

/-- The constraint `∑ᵢ κᵢ vᵢ² - 1 ≥ 0`, as `BS23.ColinearSoS.sphLoRaw`. -/
def sphLoRawL (d : ℕ) (κ : List ℚ) : RawPoly :=
  ([], -1) :: (List.range d).map fun i ↦ (expAt d i 2, κ.getD i 0)

/-- The constraint `1 - ∑ᵢ κᵢ vᵢ² ≥ 0`, as `BS23.ColinearSoS.sphHiRaw`. -/
def sphHiRawL (d : ℕ) (κ : List ℚ) : RawPoly :=
  ([], 1) :: (List.range d).map fun i ↦ (expAt d i 2, -κ.getD i 0)

/-- `c ∑ⱼ ⟨Zⱼ, v⟩^r`, as `BS23.ColinearSoS.momRaw`, for a table of `n` points. -/
def momRawL (c : ℚ) (n d Lb r : ℕ) (Z : List (List ℚ)) : RawPoly :=
  scaleRaw c ((List.range n).flatMap fun j ↦ powRawL d Lb r (Z.getD j []))

/-- The problem of degree `ℓ` with the ball, the equality `vᵀ diag(κ) v = 1` and the objective
`obj`, as `BS23.ColinearSoS.progC`. -/
def progCL (d ℓ : ℕ) (κ : List ℚ) (obj : RawPoly) : Problem :=
  (d, ℓ, [ballRawL d, sphLoRawL d κ, sphHiRawL d κ], (obj, []))

/-- Program U on the points, as `BS23.ColinearSoS.progUY`. -/
def progUL (w : ℚ) (Lb : ℕ) (pts : Points) : Problem :=
  progCL (dim pts) (2 * sCol w) (kappaL pts)
    (momRawL (-(pts.length : ℚ)⁻¹) pts.length (dim pts) Lb (2 * sCol w) (whitenL pts))

/-- Program L on the points, as `BS23.ColinearSoS.progLY`. -/
def progLL (w : ℚ) (Lb : ℕ) (pts : Points) : Problem :=
  progCL (dim pts) (2 * tCol w) (kappaL pts)
    (momRawL ((pts.length : ℚ)⁻¹) pts.length (dim pts) Lb (2 * tCol w) (whitenL pts))

/-- `(1/n) ∑ⱼ Ẽ ⟨Zⱼ, v⟩^r` read off `out`, as `BS23.ColinearSoS.momVal`. -/
def momValL (n d Lb r : ℕ) (Z : List (List ℚ)) (out : RawPoly) : ℚ :=
  (n : ℚ)⁻¹ * ((List.range n).map fun j ↦ qvOfL d Lb r out (Z.getD j [])).sum

/-- The chosen output, as `BS23.ColinearSoS.outC`. -/
def outCL (w : ℚ) (Lb : ℕ) (pts : Points) : RawPoly :=
  if testU w ≤ momValL pts.length (dim pts) Lb (2 * sCol w) (whitenL pts)
      (solve Lb (progUL w Lb pts))
  then solve Lb (progUL w Lb pts) else solve Lb (progLL w Lb pts)

/-- The column `â = M e_{j*}`, as `BS23.ColinearSoS.ahatOut`. -/
def ahatL (d : ℕ) (out : RawPoly) : List ℚ :=
  (List.range d).map fun i ↦ momOut d out i (jstarOut d out)

/-- The rows of the whitening matrix `W Ĉ`: row `i` is `λᵢ / scaleOf (λᵢᵀĈλᵢ)`. -/
def wRowsL (pts : Points) : List (List ℚ) :=
  (List.range (dim pts)).map fun i ↦ (List.range (dim pts)).map fun a ↦
    (topScaleL (1 / 2) (quadL (dim pts) (covOf pts) ((basOf pts).getD i [])))⁻¹ *
      ent (basOf pts) i a

/-- `Wᵀ â` for the rows `Wr` of `W`. -/
def dirWL (d : ℕ) (Wr : List (List ℚ)) (ah : List ℚ) : List ℚ :=
  (List.range d).map fun a ↦ ((List.range d).map fun i ↦ ent Wr i a * ah.getD i 0).sum

/-- The direction `a = Wᵀ â` of the chosen output, as in `BS23.ColinearSoS.colLabels`. -/
def aL (w : ℚ) (Lb : ℕ) (pts : Points) : List ℚ :=
  dirWL (dim pts) (wRowsL pts) (ahatL (dim pts) (outCL w Lb pts))

/-- The labels, as `BS23.ColinearSoS.colLabels`: all `0` for `k ≤ 1`, otherwise the line
clustering of the projections on the direction `a`. -/
def labelsL (k : ℕ) (w : ℚ) (Lb : ℕ) (pts : Points) : BS23.Output :=
  if k ≤ 1 then List.replicate pts.length 0
  else clusterL k (w ^ 2 / 100) (w / 4)
    (topScaleL (rangeA w) (quadL (dim pts) (covOf pts) (aL w Lb pts)))
    (Nat.clog 2 pts.length + 8) (projL pts.length (dim pts) pts (aL w Lb pts))

/-- **The algorithm as a list program**, on `((k, wmin, points), Lb)`. -/
def colL (y : (ℕ × ℚ × Points) × ℕ) : BS23.Output := labelsL y.1.1 y.1.2.1 y.2 y.1.2.2

/-! ### It computes the algorithm -/

variable {n d : ℕ}

theorem whitenL_rep' (pts : Points) : RepT (whitenL pts) (whiten (pointsFun pts)) :=
  whitenL_rep ⟨0, 0, pts⟩

theorem cov_rep (pts : Points) : RepT (covOf pts) (empCov (pointsFun pts)) := by
  have hP : RepT pts (pointsFun pts) := ent_pointsFun pts
  have hc : RepT (csOf pts) fun j ↦ pointsFun pts j - mean (pointsFun pts) :=
    centL_rep hP (meanL_rep hP)
  exact covL_rep hc

theorem bas_rep (pts : Points) :
    RepT (basOf pts) fun i ↦ basisVec (empCov (pointsFun pts)) i :=
  basisL_rep (cov_rep pts)

theorem kappaL_rep (pts : Points) : RepV (kappaL pts) (kappa (empCov (pointsFun pts))) := by
  refine repV_map_range _ _ fun i ↦ ?_
  rw [quadL_eq (cov_rep pts) ((bas_rep pts).row i), topScaleL_eq]
  rfl

theorem sphLoRawL_eq {κ : List ℚ} {κ' : Fin d → ℚ} (h : RepV κ κ') :
    sphLoRawL d κ = sphLoRaw κ' := by
  unfold sphLoRawL sphLoRaw
  congr 1
  exact (map_finRange_eq _ _ fun i ↦ by rw [h i]).symm

theorem sphHiRawL_eq {κ : List ℚ} {κ' : Fin d → ℚ} (h : RepV κ κ') :
    sphHiRawL d κ = sphHiRaw κ' := by
  unfold sphHiRawL sphHiRaw
  congr 1
  exact (map_finRange_eq _ _ fun i ↦ by rw [h i]).symm

theorem momRawL_eq (c : ℚ) (Lb r : ℕ) {Z : List (List ℚ)} {Z' : Fin n → Fin d → ℚ}
    (hZ : RepT Z Z') : momRawL c n d Lb r Z = momRaw c Lb r Z' := by
  unfold momRawL momRaw
  congr 1
  exact (flatMap_finRange_eq _ _ fun j ↦ powRawL_eq Lb r (hZ.row j)).symm

theorem progCL_eq (ℓ : ℕ) {κ : List ℚ} {κ' : Fin d → ℚ} (h : RepV κ κ') (obj : RawPoly) :
    progCL d ℓ κ obj = progC ℓ κ' obj := by
  unfold progCL progC
  rw [ballRawL_eq, sphLoRawL_eq h, sphHiRawL_eq h]

theorem progUL_eq (w : ℚ) (Lb : ℕ) (pts : Points) :
    progUL w Lb pts = progUY w Lb (pointsFun pts) := by
  unfold progUL progUY probU
  rw [progCL_eq _ (kappaL_rep pts), momRawL_eq _ _ _ (whitenL_rep' pts)]

theorem progLL_eq (w : ℚ) (Lb : ℕ) (pts : Points) :
    progLL w Lb pts = progLY w Lb (pointsFun pts) := by
  unfold progLL progLY probL
  rw [progCL_eq _ (kappaL_rep pts), momRawL_eq _ _ _ (whitenL_rep' pts)]

theorem momValL_eq (Lb r : ℕ) (out : RawPoly) {Z : List (List ℚ)} {Z' : Fin n → Fin d → ℚ}
    (hZ : RepT Z Z') : momValL n d Lb r Z out = momVal Lb r Z' out := by
  rw [momValL, momVal,
    sum_fin_eq_list _ (fun j ↦ qvOfL d Lb r out (Z.getD j [])) fun j ↦ qvOfL_eq Lb r out (hZ.row j)]

theorem outCL_eq (w : ℚ) (Lb : ℕ) (pts : Points) :
    outCL w Lb pts = outC w Lb (pointsFun pts) := by
  rw [outC_eq, optU, outU, outL, outCL, progUL_eq, progLL_eq,
    momValL_eq _ _ _ (whitenL_rep' pts)]

theorem ahatL_rep (d : ℕ) (out : RawPoly) : RepV (ahatL d out) (ahatOut d out) :=
  repV_map_range _ _ fun _ ↦ rfl

theorem wRowsL_rep (pts : Points) : RepT (wRowsL pts) (W (empCov (pointsFun pts))) :=
  repT_map_range _ _ fun i a ↦ by
    rw [quadL_eq (cov_rep pts) ((bas_rep pts).row i), topScaleL_eq, bas_rep pts i a]
    rfl

theorem dirWL_rep {Wr : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} (hW : RepT Wr M)
    {ah : List ℚ} {ah' : Fin d → ℚ} (hah : RepV ah ah') : RepV (dirWL d Wr ah) (Mᵀ *ᵥ ah') :=
  repV_map_range _ _ fun a ↦ by
    simp only [mulVec, dotProduct, transpose_apply]
    exact (sum_fin_eq_list _ _ fun i ↦ by rw [hW i a, hah i]).symm

theorem aL_rep (w : ℚ) (Lb : ℕ) (pts : Points) :
    RepV (aL w Lb pts)
      (ColinearSoS.dirOf (pointsFun pts) (ahatOut (dim pts) (outC w Lb (pointsFun pts)))) := by
  rw [aL, outCL_eq]
  exact dirWL_rep (wRowsL_rep pts) (ahatL_rep _ _)

theorem labelsL_eq (k : ℕ) (w : ℚ) (Lb : ℕ) (pts : Points) :
    labelsL k w Lb pts = List.ofFn (colLabels k w Lb (pointsFun pts)) := by
  by_cases hk : k ≤ 1
  · rw [labelsL, ite_eq_left hk, colLabels_of_le_one hk, List.ofFn_const]
  · rw [labelsL, ite_eq_right hk, colLabels_of_two_le (by omega), lineLabels_def, clusterL_eq,
      projL_eq (ent_pointsFun pts) (aL_rep w Lb pts), quadL_eq (cov_rep pts) (aL_rep w Lb pts),
      topScaleL_eq]
    rfl

/-- **The list program computes the algorithm.** -/
theorem colL_eq (x : ColinearInput) (Lb : ℕ) : colL ((x.k, x.wmin, x.points), Lb) = colSoS x Lb :=
  labelsL_eq _ _ _ _

/-! ### Polynomial time -/

theorem kappaL_polytime : ComputableInPolyTime kappaL encM encV := by
  unfold kappaL
  have hP : ComputableInPolyTime (fun p : Points × ℕ ↦ p.1) (encPair encM encUnary) encM :=
    fst _ _
  have hq := quadL' (dim' hP) (covOf' hP) (row' (basOf' hP) (snd _ _))
  exact mapWithInput (range.comp (dim' id'))
    (rat_div' hq (rat_sq' (topScaleL' (const (1 / 2)) hq)))

@[fun_prop]
theorem kappaL' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ kappaL (P a)) input encV :=
  kappaL_polytime.comp hP

theorem sphLoRawL_polytime : ComputableInPolyTime (fun p : ℕ × List ℚ ↦ sphLoRawL p.1 p.2)
    (encPair encUnary encV) encRaw := by
  unfold sphLoRawL
  set E := encPair encUnary encV
  have hd : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.1) (encPair E encUnary)
      encUnary := (fst _ _).comp (fst _ _)
  have hκ : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.2) (encPair E encUnary)
      encV := (snd _ _).comp (fst _ _)
  exact cons' (const ([], -1)) (mapWithInput (range.comp (fst _ _))
    ((expAt' hd (snd _ _) (const 2)).prod (vget' hκ (snd _ _))))

theorem sphHiRawL_polytime : ComputableInPolyTime (fun p : ℕ × List ℚ ↦ sphHiRawL p.1 p.2)
    (encPair encUnary encV) encRaw := by
  unfold sphHiRawL
  set E := encPair encUnary encV
  have hd : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.1) (encPair E encUnary)
      encUnary := (fst _ _).comp (fst _ _)
  have hκ : ComputableInPolyTime (fun q : (ℕ × List ℚ) × ℕ ↦ q.1.2) (encPair E encUnary)
      encV := (snd _ _).comp (fst _ _)
  exact cons' (const ([], 1)) (mapWithInput (range.comp (fst _ _))
    ((expAt' hd (snd _ _) (const 2)).prod (rat_neg' (vget' hκ (snd _ _)))))

@[fun_prop]
theorem sphLoRawL' {d : α → ℕ} {κ : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hκ : ComputableInPolyTime κ input encV) :
    ComputableInPolyTime (fun a ↦ sphLoRawL (d a) (κ a)) input encRaw :=
  sphLoRawL_polytime.comp (g := fun a ↦ (d a, κ a)) (hd.prod hκ)

@[fun_prop]
theorem sphHiRawL' {d : α → ℕ} {κ : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hκ : ComputableInPolyTime κ input encV) :
    ComputableInPolyTime (fun a ↦ sphHiRawL (d a) (κ a)) input encRaw :=
  sphHiRawL_polytime.comp (g := fun a ↦ (d a, κ a)) (hd.prod hκ)

/-- The inputs `(c, n, d, Lb, r, Z)` of `BS23.ColinearSoS.PTc.momRawL`. -/
abbrev encMR : ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↪ List Bool :=
  encPair encRat (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encM))))

theorem momRawL_polytime : ComputableInPolyTime
    (fun q : ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ) ↦
      momRawL q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) encMR encRaw := by
  unfold momRawL
  set E := encPair encMR encUnary
  have hd : ComputableInPolyTime (fun z : (ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ ↦ z.1.2.2.1)
      E encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))
  have hLb : ComputableInPolyTime
      (fun z : (ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ ↦ z.1.2.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _))))
  have hr : ComputableInPolyTime
      (fun z : (ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ ↦ z.1.2.2.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))))
  have hZ : ComputableInPolyTime
      (fun z : (ℚ × ℕ × ℕ × ℕ × ℕ × List (List ℚ)) × ℕ ↦ z.1.2.2.2.2.2) E encM :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))))
  exact scaleRaw' (fst _ _) (flatMapWithInput (range.comp ((fst _ _).comp (snd _ _)))
    (powRawL' hd hLb hr (row' hZ (snd _ _))))

@[fun_prop]
theorem momRawL' {c : α → ℚ} {n d Lb r : α → ℕ} {Z : α → List (List ℚ)}
    (hc : ComputableInPolyTime c input encRat) (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hLb : ComputableInPolyTime Lb input encUnary)
    (hr : ComputableInPolyTime r input encUnary) (hZ : ComputableInPolyTime Z input encM) :
    ComputableInPolyTime (fun a ↦ momRawL (c a) (n a) (d a) (Lb a) (r a) (Z a)) input encRaw :=
  momRawL_polytime.comp (g := fun a ↦ (c a, n a, d a, Lb a, r a, Z a))
    (hc.prod (hn.prod (hd.prod (hLb.prod (hr.prod hZ)))))

@[fun_prop]
theorem progCL' {d ℓ : α → ℕ} {κ : α → List ℚ} {obj : α → RawPoly}
    (hd : ComputableInPolyTime d input encUnary) (hℓ : ComputableInPolyTime ℓ input encUnary)
    (hκ : ComputableInPolyTime κ input encV) (hobj : ComputableInPolyTime obj input encRaw) :
    ComputableInPolyTime (fun a ↦ progCL (d a) (ℓ a) (κ a) (obj a)) input
      SoS.PolyTime.encProblemM := by
  unfold progCL
  exact (toBinary' hd).prod ((toBinary' hℓ).prod ((cons' (ballRawL_polytime.comp hd)
    (cons' (sphLoRawL' hd hκ) (cons' (sphHiRawL' hd hκ) (const [])))).prod
      (hobj.prod (const []))))

@[fun_prop]
theorem sCol' {w : α → ℚ} (hw : ComputableInPolyTime w input encRat) :
    ComputableInPolyTime (fun a ↦ sCol (w a)) input encUnary := by
  unfold sCol
  exact unary_add' (logInv' hw) (const 1)

@[fun_prop]
theorem tCol' {w : α → ℚ} (hw : ComputableInPolyTime w input encRat) :
    ComputableInPolyTime (fun a ↦ tCol (w a)) input encUnary := by
  unfold tCol
  exact unary_mul' (const 256) (sCol' hw)

@[fun_prop]
theorem testU' {w : α → ℚ} (hw : ComputableInPolyTime w input encRat) :
    ComputableInPolyTime (fun a ↦ testU (w a)) input encRat := by
  unfold testU
  exact rat_natCast' (binary_pow' (toBinary' (unary_mul' (const 5) (sCol' hw))) (sCol' hw))

@[fun_prop]
theorem progUL' {w : α → ℚ} {Lb : α → ℕ} {P : α → Points}
    (hw : ComputableInPolyTime w input encRat) (hLb : ComputableInPolyTime Lb input encUnary)
    (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ progUL (w a) (Lb a) (P a)) input SoS.PolyTime.encProblemM := by
  unfold progUL
  have hs := unary_mul' (const 2) (sCol' hw)
  exact progCL' (dim' hP) hs (kappaL' hP)
    (momRawL' (rat_neg' (rat_inv' (rat_ofUnary (len' hP)))) (len' hP) (dim' hP) hLb hs
      (whitenL' hP))

@[fun_prop]
theorem progLL' {w : α → ℚ} {Lb : α → ℕ} {P : α → Points}
    (hw : ComputableInPolyTime w input encRat) (hLb : ComputableInPolyTime Lb input encUnary)
    (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ progLL (w a) (Lb a) (P a)) input SoS.PolyTime.encProblemM := by
  unfold progLL
  have ht := unary_mul' (const 2) (tCol' hw)
  exact progCL' (dim' hP) ht (kappaL' hP)
    (momRawL' (rat_inv' (rat_ofUnary (len' hP))) (len' hP) (dim' hP) hLb ht (whitenL' hP))

@[fun_prop]
theorem momValL' {n d Lb r : α → ℕ} {Z : α → List (List ℚ)} {out : α → RawPoly}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hLb : ComputableInPolyTime Lb input encUnary) (hr : ComputableInPolyTime r input encUnary)
    (hZ : ComputableInPolyTime Z input encM) (hout : ComputableInPolyTime out input encRaw) :
    ComputableInPolyTime (fun a ↦ momValL (n a) (d a) (Lb a) (r a) (Z a) (out a)) input
      encRat := by
  unfold momValL
  exact rat_mul' (rat_inv' (rat_ofUnary hn)) (rat_sum' (mapWithInput (range.comp hn)
    (qvOfL' (hd.comp (fst _ _)) (hLb.comp (fst _ _)) (hr.comp (fst _ _)) (hout.comp (fst _ _))
      (row' (hZ.comp (fst _ _)) (snd _ _)))))

/-- The inputs `(w, Lb, points)`. -/
abbrev encWLP : ℚ × ℕ × Points ↪ List Bool := encPair encRat (encPair encUnary encM)

theorem outCL_polytime : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ outCL q.1 q.2.1 q.2.2)
    encWLP encRaw := by
  unfold outCL
  have hw : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.1) encWLP encRat := fst _ _
  have hLb : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.2.1) encWLP encUnary :=
    (fst _ _).comp (snd _ _)
  have hP : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.2.2) encWLP encM :=
    (snd _ _).comp (snd _ _)
  have hU := solve' hLb (progUL' hw hLb hP)
  exact ite_prop (rat_le' (testU' hw) (momValL' (len' hP) (dim' hP) hLb
    (unary_mul' (const 2) (sCol' hw)) (whitenL' hP) hU)) hU (solve' hLb (progLL' hw hLb hP))

@[fun_prop]
theorem outCL' {w : α → ℚ} {Lb : α → ℕ} {P : α → Points}
    (hw : ComputableInPolyTime w input encRat) (hLb : ComputableInPolyTime Lb input encUnary)
    (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ outCL (w a) (Lb a) (P a)) input encRaw :=
  outCL_polytime.comp (g := fun a ↦ (w a, Lb a, P a)) (hw.prod (hLb.prod hP))

theorem pairExp_polytime : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ ↦ pairExp p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList encNat) := by
  unfold pairExp
  set E := encPair encUnary (encPair encUnary encUnary)
  have ha : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.1.2.1) (encPair E encUnary)
      encUnary := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hb : ComputableInPolyTime (fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.1.2.2) (encPair E encUnary)
      encUnary := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact mapWithInput (range.comp (fst _ _))
    (binAdd' (ite_prop (decide_eq' (snd _ _) ha) (const 1) (const 0))
      (ite_prop (decide_eq' (snd _ _) hb) (const 1) (const 0)))

@[fun_prop]
theorem momOut' {d a b : α → ℕ} {out : α → RawPoly} (hd : ComputableInPolyTime d input encUnary)
    (hout : ComputableInPolyTime out input encRaw) (ha : ComputableInPolyTime a input encUnary)
    (hb : ComputableInPolyTime b input encUnary) :
    ComputableInPolyTime (fun x ↦ momOut (d x) (out x) (a x) (b x)) input encRat := by
  unfold momOut
  exact SoS.Poly.coeff' hd hout
    (pairExp_polytime.comp (g := fun x ↦ (d x, a x, b x)) (hd.prod (ha.prod hb)))

/-- `j*` as a left fold over the indices. -/
theorem jstarOut_eq_foldl (d : ℕ) (out : RawPoly) :
    jstarOut d out = (List.range d).foldl
      (fun b a ↦ if momOut d out b b < momOut d out a a then a else b) 0 := by
  rw [jstarOut, argmaxFrom_eq_foldl]

theorem jstarOut_polytime : ComputableInPolyTime (fun p : ℕ × RawPoly ↦ jstarOut p.1 p.2)
    (encPair encUnary encRaw) encUnary := by
  have e : (fun p : ℕ × RawPoly ↦ jstarOut p.1 p.2) = fun p ↦ (List.range p.1).foldl
      (fun b a ↦ if momOut p.1 p.2 b b < momOut p.1 p.2 a a then a else b) 0 :=
    funext fun p ↦ jstarOut_eq_foldl p.1 p.2
  rw [e]
  set E := encPair encUnary encRaw
  have hstep : ComputableInPolyTime (fun q : ((ℕ × RawPoly) × ℕ) × ℕ ↦
      if momOut q.1.1.1 q.1.1.2 q.1.2 q.1.2 < momOut q.1.1.1 q.1.1.2 q.2 q.2 then q.2 else q.1.2)
      (encPair (encPair E encUnary) encUnary) encUnary := by
    have hd : ComputableInPolyTime (fun q : ((ℕ × RawPoly) × ℕ) × ℕ ↦ q.1.1.1)
        (encPair (encPair E encUnary) encUnary) encUnary :=
      (fst _ _).comp ((fst _ _).comp (fst _ _))
    have hout : ComputableInPolyTime (fun q : ((ℕ × RawPoly) × ℕ) × ℕ ↦ q.1.1.2)
        (encPair (encPair E encUnary) encUnary) encRaw := (snd _ _).comp ((fst _ _).comp (fst _ _))
    have hb : ComputableInPolyTime (fun q : ((ℕ × RawPoly) × ℕ) × ℕ ↦ q.1.2)
        (encPair (encPair E encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
    exact ite_prop (rat_lt' (momOut' hd hout hb hb) (momOut' hd hout (snd _ _) (snd _ _)))
      (snd _ _) hb
  refine foldlWith_of_bounded_growth (par := fun p : ℕ × RawPoly ↦ p)
    (step := fun p b a ↦ if momOut p.1 p.2 b b < momOut p.1 p.2 a a then a else b)
    id' (range.comp (fst _ _)) (const 0) hstep
    (growth := fun p ↦ (encUnary p.1).length) (fst _ _).polyBounded_length
    fun x state value hv ↦ ?_
  have h := List.mem_range.1 hv
  simp only [encUnary_apply, List.length_replicate]
  split_ifs <;> omega

@[fun_prop]
theorem jstarOut' {d : α → ℕ} {out : α → RawPoly} (hd : ComputableInPolyTime d input encUnary)
    (hout : ComputableInPolyTime out input encRaw) :
    ComputableInPolyTime (fun x ↦ jstarOut (d x) (out x)) input encUnary :=
  jstarOut_polytime.comp (g := fun x ↦ (d x, out x)) (hd.prod hout)

theorem ahatL_polytime : ComputableInPolyTime (fun p : ℕ × RawPoly ↦ ahatL p.1 p.2)
    (encPair encUnary encRaw) encV := by
  unfold ahatL
  set E := encPair encUnary encRaw
  have hd : ComputableInPolyTime (fun q : (ℕ × RawPoly) × ℕ ↦ q.1.1) (encPair E encUnary)
      encUnary := (fst _ _).comp (fst _ _)
  have hout : ComputableInPolyTime (fun q : (ℕ × RawPoly) × ℕ ↦ q.1.2) (encPair E encUnary)
      encRaw := (snd _ _).comp (fst _ _)
  exact mapWithInput (range.comp (fst _ _)) (momOut' hd hout (snd _ _) (jstarOut' hd hout))

@[fun_prop]
theorem ahatL' {d : α → ℕ} {out : α → RawPoly} (hd : ComputableInPolyTime d input encUnary)
    (hout : ComputableInPolyTime out input encRaw) :
    ComputableInPolyTime (fun x ↦ ahatL (d x) (out x)) input encV :=
  ahatL_polytime.comp (g := fun x ↦ (d x, out x)) (hd.prod hout)

theorem wRowsL_polytime : ComputableInPolyTime wRowsL encM encM := by
  unfold wRowsL
  have hP : ComputableInPolyTime (fun p : (Points × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair encM encUnary) encUnary) encM := (fst _ _).comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : (Points × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair encM encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  exact mapWithInput (range.comp (dim' id')) (mapWithInput (range.comp (dim' (fst _ _)))
    (rat_mul' (rat_inv' (topScaleL' (const (1 / 2))
      (quadL' (dim' hP) (covOf' hP) (row' (basOf' hP) hi)))) (ent' (basOf' hP) hi (snd _ _))))

@[fun_prop]
theorem wRowsL' {P : α → Points} (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ wRowsL (P a)) input encM :=
  wRowsL_polytime.comp hP

theorem dirWL_polytime : ComputableInPolyTime
    (fun p : ℕ × List (List ℚ) × List ℚ ↦ dirWL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encM encV)) encV := by
  unfold dirWL
  set E := encPair encUnary (encPair encM encV)
  have hd : ComputableInPolyTime (fun q : (ℕ × List (List ℚ) × List ℚ) × ℕ ↦ q.1.1)
      (encPair E encUnary) encUnary := (fst _ _).comp (fst _ _)
  have hW : ComputableInPolyTime (fun z : ((ℕ × List (List ℚ) × List ℚ) × ℕ) × ℕ ↦ z.1.1.2.1)
      (encPair (encPair E encUnary) encUnary) encM :=
    (fst _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hah : ComputableInPolyTime (fun z : ((ℕ × List (List ℚ) × List ℚ) × ℕ) × ℕ ↦ z.1.1.2.2)
      (encPair (encPair E encUnary) encUnary) encV :=
    (snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  exact mapWithInput (range.comp (fst _ _)) (rat_sum' (mapWithInput (range.comp hd)
    (rat_mul' (ent' hW (snd _ _) ((snd _ _).comp (fst _ _))) (vget' hah (snd _ _)))))

@[fun_prop]
theorem dirWL' {d : α → ℕ} {Wr : α → List (List ℚ)} {ah : α → List ℚ}
    (hd : ComputableInPolyTime d input encUnary) (hW : ComputableInPolyTime Wr input encM)
    (hah : ComputableInPolyTime ah input encV) :
    ComputableInPolyTime (fun x ↦ dirWL (d x) (Wr x) (ah x)) input encV :=
  dirWL_polytime.comp (g := fun x ↦ (d x, Wr x, ah x)) (hd.prod (hW.prod hah))

theorem aL_polytime : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ aL q.1 q.2.1 q.2.2)
    encWLP encV := by
  unfold aL
  have hw : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.1) encWLP encRat := fst _ _
  have hLb : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.2.1) encWLP encUnary :=
    (fst _ _).comp (snd _ _)
  have hP : ComputableInPolyTime (fun q : ℚ × ℕ × Points ↦ q.2.2) encWLP encM :=
    (snd _ _).comp (snd _ _)
  exact dirWL' (dim' hP) (wRowsL' hP) (ahatL' (dim' hP) (outCL' hw hLb hP))

@[fun_prop]
theorem aL' {w : α → ℚ} {Lb : α → ℕ} {P : α → Points}
    (hw : ComputableInPolyTime w input encRat) (hLb : ComputableInPolyTime Lb input encUnary)
    (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a ↦ aL (w a) (Lb a) (P a)) input encV :=
  aL_polytime.comp (g := fun a ↦ (w a, Lb a, P a)) (hw.prod (hLb.prod hP))

/-- The inputs `((k, wmin, points), Lb)`, with the budget in unary. -/
abbrev encY : (ℕ × ℚ × Points) × ℕ ↪ List Bool := encPair Colinear.PT.encX encUnary

/-- **The list program runs in polynomial time** in the length of `((k, wmin, points), Lb)`. -/
theorem colL_polytime : ComputableInPolyTime colL encY BS23.encOutput := by
  unfold colL labelsL
  have hk : ComputableInPolyTime (fun y : (ℕ × ℚ × Points) × ℕ ↦ y.1.1) encY encNat :=
    (fst _ _).comp (fst _ _)
  have hw : ComputableInPolyTime (fun y : (ℕ × ℚ × Points) × ℕ ↦ y.1.2.1) encY encRat :=
    (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hP : ComputableInPolyTime (fun y : (ℕ × ℚ × Points) × ℕ ↦ y.1.2.2) encY encM :=
    (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hLb : ComputableInPolyTime (fun y : (ℕ × ℚ × Points) × ℕ ↦ y.2) encY encUnary := snd _ _
  have ha := aL' hw hLb hP
  have hz : ComputableInPolyTime (fun y : (ℕ × ℚ × Points) × ℕ ↦
      List.replicate y.1.2.2.length 0) encY (encList encNat) := replicate (len' hP) (const 0)
  exact ite_prop (binary_le' hk (const 1)) hz (unaryList_to_binary.comp
    (clusterL' hk (rat_div' (rat_sq' hw) (const 100)) (rat_div' hw (const 4))
      (topScaleL' (rangeA' hw) (quadL' (dim' hP) (covOf' hP) ha))
      (unary_add' (binary_clog_two.comp (toBinary' (len' hP))) (const 8))
      (projL' (len' hP) (dim' hP) hP ha)))

end BS23.ColinearSoS.PTc
