module

public import BS23.SmallRadius.Alg
public import BS23.Separating.PolyTime

/-!
# The program of a round as a list program, in polynomial time

List versions of the raw polynomials of the program of a round of the small-radius algorithm
([Program.lean](Program.lean)): the points are a table of rows (`BS23.Colinear.PT.RepT`), the
indices are numbers instead of `Fin`, and the coefficients of `B̃` are read from the raw
polynomial `bRaw` (`SoS.Poly.coeff`). Each list version equals the original
(`BS23.SmallRadius.PT.problemL_eq`, `BS23.SmallRadius.PT.bRawL_eq`), and runs in polynomial time
in its inputs, with the layout, the degrees and the budget in unary
(`BS23.SmallRadius.PT.problemL'`, `BS23.SmallRadius.PT.bRawL'`): every list is cut by the budget
(`SoS.Mono.allB`, `SoS.Poly.prodRaw`) or has the length of the layout.
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg
open BS23.Colinear.PT (RepV RepT ent)

/-! ### The list versions -/

namespace Lay

variable (L : Lay)

/-- `⟨zᵢ - μ, v⟩`, for the row `Zi` of `zᵢ`, as `Lay.linRaw`. -/
def linRawL (Zi : List ℚ) : RawPoly :=
  (List.range L.d).flatMap fun a => [tm (List.replicate L.N 0) (unitExp L.d a 1) (Zi.getD a 0),
    tm (unitExp L.N (L.n + a) 1) (unitExp L.d a 1) (-1)]

/-- `wᵢ`, as `Lay.wTerm`. -/
def wTermL (i : ℕ) : RawPoly := [tm (unitExp L.N i 1) [] 1]

/-- `∑_α C_α v^α`, as `Lay.cLin`. -/
def cLinL : RawPoly :=
  (List.range L.A).map fun j => tm (unitExp L.N (L.n + L.d + 1 + j) 1) (L.As.getD j []) 1

/-- `∑_β P_{βc} v^β`, as `Lay.pLin`. -/
def pLinL (c : ℕ) : RawPoly :=
  (List.range L.B).map fun β =>
    tm (unitExp L.N (L.n + L.d + 1 + L.A + (c + L.B * β)) 1) (L.Bs.getD β []) 1

/-- `F_coef`, as `Lay.coefF`, for the table `Z` of the points. -/
def coefFL (Z : List (List ℚ)) (s Lb : ℕ) : RawPoly :=
  L.cLinL ++ neg ((List.range L.n).flatMap fun i =>
    prodRaw (L.N + L.d) Lb (L.wTermL i :: List.replicate (2 * s) (L.linRawL (Z.getD i []))))

/-- `K σ^m B̃(v)`, as `Lay.bPart`, with the coefficients of `B̃` read from `bR`. -/
def bPartL (Gs : List (List ℕ)) (bR : RawPoly) (m : ℕ) (K : ℚ) : RawPoly :=
  Gs.map fun γ => tm (unitExp L.N (L.n + L.d) m) γ (K * SoS.Poly.coeff L.d bR γ)

/-- `F_mom`, as `Lay.momF`. -/
def momFL (Gs : List (List ℕ)) (bR : RawPoly) (m : ℕ) (K : ℚ) (Lb : ℕ) : RawPoly :=
  L.bPartL Gs bR m K ++ neg (prodRaw (L.N + L.d) Lb (List.replicate m L.cLinL)) ++
    neg ((List.range L.B).flatMap fun c => prodRaw (L.N + L.d) Lb (List.replicate 2 (L.pLinL c)))

/-- The ball, as `Lay.ballRaw`. -/
def ballRawL (Bd : ℚ) : RawPoly :=
  ([], Bd) :: (List.range L.N).map fun k => (unitExp L.N k 2, -1)

/-- `wᵢ² - wᵢ`, as `Lay.boolRaw`. -/
def boolRawL (i : ℕ) : RawPoly := [(unitExp L.N i 2, 1), (unitExp L.N i 1, -1)]

/-- `σ - ∑ᵢ wᵢ`, as `Lay.sumRaw`. -/
def sumRawL : RawPoly :=
  (unitExp L.N (L.n + L.d) 1, 1) :: (List.range L.n).map fun i => (unitExp L.N i 1, -1)

/-- The objective, as `Lay.objRaw`. -/
def objRawL : RawPoly := (List.range L.n).map fun i => (unitExp L.N i 1, -1)

/-- The constraints, as `Lay.constraints`. -/
def constraintsL (Z : List (List ℚ)) (Gs : List (List ℕ)) (bR : RawPoly) (s m : ℕ) (K Bd : ℚ)
    (Lb : ℕ) : List RawPoly :=
  L.ballRawL Bd :: ((List.range L.n).flatMap fun i => [L.boolRawL i, neg (L.boolRawL i)]) ++
    [L.sumRawL, neg L.sumRawL] ++
    (L.As.flatMap fun α => [coeffV L.N L.d (L.coefFL Z s Lb) α,
      neg (coeffV L.N L.d (L.coefFL Z s Lb) α)]) ++
    (Gs.flatMap fun γ => [coeffV L.N L.d (L.momFL Gs bR m K Lb) γ,
      neg (coeffV L.N L.d (L.momFL Gs bR m K Lb) γ)])

/-! ### They compute the originals -/

theorem linRawL_eq {z : Fin L.n → Fin L.d → ℚ} {i : Fin L.n} {Zi : List ℚ} (h : RepV Zi (z i)) :
    L.linRawL Zi = L.linRaw z i := by
  unfold linRawL linRaw
  exact (BS23.Separating.PT.flatMap_finRange_eq _ _ fun a => by rw [h a]; rfl).symm

theorem wTermL_eq (i : Fin L.n) : L.wTermL i = L.wTerm i := rfl

theorem cLinL_eq : L.cLinL = L.cLin := by
  unfold cLinL cLin
  refine (BS23.Separating.PT.map_finRange_eq _ _ fun j => ?_).symm
  rw [List.getD_eq_getElem _ _ j.isLt, List.get_eq_getElem]
  rfl

theorem pLinL_eq (c : Fin L.B) : L.pLinL c = L.pLin c := by
  unfold pLinL pLin
  refine (BS23.Separating.PT.map_finRange_eq _ _ fun β => ?_).symm
  rw [List.getD_eq_getElem _ _ β.isLt, List.get_eq_getElem, val_pv]

theorem coefFL_eq {z : Fin L.n → Fin L.d → ℚ} {Z : List (List ℚ)} (hZ : RepT Z z) (s Lb : ℕ) :
    L.coefFL Z s Lb = L.coefF z s Lb := by
  unfold coefFL coefF
  rw [cLinL_eq]
  congr 2
  refine (BS23.Separating.PT.flatMap_finRange_eq _ _ fun i => ?_).symm
  rw [linRawL_eq L (hZ.row i), wTermL_eq]

theorem bPartL_eq (Gs : List (List ℕ)) (bR : RawPoly) (m : ℕ) (K : ℚ) :
    L.bPartL Gs bR m K = L.bPart Gs (SoS.Poly.coeff L.d bR) m K := rfl

theorem momFL_eq (Gs : List (List ℕ)) (bR : RawPoly) (m : ℕ) (K : ℚ) (Lb : ℕ) :
    L.momFL Gs bR m K Lb = L.momF Gs (SoS.Poly.coeff L.d bR) m K Lb := by
  unfold momFL momF
  rw [bPartL_eq, cLinL_eq]
  congr 2
  exact (BS23.Separating.PT.flatMap_finRange_eq _ _ fun c => by rw [pLinL_eq]).symm

theorem ballRawL_eq (Bd : ℚ) : L.ballRawL Bd = L.ballRaw Bd := by
  unfold ballRawL ballRaw
  congr 1
  exact (BS23.Separating.PT.map_finRange_eq _ _ fun _ => rfl).symm

theorem sumRawL_eq : L.sumRawL = L.sumRaw := by
  unfold sumRawL sumRaw
  congr 1
  exact (BS23.Separating.PT.map_finRange_eq _ _ fun _ => rfl).symm

theorem objRawL_eq : L.objRawL = L.objRaw := by
  unfold objRawL objRaw
  exact (BS23.Separating.PT.map_finRange_eq _ _ fun _ => rfl).symm

theorem constraintsL_eq {z : Fin L.n → Fin L.d → ℚ} {Z : List (List ℚ)} (hZ : RepT Z z)
    (Gs : List (List ℕ)) (bR : RawPoly) (s m : ℕ) (K Bd : ℚ) (Lb : ℕ) :
    L.constraintsL Z Gs bR s m K Bd Lb =
      L.constraints z Gs (SoS.Poly.coeff L.d bR) s m K Bd Lb := by
  unfold constraintsL constraints
  have h : ((List.range L.n).flatMap fun i => [L.boolRawL i, neg (L.boolRawL i)]) =
      (List.finRange L.n).flatMap fun i => [L.boolRaw i, neg (L.boolRaw i)] :=
    (BS23.Separating.PT.flatMap_finRange_eq _ _ fun _ => rfl).symm
  rw [ballRawL_eq, sumRawL_eq, coefFL_eq L hZ, momFL_eq, h]
  rfl

end Lay

namespace PT

/-- **The program of a round** as a list program, as `BS23.SmallRadius.problem`, on the table
`Z` of `n` points in dimension `d`, with the coefficients of `B̃` read from `bR`. -/
def problemL (n d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (s t m : ℕ) (K Bd : ℚ) (Lb : ℕ) :
    Problem :=
  ((lay n d s t Lb).N, 64 * t, (lay n d s t Lb).constraintsL Z (gams d t Lb) bR s m K Bd Lb,
    ((lay n d s t Lb).objRawL, []))

theorem problemL_eq {n d : ℕ} {z : Fin n → Fin d → ℚ} {Z : List (List ℚ)} (hZ : RepT Z z)
    (bR : RawPoly) (s t m : ℕ) (K Bd : ℚ) (Lb : ℕ) :
    problemL n d Z bR s t m K Bd Lb = problem z (SoS.Poly.coeff d bR) s t m K Bd Lb := by
  unfold problemL problem
  rw [Lay.constraintsL_eq _ hZ, Lay.objRawL_eq]
  rfl

/-- `⟨Yⱼ, v⟩`, for the row `Yj`, as `BS23.SmallRadius.yLin`. -/
def yLinL (d : ℕ) (Yj : List ℚ) : RawPoly :=
  (List.range d).map fun a => (unitExp d a 1, Yj.getD a 0)

/-- `B̃`, as `BS23.SmallRadius.bRaw`, for the table `Y` of `n` points in dimension `d`. -/
def bRawL (n d : ℕ) (Y : List (List ℚ)) (t Lb : ℕ) : RawPoly :=
  (List.range n).flatMap fun j =>
    smul ((n : ℚ) * t ^ t)⁻¹ (prodRaw d Lb (List.replicate (2 * t) (yLinL d (Y.getD j []))))

theorem bRawL_eq {n d : ℕ} {Y' : Fin n → Fin d → ℚ} {Y : List (List ℚ)} (hY : RepT Y Y')
    (t Lb : ℕ) : bRawL n d Y t Lb = bRaw Y' t Lb := by
  unfold bRawL bRaw
  refine (BS23.Separating.PT.flatMap_finRange_eq _ _ fun j => ?_).symm
  have : yLinL d (Y.getD j []) = yLin Y' j := by
    unfold yLinL yLin
    exact (BS23.Separating.PT.map_finRange_eq _ _ fun a => by rw [hY.row j a]).symm
  rw [this]

/-! ### Polynomial time -/

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open BS23.Colinear.PT (encV encM vget' row' rat_ofUnary rat_pow' toBinary')

variable {α : Type} {input : α ↪ List Bool}

/-- Exponent vectors, in binary. -/
abbrev encE : List ℕ ↪ List Bool := encList encNat

/-- Lists of exponent vectors. -/
abbrev encEs : List (List ℕ) ↪ List Bool := encList encE

/-- The components `(n, d, As, Bs)` of a layout. -/
abbrev encLayT : ℕ × ℕ × List (List ℕ) × List (List ℕ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encEs encEs))

/-- Layouts, by their components: `n` and `d` in unary, the exponent vectors in binary. -/
def encLay : Lay ↪ List Bool :=
  ⟨fun L => encLayT (L.n, L.d, L.As, L.Bs), fun L L' h => by
    obtain ⟨n, d, As, Bs⟩ := L
    obtain ⟨n', d', As', Bs'⟩ := L'
    have := encLayT.injective h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl, rfl⟩ := this
    rfl⟩

theorem layT_polytime : ComputableInPolyTime (fun L : Lay => (L.n, L.d, L.As, L.Bs)) encLay
    encLayT :=
  of_eq fun _ => rfl

theorem mkLay_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (List ℕ) × List (List ℕ) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : Lay))
    encLayT encLay :=
  of_eq fun _ => rfl

section LayP

variable {L : α → Lay} (hL : ComputableInPolyTime L input encLay)
include hL

theorem lay_n' : ComputableInPolyTime (fun a => (L a).n) input encUnary :=
  (fst _ _).comp (layT_polytime.comp hL)

theorem lay_d' : ComputableInPolyTime (fun a => (L a).d) input encUnary :=
  (fst _ _).comp ((snd _ _).comp (layT_polytime.comp hL))

theorem lay_As' : ComputableInPolyTime (fun a => (L a).As) input encEs :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (layT_polytime.comp hL)))

theorem lay_Bs' : ComputableInPolyTime (fun a => (L a).Bs) input encEs :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (layT_polytime.comp hL)))

theorem lay_A' : ComputableInPolyTime (fun a => (L a).A) input encUnary :=
  (length_list encE).comp (lay_As' hL)

theorem lay_B' : ComputableInPolyTime (fun a => (L a).B) input encUnary :=
  (length_list encE).comp (lay_Bs' hL)

theorem lay_N' : ComputableInPolyTime (fun a => (L a).N) input encUnary :=
  unary_add' (unary_add' (unary_add' (unary_add' (lay_n' hL) (lay_d' hL)) (const 1)) (lay_A' hL))
    (unary_mul' (lay_B' hL) (lay_B' hL))

end LayP

theorem lay' {n d s t Lb : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (ht : ComputableInPolyTime t input encUnary) (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => lay (n a) (d a) (s a) (t a) (Lb a)) input encLay :=
  mkLay_polytime.comp (g := fun a => (n a, d a, Mono.allB (Lb a) (d a) (2 * s a),
      Mono.allB (Lb a) (d a) (t a)))
    (hn.prod (hd.prod ((SoS.PolyTime.allBE' hLb hd (unary_mul' (const 2) hs)).prod
      (SoS.PolyTime.allBE' hLb hd ht))))

theorem unitExp' {N k e : α → ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hk : ComputableInPolyTime k input encUnary) (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a => unitExp (N a) (k a) (e a)) input encE :=
  BS23.Separating.PT.expAt' hN hk he

theorem tm' {u v : α → List ℕ} {c : α → ℚ} (hu : ComputableInPolyTime u input encE)
    (hv : ComputableInPolyTime v input encE) (hc : ComputableInPolyTime c input encRat) :
    ComputableInPolyTime (fun a => tm (u a) (v a) (c a)) input encTerm :=
  (listAppend' hu hv).prod hc

theorem neg' {p : α → RawPoly} (hp : ComputableInPolyTime p input encRaw) :
    ComputableInPolyTime (fun a => neg (p a)) input encRaw :=
  mapWithInput hp (((fst _ _).comp (snd _ _)).prod (rat_neg' ((snd _ _).comp (snd _ _))))

theorem smul' {c : α → ℚ} {p : α → RawPoly} (hc : ComputableInPolyTime c input encRat)
    (hp : ComputableInPolyTime p input encRaw) :
    ComputableInPolyTime (fun a => smul (c a) (p a)) input encRaw :=
  BS23.Separating.PT.scaleRaw' hc hp

theorem vpart' {n d : α → ℕ} {e : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (he : ComputableInPolyTime e input encE) :
    ComputableInPolyTime (fun a => vpart (n a) (d a) (e a)) input encE :=
  mapWithInput (range.comp hd)
    (listGetDWithInput (he.comp (fst _ _)) (unary_add' (hn.comp (fst _ _)) (snd _ _)) 0)

theorem coeffV' {n d : α → ℕ} {F : α → RawPoly} {γ : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hF : ComputableInPolyTime F input encRaw) (hγ : ComputableInPolyTime γ input encE) :
    ComputableInPolyTime (fun a => coeffV (n a) (d a) (F a) (γ a)) input encRaw :=
  filterWithInput hF (decide_eq' (vpart' (hn.comp (fst _ _)) (hd.comp (fst _ _))
    ((fst _ _).comp (snd _ _))) (hγ.comp (fst _ _)))

section LayRaw

variable {L : α → Lay} (hL : ComputableInPolyTime L input encLay)
include hL

theorem linRawL' {Zi : α → List ℚ} (hZ : ComputableInPolyTime Zi input encV) :
    ComputableInPolyTime (fun a => (L a).linRawL (Zi a)) input encRaw := by
  unfold Lay.linRawL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  have hZ1 : ComputableInPolyTime (fun p : α × ℕ => Zi p.1) (encPair input encUnary) encV :=
    hZ.comp (fst _ _)
  exact flatMapWithInput (range.comp (lay_d' hL))
    (cons' (tm' (replicate (lay_N' hL1) (const 0)) (unitExp' (lay_d' hL1) (snd _ _) (const 1))
        (vget' hZ1 (snd _ _)))
      (cons' (tm' (unitExp' (lay_N' hL1) (unary_add' (lay_n' hL1) (snd _ _)) (const 1))
          (unitExp' (lay_d' hL1) (snd _ _) (const 1)) (const (-1))) (const [])))

theorem wTermL' {i : α → ℕ} (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (L a).wTermL (i a)) input encRaw := by
  unfold Lay.wTermL
  exact cons' (tm' (unitExp' (lay_N' hL) hi (const 1)) (const []) (const 1)) (const [])

theorem cLinL' : ComputableInPolyTime (fun a => (L a).cLinL) input encRaw := by
  unfold Lay.cLinL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact mapWithInput (range.comp (lay_A' hL))
    (tm' (unitExp' (lay_N' hL1) (unary_add' (unary_add' (unary_add' (lay_n' hL1) (lay_d' hL1))
        (const 1)) (snd _ _)) (const 1))
      (listGetDWithInput (lay_As' hL1) (snd _ _) []) (const 1))

theorem pLinL' {c : α → ℕ} (hc : ComputableInPolyTime c input encUnary) :
    ComputableInPolyTime (fun a => (L a).pLinL (c a)) input encRaw := by
  unfold Lay.pLinL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact mapWithInput (range.comp (lay_B' hL))
    (tm' (unitExp' (lay_N' hL1) (unary_add' (unary_add' (unary_add' (unary_add' (lay_n' hL1)
        (lay_d' hL1)) (const 1)) (lay_A' hL1))
          (unary_add' (hc.comp (fst _ _)) (unary_mul' (lay_B' hL1) (snd _ _)))) (const 1))
      (listGetDWithInput (lay_Bs' hL1) (snd _ _) []) (const 1))

theorem coefFL' {Z : α → List (List ℚ)} {s Lb : α → ℕ} (hZ : ComputableInPolyTime Z input encM)
    (hs : ComputableInPolyTime s input encUnary) (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => (L a).coefFL (Z a) (s a) (Lb a)) input encRaw := by
  unfold Lay.coefFL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact listAppend' (cLinL' hL) (neg' (flatMapWithInput (range.comp (lay_n' hL))
    (prodRaw' (unary_add' (lay_N' hL1) (lay_d' hL1)) (hLb.comp (fst _ _))
      (cons' (wTermL' hL1 (snd _ _)) (replicate (unary_mul' (const 2) (hs.comp (fst _ _)))
        (linRawL' hL1 (row' (hZ.comp (fst _ _)) (snd _ _))))))))

theorem bPartL' {Gs : α → List (List ℕ)} {bR : α → RawPoly} {m : α → ℕ} {K : α → ℚ}
    (hGs : ComputableInPolyTime Gs input encEs) (hbR : ComputableInPolyTime bR input encRaw)
    (hm : ComputableInPolyTime m input encNat) (hK : ComputableInPolyTime K input encRat) :
    ComputableInPolyTime (fun a => (L a).bPartL (Gs a) (bR a) (m a) (K a)) input encRaw := by
  unfold Lay.bPartL
  have hL1 : ComputableInPolyTime (fun p : α × List ℕ => L p.1) (encPair input encE) encLay :=
    hL.comp (fst _ _)
  exact mapWithInput hGs (tm' (unitExp' (lay_N' hL1) (unary_add' (lay_n' hL1) (lay_d' hL1))
      (hm.comp (fst _ _))) (snd _ _)
    (rat_mul' (hK.comp (fst _ _)) (SoS.Poly.coeff' (lay_d' hL1) (hbR.comp (fst _ _)) (snd _ _))))

theorem momFL' {Gs : α → List (List ℕ)} {bR : α → RawPoly} {m : α → ℕ} {K : α → ℚ}
    {Lb : α → ℕ} (hGs : ComputableInPolyTime Gs input encEs)
    (hbR : ComputableInPolyTime bR input encRaw) (hm : ComputableInPolyTime m input encUnary)
    (hK : ComputableInPolyTime K input encRat) (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => (L a).momFL (Gs a) (bR a) (m a) (K a) (Lb a)) input encRaw := by
  unfold Lay.momFL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact listAppend' (listAppend' (bPartL' hL hGs hbR (toBinary' hm) hK)
      (neg' (prodRaw' (unary_add' (lay_N' hL) (lay_d' hL)) hLb (replicate hm (cLinL' hL)))))
    (neg' (flatMapWithInput (range.comp (lay_B' hL))
      (prodRaw' (unary_add' (lay_N' hL1) (lay_d' hL1)) (hLb.comp (fst _ _))
        (replicate (const 2) (pLinL' hL1 (snd _ _))))))

theorem ballRawL' {Bd : α → ℚ} (hBd : ComputableInPolyTime Bd input encRat) :
    ComputableInPolyTime (fun a => (L a).ballRawL (Bd a)) input encRaw := by
  unfold Lay.ballRawL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact cons' ((const []).prod hBd) (mapWithInput (range.comp (lay_N' hL))
    ((unitExp' (lay_N' hL1) (snd _ _) (const 2)).prod (const (-1))))

theorem boolRawL' {i : α → ℕ} (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (L a).boolRawL (i a)) input encRaw := by
  unfold Lay.boolRawL
  exact cons' ((unitExp' (lay_N' hL) hi (const 2)).prod (const 1))
    (cons' ((unitExp' (lay_N' hL) hi (const 1)).prod (const (-1))) (const []))

theorem sumRawL' : ComputableInPolyTime (fun a => (L a).sumRawL) input encRaw := by
  unfold Lay.sumRawL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact cons' ((unitExp' (lay_N' hL) (unary_add' (lay_n' hL) (lay_d' hL)) (const 1)).prod
    (const 1)) (mapWithInput (range.comp (lay_n' hL))
      ((unitExp' (lay_N' hL1) (snd _ _) (const 1)).prod (const (-1))))

theorem objRawL' : ComputableInPolyTime (fun a => (L a).objRawL) input encRaw := by
  unfold Lay.objRawL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  exact mapWithInput (range.comp (lay_n' hL))
    ((unitExp' (lay_N' hL1) (snd _ _) (const 1)).prod (const (-1)))

theorem constraintsL' {Z : α → List (List ℚ)} {Gs : α → List (List ℕ)} {bR : α → RawPoly}
    {s m : α → ℕ} {K Bd : α → ℚ} {Lb : α → ℕ} (hZ : ComputableInPolyTime Z input encM)
    (hGs : ComputableInPolyTime Gs input encEs) (hbR : ComputableInPolyTime bR input encRaw)
    (hs : ComputableInPolyTime s input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hK : ComputableInPolyTime K input encRat) (hBd : ComputableInPolyTime Bd input encRat)
    (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => (L a).constraintsL (Z a) (Gs a) (bR a) (s a) (m a) (K a)
      (Bd a) (Lb a)) input (encList encRaw) := by
  unfold Lay.constraintsL
  have hL1 : ComputableInPolyTime (fun p : α × ℕ => L p.1) (encPair input encUnary) encLay :=
    hL.comp (fst _ _)
  have hL2 : ComputableInPolyTime (fun p : α × List ℕ => L p.1) (encPair input encE) encLay :=
    hL.comp (fst _ _)
  have hcoef : ComputableInPolyTime (fun p : α × List ℕ =>
      coeffV (L p.1).N (L p.1).d ((L p.1).coefFL (Z p.1) (s p.1) (Lb p.1)) p.2)
      (encPair input encE) encRaw :=
    coeffV' (lay_N' hL2) (lay_d' hL2) (coefFL' hL2 (hZ.comp (fst _ _)) (hs.comp (fst _ _))
      (hLb.comp (fst _ _))) (snd _ _)
  have hmom : ComputableInPolyTime (fun p : α × List ℕ =>
      coeffV (L p.1).N (L p.1).d ((L p.1).momFL (Gs p.1) (bR p.1) (m p.1) (K p.1) (Lb p.1)) p.2)
      (encPair input encE) encRaw :=
    coeffV' (lay_N' hL2) (lay_d' hL2) (momFL' hL2 (hGs.comp (fst _ _)) (hbR.comp (fst _ _))
      (hm.comp (fst _ _)) (hK.comp (fst _ _)) (hLb.comp (fst _ _))) (snd _ _)
  exact listAppend' (listAppend' (listAppend' (cons' (ballRawL' hL hBd)
      (flatMapWithInput (range.comp (lay_n' hL)) (cons' (boolRawL' hL1 (snd _ _))
        (cons' (neg' (boolRawL' hL1 (snd _ _))) (const [])))))
      (cons' (sumRawL' hL) (cons' (neg' (sumRawL' hL)) (const []))))
      (flatMapWithInput (lay_As' hL) (cons' hcoef (cons' (neg' hcoef) (const [])))))
    (flatMapWithInput hGs (cons' hmom (cons' (neg' hmom) (const []))))

end LayRaw

/-- **The program of a round runs in polynomial time**, with `n`, `d`, the degrees and the budget
in unary. -/
theorem problemL' {n d : α → ℕ} {Z : α → List (List ℚ)} {bR : α → RawPoly} {s t m : α → ℕ}
    {K Bd : α → ℚ} {Lb : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hZ : ComputableInPolyTime Z input encM)
    (hbR : ComputableInPolyTime bR input encRaw) (hs : ComputableInPolyTime s input encUnary)
    (ht : ComputableInPolyTime t input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hK : ComputableInPolyTime K input encRat) (hBd : ComputableInPolyTime Bd input encRat)
    (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => problemL (n a) (d a) (Z a) (bR a) (s a) (t a) (m a) (K a)
      (Bd a) (Lb a)) input SoS.PolyTime.encProblemM := by
  unfold problemL
  have hL := lay' hn hd hs ht hLb
  have hGs : ComputableInPolyTime (fun a => gams (d a) (t a) (Lb a)) input encEs :=
    SoS.PolyTime.allBE' hLb hd (unary_mul' (const 2) ht)
  exact (toBinary' (lay_N' hL)).prod ((toBinary' (unary_mul' (const 64) ht)).prod
    ((constraintsL' hL hZ hGs hbR hs hm hK hBd hLb).prod ((objRawL' hL).prod (const []))))

theorem yLinL' {d : α → ℕ} {Yj : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hY : ComputableInPolyTime Yj input encV) :
    ComputableInPolyTime (fun a => yLinL (d a) (Yj a)) input encRaw := by
  unfold yLinL
  exact mapWithInput (range.comp hd) ((unitExp' (hd.comp (fst _ _)) (snd _ _) (const 1)).prod
    (vget' (hY.comp (fst _ _)) (snd _ _)))

/-- **`B̃` runs in polynomial time**, with `n`, `d`, `t` and the budget in unary. -/
theorem bRawL' {n d t Lb : α → ℕ} {Y : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hY : ComputableInPolyTime Y input encM) (ht : ComputableInPolyTime t input encUnary)
    (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => bRawL (n a) (d a) (Y a) (t a) (Lb a)) input encRaw := by
  unfold bRawL
  have hn1 : ComputableInPolyTime (fun p : α × ℕ => n p.1) (encPair input encUnary) encUnary :=
    hn.comp (fst _ _)
  have ht1 : ComputableInPolyTime (fun p : α × ℕ => t p.1) (encPair input encUnary) encUnary :=
    ht.comp (fst _ _)
  exact flatMapWithInput (range.comp hn)
    (smul' (rat_inv' (rat_mul' (rat_ofUnary hn1) (rat_pow' (rat_ofUnary ht1) ht1)))
      (prodRaw' (hd.comp (fst _ _)) (hLb.comp (fst _ _))
        (replicate (unary_mul' (const 2) ht1) (yLinL' (hd.comp (fst _ _))
          (row' (hY.comp (fst _ _)) (snd _ _))))))

end PT

end BS23.SmallRadius
