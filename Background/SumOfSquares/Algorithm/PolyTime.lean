module

public import Background.SumOfSquares.Algorithm.Core
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# The algorithm runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for every function of the algorithm,
ending with `SoS.Core.core_polytime`.

Encodings: exponent vectors are binary (`encList encNat`), indicator vectors of sets unary, and
coordinates `encCrd`.
-/

@[expose] public section

namespace SoS.PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS.Solver SoS.Poly SoS.Coords SoS.Oracle SoS.Loop SoS.Core

variable {α : Type} {input : α ↪ List Bool}

/-- Exponent vectors, in binary. -/
abbrev encE : List ℕ ↪ List Bool := encList encNat

/-- Indicator vectors, in unary. -/
abbrev encV : List ℕ ↪ List Bool := encList encUnary

/-- Coordinates. -/
abbrev encCrd : Crd ↪ List Bool := encPair (encOption encV) encE

/-- Points and cuts. -/
abbrev encPt : List ℚ ↪ List Bool := encList encRat

/-- A case distinction on a decidable proposition. -/
theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a => decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a => if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- `List.idxOf` does not depend on the lawful equality test. -/
theorem idxOf_eq_dec {β : Type} [BEq β] [LawfulBEq β] [DecidableEq β] (a : β) (l : List β) :
    l.idxOf a = @List.idxOf β instBEqOfDecidableEq a l := by
  congr
  exact lawful_beq_subsingleton _ _

theorem val_polytime : ComputableInPolyTime (fun x : List Crd × List ℚ × Crd => val x.1 x.2.1 x.2.2)
    (encPair (encList encCrd) (encPair encPt encCrd)) encRat := by
  unfold val
  have hl : ComputableTidilyInPolyTime (fun x : List Crd × List ℚ × Crd => x.1)
      (encPair (encList encCrd) (encPair encPt encCrd)) (encList encCrd) :=
    ComputableTidilyInPolyTime.fst _ _
  have hx : ComputableTidilyInPolyTime (fun x : List Crd × List ℚ × Crd => x.2.1)
      (encPair (encList encCrd) (encPair encPt encCrd)) encPt :=
    (ComputableTidilyInPolyTime.snd _ _).fst'
  have hc : ComputableTidilyInPolyTime (fun x : List Crd × List ℚ × Crd => x.2.2)
      (encPair (encList encCrd) (encPair encPt encCrd)) encCrd :=
    (ComputableTidilyInPolyTime.snd _ _).snd'
  have hidx : ComputableTidilyInPolyTime (fun x : List Crd × List ℚ × Crd => x.1.idxOf x.2.2)
      (encPair (encList encCrd) (encPair encPt encCrd)) encUnary := by
    have heq : (fun x : List Crd × List ℚ × Crd => x.1.idxOf x.2.2) =
        fun x => @List.idxOf Crd instBEqOfDecidableEq x.2.2 x.1 :=
      funext fun x => idxOf_eq_dec _ _
    rw [heq]
    exact ComputableTidilyInPolyTime.idxOfWithInput (encA := encCrd) hl hc
  have hget : ComputableInPolyTime (fun x : List Crd × List ℚ × Crd =>
      x.2.1.getD (x.1.idxOf x.2.2) 0) (encPair (encList encCrd) (encPair encPt encCrd)) encRat :=
    .of_tidy ((ComputableTidilyInPolyTime.listGetD (encA := encRat) (encL := encList encRat) 0).comp
      (g := fun x : List Crd × List ℚ × Crd => (x.2.1, x.1.idxOf x.2.2)) (hx.prod hidx))
  exact ite_prop (decide_mem (encA := encCrd) (.of_tidy hl) (.of_tidy hc)) hget (const 0)

@[fun_prop]
theorem val' {f : α → List Crd} {g : α → List ℚ} {h : α → Crd}
    (hf : ComputableInPolyTime f input (encList encCrd)) (hg : ComputableInPolyTime g input encPt)
    (hh : ComputableInPolyTime h input encCrd) :
    ComputableInPolyTime (fun a => val (f a) (g a) (h a)) input encRat :=
  val_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem yv_polytime : ComputableInPolyTime
    (fun x : List Crd × List ℚ × List ℕ => yv x.1 x.2.1 x.2.2)
    (encPair (encList encCrd) (encPair encPt encE)) encRat := by
  unfold yv
  have hs : ComputableInPolyTime (fun x : List Crd × List ℚ × List ℕ => x.2.2.sum)
      (encPair (encList encCrd) (encPair encPt encE)) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp (g := fun x : List Crd × List ℚ × List ℕ =>
      x.2.2) ((ComputableTidilyInPolyTime.snd _ _).snd'))
  have hv : ComputableInPolyTime (fun x : List Crd × List ℚ × List ℕ =>
      val x.1 x.2.1 (none, x.2.2)) (encPair (encList encCrd) (encPair encPt encE)) encRat :=
    val' (fst _ _) ((snd _ _).fst') ((const none).prod ((snd _ _).snd'))
  exact ite_prop (by fun_prop) (const 1) hv

@[fun_prop]
theorem yv' {f : α → List Crd} {g : α → List ℚ} {h : α → List ℕ}
    (hf : ComputableInPolyTime f input (encList encCrd)) (hg : ComputableInPolyTime g input encPt)
    (hh : ComputableInPolyTime h input encE) :
    ComputableInPolyTime (fun a => yv (f a) (g a) (h a)) input encRat :=
  yv_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem wv_polytime : ComputableInPolyTime
    (fun x : List Crd × List ℚ × List ℕ × List ℕ => wv x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair (encList encCrd) (encPair encPt (encPair encV encE))) encRat := by
  unfold wv
  exact val' (fst _ _) ((snd _ _).fst') ((optionSome _ |>.comp (g := fun x : List Crd × List ℚ ×
    List ℕ × List ℕ => x.2.2.1) ((snd _ _).snd'.fst')).prod ((snd _ _).snd'.snd'))

@[fun_prop]
theorem wv' {f : α → List Crd} {g : α → List ℚ} {h k : α → List ℕ}
    (hf : ComputableInPolyTime f input (encList encCrd)) (hg : ComputableInPolyTime g input encPt)
    (hh : ComputableInPolyTime h input encV) (hk : ComputableInPolyTime k input encE) :
    ComputableInPolyTime (fun a => wv (f a) (g a) (h a) (k a)) input encRat :=
  wv_polytime.comp (g := fun a => (f a, g a, h a, k a)) (hf.prod (hg.prod (hh.prod hk)))

/-- Sparse vectors. -/
abbrev encSp : Sp ↪ List Bool := encList (encPair encCrd encRat)

theorem spAt_polytime : ComputableInPolyTime (fun x : Sp × Crd => spAt x.1 x.2)
    (encPair encSp encCrd) encRat := by
  unfold spAt
  have h : ComputableInPolyTime (fun x : Sp × Crd => x.1.filter fun q => decide (q.1 = x.2))
      (encPair encSp encCrd) encSp :=
    filterWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem spAt' {f : α → Sp} {g : α → Crd} (hf : ComputableInPolyTime f input encSp)
    (hg : ComputableInPolyTime g input encCrd) :
    ComputableInPolyTime (fun a => spAt (f a) (g a)) input encRat :=
  spAt_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem dense_polytime : ComputableInPolyTime (fun x : List Crd × Sp => dense x.1 x.2)
    (encPair (encList encCrd) encSp) encPt := by
  unfold dense
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem dense' {f : α → List Crd} {g : α → Sp} (hf : ComputableInPolyTime f input (encList encCrd))
    (hg : ComputableInPolyTime g input encSp) :
    ComputableInPolyTime (fun a => dense (f a) (g a)) input encPt :=
  dense_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem scale_polytime : ComputableInPolyTime (fun x : ℚ × Sp => scale x.1 x.2)
    (encPair encRat encSp) encSp := by
  unfold scale
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem scale' {f : α → ℚ} {g : α → Sp} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encSp) :
    ComputableInPolyTime (fun a => scale (f a) (g a)) input encSp :=
  scale_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem spY_polytime : ComputableInPolyTime (fun x : ℕ × RawPoly => spY x.1 x.2)
    (encPair encUnary encRaw) encSp := by
  unfold spY
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem spY' {f : α → ℕ} {g : α → RawPoly} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encRaw) :
    ComputableInPolyTime (fun a => spY (f a) (g a)) input encSp :=
  spY_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem spW_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ × RawPoly => spW x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encV encRaw)) encSp := by
  unfold spW
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem spW' {f : α → ℕ} {g : α → List ℕ} {h : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encV)
    (hh : ComputableInPolyTime h input encRaw) :
    ComputableInPolyTime (fun a => spW (f a) (g a) (h a)) input encSp :=
  spW_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem evalY_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × List ℚ × RawPoly => evalY x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair (encList encCrd) (encPair encPt encRaw))) encRat := by
  unfold evalY
  have h : ComputableInPolyTime (fun x : ℕ × List Crd × List ℚ × RawPoly =>
      x.2.2.2.map fun t => t.2 * yv x.2.1 x.2.2.1 (expo x.1 t.1))
      (encPair encUnary (encPair (encList encCrd) (encPair encPt encRaw))) encPt :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem evalY' {f : α → ℕ} {g : α → List Crd} {h : α → List ℚ} {k : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd))
    (hh : ComputableInPolyTime h input encPt) (hk : ComputableInPolyTime k input encRaw) :
    ComputableInPolyTime (fun a => evalY (f a) (g a) (h a) (k a)) input encRat :=
  evalY_polytime.comp (g := fun a => (f a, g a, h a, k a)) (hf.prod (hg.prod (hh.prod hk)))

theorem polyRaw_polytime : ComputableInPolyTime (fun x : List (List ℕ) × List ℚ => polyRaw x.1 x.2)
    (encPair (encList encE) encPt) encRaw := by
  unfold polyRaw
  fun_prop

@[fun_prop]
theorem polyRaw' {f : α → List (List ℕ)} {g : α → List ℚ}
    (hf : ComputableInPolyTime f input (encList encE)) (hg : ComputableInPolyTime g input encPt) :
    ComputableInPolyTime (fun a => polyRaw (f a) (g a)) input encRaw :=
  polyRaw_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem mulRaw_polytime :
    ComputableInPolyTime (fun x : ℕ × RawPoly × RawPoly => mulRaw x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encRaw encRaw)) encRaw := by
  unfold mulRaw
  exact flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

@[fun_prop]
theorem mulRaw' {f : α → ℕ} {g h : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw)
    (hh : ComputableInPolyTime h input encRaw) :
    ComputableInPolyTime (fun a => mulRaw (f a) (g a) (h a)) input encRaw :=
  mulRaw_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

/-! ### The oracle -/

@[fun_prop]
theorem unitVec' {f g : α → ℕ} {h : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encRat) :
    ComputableInPolyTime (fun a => unitVec (f a) (g a) (h a)) input encPt := by
  unfold unitVec
  exact mapWithInput (by fun_prop) (by fun_prop)

theorem orDef_polytime : ComputableInPolyTime orDef encPt encPt := by
  unfold orDef
  have hall : ComputableInPolyTime (fun a : List ℚ => a.all fun q => decide (q = 0)) encPt
      encBool :=
    allWithInput (by fun_prop) (by fun_prop)
  exact ite' hall (unitVec' (by fun_prop) (const 0) (const 1)) id'

@[fun_prop]
theorem orDef' {f : α → List ℚ} (hf : ComputableInPolyTime f input encPt) :
    ComputableInPolyTime (fun a => orDef (f a)) input encPt :=
  orDef_polytime.comp (g := f) hf

theorem boxCuts_polytime : ComputableInPolyTime (fun x : ℚ × List ℚ => boxCuts x.1 x.2)
    (encPair encRat encPt) (encList encPt) := by
  unfold boxCuts
  have hz : ComputableInPolyTime (fun x : ℚ × List ℚ => x.2.zipIdx) (encPair encRat encPt)
      (encList (encPair encRat encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx encRat).comp (g := fun x : ℚ × List ℚ => x.2)
      (ComputableTidilyInPolyTime.snd _ _))
  have hf : ComputableInPolyTime (fun x : ℚ × List ℚ =>
      x.2.zipIdx.filter fun p => decide (x.1 < |p.1|)) (encPair encRat encPt)
      (encList (encPair encRat encUnary)) :=
    filterWithInput hz (by fun_prop)
  exact mapWithInput hf (by fun_prop)

@[fun_prop]
theorem boxCuts' {f : α → ℚ} {g : α → List ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encPt) :
    ComputableInPolyTime (fun a => boxCuts (f a) (g a)) input (encList encPt) :=
  boxCuts_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

/-- The moment matrix of the moments of a point. -/
theorem momRowsY_polytime : ComputableInPolyTime
    (fun x : (ℕ × List Crd × List ℚ) × ℚ × List (List ℕ) =>
      momRows x.1.1 (yv x.1.2.1 x.1.2.2) x.2.1 x.2.2)
    (encPair (encPair encUnary (encPair (encList encCrd) encPt)) (encPair encRat (encList encE)))
    (encList encPt) := by
  unfold momRows
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

/-- The moment matrix of an auxiliary sequence of a point. -/
theorem momRowsW_polytime : ComputableInPolyTime
    (fun x : (ℕ × List Crd × List ℚ × List ℕ) × ℚ × List (List ℕ) =>
      momRows x.1.1 (wv x.1.2.1 x.1.2.2.1 x.1.2.2.2) x.2.1 x.2.2)
    (encPair (encPair encUnary (encPair (encList encCrd) (encPair encPt encV)))
      (encPair encRat (encList encE))) (encList encPt) := by
  unfold momRows
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

theorem sqRaw_polytime : ComputableInPolyTime
    (fun x : ℕ × List (List ℕ) × List ℤ => sqRaw x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encE) (encList encIntBin))) encRaw := by
  unfold sqRaw
  have hw : ComputableInPolyTime (fun x : ℕ × List (List ℕ) × List ℤ =>
      x.2.2.map (Int.cast : ℤ → ℚ))
      (encPair encUnary (encPair (encList encE) (encList encIntBin))) encPt :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem sqRaw' {f : α → ℕ} {g : α → List (List ℕ)} {h : α → List ℤ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input (encList encE))
    (hh : ComputableInPolyTime h input (encList encIntBin)) :
    ComputableInPolyTime (fun a => sqRaw (f a) (g a) (h a)) input encRaw :=
  sqRaw_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

@[fun_prop]
theorem pdTestRat' {f : α → List (List ℚ)} (hf : ComputableInPolyTime f input (encList encPt)) :
    ComputableInPolyTime (fun a => PDTestRat.test (f a)) input (encOption (encList encIntBin)) :=
  PDTestRat.test_polytime.comp (g := f) hf

/-- The input of a positive definiteness test of the moments: `(n, cs, τ, ms, c)`. -/
abbrev encPsdY : ℕ × List Crd × ℚ × List (List ℕ) × List ℚ ↪ List Bool :=
  encPair encUnary (encPair (encList encCrd) (encPair encRat (encPair (encList encE) encPt)))

theorem psdYCuts_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × ℚ × List (List ℕ) × List ℚ =>
      psdYCuts x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) encPsdY (encList encPt) := by
  unfold psdYCuts
  have hrows : ComputableInPolyTime (fun x : ℕ × List Crd × ℚ × List (List ℕ) × List ℚ =>
      momRows x.1 (yv x.2.1 x.2.2.2.2) x.2.2.1 x.2.2.2.1) encPsdY (encList encPt) :=
    momRowsY_polytime.comp (g := fun x : ℕ × List Crd × ℚ × List (List ℕ) × List ℚ =>
      ((x.1, x.2.1, x.2.2.2.2), x.2.2.1, x.2.2.2.1)) (by fun_prop)
  have htest := pdTestRat' hrows
  have hbody : ComputableInPolyTime (fun p : (ℕ × List Crd × ℚ × List (List ℕ) × List ℚ) ×
      List ℤ => [orDef (dense p.1.2.1 (scale (-1) (spY p.1.1 (sqRaw p.1.1 p.1.2.2.2.1 p.2))))])
      (encPair encPsdY (encList encIntBin)) (encList encPt) := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.optionElimWithInput htest.tidy
    (ComputableTidilyInPolyTime.const []) hbody.tidy)

/-- The input of a positive definiteness test of an auxiliary sequence: `(n, cs, τ, v, ms, c)`. -/
abbrev encPsdW : ℕ × List Crd × ℚ × List ℕ × List (List ℕ) × List ℚ ↪ List Bool :=
  encPair encUnary (encPair (encList encCrd) (encPair encRat (encPair encV
    (encPair (encList encE) encPt))))

theorem psdWCuts_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × ℚ × List ℕ × List (List ℕ) × List ℚ =>
      psdWCuts x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) encPsdW (encList encPt) := by
  unfold psdWCuts
  have hrows : ComputableInPolyTime (fun x : ℕ × List Crd × ℚ × List ℕ × List (List ℕ) × List ℚ =>
      momRows x.1 (wv x.2.1 x.2.2.2.2.2 x.2.2.2.1) x.2.2.1 x.2.2.2.2.1) encPsdW (encList encPt) :=
    momRowsW_polytime.comp (g := fun x : ℕ × List Crd × ℚ × List ℕ × List (List ℕ) × List ℚ =>
      ((x.1, x.2.1, x.2.2.2.2.2, x.2.2.2.1), x.2.2.1, x.2.2.2.2.1)) (by fun_prop)
  have htest := pdTestRat' hrows
  have hbody : ComputableInPolyTime (fun p : (ℕ × List Crd × ℚ × List ℕ × List (List ℕ) ×
      List ℚ) × List ℤ => [orDef (dense p.1.2.1 (scale (-1) (spW p.1.1 p.1.2.2.2.1
        (sqRaw p.1.1 p.1.2.2.2.2.1 p.2))))])
      (encPair encPsdW (encList encIntBin)) (encList encPt) := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.optionElimWithInput htest.tidy
    (ComputableTidilyInPolyTime.const []) hbody.tidy)

theorem resid_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × List ℚ × List ℕ × RawPoly × List ℕ =>
      resid x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (encPair encUnary (encPair (encList encCrd) (encPair encPt (encPair encV
      (encPair encRaw encE))))) encRat := by
  unfold resid
  fun_prop

@[fun_prop]
theorem resid' {f : α → ℕ} {g : α → List Crd} {h : α → List ℚ} {k : α → List ℕ}
    {l : α → RawPoly} {m : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd)) (hh : ComputableInPolyTime h input encPt)
    (hk : ComputableInPolyTime k input encV) (hl : ComputableInPolyTime l input encRaw)
    (hm : ComputableInPolyTime m input encE) :
    ComputableInPolyTime (fun a => resid (f a) (g a) (h a) (k a) (l a) (m a)) input encRat :=
  resid_polytime.comp (g := fun a => (f a, g a, h a, k a, l a, m a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hl.prod hm)))))

theorem distSp_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × List ℚ × List ℕ × RawPoly × List (List ℕ) =>
      distSp x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (encPair encUnary (encPair (encList encCrd) (encPair encPt (encPair encV
      (encPair encRaw (encList encE)))))) encSp := by
  unfold distSp
  exact flatMapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem distSp' {f : α → ℕ} {g : α → List Crd} {h : α → List ℚ} {k : α → List ℕ}
    {l : α → RawPoly} {m : α → List (List ℕ)} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd)) (hh : ComputableInPolyTime h input encPt)
    (hk : ComputableInPolyTime k input encV) (hl : ComputableInPolyTime l input encRaw)
    (hm : ComputableInPolyTime m input (encList encE)) :
    ComputableInPolyTime (fun a => distSp (f a) (g a) (h a) (k a) (l a) (m a)) input encSp :=
  distSp_polytime.comp (g := fun a => (f a, g a, h a, k a, l a, m a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hl.prod hm)))))

theorem distCuts_polytime : ComputableInPolyTime
    (fun x : ℕ × List Crd × ℚ × List ℚ × List ℕ × List (List ℕ) × RawPoly × ℚ =>
      distCuts x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
        x.2.2.2.2.2.2.2)
    (encPair encUnary (encPair (encList encCrd) (encPair encRat (encPair encPt (encPair encV
      (encPair (encList encE) (encPair encRaw encRat))))))) (encList encPt) := by
  unfold distCuts
  have hsum : ComputableInPolyTime
      (fun x : ℕ × List Crd × ℚ × List ℚ × List ℕ × List (List ℕ) × RawPoly × ℚ =>
        (x.2.2.2.2.2.1.map fun e => resid x.1 x.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.2.1 e ^ 2))
      (encPair encUnary (encPair (encList encCrd) (encPair encRat (encPair encPt (encPair encV
        (encPair (encList encE) (encPair encRaw encRat))))))) encPt :=
    mapWithInput (by fun_prop) (by fun_prop)
  exact ite_prop (by fun_prop) (by fun_prop) (const [])

@[fun_prop]
theorem psdYCuts' {f : α → ℕ} {g : α → List Crd} {h : α → ℚ} {k : α → List (List ℕ)}
    {l : α → List ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd)) (hh : ComputableInPolyTime h input encRat)
    (hk : ComputableInPolyTime k input (encList encE)) (hl : ComputableInPolyTime l input encPt) :
    ComputableInPolyTime (fun a => psdYCuts (f a) (g a) (h a) (k a) (l a)) input (encList encPt) :=
  psdYCuts_polytime.comp (g := fun a => (f a, g a, h a, k a, l a))
    (hf.prod (hg.prod (hh.prod (hk.prod hl))))

@[fun_prop]
theorem psdWCuts' {f : α → ℕ} {g : α → List Crd} {h : α → ℚ} {k : α → List ℕ}
    {m : α → List (List ℕ)} {l : α → List ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd)) (hh : ComputableInPolyTime h input encRat)
    (hk : ComputableInPolyTime k input encV) (hm : ComputableInPolyTime m input (encList encE))
    (hl : ComputableInPolyTime l input encPt) :
    ComputableInPolyTime (fun a => psdWCuts (f a) (g a) (h a) (k a) (m a) (l a)) input
      (encList encPt) :=
  psdWCuts_polytime.comp (g := fun a => (f a, g a, h a, k a, m a, l a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hm.prod hl)))))

@[fun_prop]
theorem distCuts' {f : α → ℕ} {g : α → List Crd} {h : α → ℚ} {k : α → List ℚ} {l : α → List ℕ}
    {m : α → List (List ℕ)} {o : α → RawPoly} {r : α → ℚ}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encCrd)) (hh : ComputableInPolyTime h input encRat)
    (hk : ComputableInPolyTime k input encPt) (hl : ComputableInPolyTime l input encV)
    (hm : ComputableInPolyTime m input (encList encE)) (ho : ComputableInPolyTime o input encRaw)
    (hr : ComputableInPolyTime r input encRat) :
    ComputableInPolyTime (fun a => distCuts (f a) (g a) (h a) (k a) (l a) (m a) (o a) (r a)) input
      (encList encPt) :=
  distCuts_polytime.comp (g := fun a => (f a, g a, h a, k a, l a, m a, o a, r a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hl.prod (hm.prod (ho.prod hr)))))))

/-- The data of a set. -/
abbrev encSD : SetData ↪ List Bool :=
  encPair encV (encPair (encList encE) (encPair (encList encE) (encPair encRaw encRat)))

/-- Contexts of the loop. -/
abbrev encCtx : Ctx ↪ List Bool :=
  encPair encUnary (encPair (encList encCrd) (encPair (encList encE) (encPair (encList encSD)
    (encPair encRaw (encPair (encList encRaw) (encPair encRat (encPair encRat encRat)))))))

theorem cuts_polytime : ComputableInPolyTime
    (fun x : Ctx × List ℚ => cuts x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2.2.2.1
      x.1.2.2.2.2.2.2.2.1 x.1.2.2.2.2.2.2.2.2 x.2) (encPair encCtx encPt) (encList encPt) := by
  unfold cuts
  have h1 : ComputableInPolyTime (fun x : Ctx × List ℚ =>
      x.1.2.2.2.1.flatMap fun d => psdWCuts x.1.1 x.1.2.1 x.1.2.2.2.2.2.2.2.1 d.1 d.2.1 x.2)
      (encPair encCtx encPt) (encList encPt) :=
    flatMapWithInput (by fun_prop) (by fun_prop)
  have h2 : ComputableInPolyTime (fun x : Ctx × List ℚ =>
      x.1.2.2.2.1.flatMap fun d => distCuts x.1.1 x.1.2.1 x.1.2.2.2.2.2.2.1 x.2 d.1 d.2.2.1
        d.2.2.2.1 d.2.2.2.2)
      (encPair encCtx encPt) (encList encPt) :=
    flatMapWithInput (by fun_prop) (by fun_prop)
  fun_prop

theorem objVal_polytime : ComputableInPolyTime (fun x : Ctx × List ℚ => ctxObj x.1 x.2)
    (encPair encCtx encPt) encRat := by
  unfold ctxObj objVal
  have h : ComputableInPolyTime (fun x : Ctx × List ℚ =>
      x.1.2.2.2.2.2.1.map fun q => evalY x.1.1 x.1.2.1 x.2 q ^ 2)
      (encPair encCtx encPt) encPt :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

theorem objSp_polytime : ComputableInPolyTime
    (fun x : Ctx × List ℚ => objSp x.1.1 x.1.2.1 x.1.2.2.2.2.1 x.1.2.2.2.2.2.1 x.2)
    (encPair encCtx encPt) encSp := by
  unfold objSp
  have h : ComputableInPolyTime (fun x : Ctx × List ℚ =>
      x.1.2.2.2.2.2.1.flatMap fun q => scale (2 * evalY x.1.1 x.1.2.1 x.2 q) (spY x.1.1 q))
      (encPair encCtx encPt) encSp :=
    flatMapWithInput (by fun_prop) (by fun_prop)
  fun_prop

/-- **The oracle runs in polynomial time.** -/
theorem oracle_polytime : ComputableInPolyTime (fun x : Ctx × List ℚ => ctxOracle x.1 x.2)
    (encPair encCtx encPt) (encPair encBool encPt) := by
  unfold ctxOracle oracle
  have hc := cuts_polytime
  have ho := objSp_polytime
  have hempty : ComputableInPolyTime (fun x : Ctx × List ℚ => (cuts x.1.1 x.1.2.1 x.1.2.2.1
      x.1.2.2.2.1 x.1.2.2.2.2.2.2.1 x.1.2.2.2.2.2.2.2.1 x.1.2.2.2.2.2.2.2.2 x.2).isEmpty)
      (encPair encCtx encPt) encBool := by fun_prop
  refine ite' hempty ((const true).prod (by fun_prop)) ((const false).prod (by fun_prop))

/-! ### The loop -/

theorem roundP_polytime : ComputableInPolyTime (fun x : ℕ × ℚ => roundP x.1 x.2)
    (encPair encUnary encRat) encRat := by
  unfold roundP
  fun_prop

@[fun_prop]
theorem roundP' {f : α → ℕ} {g : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => roundP (f a) (g a)) input encRat :=
  roundP_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

@[fun_prop]
theorem clamp' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => clamp (f a) (g a)) input encRat := by
  unfold clamp
  fun_prop

theorem sqrtP_polytime : ComputableInPolyTime (fun x : ℕ × ℚ => sqrtP x.1 x.2)
    (encPair encUnary encRat) encRat := by
  have h4 : ∀ p : ℕ, (4 : ℚ) ^ p = 2 ^ p * 2 ^ p := fun p => by
    rw [← mul_pow]; norm_num
  have hfl : ComputableInPolyTime (fun x : ℕ × ℚ => ⌊x.2 * (2 ^ x.1 * 2 ^ x.1)⌋)
      (encPair encUnary encRat) encIntBin := by fun_prop
  have habs : ComputableInPolyTime (fun x : ℕ × ℚ => ⌊x.2 * (2 ^ x.1 * 2 ^ x.1)⌋.natAbs)
      (encPair encUnary encRat) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_natAbs.comp (g := fun x : ℕ × ℚ =>
      ⌊x.2 * (2 ^ x.1 * 2 ^ x.1)⌋) hfl.tidy)
  have hsq : ComputableInPolyTime (fun x : ℕ × ℚ => (⌊x.2 * (2 ^ x.1 * 2 ^ x.1)⌋.natAbs).sqrt)
      (encPair encUnary encRat) encNat := binary_sqrt' habs
  have h : ComputableInPolyTime (fun x : ℕ × ℚ =>
      ((⌊x.2 * (2 ^ x.1 * 2 ^ x.1)⌋.natAbs).sqrt : ℚ) / 2 ^ x.1)
      (encPair encUnary encRat) encRat := by fun_prop
  simpa only [sqrtP, h4] using h

@[fun_prop]
theorem sqrtP' {f : α → ℕ} {g : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => sqrtP (f a) (g a)) input encRat :=
  sqrtP_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem dotL_polytime : ComputableInPolyTime (fun x : List ℚ × List ℚ => dotL x.1 x.2)
    (encPair encPt encPt) encRat := by
  have h : ComputableInPolyTime (fun x : List ℚ × List ℚ => ((x.1.zip x.2).map fun q =>
      q.1 * q.2).sum) (encPair encPt encPt) encRat := by
    have hz : ComputableInPolyTime (fun x : List ℚ × List ℚ => x.1.zip x.2) (encPair encPt encPt)
        (encList (encPair encRat encRat)) :=
      .of_tidy (ComputableTidilyInPolyTime.zip encRat encRat)
    have hm : ComputableInPolyTime (fun x : List ℚ × List ℚ => (x.1.zip x.2).map fun q =>
        q.1 * q.2) (encPair encPt encPt) encPt := mapWithInput hz (by fun_prop)
    fun_prop
  have heq : ∀ x : List ℚ × List ℚ, dotL x.1 x.2 = ((x.1.zip x.2).map fun q => q.1 * q.2).sum :=
    fun x => by rw [dotL, List.map_zip_eq_zipWith]; rfl
  simpa only [heq] using h

@[fun_prop]
theorem dotL' {f g : α → List ℚ} (hf : ComputableInPolyTime f input encPt)
    (hg : ComputableInPolyTime g input encPt) :
    ComputableInPolyTime (fun a => dotL (f a) (g a)) input encRat :=
  dotL_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

@[fun_prop]
theorem mulVecL' {f : α → List (List ℚ)} {g : α → List ℚ}
    (hf : ComputableInPolyTime f input (encList encPt)) (hg : ComputableInPolyTime g input encPt) :
    ComputableInPolyTime (fun a => mulVecL (f a) (g a)) input encPt := by
  unfold mulVecL
  exact mapWithInput hf (by fun_prop)

@[fun_prop]
theorem sgn' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => sgn (f a)) input encRat := by
  unfold sgn
  exact ite_prop (by fun_prop) (const 1) (const (-1))

/-- The input of a step: `(N, p, B, c, a, P)`. -/
abbrev encStepIn : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encRat (encPair encPt (encPair encPt
    (encList encPt)))))

theorem stepL_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
      stepL x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    encStepIn (encPair encPt (encList encPt)) := by
  unfold stepL
  have hPa : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
      mulVecL x.2.2.2.2.2 x.2.2.2.2.1) encStepIn encPt := by fun_prop
  have hz1 : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
      x.2.2.2.1.zip (mulVecL x.2.2.2.2.2 x.2.2.2.2.1)) encStepIn
      (encList (encPair encRat encRat)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zip encRat encRat).comp
      (g := fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
        (x.2.2.2.1, mulVecL x.2.2.2.2.2 x.2.2.2.2.1)) ((by fun_prop : ComputableInPolyTime
          (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) => x.2.2.2.1) encStepIn
            encPt).prod hPa).tidy)
  have hz2 : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
      x.2.2.2.2.2.zip (mulVecL x.2.2.2.2.2 x.2.2.2.2.1)) encStepIn
      (encList (encPair encPt encRat)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zip encPt encRat).comp
      (g := fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) =>
        (x.2.2.2.2.2, mulVecL x.2.2.2.2.2 x.2.2.2.2.1)) ((by fun_prop : ComputableInPolyTime
          (fun x : ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ) => x.2.2.2.2.2) encStepIn
            (encList encPt)).prod hPa).tidy)
  refine (mapWithInput hz1 (by fun_prop)).prod (mapWithInput hz2 ?_)
  have hz3 : ComputableInPolyTime (fun p : (ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ)) ×
      (List ℚ × ℚ) => p.2.1.zip (mulVecL p.1.2.2.2.2.2 p.1.2.2.2.2.1))
      (encPair encStepIn (encPair encPt encRat)) (encList (encPair encRat encRat)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zip encRat encRat).comp
      (g := fun p : (ℕ × ℕ × ℚ × List ℚ × List ℚ × List (List ℚ)) × (List ℚ × ℚ) =>
        (p.2.1, mulVecL p.1.2.2.2.2.2 p.1.2.2.2.2.1)) (by fun_prop : ComputableInPolyTime _ _
          (encPair encPt encPt)).tidy)
  exact mapWithInput hz3 (by fun_prop)

@[fun_prop]
theorem stepL' {f g : α → ℕ} {h : α → ℚ} {k l : α → List ℚ} {m : α → List (List ℚ)}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hh : ComputableInPolyTime h input encRat) (hk : ComputableInPolyTime k input encPt)
    (hl : ComputableInPolyTime l input encPt) (hm : ComputableInPolyTime m input (encList encPt)) :
    ComputableInPolyTime (fun a => stepL (f a) (g a) (h a) (k a) (l a) (m a)) input
      (encPair encPt (encList encPt)) :=
  stepL_polytime.comp (g := fun a => (f a, g a, h a, k a, l a, m a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hl.prod hm)))))

/-- The parameters of the loop: the context, `N`, `p` and `B`. -/
abbrev encLoopPar : Ctx × ℕ × ℕ × ℚ ↪ List Bool :=
  encPair encCtx (encPair encUnary (encPair encUnary encRat))

/-- The states of the loop. -/
abbrev encState : State ↪ List Bool :=
  encPair encPt (encPair (encList encPt) (encPair encBool encPt))

theorem loopStep_polytime : ComputableInPolyTime
    (fun x : (Ctx × ℕ × ℕ × ℚ) × State =>
      loopStep x.1.2.1 x.1.2.2.1 x.1.2.2.2 (ctxOracle x.1.1) (ctxObj x.1.1) x.2)
    (encPair encLoopPar encState) encState := by
  unfold loopStep better
  have ho : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State => ctxOracle x.1.1 x.2.1)
      (encPair encLoopPar encState) (encPair encBool encPt) :=
    oracle_polytime.comp (g := fun x : (Ctx × ℕ × ℕ × ℚ) × State => (x.1.1, x.2.1)) (by fun_prop)
  have hf1 : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State => ctxObj x.1.1 x.2.1)
      (encPair encLoopPar encState) encRat :=
    objVal_polytime.comp (g := fun x : (Ctx × ℕ × ℕ × ℚ) × State => (x.1.1, x.2.1)) (by fun_prop)
  have hf2 : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State => ctxObj x.1.1 x.2.2.2.2)
      (encPair encLoopPar encState) encRat :=
    objVal_polytime.comp (g := fun x : (Ctx × ℕ × ℕ × ℚ) × State => (x.1.1, x.2.2.2.2))
      (by fun_prop)
  have hst : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State =>
      stepL x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 (ctxOracle x.1.1 x.2.1).2 x.2.2.1)
      (encPair encLoopPar encState) (encPair encPt (encList encPt)) := by fun_prop
  have hb : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State =>
      ((ctxOracle x.1.1 x.2.1).1 && (!x.2.2.2.1 ||
        decide (ctxObj x.1.1 x.2.1 < ctxObj x.1.1 x.2.2.2.2))))
      (encPair encLoopPar encState) encBool := by fun_prop
  have hor : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State =>
      (x.2.2.2.1 || (ctxOracle x.1.1 x.2.1).1)) (encPair encLoopPar encState) encBool := by fun_prop
  have hbest : ComputableInPolyTime (fun x : (Ctx × ℕ × ℕ × ℚ) × State =>
      if ((ctxOracle x.1.1 x.2.1).1 && (!x.2.2.2.1 ||
        decide (ctxObj x.1.1 x.2.1 < ctxObj x.1.1 x.2.2.2.2))) then x.2.1 else x.2.2.2.2)
      (encPair encLoopPar encState) encPt := ite' hb (by fun_prop) (by fun_prop)
  exact hst.fst'.prod (hst.snd'.prod (hor.prod hbest))

/-! ### Sizes of the loop's states -/

/-- A small number: at most `2^b` in absolute value, and a multiple of `2^-p`. -/
def Small (p b : ℕ) (q : ℚ) : Prop := |q| ≤ 2 ^ b ∧ ∃ z : ℤ, q * 2 ^ p = z

theorem Small.lt {p b : ℕ} {q : ℚ} (h : Small p b q) :
    q.num.natAbs < 2 ^ (b + p + 1) ∧ q.den < 2 ^ (b + p + 1) := by
  obtain ⟨hq, z, hz⟩ := h
  have h2 : (0 : ℚ) < 2 ^ p := by positivity
  have hq' : q = z / 2 ^ p := by rw [← hz]; field_simp
  have hden : q.den ∣ 2 ^ p := by
    have := Rat.den_dvd z (2 ^ p)
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    rw [← hq'] at this
    exact_mod_cast this
  have hden_le : q.den ≤ 2 ^ p := Nat.le_of_dvd (by positivity) hden
  have hlt : 2 ^ (b + p) < 2 ^ (b + p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  constructor
  · have h1 : (q.num.natAbs : ℚ) = |q| * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
    have h2 : (q.num.natAbs : ℚ) ≤ 2 ^ (b + p) := by
      rw [h1, pow_add]
      exact mul_le_mul hq (by exact_mod_cast hden_le) (by positivity) (by positivity)
    have : q.num.natAbs ≤ 2 ^ (b + p) := by exact_mod_cast h2
    omega
  · exact hden_le.trans_lt ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans_lt hlt)

theorem length_encRat_le_of_small {p b : ℕ} {q : ℚ} (h : Small p b q) :
    (encRat q).length ≤ 3 * (b + p) + 6 := by
  obtain ⟨h1, h2⟩ := h.lt
  have : (encRat q).length = (encPair encIntBin encNat (q.num, q.den)).length := rfl
  rw [this, length_encPair, length_encIntBin]
  have h3 := length_encNat_le_of_lt_two_pow h2
  have h4 : q.num.natAbs.size ≤ b + p + 1 := Nat.size_le.2 h1
  simp only at h3 h4 ⊢
  omega

theorem small_zero (p b : ℕ) : Small p b 0 := ⟨by simp, 0, by simp⟩

theorem small_two_pow {p b k : ℕ} (hk : k ≤ b) : Small p b (2 ^ k) := by
  refine ⟨?_, 2 ^ (k + p), by push_cast; ring⟩
  rw [abs_of_pos (by positivity)]
  exact pow_le_pow_right₀ (by norm_num) hk

theorem small_clamp_roundP (p b : ℕ) (y : ℚ) : Small p b (clamp (2 ^ b) (roundP p y)) := by
  refine ⟨abs_clamp_le (by positivity) _, ?_⟩
  have hr : ∃ z : ℤ, roundP p y * 2 ^ p = z := ⟨⌊y * 2 ^ p⌋, by rw [roundP]; field_simp⟩
  have hB : ∃ z : ℤ, (2 : ℚ) ^ b * 2 ^ p = z := ⟨2 ^ (b + p), by push_cast; ring⟩
  have hB' : ∃ z : ℤ, -(2 : ℚ) ^ b * 2 ^ p = z := by
    obtain ⟨z, hz⟩ := hB
    exact ⟨-z, by push_cast; rw [← hz]; ring⟩
  unfold clamp
  rcases le_total (2 ^ b) (roundP p y) with h | h
  · have h0 : (0 : ℚ) ≤ 2 ^ b := by positivity
    rw [min_eq_left h, max_eq_right (by linarith)]
    exact hB
  · rw [min_eq_right h]
    rcases le_total (-2 ^ b) (roundP p y) with h' | h'
    · rw [max_eq_right h']
      exact hr
    · rw [max_eq_left h']
      exact hB'

/-- The invariant of the loop's states: lists of at most `N` small numbers. -/
def Inv (N p b : ℕ) (s : State) : Prop :=
  s.1.length ≤ N ∧ (∀ q ∈ s.1, Small p b q) ∧ s.2.1.length ≤ N ∧
    (∀ row ∈ s.2.1, row.length ≤ N ∧ ∀ q ∈ row, Small p b q) ∧ s.2.2.2.length ≤ N ∧
    ∀ q ∈ s.2.2.2, Small p b q

theorem inv_loopStep {N p b : ℕ} (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ) {s : State}
    (h : Inv N p b s) : Inv N p b (loopStep N p (2 ^ b) orc f s) := by
  obtain ⟨hc, hcs, hP, hPs, hb, hbs⟩ := h
  simp only [loopStep, stepL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_zip]
    omega
  · intro q hq
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
    exact small_clamp_roundP p b _
  · simp only [List.length_map, List.length_zip]
    omega
  · intro row hrow
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hrow
    refine ⟨?_, fun q hq => ?_⟩
    · simp only [List.length_map, List.length_zip]
      have := (hPs _ (List.of_mem_zip hx).1).1
      omega
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hq
      exact small_clamp_roundP p b _
  · split_ifs <;> assumption
  · split_ifs
    · exact hcs
    · exact hbs

theorem length_encPt_le {N p b : ℕ} {c : List ℚ} (hc : c.length ≤ N)
    (hcs : ∀ q ∈ c, Small p b q) : (encPt c).length ≤ N * (6 * (b + p) + 13) := by
  refine (length_encList_le encRat c (b := 3 * (b + p) + 6) fun q hq =>
    length_encRat_le_of_small (hcs q hq)).trans ?_
  have : 2 * (3 * (b + p) + 6) + 1 = 6 * (b + p) + 13 := by ring
  rw [this]
  exact Nat.mul_le_mul_right _ hc

/-- **The states are small.** -/
theorem length_encState_le {N p b : ℕ} {s : State} (h : Inv N p b s) :
    (encState s).length ≤ 10 * (N + 1) ^ 2 * (6 * (b + p) + 13) := by
  obtain ⟨hc, hcs, hP, hPs, hb, hbs⟩ := h
  have h1 := length_encPt_le hc hcs
  have h2 := length_encPt_le hb hbs
  have h3 : (encList encPt s.2.1).length ≤ N * (2 * (N * (6 * (b + p) + 13)) + 1) :=
    (length_encList_le encPt s.2.1 fun row hrow =>
      length_encPt_le (hPs row hrow).1 (hPs row hrow).2).trans (Nat.mul_le_mul_right _ hP)
  simp only [encState, length_encPair, encBool_apply, List.length_singleton]
  set e := 6 * (b + p) + 13
  have he : 1 ≤ e := by omega
  nlinarith

/-! ### The setup -/

/-- A unary natural, in binary. -/
theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

@[fun_prop]
theorem allBU' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a => Mono.allB (f a) (g a) (h a)) input (encList encV) :=
  Mono.allB_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

/-- The budgeted monomials, with binary exponents. -/
theorem allBE' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a => Mono.allB (f a) (g a) (h a)) input (encList encE) := by
  have h1 : ComputableInPolyTime (fun a => (Mono.allB (f a) (g a) (h a)).map fun e =>
      e.map fun k => k) input (encList encE) :=
    mapWithInput (allBU' hf hg hh) (mapWithInput (by fun_prop) (toBinary' (by fun_prop)))
  simpa only [List.map_id'] using h1

@[fun_prop]
theorem degCap' {f g : α → ℕ} {h : α → RawPoly} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encRaw) :
    ComputableInPolyTime (fun a => degCap (f a) (g a) (h a)) input encUnary :=
  degCap_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem dsum_polytime : ComputableInPolyTime (fun x : List ℕ × List ℕ => dsum x.1 x.2)
    (encPair encV encV) encNat := by
  unfold dsum
  have hm : ComputableInPolyTime (fun x : List ℕ × List ℕ =>
      (List.range x.1.length).map fun i => x.2.getD i 0 * x.1.getD i 0)
      (encPair encV encV) (encList encNat) :=
    mapWithInput (by fun_prop) (binary_mul' (toBinary' (by fun_prop)) (toBinary' (by fun_prop)))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp (g := fun x : List ℕ × List ℕ =>
    (List.range x.1.length).map fun i => x.2.getD i 0 * x.1.getD i 0) hm.tidy)

@[fun_prop]
theorem dsum' {f g : α → List ℕ} (hf : ComputableInPolyTime f input encV)
    (hg : ComputableInPolyTime g input encV) :
    ComputableInPolyTime (fun a => dsum (f a) (g a)) input encNat :=
  dsum_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

/-- `ℓ - dsum ds v`, in unary. -/
theorem sub_dsum' {f : α → ℕ} {g h : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encV) (hh : ComputableInPolyTime h input encV) :
    ComputableInPolyTime (fun a => f a - dsum (g a) (h a)) input encUnary := by
  have h1 : ComputableInPolyTime (fun a => f a - min (f a) (dsum (g a) (h a))) input encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_sub.comp
      (g := fun a => (f a, min (f a) (dsum (g a) (h a))))
      (hf.prod (binary_min_unary' hf (dsum' hg hh))).tidy)
  have heq : ∀ a, f a - min (f a) (dsum (g a) (h a)) = f a - dsum (g a) (h a) := fun a => by
    rcases le_total (f a) (dsum (g a) (h a)) with h' | h'
    · rw [min_eq_left h']; omega
    · rw [min_eq_right h']
  simpa only [heq] using h1

theorem isSet_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => isSet x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encV encV)) encBool := by
  unfold isSet
  have hsum : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => x.2.2.sum)
      (encPair encUnary (encPair encV encV)) encNat := by
    have : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => x.2.2.map fun k => k)
        (encPair encUnary (encPair encV encV)) (encList encNat) :=
      mapWithInput (by fun_prop) (toBinary' (by fun_prop))
    have h2 := ComputableTidilyInPolyTime.binary_sum.comp (g := fun x : ℕ × List ℕ × List ℕ =>
      x.2.2.map fun k => k) this.tidy
    simpa only [List.map_id', Function.comp_def] using ComputableInPolyTime.of_tidy h2
  have h1 : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ =>
      x.2.2.all fun a => decide (a ≤ 1)) (encPair encUnary (encPair encV encV)) encBool :=
    allWithInput (by fun_prop) (by fun_prop)
  have h3 : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ =>
      (List.range x.2.1.length).all fun i => decide (x.2.2.getD i 0 = 0 ∨ x.2.1.getD i 0 ≠ 0))
      (encPair encUnary (encPair encV encV)) encBool :=
    allWithInput (by fun_prop) (by fun_prop)
  have h4 : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => decide (dsum x.2.1 x.2.2 ≤ x.1))
      (encPair encUnary (encPair encV encV)) encBool :=
    binary_le' (by fun_prop) (toBinary' (by fun_prop))
  fun_prop

theorem setsB_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × List ℕ => setsB x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encV)) (encList encV) := by
  unfold setsB
  exact filterWithInput (by fun_prop) (isSet_polytime.comp
    (g := fun p : (ℕ × ℕ × List ℕ) × List ℕ => (p.1.2.1, p.1.2.2, p.2)) (by fun_prop))

@[fun_prop]
theorem setsB' {f g : α → ℕ} {h : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encV) :
    ComputableInPolyTime (fun a => setsB (f a) (g a) (h a)) input (encList encV) :=
  setsB_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem coordsB_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℕ × List ℕ => coordsB x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encUnary encV))) (encList encCrd) := by
  unfold coordsB
  have hm := allBE' (input := encPair encUnary (encPair encUnary (encPair encUnary encV)))
    (f := fun x : ℕ × ℕ × ℕ × List ℕ => x.1) (g := fun x => x.2.1) (h := fun x => x.2.2.1)
    (by fun_prop) (by fun_prop) (by fun_prop)
  have hf : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ × List ℕ =>
      (Mono.allB x.1 x.2.1 x.2.2.1).filter fun e => decide (e.sum ≠ 0))
      (encPair encUnary (encPair encUnary (encPair encUnary encV))) (encList encE) :=
    filterWithInput hm (.of_tidy (ComputableTidilyInPolyTime.decide_ne
      (ComputableTidilyInPolyTime.binary_sum.comp
        (g := fun p : (ℕ × ℕ × ℕ × List ℕ) × List ℕ => p.2) (ComputableTidilyInPolyTime.snd _ _))
      (ComputableTidilyInPolyTime.const 0)))
  have h1 : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ × List ℕ =>
      ((Mono.allB x.1 x.2.1 x.2.2.1).filter fun e => decide (e.sum ≠ 0)).map fun e => (none, e))
      (encPair encUnary (encPair encUnary (encPair encUnary encV))) (encList encCrd) :=
    mapWithInput hf (by fun_prop)
  have h2 : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ × List ℕ =>
      (setsB x.1 x.2.2.1 x.2.2.2).flatMap fun v =>
        (Mono.allB x.1 x.2.1 (x.2.2.1 - dsum x.2.2.2 v)).map fun e => (some v, e))
      (encPair encUnary (encPair encUnary (encPair encUnary encV))) (encList encCrd) :=
    flatMapWithInput (by fun_prop) (mapWithInput (allBE' (by fun_prop) (by fun_prop)
      (sub_dsum' (by fun_prop) (by fun_prop) (by fun_prop))) (by fun_prop))
  fun_prop

theorem pick_polytime : ComputableInPolyTime (fun x : List RawPoly × List ℕ => pick x.1 x.2)
    (encPair (encList encRaw) encV) (encList encRaw) := by
  unfold pick
  have hf : ComputableInPolyTime (fun x : List RawPoly × List ℕ =>
      (List.range x.1.length).filter fun i => decide (x.2.getD i 0 = 1))
      (encPair (encList encRaw) encV) (encList encUnary) :=
    filterWithInput (by fun_prop) (by fun_prop)
  exact mapWithInput hf (by fun_prop)

@[fun_prop]
theorem pick' {f : α → List RawPoly} {g : α → List ℕ}
    (hf : ComputableInPolyTime f input (encList encRaw)) (hg : ComputableInPolyTime g input encV) :
    ComputableInPolyTime (fun a => pick (f a) (g a)) input (encList encRaw) :=
  pick_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem setDataB_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℕ × List RawPoly × List ℕ => setDataB x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair (encList encRaw) encV))))
    (encList encSD) := by
  unfold setDataB
  refine mapWithInput (by fun_prop) ?_
  have hD : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List RawPoly × List ℕ) × List ℕ =>
      p.1.2.2.1 - dsum p.1.2.2.2.2 p.2)
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair (encList encRaw)
        encV)))) encV) encUnary := sub_dsum' (by fun_prop) (by fun_prop) (by fun_prop)
  have hnorm : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List RawPoly × List ℕ) × List ℕ =>
      (pick p.1.2.2.2.1 p.2).map (normSq p.1.2.1))
      (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair (encList encRaw)
        encV)))) encV) encPt :=
    mapWithInput (by fun_prop) (by fun_prop)
  exact (by fun_prop : ComputableInPolyTime _ _ encV).prod
    ((allBE' (by fun_prop) (by fun_prop) (by fun_prop)).prod
      ((allBE' (by fun_prop) (by fun_prop) hD).prod
        ((prodRaw' (by fun_prop) (by fun_prop) (by fun_prop)).prod (rat_prod' hnorm))))

/-! ### The algorithm -/

/-- Problems, with complexitylib's encodings (the same as `SoS.Solver.encProblem`). -/
abbrev encProblemM : Problem ↪ List Bool :=
  encPair encNat (encPair encNat (encPair (encList encRaw) (encPair encRaw (encList encRaw))))

/-- Inputs, with complexitylib's encodings (the same as `SoS.Solver.encInput`). -/
abbrev encInputM : Input ↪ List Bool := encPair encProblemM (encPair encRat encRat)

theorem encInput_apply (x : Input) : encInput x = encInputM x := rfl

/-- The inputs of `core`. -/
abbrev encCore : Input × ℕ ↪ List Bool := encPair encInputM encUnary

theorem sizeZ_polytime : ComputableInPolyTime (fun x : Input × ℕ => sizeZ x.1 x.2) encCore
    encUnary := by
  have h : ComputableInPolyTime (fun x : Input × ℕ => (encInputM x.1).length) encCore encUnary :=
    (encoding_length encInputM).comp (g := fun x : Input × ℕ => x.1) (fst _ _)
  have h2 : ComputableInPolyTime (fun x : Input × ℕ => (encInputM x.1).length + x.2 + 4) encCore
      encUnary := unary_add' (unary_add' h (snd _ _)) (const 4)
  have heq : (fun x : Input × ℕ => sizeZ x.1 x.2) = fun x => (encInputM x.1).length + x.2 + 4 := by
    funext x
    unfold sizeZ
    rw [encInput_apply]
  rw [heq]
  exact h2

theorem ctx_polytime : ComputableInPolyTime ctx encCore encCtx := by
  have hZ := sizeZ_polytime
  have hn : ComputableInPolyTime (fun x : Input × ℕ => min x.2 x.1.1.1) encCore encUnary :=
    binary_min_unary' (by fun_prop) (by fun_prop)
  have hl : ComputableInPolyTime (fun x : Input × ℕ => min x.2 x.1.1.2.1) encCore encUnary :=
    binary_min_unary' (by fun_prop) (by fun_prop)
  have hds : ComputableInPolyTime (fun x : Input × ℕ =>
      x.1.1.2.2.1.map (degCap (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 + 1))) encCore encV :=
    mapWithInput (by fun_prop) (by fun_prop)
  have hcs : ComputableInPolyTime (fun x : Input × ℕ => coordsB x.2 (min x.2 x.1.1.1)
      (min x.2 x.1.1.2.1) (x.1.1.2.2.1.map (degCap (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 + 1))))
      encCore (encList encCrd) :=
    coordsB_polytime.comp (g := fun x : Input × ℕ => (x.2, min x.2 x.1.1.1, min x.2 x.1.1.2.1,
      x.1.1.2.2.1.map (degCap (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 + 1))))
      ((by fun_prop : ComputableInPolyTime (fun x : Input × ℕ => x.2) encCore encUnary).prod
        (hn.prod (hl.prod hds)))
  have hms : ComputableInPolyTime (fun x : Input × ℕ =>
      Mono.allB x.2 (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 / 2)) encCore (encList encE) :=
    allBE' (by fun_prop) hn (.of_tidy ((ComputableTidilyInPolyTime.unary_div_const 2).comp
      (g := fun x : Input × ℕ => min x.2 x.1.1.2.1) hl.tidy))
  have hsd : ComputableInPolyTime (fun x : Input × ℕ => setDataB x.2 (min x.2 x.1.1.1)
      (min x.2 x.1.1.2.1) x.1.1.2.2.1
      (x.1.1.2.2.1.map (degCap (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 + 1))))
      encCore (encList encSD) :=
    setDataB_polytime.comp (g := fun x : Input × ℕ => (x.2, min x.2 x.1.1.1, min x.2 x.1.1.2.1,
      x.1.1.2.2.1, x.1.1.2.2.1.map (degCap (min x.2 x.1.1.1) (min x.2 x.1.1.2.1 + 1))))
      ((by fun_prop : ComputableInPolyTime (fun x : Input × ℕ => x.2) encCore encUnary).prod
        (hn.prod (hl.prod ((by fun_prop : ComputableInPolyTime (fun x : Input × ℕ =>
          x.1.1.2.2.1) encCore (encList encRaw)).prod hds))))
  have hτ : ComputableInPolyTime (fun x : Input × ℕ => (1 : ℚ) / 2 ^ (16 * sizeZ x.1 x.2 ^ 4))
      encCore encRat := by fun_prop
  have hR : ComputableInPolyTime (fun x : Input × ℕ => (2 : ℚ) ^ (3 * sizeZ x.1 x.2 ^ 2 + 1))
      encCore encRat := by fun_prop
  unfold ctx
  have hq0 : ComputableInPolyTime (fun x : Input × ℕ => x.1.1.2.2.2.1) encCore encRaw := by
    fun_prop
  have hqs : ComputableInPolyTime (fun x : Input × ℕ => x.1.1.2.2.2.2) encCore
      (encList encRaw) := by
    fun_prop
  have hη : ComputableInPolyTime (fun x : Input × ℕ => x.1.2.1 + x.1.2.2 / 2) encCore encRat := by
    fun_prop
  exact hn.prod (hcs.prod (hms.prod (hsd.prod (hq0.prod (hqs.prod (hη.prod (hτ.prod hR)))))))

@[fun_prop]
theorem expK' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a => expK (f a) (g a)) input encUnary := by
  unfold expK
  fun_prop

@[fun_prop]
theorem expP' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a => expP (f a) (g a)) input encUnary := by
  unfold expP
  fun_prop

@[fun_prop]
theorem expB' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a => expB (f a) (g a)) input encUnary := by
  unfold expB
  fun_prop

/-- The dimension `N`, in unary. -/
theorem dim_polytime : ComputableInPolyTime (fun x : Input × ℕ => (ctx x).2.1.length) encCore
    encUnary :=
  (length_list encCrd).comp (g := fun x : Input × ℕ => (ctx x).2.1) ctx_polytime.snd'.fst'

@[fun_prop]
theorem shape₀' {f : α → ℕ} {g : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => shape₀ (f a) (g a)) input (encList encPt) := by
  unfold shape₀
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

theorem inv_init (N p b k : ℕ) (hk : k ≤ b) :
    Inv N p b (List.replicate N 0, shape₀ N (2 ^ k), false, List.replicate N 0) := by
  refine ⟨by simp, fun q hq => ?_, by simp [shape₀], fun row hrow => ?_, by simp, fun q hq => ?_⟩
  · rw [List.eq_of_mem_replicate hq]; exact small_zero p b
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hrow
    refine ⟨by simp, fun q hq => ?_⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
    split_ifs
    · exact small_two_pow hk
    · exact small_zero p b
  · rw [List.eq_of_mem_replicate hq]; exact small_zero p b

theorem init' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a => ((List.replicate (f a) 0, shape₀ (f a) (2 ^ (8 * g a ^ 2)),
      false, List.replicate (f a) 0) : State)) input encState := by
  fun_prop

/-- **The loop runs in polynomial time.** -/
theorem finalState_polytime : ComputableInPolyTime finalState encCore encState := by
  have hctx := ctx_polytime
  have hN := dim_polytime
  have hZ := sizeZ_polytime
  have hK := expK' hZ hN
  have hP := expP' hZ hN
  have hB := expB' hZ hN
  have hpar : ComputableInPolyTime (fun x : Input × ℕ => (ctx x, (ctx x).2.1.length,
      expP (sizeZ x.1 x.2) (ctx x).2.1.length,
      (2 : ℚ) ^ expB (sizeZ x.1 x.2) (ctx x).2.1.length)) encCore encLoopPar :=
    hctx.prod (hN.prod (hP.prod (rat_two_pow' hB)))
  have hinit := init' hN hZ
  have hsize : PolyBounded (fun x : Input × ℕ => (encCore x).length) (fun x =>
      10 * ((ctx x).2.1.length + 1) ^ 2 * (6 * (expB (sizeZ x.1 x.2) (ctx x).2.1.length +
        expP (sizeZ x.1 x.2) (ctx x).2.1.length) + 13)) := by
    have h1 := hN.polyBounded
    have h2 := hB.polyBounded
    have h3 := hP.polyBounded
    exact ((PolyBounded.const 10).mul ((h1.add (.const 1)).pow 2)).mul
      (((PolyBounded.const 6).mul (h2.add h3)).add (.const 13))
  exact (iterateWith_spec (par := fun x : Input × ℕ => (ctx x, (ctx x).2.1.length,
      expP (sizeZ x.1 x.2) (ctx x).2.1.length, (2 : ℚ) ^ expB (sizeZ x.1 x.2) (ctx x).2.1.length))
    (count := fun x => expK (sizeZ x.1 x.2) (ctx x).2.1.length)
    (init := fun x => ((List.replicate (ctx x).2.1.length 0,
      shape₀ (ctx x).2.1.length (2 ^ (8 * sizeZ x.1 x.2 ^ 2)), false,
      List.replicate (ctx x).2.1.length 0) : State))
    (step := fun π s => loopStep π.2.1 π.2.2.1 π.2.2.2 (ctxOracle π.1) (ctxObj π.1) s)
    hpar hK hinit loopStep_polytime
    (fun x _ s => Inv (ctx x).2.1.length (expP (sizeZ x.1 x.2) (ctx x).2.1.length)
      (expB (sizeZ x.1 x.2) (ctx x).2.1.length) s)
    (fun x => inv_init _ _ _ _ (by unfold expB; omega))
    (fun x _ s _ h => inv_loopStep _ _ h) hsize
    (fun x _ s _ h => length_encState_le h)).1

/-- A unary list, in binary. -/
theorem listToBinary' {f : α → List ℕ} (hf : ComputableInPolyTime f input encV) :
    ComputableInPolyTime f input encE := by
  have h : ComputableInPolyTime (fun a => (f a).map fun k => k) input encE :=
    mapWithInput hf (toBinary' (by fun_prop))
  simpa only [List.map_id'] using h

@[fun_prop]
theorem gridL' {f : α → ℕ} {g : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encV) :
    ComputableInPolyTime (fun a => gridL (f a) (g a)) input encRat := by
  unfold gridL
  have hpow : ComputableInPolyTime (fun p : (α × ℕ) × ℕ => ((p.2 ^ p.1.2 : ℕ) : ℚ))
      (encPair (encPair input encUnary) encUnary) encRat :=
    rat_natCast' (binary_pow' (toBinary' (by fun_prop)) (by fun_prop))
  have hterm : ComputableInPolyTime (fun p : α × ℕ =>
      ((List.range (f p.1 + 1)).map fun t : ℕ => ((t ^ p.2 : ℕ) : ℚ)).sum / (f p.1 + 1))
      (encPair input encUnary) encRat := by
    have hl : ComputableInPolyTime (fun p : α × ℕ =>
        (List.range (f p.1 + 1)).map fun t : ℕ => ((t ^ p.2 : ℕ) : ℚ))
        (encPair input encUnary) encPt := mapWithInput (by fun_prop) hpow
    fun_prop
  have h : ComputableInPolyTime (fun a => ((g a).map fun k =>
      ((List.range (f a + 1)).map fun t : ℕ => ((t ^ k : ℕ) : ℚ)).sum / (f a + 1)).prod)
      input encRat := rat_prod' (mapWithInput hg hterm)
  simpa only [Nat.cast_pow] using h

theorem outputL_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℕ × List Crd × List ℚ × ℚ => outputL x.1 x.2.1 x.2.2.1 x.2.2.2.1
      x.2.2.2.2.1 x.2.2.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair (encList encCrd)
      (encPair encPt encRat))))) encRaw := by
  unfold outputL
  refine mapWithInput (allBU' (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  have he := listToBinary' (input := encPair (encPair encUnary (encPair encUnary (encPair encUnary
    (encPair (encList encCrd) (encPair encPt encRat))))) encV)
    (f := fun p : (ℕ × ℕ × ℕ × List Crd × List ℚ × ℚ) × List ℕ => p.2) (by fun_prop)
  have hd : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ × List Crd × List ℚ × ℚ) × List ℕ =>
      p.1.2.2.1 / 2) (encPair (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair (encList encCrd) (encPair encPt encRat))))) encV) encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.unary_div_const 2).comp
      (g := fun p : (ℕ × ℕ × ℕ × List Crd × List ℚ × ℚ) × List ℕ => p.1.2.2.1) (by fun_prop))
  exact he.prod (by fun_prop)

@[fun_prop]
theorem outputL' {f g h : α → ℕ} {k : α → List Crd} {l : α → List ℚ} {m : α → ℚ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hh : ComputableInPolyTime h input encUnary)
    (hk : ComputableInPolyTime k input (encList encCrd))
    (hl : ComputableInPolyTime l input encPt) (hm : ComputableInPolyTime m input encRat) :
    ComputableInPolyTime (fun a => outputL (f a) (g a) (h a) (k a) (l a) (m a)) input encRaw :=
  outputL_polytime.comp (g := fun a => (f a, g a, h a, k a, l a, m a))
    (hf.prod (hg.prod (hh.prod (hk.prod (hl.prod hm)))))

/-- **The algorithm runs in polynomial time**, in the input and the budget. -/
theorem core_polytime' : ComputableInPolyTime core encCore encRaw := by
  have hctx := ctx_polytime
  have hN := dim_polytime
  have hZ := sizeZ_polytime
  have hF := finalState_polytime
  have hl : ComputableInPolyTime (fun x : Input × ℕ => min x.2 x.1.1.2.1) encCore encUnary :=
    binary_min_unary' (by fun_prop) (by fun_prop)
  have hbest : ComputableInPolyTime (fun x : Input × ℕ => if (finalState x).2.2.1 then
      (finalState x).2.2.2 else List.replicate (ctx x).2.1.length 0) encCore encPt :=
    ite' hF.snd'.snd'.fst' hF.snd'.snd'.snd' (replicate hN (const 0))
  exact outputL' (snd _ _) hctx.fst' hl hctx.snd'.fst' hbest
    (rat_div' (const 1) (rat_two_pow' (by fun_prop)))

/-- **The algorithm runs in polynomial time**, with the encodings of `SoS.Solver`. -/
theorem core_polytime : ComputableInPolyTime core (encPair encInput encUnary) encOutput :=
  core_polytime'.comp (g := id) (of_eq fun _ => rfl)

end SoS.PolyTime
