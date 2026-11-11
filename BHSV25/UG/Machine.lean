module

public import BHSV25.UG.Cover
public import BHSV25.UG.Regular
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The double cover and the regularization run in polynomial time

`BHSV25.UG.cover_polytime` and `BHSV25.UG.regularize_polytime`, certified with complexitylib's
calculus: the inverse table maps the positions `a < |π|` to `π.idxOf a`; a block reads the
constraint at position `j`, filters the constraints at its left vertex, and repeats them a
unary number of times (`⌊A / d⌋` and `A mod d`, for `A = ℓ |cs|`).
-/

@[expose] public section

namespace BHSV25.UG

open UniqueGames BK Turing.MultiTapeTM ComputableInPolyTime

/-- The encoding of a constraint. -/
abbrev encC : UGConstraint ↪ List Bool := encPair (encPair encNat encNat) (encList encNat)

theorem toBin : ComputableInPolyTime (fun n : ℕ ↦ n) encUnary encNat := by fun_prop

theorem invTable_polytime : ComputableInPolyTime invTable (encList encNat) (encList encNat) := by
  unfold invTable
  have hl : ComputableInPolyTime (fun π : List ℕ ↦ List.range π.length) (encList encNat)
      (encList encUnary) := by fun_prop
  have hval : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.2)
      (encPair (encList encNat) encUnary) encNat := toBin.comp (snd _ _)
  have hidx : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.1.idxOf p.2)
      (encPair (encList encNat) encUnary) encNat :=
    toBin.comp (.of_tidy (ComputableTidilyInPolyTime.idxOfWithInput (fst _ _).tidy hval.tidy))
  exact mapWithInput (f := fun (π : List ℕ) (a : ℕ) ↦ π.idxOf a) hl hidx

/-- **The double cover runs in polynomial time.** -/
theorem cover_polytime : ComputableInPolyTime cover encUGGraph encUG := by
  unfold cover encUGGraph encUG
  have hp : ComputableInPolyTime (fun c : UGConstraint ↦ (c.1.2, c.1.1)) encC
      (encPair encNat encNat) := ((snd _ _).comp (fst _ _)).prod ((fst _ _).comp (fst _ _))
  have hc : ComputableInPolyTime (fun c : UGConstraint ↦ [c, ((c.1.2, c.1.1), invTable c.2)])
      encC (encList encC) :=
    cons' id' (cons' (hp.prod (invTable_polytime.comp (snd _ _))) (const []))
  have hlist : ComputableInPolyTime (fun G : UGGraphInstance ↦ G.2.2)
      (encPair encNat (encPair encNat (encList encC))) (encList encC) := (snd _ _).comp (snd _ _)
  have hL : ComputableInPolyTime (fun G : UGGraphInstance ↦
      G.2.2.flatMap fun c ↦ [c, ((c.1.2, c.1.1), invTable c.2)])
      (encPair encNat (encPair encNat (encList encC))) (encList encC) :=
    flatMapWithInput (f := fun _ (c : UGConstraint) ↦ [c, ((c.1.2, c.1.1), invTable c.2)]) hlist
      (hc.comp (snd _ _))
  have h1 : ComputableInPolyTime (fun G : UGGraphInstance ↦ G.1)
      (encPair encNat (encPair encNat (encList encC))) encNat := fst _ _
  have h2 : ComputableInPolyTime (fun G : UGGraphInstance ↦ G.2.1)
      (encPair encNat (encPair encNat (encList encC))) encNat := (fst _ _).comp (snd _ _)
  exact h1.prod (h1.prod (h2.prod hL))

/-- The input of a block: the constraints and the position `j`, in unary. -/
abbrev encBlk : List UGConstraint × ℕ ↪ List Bool := encPair (encList encC) encUnary

theorem block_polytime (ℓ : ℕ) :
    ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ block ℓ x.1 x.2) encBlk
      (encList encC) := by
  have hcs : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ x.1) encBlk (encList encC) :=
    fst _ _
  have hj : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ x.2) encBlk encUnary := snd _ _
  have hjb : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ x.2) encBlk encNat :=
    toBin.comp hj
  have hget : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ x.1.getD x.2 dflt) encBlk
      encC := listGetDWithInput hcs hj dflt
  have hlv : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ lv x.1 x.2) encBlk encNat :=
    (fst _ _).comp ((fst _ _).comp hget)
  have htest : ComputableInPolyTime (fun p : (List UGConstraint × ℕ) × UGConstraint ↦
      decide (p.2.1.1 = lv p.1.1 p.1.2)) (encPair encBlk encC) encBool :=
    decide_eq' ((fst _ _).comp ((fst _ _).comp (snd _ _))) (hlv.comp (fst _ _))
  have hN : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ nbrs x.1 (lv x.1 x.2)) encBlk
      (encList encC) :=
    filterWithInput (list := fun x : List UGConstraint × ℕ ↦ x.1)
      (test := fun (x : List UGConstraint × ℕ) (c : UGConstraint) ↦ decide (c.1.1 = lv x.1 x.2))
      hcs htest
  have hd : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ (nbrs x.1 (lv x.1 x.2)).length)
      encBlk encUnary := (length_list encC).comp hN
  have hA : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦ ℓ * x.1.length) encBlk
      encUnary := unary_mul' (const ℓ) ((length_list encC).comp hcs)
  have hq : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦
      ℓ * x.1.length / (nbrs x.1 (lv x.1 x.2)).length) encBlk encUnary :=
    unary_div.comp (hA.prod hd)
  have hr : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦
      ℓ * x.1.length % (nbrs x.1 (lv x.1 x.2)).length) encBlk encUnary :=
    unary_mod.comp (hA.prod hd)
  have hf : ComputableInPolyTime (fun p : (List UGConstraint × ℕ) × UGConstraint ↦
      List.replicate (ℓ * p.1.1.length / (nbrs p.1.1 (lv p.1.1 p.1.2)).length)
        ((p.1.2, p.2.1.2), p.2.2)) (encPair encBlk encC) (encList encC) :=
    replicate (hq.comp (fst _ _))
      (((hjb.comp (fst _ _)).prod ((snd _ _).comp ((fst _ _).comp (snd _ _)))).prod
        ((snd _ _).comp (snd _ _)))
  have h1 : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦
      (nbrs x.1 (lv x.1 x.2)).flatMap fun c ↦
        List.replicate (ℓ * x.1.length / (nbrs x.1 (lv x.1 x.2)).length) ((x.2, c.1.2), c.2))
      encBlk (encList encC) :=
    flatMapWithInput (f := fun (x : List UGConstraint × ℕ) (c : UGConstraint) ↦
      List.replicate (ℓ * x.1.length / (nbrs x.1 (lv x.1 x.2)).length) ((x.2, c.1.2), c.2))
      hN hf
  have hh : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦
      (nbrs x.1 (lv x.1 x.2)).headD dflt) encBlk encC := (headD dflt).comp hN
  have h2 : ComputableInPolyTime (fun x : List UGConstraint × ℕ ↦
      List.replicate (ℓ * x.1.length % (nbrs x.1 (lv x.1 x.2)).length)
        ((x.2, ((nbrs x.1 (lv x.1 x.2)).headD dflt).1.2), ((nbrs x.1 (lv x.1 x.2)).headD dflt).2))
      encBlk (encList encC) :=
    replicate hr ((hjb.prod ((snd _ _).comp ((fst _ _).comp hh))).prod ((snd _ _).comp hh))
  exact listAppend' h1 h2

/-- **The regularization runs in polynomial time**, for a fixed `ℓ`. -/
theorem regularize_polytime (ℓ : ℕ) : ComputableInPolyTime (regularize ℓ) encUG encUG := by
  unfold regularize encUG
  have hcs : ComputableInPolyTime (fun G : UGInstance ↦ G.2.2.2)
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) (encList encC) :=
    (snd _ _).comp ((snd _ _).comp (snd _ _))
  have hlen : ComputableInPolyTime (fun G : UGInstance ↦ G.2.2.2.length)
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) encUnary :=
    (length_list encC).comp hcs
  have hrange : ComputableInPolyTime (fun G : UGInstance ↦ List.range G.2.2.2.length)
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) (encList encUnary) :=
    unary_range' hlen
  have hblk : ComputableInPolyTime (fun p : UGInstance × ℕ ↦ block ℓ p.1.2.2.2 p.2)
      (encPair (encPair encNat (encPair encNat (encPair encNat (encList encC)))) encUnary)
      (encList encC) :=
    (block_polytime ℓ).comp ((hcs.comp (fst _ _)).prod (snd _ _))
  have hL : ComputableInPolyTime (fun G : UGInstance ↦
      (List.range G.2.2.2.length).flatMap (block ℓ G.2.2.2))
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) (encList encC) :=
    flatMapWithInput (f := fun (G : UGInstance) (j : ℕ) ↦ block ℓ G.2.2.2 j) hrange hblk
  have hn : ComputableInPolyTime (fun G : UGInstance ↦ G.2.1)
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) encNat :=
    (fst _ _).comp (snd _ _)
  have hR : ComputableInPolyTime (fun G : UGInstance ↦ G.2.2.1)
      (encPair encNat (encPair encNat (encPair encNat (encList encC)))) encNat :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  exact (toBin.comp hlen).prod (hn.prod (hR.prod hL))

end BHSV25.UG
