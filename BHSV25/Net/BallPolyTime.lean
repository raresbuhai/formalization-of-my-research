module

public import BHSV25.Net.Ball
public import BHSV25.Net.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-!
# The tuples of the ball in polynomial time

The certificate of `BHSV25.Net.ballTuples` (`BHSV25.Net.ballTuples_polytime`), with the budget
`L`, the radius `N` and the length `T` in unary, as for `Tuples.tuples_unary_polytime`: one step
extends every tuple by every value below `2N + 1`, keeps those in the ball (a test on rational
numbers) and the first `L`; the states have at most `L + 1` tuples of at most `T` entries below
`2N + 1`.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Turing.MultiTapeTM ComputableInPolyTime Tuples
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- The test of the ball. -/
theorem inBall' {N : α → ℕ} {q : α → List ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hq : ComputableInPolyTime q input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ inBall (N a) (q a)) input encBool := by
  unfold inBall offSq
  have hm : ComputableInPolyTime (fun p : α × ℕ ↦ ((p.2 : ℚ) - N p.1) ^ 2)
      (encPair input encUnary) encRat :=
    rat_sq' (rat_sub' (rat_natCast' (toBinary' (snd _ _)))
      (rat_natCast' (toBinary' (hN.comp (fst _ _)))))
  have hmap := mapWithInput (f := fun a (m : ℕ) ↦ ((m : ℚ) - N a) ^ 2) hq hm
  exact rat_le' (rat_sum' hmap) (rat_sq' (rat_natCast' (toBinary' hN)))

/-- The input of one step: `L` and `N` in unary, with the tuples. -/
abbrev encBallIn : (ℕ × ℕ) × List (List ℕ) ↪ List Bool :=
  encPair (encPair encUnary encUnary) (encList encVs)

theorem ballStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (List ℕ) ↦ ballStep p.1.1 p.1.2 p.2) encBallIn (encList encVs) := by
  unfold ballStep tupleStepFull
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℕ) ↦
      p.2.flatMap fun q ↦ (List.range (2 * p.1.2 + 1)).map (· :: q)) encBallIn (encList encVs) :=
    flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  have hN : ComputableInPolyTime (fun z : ((ℕ × ℕ) × List (List ℕ)) × List ℕ ↦ z.1.1.2)
      (encPair encBallIn encVs) encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hb : ComputableInPolyTime (fun z : ((ℕ × ℕ) × List (List ℕ)) × List ℕ ↦ inBall z.1.1.2 z.2)
      (encPair encBallIn encVs) encBool := inBall' hN (snd _ _)
  have hf := filterWithInput (test := fun (p : (ℕ × ℕ) × List (List ℕ)) q ↦ inBall p.1.2 q) h hb
  fun_prop

/-- **The tuples of the ball are polynomial-time**, with `L`, `N` and `T` in unary. -/
theorem ballTuples_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℕ ↦ ballTuples x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList encVs) := by
  unfold ballTuples
  refine iterateWith (par := fun x : ℕ × ℕ × ℕ ↦ (x.1, x.2.1)) (count := fun x ↦ x.2.2)
    (init := fun _ ↦ [[]]) (step := fun p l ↦ ballStep p.1 p.2 l) (by fun_prop) (by fun_prop)
    (by fun_prop) ballStep_polytime
    (bound := fun x ↦ (x.1 + 1) * (2 * (x.2.2 * (2 * (2 * x.2.1 + 1) + 1)) + 1)) ?_ ?_
  · refine PolyBounded.of_forall_le 25 3 fun x ↦ ?_
    set s := (encPair encUnary (encPair encUnary encUnary) x).length
    have hs : x.1 + x.2.1 + x.2.2 ≤ s := by
      simp only [s, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have h1 : x.1 + 1 ≤ s + 1 := by omega
    have h2 : x.2.2 ≤ s + 1 := by omega
    have h3 : 2 * (2 * x.2.1 + 1) + 1 ≤ 4 * (s + 1) := by omega
    calc (x.1 + 1) * (2 * (x.2.2 * (2 * (2 * x.2.1 + 1) + 1)) + 1)
        ≤ (s + 1) * (2 * ((s + 1) * (4 * (s + 1))) + 1 * (s + 1) * (s + 1)) := by
          gcongr
          nlinarith
      _ = 9 * (s + 1) ^ 3 := by ring
      _ ≤ 25 * (s + 1) ^ 3 := by gcongr; norm_num
  · intro x i hi
    obtain ⟨hsmall, hlen⟩ := ballTuples_iter_small x.1 x.2.1 i
    have helem : ∀ q ∈ (ballStep x.1 x.2.1)^[i] [[]], (encVs q).length ≤
        x.2.2 * (2 * (2 * x.2.1 + 1) + 1) := by
      intro q hq
      obtain ⟨h1, h2⟩ := hsmall q hq
      refine (length_encList_le encUnary q (b := 2 * x.2.1 + 1) fun a ha ↦ ?_).trans
        (Nat.mul_le_mul_right _ (h1.trans hi))
      simpa [encUnary_apply] using (h2 a ha).le
    calc (encList encVs ((ballStep x.1 x.2.1)^[i] [[]])).length
        ≤ ((ballStep x.1 x.2.1)^[i] [[]]).length *
            (2 * (x.2.2 * (2 * (2 * x.2.1 + 1) + 1)) + 1) :=
          length_encList_le _ _ helem
      _ ≤ (x.1 + 1) * (2 * (x.2.2 * (2 * (2 * x.2.1 + 1) + 1)) + 1) :=
          Nat.mul_le_mul_right _ hlen

theorem ballTuples' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ ballTuples (f a) (g a) (h a)) input (encList encVs) :=
  ballTuples_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

end Net

end BHSV25
