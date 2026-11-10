module

public import BHSV25.Net.GSMachine
public import BHSV25.Net.PolyTime
public import BHSV25.Net.BallPolyTime
public import BHSV25.Time
public import Background.TuplesPolyTime
public import Background.PolyTime.Rat
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# The greedy net is computed in polynomial time

`BHSV25.Net.netGS_polytime`: the greedy net, as one machine reading the exponent `E`, the number
`T` of rounds, the resolution `N` and the budget `B` in unary together with the graph, runs in
polynomial time. Fixing the parameters (`BHSV25.runsInTime_graph_fix`) then gives running times
`g(E, T, N, B) · n^C` with `C` independent of them.

The loops are the matrix power (`E` multiplications, states `N × N` matrices with entries at most
`N^(2i)` after `i` steps, `BHSV25.Net.length_powL_le`), the search for the first maximizer
(states `none` or a vertex), the greedy rounds (states lists of at most `T` vertices) and the
tuples of the ball (cut at the budget, `BHSV25/Net/BallPolyTime.lean`). Everything else is a
fixed composition of polynomial-time pieces, among them complexitylib's determinant
`Cslib.Circuits.Rational.detRows`.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib (rowEntry tabulateTable)
open Cslib.Circuits.Rational (detRows detRows_polytime)
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

@[fun_prop]
theorem detRowsGS' {f : α → List (List ℤ)} (hf : ComputableInPolyTime f input encMat) :
    ComputableInPolyTime (fun a ↦ detRows (f a)) input encIntBin :=
  detRows_polytime.comp (g := f) hf

/-! ### The filter -/

theorem fst_le_length_encPair (y : ℕ × (ℕ × List Bool)) :
    y.1 ≤ (encPair encUnary encIn y).length := by
  simp
  omega

theorem snd_le_length_encPair (y : ℕ × (ℕ × List Bool)) :
    (encIn y.2).length ≤ (encPair encUnary encIn y).length := by
  simp

/-- The filter `Q = M^E`, for `E` read in unary. -/
theorem filtQ_polytime (bottom : Bool) : ComputableInPolyTime
    (fun y : ℕ × (ℕ × List Bool) ↦ filtQ bottom y.1 y.2) (encPair encUnary encIn) encMat := by
  have hx2 : ComputableInPolyTime (fun y : ℕ × (ℕ × List Bool) ↦ y.2)
      (encPair encUnary encIn) encIn := snd _ _
  have hN : ComputableInPolyTime (fun y : ℕ × (ℕ × List Bool) ↦ numV y.2)
      (encPair encUnary encIn) encUnary := numV_polytime.comp hx2
  have htab : ComputableInPolyTime (fun y : ℕ × (ℕ × List Bool) ↦ y.2.2)
      (encPair encUnary encIn) encBits := (snd encNat encBits).comp hx2
  have hdeg : ComputableInPolyTime (fun y : ℕ × (ℕ × List Bool) ↦ deg (numV y.2) y.2.2)
      (encPair encUnary encIn) encUnary := deg' hN htab
  have hM : ComputableInPolyTime
      (fun y : ℕ × (ℕ × List Bool) ↦ baseMat bottom (numV y.2) (deg (numV y.2) y.2.2) y.2.2)
      (encPair encUnary encIn) encMat := by
    have hg := (hN.prod hdeg).prod htab
    have := (baseMat_polytime bottom).comp hg
    exact this
  have hpar := hN.prod hM
  have hcount : ComputableInPolyTime (fun y : ℕ × (ℕ × List Bool) ↦ y.1)
      (encPair encUnary encIn) encUnary := fst _ _
  have hinit := idL_polytime.comp hN
  set size : ℕ × (ℕ × List Bool) → ℕ := fun y ↦ (encPair encUnary encIn y).length
  have hs : PolyBounded size size := .self
  have hG : PolyBounded size (fun y ↦ size y * (2 * (size y * (2 * (2 * size y * size y + 2) +
      1)) + 1)) :=
    hs.mul (((PolyBounded.const 2).mul (hs.mul (((PolyBounded.const 2).mul ((((PolyBounded.const
      2).mul hs).mul hs).add (.const 2))).add (.const 1)))).add (.const 1))
  have key := @iterateWith (ℕ × (ℕ × List Bool)) (List (List ℤ)) (ℕ × List (List ℤ))
    (encPair encUnary encIn) encMat (encPair encUnary encMat)
    (fun y ↦ (numV y.2, baseMat bottom (numV y.2) (deg (numV y.2) y.2.2) y.2.2))
    (fun y ↦ y.1) (fun y ↦ idL (numV y.2)) (fun q X ↦ mulL q.1 X q.2) hpar hcount hinit
    mulL_polytime
    (fun y ↦ numV y.2 * (2 * (numV y.2 * (2 * (2 * y.1 * numV y.2 + 2) + 1)) + 1))
    (hG.mono fun y ↦ by
      have h1 := (numV_le y.2).trans (snd_le_length_encPair y)
      have h2 := fst_le_length_encPair y
      simp only [size]
      gcongr)
    (fun y i hi ↦ by
      refine (length_powL_le (entBound_baseMat bottom y.2.2 (deg_le _ _)) i).trans ?_
      gcongr)
  exact key

/-! ### Tables and determinants -/

theorem gramRows_polytime : ComputableInPolyTime (fun p : ℕ × List (List ℤ) ↦ gramRows p.1 p.2)
    (encPair encUnary encMat) encMat := by
  unfold gramRows
  refine Cslib.computableInPolyTime_tabulateTable (fst _ _) (fst _ _) ?_
  refine intSum' (mapWithInput (by fun_prop) ?_)
  fun_prop

theorem subTable_polytime : ComputableInPolyTime (fun p : List (List ℤ) × List ℕ ↦
    subTable p.1 p.2) (encPair encMat encVs) encMat := by
  unfold subTable
  fun_prop

theorem scoreZ_polytime : ComputableInPolyTime
    (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ scoreZ p.1.1 p.1.2 p.2)
    (encPair (encPair encMat encVs) encUnary) encIntBin := by
  unfold scoreZ
  have := subTable_polytime
  fun_prop

/-! ### Small helpers -/

/-- The input of a step of the search: the table, the list, the state and the vertex. -/
abbrev encStepIn : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↪ List Bool :=
  encPair (encPair (encPair encMat encVs) (encOption encUnary)) encUnary

/-- The input of a greedy round: the number of vertices, the table and the list. -/
abbrev encRound : (ℕ × List (List ℤ)) × List ℕ ↪ List Bool :=
  encPair (encPair encUnary encMat) encVs

/-- The input of the selection: the number of vertices, the number of rounds and the table. -/
abbrev encSel : (ℕ × ℕ) × List (List ℤ) ↪ List Bool :=
  encPair (encPair encUnary encUnary) encMat

theorem someU' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ some (f a)) input (encOption encUnary) :=
  .of_tidy ((ComputableTidilyInPolyTime.optionSome encUnary).comp hf.tidy)

theorem ltZ' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ decide (f a < g a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_lt' hf.tidy hg.tidy)

theorem optElim' {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hv : ComputableInPolyTime value input (encOption encB))
    (hf : ComputableInPolyTime fallback input encC)
    (hb : ComputableInPolyTime (fun p : α × β ↦ body p.1 p.2) (encPair input encB) encC) :
    ComputableInPolyTime (fun a ↦ (value a).elim (fallback a) (body a)) input encC :=
  .of_tidy (ComputableTidilyInPolyTime.optionElimWithInput hv.tidy hf.tidy hb.tidy)

theorem takeU' {f : α → List ℕ} {g : α → ℕ} (hf : ComputableInPolyTime f input encVs)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ (f a).take (g a)) input encVs :=
  .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hf.tidy hg.tidy)

theorem appendOne' {f : α → List ℕ} {g : α → ℕ} (hf : ComputableInPolyTime f input encVs)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ++ [g a]) input encVs :=
  .of_tidy (ComputableTidilyInPolyTime.listAppend' hf.tidy
    (ComputableTidilyInPolyTime.cons' hg.tidy (ComputableTidilyInPolyTime.const [])))

/-! ### The search for the first maximizer -/

theorem argStep_eq {β : Type*} [LinearOrder β] [Zero β] (f : ℕ → β) (acc : Option ℕ) (v : ℕ) :
    argStep f acc v = acc.elim (if 0 < f v then some v else none)
      (fun u ↦ if f u < f v then some v else some u) := by
  cases acc <;> rfl

/-- One step of the search, with the scores of `(G, S)`. -/
theorem argStepZ_polytime : ComputableInPolyTime
    (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦
      argStep (scoreZ p.1.1.1 p.1.1.2) p.1.2 p.2)
    encStepIn (encOption encUnary) := by
  have hp1 : ComputableInPolyTime (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦ p.1)
      encStepIn (encPair (encPair encMat encVs) (encOption encUnary)) := fst _ _
  have hctx : ComputableInPolyTime (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦ p.1.1)
      encStepIn (encPair encMat encVs) := (fst _ _).comp hp1
  have hacc : ComputableInPolyTime (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦ p.1.2)
      encStepIn (encOption encUnary) := (snd _ _).comp hp1
  have hv : ComputableInPolyTime (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦ p.2)
      encStepIn encUnary := snd _ _
  have hsv0 := scoreZ_polytime.comp (hctx.prod hv)
  have hsv : ComputableInPolyTime (fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦
      scoreZ p.1.1.1 p.1.1.2 p.2) encStepIn encIntBin := hsv0
  have hlt0 := ltZ' (const (encIn := encStepIn) (encOut := encIntBin) (0 : ℤ)) hsv
  have hfb0 := ite_prop (p := fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦
    0 < scoreZ p.1.1.1 p.1.1.2 p.2) hlt0 (someU' hv) (const (encIn := encStepIn)
      (encOut := encOption encUnary) (none : Option ℕ))
  have hq1 : ComputableInPolyTime (fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
      q.1) (encPair encStepIn encUnary) encStepIn := fst _ _
  have hu : ComputableInPolyTime (fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
      q.2) (encPair encStepIn encUnary) encUnary := snd _ _
  have hsu0 := scoreZ_polytime.comp ((hctx.comp hq1).prod hu)
  have hsu : ComputableInPolyTime (fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
      scoreZ q.1.1.1.1 q.1.1.1.2 q.2) (encPair encStepIn encUnary) encIntBin := hsu0
  have hsv'0 := hsv.comp hq1
  have hsv' : ComputableInPolyTime (fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
      scoreZ q.1.1.1.1 q.1.1.1.2 q.1.2) (encPair encStepIn encUnary) encIntBin := hsv'0
  have hvq0 := hv.comp hq1
  have hvq : ComputableInPolyTime (fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
      q.1.2) (encPair encStepIn encUnary) encUnary := hvq0
  have hbody0 := ite_prop (p := fun q : (((List (List ℤ) × List ℕ) × Option ℕ) × ℕ) × ℕ ↦
    scoreZ q.1.1.1.1 q.1.1.1.2 q.2 < scoreZ q.1.1.1.1 q.1.1.1.2 q.1.2) (ltZ' hsu hsv')
    (someU' hvq) (someU' hu)
  have key := optElim' (value := fun p : ((List (List ℤ) × List ℕ) × Option ℕ) × ℕ ↦ p.1.2)
    (fallback := fun p ↦ if 0 < scoreZ p.1.1.1 p.1.1.2 p.2 then some p.2 else none)
    (body := fun p u ↦ if scoreZ p.1.1.1 p.1.1.2 u < scoreZ p.1.1.1 p.1.1.2 p.2 then some p.2
      else some u) hacc hfb0 hbody0
  simp only [argStep_eq]
  exact key

/-- The states of the search are `none` or a vertex below `i`. -/
theorem foldl_argStep_spec {β : Type*} [LinearOrder β] [Zero β] (f : ℕ → β) (N i : ℕ) :
    ∀ v, ((List.range N).take i).foldl (argStep f) none = some v → v < N := by
  intro v hv
  rw [List.take_range] at hv
  exact ((argmaxPos_some hv).1).trans_le (min_le_right _ _)

/-- **The first maximizer**, in polynomial time. -/
theorem argmaxPosZ_polytime : ComputableInPolyTime
    (fun q : (ℕ × List (List ℤ)) × List ℕ ↦ argmaxPos q.1.1 (scoreZ q.1.2 q.2))
    encRound (encOption encUnary) := by
  have hpar : ComputableInPolyTime (fun q : (ℕ × List (List ℤ)) × List ℕ ↦ (q.1.2, q.2)) encRound
      (encPair encMat encVs) := ((snd _ _).comp (fst _ _)).prod (snd _ _)
  have hlist : ComputableInPolyTime (fun q : (ℕ × List (List ℤ)) × List ℕ ↦ List.range q.1.1)
      encRound
      encVs := rangeU' ((fst _ _).comp (fst _ _))
  have hinit : ComputableInPolyTime (fun _ : (ℕ × List (List ℤ)) × List ℕ ↦ (none : Option ℕ))
      encRound (encOption encUnary) := const none
  set size : (ℕ × List (List ℤ)) × List ℕ → ℕ := fun q ↦ (encRound q).length
  have hB : PolyBounded size (fun q ↦ q.1.1 + 1) := by
    refine (PolyBounded.self.add (.const 1)).mono fun q ↦ ?_
    have : q.1.1 ≤ (encRound q).length := by simp [encRound]; omega
    simp only [size]
    omega
  have key := @foldlWith _ ℕ (Option ℕ) (List (List ℤ) × List ℕ) encRound encUnary
    (encOption encUnary)
    encVs (encPair encMat encVs) _ _ (fun q ↦ (q.1.2, q.2)) (fun q ↦ List.range q.1.1)
    (fun _ ↦ none) (fun par acc v ↦ argStep (scoreZ par.1 par.2) acc v) hpar hlist hinit
    argStepZ_polytime (fun q ↦ q.1.1 + 1) hB (fun q i _ ↦ by
      rcases h : ((List.range q.1.1).take i).foldl (argStep (scoreZ q.1.2 q.2)) none with _ | v
      · simp [encOption_none]
      · have := foldl_argStep_spec (scoreZ q.1.2 q.2) q.1.1 i v h
        simp only [encOption_some, List.length_cons, encUnary_apply, List.length_replicate]
        omega)
  exact key

/-! ### The greedy rounds -/

theorem greedyStep_eq {β : Type*} [LinearOrder β] [Zero β] (N : ℕ) (score : List ℕ → ℕ → β)
    (S : List ℕ) : greedyStep N score S = (argmaxPos N (score S)).elim S (fun v ↦ S ++ [v]) := by
  unfold greedyStep
  cases argmaxPos N (score S) <;> rfl

theorem greedyStepZ_polytime : ComputableInPolyTime
    (fun q : (ℕ × List (List ℤ)) × List ℕ ↦ greedyStep q.1.1 (scoreZ q.1.2) q.2)
    encRound encVs := by
  have hS : ComputableInPolyTime (fun q : (ℕ × List (List ℤ)) × List ℕ ↦ q.2) encRound encVs :=
    snd _ _
  have hbody : ComputableInPolyTime (fun p : ((ℕ × List (List ℤ)) × List ℕ) × ℕ ↦ p.1.2 ++ [p.2])
      (encPair encRound encUnary) encVs := appendOne' (hS.comp (fst _ _)) (snd _ _)
  have key := optElim' (value := fun q : (ℕ × List (List ℤ)) × List ℕ ↦
      argmaxPos q.1.1 (scoreZ q.1.2 q.2)) (fallback := fun q ↦ q.2)
    (body := fun q v ↦ q.2 ++ [v]) argmaxPosZ_polytime hS hbody
  simp only [greedyStep_eq]
  exact key

theorem mem_greedySeq_lt {β : Type*} [LinearOrder β] [Zero β] (N : ℕ)
    (score : List ℕ → ℕ → β) (t : ℕ) : ∀ s ∈ greedySeq N score t, s < N := by
  induction t with
  | zero => simp [greedySeq]
  | succ t ih =>
    rw [greedySeq_succ]
    rcases h : argmaxPos N (score (greedySeq N score t)) with _ | v
    · rw [greedyStep_of_none h]; exact ih
    · rw [greedyStep_of_some h]
      intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact ih s hs
      · rw [List.mem_singleton] at hs; exact hs ▸ (argmaxPos_some h).1

/-- **The greedy selection**, for `n` and `T` in unary, in polynomial time. -/
theorem selOf_polytime : ComputableInPolyTime
    (fun r : (ℕ × ℕ) × List (List ℤ) ↦ selOf r.1.1 r.1.2 r.2)
    encSel encVs := by
  have hpar : ComputableInPolyTime (fun r : (ℕ × ℕ) × List (List ℤ) ↦ (r.1.1, r.2)) encSel
      (encPair encUnary encMat) := ((fst _ _).comp (fst _ _)).prod (snd _ _)
  have hcount : ComputableInPolyTime (fun r : (ℕ × ℕ) × List (List ℤ) ↦ r.1.2) encSel encUnary :=
    (snd _ _).comp (fst _ _)
  have hinit : ComputableInPolyTime (fun _ : (ℕ × ℕ) × List (List ℤ) ↦ ([] : List ℕ)) encSel
      encVs :=
    const []
  have hB : PolyBounded (fun r ↦ (encSel r).length) (fun r ↦ r.1.2 * (2 * (r.1.1 + 1) + 1)) := by
    refine (PolyBounded.self.mul (((PolyBounded.const 2).mul (PolyBounded.self.add
      (.const 1))).add (.const 1))).mono fun r ↦ ?_
    have h1 : r.1.1 ≤ (encSel r).length := by simp [encSel]; omega
    have h2 : r.1.2 ≤ (encSel r).length := by simp [encSel]; omega
    gcongr
  have key := @iterateWith _ (List ℕ) (ℕ × List (List ℤ)) encSel encVs (encPair encUnary encMat)
    (fun r ↦ (r.1.1, r.2)) (fun r ↦ r.1.2) (fun _ ↦ []) (fun par S ↦ greedyStep par.1
      (scoreZ par.2) S) hpar hcount hinit greedyStepZ_polytime
    (fun r ↦ r.1.2 * (2 * (r.1.1 + 1) + 1)) hB (fun r i hi ↦ by
      change (encVs (greedySeq r.1.1 (scoreZ r.2) i)).length ≤ _
      refine (length_encList_le encUnary _ (b := r.1.1 + 1) fun s hs ↦ ?_).trans ?_
      · have := mem_greedySeq_lt r.1.1 (scoreZ r.2) i s hs
        simp only [encUnary_apply, List.length_replicate]
        omega
      · exact Nat.mul_le_mul_right _ ((length_greedySeq_le _ _ i).trans hi))
  unfold selOf greedySel greedySeq
  exact key

/-! ### The Gram–Schmidt data -/

/-- The input of the leading determinants: the table, the list and the index. -/
abbrev encLead : (List (List ℤ) × List ℕ) × ℕ ↪ List Bool := encPair (encPair encMat encVs) encUnary

theorem deltaZ_polytime : ComputableInPolyTime
    (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ deltaZ p.1.1 p.1.2 p.2) encLead encIntBin := by
  have hG : ComputableInPolyTime (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ p.1.1) encLead encMat :=
    (fst _ _).comp (fst _ _)
  have hS : ComputableInPolyTime (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ p.1.2) encLead encVs :=
    (snd _ _).comp (fst _ _)
  have hl : ComputableInPolyTime (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ p.2) encLead encUnary :=
    snd _ _
  have h1 := takeU' hS hl
  have h2 := subTable_polytime.comp (hG.prod h1)
  have h3 := detRowsGS' h2
  exact h3

theorem cramerTable_polytime : ComputableInPolyTime
    (fun p : ((List (List ℤ) × List ℕ) × ℕ) × ℕ ↦ cramerTable p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair encLead encUnary) encMat := by
  unfold cramerTable
  fun_prop

theorem gammaZ_polytime : ComputableInPolyTime
    (fun p : ((List (List ℤ) × List ℕ) × ℕ) × ℕ ↦ gammaZ p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair encLead encUnary) encIntBin := by
  have h := detRowsGS' cramerTable_polytime
  exact h

/-- The input of the Gram–Schmidt rows: the number of vertices, `Q`, `G`, the list and the
index. -/
abbrev encRow : (((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) × ℕ ↪ List Bool :=
  encPair (encPair (encPair (encPair encUnary encMat) encMat) encVs) encUnary

theorem rtZ_polytime : ComputableInPolyTime
    (fun p : (((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) × ℕ ↦
      rtZ p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) encRow (encList encIntBin) := by
  have hc : ComputableInPolyTime (fun p : (((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) × ℕ ↦
      p.1) encRow (encPair (encPair (encPair encUnary encMat) encMat) encVs) := fst _ _
  have hn := (fst _ _).comp ((fst _ _).comp ((fst _ _).comp hc))
  have hQ := (snd _ _).comp ((fst _ _).comp ((fst _ _).comp hc))
  have hG := (snd _ _).comp ((fst _ _).comp hc)
  have hS := (snd _ _).comp hc
  have hl : ComputableInPolyTime (fun p : (((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) × ℕ ↦
      p.2) encRow encUnary := snd _ _
  have hdelta0 := deltaZ_polytime.comp ((hG.prod hS).prod hl)
  unfold rtZ
  refine mapWithInput (rangeU' hn) ?_
  have hp1 := fst encRow encUnary
  have hu := snd encRow encUnary
  have hdelta := hdelta0.comp hp1
  have hsl := ComputableInPolyTime.listGetD (encA := encUnary) (encL := encVs) 0 |>.comp
    ((hS.comp hp1).prod (hl.comp hp1))
  have hQe := Cslib.computableInPolyTime_rowEntry (hQ.comp hp1) hsl hu
  have hprod := intBin_mul' hdelta hQe
  refine intSub' hprod (intSum' (mapWithInput (rangeU' (hl.comp hp1)) ?_))
  have hq1 := fst (encPair encRow encUnary) encUnary
  have hj := snd (encPair encRow encUnary) encUnary
  have hgam := gammaZ_polytime.comp ((((hG.comp hp1).comp hq1).prod ((hS.comp hp1).comp hq1)).prod
    ((hl.comp hp1).comp hq1) |>.prod hj)
  have hsj := ComputableInPolyTime.listGetD (encA := encUnary) (encL := encVs) 0 |>.comp
    (((hS.comp hp1).comp hq1).prod hj)
  have hQj := Cslib.computableInPolyTime_rowEntry ((hQ.comp hp1).comp hq1) hsj (hu.comp hq1)
  exact intBin_mul' hgam hQj

theorem sigmaZ_polytime : ComputableInPolyTime
    (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ sigmaZ p.1.1 p.1.2 p.2) encLead encNat := by
  have hl : ComputableInPolyTime (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ p.2) encLead encUnary :=
    snd _ _
  have hl1 : ComputableInPolyTime (fun p : (List (List ℤ) × List ℕ) × ℕ ↦ p.2 + 1) encLead
      encUnary := unary_add' hl (const 1)
  have h1 := deltaZ_polytime.comp ((fst _ _).prod hl1)
  have h2 := deltaZ_polytime
  have h3 := intBin_mul' h1 h2
  have h4 := intBin_toNat.comp h3
  have h5 := binary_sqrt' h4
  exact h5

/-- The input of the data: the number of vertices, `Q`, `G` and the list. -/
abbrev encDataIn : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ ↪ List Bool :=
  encPair (encPair (encPair encUnary encMat) encMat) encVs

/-- The data: the number of vertices, the rows `r̃_l` and the numbers `σ_l` in binary. -/
abbrev encData : ℕ × List (List ℤ) × List ℕ ↪ List Bool :=
  encPair encUnary (encPair encMat (encList encNat))

theorem dataOf_polytime : ComputableInPolyTime
    (fun p : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ ↦ dataOf p.1.1.1 p.1.1.2 p.1.2 p.2)
    encDataIn encData := by
  have hn := (fst encUnary encMat).comp ((fst _ _).comp
    (fst (encPair (encPair encUnary encMat) encMat) encVs))
  have hG : ComputableInPolyTime (fun p : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ ↦ p.1.2)
      encDataIn encMat := (snd _ _).comp (fst _ _)
  have hS : ComputableInPolyTime (fun p : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ ↦ p.2)
      encDataIn encVs := snd _ _
  have hlen := (length_list encUnary).comp hS
  have hrts := mapWithInput (f := fun (p : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) l ↦
    rtZ p.1.1.1 p.1.1.2 p.1.2 p.2 l) (rangeU' hlen) rtZ_polytime
  have hp1 := fst encDataIn encUnary
  have hl := snd encDataIn encUnary
  have hsig0 := sigmaZ_polytime.comp (((hG.comp hp1).prod (hS.comp hp1)).prod hl)
  have hsig := mapWithInput (f := fun (p : ((ℕ × List (List ℤ)) × List (List ℤ)) × List ℕ) l ↦
    sigmaZ p.1.2 p.2 l) (rangeU' hlen) hsig0
  have key := hn.prod (hrts.prod hsig)
  exact key

/-- The input of a candidate: the number of vertices, `N`, the data and the tuple. -/
abbrev encCandIn : ((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) (encPair encMat (encList encNat))) encVs

theorem candGS_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ ↦
      candGS p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) encCandIn (encList encRat) := by
  have hc := fst (encPair (encPair encUnary encUnary) (encPair encMat (encList encNat))) encVs
  have hn := (fst encUnary encUnary).comp ((fst _ _).comp hc)
  have hN := (snd encUnary encUnary).comp ((fst _ _).comp hc)
  have hrts := (fst encMat (encList encNat)).comp ((snd _ _).comp hc)
  have hsig := (snd encMat (encList encNat)).comp ((snd _ _).comp hc)
  have hms : ComputableInPolyTime (fun p : ((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ ↦ p.2)
      encCandIn encVs := snd _ _
  unfold candGS
  refine mapWithInput (rangeU' hn) (rat_sum' (mapWithInput (rangeU' ?_) ?_))
  · exact (length_list _).comp (hrts.comp (fst _ _))
  · set E2 := encPair (encPair encCandIn encUnary) encUnary
    have hq : ComputableInPolyTime (fun q : ((((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ) ×
        ℕ) × ℕ ↦ q.1.1) E2 encCandIn := (fst _ _).comp (fst _ _)
    have hu : ComputableInPolyTime (fun q : ((((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ) ×
        ℕ) × ℕ ↦ q.1.2) E2 encUnary := (snd _ _).comp (fst _ _)
    have hl : ComputableInPolyTime (fun q : ((((ℕ × ℕ) × (List (List ℤ) × List ℕ)) × List ℕ) ×
        ℕ) × ℕ ↦ q.2) E2 encUnary := snd _ _
    have hm := ComputableInPolyTime.listGetD (encA := encUnary) (encL := encVs) 0 |>.comp
      ((hms.comp hq).prod hl)
    have hsg := ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0 |>.comp
      ((hsig.comp hq).prod hl)
    have hr := Cslib.computableInPolyTime_rowEntry (hrts.comp hq) hl hu
    have hNq := toBinary' (hN.comp hq)
    have h1 := rat_sub' (rat_natCast' (toBinary' hm)) (rat_natCast' hNq)
    have h2 := rat_mul' (rat_natCast' hNq) (rat_natCast' hsg)
    have h3 := rat_mul' (rat_div' h1 h2) (rat_intCast' hr)
    exact h3

/-- The candidates of the data, for `N` and `B` in unary. -/
theorem candsOf_polytime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (ℕ × List (List ℤ) × List ℕ) ↦ candsOf p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encData) (encList (encList encRat)) := by
  set E := encPair (encPair encUnary encUnary) encData
  have hN : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × List (List ℤ) × List ℕ) ↦ p.1.1) E
      encUnary := (fst _ _).comp (fst _ _)
  have hB : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × List (List ℤ) × List ℕ) ↦ p.1.2) E
      encUnary := (snd _ _).comp (fst _ _)
  have hd : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × List (List ℤ) × List ℕ) ↦ p.2) E
      encData := snd _ _
  have hrts := (fst encMat (encList encNat)).comp ((snd _ _).comp hd)
  have hk := (length_list _).comp hrts
  have htup := ballTuples' hB hN hk
  unfold candsOf
  refine mapWithInput htup ?_
  have hp1 := fst E encVs
  have hms := snd E encVs
  have hctx := ((((fst _ _).comp (hd.comp hp1)).prod (hN.comp hp1)).prod
    ((snd _ _).comp (hd.comp hp1))).prod hms
  have key := candGS_polytime.comp hctx
  exact key

/-! ### The net -/

/-- The parameters of the net: `E`, `T`, `N` and `B`, in unary. -/
abbrev encGSPar : ℕ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encUnary))

/-- **The greedy net is computed in polynomial time**, reading its parameters `E`, `T`, `N`, `B`
in unary with the graph. -/
theorem netGS_polytime (bottom : Bool) : ComputableInPolyTime
    (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      netGS bottom z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2)
    (encPair encGSPar encIn) (encList (encList encRat)) := by
  set E := encPair encGSPar encIn
  have hpar : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.1) E encGSPar :=
    fst _ _
  have hx : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2) E encIn :=
    snd _ _
  have hE := (fst _ _).comp hpar
  have hT := (fst _ _).comp ((snd _ _).comp hpar)
  have hN := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hpar))
  have hB := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hpar))
  have hn := numV_polytime.comp hx
  have hQ := (filtQ_polytime bottom).comp (hE.prod hx)
  have hG := gramRows_polytime.comp (hn.prod hQ)
  have hS := selOf_polytime.comp ((hn.prod hT).prod hG)
  have hdata := dataOf_polytime.comp (((hn.prod hQ).prod hG).prod hS)
  have key := candsOf_polytime.comp ((hN.prod hB).prod hdata)
  exact key

end Net

end BHSV25
