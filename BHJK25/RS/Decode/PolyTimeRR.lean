module

public import BHJK25.RS.Decode.PolyTimeBase

/-!
# The per-guess decoder in polynomial time: Roth–Ruckenstein and agreement

Given the interpolant in polynomial time, the decoder `BHJK25.RS.DecodeAux.decode` runs in
polynomial time, with `m` and `W` in unary (`BHJK25.RS.DecodeAux.PT.decode'`). Every node built by
`BHJK25.RS.DecodeAux.children` has a polynomial with `W + 1` rows of `L = (m + 1)(W + 1)`
reduced field elements (`stripL` reduces its entries) and at most `m` reduced coefficients, and a
level keeps at most `W + 1` nodes, so every frontier has a size bounded by a polynomial in the
input, whatever the previous frontier was.
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux.PT

open Turing.MultiTapeTM ComputableInPolyTime Cslib

variable {α : Type} {input : α ↪ List Bool}

/-! ### Sizes -/

/-- A `a × b` table of field elements of size at most `B` has size at most
`a (2 b (2 B + 1) + 1)`. -/
theorem length_encM_table_le {a b B : ℕ} (f : ℕ → ℕ → List ℕ)
    (hf : ∀ j i, (encE (f j i)).length ≤ B) :
    (encM ((List.range a).map fun j ↦ (List.range b).map fun i ↦ f j i)).length ≤
      a * (2 * (b * (2 * B + 1)) + 1) := by
  refine (length_encList_le encV _ (b := b * (2 * B + 1)) fun v hv ↦ ?_).trans (by simp)
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
  refine (length_encList_le encE _ (b := B) fun e he ↦ ?_).trans (by simp)
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
  exact hf j i

/-- The size bound `a (2 b (6 r + 1) + 1)` of an `a × b` table of reduced field elements is
polynomial in the input. -/
theorem polyBounded_table {fl : α → List ℕ} {a b : α → ℕ}
    (hfl : ComputableInPolyTime fl input encE) (ha : ComputableInPolyTime a input encUnary)
    (hb : ComputableInPolyTime b input encUnary) :
    PolyBounded (fun x ↦ (input x).length)
      (fun x ↦ a x * (2 * (b x * (2 * ((fl x).length * 3) + 1)) + 1)) :=
  ha.polyBounded.mul (((PolyBounded.const 2).mul (hb.polyBounded.mul
    (((PolyBounded.const 2).mul (polyBounded_three_mul_length hfl)).add (.const 1)))).add
      (.const 1))

/-- A step of Horner's rule builds a `BY × L` table of reduced field elements. -/
theorem length_encM_taylorStep (fl : List ℕ) (BY L : ℕ) (c : List ℕ)
    (acc : List (List (List ℕ))) (q : List (List ℕ)) :
    (encM (taylorStep fl BY L c acc q)).length ≤
      BY * (2 * (L * (2 * (fl.length * 3) + 1)) + 1) :=
  length_encM_table_le _ fun _ _ ↦ length_encE_fadd _ _ _

/-- `BHJK25.RS.DecodeAux.stripL` builds a `BY × L` table of reduced field elements. -/
theorem length_encM_stripL (fl : List ℕ) (BY L : ℕ) (Q : List (List (List ℕ))) :
    (encM (stripL fl BY L Q)).length ≤ BY * (2 * (L * (2 * (fl.length * 3) + 1)) + 1) := by
  dsimp only [stripL]
  exact length_encM_table_le _ fun _ _ ↦ by
    split
    · exact length_encE_fadd _ _ _
    · exact length_encE_fzero _

/-- A bound on the size of a node built by `BHJK25.RS.DecodeAux.children`: a `BY × L` table of
reduced field elements and at most `m` reduced coefficients. -/
def nodeSize (r m BY L : ℕ) : ℕ :=
  2 * (BY * (2 * (L * (2 * (r * 3) + 1)) + 1)) + 1 + m * (2 * (r * 3) + 1)

/-- Every child of a node has size at most `nodeSize`. -/
theorem length_child_le (fl : List ℕ) (elts : List (List ℕ)) (m BY L : ℕ)
    (nd : List (List (List ℕ)) × List (List ℕ)) :
    ∀ y ∈ children fl elts m BY L nd,
      (encPair encM encV y).length ≤ nodeSize fl.length m BY L := by
  intro y hy
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
  have h₁ := length_encM_stripL fl BY L (shiftL fl BY L (taylorL fl BY L nd.1 c))
  have h₂ : (encV (((nd.2 ++ [c]).map fun e ↦ fadd fl e (fzero fl)).take m)).length ≤
      m * (2 * (fl.length * 3) + 1) := by
    refine (length_encList_le encE _ (b := fl.length * 3) fun e he ↦ ?_).trans
      (Nat.mul_le_mul_right _ (List.length_take_le _ _))
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take he)
    exact length_encE_fadd _ _ _
  simp only [length_encPair, nodeSize]
  omega

/-- A level keeps at most `cap` nodes, each of size at most `nodeSize`. -/
theorem length_level_le (fl : List ℕ) (elts : List (List ℕ)) (m BY L cap : ℕ)
    (fr : List (List (List (List ℕ)) × List (List ℕ))) :
    (encList (encPair encM encV) (level fl elts m BY L cap fr)).length ≤
      cap * (2 * nodeSize fl.length m BY L + 1) := by
  unfold level
  refine (length_encList_le _ _ (b := nodeSize fl.length m BY L) fun y hy ↦ ?_).trans
    (Nat.mul_le_mul_right _ (List.length_take_le _ _))
  obtain ⟨nd, -, hy⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hy)
  exact length_child_le _ _ _ _ _ _ y hy

/-- The node size bound is polynomial in the input. -/
theorem polyBounded_nodeSize {fl : α → List ℕ} {m BY L : α → ℕ}
    (hfl : ComputableInPolyTime fl input encE) (hm : ComputableInPolyTime m input encUnary)
    (hBY : ComputableInPolyTime BY input encUnary) (hL : ComputableInPolyTime L input encUnary) :
    PolyBounded (fun x ↦ (input x).length) (fun x ↦ nodeSize (fl x).length (m x) (BY x) (L x)) :=
  (((PolyBounded.const 2).mul (polyBounded_table hfl hBY hL)).add (.const 1)).add
    (hm.polyBounded.mul
      (((PolyBounded.const 2).mul (polyBounded_three_mul_length hfl)).add (.const 1)))

/-! ### Lists -/

/-- Taking a computed unary number of entries of a computed list is polynomial-time. -/
theorem listTake' {β : Type} {encB : β ↪ List Bool} {l : α → List β} {n : α → ℕ}
    (hl : ComputableInPolyTime l input (encList encB))
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun x ↦ (l x).take (n x)) input (encList encB) :=
  .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hl.tidy hn.tidy)

/-! ### Roth–Ruckenstein -/

/-- Reading an entry of a matrix of field elements is polynomial-time. -/
theorem entry' {M : α → List (List (List ℕ))} {j i : α → ℕ}
    (hM : ComputableInPolyTime M input encM) (hj : ComputableInPolyTime j input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x ↦ ((M x).getD (j x) []).getD (i x) []) input encE :=
  listGetDWithInput (listGetDWithInput hM hj []) hi []

/-- `Q(0, c)` is polynomial-time. -/
theorem eval0' {fl c : α → List ℕ} {BY : α → ℕ} {Q : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hBY : ComputableInPolyTime BY input encUnary)
    (hQ : ComputableInPolyTime Q input encM) (hc : ComputableInPolyTime c input encE) :
    ComputableInPolyTime (fun x ↦ eval0 (fl x) (BY x) (Q x) (c x)) input encE := by
  unfold eval0
  exact fsum' hfl (mapWithInput (range.comp hBY)
    (fmul' (hfl.comp (fst _ _)) (entry' (hQ.comp (fst _ _)) (snd _ _) (const 0))
      (fpow' (hfl.comp (fst _ _)) (hc.comp (fst _ _)) (snd _ _))))

/-- One step of Horner's rule for the Taylor shift is polynomial-time. -/
theorem taylorStep' {fl c : α → List ℕ} {BY L : α → ℕ} {acc : α → List (List (List ℕ))}
    {q : α → List (List ℕ)} (hfl : ComputableInPolyTime fl input encE)
    (hBY : ComputableInPolyTime BY input encUnary) (hL : ComputableInPolyTime L input encUnary)
    (hc : ComputableInPolyTime c input encE) (hacc : ComputableInPolyTime acc input encM)
    (hq : ComputableInPolyTime q input encV) :
    ComputableInPolyTime (fun x ↦ taylorStep (fl x) (BY x) (L x) (c x) (acc x) (q x)) input
      encM := by
  unfold taylorStep
  have hx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).fst'
  have hj : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (fst _ _).snd'
  have hi := snd (encPair input encUnary) encUnary
  have hA := hacc.comp hx
  exact mapWithInput (range.comp hBY) (mapWithInput (range.comp (hL.comp (fst _ _)))
    (fadd' (hfl.comp hx) (fmul' (hfl.comp hx) (hc.comp hx) (entry' hA hj hi))
      (ComputableInPolyTime.ite_decide (decide_eq' hj (const 0))
        (listGetDWithInput (hq.comp hx) hi []) (entry' hA (unary_sub' hj (const 1)) hi))))

/-- The Taylor shift is polynomial-time: each step of Horner's rule builds a fresh table of
reduced field elements. -/
theorem taylorL' {fl c : α → List ℕ} {BY L : α → ℕ} {Q : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary) (hQ : ComputableInPolyTime Q input encM)
    (hc : ComputableInPolyTime c input encE) :
    ComputableInPolyTime (fun x ↦ taylorL (fl x) (BY x) (L x) (Q x) (c x)) input encM := by
  unfold taylorL
  have hx : ComputableInPolyTime (fun p : (α × List (List (List ℕ))) × ℕ ↦ p.1.1)
      (encPair (encPair input encM) encUnary) input := (fst _ _).fst'
  have hstep : ComputableInPolyTime (fun p : (α × List (List (List ℕ))) × ℕ ↦
      taylorStep (fl p.1.1) (BY p.1.1) (L p.1.1) (c p.1.1) p.1.2 ((Q p.1.1).getD p.2 []))
      (encPair (encPair input encM) encUnary) encM :=
    taylorStep' (hfl.comp hx) (hBY.comp hx) (hL.comp hx) (hc.comp hx) (fst _ _).snd'
      (listGetDWithInput (hQ.comp hx) (snd _ _) [])
  exact foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (step := fun x acc b ↦ taylorStep (fl x) (BY x) (L x) (c x) acc ((Q x).getD b []))
    (const []) ⟨listReverseWithInput (range.comp hBY), hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_table hfl hBY hL, fun x _ _ _ ↦
      (length_encM_taylorStep _ _ _ _ _ _).trans (Nat.le_add_left _ _)⟩

/-- `H(X, X Y)` is polynomial-time. -/
theorem shiftL' {fl : α → List ℕ} {BY L : α → ℕ} {H : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary) (hH : ComputableInPolyTime H input encM) :
    ComputableInPolyTime (fun x ↦ shiftL (fl x) (BY x) (L x) (H x)) input encM := by
  unfold shiftL
  have hx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).fst'
  have hj : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (fst _ _).snd'
  have hi := snd (encPair input encUnary) encUnary
  exact mapWithInput (range.comp hBY) (mapWithInput (range.comp (hL.comp (fst _ _)))
    (ComputableInPolyTime.ite_decide (unary_le' hj hi) (entry' (hH.comp hx) hj (unary_sub' hi hj))
      (fzero' (hfl.comp hx))))

/-- The `X`-valuation used by `BHJK25.RS.DecodeAux.stripL` is polynomial-time. -/
theorem stripShift' {fl : α → List ℕ} {BY L : α → ℕ} {Q : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary) (hQ : ComputableInPolyTime Q input encM) :
    ComputableInPolyTime (fun x ↦ ((List.range (L x)).find? fun i ↦
      (List.range (BY x)).any fun j ↦ !isZ (fl x) (((Q x).getD j []).getD i [])).getD 0)
      input encUnary := by
  have hx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).fst'
  have hi : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (fst _ _).snd'
  exact optionGetDWithInput (findWithInput (range.comp hL)
    (anyWithInput (range.comp (hBY.comp (fst _ _)))
      (bool_not.comp (isZ' (hfl.comp hx) (entry' (hQ.comp hx) (snd _ _) hi))))) (const 0)

/-- Dividing by the largest power of `X` is polynomial-time. -/
theorem stripL' {fl : α → List ℕ} {BY L : α → ℕ} {Q : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary) (hQ : ComputableInPolyTime Q input encM) :
    ComputableInPolyTime (fun x ↦ stripL (fl x) (BY x) (L x) (Q x)) input encM := by
  dsimp only [stripL]
  have hx : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).fst'
  have hj : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (fst _ _).snd'
  have hi := snd (encPair input encUnary) encUnary
  have hv := unary_add' hi ((stripShift' hfl hBY hL hQ).comp hx)
  exact mapWithInput (range.comp hBY) (mapWithInput (range.comp (hL.comp (fst _ _)))
    (ComputableInPolyTime.ite_decide (unary_lt' hv (hL.comp hx))
      (fadd' (hfl.comp hx) (entry' (hQ.comp hx) hj hv) (fzero' (hfl.comp hx)))
      (fzero' (hfl.comp hx))))

/-- The children of a node are polynomial-time. -/
theorem children' {fl : α → List ℕ} {elts : α → List (List ℕ)} {m BY L : α → ℕ}
    {nd : α → List (List (List ℕ)) × List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (helts : ComputableInPolyTime elts input encV)
    (hm : ComputableInPolyTime m input encUnary) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary)
    (hnd : ComputableInPolyTime nd input (encPair encM encV)) :
    ComputableInPolyTime (fun x ↦ children (fl x) (elts x) (m x) (BY x) (L x) (nd x)) input
      (encList (encPair encM encV)) := by
  unfold children
  have hx := fst input encE
  have hc := snd input encE
  have hF := hfl.comp hx
  have hB := hBY.comp hx
  have hL' := hL.comp hx
  have hN := hnd.comp hx
  exact mapWithInput (filterWithInput helts (isZ' hF (eval0' hF hB hN.fst' hc)))
    ((stripL' hF hB hL' (shiftL' hF hB hL' (taylorL' hF hB hL' hN.fst' hc))).prod
      (listTake' (mapWithInput (listAppend' hN.snd' (cons' hc (const [])))
        (fadd' (hF.comp (fst _ _)) (snd _ _) (fzero' (hF.comp (fst _ _))))) (hm.comp hx)))

/-- A level of Roth–Ruckenstein is polynomial-time. -/
theorem level' {fl : α → List ℕ} {elts : α → List (List ℕ)} {m BY L cap : α → ℕ}
    {fr : α → List (List (List (List ℕ)) × List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (helts : ComputableInPolyTime elts input encV)
    (hm : ComputableInPolyTime m input encUnary) (hBY : ComputableInPolyTime BY input encUnary)
    (hL : ComputableInPolyTime L input encUnary) (hcap : ComputableInPolyTime cap input encUnary)
    (hfr : ComputableInPolyTime fr input (encList (encPair encM encV))) :
    ComputableInPolyTime (fun x ↦ level (fl x) (elts x) (m x) (BY x) (L x) (cap x) (fr x)) input
      (encList (encPair encM encV)) := by
  unfold level
  have hx := fst input (encPair encM encV)
  exact listTake' (flatMapWithInput hfr (children' (hfl.comp hx) (helts.comp hx) (hm.comp hx)
    (hBY.comp hx) (hL.comp hx) (snd _ _))) hcap

/-- **Roth–Ruckenstein is polynomial-time**: every level has at most `W + 1` nodes of size at
most `nodeSize`, whatever the previous frontier. -/
theorem rrRoots' {fl : α → List ℕ} {elts : α → List (List ℕ)} {m W : α → ℕ}
    {Q : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (helts : ComputableInPolyTime elts input encV)
    (hm : ComputableInPolyTime m input encUnary) (hW : ComputableInPolyTime W input encUnary)
    (hQ : ComputableInPolyTime Q input encM) :
    ComputableInPolyTime (fun x ↦ rrRoots (fl x) (elts x) (m x) (W x) (Q x)) input encM := by
  unfold rrRoots
  have hW1 : ComputableInPolyTime (fun x ↦ W x + 1) input encUnary := unary_add' hW (const 1)
  have hL : ComputableInPolyTime (fun x ↦ (m x + 1) * (W x + 1)) input encUnary :=
    unary_mul' (unary_add' hm (const 1)) hW1
  have hx : ComputableInPolyTime (fun p : (α × List (List (List (List ℕ)) × List (List ℕ))) × ℕ ↦
      p.1.1) (encPair (encPair input (encList (encPair encM encV))) encUnary) input :=
    (fst _ _).fst'
  have hstep := level' (hfl.comp hx) (helts.comp hx) (hm.comp hx) (hW1.comp hx) (hL.comp hx)
    (hW1.comp hx) (fst _ _).snd'
  have hfold := foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (encB := encList (encPair encM encV))
    (step := fun x fr _ ↦ level (fl x) (elts x) (m x) (W x + 1) ((m x + 1) * (W x + 1))
      (W x + 1) fr)
    (cons' ((stripL' hfl hW1 hL hQ).prod (const [])) (const []))
    ⟨range.comp hm, hstep, inferInstance, inferInstance⟩
    ⟨hW1.polyBounded.mul (((PolyBounded.const 2).mul
      (polyBounded_nodeSize hfl hm hW1 hL)).add (.const 1)), fun x _ _ _ ↦
      (length_level_le _ _ _ _ _ _ _).trans (Nat.le_add_left _ _)⟩
  exact (ComputableInPolyTime.map (snd encM encV)).comp hfold

/-! ### Agreement -/

/-- Evaluating a polynomial is polynomial-time. -/
theorem evalPoly' {fl y : α → List ℕ} {p : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hp : ComputableInPolyTime p input encV)
    (hy : ComputableInPolyTime y input encE) :
    ComputableInPolyTime (fun x ↦ evalPoly (fl x) (p x) (y x)) input encE := by
  unfold evalPoly
  have hx := fst input encUnary
  exact fsum' hfl (mapWithInput (range.comp ((length_list encE).comp hp))
    (fmul' (hfl.comp hx) (listGetDWithInput (hp.comp hx) (snd _ _) [])
      (fpow' (hfl.comp hx) (hy.comp hx) (snd _ _))))

/-- The agreement of a polynomial with the points is polynomial-time. -/
theorem agree' {fl : α → List ℕ} {pts : α → List (List ℕ × List ℕ)} {p : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE)
    (hpts : ComputableInPolyTime pts input (encList (encPair encE encE)))
    (hp : ComputableInPolyTime p input encV) :
    ComputableInPolyTime (fun x ↦ agree (fl x) (pts x) (p x)) input encUnary := by
  unfold agree
  have hx := fst input (encPair encE encE)
  have hxy := snd input (encPair encE encE)
  exact (length_list encE).comp (eraseDupsByWithInput
    (mapWithInput (filterWithInput hpts (isZ' (hfl.comp hx)
      (fsub' (hfl.comp hx) (evalPoly' (hfl.comp hx) (hp.comp hx) hxy.fst') hxy.snd')))
      (snd _ _).fst')
    (decide_eq' (fst _ _).snd' (snd _ _)))

/-- **The decoder runs in polynomial time**, given the interpolant in polynomial time. -/
theorem decode' {fl : α → List ℕ} {elts : α → List (List ℕ)} {m W : α → ℕ}
    {pts : α → List (List ℕ × List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (helts : ComputableInPolyTime elts input encV)
    (hm : ComputableInPolyTime m input encUnary) (hW : ComputableInPolyTime W input encUnary)
    (hpts : ComputableInPolyTime pts input (encList (encPair encE encE)))
    (hQ : ComputableInPolyTime (fun x ↦ interp (fl x) (m x) (W x) (pts x)) input encM) :
    ComputableInPolyTime (fun x ↦ decode (fl x) (elts x) (m x) (W x) (pts x)) input encBool := by
  unfold decode
  have hx := fst input encV
  exact anyWithInput (rrRoots' hfl helts hm hW hQ)
    (unary_le' (unary_add' (hW.comp hx) (const 1)) (agree' (hfl.comp hx) (hpts.comp hx) (snd _ _)))

end BHJK25.RS.DecodeAux.PT
