module

public import BHJK25.RS.Decode.PolyTimeBase

/-!
# The per-guess decoder in polynomial time: interpolation

The interpolant `BHJK25.RS.DecodeAux.interp` is computed in polynomial time, with `m` and `W` in
unary (`BHJK25.RS.DecodeAux.PT.interp'`). The elimination folds `elimStep` over the rows; each step
keeps the family or replaces it by a fresh `K × K` matrix of reduced field elements
(`K = (W + 1)²`), so the family grows by a polynomial amount per row
(`BHJK25.RS.DecodeAux.PT.length_encM_elimStep`).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux.PT

open Turing.MultiTapeTM Cslib ComputableInPolyTime

/-! ### The size of an elimination step -/

/-- An elimination step keeps the family or replaces it by a `K × K` matrix of reduced field
elements, so it adds at most `K (2 K (6 r + 1) + 1)` to the encoding length, `r = fl.length`. -/
theorem length_encM_elimStep (fl : List ℕ) (K : ℕ) (N : List (List (List ℕ)))
    (a : List (List ℕ)) :
    (encM (elimStep fl K N a)).length ≤
      (encM N).length + K * (2 * (K * (2 * (fl.length * 3) + 1)) + 1) := by
  simp only [elimStep]
  split
  · omega
  · refine (length_encList_le _ _ (b := K * (2 * (fl.length * 3) + 1)) fun v hv ↦ ?_).trans ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
      refine (length_encList_le _ _ (b := fl.length * 3) fun e he ↦ ?_).trans ?_
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp he
        exact length_encE_fsub _ _ _
      · simp
    · simp only [List.length_map, List.length_range]
      omega

/-! ### Certificates -/

variable {α : Type} {input : α ↪ List Bool}

/-- The number `K = (W + 1)²` of columns, in unary. -/
private theorem sq' {W : α → ℕ} (hW : ComputableInPolyTime W input encUnary) :
    ComputableInPolyTime (fun x ↦ (W x + 1) * (W x + 1)) input encUnary :=
  unary_mul' (unary_add' hW (const 1)) (unary_add' hW (const 1))

/-- The test for allowed columns is polynomial-time. -/
@[fun_prop]
theorem low' {m W k : α → ℕ} (hm : ComputableInPolyTime m input encUnary)
    (hW : ComputableInPolyTime W input encUnary) (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun x ↦ low (m x) (W x) (k x)) input encBool := by
  have hW1 : ComputableInPolyTime (fun x ↦ W x + 1) input encUnary := unary_add' hW (const 1)
  exact unary_le' (unary_add' (unary_mod.comp (hk.prod hW1))
    (unary_mul' (unary_sub' hm (const 1)) (unary_div.comp (hk.prod hW1)))) hW

/-- The dot product is polynomial-time. -/
@[fun_prop]
theorem dot' {fl : α → List ℕ} {K : α → ℕ} {a v : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hK : ComputableInPolyTime K input encUnary)
    (ha : ComputableInPolyTime a input encV) (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ dot (fl x) (K x) (a x) (v x)) input encE := by
  unfold dot
  exact fsum' hfl (mapWithInput (range.comp hK) (fmul' (hfl.comp (fst _ _))
    (listGetDWithInput (ha.comp (fst _ _)) (snd _ _) [])
    (listGetDWithInput (hv.comp (fst _ _)) (snd _ _) [])))

/-- The initial family is polynomial-time. -/
@[fun_prop]
theorem initFam' {fl : α → List ℕ} {m W : α → ℕ}
    (hfl : ComputableInPolyTime fl input encE) (hm : ComputableInPolyTime m input encUnary)
    (hW : ComputableInPolyTime W input encUnary) :
    ComputableInPolyTime (fun x ↦ initFam (fl x) (m x) (W x)) input encM := by
  unfold initFam
  have hfl2 := hfl.comp ((fst _ _).comp (fst (encPair input encUnary) encUnary))
  have hdiag : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2 == p.2)
      (encPair (encPair input encUnary) encUnary) encBool :=
    ComputableInPolyTime.beq ((snd _ _).comp (fst _ _)) (snd _ _)
  exact mapWithInput (range.comp (sq' hW)) (mapWithInput (range.comp ((sq' hW).comp (fst _ _)))
    (ComputableInPolyTime.ite (bool_and' hdiag
      (low' (hm.comp ((fst _ _).comp (fst _ _))) (hW.comp ((fst _ _).comp (fst _ _))) (snd _ _)))
      (fone' hfl2) (fzero' hfl2)))

/-- The row values `bᵢ = a · Nᵢ` of an elimination step. -/
private theorem elimVals' {fl : α → List ℕ} {K : α → ℕ} {N : α → List (List (List ℕ))}
    {a : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hK : ComputableInPolyTime K input encUnary)
    (hN : ComputableInPolyTime N input encM) (ha : ComputableInPolyTime a input encV) :
    ComputableInPolyTime (fun x ↦ (List.range (K x)).map fun i ↦
      dot (fl x) (K x) (a x) ((N x).getD i [])) input encV :=
  mapWithInput (range.comp hK) (dot' (hfl.comp (fst _ _)) (hK.comp (fst _ _))
    (ha.comp (fst _ _)) (listGetDWithInput (hN.comp (fst _ _)) (snd _ _) []))

/-- The pivot of an elimination step: the first nonzero row value. -/
private theorem elimPivot' {fl : α → List ℕ} {K : α → ℕ} {bs : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hK : ComputableInPolyTime K input encUnary)
    (hbs : ComputableInPolyTime bs input encV) :
    ComputableInPolyTime (fun x ↦ ((List.range (K x)).find? fun i ↦
      !isZ (fl x) ((bs x).getD i [])).getD 0) input encUnary :=
  optionGetDWithInput (findWithInput (range.comp hK) (bool_not.comp
    (isZ' (hfl.comp (fst _ _)) (listGetDWithInput (hbs.comp (fst _ _)) (snd _ _) []))))
    (const 0)

/-- An elimination step is polynomial-time. -/
@[fun_prop]
theorem elimStep' {fl : α → List ℕ} {K : α → ℕ} {N : α → List (List (List ℕ))}
    {a : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hK : ComputableInPolyTime K input encUnary)
    (hN : ComputableInPolyTime N input encM) (ha : ComputableInPolyTime a input encV) :
    ComputableInPolyTime (fun x ↦ elimStep (fl x) (K x) (N x) (a x)) input encM := by
  have hbs := elimVals' hfl hK hN ha
  have hj := elimPivot' hfl hK hbs
  have hbj := listGetDWithInput hbs hj []
  have hfl2 := hfl.comp ((fst _ _).comp (fst (encPair input encUnary) encUnary))
  have hN2 := hN.comp ((fst _ _).comp (fst (encPair input encUnary) encUnary))
  unfold elimStep
  exact ComputableInPolyTime.ite (isZ' hfl hbj) hN (mapWithInput (range.comp hK)
    (mapWithInput (range.comp (hK.comp (fst _ _)))
      (fsub' hfl2 (fmul' hfl2 (hbj.comp ((fst _ _).comp (fst _ _)))
          (listGetDWithInput (listGetDWithInput hN2 ((snd _ _).comp (fst _ _)) []) (snd _ _) []))
        (fmul' hfl2 (listGetDWithInput (hbs.comp ((fst _ _).comp (fst _ _)))
            ((snd _ _).comp (fst _ _)) [])
          (listGetDWithInput (listGetDWithInput hN2 (hj.comp ((fst _ _).comp (fst _ _))) [])
            (snd _ _) [])))))

/-- The kernel vector is polynomial-time: the elimination is a fold whose state grows by
`length_encM_elimStep` per row, a polynomial in the input. -/
@[fun_prop]
theorem kernelVec' {fl : α → List ℕ} {K : α → ℕ} {N₀ : α → List (List (List ℕ))}
    {rows : α → List (List (List ℕ))}
    (hfl : ComputableInPolyTime fl input encE) (hK : ComputableInPolyTime K input encUnary)
    (hN₀ : ComputableInPolyTime N₀ input encM) (hrows : ComputableInPolyTime rows input encM) :
    ComputableInPolyTime (fun x ↦ kernelVec (fl x) (K x) (N₀ x) (rows x)) input encV := by
  have hKb : PolyBounded (fun x ↦ (input x).length) K :=
    hK.polyBounded_length.mono fun x ↦ by simp [encUnary_apply]
  have hgrowth : PolyBounded (fun x ↦ (input x).length)
      (fun x ↦ K x * (2 * (K x * (2 * ((fl x).length * 3) + 1)) + 1)) :=
    hKb.mul (((PolyBounded.const 2).mul (hKb.mul (((PolyBounded.const 2).mul
      (polyBounded_three_mul_length hfl)).add (.const 1)))).add (.const 1))
  have hfold : ComputableInPolyTime (fun x ↦ (rows x).foldl (elimStep (fl x) (K x)) (N₀ x))
      input encM :=
    foldlWithInput_of_bounded_growth (encA := encV) (encL := encM)
      (step := fun x N a ↦ elimStep (fl x) (K x) N a) hN₀
      ⟨hrows, elimStep' (hfl.comp ((fst _ _).comp (fst _ _))) (hK.comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _)) (snd _ _), inferInstance, inferInstance⟩
      ⟨hgrowth, fun x N a _ ↦ length_encM_elimStep (fl x) (K x) N a⟩
  have hfold2 := hfold.comp ((fst _ _).comp (fst (encPair input encUnary) encUnary))
  unfold kernelVec
  exact listGetDWithInput hfold (optionGetDWithInput (findWithInput (range.comp hK)
    (anyWithInput (range.comp (hK.comp (fst _ _))) (bool_not.comp (isZ'
      (hfl.comp ((fst _ _).comp (fst _ _)))
      (listGetDWithInput (listGetDWithInput hfold2 ((snd _ _).comp (fst _ _)) [])
        (snd _ _) []))))) (const 0)) []

/-- The row of a point is polynomial-time. -/
@[fun_prop]
theorem row' {fl : α → List ℕ} {W : α → ℕ} {xy : α → List ℕ × List ℕ}
    (hfl : ComputableInPolyTime fl input encE) (hW : ComputableInPolyTime W input encUnary)
    (hxy : ComputableInPolyTime xy input (encPair encE encE)) :
    ComputableInPolyTime (fun x ↦ row (fl x) (W x) (xy x)) input encV := by
  unfold row
  have hfl1 := hfl.comp (fst input encUnary)
  have hW1 : ComputableInPolyTime (fun p : α × ℕ ↦ W p.1 + 1) (encPair input encUnary)
      encUnary := unary_add' (hW.comp (fst _ _)) (const 1)
  exact mapWithInput (range.comp (sq' hW)) (fmul' hfl1
    (fpow' hfl1 ((fst _ _).comp (hxy.comp (fst _ _))) (unary_mod.comp ((snd _ _).prod hW1)))
    (fpow' hfl1 ((snd _ _).comp (hxy.comp (fst _ _))) (unary_div.comp ((snd _ _).prod hW1))))

/-- **The interpolant is computed in polynomial time.** -/
@[fun_prop]
theorem interp' {fl : α → List ℕ} {m W : α → ℕ} {pts : α → List (List ℕ × List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hm : ComputableInPolyTime m input encUnary)
    (hW : ComputableInPolyTime W input encUnary)
    (hpts : ComputableInPolyTime pts input (encList (encPair encE encE))) :
    ComputableInPolyTime (fun x ↦ interp (fl x) (m x) (W x) (pts x)) input encM := by
  have hrows : ComputableInPolyTime (fun x ↦ (pts x).map (row (fl x) (W x))) input encM :=
    mapWithInput hpts (row' (hfl.comp (fst _ _)) (hW.comp (fst _ _)) (snd _ _))
  have hc := kernelVec' hfl (sq' hW) (initFam' hfl hm hW) hrows
  have hW1 : ComputableInPolyTime (fun x ↦ W x + 1) input encUnary := unary_add' hW (const 1)
  have hW2 := hW1.comp ((fst _ _).comp (fst (encPair input encUnary) encUnary))
  unfold interp
  exact mapWithInput (range.comp hW1) (mapWithInput (range.comp (hW1.comp (fst _ _)))
    (listGetDWithInput (hc.comp ((fst _ _).comp (fst _ _)))
      (unary_add' (unary_mul' ((snd _ _).comp (fst _ _)) hW2) (snd _ _)) []))

end BHJK25.RS.DecodeAux.PT
