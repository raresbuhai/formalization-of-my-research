module

public import BCFGJPSSV26.Greedy.PolyTime.AuxCtx

/-!
# Polynomial time of the core: completion and bisection

Certificates for `BCFGJPSSV26.Greedy.Ctx.firstOpen`, `Ctx.seqStep`, `Ctx.completeSeq` (an
iteration that adds at most one atom per step), `Ctx.complete` (a fold that adds at most one
sequence of at most `L` atoms per step), `Ctx.sol`, `Ctx.cnt`, the binary searches
(`BCFGJPSSV26.Greedy.Ctx.searchStep`, whose state stays below its initial upper end) and
`Ctx.bisect`. Pairs and results of the merge are encoded as tuples
(`BCFGJPSSV26.Greedy.PT.encPr`, `BCFGJPSSV26.Greedy.PT.encRs`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Structure of the completion -/

theorem seqStep_cases (C : Ctx) (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    C.seqStep b f θ pre cur = cur ∨ ∃ i < C.ip.m, C.seqStep b f θ pre cur = cur ++ [(i, 0)] := by
  unfold Ctx.seqStep
  split
  · rename_i i h
    right
    refine ⟨i, ?_, rfl⟩
    exact List.mem_range.1 (List.mem_of_find?_eq_some h)
  · left; rfl

theorem iterate_seqStep (C : Ctx) (b : Bool) (f θ : ℚ) (pre cur : List AAtom) (t : ℕ) :
    ∃ new, (C.seqStep b f θ pre)^[t] cur = cur ++ new ∧ new.length ≤ t ∧
      ∀ a ∈ new, a.1 < C.ip.m ∧ a.2 = 0 := by
  induction t with
  | zero => exact ⟨[], by simp, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨new, hnew, hlen, hat⟩ := ih
    rw [Function.iterate_succ_apply', hnew]
    rcases seqStep_cases C b f θ pre (cur ++ new) with h | ⟨i, hi, h⟩
    · exact ⟨new, h, by omega, hat⟩
    · refine ⟨new ++ [(i, 0)], by rw [h, List.append_assoc], by simp; omega, ?_⟩
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hat a ha
      · rw [List.mem_singleton.1 ha]; exact ⟨hi, rfl⟩

/-- **CompleteSequence adds at most `L` regular atoms**, of facilities below `m`. -/
theorem completeSeq_eq (C : Ctx) (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    ∃ new, C.completeSeq b f θ pre cur = cur ++ new ∧ new.length ≤ C.ip.L ∧
      ∀ a ∈ new, a.1 < C.ip.m ∧ a.2 = 0 :=
  iterate_seqStep C b f θ pre cur C.ip.L

/-- A fresh sequence: at most `L` regular atoms of facilities below `m`. -/
def Fresh (C : Ctx) (S : List AAtom) : Prop := S.length ≤ C.ip.L ∧ ∀ a ∈ S, a.1 < C.ip.m ∧ a.2 = 0

theorem fresh_completeSeq (C : Ctx) (b : Bool) (f θ : ℚ) (pre : List AAtom) :
    Fresh C (C.completeSeq b f θ pre []) := by
  obtain ⟨new, h, hl, ha⟩ := completeSeq_eq C b f θ pre []
  rw [h, List.nil_append]
  exact ⟨hl, ha⟩

theorem foldl_complete (C : Ctx) (f : ℚ) (l : List ℕ) (hl : ∀ p ∈ l, p < 2 * C.ip.R)
    (H : List (List AAtom)) :
    ∃ T, l.foldl (fun H p ↦ if H.length = p then
        H ++ [C.completeSeq (typ1 p) f (C.θseq p) H.flatten []] else H) H = H ++ T ∧
      (H ++ T).length ≤ max H.length (2 * C.ip.R) ∧ ∀ S ∈ T, Fresh C S := by
  induction l generalizing H with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | cons p l ih =>
    rw [List.foldl_cons]
    split_ifs with hp
    · obtain ⟨T, hT, hlen, hS⟩ := ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)) _
      refine ⟨_ :: T, by rw [hT, List.append_assoc, List.singleton_append], ?_, ?_⟩
      · have := hl p (List.mem_cons_self ..)
        simp only [List.length_append, List.length_singleton] at hlen ⊢
        simp only [List.length_cons]
        omega
      · intro S hS'
        rcases List.mem_cons.1 hS' with rfl | hS'
        · exact fresh_completeSeq ..
        · exact hS S hS'
    · exact ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)) H

/-- **The completion appends fresh sequences**, up to `2R` sequences. -/
theorem complete_eq (C : Ctx) (f : ℚ) (H : List (List AAtom)) :
    ∃ T, C.complete f H = H ++ T ∧ (H ++ T).length ≤ max H.length (2 * C.ip.R) ∧
      ∀ S ∈ T, Fresh C S :=
  foldl_complete C f _ (fun _ hp ↦ List.mem_range.1 hp) H

/-! ### Encoded lengths of atoms -/

theorem len_encAt (a : AAtom) :
    (encAt a).length = 2 * (encNat a.1).length + 1 + (encNat a.2).length :=
  length_encPair a

theorem len_encAt_reg {m : ℕ} {a : AAtom} (h : a.1 < m ∧ a.2 = 0) :
    (encAt a).length ≤ 2 * m + 1 := by
  rw [len_encAt, h.2]
  have := len_encNat_le_self a.1
  have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
  omega

theorem len_fresh_le (C : Ctx) {S : List AAtom} (h : Fresh C S) :
    (encSq S).length ≤ C.ip.L * (2 * (2 * C.ip.m + 1) + 1) :=
  len_encList_le_of encAt h.1 fun a ha ↦ len_encAt_reg (h.2 a ha)

variable {α : Type} {input : α ↪ List Bool} (c : Consts) {X : α → CoreIn}

/-! ### Certificates of the completion -/

theorem firstOpenO {b : α → Bool} {f θ : α → ℚ} {S : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hS : ComputableInPolyTime S input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).firstOpen (b a) (f a) (θ a) (S a)) input
      (encOption encUnary) :=
  findWithInput (unary_range' (mU c hX))
    (testTQ c (hX.comp (fst _ _)) (hb.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
      (profL c (hX.comp (fst _ _)) (hS.comp (fst _ _))) (toBin (snd _ _)))

theorem seqStep_eq (C : Ctx) (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    C.seqStep b f θ pre cur =
      (C.firstOpen b f θ (pre ++ cur)).elim cur fun i ↦ cur ++ [(i, 0)] := by
  unfold Ctx.seqStep
  split <;> rename_i h <;> rw [h] <;> rfl

theorem seqStepS {b : α → Bool} {f θ : α → ℚ} {pre cur : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hpre : ComputableInPolyTime pre input encSq) (hcur : ComputableInPolyTime cur input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).seqStep (b a) (f a) (θ a) (pre a) (cur a)) input
      encSq := by
  simp only [seqStep_eq]
  exact optionElimWithInput (firstOpenO c hX hb hf hθ (listAppend' hpre hcur)) hcur
    (listAppend' (hcur.comp (fst _ _)) (cons' ((toBin (snd _ _)).prod (const 0)) (const [])))

theorem len_seqStep_le (C : Ctx) (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    (encSq (C.seqStep b f θ pre cur)).length ≤ (encSq cur).length + (4 * C.ip.m + 3) := by
  dsimp only [encSq]
  rcases seqStep_cases C b f θ pre cur with h | ⟨i, hi, h⟩
  · rw [h]; omega
  · rw [h, len_encList_append]
    have := len_encAt_reg (m := C.ip.m) (a := (i, 0)) ⟨hi, rfl⟩
    simp only [encList_cons, encList_nil, List.append_nil, length_frame]
    omega

theorem completeSeqS {b : α → Bool} {f θ : α → ℚ} {pre cur : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hpre : ComputableInPolyTime pre input encSq) (hcur : ComputableInPolyTime cur input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).completeSeq (b a) (f a) (θ a) (pre a) (cur a))
      input encSq := by
  unfold Ctx.completeSeq
  refine iterateWithInput_of_bounded_growth (LU c hX) hcur
    (seqStepS c (hX.comp (fst _ _)) (hb.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
      (hpre.comp (fst _ _)) (snd _ _))
    (growth := fun a ↦ 4 * (ctx c (X a)).ip.m + 3) ⟨?_, fun a s ↦ len_seqStep_le _ _ _ _ _ _⟩
  exact ((PolyBounded.const 4).mul (mU c hX).polyBounded).add (.const 3)

theorem typ1B {p : α → ℕ} (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ typ1 (p a)) input encBool :=
  beq (binMod (toBin hp) (const 2)) (const 0)

theorem len_complete_step (C : Ctx) (f : ℚ) (H : List (List AAtom)) (p : ℕ) :
    (encSl (if H.length = p then
        H ++ [C.completeSeq (typ1 p) f (C.θseq p) H.flatten []] else H)).length ≤
      (encSl H).length + (2 * (C.ip.L * (2 * (2 * C.ip.m + 1) + 1)) + 1) := by
  dsimp only [encSl]
  split_ifs
  · rw [len_encList_append]
    have := len_fresh_le C (fresh_completeSeq C (typ1 p) f (C.θseq p) H.flatten)
    simp only [encList_cons, encList_nil, List.append_nil, length_frame]
    omega
  · omega

theorem lenL {β : Type} {e : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l input (encList e)) :
    ComputableInPolyTime (fun a ↦ (l a).length) input encUnary :=
  (length_list e).comp hl

theorem flattenS {H : α → List (List AAtom)} (hH : ComputableInPolyTime H input encSl) :
    ComputableInPolyTime (fun a ↦ (H a).flatten) input encSq :=
  .of_tidy ((ComputableTidilyInPolyTime.flatten encAt).comp hH.tidy)

theorem completeL {f : α → ℚ} {H : α → List (List AAtom)}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hH : ComputableInPolyTime H input encSl) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).complete (f a) (H a)) input encSl := by
  unfold Ctx.complete
  have hX' : ComputableInPolyTime (fun q : (α × List (List AAtom)) × ℕ ↦ X q.1.1)
      (encPair (encPair input encSl) encUnary) encCI := hX.comp ((fst _ _).comp (fst _ _))
  have hH' : ComputableInPolyTime (fun q : (α × List (List AAtom)) × ℕ ↦ q.1.2)
      (encPair (encPair input encSl) encUnary) encSl := (snd _ _).comp (fst _ _)
  have hp : ComputableInPolyTime (fun q : (α × List (List AAtom)) × ℕ ↦ q.2)
      (encPair (encPair input encSl) encUnary) encUnary := snd _ _
  have hstep := itep (decide_eq' (lenL hH') hp)
    (listAppend' hH' (cons' (completeSeqS c hX' (typ1B hp) (hf.comp ((fst _ _).comp (fst _ _)))
      (θseqQ (X := fun q : (α × List (List AAtom)) × ℕ ↦ X q.1.1) c hp) (flattenS hH')
      (const [])) (const []))) hH'
  refine foldlWithInput_of_bounded_growth hH
    ⟨unary_range' (unary_mul' (const 2) (RU c hX)), hstep, inferInstance, inferInstance⟩
    (growth := fun a ↦ 2 * ((ctx c (X a)).ip.L * (2 * (2 * (ctx c (X a)).ip.m + 1) + 1)) + 1)
    ⟨?_, fun a s p _ ↦ len_complete_step _ _ _ _⟩
  exact ((PolyBounded.const 2).mul ((LU c hX).polyBounded.mul ((PolyBounded.const 2).mul
    (((PolyBounded.const 2).mul (mU c hX).polyBounded).add (.const 1)) |>.add (.const 1)))).add
    (.const 1)

theorem fhatQ {b : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hb : ComputableInPolyTime b input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).fhat (b a)) input encRat :=
  rat_add' (const c.δ) (rat_div' (rat_mul' (rat_sub' (fmaxQ c hX) (const c.δ))
    (rat_natCast' hb)) (rat_two_pow' (PfU c hX)))

theorem solL {b : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hb : ComputableInPolyTime b input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).sol (b a)) input encSl :=
  completeL c hX (fhatQ c hX hb) (const [])

theorem nRegAU {H : α → List (List AAtom)} (hH : ComputableInPolyTime H input encSl) :
    ComputableInPolyTime (fun a ↦ nRegA (H a)) input encUnary :=
  lenL (filterWithInput (test := fun _ (a : AAtom) ↦ a.2 == 0) (flattenS hH)
    (beq ((snd _ _).comp (snd _ _)) (const 0)))

theorem cntU {f : α → ℚ} {pre : α → List (List AAtom)} {W : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hpre : ComputableInPolyTime pre input encSl) (hW : ComputableInPolyTime W input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).cnt (f a) (pre a) (W a)) input encUnary :=
  nRegAU (completeL c hX hf (listAppend' hpre (cons' hW (const []))))

end BCFGJPSSV26.Greedy.PT
