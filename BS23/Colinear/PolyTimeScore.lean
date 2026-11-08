module

public import BS23.Colinear.PolyTimeLinAlg

/-!
# Polynomial time for the colinear algorithm: Hermite moments, selection, direction

List programs for the middle steps of the colinear algorithm (`BS23/Colinear/Alg.lean`), with
certificates (`Turing.MultiTapeTM.ComputableInPolyTime`), from the centered points `cs`, the
empirical covariance `C` and the basis `B` as lists of rows:

* the empirical Hermite moments `BS23.Colinear.phat` and the scores `BS23.Colinear.score`;
* the selection `BS23.Colinear.selectBest` of the first candidate `(m, i)` with the largest score,
  as a left fold over the candidates, with basis indices as numbers;
* the gradient `BS23.Colinear.gradPhat`, the direction `BS23.Colinear.direction`, and the
  projections of the points on it.

Every quantity is a sum over the points of products of a bounded number of entries, Hermite
polynomials of degree at most `M`, and quotients by quadratic forms, so it has polynomial size.
-/

@[expose] public section

namespace BS23.Colinear.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Matrix

variable {α : Type} {input : α ↪ List Bool}

/-! ### The list programs -/

/-- The empirical Hermite moment `P̂_m(v)`, from the centered points and the covariance. -/
def phatL (m n d : ℕ) (cs C : List (List ℚ)) (v : List ℚ) : ℚ :=
  ((List.range n).map fun j ↦ hermL m (dotL d (cs.getD j []) v) (quadL d C v)).sum / n

/-- The score of the candidate `(m, i)`, with the basis `B`. -/
def scoreL (n d : ℕ) (cs C B : List (List ℚ)) (p : ℕ × ℕ) : ℚ :=
  phatL p.1 n d cs C (B.getD p.2 []) ^ 2 / quadL d C (B.getD p.2 []) ^ p.1

/-- The candidates `(m, i)`, `3 ≤ m ≤ M`, `i < d`, in lexicographic order. -/
def candidatesL (M d : ℕ) : List (ℕ × ℕ) :=
  ((List.range (M - 2)).map fun m ↦ 3 + m).flatMap fun m ↦ (List.range d).map fun i ↦ (m, i)

/-- One step of the selection: keep `b` unless `a` has a larger score. -/
def selStep (n d : ℕ) (cs C B : List (List ℚ)) (b a : ℕ × ℕ) : ℕ × ℕ :=
  if scoreL n d cs C B b < scoreL n d cs C B a then a else b

/-- The first candidate with the largest score, if there is a candidate. -/
def selectBestL (M n d : ℕ) (cs C B : List (List ℚ)) : Option (ℕ × ℕ) :=
  if (candidatesL M d).isEmpty then none
  else some (((candidatesL M d).tail).foldl (selStep n d cs C B) ((candidatesL M d).headD (0, 0)))

/-- The gradient of `P̂_m` at `v`. -/
def gradL (m n d : ℕ) (cs C : List (List ℚ)) (v : List ℚ) : List ℚ :=
  (List.range d).map fun a ↦ ((List.range n).map fun j ↦
    (m : ℚ) * hermL (m - 1) (dotL d (cs.getD j []) v) (quadL d C v) * ent cs j a -
      ((m : ℚ) * ((m : ℚ) - 1)) * hermL (m - 2) (dotL d (cs.getD j []) v) (quadL d C v) *
        (mulVecL d C v).getD a 0).sum / n

/-- The direction `∑ᵢ (⟨λᵢ, g⟩ / λᵢᵀCλᵢ) λᵢ`. -/
def dirL (d : ℕ) (C B : List (List ℚ)) (g : List ℚ) : List ℚ :=
  (List.range d).map fun a ↦ ((List.range d).map fun i ↦
    dotL d (B.getD i []) g / quadL d C (B.getD i []) * ent B i a).sum

/-- The projections `⟨a, y_j⟩` of the points. -/
def projL (n d : ℕ) (P : List (List ℚ)) (a : List ℚ) : List ℚ :=
  (List.range n).map fun j ↦ dotL d a (P.getD j [])

/-! ### They compute the algorithm's quantities -/

variable {n d : ℕ} {Y : Fin n → Fin d → ℚ} {cs C B : List (List ℚ)}

theorem ofFn_eq_map_range {β : Type*} {m : ℕ} (f : Fin m → β) (g : ℕ → β)
    (h : ∀ j : Fin m, g j = f j) : List.ofFn f = (List.range m).map g := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact (h ⟨j, by simpa using h1⟩).symm

theorem phatL_eq (m : ℕ) (hc : RepT cs fun j ↦ Y j - mean Y) (hC : RepT C (empCov Y))
    {v : List ℚ} {w : Fin d → ℚ} (hv : RepV v w) : phatL m n d cs C v = phat m Y w := by
  rw [phatL, phat, sum_fin_eq_list _ (fun j ↦ hermL m (dotL d (cs.getD j []) v) (quadL d C v))
    fun j ↦ by rw [hermL_eq, dotL_eq (hc.row j) hv, quadL_eq hC hv]]

theorem scoreL_eq (hc : RepT cs fun j ↦ Y j - mean Y) (hC : RepT C (empCov Y))
    (hB : RepT B fun i ↦ basisVec (empCov Y) i) (p : ℕ × Fin d) :
    scoreL n d cs C B (p.1, p.2.val) = score Y p := by
  rw [scoreL, score, phatL_eq _ hc hC (hB.row p.2), quadL_eq hC (hB.row p.2)]

theorem candidatesL_eq (M d : ℕ) :
    candidatesL M d = (candidates M d).map fun p ↦ (p.1, p.2.val) := by
  rw [candidatesL, candidates, List.map_flatMap, List.range'_eq_map_range]
  congr 1
  funext m
  rw [List.map_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem argmaxFrom_eq_foldl {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] {β : Type*} (f : β → K) (l : List β) (b : β) :
    argmaxFrom f l b = l.foldl (fun b a ↦ if f b < f a then a else b) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih _

theorem map_argmaxFrom {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] {β γ : Type*} (f : β → K) (f' : γ → K) (g : β → γ) (h : ∀ x, f' (g x) = f x)
    (l : List β) (b : β) : g (argmaxFrom f l b) = argmaxFrom f' (l.map g) (g b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons]
    change g (argmaxFrom f l _) = argmaxFrom f' (l.map g) _
    rw [ih, h, h]
    split_ifs <;> rfl

theorem selectBestL_eq (M : ℕ) (hc : RepT cs fun j ↦ Y j - mean Y) (hC : RepT C (empCov Y))
    (hB : RepT B fun i ↦ basisVec (empCov Y) i) :
    (selectBest M Y).map (fun p ↦ (p.1, p.2.val)) = selectBestL M n d cs C B := by
  rw [selectBest, selectBestL, candidatesL_eq]
  cases candidates M d with
  | nil => rfl
  | cons p l =>
    simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.tail_cons,
      List.headD_cons, Option.map_some]
    rw [map_argmaxFrom (score Y) (scoreL n d cs C B) _ (fun x ↦ scoreL_eq hc hC hB x),
      argmaxFrom_eq_foldl]
    rfl

theorem gradL_rep (m : ℕ) (hc : RepT cs fun j ↦ Y j - mean Y) (hC : RepT C (empCov Y))
    {v : List ℚ} {w : Fin d → ℚ} (hv : RepV v w) : RepV (gradL m n d cs C v) (gradPhat m Y w) :=
  repV_map_range _ _ fun a ↦ by
    rw [gradPhat]
    congr 1
    refine (sum_fin_eq_list _ _ fun j ↦ ?_).symm
    rw [hermL_eq, hermL_eq, dotL_eq (hc.row j) hv, quadL_eq hC hv, hc j a, mulVecL_rep hC hv a]
    rfl

theorem dirL_rep {M : Matrix (Fin d) (Fin d) ℚ} (hC : RepT C M) (hB : RepT B fun i ↦ basisVec M i)
    {g : List ℚ} {g' : Fin d → ℚ} (hg : RepV g g') : RepV (dirL d C B g) (direction M g') :=
  repV_map_range _ _ fun a ↦ by
    rw [direction, Finset.sum_apply]
    refine (sum_fin_eq_list _ _ fun i ↦ ?_).symm
    rw [dotL_eq (hB.row i) hg, quadL_eq hC (hB.row i), hB i a, Pi.smul_apply, smul_eq_mul]

theorem projL_eq {P : List (List ℚ)} (hP : RepT P Y) {a : List ℚ} {a' : Fin d → ℚ}
    (ha : RepV a a') : projL n d P a = List.ofFn fun j ↦ a' ⬝ᵥ Y j :=
  (ofFn_eq_map_range _ _ fun j ↦ dotL_eq ha (hP.row j)).symm

/-! ### Polynomial time -/

/-- The data `(n, d, cs, C)`. -/
abbrev encD : ℕ × ℕ × List (List ℚ) × List (List ℚ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encM encM))

theorem phatL_polytime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      phatL p.1 p.2.1.1 p.2.1.2.1 p.2.1.2.2.1 p.2.1.2.2.2 p.2.2)
    (encPair encUnary (encPair encD encV)) encRat := by
  unfold phatL
  set E := encPair encUnary (encPair encD encV)
  have hm : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.1) E encUnary := fst _ _
  have hn : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.2.1.1) E encUnary := (fst _ _).comp ((fst _ _).comp (snd _ _))
  have hd : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.2.1.2.1) E encUnary := (fst _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _)))
  have hcs : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.2.1.2.2.1) E encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _))))
  have hC : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.2.1.2.2.2) E encM :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _))))
  have hv : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      p.2.2) E encV := (snd _ _).comp (snd _ _)
  exact rat_div' (rat_sum' (mapWithInput (range.comp hn)
    (hermL' (hm.comp (fst _ _)) (dotL' (hd.comp (fst _ _)) (row' (hcs.comp (fst _ _)) (snd _ _))
      (hv.comp (fst _ _))) (quadL' (hd.comp (fst _ _)) (hC.comp (fst _ _)) (hv.comp (fst _ _))))))
    (rat_ofUnary hn)

@[fun_prop]
theorem phatL' {m n d : α → ℕ} {cs C : α → List (List ℚ)} {v : α → List ℚ}
    (hm : ComputableInPolyTime m input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hcs : ComputableInPolyTime cs input encM)
    (hC : ComputableInPolyTime C input encM) (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ phatL (m x) (n x) (d x) (cs x) (C x) (v x)) input encRat :=
  phatL_polytime.comp (g := fun x ↦ (m x, (n x, d x, cs x, C x), v x))
    (hm.prod ((hn.prod (hd.prod (hcs.prod hC))).prod hv))

@[fun_prop]
theorem scoreL' {n d : α → ℕ} {cs C B : α → List (List ℚ)} {p : α → ℕ × ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hcs : ComputableInPolyTime cs input encM) (hC : ComputableInPolyTime C input encM)
    (hB : ComputableInPolyTime B input encM)
    (hp : ComputableInPolyTime p input (encPair encUnary encUnary)) :
    ComputableInPolyTime (fun x ↦ scoreL (n x) (d x) (cs x) (C x) (B x) (p x)) input encRat := by
  unfold scoreL
  have hm : ComputableInPolyTime (fun x ↦ (p x).1) input encUnary := (fst _ _).comp hp
  have hv : ComputableInPolyTime (fun x ↦ (B x).getD (p x).2 []) input encV :=
    row' hB ((snd _ _).comp hp)
  exact rat_div' (rat_sq' (phatL' hm hn hd hcs hC hv)) (rat_pow' (quadL' hd hC hv) hm)

theorem candidatesL_polytime : ComputableInPolyTime (fun p : ℕ × ℕ ↦ candidatesL p.1 p.2)
    (encPair encUnary encUnary) (encList (encPair encUnary encUnary)) := by
  unfold candidatesL
  exact flatMapWithInput (mapWithInput (range.comp (unary_sub' (fst _ _) (const 2)))
    (unary_add' (const 3) (snd _ _)))
    (mapWithInput (range.comp ((snd _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _) |>.prod
      (snd _ _)))

/-- The input `(M, n, d, cs, C, B)` of the selection. -/
abbrev SelT := ℕ × ℕ × ℕ × List (List ℚ) × List (List ℚ) × List (List ℚ)

/-- The input `(m, (n, d, cs, C), v)` of the gradient. -/
abbrev GradT := ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ

/-- The input `(d, C, B, g)` of the direction. -/
abbrev DirT := ℕ × List (List ℚ) × List (List ℚ) × List ℚ

/-- The data `(n, d, cs, C, B)` of the selection. -/
abbrev encS : ℕ × ℕ × List (List ℚ) × List (List ℚ) × List (List ℚ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encM (encPair encM encM)))

theorem selectBestL_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ × List (List ℚ) × List (List ℚ) × List (List ℚ) ↦
      selectBestL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    (encPair encUnary encS) (encOption (encPair encUnary encUnary)) := by
  unfold selectBestL
  set E := encPair encUnary encS
  have hn : ComputableInPolyTime (fun p : SelT ↦ p.2.1) E encUnary := (fst _ _).comp (snd _ _)
  have hd : ComputableInPolyTime (fun p : SelT ↦ p.2.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hcs : ComputableInPolyTime (fun p : SelT ↦ p.2.2.2.1) E encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hC : ComputableInPolyTime (fun p : SelT ↦ p.2.2.2.2.1) E encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hB : ComputableInPolyTime (fun p : SelT ↦ p.2.2.2.2.2) E encM :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hcand : ComputableInPolyTime (fun p : SelT ↦ candidatesL p.1 p.2.2.1) E
      (encList (encPair encUnary encUnary)) :=
    candidatesL_polytime.comp (g := fun p : SelT ↦ (p.1, p.2.2.1)) ((fst _ _).prod hd)
  have hstep : ComputableInPolyTime (fun q : (SelT × (ℕ × ℕ)) × (ℕ × ℕ) ↦
      selStep q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2.1 q.1.1.2.2.2.2.1 q.1.1.2.2.2.2.2 q.1.2 q.2)
      (encPair (encPair E (encPair encUnary encUnary)) (encPair encUnary encUnary))
      (encPair encUnary encUnary) := by
    unfold selStep
    have h1 : ComputableInPolyTime (fun q : (SelT × (ℕ × ℕ)) × (ℕ × ℕ) ↦ q.1.1)
        (encPair (encPair E (encPair encUnary encUnary)) (encPair encUnary encUnary)) E :=
      (fst _ _).comp (fst _ _)
    have hn' := hn.comp h1
    have hd' := hd.comp h1
    have hcs' := hcs.comp h1
    have hC' := hC.comp h1
    have hB' := hB.comp h1
    exact ite_prop (rat_lt' (scoreL' hn' hd' hcs' hC' hB' ((snd _ _).comp (fst _ _)))
      (scoreL' hn' hd' hcs' hC' hB' (snd _ _))) (snd _ _) ((snd _ _).comp (fst _ _))
  have hfold : ComputableInPolyTime (fun p : SelT ↦
      ((candidatesL p.1 p.2.2.1).tail).foldl
        (selStep p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
        ((candidatesL p.1 p.2.2.1).headD (0, 0))) E (encPair encUnary encUnary) := by
    refine foldlWith_of_bounded_growth (par := fun p : SelT ↦ p)
      (step := fun p b a ↦ selStep p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 b a)
      id' ((tail (encA := encPair encUnary encUnary)).comp hcand)
      ((headD (encA := encPair encUnary encUnary) (0, 0)).comp hcand) hstep
      (growth := fun p ↦ (encList (encPair encUnary encUnary) (candidatesL p.1 p.2.2.1)).length)
      hcand.polyBounded_length fun x state value hv ↦ ?_
    have h := SizedListEncoding.length_elem_le (encA := encPair encUnary encUnary)
      (encL := encList (encPair encUnary encUnary)) _ _ (List.mem_of_mem_tail hv)
    unfold selStep
    split_ifs <;> omega
  exact ite' ((listIsEmpty (encA := encPair encUnary encUnary)).comp hcand) (const none)
    ((optionSome _).comp hfold)

@[fun_prop]
theorem selectBestL' {M n d : α → ℕ} {cs C B : α → List (List ℚ)}
    (hM : ComputableInPolyTime M input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hcs : ComputableInPolyTime cs input encM)
    (hC : ComputableInPolyTime C input encM) (hB : ComputableInPolyTime B input encM) :
    ComputableInPolyTime (fun x ↦ selectBestL (M x) (n x) (d x) (cs x) (C x) (B x)) input
      (encOption (encPair encUnary encUnary)) :=
  selectBestL_polytime.comp (g := fun x ↦ (M x, n x, d x, cs x, C x, B x))
    (hM.prod (hn.prod (hd.prod (hcs.prod (hC.prod hB)))))

theorem gradL_polytime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ × List (List ℚ) × List (List ℚ)) × List ℚ ↦
      gradL p.1 p.2.1.1 p.2.1.2.1 p.2.1.2.2.1 p.2.1.2.2.2 p.2.2)
    (encPair encUnary (encPair encD encV)) encV := by
  unfold gradL
  set E := encPair encUnary (encPair encD encV)
  have hm : ComputableInPolyTime (fun p : GradT ↦ p.1) E encUnary := fst _ _
  have hn : ComputableInPolyTime (fun p : GradT ↦ p.2.1.1) E encUnary :=
    (fst _ _).comp ((fst _ _).comp (snd _ _))
  have hd : ComputableInPolyTime (fun p : GradT ↦ p.2.1.2.1) E encUnary :=
    (fst _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _)))
  have hcs : ComputableInPolyTime (fun p : GradT ↦ p.2.1.2.2.1) E encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _))))
  have hC : ComputableInPolyTime (fun p : GradT ↦ p.2.1.2.2.2) E encM :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (snd _ _))))
  have hv : ComputableInPolyTime (fun p : GradT ↦ p.2.2) E encV := (snd _ _).comp (snd _ _)
  have h2 : ComputableInPolyTime (fun p : (GradT × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair E encUnary) encUnary) E := (fst _ _).comp (fst _ _)
  have hm2 := hm.comp h2
  have hd2 := hd.comp h2
  have hcs2 := hcs.comp h2
  have hC2 := hC.comp h2
  have hv2 := hv.comp h2
  have hx : ComputableInPolyTime (fun p : (GradT × ℕ) × ℕ ↦ dotL p.1.1.2.1.2.1
      (p.1.1.2.1.2.2.1.getD p.2 []) p.1.1.2.2) (encPair (encPair E encUnary) encUnary) encRat :=
    dotL' hd2 (row' hcs2 (snd _ _)) hv2
  have hq : ComputableInPolyTime (fun p : (GradT × ℕ) × ℕ ↦ quadL p.1.1.2.1.2.1 p.1.1.2.1.2.2.2
      p.1.1.2.2) (encPair (encPair E encUnary) encUnary) encRat := quadL' hd2 hC2 hv2
  have hmq := rat_ofUnary hm2
  exact mapWithInput (range.comp hd) (rat_div' (rat_sum' (mapWithInput
    (range.comp (hn.comp (fst _ _)))
    (rat_sub' (rat_mul' (rat_mul' hmq (hermL' (unary_sub' hm2 (const 1)) hx hq))
        (ent' hcs2 (snd _ _) ((snd _ _).comp (fst _ _))))
      (rat_mul' (rat_mul' (rat_mul' hmq (rat_sub' hmq (const 1)))
        (hermL' (unary_sub' hm2 (const 2)) hx hq))
        (vget' (mulVecL' hd2 hC2 hv2) ((snd _ _).comp (fst _ _)))))))
    (rat_ofUnary (hn.comp (fst _ _))))

@[fun_prop]
theorem gradL' {m n d : α → ℕ} {cs C : α → List (List ℚ)} {v : α → List ℚ}
    (hm : ComputableInPolyTime m input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hcs : ComputableInPolyTime cs input encM)
    (hC : ComputableInPolyTime C input encM) (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ gradL (m x) (n x) (d x) (cs x) (C x) (v x)) input encV :=
  gradL_polytime.comp (g := fun x ↦ (m x, (n x, d x, cs x, C x), v x))
    (hm.prod ((hn.prod (hd.prod (hcs.prod hC))).prod hv))

theorem dirL_polytime : ComputableInPolyTime
    (fun p : ℕ × List (List ℚ) × List (List ℚ) × List ℚ ↦ dirL p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encM (encPair encM encV))) encV := by
  unfold dirL
  set E := encPair encUnary (encPair encM (encPair encM encV))
  have h2 : ComputableInPolyTime (fun p : (DirT × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair E encUnary) encUnary) E := (fst _ _).comp (fst _ _)
  have hd2 : ComputableInPolyTime (fun p : (DirT × ℕ) × ℕ ↦ p.1.1.1)
      (encPair (encPair E encUnary) encUnary) encUnary := (fst _ _).comp h2
  have hC2 : ComputableInPolyTime (fun p : (DirT × ℕ) × ℕ ↦ p.1.1.2.1)
      (encPair (encPair E encUnary) encUnary) encM := (fst _ _).comp ((snd _ _).comp h2)
  have hB2 : ComputableInPolyTime (fun p : (DirT × ℕ) × ℕ ↦ p.1.1.2.2.1)
      (encPair (encPair E encUnary) encUnary) encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp h2))
  have hg2 : ComputableInPolyTime (fun p : (DirT × ℕ) × ℕ ↦ p.1.1.2.2.2)
      (encPair (encPair E encUnary) encUnary) encV :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp h2))
  have hrow := row' hB2 (snd _ _)
  exact mapWithInput (range.comp (fst _ _)) (rat_sum' (mapWithInput
    (range.comp ((fst _ _).comp (fst _ _)))
    (rat_mul' (rat_div' (dotL' hd2 hrow hg2) (quadL' hd2 hC2 hrow))
      (ent' hB2 (snd _ _) ((snd _ _).comp (fst _ _))))))

@[fun_prop]
theorem dirL' {d : α → ℕ} {C B : α → List (List ℚ)} {g : α → List ℚ}
    (hd : ComputableInPolyTime d input encUnary) (hC : ComputableInPolyTime C input encM)
    (hB : ComputableInPolyTime B input encM) (hg : ComputableInPolyTime g input encV) :
    ComputableInPolyTime (fun x ↦ dirL (d x) (C x) (B x) (g x)) input encV :=
  dirL_polytime.comp (g := fun x ↦ (d x, C x, B x, g x)) (hd.prod (hC.prod (hB.prod hg)))

@[fun_prop]
theorem projL' {n d : α → ℕ} {P : α → List (List ℚ)} {a : α → List ℚ}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hP : ComputableInPolyTime P input encM) (ha : ComputableInPolyTime a input encV) :
    ComputableInPolyTime (fun x ↦ projL (n x) (d x) (P x) (a x)) input encV := by
  unfold projL
  exact mapWithInput (range.comp hn)
    (dotL' (hd.comp (fst _ _)) (ha.comp (fst _ _)) (row' (hP.comp (fst _ _)) (snd _ _)))

end BS23.Colinear.PT
