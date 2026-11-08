module

public import BS23.Colinear.PolyTimeBasic

/-!
# Polynomial time for the colinear algorithm: the clustering on the line

The clustering on the line `BS23.OneDim.cluster` as a list program
(`BS23.Colinear.PT.clusterL`), on the list of the points: cells and heavy cells as lists of
integers (heavy cells without repetitions, so that cardinalities of sets of cells are lengths of
lists), the next heavy cell as the minimum of a list (`List.min?`), the chosen level as a fold of
`max`. It computes the clustering (`BS23.Colinear.PT.clusterL_eq`) and runs in polynomial time
(`BS23.Colinear.PT.clusterL_polytime`).
-/

@[expose] public section

namespace BS23.Colinear.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open OneDim

variable {α : Type} {input : α ↪ List Bool}

/-! ### The list program -/

/-- The cells of the points at scale `h`. -/
def cellsL (h : ℚ) (zs : List ℚ) : List ℤ := zs.map (cell h)

/-- The number of points in the cell `p`. -/
def countL (cs : List ℤ) (p : ℤ) : ℕ := cs.countP fun c ↦ decide (c = p)

/-- The heavy cells, without repetitions: those holding at least `θ n` of the cells `cs`. -/
def heavyL (θ : ℚ) (n : ℕ) (cs : List ℤ) : List ℤ :=
  cs.dedup.filter fun p ↦ decide (θ * n ≤ (countL cs p : ℚ))

/-- The fraction of the cells `cs` that are heavy. -/
def coverageL (θ : ℚ) (n : ℕ) (cs : List ℤ) : ℚ :=
  ((cs.countP fun c ↦ decide (c ∈ heavyL θ n cs) : ℕ) : ℚ) / n

/-- The chosen level. -/
def levelL (θ ε H : ℚ) (ℓmax : ℕ) (zs : List ℚ) : ℕ :=
  ((List.range (ℓmax + 1)).filter fun ℓ ↦
    decide (1 - ε ≤ coverageL θ zs.length (cellsL (scale H ℓ) zs))).foldr max 0

/-- The next heavy cell after `p`. -/
def nextL (S : List ℤ) (p : ℤ) : Option ℤ := (S.filter fun q ↦ decide (p < q)).min?

/-- The gap after the heavy cell `p`. -/
def gapL (S : List ℤ) (p : ℤ) : ℤ := (nextL S p).elim 0 fun q ↦ q - p

/-- The heavy cells followed by another one, with a larger gap, or an equal gap further left. -/
def beforeL (S : List ℤ) (p : ℤ) : List ℤ :=
  S.filter fun q ↦ (nextL S q).isSome &&
    (decide (gapL S p < gapL S q) || (decide (gapL S q = gapL S p) && decide (q < p)))

/-- The boundaries. -/
def boundariesL (k : ℕ) (S : List ℤ) : List ℤ :=
  S.filter fun p ↦ (nextL S p).isSome && decide ((beforeL S p).length < k - 1)

/-- The label of a point in the cell `p`. -/
def labelOfCellL (k : ℕ) (S : List ℤ) (p : ℤ) : ℕ :=
  ((boundariesL k S).filter fun b ↦ decide (b + (b + gapL S b) < 2 * p)).length

/-- **The clustering on the line**, as a list program. -/
def clusterL (k : ℕ) (θ ε H : ℚ) (ℓmax : ℕ) (zs : List ℚ) : List ℕ :=
  (cellsL (scale H (levelL θ ε H ℓmax zs)) zs).map
    (labelOfCellL k (heavyL θ zs.length (cellsL (scale H (levelL θ ε H ℓmax zs)) zs)))

/-! ### It computes the clustering -/

theorem card_filter_univ {β : Type*} {n : ℕ} (f : Fin n → β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j ↦ P (f j)).card = (List.ofFn f).countP fun b ↦ decide (P b) := by
  rw [List.ofFn_eq_map, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext j
  simp

variable {n : ℕ}

theorem cellCount_eq (h : ℚ) (z : Fin n → ℚ) (p : ℤ) :
    cellCount h z p = countL (cellsL h (List.ofFn z)) p := by
  rw [cellCount, card_filter_univ (fun j ↦ z j) (fun x ↦ cell h x = p), countL, cellsL,
    List.countP_map]
  rfl

theorem heavy_eq (θ h : ℚ) (z : Fin n → ℚ) :
    heavy θ h z = (heavyL θ n (cellsL h (List.ofFn z))).toFinset := by
  ext p
  simp only [heavy, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    List.mem_toFinset, heavyL, List.mem_filter, List.mem_dedup, cellsL, List.mem_map,
    List.mem_ofFn, cellCount_eq]
  constructor
  · rintro ⟨⟨j, rfl⟩, h2⟩
    exact ⟨⟨z j, ⟨j, rfl⟩, rfl⟩, by simpa using h2⟩
  · rintro ⟨⟨_, ⟨j, rfl⟩, rfl⟩, h2⟩
    exact ⟨⟨j, rfl⟩, by simpa using h2⟩

theorem nodup_heavyL (θ : ℚ) (n : ℕ) (cs : List ℤ) : (heavyL θ n cs).Nodup :=
  (List.nodup_dedup cs).filter _

theorem coverage_eq (θ h : ℚ) (z : Fin n → ℚ) :
    coverage θ h z = coverageL θ n (cellsL h (List.ofFn z)) := by
  rw [coverage, coverageL, card_filter_univ (fun j ↦ z j) (fun x ↦ cell h x ∈ heavy θ h z),
    cellsL, List.countP_map]
  congr 3
  funext x
  simp [heavy_eq, cellsL, List.map_ofFn]

theorem sup_toFinset (l : List ℕ) : l.toFinset.sup id = l.foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.toFinset_cons, Finset.sup_insert, ih, List.foldr_cons]
    rfl

theorem level_eq (θ ε H : ℚ) (ℓmax : ℕ) (z : Fin n → ℚ) :
    level θ ε H ℓmax z = levelL θ ε H ℓmax (List.ofFn z) := by
  rw [level, levelL, ← sup_toFinset, List.length_ofFn]
  congr 1
  ext ℓ
  simp [coverage_eq]

theorem filter_toFinset (l : List ℤ) (P : ℤ → Prop) [DecidablePred P] :
    l.toFinset.filter P = (l.filter fun q ↦ decide (P q)).toFinset := by
  ext q
  simp

theorem next_eq (l : List ℤ) (p : ℤ) : next l.toFinset p = nextL l p := by
  unfold next nextL
  have hset := filter_toFinset l (fun q ↦ p < q)
  split_ifs with h
  · have hne : (l.filter fun q ↦ decide (p < q)) ≠ [] := by
      intro he
      rw [hset, he] at h
      simp at h
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (mt List.min?_eq_none_iff.mp hne)
    rw [hv]
    replace hv := List.min?_eq_some_iff.mp hv
    congr 1
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [hset]; simpa using hv.1)
    · exact Finset.le_min' _ _ _ fun y hy ↦ hv.2 y (by rw [hset] at hy; simpa using hy)
  · symm
    rw [List.min?_eq_none_iff]
    by_contra hne
    apply h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    rw [hset]
    exact ⟨x, List.mem_toFinset.2 hx⟩

theorem gap_eq (l : List ℤ) (p : ℤ) : gap l.toFinset p = gapL l p := by
  rw [gap, gapL, next_eq]
  cases nextL l p <;> rfl

theorem before_eq (l : List ℤ) (p : ℤ) : before l.toFinset p = (beforeL l p).toFinset := by
  rw [before, beforeL, filter_toFinset]
  congr 2
  funext q
  simp [next_eq, gap_eq]

theorem boundaries_eq (k : ℕ) {l : List ℤ} (hl : l.Nodup) :
    boundaries k l.toFinset = (boundariesL k l).toFinset := by
  rw [boundaries, boundariesL, filter_toFinset]
  congr 2
  funext q
  have hc : (beforeL l q).toFinset.card = (beforeL l q).length :=
    List.toFinset_card_of_nodup (hl.filter _)
  simp [next_eq, before_eq, hc]

theorem labelOfCell_eq (k : ℕ) {l : List ℤ} (hl : l.Nodup) (p : ℤ) :
    labelOfCell k l.toFinset p = labelOfCellL k l p := by
  have hb : (boundariesL k l).Nodup := hl.filter _
  rw [labelOfCell, labelOfCellL, boundaries_eq k hl, filter_toFinset,
    List.toFinset_card_of_nodup (hb.filter _)]
  congr 2
  funext b
  simp [gap_eq]

/-- **The list program computes the clustering on the line.** -/
theorem clusterL_eq (k : ℕ) (θ ε H : ℚ) (ℓmax : ℕ) (z : Fin n → ℚ) :
    List.ofFn (OneDim.cluster k θ ε H ℓmax z) = clusterL k θ ε H ℓmax (List.ofFn z) := by
  rw [clusterL, ← level_eq, List.length_ofFn]
  set h := scale H (level θ ε H ℓmax z)
  have hc : cellsL h (List.ofFn z) = List.ofFn (cell h ∘ z) := List.map_ofFn
  rw [hc, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, OneDim.cluster]
  rw [heavy_eq, labelOfCell_eq k (nodup_heavyL _ _ _), hc]

/-! ### Polynomial time -/

/-- Lists of cells. -/
abbrev encZ : List ℤ ↪ List Bool := encList encIntBin

theorem intLe' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ decide (f a ≤ g a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_le' hf.tidy hg.tidy)

theorem intLt' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ decide (f a < g a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_lt' hf.tidy hg.tidy)

theorem intAdd' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_add' hf.tidy hg.tidy)

theorem intSub' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ f a - g a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_sub' hf.tidy hg.tidy)

theorem intMul' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ f a * g a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_mul' hf.tidy hg.tidy)

theorem boolOr' {f g : α → Bool} (hf : ComputableInPolyTime f input encBool)
    (hg : ComputableInPolyTime g input encBool) :
    ComputableInPolyTime (fun a ↦ f a || g a) input encBool :=
  bool_or.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem cellsL_polytime : ComputableInPolyTime (fun p : ℚ × List ℚ ↦ cellsL p.1 p.2)
    (encPair encRat (encList encRat)) encZ := by
  unfold cellsL cell
  exact mapWithInput (snd _ _) (rat_floor' (rat_div' (snd _ _) ((fst _ _).comp (fst _ _))))

@[fun_prop]
theorem cellsL' {h : α → ℚ} {zs : α → List ℚ} (hh : ComputableInPolyTime h input encRat)
    (hz : ComputableInPolyTime zs input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ cellsL (h a) (zs a)) input encZ :=
  cellsL_polytime.comp (g := fun a ↦ (h a, zs a)) (hh.prod hz)

@[fun_prop]
theorem countL' {cs : α → List ℤ} {p : α → ℤ} (hc : ComputableInPolyTime cs input encZ)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a ↦ countL (cs a) (p a)) input encUnary := by
  unfold countL
  exact countPWithInput hc (decide_eq' (snd _ _) (hp.comp (fst _ _)))

theorem heavyL_polytime : ComputableInPolyTime (fun p : ℚ × ℕ × List ℤ ↦ heavyL p.1 p.2.1 p.2.2)
    (encPair encRat (encPair encUnary encZ)) encZ := by
  unfold heavyL
  set E := encPair encRat (encPair encUnary encZ)
  have hc : ComputableInPolyTime (fun p : ℚ × ℕ × List ℤ ↦ p.2.2) E encZ :=
    (snd _ _).comp (snd _ _)
  exact filterWithInput (listDedup hc)
    (rat_le' (rat_mul' ((fst _ _).comp (fst _ _)) (rat_ofUnary ((fst _ _).comp ((snd _ _).comp
      (fst _ _))))) (rat_ofUnary (countL' (hc.comp (fst _ _)) (snd _ _))))

@[fun_prop]
theorem heavyL' {θ : α → ℚ} {n : α → ℕ} {cs : α → List ℤ}
    (hθ : ComputableInPolyTime θ input encRat) (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime cs input encZ) :
    ComputableInPolyTime (fun a ↦ heavyL (θ a) (n a) (cs a)) input encZ :=
  heavyL_polytime.comp (g := fun a ↦ (θ a, n a, cs a)) (hθ.prod (hn.prod hc))

@[fun_prop]
theorem coverageL' {θ : α → ℚ} {n : α → ℕ} {cs : α → List ℤ}
    (hθ : ComputableInPolyTime θ input encRat) (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime cs input encZ) :
    ComputableInPolyTime (fun a ↦ coverageL (θ a) (n a) (cs a)) input encRat := by
  unfold coverageL
  exact rat_div' (rat_ofUnary (countPWithInput hc (decide_mem
    (heavyL' (hθ.comp (fst _ _)) (hn.comp (fst _ _)) (hc.comp (fst _ _))) (snd _ _))))
    (rat_ofUnary hn)

theorem max_polytime : ComputableInPolyTime (fun p : ℕ × ℕ ↦ max p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ ↦ if p.1 ≤ p.2 then p.2 else p.1)
      (encPair encUnary encUnary) encUnary :=
    ite_prop (unary_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)
  refine h.of_enc_eq fun p ↦ ?_
  rw [max_def]

theorem levelL_polytime : ComputableInPolyTime
    (fun p : ℚ × ℚ × ℚ × ℕ × List ℚ ↦ levelL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (encPair encRat (encPair encRat (encPair encRat (encPair encUnary (encList encRat)))))
    encUnary := by
  unfold levelL
  set E := encPair encRat (encPair encRat (encPair encRat (encPair encUnary (encList encRat))))
  have hz : ComputableInPolyTime (fun p : (ℚ × ℚ × ℚ × ℕ × List ℚ) × ℕ ↦ p.1.2.2.2.2)
      (encPair E encUnary) (encList encRat) :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _))))
  have hH : ComputableInPolyTime (fun p : (ℚ × ℚ × ℚ × ℕ × List ℚ) × ℕ ↦ p.1.2.2.1)
      (encPair E encUnary) encRat :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _)))
  have hlist : ComputableInPolyTime (fun p : ℚ × ℚ × ℚ × ℕ × List ℚ ↦
      (List.range (p.2.2.2.1 + 1)).filter fun ℓ ↦
        decide (1 - p.2.1 ≤ coverageL p.1 p.2.2.2.2.length (cellsL (scale p.2.2.1 ℓ) p.2.2.2.2)))
      E (encList encUnary) := by
    refine filterWithInput (range.comp (unary_add' ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp
      (snd _ _)))) (const 1))) (rat_le' (rat_sub' (const 1) ((fst _ _).comp ((snd _ _).comp
        (fst _ _)))) (coverageL' ((fst _ _).comp (fst _ _)) ((length_list encRat).comp hz)
          (cellsL' ?_ hz)))
    unfold scale
    exact rat_div' hH (rat_two_pow' (snd _ _))
  have hr : ComputableInPolyTime (fun p : ℚ × ℚ × ℚ × ℕ × List ℚ ↦ List.range (p.2.2.2.1 + 1))
      E (encList encUnary) :=
    range.comp (unary_add' ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
      (const 1))
  refine foldrWithInput_of_bounded_growth (step := fun _ a acc ↦ max a acc) hlist (const 0)
    (max_polytime.comp (g := fun p : ((ℚ × ℚ × ℚ × ℕ × List ℚ) × ℕ) × ℕ ↦ (p.2, p.1.2))
      ((snd _ _).prod ((snd _ _).comp (fst _ _))))
    (growth := fun x ↦ (encList encUnary (List.range (x.2.2.2.1 + 1))).length)
    hr.polyBounded_length fun x state value hv ↦ ?_
  have h := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary) _ _
    (List.mem_of_mem_filter hv)
  simp only [encUnary_apply, List.length_replicate] at h ⊢
  omega

@[fun_prop]
theorem levelL' {θ ε H : α → ℚ} {ℓmax : α → ℕ} {zs : α → List ℚ}
    (hθ : ComputableInPolyTime θ input encRat) (hε : ComputableInPolyTime ε input encRat)
    (hH : ComputableInPolyTime H input encRat) (hℓ : ComputableInPolyTime ℓmax input encUnary)
    (hz : ComputableInPolyTime zs input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ levelL (θ a) (ε a) (H a) (ℓmax a) (zs a)) input encUnary :=
  levelL_polytime.comp (g := fun a ↦ (θ a, ε a, H a, ℓmax a, zs a))
    (hθ.prod (hε.prod (hH.prod (hℓ.prod hz))))

/-- `List.min?` with a fold. -/
theorem min?_eq (l : List ℤ) :
    l.min? = if l.isEmpty then none else some (l.tail.foldl min (l.headD 0)) := by
  cases l <;> rfl

theorem min?_polytime : ComputableInPolyTime (fun l : List ℤ ↦ l.min?) encZ
    (encOption encIntBin) := by
  have hmin : ComputableInPolyTime (fun p : (List ℤ × ℤ) × ℤ ↦ min p.1.2 p.2)
      (encPair (encPair encZ encIntBin) encIntBin) encIntBin := by
    have h : ComputableInPolyTime (fun p : (List ℤ × ℤ) × ℤ ↦ if p.1.2 ≤ p.2 then p.1.2 else p.2)
        (encPair (encPair encZ encIntBin) encIntBin) encIntBin :=
      ite_prop (intLe' ((snd _ _).comp (fst _ _)) (snd _ _)) ((snd _ _).comp (fst _ _)) (snd _ _)
    exact h.of_enc_eq fun p ↦ by rw [min_def]
  have hfold : ComputableInPolyTime (fun l : List ℤ ↦ l.tail.foldl min (l.headD 0)) encZ
      encIntBin := by
    refine foldlWith_of_bounded_growth (par := fun l : List ℤ ↦ l) (step := fun _ a b ↦ min a b)
      id' (tail (encA := encIntBin)) (headD (encA := encIntBin) 0) hmin
      (growth := fun l ↦ (encZ l).length) .self fun l state value hv ↦ ?_
    have h := SizedListEncoding.length_elem_le (encA := encIntBin) (encL := encZ) _ _
      (List.mem_of_mem_tail hv)
    rcases min_choice state value with h' | h' <;> rw [h'] <;> omega
  have h : ComputableInPolyTime (fun l : List ℤ ↦
      if l.isEmpty = true then none else some (l.tail.foldl min (l.headD 0))) encZ
      (encOption encIntBin) :=
    ite' (listIsEmpty (encA := encIntBin)) (const none) ((optionSome encIntBin).comp hfold)
  exact h.of_enc_eq fun l ↦ by rw [min?_eq]

@[fun_prop]
theorem nextL' {S : α → List ℤ} {p : α → ℤ} (hS : ComputableInPolyTime S input encZ)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a ↦ nextL (S a) (p a)) input (encOption encIntBin) := by
  unfold nextL
  exact min?_polytime.comp (filterWithInput hS (intLt' (hp.comp (fst _ _)) (snd _ _)))

@[fun_prop]
theorem gapL' {S : α → List ℤ} {p : α → ℤ} (hS : ComputableInPolyTime S input encZ)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a ↦ gapL (S a) (p a)) input encIntBin := by
  unfold gapL
  exact optionElimWithInput (nextL' hS hp) (const 0) (intSub' (snd _ _) (hp.comp (fst _ _)))

@[fun_prop]
theorem beforeL' {S : α → List ℤ} {p : α → ℤ} (hS : ComputableInPolyTime S input encZ)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a ↦ beforeL (S a) (p a)) input encZ := by
  unfold beforeL
  have hS' : ComputableInPolyTime (fun x : α × ℤ ↦ S x.1) (encPair input encIntBin) encZ :=
    hS.comp (fst _ _)
  have hp' : ComputableInPolyTime (fun x : α × ℤ ↦ p x.1) (encPair input encIntBin) encIntBin :=
    hp.comp (fst _ _)
  have hq : ComputableInPolyTime (fun x : α × ℤ ↦ x.2) (encPair input encIntBin) encIntBin :=
    snd _ _
  exact filterWithInput hS (bool_and' (optionIsSome (nextL' hS' hq))
    (boolOr' (intLt' (gapL' hS' hp') (gapL' hS' hq))
      (bool_and' (decide_eq' (gapL' hS' hq) (gapL' hS' hp')) (intLt' hq hp'))))

@[fun_prop]
theorem boundariesL' {k : α → ℕ} {S : α → List ℤ} (hk : ComputableInPolyTime k input encNat)
    (hS : ComputableInPolyTime S input encZ) :
    ComputableInPolyTime (fun a ↦ boundariesL (k a) (S a)) input encZ := by
  unfold boundariesL
  have hS' : ComputableInPolyTime (fun x : α × ℤ ↦ S x.1) (encPair input encIntBin) encZ :=
    hS.comp (fst _ _)
  have hq : ComputableInPolyTime (fun x : α × ℤ ↦ x.2) (encPair input encIntBin) encIntBin :=
    snd _ _
  exact filterWithInput hS (bool_and' (optionIsSome (nextL' hS' hq))
    (binary_lt' (toBinary' ((length_list encIntBin).comp (beforeL' hS' hq)))
      (binary_sub' (hk.comp (fst _ _)) (const 1))))

@[fun_prop]
theorem labelOfCellL' {k : α → ℕ} {S : α → List ℤ} {p : α → ℤ}
    (hk : ComputableInPolyTime k input encNat) (hS : ComputableInPolyTime S input encZ)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a ↦ labelOfCellL (k a) (S a) (p a)) input encUnary := by
  unfold labelOfCellL
  have hb : ComputableInPolyTime (fun x : α × ℤ ↦ x.2) (encPair input encIntBin) encIntBin :=
    snd _ _
  exact (length_list encIntBin).comp (filterWithInput (boundariesL' hk hS)
    (intLt' (intAdd' hb (intAdd' hb (gapL' (hS.comp (fst _ _)) hb)))
      (intMul' (const 2) (hp.comp (fst _ _)))))

theorem clusterL_polytime : ComputableInPolyTime
    (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦
      clusterL p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    (encPair encNat (encPair encRat (encPair encRat (encPair encRat (encPair encUnary
      (encList encRat)))))) (encList encUnary) := by
  unfold clusterL
  set E := encPair encNat (encPair encRat (encPair encRat (encPair encRat (encPair encUnary
      (encList encRat)))))
  have hk : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.1) E encNat := fst _ _
  have hθ : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.2.1) E encRat :=
    (fst _ _).comp (snd _ _)
  have hε : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.2.2.1) E encRat :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hH : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.2.2.2.1) E encRat :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hℓ : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.2.2.2.2.1) E
      encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hz : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦ p.2.2.2.2.2) E
      (encList encRat) :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hh : ComputableInPolyTime (fun p : ℕ × ℚ × ℚ × ℚ × ℕ × List ℚ ↦
      scale p.2.2.2.1 (levelL p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)) E encRat := by
    unfold scale
    exact rat_div' hH (rat_two_pow' (levelL' hθ hε hH hℓ hz))
  have hc := cellsL' hh hz
  exact mapWithInput hc (labelOfCellL' (hk.comp (fst _ _))
    (heavyL' (hθ.comp (fst _ _)) ((length_list encRat).comp (hz.comp (fst _ _)))
      (hc.comp (fst _ _))) (snd _ _))

@[fun_prop]
theorem clusterL' {k ℓmax : α → ℕ} {θ ε H : α → ℚ} {zs : α → List ℚ}
    (hk : ComputableInPolyTime k input encNat) (hθ : ComputableInPolyTime θ input encRat)
    (hε : ComputableInPolyTime ε input encRat) (hH : ComputableInPolyTime H input encRat)
    (hℓ : ComputableInPolyTime ℓmax input encUnary)
    (hz : ComputableInPolyTime zs input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ clusterL (k a) (θ a) (ε a) (H a) (ℓmax a) (zs a)) input
      (encList encUnary) :=
  clusterL_polytime.comp (g := fun a ↦ (k a, θ a, ε a, H a, ℓmax a, zs a))
    (hk.prod (hθ.prod (hε.prod (hH.prod (hℓ.prod hz)))))

end BS23.Colinear.PT
