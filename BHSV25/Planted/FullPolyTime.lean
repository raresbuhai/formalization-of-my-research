module

public import BHSV25.Planted.FullAlg
public import BHSV25.Alg.GridPolyTime

/-!
# The algorithm of Theorem 7.17 in polynomial time

`BHSV25.Planted.fullAlg_polytime`: the algorithm `BHSV25.Planted.fullAlg`, as one machine
reading its parameters `((k, K₀, S, K, B), (a, T, N, B'))` in unary with the graph, runs in
polynomial time. All colors are in unary: the numbers stay at most `k + 1`.

* **Uncoloring and safe recoloring**: each round maps the vertices `0, …, n - 1` with counts over
  the neighbors (`countP`, `any`, `filter`), and `n + 1` rounds of a state whose entries stay at
  most `k` once the first round is done (`BHSV25.Planted.uncolor'`, `BHSV25.Planted.recolor'`).
* **Brute force**: the closure is `n` rounds on membership bits; the tuples are cut at `n²`; the
  search is `find?` over them with a nested `all` (`BHSV25.Planted.brute'`).
* **The list**: as the candidates of the grid clustering, without the rounding
  (`BHSV25.Planted.clusterList'`), then a `flatMap` over the candidates and the degrees `d ≤ n`, and
  the selection of `BHSV25.Alg.bestColoring`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Uncoloring -/

theorem nbrCount' {n k y a : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hy : ComputableInPolyTime y input encUnary) (ha : ComputableInPolyTime a input encUnary) :
    ComputableInPolyTime (fun x ↦ nbrCount (n x) (k x) (adj x) (c x) (y x) (a x)) input
      encUnary := by
  unfold nbrCount
  have hz : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have h1 := Alg.adjBit' (hn.comp hx) (hadj.comp hx) (hy.comp hx) hz
  have h2 := Alg.listGetDWithInput' (hc.comp hx) hz (hk.comp hx)
  have h3 : ComputableInPolyTime (fun p : α × ℕ ↦ decide ((c p.1).getD p.2 (k p.1) = a p.1))
      (encPair input encUnary) encBool := decide_eq' h2 (ha.comp hx)
  have h4 : ComputableInPolyTime (fun p : α × ℕ ↦ Alg.adjBit (n p.1) (adj p.1) (y p.1) p.2 &&
      decide ((c p.1).getD p.2 (k p.1) = a p.1)) (encPair input encUnary) encBool :=
    bool_and' h1 h3
  exact countPWithInput (unary_range' hn) h4

theorem violates' {n k d y : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hy : ComputableInPolyTime y input encUnary) :
    ComputableInPolyTime (fun x ↦ violates (n x) (k x) (d x) (adj x) (c x) (y x)) input
      encBool := by
  unfold violates
  have hcy := Alg.listGetDWithInput' hc hy hk
  have h1 : ComputableInPolyTime (fun x ↦ decide ((c x).getD (y x) (k x) < k x)) input encBool :=
    unary_lt' hcy hk
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have ha : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have h2 : ComputableInPolyTime (fun p : α × ℕ ↦ !decide (p.2 = (c p.1).getD (y p.1) (k p.1)))
      (encPair input encUnary) encBool := bool_not.comp (decide_eq' ha (hcy.comp hx))
  have h3 : ComputableInPolyTime (fun p : α × ℕ ↦
      decide (6 * k p.1 * nbrCount (n p.1) (k p.1) (adj p.1) (c p.1) (y p.1) p.2 < d p.1))
      (encPair input encUnary) encBool :=
    unary_lt' (unary_mul' (unary_mul' (const 6) (hk.comp hx))
      (nbrCount' (hn.comp hx) (hk.comp hx) (hadj.comp hx) (hc.comp hx) (hy.comp hx) ha))
      (hd.comp hx)
  have h4 := anyWithInput (test := fun x a ↦ !decide (a = (c x).getD (y x) (k x)) &&
    decide (6 * k x * nbrCount (n x) (k x) (adj x) (c x) (y x) a < d x))
    (unary_range' hk) (bool_and' h2 h3)
  exact bool_and' h1 h4

/-- The parameters `((n, k, d), a)` of a round. -/
abbrev encRound : ((ℕ × ℕ × ℕ) × List Bool) ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary encUnary)) encBits

theorem uncolorStep_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦
      uncolorStep p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
    (encPair encRound (encList encUnary)) (encList encUnary) := by
  unfold uncolorStep
  set E := encPair encRound (encList encUnary)
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.1.1) E
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hk : ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.1.2.1) E
      encUnary := (fst _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hd : ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.1.2.2) E
      encUnary := (snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  have hadj : ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.2) E
      encBits := (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun p : ((ℕ × ℕ × ℕ) × List Bool) × List ℕ ↦ p.2) E
      (encList encUnary) := snd _ _
  have hx : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List Bool) × List ℕ) × ℕ ↦ q.1)
      (encPair E encUnary) E := fst _ _
  have hy : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List Bool) × List ℕ) × ℕ ↦ q.2)
      (encPair E encUnary) encUnary := snd _ _
  have hv := violates' (hn.comp hx) (hk.comp hx) (hd.comp hx) (hadj.comp hx) (hc.comp hx) hy
  have hg := Alg.listGetDWithInput' (hc.comp hx) hy (hk.comp hx)
  have hbody := ite' hv (hk.comp hx) hg
  exact mapWithInput (unary_range' hn) hbody

/-! ### Bounded iterations -/

theorem le_length_encList_unary {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    v ≤ (encList encUnary l).length := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    rw [encList_cons, List.length_append, Turing.MultiTapeTM.length_frame, encUnary_apply,
      List.length_replicate]
    rcases List.mem_cons.1 hv with rfl | h
    · omega
    · have := ih h; omega

theorem getD_mem_or (c : List ℕ) (y d : ℕ) : c.getD y d ∈ c ∨ c.getD y d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : c[y]? with _ | v
  · right; rfl
  · left; exact List.mem_of_getElem? h

/-- The size of the iterates of a round that keeps `n` entries, each at most `K` or an entry of
its input. -/
theorem length_iterate_le {n K : ℕ} (step : List ℕ → List ℕ)
    (hstep : ∀ c, (step c).length = n ∧ ∀ v ∈ step c, v ≤ K ∨ v ∈ c) (c₀ : List ℕ) (i : ℕ) :
    (encList encUnary (step^[i] c₀)).length ≤
      (encList encUnary c₀).length + n * (2 * (K + (encList encUnary c₀).length) + 1) := by
  have hinv : ∀ i, ∀ v ∈ step^[i] c₀, v ≤ K ∨ v ∈ c₀ := by
    intro i
    induction i with
    | zero => intro v hv; exact Or.inr hv
    | succ i ih =>
      intro v hv
      rw [Function.iterate_succ_apply'] at hv
      rcases (hstep _).2 v hv with h | h
      · exact Or.inl h
      · exact ih v h
  rcases i with _ | i
  · simp
  · have hlen : (step^[i + 1] c₀).length = n := by
      rw [Function.iterate_succ_apply']; exact (hstep _).1
    have hb : ∀ v ∈ step^[i + 1] c₀, (encUnary v).length ≤ K + (encList encUnary c₀).length := by
      intro v hv
      rw [encUnary_apply, List.length_replicate]
      rcases hinv (i + 1) v hv with h | h
      · omega
      · have := le_length_encList_unary h; omega
    have := length_encList_le encUnary _ hb
    rw [hlen] at this
    omega

theorem uncolorStep_props (n k d : ℕ) (adj : List Bool) (c : List ℕ) :
    (uncolorStep n k d adj c).length = n ∧ ∀ v ∈ uncolorStep n k d adj c, v ≤ k ∨ v ∈ c := by
  refine ⟨by simp [uncolorStep], fun v hv ↦ ?_⟩
  rw [uncolorStep, List.mem_map] at hv
  obtain ⟨y, -, rfl⟩ := hv
  split_ifs
  · exact Or.inl le_rfl
  · rcases getD_mem_or c y k with h | h
    · exact Or.inr h
    · exact Or.inl h.le

theorem uncolor' {n k d : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ uncolor (n x) (k x) (d x) (adj x) (c x)) input
      (encList encUnary) := by
  unfold uncolor
  refine iterateWith (par := fun x ↦ ((n x, k x, d x), adj x)) (count := fun x ↦ n x + 1)
    (init := c) (step := fun p c ↦ uncolorStep p.1.1 p.1.2.1 p.1.2.2 p.2 c)
    ((hn.prod (hk.prod hd)).prod hadj) (unary_add' hn (const 1)) hc uncolorStep_polytime
    (bound := fun x ↦ (encList encUnary (c x)).length +
      n x * (2 * (k x + (encList encUnary (c x)).length) + 1)) ?_ ?_
  · exact hc.polyBounded_length.add (hn.polyBounded.mul
      (((PolyBounded.const 2).mul (hk.polyBounded.add hc.polyBounded_length)).add (.const 1)))
  · intro x i _
    exact length_iterate_le _ (uncolorStep_props (n x) (k x) (d x) (adj x)) (c x) i

/-! ### Safe recoloring -/

theorem missing' {n k y : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hy : ComputableInPolyTime y input encUnary) :
    ComputableInPolyTime (fun x ↦ missing (n x) (k x) (adj x) (c x) (y x)) input
      (encList encUnary) := by
  unfold missing
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have ha : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hx2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).comp (fst _ _)
  have ha2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hz2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.2)
      (encPair (encPair input encUnary) encUnary) encUnary := snd _ _
  have h1 := Alg.adjBit' (hn.comp hx2) (hadj.comp hx2) (hy.comp hx2) hz2
  have h2 : ComputableInPolyTime
      (fun q : (α × ℕ) × ℕ ↦ decide ((c q.1.1).getD q.2 (k q.1.1) = q.1.2))
      (encPair (encPair input encUnary) encUnary) encBool :=
    decide_eq' (Alg.listGetDWithInput' (hc.comp hx2) hz2 (hk.comp hx2)) ha2
  have h3 := anyWithInput (test := fun p : α × ℕ ↦ fun z ↦
    Alg.adjBit (n p.1) (adj p.1) (y p.1) z && decide ((c p.1).getD z (k p.1) = p.2))
    (unary_range' (hn.comp hx)) (bool_and' h1 h2)
  exact filterWithInput (test := fun x a ↦ !(List.range (n x)).any fun z ↦
    Alg.adjBit (n x) (adj x) (y x) z && decide ((c x).getD z (k x) = a))
    (unary_range' hk) (bool_not.comp h3)

theorem headD_eq_getD (l : List ℕ) (d : ℕ) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

/-- The parameters `(n, k)` and the table of a round of recoloring. -/
abbrev encRound2 : ((ℕ × ℕ) × List Bool) ↪ List Bool :=
  encPair (encPair encUnary encUnary) encBits

theorem recolorStep_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List Bool) × List ℕ ↦ recolorStep p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair encRound2 (encList encUnary)) (encList encUnary) := by
  unfold recolorStep
  simp only [headD_eq_getD]
  set E := encPair encRound2 (encList encUnary)
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.1.1) E
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hk : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.1.2) E
      encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hadj : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool) × List ℕ ↦ p.1.2) E
      encBits := (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool) × List ℕ ↦ p.2) E
      (encList encUnary) := snd _ _
  have hx : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List Bool) × List ℕ) × ℕ ↦ q.1)
      (encPair E encUnary) E := fst _ _
  have hy : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List Bool) × List ℕ) × ℕ ↦ q.2)
      (encPair E encUnary) encUnary := snd _ _
  have hm := missing' (hn.comp hx) (hk.comp hx) (hadj.comp hx) (hc.comp hx) hy
  have hg := Alg.listGetDWithInput' (hc.comp hx) hy (hk.comp hx)
  have hcond := bool_and' (unary_le' (hk.comp hx) hg)
    (decide_eq' ((length_list encUnary).comp hm) (const 1))
  have hhead := Alg.listGetDWithInput' hm (const 0) (hk.comp hx)
  have hbody := ite' hcond hhead hg
  exact mapWithInput (unary_range' hn) hbody

theorem recolorStep_props (n k : ℕ) (adj : List Bool) (c : List ℕ) :
    (recolorStep n k adj c).length = n ∧ ∀ v ∈ recolorStep n k adj c, v ≤ k ∨ v ∈ c := by
  refine ⟨by simp [recolorStep], fun v hv ↦ ?_⟩
  rw [recolorStep, List.mem_map] at hv
  obtain ⟨y, -, rfl⟩ := hv
  split_ifs
  · left
    rcases hm : missing n k adj c y with _ | ⟨a, l⟩
    · simp
    · have : a ∈ missing n k adj c y := by rw [hm]; exact List.mem_cons_self
      rw [missing, List.mem_filter, List.mem_range] at this
      simp only [List.headD_cons]
      exact this.1.le
  · rcases getD_mem_or c y k with h | h
    · exact Or.inr h
    · exact Or.inl h.le

theorem recolor' {n k : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ recolor (n x) (k x) (adj x) (c x)) input
      (encList encUnary) := by
  unfold recolor
  refine iterateWith (par := fun x ↦ ((n x, k x), adj x)) (count := fun x ↦ n x + 1)
    (init := c) (step := fun p c ↦ recolorStep p.1.1 p.1.2 p.2 c)
    ((hn.prod hk).prod hadj) (unary_add' hn (const 1)) hc recolorStep_polytime
    (bound := fun x ↦ (encList encUnary (c x)).length +
      n x * (2 * (k x + (encList encUnary (c x)).length) + 1)) ?_ ?_
  · exact hc.polyBounded_length.add (hn.polyBounded.mul
      (((PolyBounded.const 2).mul (hk.polyBounded.add hc.polyBounded_length)).add (.const 1)))
  · intro x i _
    exact length_iterate_le _ (recolorStep_props (n x) (k x) (adj x)) (c x) i

/-! ### Brute force -/

/-- The parameters `((n, k), a, c)` of a round of the closure. -/
abbrev encClose : ((ℕ × ℕ) × List Bool × List ℕ) ↪ List Bool :=
  encPair (encPair encUnary encUnary) (encPair encBits (encList encUnary))

theorem closeStep_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦
      closeStep p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2)
    (encPair encClose encBits) encBits := by
  unfold closeStep
  set E := encPair encClose encBits
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦ p.1.1.1) E
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hk : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦ p.1.1.2) E
      encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hadj : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦ p.1.2.1)
      E encBits := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hc : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦ p.1.2.2) E
      (encList encUnary) := (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hs : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool × List ℕ) × List Bool ↦ p.2) E
      encBits := snd _ _
  have hx : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ ↦ q.1)
      (encPair E encUnary) E := fst _ _
  have hy : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ ↦ q.2)
      (encPair E encUnary) encUnary := snd _ _
  set E2 := encPair (encPair E encUnary) encUnary
  have hx2 : ComputableInPolyTime
      (fun r : ((((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ) × ℕ ↦ r.1.1) E2 E :=
    (fst _ _).comp (fst _ _)
  have hy2 : ComputableInPolyTime
      (fun r : ((((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ) × ℕ ↦ r.1.2) E2 encUnary :=
    (snd _ _).comp (fst _ _)
  have hz2 : ComputableInPolyTime
      (fun r : ((((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ) × ℕ ↦ r.2) E2 encUnary :=
    snd _ _
  have hin := bool_and' (bitsGetDWithInput (hs.comp hx2) hz2 false)
    (Alg.adjBit' (hn.comp hx2) (hadj.comp hx2) hz2 hy2)
  have hany := anyWithInput (test := fun q : (((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ ↦
    fun z ↦ q.1.2.getD z false && Alg.adjBit q.1.1.1.1 q.1.1.2.1 z q.2)
    (unary_range' (hn.comp hx)) hin
  have hU := decide_eq' (Alg.listGetDWithInput' (hc.comp hx) hy (hk.comp hx)) (hk.comp hx)
  have hbody : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × List Bool × List ℕ) × List Bool) × ℕ ↦ q.1.2.getD q.2 false ||
        (decide (q.1.1.2.2.getD q.2 q.1.1.1.2 = q.1.1.1.2) &&
          (List.range q.1.1.1.1).any fun z ↦ q.1.2.getD z false && Alg.adjBit q.1.1.1.1
            q.1.1.2.1 z q.2)) (encPair E encUnary) encBool :=
    bool_or.comp ((bitsGetDWithInput (hs.comp hx) hy false).prod (bool_and' hU hany))
  exact mapToBitsWithInput (f := fun p y ↦ p.2.getD y false ||
    (decide (p.1.2.2.getD y p.1.1.2 = p.1.1.2) &&
      (List.range p.1.1.1).any fun z ↦ p.2.getD z false && Alg.adjBit p.1.1.1 p.1.2.1 z y))
    (unary_range' hn) hbody

theorem closure' {n k v : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun x ↦ closure (n x) (k x) (adj x) (c x) (v x)) input encBits := by
  unfold closure
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have hinit : ComputableInPolyTime (fun x ↦ (List.range (n x)).map fun y ↦ decide (y = v x))
      input encBits :=
    mapToBitsWithInput (unary_range' hn) (decide_eq' (snd _ _) (hv.comp hx))
  refine iterateWith (par := fun x ↦ ((n x, k x), adj x, c x)) (count := n)
    (init := fun x ↦ (List.range (n x)).map fun y ↦ decide (y = v x))
    (step := fun p s ↦ closeStep p.1.1 p.1.2 p.2.1 p.2.2 s)
    ((hn.prod hk).prod (hadj.prod hc)) hn hinit closeStep_polytime (bound := n) hn.polyBounded ?_
  intro x i _
  rcases i with _ | i
  · simp
  · rw [Function.iterate_succ_apply', closeStep]
    simp

theorem assignAt' {k z : α → ℕ} {c C σ : α → List ℕ}
    (hk : ComputableInPolyTime k input encUnary)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hC : ComputableInPolyTime C input (encList encUnary))
    (hσ : ComputableInPolyTime σ input (encList encUnary))
    (hz : ComputableInPolyTime z input encUnary) :
    ComputableInPolyTime (fun x ↦ assignAt (k x) (c x) (C x) (σ x) (z x)) input encUnary := by
  unfold assignAt
  exact ite_decide (decide_mem hC hz)
    (Alg.listGetDWithInput' hσ (idxOfWithInput hC hz) (const 0)) (Alg.listGetDWithInput' hc hz hk)

theorem validAssign' {n k : α → ℕ} {adj : α → List Bool} {c C σ : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hC : ComputableInPolyTime C input (encList encUnary))
    (hσ : ComputableInPolyTime σ input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ validAssign (n x) (k x) (adj x) (c x) (C x) (σ x)) input
      encBool := by
  unfold validAssign
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have hu : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hx2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).comp (fst _ _)
  have hu2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hw2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.2)
      (encPair (encPair input encUnary) encUnary) encUnary := snd _ _
  have hA : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦
      !Alg.adjBit (n q.1.1) (adj q.1.1) q.1.2 q.2 ||
        !decide (assignAt (k q.1.1) (c q.1.1) (C q.1.1) (σ q.1.1) q.1.2 =
          assignAt (k q.1.1) (c q.1.1) (C q.1.1) (σ q.1.1) q.2))
      (encPair (encPair input encUnary) encUnary) encBool :=
    bool_or.comp ((bool_not.comp (Alg.adjBit' (hn.comp hx2) (hadj.comp hx2) hu2 hw2)).prod
      (bool_not.comp (decide_eq'
        (assignAt' (hk.comp hx2) (hc.comp hx2) (hC.comp hx2) (hσ.comp hx2) hu2)
        (assignAt' (hk.comp hx2) (hc.comp hx2) (hC.comp hx2) (hσ.comp hx2) hw2))))
  have hin := allWithInput (test := fun p : α × ℕ ↦ fun w ↦
    !Alg.adjBit (n p.1) (adj p.1) p.2 w ||
      !decide (assignAt (k p.1) (c p.1) (C p.1) (σ p.1) p.2 =
        assignAt (k p.1) (c p.1) (C p.1) (σ p.1) w))
    (unary_range' (hn.comp hx)) hA
  exact allWithInput (test := fun x u ↦ (List.range (n x)).all fun w ↦
    !Alg.adjBit (n x) (adj x) u w ||
      !decide (assignAt (k x) (c x) (C x) (σ x) u = assignAt (k x) (c x) (C x) (σ x) w))
    hC hin

theorem getD_map_eq_elim {β : Type} (o : Option β) (f : β → ℕ) (d : ℕ) :
    (o.map f).getD d = o.elim d f := by
  cases o <;> rfl

theorem bruteAt' {n k y : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary))
    (hy : ComputableInPolyTime y input encUnary) :
    ComputableInPolyTime (fun x ↦ bruteAt (n x) (k x) (adj x) (c x) (y x)) input encUnary := by
  unfold bruteAt
  simp only [getD_map_eq_elim]
  have hL : ComputableInPolyTime
      (fun x ↦ Alg.bitsToList (n x) (closure (n x) (k x) (adj x) (c x) (y x))) input
      (encList encUnary) := Alg.bitsToList' hn (closure' hn hk hadj hc hy)
  have hT : ComputableInPolyTime (fun x ↦ Tuples.tuples (n x * n x) (k x)
      (Alg.bitsToList (n x) (closure (n x) (k x) (adj x) (c x) (y x))).length) input
      (encList (encList encUnary)) :=
    Alg.tuplesUnary' (unary_mul' hn hn) hk ((length_list encUnary).comp hL)
  have hx : ComputableInPolyTime (fun p : α × List ℕ ↦ p.1) (encPair input (encList encUnary))
      input := fst _ _
  have hσ : ComputableInPolyTime (fun p : α × List ℕ ↦ p.2) (encPair input (encList encUnary))
      (encList encUnary) := snd _ _
  have hval := validAssign' (hn.comp hx) (hk.comp hx) (hadj.comp hx) (hc.comp hx) (hL.comp hx) hσ
  have hfind := findWithInput (test := fun x σ ↦ validAssign (n x) (k x) (adj x) (c x)
    (Alg.bitsToList (n x) (closure (n x) (k x) (adj x) (c x) (y x))) σ) hT hval
  have hbody : ComputableInPolyTime (fun p : α × List ℕ ↦
      p.2.getD ((Alg.bitsToList (n p.1) (closure (n p.1) (k p.1) (adj p.1) (c p.1)
        (y p.1))).idxOf (y p.1)) 0) (encPair input (encList encUnary)) encUnary :=
    Alg.listGetDWithInput' hσ (idxOfWithInput (hL.comp hx) (hy.comp hx)) (const 0)
  exact optionElimWithInput hfind hk hbody

theorem brute' {n k : α → ℕ} {adj : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ brute (n x) (k x) (adj x) (c x)) input (encList encUnary) := by
  unfold brute
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have hy : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hg := Alg.listGetDWithInput' (hc.comp hx) hy (hk.comp hx)
  have hbody := ite_decide (decide_eq' hg (hk.comp hx))
    (bruteAt' (hn.comp hx) (hk.comp hx) (hadj.comp hx) (hc.comp hx) hy) hg
  exact mapWithInput (unary_range' hn) hbody

/-! ### The algorithm -/

theorem clampK' {n k : α → ℕ} {c : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ clampK (n x) (k x) (c x)) input (encList encUnary) := by
  unfold clampK
  have hx : ComputableInPolyTime (fun p : α × ℕ ↦ p.1) (encPair input encUnary) input := fst _ _
  have hy : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hg := Alg.listGetDWithInput' (hc.comp hx) hy (hk.comp hx)
  exact mapWithInput (unary_range' hn) (ite_decide (unary_lt' hg (hk.comp hx)) hg (const 0))

theorem pipeline' {n k d : α → ℕ} {adj : α → List Bool} {q : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hq : ComputableInPolyTime q input (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ pipeline (n x) (k x) (d x) (adj x) (q x)) input
      (encList encUnary) := by
  unfold pipeline
  have h1 := uncolor' hn hk hd hadj hq
  have h2 := recolor' hn hk hadj h1
  have h3 := brute' hn hk hadj h2
  have h4 := clampK' hn hk h3
  exact Alg.colorOfI' hn hk hk hadj h4

/-- The clusters of one candidate. -/
theorem candC' {n m S K : α → ℕ} {U : α → List (List ℚ)} {is ts : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hS : ComputableInPolyTime S input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hU : ComputableInPolyTime U input (encList (encList encRat)))
    (his : ComputableInPolyTime is input (encList encUnary))
    (hts : ComputableInPolyTime ts input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ Alg.clustersC (n a) ((is a).map fun i ↦ (U a).getD i [])
      (Alg.gridCenters (m a) (S a) (K a) (Nat.sqrt (n a)) (ts a))) input (encList encUnary) := by
  have hus := mapWithInput (f := fun a i ↦ (U a).getD i []) his
    (listGetDWithInput (hU.comp (fst _ _)) (snd input encUnary) [])
  have hr := binary_sqrt' (Alg.toBin' hn)
  have hcs := Alg.gridCenters' hm hS hK hr hts
  exact Alg.clustersC' hn hus hcs

theorem clusterList' {n m S K B : α → ℕ} {U : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hS : ComputableInPolyTime S input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hB : ComputableInPolyTime B input encUnary)
    (hU : ComputableInPolyTime U input (encList (encList encRat))) :
    ComputableInPolyTime (fun a ↦ clusterList (n a) (m a) (S a) (K a) (B a) (U a)) input
      (encList (encList encUnary)) := by
  have hx := fst input (encList encUnary)
  have h2K1 : ComputableInPolyTime (fun a ↦ 2 * K a + 1) input encUnary :=
    unary_add' (unary_mul' (const 2) hK) (const 1)
  have hmm : ComputableInPolyTime (fun a ↦ m a * m a) input encUnary := unary_mul' hm hm
  -- the inner map, over the grids
  have hy := fst (encPair input (encList encUnary)) (encList encUnary)
  have hc := candC' (hn.comp (hx.comp hy)) (hm.comp (hx.comp hy)) (hS.comp (hx.comp hy))
    (hK.comp (hx.comp hy)) (hU.comp (hx.comp hy)) ((snd _ _).comp hy)
    (snd (encPair input (encList encUnary)) (encList encUnary))
  have hin : ComputableInPolyTime (fun p : α × List ℕ ↦
      (Tuples.tuples (B p.1) (2 * K p.1 + 1) (m p.1 * m p.1)).map fun ts ↦
        Alg.clustersC (n p.1) (p.2.map fun i ↦ (U p.1).getD i [])
          (Alg.gridCenters (m p.1) (S p.1) (K p.1) (Nat.sqrt (n p.1)) ts))
      (encPair input (encList encUnary)) (encList (encList encUnary)) :=
    mapWithInput (f := fun (p : α × List ℕ) ts ↦ Alg.clustersC (n p.1)
      (p.2.map fun i ↦ (U p.1).getD i [])
      (Alg.gridCenters (m p.1) (S p.1) (K p.1) (Nat.sqrt (n p.1)) ts))
      (Alg.tuplesUnary' (hB.comp hx) (h2K1.comp hx) (hmm.comp hx)) hc
  have htup : ComputableInPolyTime (fun a ↦ Tuples.tuples (B a) (U a).length (m a)) input
      (encList (encList encUnary)) :=
    Alg.tuplesUnary' hB ((length_list (encList encRat)).comp hU) hm
  unfold clusterList
  exact flatMapWithInput htup hin

/-- **The algorithm of Theorem 7.17 runs in polynomial time**, reading its parameters in unary
with the graph. -/
theorem fullAlg_polytime : ComputableInPolyTime
    (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ fullAlg z.1 z.2)
    (encPair Alg.encExpPar (encPair encNat encBits)) encColoring := by
  set E := encPair Alg.encExpPar (encPair encNat encBits)
  have hp1 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.1) E
      Alg.encGridPar := (fst _ _).comp (fst _ _)
  have hp2 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.2) E
      Net.encGSPar := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.2) E
      (encPair encNat encBits) := snd _ _
  have hm := (fst _ _).comp hp1
  have hS := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hp1))
  have hK := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp1)))
  have hB := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp1)))
  have hn := Alg.numV_polytime.comp hx
  have hadj := (snd encNat encBits).comp hx
  have hU := Alg.expNet_polytime.comp (hp2.prod hx)
  have hL := clusterList' hn hm hS hK hB hU
  -- the results of the steps, for every candidate and degree
  have hz := fst E (encList encUnary)
  have hz2 := fst (encPair E (encList encUnary)) encUnary
  have hpipe := pipeline' (hn.comp (hz.comp hz2)) (hm.comp (hz.comp hz2))
    (snd (encPair E (encList encUnary)) encUnary) (hadj.comp (hz.comp hz2))
    ((snd _ _).comp hz2)
  have hin : ComputableInPolyTime (fun p : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) ×
      (ℕ × List Bool)) × List ℕ ↦ (List.range (Alg.numV p.1.2 + 1)).map fun d ↦
        pipeline (Alg.numV p.1.2) p.1.1.1.1 d p.1.2.2 p.2)
      (encPair E (encList encUnary)) (encList (encList encUnary)) :=
    mapWithInput (f := fun (p : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) ×
      (ℕ × List Bool)) × List ℕ) d ↦ pipeline (Alg.numV p.1.2) p.1.1.1.1 d p.1.2.2 p.2)
      (unary_range' (unary_add' (hn.comp hz) (const 1))) hpipe
  have hall := flatMapWithInput (f := fun (z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) ×
      (ℕ × List Bool)) q ↦ (List.range (Alg.numV z.2 + 1)).map fun d ↦
        pipeline (Alg.numV z.2) z.1.1.1 d z.2.2 q) hL hin
  have hbest := Alg.bestColoringI' hn hm hall
  have key := Alg.unaryList_to_binary.comp hbest
  unfold fullAlg
  exact key

end Planted

end BHSV25
