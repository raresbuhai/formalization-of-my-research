module

public import BHSV25.BK.Copies
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# The reduction runs in polynomial time

`BHSV25.BK.Prm.reduce_polytime`: for fixed parameters, the reduction `BHSV25.BK.Prm.reduce` is
computable in polynomial time from the encoded Unique Games instance to the encoded graph.

The output is the number of vertices `k₀ N` and the adjacency table, whose entry for two vertex
numbers is computed from their digits (`BHSV25.BK.Prm.rv`) by list functions
(`BHSV25.BK.Mach.tableB`, `BHSV25.BK.Mach.adjTable_copies`); each piece is certified with
complexitylib's list and number rules, as in `BGHKLMM26/Hardness/MachineList.lean` (whose helper
lemmas `toBinary'`, `binMod'`, `lengthL'`, `nbrs'` are copied here). The entries of the
permutation tables are only used as indices into lists of `R` digits. Every length is polynomial:
`N = M^R 2^R L^t m'` with `L ≤ |cs|` and `m' = min(m, |cs|)`, and `t, R, M, k₀` are constants.
-/

@[expose] public section

namespace BHSV25.BK.Mach

open UniqueGames Turing.MultiTapeTM ComputableInPolyTime

/-- A constraint. -/
abbrev encC : UGConstraint ↪ List Bool := encPair (encPair encNat encNat) (encList encNat)

/-- An instance. -/
abbrev encU : UGInstance ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encList encC)))

theorem encUG_eq : encUG = encU := rfl

/-- The digits of a vertex. -/
abbrev encRV : RV ↪ List Bool :=
  encPair encNat (encPair (encList encNat) (encPair (encList encBool) (encList encNat)))

variable {α : Type} {input : α ↪ List Bool}

/-! ### Helpers (from BGHKLMM26) -/

theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

theorem binMod' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a % g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mod' hf.tidy hg.tidy)

theorem binDiv' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a / g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_div' hf.tidy hg.tidy)

theorem lengthL' {β : Type} {enc : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l input (encList enc)) :
    ComputableInPolyTime (fun a ↦ (l a).length) input encUnary :=
  (length_list enc).comp hl

theorem nbrs' {cs : α → List UGConstraint} {u : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ nbrs (cs a) (u a)) input (encList encC) := by
  unfold nbrs
  have h1 : ComputableInPolyTime (fun p : α × UGConstraint ↦ p.2.1.1) (encPair input encC)
      encNat := by
    fun_prop
  exact filterWithInput (test := fun a c ↦ decide (c.1.1 = u a)) hcs
    (decide_eq' h1 (hu.comp (fst _ _)))

/-! ### The digits of a vertex -/

theorem rv' (P : Prm) {m L x : α → ℕ} (hm : ComputableInPolyTime m input encNat)
    (hL : ComputableInPolyTime L input encNat) (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a ↦ P.rv (m a) (L a) (x a)) input encRV := by
  unfold Prm.rv
  have hxm := binDiv' hx hm
  have hLt := binary_pow' hL (const (encIn := input) P.t)
  have hy := binDiv' hxm hLt
  have h2R : ComputableInPolyTime (fun _ : α ↦ 2 ^ P.R) input encNat := const _
  have hj : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    snd _ _
  have hks := mapWithInput (list := fun _ ↦ List.range P.t)
    (f := fun a p ↦ x a / m a % L a ^ P.t / L a ^ p % L a) (const _)
    (binMod' (binDiv' (binMod' (hxm.comp (fst _ _)) (hLt.comp (fst _ _)))
      (binary_pow' (hL.comp (fst _ _)) hj)) (hL.comp (fst _ _)))
  have hzs := mapWithInput (list := fun _ ↦ List.range P.R)
    (f := fun a j ↦ decide (x a / m a / L a ^ P.t % 2 ^ P.R / 2 ^ j % 2 = 1)) (const _)
    (decide_eq' (binMod' (binDiv' (binMod' (hy.comp (fst _ _)) (h2R.comp (fst _ _)))
      (binary_pow' (const 2) hj)) (const 2)) (const 1))
  have has := mapWithInput (list := fun _ ↦ List.range P.R)
    (f := fun a j ↦ x a / m a / L a ^ P.t / 2 ^ P.R / P.M ^ j % P.M) (const _)
    (binMod' (binDiv' (binDiv' (hy.comp (fst _ _)) (h2R.comp (fst _ _)))
      (binary_pow' (const P.M) hj)) (const P.M))
  exact (binMod' hx hm).prod (hks.prod (hzs.prod has))

/-! ### Conflicts -/

theorem conAt' {cs : α → List UGConstraint} {r : α → RV} {p : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ conAt (cs a) (r a) (p a)) input encC := by
  unfold conAt
  have h1 : ComputableInPolyTime (fun a ↦ (r a).1) input encNat := by fun_prop
  have h2 : ComputableInPolyTime (fun a ↦ (r a).2.1) input (encList encNat) := by fun_prop
  exact listGetD_binary default (nbrs' hcs h1) (listGetDWithInput h2 hp 0)

theorem jAt' {cs : α → List UGConstraint} {r : α → RV} {p i : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hp : ComputableInPolyTime p input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ jAt (cs a) (r a) (p a) (i a)) input encNat := by
  unfold jAt
  have hc := conAt' hcs hr hp
  have h2 : ComputableInPolyTime (fun a ↦ (conAt (cs a) (r a) (p a)).2) input (encList encNat) :=
    (snd _ _).comp hc
  exact listGetDWithInput h2 hi 0

theorem fixedAt' {cs : α → List UGConstraint} {r : α → RV} {p i : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hp : ComputableInPolyTime p input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ fixedAt (cs a) (r a) (p a) (i a)) input encBool := by
  unfold fixedAt
  have h2 : ComputableInPolyTime (fun a ↦ (r a).2.2.2) input (encList encNat) := by fun_prop
  exact bne (listGetD_binary (encA := encNat) 0 h2 (jAt' hcs hr hp hi)) (const 0)

theorem zAt' {cs : α → List UGConstraint} {r : α → RV} {p i : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hp : ComputableInPolyTime p input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ zAt (cs a) (r a) (p a) (i a)) input encBool := by
  unfold zAt
  have h2 : ComputableInPolyTime (fun a ↦ (r a).2.2.1) input (encList encBool) := by fun_prop
  exact listGetD_binary (encA := encBool) false h2 (jAt' hcs hr hp hi)

theorem clash' (P : Prm) {cs : α → List UGConstraint} {r r' : α → RV} {p q : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hr' : ComputableInPolyTime r' input encRV)
    (hp : ComputableInPolyTime p input encUnary) (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a ↦ P.clash (cs a) (r a) (r' a) (p a) (q a)) input encBool := by
  unfold Prm.clash
  have hc := conAt' hcs hr hp
  have hc' := conAt' hcs hr' hq
  have hv : ComputableInPolyTime (fun a ↦ (conAt (cs a) (r a) (p a)).1.2) input encNat :=
    (snd _ _).comp ((fst _ _).comp hc)
  have hv' : ComputableInPolyTime (fun a ↦ (conAt (cs a) (r' a) (q a)).1.2) input encNat :=
    (snd _ _).comp ((fst _ _).comp hc')
  have hcs1 := hcs.comp (fst input encUnary)
  have hr1 := hr.comp (fst input encUnary)
  have hr1' := hr'.comp (fst input encUnary)
  have hp1 := hp.comp (fst input encUnary)
  have hq1 := hq.comp (fst input encUnary)
  have hi : ComputableInPolyTime (fun x : α × ℕ ↦ x.2) (encPair input encUnary) encUnary :=
    snd _ _
  have htest := bool_or.comp ((bool_not.comp (bool_and' (fixedAt' hcs1 hr1 hp1 hi)
    (fixedAt' hcs1 hr1' hq1 hi))).prod (bne (zAt' hcs1 hr1 hp1 hi) (zAt' hcs1 hr1' hq1 hi)))
  exact bool_and' (decide_eq' hv hv') (allWithInput (list := fun _ ↦ List.range P.R)
    (test := fun a i ↦ !(fixedAt (cs a) (r a) (p a) i && fixedAt (cs a) (r' a) (q a) i) ||
      (zAt (cs a) (r a) (p a) i != zAt (cs a) (r' a) (q a) i)) (const _) htest)

theorem conflict' (P : Prm) {cs : α → List UGConstraint} {r r' : α → RV}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encRV) (hr' : ComputableInPolyTime r' input encRV) :
    ComputableInPolyTime (fun a ↦ P.conflict (cs a) (r a) (r' a)) input encBool := by
  unfold Prm.conflict
  have hin : ComputableInPolyTime (fun x : (α × ℕ) × ℕ ↦ x.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).comp (fst _ _)
  have hp : ComputableInPolyTime (fun x : (α × ℕ) × ℕ ↦ x.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hq : ComputableInPolyTime (fun x : (α × ℕ) × ℕ ↦ x.2)
      (encPair (encPair input encUnary) encUnary) encUnary := snd _ _
  have hinner := clash' P (hcs.comp hin) (hr.comp hin) (hr'.comp hin) hp hq
  exact anyWithInput (list := fun _ ↦ List.range P.t) (const _)
    (anyWithInput (list := fun _ ↦ List.range P.t) (const _) hinner)

/-! ### The adjacency table -/

/-- The adjacency bit of the vertices numbered `a` and `b` in the copies: same copy, distinct
vertices, and a conflict in either order. -/
def adjB (P : Prm) (cs : List UGConstraint) (m L a b : ℕ) : Bool :=
  decide (a / P.nV m L = b / P.nV m L) && (decide (a % P.nV m L ≠ b % P.nV m L) &&
    (P.conflict cs (P.rv m L (a % P.nV m L)) (P.rv m L (b % P.nV m L)) ||
      P.conflict cs (P.rv m L (b % P.nV m L)) (P.rv m L (a % P.nV m L))))

/-- The adjacency table of the copies, computed on lists. -/
def tableB (P : Prm) (cs : List UGConstraint) (m L : ℕ) : List Bool :=
  (List.range (P.k₀ * P.nV m L * (P.k₀ * P.nV m L))).map fun k ↦
    adjB P cs m L (k / (P.k₀ * P.nV m L)) (k % (P.k₀ * P.nV m L))

theorem decide_eq_of_iff {p : Prop} (i : Decidable p) {b : Bool} (h : p ↔ b = true) :
    @decide p i = b := by
  cases i <;> cases b <;> simp_all

/-- **The adjacency table of the copies, on lists.** -/
theorem adjTable_copies (P : Prm) (cs : List UGConstraint) (m L : ℕ) :
    adjTable (copies (P.baseGraph cs m L) P.k₀) = tableB P cs m L := by
  unfold adjTable tableB
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  apply decide_eq_of_iff
  simp only [adjB, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat, SimpleGraph.fromRel_adj,
    Fin.ext_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]

/-- The encoded output of the reduction: the number of vertices and the adjacency table. -/
noncomputable def redOut (P : Prm) (G : UGInstance) : ℕ × List Bool :=
  if decide (Prm.ldeg G.2.2.2 = 0) then (P.k₀ * P.s, adjTable (copies (clique P.s) P.k₀))
  else (P.k₀ * P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2),
    tableB P G.2.2.2 (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2))

/-- The encoded output of the reduction. -/
theorem encGraph_reduce (P : Prm) (G : UGInstance) :
    encGraph (P.reduce G) = encPair encNat encBits (redOut P G) := by
  unfold Prm.reduce redOut
  by_cases h : Prm.ldeg G.2.2.2 = 0
  · simp only [h, ↓reduceIte, decide_true]
    rfl
  · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true]
    change encPair encNat encBits (_, adjTable _) = _
    rw [adjTable_copies]

theorem redOut_polytime (P : Prm) :
    ComputableInPolyTime (redOut P) encU (encPair encNat encBits) := by
  unfold redOut
  have hcs : ComputableInPolyTime (fun G : UGInstance ↦ G.2.2.2) encU (encList encC) := by
    fun_prop
  have hm : ComputableInPolyTime (fun G : UGInstance ↦ G.1) encU encNat := by fun_prop
  have hmin := binary_min_unary' (lengthL' hcs) hm
  simp only [min_comm (List.length _)] at hmin
  have hL : ComputableInPolyTime (fun G : UGInstance ↦ Prm.ldeg G.2.2.2) encU encUnary :=
    lengthL' (nbrs' hcs (const 0))
  have hN : ComputableInPolyTime (fun G : UGInstance ↦
      P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2)) encU encUnary :=
    unary_mul' (unary_mul' (const _) ((unary_pow P.t).comp hL)) hmin
  have hNf : ComputableInPolyTime (fun G : UGInstance ↦
      P.k₀ * P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2)) encU encUnary :=
    unary_mul' (const _) hN
  -- the entries of the table
  have hG1 : ComputableInPolyTime (fun x : UGInstance × ℕ ↦ x.1) (encPair encU encUnary) encU :=
    fst _ _
  have hk : ComputableInPolyTime (fun x : UGInstance × ℕ ↦ x.2) (encPair encU encUnary)
      encUnary := snd _ _
  have hN1 := hN.comp hG1
  have hNf1 := hNf.comp hG1
  have ha : ComputableInPolyTime (fun x : UGInstance × ℕ ↦
      x.2 / (P.k₀ * P.nV (min x.1.1 x.1.2.2.2.length) (Prm.ldeg x.1.2.2.2)))
      (encPair encU encUnary) encUnary := unary_div.comp (hk.prod hNf1)
  have hb : ComputableInPolyTime (fun x : UGInstance × ℕ ↦
      x.2 % (P.k₀ * P.nV (min x.1.1 x.1.2.2.2.length) (Prm.ldeg x.1.2.2.2)))
      (encPair encU encUnary) encUnary := unary_mod.comp (hk.prod hNf1)
  have hdiv := fun {f : UGInstance × ℕ → ℕ}
      (hf : ComputableInPolyTime f (encPair encU encUnary) encUnary) ↦
    unary_div.comp (hf.prod hN1)
  have hmod := fun {f : UGInstance × ℕ → ℕ}
      (hf : ComputableInPolyTime f (encPair encU encUnary) encUnary) ↦
    unary_mod.comp (hf.prod hN1)
  have hcs1 := hcs.comp hG1
  have hm1 := toBinary' (hmin.comp hG1)
  have hL1 := toBinary' (hL.comp hG1)
  have hra := rv' P hm1 hL1 (toBinary' (hmod ha))
  have hrb := rv' P hm1 hL1 (toBinary' (hmod hb))
  have hentry := bool_and' (decide_eq' (hdiv ha) (hdiv hb))
    (bool_and' (decide_not (decide_eq' (hmod ha) (hmod hb)))
      (bool_or.comp ((conflict' P hcs1 hra hrb).prod (conflict' P hcs1 hrb hra))))
  have htab := mapWithInput
    (list := fun G : UGInstance ↦ List.range (P.k₀ * P.nV (min G.1 G.2.2.2.length)
      (Prm.ldeg G.2.2.2) * (P.k₀ * P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2))))
    (f := fun G k ↦ adjB P G.2.2.2 (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2)
      (k / (P.k₀ * P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2)))
      (k % (P.k₀ * P.nV (min G.1 G.2.2.2.length) (Prm.ldeg G.2.2.2))))
    (unary_range' (unary_mul' hNf hNf)) hentry
  exact ite' (decide_eq' hL (const 0)) (const _) ((toBinary' hNf).prod (listToBits.comp htab))

end BHSV25.BK.Mach

namespace BHSV25.BK

open UniqueGames Turing.MultiTapeTM

/-- **The reduction runs in polynomial time.** -/
theorem Prm.reduce_polytime (P : Prm) : ComputableInPolyTime P.reduce encUG encGraph := by
  rw [Mach.encUG_eq]
  exact (Mach.redOut_polytime P).of_enc_eq (Mach.encGraph_reduce P)

end BHSV25.BK
