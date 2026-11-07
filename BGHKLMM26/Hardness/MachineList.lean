module

public import BGHKLMM26.Hardness.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# The reduction runs in polynomial time: the pieces

List forms of the decoder of one sampled edge (`BGHKLMM26.Hard.Mach.edgeOfBlock_eq`) and of the
adjacency table of the output graph (`BGHKLMM26.Hard.Mach.adjTable_graphOf`), and polynomial-time
certificates for every piece of the reduction `BGHKLMM26.Hard.reduce`, ending with
`BGHKLMM26.Hard.Mach.reduce_polytime'` and `BGHKLMM26.Hard.Mach.coinCount_polytime'`.

Encodings: numbers in binary, except the lengths, counts and indices into the coins, which are in
unary; the sampled and kept edges are lists of pairs of binary numbers; the output is the number of
vertices in binary and the adjacency table as a bit string (`BGHKLMM26.encGraph`).
-/

@[expose] public section

namespace BGHKLMM26.Hard.Mach

open UniqueGames

open OAI.MaxCutGames.Foundations.Hastad
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### List forms -/

/-- `bitsVal` is complexitylib's `ofBits` (least significant bit first). -/
theorem bitsVal_eq_ofBits : bitsVal = Turing.MultiTapeTM.ofBits := by
  funext l
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [bitsVal, Turing.MultiTapeTM.ofBits, List.foldr_cons] at ih ⊢
    rw [ih]
    cases b
    · simp [Nat.bit]
    · simp [Nat.bit]; omega

theorem getD_ofFn_cube {R : ℕ} (x : Cube (Fin R)) (a : ℕ) :
    (List.ofFn x).getD a false = if h : a < R then x ⟨a, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `π x` as a list: `(π x)ⱼ = x[π(j)]`, `false` past the end. -/
theorem ofFn_permCube {R : ℕ} (π : List ℕ) (x : Cube (Fin R)) :
    List.ofFn (permCube π x) =
      (List.range R).map fun j ↦ (List.ofFn x).getD (π.getD j 0) false := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, permCube, getD_ofFn_cube]

theorem ofFn_eq_range_map {R : ℕ} (f : ℕ → Bool) :
    List.ofFn (fun i : Fin R ↦ f i) = (List.range R).map f := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

/-- The point `x` of a block, as a list. -/
def xsOf (R t : ℕ) (blk : List Bool) : List Bool :=
  (List.range R).map fun i ↦ blk.getD (2 * t + i) false

/-- The number `zᵢ` of a block. -/
def zOf (R b t : ℕ) (blk : List Bool) (i : ℕ) : ℕ :=
  bitsVal (((blk.drop (2 * t + R)).drop (i * b)).take b)

/-- The point `y` of a block, as a list. -/
def ysOf (R b q t : ℕ) (blk : List Bool) : List Bool :=
  (List.range R).map fun i ↦ xor (blk.getD (2 * t + i) false) (decide (zOf R b t blk i < q))

/-- The index of `π x` for a point given as a list. -/
def permVal (R : ℕ) (π : List ℕ) (xs : List Bool) : ℕ :=
  bitsVal ((List.range R).map fun j ↦ xs.getD (π.getD j 0) false)

/-- The first constraint of an edge. -/
def con1 (cs : List UGConstraint) (r : ℕ) : UGConstraint := cs.getD (r % cs.length) default

/-- The second constraint of an edge. -/
def con2 (cs : List UGConstraint) (u r : ℕ) : UGConstraint :=
  (nbrs cs u).getD (r % (nbrs cs u).length) default

/-- The bits of an index. -/
def tOf (P : Prm) (cs : List UGConstraint) : ℕ := 2 * cs.length + P.R + P.Δ

/-- The edge of a block, computed on lists. -/
def edgeL (P : Prm) (cs : List UGConstraint) (blk : List Bool) : ℕ × ℕ :=
  ((con1 cs (bitsVal (blk.take (tOf P cs)))).1.2 * 2 ^ P.R +
      permVal P.R (con1 cs (bitsVal (blk.take (tOf P cs)))).2 (xsOf P.R (tOf P cs) blk),
    (con2 cs (con1 cs (bitsVal (blk.take (tOf P cs)))).1.1
        (bitsVal ((blk.drop (tOf P cs)).take (tOf P cs)))).1.2 * 2 ^ P.R +
      permVal P.R (con2 cs (con1 cs (bitsVal (blk.take (tOf P cs)))).1.1
        (bitsVal ((blk.drop (tOf P cs)).take (tOf P cs)))).2 (ysOf P.R P.b P.q (tOf P cs) blk))

/-- **The decoder of an edge, on lists.** -/
theorem edgeOfBlock_eq (P : Prm) (G : UGInstance) (blk : List Bool) :
    edgeOfBlock P G blk = edgeL P G.2.2.2 blk := by
  unfold edgeOfBlock edgeOf edgeL vtx cubeIdx permVal con1 con2
  simp only [ofFn_permCube]
  rw [ofFn_eq_range_map (R := P.R) (fun i ↦ blk.getD (2 * P.tBits G + i) false)]
  rw [ofFn_eq_range_map (R := P.R) (fun i ↦ xor (blk.getD (2 * P.tBits G + i) false)
    (decide (bitsVal (((blk.drop (2 * P.tBits G + P.R)).drop (i * P.b)).take P.b) < P.q)))]
  rfl

/-! ### Certificates -/

/-- A constraint. -/
abbrev encC : UGConstraint ↪ List Bool := encPair (encPair encNat encNat) (encList encNat)

/-- An instance. -/
abbrev encU : UGInstance ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encList encC)))

theorem encUG_eq : encUG = encU := rfl

/-- An edge. -/
abbrev encE : ℕ × ℕ ↪ List Bool := encPair encNat encNat

variable {α : Type} {input : α ↪ List Bool}

theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

theorem binMod' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a % g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mod' hf.tidy hg.tidy)

theorem binAdd' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hf.tidy hg.tidy)

/-- The value of a computed bit string, in binary. -/
theorem bitsVal' {l : α → List Bool} (hl : ComputableInPolyTime l input encBits) :
    ComputableInPolyTime (fun a ↦ bitsVal (l a)) input encNat := by
  rw [bitsVal_eq_ofBits]
  exact .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hl.tidy)

theorem bitsValL' {l : α → List Bool} (hl : ComputableInPolyTime l input (encList encBool)) :
    ComputableInPolyTime (fun a ↦ bitsVal (l a)) input encNat :=
  bitsVal' (listToBits.comp hl)

theorem lengthL' {β : Type} {enc : β ↪ List Bool} {l : α → List β}
    (hl : ComputableInPolyTime l input (encList enc)) :
    ComputableInPolyTime (fun a ↦ (l a).length) input encUnary :=
  (length_list enc).comp hl

theorem xsOf' (R : ℕ) {t : α → ℕ} {blk : α → List Bool}
    (ht : ComputableInPolyTime t input encUnary) (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ xsOf R (t a) (blk a)) input (encList encBool) := by
  unfold xsOf
  have hi : ComputableInPolyTime (fun p : α × ℕ ↦ 2 * t p.1 + p.2) (encPair input encUnary)
      encUnary := by
    have := ht.comp (fst input encUnary)
    fun_prop
  exact mapWithInput (list := fun _ ↦ List.range R)
    (f := fun a i ↦ (blk a).getD (2 * t a + i) false)
    (const _) (bitsGetDWithInput (hb.comp (fst _ _)) hi false)

theorem zOf' (R b : ℕ) {t i : α → ℕ} {blk : α → List Bool}
    (ht : ComputableInPolyTime t input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ zOf R b (t a) (blk a) (i a)) input encNat := by
  unfold zOf
  have h1 : ComputableInPolyTime (fun a ↦ 2 * t a + R) input encUnary := by fun_prop
  have h2 : ComputableInPolyTime (fun a ↦ i a * b) input encUnary := by fun_prop
  exact bitsVal' (bitsTakeWithInput (bitsDropWithInput (bitsDropWithInput hb h1) h2) (const b))

theorem ysOf' (R b q : ℕ) {t : α → ℕ} {blk : α → List Bool}
    (ht : ComputableInPolyTime t input encUnary) (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ ysOf R b q (t a) (blk a)) input (encList encBool) := by
  unfold ysOf
  have ht1 := ht.comp (fst input encUnary)
  have hb1 := hb.comp (fst input encUnary)
  have hi : ComputableInPolyTime (fun p : α × ℕ ↦ 2 * t p.1 + p.2) (encPair input encUnary)
      encUnary := by fun_prop
  have hg := bitsGetDWithInput hb1 hi false
  have hz := zOf' R b ht1 (snd input encUnary) hb1
  have hlt := binary_lt' hz (const (encIn := encPair input encUnary) q)
  exact mapWithInput (list := fun _ ↦ List.range R)
    (f := fun a i ↦ xor ((blk a).getD (2 * t a + i) false) (decide (zOf R b (t a) (blk a) i < q)))
    (const _) (bool_xor.comp (hg.prod hlt))

theorem permVal' (R : ℕ) {π : α → List ℕ} {xs : α → List Bool}
    (hπ : ComputableInPolyTime π input (encList encNat))
    (hxs : ComputableInPolyTime xs input (encList encBool)) :
    ComputableInPolyTime (fun a ↦ permVal R (π a) (xs a)) input encNat := by
  unfold permVal
  have hj := listGetDWithInput (hπ.comp (fst input encUnary)) (snd input encUnary) 0
  have hg := listGetD_binary (encA := encBool) false (hxs.comp (fst input encUnary)) hj
  exact bitsValL' (mapWithInput (list := fun _ ↦ List.range R)
    (f := fun a j ↦ (xs a).getD ((π a).getD j 0) false) (const _) hg)

theorem con1' {cs : α → List UGConstraint} {r : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun a ↦ con1 (cs a) (r a)) input encC := by
  unfold con1
  exact listGetD_binary default hcs (binMod' hr (toBinary' (lengthL' hcs)))

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

theorem con2' {cs : α → List UGConstraint} {u r : α → ℕ}
    (hcs : ComputableInPolyTime cs input (encList encC)) (hu : ComputableInPolyTime u input encNat)
    (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun a ↦ con2 (cs a) (u a) (r a)) input encC := by
  unfold con2
  have hn := nbrs' hcs hu
  exact listGetD_binary default hn (binMod' hr (toBinary' (lengthL' hn)))

theorem tOf' (P : Prm) {cs : α → List UGConstraint}
    (hcs : ComputableInPolyTime cs input (encList encC)) :
    ComputableInPolyTime (fun a ↦ tOf P (cs a)) input encUnary := by
  unfold tOf
  have := lengthL' hcs
  fun_prop

/-- The edge of a computed block, for computed constraints. -/
theorem edgeL' (P : Prm) {cs : α → List UGConstraint} {blk : α → List Bool}
    (hcs : ComputableInPolyTime cs input (encList encC))
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ edgeL P (cs a) (blk a)) input encE := by
  unfold edgeL
  have ht := tOf' P hcs
  have hr1 := bitsVal' (bitsTakeWithInput hb ht)
  have hr2 := bitsVal' (bitsTakeWithInput (bitsDropWithInput hb ht) ht)
  have hc1 := con1' hcs hr1
  have hu : ComputableInPolyTime
      (fun a ↦ (con1 (cs a) (bitsVal ((blk a).take (tOf P (cs a))))).1.1) input encNat := by
    fun_prop
  have hc2 := con2' hcs hu hr2
  have hpow : ComputableInPolyTime (fun _ : α ↦ 2 ^ P.R) input encNat := const _
  exact (binAdd' (binary_mul' (by fun_prop) hpow)
      (permVal' P.R (by fun_prop) (xsOf' P.R ht hb))).prod
    (binAdd' (binary_mul' (by fun_prop) hpow)
      (permVal' P.R (by fun_prop) (ysOf' P.R P.b P.q ht hb)))

/-- **The decoder of an edge runs in polynomial time.** -/
theorem edgeOfBlock' (P : Prm) {G : α → UGInstance} {blk : α → List Bool}
    (hG : ComputableInPolyTime G input encU)
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ edgeOfBlock P (G a) (blk a)) input encE := by
  simp only [edgeOfBlock_eq]
  exact edgeL' P (by fun_prop) hb

/-! ### The greedy simplification -/

theorem contains_eq_decide (l : List (ℕ × ℕ)) (e : ℕ × ℕ) : l.contains e = decide (e ∈ l) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]

theorem contains' {l : α → List (ℕ × ℕ)} {e : α → ℕ × ℕ}
    (hl : ComputableInPolyTime l input (encList encE)) (he : ComputableInPolyTime e input encE) :
    ComputableInPolyTime (fun a ↦ (l a).contains (e a)) input encBool := by
  simp only [contains_eq_decide]
  exact decide_mem hl he

theorem degIn' {l : α → List (ℕ × ℕ)} {u : α → ℕ}
    (hl : ComputableInPolyTime l input (encList encE)) (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ degIn (l a) (u a)) input encUnary := by
  unfold degIn
  have h1 : ComputableInPolyTime (fun p : α × (ℕ × ℕ) ↦ p.2.1) (encPair input encE) encNat := by
    fun_prop
  have h2 : ComputableInPolyTime (fun p : α × (ℕ × ℕ) ↦ p.2.2) (encPair input encE) encNat := by
    fun_prop
  have hu1 := hu.comp (fst input encE)
  exact lengthL' (filterWithInput (test := fun a p ↦ decide (p.1 = u a ∨ p.2 = u a)) hl
    (decide_or (decide_eq' h1 hu1) (decide_eq' h2 hu1)))

/-- The pair encoding of a step of the greedy simplification. -/
abbrev encKE : List (ℕ × ℕ) × (ℕ × ℕ) ↪ List Bool := encPair (encList encE) encE

theorem keepOK_polytime (Δ : ℕ) :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ keepOK Δ p.1 p.2) encKE encBool := by
  unfold keepOK
  have hl : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ p.1) encKE (encList encE) :=
    fst _ _
  have he : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2) encKE encE := snd _ _
  have h1 : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.1) encKE encNat := by
    fun_prop
  have h2 : ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.2) encKE encNat := by
    fun_prop
  have hne := decide_not (decide_eq' h1 h2)
  have hc1 := bool_not.comp (contains' hl he)
  have hc2 := bool_not.comp (contains' hl (h2.prod h1))
  have hd1 := unary_lt' (degIn' hl h1) (const (encIn := encKE) Δ)
  have hd2 := unary_lt' (degIn' hl h2) (const (encIn := encKE) Δ)
  exact bool_and' (bool_and' (bool_and' (bool_and' hne hc1) hc2) hd1) hd2

/-- One step of the greedy simplification. -/
theorem keepStep_polytime (Δ : ℕ) :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) ↦ keepStep Δ p.1 p.2) encKE
      (encList encE) := by
  unfold keepStep
  exact ite' (keepOK_polytime Δ) (snoc encE) (fst _ _)

/-- The kept edges are a sublist of the sampled ones. -/
theorem foldl_keepStep_sublist (Δ : ℕ) (l acc : List (ℕ × ℕ)) :
    (l.foldl (keepStep Δ) acc).Sublist (acc ++ l) := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    unfold keepStep
    split_ifs
    · simp
    · exact List.Sublist.append_left (List.sublist_cons_self e l) acc

theorem length_encList_sublist {β : Type} (enc : β ↪ List Bool) {l₁ l₂ : List β}
    (h : l₁.Sublist l₂) : (encList enc l₁).length ≤ (encList enc l₂).length := by
  rw [length_encList, length_encList]
  exact (h.map _).sum_le_sum fun _ _ ↦ Nat.zero_le _

/-- **The greedy simplification runs in polynomial time**: its states are sublists of the
sampled edges, so their encodings are no longer. -/
theorem keptEdges' (Δ : ℕ) {es : α → List (ℕ × ℕ)}
    (hes : ComputableInPolyTime es input (encList encE)) :
    ComputableInPolyTime (fun a ↦ keptEdges Δ (es a)) input (encList encE) := by
  unfold keptEdges
  refine foldl' (step := keepStep Δ) hes (const []) (keepStep_polytime Δ)
    (B := fun a ↦ (encList encE (es a)).length) hes.polyBounded_length fun a i _ ↦ ?_
  refine length_encList_sublist encE ((foldl_keepStep_sublist Δ _ []).trans ?_)
  simpa using List.take_sublist i (es a)

/-! ### The adjacency table -/

/-- The adjacency table of `graphOf n kept`, computed on lists. -/
def tableOf (n : ℕ) (kept : List (ℕ × ℕ)) : List Bool :=
  (List.range (n * n)).map fun k ↦
    decide (k / n ≠ k % n) && (kept.contains (k / n, k % n) || kept.contains (k % n, k / n))

theorem decide_eq_of_iff {p : Prop} (i : Decidable p) {b : Bool} (h : p ↔ b = true) :
    @decide p i = b := by
  cases i <;> cases b <;> simp_all

/-- **The adjacency table of `graphOf n kept`, on lists.** -/
theorem adjTable_graphOf (n : ℕ) (kept : List (ℕ × ℕ)) :
    adjTable (graphOf n kept) = tableOf n kept := by
  unfold adjTable graphOf tableOf
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  apply decide_eq_of_iff
  simp only [SimpleGraph.fromRel_adj, finProdFinEquiv, Equiv.coe_fn_symm_mk, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem, ne_eq, Fin.ext_iff]
  rfl

/-- The adjacency table, as a bit string. -/
theorem tableOf' {n : α → ℕ} {kept : α → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime kept input (encList encE)) :
    ComputableInPolyTime (fun a ↦ tableOf (n a) (kept a)) input encBits := by
  unfold tableOf
  have hn1 := hn.comp (fst input encUnary)
  have hk1 := hk.comp (fst input encUnary)
  have hd : ComputableInPolyTime (fun p : α × ℕ ↦ p.2 / n p.1) (encPair input encUnary) encUnary :=
    unary_div.comp ((snd input encUnary).prod hn1)
  have hm : ComputableInPolyTime (fun p : α × ℕ ↦ p.2 % n p.1) (encPair input encUnary) encUnary :=
    unary_mod.comp ((snd input encUnary).prod hn1)
  have hne := decide_not (decide_eq' hd hm)
  have hc1 := contains' hk1 ((toBinary' hd).prod (toBinary' hm))
  have hc2 := contains' hk1 ((toBinary' hm).prod (toBinary' hd))
  have hl := mapWithInput (list := fun a ↦ List.range (n a * n a))
    (f := fun a k ↦ decide (k / n a ≠ k % n a) &&
      ((kept a).contains (k / n a, k % n a) || (kept a).contains (k % n a, k / n a)))
    (unary_range' (unary_mul' hn hn)) (bool_and' hne (bool_or.comp (hc1.prod hc2)))
  exact listToBits.comp hl

/-! ### The parameters -/

/-- The test of the promise. -/
theorem ok' (P : Prm) {G : α → UGInstance} (hG : ComputableInPolyTime G input encU) :
    ComputableInPolyTime (fun a ↦ P.ok (G a)) input encBool := by
  unfold Prm.ok
  have hcs : ComputableInPolyTime (fun a ↦ (G a).2.2.2) input (encList encC) := by fun_prop
  have hl := lengthL' hcs
  have h1 : ComputableInPolyTime (fun a ↦ (G a).2.2.1) input encNat := by fun_prop
  have h2 : ComputableInPolyTime (fun a ↦ (G a).1) input encNat := by fun_prop
  have h3 : ComputableInPolyTime (fun a ↦ (G a).2.1) input encNat := by fun_prop
  exact bool_and' (bool_and' (bool_and' (decide_eq' h1 (const P.R))
    (unary_lt' (const 0) hl)) (binary_le' h2 (toBinary' hl))) (binary_le' h3 (toBinary' hl))

/-- The number of vertices, in unary: at most `|cs| 2^R`. -/
theorem nVert' (P : Prm) {G : α → UGInstance} (hG : ComputableInPolyTime G input encU) :
    ComputableInPolyTime (fun a ↦ P.nVert (G a)) input encUnary := by
  unfold Prm.nVert
  have hcs : ComputableInPolyTime (fun a ↦ (G a).2.2.2) input (encList encC) := by fun_prop
  have h3 : ComputableInPolyTime (fun a ↦ (G a).2.1) input encNat := by fun_prop
  have hmin := binary_min_unary' (lengthL' hcs) h3
  simp only [min_comm (G _).2.2.2.length] at hmin
  exact unary_mul' hmin (const _)

theorem samples' (P : Prm) {G : α → UGInstance} (hG : ComputableInPolyTime G input encU) :
    ComputableInPolyTime (fun a ↦ P.samples (G a)) input encUnary := by
  unfold Prm.samples
  exact unary_mul' (nVert' P hG) (const _)

theorem blockLen' (P : Prm) {G : α → UGInstance} (hG : ComputableInPolyTime G input encU) :
    ComputableInPolyTime (fun a ↦ P.blockLen (G a)) input encUnary := by
  unfold Prm.blockLen
  have ht : ComputableInPolyTime (fun a ↦ P.tBits (G a)) input encUnary :=
    tOf' P (cs := fun a ↦ (G a).2.2.2) (by fun_prop)
  fun_prop

/-- **The number of coins, in unary.** -/
theorem coinCount_polytime' (P : Prm) : ComputableInPolyTime P.coinCount encUG encUnary := by
  rw [encUG_eq]
  unfold Prm.coinCount
  exact ite' (ok' P id') (unary_mul' (samples' P id') (blockLen' P id')) (const 0)

/-! ### The reduction -/

/-- The input of the reduction. -/
abbrev encRed : UGInstance × List Bool ↪ List Bool := encPair encU encBits

/-- The sampled edges. -/
def sampled (P : Prm) (x : UGInstance × List Bool) : List (ℕ × ℕ) :=
  (List.range (P.samples x.1)).map fun i ↦
    edgeOfBlock P x.1 ((x.2.drop (i * P.blockLen x.1)).take (P.blockLen x.1))

/-- The sampled edges. -/
theorem sampled_polytime (P : Prm) : ComputableInPolyTime (sampled P) encRed (encList encE) := by
  unfold sampled
  have hG : ComputableInPolyTime (fun p : (UGInstance × List Bool) × ℕ ↦ p.1.1)
      (encPair encRed encUnary) encU := (fst _ _).comp (fst _ _)
  have hr : ComputableInPolyTime (fun p : (UGInstance × List Bool) × ℕ ↦ p.1.2)
      (encPair encRed encUnary) encBits := (snd _ _).comp (fst _ _)
  have hbl := blockLen' P hG
  have hi : ComputableInPolyTime (fun p : (UGInstance × List Bool) × ℕ ↦ p.2 * P.blockLen p.1.1)
      (encPair encRed encUnary) encUnary := unary_mul' (snd _ _) hbl
  have he := edgeOfBlock' P hG (bitsTakeWithInput (bitsDropWithInput hr hi) hbl)
  have hs : ComputableInPolyTime (fun x : UGInstance × List Bool ↦ List.range (P.samples x.1))
      encRed (encList encUnary) := unary_range' (samples' P (fst encU encBits))
  exact mapWithInput hs he

/-- The encoded output of the reduction: the number of vertices and the adjacency table. -/
noncomputable def redOut (P : Prm) (x : UGInstance × List Bool) : ℕ × List Bool :=
  if P.ok x.1 then (P.nVert x.1, tableOf (P.nVert x.1) (keptEdges P.Δ (sampled P x)))
  else (1, adjTable pointGraph)

/-- The encoded output of the reduction. -/
theorem encGraph_reduce (P : Prm) (x : UGInstance × List Bool) :
    encGraph (reduce P x) = encPair encNat encBits (redOut P x) := by
  unfold reduce redOut
  split_ifs
  · change encPair encNat encBits (_, adjTable _) = _
    rw [adjTable_graphOf]
    rfl
  · rfl

theorem redOut_polytime (P : Prm) :
    ComputableInPolyTime (redOut P) encRed (encPair encNat encBits) := by
  unfold redOut
  have hG : ComputableInPolyTime (fun x : UGInstance × List Bool ↦ x.1) encRed encU := fst _ _
  have hn := nVert' P hG
  exact ite' (ok' P hG) ((toBinary' hn).prod (tableOf' hn (keptEdges' P.Δ (sampled_polytime P))))
    (const _)

/-- **The reduction runs in polynomial time.** -/
theorem reduce_polytime' (P : Prm) :
    ComputableInPolyTime (reduce P) (encPair encUG encBits) encGraph := by
  rw [encUG_eq]
  exact (redOut_polytime P).of_enc_eq (encGraph_reduce P)

end BGHKLMM26.Hard.Mach
