module

public import BGHKLMM26.Model
public import BGHKLMM26.GW
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Complexity.Classes.Promise.Probabilistic
public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.Sampling
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Corollary 1.3 from Theorem 1.2

[BGHKLMM26, Corollary 1.3] is "immediate" from Theorem 1.2. This file proves it
(`BGHKLMM26.Inapprox.of_hardness`): an algorithm that, on graphs of maximum degree `d`, finds cuts
of expected size at least `α opt` with `α c > s` solves the gap problem `maxCutGap d c s` in
`PromiseBPP` (`BGHKLMM26.Inapprox.mem_PromiseBPP`), which Theorem 1.2 rules out.

* **Graphs as instances** (`BGHKLMM26.Inapprox.toInst`): the constraints `xᵢ xⱼ = -1` of weight
  `1` on the edges `i < j`, read off the adjacency table in polynomial time
  (`BGHKLMM26.Inapprox.toInst_polytime`). Its constraints biject with the edges
  (`BGHKLMM26.Inapprox.length_filter_toInst`), so it is a valid Max-Cut instance with the degrees
  of the graph, and an assignment satisfies exactly the edges it cuts.
* **One run** (`BGHKLMM26.Inapprox.run1`): draw `(|I| + 2)^k` coins, run the algorithm and accept
  if its cut crosses more than a fraction `a / b ∈ (s, α c)` of the edges. A no-instance has no
  such cut. On a yes-instance the expected cut is at least `α c |E|` and every cut is at most
  `|E|`, so a run accepts with probability at least `α c - a / b` (Markov's inequality,
  `BGHKLMM26.Inapprox.coinMean_le`).
* **`m` runs** (`BGHKLMM26.Inapprox.prog`), accepting if one accepts: all fail with probability
  `(1 - p)^m` (`BGHKLMM26.Inapprox.probability_not_prog`), below `1/3` for `m` large depending on
  `d`. The program is strict PPT by complexitylib's repetition and sampling certificates.
* **Constants.** With `C₂` the constant of Theorem 1.2 and `B = max C₂ 1`, the ratio
  `α_GW + (4 B / c*) log d / d` times `c* - C₂ / d` exceeds `s* + C₂ log d / d` once
  `d ≥ 3` and `d > 4 B / c*`, since `α_GW c* = s*`.
-/

@[expose] public section

namespace BGHKLMM26.Inapprox

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### From a graph to a Max-Cut instance -/

/-- The Max-Cut instance of the graph with `n` vertices and adjacency table `t`: the constraints
`xᵢ xⱼ = -1` of weight `1` on the pairs `i < j` with `t[i m + j]`, where the number of variables
`m = min n |t|` is `n` for a graph (whose table has `n²` bits) and can be written in unary. -/
def instOf (n : ℕ) (t : List Bool) : Instance :=
  (min n t.length,
    ((List.range (min n t.length * min n t.length)).filter fun k ↦
      decide (k / min n t.length < k % min n t.length) && t.getD k false).map
      fun k ↦ ((k / min n t.length, k % min n t.length), false, 1))

/-- The Max-Cut instance of a graph. -/
noncomputable def toInst (H : Graph) : Instance := instOf H.1 (adjTable H)

/-- A constraint. -/
abbrev encC : Constraint ↪ List Bool := encPair (encPair encNat encNat) (encPair encBool encRat)

/-- An instance. -/
abbrev encI : Instance ↪ List Bool := encPair encUnary (encList encC)

theorem encInstance_eq : encInstance = encI := rfl

theorem toBinary' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) : ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-- **`instOf` in polynomial time.** -/
theorem instOf_polytime :
    ComputableInPolyTime (fun p : ℕ × List Bool ↦ instOf p.1 p.2) (encPair encNat encBits)
      encI := by
  unfold instOf
  have hm : ComputableInPolyTime (fun p : ℕ × List Bool ↦ min p.1 p.2.length)
      (encPair encNat encBits) encUnary := by
    have hl : ComputableInPolyTime (fun p : ℕ × List Bool ↦ p.2.length) (encPair encNat encBits)
        encUnary := length_bits.comp (snd encNat encBits)
    have h := binary_min_unary' hl (fst encNat encBits)
    rw [show (fun p : ℕ × List Bool ↦ min p.1 p.2.length) = fun p ↦ min p.2.length p.1 from
      funext fun p ↦ min_comm _ _]
    exact h
  have hm1 := hm.comp (fst (encPair encNat encBits) encUnary)
  have hd : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦ q.2 / min q.1.1 q.1.2.length)
      (encPair (encPair encNat encBits) encUnary) encUnary :=
    unary_div.comp ((snd _ encUnary).prod hm1)
  have hmo : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦ q.2 % min q.1.1 q.1.2.length)
      (encPair (encPair encNat encBits) encUnary) encUnary :=
    unary_mod.comp ((snd _ encUnary).prod hm1)
  have ht : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦ q.1.2)
      (encPair (encPair encNat encBits) encUnary) encBits :=
    (snd encNat encBits).comp (fst _ encUnary)
  have hg : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦ q.1.2.getD q.2 false)
      (encPair (encPair encNat encBits) encUnary) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.bitsGetDWithInput ht.tidy (snd _ encUnary).tidy false)
  have htest : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦
      decide (q.2 / min q.1.1 q.1.2.length < q.2 % min q.1.1 q.1.2.length) &&
        q.1.2.getD q.2 false) (encPair (encPair encNat encBits) encUnary) encBool :=
    bool_and' (unary_lt' hd hmo) hg
  have hr : ComputableInPolyTime (fun p : ℕ × List Bool ↦
      List.range (min p.1 p.2.length * min p.1 p.2.length)) (encPair encNat encBits)
      (encList encUnary) := unary_range' (unary_mul' hm hm)
  have hf := filterWithInput (test := fun p k ↦
    decide (k / min p.1 p.2.length < k % min p.1 p.2.length) && p.2.getD k false) hr htest
  have hc : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ ↦
      (((q.2 / min q.1.1 q.1.2.length, q.2 % min q.1.1 q.1.2.length), false, (1 : ℚ)) :
        Constraint)) (encPair (encPair encNat encBits) encUnary) encC :=
    ((toBinary' hd).prod (toBinary' hmo)).prod (const _)
  exact hm.prod (mapWithInput hf hc)

/-- **`toInst` in polynomial time**, reading the graph through its encoding. -/
theorem toInst_polytime : ComputableInPolyTime toInst encGraph encInstance := by
  have he : ComputableInPolyTime (fun H : Graph ↦ (H.1, adjTable H)) encGraph
      (encPair encNat encBits) := of_eq fun _ ↦ rfl
  exact instOf_polytime.comp he

/-! ### The instance of a graph -/

section Graph

variable (H : Graph)

theorem length_adjTable : (adjTable H).length = H.1 * H.1 := by simp [adjTable]

theorem min_mul_self (n : ℕ) : min n (n * n) = n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact min_eq_left (Nat.le_mul_of_pos_left n h)

theorem div_lt_of_lt_mul {n k : ℕ} (hk : k < n * n) : k / n < n :=
  (Nat.div_lt_iff_lt_mul (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hk))).2 hk

theorem mod_lt_of_lt_mul {n k : ℕ} (hk : k < n * n) : k % n < n :=
  Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hk))

open Classical in
theorem getD_adjTable {k : ℕ} (hk : k < H.1 * H.1) :
    (adjTable H).getD k false =
      decide (H.2.Adj ⟨k / H.1, div_lt_of_lt_mul hk⟩ ⟨k % H.1, mod_lt_of_lt_mul hk⟩) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_adjTable]; exact hk)]
  simp only [adjTable, List.getElem_ofFn, Option.getD_some]
  rfl

/-- The test selecting the cells `k = i n + j` with `i < j` and `i ~ j`. -/
noncomputable def cell (k : ℕ) : Bool := decide (k / H.1 < k % H.1) && (adjTable H).getD k false

/-- The constraint of the cell `k`. -/
def conOf (n k : ℕ) : Constraint := ((k / n, k % n), false, 1)

theorem toInst_eq : toInst H =
    (H.1, ((List.range (H.1 * H.1)).filter (cell H)).map (conOf H.1)) := by
  unfold toInst instOf cell conOf
  rw [length_adjTable, min_mul_self]

theorem toInst_fst : (toInst H).1 = H.1 := by rw [toInst_eq]

open Classical in
/-- **Counting constraints by edges**: the constraints of `toInst H` satisfying a symmetric test
are as many as the edges satisfying it. -/
theorem length_filter_toInst (P : ℕ → ℕ → Prop) [DecidableRel P]
    (hP : ∀ i j, P i j → P j i) :
    ((toInst H).2.filter fun c ↦ decide (P c.1.1 c.1.2)).length =
      (H.2.edgeFinset.filter fun e ↦
        ∀ u : Fin H.1, u ∈ e → ∀ w : Fin H.1, w ∈ e → u ≠ w → P u w).card := by
  classical
  obtain ⟨n, G⟩ := H
  rw [toInst_eq, List.filter_map, List.length_map, List.filter_filter]
  have hl : ∀ (f : ℕ → Bool) (N : ℕ), ((List.range N).filter f).length =
      ((Finset.range N).filter fun k ↦ f k = true).card := fun f N ↦ by
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp only [Bool.decide_eq_true]
  rw [hl]
  refine Finset.card_bij (fun k hk ↦ (s(⟨k / n, ?_⟩, ⟨k % n, ?_⟩) : Sym2 (Fin n))) ?_ ?_ ?_
  · exact div_lt_of_lt_mul (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
  · exact mod_lt_of_lt_mul (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, Function.comp_apply,
      decide_eq_true_eq, cell, conOf] at hk
    obtain ⟨hk, hp, hlt, hadj⟩ := hk
    rw [getD_adjTable ⟨n, G⟩ hk, decide_eq_true_eq] at hadj
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    refine ⟨hadj, fun u hu w hw huw ↦ ?_⟩
    rw [Sym2.mem_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · exact of_decide_eq_true hp
    · exact hP _ _ (of_decide_eq_true hp)
    · exact absurd rfl huw
  · intro k hk k' hk' h
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      cell] at hk hk'
    rw [Sym2.eq_iff] at h
    simp only [Fin.ext_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← Nat.div_add_mod k n, ← Nat.div_add_mod k' n, h1, h2]
    · exfalso
      have := hk.2.2.1
      have := hk'.2.2.1
      omega
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, hpe⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hab : a ≠ b := G.ne_of_adj he
    have hpab := hpe a (Sym2.mem_mk_left a b) b (Sym2.mem_mk_right a b) hab
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · -- `k = a n + b`
      have hk : (a : ℕ) * n + b < n * n := by nlinarith [a.2, b.2]
      have hd : ((a : ℕ) * n + b) / n = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt a.2),
          Nat.div_eq_of_lt b.2, Nat.zero_add]
      have hm : ((a : ℕ) * n + b) % n = b := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]
      refine ⟨a * n + b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq,
          Function.comp_apply, cell, conOf]
        refine ⟨hk, decide_eq_true (by rw [hd, hm]; exact hpab), by rw [hd, hm]; exact h, ?_⟩
        rw [getD_adjTable ⟨n, G⟩ hk, decide_eq_true_eq]
        convert he using 2
      · rw [Sym2.eq_iff]
        left
        exact ⟨Fin.ext hd, Fin.ext hm⟩
    · have hk : (b : ℕ) * n + a < n * n := by nlinarith [a.2, b.2]
      have hd : ((b : ℕ) * n + a) / n = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt a.2),
          Nat.div_eq_of_lt a.2, Nat.zero_add]
      have hm : ((b : ℕ) * n + a) % n = a := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.2]
      refine ⟨b * n + a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq,
          Function.comp_apply, cell, conOf]
        refine ⟨hk, decide_eq_true (by rw [hd, hm]; exact hP _ _ hpab), by rw [hd, hm]; exact h, ?_⟩
        rw [getD_adjTable ⟨n, G⟩ hk, decide_eq_true_eq]
        convert he.symm using 2
      · rw [Sym2.eq_iff]
        right
        exact ⟨Fin.ext hd, Fin.ext hm⟩

/-- The constraints of `toInst H` are `((i, j), false, 1)` with `i < j < n`. -/
theorem mem_toInst {c : Constraint} (hc : c ∈ (toInst H).2) :
    c.1.1 < c.1.2 ∧ c.1.2 < H.1 ∧ c.2 = (false, 1) := by
  rw [toInst_eq] at hc
  simp only [List.mem_map, List.mem_filter, List.mem_range, cell, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨k, ⟨hk, hlt, -⟩, rfl⟩ := hc
  exact ⟨hlt, mod_lt_of_lt_mul hk, rfl⟩

theorem isMaxCutInstance_toInst : IsMaxCutInstance (toInst H) :=
  fun _ hc ↦ (mem_toInst H hc).2.2

theorem valid_toInst : Valid (toInst H) := by
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_toInst H hc
    rw [toInst_fst, h3]
    exact ⟨h1, h2, zero_le_one⟩
  · rw [toInst_eq, List.map_map]
    refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
    intro k _ k' _ h
    simp only [Function.comp_apply, conOf, Prod.mk.injEq] at h
    rw [← Nat.div_add_mod k H.1, ← Nat.div_add_mod k' H.1, h.1, h.2]

/-- On a Max-Cut instance, an assignment satisfies the constraints it cuts. -/
theorem satWeight_eq_length {I : Instance} (hI : IsMaxCutInstance I) (x : ℕ → Bool) :
    satWeight I x = ((I.2.filter fun c ↦ decide (x c.1.1 ≠ x c.1.2)).length : ℝ) := by
  obtain ⟨n, cs⟩ := I
  unfold satWeight
  simp only [IsMaxCutInstance] at hI ⊢
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons, ih fun c' hc' ↦ hI c' (by simp [hc']),
      hI c (by simp)]
    by_cases h : x c.1.1 = x c.1.2 <;> simp [h, add_comm]

open Classical in
/-- **An assignment satisfies, in `toInst H`, the edges it cuts.** -/
theorem satWeight_toInst (x : ℕ → Bool) :
    satWeight (toInst H) x = cutSize H.2 (fun v ↦ x v) := by
  rw [satWeight_eq_length (isMaxCutInstance_toInst H),
    length_filter_toInst H (fun i j ↦ x i ≠ x j) (fun _ _ h ↦ Ne.symm h)]
  rfl

open Classical in
/-- `toInst H` has one constraint per edge. -/
theorem length_toInst : (toInst H).2.length = H.2.edgeFinset.card := by
  have h := length_filter_toInst H (fun _ _ ↦ True) (fun _ _ _ ↦ trivial)
  simpa using h

open Classical in
/-- `toInst H` has the degrees of `H`. -/
theorem maxDegreeLE_toInst {d : ℕ} (hH : MaxDegreeAtMost H d) : MaxDegreeLE (toInst H) d := by
  intro v
  unfold degree
  rw [length_filter_toInst H (fun i j ↦ i = v ∨ j = v) (fun _ _ h ↦ h.symm)]
  by_cases hv : v < H.1
  · refine (Finset.card_le_card fun e he ↦ ?_).trans
      ((H.2.card_incidenceFinset_eq_degree ⟨v, hv⟩).le.trans (hH _))
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, hpe⟩ := he
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨he, ?_⟩
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases hpe a (Sym2.mem_mk_left a b) b (Sym2.mem_mk_right a b) (H.2.ne_of_adj he) with h | h
    · rw [show (⟨v, hv⟩ : Fin H.1) = a from Fin.ext h.symm]
      exact Sym2.mem_mk_left a b
    · rw [show (⟨v, hv⟩ : Fin H.1) = b from Fin.ext h.symm]
      exact Sym2.mem_mk_right a b
  · refine (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun e he hpe ↦ ?_)).le.trans
      (Nat.zero_le _)
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases hpe a (Sym2.mem_mk_left a b) b (Sym2.mem_mk_right a b) (H.2.ne_of_adj he) with h | h
    · exact hv (h ▸ a.2)
    · exact hv (h ▸ b.2)

/-- Every cut of `H` is at most the optimum of `toInst H`. -/
theorem le_opt_toInst (x : Fin H.1 → Bool) : (cutSize H.2 x : ℝ) ≤ opt (toInst H) := by
  have hn := toInst_fst H
  have hx : satWeight (toInst H) (fun v ↦ if h : v < (toInst H).1 then
      (fun i : Fin (toInst H).1 ↦ x ⟨i, hn ▸ i.2⟩) ⟨v, h⟩ else false) = cutSize H.2 x := by
    rw [satWeight_toInst]
    refine congrArg (fun y ↦ (cutSize H.2 y : ℝ)) (funext fun v ↦ ?_)
    have hv : (v : ℕ) < (toInst H).1 := hn.symm ▸ v.2
    simp [hv]
  rw [← hx]
  unfold opt
  exact le_ciSup (f := fun y : Fin (toInst H).1 → Bool ↦ satWeight (toInst H)
    fun v ↦ if h : v < (toInst H).1 then y ⟨v, h⟩ else false) (Set.finite_range _).bddAbove
    (fun i : Fin (toInst H).1 ↦ x ⟨i, hn ▸ i.2⟩)

open Classical in
/-- Every output is a cut of `H`. -/
theorem outputWeight_toInst_le (y : List Bool) :
    outputWeight (toInst H) y ≤ ((Finset.univ.sup (cutSize H.2) : ℕ) : ℝ) := by
  unfold outputWeight
  rw [satWeight_toInst]
  exact_mod_cast Finset.le_sup (f := cutSize H.2) (Finset.mem_univ _)

open Classical in
/-- The maximum cut of `H` is at most the optimum of `toInst H`. -/
theorem sup_le_opt_toInst : ((Finset.univ.sup (cutSize H.2) : ℕ) : ℝ) ≤ opt (toInst H) := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin H.1 → Bool))
    Finset.univ_nonempty (cutSize H.2)
  rw [hx]
  exact le_opt_toInst H x

end Graph

/-! ### One run of the algorithm -/

/-- The number of constraints `xᵢ xⱼ = -1` that the output `y` cuts. -/
def cutCnt (I : Instance) (y : List Bool) : ℕ :=
  I.2.countP fun c ↦ decide (y.getD c.1.1 false ≠ y.getD c.1.2 false)

theorem outputWeight_eq_cutCnt {I : Instance} (hI : IsMaxCutInstance I) (y : List Bool) :
    outputWeight I y = cutCnt I y := by
  unfold outputWeight cutCnt
  rw [satWeight_eq_length hI, List.countP_eq_length_filter]

theorem cutCnt_le (I : Instance) (y : List Bool) : cutCnt I y ≤ I.2.length :=
  List.countP_le_length

/-- **The test of one run**: does the cut that `A` finds with the coins `x.2` cross more than a
fraction `a / b` of the edges? -/
noncomputable def test (A : Instance × List Bool → List Bool) (a b : ℕ) (x : Graph × List Bool) :
    Bool :=
  decide (a * (toInst x.1).2.length < b * cutCnt (toInst x.1) (A (toInst x.1, x.2)))

/-- A machine within `c ((|x| + 2)^k + |(x, r)| + 1)` steps runs in polynomial time. -/
theorem polytime_of_runsInTime {A : Instance × List Bool → List Bool} {k : ℕ}
    (h : RunsInTime A fun N ↦ (N + 2) ^ k) :
    ComputableInPolyTime A (encPair encInstance encBits) encBits := by
  obtain ⟨c, hc⟩ := h
  have hp : Cslib.PolynomiallyBounded fun N ↦ c * ((N + 2) ^ k + N + 1) := by
    refine Cslib.polynomiallyBounded_iff_le.2 ⟨3 * c * 2 ^ k, k + 1, fun N ↦ ?_⟩
    have h1 : (N + 2) ^ k ≤ 2 ^ k * (N + 1) ^ (k + 1) := by
      calc (N + 2) ^ k ≤ (2 * (N + 1)) ^ k := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ k * (N + 1) ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * (N + 1) ^ (k + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : N + 1 ≤ 2 ^ k * (N + 1) ^ (k + 1) := by
      calc N + 1 = 1 * (N + 1) ^ 1 := by ring
        _ ≤ 2 ^ k * (N + 1) ^ (k + 1) :=
          Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by omega) (by omega))
    calc c * ((N + 2) ^ k + N + 1) ≤ c * (3 * (2 ^ k * (N + 1) ^ (k + 1))) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * c * 2 ^ k * (N + 1) ^ (k + 1) := by ring
  refine ⟨_, _, hp, hp, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩ <;>
  · have h1 :
        (encInstance xr.1).length ≤ (Encoding.encPair encInstance Encoding.encBits xr).length :=
      length_le_encPair_left encInstance encBits xr
    have h2 : (Encoding.encPair encInstance Encoding.encBits xr).length =
        (encPair encInstance encBits xr).length := rfl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.pow_le_pow_left (by omega) _) _) _)

theorem coins_polytime (k : ℕ) :
    ComputableInPolyTime (fun H : Graph ↦ ((encInstance (toInst H)).length + 2) ^ k)
      encGraph encUnary := by
  have h := (unary_eval ((Polynomial.X + 2) ^ k)).comp
    ((encoding_length encInstance).comp toInst_polytime)
  simpa [Function.comp_def] using h

theorem test_polytime {A : Instance × List Bool → List Bool}
    (hA : ComputableInPolyTime A (encPair encInstance encBits) encBits) (a b : ℕ) :
    ComputableInPolyTime (test A a b) (encPair encGraph encBits) encBool := by
  unfold test
  rw [encInstance_eq] at hA
  have hI : ComputableInPolyTime (fun x : Graph × List Bool ↦ toInst x.1)
      (encPair encGraph encBits) encI := toInst_polytime.comp (fst _ _)
  have hy : ComputableInPolyTime (fun x : Graph × List Bool ↦ A (toInst x.1, x.2))
      (encPair encGraph encBits) encBits := hA.comp (hI.prod (snd _ _))
  have hcs : ComputableInPolyTime (fun x : Graph × List Bool ↦ (toInst x.1).2)
      (encPair encGraph encBits) (encList encC) := (snd _ _).comp hI
  have hlen : ComputableInPolyTime (fun x : Graph × List Bool ↦ (toInst x.1).2.length)
      (encPair encGraph encBits) encUnary := (length_list encC).comp hcs
  have hy1 : ComputableInPolyTime
      (fun p : (Graph × List Bool) × Constraint ↦ A (toInst p.1.1, p.1.2))
      (encPair (encPair encGraph encBits) encC) encBits := hy.comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : (Graph × List Bool) × Constraint ↦ p.2.1.1)
      (encPair (encPair encGraph encBits) encC) encNat := by fun_prop
  have hj : ComputableInPolyTime (fun p : (Graph × List Bool) × Constraint ↦ p.2.1.2)
      (encPair (encPair encGraph encBits) encC) encNat := by fun_prop
  have hgi := ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false hy1.tidy hi.tidy
  have hgj := ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false hy1.tidy hj.tidy
  have hne := (ComputableTidilyInPolyTime.of_finite (encA := encPair encBool encBool)
    (encB := encBool) fun q : Bool × Bool ↦ decide (q.1 ≠ q.2)).comp (hgi.prod hgj)
  have hcnt : ComputableInPolyTime (fun x : Graph × List Bool ↦
      cutCnt (toInst x.1) (A (toInst x.1, x.2))) (encPair encGraph encBits) encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.countPWithInput hcs.tidy hne)
  exact .of_tidy (ComputableTidilyInPolyTime.unary_lt' (unary_mul' (const a) hlen).tidy
    (unary_mul' (const b) hcnt).tidy)

/-! ### Repeated runs -/

section Runs

open Cslib Cslib.Probability Cslib.Complexity

variable (A : Instance × List Bool → List Bool) (k a b m : ℕ)

/-- **One run**: draw the coins and test the cut. -/
noncomputable def run1 (H : Graph) : ProbComp Bool :=
  (fun w ↦ test A a b (H, w)) <$> BitString.sampleList (((encInstance (toInst H)).length + 2) ^ k)

/-- **`m` independent runs**, accepting if one of them succeeds. -/
noncomputable def prog (H : Graph) : ProbComp Bool :=
  (fun n ↦ decide (0 < n)) <$> OracleComp.countTrue m (run1 A k a b H)

variable {A} in
theorem prog_isPPTOn (hA : ComputableInPolyTime A (encPair encInstance encBits) encBits) :
    IsPPTOn encGraph encBool (prog A k a b m) := by
  have h1 : IsPPTOn encGraph encBool (run1 A k a b) :=
    IsPPTOn.of_seeded (coins_polytime k) (test_polytime hA a b)
  have h0 : ComputableInPolyTime (fun n : ℕ ↦ decide (0 < n)) encUnary encBool :=
    .of_tidy (ComputableTidilyInPolyTime.unary_lt' (ComputableTidilyInPolyTime.const 0)
      ComputableTidilyInPolyTime.id')
  exact (h1.countTrue (const m)).map h0

/-- **All runs fail** with probability `(1 - p)^m`. -/
theorem probability_not_prog (H : Graph) :
    Pr[Bool.not <$> prog A k a b m H] = (1 - Pr[run1 A k a b H]) ^ m := by
  have hset : ((fun l : List Bool ↦ !decide (0 < l.count true)) ⁻¹' {true}) =
      {l | ∀ x ∈ l, (!x) = true} := by
    ext l
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not, not_lt,
      Nat.le_zero, List.count_eq_zero, Set.mem_ofPred_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · intro h x hx
      cases x
      · rfl
      · exact absurd hx h
    · intro h ht
      exact absurd (h true ht) (by decide)
  have h1 : ProbComp.eval (Bool.not <$> prog A k a b m H) true =
      (ProbComp.eval (OracleComp.replicate m (run1 A k a b H))).toOuterMeasure
        {l | ∀ x ∈ l, (!x) = true} := by
    rw [← hset, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
    simp only [prog, OracleComp.countTrue, ProbComp.eval_map, PMF.map_comp]
    rfl
  have h2 : (ProbComp.eval (run1 A k a b H)).toOuterMeasure {x | (!x) = true} =
      ProbComp.eval (Bool.not <$> run1 A k a b H) true := by
    rw [ProbComp.eval_map, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  rw [h1, ProbComp.toOuterMeasure_replicate_forall, h2, ENNReal.toReal_pow,
    ProbComp.probability_not]

end Runs

/-! ### The success probability of one run -/

/-- **Markov's inequality for one run**: if `f ≤ M` always and `f ≤ t M` when `V` rejects, the
mean of `f` is at most `p M + t M`, where `p` is the fraction of accepted coin strings. -/
theorem coinMean_le (L : ℕ) (f : List Bool → ℝ) (V : List Bool → Bool) {M t : ℝ} (ht : 0 ≤ t)
    (hM : 0 ≤ M) (hf : ∀ r, f r ≤ M) (hbad : ∀ r, V r = false → f r ≤ t * M) :
    coinMean L f ≤
      ((Finset.univ.filter fun r : Fin L → Bool ↦ V (List.ofFn r) = true).card : ℝ) / 2 ^ L * M +
        t * M := by
  unfold coinMean
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  rw [div_le_iff₀ h2]
  have hsum : ∑ r : Fin L → Bool, f (List.ofFn r) ≤
      ∑ r : Fin L → Bool, if V (List.ofFn r) = true then M else t * M := by
    refine Finset.sum_le_sum fun r _ ↦ ?_
    split_ifs with h
    · exact hf _
    · exact hbad _ (by simpa using h)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  have hcard : ((Finset.univ.filter fun r : Fin L → Bool ↦ ¬V (List.ofFn r) = true).card : ℝ) ≤
      2 ^ L := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin L → Bool))
      fun r ↦ ¬V (List.ofFn r) = true
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  have htM : 0 ≤ t * M := mul_nonneg ht hM
  calc ∑ r : Fin L → Bool, f (List.ofFn r) ≤ _ := hsum
    _ ≤ ((Finset.univ.filter fun r : Fin L → Bool ↦ V (List.ofFn r) = true).card : ℝ) * M +
        2 ^ L * (t * M) := by gcongr
    _ = _ := by field_simp

/-! ### The gap problem in `PromiseBPP` -/

open Cslib Cslib.Probability Cslib.Complexity in
/-- **An approximation algorithm solves the gap problem.** If `A` finds cuts of expected size at
least `α opt` on graphs of maximum degree at most `d`, and `s < α c`, then repeating `A` and
comparing its cut with a fraction `a / b ∈ (s, α c)` of the edges decides the gap problem
between `c` and `s` with bounded error: no-instances are never accepted, and each run accepts a
yes-instance with probability at least `α c - a / b`. -/
theorem mem_PromiseBPP {A : Instance × List Bool → List Bool} {k d : ℕ}
    (hA : RunsInTime A fun N ↦ (N + 2) ^ k) {α c s : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hsc : s < α * c)
    (hguar : ∀ I : Instance, Valid I → IsMaxCutInstance I → MaxDegreeLE I d →
      α * opt I ≤ coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r))) :
    maxCutGap d c s ∈ PromiseBPP encGraph := by
  classical
  -- the threshold `q = a / b`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hsc (mul_pos hα hc))
  have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
  have hqs : s < q := (le_max_left _ _).trans_lt hq1
  set a := q.num.toNat
  set b := q.den
  have hb : (0 : ℝ) < b := by exact_mod_cast q.den_pos
  have hab : (a : ℝ) = q * b := by
    have hnum : 0 ≤ q.num := Rat.num_nonneg.2 (by exact_mod_cast hq0.le)
    have : (a : ℤ) = q.num := Int.toNat_of_nonneg hnum
    have h' : ((q.num : ℤ) : ℝ) = q * b := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_mul, Rat.mul_den_eq_num]
    rw [← h', ← this]
    rfl
  -- the number of runs
  set γ := min (α * c - q) 1
  have hγ : 0 < γ := lt_min (by linarith) one_pos
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 3)
    (by linarith : 1 - γ < 1)
  have hA' := polytime_of_runsInTime hA
  refine mem_PromiseBPP_iff_exists_isPPTOn.2 ⟨prog A k a b m, prog_isPPTOn k a b m hA',
    fun H hH ↦ ?_, fun H hH ↦ ?_⟩
  · -- a yes-instance
    simp only [maxCutGap, PromiseProblem.yes_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq] at hH
    obtain ⟨hval, hdeg⟩ := hH
    set I := toInst H
    set E := H.2.edgeFinset.card
    set S := ((Finset.univ.sup (cutSize H.2) : ℕ) : ℝ)
    have hE : (0 : ℝ) < E := by
      rcases Nat.eq_zero_or_pos E with h | h
      · exfalso
        unfold maxCutValue at hval
        rw [show (H.2.edgeFinset.card : ℝ) = 0 by exact_mod_cast h, div_zero] at hval
        linarith
      · exact_mod_cast h
    have hS : c * E ≤ S := by
      unfold maxCutValue at hval
      rwa [le_div_iff₀ hE] at hval
    have hlen : (I.2.length : ℝ) = E := by exact_mod_cast length_toInst H
    have hmean := hguar I (valid_toInst H) (isMaxCutInstance_toInst H) (maxDegreeLE_toInst H hdeg)
    have hopt := sup_le_opt_toInst H
    set L := ((encInstance I).length + 2) ^ k
    have hbound := coinMean_le L (fun r ↦ outputWeight I (A (I, r))) (fun r ↦ test A a b (H, r))
      hq0.le hE.le (fun r ↦ ?_) (fun r hr ↦ ?_)
    rotate_left
    · rw [outputWeight_eq_cutCnt (isMaxCutInstance_toInst H), ← hlen]
      exact_mod_cast cutCnt_le _ _
    · simp only [test, decide_eq_false_iff_not, not_lt] at hr
      rw [outputWeight_eq_cutCnt (isMaxCutInstance_toInst H), ← hlen]
      have hr' : (b : ℝ) * cutCnt I (A (I, r)) ≤ a * I.2.length := by exact_mod_cast hr
      rw [hab] at hr'
      nlinarith
    -- the success probability of one run
    set p := Pr[run1 A k a b H]
    have hp : p = ((Finset.univ.filter fun r : Fin L → Bool ↦
        test A a b (H, List.ofFn r) = true).card : ℝ) / 2 ^ L :=
      probability_sampleList_verifier (test A a b) H L
    have hpγ : γ ≤ p := by
      have h1 : α * c * E ≤ p * E + q * E := by
        rw [hp]
        calc α * c * E = α * (c * E) := by ring
          _ ≤ α * opt I := mul_le_mul_of_nonneg_left (hS.trans hopt) hα.le
          _ ≤ _ := hmean.trans hbound
      have h2 : α * c - q ≤ p := by
        have := (mul_le_mul_iff_of_pos_right hE).1 (by linarith : (α * c - q) * E ≤ p * E)
        exact this
      exact (min_le_left _ _).trans h2
    have hp1 : p ≤ 1 := by
      have := (ProbComp.eval (run1 A k a b H)).coe_le_one true
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have hfail : Pr[Bool.not <$> prog A k a b m H] < 1 / 3 := by
      rw [probability_not_prog]
      calc (1 - p) ^ m ≤ (1 - γ) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith) m
        _ < 1 / 3 := hm
    rw [ProbComp.probability_not] at hfail
    linarith
  · -- a no-instance: no run accepts
    simp only [maxCutGap, PromiseProblem.no_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_no_gapMax, Set.mem_ofPred_eq] at hH
    obtain ⟨⟨hval, -⟩, -⟩ := hH
    have htest : ∀ w, test A a b (H, w) = false := by
      intro w
      simp only [test, decide_eq_false_iff_not, not_lt]
      set I := toInst H
      set E := H.2.edgeFinset.card
      have hlen : I.2.length = E := length_toInst H
      have hcut : (cutCnt I (A (I, w)) : ℝ) ≤ ((Finset.univ.sup (cutSize H.2) : ℕ) : ℝ) := by
        rw [← outputWeight_eq_cutCnt (isMaxCutInstance_toInst H)]
        exact outputWeight_toInst_le H _
      rcases Nat.eq_zero_or_pos E with h | h
      · have := cutCnt_le I (A (I, w))
        rw [hlen, h] at this ⊢
        simp [Nat.le_zero.1 this]
      · have hE : (0 : ℝ) < E := by exact_mod_cast h
        have hS : ((Finset.univ.sup (cutSize H.2) : ℕ) : ℝ) ≤ s * E := by
          unfold maxCutValue at hval
          rwa [div_le_iff₀ hE] at hval
        have h1 : (cutCnt I (A (I, w)) : ℝ) ≤ q * E :=
          hcut.trans (hS.trans (mul_le_mul_of_nonneg_right hqs.le hE.le))
        have : (b : ℝ) * cutCnt I (A (I, w)) ≤ a * I.2.length := by
          rw [hab, hlen]
          calc (b : ℝ) * cutCnt I (A (I, w)) ≤ b * (q * E) := mul_le_mul_of_nonneg_left h1 hb.le
            _ = q * b * E := by ring
        exact_mod_cast this
    have hp : Pr[run1 A k a b H] = 0 := by
      rw [run1, probability_sampleList_verifier (test A a b) H]
      simp [acceptCount, htest]
    rw [probability_not_prog, hp]
    norm_num

/-! ### Corollary 1.3 -/

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_three

open Cslib.Complexity in
/-- **Corollary 1.3 from Theorem 1.2**: with `C₂` the constant of Theorem 1.2 and
`B = max C₂ 1`, an algorithm reaching `α_GW + (4 B / c*) log d / d` on graphs of maximum degree
`d ≥ max(d₂, 3, 4 B / c* + 1)` solves Theorem 1.2's gap problem, which puts `NP` in `BPP`. -/
theorem of_hardness
    (h : ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      maxCutGap d ((1 - ρ) / 2 - C / d) (Real.arccos ρ / Real.pi + C * Real.log d / d) ∈
        PromiseBPP encGraph →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
      ∀ (A : Instance × List Bool → List Bool) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) →
      (∀ I : Instance, Valid I → IsMaxCutInstance I → MaxDegreeLE I d →
        (alphaGW + C * Real.log d / d) * opt I ≤
          coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r))) →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc := by
  obtain ⟨C₂, d₂, h⟩ := h
  have hρ := GW.rhoStar_mem_window
  set cs := (1 - GW.rhoStar) / 2 with hcs_def
  have hcs : 0 < cs := by rw [hcs_def]; linarith [hρ.2]
  have hss : Real.arccos GW.rhoStar / Real.pi = alphaGW * cs := by
    rw [GW.alphaGW_eq, gwRatio, div_mul_cancel₀ _ hcs.ne']
  have hα0 := GW.alphaGW_pos
  have hα1 := GW.alphaGW_lt_one
  set B := max C₂ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hCB : C₂ ≤ B := le_max_left _ _
  refine ⟨4 * B / cs, max d₂ (max 3 (⌈4 * B / cs⌉₊ + 1)), fun d hd A k hA hguar ↦ ?_⟩
  have hd₂ : d₂ ≤ d := le_of_max_le_left hd
  have hd3 : (3 : ℝ) ≤ d := by
    exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdB : 4 * B / cs < d := by
    have h1 : ⌈4 * B / cs⌉₊ + 1 ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
    have h2 : ((⌈4 * B / cs⌉₊ : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast h1
    linarith [Nat.le_ceil (4 * B / cs)]
  have hd0 : (0 : ℝ) < d := by linarith
  set Lg := Real.log d
  have hL : 1 ≤ Lg := (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hd3)).le
  -- `u = B / d` and `v = 4 B / (c* d) < 1`
  set u := B / d
  set v := 4 * B / cs / d
  have hu : 0 < u := by positivity
  have hv : v < 1 := by rw [div_lt_one hd0]; exact hdB
  have hv0 : 0 < v := by positivity
  have hvcs : v * cs = 4 * u := by
    simp only [u, v]
    field_simp
  have hα : 0 < alphaGW + 4 * B / cs * Lg / d := by
    have : 0 ≤ 4 * B / cs * Lg / d := by positivity
    linarith
  have hc' : cs - u ≤ cs - C₂ / d := by
    have : C₂ / d ≤ u := div_le_div_of_nonneg_right hCB hd0.le
    linarith
  have hcu : u < cs / 4 := by
    have : u * 4 = v * cs := by rw [hvcs]; ring
    nlinarith
  have hc : 0 < cs - C₂ / d := by linarith
  have hs' : Real.arccos GW.rhoStar / Real.pi + C₂ * Lg / d ≤ alphaGW * cs + u * Lg := by
    rw [hss]
    have h1 : C₂ * Lg / d ≤ B * Lg / d := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCB (by linarith : (0 : ℝ) ≤ Lg)) hd0.le
    have h2 : B * Lg / d = u * Lg := by simp only [u]; ring
    linarith
  have hαv : alphaGW + 4 * B / cs * Lg / d = alphaGW + v * Lg := by
    simp only [v]
    ring
  have hsc : Real.arccos GW.rhoStar / Real.pi + C₂ * Lg / d <
      (alphaGW + 4 * B / cs * Lg / d) * (cs - C₂ / d) := by
    refine hs'.trans_lt (lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_left hc' hα.le))
    rw [hαv]
    have hexp : (alphaGW + v * Lg) * (cs - u) =
        alphaGW * cs - alphaGW * u + 4 * u * Lg - v * u * Lg := by
      have : v * Lg * cs = 4 * u * Lg := by rw [mul_right_comm, hvcs]
      linear_combination this
    rw [hexp]
    have h1 : v * u * Lg < u * Lg := by
      have := mul_lt_mul_of_pos_right hv (mul_pos hu (by linarith : (0 : ℝ) < Lg))
      linarith
    nlinarith
  exact h d hd₂ GW.rhoStar GW.isGWMinimizer_rhoStar (mem_PromiseBPP hA hα hc hsc hguar)

end BGHKLMM26.Inapprox
