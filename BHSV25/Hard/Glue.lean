module

public import BHSV25.BansalKhot
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# From a reduction and an algorithm to `NP ⊆ P`

The common last step of the hardness theorems (`BHSV25.Hard.npSubsetP_of_reduction`): given a
polynomial-time map `R` from graphs to graphs and a polynomial-time algorithm `A`, if `A` finds on
`R G` a partial `k`-coloring coloring at least `q₁ |V(R G)|` vertices for every yes-instance `G`
of the gap problem `bkGap ε γ η` of Bansal and Khot, while no partial `k`-coloring of `R G`
colors more than `q₀ |V(R G)|` vertices for its no-instances, with `0 ≤ q₀ < q₁`, then checking
the output of `A` on `R G` against a rational threshold between `q₀` and `q₁` solves the gap
problem in polynomial time; if it is NP-hard, `NP ⊆ P`.

The check (`BHSV25.Hard.checkL`) reads the number of vertices, the adjacency table and the
coloring: every pair `p = u n + v` with `u ~ v` must have `u` uncolored or colored differently from
`v`, and the colored vertices must number at least `num / den` times `n`.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Cslib.Complexity

/-- The pair `p = u n + v` is not a monochromatic edge of a partial `k`-coloring. -/
def pairOK (k n : ℕ) (tbl : List Bool) (c : List ℕ) (p : ℕ) : Bool :=
  !(tbl.getD p false) || decide (k ≤ c.getD (p / n) k) ||
    !decide (c.getD (p / n) k = c.getD (p % n) k)

/-- **The check**: `c` is a partial `k`-coloring of the graph with `n` vertices and adjacency
table `tbl`, coloring at least `num / den` times `n` vertices. -/
def checkL (k num den n : ℕ) (tbl : List Bool) (c : List ℕ) : Bool :=
  (List.range (n * n)).all (pairOK k n tbl c) &&
    decide (num * n ≤ den * (List.range n).countP fun v ↦ decide (c.getD v k < k))

/-! ### Correctness of the check -/

open Classical in
theorem adjTable_getD (G : Graph) (u v : Fin G.1) :
    (adjTable G).getD (u * G.1 + v) false = decide (G.2.Adj u v) := by
  have hlt : (u : ℕ) * G.1 + v < G.1 * G.1 := by
    have := u.2; have := v.2; nlinarith
  unfold adjTable
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hlt, ↓reduceDIte, Option.getD_some]
  have hk : (⟨u * G.1 + v, hlt⟩ : Fin (G.1 * G.1)) = finProdFinEquiv (u, v) := by
    ext; simp [finProdFinEquiv]; ring
  rw [hk, Equiv.symm_apply_apply]

theorem countP_range_eq_card {n : ℕ} (f : ℕ → Bool) :
    (List.range n).countP f = (univ.filter fun v : Fin n ↦ f v = true).card := by
  rw [List.countP_eq_length_filter]
  have h1 : ((List.range n).filter f).length =
      ((Finset.range n).filter fun v ↦ f v = true).card := by
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
      Multiset.coe_card]
    congr 1
  rw [h1]
  refine card_bij (fun v hv ↦ ⟨v, mem_range.1 (mem_filter.1 hv).1⟩) (by simp)
    (fun _ _ _ _ h ↦ by simpa using congrArg Fin.val h) (fun v hv ↦ ⟨v.1, ?_, rfl⟩)
  simpa using hv

theorem checkL_iff (k num den : ℕ) (G : Graph) (c : List ℕ) :
    checkL k num den G.1 (adjTable G) c = true ↔
      G.IsPartialColoring k c ∧ num * G.1 ≤ den * G.numColored k c := by
  classical
  have hcount :
      (List.range G.1).countP (fun v ↦ decide (c.getD v k < k)) = G.numColored k c := by
    rw [countP_range_eq_card]
    unfold Graph.numColored Graph.color
    congr 1
  unfold checkL
  rw [Bool.and_eq_true, decide_eq_true_iff, hcount, List.all_eq_true]
  refine and_congr_left fun _ ↦ ⟨fun h u v huv hu ↦ ?_, fun h p hp ↦ ?_⟩
  · have hp : (u : ℕ) * G.1 + v ∈ List.range (G.1 * G.1) := by
      rw [List.mem_range]; have := u.2; have := v.2; nlinarith
    have h1 := h _ hp
    have hv : (v : ℕ) < G.1 := v.2
    have hdiv : ((u : ℕ) * G.1 + v) / G.1 = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, zero_add]
    have hmod : ((u : ℕ) * G.1 + v) % G.1 = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    unfold pairOK at h1
    rw [adjTable_getD, hdiv, hmod] at h1
    unfold Graph.color at hu ⊢
    simp only [huv, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
    rcases h1 with h1 | h1
    · omega
    · exact h1
  · rw [List.mem_range] at hp
    have hn : 0 < G.1 := by
      rcases Nat.eq_zero_or_pos G.1 with h0 | h0
      · rw [h0] at hp; simp at hp
      · exact h0
    set u : Fin G.1 := ⟨p / G.1, Nat.div_lt_of_lt_mul hp⟩
    set v : Fin G.1 := ⟨p % G.1, Nat.mod_lt _ hn⟩
    have hpuv : p = (u : ℕ) * G.1 + v := by
      simp only [u, v]; rw [Nat.mul_comm]; exact (Nat.div_add_mod p G.1).symm
    unfold pairOK
    rw [hpuv, adjTable_getD]
    have hdiv : ((u : ℕ) * G.1 + v) / G.1 = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.2, zero_add]
    have hmod : ((u : ℕ) * G.1 + v) % G.1 = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.2]
    rw [hdiv, hmod]
    by_cases huv : G.2.Adj u v
    · by_cases hk : k ≤ c.getD u k
      · rw [List.getD_eq_getElem?_getD] at hk
        simp [hk]
      · have := h u v huv (by unfold Graph.color; omega)
        unfold Graph.color at this
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
        simp [this]
    · simp [huv]

/-! ### The check runs in polynomial time -/

/-- The check, with the number of vertices capped by the length of the table, so that it can be
read in unary. -/
def checkU (k num den : ℕ) (x : (ℕ × List Bool) × List ℕ) : Bool :=
  checkL k num den (min (x.1.2.length + 1) x.1.1) x.1.2 x.2

theorem length_adjTable (G : Graph) : (adjTable G).length = G.1 * G.1 := by
  simp [adjTable]

theorem checkU_graph (k num den : ℕ) (G : Graph) (c : List ℕ) :
    checkU k num den ((G.1, adjTable G), c) = checkL k num den G.1 (adjTable G) c := by
  unfold checkU
  simp only
  rw [length_adjTable, min_eq_right (by nlinarith)]

section Machine

open ComputableInPolyTime

/-- The input of the check: the number of vertices in binary, the adjacency table, and the
coloring. -/
abbrev encCheck : (ℕ × List Bool) × List ℕ ↪ List Bool :=
  encPair (encPair encNat encBits) (encList encNat)

theorem toBinary' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) : ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-- The number of vertices, capped by the length of the table, in unary. -/
def nU (x : (ℕ × List Bool) × List ℕ) : ℕ := min (x.1.2.length + 1) x.1.1

theorem nU_polytime : ComputableInPolyTime nU encCheck encUnary := by
  have hn : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.1.1) encCheck encNat :=
    (fst _ _).comp (fst _ _)
  have ht : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.1.2) encCheck encBits :=
    (snd _ _).comp (fst _ _)
  have hlen : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.1.2.length + 1)
      encCheck encUnary := unary_succ.comp (length_bits.comp ht)
  exact binary_min_unary' hlen hn

theorem pairOK_polytime (k : ℕ) :
    ComputableInPolyTime (fun q : ((ℕ × List Bool) × List ℕ) × ℕ ↦
      pairOK k (nU q.1) q.1.1.2 q.1.2 q.2) (encPair encCheck encUnary) encBool := by
  have ht : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.1.2) encCheck encBits :=
    (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.2) encCheck
      (encList encNat) := snd _ _
  have hp := snd encCheck encUnary
  have hnU1 := nU_polytime.comp (fst encCheck encUnary)
  have ht1 := ht.comp (fst encCheck encUnary)
  have hc1 := hc.comp (fst encCheck encUnary)
  have hdiv := unary_div.comp (hp.prod hnU1)
  have hmod := unary_mod.comp (hp.prod hnU1)
  have hg := bitsGetDWithInput ht1 hp false
  have hcu := listGetDWithInput hc1 hdiv k
  have hcv := listGetDWithInput hc1 hmod k
  have hle := binary_le' (const k) hcu
  have heq := decide_eq' hcu hcv
  exact bool_or.comp ((bool_or.comp ((bool_not.comp hg).prod hle)).prod (bool_not.comp heq))

theorem checkU_polytime (k num den : ℕ) :
    ComputableInPolyTime (checkU k num den) encCheck encBool := by
  have hc : ComputableInPolyTime (fun x : (ℕ × List Bool) × List ℕ ↦ x.2) encCheck
      (encList encNat) := snd _ _
  have hall := allWithInput (list := fun x ↦ List.range (nU x * nU x))
    (test := fun x p ↦ pairOK k (nU x) x.1.2 x.2 p)
    (unary_range' (unary_mul' nU_polytime nU_polytime)) (pairOK_polytime k)
  have htest2 : ComputableInPolyTime (fun q : ((ℕ × List Bool) × List ℕ) × ℕ ↦
      decide (q.1.2.getD q.2 k < k)) (encPair encCheck encUnary) encBool :=
    binary_lt' (listGetDWithInput (hc.comp (fst _ _)) (snd _ _) k) (const k)
  have hcount := countPWithInput (list := fun x ↦ List.range (nU x))
    (test := fun x v ↦ decide (x.2.getD v k < k)) (unary_range' nU_polytime) htest2
  have hcmp := binary_le' (binary_mul' (const num) (toBinary' nU_polytime))
    (binary_mul' (const den) (toBinary' hcount))
  exact bool_and' hall hcmp

end Machine

/-! ### The glue -/

theorem graph_polytime :
    ComputableInPolyTime (fun G : Graph ↦ (G.1, adjTable G)) encGraph (encPair encNat encBits) :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

/-- **A reduction and an algorithm give `NP ⊆ P`.** -/
theorem npSubsetP_of_reduction {ε γ η : ℝ} (hNP : PromiseProblem.NPHard encGraph (bkGap ε γ η))
    (R : Graph → Graph) (hR : ComputableInPolyTime R encGraph encGraph)
    (A : Graph → List ℕ) (hA : ComputableInPolyTime A encGraph encColoring) (k : ℕ)
    {q₀ q₁ : ℝ} (hq₀ : 0 ≤ q₀) (hq : q₀ < q₁)
    (hyes : ∀ G ∈ (bkGap ε γ η).yes, (R G).IsPartialColoring k (A (R G)) ∧
      q₁ * (R G).1 ≤ (R G).numColored k (A (R G)))
    (hno : ∀ G ∈ (bkGap ε γ η).no, 0 < (R G).1 ∧ ∀ c, (R G).IsPartialColoring k c →
      ((R G).numColored k c : ℝ) ≤ q₀ * (R G).1) :
    NPSubsetP := by
  obtain ⟨q, hq0q, hqq1⟩ := exists_rat_btwn hq
  have hqpos : (0 : ℝ) < q := hq₀.trans_lt hq0q
  have hnum : 0 < q.num := Rat.num_pos.2 (by exact_mod_cast hqpos)
  set num := q.num.toNat
  set den := q.den
  have hden : (0 : ℝ) < den := by exact_mod_cast q.den_pos
  have hqeq : (q : ℝ) = num / den := by
    rw [Rat.cast_def]
    congr 1
    simp only [num]
    exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
  set f : Graph → Bool := fun G ↦ checkL k num den (R G).1 (adjTable (R G)) (A (R G))
  have hf : ComputableInPolyTime f encGraph encBool := by
    have h1 : ComputableInPolyTime (fun G : Graph ↦ (((R G).1, adjTable (R G)), A (R G)))
        encGraph encCheck := (graph_polytime.comp hR).prod (hA.comp hR)
    have h2 := (checkU_polytime k num den).comp h1
    have : f = fun G ↦ checkU k num den (((R G).1, adjTable (R G)), A (R G)) :=
      funext fun G ↦ (checkU_graph k num den (R G) (A (R G))).symm
    rw [this]
    exact h2
  have hsolved : (bkGap ε γ η).SolvedBy f := by
    refine ⟨fun G hG ↦ ?_, fun G hG ↦ ?_⟩
    · obtain ⟨hcol, hcount⟩ := hyes G hG
      refine (checkL_iff k num den (R G) (A (R G))).2 ⟨hcol, ?_⟩
      have hN : (0 : ℝ) ≤ (R G).1 := Nat.cast_nonneg _
      have h1 : (q : ℝ) * (R G).1 ≤ (R G).numColored k (A (R G)) :=
        (mul_le_mul_of_nonneg_right hqq1.le hN).trans hcount
      rw [hqeq, div_mul_eq_mul_div, div_le_iff₀ hden] at h1
      exact_mod_cast (by linarith : (num : ℝ) * (R G).1 ≤ den * (R G).numColored k (A (R G)))
    · obtain ⟨hpos, hbound⟩ := hno G hG
      simp only [f]
      by_contra hc
      rw [Bool.not_eq_false, checkL_iff] at hc
      obtain ⟨hcol, hcount⟩ := hc
      have h1 := hbound _ hcol
      have hN : (0 : ℝ) < (R G).1 := by exact_mod_cast hpos
      have h2 : ((R G).numColored k (A (R G)) : ℝ) < q * (R G).1 :=
        h1.trans_lt (mul_lt_mul_of_pos_right hq0q hN)
      rw [hqeq, div_mul_eq_mul_div, lt_div_iff₀ hden] at h2
      have h3 : (num : ℝ) * (R G).1 ≤ den * (R G).numColored k (A (R G)) := by exact_mod_cast hcount
      linarith
  intro T enc
  exact hNP.NP_subset_P_of_mem_PromiseP (mem_PromiseP_iff.2 ⟨f, hf, hsolved⟩) enc

end BHSV25.Hard
