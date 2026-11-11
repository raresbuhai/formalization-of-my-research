module

public import BHSV25.BansalKhot
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# From reductions to NP-hardness, and from NP-hardness to `NP ⊆ P`

* **The common last step of the hardness theorems** (`BHSV25.Hard.npHard_of_reduction`): a
  polynomial-time map from graphs to graphs sending the yes-instances of the gap problem
  `bkGap ε γ η` of Bansal and Khot to yes-instances of a promise problem `Y`, and its
  no-instances to no-instances of `Y`, makes `Y` NP-hard. The graph without vertices, a
  yes-instance of `bkGap ε γ η` that no blow-up maps to a graph with an `(M, ε)`-coloring, is
  first replaced by two isolated vertices (`BHSV25.Hard.nonempty`).
* **NP-hardness rules out algorithms** (`BHSV25.Hard.npSubsetP_of_npHard`): if the gap problem
  `coloringGap P k δ` is NP-hard and a polynomial-time algorithm finds `(k, δ')`-colorings of the
  graphs with property `P`, `δ' < δ ≤ 1`, then checking its output against a rational threshold
  between `1 - δ` and `1 - δ'` solves the gap problem in polynomial time, so `NP ⊆ P`. This
  check, for a polynomial-time map `R` and a gap of coverages `q₀ < q₁`, is
  `BHSV25.Hard.npSubsetP_of_reduction`.

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

/-! ### Colorings -/

theorem isColoring_mono {G : Graph} {k : ℕ} {δ δ' : ℝ} {c : List ℕ} (h : G.IsColoring k δ c)
    (hδ : δ ≤ δ') : G.IsColoring k δ' c :=
  ⟨h.1, le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) h.2⟩

theorem hasColoring_mono {G : Graph} {k : ℕ} {δ δ' : ℝ} (h : G.HasColoring k δ) (hδ : δ ≤ δ') :
    G.HasColoring k δ' :=
  let ⟨c, hc⟩ := h
  ⟨c, isColoring_mono hc hδ⟩

theorem mColorable_mono {G : Graph} {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {δ δ' : ℝ}
    (h : G.MColorable M δ) (hδ : δ ≤ δ') : G.MColorable M δ' := by
  obtain ⟨χ, h1, S, hS, hmono⟩ := h
  exact ⟨χ, fun a b ↦ (h1 a b).trans hδ, S,
    hS.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)), hmono⟩

/-- An `(M, ε)`-coloring gives a `(k, ε)`-coloring: uncolor the vertices covering the
monochromatic edges. -/
theorem hasColoring_of_mColorable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ} (G : Graph)
    (h : G.MColorable M ε) : G.HasColoring k ε := by
  classical
  obtain ⟨χ, -, S, hS, hmono⟩ := h
  set c : List ℕ := List.ofFn fun v : Fin G.1 ↦ if v ∈ S then k else (χ v : ℕ)
  have hcol : ∀ v, G.color k c v = if v ∈ S then k else (χ v : ℕ) := by
    intro v
    unfold Graph.color
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [v.2, ↓reduceDIte, Option.getD_some, Fin.eta]
  refine ⟨c, fun u v huv hu ↦ ?_, ?_⟩
  · rw [hcol] at hu ⊢
    rw [hcol]
    have huS : u ∉ S := by intro h; rw [ite_eq_left h] at hu; exact lt_irrefl _ hu
    rw [ite_eq_right huS]
    by_cases hvS : v ∈ S
    · rw [ite_eq_left hvS]; exact (χ u).2.ne
    · rw [ite_eq_right hvS]
      intro heq
      rcases hmono u v huv (Fin.ext heq) with h | h
      · exact huS h
      · exact hvS h
  · unfold Graph.numColored
    have hsub : Sᶜ ⊆ univ.filter fun v ↦ G.color k c v < k := by
      intro v hv
      rw [mem_compl] at hv
      simp only [mem_filter, mem_univ, true_and, hcol, ite_eq_right hv]
      exact (χ v).2
    have h1 := card_le_card hsub
    rw [card_compl, Fintype.card_fin] at h1
    have h2 : (S.card : ℝ) ≤ G.1 := by exact_mod_cast (card_le_univ S).trans (by simp)
    have h3 : ((G.1 - S.card : ℕ) : ℝ) = G.1 - S.card := by
      rw [Nat.cast_sub (by exact_mod_cast h2)]
    have h4 : ((G.1 - S.card : ℕ) : ℝ) ≤ (univ.filter fun v ↦ G.color k c v < k).card := by
      exact_mod_cast h1
    linarith

/-- No `(k, δ)`-coloring: every partial `k`-coloring colors at most `q n` vertices, `q < 1 - δ`,
and there is a vertex. -/
theorem not_hasColoring_of_le {H : Graph} {k : ℕ} {q δ : ℝ} (hn : 0 < H.1) (hq : q < 1 - δ)
    (h : ∀ c, H.IsPartialColoring k c → (H.numColored k c : ℝ) ≤ q * H.1) :
    ¬ H.HasColoring k δ := by
  rintro ⟨c, hc, hcount⟩
  have hN : (0 : ℝ) < H.1 := by exact_mod_cast hn
  have := mul_lt_mul_of_pos_right hq hN
  linarith [h c hc]

/-! ### NP-hardness from Fact 8.1 -/

theorem graph_polytime :
    ComputableInPolyTime (fun G : Graph ↦ (G.1, adjTable G)) encGraph (encPair encNat encBits) :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

/-- Two isolated vertices. -/
abbrev twoPoints : Graph := ⟨2, ⊥⟩

/-- The graph, with two isolated vertices in place of the graph without vertices. -/
def nonempty (G : Graph) : Graph := if G.1 = 0 then twoPoints else G

section Machine

open ComputableInPolyTime

theorem nonempty_polytime : ComputableInPolyTime nonempty encGraph encGraph := by
  have h0 : ComputableInPolyTime (fun G : Graph ↦ decide (G.1 = 0)) encGraph encBool :=
    decide_eq' ((fst _ _).comp graph_polytime) (const 0)
  have h := ite' h0 (const twoPoints) id'
  have : nonempty = fun G ↦ if decide (G.1 = 0) then twoPoints else G :=
    funext fun G ↦ by simp [nonempty]
  rw [this]
  exact h

end Machine

open Classical in
theorem twoPoints_mem_yes {ε γ η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    twoPoints ∈ (bkGap ε γ η).yes := by
  refine ⟨fun v ↦ ?_, ({0} : Finset (Fin 2)), ({1} : Finset (Fin 2)), by decide,
    fun _ _ _ _ _ h ↦ h, fun _ _ _ _ _ h ↦ h, ?_, ?_⟩
  · have h : ((⊥ : SimpleGraph (Fin 2)).degree v : ℝ) ≤ η * ((2 : ℕ) : ℝ) := by
      simp only [SimpleGraph.bot_degree, Nat.cast_zero]
      positivity
    convert h
  · rw [card_singleton]
    push_cast
    linarith
  · rw [card_singleton]
    push_cast
    linarith

theorem pos_of_mem_no {ε γ η : ℝ} (hγ : 0 < γ) {G : Graph} (hG : G ∈ (bkGap ε γ η).no) :
    0 < G.1 := by
  obtain ⟨-, -, hno⟩ := hG
  have h0 := hno ∅ (by simp)
  simp only [card_empty, Nat.cast_zero] at h0
  exact_mod_cast pos_of_mul_pos_right h0 hγ.le

/-- **A reduction from Fact 8.1 proves NP-hardness**: a polynomial-time map sending the
yes-instances of `bkGap ε γ η` with a vertex to yes-instances of `Y`, and its no-instances to
no-instances of `Y`. (The graph without vertices, a yes-instance, is first replaced by two isolated
vertices.) -/
theorem npHard_of_reduction {ε γ η : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) (hη : 0 ≤ η)
    (hNP : PromiseProblem.NPHard encGraph (bkGap ε γ η)) {Y : PromiseProblem Graph}
    (R : Graph → Graph) (hR : ComputableInPolyTime R encGraph encGraph)
    (hyes : ∀ G ∈ (bkGap ε γ η).yes, 0 < G.1 → R G ∈ Y.yes)
    (hno : ∀ G ∈ (bkGap ε γ η).no, R G ∈ Y.no) : PromiseProblem.NPHard encGraph Y := by
  refine hNP.trans ⟨R ∘ nonempty, hR.comp nonempty_polytime, fun G hG ↦ ?_, fun G hG ↦ ?_⟩
  · change R (nonempty G) ∈ Y.yes
    by_cases h0 : G.1 = 0
    · have : nonempty G = twoPoints := by unfold nonempty; exact ite_eq_left h0
      rw [this]
      exact hyes _ (twoPoints_mem_yes hε hη) (by decide)
    · have : nonempty G = G := by unfold nonempty; exact ite_eq_right h0
      rw [this]
      exact hyes G hG (Nat.pos_of_ne_zero h0)
  · change R (nonempty G) ∈ Y.no
    have : nonempty G = G := by unfold nonempty; exact ite_eq_right (pos_of_mem_no hγ hG).ne'
    rw [this]
    exact hno G hG

/-! ### NP-hardness rules out algorithms -/

/-- **`NP ⊆ P`**: every problem in `NP`, with any encoding of its instances, is in `P`. -/
def NPSubsetP : Prop := ∀ ⦃T : Type⦄ (enc : T ↪ List Bool), NP enc ⊆ P enc

/-- **A reduction and an algorithm give `NP ⊆ P`.** -/
theorem npSubsetP_of_reduction {Y : PromiseProblem Graph}
    (hNP : PromiseProblem.NPHard encGraph Y)
    (R : Graph → Graph) (hR : ComputableInPolyTime R encGraph encGraph)
    (A : Graph → List ℕ) (hA : ComputableInPolyTime A encGraph encColoring) (k : ℕ)
    {q₀ q₁ : ℝ} (hq₀ : 0 ≤ q₀) (hq : q₀ < q₁)
    (hyes : ∀ G ∈ Y.yes, (R G).IsPartialColoring k (A (R G)) ∧
      q₁ * (R G).1 ≤ (R G).numColored k (A (R G)))
    (hno : ∀ G ∈ Y.no, 0 < (R G).1 ∧ ∀ c, (R G).IsPartialColoring k c →
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
  have hsolved : Y.SolvedBy f := by
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


/-- **NP-hardness rules out algorithms**: if the gap problem of `(k, δ)`-colorings of the graphs
with property `P` is NP-hard, with `δ ≤ 1`, then a polynomial-time algorithm finding
`(k, δ')`-colorings of them, for some `δ' < δ`, gives `NP ⊆ P`: checking its output against a
rational threshold between `1 - δ` and `1 - δ'` solves the gap problem. -/
theorem npSubsetP_of_npHard {P : Graph → Prop} {k : ℕ} {δ δ' : ℝ} (hδ : δ ≤ 1) (hδ' : δ' < δ)
    (hNP : PromiseProblem.NPHard encGraph (coloringGap P k δ))
    (A : Graph → List ℕ) (hA : ComputableInPolyTime A encGraph encColoring)
    (hsolve : ∀ G, P G → G.IsColoring k δ' (A G)) : NPSubsetP := by
  refine npSubsetP_of_reduction hNP id ComputableInPolyTime.id' A hA k (q₀ := 1 - δ)
    (q₁ := 1 - δ') (by linarith) (by linarith) (fun G hG ↦ hsolve G hG.1) fun G hG ↦ ?_
  have hpos : 0 < G.1 := by
    by_contra h0
    have h0' : (G.1 : ℝ) = 0 := by exact_mod_cast (show G.1 = 0 by omega)
    refine hG ⟨[], fun u ↦ absurd u.2 (by omega), ?_⟩
    rw [h0', mul_zero]
    exact Nat.cast_nonneg _
  refine ⟨hpos, fun c hc ↦ ?_⟩
  by_contra hlt
  exact hG ⟨c, hc, (lt_of_not_ge hlt).le⟩

end BHSV25.Hard
