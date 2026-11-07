module

public import BGHKLMM26.Hardness.Sparsify

/-!
# Sparsification: the kept edges

Deterministic facts about the greedy simplification `BGHKLMM26.Hard.keptEdges` of [BGHKLMM26,
Section 6], step (R2):

* the kept list is a sublist of the samples, with no loops and no pair twice in either direction
  (`BGHKLMM26.Hard.simpleList_keptEdges`), so that the edges of the graph are the kept pairs and
  the edges crossing a cut are the kept pairs it cuts (`BGHKLMM26.Hard.maxCutValue_graphOf`);
* every sample that is not kept is a loop, a repeat of an earlier sample, or beyond the first `Δ`
  samples at one of its ends (`BGHKLMM26.Hard.le_length_keptEdges_add`);
* the Max-Cut value of the sampled graph is at least `(Z_f - drops)/S` for every cut `f` with
  `Z_f` sampled edges cut by `f` (`BGHKLMM26.Hard.empCut_sub_drops_le`), and at most
  `max_f Z_f / (S - drops)` (`BGHKLMM26.Hard.maxCutValue_le_of_empCut`).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset

/-! ### The kept list -/

theorem keepStep_foldl_sublist (Δ : ℕ) (es : List (ℕ × ℕ)) :
    ∀ acc : List (ℕ × ℕ), List.Sublist (es.foldl (keepStep Δ) acc) (acc ++ es) := by
  induction es with
  | nil => intro acc; simp
  | cons e es ih =>
    intro acc
    refine (ih _).trans ?_
    have : List.Sublist (keepStep Δ acc e) (acc ++ [e]) := by
      unfold keepStep
      split_ifs
      · exact List.Sublist.refl _
      · exact List.sublist_append_left _ _
    simpa using this.append_right es

theorem keptEdges_sublist (Δ : ℕ) (es : List (ℕ × ℕ)) : List.Sublist (keptEdges Δ es) es := by
  unfold keptEdges
  simpa using keepStep_foldl_sublist Δ es []

theorem keptEdges_def (Δ : ℕ) (es : List (ℕ × ℕ)) : keptEdges Δ es = es.foldl (keepStep Δ) [] :=
  rfl

/-- The kept list has no loops and no pair twice, in either direction. -/
def SimpleList (kept : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ kept, p.1 ≠ p.2) ∧ kept.Nodup ∧ ∀ p ∈ kept, (p.2, p.1) ∉ kept

theorem simpleList_keepStep (Δ : ℕ) {kept : List (ℕ × ℕ)} (h : SimpleList kept) (e : ℕ × ℕ) :
    SimpleList (keepStep Δ kept e) := by
  unfold keepStep
  split_ifs with hk
  · simp only [keepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hk
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩ := hk
    obtain ⟨hl, hn, hr⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hl p hp
      · simp only [List.mem_singleton] at hp; subst hp; exact h1
    · refine List.nodup_append.2 ⟨hn, List.nodup_singleton e, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      exact h2 ha
    · intro p hp hq
      rcases List.mem_append.1 hp with hp | hp
      · rcases List.mem_append.1 hq with hq | hq
        · exact hr p hp hq
        · simp only [List.mem_singleton] at hq
          apply h3
          rw [← hq]
          exact hp
      · simp only [List.mem_singleton] at hp
        subst hp
        rcases List.mem_append.1 hq with hq | hq
        · exact h3 hq
        · simp only [List.mem_singleton, Prod.ext_iff] at hq
          exact h1 hq.1.symm
  · exact h

theorem simpleList_foldl (Δ : ℕ) (es : List (ℕ × ℕ)) :
    ∀ kept : List (ℕ × ℕ), SimpleList kept → SimpleList (es.foldl (keepStep Δ) kept) := by
  induction es with
  | nil => intro kept h; simpa using h
  | cons e es ih => intro kept h; exact ih _ (simpleList_keepStep Δ h e)

theorem simpleList_keptEdges (Δ : ℕ) (es : List (ℕ × ℕ)) : SimpleList (keptEdges Δ es) :=
  simpleList_foldl Δ es [] ⟨by simp, List.nodup_nil, by simp⟩

/-! ### Edges and cuts of `graphOf` -/

/-- Edges of `graphOf n kept` satisfying `Q` correspond to the kept pairs satisfying `Q'`. -/
theorem card_filter_edgeFinset_graphOf {n : ℕ} {kept : List (ℕ × ℕ)}
    (hin : ∀ p ∈ kept, p.1 < n ∧ p.2 < n) (hs : SimpleList kept)
    {_ : Fintype (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeSet}
    (Q : Sym2 (Fin n) → Prop) {_ : DecidablePred Q} (Q' : ℕ × ℕ → Prop) {_ : DecidablePred Q'}
    (hQ : ∀ a b : Fin n, a ≠ b → (Q s(a, b) ↔ Q' (a.1, b.1))) :
    ((SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeFinset.filter Q).card =
      (kept.filter fun p ↦ decide (Q' p)).length := by
  classical
  obtain ⟨hl, hn, hr⟩ := hs
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  symm
  refine Finset.card_bij (fun p hp ↦
      s(⟨p.1, (hin p (List.mem_filter.1 (List.mem_toFinset.1 hp)).1).1⟩,
        ⟨p.2, (hin p (List.mem_filter.1 (List.mem_toFinset.1 hp)).1).2⟩)) ?_ ?_ ?_
  · intro p hp
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.fromRel_adj]
    have hne : (⟨p.1, (hin p hp.1).1⟩ : Fin n) ≠ ⟨p.2, (hin p hp.1).2⟩ :=
      fun h ↦ hl p hp.1 (congrArg Fin.val h)
    refine ⟨⟨hne, Or.inl hp.1⟩, (hQ _ _ hne).2 hp.2⟩
  · intro p hp q hq hpq
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.mk.injEq] at h1 h2
      exact Prod.ext h1 h2
    · simp only [Fin.mk.injEq] at h1 h2
      exact absurd (show (q.2, q.1) ∈ kept by rw [← h1, ← h2]; exact hp.1) (hr q hq.1)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.fromRel_adj] at he
    obtain ⟨⟨hab, h | h⟩, hq⟩ := he
    · refine ⟨(a.1, b.1), ?_, rfl⟩
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨h, (hQ a b hab).1 hq⟩
    · refine ⟨(b.1, a.1), ?_, Sym2.eq_swap⟩
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      refine ⟨h, (hQ b a (Ne.symm hab)).1 ?_⟩
      rwa [Sym2.eq_swap]

/-! ### Lists of samples -/

theorem keptEdges_ofFn_succ (Δ : ℕ) {S : ℕ} (e : Fin (S + 1) → ℕ × ℕ) :
    keptEdges Δ (List.ofFn e) =
      keepStep Δ (keptEdges Δ (List.ofFn fun i ↦ e i.castSucc)) (e (Fin.last S)) := by
  rw [List.ofFn_succ_last]
  simp [keptEdges, List.foldl_append]

theorem length_filter_ofFn {α : Type*} {S : ℕ} (e : Fin S → α) (p : α → Bool) :
    ((List.ofFn e).filter p).length = (univ.filter fun i ↦ p (e i) = true).card := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [List.ofFn_succ_last, List.filter_append, List.length_append, ih,
      Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    by_cases h : p (e (Fin.last S)) <;> simp [h]

/-- The number of loops among the samples. -/
def nLoops {S : ℕ} (e : Fin S → ℕ × ℕ) : ℕ := (univ.filter fun i ↦ (e i).1 = (e i).2).card

/-- The number of samples equal to an earlier one, in either direction. -/
def nReps {S : ℕ} (e : Fin S → ℕ × ℕ) : ℕ :=
  (univ.filter fun i ↦ ∃ j, j < i ∧ (e j = e i ∨ e j = ((e i).2, (e i).1))).card

/-- The number of samples at `a`. -/
def nTouch {S : ℕ} (e : Fin S → ℕ × ℕ) (a : ℕ) : ℕ :=
  (univ.filter fun i ↦ (e i).1 = a ∨ (e i).2 = a).card

theorem nLoops_succ {S : ℕ} (e : Fin (S + 1) → ℕ × ℕ) :
    nLoops e = nLoops (fun i ↦ e i.castSucc) +
      if (e (Fin.last S)).1 = (e (Fin.last S)).2 then 1 else 0 := by
  unfold nLoops
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

theorem nTouch_succ {S : ℕ} (e : Fin (S + 1) → ℕ × ℕ) (a : ℕ) :
    nTouch e a = nTouch (fun i ↦ e i.castSucc) a +
      if (e (Fin.last S)).1 = a ∨ (e (Fin.last S)).2 = a then 1 else 0 := by
  unfold nTouch
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

theorem nReps_succ {S : ℕ} (e : Fin (S + 1) → ℕ × ℕ) :
    nReps e = nReps (fun i ↦ e i.castSucc) +
      if ∃ j : Fin S, e j.castSucc = e (Fin.last S) ∨
        e j.castSucc = ((e (Fin.last S)).2, (e (Fin.last S)).1) then 1 else 0 := by
  unfold nReps
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    apply propext
    rw [Fin.exists_fin_succ']
    constructor
    · rintro (⟨j, hj, h⟩ | ⟨hj, -⟩)
      · exact ⟨j, Fin.castSucc_lt_castSucc_iff.1 hj, h⟩
      · exact absurd hj (not_lt.2 (Fin.castSucc_lt_last i).le)
    · rintro ⟨j, hj, h⟩
      exact Or.inl ⟨j, Fin.castSucc_lt_castSucc_iff.2 hj, h⟩
  · congr 1
    apply propext
    rw [Fin.exists_fin_succ']
    constructor
    · rintro (⟨j, -, h⟩ | ⟨hj, -⟩)
      · exact ⟨j, h⟩
      · exact absurd hj (lt_irrefl _)
    · rintro ⟨j, h⟩
      exact Or.inl ⟨j, Fin.castSucc_lt_last j, h⟩

theorem degIn_keptEdges_le_nTouch (Δ : ℕ) {S : ℕ} (e : Fin S → ℕ × ℕ) (a : ℕ) :
    degIn (keptEdges Δ (List.ofFn e)) a ≤ nTouch e a := by
  unfold degIn nTouch
  have := length_filter_ofFn e (fun p ↦ decide (p.1 = a ∨ p.2 = a))
  simp only [decide_eq_true_eq] at this
  rw [← this]
  exact ((keptEdges_sublist Δ _).filter _).length_le

theorem sum_add_one_le {A : Finset ℕ} {f g : ℕ → ℕ} (hfg : ∀ b ∈ A, f b ≤ g b) {a : ℕ}
    (ha : a ∈ A) (h : f a + 1 ≤ g a) : (∑ b ∈ A, f b) + 1 ≤ ∑ b ∈ A, g b := by
  rw [← Finset.add_sum_erase A f ha, ← Finset.add_sum_erase A g ha]
  have := Finset.sum_le_sum (s := A.erase a) fun b hb ↦ hfg b (Finset.mem_of_mem_erase hb)
  omega

theorem keepOK_false {Δ : ℕ} {K : List (ℕ × ℕ)} {e : ℕ × ℕ} (h : ¬ keepOK Δ K e = true) :
    e.1 = e.2 ∨ e ∈ K ∨ (e.2, e.1) ∈ K ∨ Δ ≤ degIn K e.1 ∨ Δ ≤ degIn K e.2 := by
  by_contra hc
  push Not at hc
  apply h
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  simp [keepOK, h1, h2, h3, h4, h5]

/-- **The number of dropped samples**: every sample that is not kept is a loop, a repeat of an
earlier sample, or beyond the first `Δ` samples at one of its ends. -/
theorem le_length_keptEdges_add (Δ : ℕ) (A : Finset ℕ) :
    ∀ {S : ℕ} (e : Fin S → ℕ × ℕ), (∀ i, (e i).1 ∈ A ∧ (e i).2 ∈ A) →
      S ≤ (keptEdges Δ (List.ofFn e)).length + nLoops e + nReps e +
        ∑ a ∈ A, (nTouch e a - Δ) := by
  intro S
  induction S with
  | zero => intro e _; simp
  | succ S ih =>
    intro e hA
    have ih' := ih (fun i ↦ e i.castSucc) (fun i ↦ hA _)
    rw [keptEdges_ofFn_succ, nLoops_succ, nReps_succ]
    have hsum : ∀ b ∈ A, nTouch (fun i ↦ e i.castSucc) b - Δ ≤ nTouch e b - Δ := by
      intro b _
      rw [nTouch_succ]
      omega
    have hsum' := Finset.sum_le_sum hsum
    set K := keptEdges Δ (List.ofFn fun i ↦ e i.castSucc) with hK
    unfold keepStep
    by_cases hk : keepOK Δ K (e (Fin.last S)) = true
    · simp only [hk, ↓reduceIte]
      simp only [List.length_append, List.length_singleton]
      split_ifs <;> omega
    · simp only [hk, Bool.false_eq_true, ↓reduceIte]
      have hk := keepOK_false hk
      have hmem : ∀ p ∈ K, ∃ j : Fin S, e j.castSucc = p := by
        intro p hp
        have := (keptEdges_sublist Δ _).subset hp
        simpa [List.mem_ofFn] using this
      rcases hk with h | h | h | h | h
      · simp only [h, ↓reduceIte]
        split_ifs <;> omega
      · obtain ⟨j, hj⟩ := hmem _ h
        have hex : ∃ j : Fin S, e j.castSucc = e (Fin.last S) ∨
            e j.castSucc = ((e (Fin.last S)).2, (e (Fin.last S)).1) := ⟨j, Or.inl hj⟩
        simp only [hex, ↓reduceIte]
        split_ifs <;> omega
      · obtain ⟨j, hj⟩ := hmem _ h
        have hex : ∃ j : Fin S, e j.castSucc = e (Fin.last S) ∨
            e j.castSucc = ((e (Fin.last S)).2, (e (Fin.last S)).1) := ⟨j, Or.inr hj⟩
        simp only [hex, ↓reduceIte]
        split_ifs <;> omega
      · have h1 := degIn_keptEdges_le_nTouch Δ (fun i ↦ e i.castSucc) (e (Fin.last S)).1
        have h2 := sum_add_one_le hsum (hA (Fin.last S)).1 (by
          rw [nTouch_succ e]
          simp only [true_or, ↓reduceIte]
          rw [← hK] at h1
          omega)
        split_ifs <;> omega
      · have h1 := degIn_keptEdges_le_nTouch Δ (fun i ↦ e i.castSucc) (e (Fin.last S)).2
        have h2 := sum_add_one_le hsum (hA (Fin.last S)).2 (by
          rw [nTouch_succ e]
          simp only [or_true, ↓reduceIte]
          rw [← hK] at h1
          omega)
        split_ifs <;> omega

/-! ### The sampled graph -/

section Sampled

variable {Ω : Type} {n S : ℕ}

/-- The sampled edges, as pairs of numbers. -/
def sampleEdge (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) (i : Fin S) : ℕ × ℕ :=
  ((dec (ω i)).1.val, (dec (ω i)).2.val)

/-- The kept samples. -/
def keptS (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) : List (ℕ × ℕ) :=
  keptEdges Δ (List.ofFn (sampleEdge dec ω))

/-- The number of samples that are not kept. -/
def drops (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) : ℕ := S - (keptS Δ dec ω).length

/-- The number of samples cut by `f`. -/
def empCut (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) (f : Fin n → Bool) : ℕ :=
  (univ.filter fun i ↦ f (dec (ω i)).1 ≠ f (dec (ω i)).2).card

/-- A cut of `Fin n`, read on numbers. -/
def fext (f : Fin n → Bool) (a : ℕ) : Bool := if h : a < n then f ⟨a, h⟩ else false

theorem fext_val (f : Fin n → Bool) (a : Fin n) : fext f a.1 = f a := by
  simp [fext, a.2]

theorem length_keptS_le (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) :
    (keptS Δ dec ω).length ≤ S :=
  (keptEdges_sublist Δ _).length_le.trans (by simp)

theorem drops_cast (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) :
    (drops Δ dec ω : ℝ) = S - (keptS Δ dec ω).length := by
  rw [drops, Nat.cast_sub (length_keptS_le Δ dec ω)]

theorem keptS_lt (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) :
    ∀ p ∈ keptS Δ dec ω, p.1 < n ∧ p.2 < n := by
  intro p hp
  have := (keptEdges_sublist Δ _).subset hp
  simp only [List.mem_ofFn, sampleEdge] at this
  obtain ⟨i, rfl⟩ := this
  exact ⟨(dec (ω i)).1.2, (dec (ω i)).2.2⟩

/-- The kept samples cut by `f`. -/
def keptCut (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) (f : Fin n → Bool) : ℕ :=
  ((keptS Δ dec ω).filter fun p ↦ decide (fext f p.1 ≠ fext f p.2)).length

theorem length_filter_sample (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) (f : Fin n → Bool) :
    ((List.ofFn (sampleEdge dec ω)).filter fun p ↦ decide (fext f p.1 ≠ fext f p.2)).length =
      empCut dec ω f := by
  rw [length_filter_ofFn]
  simp [empCut, sampleEdge, fext_val]

theorem keptCut_le_empCut (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) (f : Fin n → Bool) :
    keptCut Δ dec ω f ≤ empCut dec ω f := by
  rw [← length_filter_sample]
  exact ((keptEdges_sublist Δ _).filter _).length_le

theorem empCut_le_keptCut_add (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω)
    (f : Fin n → Bool) : empCut dec ω f ≤ keptCut Δ dec ω f + drops Δ dec ω := by
  rw [← length_filter_sample]
  unfold keptCut drops keptS
  have hsub := keptEdges_sublist Δ (List.ofFn (sampleEdge dec ω))
  have h1 := List.length_eq_length_filter_add (l := List.ofFn (sampleEdge dec ω))
    (fun p ↦ decide (fext f p.1 ≠ fext f p.2))
  have h2 := List.length_eq_length_filter_add (l := keptEdges Δ (List.ofFn (sampleEdge dec ω)))
    (fun p ↦ decide (fext f p.1 ≠ fext f p.2))
  have h3 := (hsub.filter fun p ↦ !decide (fext f p.1 ≠ fext f p.2)).length_le
  simp only [List.length_ofFn] at h1
  omega

theorem card_edgeFinset_graphOf {kept : List (ℕ × ℕ)} (hin : ∀ p ∈ kept, p.1 < n ∧ p.2 < n)
    (hs : SimpleList kept)
    {inst : Fintype (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeSet} :
    (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeFinset.card = kept.length := by
  have := @card_filter_edgeFinset_graphOf n kept hin hs inst (fun _ ↦ True)
    (fun _ ↦ instDecidableTrue) (fun _ ↦ True) (fun _ ↦ instDecidableTrue) (fun _ _ _ ↦ Iff.rfl)
  simp only [Finset.filter_true, decide_true, List.filter_true] at this
  exact this

open Classical in
theorem maxCutValue_graphOf {kept : List (ℕ × ℕ)} (hin : ∀ p ∈ kept, p.1 < n ∧ p.2 < n)
    (hs : SimpleList kept) :
    maxCutValue (graphOf n kept) =
      ((univ.sup (fun f : Fin n → Bool ↦
        (kept.filter fun p ↦ decide (fext f p.1 ≠ fext f p.2)).length) : ℕ) : ℝ) /
        kept.length := by
  unfold maxCutValue graphOf
  dsimp only
  congr 3
  · funext f
    unfold cutSize
    refine card_filter_edgeFinset_graphOf hin hs _ _ ?_
    intro a b hab
    dsimp only
    rw [fext_val, fext_val]
    constructor
    · intro h
      exact h a (Sym2.mem_mk_left a b) b (Sym2.mem_mk_right a b) hab
    · intro h u hu v hv huv
      rcases Sym2.mem_iff.1 hu with rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact absurd rfl huv
      · exact h
      · exact Ne.symm h
      · exact absurd rfl huv
  · exact card_edgeFinset_graphOf hin hs

theorem maxCutValue_sampledGraph (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) :
    maxCutValue (sampledGraph n Δ dec ω) =
      ((univ.sup (keptCut Δ dec ω) : ℕ) : ℝ) / (keptS Δ dec ω).length :=
  maxCutValue_graphOf (keptS_lt Δ dec ω) (simpleList_keptEdges Δ _)

/-- **A lower bound on the Max-Cut value** from one cut of the samples. -/
theorem empCut_sub_drops_le (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω)
    (f : Fin n → Bool) :
    (empCut dec ω f : ℝ) - drops Δ dec ω ≤ S * maxCutValue (sampledGraph n Δ dec ω) := by
  classical
  rw [maxCutValue_sampledGraph, drops_cast]
  have h1 : (empCut dec ω f : ℝ) ≤ keptCut Δ dec ω f + drops Δ dec ω := by
    exact_mod_cast empCut_le_keptCut_add Δ dec ω f
  rw [drops_cast] at h1
  have h2 : (keptCut Δ dec ω f : ℝ) ≤ ((univ.sup (keptCut Δ dec ω) : ℕ) : ℝ) :=
    Nat.cast_le.2 (Finset.le_sup (mem_univ f))
  have hk := length_keptS_le Δ dec ω
  have h3 : (keptCut Δ dec ω f : ℝ) ≤ (keptS Δ dec ω).length := by
    exact_mod_cast (List.length_filter_le _ _)
  rcases Nat.eq_zero_or_pos (keptS Δ dec ω).length with h0 | h0
  · rw [h0] at h3 ⊢
    simp only [Nat.cast_zero, div_zero, mul_zero] at h3 ⊢
    linarith
  · have hpos : (0 : ℝ) < (keptS Δ dec ω).length := by exact_mod_cast h0
    have hkS : ((keptS Δ dec ω).length : ℝ) ≤ S := by exact_mod_cast hk
    have : ((univ.sup (keptCut Δ dec ω) : ℕ) : ℝ) ≤
        S * (((univ.sup (keptCut Δ dec ω) : ℕ) : ℝ) / (keptS Δ dec ω).length) := by
      rw [mul_div_assoc', le_div_iff₀ hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right hkS (Nat.cast_nonneg _)
    linarith

/-- **An upper bound on the Max-Cut value** from all cuts of the samples. -/
theorem maxCutValue_le_of_empCut (Δ : ℕ) (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) {B K : ℝ}
    (hB : ∀ f, (empCut dec ω f : ℝ) ≤ B) (hK : (drops Δ dec ω : ℝ) ≤ K) (hKS : K < S) :
    maxCutValue (sampledGraph n Δ dec ω) ≤ B / (S - K) := by
  classical
  rw [maxCutValue_sampledGraph]
  rw [drops_cast] at hK
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin n → Bool)) univ_nonempty
    (keptCut Δ dec ω)
  rw [hf]
  have h1 : (keptCut Δ dec ω f : ℝ) ≤ B :=
    (Nat.cast_le.2 (keptCut_le_empCut Δ dec ω f)).trans (hB f)
  have hpos : (0 : ℝ) < S - K := by linarith
  have hB0 : 0 ≤ B := (Nat.cast_nonneg _).trans h1
  calc (keptCut Δ dec ω f : ℝ) / (keptS Δ dec ω).length ≤ B / (keptS Δ dec ω).length :=
        div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
    _ ≤ B / (S - K) := div_le_div_of_nonneg_left hB0 hpos (by linarith)

end Sampled

end BGHKLMM26.Hard
