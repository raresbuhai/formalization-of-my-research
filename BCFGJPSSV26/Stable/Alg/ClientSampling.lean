module

public import BCFGJPSSV26.Stable.Alg.Coins
public import BCFGJPSSV26.Stable.Alg.Mixed
public import BCFGJPSSV26.Stable.Structure.ClientWitness
public import BCFGJPSSV26.Stable.Stability.FewNotInSync
public import BCFGJPSSV26.Stable.LocalSearch.ThreeApprox

/-!
# Client sampling

[BCFGJPSSV26b, Algorithm 1]: `2 s` iterations, each reading three chunks `(u_s, u_k, u_r)`:
sample a client `ℓ` with probability proportional to `d(ℓ, LS)`; skip on a fair bit; otherwise
add the dummy `(ℓ, grid(d(ℓ, LS), x))` with a uniform grid index `x` (`BCFGJPSSV26.Stable.csStep`,
`BCFGJPSSV26.Stable.csRun`). The paper reads the skip coin after sampling; the order of
independent chunks does not matter.

**The process lemma** (`BCFGJPSSV26.Stable.Hyp.card_clientWitness`; the client-sampling theorem
of [BCFGJPSSV26b, Section 4.2] and the lemma of its proof in [BCFGJPSSV26b, Section 4.6]): at
least `q₁^(2s) K^(6s)` of the chunk vectors give a good outcome
(`BCFGJPSSV26.Stable.ClientWitness`), `q₁ = 1/(440 N⁸)`. Proof:
`BCFGJPSSV26.Stable.guided_count` with the invariant (A)–(E) described below: in each
iteration, the good chunks (an acceptable client of an unhit cluster of `O₁`, the right skip bit,
a grid radius in the target interval) have density at least `q₁` whenever progress is needed,
since the acceptable clients carry at least `ε⁶ opt` of the total weight `cost(S) ≤ 4 opt`.

The proof, in the namespace `BCFGJPSSV26.Stable.ClientSampling`:

* the hit and early clusters of a list of dummies (`hit`, `early`), the sums `Σ₆` and `Σ_κ` of the
  costs in `S` of the cores still to hit (`sum6`, `sumK`), the target radii (`tgt`) and the punched
  cores (`pcore`, the clients of a core at distance at least `ε⁶ per` from `S`);
* the invariant (`InvL`): good dummies of distinct clusters of `O₁` (A, B), all early in the first
  `s` iterations (E), and `Σ₆ < ε⁵ opt` unless `t < s` hits were made (C), `Σ_κ < ε⁵ opt` unless
  `t - s` hits were made after the first `s` iterations (D); it holds initially (`invL_zero`), is
  kept by skips when no progress is needed (`invL_skip`) and by new dummies of unhit clusters
  (`invL_add`), and gives a `ClientWitness` after `2 s` iterations (`witness`);
* the good chunks (`GoodCh`) keep the invariant (`inv_step`); a good radius exists by Part II's
  case analysis on `r₀ ≤ per/ε` (`exists_grid_rad`); if progress is needed the acceptable clients
  get at least `2^b/(8 N⁶)` sampling chunks (`card_acc_ge`), so the good chunks have density at
  least `q₁` (`density`);
* `2 s` triples of chunks are `6 s` chunks (`spread`, `foldl_eq_runFin`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- One iteration of the client sampling. -/
def csStep (N : ℕ) (x : Raw) (LS : List ℕ) (b : ℕ) (Λ : List DumQ) (us uk ur : ℕ) :
    List DumQ :=
  let ℓ := wsample b ((List.range x.n).map fun j ↦ x.dSetQ j LS) us
  if cbit b uk then Λ else Λ ++ [(ℓ, grid N (x.dSetQ ℓ LS) (cunif (Par.Gr N) ur))]

/-- **The client sampling**: `2 s` iterations of three chunks. -/
def csRun (N : ℕ) (x : Raw) (LS : List ℕ) (s b : ℕ) (ch : ℕ → ℕ) : List DumQ :=
  (List.range (2 * s)).foldl
    (fun Λ i ↦ csStep N x LS b Λ (ch (3 * i)) (ch (3 * i + 1)) (ch (3 * i + 2))) []

/-- An iteration adds only client leaders. -/
theorem csStep_valid {I : Instance} (hn : 1 ≤ I.n) (N : ℕ) (LS : List ℕ) (b : ℕ)
    {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ) (us uk ur : ℕ) :
    (toRaw I).ValidDums (csStep N (toRaw I) LS b Λ us uk ur) := by
  unfold csStep
  dsimp only
  split_ifs
  · exact hΛ
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hΛ l hl
    · rw [List.mem_singleton] at hl
      subst hl
      have hw : ((List.range (toRaw I).n).map fun j ↦ (toRaw I).dSetQ j LS) ≠ [] := by
        rw [← List.length_pos_iff, List.length_map, List.length_range, Raw.n_toRaw]
        omega
      have h := wsample_lt (b := b) hw us
      rw [List.length_map, List.length_range, Raw.n_toRaw] at h
      rw [Raw.n_toRaw, Raw.m_toRaw]
      omega

/-- The leaders are clients. -/
theorem csRun_valid {I : Instance} (hn : 1 ≤ I.n) (N : ℕ) (LS : List ℕ) (s b : ℕ)
    (ch : ℕ → ℕ) : (toRaw I).ValidDums (csRun N (toRaw I) LS s b ch) := by
  unfold csRun
  suffices h : ∀ (l : List ℕ) (Λ : List DumQ), (toRaw I).ValidDums Λ →
      (toRaw I).ValidDums (l.foldl (fun Λ i ↦ csStep N (toRaw I) LS b Λ (ch (3 * i))
        (ch (3 * i + 1)) (ch (3 * i + 2))) Λ) from
    h _ _ fun l hl ↦ absurd hl List.not_mem_nil
  intro l
  induction l with
  | nil => exact fun Λ hΛ ↦ hΛ
  | cons i l ih => exact fun Λ hΛ ↦ ih _ (csStep_valid hn N LS b hΛ _ _ _)

namespace ClientSampling

/-! ### Generic helpers -/

/-- A sum over `List.range` is a sum over `Finset.range`. -/
theorem sum_map_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Two members of a list related by a symmetric relation that holds for no two of its
positions are equal. -/
theorem eq_of_pairwise_not {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {l : List α} (h : l.Pairwise fun a b ↦ ¬ R a b) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : R a b) : a = b := by
  by_contra hne
  have : Std.Symm fun a b ↦ ¬ R a b := ⟨fun a b h h' ↦ h (hR _ _ h')⟩
  exact h.forall ha hb hne hab

/-- Counting pairs fiber by fiber. -/
theorem card_prod_ge {α β : Type*} [Fintype α] [Fintype β] (P : α × β → Prop)
    [DecidablePred P] (A : Finset α) (m : ℝ)
    (h : ∀ a ∈ A, m ≤ (univ.filter fun b ↦ P (a, b)).card) :
    A.card * m ≤ (univ.filter P).card := by
  classical
  have h1 : (univ.filter P).card = ∑ a, (univ.filter fun b ↦ P (a, b)).card := by
    rw [card_filter, Fintype.sum_prod_type]
    exact sum_congr rfl fun a _ ↦ (card_filter _ _).symm
  rw [h1]
  push_cast
  calc (A.card : ℝ) * m = ∑ a ∈ A, m := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ A, ((univ.filter fun b ↦ P (a, b)).card : ℝ) := sum_le_sum h
    _ ≤ ∑ a, ((univ.filter fun b ↦ P (a, b)).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ A) fun _ _ _ ↦ Nat.cast_nonneg _

section Analysis

/-! ### The objects of the analysis -/

variable (X : Ctx)

/-- A dummy led by a client of `A`. -/
def LedIn (d : Dummy X.I) (A : Finset (Fin X.I.n)) : Prop := ∃ j ∈ A, d.leader = .inl j

open Classical in
/-- The hit clusters: those containing a leader. -/
noncomputable def hit (Λ : List (Dummy X.I)) : Finset (Fin X.I.m) :=
  X.O.filter fun c ↦ ∃ d ∈ Λ, LedIn X d (X.C c)

open Classical in
/-- The early clusters: those with a leader in `core_{6ε}`. -/
noncomputable def early (Λ : List (Dummy X.I)) : Finset (Fin X.I.m) :=
  X.O.filter fun c ↦ ∃ d ∈ Λ, LedIn X d (X.core (6 * X.ε) c)

/-- `Σ₆`: the cost in `S` of the `core_{6ε}` of the non-early clusters of `O₁`. -/
noncomputable def sum6 (Λ : List (Dummy X.I)) : ℝ :=
  ∑ c ∈ X.O1 \ early X Λ, X.costS (X.core (6 * X.ε) c)

/-- `Σ_κ`: the cost in `S` of the `core_κ` of the missed clusters of `O₁`. -/
noncomputable def sumK (Λ : List (Dummy X.I)) : ℝ :=
  ∑ c ∈ X.O1 \ hit X Λ, X.costS (X.core (X.kap c) c)

/-- The target radius of a leader `j` of the cluster of `c`. -/
noncomputable def tgt (j : Fin X.I.n) (c : Fin X.I.m) : ℝ :=
  (1 + (if j ∈ X.core (6 * X.ε) c then 0 else X.kap c) + 8 * X.ε) * X.per c + X.ε * X.avgS c

open Classical in
/-- The punched core: the clients of the core at distance at least `ε⁶ per` from `S`. -/
noncomputable def pcore (γ : ℝ) (c : Fin X.I.m) : Finset (Fin X.I.n) :=
  (X.core γ c).filter fun j ↦ X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S

/-- A good dummy: led by a client of the `core_κ` of a cluster of `O₁`, with a radius between
the distance to the center and the target. -/
def GoodDum (d : Dummy X.I) : Prop :=
  ∃ j c, d.leader = .inl j ∧ c ∈ X.O1 ∧ j ∈ X.core (X.kap c) c ∧ X.dist j c ≤ d.radius ∧
    d.radius ≤ tgt X j c

/-- Two dummies led from the same optimal cluster. -/
def SameCl (d d' : Dummy X.I) : Prop := ∃ c, LedIn X d (X.C c) ∧ LedIn X d' (X.C c)

/-- (A), (B): good dummies of distinct clusters. -/
structure GoodL (Λ : List (Dummy X.I)) : Prop where
  good : ∀ d ∈ Λ, GoodDum X d
  pw : Λ.Pairwise fun d d' ↦ ¬ SameCl X d d'
  card : (hit X Λ).card = Λ.length

/-- Progress is needed: the relevant cores are still expensive. -/
def NeedProg (t : ℕ) (Λ : List (Dummy X.I)) : Prop :=
  (t < X.s ∧ X.ε ^ 5 * X.opt ≤ sum6 X Λ) ∨ (X.s ≤ t ∧ X.ε ^ 5 * X.opt ≤ sumK X Λ)

/-- The invariant (A)–(E) after `t` iterations. -/
structure InvL (t : ℕ) (Λ : List (Dummy X.I)) : Prop where
  good : GoodL X Λ
  early : t ≤ X.s → ∀ d ∈ Λ, ∃ c, LedIn X d (X.core (6 * X.ε) c)
  c6 : sum6 X Λ < X.ε ^ 5 * X.opt ∨ (t < X.s ∧ t ≤ (hit X Λ).card)
  cK : sumK X Λ < X.ε ^ 5 * X.opt ∨ (t < 2 * X.s ∧ t - X.s ≤ (hit X Λ).card)

variable {X}

/-! ### Basic facts -/

theorem mem_core {γ : ℝ} {c : Fin X.I.m} {j : Fin X.I.n} :
    j ∈ X.core γ c ↔ j ∈ X.C c ∧ X.dist j c ≤ (1 + γ) * X.per c := by
  unfold Ctx.core Stable.core
  rw [mem_filter]
  rfl

theorem core_sub_C (γ : ℝ) (c : Fin X.I.m) : X.core γ c ⊆ X.C c := core_subset _ _ _ _

theorem pcore_sub_core (γ : ℝ) (c : Fin X.I.m) : pcore X γ c ⊆ X.core γ c := filter_subset _ _

theorem mem_pcore {γ : ℝ} {c : Fin X.I.m} {j : Fin X.I.n} :
    j ∈ pcore X γ c ↔ j ∈ X.core γ c ∧ X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S := by
  classical
  unfold pcore
  rw [mem_filter]

theorem pcore_mono (hv : X.I.Valid) {γ γ' : ℝ} (h : γ ≤ γ') (c : Fin X.I.m) :
    pcore X γ c ⊆ pcore X γ' c := by
  intro j hj
  rw [mem_pcore] at hj ⊢
  exact ⟨core_mono h hv _ _ hj.1, hj.2⟩

theorem eq_of_mem_C {j : Fin X.I.n} {c c' : Fin X.I.m} (h : j ∈ X.C c) (h' : j ∈ X.C c') :
    c = c' := by
  by_contra hne
  exact disjoint_left.1 (Instance.disjoint_cluster X.O hne) h h'

theorem mem_O_of_mem_C {j : Fin X.I.n} {c : Fin X.I.m} (h : j ∈ X.C c) : c ∈ X.O := by
  by_contra hc
  have h0 : X.C c = ∅ := Instance.cluster_eq_empty_of_notMem hc
  rw [h0] at h
  simp at h

theorem ledIn_mk {j : Fin X.I.n} {r : ℝ} {A : Finset (Fin X.I.n)} :
    LedIn X ⟨.inl j, r⟩ A ↔ j ∈ A := by
  constructor
  · rintro ⟨j', hj', h⟩
    have h' : j = j' := Sum.inl_injective h
    rw [h']
    exact hj'
  · intro h
    exact ⟨j, h, rfl⟩

theorem sameCl_symm (d d' : Dummy X.I) : SameCl X d d' → SameCl X d' d := by
  rintro ⟨c, h, h'⟩
  exact ⟨c, h', h⟩

theorem ledIn_unique {d : Dummy X.I} {A A' : Finset (Fin X.I.n)} {c c' : Fin X.I.m}
    (hA : A ⊆ X.C c) (hA' : A' ⊆ X.C c') (h : LedIn X d A) (h' : LedIn X d A') : c = c' := by
  obtain ⟨j, hj, hl⟩ := h
  obtain ⟨j', hj', hl'⟩ := h'
  rw [hl] at hl'
  have e : j = j' := Sum.inl_injective hl'
  rw [← e] at hj'
  exact eq_of_mem_C (hA hj) (hA' hj')

theorem goodDum_of_ledIn {d : Dummy X.I} (hd : GoodDum X d) {c : Fin X.I.m}
    (hc : LedIn X d (X.C c)) :
    ∃ j, d.leader = .inl j ∧ c ∈ X.O1 ∧ j ∈ X.core (X.kap c) c ∧ X.dist j c ≤ d.radius ∧
      d.radius ≤ tgt X j c := by
  obtain ⟨j, c', hl, hc', hj, h1, h2⟩ := hd
  have e : c' = c := ledIn_unique (core_sub_C _ _) subset_rfl ⟨j, hj, hl⟩ hc
  subst e
  exact ⟨j, hl, hc', hj, h1, h2⟩

theorem mem_hit {Λ : List (Dummy X.I)} {c : Fin X.I.m} :
    c ∈ hit X Λ ↔ c ∈ X.O ∧ ∃ d ∈ Λ, LedIn X d (X.C c) := by
  classical
  unfold hit
  rw [mem_filter]

theorem mem_early {Λ : List (Dummy X.I)} {c : Fin X.I.m} :
    c ∈ early X Λ ↔ c ∈ X.O ∧ ∃ d ∈ Λ, LedIn X d (X.core (6 * X.ε) c) := by
  classical
  unfold early
  rw [mem_filter]

theorem hit_nil : hit X [] = ∅ := by
  ext c
  simp [mem_hit]

theorem hit_sub_O1 {Λ : List (Dummy X.I)} (hΛ : ∀ d ∈ Λ, GoodDum X d) : hit X Λ ⊆ X.O1 := by
  intro c hc
  obtain ⟨-, d, hd, hl⟩ := mem_hit.1 hc
  obtain ⟨j, -, hc', -⟩ := goodDum_of_ledIn (hΛ d hd) hl
  exact hc'

theorem early_sub_hit (Λ : List (Dummy X.I)) : early X Λ ⊆ hit X Λ := by
  intro c hc
  obtain ⟨hO, d, hd, j, hj, hl⟩ := mem_early.1 hc
  exact mem_hit.2 ⟨hO, d, hd, j, core_sub_C _ _ hj, hl⟩

theorem hit_sub_early {Λ : List (Dummy X.I)}
    (h : ∀ d ∈ Λ, ∃ c, LedIn X d (X.core (6 * X.ε) c)) : hit X Λ ⊆ early X Λ := by
  intro c hc
  obtain ⟨hO, d, hd, hl⟩ := mem_hit.1 hc
  obtain ⟨c', hl'⟩ := h d hd
  have e : c' = c := ledIn_unique (core_sub_C _ _) subset_rfl hl' hl
  subst e
  exact mem_early.2 ⟨hO, d, hd, hl'⟩

theorem hit_mono (Λ l : List (Dummy X.I)) : hit X Λ ⊆ hit X (Λ ++ l) := by
  intro c hc
  obtain ⟨hO, d, hd, hl⟩ := mem_hit.1 hc
  exact mem_hit.2 ⟨hO, d, List.mem_append_left _ hd, hl⟩

theorem early_mono (Λ l : List (Dummy X.I)) : early X Λ ⊆ early X (Λ ++ l) := by
  intro c hc
  obtain ⟨hO, d, hd, hl⟩ := mem_early.1 hc
  exact mem_early.2 ⟨hO, d, List.mem_append_left _ hd, hl⟩

theorem hit_append_mk {Λ : List (Dummy X.I)} {j : Fin X.I.n} {c : Fin X.I.m} (hj : j ∈ X.C c)
    (r : ℝ) : hit X (Λ ++ [⟨.inl j, r⟩]) = insert c (hit X Λ) := by
  ext c'
  rw [mem_insert, mem_hit, mem_hit]
  constructor
  · rintro ⟨hO, d, hd, hl⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact Or.inr ⟨hO, d, hd, hl⟩
    · rw [List.mem_singleton] at hd
      subst hd
      exact Or.inl (eq_of_mem_C (ledIn_mk.1 hl) hj)
  · rintro (e | ⟨hO, d, hd, hl⟩)
    · subst e
      exact ⟨mem_O_of_mem_C hj, _, List.mem_append_right _ (List.mem_singleton_self _),
        ledIn_mk.2 hj⟩
    · exact ⟨hO, d, List.mem_append_left _ hd, hl⟩

theorem sum6_anti (hv : X.I.Valid) (Λ l : List (Dummy X.I)) : sum6 X (Λ ++ l) ≤ sum6 X Λ :=
  sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff subset_rfl (early_mono Λ l))
    fun _ _ _ ↦ Instance.costOn_nonneg hv _ _

theorem sumK_anti (hv : X.I.Valid) (Λ l : List (Dummy X.I)) : sumK X (Λ ++ l) ≤ sumK X Λ :=
  sum_le_sum_of_subset_of_nonneg (sdiff_subset_sdiff subset_rfl (hit_mono Λ l))
    fun _ _ _ ↦ Instance.costOn_nonneg hv _ _

theorem sum6_eq_zero {Λ : List (Dummy X.I)} (h : X.O1 ⊆ early X Λ) : sum6 X Λ = 0 := by
  rw [sum6, sdiff_eq_empty_iff_subset.2 h, sum_empty]

theorem sumK_eq_zero {Λ : List (Dummy X.I)} (h : X.O1 ⊆ hit X Λ) : sumK X Λ = 0 := by
  rw [sumK, sdiff_eq_empty_iff_subset.2 h, sum_empty]

section Hyp

variable (H : Hyp X)
include H

theorem thr_pos : 0 < X.ε ^ 5 * X.opt := mul_pos (pow_pos H.eps_pos 5) H.opt_pos

theorem s_pos : 0 < X.s := by
  have h1 := X.P.N_pos
  have h2 := H.one_le_L
  unfold Ctx.s Par.s
  positivity

theorem O1_sub_hit {Λ : List (Dummy X.I)} (hΛ : ∀ d ∈ Λ, GoodDum X d)
    (hs : X.s ≤ (hit X Λ).card) : X.O1 ⊆ hit X Λ := by
  have heq : hit X Λ = X.O1 := eq_of_subset_of_card_le (hit_sub_O1 hΛ) (H.card_O1_le.trans hs)
  intro c hc
  rw [heq]
  exact hc

/-! ### The invariant -/

theorem invL_zero : InvL X 0 [] := by
  have hs := s_pos H
  refine ⟨⟨by simp, List.Pairwise.nil, by simp [hit_nil]⟩, by simp, Or.inr ⟨hs, by simp⟩,
    Or.inr ⟨by omega, by simp⟩⟩

omit H in
theorem invL_skip {t : ℕ} {Λ : List (Dummy X.I)} (h : InvL X t Λ) (hnp : ¬ NeedProg X t Λ) :
    InvL X (t + 1) Λ := by
  refine ⟨h.good, fun ht ↦ h.early (by omega), ?_, ?_⟩
  · rcases h.c6 with h6 | ⟨ht, -⟩
    · exact Or.inl h6
    · exact Or.inl (lt_of_not_ge fun h6 ↦ hnp (Or.inl ⟨ht, h6⟩))
  · rcases h.cK with hK | ⟨ht, hc⟩
    · exact Or.inl hK
    · by_cases hts : X.s ≤ t
      · exact Or.inl (lt_of_not_ge fun hK ↦ hnp (Or.inr ⟨hts, hK⟩))
      · exact Or.inr ⟨by omega, by omega⟩

theorem invL_add {t : ℕ} {Λ : List (Dummy X.I)} {j : Fin X.I.n} {c : Fin X.I.m} {r : ℝ}
    (h : InvL X t Λ) (hc : c ∈ X.O1) (hcn : c ∉ hit X Λ) (hj : j ∈ X.core (X.kap c) c)
    (hj6 : t < X.s → j ∈ X.core (6 * X.ε) c) (hr1 : X.dist j c ≤ r) (hr2 : r ≤ tgt X j c) :
    InvL X (t + 1) (Λ ++ [⟨.inl j, r⟩]) := by
  have hjC : j ∈ X.C c := core_sub_C _ _ hj
  have hcard : (hit X (Λ ++ [⟨.inl j, r⟩])).card = (hit X Λ).card + 1 := by
    rw [hit_append_mk hjC r, card_insert_of_notMem hcn]
  have hgood : ∀ d ∈ Λ ++ [⟨.inl j, r⟩], GoodDum X d := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.good.good d hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact ⟨j, c, rfl, hc, hj, hr1, hr2⟩
  have hE : t + 1 ≤ X.s → ∀ d ∈ Λ ++ [⟨.inl j, r⟩], ∃ c, LedIn X d (X.core (6 * X.ε) c) := by
    intro ht d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.early (by omega) d hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact ⟨c, ledIn_mk.2 (hj6 (by omega))⟩
  refine ⟨⟨hgood, ?_, ?_⟩, hE, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨h.good.pw, List.pairwise_singleton _ _, ?_⟩
    rintro a ha b hb ⟨c', hac, hbc⟩
    rw [List.mem_singleton] at hb
    subst hb
    have e : c' = c := eq_of_mem_C (ledIn_mk.1 hbc) hjC
    subst e
    exact hcn (mem_hit.2 ⟨mem_O_of_mem_C hjC, a, ha, hac⟩)
  · rw [hcard, h.good.card, List.length_append, List.length_singleton]
  · rcases h.c6 with h6 | ⟨ht, hcd⟩
    · exact Or.inl ((sum6_anti H.valid _ _).trans_lt h6)
    · by_cases hts : t + 1 < X.s
      · exact Or.inr ⟨hts, by omega⟩
      · left
        have hs : X.s ≤ (hit X (Λ ++ [⟨.inl j, r⟩])).card := by omega
        rw [sum6_eq_zero ((O1_sub_hit H hgood hs).trans (hit_sub_early (hE (by omega))))]
        exact thr_pos H
  · rcases h.cK with hK | ⟨ht, hcd⟩
    · exact Or.inl ((sumK_anti H.valid _ _).trans_lt hK)
    · by_cases hts : t + 1 < 2 * X.s
      · exact Or.inr ⟨hts, by omega⟩
      · left
        have hs : X.s ≤ (hit X (Λ ++ [⟨.inl j, r⟩])).card := by omega
        rw [sumK_eq_zero (O1_sub_hit H hgood hs)]
        exact thr_pos H

/-! ### The witness -/

theorem witness {Λ : List (Dummy X.I)} (hg : GoodL X Λ) (h6 : sum6 X Λ < X.ε ^ 5 * X.opt)
    (hK : sumK X Λ < X.ε ^ 5 * X.opt) : Nonempty (ClientWitness X Λ) := by
  classical
  let d₀ : Dummy X.I := ⟨.inl ⟨0, H.one_le_n⟩, 0⟩
  let φ : Fin X.I.m → Dummy X.I := fun c ↦
    if h : ∃ d ∈ Λ, LedIn X d (X.C c) then h.choose else d₀
  have hφ : ∀ c ∈ hit X Λ, φ c ∈ Λ ∧ LedIn X (φ c) (X.C c) := by
    intro c hc
    have h : ∃ d ∈ Λ, LedIn X d (X.C c) := (mem_hit.1 hc).2
    have e : φ c = h.choose := dite_eq_left h
    rw [e]
    exact h.choose_spec
  have huniq : ∀ c ∈ hit X Λ, ∀ d ∈ Λ, LedIn X d (X.C c) → d = φ c := fun c hc d hd hl ↦
    eq_of_pairwise_not sameCl_symm hg.pw hd (hφ c hc).1 ⟨c, hl, (hφ c hc).2⟩
  have hdata : ∀ c ∈ hit X Λ, ∃ j, (φ c).leader = .inl j ∧ c ∈ X.O1 ∧
      j ∈ X.core (X.kap c) c ∧ X.dist j c ≤ (φ c).radius ∧ (φ c).radius ≤ tgt X j c :=
    fun c hc ↦ goodDum_of_ledIn (hg.good _ (hφ c hc).1) (hφ c hc).2
  have hearly : ∀ c ∈ hit X Λ, ∀ j, (φ c).leader = .inl j →
      (c ∈ early X Λ ↔ j ∈ X.core (6 * X.ε) c) := by
    intro c hc j hj
    constructor
    · intro he
      obtain ⟨-, d, hd, j', hj', hl⟩ := mem_early.1 he
      have e := huniq c hc d hd ⟨j', core_sub_C _ _ hj', hl⟩
      rw [e, hj] at hl
      have e' : j = j' := Sum.inl_injective hl
      rw [e']
      exact hj'
    · intro hj6
      exact mem_early.2 ⟨(mem_hit.1 hc).1, φ c, (hφ c hc).1, j, hj6, hj⟩
  exact ⟨{
    OL := hit X Λ
    OLe := early X Λ
    φ := φ
    OL_sub := hit_sub_O1 hg.good
    OLe_sub := early_sub_hit Λ
    length_eq := hg.card.symm
    φ_mem := fun c hc ↦ (hφ c hc).1
    φ_inj := fun c hc c' hc' h ↦ by
      have h1 := (hφ c hc).2
      rw [h] at h1
      exact ledIn_unique subset_rfl subset_rfl h1 (hφ c' hc').2
    leader := fun c hc ↦ by
      obtain ⟨j, hl, -, hj, -⟩ := hdata c hc
      exact ⟨j, hj, hl⟩
    leader_early := fun c hc ↦ by
      have hc' := early_sub_hit Λ hc
      obtain ⟨j, hl, -⟩ := hdata c hc'
      exact ⟨j, (hearly c hc' j hl).1 hc, hl⟩
    radius_ge := fun c hc ↦ by
      obtain ⟨j, hl, -, -, h1, -⟩ := hdata c hc
      rw [hl, Instance.dd_comm H.valid]
      exact h1
    radius_le := fun c hc ↦ by
      obtain ⟨j, hl, -, -, -, h2⟩ := hdata c hc
      have he := hearly c hc j hl
      refine h2.trans (le_of_eq ?_)
      unfold tgt
      by_cases hj6 : j ∈ X.core (6 * X.ε) c
      · rw [ite_eq_left hj6, ite_eq_left (he.2 hj6)]
      · rw [ite_eq_right hj6, ite_eq_right (fun h ↦ hj6 (he.1 h))]
    hidden_early := h6
    hidden_hit := hK }⟩

end Hyp

end Analysis

section Radius

/-! ### The radius guess -/

variable {X : Ctx}

/-- Arithmetic for `ε < 1/200`. -/
theorem ar_eps2 {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 200) : (1 + ε) * ε ^ 2 ≤ 1 := by nlinarith

/-- Arithmetic for `ε < 1/200`. -/
theorem ar_eps1 {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 200) : (1 + ε) * ε ≤ 1 / 2 := by nlinarith

/-- Arithmetic for `ε < 1/200`. -/
theorem ar_eps3 {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 200) : (1 + ε) * ε ^ 3 ≤ 2 := by
  have : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le (by linarith) (by norm_num)
  nlinarith [ar_eps2 h0 h1]

/-- The early or late offset `γ ≤ 23/65` leaves room for the factor `1 + ε`. -/
theorem ar_gam {ε γ : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 200) (hγ1 : γ ≤ 23 / 65) :
    (1 + ε) * (1 + γ + 6 * ε) ≤ 1 + γ + 8 * ε := by nlinarith

section Hyp

variable (H : Hyp X)
include H

/-- **A good grid radius exists** for a leader of a punched `core_κ`: Part II's case analysis on
`r₀ ≤ per/ε` and `r₀ > per/ε`. -/
theorem exists_grid_rad {j : Fin X.I.n} {c : Fin X.I.m} (hj : j ∈ pcore X (X.kap c) c)
    {q₀ : ℚ} (hq : (q₀ : ℝ) = X.I.dSet (.inl j) X.S) :
    ∃ x < Par.Gr X.P.N, X.dist j c ≤ (grid X.P.N q₀ x : ℝ) ∧
      (grid X.P.N q₀ x : ℝ) ≤ tgt X j c := by
  have hv := H.valid
  obtain ⟨hjc, hr₀⟩ := mem_pcore.1 hj
  obtain ⟨hjC, hja⟩ := mem_core.1 hjc
  have hN : (201 : ℝ) ≤ X.P.N := X.P.N_ge
  have hN0 : (0 : ℝ) < X.P.N := by linarith
  have hε : X.ε = 1 / (X.P.N : ℝ) := rfl
  have hεN : X.ε * X.P.N = 1 := by rw [hε]; field_simp
  have hε0 : 0 < X.ε := H.eps_pos
  have hε1 : X.ε < 1 / 200 := H.eps_lt
  have hper : 0 ≤ X.per c := per_nonneg hv _ _ _
  have hκ := kappa_mem (X.xr c)
  have hκ' : X.kap c = kappa (X.xr c) := rfl
  have havg : 0 ≤ X.avgS c := div_nonneg (Instance.costOn_nonneg hv _ _) (Nat.cast_nonneg _)
  have ha0 : 0 ≤ X.dist j c := Instance.dd_nonneg hv _ _
  have hr0 : 0 ≤ X.I.dSet (.inl j) X.S := Instance.dSet_nonneg hv _ _
  set γ₀ : ℝ := if j ∈ X.core (6 * X.ε) c then 0 else X.kap c with hγ₀
  have htgt : tgt X j c = (1 + γ₀ + 8 * X.ε) * X.per c + X.ε * X.avgS c := rfl
  have hγ : 0 ≤ γ₀ ∧ γ₀ ≤ 23 / 65 ∧ X.dist j c ≤ (1 + γ₀ + 6 * X.ε) * X.per c := by
    rw [hγ₀]
    split_ifs with h6
    · refine ⟨le_rfl, by norm_num, ?_⟩
      have := (mem_core.1 h6).2
      linarith
    · refine ⟨by rw [hκ']; linarith [hκ.1], by rw [hκ']; exact hκ.2, ?_⟩
      exact hja.trans (mul_le_mul_of_nonneg_right (by linarith) hper)
  obtain ⟨hγ0, hγ1, ha⟩ := hγ
  have htgt0 : (1 + γ₀ + 8 * X.ε) * X.per c ≤ tgt X j c := by
    rw [htgt]
    have := mul_nonneg hε0.le havg
    linarith
  rcases hr0.eq_or_lt with h0 | hpos
  · -- `r₀ = 0`: then `per = 0`, and every grid point is `0`
    have hq0 : q₀ = 0 := by exact_mod_cast hq.trans h0.symm
    have hp0 : X.per c = 0 := by
      have h1 : X.ε ^ 6 * X.per c ≤ 0 := h0 ▸ hr₀
      have h2 := pow_pos hε0 6
      by_contra hne
      have hp : 0 < X.per c := lt_of_le_of_ne hper (Ne.symm hne)
      have := mul_pos h2 hp
      linarith
    have hg0 : (grid X.P.N q₀ 0 : ℝ) = 0 := by simp [grid, hq0]
    refine ⟨0, by unfold Par.Gr; omega, ?_, ?_⟩
    · rw [hg0]
      rw [hp0, mul_zero] at ha
      exact ha
    · rw [hg0]
      rw [hp0, mul_zero] at htgt0
      exact htgt0
  · set r₀ := X.I.dSet (.inl j) X.S with hr₀def
    have hN6 : X.ε ^ 6 * (X.P.N : ℝ) ^ 6 = 1 := by rw [← mul_pow, hεN, one_pow]
    have hperle : X.per c ≤ (X.P.N : ℝ) ^ 6 * r₀ := by
      have h1 := mul_le_mul_of_nonneg_left hr₀ (pow_nonneg hN0.le 6)
      calc X.per c = (X.P.N : ℝ) ^ 6 * (X.ε ^ 6 * X.per c) := by
            rw [← mul_assoc, mul_comm ((X.P.N : ℝ) ^ 6), hN6, one_mul]
        _ ≤ _ := h1
    have ha2 : X.dist j c ≤ 2 * X.per c :=
      ha.trans (mul_le_mul_of_nonneg_right (by linarith) hper)
    have h1N : (1 + 1 / (X.P.N : ℝ)) = 1 + X.ε := by rw [hε]
    have hN3 : r₀ / (X.P.N : ℝ) ^ 3 = X.ε ^ 3 * r₀ := by rw [hε]; field_simp
    have hN7 : (X.P.N : ℝ) ^ 7 = X.P.N * (X.P.N : ℝ) ^ 6 := by ring
    have hN6pos : (0 : ℝ) < (X.P.N : ℝ) ^ 6 := by positivity
    have hd' : (1 + 1 / (X.P.N : ℝ)) * max (X.dist j c) (r₀ / (X.P.N : ℝ) ^ 3) ≤
        (X.P.N : ℝ) ^ 7 * r₀ := by
      rw [h1N, mul_max_of_nonneg _ _ (by linarith)]
      refine max_le ?_ ?_
      · have h2 : (1 + X.ε) * X.dist j c ≤ 2 * X.dist j c :=
          mul_le_mul_of_nonneg_right (by linarith) ha0
        have h6 : 0 ≤ (X.P.N : ℝ) ^ 6 * r₀ := by positivity
        have h3 : 4 * ((X.P.N : ℝ) ^ 6 * r₀) ≤ (X.P.N : ℝ) ^ 7 * r₀ := by
          rw [hN7, mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) h6
        linarith
      · rw [hN3]
        have h4 : (1 + X.ε) * (X.ε ^ 3 * r₀) ≤ 2 * r₀ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (ar_eps3 hε0 hε1) hpos.le
        have h5 : 2 * r₀ ≤ (X.P.N : ℝ) ^ 7 * r₀ := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          have : (X.P.N : ℝ) ≤ (X.P.N : ℝ) ^ 7 := le_self_pow₀ (by linarith) (by norm_num)
          linarith
        linarith
    obtain ⟨x, hx, hx1, hx2⟩ :=
      exists_grid_mem (by have := X.P.hN; omega) hpos (le_max_right _ _) hd' q₀ hq
    refine ⟨x, hx, (le_max_left _ _).trans hx1, hx2.trans ?_⟩
    rw [h1N, mul_max_of_nonneg _ _ (by linarith)]
    refine max_le ?_ ?_
    · refine le_trans ?_ htgt0
      calc (1 + X.ε) * X.dist j c ≤ (1 + X.ε) * ((1 + γ₀ + 6 * X.ε) * X.per c) :=
            mul_le_mul_of_nonneg_left ha (by linarith)
        _ = ((1 + X.ε) * (1 + γ₀ + 6 * X.ε)) * X.per c := by ring
        _ ≤ (1 + γ₀ + 8 * X.ε) * X.per c :=
            mul_le_mul_of_nonneg_right (ar_gam hε0 hε1 hγ1) hper
    · rw [hN3]
      by_cases hcase : r₀ ≤ X.P.N * X.per c
      · -- `r₀ ≤ per/ε`
        refine le_trans ?_ htgt0
        have h2 : X.ε * r₀ ≤ X.per c := by
          have := mul_le_mul_of_nonneg_left hcase hε0.le
          rwa [← mul_assoc, hεN, one_mul] at this
        have h3 : (1 + X.ε) * X.ε ^ 2 ≤ 1 := ar_eps2 hε0 hε1
        calc (1 + X.ε) * (X.ε ^ 3 * r₀) = ((1 + X.ε) * X.ε ^ 2) * (X.ε * r₀) := by ring
          _ ≤ 1 * X.per c := mul_le_mul h3 h2 (by positivity) (by norm_num)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hper
      · -- `r₀ > per/ε`: every point of `core_κ` is at least `r₀/2` from `S`
        push Not at hcase
        have h6p : 6 * X.per c ≤ r₀ := by
          have := mul_le_mul_of_nonneg_right (show (6 : ℝ) ≤ X.P.N by linarith) hper
          linarith
        have hcore : ∀ p ∈ X.core (X.kap c) c, r₀ / 2 ≤ X.I.dSet (.inl p) X.S := by
          intro p hp
          have hp' := (mem_core.1 hp).2
          have htri := Instance.dSet_triangle hv (.inl j) (.inl p) X.S
          have hjp := Instance.dd_triangle hv (.inl j) (.inr c) (.inl p)
          have hcp : X.I.dd (.inr c) (.inl p) = X.dist p c := Instance.dd_comm hv _ _
          have hk : (1 + X.kap c) * X.per c ≤ 3 / 2 * X.per c := by
            refine mul_le_mul_of_nonneg_right ?_ hper
            rw [hκ']
            linarith [hκ.2]
          have hjc' : X.I.dd (.inl j) (.inr c) = X.dist j c := rfl
          rw [hjc', hcp] at hjp
          linarith
        have hcard := card_core_ge hv (by linarith : X.ε ≤ 1)
          (by rw [hκ']; linarith [hκ.1] : 0 ≤ X.kap c) ⟨j, hjC⟩ c
        have hsum : ((X.core (X.kap c) c).card : ℝ) * (r₀ / 2) ≤
            X.costS (X.core (X.kap c) c) := by
          unfold Ctx.costS Instance.costOn
          rw [← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum hcore
        have hCS : X.costS (X.core (X.kap c) c) ≤ X.costS (X.C c) :=
          sum_le_sum_of_subset_of_nonneg (core_sub_C _ _)
            fun _ _ _ ↦ Instance.dSet_nonneg hv _ _
        have hCpos : (0 : ℝ) < (X.C c).card := by exact_mod_cast card_pos.2 ⟨j, hjC⟩
        have havgS : X.ε * r₀ / 2 ≤ X.avgS c := by
          unfold Ctx.avgS
          rw [le_div_iff₀ hCpos]
          calc X.ε * r₀ / 2 * (X.C c).card = (X.ε * (X.C c).card) * (r₀ / 2) := by ring
            _ ≤ (X.core (X.kap c) c).card * (r₀ / 2) :=
                mul_le_mul_of_nonneg_right hcard (by linarith)
            _ ≤ _ := hsum.trans hCS
        have h7 : X.ε * (X.ε * r₀ / 2) ≤ X.ε * X.avgS c := mul_le_mul_of_nonneg_left havgS hε0.le
        have h8 : (1 + X.ε) * (X.ε ^ 3 * r₀) ≤ X.ε * (X.ε * r₀ / 2) := by
          have : (1 + X.ε) * X.ε ≤ 1 / 2 := ar_eps1 hε0 hε1
          have h9 : 0 ≤ X.ε ^ 2 * r₀ := by positivity
          calc (1 + X.ε) * (X.ε ^ 3 * r₀) = ((1 + X.ε) * X.ε) * (X.ε ^ 2 * r₀) := by ring
            _ ≤ 1 / 2 * (X.ε ^ 2 * r₀) := mul_le_mul_of_nonneg_right this h9
            _ = X.ε * (X.ε * r₀ / 2) := by ring
        have h10 : 0 ≤ (1 + γ₀ + 8 * X.ε) * X.per c := by
          have : 0 ≤ 1 + γ₀ + 8 * X.ε := by linarith
          positivity
        rw [htgt]
        linarith

end Hyp

end Radius

section Iteration

/-! ### The exact weights -/

/-- The weights `d(j, LS)` of the client sampling. -/
def csW (x : Raw) (LS : List ℕ) : List ℚ := (List.range x.n).map fun j ↦ x.dSetQ j LS

theorem csStep_eq (N : ℕ) (x : Raw) (LS : List ℕ) (b : ℕ) (Λ : List DumQ) (us uk ur : ℕ) :
    csStep N x LS b Λ us uk ur = if cbit b uk then Λ else
      Λ ++ [(wsample b (csW x LS) us,
        grid N (x.dSetQ (wsample b (csW x LS) us) LS) (cunif (Par.Gr N) ur))] := rfl

theorem toDums_single {I : Instance} {ℓ : ℕ} (h : ℓ < I.n) (r : ℚ) :
    toDums I [(ℓ, r)] = [⟨.inl ⟨ℓ, h⟩, (r : ℝ)⟩] := by
  have h' : ℓ < I.n + I.m := by omega
  simp only [toDums, List.filterMap_cons, List.filterMap_nil, dite_eq_left h']
  rw [show (⟨ℓ, h'⟩ : Fin (I.n + I.m)) = Fin.castAdd I.m ⟨ℓ, h⟩ from rfl,
    finSumFinEquiv_symm_apply_castAdd]

variable {X : Ctx} {LS : List ℕ}

theorem csW_length : (csW (toRaw X.I) LS).length = X.I.n := by simp [csW]

theorem csW_getD (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m) {i : ℕ}
    (hi : i < X.I.n) :
    ((csW (toRaw X.I) LS).getD i 0 : ℝ) = X.I.dSet (.inl ⟨i, hi⟩) X.S := by
  have e : (csW (toRaw X.I) LS).getD i 0 = (toRaw X.I).dSetQ i LS := by
    simp [csW, List.getD_eq_getElem?_getD, hi]
  rw [e, ← hLS]
  exact Raw.dSetQ_toRaw (I := X.I) (.inl ⟨i, hi⟩) hLSm

theorem csW_sum (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m) :
    ((csW (toRaw X.I) LS).sum : ℝ) = X.I.costF X.S := by
  rw [csW, sum_map_range, Rat.cast_sum, Raw.n_toRaw, Finset.sum_range]
  unfold Instance.costF
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← hLS]
  exact Raw.dSetQ_toRaw (I := X.I) (.inl j) hLSm

theorem csW_nonneg (hv : X.I.Valid) (hLSm : ∀ i ∈ LS, i < X.I.m) :
    ∀ q ∈ csW (toRaw X.I) LS, 0 ≤ q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
  have hi' : i < X.I.n := by simpa using hi
  have h := Raw.dSetQ_toRaw (I := X.I) (.inl ⟨i, hi'⟩) hLSm
  have h0 := Instance.dSet_nonneg hv (.inl ⟨i, hi'⟩) (X.I.centers LS)
  rw [← h] at h0
  exact_mod_cast h0

theorem csW_ne_nil (hn : 1 ≤ X.I.n) : csW (toRaw X.I) LS ≠ [] := by
  rw [← List.length_pos_iff, csW_length]
  omega

/-! ### One iteration -/

variable (X LS)

/-- The sampled client. -/
def smp (us : ℕ) : ℕ := wsample X.b (csW (toRaw X.I) LS) us

/-- The guessed radius. -/
def rad (us ur : ℕ) : ℚ :=
  grid X.P.N ((toRaw X.I).dSetQ (smp X LS us) LS) (cunif (Par.Gr X.P.N) ur)

/-- The chunks of one iteration. -/
abbrev Tri (X : Ctx) : Type := Fin (2 ^ X.b) × Fin (2 ^ X.b) × Fin (2 ^ X.b)

/-- One iteration, as a step of `BCFGJPSSV26.Stable.runFin`. -/
def stp (_t : ℕ) (Λ : List DumQ) (u : Tri X) : List DumQ :=
  csStep X.P.N (toRaw X.I) LS X.b Λ u.1 u.2.1 u.2.2

/-- The sampled client is acceptable: a punched-core client of a missed cluster of `O₁`, of
`core_{6ε}` in the first `s` iterations. -/
def AccN (t : ℕ) (Λ : List DumQ) (ℓ : ℕ) : Prop :=
  ∃ h : ℓ < X.I.n, ∃ c ∈ X.O1 \ hit X (toDums X.I Λ),
    (⟨ℓ, h⟩ : Fin X.I.n) ∈ pcore X (X.kap c) c ∧
      (t < X.s → (⟨ℓ, h⟩ : Fin X.I.n) ∈ pcore X (6 * X.ε) c)

/-- The radius is between the distance to the center and the target. -/
def RadOK (ℓ : ℕ) (r : ℚ) : Prop :=
  ∀ h : ℓ < X.I.n, ∀ c, (⟨ℓ, h⟩ : Fin X.I.n) ∈ X.C c →
    X.dist ⟨ℓ, h⟩ c ≤ r ∧ (r : ℝ) ≤ tgt X ⟨ℓ, h⟩ c

/-- The good chunks of an iteration. -/
def GoodCh (t : ℕ) (Λ : List DumQ) (u : Tri X) : Prop :=
  (NeedProg X t (toDums X.I Λ) → AccN X t Λ (smp X LS u.1)) ∧
    (cbit X.b u.2.1 = true ↔ ¬ AccN X t Λ (smp X LS u.1)) ∧
    (AccN X t Λ (smp X LS u.1) → RadOK X (smp X LS u.1) (rad X LS u.1 u.2.2))

/-- The invariant on exact dummies. -/
def Inv (t : ℕ) (Λ : List DumQ) : Prop := InvL X t (toDums X.I Λ)

variable {X LS}

theorem stp_eq (t : ℕ) (Λ : List DumQ) (u : Tri X) :
    stp X LS t Λ u = if cbit X.b u.2.1 then Λ else Λ ++ [(smp X LS u.1, rad X LS u.1 u.2.2)] :=
  rfl

section Hyp

variable (H : Hyp X)
include H

theorem smp_lt (us : ℕ) : smp X LS us < X.I.n := by
  have h := wsample_lt (b := X.b) (csW_ne_nil (LS := LS) H.one_le_n) us
  rwa [csW_length] at h

/-- **The step**: good chunks keep the invariant. -/
theorem inv_step {t : ℕ} {Λ : List DumQ} {u : Tri X} (hI : Inv X t Λ)
    (hG : GoodCh X LS t Λ u) : Inv X (t + 1) (stp X LS t Λ u) := by
  obtain ⟨hnp, hbit, hrad⟩ := hG
  rw [stp_eq]
  by_cases hb : cbit X.b u.2.1 = true
  · rw [ite_eq_left hb]
    exact invL_skip hI fun hn ↦ hbit.1 hb (hnp hn)
  · rw [ite_eq_right hb]
    have hacc : AccN X t Λ (smp X LS u.1) := by
      by_contra hn
      exact hb (hbit.2 hn)
    have hR := hrad hacc
    obtain ⟨h, c, hc, hj, hj6⟩ := hacc
    obtain ⟨hr1, hr2⟩ := hR h c (core_sub_C _ _ (pcore_sub_core _ _ hj))
    unfold Inv
    rw [toDums_append, toDums_single h]
    exact invL_add H hI (mem_sdiff.1 hc).1 (mem_sdiff.1 hc).2 (pcore_sub_core _ _ hj)
      (fun ht ↦ pcore_sub_core _ _ (hj6 ht)) hr1 hr2

end Hyp

end Iteration

section Density

/-! ### The density of good chunks -/

variable {X : Ctx} {LS : List ℕ}

/-- The punched cores still carry `ε⁶ opt`: `ε⁵ opt - ε⁶ Σ |C*| per ≥ ε⁶ opt`. -/
theorem ar_mass {ε P o : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 200) (hP : 0 ≤ P) (ho : 0 ≤ o)
    (h : (1 - ε) * P ≤ o) : ε ^ 6 * o ≤ ε ^ 5 * o - ε ^ 6 * P := by
  have a0 : 0 ≤ ε * P * (1 - 2 * ε) := mul_nonneg (mul_nonneg h0.le hP) (by linarith)
  have a1 : ε * P ≤ 2 * ε * ((1 - ε) * P) := by nlinarith
  have a2 : 2 * ε * ((1 - ε) * P) ≤ 2 * ε * o := mul_le_mul_of_nonneg_left h (by linarith)
  have a3 : 2 * ε * o ≤ (1 - ε) * o := mul_le_mul_of_nonneg_right (by linarith) ho
  have h2 : ε * P ≤ (1 - ε) * o := by linarith
  have h5 : 0 < ε ^ 5 := pow_pos h0 5
  have h3 : ε ^ 6 * P ≤ ε ^ 5 * ((1 - ε) * o) := by
    calc ε ^ 6 * P = ε ^ 5 * (ε * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 h5.le
  have h4 : ε ^ 5 * ((1 - ε) * o) = ε ^ 5 * o - ε ^ 6 * o := by ring
  linarith

/-- `32 N⁶ G_r ≤ 440 N⁸`. -/
theorem ar_q {N : ℝ} (hN : 1 ≤ N) : 32 * N ^ 6 * (10 * N ^ 2 + 1) ≤ 440 * N ^ 8 := by
  have h6 : 0 ≤ N ^ 6 := by positivity
  have h2 : 32 ≤ 120 * N ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h2 h6
  nlinarith

/-- `2^b ≥ 8 n N⁶`: the chunks are long enough. -/
theorem K_ge (X : Ctx) : 8 * X.I.n * X.P.N ^ 6 ≤ 2 ^ X.b := by
  have hN := X.P.hN
  have h1 : X.I.n ≤ 2 ^ (encInstance X.I).length :=
    (Combine.n_le_length X.I).trans Nat.lt_two_pow_self.le
  have h2 : X.P.N ^ 6 ≤ 2 ^ (6 * X.P.N) := by
    rw [show 6 * X.P.N = X.P.N * 6 by ring, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 6
  have h3 : 8 * 2 ^ (6 * X.P.N) ≤ 2 ^ (7 * X.P.N) := by
    rw [show 8 = 2 ^ 3 from rfl, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 8 * X.I.n * X.P.N ^ 6 = X.I.n * (8 * X.P.N ^ 6) := by ring
    _ ≤ 2 ^ (encInstance X.I).length * 2 ^ (7 * X.P.N) :=
        Nat.mul_le_mul h1 ((Nat.mul_le_mul_left 8 h2).trans h3)
    _ = 2 ^ X.b := by rw [← pow_add]; rfl

theorem Gr_le_K (H : Hyp X) : Par.Gr X.P.N ≤ 2 ^ X.b := by
  have hK := K_ge X
  have hn := H.one_le_n
  have hN := X.P.hN
  have hN2 : 1 ≤ X.P.N ^ 2 := Nat.one_le_pow _ _ X.P.N_pos
  have hN4 : 2 ≤ X.P.N ^ 4 := le_trans (by omega) (Nat.le_self_pow (by norm_num) X.P.N)
  unfold Par.Gr
  calc 10 * X.P.N ^ 2 + 1 ≤ 8 * (X.P.N ^ 2 * X.P.N ^ 4) := by nlinarith
    _ = 8 * 1 * X.P.N ^ 6 := by ring
    _ ≤ 8 * X.I.n * X.P.N ^ 6 := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    _ ≤ _ := hK

theorem Gr_pos (N : ℕ) : 0 < Par.Gr N := by unfold Par.Gr; omega

/-- The punching costs at most `ε⁶ |C*| per` per cluster. -/
theorem costS_pcore_ge (hv : X.I.Valid) (γ : ℝ) (c : Fin X.I.m) :
    X.costS (X.core γ c) - X.ε ^ 6 * ((X.C c).card * X.per c) ≤ X.costS (pcore X γ c) := by
  classical
  have hper := per_nonneg hv X.ε (X.C c) c
  have hsplit : X.costS (X.core γ c) = X.costS (pcore X γ c) +
      ∑ j ∈ (X.core γ c).filter (fun j ↦ ¬ (X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S)),
        X.I.dSet (.inl j) X.S := by
    unfold Ctx.costS Instance.costOn pcore
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : ∑ j ∈ (X.core γ c).filter
      (fun j ↦ ¬ (X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S)), X.I.dSet (.inl j) X.S ≤
        X.ε ^ 6 * ((X.C c).card * X.per c) := by
    calc _ ≤ ∑ j ∈ (X.core γ c).filter
          (fun j ↦ ¬ (X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S)), X.ε ^ 6 * X.per c :=
          sum_le_sum fun j hj ↦ (not_le.1 (mem_filter.1 hj).2).le
      _ = ((X.core γ c).filter
          (fun j ↦ ¬ (X.ε ^ 6 * X.per c ≤ X.I.dSet (.inl j) X.S))).card *
            (X.ε ^ 6 * X.per c) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (X.C c).card * (X.ε ^ 6 * X.per c) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_pos X.P.eps_pos 6).le hper)
          exact_mod_cast (card_filter_le _ _).trans (card_le_card (core_sub_C _ _))
      _ = _ := by ring
  linarith

/-- `(1 - ε) Σ |C*| per ≤ opt`. -/
theorem sum_card_per_le (H : Hyp X) {A : Finset (Fin X.I.m)} (hA : A ⊆ X.O) :
    (1 - X.ε) * ∑ c ∈ A, ((X.C c).card * X.per c) ≤ X.opt := by
  have hv := H.valid
  have hcO : ∀ c, 0 ≤ X.costO c := fun c ↦ sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
  rw [mul_sum, H.opt_eq_sum]
  refine (sum_le_sum fun c _ ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg hA fun c _ _ ↦ hcO c)
  rcases (X.C c).eq_empty_or_nonempty with h | h
  · rw [h, card_empty, Nat.cast_zero, zero_mul, mul_zero]
    exact hcO c
  · rw [← mul_assoc]
    exact per_mul_le_costAt hv H.eps_pos (by linarith [H.eps_lt]) h c

/-- The offset of the punched core sampled in iteration `t`. -/
noncomputable def gam (X : Ctx) (t : ℕ) (c : Fin X.I.m) : ℝ :=
  if t < X.s then 6 * X.ε else X.kap c

/-- The acceptable clients of iteration `t`. -/
noncomputable def accSet (X : Ctx) (t : ℕ) (Λ₁ : List (Dummy X.I)) : Finset (Fin X.I.n) :=
  (X.O1 \ hit X Λ₁).biUnion fun c ↦ pcore X (gam X t c) c

open Classical in
/-- **If progress is needed, a client of a missed cluster is sampled** with probability at
least `1/(8 N⁶)`: the acceptable clients carry at least `ε⁶ opt` of the weight `cost(S) ≤ 4 opt`.
-/
theorem card_acc_ge (H : Hyp X) (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {t : ℕ} {Λ : List DumQ} (hI : Inv X t Λ) (hn : NeedProg X t (toDums X.I Λ)) :
    (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) ≤
      (univ.filter fun us : Fin (2 ^ X.b) ↦ AccN X t Λ (smp X LS us)).card := by
  classical
  have hv := H.valid
  set Λ₁ := toDums X.I Λ with hΛ₁
  set Gs : Finset ℕ := (accSet X t Λ₁).image Fin.val with hGs
  -- the cores still to hit are expensive
  have hbig : X.ε ^ 5 * X.opt ≤ ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (X.core (gam X t c) c) := by
    by_cases hts : t < X.s
    · have h6 : X.ε ^ 5 * X.opt ≤ sum6 X Λ₁ := by
        rcases hn with ⟨-, h⟩ | ⟨h', -⟩
        · exact h
        · omega
      have he : early X Λ₁ = hit X Λ₁ :=
        subset_antisymm (early_sub_hit _) (hit_sub_early (hI.early (by omega)))
      unfold sum6 at h6
      rw [he] at h6
      refine h6.trans (le_of_eq (sum_congr rfl fun c _ ↦ ?_))
      rw [gam, ite_eq_left hts]
    · have hK : X.ε ^ 5 * X.opt ≤ sumK X Λ₁ := by
        rcases hn with ⟨h', -⟩ | ⟨-, h⟩
        · exact absurd h' hts
        · exact h
      refine hK.trans (le_of_eq (sum_congr rfl fun c _ ↦ ?_))
      rw [gam, ite_eq_right hts]
  -- the sampled clients of `Gs` are acceptable
  have hsub : (univ.filter fun us : Fin (2 ^ X.b) ↦ wsample X.b (csW (toRaw X.I) LS) us ∈ Gs) ⊆
      (univ.filter fun us : Fin (2 ^ X.b) ↦ AccN X t Λ (smp X LS us)) := by
    intro us hus
    rw [mem_filter] at hus ⊢
    refine ⟨mem_univ _, ?_⟩
    obtain ⟨j, hj, hjl⟩ := mem_image.1 hus.2
    obtain ⟨c, hc, hjc⟩ := mem_biUnion.1 hj
    have e : smp X LS us = j.1 := hjl.symm
    unfold AccN
    rw [e]
    refine ⟨j.2, c, hc, ?_, fun hts ↦ ?_⟩
    · by_cases hts : t < X.s
      · rw [gam, ite_eq_left hts] at hjc
        exact pcore_mono hv (six_eps_le_kappa H.eps_lt _) c hjc
      · rw [gam, ite_eq_right hts] at hjc
        exact hjc
    · rw [gam, ite_eq_left hts] at hjc
      exact hjc
  -- the weight of `Gs`
  have hpd : (↑(X.O1 \ hit X Λ₁) : Set (Fin X.I.m)).PairwiseDisjoint
      fun c ↦ pcore X (gam X t c) c := by
    intro c _ c' _ hne
    exact disjoint_of_subset_left ((pcore_sub_core _ _).trans (core_sub_C _ _))
      (disjoint_of_subset_right ((pcore_sub_core _ _).trans (core_sub_C _ _))
        (Instance.disjoint_cluster X.O hne))
  set M := ∑ i ∈ Gs, ((csW (toRaw X.I) LS).getD i 0 : ℝ) with hMdef
  have hmass : M = ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (pcore X (gam X t c) c) := by
    rw [hMdef, hGs, sum_image Fin.val_injective.injOn, accSet, sum_biUnion hpd]
    refine sum_congr rfl fun c _ ↦ ?_
    unfold Ctx.costS Instance.costOn
    exact sum_congr rfl fun j _ ↦ csW_getD hLS hLSm j.2
  have hpunch : ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (X.core (gam X t c) c) -
      X.ε ^ 6 * ∑ c ∈ X.O1 \ hit X Λ₁, ((X.C c).card * X.per c) ≤
        ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (pcore X (gam X t c) c) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun c _ ↦ costS_pcore_ge hv _ c
  have hP := sum_card_per_le H (A := X.O1 \ hit X Λ₁) (sdiff_subset.trans sdiff_subset)
  have hPnn : 0 ≤ ∑ c ∈ X.O1 \ hit X Λ₁, ((X.C c).card * X.per c) :=
    sum_nonneg fun c _ ↦ mul_nonneg (Nat.cast_nonneg _) (per_nonneg hv _ _ _)
  have hopt : 0 < X.opt := H.opt_pos
  have hM : X.ε ^ 6 * X.opt ≤ M := by
    have := ar_mass H.eps_pos H.eps_lt hPnn hopt.le hP
    rw [hmass]
    linarith
  -- the weighted sample
  have hW := csW_sum hLS hLSm
  have hWle : X.I.costF X.S ≤ 4 * X.opt := costF_le_four_opt hv H.k_le_m X.P.hN H.alo
  have hWpos : 0 < X.I.costF X.S :=
    H.opt_pos.trans_le (Instance.opt_le_costF H.S_nonempty H.alo.1.le)
  have hWposQ : 0 < (csW (toRaw X.I) LS).sum := by
    have h := hW ▸ hWpos
    exact_mod_cast h
  have hGsl : ∀ i ∈ Gs, i < (csW (toRaw X.I) LS).length := by
    intro i hi
    rw [csW_length]
    obtain ⟨j, -, rfl⟩ := mem_image.1 hi
    exact j.2
  have hw := card_wsample (b := X.b) (csW_nonneg hv hLSm) hWposQ Gs hGsl
  rw [hW, ← hMdef] at hw
  have hGc : (Gs.card : ℝ) ≤ X.I.n := by
    have : Gs.card ≤ X.I.n := card_image_le.trans ((card_le_univ _).trans (by simp))
    exact_mod_cast this
  have hKn : (8 * X.I.n * (X.P.N : ℝ) ^ 6) ≤ 2 ^ X.b := by exact_mod_cast K_ge X
  have hN0 : (0 : ℝ) < X.P.N := X.P.N_pos'
  have hε6 : X.ε ^ 6 = 1 / (X.P.N : ℝ) ^ 6 := by
    rw [show X.ε = 1 / (X.P.N : ℝ) from rfl, one_div_pow]
  have hK0 : (0 : ℝ) < 2 ^ X.b := by positivity
  have h1 : (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 ≤ (2 ^ X.b : ℝ) * M / X.I.costF X.S := by
    rw [div_le_div_iff₀ (by norm_num) hWpos]
    have hε0 : 0 < X.ε ^ 6 := pow_pos H.eps_pos 6
    have a1 := mul_le_mul_of_nonneg_left hWle (mul_pos hK0 hε0).le
    have a2 := mul_le_mul_of_nonneg_left hM hK0.le
    nlinarith
  have hnle : (X.I.n : ℝ) ≤ (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) =
        (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 - (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) := by
          rw [hε6]
          field_simp
          ring
    _ ≤ (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 - X.I.n := by linarith
    _ ≤ (2 ^ X.b : ℝ) * M / X.I.costF X.S - Gs.card := by linarith
    _ ≤ _ := hw
    _ ≤ _ := by exact_mod_cast card_le_card hsub

/-- A grid index good for every radius chunk mapping to it. -/
theorem rad_choice (H : Hyp X) (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {t : ℕ} {Λ : List DumQ} {us : ℕ} (hacc : AccN X t Λ (smp X LS us)) :
    ∃ x₀ < Par.Gr X.P.N, ∀ ur : ℕ, cunif (Par.Gr X.P.N) ur = x₀ →
      RadOK X (smp X LS us) (rad X LS us ur) := by
  obtain ⟨h, c, -, hj, -⟩ := hacc
  have hq : (((toRaw X.I).dSetQ (smp X LS us) LS : ℚ) : ℝ) =
      X.I.dSet (.inl ⟨smp X LS us, h⟩) X.S := by
    rw [← hLS]
    exact Raw.dSetQ_toRaw (I := X.I) (.inl ⟨_, h⟩) hLSm
  obtain ⟨x₀, hx₀, h1, h2⟩ := exists_grid_rad H hj hq
  refine ⟨x₀, hx₀, fun ur hur h' c' hc' ↦ ?_⟩
  have e : c = c' := eq_of_mem_C (core_sub_C _ _ (pcore_sub_core _ _ hj)) hc'
  subst e
  unfold rad
  rw [hur]
  exact ⟨h1, h2⟩

open Classical in
/-- **The density** of the good chunks is at least `q₁ = 1/(440 N⁸)`. -/
theorem density (H : Hyp X) (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {t : ℕ} {Λ : List DumQ} (hI : Inv X t Λ) :
    X.P.q₁ * (Fintype.card (Tri X) : ℝ) ≤ (univ.filter fun u ↦ GoodCh X LS t Λ u).card := by
  have hb1 : 1 ≤ X.b := by
    have := X.P.hN
    unfold Ctx.b Par.bits
    omega
  have hN : (201 : ℝ) ≤ X.P.N := X.P.N_ge
  have hGr : (Par.Gr X.P.N : ℝ) = 10 * (X.P.N : ℝ) ^ 2 + 1 := by
    unfold Par.Gr
    push_cast
    ring
  have hGr1 : (1 : ℝ) ≤ Par.Gr X.P.N := by exact_mod_cast Gr_pos X.P.N
  have hK0 : (0 : ℝ) < 2 ^ X.b := by positivity
  set A : Finset (Fin (2 ^ X.b)) := if NeedProg X t (toDums X.I Λ) then
    univ.filter (fun us ↦ AccN X t Λ (smp X LS us)) else univ with hAdef
  have hAmem : ∀ us ∈ A, NeedProg X t (toDums X.I Λ) → AccN X t Λ (smp X LS us) := by
    intro us hus hn
    rw [hAdef, ite_eq_left hn] at hus
    exact (mem_filter.1 hus).2
  have hA : (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) ≤ A.card := by
    by_cases hn : NeedProg X t (toDums X.I Λ)
    · rw [hAdef, ite_eq_left hn]
      exact card_acc_ge H hLS hLSm hI hn
    · rw [hAdef, ite_eq_right hn, card_univ, Fintype.card_fin]
      push_cast
      refine div_le_self hK0.le ?_
      have : (1 : ℝ) ≤ (X.P.N : ℝ) ^ 6 := one_le_pow₀ (by linarith)
      linarith
  have hfib : ∀ us ∈ A, (2 : ℝ) ^ (X.b - 1) * ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) ≤
      (univ.filter fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p)).card := by
    intro us hus
    by_cases hacc : AccN X t Λ (smp X LS us)
    · obtain ⟨x₀, hx₀, hrad⟩ := rad_choice H hLS hLSm hacc
      have h1 := card_prod_ge (fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p))
        (univ.filter fun uk : Fin (2 ^ X.b) ↦ cbit X.b uk = false)
        ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) (fun uk huk ↦ ?_)
      · rw [card_cbit hb1] at h1
        push_cast at h1
        exact h1
      · refine (card_cunif (Gr_pos X.P.N) (Gr_le_K H) hx₀).trans ?_
        have hsub : (univ.filter fun ur : Fin (2 ^ X.b) ↦ cunif (Par.Gr X.P.N) ur = x₀) ⊆
            (univ.filter fun ur : Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, (uk, ur))) := by
          intro ur hur
          refine mem_filter.2 ⟨mem_univ _, fun _ ↦ hacc, ⟨fun hcb ↦ ?_, fun hn ↦ absurd hacc hn⟩,
            fun _ ↦ hrad ur (mem_filter.1 hur).2⟩
          have hf := (mem_filter.1 huk).2
          rw [hf] at hcb
          exact absurd hcb Bool.false_ne_true
        exact_mod_cast card_le_card hsub
    · have h1 := card_prod_ge (fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p))
        (univ.filter fun uk : Fin (2 ^ X.b) ↦ cbit X.b uk = true)
        ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) (fun uk huk ↦ ?_)
      · rw [card_cbit hb1] at h1
        push_cast at h1
        exact h1
      · have hall : (univ.filter fun ur : Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, (uk, ur))) =
            univ := by
          refine eq_univ_of_forall fun ur ↦ mem_filter.2 ⟨mem_univ _,
            fun hn ↦ absurd (hAmem us hus hn) hacc, ⟨fun _ ↦ hacc, fun _ ↦ (mem_filter.1 huk).2⟩,
            fun h ↦ absurd h hacc⟩
        rw [hall, card_univ, Fintype.card_fin]
        push_cast
        refine div_le_self hK0.le ?_
        linarith
  have h := card_prod_ge (fun u : Tri X ↦ GoodCh X LS t Λ u) A _ hfib
  refine le_trans ?_ h
  have hcardT : (Fintype.card (Tri X) : ℝ) = (2 ^ X.b : ℝ) ^ 3 := by
    simp only [Tri, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have h2b : (2 : ℝ) ^ (X.b - 1) = (2 ^ X.b : ℝ) / 2 := by
    rw [eq_div_iff two_ne_zero, ← pow_succ, Nat.sub_add_cancel hb1]
  rw [hcardT, h2b]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hA (by positivity))
  have hN1 : (1 : ℝ) ≤ X.P.N := by linarith
  have hN0 : (0 : ℝ) < X.P.N := by linarith
  have e : (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) *
      ((2 ^ X.b : ℝ) / 2 * ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N))) =
        (2 ^ X.b : ℝ) ^ 3 / (32 * X.P.N ^ 6 * (10 * X.P.N ^ 2 + 1)) := by
    rw [hGr]
    field_simp
    ring
  rw [e, Prm.q₁, div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (ar_q hN1)

end Density

section Triples

/-! ### Chunk triples -/

/-- The `r`-th chunk of a triple. -/
def sel {K : ℕ} (t : Fin K × Fin K × Fin K) (r : ℕ) : Fin K :=
  if r = 0 then t.1 else if r = 1 then t.2.1 else t.2.2

/-- A vector of `2 s` triples as a vector of `6 s` chunks. -/
def spread {s K : ℕ} (v : Fin (2 * s) → Fin K × Fin K × Fin K) (i : Fin (6 * s)) : Fin K :=
  sel (v ⟨i.1 / 3, by have := i.2; omega⟩) (i.1 % 3)

theorem toCh_spread_apply {s K : ℕ} (v : Fin (2 * s) → Fin K × Fin K × Fin K) {i : ℕ}
    (hi : i < 2 * s) {r : ℕ} (hr : r < 3) :
    toCh (spread v) (3 * i + r) = sel (v ⟨i, hi⟩) r := by
  have h : 3 * i + r < 6 * s := by omega
  unfold toCh
  rw [dite_eq_left h]
  unfold spread
  have e1 : (⟨(3 * i + r) / 3, by omega⟩ : Fin (2 * s)) = ⟨i, hi⟩ := Fin.ext (by simp; omega)
  have e2 : (3 * i + r) % 3 = r := by omega
  rw [e1, e2]

theorem toCh_spread {s K : ℕ} (v : Fin (2 * s) → Fin K × Fin K × Fin K) (i : ℕ)
    (hi : i < 2 * s) :
    toCh (spread v) (3 * i) = (v ⟨i, hi⟩).1 ∧ toCh (spread v) (3 * i + 1) = (v ⟨i, hi⟩).2.1 ∧
      toCh (spread v) (3 * i + 2) = (v ⟨i, hi⟩).2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := toCh_spread_apply v hi (r := 0) (by norm_num)
    rw [add_zero] at h
    rw [h]
    rfl
  · rw [toCh_spread_apply v hi (by norm_num)]
    rfl
  · rw [toCh_spread_apply v hi (by norm_num)]
    rfl

theorem spread_injective {s K : ℕ} :
    Function.Injective (spread : (Fin (2 * s) → Fin K × Fin K × Fin K) → _) := by
  intro v v' h
  funext i
  have key : ∀ r < 3, sel (v i) r = sel (v' i) r := fun r hr ↦ by
    have h1 := toCh_spread_apply v i.2 hr
    rw [h, toCh_spread_apply v' i.2 hr] at h1
    exact Fin.ext h1.symm
  exact Prod.ext (key 0 (by norm_num)) (Prod.ext (key 1 (by norm_num)) (key 2 (by norm_num)))

theorem foldl_eq_runFin (X : Ctx) (LS : List ℕ) (M : ℕ) (v : Fin M → Tri X) (ch : ℕ → ℕ)
    (hch : ∀ i (hi : i < M), ch (3 * i) = (v ⟨i, hi⟩).1 ∧ ch (3 * i + 1) = (v ⟨i, hi⟩).2.1 ∧
      ch (3 * i + 2) = (v ⟨i, hi⟩).2.2) :
    (List.range M).foldl (fun Λ i ↦ csStep X.P.N (toRaw X.I) LS X.b Λ (ch (3 * i))
      (ch (3 * i + 1)) (ch (3 * i + 2))) [] = runFin (stp X LS) [] M v := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.range_succ, List.foldl_append,
      ih (fun i ↦ v i.castSucc) (fun i hi ↦ hch i (by omega))]
    obtain ⟨h1, h2, h3⟩ := hch M (by omega)
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h1, h2, h3]
    rfl

end Triples

end ClientSampling

open ClientSampling in
open Classical in
/-- **The process lemma of the client sampling.** -/
theorem Hyp.card_clientWitness {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m) :
    X.P.q₁ ^ (2 * X.s) * ((2 : ℝ) ^ X.b) ^ (6 * X.s) ≤
      (univ.filter fun u : Fin (6 * X.s) → Fin (2 ^ X.b) ↦
        Nonempty (ClientWitness X
          (toDums X.I (csRun X.P.N (toRaw X.I) LS X.s X.b (toCh u))))).card := by
  have _ := hLSnd
  have hq : 0 ≤ X.P.q₁ := by
    unfold Prm.q₁
    positivity
  have hg := guided_count (stp X LS) ([] : List DumQ) (Inv X) (GoodCh X LS) hq (2 * X.s)
    (invL_zero H) (fun t _ Λ u hI hG ↦ inv_step H hI hG) (fun t _ Λ hI ↦ density H hLS hLSm hI)
  have hcard : (Fintype.card (Tri X) : ℝ) ^ (2 * X.s) = ((2 : ℝ) ^ X.b) ^ (6 * X.s) := by
    simp only [Tri, Fintype.card_prod, Fintype.card_fin]
    push_cast
    rw [show 6 * X.s = 3 * (2 * X.s) by ring, pow_mul]
    ring
  rw [hcard] at hg
  refine hg.trans ?_
  have hmaps : ∀ v ∈ (univ.filter fun v : Fin (2 * X.s) → Tri X ↦
      Inv X (2 * X.s) (runFin (stp X LS) [] (2 * X.s) v)),
      spread v ∈ (univ.filter fun u : Fin (6 * X.s) → Fin (2 ^ X.b) ↦
        Nonempty (ClientWitness X
          (toDums X.I (csRun X.P.N (toRaw X.I) LS X.s X.b (toCh u))))) := by
    intro v hv
    rw [mem_filter] at hv ⊢
    refine ⟨mem_univ _, ?_⟩
    have e : csRun X.P.N (toRaw X.I) LS X.s X.b (toCh (spread v)) =
        runFin (stp X LS) [] (2 * X.s) v :=
      foldl_eq_runFin X LS _ v _ fun i hi ↦ toCh_spread v i hi
    rw [e]
    have hI := hv.2
    exact witness H hI.good (hI.c6.resolve_right (by omega)) (hI.cK.resolve_right (by omega))
  exact_mod_cast card_le_card_of_injOn spread (fun v hv ↦ hmaps v hv)
    (fun v _ v' _ h ↦ spread_injective h)

end BCFGJPSSV26.Stable
