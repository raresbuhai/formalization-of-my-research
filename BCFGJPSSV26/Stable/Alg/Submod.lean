module

public import BCFGJPSSV26.Stable.Alg.Mixed
public import BCFGJPSSV26.Stable.Alg.Coloring
public import BCFGJPSSV26.Stable.Submod.Candidate
public import Background.Tuples

/-!
# The submodular step, exactly

The algorithm of [BCFGJPSSV26b, Section 5] for one guess `p'`, over the exact
table (`BCFGJPSSV26.Stable.candidate`):

1. `ρ = |Λ| + p'`, `z = |LS'| + ρ - k`; skip the guess if `ρ > s`, `z > |red|` or a ball is
   empty.
2. `g = g₁ + g₂` exactly (`BCFGJPSSV26.Raw.gQ`, the sum of the `z` smallest values by sorting).
3. The parts: the balls of the dummies and `p'` copies of all facilities.
4. The sequential greedy with `N` rounds (`BCFGJPSSV26.Stable.seqGreedyQ`, the rule of
   `BCFGJPSSV26.Stable.IsSeqGreedy`), all sums over `[N]^ρ` by the tuples of
   `Tuples.tuples` cut at the budget `B` (complete when `N^ρ ≤ B`); `Ŷ` is the choice of one
   element per list minimizing `g`.
5. `Ẑ`: the `z` red centers of least `h_c(Ŷ)`; the candidate is `(LS' \ Ẑ) ∪ Ŷ`.

**Specification** (`BCFGJPSSV26.Stable.candidate_spec`): a computed candidate is a list of at
most `k` distinct facilities of the form `(LS' \ Ẑ) ∪ Ŷ` with `Ŷ` meeting every ball, `Ẑ`
attaining `g₂(Ŷ)`, and the greedy guarantee `BCFGJPSSV26.Stable.GreedyGuarantee` (from
`BCFGJPSSV26.Stable.seqGreedy_bound`, `BCFGJPSSV26.Stable.gfun_isMonoF`,
`BCFGJPSSV26.Stable.gfun_isSubmod`, and the exact values of `g`). The guess is not skipped when
its conditions hold (`BCFGJPSSV26.Stable.candidate_isSome`).
-/

@[expose] public section

namespace BCFGJPSSV26

namespace Raw

open Stable

/-- `g₁` exactly. -/
def g₁Q (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (Y : List ℕ) : ℚ :=
  ((List.range x.n).map fun j ↦ min (x.dMixQ j LS' Λ) (x.dSetQ j Y)).sum

/-- `h_c` exactly. -/
def hclQ (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (blue : List ℕ) (c : ℕ) (Y : List ℕ) : ℚ :=
  x.costMixOnQ LS' Λ (x.clusterMixQ LS' Λ c) +
    (x.clusterMixQ LS' Λ c).length * x.dMixQ (x.n + c) (blue ++ Y) Λ

/-- The sum of the `z` smallest entries of a list. -/
def sumSmallestQ (z : ℕ) (l : List ℚ) : ℚ := ((l.mergeSort fun a a' ↦ decide (a ≤ a')).take z).sum

/-- `g₂` exactly. -/
def g₂Q (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (red blue : List ℕ) (z : ℕ) (Y : List ℕ) : ℚ :=
  sumSmallestQ z (red.map fun c ↦ x.hclQ LS' Λ blue c Y)

/-- `g = g₁ + g₂` exactly. -/
def gQ (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (red blue : List ℕ) (z : ℕ) (Y : List ℕ) : ℚ :=
  x.g₁Q LS' Λ Y + x.g₂Q LS' Λ red blue z Y

end Raw

namespace Stable

/-- The first maximizer of `f` in `l`, `d` if `l` is empty. -/
def argmaxBy {α : Type} (f : α → ℚ) (l : List α) (d : α) : α :=
  (l.find? fun a ↦ l.all fun a' ↦ decide (f a' ≤ f a)).getD d

/-- The first minimizer of `f` in `l`, `d` if `l` is empty. -/
def argminBy {α : Type} (f : α → ℚ) (l : List α) (d : α) : α :=
  (l.find? fun a ↦ l.all fun a' ↦ decide (f a ≤ f a')).getD d

/-- `Q⁻ʲ_t(V)` for the lists `Lst` of the greedy. -/
def greedyQL (Lst : List (List ℕ)) (j t : ℕ) (V : List ℕ) : List ℕ :=
  (List.range Lst.length).filterMap fun j' ↦
    if (j' < j ∧ V.getD j' 0 ≤ t) ∨ (j < j' ∧ V.getD j' 0 < t) then
      some ((Lst.getD j' []).getD (V.getD j' 0) 0)
    else none

/-- The total gain of `f = g(∅) - g` from adding `e` to `Q⁻ʲ_t(V)`, over the tuples `Vs`. -/
def gainQ (g : List ℕ → ℚ) (Lst : List (List ℕ)) (j t : ℕ) (Vs : List (List ℕ)) (e : ℕ) : ℚ :=
  (Vs.map fun V ↦ g (greedyQL Lst j t V) - g (e :: greedyQL Lst j t V)).sum

/-- Round `t` of the greedy: each part in turn appends its best element. -/
def greedyRound (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) : List (List ℕ) :=
  (List.range parts.length).foldl (fun Lst j ↦
    Lst.set j (Lst.getD j [] ++ [argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0])) Lst

/-- The choice `{L_j[V_j]}` of one element per list. -/
def pickQ (Lst : List (List ℕ)) (V : List ℕ) : List ℕ :=
  (List.range Lst.length).map fun j ↦ (Lst.getD j []).getD (V.getD j 0) 0

/-- **The sequential greedy** with `T` rounds, tuples cut at `B`. -/
def seqGreedyQ (g : List ℕ → ℚ) (parts : List (List ℕ)) (T B : ℕ) : List ℕ :=
  let Vs := Tuples.tuples B T parts.length
  let Lst := (List.range T).foldl (fun Lst t ↦ greedyRound g parts Vs t Lst)
    (List.replicate parts.length [])
  pickQ Lst (argminBy (fun V ↦ g (pickQ Lst V)) Vs [])

/-- **The candidate of the guess `p'`**, or `none` if the guess is skipped. -/
def candidate (N : ℕ) (x : Raw) (s B : ℕ) (LS' : List ℕ) (Λ : List DumQ) (col : List Bool)
    (p' : ℕ) : Option (List ℕ) :=
  let ρ := Λ.length + p'
  let red := redOf LS' col
  let blue := blueOf LS' col
  let z := (LS'.length + ρ) - x.k
  if s < ρ ∨ red.length < z ∨ Λ.any (fun l ↦ (x.ballQ l).isEmpty) then none
  else
    let g := x.gQ LS' Λ red blue z
    let Y := seqGreedyQ g (Λ.map x.ballQ ++ List.replicate p' (List.range x.m)) N B
    let Zh := (red.mergeSort fun c c' ↦
      decide (x.hclQ LS' Λ blue c Y ≤ x.hclQ LS' Λ blue c' Y)).take z
    some ((LS'.filter fun c ↦ decide (c ∉ Zh)) ++ Y).dedup

section Helpers

open Finset

/-! ### First maximizers and minimizers -/

private theorem argmaxBy_spec {α : Type} (f : α → ℚ) {l : List α} (hl : l ≠ []) (d : α) :
    argmaxBy f l d ∈ l ∧ ∀ a ∈ l, f a ≤ f (argmaxBy f l d) := by
  classical
  obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_max_image l.toFinset f
    ((List.toFinset_nonempty_iff l).2 hl)
  have hsome : (l.find? fun a ↦ l.all fun a' ↦ decide (f a' ≤ f a)).isSome := by
    rw [List.find?_isSome]
    refine ⟨a₀, List.mem_toFinset.1 ha₀, ?_⟩
    rw [List.all_eq_true]
    exact fun b hb ↦ decide_eq_true (hmax b (List.mem_toFinset.2 hb))
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some ha
  rw [List.all_eq_true] at hp
  unfold argmaxBy
  rw [ha, Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some ha, fun b hb ↦ of_decide_eq_true (hp b hb)⟩

private theorem argminBy_spec {α : Type} (f : α → ℚ) {l : List α} (hl : l ≠ []) (d : α) :
    argminBy f l d ∈ l ∧ ∀ a ∈ l, f (argminBy f l d) ≤ f a := by
  obtain ⟨a, ha, hmem, hmin⟩ := Combine.find?_min f hl
  unfold argminBy
  rw [ha, Option.getD_some]
  exact ⟨hmem, hmin⟩

/-! ### Lists -/

private theorem getD_set_self' {α : Type*} {L : List α} {j : ℕ} (hj : j < L.length) (v d : α) :
    (L.set j v).getD j d = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj, Option.getD_some]

private theorem getD_set_ne' {α : Type*} (L : List α) {j j' : ℕ} (h : j ≠ j') (v d : α) :
    (L.set j v).getD j' d = L.getD j' d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, ← List.getD_eq_getElem?_getD]

private theorem getD_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) (d : α) : l₂.getD i d = l₁.getD i d := by
  obtain ⟨u, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

private theorem getD_lt_of {l : List ℕ} {m : ℕ} (hl : ∀ a ∈ l, a < m) (hm : 0 < m) (i : ℕ) :
    l.getD i 0 < m := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hm

private theorem getD_ofFn_val {ρ T : ℕ} (v : Fin ρ → Fin T) {a : ℕ} (ha : a < ρ) :
    (List.ofFn fun j ↦ (v j : ℕ)).getD a 0 = v ⟨a, ha⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_ofFn]

/-! ### The greedy lists -/

section Greedy

variable (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ))

/-- One step of a round of the greedy: part `j` appends its best element. -/
private def greedyStep (t : ℕ) (Lst : List (List ℕ)) (j : ℕ) : List (List ℕ) :=
  Lst.set j (Lst.getD j [] ++ [argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0])

/-- The lists before round `t`. -/
private def greedyR (t : ℕ) : List (List ℕ) :=
  (List.range t).foldl (fun Lst t ↦ greedyRound g parts Vs t Lst)
    (List.replicate parts.length [])

/-- The lists in round `t`, before part `j`. -/
private def greedyS (t j : ℕ) : List (List ℕ) :=
  (List.range j).foldl (greedyStep g parts Vs t) (greedyR g parts Vs t)

private theorem greedyS_zero (t : ℕ) : greedyS g parts Vs t 0 = greedyR g parts Vs t := rfl

private theorem greedyS_succ (t j : ℕ) :
    greedyS g parts Vs t (j + 1) = greedyStep g parts Vs t (greedyS g parts Vs t j) j := by
  rw [greedyS, List.range_succ, List.foldl_append]
  rfl

private theorem greedyR_succ (t : ℕ) :
    greedyR g parts Vs (t + 1) = greedyS g parts Vs t parts.length := by
  rw [greedyR, List.range_succ, List.foldl_append]
  rfl

private theorem length_greedyS_of (t : ℕ) (h : (greedyR g parts Vs t).length = parts.length)
    (j : ℕ) :
    (greedyS g parts Vs t j).length = parts.length := by
  induction j with
  | zero => exact h
  | succ j ih => rw [greedyS_succ, greedyStep, List.length_set, ih]

private theorem length_greedyR (t : ℕ) : (greedyR g parts Vs t).length = parts.length := by
  induction t with
  | zero => simp [greedyR]
  | succ t ih => rw [greedyR_succ]; exact length_greedyS_of g parts Vs t ih _

private theorem length_greedyS (t j : ℕ) : (greedyS g parts Vs t j).length = parts.length :=
  length_greedyS_of g parts Vs t (length_greedyR g parts Vs t) j

private theorem length_getD_greedyS (t : ℕ)
    (hR : ∀ j' < parts.length, ((greedyR g parts Vs t).getD j' []).length = t) :
    ∀ j ≤ parts.length, ∀ j' < parts.length,
      ((greedyS g parts Vs t j).getD j' []).length = if j' < j then t + 1 else t := by
  intro j
  induction j with
  | zero =>
    intro _ j' hj'
    rw [greedyS_zero, hR j' hj', ite_eq_right (by omega)]
  | succ j ih =>
    intro hj j' hj'
    rw [greedyS_succ, greedyStep]
    by_cases hjj : j = j'
    · subst hjj
      rw [getD_set_self' (by rw [length_greedyS]; omega), List.length_append,
        ih (by omega) j hj', ite_eq_right (lt_irrefl j), ite_eq_left (by omega)]
      rfl
    · rw [getD_set_ne' _ hjj, ih (by omega) j' hj']
      by_cases h1 : j' < j
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

private theorem length_getD_greedyR (t : ℕ) :
    ∀ j' < parts.length, ((greedyR g parts Vs t).getD j' []).length = t := by
  induction t with
  | zero =>
    intro j' hj'
    simp [greedyR, List.getD_eq_getElem?_getD]
  | succ t ih =>
    intro j' hj'
    rw [greedyR_succ, length_getD_greedyS g parts Vs t ih _ le_rfl j' hj', ite_eq_left hj']

/-- `A` extends to `B`, list by list. -/
private def ListsPrefix (A B : List (List ℕ)) : Prop := ∀ j, A.getD j [] <+: B.getD j []

private theorem prefix_greedyStep (t : ℕ) (Lst : List (List ℕ)) (j : ℕ) :
    ListsPrefix Lst (greedyStep g parts Vs t Lst j) := by
  intro j'
  unfold greedyStep
  by_cases hjj : j = j'
  · subst hjj
    by_cases hj : j < Lst.length
    · rw [getD_set_self' hj]
      exact List.prefix_append _ _
    · rw [List.set_eq_of_length_le (by omega)]
  · rw [getD_set_ne' _ hjj]

private theorem greedyS_mono (t : ℕ) {j j' : ℕ} (h : j ≤ j') :
    ListsPrefix (greedyS g parts Vs t j) (greedyS g parts Vs t j') := by
  induction j', h using Nat.le_induction with
  | base => exact fun _ ↦ List.prefix_refl _
  | succ j' _ ih =>
    rw [greedyS_succ]
    exact fun i ↦ (ih i).trans (prefix_greedyStep g parts Vs t _ j' i)

private theorem greedyR_mono {t t' : ℕ} (h : t ≤ t') :
    ListsPrefix (greedyR g parts Vs t) (greedyR g parts Vs t') := by
  induction t', h using Nat.le_induction with
  | base => exact fun _ ↦ List.prefix_refl _
  | succ t' _ ih =>
    rw [greedyR_succ, ← greedyS_zero]
    exact fun i ↦ (ih i).trans (greedyS_mono g parts Vs t' (Nat.zero_le _) i)

private theorem greedyS_prefix_R {T t j : ℕ} (ht : t < T) (hj : j ≤ parts.length) :
    ListsPrefix (greedyS g parts Vs t j) (greedyR g parts Vs T) := by
  intro i
  refine (greedyS_mono g parts Vs t hj i).trans ?_
  rw [← greedyR_succ]
  exact greedyR_mono g parts Vs ht i

private theorem greedyR_entry {T t j : ℕ} (ht : t < T) (hj : j < parts.length) :
    ((greedyR g parts Vs T).getD j []).getD t 0 =
      argmaxBy (gainQ g (greedyS g parts Vs t j) j t Vs) (parts.getD j []) 0 := by
  have hlen := length_getD_greedyS g parts Vs t (length_getD_greedyR g parts Vs t) j hj.le j hj
  rw [ite_eq_right (lt_irrefl j)] at hlen
  have hpre := greedyS_prefix_R g parts Vs ht (Nat.succ_le_of_lt hj) j
  rw [greedyS_succ, greedyStep, getD_set_self' (by rw [length_greedyS]; exact hj)] at hpre
  rw [getD_of_prefix hpre (by rw [List.length_append, hlen]; simp) 0,
    List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
  rfl

private theorem greedyQL_greedyS {T t j : ℕ} (ht : t < T) (hj : j < parts.length) (V : List ℕ) :
    greedyQL (greedyS g parts Vs t j) j t V = greedyQL (greedyR g parts Vs T) j t V := by
  unfold greedyQL
  rw [length_greedyS, length_greedyR]
  refine List.filterMap_congr fun j' hj' ↦ ?_
  have hj'ρ := List.mem_range.1 hj'
  have hpre := greedyS_prefix_R g parts Vs ht hj.le j'
  have hlen := length_getD_greedyS g parts Vs t (length_getD_greedyR g parts Vs t) j hj.le j'
    hj'ρ
  by_cases hc : (j' < j ∧ V.getD j' 0 ≤ t) ∨ (j < j' ∧ V.getD j' 0 < t)
  · rw [ite_eq_left hc, ite_eq_left hc]
    congr 1
    refine (getD_of_prefix hpre ?_ 0).symm
    rw [hlen]
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1]
      omega
    · rw [ite_eq_right (by omega)]
      omega
  · rw [ite_eq_right hc, ite_eq_right hc]

private theorem gainQ_greedyS {T t j : ℕ} (ht : t < T) (hj : j < parts.length) :
    gainQ g (greedyS g parts Vs t j) j t Vs = gainQ g (greedyR g parts Vs T) j t Vs := by
  funext e
  unfold gainQ
  simp only [greedyQL_greedyS g parts Vs ht hj]

/-- **The greedy lists**: `N` entries per part, each a first maximizer of the total gain over the
part, on the final lists. -/
private theorem greedyR_spec (hp : ∀ j < parts.length, parts.getD j [] ≠ []) (T : ℕ) :
    (greedyR g parts Vs T).length = parts.length ∧
    (∀ j < parts.length, ((greedyR g parts Vs T).getD j []).length = T) ∧
    ∀ j < parts.length, ∀ t < T,
      ((greedyR g parts Vs T).getD j []).getD t 0 ∈ parts.getD j [] ∧
      ∀ e ∈ parts.getD j [], gainQ g (greedyR g parts Vs T) j t Vs e ≤
        gainQ g (greedyR g parts Vs T) j t Vs (((greedyR g parts Vs T).getD j []).getD t 0) := by
  refine ⟨length_greedyR g parts Vs T, length_getD_greedyR g parts Vs T, fun j hj t ht ↦ ?_⟩
  rw [greedyR_entry g parts Vs ht hj, gainQ_greedyS g parts Vs ht hj]
  exact argmaxBy_spec _ (hp j hj) 0

end Greedy

/-! ### Tuples -/

private theorem nodup_iterate_tupleStepFull (n : ℕ) : ∀ i, ((Tuples.tupleStepFull n)^[i] [[]]).Nodup
  | 0 => List.nodup_singleton _
  | i + 1 => by
    rw [Function.iterate_succ_apply', Tuples.tupleStepFull, List.nodup_flatMap]
    refine ⟨fun q _ ↦ List.Nodup.map (fun a b h ↦ (List.cons.inj h).1) List.nodup_range, ?_⟩
    refine (nodup_iterate_tupleStepFull n i).imp fun {q q'} hne ↦ ?_
    intro r hr hr'
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hr'
    exact hne (List.cons.inj hb).2.symm

/-- **Sums over all the tuples** are sums over the functions `Fin ρ → Fin T`. -/
private theorem sum_tuples {M : Type*} [AddCommMonoid M] {B T ρ : ℕ} (h : T ^ ρ ≤ B)
    (F : List ℕ → M) :
    ((Tuples.tuples B T ρ).map F).sum = ∑ v : Fin ρ → Fin T, F (List.ofFn fun j ↦ (v j : ℕ)) := by
  classical
  have hnd : (Tuples.tuples B T ρ).Nodup := by
    rw [Tuples.tuples_eq h]
    exact nodup_iterate_tupleStepFull T ρ
  rw [← List.sum_toFinset F hnd]
  have hinj : Function.Injective fun v : Fin ρ → Fin T ↦ List.ofFn fun j ↦ (v j : ℕ) := by
    intro v w hvw
    have := List.ofFn_inj.1 hvw
    funext j
    exact Fin.ext (congrFun this j)
  have himg : (Tuples.tuples B T ρ).toFinset =
      univ.image fun v : Fin ρ → Fin T ↦ List.ofFn fun j ↦ (v j : ℕ) := by
    ext q
    rw [List.mem_toFinset, Tuples.mem_tuples h, Finset.mem_image]
    constructor
    · rintro ⟨hlen, hq⟩
      subst hlen
      exact ⟨fun j ↦ ⟨q[j.1], hq _ (List.getElem_mem _)⟩, mem_univ _, List.ofFn_getElem⟩
    · rintro ⟨v, -, rfl⟩
      refine ⟨by simp, fun x hx ↦ ?_⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact (v j).2
  rw [himg, Finset.sum_image fun v _ w _ h ↦ hinj h]

/-! ### From lists to sets of facilities -/

private theorem centers_cons {I : Instance} {a : ℕ} (ha : a < I.m) (l : List ℕ) :
    I.centers (a :: l) = insert ⟨a, ha⟩ (I.centers l) := by
  ext i
  simp only [Instance.mem_centers, List.mem_cons, mem_insert, Fin.ext_iff]

private theorem centers_greedyQL {I : Instance} {ρ T : ℕ} {L : List (List ℕ)} (hL : L.length = ρ)
    (Lst' : Fin ρ → Fin T → Fin I.m)
    (hLst' : ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0)
    (j : Fin ρ) (t : Fin T) (v : Fin ρ → Fin T) :
    I.centers (greedyQL L j t (List.ofFn fun j ↦ (v j : ℕ))) = greedyQ Lst' j t v := by
  ext i
  simp only [Instance.mem_centers, greedyQL, List.mem_filterMap, List.mem_range, greedyQ,
    mem_image, mem_union, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hai⟩
    rw [hL] at ha
    rw [getD_ofFn_val v ha] at hai
    by_cases hc : (a < j ∧ (v ⟨a, ha⟩ : ℕ) ≤ t) ∨ (j < a ∧ (v ⟨a, ha⟩ : ℕ) < t)
    · rw [ite_eq_left hc] at hai
      refine ⟨⟨a, ha⟩, ?_, Fin.ext ?_⟩
      · simpa only [Fin.lt_def, Fin.le_def] using hc
      · rw [hLst']
        exact Option.some.inj hai
    · rw [ite_eq_right hc] at hai
      exact absurd hai (by simp)
  · rintro ⟨j', hc, rfl⟩
    refine ⟨j'.1, hL ▸ j'.2, ?_⟩
    have hc' : (j'.1 < j ∧ (v j' : ℕ) ≤ t) ∨ (j < j'.1 ∧ (v j' : ℕ) < t) := by
      simpa only [Fin.lt_def, Fin.le_def] using hc
    rw [getD_ofFn_val v j'.2, ite_eq_left hc', hLst']

private theorem centers_pickQ {I : Instance} {ρ T : ℕ} {L : List (List ℕ)} (hL : L.length = ρ)
    (Lst' : Fin ρ → Fin T → Fin I.m)
    (hLst' : ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0)
    (v : Fin ρ → Fin T) :
    I.centers (pickQ L (List.ofFn fun j ↦ (v j : ℕ))) = univ.image fun j ↦ Lst' j (v j) := by
  ext i
  simp only [Instance.mem_centers, pickQ, List.mem_map, List.mem_range, mem_image, mem_univ,
    true_and]
  constructor
  · rintro ⟨a, ha, hai⟩
    rw [hL] at ha
    refine ⟨⟨a, ha⟩, Fin.ext ?_⟩
    rw [hLst', ← hai, getD_ofFn_val v ha]
  · rintro ⟨j, rfl⟩
    exact ⟨j.1, hL ▸ j.2, by rw [hLst', getD_ofFn_val v j.2]⟩

private theorem greedyQL_lt {L : List (List ℕ)} {m : ℕ} (hLm : ∀ j', ∀ a ∈ L.getD j' [], a < m)
    (hm : 0 < m) (j t : ℕ) (V : List ℕ) : ∀ i ∈ greedyQL L j t V, i < m := by
  intro i hi
  simp only [greedyQL, List.mem_filterMap] at hi
  obtain ⟨a, -, ha⟩ := hi
  by_cases h : (a < j ∧ V.getD a 0 ≤ t) ∨ (j < a ∧ V.getD a 0 < t)
  · rw [ite_eq_left h] at ha
    rw [← Option.some.inj ha]
    exact getD_lt_of (hLm a) hm _
  · rw [ite_eq_right h] at ha
    exact absurd ha (by simp)

private theorem pickQ_lt {L : List (List ℕ)} {m : ℕ} (hLm : ∀ j', ∀ a ∈ L.getD j' [], a < m)
    (hm : 0 < m) (V : List ℕ) : ∀ i ∈ pickQ L V, i < m := by
  intro i hi
  simp only [pickQ, List.mem_map, List.mem_range] at hi
  obtain ⟨a, -, rfl⟩ := hi
  exact getD_lt_of (hLm a) hm _

/-! ### The sequential greedy, exactly -/

/-- **The exact sequential greedy** picks one element of each part and satisfies the guarantee
of `BCFGJPSSV26.Stable.seqGreedy_bound`, for `g` computing a function `G` with `G ∅ - G`
monotone and submodular. -/
private theorem seqGreedyQ_spec {I : Instance} (hm : 1 ≤ I.m) {g : List ℕ → ℚ}
    {G : Finset (Fin I.m) → ℝ}
    (hg : ∀ l : List ℕ, (∀ i ∈ l, i < I.m) → (g l : ℝ) = G (I.centers l))
    (hmono : IsMonoF fun Y ↦ G ∅ - G Y) (hsub : IsSubmod fun Y ↦ G ∅ - G Y)
    {parts : List (List ℕ)} (hp : ∀ j < parts.length, parts.getD j [] ≠ [])
    (hpm : ∀ j < parts.length, ∀ i ∈ parts.getD j [], i < I.m)
    {N B : ℕ} (hN : 1 ≤ N) (hB : N ^ parts.length ≤ B) :
    (seqGreedyQ g parts N B).length = parts.length ∧
    (∀ j < parts.length, (seqGreedyQ g parts N B).getD j 0 ∈ parts.getD j []) ∧
    ∀ o : Fin parts.length → Fin I.m, (∀ j : Fin parts.length, (o j).1 ∈ parts.getD j []) →
      (1 - ((N : ℝ) / (N + 1)) ^ N) * (G ∅ - G (univ.image o)) ≤
        G ∅ - G (I.centers (seqGreedyQ g parts N B)) := by
  classical
  obtain ⟨hLlen, hLj, hent⟩ := greedyR_spec g parts (Tuples.tuples B N parts.length) hp N
  set Vs := Tuples.tuples B N parts.length with hVs
  set L := greedyR g parts Vs N with hL
  have hseq : seqGreedyQ g parts N B = pickQ L (argminBy (fun V ↦ g (pickQ L V)) Vs []) := rfl
  have hVsne : Vs ≠ [] :=
    List.ne_nil_of_mem (Tuples.ofFn_mem_tuples hB fun _ ↦ (⟨0, hN⟩ : Fin N))
  obtain ⟨hVminmem, hVminle⟩ := argminBy_spec (fun V ↦ g (pickQ L V)) hVsne []
  obtain ⟨hVminlen, hVminlt⟩ := Tuples.mem_tuples_le hVminmem
  set Vmin := argminBy (fun V ↦ g (pickQ L V)) Vs [] with hVmin
  -- all entries are facilities
  have hLm : ∀ j', ∀ a ∈ L.getD j' [], a < I.m := by
    intro j' a ha
    by_cases hj' : j' < parts.length
    · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 ha
      have ht' : t < N := by rw [← hLj j' hj']; exact ht
      have := (hent j' hj' t ht').1
      rw [List.getD_eq_getElem _ _ ht] at this
      exact hpm j' hj' _ this
    · rw [List.getD_eq_default _ _ (by rw [hLlen]; omega)] at ha
      simp at ha
  have hm0 : 0 < I.m := by omega
  rw [hseq]
  refine ⟨by simp [pickQ, hLlen], fun j hj ↦ ?_, fun o ho ↦ ?_⟩
  · have hjL : j < (pickQ L Vmin).length := by simp [pickQ, hLlen, hj]
    rw [List.getD_eq_getElem _ _ hjL]
    simp only [pickQ, List.getElem_map, List.getElem_range]
    have hVj : Vmin.getD j 0 < N := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hVminlt _ (List.getElem_mem _)
    exact (hent j hj _ hVj).1
  -- the greedy rule on functions
  obtain ⟨Lst', hLst'⟩ : ∃ Lst' : Fin parts.length → Fin N → Fin I.m,
      ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0 :=
    ⟨fun j t ↦ ⟨_, getD_lt_of (hLm j) hm0 t⟩, fun _ _ ↦ rfl⟩
  have hgain : ∀ (j : Fin parts.length) (t : Fin N) (e : Fin I.m),
      ∑ v : Fin parts.length → Fin N,
        (G (greedyQ Lst' j t v) - G (insert e (greedyQ Lst' j t v))) =
        (gainQ g L j t Vs e : ℝ) := by
    intro j t e
    rw [gainQ, Rat.cast_list_sum, List.map_map, sum_tuples hB]
    refine sum_congr rfl fun v _ ↦ ?_
    have hQm := greedyQL_lt hLm hm0 j t (List.ofFn fun j ↦ (v j : ℕ))
    have hQm' : ∀ i ∈ (e : ℕ) :: greedyQL L j t (List.ofFn fun j ↦ (v j : ℕ)), i < I.m := by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact e.2
      · exact hQm i hi
    rw [← centers_greedyQL hLlen Lst' hLst' j t v]
    simp only [Function.comp_apply, Rat.cast_sub]
    rw [hg _ hQm, hg _ hQm', centers_cons e.2]
  have hIS : IsSeqGreedy (fun Y ↦ G ∅ - G Y) (fun j ↦ I.centers (parts.getD j [])) Lst' := by
    intro j t
    refine ⟨?_, fun e he ↦ ?_⟩
    · simp only [Instance.mem_centers, hLst']
      exact (hent j j.2 t t.2).1
    · have h3 := (hent j j.2 t t.2).2 e.1 (Instance.mem_centers.1 he)
      rw [← hLst'] at h3
      simp only [sub_sub_sub_cancel_left]
      rw [hgain j t e, hgain j t (Lst' j t)]
      exact_mod_cast h3
  have hbound := seqGreedy_bound (f := fun Y ↦ G ∅ - G Y) hmono hsub (by simp) (by omega) hIS o
    (fun j ↦ by simpa only [Instance.mem_centers] using ho j)
  have hpick : ∀ v : Fin parts.length → Fin N, G ∅ - G (univ.image fun j ↦ Lst' j (v j)) ≤
      G ∅ - G (I.centers (pickQ L Vmin)) := by
    intro v
    rw [← centers_pickQ hLlen Lst' hLst' v, ← hg _ (pickQ_lt hLm hm0 _),
      ← hg _ (pickQ_lt hLm hm0 _)]
    have h1 := hVminle _ (Tuples.ofFn_mem_tuples hB v)
    have h2 : (g (pickQ L Vmin) : ℝ) ≤ g (pickQ L (List.ofFn fun j ↦ (v j : ℕ))) := by
      exact_mod_cast h1
    linarith
  have hsum : ∑ v : Fin parts.length → Fin N, (G ∅ - G (univ.image fun j ↦ Lst' j (v j))) ≤
      (G ∅ - G (I.centers (pickQ L Vmin))) * (N : ℝ) ^ parts.length := by
    calc _ ≤ ∑ v : Fin parts.length → Fin N, (G ∅ - G (I.centers (pickQ L Vmin))) :=
          sum_le_sum fun v _ ↦ hpick v
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have hNpos : (0 : ℝ) < (N : ℝ) ^ parts.length := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  exact le_of_mul_le_mul_right (hbound.trans hsum) hNpos

/-! ### The exact submodular function -/

private theorem map_val_filter_mem {n : ℕ} {D : List ℕ} (hn : ∀ j ∈ D, j < n) :
    ((univ : Finset (Fin n)).filter fun j ↦ j.1 ∈ D).map Fin.valEmbedding = D.toFinset := by
  ext j
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, List.mem_toFinset]
  exact ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun h ↦ ⟨⟨j, hn j h⟩, h, rfl⟩⟩

private theorem sum_map_eq_sum_filter {n : ℕ} {D : List ℕ} (hD : D.Nodup) (hn : ∀ j ∈ D, j < n)
    (F : ℕ → ℝ) :
    (D.map F).sum = ∑ j ∈ (univ : Finset (Fin n)).filter (fun j ↦ j.1 ∈ D), F j := by
  classical
  rw [← List.sum_toFinset _ hD, ← map_val_filter_mem hn, Finset.sum_map]
  rfl

private theorem card_filter_mem {n : ℕ} {D : List ℕ} (hD : D.Nodup) (hn : ∀ j ∈ D, j < n) :
    ((univ : Finset (Fin n)).filter fun j ↦ j.1 ∈ D).card = D.length := by
  rw [← card_map Fin.valEmbedding, map_val_filter_mem hn, List.toFinset_card_of_nodup hD]

private theorem g₁Q_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {Y : List ℕ} (hY : ∀ i ∈ Y, i < I.m) :
    ((toRaw I).g₁Q LS' Λ Y : ℝ) = g₁ I (I.centers LS') (toDums I Λ) (I.centers Y) := by
  unfold Raw.g₁Q g₁
  rw [Rat.cast_list_sum, List.map_map, Raw.n_toRaw,
    sum_map_eq_sum_filter List.nodup_range (fun j hj ↦ List.mem_range.1 hj)]
  have : ((univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ List.range I.n) = univ := by
    ext j
    simp
  rw [this]
  refine sum_congr rfl fun j _ ↦ ?_
  have h1 := Raw.dMixQ_toRaw hm hΛ (.inl j)
  have h2 := Raw.dSetQ_toRaw (.inl j) hY
  rw [Instance.ptIdx_inl] at h1 h2
  simp only [Function.comp_apply, Rat.cast_min, h1, h2]

private theorem hclQ_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {blue : List ℕ} (hb : ∀ i ∈ blue, i < I.m) {Y : List ℕ}
    (hY : ∀ i ∈ Y, i < I.m) {c : Fin I.m} (hc : c.1 ∈ LS') :
    ((toRaw I).hclQ LS' Λ blue c Y : ℝ) =
      hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c (I.centers Y) := by
  have hne : LS' ≠ [] := List.ne_nil_of_mem hc
  have hDnd : ((toRaw I).clusterMixQ LS' Λ c).Nodup := List.nodup_range.filter _
  have hDn : ∀ j ∈ (toRaw I).clusterMixQ LS' Λ c, j < I.n :=
    fun j hj ↦ List.mem_range.1 (List.mem_of_mem_filter hj)
  have hDeq : ((univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ (toRaw I).clusterMixQ LS' Λ c) =
      clusterMix I (I.centers LS') (toDums I Λ) c := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact Raw.mem_clusterMixQ hne hm hΛ
  have hcard : ((toRaw I).clusterMixQ LS' Λ c).length =
      (clusterMix I (I.centers LS') (toDums I Λ) c).card := by
    rw [← hDeq, card_filter_mem hDnd hDn]
  have hbY : ∀ i ∈ blue ++ Y, i < I.m := by
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · exact hb i h
    · exact hY i h
  have hcen : I.centers (blue ++ Y) = I.centers blue ∪ I.centers Y := by
    ext i
    simp [Instance.mem_centers]
  have h2 := Raw.dMixQ_toRaw hbY hΛ (.inr c)
  rw [Instance.ptIdx_inr, hcen] at h2
  unfold Raw.hclQ hcl Raw.costMixOnQ costMixOn
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Raw.n_toRaw, h2, hcard, Rat.cast_list_sum,
    List.map_map, sum_map_eq_sum_filter hDnd hDn, hDeq]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  have h1 := Raw.dMixQ_toRaw hm hΛ (.inl j)
  rw [Instance.ptIdx_inl] at h1
  exact h1

private theorem sumSmallest_congr {ι : Type*} {z : ℕ} {A : Finset ι} {u v : ι → ℝ}
    (h : ∀ c ∈ A, u c = v c) : sumSmallest z A u = sumSmallest z A v :=
  le_antisymm (sumSmallest_mono fun c hc ↦ (h c hc).le) (sumSmallest_mono fun c hc ↦ (h c hc).ge)

/-- **Threshold**: a set whose values are at most all the values outside it has the least sum
among the sets of its size. -/
private theorem sum_le_sum_of_forall_le {ι : Type*} {A Zh Z : Finset ι} (v : ι → ℝ)
    (hZ : Z ⊆ A) (hcard : Zh.card = Z.card)
    (hle : ∀ a ∈ Zh, ∀ b ∈ A, b ∉ Zh → v a ≤ v b) : ∑ c ∈ Zh, v c ≤ ∑ c ∈ Z, v c := by
  classical
  rw [← sum_sdiff (inter_subset_left : Zh ∩ Z ⊆ Zh),
    ← sum_sdiff (inter_subset_right : Zh ∩ Z ⊆ Z)]
  have hc : (Zh \ (Zh ∩ Z)).card = (Z \ (Zh ∩ Z)).card := by
    rw [card_sdiff_of_subset inter_subset_left, card_sdiff_of_subset inter_subset_right, hcard]
  rcases (Zh \ (Zh ∩ Z)).eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty] at hc
    rw [h0, card_eq_zero.1 hc.symm]
  · obtain ⟨a, ha, hmax⟩ := exists_max_image _ v hne
    have h1 : ∑ c ∈ Zh \ (Zh ∩ Z), v c ≤ (Zh \ (Zh ∩ Z)).card • v a :=
      sum_le_card_nsmul _ _ _ hmax
    have h2 : (Z \ (Zh ∩ Z)).card • v a ≤ ∑ c ∈ Z \ (Zh ∩ Z), v c := by
      refine card_nsmul_le_sum _ _ _ fun b hb ↦ ?_
      have hb' := mem_sdiff.1 hb
      exact hle a (mem_sdiff.1 ha).1 b (hZ hb'.1) fun hbZh ↦ hb'.2 (mem_inter.2 ⟨hbZh, hb'.1⟩)
    rw [hc] at h1
    linarith

/-- The `z` first entries of a list sorted by `key` attain the sum of the `z` smallest values. -/
private theorem sum_take_mergeSort {I : Instance} {l : List ℕ} (hnd : l.Nodup)
    (hm : ∀ i ∈ l, i < I.m)
    (key : ℕ → ℚ) {z : ℕ} (hz : z ≤ l.length) :
    ∑ c ∈ I.centers ((l.mergeSort fun c c' ↦ decide (key c ≤ key c')).take z), (key c.1 : ℝ) =
      sumSmallest z (I.centers l) fun c ↦ (key c.1 : ℝ) := by
  classical
  set L := l.mergeSort fun c c' ↦ decide (key c ≤ key c') with hL
  have hperm : L.Perm l := List.mergeSort_perm _ _
  have hLnd : L.Nodup := hperm.nodup_iff.2 hnd
  have hsort : L.Pairwise fun c c' ↦ decide (key c ≤ key c') = true :=
    List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b ↦ by simpa using le_total _ _) l
  have htake_m : ∀ i ∈ L.take z, i < I.m := fun i hi ↦ hm i (hperm.subset (List.mem_of_mem_take hi))
  have hsub : I.centers (L.take z) ⊆ I.centers l :=
    Instance.centers_mono fun i hi ↦ hperm.subset (List.mem_of_mem_take hi)
  have hcard : (I.centers (L.take z)).card = z := by
    rw [Instance.card_centers (hLnd.sublist (List.take_sublist _ _)) htake_m, List.length_take,
      hperm.length_eq]
    omega
  refine le_antisymm ?_ (sumSmallest_le hsub hcard _)
  obtain ⟨Z, hZA, hZc, hZs⟩ := exists_sumSmallest_eq (z := z)
    (by rw [Instance.card_centers hnd hm]; exact hz) (fun c : Fin I.m ↦ (key c.1 : ℝ))
  rw [← hZs]
  refine sum_le_sum_of_forall_le _ hZA (by rw [hcard, hZc]) fun a ha b hb hbn ↦ ?_
  have ha' := Instance.mem_centers.1 ha
  have hb' : b.1 ∈ L.drop z := by
    have : b.1 ∈ L := hperm.symm.subset (Instance.mem_centers.1 hb)
    rw [← List.take_append_drop z L, List.mem_append] at this
    exact this.resolve_left fun h ↦ hbn (Instance.mem_centers.2 h)
  have hs := hsort
  rw [← List.take_append_drop z L] at hs
  have hp := (List.pairwise_append.1 hs).2.2 _ ha' _ hb'
  simpa using hp

private theorem sumSmallestQ_map {I : Instance} {l : List ℕ} (hnd : l.Nodup) (hm : ∀ i ∈ l, i < I.m)
    (key : ℕ → ℚ) {z : ℕ} (hz : z ≤ l.length) :
    (Raw.sumSmallestQ z (l.map key) : ℝ) = sumSmallest z (I.centers l) fun c ↦ (key c.1 : ℝ) := by
  rw [← sum_take_mergeSort hnd hm key hz]
  set L := l.mergeSort fun c c' ↦ decide (key c ≤ key c') with hL
  have hperm : L.Perm l := List.mergeSort_perm _ _
  have hLnd : L.Nodup := hperm.nodup_iff.2 hnd
  have hsort : L.Pairwise fun c c' ↦ decide (key c ≤ key c') = true :=
    List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b ↦ by simpa using le_total _ _) l
  have heq : (l.map key).mergeSort (fun a a' ↦ decide (a ≤ a')) = L.map key := by
    refine List.Perm.eq_of_pairwise (le := fun a a' ↦ decide (a ≤ a') = true)
      (fun a b _ _ h1 h2 ↦ by simp only [decide_eq_true_eq] at h1 h2; exact le_antisymm h1 h2)
      (List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
        (fun a b ↦ by simpa using le_total _ _) _)
      (List.pairwise_map.2 hsort) ?_
    exact (List.mergeSort_perm _ _).trans (hperm.map key).symm
  have htake_m : ∀ i ∈ L.take z, i < I.m := fun i hi ↦ hm i (hperm.subset (List.mem_of_mem_take hi))
  unfold Raw.sumSmallestQ
  rw [heq, ← List.map_take, Rat.cast_list_sum, List.map_map]
  exact sum_map_eq_sum_filter (hLnd.sublist (List.take_sublist _ _)) htake_m _

/-- **The exact `g`** is `g` on the facilities. -/
private theorem gQ_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {red blue : List ℕ} (hred : ∀ c ∈ red, c ∈ LS')
    (hrnd : red.Nodup) (hb : ∀ c ∈ blue, c < I.m) {z : ℕ} (hz : z ≤ red.length) {Y : List ℕ}
    (hY : ∀ i ∈ Y, i < I.m) :
    ((toRaw I).gQ LS' Λ red blue z Y : ℝ) =
      gfun I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z (I.centers Y) := by
  have hrm : ∀ c ∈ red, c < I.m := fun c hc ↦ hm c (hred c hc)
  unfold Raw.gQ gfun Raw.g₂Q g₂
  rw [Rat.cast_add, g₁Q_toRaw hm hΛ hY, sumSmallestQ_map hrnd hrm _ hz]
  congr 1
  refine sumSmallest_congr fun c hc ↦ ?_
  exact hclQ_toRaw hm hΛ hb hY (hred _ (Instance.mem_centers.1 hc))

/-! ### Red, blue and the dummies -/

private theorem redOf_sublist : ∀ (LS' : List ℕ) (col : List Bool), (redOf LS' col).Sublist LS'
  | [], _ => by simp [redOf]
  | _ :: _, [] => by simp [redOf]
  | a :: l, b :: c => by
    have ih := redOf_sublist l c
    unfold redOf at ih ⊢
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b
    · exact ih.cons a
    · exact ih.cons_cons a

private theorem blueOf_sublist : ∀ (LS' : List ℕ) (col : List Bool), (blueOf LS' col).Sublist LS'
  | [], _ => by simp [blueOf]
  | _ :: _, [] => by simp [blueOf]
  | a :: l, b :: c => by
    have ih := blueOf_sublist l c
    unfold blueOf at ih ⊢
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b
    · exact ih.cons_cons a
    · exact ih.cons a

private theorem toDums_eq_pmap {I : Instance} : ∀ {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m),
    toDums I Λ = Λ.pmap (fun l h ↦ (⟨finSumFinEquiv.symm ⟨l.1, h⟩, (l.2 : ℝ)⟩ : Dummy I)) hΛ
  | [], _ => rfl
  | l :: Λ, hΛ => by
    have hl : l.1 < I.n + I.m := hΛ l List.mem_cons_self
    have ih := toDums_eq_pmap (Λ := Λ) fun l' hl' ↦ hΛ l' (List.mem_cons_of_mem _ hl')
    unfold toDums at ih ⊢
    rw [List.filterMap_cons, dite_eq_left hl, List.pmap_cons, ih]

private theorem length_toDums' {I : Instance} {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m) :
    (toDums I Λ).length = Λ.length := by
  rw [toDums_eq_pmap hΛ, List.length_pmap]

private theorem getElem_toDums {I : Instance} {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m)
    {j : ℕ}
    (hj : j < Λ.length) :
    (toDums I Λ)[j]'(by rw [length_toDums' hΛ]; exact hj) =
      ⟨finSumFinEquiv.symm ⟨Λ[j].1, hΛ _ (List.getElem_mem _)⟩, (Λ[j].2 : ℝ)⟩ := by
  rw [List.getElem_of_eq (toDums_eq_pmap hΛ), List.getElem_pmap]

/-! ### The candidate -/

/-- The parts of the guess `p'`: the balls of the dummies, then `p'` copies of all facilities. -/
private def partsOf (I : Instance) (Λ : List DumQ) (p' : ℕ) : List (List ℕ) :=
  Λ.map (toRaw I).ballQ ++ List.replicate p' (List.range I.m)

private theorem length_partsOf (I : Instance) (Λ : List DumQ) (p' : ℕ) :
    (partsOf I Λ p').length = Λ.length + p' := by
  simp [partsOf]

private theorem getD_partsOf_lt {I : Instance} {Λ : List DumQ} {p' j : ℕ} (hj : j < Λ.length) :
    (partsOf I Λ p').getD j [] = (toRaw I).ballQ Λ[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_partsOf]; omega)]
  simp only [partsOf]
  rw [List.getElem_append_left (by simpa using hj), List.getElem_map]

private theorem getD_partsOf_ge {I : Instance} {Λ : List DumQ} {p' j : ℕ} (h1 : Λ.length ≤ j)
    (h2 : j < Λ.length + p') : (partsOf I Λ p').getD j [] = List.range I.m := by
  rw [List.getD_eq_getElem _ _ (by rw [length_partsOf]; omega)]
  simp only [partsOf]
  rw [List.getElem_append_right (by simpa using h1), List.getElem_replicate]

variable {I : Instance}

/-- **The specification of the candidate**, unfolded. -/
private theorem candidate_spec_aux (hv : I.Valid) {N B : ℕ} (hN : 1 ≤ N) {LS' : List ℕ}
    (hnd : LS'.Nodup) (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    {col : List Bool} {p' : ℕ} (hB : N ^ (Λ.length + p') ≤ B)
    (hzr : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length)
    (hballs : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ []) :
    let red := redOf LS' col
    let blue := blueOf LS' col
    let z := (LS'.length + (Λ.length + p')) - I.k
    let Y := seqGreedyQ ((toRaw I).gQ LS' Λ red blue z)
      (Λ.map (toRaw I).ballQ ++ List.replicate p' (List.range I.m)) N B
    let Zl := (red.mergeSort fun c c' ↦
      decide ((toRaw I).hclQ LS' Λ blue c Y ≤ (toRaw I).hclQ LS' Λ blue c' Y)).take z
    let T := ((LS'.filter fun c ↦ decide (c ∉ Zl)) ++ Y).dedup
    T.Nodup ∧ (∀ i ∈ T, i < I.m) ∧ T.length ≤ I.k ∧
      ∃ Y' Zh : Finset (Fin I.m), I.centers T = (I.centers LS' \ Zh) ∪ Y' ∧
        (∀ l ∈ toDums I Λ, ∃ i ∈ Y', i ∈ l.ball) ∧ Zh ⊆ I.centers red ∧
        Zh.card = z ∧
        ∑ c ∈ Zh, hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c Y' =
          g₂ I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z Y' ∧
        GreedyGuarantee I N (gfun I (I.centers LS') (toDums I Λ) (I.centers red)
          (I.centers blue) z) (toDums I Λ) p' Y' := by
  intro red blue z Y Zl T
  classical
  have hm1 : 1 ≤ I.m := hv.one_le_m
  have hΛ' : ∀ l ∈ Λ, l.1 < I.n + I.m := hΛ
  -- red and blue
  have hredsub : red.Sublist LS' := redOf_sublist LS' col
  have hrednd : red.Nodup := hnd.sublist hredsub
  have hredLS : ∀ c ∈ red, c ∈ LS' := fun c hc ↦ hredsub.subset hc
  have hredm : ∀ c ∈ red, c < I.m := fun c hc ↦ hm c (hredLS c hc)
  have hbluem : ∀ c ∈ blue, c < I.m := fun c hc ↦ hm c ((blueOf_sublist LS' col).subset hc)
  have hzr' : z ≤ red.length := hzr
  -- the parts
  have hplen : (partsOf I Λ p').length = Λ.length + p' := length_partsOf I Λ p'
  have hballm : ∀ l, ∀ i ∈ (toRaw I).ballQ l, i < I.m :=
    fun l i hi ↦ List.mem_range.1 (List.mem_of_mem_filter hi)
  have hp : ∀ j < (partsOf I Λ p').length, (partsOf I Λ p').getD j [] ≠ [] := by
    intro j hj
    rw [hplen] at hj
    by_cases h : j < Λ.length
    · rw [getD_partsOf_lt h]
      exact hballs _ (List.getElem_mem _)
    · rw [getD_partsOf_ge (by omega) hj]
      exact List.ne_nil_of_mem (List.mem_range.2 (by omega : 0 < I.m))
  have hpm : ∀ j < (partsOf I Λ p').length, ∀ i ∈ (partsOf I Λ p').getD j [], i < I.m := by
    intro j hj i hi
    rw [hplen] at hj
    by_cases h : j < Λ.length
    · rw [getD_partsOf_lt h] at hi
      exact hballm _ i hi
    · rw [getD_partsOf_ge (by omega) hj] at hi
      exact List.mem_range.1 hi
  -- the greedy
  set G := gfun I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z with hG
  have hgG : ∀ l : List ℕ, (∀ i ∈ l, i < I.m) →
      ((toRaw I).gQ LS' Λ red blue z l : ℝ) = G (I.centers l) :=
    fun l hl ↦ gQ_toRaw hm hΛ hredLS hrednd hbluem hzr' hl
  obtain ⟨hYlen, hYmem, hYG⟩ : Y.length = (partsOf I Λ p').length ∧
      (∀ j < (partsOf I Λ p').length, Y.getD j 0 ∈ (partsOf I Λ p').getD j []) ∧
      ∀ o : Fin (partsOf I Λ p').length → Fin I.m,
        (∀ j : Fin (partsOf I Λ p').length, (o j).1 ∈ (partsOf I Λ p').getD j []) →
        (1 - ((N : ℝ) / (N + 1)) ^ N) * (G ∅ - G (univ.image o)) ≤ G ∅ - G (I.centers Y) :=
    seqGreedyQ_spec hm1 hgG (gfun_isMonoF hv _ _ _ _ _) (gfun_isSubmod hv _ _ _ _ _) hp hpm hN
      (by rw [hplen]; exact hB)
  have hYm : ∀ i ∈ Y, i < I.m := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
    have hjp : j < (partsOf I Λ p').length := hYlen ▸ hj
    have := hYmem j hjp
    rw [List.getD_eq_getElem _ _ hj] at this
    exact hpm j hjp _ this
  -- the centers to close
  have hZperm := List.mergeSort_perm red (fun c c' ↦
    decide ((toRaw I).hclQ LS' Λ blue c Y ≤ (toRaw I).hclQ LS' Λ blue c' Y))
  have hZlsub : ∀ c ∈ Zl, c ∈ red := fun c hc ↦ hZperm.subset (List.mem_of_mem_take hc)
  have hZlnd : Zl.Nodup := (hZperm.nodup_iff.2 hrednd).sublist (List.take_sublist _ _)
  have hZllen : Zl.length = z := by
    change (List.take z _).length = z
    rw [List.length_take, hZperm.length_eq]
    omega
  have hZlm : ∀ c ∈ Zl, c < I.m := fun c hc ↦ hredm c (hZlsub c hc)
  -- the candidate
  have hTm : ∀ i ∈ T, i < I.m := by
    intro i hi
    simp only [T, List.mem_dedup, List.mem_append, List.mem_filter] at hi
    rcases hi with hi | hi
    · exact hm i hi.1
    · exact hYm i hi
  have hTc : I.centers T = (I.centers LS' \ I.centers Zl) ∪ I.centers Y := by
    ext i
    simp only [T, Instance.mem_centers, List.mem_dedup, List.mem_append, List.mem_filter,
      mem_union, mem_sdiff, decide_eq_true_eq]
  have hTlen : T.length ≤ I.k := by
    have h1 : T.length = (I.centers T).card :=
      (Instance.card_centers (List.nodup_dedup _) hTm).symm
    have h2 : (I.centers T).card ≤ (I.centers LS' \ I.centers Zl).card + (I.centers Y).card := by
      rw [hTc]
      exact card_union_le _ _
    have h3 : (I.centers LS' \ I.centers Zl).card = LS'.length - z := by
      rw [card_sdiff_of_subset (Instance.centers_mono fun c hc ↦ hredLS c (hZlsub c hc)),
        Instance.card_centers hnd hm, Instance.card_centers hZlnd hZlm, hZllen]
    have h4 : (I.centers Y).card ≤ Λ.length + p' :=
      (Instance.card_centers_le Y).trans (by rw [hYlen, hplen])
    have h5 : z ≤ LS'.length := hzr'.trans hredsub.length_le
    have hz : z = (LS'.length + (Λ.length + p')) - I.k := rfl
    omega
  -- the balls
  have hYball : ∀ l ∈ toDums I Λ, ∃ i ∈ I.centers Y, i ∈ l.ball := by
    intro l hl
    rw [toDums_eq_pmap hΛ', List.mem_pmap] at hl
    obtain ⟨a, haΛ, rfl⟩ := hl
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 haΛ
    have hjp : j < (partsOf I Λ p').length := by rw [hplen]; omega
    have hmem := hYmem j hjp
    rw [getD_partsOf_lt hj] at hmem
    have hjY : j < Y.length := by rw [hYlen]; exact hjp
    rw [List.getD_eq_getElem _ _ hjY] at hmem
    exact ⟨⟨Y[j], hYm _ (List.getElem_mem _)⟩, Instance.mem_centers.2 (List.getElem_mem _),
      (Raw.mem_ballQ (hΛ' _ haΛ)).1 hmem⟩
  -- the sum of the `z` smallest
  have hkey : ∀ c ∈ I.centers red,
      hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c (I.centers Y) =
        ((toRaw I).hclQ LS' Λ blue c Y : ℝ) :=
    fun c hc ↦ (hclQ_toRaw hm hΛ hbluem hYm (hredLS _ (Instance.mem_centers.1 hc))).symm
  have hZs : ∑ c ∈ I.centers Zl, hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c
      (I.centers Y) = g₂ I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z
      (I.centers Y) := by
    unfold g₂
    rw [sum_congr rfl fun c hc ↦ hkey c (Instance.centers_mono hZlsub hc),
      sumSmallest_congr hkey]
    exact sum_take_mergeSort hrednd hredm (fun c ↦ (toRaw I).hclQ LS' Λ blue c Y) hzr'
  -- the greedy guarantee
  have hGG : GreedyGuarantee I N G (toDums I Λ) p' (I.centers Y) := by
    unfold GreedyGuarantee
    intro o ho E hE
    have hlenD : (toDums I Λ).length = Λ.length := length_toDums' hΛ'
    have hjE : ∀ j : Fin (partsOf I Λ p').length, ¬ j.1 < Λ.length →
        j.1 - Λ.length < E.card := by
      intro j hj
      have := j.2
      omega
    let o' : Fin (partsOf I Λ p').length → Fin I.m := fun j ↦
      if h : j.1 < Λ.length then o ⟨j.1, by rw [hlenD]; exact h⟩
      else (E.equivFin.symm ⟨j.1 - Λ.length, hjE j h⟩ : Fin I.m)
    have ho' : ∀ j : Fin (partsOf I Λ p').length, (o' j).1 ∈ (partsOf I Λ p').getD j [] := by
      intro j
      by_cases h : j.1 < Λ.length
      · have h1 : o' j = o ⟨j.1, by rw [hlenD]; exact h⟩ := dite_eq_left h
        rw [h1, getD_partsOf_lt h]
        have := ho ⟨j.1, by rw [hlenD]; exact h⟩
        rw [List.get_eq_getElem, getElem_toDums hΛ' h] at this
        exact (Raw.mem_ballQ (hΛ' _ (List.getElem_mem _))).2 this
      · have : j.1 < Λ.length + p' := by have := j.2; omega
        rw [getD_partsOf_ge (by omega) this]
        exact List.mem_range.2 (o' j).2
    have himg : univ.image o' = univ.image o ∪ E := by
      ext i
      simp only [mem_image, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨j, rfl⟩
        by_cases h : j.1 < Λ.length
        · have h1 : o' j = o ⟨j.1, by rw [hlenD]; exact h⟩ := dite_eq_left h
          exact .inl ⟨_, h1.symm⟩
        · right
          have h1 : o' j = (E.equivFin.symm ⟨j.1 - Λ.length, hjE j h⟩ : Fin I.m) :=
            dite_eq_right h
          rw [h1]
          exact (E.equivFin.symm _).2
      · rintro (⟨i₀, rfl⟩ | hi)
        · have h : i₀.1 < Λ.length := by have := i₀.2; omega
          refine ⟨⟨i₀.1, by rw [hplen]; omega⟩, ?_⟩
          exact dite_eq_left h
        · have hb := (E.equivFin ⟨i, hi⟩).2
          have h : ¬ (Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) < Λ.length) := by omega
          refine ⟨⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ), by rw [hplen]; omega⟩, ?_⟩
          have h1 : o' ⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ), by rw [hplen]; omega⟩ =
              (E.equivFin.symm ⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) - Λ.length,
                hjE ⟨_, by rw [hplen]; omega⟩ h⟩ : Fin I.m) := dite_eq_right h
          rw [h1]
          have h2 : (⟨Λ.length + (E.equivFin ⟨i, hi⟩ : ℕ) - Λ.length,
              hjE ⟨_, by rw [hplen]; omega⟩ h⟩ : Fin E.card) = E.equivFin ⟨i, hi⟩ :=
            Fin.ext (by simp)
          rw [h2, Equiv.symm_apply_apply]
    have := hYG o' ho'
    rw [himg] at this
    exact this
  exact ⟨List.nodup_dedup _, hTm, hTlen, I.centers Y, I.centers Zl, hTc, hYball,
    Instance.centers_mono hZlsub, by rw [Instance.card_centers hZlnd hZlm, hZllen], hZs, hGG⟩

end Helpers

variable {I : Instance}

/-- **The guess is not skipped** when its conditions hold. -/
theorem candidate_isSome {N s B : ℕ} {LS' : List ℕ} {Λ : List DumQ} {col : List Bool} {p' : ℕ}
    (hρ : Λ.length + p' ≤ s) (hz : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length)
    (hball : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ []) :
    (candidate N (toRaw I) s B LS' Λ col p').isSome := by
  have hk : (toRaw I).k = I.k := rfl
  have hcond : ¬ (s < Λ.length + p' ∨
      (redOf LS' col).length < LS'.length + (Λ.length + p') - (toRaw I).k ∨
        (Λ.any fun l ↦ ((toRaw I).ballQ l).isEmpty) = true) := by
    rintro (h | h | h)
    · omega
    · omega
    · obtain ⟨l, hl, he⟩ := List.any_eq_true.1 h
      exact hball l hl (List.isEmpty_iff.1 he)
  dsimp only [candidate]
  rw [ite_eq_right hcond]
  rfl

open Classical in
/-- **The specification of a computed candidate.** -/
theorem candidate_spec (hv : I.Valid) {N s B : ℕ} (hN : 1 ≤ N) {LS' : List ℕ}
    (hnd : LS'.Nodup) (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    {col : List Bool} (hcol : col.length = LS'.length) {p' : ℕ} (hB : N ^ (Λ.length + p') ≤ B)
    {T : List ℕ} (hT : candidate N (toRaw I) s B LS' Λ col p' = some T) :
    T.Nodup ∧ (∀ i ∈ T, i < I.m) ∧ T.length ≤ I.k ∧
      ∃ Y Zh : Finset (Fin I.m), I.centers T = (I.centers LS' \ Zh) ∪ Y ∧
        (∀ l ∈ toDums I Λ, ∃ i ∈ Y, i ∈ l.ball) ∧ Zh ⊆ I.centers (redOf LS' col) ∧
        Zh.card = (LS'.length + (Λ.length + p')) - I.k ∧
        ∑ c ∈ Zh, hcl I (I.centers LS') (toDums I Λ) (I.centers (blueOf LS' col)) c Y =
          g₂ I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
            (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k) Y ∧
        GreedyGuarantee I N (gfun I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
          (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k))
          (toDums I Λ) p' Y := by
  have _ := hcol
  have hT' := hT
  dsimp only [candidate] at hT'
  have hk : (toRaw I).k = I.k := rfl
  by_cases hskip : s < Λ.length + p' ∨
      (redOf LS' col).length < LS'.length + (Λ.length + p') - (toRaw I).k ∨
        (Λ.any fun l ↦ ((toRaw I).ballQ l).isEmpty) = true
  · rw [ite_eq_left hskip] at hT'
    exact absurd hT' (by simp)
  rw [ite_eq_right hskip] at hT'
  have hzr : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length := by
    simp only [not_or, not_lt] at hskip
    have := hskip.2.1
    omega
  have hballs : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ [] := by
    intro l hl he
    simp only [not_or] at hskip
    exact hskip.2.2 (List.any_eq_true.2 ⟨l, hl, by simp [he]⟩)
  obtain rfl := (Option.some.inj hT').symm
  exact candidate_spec_aux hv hN hnd hm hΛ hB hzr hballs

end Stable

end BCFGJPSSV26
