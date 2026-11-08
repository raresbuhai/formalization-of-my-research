module

public import BB20.Machine.Search

/-!
# The algorithms as one loop

The algorithms of Theorems 6 and 11 (`BB20.alg6`, `BB20.alg11`) as a single state machine
(`BB20.Machine.Run.fstep`) run for a number of rounds of the form `a · b^k`, as the loop of
`BB20/Machine/Loop.lean` requires.

For each variable `u < n` there are `2n` phases: `n` greedy steps (`BB20.Machine.Run.growL`), then
the pruning of each `i < n`. Every phase is a search (`BB20.Machine.Run.search`) of exactly
`K = (n + 1)^k` rounds; at its last round the state between phases (`BB20.Machine.Run.Mac`) is
updated with the result (`BB20.Machine.Run.trans`). The pruning of Theorem 11 uses the result of
its search; the pruning of Theorem 6 does not search, and tests `i` directly. So the loop runs
`2n · n · K` rounds (`BB20.Machine.Run.run_eq`), and on a well-formed input, with `n` and
`k = min(2^s, n)`, it outputs what the algorithms output (`BB20.Machine.Run.run6_eq`,
`BB20.Machine.Run.run11_eq`). On other inputs, or without thresholds, it runs `0` rounds and outputs
`[]`, as the algorithms do.
-/

@[expose] public section

namespace BB20.Machine.Run

open Finset

/-! ### The greedy step and the pruning step on lists -/

/-- One greedy step on lists: add the first candidate above the threshold. -/
def growL (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (k : ℕ) (S : List ℕ) : List ℕ :=
  S ++ (search samples n u t k S).getD []

/-- The greedy steps on lists. -/
def greedyL (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (k : ℕ) : List ℕ :=
  (growL samples n u t k)^[n] []

theorem toFinset_erase {S : List ℕ} (hS : S.Nodup) (i : ℕ) :
    (S.erase i).toFinset = S.toFinset.erase i := by
  ext a
  simp [hS.mem_erase_iff]

/-- The greedy steps on lists are those of `BB20.greedy`. -/
theorem growL_spec {samples : List (List Bool)} {n u : ℕ} {t : ℚ} {k K : ℕ} (hu : u < n)
    (hk : ∀ S, candList n u k S = candList n u K S) (g : ℕ) :
    ((growL samples n u t k)^[g] []).toFinset =
        (grow (fun I S ↦ empNuL samples n u I S) n u K t)^[g] ∅ ∧
      ((growL samples n u t k)^[g] []).Nodup ∧
      ∀ i ∈ (growL samples n u t k)^[g] [], i < n ∧ i ≠ u := by
  induction g with
  | zero => simp
  | succ g ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← h1]
    set Sl := (growL samples n u t k)^[g] []
    have hs := search_eq (samples := samples) (t := t) (k := k) hu (fun i hi ↦ (h3 i hi).1)
      (fun h ↦ (h3 u h).2 rfl) h2
    unfold growL grow
    rw [hs, hk]
    cases hf : (candList n u K Sl.toFinset).find?
        (fun l ↦ decide (t < empNuL samples n u l.toFinset Sl.toFinset)) with
    | none => simpa using ⟨h2, h3⟩
    | some l =>
      obtain ⟨hl, -, -, hli⟩ := mem_candList.1 (List.mem_of_find?_eq_some hf)
      refine ⟨by simp [List.toFinset_append], List.nodup_append.2 ⟨h2, hl.nodup, ?_⟩, ?_⟩
      · rintro a ha b hb rfl
        exact (hli a hb).2.2 (List.mem_toFinset.2 ha)
      · intro i hi
        rcases List.mem_append.1 (by simpa using hi) with hi | hi
        · exact h3 i hi
        · exact ⟨(hli i hi).1, (hli i hi).2.1⟩

/-- The pruning of Theorem 6 on lists. -/
theorem prune6_eq {samples : List (List Bool)} {n u : ℕ} {t : ℚ} {Sl : List ℕ} (hu : u < n)
    (hn : Sl.Nodup) (hS : ∀ i ∈ Sl, i < n ∧ i ≠ u) :
    (List.range n).filter
        (fun i ↦ decide (i ∈ Sl) && decide (t < effNu samples n u [i] (Sl.erase i))) =
      (Sl.toFinset.filter fun i ↦ t < empNuL samples n u {i} (Sl.toFinset.erase i)).sort
        (· ≤ ·) := by
  refine (((List.sortedLT_range n).pairwise.sublist List.filter_sublist).sortedLT).eq_of_mem_iff
    (Finset.sortedLT_sort _) fun i ↦ ?_
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_sort, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨-, hi, ht⟩
    refine ⟨hi, ?_⟩
    rwa [effNu_eq hu (by simpa using (hS i hi).1) (fun j hj ↦ (hS j (List.mem_of_mem_erase hj)).1)
      (by simpa using fun h ↦ (hS i hi).2 h.symm)
      (fun h ↦ (hS u (List.mem_of_mem_erase h)).2 rfl) (by simp [hn.mem_erase_iff])
      (List.nodup_singleton i) (hn.erase i), toFinset_erase hn] at ht
  · rintro ⟨hi, ht⟩
    refine ⟨(hS i hi).1, hi, ?_⟩
    rwa [effNu_eq hu (by simpa using (hS i hi).1) (fun j hj ↦ (hS j (List.mem_of_mem_erase hj)).1)
      (by simpa using fun h ↦ (hS i hi).2 h.symm)
      (fun h ↦ (hS u (List.mem_of_mem_erase h)).2 rfl) (by simp [hn.mem_erase_iff])
      (List.nodup_singleton i) (hn.erase i), toFinset_erase hn]

theorem find?_isSome_eq_any {α : Type} (l : List α) (p : α → Bool) :
    (l.find? p).isSome = l.any p := by
  rw [Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]

/-- The pruning of Theorem 11 on lists. -/
theorem prune11_eq {samples : List (List Bool)} {n u : ℕ} {t : ℚ} {k K : ℕ} {Sl : List ℕ}
    (hu : u < n) (hk : ∀ S, candList n u k S = candList n u K S) (hn : Sl.Nodup)
    (hS : ∀ i ∈ Sl, i < n ∧ i ≠ u) :
    (List.range n).filter
        (fun i ↦ decide (i ∈ Sl) && (search samples n u t k (Sl.erase i)).isSome) =
      (Sl.toFinset.filter fun i ↦ (candList n u K (Sl.toFinset.erase i)).any fun l ↦
        decide (t < empNuL samples n u l.toFinset (Sl.toFinset.erase i))).sort (· ≤ ·) := by
  refine (((List.sortedLT_range n).pairwise.sublist List.filter_sublist).sortedLT).eq_of_mem_iff
    (Finset.sortedLT_sort _) fun i ↦ ?_
  have hsearch : ∀ i, (search samples n u t k (Sl.erase i)).isSome =
      (candList n u K (Sl.toFinset.erase i)).any fun l ↦
        decide (t < empNuL samples n u l.toFinset (Sl.toFinset.erase i)) := by
    intro i
    rw [search_eq hu (fun j hj ↦ (hS j (List.mem_of_mem_erase hj)).1)
      (fun h ↦ (hS u (List.mem_of_mem_erase h)).2 rfl) (hn.erase i), hk, toFinset_erase hn,
      find?_isSome_eq_any]
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_sort, Finset.mem_filter, List.mem_toFinset, hsearch]
  constructor
  · rintro ⟨-, hi, ht⟩
    exact ⟨hi, ht⟩
  · rintro ⟨hi, ht⟩
    exact ⟨(hS i hi).1, hi, ht⟩

/-! ### The loop -/

/-- The data of a run: the samples, `n`, `k`, `K = (n + 1)^k`, the thresholds `t₂` and `t₃`, and
whether the pruning step searches (Theorem 11) or tests single variables (Theorem 6). -/
abbrev Dat := List (List Bool) × ℕ × ℕ × ℕ × ℚ × ℚ × Bool

/-- The state between phases: the variable `u`, the phase, the current set `S`, the variables kept
so far by the pruning step, and the lists output so far. -/
abbrev Mac := ℕ × ℕ × List ℕ × List ℕ × List (List ℕ)

/-- The state within a phase: the round, the current word, and the best candidate so far. -/
abbrev Inn := ℕ × List ℕ × Option (List ℕ)

/-- The state of the loop. -/
abbrev St := Dat × Mac × Inn

/-- The set the search of phase `ph` conditions on: `S` in the greedy phases `ph < n`, and
`S ∖ {ph - n}` in the pruning phases. -/
def curS (n ph : ℕ) (S : List ℕ) : List ℕ := if ph < n then S else S.erase (ph - n)

/-- The threshold of the search of phase `ph`. -/
def curT (n ph : ℕ) (t₂ t₃ : ℚ) : ℚ := if ph < n then t₂ else t₃

/-- Whether the pruning step keeps `i`, given the result `r` of its search. -/
def keep (samples : List (List Bool)) (n u : ℕ) (t₃ : ℚ) (mode : Bool) (S : List ℕ) (i : ℕ)
    (r : Option (List ℕ)) : Bool :=
  decide (i ∈ S) && if mode then r.isSome else decide (t₃ < effNu samples n u [i] (S.erase i))

/-- The variables kept by the pruning step so far, after the phase `ph ≥ n` with result `r`. -/
def newP (d : Dat) (m : Mac) (r : Option (List ℕ)) : List ℕ :=
  m.2.2.2.1 ++ if keep d.1 d.2.1 m.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 m.2.2.1 (m.2.1 - d.2.1) r then
    [m.2.1 - d.2.1] else []

/-- The end of a phase with search result `r`: a greedy step, or a pruning step, after which the
next variable starts. -/
def trans (d : Dat) (m : Mac) (r : Option (List ℕ)) : Mac :=
  if m.2.1 < d.2.1 then (m.1, m.2.1 + 1, m.2.2.1 ++ r.getD [], m.2.2.2)
  else if m.2.1 + 1 < 2 * d.2.1 then (m.1, m.2.1 + 1, m.2.2.1, newP d m r, m.2.2.2.2)
  else (m.1 + 1, 0, [], [], m.2.2.2.2 ++ [newP d m r])

/-- A round of the search of the current phase. -/
def sstepAt (d : Dat) (m : Mac) (q : List ℕ × Option (List ℕ)) : List ℕ × Option (List ℕ) :=
  sstep d.1 d.2.1 m.1 (curT d.2.1 m.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1) (curS d.2.1 m.2.1 m.2.2.1) q

/-- **A round of the loop**: a round of the search, and at the last round of a phase, the end of
the phase. Once all variables are done, nothing changes. -/
def fstep (s : St) : St :=
  if s.2.1.1 < s.1.2.1 then
    if s.2.2.1 + 1 < s.1.2.2.2.1 then (s.1, s.2.1, s.2.2.1 + 1, sstepAt s.1 s.2.1 s.2.2.2)
    else (s.1, trans s.1 s.2.1 (sstepAt s.1 s.2.1 s.2.2.2).2, 0, List.replicate s.1.2.2.1 0, none)
  else s

/-- The state at the start of a phase. -/
def inn0 (d : Dat) : Inn := (0, List.replicate d.2.2.1 0, none)

/-- The start of a run. -/
def start (d : Dat) : St := (d, (0, 0, [], [], []), inn0 d)

/-- The output: the lists output so far. -/
def finish (s : St) : List (List ℕ) := s.2.1.2.2.2.2

/-- A phase between phases: the search, and the end of the phase. -/
def mstep (d : Dat) (m : Mac) : Mac :=
  if m.1 < d.2.1 then
    trans d m (search d.1 d.2.1 m.1 (curT d.2.1 m.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1) d.2.2.1
      (curS d.2.1 m.2.1 m.2.2.1))
  else m

/-- **A phase takes `K` rounds.** -/
theorem fstep_phase (d : Dat) (m : Mac) (hK : d.2.2.2.1 = (d.2.1 + 1) ^ d.2.2.1) :
    fstep^[d.2.2.2.1] (d, m, inn0 d) = (d, mstep d m, inn0 d) := by
  obtain ⟨smp, n, k, K, t₂, t₃, mode⟩ := d
  obtain ⟨u, ph, S, P, acc⟩ := m
  simp only at hK
  subst hK
  by_cases hu : u < n
  · have hit : ∀ i, i < (n + 1) ^ k → fstep^[i] ((smp, n, k, (n + 1) ^ k, t₂, t₃, mode),
        (u, ph, S, P, acc), inn0 (smp, n, k, (n + 1) ^ k, t₂, t₃, mode)) =
        ((smp, n, k, (n + 1) ^ k, t₂, t₃, mode), (u, ph, S, P, acc), i,
          (sstep smp n u (curT n ph t₂ t₃) (curS n ph S))^[i] (List.replicate k 0, none)) := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
        simp only [fstep, hu, ↓reduceIte, hi, sstepAt]
    have hpos : 0 < (n + 1) ^ k := pow_pos (Nat.succ_pos n) k
    obtain ⟨K, hK⟩ : ∃ K, (n + 1) ^ k = K + 1 := ⟨(n + 1) ^ k - 1, by omega⟩
    rw [hK, Function.iterate_succ_apply', ← hK, hit K (by omega)]
    simp only [fstep, hu, ↓reduceIte, show ¬ K + 1 < (n + 1) ^ k by omega, sstepAt, mstep,
      search, inn0]
    rw [← Function.iterate_succ_apply' (sstep smp n u (curT n ph t₂ t₃) (curS n ph S)), hK]
  · have hfix : fstep ((smp, n, k, (n + 1) ^ k, t₂, t₃, mode), (u, ph, S, P, acc),
        inn0 (smp, n, k, (n + 1) ^ k, t₂, t₃, mode)) =
        ((smp, n, k, (n + 1) ^ k, t₂, t₃, mode), (u, ph, S, P, acc),
          inn0 (smp, n, k, (n + 1) ^ k, t₂, t₃, mode)) := by
      simp [fstep, hu]
    rw [Function.iterate_fixed hfix]
    simp [mstep, hu]

/-- **`p` phases take `K p` rounds.** -/
theorem fstep_phases (d : Dat) (hK : d.2.2.2.1 = (d.2.1 + 1) ^ d.2.2.1) (p : ℕ) (m : Mac) :
    fstep^[d.2.2.2.1 * p] (d, m, inn0 d) = (d, (mstep d)^[p] m, inn0 d) := by
  induction p generalizing m with
  | zero => rfl
  | succ p ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, fstep_phase d m hK, ih,
      Function.iterate_succ_apply]

/-- The value of `perU` at `u`: the variables kept for `u`. -/
def perU (d : Dat) (u : ℕ) : List ℕ :=
  (List.range d.2.1).filter fun i ↦
    keep d.1 d.2.1 u d.2.2.2.2.2.1 d.2.2.2.2.2.2 (greedyL d.1 d.2.1 u d.2.2.2.2.1 d.2.2.1) i
      (search d.1 d.2.1 u d.2.2.2.2.2.1 d.2.2.1
        ((greedyL d.1 d.2.1 u d.2.2.2.2.1 d.2.2.1).erase i))

theorem mstep_greedy (d : Dat) {u : ℕ} (hu : u < d.2.1) (acc : List (List ℕ)) {g : ℕ}
    (hg : g ≤ d.2.1) :
    (mstep d)^[g] (u, 0, [], [], acc) =
      (u, g, (growL d.1 d.2.1 u d.2.2.2.2.1 d.2.2.1)^[g] [], [], acc) := by
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
    simp only [mstep, hu, ↓reduceIte, trans, curT, curS, show g < d.2.1 by omega, growL]

theorem mstep_prune (d : Dat) {u : ℕ} (hu : u < d.2.1) (S : List ℕ) (acc : List (List ℕ))
    {i : ℕ} (hi : i < d.2.1) :
    (mstep d)^[i] (u, d.2.1, S, [], acc) =
      (u, d.2.1 + i, S, (List.range i).filter fun j ↦
        keep d.1 d.2.1 u d.2.2.2.2.2.1 d.2.2.2.2.2.2 S j
          (search d.1 d.2.1 u d.2.2.2.2.2.1 d.2.2.1 (S.erase j)), acc) := by
  obtain ⟨smp, n, k, K, t₂, t₃, mode⟩ := d
  simp only at hu hi ⊢
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [mstep, hu, ↓reduceIte, trans, curT, curS, newP,
      show ¬ n + i < n by omega, ← Nat.add_assoc, Nat.add_sub_cancel_left, List.range_succ,
      List.filter_append, List.filter_singleton, Bool.cond_eq_ite]
    rw [ite_eq_left (show n + i + 1 < 2 * n by omega)]

theorem mstep_var (d : Dat) {u : ℕ} (hu : u < d.2.1) (acc : List (List ℕ)) :
    (mstep d)^[2 * d.2.1] (u, 0, [], [], acc) = (u + 1, 0, [], [], acc ++ [perU d u]) := by
  obtain ⟨smp, n, k, K, t₂, t₃, mode⟩ := d
  simp only at hu ⊢
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hg := mstep_greedy (smp, n' + 1, k, K, t₂, t₃, mode) hu acc le_rfl
  have hp := mstep_prune (smp, n' + 1, k, K, t₂, t₃, mode) hu
    ((growL smp (n' + 1) u t₂ k)^[n' + 1] []) acc (i := n') (by simp)
  simp only at hg hp
  rw [show 2 * (n' + 1) = 1 + (n' + (n' + 1)) by omega, Function.iterate_add_apply,
    Function.iterate_add_apply, hg, hp]
  simp only [Function.iterate_one, mstep, hu, ↓reduceIte, trans, curT, curS, newP,
    show ¬ n' + 1 + n' < n' + 1 by omega, show ¬ n' + 1 + n' + 1 < 2 * (n' + 1) by omega,
    Nat.add_sub_cancel_left, perU, greedyL, List.range_succ, List.filter_append,
    List.filter_singleton, Bool.cond_eq_ite]

theorem mstep_all (d : Dat) {u : ℕ} (hu : u ≤ d.2.1) :
    (mstep d)^[2 * d.2.1 * u] (0, 0, [], [], []) =
      (u, 0, [], [], (List.range u).map (perU d)) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih (by omega),
      mstep_var d (by omega), List.range_succ, List.map_append, List.map_singleton]

/-- **The run**: `2n · n · K` rounds output the variables kept for each `u < n`. -/
theorem run_eq (d : Dat) (hK : d.2.2.2.1 = (d.2.1 + 1) ^ d.2.2.1) :
    finish (fstep^[2 * d.2.1 * d.2.1 * d.2.2.2.1] (start d)) =
      (List.range d.2.1).map (perU d) := by
  rw [mul_comm _ d.2.2.2.1, start, fstep_phases d hK, mstep_all d le_rfl]
  rfl

/-! ### The algorithms -/

/-- Whether the input is well formed (`BB20.WellFormed`), as a Boolean. -/
def wf (x : Input) : Bool := !x.samples.isEmpty && x.samples.all fun l ↦ decide (l.length = x.n)

theorem wf_iff (x : Input) : wf x = true ↔ WellFormed x := by
  simp [wf, WellFormed, List.all_eq_true]

/-- The number of variables, capped by the length of the encoded input (it is the number of
variables on well-formed inputs). -/
def capN (x : Input) : ℕ := min (encInput x).length x.n

/-- The size bound `min(n, 2^s)` of the candidates, computed as `min(n, 2^{min(n, s)})`. -/
def capK (x : Input) : ℕ := min (capN x) (2 ^ min (capN x) x.s)

/-- The data of a run on `x` with thresholds `t₂`, `t₃`. -/
def datOf (x : Input) (t₂ t₃ : ℚ) (mode : Bool) : Dat :=
  (x.samples, capN x, capK x, (capN x + 1) ^ capK x, t₂, t₃, mode)

/-- The start of the run of the algorithm of Theorem 6. -/
def init6 (thr : Input → Option ℚ) (x : Input) : St :=
  start (datOf x ((thr x).getD 0) ((thr x).getD 0) false)

/-- The start of the run of the algorithm of Theorem 11. -/
def init11 (thr : Input → Option (ℚ × ℚ)) (x : Input) : St :=
  start (datOf x ((thr x).getD (0, 0)).1 ((thr x).getD (0, 0)).2 true)

/-- The number of phases of the run of the algorithm of Theorem 6 (each of `(n + 1)^k`
rounds). -/
def rounds6 (thr : Input → Option ℚ) (x : Input) : ℕ :=
  if wf x && (thr x).isSome then 2 * capN x * capN x else 0

/-- The number of phases of the run of the algorithm of Theorem 11. -/
def rounds11 (thr : Input → Option (ℚ × ℚ)) (x : Input) : ℕ :=
  if wf x && (thr x).isSome then 2 * capN x * capN x else 0

theorem n_le_length {x : Input} (hx : WellFormed x) : x.n ≤ (encInput x).length := by
  obtain ⟨hne, hlen⟩ := hx
  obtain ⟨l, rest, hl⟩ := List.exists_cons_of_ne_nil hne
  have hn := hlen l (by simp [hl])
  have h : (Encoding.encList Encoding.encBits x.samples).length ≤ (encInput x).length := by
    simp [encInput, Encoding.encPair, Encoding.frame]
    omega
  rw [hl] at h
  simp [Encoding.encList, Encoding.encBits, Encoding.frame] at h
  omega

theorem capN_eq {x : Input} (hx : WellFormed x) : capN x = x.n := min_eq_right (n_le_length hx)

theorem min_two_pow (n s : ℕ) : min n (2 ^ min n s) = min (2 ^ s) n := by
  rcases le_total s n with h | h
  · rw [min_eq_right h, min_comm]
  · rw [min_eq_left h, min_eq_left (Nat.lt_two_pow_self).le,
      min_eq_right ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) h))]

theorem candList_capK {x : Input} (hx : WellFormed x) (u : ℕ) (S : Finset ℕ) :
    candList x.n u (capK x) S = candList x.n u (2 ^ x.s) S := by
  rw [capK, capN_eq hx, min_two_pow, ← candList_min]

/-- **The run of the algorithm of Theorem 6.** -/
theorem run6_eq (thr : Input → Option ℚ) (x : Input) :
    finish (fstep^[rounds6 thr x * (capN x + 1) ^ capK x] (init6 thr x)) = alg6 thr x := by
  unfold rounds6 alg6
  by_cases hw : WellFormed x
  · rw [ite_eq_left hw]
    cases ht : thr x with
    | none => simp; rfl
    | some t =>
      have hwf : wf x = true := (wf_iff x).2 hw
      simp only [hwf, Option.isSome_some, Bool.and_self, ↓reduceIte]
      have h := run_eq (datOf x t t false) rfl
      simp only [datOf] at h
      rw [init6, ht, Option.getD_some, datOf, h, capN_eq hw]
      refine List.map_congr_left fun u hu ↦ ?_
      have hu' : u < x.n := List.mem_range.1 hu
      have hk : ∀ S, candList x.n u (capK x) S = candList x.n u (2 ^ x.s) S :=
        candList_capK hw u
      obtain ⟨h1, h2, h3⟩ := growL_spec (samples := x.samples) (t := t) hu' hk x.n
      simp only [perU, keep, Bool.false_eq_true, ↓reduceIte, greedyL]
      refine (prune6_eq hu' h2 h3).trans ?_
      rw [h1]
      rfl
  · rw [ite_eq_right hw]
    have hwf : wf x = false := by
      rw [← Bool.not_eq_true, wf_iff]
      exact hw
    simp only [hwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, zero_mul,
      Function.iterate_zero, id_eq]
    rfl

/-- **The run of the algorithm of Theorem 11.** -/
theorem run11_eq (thr : Input → Option (ℚ × ℚ)) (x : Input) :
    finish (fstep^[rounds11 thr x * (capN x + 1) ^ capK x] (init11 thr x)) = alg11 thr x := by
  unfold rounds11 alg11
  by_cases hw : WellFormed x
  · rw [ite_eq_left hw]
    cases ht : thr x with
    | none => simp; rfl
    | some t =>
      obtain ⟨t₂, t₃⟩ := t
      have hwf : wf x = true := (wf_iff x).2 hw
      simp only [hwf, Option.isSome_some, Bool.and_self, ↓reduceIte]
      have h := run_eq (datOf x t₂ t₃ true) rfl
      simp only [datOf] at h
      rw [init11, ht, Option.getD_some, datOf, h, capN_eq hw]
      refine List.map_congr_left fun u hu ↦ ?_
      have hu' : u < x.n := List.mem_range.1 hu
      have hk : ∀ S, candList x.n u (capK x) S = candList x.n u (2 ^ x.s) S :=
        candList_capK hw u
      obtain ⟨h1, h2, h3⟩ := growL_spec (samples := x.samples) (t := t₂) hu' hk x.n
      simp only [perU, keep, ↓reduceIte, greedyL]
      refine (prune11_eq hu' hk h2 h3).trans ?_
      rw [h1]
      rfl
  · rw [ite_eq_right hw]
    have hwf : wf x = false := by
      rw [← Bool.not_eq_true, wf_iff]
      exact hw
    simp only [hwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, zero_mul,
      Function.iterate_zero, id_eq]
    rfl

end BB20.Machine.Run
