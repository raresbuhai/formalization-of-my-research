module

public import BB20.Machine.EffNu
public import Mathlib.Data.Nat.BitIndices

/-!
# Finding the first candidate above the threshold

The greedy step of the algorithms (`BB20.grow`) adds the first candidate `I`, in the order of
`BB20.candList`, with `ν̂_{u,I|S} > t`. There are up to `(n + 1)^k` candidates, and the machines
must spend `poly(|x|)` steps on each of them, so they cannot store or sort the list of candidates.
Instead, a counter runs through all `(n + 1)^k` words of `k` digits `0, …, n`
(`BB20.Machine.Run.incr`), each word standing for the set of its digits below `n`
(`BB20.Machine.Run.candOf`), and the search keeps the best candidate so far
(`BB20.Machine.Run.upd`).

`BB20.candList` lists the subsets of an increasing list in the order of `List.sublists`, which is
the order of their codes `∑_{i ∈ I} 2^i` (`BB20.Machine.Run.pairwise_code_candList`). So the first
candidate above the threshold is the one with the smallest code, which is what the search keeps
(`BB20.Machine.Run.search_eq`).
-/

@[expose] public section

namespace BB20.Machine.Run

/-! ### The counter -/

/-- The successor of a word of digits `0, …, n` in base `n + 1`, least significant digit first
(digits above `n` count as `n`; the largest word wraps around to zero). -/
def incr (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d < n then (d + 1) :: ds else 0 :: incr n ds

/-- The value of a word of digits in base `n + 1`, least significant digit first. -/
def val (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + (n + 1) * val n ds

theorem length_incr (n : ℕ) (t : List ℕ) : (incr n t).length = t.length := by
  induction t with
  | nil => rfl
  | cons d ds ih =>
    unfold incr
    split_ifs <;> simp [ih]

theorem incr_le (n : ℕ) (t : List ℕ) (ht : ∀ d ∈ t, d ≤ n) : ∀ d ∈ incr n t, d ≤ n := by
  induction t with
  | nil => simp [incr]
  | cons d ds ih =>
    unfold incr
    split_ifs with h
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact ht e (List.mem_cons_of_mem _ he)
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact ih (fun e he ↦ ht e (List.mem_cons_of_mem _ he)) e he

theorem val_lt (n : ℕ) (t : List ℕ) (ht : ∀ d ∈ t, d ≤ n) : val n t < (n + 1) ^ t.length := by
  induction t with
  | nil => simp [val]
  | cons d ds ih =>
    have hd := ht d List.mem_cons_self
    have h := ih fun e he ↦ ht e (List.mem_cons_of_mem _ he)
    simp only [val, List.length_cons, pow_succ]
    nlinarith

theorem val_incr (n : ℕ) (t : List ℕ) (ht : ∀ d ∈ t, d ≤ n)
    (hv : val n t + 1 < (n + 1) ^ t.length) : val n (incr n t) = val n t + 1 := by
  induction t with
  | nil => simp at hv
  | cons d ds ih =>
    have hd := ht d List.mem_cons_self
    unfold incr
    split_ifs with h
    · simp only [val]
      ring
    · have hdn : d = n := by omega
      subst hdn
      simp only [val, List.length_cons, pow_succ] at hv ⊢
      have hv' : val d ds + 1 < (d + 1) ^ ds.length := by nlinarith
      rw [ih (fun e he ↦ ht e (List.mem_cons_of_mem _ he)) hv']
      ring

theorem val_inj (n : ℕ) (t t' : List ℕ) (ht : ∀ d ∈ t, d ≤ n) (ht' : ∀ d ∈ t', d ≤ n)
    (hl : t.length = t'.length) (hv : val n t = val n t') : t = t' := by
  induction t generalizing t' with
  | nil =>
    cases t' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons d ds ih =>
    cases t' with
    | nil => simp at hl
    | cons d' ds' =>
      have hd := ht d List.mem_cons_self
      have hd' := ht' d' List.mem_cons_self
      simp only [val] at hv
      have h1 : d = d' := by
        have := congrArg (· % (n + 1)) hv
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd),
          Nat.mod_eq_of_lt (Nat.lt_succ_of_le hd')] at this
        exact this
      subst h1
      have h2 : val n ds = val n ds' := by
        have := Nat.add_left_cancel hv
        exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) this
      rw [ih ds' (fun e he ↦ ht e (List.mem_cons_of_mem _ he))
        (fun e he ↦ ht' e (List.mem_cons_of_mem _ he)) (by simpa using hl) h2]

/-- The words visited by the counter in `(n + 1)^k` steps from zero. -/
def words (n k : ℕ) : List (List ℕ) :=
  (List.range ((n + 1) ^ k)).map fun j ↦ (incr n)^[j] (List.replicate k 0)

theorem iterate_incr (n k j : ℕ) :
    ((incr n)^[j] (List.replicate k 0)).length = k ∧
      ∀ d ∈ (incr n)^[j] (List.replicate k 0), d ≤ n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨by rw [length_incr, ih.1], incr_le n _ ih.2⟩

theorem val_iterate_incr (n k j : ℕ) (hj : j < (n + 1) ^ k) :
    val n ((incr n)^[j] (List.replicate k 0)) = j := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, val, ih (Nat.one_le_pow _ _ (Nat.succ_pos n))]
  | succ j ih =>
    rw [Function.iterate_succ_apply', val_incr n _ (iterate_incr n k j).2
      (by rw [(iterate_incr n k j).1, ih (by omega)]; exact hj), ih (by omega)]

theorem mem_words {n k : ℕ} {t : List ℕ} (hl : t.length = k) (ht : ∀ d ∈ t, d ≤ n) :
    t ∈ words n k := by
  refine List.mem_map.2 ⟨val n t, List.mem_range.2 (hl ▸ val_lt n t ht), ?_⟩
  have hlt : val n t < (n + 1) ^ k := hl ▸ val_lt n t ht
  exact val_inj n _ t (iterate_incr n k _).2 ht ((iterate_incr n k _).1.trans hl.symm)
    (val_iterate_incr n k _ hlt)

theorem length_of_mem_words {n k : ℕ} {t : List ℕ} (ht : t ∈ words n k) : t.length = k := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
  exact (iterate_incr n k j).1

/-! ### Candidates and their codes -/

/-- The set of digits of the word `t` below `n`, as an increasing list. -/
def candOf (n : ℕ) (t : List ℕ) : List ℕ := (List.range n).filter fun i ↦ decide (i ∈ t)

/-- The code `∑_{i ∈ I} 2^i` of a list of numbers. -/
def code (I : List ℕ) : ℕ := (I.map (2 ^ ·)).sum

/-- A candidate other than `u` and the elements of `S`, and not empty. -/
def okCand (u : ℕ) (S I : List ℕ) : Bool :=
  !I.isEmpty && !decide (u ∈ I) && I.all fun i ↦ !decide (i ∈ S)

theorem code_inj {I J : List ℕ} (hI : I.SortedLT) (hJ : J.SortedLT) (h : code I = code J) :
    I = J := by
  rw [← Nat.bitIndices_sum_map_two_pow hI, ← Nat.bitIndices_sum_map_two_pow hJ]
  exact congrArg Nat.bitIndices h

theorem sortedLT_candOf (n : ℕ) (t : List ℕ) : (candOf n t).SortedLT :=
  ((List.sortedLT_range n).pairwise.sublist List.filter_sublist).sortedLT

theorem mem_candOf {n : ℕ} {t : List ℕ} {i : ℕ} : i ∈ candOf n t ↔ i < n ∧ i ∈ t := by
  simp [candOf]

theorem length_candOf_le (n : ℕ) (t : List ℕ) : (candOf n t).length ≤ t.length := by
  have hnd : (candOf n t).Nodup := (sortedLT_candOf n t).nodup
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card fun i hi ↦ by
    simp only [List.mem_toFinset, mem_candOf] at hi
    exact List.mem_toFinset.2 hi.2).trans (List.toFinset_card_le t)

/-- An increasing list of numbers below `n` is the set of digits of itself padded with `n`. -/
theorem candOf_pad {n : ℕ} {I : List ℕ} (hI : I.SortedLT) (hn : ∀ i ∈ I, i < n) (k : ℕ) :
    candOf n (I ++ List.replicate k n) = I := by
  refine (sortedLT_candOf n _).eq_of_mem_iff hI fun i ↦ ?_
  rw [mem_candOf, List.mem_append, List.mem_replicate]
  constructor
  · rintro ⟨hi, hi' | ⟨-, rfl⟩⟩
    · exact hi'
    · omega
  · intro hi
    exact ⟨hn i hi, Or.inl hi⟩

/-! ### The candidates in the order of `List.sublists` -/

theorem mem_candList {n u k : ℕ} {S : Finset ℕ} {l : List ℕ} :
    l ∈ candList n u k S ↔
      l.SortedLT ∧ l ≠ [] ∧ l.length ≤ k ∧ ∀ i ∈ l, i < n ∧ i ≠ u ∧ i ∉ S := by
  have hL : ((List.range n).filter fun i ↦ decide (i ≠ u ∧ i ∉ S)).SortedLT :=
    ((List.sortedLT_range n).pairwise.sublist List.filter_sublist).sortedLT
  simp only [candList, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hne, hk⟩
    refine ⟨(hL.pairwise.sublist hs).sortedLT, hne, hk, fun i hi ↦ ?_⟩
    have := hs.subset hi
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · rintro ⟨hs, hne, hk, hi⟩
    refine ⟨List.sublist_of_subperm_of_sortedLE (List.subperm_of_subset hs.nodup fun i hii ↦ ?_)
      hs.sortedLE hL.sortedLE, hne, hk⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨(hi i hii).1, (hi i hii).2⟩

theorem two_pow_dvd_code {a : ℕ} {x : List ℕ} (h : ∀ e ∈ x, a < e) : 2 ^ (a + 1) ∣ code x :=
  List.dvd_sum fun y hy ↦ by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    exact pow_dvd_pow 2 (h e he)

/-- The subsets of an increasing list come in the order of their codes. -/
theorem pairwise_code_sublists (L : List ℕ) (hL : L.SortedLT) :
    L.sublists.Pairwise fun a b ↦ code a < code b := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have hl : l.Pairwise (· < ·) := (List.pairwise_cons.1 hL.pairwise).2
    have ha : ∀ e ∈ l, a < e := (List.pairwise_cons.1 hL.pairwise).1
    have ih' := ih hl.sortedLT
    rw [List.sublists_cons]
    change List.Pairwise _ (List.flatMap _ _)
    rw [List.pairwise_flatMap]
    refine ⟨fun x _ ↦ ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      simp only [code, List.map_cons, List.sum_cons]
      have := Nat.two_pow_pos a
      omega
    · refine ih'.imp_of_mem fun {x y} hx hy hxy ↦ ?_
      have hdx := two_pow_dvd_code fun e he ↦ ha e ((List.mem_sublists.1 hx).subset he)
      have hdy := two_pow_dvd_code fun e he ↦ ha e ((List.mem_sublists.1 hy).subset he)
      obtain ⟨p, hp⟩ := hdx
      obtain ⟨q, hq⟩ := hdy
      have hpq : p < q := by
        rw [hp, hq] at hxy
        exact Nat.lt_of_mul_lt_mul_left hxy
      have hgap : code x + 2 ^ (a + 1) ≤ code y := by
        rw [hp, hq]
        nlinarith
      have h2 : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      intro c hc d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp only [code, List.map_cons,
        List.sum_cons] at * <;> omega

theorem pairwise_code_candList (n u k : ℕ) (S : Finset ℕ) :
    (candList n u k S).Pairwise fun a b ↦ code a < code b :=
  (pairwise_code_sublists _
    ((List.sortedLT_range n).pairwise.sublist List.filter_sublist).sortedLT).filter _

/-- In a list ordered by codes, the first element passing a test has the smallest code among
those passing it. -/
theorem code_le_of_find? {l : List (List ℕ)} (hl : l.Pairwise fun a b ↦ code a < code b)
    {q : List ℕ → Bool} {J J' : List ℕ} (hJ : l.find? q = some J) (hJ' : J' ∈ l)
    (hq : q J' = true) : code J ≤ code J' := by
  induction l with
  | nil => simp at hJ'
  | cons a l ih =>
    rw [List.find?_cons] at hJ
    rcases List.mem_cons.1 hJ' with rfl | hJl
    · rw [hq] at hJ
      cases hJ
      exact le_rfl
    · cases hqa : q a
      · rw [hqa] at hJ
        exact ih (List.pairwise_cons.1 hl).2 hJ hJl
      · rw [hqa] at hJ
        have haJ : a = J := Option.some.inj hJ
        subst haJ
        exact ((List.pairwise_cons.1 hl).1 J' hJl).le

theorem candList_min (n u k : ℕ) (S : Finset ℕ) : candList n u k S = candList n u (min k n) S := by
  unfold candList
  refine List.filter_congr fun l hl ↦ ?_
  have hlen : l.length ≤ n :=
    ((List.mem_sublists.1 hl).length_le).trans (List.length_filter_le _ _ |>.trans (by simp))
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_min h2 hlen⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans (min_le_left _ _)⟩

/-! ### The search -/

/-- The candidate `I` is admissible and above the threshold. -/
def nuOK (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (S I : List ℕ) : Bool :=
  okCand u S I && decide (t < effNu samples n u I S)

/-- `I` has a smaller code than the best candidate so far, if there is one. -/
def better (I : List ℕ) (b : Option (List ℕ)) : Bool :=
  b.elim true fun J ↦ decide (code I < code J)

/-- Keep the candidate `I` if it is admissible, above the threshold, and better than `b`. -/
def upd (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (S : List ℕ) (b : Option (List ℕ))
    (I : List ℕ) : Option (List ℕ) :=
  if nuOK samples n u t S I && better I b then some I else b

/-- One round of the search: look at the candidate of the current word, then count. -/
def sstep (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (S : List ℕ)
    (q : List ℕ × Option (List ℕ)) : List ℕ × Option (List ℕ) :=
  (incr n q.1, upd samples n u t S q.2 (candOf n q.1))

/-- **The search**: the candidate with the smallest code among those above the threshold, after
`(n + 1)^k` rounds. -/
def search (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (k : ℕ) (S : List ℕ) :
    Option (List ℕ) :=
  ((sstep samples n u t S)^[(n + 1) ^ k] (List.replicate k 0, none)).2

theorem iterate_sstep (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (k : ℕ) (S : List ℕ)
    (j : ℕ) :
    (sstep samples n u t S)^[j] (List.replicate k 0, none) =
      ((incr n)^[j] (List.replicate k 0), ((List.range j).map fun i ↦
        candOf n ((incr n)^[i] (List.replicate k 0))).foldl (upd samples n u t S) none) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', List.range_succ,
      List.map_append, List.foldl_append]
    rfl

theorem search_eq_foldl (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (k : ℕ) (S : List ℕ) :
    search samples n u t k S =
      ((words n k).map (candOf n)).foldl (upd samples n u t S) none := by
  rw [search, iterate_sstep, words, List.map_map]
  rfl

/-- The best candidate after a fold: `none` if no candidate passes, and otherwise a passing
candidate with the smallest code. -/
theorem foldl_upd (samples : List (List Bool)) (n u : ℕ) (t : ℚ) (S : List ℕ)
    (X : List (List ℕ)) :
    (X.foldl (upd samples n u t S) none = none → ∀ I ∈ X, nuOK samples n u t S I = false) ∧
      ∀ J, X.foldl (upd samples n u t S) none = some J → J ∈ X ∧
        nuOK samples n u t S J = true ∧
          ∀ I ∈ X, nuOK samples n u t S I = true → code J ≤ code I := by
  induction X using List.reverseRecOn with
  | nil => simp
  | append_singleton Y a ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨ih₁, ih₂⟩ := ih
    cases hY : Y.foldl (upd samples n u t S) none with
    | none =>
      have hY' := ih₁ hY
      unfold upd
      cases ha : nuOK samples n u t S a
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, true_implies,
          reduceCtorEq, false_implies, implies_true, and_true]
        intro I hI
        rcases List.mem_append.1 hI with hI | hI
        · exact hY' I hI
        · rw [List.mem_singleton.1 hI]
          exact ha
      · simp only [better, Option.elim_none, Bool.and_self, ↓reduceIte, reduceCtorEq,
          false_implies, Option.some.injEq, true_and]
        rintro J rfl
        refine ⟨List.mem_append_right _ (List.mem_singleton_self a), ha, fun I hI hIok ↦ ?_⟩
        rcases List.mem_append.1 hI with hI | hI
        · simp [hY' I hI] at hIok
        · rw [List.mem_singleton.1 hI]
    | some J₀ =>
      obtain ⟨hJ₀, hJ₀ok, hJ₀min⟩ := ih₂ J₀ hY
      unfold upd
      refine ⟨fun h ↦ ?_, fun J hJ ↦ ?_⟩
      · split_ifs at h
      · split_ifs at hJ with hc
        · cases hJ
          simp only [Bool.and_eq_true, better, Option.elim_some, decide_eq_true_eq] at hc
          refine ⟨List.mem_append_right _ (List.mem_singleton_self a), hc.1, fun I hI hIok ↦ ?_⟩
          rcases List.mem_append.1 hI with hI | hI
          · exact (hc.2.trans_le (hJ₀min I hI hIok)).le
          · rw [List.mem_singleton.1 hI]
        · cases hJ
          refine ⟨List.mem_append_left _ hJ₀, hJ₀ok, fun I hI hIok ↦ ?_⟩
          rcases List.mem_append.1 hI with hI | hI
          · exact hJ₀min I hI hIok
          · rw [List.mem_singleton.1 hI] at hIok ⊢
            simp only [hIok, better, Option.elim_some, Bool.true_and, decide_eq_true_eq,
              not_lt] at hc
            exact hc

theorem okCand_iff {u : ℕ} {S I : List ℕ} :
    okCand u S I = true ↔ I ≠ [] ∧ u ∉ I ∧ ∀ i ∈ I, i ∉ S := by
  simp [okCand, List.all_eq_true, and_assoc]

/-- What the search returns is a candidate. -/
theorem search_some {samples : List (List Bool)} {n u : ℕ} {t : ℚ} {k : ℕ} {S J : List ℕ}
    (h : search samples n u t k S = some J) :
    J.SortedLT ∧ J ≠ [] ∧ J.length ≤ k ∧ ∀ i ∈ J, i < n ∧ i ≠ u ∧ i ∉ S := by
  rw [search_eq_foldl] at h
  obtain ⟨hJ, hok, -⟩ := (foldl_upd samples n u t S _).2 J h
  obtain ⟨tup, htup, rfl⟩ := List.mem_map.1 hJ
  simp only [nuOK, Bool.and_eq_true] at hok
  obtain ⟨hne, hu, hS⟩ := okCand_iff.1 hok.1
  refine ⟨sortedLT_candOf n tup, hne,
    (length_candOf_le n tup).trans (length_of_mem_words htup).le, fun i hi ↦ ?_⟩
  exact ⟨(mem_candOf.1 hi).1, fun h ↦ hu (h ▸ hi), hS i hi⟩

/-- **The search finds the first candidate above the threshold.** -/
theorem search_eq {samples : List (List Bool)} {n u : ℕ} {t : ℚ} {k : ℕ} {S : List ℕ}
    (hu : u < n) (hS : ∀ i ∈ S, i < n) (huS : u ∉ S) (hSn : S.Nodup) :
    search samples n u t k S = (candList n u k S.toFinset).find?
      fun l ↦ decide (t < empNuL samples n u l.toFinset S.toFinset) := by
  set X := (words n k).map (candOf n) with hX
  set q : List ℕ → Bool := fun l ↦ decide (t < empNuL samples n u l.toFinset S.toFinset)
  -- the candidates of `candList` are the admissible candidates of the words
  have hcand : ∀ J ∈ candList n u k S.toFinset, J ∈ X ∧ okCand u S J = true ∧
      effNu samples n u J S = empNuL samples n u J.toFinset S.toFinset := by
    intro J hJ
    obtain ⟨hs, hne, hk, hi⟩ := mem_candList.1 hJ
    refine ⟨List.mem_map.2 ⟨J ++ List.replicate (k - J.length) n, mem_words (by simp; omega)
      fun d hd ↦ ?_, candOf_pad hs (fun i hi' ↦ (hi i hi').1) _⟩, okCand_iff.2 ⟨hne,
        fun h ↦ (hi u h).2.1 rfl, fun i hi' ↦ by simpa using (hi i hi').2.2⟩, ?_⟩
    · rcases List.mem_append.1 hd with hd | hd
      · exact (hi d hd).1.le
      · exact (List.mem_replicate.1 hd).2.le
    · exact effNu_eq hu (fun i hi' ↦ (hi i hi').1) hS (fun h ↦ (hi u h).2.1 rfl) huS
        (fun i hi' ↦ by simpa using (hi i hi').2.2) hs.nodup hSn
  have hback : ∀ J ∈ X, okCand u S J = true → J ∈ candList n u k S.toFinset := by
    intro J hJ hok
    obtain ⟨tup, htup, rfl⟩ := List.mem_map.1 hJ
    obtain ⟨hne, hu', hS'⟩ := okCand_iff.1 hok
    refine mem_candList.2 ⟨sortedLT_candOf n tup, hne,
      (length_candOf_le n tup).trans (length_of_mem_words htup).le, fun i hi ↦ ?_⟩
    exact ⟨(mem_candOf.1 hi).1, fun h ↦ hu' (h ▸ hi), by simpa using hS' i hi⟩
  have hnu : ∀ J ∈ candList n u k S.toFinset, nuOK samples n u t S J = q J := by
    intro J hJ
    obtain ⟨-, hok, he⟩ := hcand J hJ
    simp [nuOK, hok, he, q]
  rw [search_eq_foldl, ← hX]
  obtain ⟨hnone, hsome⟩ := foldl_upd samples n u t S X
  cases hf : (candList n u k S.toFinset).find? q with
  | none =>
    rw [List.find?_eq_none] at hf
    cases hr : X.foldl (upd samples n u t S) none with
    | none => rfl
    | some J =>
      obtain ⟨hJ, hok, -⟩ := hsome J hr
      have hc := hback J hJ (by simp only [nuOK, Bool.and_eq_true] at hok; exact hok.1)
      exact absurd ((hnu J hc).symm.trans hok) (hf J hc)
  | some J =>
    have hJc := List.mem_of_find?_eq_some hf
    have hqJ := List.find?_some hf
    obtain ⟨hJX, -, -⟩ := hcand J hJc
    cases hr : X.foldl (upd samples n u t S) none with
    | none =>
      exact absurd ((hnu J hJc).trans hqJ) (by rw [hnone hr J hJX]; simp)
    | some J' =>
      obtain ⟨hJ'X, hok', hmin⟩ := hsome J' hr
      have hJ'c := hback J' hJ'X (by simp only [nuOK, Bool.and_eq_true] at hok'; exact hok'.1)
      have h1 := hmin J hJX ((hnu J hJc).trans hqJ)
      have h2 := code_le_of_find? (pairwise_code_candList n u k _) hf hJ'c
        ((hnu J' hJ'c).symm.trans hok')
      have hs := (mem_candList.1 hJc).1
      have hs' := (mem_candList.1 hJ'c).1
      rw [code_inj hs' hs (le_antisymm h1 h2)]

end BB20.Machine.Run
