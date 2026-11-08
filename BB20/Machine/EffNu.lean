module

public import BB20.Learning.Algorithm

/-!
# The empirical proxy from the sample patterns

`BB20.empNuL` sums over all `2ⁿ` configurations `z`. Only the configurations that agree with some
sample on `I ∪ S` contribute, and each contributing term depends on `z` only through its values on
`{u} ∪ I ∪ S`. Grouping the configurations by the samples that agree with them on `I ∪ S` gives a
sum over the `M` samples and the two values of `X_u` (`BB20.Machine.Run.effNu`), with each pattern
weighted by one over the number of samples showing it on `I ∪ S`:

`ν̂_{u,I|S} = 2^{n - |I| - |S| - 1} / 2^{n - |S|} · ∑_k ∑_b g(z_{k,b}) / c(z_{k,b})`,

where `z_{k,b}` is sample `k` with `X_u` set to `b`, `g` the summand of `BB20.empNuL` and `c(z)`
the number of samples agreeing with `z` on `I ∪ S` (`BB20.Machine.Run.effNu_eq`). This is the form
the machines compute.
-/

@[expose] public section

namespace BB20.Machine.Run

open Finset

/-- Whether the sample `y` agrees on the variables of `L` with the configuration that is the sample
`x` with variable `u` set to `b`. -/
def agreeAt (u : ℕ) (L : List ℕ) (x : List Bool) (b : Bool) (y : List Bool) : Bool :=
  L.all fun i ↦ y.getD i false == if i = u then b else x.getD i false

/-- The number of samples agreeing on `L` with the sample `x` with variable `u` set to `b`. -/
def cntL (samples : List (List Bool)) (u : ℕ) (L : List ℕ) (x : List Bool) (b : Bool) : ℕ :=
  samples.countP (agreeAt u L x b)

/-- The empirical probability of the pattern on `L` of the sample `x` with `u` set to `b`. -/
def margL (samples : List (List Bool)) (u : ℕ) (L : List ℕ) (x : List Bool) (b : Bool) : ℚ :=
  (cntL samples u L x b : ℚ) / samples.length

/-- The term of the sample `x` and the value `b` of `X_u`: the summand of `BB20.empNuL` at the
sample `x` with `u` set to `b`, divided by the number of samples agreeing with it on `I ∪ S`. -/
def termL (samples : List (List Bool)) (u : ℕ) (I S : List ℕ) (x : List Bool) (b : Bool) : ℚ :=
  |margL samples u (u :: (I ++ S)) x b -
      margL samples u (u :: S) x b * margL samples u (I ++ S) x b / margL samples u S x b| /
    (cntL samples u (I ++ S) x b : ℚ)

/-- The empirical proxy `ν̂_{u,I|S}` as a sum over the samples (`BB20.Machine.Run.effNu_eq`). -/
def effNu (samples : List (List Bool)) (n u : ℕ) (I S : List ℕ) : ℚ :=
  (samples.map fun x ↦ termL samples u I S x true + termL samples u I S x false).sum *
    2 ^ (n - (I.length + S.length + 1)) / 2 ^ (n - S.length)

/-! ### Counting configurations -/

/-- The configurations with prescribed values on a set `T` of variables: `2^{n - |T|}` of them. -/
theorem card_agree {n : ℕ} (T : Finset (Fin n)) (w : Fin n → Bool) :
    (univ.filter fun z : Fin n → Bool ↦ ∀ i ∈ T, z i = w i).card = 2 ^ (n - T.card) := by
  classical
  let e : {z : Fin n → Bool // ∀ i ∈ T, z i = w i} ≃ ({i : Fin n // i ∉ T} → Bool) :=
    { toFun := fun z i ↦ z.1 i.1
      invFun := fun y ↦ ⟨fun i ↦ if h : i ∈ T then w i else y ⟨i, h⟩, fun i hi ↦ by simp [hi]⟩
      left_inv := fun z ↦ by
        ext i
        by_cases h : i ∈ T
        · simp [h, z.2 i h]
        · simp [h]
      right_inv := fun y ↦ by
        ext i
        simp [i.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-! ### Sums over sample indices -/

theorem map_getD_range (l : List (List Bool)) :
    (List.range l.length).map (fun k ↦ l.getD k []) = l := by
  apply List.ext_getElem (by simp)
  intro k h₁ h₂
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

theorem sum_range_eq_list (M : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range M, f k = ((List.range M).map f).sum := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem sum_range_ite (M : ℕ) (p : ℕ → Prop) [DecidablePred p] (a : ℚ) :
    ∑ k ∈ range M, (if p k then a else 0) =
      ((List.range M).countP (fun k ↦ decide (p k)) : ℚ) * a := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, List.range_succ, List.countP_append]
    by_cases h : p M <;> simp [h, add_mul]

/-- Counting the sample indices that agree with `z` on `A` is counting the samples that agree with
it. -/
theorem countP_range_eq (samples : List (List Bool)) {n : ℕ} (A : Finset ℕ)
    (hA : ∀ i ∈ A, i < n) (z : Fin n → Bool) (w : ℕ → Bool)
    (hzw : ∀ i (h : i < n), z ⟨i, h⟩ = w i) :
    (List.range samples.length).countP
        (fun k ↦ decide (∀ i ∈ A, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩)) =
      samples.countP (fun y ↦ decide (∀ i ∈ A, y.getD i false = w i)) := by
  conv_rhs => rw [← map_getD_range samples]
  rw [List.countP_map]
  congr 1
  funext k
  simp only [Function.comp_apply, bitAt]
  refine decide_eq_decide.2 ⟨fun h i hi ↦ ?_, fun h i hi hn ↦ ?_⟩
  · rw [h i hi (hA i hi), hzw]
  · rw [h i hi, hzw]


theorem countP_agreeAt (samples : List (List Bool)) (u : ℕ) (L : List ℕ) (x : List Bool)
    (b : Bool) :
    samples.countP (fun y ↦ decide (∀ i ∈ L.toFinset, y.getD i false =
        if i = u then b else x.getD i false)) = cntL samples u L x b := by
  unfold cntL agreeAt
  congr 1
  funext y
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

/-! ### The identity -/

section Identity

variable (samples : List (List Bool)) (n u : ℕ)

/-- The number of samples agreeing with `z` on `C`, the numerator of `BB20.empMargL`. -/
def cZ (C : Finset ℕ) (z : Fin n → Bool) : ℕ :=
  (List.range samples.length).countP
    fun k ↦ decide (∀ i ∈ C, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩)

theorem empMargL_eq_cZ (C : Finset ℕ) (z : Fin n → Bool) :
    empMargL samples n C z = (cZ samples n C z : ℚ) / samples.length := rfl

/-- The summand of `BB20.empNuL`. -/
def gZ (I S : Finset ℕ) (z : Fin n → Bool) : ℚ :=
  |empMargL samples n (insert u (I ∪ S)) z -
    empMargL samples n (insert u S) z * empMargL samples n (I ∪ S) z / empMargL samples n S z|

/-- The sample `k` with variable `u` set to `b`. -/
def zOf (k : ℕ) (b : Bool) : Fin n → Bool := fun i ↦ if i.val = u then b else bitAt samples k i

variable {samples n}

theorem cZ_congr {C : Finset ℕ} {z z' : Fin n → Bool}
    (h : ∀ i : Fin n, i.val ∈ C → z i = z' i) : cZ samples n C z = cZ samples n C z' := by
  unfold cZ
  congr 1
  funext k
  refine decide_eq_decide.2 ⟨fun hk i hi hn ↦ ?_, fun hk i hi hn ↦ ?_⟩
  · rw [hk i hi hn, h ⟨i, hn⟩ hi]
  · rw [hk i hi hn, h ⟨i, hn⟩ hi]

theorem empMargL_congr {C : Finset ℕ} {z z' : Fin n → Bool}
    (h : ∀ i : Fin n, i.val ∈ C → z i = z' i) :
    empMargL samples n C z = empMargL samples n C z' := by
  rw [empMargL_eq_cZ, empMargL_eq_cZ, cZ_congr h]

theorem cZ_anti {C D : Finset ℕ} (hCD : C ⊆ D) (z : Fin n → Bool) :
    cZ samples n D z ≤ cZ samples n C z := by
  unfold cZ
  apply List.countP_mono_left
  intro k _ hk
  simp only [decide_eq_true_eq] at hk ⊢
  exact fun i hi hn ↦ hk i (hCD hi) hn

theorem gZ_eq_zero {I S : Finset ℕ} {z : Fin n → Bool} (h : cZ samples n (I ∪ S) z = 0) :
    gZ samples n u I S z = 0 := by
  have h' : cZ samples n (insert u (I ∪ S)) z = 0 :=
    Nat.eq_zero_of_le_zero ((cZ_anti (subset_insert _ _) z).trans h.le)
  unfold gZ
  rw [empMargL_eq_cZ, empMargL_eq_cZ samples n (I ∪ S), h, h']
  simp

/-- Each configuration's term, spread over the samples that agree with it on `I ∪ S`. -/
theorem gZ_eq_sum (I S : Finset ℕ) (z : Fin n → Bool) :
    gZ samples n u I S z = ∑ k ∈ range samples.length,
      if (∀ i ∈ I ∪ S, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩) then
        gZ samples n u I S z / cZ samples n (I ∪ S) z else 0 := by
  rw [sum_range_ite]
  change _ = (cZ samples n (I ∪ S) z : ℚ) * _
  by_cases h : cZ samples n (I ∪ S) z = 0
  · rw [gZ_eq_zero u h]
    simp
  · rw [mul_div_cancel₀]
    exact_mod_cast h

/-- The configurations agreeing with sample `k` on `I ∪ S`, grouped by their value at `u`. -/
theorem sum_agree (hu : u < n) {I S : Finset ℕ} (hT : ∀ i ∈ insert u (I ∪ S), i < n)
    (huIS : u ∉ I ∪ S) (k : ℕ) :
    ∑ z : Fin n → Bool, (if (∀ i ∈ I ∪ S, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩) then
        gZ samples n u I S z / cZ samples n (I ∪ S) z else 0) =
      2 ^ (n - (insert u (I ∪ S)).card) * ∑ b : Bool,
        gZ samples n u I S (zOf samples n u k b) /
          cZ samples n (I ∪ S) (zOf samples n u k b) := by
  set T' : Finset (Fin n) := univ.filter fun i ↦ i.val ∈ insert u (I ∪ S) with hT'def
  have hT' : T'.card = (insert u (I ∪ S)).card := by
    rw [← card_map Fin.valEmbedding]
    congr 1
    ext i
    simp only [hT'def, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      exact ⟨⟨i, hT i hi⟩, hi, rfl⟩
  have hiff : ∀ (z : Fin n → Bool) (b : Bool), (∀ i ∈ T', z i = zOf samples n u k b i) ↔
      ((∀ i ∈ I ∪ S, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩) ∧ z ⟨u, hu⟩ = b) := by
    intro z b
    constructor
    · intro hz
      refine ⟨fun i hi hn ↦ ?_, ?_⟩
      · have hne : i ≠ u := by
          rintro rfl
          exact huIS hi
        have hmem : (⟨i, hn⟩ : Fin n) ∈ T' := by
          simp only [hT'def, mem_filter, mem_univ, true_and]
          exact mem_insert_of_mem hi
        rw [hz ⟨i, hn⟩ hmem, zOf, ite_eq_right hne]
      · rw [hz ⟨u, hu⟩ (by simp [hT'def]), zOf, ite_eq_left rfl]
    · rintro ⟨hP, hb⟩ i hi
      simp only [hT'def, mem_filter, mem_univ, true_and, mem_insert] at hi
      unfold zOf
      split_ifs with hiu
      · rw [← hb]
        congr 1
        exact Fin.ext hiu
      · rcases hi with hi | hi
        · exact absurd hi hiu
        · exact (hP i hi i.2).symm
  have hcongr : ∀ (z : Fin n → Bool) (b : Bool), (∀ i ∈ T', z i = zOf samples n u k b i) →
      gZ samples n u I S z / cZ samples n (I ∪ S) z =
        gZ samples n u I S (zOf samples n u k b) /
          cZ samples n (I ∪ S) (zOf samples n u k b) := by
    intro z b hz
    have h' : ∀ A : Finset ℕ, A ⊆ insert u (I ∪ S) →
        ∀ i : Fin n, i.val ∈ A → z i = zOf samples n u k b i :=
      fun A hA i hi ↦ hz i (by simp only [hT'def, mem_filter, mem_univ, true_and]; exact hA hi)
    unfold gZ
    rw [empMargL_congr (h' _ subset_rfl),
      empMargL_congr (h' (insert u S) (insert_subset_insert _ subset_union_right)),
      empMargL_congr (h' (I ∪ S) (subset_insert _ _)),
      empMargL_congr (h' S (subset_union_right.trans (subset_insert _ _))),
      cZ_congr (h' (I ∪ S) (subset_insert _ _))]
  have hsplit : ∀ z : Fin n → Bool,
      (if (∀ i ∈ I ∪ S, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩) then
        gZ samples n u I S z / cZ samples n (I ∪ S) z else 0) =
      ∑ b : Bool, if (∀ i ∈ T', z i = zOf samples n u k b i) then
        gZ samples n u I S (zOf samples n u k b) /
          cZ samples n (I ∪ S) (zOf samples n u k b) else 0 := by
    intro z
    rw [Fintype.sum_bool]
    by_cases hP : ∀ i ∈ I ∪ S, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩
    · rw [ite_eq_left hP]
      cases hzu : z ⟨u, hu⟩
      · have hf := (hiff z false).2 ⟨hP, hzu⟩
        have ht : ¬ ∀ i ∈ T', z i = zOf samples n u k true i := fun h ↦ by
          simp [((hiff z true).1 h).2] at hzu
        rw [ite_eq_right ht, ite_eq_left hf, hcongr z false hf, zero_add]
      · have ht := (hiff z true).2 ⟨hP, hzu⟩
        have hf : ¬ ∀ i ∈ T', z i = zOf samples n u k false i := fun h ↦ by
          simp [((hiff z false).1 h).2] at hzu
        rw [ite_eq_right hf, ite_eq_left ht, hcongr z true ht, add_zero]
    · rw [ite_eq_right hP, ite_eq_right (fun h ↦ hP ((hiff z true).1 h).1),
        ite_eq_right (fun h ↦ hP ((hiff z false).1 h).1), add_zero]
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_agree, hT']
  push_cast
  ring

theorem cZ_zOf (L : List ℕ) (hL : ∀ i ∈ L, i < n) (k : ℕ) (b : Bool) :
    cZ samples n L.toFinset (zOf samples n u k b) = cntL samples u L (samples.getD k []) b := by
  unfold cZ
  rw [countP_range_eq samples L.toFinset (by simpa using hL) _
    (fun i ↦ if i = u then b else (samples.getD k []).getD i false) (fun i h ↦ rfl),
    countP_agreeAt]

theorem empMargL_zOf (L : List ℕ) (hL : ∀ i ∈ L, i < n) (k : ℕ) (b : Bool) :
    empMargL samples n L.toFinset (zOf samples n u k b) =
      margL samples u L (samples.getD k []) b := by
  rw [empMargL_eq_cZ, cZ_zOf u L hL]
  rfl

theorem term_eq {I S : List ℕ} (hu : u < n) (hI : ∀ i ∈ I, i < n) (hS : ∀ i ∈ S, i < n)
    (k : ℕ) (b : Bool) :
    gZ samples n u I.toFinset S.toFinset (zOf samples n u k b) /
        cZ samples n (I.toFinset ∪ S.toFinset) (zOf samples n u k b) =
      termL samples u I S (samples.getD k []) b := by
  have hIS : ∀ i ∈ I ++ S, i < n := by
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact hI i hi
    · exact hS i hi
  have h₁ : insert u (I.toFinset ∪ S.toFinset) = (u :: (I ++ S)).toFinset := by
    simp [List.toFinset_append]
  have h₂ : insert u S.toFinset = (u :: S).toFinset := by simp
  have h₃ : I.toFinset ∪ S.toFinset = (I ++ S).toFinset := by simp [List.toFinset_append]
  unfold gZ termL
  rw [h₁, h₂, h₃, empMargL_zOf u _ (List.forall_mem_cons.2 ⟨hu, hIS⟩),
    empMargL_zOf u _ (List.forall_mem_cons.2 ⟨hu, hS⟩), empMargL_zOf u _ hIS,
    empMargL_zOf u _ hS,
    cZ_zOf u _ hIS]

end Identity

/-- **The empirical proxy from the samples**: for disjoint `{u}`, `I` and `S` of variables
below `n`, `BB20.Machine.Run.effNu` is `BB20.empNuL`. -/
theorem effNu_eq {samples : List (List Bool)} {n u : ℕ} {I S : List ℕ} (hu : u < n)
    (hI : ∀ i ∈ I, i < n) (hS : ∀ i ∈ S, i < n) (huI : u ∉ I) (huS : u ∉ S)
    (hIS : ∀ i ∈ I, i ∉ S) (hIn : I.Nodup) (hSn : S.Nodup) :
    effNu samples n u I S = empNuL samples n u I.toFinset S.toFinset := by
  have hdisj : Disjoint I.toFinset S.toFinset := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact hIS i (List.mem_toFinset.1 hi) (List.mem_toFinset.1 hi')
  have huIS : u ∉ I.toFinset ∪ S.toFinset := by simp [huI, huS]
  have hcard : (insert u (I.toFinset ∪ S.toFinset)).card = I.length + S.length + 1 := by
    rw [card_insert_of_notMem huIS, card_union_of_disjoint hdisj,
      List.toFinset_card_of_nodup hIn, List.toFinset_card_of_nodup hSn]
  have hT : ∀ i ∈ insert u (I.toFinset ∪ S.toFinset), i < n := by
    intro i hi
    simp only [mem_insert, mem_union, List.mem_toFinset] at hi
    rcases hi with rfl | hi | hi
    · exact hu
    · exact hI i hi
    · exact hS i hi
  have hsum : ∑ z : Fin n → Bool, gZ samples n u I.toFinset S.toFinset z =
      2 ^ (n - (I.length + S.length + 1)) *
        (samples.map fun x ↦ termL samples u I S x true + termL samples u I S x false).sum := by
    rw [Finset.sum_congr rfl fun z _ ↦ gZ_eq_sum u _ _ z, Finset.sum_comm,
      Finset.sum_congr rfl fun k _ ↦ sum_agree u hu hT huIS k, ← Finset.mul_sum, hcard,
      sum_range_eq_list]
    congr 1
    have hmap := congrArg
      (List.map fun x ↦ termL samples u I S x true + termL samples u I S x false)
      (map_getD_range samples)
    rw [List.map_map] at hmap
    rw [← hmap]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Fintype.sum_bool, term_eq u hu hI hS]
  change _ = (∑ z, gZ samples n u I.toFinset S.toFinset z) / 2 ^ (n - S.toFinset.card)
  rw [hsum, List.toFinset_card_of_nodup hSn]
  unfold effNu
  ring

end BB20.Machine.Run
