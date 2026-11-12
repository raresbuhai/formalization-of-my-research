module

public import BDT24.Alg.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Foundations.Data.List.Fold

/-!
# The running time of the algorithm

`BDT24.Alg.algB_runsInTime`: for a regression algorithm within `slrTime e`, the PCA algorithm
`BDT24.Alg.algB A e` runs in time `spcaTime e'` for some `e'`, that is
`O((⌊√⌈1/δ⌉⌋ + 1) (|x| + 2)^(e') + |(x, r)|)`, and its coins suffice for all its rounds:
`rounds δ n · lenBlk ≤ spcaTime e'`.

The machine computes the initial state from the input, copying the coins, in time polynomial in
`|x|` plus linear in `|r|`, and then folds the coins into the state with complexitylib's streaming
fold (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum`), whose time
is the sum of the costs of the steps. While a round is running the state has length polynomial
in `|x|`, and so has the cost of a step; there are at most `rounds δ n · lenBlk` such steps, with
`rounds δ n ≤ ⌊√⌈1/δ⌉⌋` and `lenBlk` polynomial in `|x|`. Once the last round is done the state
is `doneSt a`, of constant length, and every further coin costs a constant.
-/

@[expose] public section

namespace BDT24.Alg

open Turing.MultiTapeTM

namespace RT

open Finset

/-! ### Polynomial-time certificates -/

/-- A polynomial-time map is tidily computable within `O(c (|a| + 1)^d)`. -/
theorem exists_inO_pow {β γ : Type} {f : β → γ} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} (h : ComputableInPolyTime f encB encC) :
    ∃ c d : ℕ, ComputableTidilyInO f encB encC (fun b ↦ c * ((encB b).length + 1) ^ d)
      (fun b ↦ c * ((encB b).length + 1) ^ d) := by
  obtain ⟨T, S, hT, hS, hO⟩ := h.exists_computableInO
  obtain ⟨cT, dT, hT'⟩ := hT.exists_le
  obtain ⟨cS, dS, hS'⟩ := hS.exists_le
  refine ⟨cT + cS, dT + dS, hO.tidy.mono_le (fun a ↦ (hT' a).trans ?_)
    (fun a ↦ (hS' a).trans ?_)⟩
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- A polynomial-time map is tidily computable within `C (|a| + 1)^d` steps and cells. -/
theorem exists_tidy_pow {β γ : Type} {f : β → γ} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} (h : ComputableInPolyTime f encB encC) :
    ∃ C d : ℕ, ComputableTidilyInTimeAndSpace f encB encC
      (fun b ↦ C * ((encB b).length + 1) ^ d) (fun b ↦ C * ((encB b).length + 1) ^ d) := by
  obtain ⟨c, d, k, hk, -⟩ := exists_inO_pow h
  refine ⟨k * c + k, d, hk.mono (fun b ↦ ?_) (fun b ↦ ?_)⟩ <;>
  · have h1 : 1 ≤ ((encB b).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h2 := Nat.mul_le_mul_left k h1
    nlinarith

/-! ### Lengths of encodings -/

/-- The length of an encoded pair. -/
theorem len_pair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (p : α × β) :
    (Encoding.encPair a b p).length = 2 * (a p.1).length + 1 + (b p.2).length :=
  length_encPair (enc₁ := a) (enc₂ := b) p

/-- The length of an encoded nonempty list. -/
theorem len_list_cons {α : Type} (enc : α ↪ List Bool) (a : α) (l : List α) :
    (Encoding.encList enc (a :: l)).length =
      2 * (enc a).length + 1 + (Encoding.encList enc l).length := by
  change (Encoding.frame (enc a) ++ Encoding.encList enc l).length = _
  rw [List.length_append]
  exact congrArg (· + _) (length_frame (enc a))

/-- A list is no longer than its encoding. -/
theorem length_le_list {α : Type} (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (Encoding.encList enc l).length := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => rw [len_list_cons, List.length_cons]; omega

/-- The length of a number in unary. -/
theorem len_unary (n : ℕ) : (Encoding.encUnary n).length = n := List.length_replicate

/-- The length of a number in binary. -/
theorem len_nat (n : ℕ) : (Encoding.encNat n).length = n.size := Nat.size_eq_bits_len n

/-- The length of an input of the PCA algorithm. -/
theorem len_spca (x : SPCAInput) : (encSPCAInput x).length =
    2 * (Encoding.encRat x.δ).length + 1 + (2 * x.p + 1 + (2 * (Encoding.encNat x.k).length + 1 +
      (2 * x.q + 1 + (Encoding.encList (Encoding.encList Encoding.encInt) x.points).length))) := by
  change (Encoding.encPair _ _ (x.δ, x.p, x.k, x.q, x.points)).length = _
  simp only [len_pair, len_unary]

/-- The number of coordinates is at most the length of the encoded points. -/
theorem mOf_le (u : Pts) :
    mOf u ≤ (Encoding.encList (Encoding.encList Encoding.encInt) u).length := by
  cases u with
  | nil => exact Nat.zero_le _
  | cons a l =>
    have := length_le_list Encoding.encInt a
    change a.length ≤ _
    rw [len_list_cons]
    omega

/-- The parameters of the input are at most its length. -/
theorem params_le (x : SPCAInput) :
    x.p ≤ (encSPCAInput x).length ∧ x.q ≤ (encSPCAInput x).length ∧
      (Encoding.encNat x.k).length ≤ (encSPCAInput x).length ∧
      nOf x.points ≤ (encSPCAInput x).length ∧ mOf x.points ≤ (encSPCAInput x).length := by
  have h := len_spca x
  have hn := length_le_list (Encoding.encList Encoding.encInt) x.points
  have hm := mOf_le x.points
  unfold nOf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The length of a state. -/
theorem len_st (s : St) : (encSt s).length =
    2 * (encSPCAInput s.x).length + 1 + (2 * s.j.size + 1 + (2 * s.M.size + 1 +
      (2 * s.buf.length + 1 + 1))) := by
  change (Encoding.encPair _ _ (s.x, s.j, s.M, s.buf, s.acc)).length = _
  simp only [len_pair, len_nat]
  rfl

/-! ### Rounds -/

/-- At most `2^n` rounds. -/
theorem rounds_le_two_pow (δ : ℚ) (n : ℕ) : rounds δ n ≤ 2 ^ n :=
  (min_le_right _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _))

/-- At most `⌊√⌈1/δ⌉⌋` rounds. -/
theorem rounds_le_sqrt (δ : ℚ) (n : ℕ) : rounds δ n ≤ Nat.sqrt ⌈1 / δ⌉₊ := by
  refine (min_le_left _ _).trans (Nat.sqrt_le_sqrt ?_)
  rcases le_or_gt δ 0 with hδ | hδ
  · rw [Nat.floor_of_nonpos (by rw [one_div]; exact inv_nonpos.2 (by linarith))]
    exact Nat.zero_le _
  · exact (Nat.floor_le_ceil _).trans (Nat.ceil_mono (one_div_le_one_div_of_le hδ (by linarith)))

/-- A block has at least one coin. -/
theorem lenBlk_pos (e : ℕ) (x : SPCAInput) : 0 < lenBlk e x := by
  unfold lenBlk lenA
  positivity

/-! ### The states of the fold -/

/-- The states reached from the initial state after `i` coins: a running round, after `i` coins
of its blocks, or the final state. -/
def Good (e : ℕ) (x : SPCAInput) (i : ℕ) (s : St) : Prop :=
  (s.x = x ∧ s.M = rounds x.δ (nOf x.points) ∧ s.j < s.M ∧ s.buf.length < lenBlk e x ∧
    s.j * lenBlk e x + s.buf.length = i) ∨ ∃ a, s = doneSt a

/-- The final state stays. -/
theorem stepSt_doneSt (A : SLRInput × List Bool → Estimate) (e : ℕ) (a b : Bool) :
    stepSt A e (doneSt a) b = doneSt a := by
  simp [stepSt, doneSt]

/-- The initial state is good. -/
theorem good_init (e : ℕ) (x : SPCAInput) : Good e x 0 (initSt x) := by
  unfold initSt
  split_ifs with h
  · exact Or.inl ⟨rfl, rfl, h, lenBlk_pos e x, by simp⟩
  · exact Or.inr ⟨true, rfl⟩

/-- A step keeps the states good. -/
theorem good_step (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput) {i : ℕ}
    {s : St} (b : Bool) (h : Good e x i s) : Good e x (i + 1) (stepSt A e s b) := by
  rcases h with ⟨hx, hM, hj, hb, hi⟩ | ⟨a, rfl⟩
  · obtain ⟨sx, sj, sM, sbuf, sacc⟩ := s
    dsimp only at hx hM hj hb hi
    subst hx
    unfold stepSt
    simp only [hj, ↓reduceIte]
    split_ifs with h1 h2
    · refine Or.inl ⟨rfl, hM, hj, by simpa using h1, ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega
    · refine Or.inl ⟨rfl, hM, h2, by simp; omega, ?_⟩
      simp only [List.length_nil, Nat.add_zero, Nat.succ_mul]
      omega
    · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨a, stepSt_doneSt A e a b⟩

/-- The state after the first `i` coins. -/
def stI (A : SLRInput × List Bool → Estimate) (e : ℕ) (p : St × List Bool) (i : ℕ) : St :=
  (p.2.take i).foldl (stepSt A e) p.1

/-- The state after `i + 1` coins. -/
theorem stI_succ (A : SLRInput × List Bool → Estimate) (e : ℕ) (p : St × List Bool) (i : ℕ)
    (hi : i < p.2.length) : stI A e p (i + 1) = stepSt A e (stI A e p i) p.2[i] := by
  simp only [stI, List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The states reached from the initial state are good. -/
theorem good_stI (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    (r : List Bool) (i : ℕ) (hi : i ≤ r.length) : Good e x i (stI A e (initSt x, r) i) :=
  List.foldl_take_invariant r (stepSt A e) (initSt x) (Good e x) (good_init e x)
    (fun _ _ _ hs ↦ good_step A e x _ hs) i hi

/-- A bound on the length of the running states. -/
def sRun (e : ℕ) (x : SPCAInput) : ℕ := 6 * (encSPCAInput x).length + 2 * lenBlk e x + 8

/-- A bound on the length of the final states. -/
def lDone : ℕ := (encSt (doneSt true)).length + (encSt (doneSt false)).length

/-- The length of a running state. -/
theorem len_running {e : ℕ} {x : SPCAInput} {s : St} (hx : s.x = x)
    (hM : s.M = rounds x.δ (nOf x.points)) (hj : s.j < s.M) (hb : s.buf.length < lenBlk e x) :
    (encSt s).length ≤ sRun e x := by
  have hn := (params_le x).2.2.2.1
  have hM2 := rounds_le_two_pow x.δ (nOf x.points)
  have h1 : s.j.size ≤ nOf x.points := Nat.size_le.2 (by omega)
  have h2 : s.M.size ≤ nOf x.points + 1 := Nat.size_le.2 (by rw [pow_succ]; omega)
  rw [len_st, hx]
  unfold sRun
  omega

/-- The length of a final state. -/
theorem len_done (a : Bool) : (encSt (doneSt a)).length ≤ lDone := by
  unfold lDone
  cases a <;> omega

/-- The length of a good state. -/
theorem len_good {e : ℕ} {x : SPCAInput} {i : ℕ} {s : St} (h : Good e x i s) :
    (encSt s).length ≤ sRun e x + lDone := by
  rcases h with ⟨hx, hM, hj, hb, -⟩ | ⟨a, rfl⟩
  · have := len_running hx hM hj hb
    omega
  · have := len_done a
    omega

/-- A running good state comes before the last coin of the last round. -/
theorem lt_of_good {e : ℕ} {x : SPCAInput} {i : ℕ} {s : St}
    (hM : s.M = rounds x.δ (nOf x.points)) (hj : s.j < s.M) (hb : s.buf.length < lenBlk e x)
    (hi : s.j * lenBlk e x + s.buf.length = i) :
    i < rounds x.δ (nOf x.points) * lenBlk e x := by
  have h := Nat.mul_le_mul_right (lenBlk e x) (show s.j + 1 ≤ rounds x.δ (nOf x.points) by omega)
  rw [Nat.succ_mul] at h
  omega

/-! ### The fold over the coins -/

/-- The cost of step `i` of the fold: its time, and the lengths of the states before and after. -/
def costR (A : SLRInput × List Bool → Estimate) (e C d : ℕ) (p : St × List Bool) (i : ℕ) : ℕ :=
  C * ((encPair encSt encBool (stI A e p i, p.2.getD i false)).length + 1) ^ d +
    (encSt (stI A e p i)).length + (encSt (stI A e p (i + 1))).length + 1

/-- The longest state of the fold. -/
def maxB (A : SLRInput × List Bool → Estimate) (e : ℕ) (p : St × List Bool) : ℕ :=
  (range (p.2.length + 1)).sup fun i ↦ (encSt (stI A e p i)).length

/-- A bound on the space of the steps of the fold. -/
def spQ (A : SLRInput × List Bool → Estimate) (e C d : ℕ) (p : St × List Bool) : ℕ :=
  C * (2 * maxB A e p + 3) ^ d

/-- The states of the fold are no longer than the longest. -/
theorem len_le_maxB (A : SLRInput × List Bool → Estimate) (e : ℕ) (p : St × List Bool) (i : ℕ)
    (hi : i ≤ p.2.length) : (encSt (stI A e p i)).length ≤ maxB A e p :=
  le_sup (f := fun i ↦ (encSt (stI A e p i)).length) (mem_range.2 (Nat.lt_succ_of_le hi))

/-- The cost of a step, in the lengths of the states. -/
theorem costR_eq (A : SLRInput × List Bool → Estimate) (e C d : ℕ) (p : St × List Bool)
    (i : ℕ) : costR A e C d p i =
      C * (2 * (encSt (stI A e p i)).length + 3) ^ d + (encSt (stI A e p i)).length +
        (encSt (stI A e p (i + 1))).length + 1 := by
  simp only [costR, length_encPair, encBool_apply, List.length_singleton]

/-- **The fold over the coins**, within the sum of the costs of its steps. -/
theorem fold_inO {A : SLRInput × List Bool → Estimate} {e C d : ℕ}
    (hT : ComputableTidilyInTimeAndSpace (fun s : St × Bool ↦ stepSt A e s.1 s.2)
      (encPair encSt encBool) encSt (fun b ↦ C * ((encPair encSt encBool b).length + 1) ^ d)
      (fun b ↦ C * ((encPair encSt encBool b).length + 1) ^ d)) :
    ComputableTidilyInO (fun p : St × List Bool ↦ p.2.foldl (stepSt A e) p.1)
      (encPair encSt encBits) encSt
      (fun p ↦ (∑ i ∈ range p.2.length, costR A e C d p i) + maxB A e p)
      (fun p ↦ spQ A e C d p + maxB A e p) := by
  obtain ⟨cF, hF⟩ := ComputableTidilyInTimeAndSpace.foldl_bits_pair_stream_sum
    (step := stepSt A e) hT (R := costR A e C d) (Q := spQ A e C d) (B := maxB A e)
    (fun p i hi ↦ by
      simp only [costR, stI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some]
      exact le_rfl)
    (fun p i hi ↦ by
      have h := len_le_maxB A e p i hi.le
      simp only [stI] at h
      simp only [spQ, length_encPair, encBool_apply, List.length_singleton]
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d))
    (fun p i hi ↦ len_le_maxB A e p i hi)
  refine ComputableTidilyInO.of_bounds hF (cF + 1) (fun p ↦ ?_) (fun p ↦ ?_) (fun p ↦ ?_)
  · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · have h := len_le_maxB A e p p.2.length le_rfl
    simp only [stI, List.take_length] at h
    exact h.trans (le_trans (by omega) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))

/-- The answer of a state, read off its encoding. -/
theorem acc_inO : ComputableTidilyInO St.acc encSt encBool (fun s ↦ (encSt s).length)
    (fun s ↦ (encSt s).length) :=
  (ComputableTidilyInO.snd' (ComputableTidilyInO.snd' (ComputableTidilyInO.snd'
    (ComputableTidilyInO.snd encSPCAInput
      (encPair encNat (encPair encNat (encPair encBits encBool))))))).of_encIn_eq
    (fun s : St ↦ (s.x, s.j, s.M, s.buf, s.acc)) (fun _ ↦ rfl)

/-- The initial state, with the coins. -/
theorem pre_inO {c₁ d₁ : ℕ} (h : ComputableTidilyInO initSt encSPCAInput encSt
      (fun x ↦ c₁ * ((encSPCAInput x).length + 1) ^ d₁)
      (fun x ↦ c₁ * ((encSPCAInput x).length + 1) ^ d₁)) :
    ComputableTidilyInO (fun a : SPCAInput × List Bool ↦ (initSt a.1, a.2))
      (encPair encSPCAInput encBits) (encPair encSt encBits)
      (fun a ↦ (encPair encSPCAInput encBits a).length +
        c₁ * ((encSPCAInput a.1).length + 1) ^ d₁ + (encPair encSPCAInput encBits a).length)
      (fun a ↦ (encPair encSPCAInput encBits a).length +
        c₁ * ((encSPCAInput a.1).length + 1) ^ d₁ + (encPair encSPCAInput encBits a).length) :=
  (h.comp (ComputableTidilyInO.fst encSPCAInput encBits)).prod
    (ComputableTidilyInO.snd encSPCAInput encBits)

/-! ### The costs of the steps -/

/-- The cost of a step of a final state. -/
def rDone (C d : ℕ) : ℕ := C * (2 * lDone + 3) ^ d + 2 * lDone + 1

/-- The cost of a step of a running state. -/
def rRun (e C d : ℕ) (x : SPCAInput) : ℕ :=
  C * (2 * (sRun e x + lDone) + 3) ^ d + 2 * (sRun e x + lDone) + 1

/-- The cost of a step: a constant, and the cost of a running step for the first
`rounds · lenBlk` coins. -/
theorem cost_le (A : SLRInput × List Bool → Estimate) (e C d : ℕ) (x : SPCAInput)
    (r : List Bool) (i : ℕ) (hi : i < r.length) :
    costR A e C d (initSt x, r) i ≤ rDone C d +
      if i < rounds x.δ (nOf x.points) * lenBlk e x then rRun e C d x else 0 := by
  have hg := good_stI A e x r i hi.le
  have hg' := len_good (good_stI A e x r (i + 1) hi)
  rw [costR_eq]
  rcases hg with ⟨hx, hM, hj, hb, hidx⟩ | ⟨a, ha⟩
  · have hlt := lt_of_good hM hj hb hidx
    simp only [hlt, ↓reduceIte]
    have h1 := len_running hx hM hj hb
    have h3 : C * (2 * (encSt (stI A e (initSt x, r) i)).length + 3) ^ d ≤
        C * (2 * (sRun e x + lDone) + 3) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)
    unfold rRun
    omega
  · refine le_add_right ?_
    have hs : stI A e (initSt x, r) (i + 1) = doneSt a := by
      rw [stI_succ A e _ i hi, ha]
      exact stepSt_doneSt A e a _
    rw [hs, ha]
    have h1 := len_done a
    have h3 : C * (2 * (encSt (doneSt a)).length + 3) ^ d ≤ C * (2 * lDone + 3) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)
    unfold rDone
    omega

/-- At most `K` of the first `n` indices are below `K`. -/
theorem sum_ite_le (n K R : ℕ) : ∑ i ∈ range n, (if i < K then R else 0) ≤ K * R := by
  rw [← sum_filter]
  calc ∑ _i ∈ (range n).filter (· < K), R ≤ ∑ _i ∈ range K, R :=
        sum_le_sum_of_subset (fun i hi ↦ by simp only [mem_filter, mem_range] at hi ⊢; omega)
    _ = K * R := by simp

/-- **The time of the fold**: a constant per coin, and a running step for the first
`rounds · lenBlk` coins. -/
theorem sum_cost_le (A : SLRInput × List Bool → Estimate) (e C d : ℕ) (x : SPCAInput)
    (r : List Bool) :
    ∑ i ∈ range r.length, costR A e C d (initSt x, r) i ≤
      r.length * rDone C d + rounds x.δ (nOf x.points) * lenBlk e x * rRun e C d x := by
  calc _ ≤ ∑ i ∈ range r.length, (rDone C d +
        if i < rounds x.δ (nOf x.points) * lenBlk e x then rRun e C d x else 0) :=
        sum_le_sum fun i hi ↦ cost_le A e C d x r i (mem_range.1 hi)
    _ = r.length * rDone C d + ∑ i ∈ range r.length,
        (if i < rounds x.δ (nOf x.points) * lenBlk e x then rRun e C d x else 0) := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_left (sum_ite_le _ _ _) _

/-- The states of the fold are no longer than the running states and the final states. -/
theorem maxB_le (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    (r : List Bool) : maxB A e (initSt x, r) ≤ sRun e x + lDone :=
  Finset.sup_le fun i hi ↦ len_good (good_stI A e x r i (Nat.lt_succ_iff.1 (mem_range.1 hi)))

/-! ### Polynomial bounds -/

/-- The exponent of the length of a block. -/
def dL (e : ℕ) : ℕ := 16 * e + 9

/-- **A block has polynomially many coins**: `lenBlk ≤ (|x| + 2)^(16 e + 9)`. -/
theorem lenBlk_le (e : ℕ) (x : SPCAInput) :
    lenBlk e x ≤ ((encSPCAInput x).length + 2) ^ dL e := by
  obtain ⟨hp, hq, hk, hn, hm⟩ := params_le x
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (encSPCAInput x).length + 2 := ⟨_, rfl⟩
  rw [← hY]
  have hY2 : 2 ≤ Y := by omega
  have hp' : x.p ≤ Y := by omega
  have hq' : x.q ≤ Y := by omega
  have hk' : (Encoding.encNat x.k).length ≤ Y := by omega
  have hn' : nOf x.points ≤ Y := by omega
  have hm' : mOf x.points ≤ Y := by omega
  have hYY : 2 * Y ≤ Y * Y := Nat.mul_le_mul_right Y hY2
  have hYYY : 2 * (Y * Y) ≤ Y * Y * Y := by
    have := Nat.mul_le_mul_left (Y * Y) hY2
    linarith
  have hA1 : (Y + Y + 1 + 1) ^ 2 + Y + Y + Y + 20 ≤ 16 * Y ^ 2 := by nlinarith
  have hB1 : 128 * (Y + 1) * (Y + 1) * (Y + Y + Y + 10) + 4 * (Y : ℕ) + 64 + 2 ≤
      2 ^ 13 * Y ^ 3 := by nlinarith
  have hpow : (2 ^ 13 * Y ^ 3) ^ e ≤ Y ^ (16 * e) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    calc 2 ^ (13 * e) * Y ^ (3 * e) ≤ Y ^ (13 * e) * Y ^ (3 * e) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hY2 _)
      _ = Y ^ (16 * e) := by rw [← pow_add]; ring_nf
  have h4 : Y ^ 4 ≤ Y ^ (16 * e + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : Y ^ (16 * e) ≤ Y ^ (16 * e + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have h32 : 2 ^ 5 ≤ Y ^ 5 := Nat.pow_le_pow_left hY2 5
  unfold lenBlk lenC lenA linB cbits rad
  calc _ ≤ Y * Y * ((Y + Y + 1 + 1) ^ 2 + Y + Y + Y + 20) +
        2 * (128 * (Y + 1) * (Y + 1) * (Y + Y + Y + 10) + 4 * Y + 64 + 2) ^ e := by gcongr
    _ ≤ Y * Y * (16 * Y ^ 2) + 2 * (2 ^ 13 * Y ^ 3) ^ e := by gcongr
    _ ≤ 2 ^ 5 * Y ^ (16 * e + 4) := by
        have : Y * Y * (16 * Y ^ 2) = 16 * Y ^ 4 := by ring
        rw [this]
        omega
    _ ≤ Y ^ 5 * Y ^ (16 * e + 4) := Nat.mul_le_mul_right _ h32
    _ = Y ^ dL e := by rw [← pow_add]; unfold dL; ring_nf

/-- The states are polynomially long: `sRun + lDone ≤ (8 + lDone) (|x| + 2)^(16 e + 9)`. -/
theorem sRun_le (e : ℕ) (x : SPCAInput) :
    sRun e x + lDone ≤ (8 + lDone) * ((encSPCAInput x).length + 2) ^ dL e := by
  have h := lenBlk_le e x
  have h1 : (encSPCAInput x).length + 2 ≤ ((encSPCAInput x).length + 2) ^ dL e :=
    Nat.le_self_pow (by unfold dL; omega) _
  have h2 : 1 ≤ ((encSPCAInput x).length + 2) ^ dL e := Nat.one_le_pow _ _ (by omega)
  have h3 := Nat.mul_le_mul_left lDone h2
  unfold sRun
  rw [Nat.add_mul]
  omega

/-- `C (2B + 3)^d + 2B + 1 ≤ CR · Y^(D (d + 1))` when `B ≤ CB · Y^D`. -/
theorem rrun_le {B CB Y D C d : ℕ} (hY : 1 ≤ Y) (hB : B ≤ CB * Y ^ D) :
    C * (2 * B + 3) ^ d + 2 * B + 1 ≤
      (C * (2 * CB + 3) ^ d + 2 * CB + 1) * Y ^ (D * (d + 1)) := by
  have hP : 1 ≤ Y ^ D := Nat.one_le_pow _ _ hY
  have h1 : 2 * B + 3 ≤ (2 * CB + 3) * Y ^ D := by nlinarith
  have h2 : (2 * B + 3) ^ d ≤ (2 * CB + 3) ^ d * Y ^ (D * d) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left h1 d
  have h3 : Y ^ (D * d) ≤ Y ^ (D * (d + 1)) :=
    Nat.pow_le_pow_right hY (Nat.mul_le_mul_left D (Nat.le_succ d))
  have h4 : Y ^ D ≤ Y ^ (D * (d + 1)) :=
    Nat.pow_le_pow_right hY (Nat.le_mul_of_pos_right _ (Nat.succ_pos d))
  have h5 : 2 * B + 1 ≤ (2 * CB + 1) * Y ^ D := by nlinarith
  have h6 := Nat.mul_le_mul_left C (h2.trans (Nat.mul_le_mul_left _ h3))
  have h7 := h5.trans (Nat.mul_le_mul_left (2 * CB + 1) h4)
  calc C * (2 * B + 3) ^ d + 2 * B + 1
      ≤ C * ((2 * CB + 3) ^ d * Y ^ (D * (d + 1))) + (2 * CB + 1) * Y ^ (D * (d + 1)) := by
        omega
    _ = _ := by ring

/-! ### The arithmetic of the bound -/

/-- The terms of the time bound: with `W = (X + 2)^(d₁ + D + D (d + 1))`, the preprocessing,
`R` coins at constant cost, `M L ≤ s (X + 2)^D` running steps and the states are
`O((s + 1) W + N)`. -/
theorem time_arith {N X R M s L B CB c₁ d₁ D d Rd Rr CR W K : ℕ} (hN : 2 * X + 1 + R = N)
    (hM : M ≤ s) (hL : L ≤ (X + 2) ^ D) (hB : B ≤ CB * (X + 2) ^ D)
    (hRr : Rr ≤ CR * (X + 2) ^ (D * (d + 1))) (hW : (X + 2) ^ (d₁ + D + D * (d + 1)) = W)
    (hK : 2 + Rd + c₁ + CR + CB = K) :
    N + c₁ * (X + 1) ^ d₁ + N + (R * Rd + M * L * Rr + B) ≤ K * ((s + 1) * W + N + 1) := by
  have hY : 1 ≤ X + 2 := by omega
  have hA : (X + 1) ^ d₁ ≤ W :=
    hW ▸ (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hY (by omega))
  have hDW : (X + 2) ^ D ≤ W := hW ▸ Nat.pow_le_pow_right hY (by omega)
  have hMLR : M * L * Rr ≤ CR * (s * W) :=
    calc M * L * Rr ≤ s * (X + 2) ^ D * (CR * (X + 2) ^ (D * (d + 1))) :=
          Nat.mul_le_mul (Nat.mul_le_mul hM hL) hRr
      _ = CR * (s * (X + 2) ^ (D + D * (d + 1))) := by rw [pow_add]; ring
      _ ≤ CR * (s * W) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hW ▸ Nat.pow_le_pow_right hY (by omega)))
  have h1 := Nat.mul_le_mul_left c₁ hA
  have h2 : R * Rd ≤ N * Rd := Nat.mul_le_mul_right _ (by omega)
  have h3 := hB.trans (Nat.mul_le_mul_left CB hDW)
  calc N + c₁ * (X + 1) ^ d₁ + N + (R * Rd + M * L * Rr + B)
      ≤ N * (2 + Rd) + (c₁ + CB) * W + CR * (s * W) := by
        rw [Nat.mul_add, Nat.add_mul]
        omega
    _ ≤ N * K + K * W + K * (s * W) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))) (Nat.mul_le_mul_right _ (by omega))
    _ ≤ K * (s * W) + K * W + K * N + K := by rw [Nat.mul_comm N K]; omega
    _ = K * ((s + 1) * W + N + 1) := by ring

/-- The terms of the space bound: the preprocessing, the space of a step and the states. -/
theorem space_arith {N X s B CB c₁ d₁ D d Rd Rr CR W K Q mB : ℕ} (hmB : mB ≤ B) (hQ : Q ≤ Rr)
    (hB : B ≤ CB * (X + 2) ^ D)
    (hRr : Rr ≤ CR * (X + 2) ^ (D * (d + 1))) (hW : (X + 2) ^ (d₁ + D + D * (d + 1)) = W)
    (hK : 2 + Rd + c₁ + CR + CB = K) :
    N + c₁ * (X + 1) ^ d₁ + N + (Q + mB) ≤ K * ((s + 1) * W + N + 1) := by
  have hY : 1 ≤ X + 2 := by omega
  have hA : (X + 1) ^ d₁ ≤ W :=
    hW ▸ (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hY (by omega))
  have hDW : (X + 2) ^ D ≤ W := hW ▸ Nat.pow_le_pow_right hY (by omega)
  have hRW : (X + 2) ^ (D * (d + 1)) ≤ W := hW ▸ Nat.pow_le_pow_right hY (by omega)
  have h1 := Nat.mul_le_mul_left c₁ hA
  have h3 := hB.trans (Nat.mul_le_mul_left CB hDW)
  have h4 := hRr.trans (Nat.mul_le_mul_left CR hRW)
  calc N + c₁ * (X + 1) ^ d₁ + N + (Q + mB) ≤ N * 2 + (c₁ + CR + CB) * W := by
        rw [Nat.add_mul, Nat.add_mul]
        omega
    _ ≤ N * K + K * W := Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))
    _ ≤ K * (s * W) + K * W + K * N + K := by rw [Nat.mul_comm N K]; omega
    _ = K * ((s + 1) * W + N + 1) := by ring

/-- A bound `T ≤ K Z` with `Z ≥ 1` gives `c (T + 1) ≤ c (K + 1) Z`. -/
theorem scale {c T K Z : ℕ} (hT : T ≤ K * Z) (hZ : 1 ≤ Z) : c * (T + 1) ≤ c * (K + 1) * Z :=
  calc c * (T + 1) ≤ c * (K * Z + Z) := Nat.mul_le_mul_left _ (by omega)
    _ = c * (K + 1) * Z := by ring

/-! ### The bounds of the algorithm -/

/-- The exponent of the running time. -/
def eExp (e d d₁ : ℕ) : ℕ := d₁ + dL e + dL e * (d + 1)

/-- The constant of a running step. -/
def cR (C d : ℕ) : ℕ := C * (2 * (8 + lDone) + 3) ^ d + 2 * (8 + lDone) + 1

/-- The constant of the bound. -/
def kConst (C d c₁ : ℕ) : ℕ := 2 + rDone C d + c₁ + cR C d + (8 + lDone)

/-- The cost of a running step is polynomial. -/
theorem rRun_le (e C d : ℕ) (x : SPCAInput) :
    rRun e C d x ≤ cR C d * ((encSPCAInput x).length + 2) ^ (dL e * (d + 1)) :=
  rrun_le (by omega) (sRun_le e x)

/-- The length of the input with the coins. -/
theorem len_input (a : SPCAInput × List Bool) :
    2 * (encSPCAInput a.1).length + 1 + a.2.length = (encPair encSPCAInput encBits a).length :=
  (length_encPair (enc₁ := encSPCAInput) (enc₂ := encBits) a).symm

/-- **The time bound.** -/
theorem time_le (A : SLRInput × List Bool → Estimate) (e C d c₁ d₁ : ℕ)
    (a : SPCAInput × List Bool) :
    (encPair encSPCAInput encBits a).length + c₁ * ((encSPCAInput a.1).length + 1) ^ d₁ +
        (encPair encSPCAInput encBits a).length +
        ((∑ i ∈ range a.2.length, costR A e C d (initSt a.1, a.2) i) +
          maxB A e (initSt a.1, a.2)) ≤
      kConst C d c₁ *
        (spcaTime (eExp e d d₁) a.1 + (encPair encSPCAInput encBits a).length + 1) := by
  have hs := sum_cost_le A e C d a.1 a.2
  have hm := maxB_le A e a.1 a.2
  calc _ ≤ (encPair encSPCAInput encBits a).length + c₁ * ((encSPCAInput a.1).length + 1) ^ d₁ +
        (encPair encSPCAInput encBits a).length + (a.2.length * rDone C d +
          rounds a.1.δ (nOf a.1.points) * lenBlk e a.1 * rRun e C d a.1 +
            (sRun e a.1 + lDone)) := by
        omega
    _ ≤ _ := time_arith (len_input a) (rounds_le_sqrt _ _) (lenBlk_le e a.1) (sRun_le e a.1)
        (rRun_le e C d a.1) rfl rfl

/-- **The space bound.** -/
theorem space_le (A : SLRInput × List Bool → Estimate) (e C d c₁ d₁ : ℕ)
    (a : SPCAInput × List Bool) :
    (encPair encSPCAInput encBits a).length + c₁ * ((encSPCAInput a.1).length + 1) ^ d₁ +
        (encPair encSPCAInput encBits a).length +
        (spQ A e C d (initSt a.1, a.2) + maxB A e (initSt a.1, a.2)) ≤
      kConst C d c₁ *
        (spcaTime (eExp e d d₁) a.1 + (encPair encSPCAInput encBits a).length + 1) := by
  have hm := maxB_le A e a.1 a.2
  have hQ : spQ A e C d (initSt a.1, a.2) ≤ rRun e C d a.1 := by
    unfold spQ rRun
    have := Nat.mul_le_mul_left C (Nat.pow_le_pow_left
      (show 2 * maxB A e (initSt a.1, a.2) + 3 ≤ 2 * (sRun e a.1 + lDone) + 3 by omega) d)
    omega
  exact space_arith hm hQ (sRun_le e a.1) (rRun_le e C d a.1) rfl rfl

/-- **The coins of all rounds**: `rounds · lenBlk ≤ spcaTime`. -/
theorem coins_le (e d d₁ : ℕ) (x : SPCAInput) :
    rounds x.δ (nOf x.points) * lenBlk e x ≤ spcaTime (eExp e d d₁) x := by
  unfold spcaTime
  have h1 : ((encSPCAInput x).length + 2) ^ dL e ≤ ((encSPCAInput x).length + 2) ^ eExp e d d₁ :=
    Nat.pow_le_pow_right (by omega) (by unfold eExp; omega)
  exact Nat.mul_le_mul ((rounds_le_sqrt _ _).trans (Nat.le_succ _)) ((lenBlk_le e x).trans h1)

end RT

open RT in
/-- **The running time of the algorithm.** -/
theorem algB_runsInTime {A : SLRInput × List Bool → Estimate} {e : ℕ}
    (hA : RunsInTime encSLRInput encEstimate A (slrTime e)) :
    ∃ e' : ℕ, RunsInTime encSPCAInput Encoding.encBool (algB A e) (spcaTime e') ∧
      ∀ x : SPCAInput, rounds x.δ (nOf x.points) * lenBlk e x ≤ spcaTime e' x := by
  -- One step of the fold, and the initial state, in polynomial time.
  obtain ⟨C, d, hT⟩ := exists_tidy_pow (stepSt_polytime (polytime_of_runsInTime hA) e)
  obtain ⟨c₁, d₁, hI⟩ := exists_inO_pow initSt_polytime
  -- The initial state with the coins, the fold, and the answer.
  obtain ⟨c, hc, -⟩ := acc_inO.comp_linear ((fold_inO hT).comp (pre_inO hI))
  refine ⟨eExp e d d₁, ⟨c * (kConst C d c₁ + 1),
    hc.computableInTimeAndSpace.mono (fun a ↦ ?_) (fun a ↦ ?_)⟩, coins_le e d d₁⟩
  · exact scale (time_le A e C d c₁ d₁ a) (by omega)
  · exact scale (space_le A e C d c₁ d₁ a) (by omega)

end BDT24.Alg
