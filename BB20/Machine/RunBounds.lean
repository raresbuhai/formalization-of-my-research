module

public import BB20.Machine.StepPolyTime
public import BB20.Machine.ThrPolyTime

/-!
# The start, the end and the states of the loop

* Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the start of the runs
  (`BB20.Machine.Run.PT.init6_polytime`, `BB20.Machine.Run.PT.init11_polytime`), the output
  (`BB20.Machine.Run.PT.finish_polytime`), and the numbers `a`, `b`, `k` of the `a · b^k` rounds.
* The states of a run stay polynomially bounded (`BB20.Machine.Run.PT.length_iterate_le`): an
  invariant (`BB20.Machine.Run.Inv`) bounds the lengths of the lists and the numbers in them.
* The number of rounds: `a = 2n²`, `b = n + 1` and `k` are polynomially bounded
  (`BB20.Machine.Run.abk_le`), and the time of the loop is within the running time of the theorems
  (`BB20.Machine.Run.time_le`), since `(n + 1)^k ≤ (n + 2)^{2^s}`.
-/

@[expose] public section

namespace BB20.Machine.Run

/-! ### The invariant -/

/-- The invariant of the states of a run with data `d`. -/
def Inv (d : Dat) (s : St) : Prop :=
  s.1 = d ∧ s.2.1.1 ≤ d.2.1 ∧ s.2.1.2.1 ≤ 2 * d.2.1 - 1 ∧
    s.2.1.2.2.1.length ≤ s.2.1.2.1 * d.2.2.1 ∧ (∀ i ∈ s.2.1.2.2.1, i < d.2.1) ∧
    s.2.1.2.2.2.1.length ≤ s.2.1.2.1 ∧ (∀ i ∈ s.2.1.2.2.2.1, i < d.2.1) ∧
    s.2.1.2.2.2.2.length ≤ s.2.1.1 ∧
    (∀ l ∈ s.2.1.2.2.2.2, l.length ≤ 2 * d.2.1 ∧ ∀ i ∈ l, i < d.2.1) ∧
    s.2.2.1 < d.2.2.2.1 ∧ s.2.2.2.1.length = d.2.2.1 ∧ (∀ e ∈ s.2.2.2.1, e ≤ d.2.1) ∧
    ∀ J, s.2.2.2.2 = some J → J.length ≤ d.2.2.1 ∧ ∀ i ∈ J, i < d.2.1

theorem inv_start (d : Dat) (hK : 0 < d.2.2.2.1) : Inv d (start d) := by
  simp [Inv, start, inn0, hK]

/-- What a round of a search keeps is a candidate of at most `k` numbers below `n`. -/
theorem upd_some {smp : List (List Bool)} {n u : ℕ} {t : ℚ} {S : List ℕ} {b : Option (List ℕ)}
    {tup : List ℕ} {k : ℕ} (hb : ∀ J, b = some J → J.length ≤ k ∧ ∀ i ∈ J, i < n)
    (htup : tup.length = k) (J : List ℕ) (hJ : upd smp n u t S b (candOf n tup) = some J) :
    J.length ≤ k ∧ ∀ i ∈ J, i < n := by
  unfold upd at hJ
  split_ifs at hJ
  · cases hJ
    exact ⟨htup ▸ length_candOf_le n tup, fun i hi ↦ (mem_candOf.1 hi).1⟩
  · exact hb J hJ

theorem newP_spec (d : Dat) (m : Mac) (r : Option (List ℕ)) :
    (newP d m r).length ≤ m.2.2.2.1.length + 1 ∧
      ∀ i ∈ newP d m r, i ∈ m.2.2.2.1 ∨ i = m.2.1 - d.2.1 := by
  unfold newP
  split
  · simp
  · exact ⟨by simp, fun i hi ↦ Or.inl (by simpa using hi)⟩

theorem inv_fstep {d : Dat} {s : St} (h : Inv d s) : Inv d (fstep s) := by
  obtain ⟨s₁, ⟨u, ph, S, P, acc⟩, ⟨j, tup, best⟩⟩ := s
  obtain ⟨rfl, hu, hph, hS, hS', hP, hP', hacc, hacc', hj, htup, htup', hbest⟩ := h
  obtain ⟨smp, n, k, K, t₂, t₃, mode⟩ := s₁
  simp only at *
  unfold fstep
  simp only
  split_ifs with hun hjK
  · dsimp only [Inv]
    refine ⟨rfl, hu, hph, hS, hS', hP, hP', hacc, hacc', hjK, ?_, ?_, ?_⟩
    · simp [sstepAt, sstep, length_incr, htup]
    · exact incr_le n tup htup'
    · exact upd_some hbest htup
  · have hr := upd_some (smp := smp) (u := u) (t := curT n ph t₂ t₃) (S := curS n ph S) hbest
      htup
    have hK : 0 < K := by omega
    set r := (sstepAt (smp, n, k, K, t₂, t₃, mode) (u, ph, S, P, acc) (tup, best)).2 with hrdef
    have hr' : ∀ J, r = some J → J.length ≤ k ∧ ∀ i ∈ J, i < n := hr
    have hnP := newP_spec (smp, n, k, K, t₂, t₃, mode) (u, ph, S, P, acc) r
    simp only at hnP
    unfold trans
    split_ifs with h₁ h₂
    all_goals try dsimp only at h₁
    all_goals try dsimp only at h₂
    · dsimp only [Inv]
      refine ⟨rfl, hu, by omega, ?_, ?_, by omega, hP', hacc, hacc', hK,
        by simp, by simp, by simp⟩
      · cases hr'' : r with
        | none => simp only [Option.getD_none, List.append_nil]; nlinarith
        | some J =>
          have := (hr' J hr'').1
          simp only [Option.getD_some, List.length_append]
          nlinarith
      · intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · exact hS' i hi
        · cases hr'' : r with
          | none => simp [hr''] at hi
          | some J => simp only [hr'', Option.getD_some] at hi; exact (hr' J hr'').2 i hi
    · dsimp only [Inv]
      refine ⟨rfl, hu, by omega, by nlinarith, hS', by omega, fun i hi ↦ ?_, hacc, hacc', hK,
        by simp, by simp, by simp⟩
      rcases hnP.2 i hi with hi | rfl
      · exact hP' i hi
      · omega
    · dsimp only [Inv]
      refine ⟨rfl, by omega, by omega, Nat.zero_le _, fun _ h ↦ (List.not_mem_nil h).elim,
        Nat.zero_le _, fun _ h ↦ (List.not_mem_nil h).elim, ?_, ?_, hK, by simp, by simp,
        by simp⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro l hl
        rcases List.mem_append.1 hl with hl | hl
        · exact hacc' l hl
        · rw [List.mem_singleton.1 hl]
          refine ⟨by omega, fun i hi ↦ ?_⟩
          rcases hnP.2 i hi with hi | rfl
          · exact hP' i hi
          · omega
  · exact ⟨rfl, hu, hph, hS, hS', hP, hP', hacc, hacc', hj, htup, htup', hbest⟩

theorem inv_iterate {d : Dat} {s : St} (h : Inv d s) (i : ℕ) : Inv d (fstep^[i] s) := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact inv_fstep ih


/-! ### The number of rounds -/

theorem capN_le_length (x : Input) : capN x ≤ (encInput x).length := min_le_left _ _

theorem capN_le_n (x : Input) : capN x ≤ x.n := min_le_right _ _

theorem capK_le (x : Input) : capK x ≤ 2 ^ x.s :=
  (min_le_right _ _).trans (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))

/-- The number of rounds and its cost, within the running time of the theorems. -/
theorem time_le (x : Input) {a : ℕ} (ha : a ≤ 2 * capN x * capN x) (c : ℕ) :
    c * ((a * (capN x + 1) ^ capK x + 1) * ((encInput x).length + 2) ^ c) ≤
      3 * c * (learnTime (c + 2) x + (encInput x).length + 1) := by
  set L := (encInput x).length
  set P := (x.n + 2) ^ 2 ^ x.s
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hb : (capN x + 1) ^ capK x ≤ P :=
    (Nat.pow_le_pow_left (by have := capN_le_n x; omega) _).trans
      (Nat.pow_le_pow_right (by omega) (capK_le x))
  have hN := capN_le_length x
  have ha' : a ≤ 2 * (L + 2) ^ 2 := ha.trans (by nlinarith)
  have h1 : a * (capN x + 1) ^ capK x + 1 ≤ 3 * (L + 2) ^ 2 * P := by
    have := Nat.mul_le_mul ha' hb
    have : 1 ≤ (L + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h2 : (a * (capN x + 1) ^ capK x + 1) * (L + 2) ^ c ≤ 3 * learnTime (c + 2) x := by
    calc _ ≤ 3 * (L + 2) ^ 2 * P * (L + 2) ^ c := Nat.mul_le_mul_right _ h1
      _ = 3 * ((L + 2) ^ (c + 2) * P) := by ring
      _ = 3 * learnTime (c + 2) x := rfl
  calc c * ((a * (capN x + 1) ^ capK x + 1) * (L + 2) ^ c) ≤ c * (3 * learnTime (c + 2) x) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ 3 * c * (learnTime (c + 2) x + L + 1) := by nlinarith

theorem abk_le (x : Input) {a : ℕ} (ha : a ≤ 2 * capN x * capN x) :
    a + (capN x + 1) + capK x ≤ 100 * ((encInput x).length + 1) ^ 4 := by
  have hN := capN_le_length x
  have hK : capK x ≤ capN x := min_le_left _ _
  have h : a + (capN x + 1) + capK x ≤ 2 * ((encInput x).length + 1) ^ 2 := by nlinarith
  have : ((encInput x).length + 1) ^ 2 ≤ ((encInput x).length + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem rounds6_le (thr : Input → Option ℚ) (x : Input) :
    rounds6 thr x ≤ 2 * capN x * capN x := by
  unfold rounds6
  split_ifs <;> omega

theorem rounds11_le (thr : Input → Option (ℚ × ℚ)) (x : Input) :
    rounds11 thr x ≤ 2 * capN x * capN x := by
  unfold rounds11
  split_ifs <;> omega

end BB20.Machine.Run

namespace BB20.Machine.Run.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### The lengths of the states -/

theorem length_encL_le (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    (encL l).length ≤ l.length * (2 * N + 1) := by
  rw [length_encList]
  refine (List.sum_le_length_nsmul _ (2 * N + 1) fun y hy ↦ ?_).trans (by simp)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  have := h i hi
  simp only [encUnary_apply, List.length_replicate]
  omega

theorem length_encLL_le (acc : List (List ℕ)) (L N : ℕ)
    (h : ∀ l ∈ acc, l.length ≤ L ∧ ∀ i ∈ l, i < N) :
    (encList encL acc).length ≤ acc.length * (2 * (L * (2 * N + 1)) + 1) := by
  rw [length_encList]
  refine (List.sum_le_length_nsmul _ (2 * (L * (2 * N + 1)) + 1) fun y hy ↦ ?_).trans (by simp)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
  have h1 := length_encL_le l N (h l hl).2
  have h2 := Nat.mul_le_mul_right (2 * N + 1) (h l hl).1
  omega

theorem length_encNat_le {m n : ℕ} (h : m ≤ n) : (encNat m).length ≤ (encNat n).length := by
  simp only [encNat_apply]
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-- **The states of a run are bounded** by the length of the encoded data and a polynomial in
`n`. -/
theorem length_st_le {d : Dat} {s : St} (h : Inv d s) (hk : d.2.2.1 ≤ d.2.1) :
    (encSt s).length ≤ 4 * (encDat d).length + 100 * (d.2.1 + 1) ^ 4 := by
  obtain ⟨s₁, ⟨u, ph, S, P, acc⟩, ⟨j, tup, best⟩⟩ := s
  obtain ⟨rfl, hu, hph, hS, hS', hP, hP', hacc, hacc', hj, htup, htup', hbest⟩ := h
  obtain ⟨smp, n, k, K, t₂, t₃, mode⟩ := s₁
  simp only at *
  have e1 := length_encL_le S n hS'
  have e2 := length_encL_le P n hP'
  have e3 := length_encLL_le acc (2 * n) n hacc'
  have e4 := length_encL_le tup (n + 1) fun e he ↦ by have := htup' e he; omega
  have e5 : (encOption encL best).length ≤ 1 + k * (2 * n + 1) := by
    cases best with
    | none => simp
    | some J =>
      have := length_encL_le J n (hbest J rfl).2
      have := Nat.mul_le_mul_right (2 * n + 1) (hbest J rfl).1
      simp only [encOption_some, List.length_cons]
      omega
  have e6 : (encNat j).length ≤ (encDat (smp, n, k, K, t₂, t₃, mode)).length := by
    refine (length_encNat_le hj.le).trans ?_
    simp only [length_encPair]
    omega
  simp only [length_encPair, encUnary_apply, List.length_replicate] at e6 ⊢
  rw [htup] at e4
  have f1 : S.length * (2 * n + 1) ≤ 2 * n * n * (2 * n + 1) :=
    Nat.mul_le_mul_right _ (hS.trans (Nat.mul_le_mul (by omega) hk))
  have f2 : P.length * (2 * n + 1) ≤ 2 * n * (2 * n + 1) := Nat.mul_le_mul_right _ (by omega)
  have f3 : acc.length * (2 * (2 * n * (2 * n + 1)) + 1) ≤ n * (2 * (2 * n * (2 * n + 1)) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have f4 : k * (2 * (n + 1) + 1) ≤ n * (2 * (n + 1) + 1) := Nat.mul_le_mul_right _ hk
  have f5 : k * (2 * n + 1) ≤ n * (2 * n + 1) := Nat.mul_le_mul_right _ hk
  have hp : (n + 1) ^ 4 = (n + 1) * (n + 1) * (n + 1) * (n + 1) := by ring
  have hph' : ph ≤ 2 * n := by omega
  rw [hp]
  nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n), Nat.zero_le (n * n * n * n)]

/-- **The states of a run on `x` are polynomially bounded.** -/
theorem length_iterate_le (x : Input) (t₂ t₃ : ℚ) (mode : Bool) (i : ℕ) :
    (encSt (fstep^[i] (start (datOf x t₂ t₃ mode)))).length ≤
      4 * (encSt (start (datOf x t₂ t₃ mode))).length + 100 * ((encInput x).length + 1) ^ 4 := by
  have hK : 0 < (datOf x t₂ t₃ mode).2.2.2.1 := pow_pos (Nat.succ_pos _) _
  have h := length_st_le (inv_iterate (inv_start _ hK) i) (min_le_left _ _)
  have h1 : (encDat (datOf x t₂ t₃ mode)).length ≤ (encSt (start (datOf x t₂ t₃ mode))).length := by
    simp only [start, length_encPair]
    omega
  have h2 : ((datOf x t₂ t₃ mode).2.1 + 1) ^ 4 ≤ ((encInput x).length + 1) ^ 4 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (min_le_left _ _) 1) 4
  omega

/-! ### The start, the end and the round count -/

theorem n_polytime : ComputableInPolyTime (fun x : Input => x.n) encInput encNat :=
  (fst _ _).comp' Thr.fields_polytime

theorem wf_polytime : ComputableInPolyTime wf encInput encBool := by
  unfold wf
  have hs := Thr.samples_polytime
  have he := bool_not.comp' ((ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listIsEmpty' encBits)).comp' hs)
  have ha := allWithInput (test := fun x (l : List Bool) => decide (l.length = x.n)) hs
    (decide_eq' (unary_to_binary.comp' (length_bits.comp' (snd _ _)))
      (n_polytime.comp' (fst _ _)))
  exact bool_and' he ha

theorem capN_polytime : ComputableInPolyTime capN encInput encUnary :=
  binary_min_unary' (encoding_length encInput) n_polytime

theorem capK_polytime : ComputableInPolyTime capK encInput encUnary :=
  binary_min_unary' capN_polytime
    (binary_two_pow.comp' (binary_min_unary' capN_polytime Thr.s_polytime))

theorem datOf' {t₂ t₃ : Input → ℚ} (mode : Bool) (h₂ : ComputableInPolyTime t₂ encInput encRat)
    (h₃ : ComputableInPolyTime t₃ encInput encRat) :
    ComputableInPolyTime (fun x => datOf x (t₂ x) (t₃ x) mode) encInput encDat := by
  unfold datOf
  have hK := binary_pow' (unary_to_binary.comp' (unary_add' capN_polytime (const 1)))
    capK_polytime
  exact Thr.samples_polytime.prod (capN_polytime.prod (capK_polytime.prod (hK.prod
    (h₂.prod (h₃.prod (const mode))))))

theorem start' {α : Type} {input : α ↪ List Bool} {d : α → Dat}
    (hd : ComputableInPolyTime d input encDat) :
    ComputableInPolyTime (fun a => start (d a)) input encSt := by
  unfold start inn0
  exact hd.prod ((const (0, 0, [], [], [])).prod ((const 0).prod
    ((replicate (dat_k hd) (const 0)).prod (const none))))

theorem init6_polytime {thr : Input → Option ℚ}
    (hthr : ComputableInPolyTime thr encInput (encOption encRat)) :
    ComputableInPolyTime (init6 thr) encInput encSt := by
  unfold init6
  have ht := (optionGetD encRat).comp' (hthr.prod (const 0))
  exact start' (datOf' false ht ht)

theorem init11_polytime {thr : Input → Option (ℚ × ℚ)}
    (hthr : ComputableInPolyTime thr encInput (encOption (encPair encRat encRat))) :
    ComputableInPolyTime (init11 thr) encInput encSt := by
  unfold init11
  have ht := (optionGetD (encPair encRat encRat)).comp' (hthr.prod (const (0, 0)))
  exact start' (datOf' true ((fst _ _).comp' ht) ((snd _ _).comp' ht))

theorem finish_polytime : ComputableInPolyTime finish encSt encOutput := by
  have hacc : ComputableInPolyTime finish encSt (encList encL) :=
    mac_acc ((fst _ _).comp' (snd _ _))
  have h := mapWithInput (f := fun _ (l : List ℕ) => l.map fun i => i) hacc
    (mapWithInput (f := fun _ (i : ℕ) => i) (snd _ _) (unary_to_binary.comp' (snd _ _)))
  refine h.of_enc_eq fun s => ?_
  simp only [List.map_id']
  rfl

theorem rounds6_polytime {thr : Input → Option ℚ}
    (hthr : ComputableInPolyTime thr encInput (encOption encRat)) :
    ComputableInPolyTime (rounds6 thr) encInput encNat := by
  unfold rounds6
  exact ite' (bool_and' wf_polytime (optionIsSome hthr))
    (unary_to_binary.comp' (unary_mul' (unary_mul' (const 2) capN_polytime) capN_polytime))
    (const 0)

theorem rounds11_polytime {thr : Input → Option (ℚ × ℚ)}
    (hthr : ComputableInPolyTime thr encInput (encOption (encPair encRat encRat))) :
    ComputableInPolyTime (rounds11 thr) encInput encNat := by
  unfold rounds11
  exact ite' (bool_and' wf_polytime (optionIsSome hthr))
    (unary_to_binary.comp' (unary_mul' (unary_mul' (const 2) capN_polytime) capN_polytime))
    (const 0)

theorem base_polytime : ComputableInPolyTime (fun x => capN x + 1) encInput encNat :=
  unary_to_binary.comp' (unary_add' capN_polytime (const 1))

theorem capK_bin_polytime : ComputableInPolyTime capK encInput encNat :=
  unary_to_binary.comp' capK_polytime

end BB20.Machine.Run.PT
