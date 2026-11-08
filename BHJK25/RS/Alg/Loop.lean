module

public import BHJK25.RS.Alg.PolyTimeData
public import BHJK25.Machine.Loop

/-!
# The algorithm as a loop

The algorithm runs through the indices `idx < n^L` one per round: the state is the data of the
run, the next index and whether a guess was accepted so far (`BHJK25.RS.AlgAux.stepSt`), so the
algorithm is `n^L` rounds from the initial state (`BHJK25.RS.AlgAux.run_eq_iterate`). The input of
the machine is `T` in unary followed by the tensor input (`BHJK25.RS.AlgAux.encInp`), so that a
single machine runs the algorithm for every `T`, and the degree of its polynomial factor does not
depend on `T`. The initial state, a round and the output are computed in polynomial time, and the
states have polynomial length, since the index has at most `L ⌈log₂ (n + 1)⌉ + 1` bits
(`BHJK25.RS.AlgAux.length_iterate_le`). By the loop theorem
(`BHJK25.Machine.Loop.iterate_inTime`), the algorithm runs in time
`c (n^L + 1) (|x| + 2)^c` (`BHJK25.RS.AlgAux.loop_time`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### The loop -/

/-- The input of the machine: `T` and the tensor input. -/
abbrev Inp (k : ℕ) : Type := ℕ × TensorInput k

/-- `T` in unary, then the tensor input. -/
noncomputable abbrev encInp (k : ℕ) : Inp k ↪ List Bool := encPair encUnary (encTensor k)

/-- The state of the loop: the data of the run, the next index, and whether a guess was accepted
so far. -/
abbrev St : Type := Dat × ℕ × Bool

/-- The encoding of the state, with the index in binary. -/
abbrev encSt : St ↪ List Bool := encPair encDat (encPair encNat encBool)

/-- The initial state. -/
noncomputable def initSt (k : ℕ) (y : Inp k) : St := (mkDat k y.1 y.2.1 (table y.2.2), 0, false)

/-- A round: test the guess of the current index. -/
def stepSt (k : ℕ) (s : St) : St := (s.1, s.2.1 + 1, s.2.2 || guessOK k s.1 s.2.1)

/-- The output: whether a guess was accepted. -/
def finishSt (s : St) : Bool := s.2.2

theorem iterate_stepSt (k : ℕ) (d : Dat) (i : ℕ) :
    (stepSt k)^[i] (d, 0, false) = (d, i, (List.range i).any (guessOK k d)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [stepSt, List.range_succ, List.any_append]

theorem run_eq_iterate (k T : ℕ) (x : TensorInput k) :
    run k T x = finishSt ((stepSt k)^[1 * x.1 ^ (mkDat k T x.1 (table x.2)).L]
      (initSt k (T, x))) := by
  rw [one_mul, initSt, iterate_stepSt]
  rfl

/-! ### Certificates -/

theorem length_encTensor {k : ℕ} (x : TensorInput k) :
    (encTensor k x).length = 2 * x.1.size + 1 + x.1 ^ k := by
  change (encPair encNat encBits (x.1, table x.2)).length = _
  rw [length_encPair]
  simp [table, Nat.size_eq_bits_len, encBits]

theorem length_encInp {k : ℕ} (y : Inp k) :
    (encInp k y).length = 2 * y.1 + 1 + (2 * y.2.1.size + 1 + y.2.1 ^ k) := by
  rw [length_encPair, length_encTensor]
  simp

theorem le_length_encInp {k : ℕ} (hk : 1 ≤ k) (y : Inp k) :
    y.2.1 ≤ (encInp k y).length ∧ y.2.1.size ≤ (encInp k y).length := by
  rw [length_encInp]
  have h : y.2.1 ≤ y.2.1 ^ k := by
    rcases Nat.eq_zero_or_pos y.2.1 with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    · exact Nat.le_self_pow (by omega) _
  omega

/-- The tensor input as `n` and its table. -/
theorem tensor_polytime (k : ℕ) : ComputableInPolyTime (fun x : TensorInput k ↦ (x.1, table x.2))
    (encTensor k) (encPair encNat encBits) :=
  of_eq fun _ ↦ rfl

section Input

variable (k : ℕ)

theorem inp_T : ComputableInPolyTime (fun y : Inp k ↦ y.1) (encInp k) encUnary := fst _ _

theorem inp_n : ComputableInPolyTime (fun y : Inp k ↦ y.2.1) (encInp k) encNat :=
  (fst _ _).comp' ((tensor_polytime k).comp' (snd _ _))

theorem inp_w : ComputableInPolyTime (fun y : Inp k ↦ table y.2.2) (encInp k) encBits :=
  (snd _ _).comp' ((tensor_polytime k).comp' (snd _ _))

theorem inp_nu (hk : 1 ≤ k) : ComputableInPolyTime (fun y : Inp k ↦ y.2.1) (encInp k) encUnary :=
  binary_to_unary_bounded (inp_n k) (encoding_length (encInp k))
    fun y ↦ (le_length_encInp hk y).1

theorem mkDat_inp (hk : 1 ≤ k) : ComputableInPolyTime
    (fun y : Inp k ↦ mkDat k y.1 y.2.1 (table y.2.2)) (encInp k) encDat :=
  mkDat_polytime k (inp_T k) (inp_n k) (inp_nu k hk) (inp_w k)

theorem initSt_polytime (hk : 1 ≤ k) : ComputableInPolyTime (initSt k) (encInp k) encSt :=
  (mkDat_inp k hk).prod ((const 0).prod (const false))

end Input

theorem stepSt_polytime (k : ℕ) : ComputableInPolyTime (stepSt k) encSt encSt := by
  have hd : ComputableInPolyTime (fun s : St ↦ s.1) encSt encDat := fst _ _
  have hi : ComputableInPolyTime (fun s : St ↦ s.2.1) encSt encNat := (fst _ _).comp' (snd _ _)
  have ha : ComputableInPolyTime (fun s : St ↦ s.2.2) encSt encBool := (snd _ _).comp' (snd _ _)
  exact hd.prod ((binary_add.comp' (hi.prod (const 1))).prod
    (bool_or.comp' (ha.prod (guessOK_polytime k hd hi))))

theorem finishSt_polytime : ComputableInPolyTime finishSt encSt encBool :=
  (snd _ _).comp' (snd _ _)

/-! ### Bounds on the states -/

theorem size_pow_le (n L : ℕ) : (n ^ L).size ≤ L * n.size + 1 := by
  refine Nat.size_le.2 ?_
  calc n ^ L ≤ (2 ^ n.size) ^ L := Nat.pow_le_pow_left (Nat.lt_size_self n).le L
    _ = 2 ^ (L * n.size) := by rw [← pow_mul, Nat.mul_comm]
    _ < 2 ^ (L * n.size + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem length_encSt (d : Dat) (i : ℕ) (b : Bool) :
    (encSt (d, i, b)).length = 2 * (encDat d).length + 2 * i.size + 3 := by
  rw [length_encPair, length_encPair]
  simp [Nat.size_eq_bits_len]
  ring

/-- `L ≤ 2 k (2 |y| + 4)`. -/
theorem L_le {k : ℕ} (hk : 1 ≤ k) (y : Inp k) :
    (mkDat k y.1 y.2.1 (table y.2.2)).L ≤ 2 * k * (2 * (encInp k y).length + 4) := by
  have h1 := ell_le_rbits k y.1 y.2.1
  have h2 := rbits_le y.1 y.2.1
  have h3 := clog_le_self y.2.1
  have h4 := (le_length_encInp hk y).1
  change 2 * (k - 1) * ell k y.1 y.2.1 ≤ _
  have h5 : ell k y.1 y.2.1 ≤ 2 * (encInp k y).length + 4 := by omega
  calc 2 * (k - 1) * ell k y.1 y.2.1 ≤ 2 * k * ell k y.1 y.2.1 := by gcongr; omega
    _ ≤ _ := Nat.mul_le_mul_left _ h5

/-- The bound on the states. -/
noncomputable def stBound (k : ℕ) (y : Inp k) : ℕ :=
  (encSt (initSt k y)).length + 30 * k * ((encInp k y).length + 4) ^ 2

theorem stBound_polyBounded (k : ℕ) (hk : 1 ≤ k) :
    PolyBounded (fun y : Inp k ↦ (encInp k y).length) (stBound k) :=
  ((initSt_polytime k hk).polyBounded_length).add
    ((PolyBounded.const (30 * k)).mul ((PolyBounded.self.add (.const 4)).pow 2))

theorem abk_le {k : ℕ} (hk : 1 ≤ k) (y : Inp k) :
    1 + y.2.1 + (mkDat k y.1 y.2.1 (table y.2.2)).L ≤ stBound k y := by
  have h1 := L_le hk y
  have h2 := (le_length_encInp hk y).1
  unfold stBound
  generalize (encInp k y).length = N at *
  have : 1 + N + 2 * k * (2 * N + 4) ≤ 30 * k * (N + 4) ^ 2 := by nlinarith
  omega

/-- **The states stay polynomially bounded.** -/
theorem length_iterate_le {k : ℕ} (hk : 1 ≤ k) (y : Inp k) (i : ℕ)
    (hi : i ≤ 1 * y.2.1 ^ (mkDat k y.1 y.2.1 (table y.2.2)).L) :
    (encSt ((stepSt k)^[i] (initSt k y))).length ≤ stBound k y := by
  unfold stBound initSt
  rw [iterate_stepSt, length_encSt, length_encSt, Nat.size_zero]
  have h1 := Nat.size_le_size hi
  rw [one_mul] at h1
  have h2 := size_pow_le y.2.1 (mkDat k y.1 y.2.1 (table y.2.2)).L
  have h3 := L_le hk y
  have h4 := (le_length_encInp hk y).2
  generalize (encInp k y).length = N at *
  generalize (mkDat k y.1 y.2.1 (table y.2.2)).L = L at *
  have h5 : L * y.2.1.size ≤ 2 * k * (2 * N + 4) * N := Nat.mul_le_mul h3 h4
  have h6 : 2 * (2 * k * (2 * N + 4) * N + 1) ≤ 30 * k * (N + 4) ^ 2 := by nlinarith
  omega

/-! ### The running time of the loop -/

/-- **The loop runs in time `c (n^L + 1) (|y| + 2)^c`**, with `c` independent of `T`. -/
theorem loop_time (k : ℕ) (hk : 1 ≤ k) : ∃ c : ℕ, ComputableInTimeAndSpace
    (fun y : Inp k ↦ run k y.1 y.2) (encInp k) encBool
    (fun y ↦ c * ((y.2.1 ^ (mkDat k y.1 y.2.1 (table y.2.2)).L + 1) *
      ((encInp k y).length + 2) ^ c))
    (fun y ↦ c * ((y.2.1 ^ (mkDat k y.1 y.2.1 (table y.2.2)).L + 1) *
      ((encInp k y).length + 2) ^ c)) := by
  obtain ⟨c, hc⟩ := BHJK25.Machine.Loop.iterate_inTime (initSt k) (stepSt k) finishSt
    (fun _ ↦ 1) (fun y ↦ y.2.1) (fun y ↦ (mkDat k y.1 y.2.1 (table y.2.2)).L)
    (initSt_polytime k hk) (stepSt_polytime k) finishSt_polytime (const 1) (inp_n k)
    (toBin (dat_L (mkDat_inp k hk))) (stBound k) (stBound_polyBounded k hk)
    (fun y ↦ abk_le hk y) (fun y i hi ↦ length_iterate_le hk y i hi)
  refine ⟨c, ?_⟩
  have hfun : (fun y : Inp k ↦ finishSt ((stepSt k)^[1 * y.2.1 ^
      (mkDat k y.1 y.2.1 (table y.2.2)).L] (initSt k y))) = fun y ↦ run k y.1 y.2 := by
    funext y
    rw [run_eq_iterate]
  rw [hfun] at hc
  simpa only [one_mul] using hc

end BHJK25.RS.AlgAux
