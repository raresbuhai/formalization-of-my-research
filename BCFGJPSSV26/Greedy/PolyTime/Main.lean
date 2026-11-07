module

public import BCFGJPSSV26.Greedy.PolyTime.Core
public import BCFGJPSSV26.Greedy.Constants
public import BCFGJPSSV26.Combine.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import BCFGJPSSV26.Greedy.PolyTime.AuxMain
public import BCFGJPSSV26.Stable.Time.PolyTimeLS

/-!
# The algorithms of Theorem 1.2 run in polynomial time

`BCFGJPSSV26.Greedy.algFor_polytime`: for each `ε`, the algorithm of Theorem 1.2 is computable in
polynomial time on encoded instances, from certificates for its parts:

* the core (`BCFGJPSSV26.Greedy.core_polytime`), the trivial solution
  (`BCFGJPSSV26.Greedy.trivialSol_polytime`), the guesses (`BCFGJPSSV26.Greedy.guesses_polytime`),
  the scaled inputs (`BCFGJPSSV26.Greedy.scaledIn_polytime`), the bounds on the number of
  facilities (`BCFGJPSSV26.Greedy.bcompBound_polytime`, `BCFGJPSSV26.Greedy.kR_polytime`);
* the local search of Part II with its budget (`BCFGJPSSV26.Greedy.localSearch_polytime`, from
  `BCFGJPSSV26.Stable.localSearch_polytime`), on the tuples with `k` at most the number of rows of
  the table: the local search outputs `k` facilities, and `k` is in binary. It runs only when the
  trivial solution has more than `k` facilities, and it has at most one more than there are rows
  (`BCFGJPSSV26.Greedy.PT.length_trivialSol_le`);
* the choice of the cheapest output (`BCFGJPSSV26.Combine.best_polytime`).

The main algorithm runs the core on scaled inputs with `n` rows of `m` entries, so it is
certified on tuples with `n` and `m` in unary (`BCFGJPSSV26.Greedy.encCoreIn`), to which the
encoding of an instance converts in polynomial time (`BCFGJPSSV26.Greedy.toRawU_polytime`: an
instance has `n + m` rows). The trivial solution and the guesses are certified with `n` and `m`
in binary, by loops over the table (`Greedy/PolyTime/AuxMain.lean`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### The parts -/

theorem raw_n_polytime : ComputableInPolyTime Raw.n encRaw encNat := fst _ _

theorem raw_m_polytime : ComputableInPolyTime Raw.m encRaw encNat := (fst _ _).comp (snd _ _)

theorem raw_k_polytime : ComputableInPolyTime Raw.k encRaw encNat :=
  ((fst _ _).comp (snd _ _)).comp (snd _ _)

theorem raw_table_polytime : ComputableInPolyTime Raw.table encRaw (encList (encList encRat)) :=
  ((snd _ _).comp (snd _ _)).comp (snd _ _)

/-- From `n` and `m` in unary to `n` and `m` in binary. -/
theorem rawU_raw_polytime : ComputableInPolyTime (fun x : Raw ↦ x) encCoreIn encRaw :=
  (PT.toBin (fst _ _)).prod ((PT.toBin ((fst _ _).comp (snd _ _))).prod ((snd _ _).comp (snd _ _)))

/-- The trivial solution. -/
theorem trivialSol_polytime : ComputableInPolyTime trivialSol encRaw (encList encNat) :=
  PT.trivialSolL (X := fun x ↦ x) id'

/-- The guesses. -/
theorem guesses_polytime : ComputableInPolyTime guesses encRaw (encList encRat) :=
  PT.guessesL (X := fun x ↦ x) id'

/-- The scaled input for a guess. -/
theorem scaledIn_polytime (c : Consts) :
    ComputableInPolyTime (fun p : Raw × ℚ ↦ scaledIn c p.1 p.2) (encPair encCoreIn encRat)
      encCoreIn := by
  unfold scaledIn scaledTable trunc tOf Raw.fdist Raw.dist Raw.n Raw.m Raw.k Raw.table
  have hn : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.1) (encPair encCoreIn encRat) encUnary :=
    (fst _ _).comp (fst _ _)
  have hm : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.2.1) (encPair encCoreIn encRat)
      encUnary := ((fst _ _).comp (snd _ _)).comp (fst _ _)
  have hk : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.2.2.1) (encPair encCoreIn encRat)
      encNat := (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp (fst _ _)
  have hT : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.2.2.2) (encPair encCoreIn encRat)
      (encList (encList encRat)) := (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp (fst _ _)
  have hn' := hn.comp ((fst _ _).comp (fst (encPair (encPair encCoreIn encRat) encUnary) encUnary))
  have hΛ : ComputableInPolyTime (fun q : ((Raw × ℚ) × ℕ) × ℕ ↦ q.1.1.2)
      (encPair (encPair (encPair encCoreIn encRat) encUnary) encUnary) encRat :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hnQ := rat_natCast' (PT.toBin hn')
  have hentry : ComputableInPolyTime (fun q : ((Raw × ℚ) × ℕ) × ℕ ↦
      min (((q.1.1.1.2.2.2.getD q.1.2 []).getD (q.1.1.1.1 + q.2) 0) /
        (c.εp * q.1.1.2 / (q.1.1.1.1 : ℚ)) + 1) (Mof c q.1.1.1.1))
      (encPair (encPair (encPair encCoreIn encRat) encUnary) encUnary) encRat := by
    refine rat_min' (rat_add' (rat_div' ?_ (rat_div' (rat_mul' (const _) hΛ) hnQ)) (const 1)) ?_
    · exact listGetD_binary (encA := encRat) 0 (listGetD_binary (encA := encList encRat) []
        (hT.comp ((fst _ _).comp (fst _ _))) (PT.toBin ((snd _ _).comp (fst _ _))))
        (PT.binAdd (PT.toBin hn') (PT.toBin (snd _ _)))
    · unfold Mof
      exact rat_add' (rat_div' (rat_mul' (const 8) (rat_sq' hnQ)) (const _)) (const 1)
  have hm' : ComputableInPolyTime (fun q : (Raw × ℚ) × ℕ ↦ q.1.1.2.1)
      (encPair (encPair encCoreIn encRat) encUnary) encUnary := hm.comp (fst _ _)
  have hrow := mapWithInput (f := fun (q : (Raw × ℚ) × ℕ) (i : ℕ) ↦
    min (((q.1.1.2.2.2.getD q.2 []).getD (q.1.1.1 + i) 0) / (c.εp * q.1.2 / (q.1.1.1 : ℚ)) + 1)
      (Mof c q.1.1.1)) (unary_range' hm') hentry
  exact hn.prod (hm.prod (hk.prod (mapWithInput (f := fun (p : Raw × ℚ) (j : ℕ) ↦
    (List.range p.1.2.1).map fun i ↦ min (((p.1.2.2.2.getD j []).getD (p.1.1 + i) 0) /
      (c.εp * p.2 / (p.1.1 : ℚ)) + 1) (Mof c p.1.1)) (unary_range' hn) hrow)))

/-- The bound `k + ⌊log₂ n⌋ ⌈1/δ²⌉` on the trivial solution. -/
theorem bcompBound_polytime (c : Consts) :
    ComputableInPolyTime (fun x : Raw ↦ x.k + bcomp c x.n) encRaw encNat := by
  unfold bcomp
  have hlog : ComputableInPolyTime (fun x : Raw ↦ Nat.log 2 x.n) encRaw encNat :=
    PT.toBin (binary_log_two.comp raw_n_polytime)
  exact PT.binAdd raw_k_polytime (binary_mul' hlog (const _))

/-- The bound `k + 6R` on the outputs of the core. -/
theorem kR_polytime (c : Consts) :
    ComputableInPolyTime (fun x : Raw ↦ x.k + 6 * Rof c x.n) encRaw encNat := by
  have hR : ComputableInPolyTime (fun x : Raw ↦ Rof c x.n) encRaw encNat := by
    unfold Rof Mof
    have hn := rat_natCast' raw_n_polytime
    exact PT.binAdd (binary_mul' (const _) (binary_clog_two_nat' (PT.natCeil (rat_mul'
      (rat_mul' (const 5) hn) (rat_add' (rat_div' (rat_mul' (const 8) (rat_sq' hn)) (const _))
        (const 1)))))) (const 1)
  exact PT.binAdd raw_k_polytime (binary_mul' (const 6) hR)

/-- **The local search of Part II with its budget** runs in polynomial time (for the fixed
`N = 201`, swaps of size `24 N`, and the budget `(|x| + 2)^(2 p + 2)`), on the tuples with `k` at
most the number of rows of the table (its output has `k` entries, and `k` is in binary). -/
theorem localSearch_polytime :
    ComputableInPolyTime (fun x : Raw ↦ if x.k ≤ x.table.length then
      Stable.localSearch lsN x (lsBudget x) else []) encRaw (encList encNat) := by
  have hB : ComputableInPolyTime lsBudget encRaw encUnary :=
    (unary_pow _).comp (unary_add' (encoding_length encRaw) (const 2))
  exact Stable.localSearch_polytime.comp ((const lsN).prod (id'.prod hB))

/-! ### The algorithms -/

theorem guessesU_polytime : ComputableInPolyTime guesses encCoreIn (encList encRat) :=
  guesses_polytime.comp rawU_raw_polytime

theorem coreRuns_polytime (c : Consts) :
    ComputableInPolyTime (coreRuns c) encCoreIn (encList (encList encNat)) :=
  mapWithInput (f := fun x Λ ↦ core c (scaledIn c x Λ)) guessesU_polytime
    ((core_polytime c).comp (scaledIn_polytime c))

theorem trivialSol_isNil_polytime :
    ComputableInPolyTime (fun x ↦ decide (trivialSol x = [])) encRaw encBool :=
  ((listIsEmpty (encA := encNat)).comp trivialSol_polytime).of_enc_eq fun x ↦ by
    change encBool (decide (trivialSol x = [])) = encBool (trivialSol x).isEmpty
    cases trivialSol x <;> rfl

theorem algMain_polytime (c : Consts) :
    ComputableInPolyTime (algMain c) encCoreIn (encList encNat) := by
  have hT := trivialSol_polytime.comp rawU_raw_polytime
  have hle : ComputableInPolyTime
      (fun x ↦ decide ((trivialSol x).length ≤ x.k + bcomp c x.n)) encCoreIn encBool :=
    binary_le' (unary_to_binary.comp ((length_list _).comp hT))
      ((bcompBound_polytime c).comp rawU_raw_polytime)
  have hbest := Combine.best_polytime (raw_n_polytime.comp rawU_raw_polytime)
    (raw_m_polytime.comp rawU_raw_polytime) ((kR_polytime c).comp rawU_raw_polytime)
    (raw_table_polytime.comp rawU_raw_polytime) (coreRuns_polytime c)
  exact ite_decide (trivialSol_isNil_polytime.comp rawU_raw_polytime) (const [0])
    (ite_decide hle hT hbest)

/-- The local search runs only if the trivial solution has more than `k` facilities, so `k` is
at most the number of rows of the table. -/
theorem algLS_eq (x : Raw) : algLS x =
    if trivialSol x = [] then [0] else if (trivialSol x).length ≤ x.k then trivialSol x
    else if x.k ≤ x.table.length then Stable.localSearch lsN x (lsBudget x) else [] := by
  unfold algLS
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rfl
  · have := PT.length_trivialSol_le x
    omega

theorem algLS_polytime : ComputableInPolyTime algLS encRaw (encList encNat) := by
  have hle : ComputableInPolyTime (fun x ↦ decide ((trivialSol x).length ≤ x.k)) encRaw encBool :=
    binary_le' (unary_to_binary.comp ((length_list _).comp trivialSol_polytime)) raw_k_polytime
  rw [show algLS = _ from funext algLS_eq]
  exact ite_decide trivialSol_isNil_polytime (const [0])
    (ite_decide hle trivialSol_polytime localSearch_polytime)

theorem toRaw_polytime : ComputableInPolyTime toRaw encInstance encRaw :=
  of_eq fun I ↦ (encInstance_eq I).symm

theorem m_le_length (I : Instance) : I.m ≤ (encInstance I).length := by
  have h : (distTable I).length ≤
      (Encoding.encList (Encoding.encList encRat) (distTable I)).length :=
    length_le_length_encList _ _
  have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
  rw [Combine.length_encInstance]
  omega

/-- The tuple of an instance, with `n` and `m` in unary. -/
theorem toRawU_polytime : ComputableInPolyTime toRaw encInstance encCoreIn :=
  (binary_to_unary_bounded (raw_n_polytime.comp toRaw_polytime) (encoding_length encInstance)
    fun I ↦ Combine.n_le_length I).prod
  ((binary_to_unary_bounded (raw_m_polytime.comp toRaw_polytime) (encoding_length encInstance)
    m_le_length).prod ((raw_k_polytime.comp toRaw_polytime).prod
      (raw_table_polytime.comp toRaw_polytime)))

/-- **The algorithm for `ε` runs in polynomial time.** -/
theorem algFor_polytime (ε : ℝ) :
    ComputableInPolyTime (fun I ↦ algFor ε (toRaw I)) encInstance encCenters := by
  unfold algFor
  split_ifs
  · exact algLS_polytime.comp toRaw_polytime
  · exact (algMain_polytime _).comp toRawU_polytime

end BCFGJPSSV26.Greedy
