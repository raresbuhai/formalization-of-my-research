module

public import BS23.SmallRadius.PolyTimeProg
public import BS23.Colinear.PolyTime

/-!
# The small-radius algorithm as a list program in polynomial time

`BS23.SmallRadius.PT.srCoreL` computes the algorithm `BS23.SmallRadius.srCore` of
[BS23, Theorem 1.3] on an input `x`, coins `c` and a unary budget `Lb`
(`BS23.SmallRadius.PT.srCoreL_eq`), and it runs in polynomial time in the length of `(x, Lb, c)`
with `Lb` in unary (`BS23.SmallRadius.PT.srCoreL_polytime`).

* **The guard.** The numeric guard compares `(d+1)^e` and `2^e` with `n` for the exponent
  `e = min (n + 1) (4t)` (`BS23.SmallRadius.PT.guardL`), which decides the same as
  `BS23.SmallRadius.numGuardB` (`BS23.SmallRadius.PT.guardL_eq`) and only computes numbers of
  `O(n log d)` bits. The leading principal minors of the second moment are integer determinants
  of the leading blocks of the scaled table (complexitylib's polynomial-time `detRows`), which
  have the signs of the minors (`BS23.SmallRadius.PT.leadPosL_iff`).
* **The whitening** (`BS23.SmallRadius.PT.whitenL`) reuses the list programs of the colinear
  algorithm for the second moment and its orthogonal basis (by determinants); the powers
  `2^{-⌊log₄ q⌋}` are computed with base-`2` logarithms (`BS23.SmallRadius.PT.wScaleL`).
* **The rounds** (`BS23.SmallRadius.PT.roundL`) build the program of
  [PolyTimeProg.lean](PolyTimeProg.lean) on the remaining points, call the solver with the unary
  budget, read the moments and pick the pivot over lists (`BS23.SmallRadius.PT.pickL`). The
  parameters (`BS23.SmallRadius.PT.parL`) use `min n t` and `min n m` instead of the degrees `t`
  and `m`, which are equal on the guard (`BS23.SmallRadius.PT.parL_eq`), so that every degree is
  at most `n` in unary.
* **The peeling** (`BS23.SmallRadius.PT.peelL`) is a fold over `min n k` rounds of a state
  `(Rem, labels)`, whose size stays polynomial: `Rem` is a list of at most `n` indices below `n`
  and the labels are `n` numbers at most the number of rounds.
-/

@[expose] public section

namespace BS23.SmallRadius.PT

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg Matrix
open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open BS23.Colinear BS23.Colinear.PT
open Cslib (rowEntry tabulateTable rowEntry_tabulateTable_of_lt)
open Cslib.Circuits.Rational (detRows detRows_eq_det_of_rowEntry)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The whitening -/

/-- `2^{-⌊log₄ q⌋}`, with base-`2` logarithms. -/
def wScaleL (q : ℚ) : ℚ :=
  if 1 ≤ q then ((2 : ℚ) ^ (Nat.log 2 ⌊q⌋₊ / 2))⁻¹ else (2 : ℚ) ^ ((Nat.clog 2 ⌈q⁻¹⌉₊ + 1) / 2)

theorem wScaleL_eq (q : ℚ) : wScaleL q = (2 : ℚ) ^ (-Int.log 4 q) := by
  rw [wScaleL, Int.log]
  split_ifs
  · rw [_root_.zpow_neg, zpow_natCast, log_four]
  · rw [neg_neg, zpow_natCast, clog_four]

/-- The whitened, re-rounded table of the `n` points `P` in dimension `d`, as
`BS23.SmallRadius.whitenData p`. -/
def whitenL (p n d : ℕ) (P : List (List ℚ)) : List (List ℚ) :=
  (List.range n).map fun j => (List.range d).map fun a =>
    reRound p ((n : ℚ) ^ 2)
      (wScaleL (quadL d (covL n d P) ((basisL d (covL n d P)).getD a [])) *
        dotL d ((basisL d (covL n d P)).getD a []) (P.getD j []))

variable {n d : ℕ}

/-- The table `covL n d P` of the points themselves is their second moment. -/
theorem secondMoment_rep {P : List (List ℚ)} {Y : Fin n → Fin d → ℚ} (hP : RepT P Y) :
    RepT (covL n d P) (secondMoment Y) :=
  repT_map_range _ _ fun a b => by
    rw [secondMoment_apply, sum_fin_eq_list (fun j => Y j a * Y j b)
      (fun j => ent P j a * ent P j b) fun j => by rw [hP j a, hP j b]]

theorem whitenData_apply (p : ℕ) (Y : Fin n → Fin d → ℚ) (j : Fin n) (a : Fin d) :
    whitenData p Y j a = reRound p ((n : ℚ) ^ 2) ((2 : ℚ) ^ whitenExp (secondMoment Y) a *
      (basisVec (secondMoment Y) a ⬝ᵥ Y j)) := by
  simp only [whitenData, whitenMat, whitenRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- **The whitened table.** -/
theorem whitenL_rep (p : ℕ) {P : List (List ℚ)} {Y : Fin n → Fin d → ℚ} (hP : RepT P Y) :
    RepT (whitenL p n d P) (whitenData p Y) := by
  have hC := secondMoment_rep hP
  have hB := basisL_rep hC
  unfold whitenL
  refine repT_map_range _ _ fun j a => ?_
  rw [quadL_eq hC (hB.row a), dotL_eq (hB.row a) (hP.row j), wScaleL_eq, whitenData_apply]
  rfl

/-! ### The guard -/

/-- The leading `(i + 1) × (i + 1)` block of an integer table. -/
def leadRows (S : List (List ℤ)) (i : ℕ) : List (List ℤ) :=
  tabulateTable (i + 1) (i + 1) fun r c => rowEntry S r c

/-- All leading principal minors of the table `C` are positive, by integer determinants of the
leading blocks of the scaled table. -/
def leadPosL (d : ℕ) (C : List (List ℚ)) : Bool :=
  (List.range d).all fun i => decide (0 < detRows (leadRows (SoS.PDTestRat.scale C) i))

theorem detRows_leadRows {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} (hC : RepT C M)
    (i : Fin d) :
    (detRows (leadRows (SoS.PDTestRat.scale C) i) : ℚ) =
      (SoS.PDTestRat.commonDen C : ℚ) ^ (i.val + 1) * (lead M i).det := by
  set D := SoS.PDTestRat.commonDen C
  set N : Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℤ := Matrix.of fun r c =>
    rowEntry (SoS.PDTestRat.scale C) r c
  have h1 : detRows (leadRows (SoS.PDTestRat.scale C) i) = N.det :=
    detRows_eq_det_of_rowEntry N (by simp [leadRows]) fun r c => by
      rw [leadRows, rowEntry_tabulateTable_of_lt _ r.2 c.2]
      rfl
  have h2 : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • lead M i := by
    ext r c
    simp only [Matrix.map_apply, N, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [SoS.PDTestRat.rowEntry_scale]
    congr 1
    exact hC (Fin.castLE i.isLt r) (Fin.castLE i.isLt c)
  rw [h1, Int.cast_det, h2, det_smul, Fintype.card_fin]

/-- **The leading minors** have the signs of the integer determinants. -/
theorem leadPosL_iff {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} (hC : RepT C M) :
    leadPosL d C = true ↔ LeadMinorsPos M := by
  rw [leadPosL, List.all_eq_true, LeadMinorsPos]
  have hD : (0 : ℚ) < SoS.PDTestRat.commonDen C := by
    exact_mod_cast SoS.PDTestRat.commonDen_pos C
  constructor
  · intro h i
    have h1 := h i (List.mem_range.2 i.2)
    rw [decide_eq_true_iff] at h1
    have h2 : (0 : ℚ) < detRows (leadRows (SoS.PDTestRat.scale C) i) := by exact_mod_cast h1
    rw [detRows_leadRows hC i] at h2
    exact pos_of_mul_pos_right h2 (pow_pos hD _).le
  · intro h i hi
    rw [decide_eq_true_iff]
    have h2 := detRows_leadRows hC ⟨i, List.mem_range.1 hi⟩
    have h3 : (0 : ℚ) < detRows (leadRows (SoS.PDTestRat.scale C) i) := by
      rw [h2]
      exact mul_pos (pow_pos hD _) (h _)
    exact_mod_cast h3

/-- **The numeric guard**, with the exponent `min (n + 1) (4t)` in place of `4t`. -/
def guardL (k : ℕ) (w R : ℚ) (n d : ℕ) : Bool :=
  decide (2 ≤ k) && decide (1 ≤ d) && decide (2 ^ 20 ≤ n) &&
    decide ((d + 1) ^ min (n + 1) (4 * tDeg w R) ≤ n) &&
    decide (2 ^ min (n + 1) (4 * tDeg w R) ≤ n) && decide (k ≤ n)

theorem pow_min_le_iff (b n e : ℕ) : (b + 1) ^ min (n + 1) e ≤ n ↔ (b + 1) ^ e ≤ n := by
  rcases le_total e (n + 1) with h | h
  · rw [min_eq_right h]
  · rw [min_eq_left h]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h1 : n < (b + 1) ^ (n + 1) :=
        calc n < 2 ^ n := Nat.lt_two_pow_self
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ (b + 1) ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
      have h2 : (b + 1) ^ (n + 1) ≤ (b + 1) ^ e := Nat.pow_le_pow_right (by omega) h
      constructor <;> intro h' <;> omega

theorem two_pow_min_le_iff (n e : ℕ) : 2 ^ min (n + 1) e ≤ n ↔ 2 ^ e ≤ n :=
  pow_min_le_iff 1 n e

theorem guardL_iff {k : ℕ} {w R : ℚ} {n d : ℕ} : guardL k w R n d = true ↔ NumGuard k w R n d := by
  rw [numGuard_iff, ← pow_min_le_iff d n (4 * tDeg w R), ← two_pow_min_le_iff n (4 * tDeg w R)]
  simp only [guardL, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem guardL_eq (k : ℕ) (w R : ℚ) (n d : ℕ) : guardL k w R n d = numGuardB k w R n d :=
  Bool.eq_iff_iff.2 (guardL_iff.trans (numGuardB_iff k w R n d).symm)

/-! ### The parameters -/

/-- The parameters of the rounds, with `min n t` and `min n m` for the degrees `t` and `m`. -/
def parL (w R : ℚ) (n Lb : ℕ) : RoundPar :=
  ⟨sDeg w, min n (tDeg w R), min n (mDeg w R),
    (((256 * sDeg w) ^ min n (tDeg w R) : ℕ) : ℚ), (ballBd n : ℚ), Lb, coinBits n, n⟩

/-- On the guard, `t ≤ n`. -/
theorem tDeg_le_of_numGuard {k : ℕ} {w R : ℚ} {n d : ℕ} (hG : NumGuard k w R n d) :
    tDeg w R ≤ n :=
  (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans hG.tpow_le

/-- **On the guard, the parameters are those of the algorithm.** -/
theorem parL_eq {k : ℕ} {w R : ℚ} {n d : ℕ} (hG : NumGuard k w R n d) (Lb : ℕ) :
    parL w R n Lb = srPar w R n Lb := by
  have ht := tDeg_le_of_numGuard hG
  have hm : mDeg w R ≤ n := (Nat.div_le_self _ _).trans ht
  simp only [parL, srPar, Kc, min_eq_right ht, min_eq_right hm]

/-! ### The pick -/

/-- The weighted pick over a list of weights, as `BS23.SmallRadius.pick`. -/
def pickL (ω : List ℚ) (b u : ℕ) : ℕ :=
  ((List.range ω.length).find? fun i =>
    decide ((u : ℚ) * ω.sum < 2 ^ b * (ω.take (i + 1)).sum)).getD 0

theorem pickL_eq {N : ℕ} [NeZero N] (ω : Fin N → ℚ) (b u : ℕ) :
    pickL (List.ofFn ω) b u = (pick ω b u : ℕ) := by
  set q : ℕ → Bool := fun i =>
    decide ((u : ℚ) * (List.ofFn ω).sum < 2 ^ b * ((List.ofFn ω).take (i + 1)).sum) with hq
  have hp : (fun i : Fin N => decide ((u : ℚ) * ∑ j, ω j < 2 ^ b * partialW ω (i + 1))) =
      q ∘ Fin.val := by
    funext i
    simp only [hq, Function.comp_apply, List.sum_ofFn, List.sum_take_ofFn, partialW]
    rfl
  rw [pickL, List.length_ofFn, pick, hp, Fin.find?_eq_find?_finRange,
    ← List.map_coe_finRange_eq_range, List.find?_map]
  cases (List.finRange N).find? (q ∘ Fin.val) <;> simp

/-! ### One round -/

/-- The rows of the points of `Rem`. -/
def remL (Z : List (List ℚ)) (Rem : List ℕ) : List (List ℚ) := Rem.map fun i => Z.getD i []

/-- The layout of the program of the round on `Rem`. -/
def layR (Q : RoundPar) (d : ℕ) (Rem : List ℕ) : Lay := lay Rem.length d Q.s Q.t Q.Lb

/-- The program of the round on `Rem`. -/
def probR (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (Rem : List ℕ) : Problem :=
  problemL Rem.length d (remL Z Rem) bR Q.s Q.t Q.m Q.K Q.Bd Q.Lb

/-- The solver output of the round on `Rem`. -/
def outL (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (Rem : List ℕ) : RawPoly :=
  SoS.Core.core ((probR Q d Z bR Rem, accOf Q.ne (probR Q d Z bR Rem),
    accOf Q.ne (probR Q d Z bR Rem)), Q.Lb)

/-- The pivot of the round on `Rem`, for the coin value `u`. -/
def pivL (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (Rem : List ℕ) (u : ℕ) : ℕ :=
  pickL ((List.range Rem.length).map fun i =>
    max (mwRead (layR Q d Rem).N (outL Q d Z bR Rem) i) 0) Q.nb u

/-- **One round as a list program**: the points of `Rem` extracted by the round, as
`BS23.SmallRadius.srRound`. -/
def roundL (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (Rem : List ℕ) (u : ℕ) :
    List ℕ :=
  if Rem.length = 0 then [] else
    ((List.range Rem.length).filter fun i => decide
      (mwRead (layR Q d Rem).N (outL Q d Z bR Rem) (pivL Q d Z bR Rem u) ≤
        2 * mwwRead (layR Q d Rem).N (outL Q d Z bR Rem) (pivL Q d Z bR Rem u) i)).map
      fun i => Rem.getD i 0

theorem remL_rep {z : Fin n → Fin d → ℚ} {Z : List (List ℚ)} (hZ : RepT Z z) (Rem : List (Fin n)) :
    RepT (remL Z (Rem.map Fin.val)) (remPts z Rem) := fun i a => by
  have h : (remL Z (Rem.map Fin.val)).getD i [] = Z.getD (Rem.get i) [] := by
    rw [remL, List.map_map, List.getD_eq_getElem _ _ (by simp), List.getElem_map]
    rfl
  rw [ent, h]
  exact hZ (Rem.get i) a

/-- **The list round computes the round.** -/
theorem roundL_eq (Q : RoundPar) {z : Fin n → Fin d → ℚ} {Z : List (List ℚ)} (hZ : RepT Z z)
    (bR : RawPoly) (Rem : List (Fin n)) (u : ℕ) :
    roundL Q d Z bR (Rem.map Fin.val) u =
      (srRound Q z (SoS.Poly.coeff d bR) Rem u).map Fin.val := by
  have hP : probR Q d Z bR (Rem.map Fin.val) = roundProb Q z (SoS.Poly.coeff d bR) Rem := by
    unfold probR
    rw [List.length_map, problemL_eq (remL_rep hZ Rem)]
    rfl
  have hout : outL Q d Z bR (Rem.map Fin.val) = roundOut Q z (SoS.Poly.coeff d bR) Rem := by
    unfold outL
    rw [hP]
    rfl
  have hN : (layR Q d (Rem.map Fin.val)).N = (remLay Q Rem d).N := by
    unfold layR
    rw [List.length_map]
  by_cases h : Rem.length = 0
  · rw [srRound_of_length_eq_zero _ _ _ _ h]
    simp only [roundL, List.length_map, h, ↓reduceIte, List.map_nil]
  · have : NeZero Rem.length := ⟨h⟩
    simp only [roundL, List.length_map, h, ↓reduceIte]
    rw [srRound_eq]
    have hpiv : pivL Q d Z bR (Rem.map Fin.val) u =
        (pick (fun i : Fin Rem.length =>
          max (mwRead (remLay Q Rem d).N (roundOut Q z (SoS.Poly.coeff d bR) Rem) i) 0)
          Q.nb u : ℕ) := by
      unfold pivL
      rw [hout, hN, List.length_map, ← pickL_eq]
      congr 1
      exact (ofFn_eq_map_range _ _ fun _ => rfl).symm
    rw [hpiv, hout, hN, ← List.map_coe_finRange_eq_range, List.filter_map,
      List.map_map, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp

/-! ### The peeling -/

/-- The coin value of round `r`, as `BS23.SmallRadius.blockNat`. -/
def blockL (c : List Bool) (b r : ℕ) : ℕ :=
  ((List.range b).map fun t => if c.getD (r * b + t) false then 2 ^ t else 0).sum

theorem blockL_eq (c : List Bool) (b r : ℕ) : blockL c b r = blockNat c b r := by
  rw [blockL, blockNat, Sampling.chunkVal, sum_range_eq_list]

/-- **One round of the peeling** on the state `(Rem, labels)`: the points extracted in round `r`
leave `Rem` and get label `r`. -/
def peelStepL (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (c : List Bool)
    (st : List ℕ × List ℕ) (r : ℕ) : List ℕ × List ℕ :=
  (st.1.filter fun i => decide (i ∉ roundL Q d Z bR st.1 (blockL c Q.nb r)),
    (List.range Q.ne).map fun i =>
      if i ∈ roundL Q d Z bR st.1 (blockL c Q.nb r) then r else st.2.getD i 0)

/-- The initial state: all `n` points remain, with label `0`. -/
def initL (n : ℕ) : List ℕ × List ℕ := (List.range n, List.replicate n 0)

/-- **The labels after `K` rounds of peeling.** -/
def peelL (Q : RoundPar) (d : ℕ) (Z : List (List ℚ)) (bR : RawPoly) (c : List Bool) (K : ℕ) :
    List ℕ :=
  ((List.range K).foldl (peelStepL Q d Z bR c) (initL Q.ne)).2

theorem mem_map_val_iff {C : List (Fin n)} {i : Fin n} : (i : ℕ) ∈ C.map Fin.val ↔ i ∈ C := by
  simp [Fin.val_inj]

/-- **The list peeling computes the peeling**, round by round. -/
theorem foldl_peelStepL (Q : RoundPar) (hQ : Q.ne = n) {z : Fin n → Fin d → ℚ}
    {Z : List (List ℚ)} (hZ : RepT Z z) (bR : RawPoly) (c : List Bool) :
    ∀ r, (List.range r).foldl (peelStepL Q d Z bR c) (initL Q.ne) =
      ((peelRem Q z (SoS.Poly.coeff d bR) (blockNat c Q.nb) r).map Fin.val,
        List.ofFn (peelLab Q z (SoS.Poly.coeff d bR) (blockNat c Q.nb) r))
  | 0 => by
    rw [List.range_zero, List.foldl_nil, peelRem_zero, peelLab_zero, initL, hQ,
      List.map_coe_finRange_eq_range, List.ofFn_const]
  | r + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_peelStepL Q hQ hZ bR c r, List.foldl_cons,
      List.foldl_nil, peelStepL, blockL_eq, roundL_eq Q hZ, peelRem_succ]
    have hC : srRound Q z (SoS.Poly.coeff d bR)
        (peelRem Q z (SoS.Poly.coeff d bR) (blockNat c Q.nb) r) (blockNat c Q.nb r) =
        peelC Q z (SoS.Poly.coeff d bR) (blockNat c Q.nb) r := rfl
    rw [hC]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun i _ => ?_
      simp only [Function.comp_apply, mem_map_val_iff]
    · dsimp only
      rw [hQ]
      refine (ofFn_eq_map_range _ _ fun i => ?_).symm
      rw [peelLab_succ, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp only [mem_map_val_iff]

/-! ### The algorithm -/

/-- **The algorithm as a list program**, on the input `x`, the coins `c` and the budget `Lb`. -/
def srCoreL (x : RadiusInput) (c : List Bool) (Lb : ℕ) : List ℕ :=
  if guardL x.k x.wmin x.R x.points.length (dim x.points) &&
      leadPosL (dim x.points) (covL x.points.length (dim x.points) x.points) then
    peelL (parL x.wmin x.R x.points.length Lb) (dim x.points)
      (whitenL (gridPrec x.R x.points.length (dim x.points)) x.points.length (dim x.points)
        x.points)
      (bRawL x.points.length (dim x.points)
        (whitenL (gridPrec x.R x.points.length (dim x.points)) x.points.length (dim x.points)
          x.points)
        (min x.points.length (tDeg x.wmin x.R)) Lb) c (min x.points.length x.k)
  else List.replicate x.points.length 0

/-- **The list program computes the algorithm.** -/
theorem srCoreL_eq (x : RadiusInput) (c : List Bool) (Lb : ℕ) : srCoreL x c Lb = srCore x c Lb := by
  have hY : RepT x.points (pointsFun x.points) := ent_pointsFun x.points
  have hg : (guardL x.k x.wmin x.R x.points.length (dim x.points) &&
      leadPosL (dim x.points) (covL x.points.length (dim x.points) x.points)) =
      guardB x.k x.wmin x.R (pointsFun x.points) := by
    rw [guardB, guardL_eq]
    congr 1
    exact Bool.eq_iff_iff.2 ((leadPosL_iff (secondMoment_rep hY)).trans decide_eq_true_iff.symm)
  rw [srCoreL, srCore, srLabels, hg]
  split_ifs with h
  · obtain ⟨hG, -⟩ := guardB_iff.1 h
    have hZ := whitenL_rep (gridPrec x.R x.points.length (dim x.points)) hY
    rw [min_eq_right (tDeg_le_of_numGuard hG), min_eq_right hG.k_le, parL_eq hG,
      bRawL_eq hZ, peelL, foldl_peelStepL _ rfl hZ]
    rfl
  · exact (List.ofFn_const _ _).symm

/-! ### Polynomial time: the whitening and the guard -/

theorem wScaleL' {q : α → ℚ} (hq : ComputableInPolyTime q input encRat) :
    ComputableInPolyTime (fun a => wScaleL (q a)) input encRat := by
  unfold wScaleL
  exact ite_prop (rat_le' (const 1) hq)
    (rat_inv' (rat_two_pow' ((unary_div_const 2).comp (binary_log_two.comp (rat_natFloor' hq)))))
    (rat_two_pow' ((unary_div_const 2).comp
      (unary_add' (binary_clog_two.comp (rat_natCeil' (rat_inv' hq))) (const 1))))

theorem reRound' {p : α → ℕ} {B x : α → ℚ} (hp : ComputableInPolyTime p input encUnary)
    (hB : ComputableInPolyTime B input encRat) (hx : ComputableInPolyTime x input encRat) :
    ComputableInPolyTime (fun a => reRound (p a) (B a) (x a)) input encRat := by
  unfold reRound clampAbs
  exact rat_div' (rat_intCast' (rat_floor' (rat_mul' (rat_two_pow' hp)
    (rat_max' (rat_neg' hB) (rat_min' hB hx))))) (rat_two_pow' hp)

theorem whitenL' {p n d : α → ℕ} {P : α → List (List ℚ)}
    (hp : ComputableInPolyTime p input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun a => whitenL (p a) (n a) (d a) (P a)) input encM := by
  unfold whitenL
  have h1 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => q.1.1)
      (encPair (encPair input encUnary) encUnary) input := (fst _ _).comp (fst _ _)
  have hn2 := hn.comp h1
  have hd2 := hd.comp h1
  have hP2 := hP.comp h1
  have hC2 := covL' hn2 hd2 hP2
  have hBa := row' (basisL' hd2 hC2) (snd _ _)
  exact mapWithInput (range.comp hn) (mapWithInput (range.comp (hd.comp (fst _ _)))
    (reRound' (hp.comp h1) (rat_sq' (rat_ofUnary hn2)) (rat_mul' (wScaleL' (quadL' hd2 hC2 hBa))
      (dotL' hd2 hBa (row' hP2 ((snd _ _).comp (fst _ _)))))))

theorem leadRows_polytime : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => leadRows p.1 p.2)
    (encPair SoS.PDTestRows.encRows encUnary) SoS.PDTestRows.encRows := by
  unfold leadRows
  fun_prop

theorem leadPosL' {d : α → ℕ} {C : α → List (List ℚ)} (hd : ComputableInPolyTime d input encUnary)
    (hC : ComputableInPolyTime C input encM) :
    ComputableInPolyTime (fun a => leadPosL (d a) (C a)) input encBool := by
  unfold leadPosL
  have hS : ComputableInPolyTime (fun p : α × ℕ => SoS.PDTestRat.scale (C p.1))
      (encPair input encUnary) SoS.PDTestRows.encRows :=
    SoS.PDTestRat.scale_polytime.comp (hC.comp (fst _ _))
  have hL : ComputableInPolyTime (fun p : α × ℕ => leadRows (SoS.PDTestRat.scale (C p.1)) p.2)
      (encPair input encUnary) SoS.PDTestRows.encRows :=
    leadRows_polytime.comp (g := fun p : α × ℕ => (SoS.PDTestRat.scale (C p.1), p.2))
      (hS.prod (snd _ _))
  exact .of_tidy (ComputableTidilyInPolyTime.allWithInput (range.comp hd).tidy
    (intLt' (const 0) (SoS.PDTestRows.detRows' hL)).tidy)

theorem clog2' {f : α → ℕ} (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => Nat.clog 2 (f a)) input encUnary :=
  binary_clog_two.comp hf

theorem twoPow' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a => 2 ^ f a) input encNat :=
  binary_two_pow.comp hf

theorem sq' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a => f a ^ 2) input encUnary :=
  (unary_pow 2).comp hf

theorem sDeg' {w : α → ℚ} (hw : ComputableInPolyTime w input encRat) :
    ComputableInPolyTime (fun a => sDeg (w a)) input encUnary :=
  unary_pow_clog_const (unary_add' (logInv' hw) (const 8)) 2 2

theorem maxB' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a => max (f a) (g a)) input encNat := by
  have e : (fun a => max (f a) (g a)) = fun a => if f a ≤ g a then g a else f a :=
    funext fun a => max_def _ _
  rw [e]
  exact ite_prop (binary_le' hf hg) hg hf

/-- The degree `t`, in binary. -/
theorem tDeg' {w R : α → ℚ} (hw : ComputableInPolyTime w input encRat)
    (hR : ComputableInPolyTime R input encRat) :
    ComputableInPolyTime (fun a => tDeg (w a) (R a)) input encNat := by
  have h0 : ComputableInPolyTime (fun a => 4 * ⌈R a ^ 2⌉₊ + 4) input encNat :=
    binAdd' (binary_mul' (const 4) (rat_natCeil' (rat_sq' hR))) (const 4)
  have h1 : ComputableInPolyTime (fun a => max (sDeg (w a)) (4 * ⌈R a ^ 2⌉₊ + 4)) input encNat :=
    maxB' (toBinary' (sDeg' hw)) h0
  have h2 : ComputableInPolyTime (fun a => Nat.clog 2 (max (sDeg (w a)) (4 * ⌈R a ^ 2⌉₊ + 4)))
      input encUnary := clog2' h1
  unfold tDeg tExp
  exact twoPow' h2

theorem guardL' {k n d : α → ℕ} {w R : α → ℚ} (hk : ComputableInPolyTime k input encNat)
    (hw : ComputableInPolyTime w input encRat) (hR : ComputableInPolyTime R input encRat)
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary) :
    ComputableInPolyTime (fun a => guardL (k a) (w a) (R a) (n a) (d a)) input encBool := by
  unfold guardL
  have he : ComputableInPolyTime (fun a => min (n a + 1) (4 * tDeg (w a) (R a))) input
      encUnary := binary_min_unary' (unary_add' hn (const 1)) (binary_mul' (const 4) (tDeg' hw hR))
  have hnB := toBinary' hn
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (binary_le' (const 2) hk)
    (binary_le' (const 1) (toBinary' hd))) (binary_le' (const _) hnB))
    (binary_le' (binary_pow' (toBinary' (unary_add' hd (const 1))) he) hnB))
    (binary_le' (binary_pow' (const 2) he) hnB)) (binary_le' hk hnB)

theorem gridPrec' {R : α → ℚ} {n d : α → ℕ} (hR : ComputableInPolyTime R input encRat)
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary) :
    ComputableInPolyTime (fun a => gridPrec (R a) (n a) (d a)) input encUnary := by
  unfold gridPrec
  exact unary_add' (clog2' (binary_mul' (binary_mul' (binary_mul' (const 4)
    (binAdd' (rat_natCeil' (rat_sq' hR)) (const 2))) (toBinary' (unary_add' hd (const 1))))
    (toBinary' (sq' hn)))) (const 1)

/-! ### Polynomial time: the parameters -/

/-- The fields `(s, t, m, K, Bd, Lb, nb, ne)` of the parameters. -/
abbrev encParT : ℕ × ℕ × ℕ × ℚ × ℚ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encRat (encPair encRat
    (encPair encUnary (encPair encUnary encUnary))))))

/-- The parameters of the rounds, by their fields: the numbers in unary, `K` and `Bd` as
rationals. -/
def encPar : RoundPar ↪ List Bool :=
  ⟨fun Q => encParT (Q.s, Q.t, Q.m, Q.K, Q.Bd, Q.Lb, Q.nb, Q.ne), by
    rintro ⟨s, t, m, K, Bd, Lb, nb, ne⟩ ⟨s', t', m', K', Bd', Lb', nb', ne'⟩ h
    have := encParT.injective h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
    rfl⟩

theorem parT_polytime : ComputableInPolyTime
    (fun Q : RoundPar => (Q.s, Q.t, Q.m, Q.K, Q.Bd, Q.Lb, Q.nb, Q.ne)) encPar encParT :=
  of_eq fun _ => rfl

theorem mkPar_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ × ℚ × ℚ × ℕ × ℕ × ℕ => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
      p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2⟩ : RoundPar)) encParT encPar :=
  of_eq fun _ => rfl

section ParP

variable {Q : α → RoundPar} (hQ : ComputableInPolyTime Q input encPar)
include hQ

theorem par_s' : ComputableInPolyTime (fun a => (Q a).s) input encUnary :=
  (fst _ _).comp (parT_polytime.comp hQ)

theorem par_t' : ComputableInPolyTime (fun a => (Q a).t) input encUnary :=
  (fst _ _).comp ((snd _ _).comp (parT_polytime.comp hQ))

theorem par_m' : ComputableInPolyTime (fun a => (Q a).m) input encUnary :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (parT_polytime.comp hQ)))

theorem par_K' : ComputableInPolyTime (fun a => (Q a).K) input encRat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (parT_polytime.comp hQ))))

theorem par_Bd' : ComputableInPolyTime (fun a => (Q a).Bd) input encRat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (parT_polytime.comp hQ)))))

theorem par_Lb' : ComputableInPolyTime (fun a => (Q a).Lb) input encUnary :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    ((snd _ _).comp (parT_polytime.comp hQ))))))

theorem par_nb' : ComputableInPolyTime (fun a => (Q a).nb) input encUnary :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    ((snd _ _).comp ((snd _ _).comp (parT_polytime.comp hQ)))))))

theorem par_ne' : ComputableInPolyTime (fun a => (Q a).ne) input encUnary :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    ((snd _ _).comp ((snd _ _).comp (parT_polytime.comp hQ)))))))

end ParP

theorem parL' {w R : α → ℚ} {n Lb : α → ℕ} (hw : ComputableInPolyTime w input encRat)
    (hR : ComputableInPolyTime R input encRat) (hn : ComputableInPolyTime n input encUnary)
    (hLb : ComputableInPolyTime Lb input encUnary) :
    ComputableInPolyTime (fun a => parL (w a) (R a) (n a) (Lb a)) input encPar := by
  unfold parL
  have hs := sDeg' hw
  have ht : ComputableInPolyTime (fun a => min (n a) (tDeg (w a) (R a))) input encUnary :=
    binary_min_unary' hn (tDeg' hw hR)
  have hm : ComputableInPolyTime (fun a => min (n a) (mDeg (w a) (R a))) input encUnary :=
    binary_min_unary' hn (binDiv' (tDeg' hw hR) (toBinary' hs))
  have hK : ComputableInPolyTime
      (fun a => ((((256 * sDeg (w a)) ^ min (n a) (tDeg (w a) (R a)) : ℕ)) : ℚ)) input encRat :=
    rat_natCast' (binary_pow' (binary_mul' (const 256) (toBinary' hs)) ht)
  have hBd : ComputableInPolyTime (fun a => ((ballBd (n a) : ℕ) : ℚ)) input encRat :=
    rat_natCast' (twoPow' (unary_mul' (const 4) (sq' hn)))
  exact mkPar_polytime.comp (g := fun a => (sDeg (w a), min (n a) (tDeg (w a) (R a)),
      min (n a) (mDeg (w a) (R a)), ((((256 * sDeg (w a)) ^ min (n a) (tDeg (w a) (R a)) : ℕ)) : ℚ),
      ((ballBd (n a) : ℕ) : ℚ), Lb a, coinBits (n a), n a))
    (hs.prod (ht.prod (hm.prod (hK.prod (hBd.prod (hLb.prod ((unary_add' hn (const 8)).prod
      hn)))))))

/-! ### Polynomial time: one round -/

theorem pickL' {ω : α → List ℚ} {b u : α → ℕ} (hω : ComputableInPolyTime ω input encV)
    (hb : ComputableInPolyTime b input encUnary) (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a => pickL (ω a) (b a) (u a)) input encUnary := by
  unfold pickL
  have hω1 : ComputableInPolyTime (fun p : α × ℕ => ω p.1) (encPair input encUnary) encV :=
    hω.comp (fst _ _)
  have htake : ComputableInPolyTime (fun p : α × ℕ => (ω p.1).take (p.2 + 1))
      (encPair input encUnary) encV :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hω1.tidy
      (unary_add' (snd _ _) (const 1)).tidy)
  have hfind : ComputableInPolyTime (fun a => (List.range (ω a).length).find? fun i =>
      decide ((u a : ℚ) * (ω a).sum < 2 ^ b a * ((ω a).take (i + 1)).sum)) input
      (encOption encUnary) :=
    findWithInput (range.comp ((length_list encRat).comp hω))
      (rat_lt' (rat_mul' (rat_natCast' (hu.comp (fst _ _))) (rat_sum' hω1))
        (rat_mul' (rat_two_pow' (hb.comp (fst _ _))) (rat_sum' htake)))
  exact .of_tidy (ComputableTidilyInPolyTime.optionGetDWithInput hfind.tidy (const 0).tidy)

theorem remL' {Z : α → List (List ℚ)} {Rem : α → List ℕ} (hZ : ComputableInPolyTime Z input encM)
    (hRem : ComputableInPolyTime Rem input (encList encUnary)) :
    ComputableInPolyTime (fun a => remL (Z a) (Rem a)) input encM := by
  unfold remL
  exact mapWithInput hRem (row' (hZ.comp (fst _ _)) (snd _ _))

theorem accOf' {ne : α → ℕ} {P : α → Problem} (hne : ComputableInPolyTime ne input encUnary)
    (hP : ComputableInPolyTime P input SoS.PolyTime.encProblemM) :
    ComputableInPolyTime (fun a => accOf (ne a) (P a)) input encRat := by
  unfold accOf accExp
  have hlen : ComputableInPolyTime (fun a => (encProblem (P a)).length) input encUnary := by
    simp only [BS23.Separating.PT.encProblem_eq]
    exact (encoding_length SoS.PolyTime.encProblemM).comp hP
  exact rat_div' (const 1) (rat_two_pow' (sq' (unary_add' (unary_add' hne hlen) (const 2))))

theorem mwRead' {N i : α → ℕ} {out : α → RawPoly} (hN : ComputableInPolyTime N input encUnary)
    (hout : ComputableInPolyTime out input encRaw) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => mwRead (N a) (out a) (i a)) input encRat := by
  unfold mwRead
  exact SoS.Poly.coeff' hN hout (unitExp' hN hi (const 1))

theorem pairExp' {N i j : α → ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hi : ComputableInPolyTime i input encUnary) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => pairExp (N a) (i a) (j a)) input encE := by
  unfold pairExp
  exact mapWithInput (range.comp hN)
    (binAdd' (ite_prop (decide_eq' (snd _ _) (hi.comp (fst _ _))) (const 1) (const 0))
      (ite_prop (decide_eq' (snd _ _) (hj.comp (fst _ _))) (const 1) (const 0)))

theorem mwwRead' {N i j : α → ℕ} {out : α → RawPoly} (hN : ComputableInPolyTime N input encUnary)
    (hout : ComputableInPolyTime out input encRaw) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => mwwRead (N a) (out a) (i a) (j a)) input encRat := by
  unfold mwwRead
  exact SoS.Poly.coeff' hN hout (pairExp' hN hi hj)

section RoundP

variable {Q : α → RoundPar} {d : α → ℕ} {Z : α → List (List ℚ)} {bR : α → RawPoly}
  {Rem : α → List ℕ}

theorem layR' (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary)
    (hRem : ComputableInPolyTime Rem input (encList encUnary)) :
    ComputableInPolyTime (fun a => layR (Q a) (d a) (Rem a)) input encLay :=
  lay' ((length_list encUnary).comp hRem) hd (par_s' hQ) (par_t' hQ) (par_Lb' hQ)

theorem probR' (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary)
    (hZ : ComputableInPolyTime Z input encM) (hbR : ComputableInPolyTime bR input encRaw)
    (hRem : ComputableInPolyTime Rem input (encList encUnary)) :
    ComputableInPolyTime (fun a => probR (Q a) (d a) (Z a) (bR a) (Rem a)) input
      SoS.PolyTime.encProblemM :=
  problemL' ((length_list encUnary).comp hRem) hd (remL' hZ hRem) hbR (par_s' hQ) (par_t' hQ)
    (par_m' hQ) (par_K' hQ) (par_Bd' hQ) (par_Lb' hQ)

theorem outL' (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary)
    (hZ : ComputableInPolyTime Z input encM) (hbR : ComputableInPolyTime bR input encRaw)
    (hRem : ComputableInPolyTime Rem input (encList encUnary)) :
    ComputableInPolyTime (fun a => outL (Q a) (d a) (Z a) (bR a) (Rem a)) input encRaw := by
  unfold outL
  have hP := probR' hQ hd hZ hbR hRem
  have hacc := accOf' (par_ne' hQ) hP
  exact BS23.Separating.PT.sosCore' (f := fun a => (probR (Q a) (d a) (Z a) (bR a) (Rem a),
    accOf (Q a).ne (probR (Q a) (d a) (Z a) (bR a) (Rem a)),
    accOf (Q a).ne (probR (Q a) (d a) (Z a) (bR a) (Rem a)))) (hP.prod (hacc.prod hacc))
    (par_Lb' hQ)

theorem pivL' {u : α → ℕ} (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary) (hZ : ComputableInPolyTime Z input encM)
    (hbR : ComputableInPolyTime bR input encRaw)
    (hRem : ComputableInPolyTime Rem input (encList encUnary))
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a => pivL (Q a) (d a) (Z a) (bR a) (Rem a) (u a)) input
      encUnary := by
  unfold pivL
  have hQ1 : ComputableInPolyTime (fun p : α × ℕ => Q p.1) (encPair input encUnary) encPar :=
    hQ.comp (fst _ _)
  have hd1 : ComputableInPolyTime (fun p : α × ℕ => d p.1) (encPair input encUnary) encUnary :=
    hd.comp (fst _ _)
  have hZ1 : ComputableInPolyTime (fun p : α × ℕ => Z p.1) (encPair input encUnary) encM :=
    hZ.comp (fst _ _)
  have hbR1 : ComputableInPolyTime (fun p : α × ℕ => bR p.1) (encPair input encUnary) encRaw :=
    hbR.comp (fst _ _)
  have hRem1 : ComputableInPolyTime (fun p : α × ℕ => Rem p.1) (encPair input encUnary)
      (encList encUnary) := hRem.comp (fst _ _)
  exact pickL' (mapWithInput (range.comp ((length_list encUnary).comp hRem))
    (rat_max' (mwRead' (lay_N' (layR' hQ1 hd1 hRem1)) (outL' hQ1 hd1 hZ1 hbR1 hRem1) (snd _ _))
      (const 0))) (par_nb' hQ) hu

/-- **One round runs in polynomial time.** -/
theorem roundL' {u : α → ℕ} (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary) (hZ : ComputableInPolyTime Z input encM)
    (hbR : ComputableInPolyTime bR input encRaw)
    (hRem : ComputableInPolyTime Rem input (encList encUnary))
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a => roundL (Q a) (d a) (Z a) (bR a) (Rem a) (u a)) input
      (encList encUnary) := by
  unfold roundL
  have hQ1 : ComputableInPolyTime (fun p : α × ℕ => Q p.1) (encPair input encUnary) encPar :=
    hQ.comp (fst _ _)
  have hd1 : ComputableInPolyTime (fun p : α × ℕ => d p.1) (encPair input encUnary) encUnary :=
    hd.comp (fst _ _)
  have hZ1 : ComputableInPolyTime (fun p : α × ℕ => Z p.1) (encPair input encUnary) encM :=
    hZ.comp (fst _ _)
  have hbR1 : ComputableInPolyTime (fun p : α × ℕ => bR p.1) (encPair input encUnary) encRaw :=
    hbR.comp (fst _ _)
  have hRem1 : ComputableInPolyTime (fun p : α × ℕ => Rem p.1) (encPair input encUnary)
      (encList encUnary) := hRem.comp (fst _ _)
  have hu1 : ComputableInPolyTime (fun p : α × ℕ => u p.1) (encPair input encUnary) encNat :=
    hu.comp (fst _ _)
  have hN1 := lay_N' (layR' hQ1 hd1 hRem1)
  have hout1 := outL' hQ1 hd1 hZ1 hbR1 hRem1
  have hpiv1 := pivL' hQ1 hd1 hZ1 hbR1 hRem1 hu1
  have hlen := (length_list encUnary).comp hRem
  exact ite_prop (decide_eq' hlen (const 0)) (const [])
    (mapWithInput (filterWithInput (range.comp hlen)
      (rat_le' (mwRead' hN1 hout1 hpiv1) (rat_mul' (const 2) (mwwRead' hN1 hout1 hpiv1 (snd _ _)))))
      (listGetDWithInput hRem1 (snd _ _) 0))

end RoundP

/-! ### Polynomial time: the peeling -/

theorem blockL' {c : α → List Bool} {b r : α → ℕ} (hc : ComputableInPolyTime c input encBits)
    (hb : ComputableInPolyTime b input encUnary) (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a => blockL (c a) (b a) (r a)) input encNat := by
  unfold blockL
  have hmap : ComputableInPolyTime (fun a => (List.range (b a)).map fun t =>
      if (c a).getD (r a * b a + t) false then 2 ^ t else 0) input (encList encNat) :=
    mapWithInput (range.comp hb) (ite' (bitsGetDWithInput (hc.comp (fst _ _))
      (unary_add' (unary_mul' (hr.comp (fst _ _)) (hb.comp (fst _ _))) (snd _ _)) false)
      (twoPow' (snd _ _)) (const 0))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp hmap.tidy)

/-- The data of the peeling: the parameters, the dimension, the table, `B̃` and the coins. -/
abbrev PeelPar := RoundPar × ℕ × List (List ℚ) × RawPoly × List Bool

/-- The data of the peeling, encoded. -/
abbrev encPeelPar : PeelPar ↪ List Bool :=
  encPair encPar (encPair encUnary (encPair encM (encPair encRaw encBits)))

/-- The states `(Rem, labels)` of the peeling: the indices in unary, the labels in binary. -/
abbrev encSt : List ℕ × List ℕ ↪ List Bool := encPair (encList encUnary) (encList encNat)

/-- The inputs of a step of the peeling. -/
abbrev encStepIn : (PeelPar × (List ℕ × List ℕ)) × ℕ ↪ List Bool :=
  encPair (encPair encPeelPar encSt) encUnary

theorem peelStepL_polytime : ComputableInPolyTime
    (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ =>
      peelStepL p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2.1 p.1.1.2.2.2.2 p.1.2 p.2)
    encStepIn encSt := by
  unfold peelStepL
  have hP : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1)
      encStepIn encPeelPar := (fst _ _).comp (fst _ _)
  have hQ : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1.1)
      encStepIn encPar := (fst _ _).comp hP
  have hd : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1.2.1)
      encStepIn encUnary := (fst _ _).comp ((snd _ _).comp hP)
  have hZ : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1.2.2.1)
      encStepIn encM := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hP))
  have hbR : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1.2.2.2.1)
      encStepIn encRaw := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hP)))
  have hc : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.1.2.2.2.2)
      encStepIn encBits := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hP)))
  have hRem : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.2.1)
      encStepIn (encList encUnary) := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hlab : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.1.2.2)
      encStepIn (encList encNat) := (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hr : ComputableInPolyTime (fun p : (PeelPar × (List ℕ × List ℕ)) × ℕ => p.2)
      encStepIn encUnary := snd _ _
  have hC := roundL' hQ hd hZ hbR hRem (blockL' hc (par_nb' hQ) hr)
  have hC1 := hC.comp (fst encStepIn encUnary)
  exact (filterWithInput hRem (decide_not (decide_mem hC1 (snd _ _)))).prod
    (mapWithInput (range.comp (par_ne' hQ)) (ite_prop (decide_mem hC1 (snd _ _))
      (toBinary' (hr.comp (fst _ _))) (listGetDWithInput (hlab.comp (fst _ _)) (snd _ _) 0)))

theorem getD_le_of_forall {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) (i : ℕ) : l.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h' : l[i]? with _ | x
  · simp
  · exact h x (List.mem_of_getElem? h')

theorem length_encNat_le' {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ b := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (h.trans_lt Nat.lt_two_pow_self)

/-- **The peeling runs in polynomial time**, with the number `K` of rounds in unary: the state
stays polynomial, as `Rem` lists at most `n` indices below `n` and the labels are `n` numbers at
most `K`. -/
theorem peelL' {Q : α → RoundPar} {d K : α → ℕ} {Z : α → List (List ℚ)} {bR : α → RawPoly}
    {c : α → List Bool} (hQ : ComputableInPolyTime Q input encPar)
    (hd : ComputableInPolyTime d input encUnary) (hZ : ComputableInPolyTime Z input encM)
    (hbR : ComputableInPolyTime bR input encRaw) (hc : ComputableInPolyTime c input encBits)
    (hK : ComputableInPolyTime K input encUnary) :
    ComputableInPolyTime (fun a => peelL (Q a) (d a) (Z a) (bR a) (c a) (K a)) input
      (encList encNat) := by
  unfold peelL
  have hpar : ComputableInPolyTime (fun a => ((Q a, d a, Z a, bR a, c a) : PeelPar)) input
      encPeelPar := hQ.prod (hd.prod (hZ.prod (hbR.prod hc)))
  have hinit : ComputableInPolyTime (fun a => initL (Q a).ne) input encSt := by
    unfold initL
    exact (range.comp (par_ne' hQ)).prod (replicate (par_ne' hQ) (const 0))
  have hsize : PolyBounded (fun a => (input a).length) (fun a =>
      2 * ((Q a).ne * (2 * (Q a).ne + 1)) + 1 + (Q a).ne * (2 * K a + 1)) := by
    have hne := (par_ne' hQ).polyBounded
    have hKb := hK.polyBounded
    exact (((PolyBounded.const 2).mul (hne.mul (((PolyBounded.const 2).mul hne).add
      (PolyBounded.const 1)))).add (PolyBounded.const 1)).add
      (hne.mul (((PolyBounded.const 2).mul hKb).add (PolyBounded.const 1)))
  have hfold := (foldlWith_spec (par := fun a => ((Q a, d a, Z a, bR a, c a) : PeelPar))
    (list := fun a => List.range (K a)) (init := fun a => initL (Q a).ne)
    (step := fun (P : PeelPar) st r => peelStepL P.1 P.2.1 P.2.2.1 P.2.2.2.1 P.2.2.2.2 st r)
    hpar (range.comp hK) hinit peelStepL_polytime
    (fun a _ st => (∀ i ∈ st.1, i < (Q a).ne) ∧ st.1.length ≤ (Q a).ne ∧
      st.2.length = (Q a).ne ∧ ∀ l ∈ st.2, l ≤ K a)
    (fun a => by
      refine ⟨fun i hi => List.mem_range.1 hi, by simp [initL], by simp [initL], fun l hl => ?_⟩
      rw [initL, List.mem_replicate] at hl
      omega)
    (fun a consumed st value hpre ⟨h1, h2, h3, h4⟩ => by
      have hv : value < K a := by
        have := hpre.subset (List.mem_append_right consumed (List.mem_singleton_self value))
        simpa using this
      simp only [peelStepL]
      refine ⟨fun i hi => h1 i (List.mem_filter.1 hi).1, (List.length_filter_le _ _).trans h2,
        by simp, fun l hl => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
      split_ifs
      · omega
      · exact getD_le_of_forall h4 i)
    hsize
    (fun a consumed st _ ⟨h1, h2, h3, h4⟩ => by
      rw [length_encPair]
      have e1 := length_encList_le encUnary st.1 (b := (Q a).ne) fun i hi => by
        rw [encUnary_apply, List.length_replicate]
        exact (h1 i hi).le
      have e2 := length_encList_le encNat st.2 (b := K a) fun l hl => length_encNat_le' (h4 l hl)
      rw [h3] at e2
      have e3 : st.1.length * (2 * (Q a).ne + 1) ≤ (Q a).ne * (2 * (Q a).ne + 1) :=
        Nat.mul_le_mul_right _ h2
      omega)).1
  exact (snd _ _).comp hfold

/-! ### Polynomial time: the algorithm -/

/-- The inputs `((x, Lb), c)` of the list program: the input, the unary budget and the coins. -/
abbrev encIn : (RadiusInput × ℕ) × List Bool ↪ List Bool :=
  encPair (encPair encRadiusInput encUnary) encBits

theorem radT_polytime : ComputableInPolyTime (fun x : RadiusInput => (x.k, x.wmin, x.R, x.points))
    encRadiusInput (encPair encNat (encPair encRat (encPair encRat encM))) :=
  of_eq fun _ => rfl

/-- **The list program runs in polynomial time** in the length of `((x, Lb), c)`, with the budget
`Lb` in unary. -/
theorem srCoreL_polytime : ComputableInPolyTime
    (fun y : (RadiusInput × ℕ) × List Bool => srCoreL y.1.1 y.2 y.1.2) encIn encOutput := by
  unfold srCoreL
  have hx : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool =>
      (y.1.1.k, y.1.1.wmin, y.1.1.R, y.1.1.points)) encIn
      (encPair encNat (encPair encRat (encPair encRat encM))) :=
    radT_polytime.comp ((fst _ _).comp (fst _ _))
  have hk : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.1.1.k) encIn
      encNat := (fst _ _).comp hx
  have hw : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.1.1.wmin) encIn
      encRat := (fst _ _).comp ((snd _ _).comp hx)
  have hR : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.1.1.R) encIn
      encRat := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hx))
  have hP : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.1.1.points) encIn
      encM := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hx))
  have hLb : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.1.2) encIn
      encUnary := (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun y : (RadiusInput × ℕ) × List Bool => y.2) encIn
      encBits := snd _ _
  have hn := len' hP
  have hd := dim' hP
  have hZ := whitenL' (gridPrec' hR hn hd) hn hd hP
  exact ite' (bool_and' (guardL' hk hw hR hn hd) (leadPosL' hd (covL' hn hd hP)))
    (peelL' (parL' hw hR hn hLb) hd hZ (bRawL' hn hd hZ (binary_min_unary' hn (tDeg' hw hR)) hLb)
      hc (binary_min_unary' hn hk))
    (replicate hn (const 0))

end BS23.SmallRadius.PT
