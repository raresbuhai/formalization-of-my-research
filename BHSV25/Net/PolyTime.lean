module

public import BHSV25.Net.Machine
public import Background.PolyTime.Rat
public import Background.PolyTime.Lists
public import Background.TuplesPolyTime
public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The nets are computed in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the functions of
`BHSV25/Net/Machine.lean`, ending with `BHSV25.Net.netList_polytime`.

Encodings: the number of vertices, the degree, the exponent, the range of the coefficients, the
budget and the entries of the tuples are in unary (all are polynomial in the input); matrices are
lists of rows of binary integers. The only loop is the matrix power: its states are `N × N`
matrices with entries at most `N^(2i)` after `i` steps, so their encodings have at most
`O(N³ e)` bits for the `e = O(log N)` steps (`BHSV25.Net.length_powL_le`). The number `N` of
vertices is at most the length of the table (`BHSV25.Net.numV_le`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- Matrices: lists of rows of binary integers. -/
abbrev encMat : List (List ℤ) ↪ List Bool := encList (encList encIntBin)

/-- Lists of numbers in unary. -/
abbrev encVs : List ℕ ↪ List Bool := encList encUnary

/-- The input: the number of vertices in binary and the adjacency table. -/
abbrev encIn : ℕ × List Bool ↪ List Bool := encPair encNat encBits

/-- A case distinction on a decidable proposition. -/
private theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a => decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a => if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- A unary natural, in binary. -/
private theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-! ### Reading the input -/

theorem numV_polytime : ComputableInPolyTime numV encIn encUnary :=
  binary_min_unary' (length_bits_comp (snd _ _)) (fst _ _)

@[fun_prop]
theorem numV' {f : α → ℕ × List Bool} (hf : ComputableInPolyTime f input encIn) :
    ComputableInPolyTime (fun a ↦ numV (f a)) input encUnary :=
  numV_polytime.comp hf

theorem deg_polytime : ComputableInPolyTime (fun p : ℕ × List Bool ↦ deg p.1 p.2)
    (encPair encUnary encBits) encUnary := by
  unfold deg
  exact countPWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem deg' {f : α → ℕ} {g : α → List Bool} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encBits) :
    ComputableInPolyTime (fun a ↦ deg (f a) (g a)) input encUnary :=
  deg_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### Integers -/

/-- A unary natural, as a binary integer. -/
private theorem intOfUnary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ (f a : ℤ)) input encIntBin :=
  intBin_natCast.comp (toBinary' hf)

private theorem intSub' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ f a - g a) input encIntBin :=
  intBin_sub.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

private theorem intSum' {f : α → List ℤ} (hf : ComputableInPolyTime f input (encList encIntBin)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_sum.comp hf.tidy)

/-! ### The matrix -/

theorem adjB_polytime : ComputableInPolyTime
    (fun p : (ℕ × List Bool) × ℕ × ℕ ↦ adjB p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encBits) (encPair encUnary encUnary)) encBool := by
  unfold adjB
  fun_prop

@[fun_prop]
theorem adjB' {f u v : α → ℕ} {g : α → List Bool} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encBits) (hu : ComputableInPolyTime u input encUnary)
    (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ adjB (f a) (g a) (u a) (v a)) input encBool :=
  adjB_polytime.comp (g := fun a ↦ ((f a, g a), u a, v a)) ((hf.prod hg).prod (hu.prod hv))

theorem entry_polytime (bottom : Bool) : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List Bool) × ℕ × ℕ ↦ entry bottom p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
    (encPair (encPair (encPair encUnary encUnary) encBits) (encPair encUnary encUnary))
    encIntBin := by
  unfold entry
  have hadj : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List Bool) × ℕ × ℕ ↦
      if adjB p.1.1.1 p.1.2 p.2.1 p.2.2 = true then (1 : ℤ) else 0)
      (encPair (encPair (encPair encUnary encUnary) encBits) (encPair encUnary encUnary))
      encIntBin := ite' (by fun_prop) (const 1) (const 0)
  cases bottom
  · simpa using hadj
  · simp only [ite_true]
    refine intSub' (ite_prop (by fun_prop) (intOfUnary' (by fun_prop)) (const 0)) hadj

theorem baseMat_polytime (bottom : Bool) : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List Bool ↦ baseMat bottom p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) encMat := by
  unfold baseMat
  refine mapWithInput (by fun_prop) (mapWithInput (by fun_prop) ?_)
  exact (entry_polytime bottom).comp (g := fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ ↦
    (q.1.1, q.1.2, q.2)) (by fun_prop)

theorem mulL_polytime : ComputableInPolyTime
    (fun p : (ℕ × List (List ℤ)) × List (List ℤ) ↦ mulL p.1.1 p.2 p.1.2)
    (encPair (encPair encUnary encMat) encMat) encMat := by
  unfold mulL
  refine mapWithInput (by fun_prop) (mapWithInput (by fun_prop) ?_)
  refine intSum' (mapWithInput (by fun_prop) ?_)
  fun_prop

theorem idL_polytime : ComputableInPolyTime idL encUnary encMat := by
  unfold idL
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop)
    (ite_prop (by fun_prop) (const 1) (const 0)))

/-! ### Sizes of the powers -/

/-- All entries of `X` (read with `getD`) are at most `B` in absolute value. -/
def EntBound (X : List (List ℤ)) (B : ℕ) : Prop := ∀ u w, |(X.getD u []).getD w 0| ≤ B

/-- A square list built from a function bounded by `B` has entries bounded by `B`. -/
theorem entBound_square (N B : ℕ) (F : ℕ → ℕ → ℤ) (hF : ∀ u < N, ∀ v < N, |F u v| ≤ B) :
    EntBound ((List.range N).map fun u ↦ (List.range N).map fun v ↦ F u v) B := by
  intro u w
  by_cases hu : u < N
  · rw [getD_map_range N _ _ hu]
    by_cases hw : w < N
    · rw [getD_map_range N _ _ hw]
      exact hF u hu w hw
    · rw [List.getD_eq_default _ _ (by simpa using hw)]
      simp
  · have h : ((List.range N).map fun u ↦ (List.range N).map fun v ↦ F u v).getD u [] = [] :=
      List.getD_eq_default _ _ (by simpa using hu)
    rw [h]
    simp

theorem abs_sum_mul_le {N B₁ B₂ : ℕ} {X Y : List (List ℤ)} (hX : EntBound X B₁)
    (hY : EntBound Y B₂) (u v : ℕ) :
    |((List.range N).map fun w ↦ (X.getD u []).getD w 0 * (Y.getD w []).getD v 0).sum| ≤
      ((N * B₁ * B₂ : ℕ) : ℤ) := by
  rw [sum_map_range]
  calc _ ≤ ∑ w : Fin N, |(X.getD u []).getD w 0 * (Y.getD w []).getD v 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w : Fin N, ((B₁ : ℤ) * B₂) := Finset.sum_le_sum fun w _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (hX u w) (hY w v) (abs_nonneg _) (by positivity)
    _ = ((N * B₁ * B₂ : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem entBound_mulL {N B₁ B₂ : ℕ} {X Y : List (List ℤ)} (hX : EntBound X B₁)
    (hY : EntBound Y B₂) : EntBound (mulL N X Y) (N * B₁ * B₂) :=
  entBound_square N _ _ fun u _ v _ ↦ abs_sum_mul_le hX hY u v

theorem entBound_idL (N : ℕ) : EntBound (idL N) 1 :=
  entBound_square N 1 _ fun u _ v _ ↦ by split_ifs <;> simp

theorem entBound_powL {N B : ℕ} {M : List (List ℤ)} (hM : EntBound M B) (i : ℕ) :
    EntBound ((fun X ↦ mulL N X M)^[i] (idL N)) ((N * B) ^ i) := by
  induction i with
  | zero => simpa using entBound_idL N
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have h := entBound_mulL (N := N) ih hM
    rwa [show N * (N * B) ^ i * B = (N * B) ^ (i + 1) by ring] at h

/-- The encoding of a square list with entries at most `B`. -/
theorem length_encMat_square_le (N B : ℕ) (F : ℕ → ℕ → ℤ)
    (hF : ∀ u < N, ∀ v < N, |F u v| ≤ B) :
    (encMat ((List.range N).map fun u ↦ (List.range N).map fun v ↦ F u v)).length ≤
      N * (2 * (N * (2 * (B.size + 1) + 1)) + 1) := by
  have hrow : ∀ u < N, (encList encIntBin ((List.range N).map fun v ↦ F u v)).length ≤
      N * (2 * (B.size + 1) + 1) := by
    intro u hu
    refine (length_encList_le encIntBin _ (b := B.size + 1) fun z hz ↦ ?_).trans (by simp)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hz
    rw [length_encIntBin]
    have h1 := hF u hu v (List.mem_range.1 hv)
    have h2 : (F u v).natAbs ≤ B := by
      rw [Int.abs_eq_natAbs] at h1
      exact_mod_cast h1
    have := Nat.size_le_size h2
    omega
  refine (length_encList_le _ _ (b := N * (2 * (B.size + 1) + 1)) fun r hr ↦ ?_).trans
    (by simp)
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
  exact hrow u (List.mem_range.1 hu)

theorem size_pow_le (N i : ℕ) : ((N * N) ^ i).size ≤ 2 * i * N + 1 := by
  refine Nat.size_le.2 ?_
  have h1 : N * N < 2 ^ (2 * N) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul'' N.lt_two_pow_self N.lt_two_pow_self
  calc (N * N) ^ i ≤ (2 ^ (2 * N)) ^ i := Nat.pow_le_pow_left h1.le i
    _ = 2 ^ (2 * i * N) := by rw [← pow_mul]; ring_nf
    _ < 2 ^ (2 * i * N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- **The states of the matrix power are small**: after `i` steps, an `N × N` matrix with
entries at most `(N B)^i`, here with `B = N`. -/
theorem length_powL_le {N : ℕ} {M : List (List ℤ)} (hM : EntBound M N) (i : ℕ) :
    (encMat ((fun X ↦ mulL N X M)^[i] (idL N))).length ≤
      N * (2 * (N * (2 * (2 * i * N + 2) + 1)) + 1) := by
  have hsq : ∀ F : ℕ → ℕ → ℤ, (∀ u < N, ∀ v < N, |F u v| ≤ ((N * N) ^ i : ℕ)) →
      (encMat ((List.range N).map fun u ↦ (List.range N).map fun v ↦ F u v)).length ≤
        N * (2 * (N * (2 * (2 * i * N + 2) + 1)) + 1) := by
    intro F hF
    refine (length_encMat_square_le N _ F hF).trans ?_
    have h1 := size_pow_le N i
    have h2 : 2 * (((N * N) ^ i).size + 1) + 1 ≤ 2 * (2 * i * N + 2) + 1 := by omega
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)) _)
  cases i with
  | zero =>
    refine hsq _ fun u _ v _ ↦ ?_
    split_ifs <;> simp
  | succ i =>
    rw [Function.iterate_succ_apply']
    refine hsq _ fun u _ v _ ↦ ?_
    have h := abs_sum_mul_le (N := N) (entBound_powL (N := N) hM i) hM u v
    rwa [show N * (N * N) ^ i * N = (N * N) ^ (i + 1) by ring] at h

theorem deg_le (N : ℕ) (tab : List Bool) : deg N tab ≤ N := by
  unfold deg
  exact (List.countP_le_length).trans (by simp)

theorem entBound_baseMat (bottom : Bool) {N d : ℕ} (tab : List Bool) (hd : d ≤ N) :
    EntBound (baseMat bottom N d tab) N := by
  refine entBound_square N N _ fun u hu v _ ↦ ?_
  have hN : 1 ≤ N := by omega
  unfold entry
  cases bottom <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> split_ifs <;>
    (rw [abs_le]; constructor <;> push_cast <;> omega)

/-! ### The context -/

theorem expo_polytime (p : Params) : ComputableInPolyTime (expo p) encUnary encUnary := by
  unfold expo
  have hs : ComputableInPolyTime (fun N : ℕ ↦ N.size) encUnary encUnary :=
    binary_size.comp (toBinary' id')
  exact unary_mul' (const _) (unary_mul' (const _) (unary_add' (const _) (unary_mul' (const 2) hs)))

theorem numV_le (x : ℕ × List Bool) : numV x ≤ (encIn x).length := by
  have h : (encIn x).length = (encPair encNat encBits x).length := rfl
  rw [h, length_encPair, encBits_apply]
  unfold numV
  omega

theorem expo_le (p : Params) (N : ℕ) : expo p N ≤ 2 * (p.c * (p.a + 2 * N)) := by
  unfold expo
  have h1 : N.size ≤ N := Nat.size_le.2 N.lt_two_pow_self
  have h2 : (if p.bottom then 1 else 2) ≤ 2 := by split_ifs <;> omega
  exact Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ (by omega))

/-- The matrix power, in polynomial time. -/
theorem powCtx_polytime (p : Params) : ComputableInPolyTime
    (fun x ↦ powL (numV x) (baseMat p.bottom (numV x) (deg (numV x) x.2) x.2)
      (expo p (numV x))) encIn encMat := by
  have hN : ComputableInPolyTime numV encIn encUnary := numV_polytime
  have hM : ComputableInPolyTime
      (fun x : ℕ × List Bool ↦ baseMat p.bottom (numV x) (deg (numV x) x.2) x.2) encIn encMat :=
    (baseMat_polytime p.bottom).comp (g := fun x ↦ ((numV x, deg (numV x) x.2), x.2))
      (by fun_prop)
  unfold powL
  set size : ℕ × List Bool → ℕ := fun x ↦ (encIn x).length
  have hs : PolyBounded size size := .self
  have hG : PolyBounded size (fun x ↦ size x * (2 * (size x * (2 * (2 *
      (2 * (p.c * (p.a + 2 * size x))) * size x + 2) + 1)) + 1)) :=
    hs.mul (((PolyBounded.const 2).mul (hs.mul (((PolyBounded.const 2).mul ((((PolyBounded.const
      2).mul ((PolyBounded.const 2).mul ((PolyBounded.const p.c).mul ((PolyBounded.const
      p.a).add ((PolyBounded.const 2).mul hs))))).mul hs).add (.const 2))).add
      (.const 1)))).add (.const 1))
  refine iterateWith (par := fun x ↦ (numV x, baseMat p.bottom (numV x) (deg (numV x) x.2) x.2))
    (count := fun x ↦ expo p (numV x)) (init := fun x ↦ idL (numV x))
    (step := fun q X ↦ mulL q.1 X q.2) (hN.prod hM) ((expo_polytime p).comp hN)
    (idL_polytime.comp hN) mulL_polytime
    (bound := fun x ↦ numV x * (2 * (numV x * (2 * (2 * expo p (numV x) * numV x + 2) + 1)) + 1))
    ?_ ?_
  · refine hG.mono fun x ↦ ?_
    have h1 := numV_le x
    have h2 := (expo_le p (numV x)).trans
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left p.c (Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 h1) p.a)))
    simp only [size]
    gcongr
  · intro x i hi
    refine (length_powL_le (entBound_baseMat p.bottom x.2 (deg_le _ _)) i).trans ?_
    gcongr

theorem zMax_polytime (p : Params) : ComputableInPolyTime (zMax p) encUnary encUnary := by
  unfold zMax
  exact unary_mul' (const _) ((unary_pow p.Ze).comp (unary_add' id' (const 1)))

theorem budget_polytime (p : Params) : ComputableInPolyTime (budget p) encUnary encUnary := by
  unfold budget
  exact (unary_pow p.T).comp
    (unary_add' (unary_add' id' (unary_mul' (const 2) (zMax_polytime p))) (const 1))

private theorem binMul' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a * g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mul' hf.tidy hg.tidy)

theorem den_polytime (p : Params) : ComputableInPolyTime
    (fun x : ℕ × List Bool ↦
      ((p.K * numV x * denBase p (deg (numV x) x.2) ^ expo p (numV x) : ℕ) : ℚ)) encIn encRat := by
  refine rat_natCast' (binMul' (binMul' (const _) (toBinary' numV_polytime)) ?_)
  unfold denBase
  exact binary_pow' (binMul' (const _) (toBinary' (by fun_prop)))
    ((expo_polytime p).comp numV_polytime)

/-- The context of the candidates: `N`, `Z`, `q`, `Q` and the budget. -/
abbrev encCtx : ℕ × ℕ × ℚ × List (List ℤ) × ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encRat (encPair encMat encUnary)))

theorem ctx_polytime (p : Params) : ComputableInPolyTime (ctx p) encIn encCtx := by
  unfold ctx
  exact numV_polytime.prod (((zMax_polytime p).comp numV_polytime).prod ((den_polytime p).prod
    ((powCtx_polytime p).prod ((budget_polytime p).comp numV_polytime))))

/-! ### The candidates -/

/-- `List.range` of a unary number. -/
private theorem rangeU' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ List.range (f a)) input (encList encUnary) :=
  .of_tidy (ComputableTidilyInPolyTime.range.comp hf.tidy)

theorem cand_polytime (T : ℕ) : ComputableInPolyTime
    (fun y : (ℕ × ℕ × ℚ × List (List ℤ)) × List ℕ × List ℕ ↦
      cand T y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 y.2.1 y.2.2)
    (encPair (encPair encUnary (encPair encUnary (encPair encRat encMat))) (encPair encVs encVs))
    (encList encRat) := by
  unfold cand
  refine mapWithInput (by fun_prop)
    (rat_div' (rat_intCast' (intSum' (mapWithInput (rangeU' (const T)) ?_))) (by fun_prop))
  exact intBin_mul' (intSub' (intOfUnary' (by fun_prop)) (intOfUnary' (by fun_prop)))
    (by fun_prop)

private theorem tuplesU' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ Tuples.tuples (f a) (g a) (h a)) input (encList encVs) :=
  Tuples.tuples_unary_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem body_polytime (T : ℕ) :
    ComputableInPolyTime (body T) encCtx (encList (encList encRat)) := by
  unfold body
  refine flatMapWithInput (tuplesU' (by fun_prop) (by fun_prop) (const T))
    (mapWithInput (tuplesU' (by fun_prop) (by fun_prop) (const T)) ?_)
  exact (cand_polytime T).comp (g := fun q : ((ℕ × ℕ × ℚ × List (List ℤ) × ℕ) × List ℕ) × List ℕ ↦
    ((q.1.1.1, q.1.1.2.1, q.1.1.2.2.1, q.1.1.2.2.2.1), q.1.2, q.2)) (by fun_prop)

/-- **The net is computed in polynomial time.** -/
theorem netList_polytime (p : Params) :
    ComputableInPolyTime (netList p) (Encoding.encPair Encoding.encNat Encoding.encBits)
      (Encoding.encList (Encoding.encList Encoding.encRat)) := by
  unfold netList
  exact cons' (const []) ((body_polytime p.T).comp (ctx_polytime p))

end Net

end BHSV25
