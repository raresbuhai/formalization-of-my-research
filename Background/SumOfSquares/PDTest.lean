module

public import Background.Ellipsoid
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Testing positive definiteness, with a witness

An exact test of whether a symmetric matrix is positive definite, which otherwise returns a
nonzero vector `v` with `vᵀ A v ≤ 0`. It is the separation oracle for a positive semidefinite
constraint: the witness is a cut.

The test peels off the last row and column. Write `A = [[B, b], [bᵀ, c]]`, and let `d = det B`,
`u = adj(B) b` (so `B u = d b`) and `s = c d - bᵀ u`.
* If the test fails on `B`, its witness, extended by `0`, is one for `A`.
* Otherwise `B` is positive definite and `d > 0`. If `s ≤ 0`, then `v = (-u, d)` has
  `vᵀ A v = d s ≤ 0`.
* Otherwise `A` is positive definite: for `v = (w, y)`,
  `d² vᵀ A v = (d w + y u)ᵀ B (d w + y u) + d s y²`.

(`s` is `det A`, so this is Sylvester's criterion, but the proof does not need that.) The test
only computes determinants and adjugates, whose entries are minors of `A`, so it runs in
polynomial time with numbers of polynomial size.

The test is defined over any ordered commutative ring, to run on integers or rationals, and its
specification is proved over `ℝ` (`SoS.PDTest.test_spec`). It commutes with order-preserving ring
maps such as `ℚ → ℝ` (`SoS.PDTest.test_map`).
-/

@[expose] public section

namespace SoS.PDTest

open Matrix

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The leading block `B`. -/
abbrev lead {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  A.submatrix Fin.castSucc Fin.castSucc

/-- The last column above the diagonal, `b`. -/
def col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Fin n → R :=
  fun i ↦ A (Fin.castSucc i) (Fin.last n)

/-- `u = adj(B) b`. -/
def cof {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Fin n → R :=
  (lead A).adjugate *ᵥ col A

/-- `s = c det B - bᵀ adj(B) b`. -/
def schur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : R :=
  A (Fin.last n) (Fin.last n) * (lead A).det - col A ⬝ᵥ cof A

/-- The witness `(-adj(B) b, det B)`. -/
def witness {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Fin (n + 1) → R :=
  Fin.snoc (α := fun _ ↦ R) (-cof A) (lead A).det

/-- **The test**: `none` if `A` is positive definite, otherwise `some v` with `v ≠ 0` and
`vᵀ A v ≤ 0` (`SoS.PDTest.test_spec`, for symmetric `A`). -/
def test : {n : ℕ} → Matrix (Fin n) (Fin n) R → Option (Fin n → R)
  | 0, _ => none
  | _ + 1, A =>
    match test (lead A) with
    | some v => some (Fin.snoc (α := fun _ ↦ R) v 0)
    | none => if schur A ≤ 0 then some (witness A) else none

/-! ### Specification -/

/-- The quadratic form of `A = [[B, b], [bᵀ, c]]` at `(w, y)`. -/
theorem quad_snoc {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A)
    (w : Fin n → ℝ) (y : ℝ) :
    Fin.snoc (α := fun _ ↦ ℝ) w y ⬝ᵥ A *ᵥ Fin.snoc (α := fun _ ↦ ℝ) w y =
      w ⬝ᵥ lead A *ᵥ w + 2 * y * (col A ⬝ᵥ w) + A (Fin.last n) (Fin.last n) * y ^ 2 := by
  have hsym : ∀ j : Fin n, A (Fin.last n) (Fin.castSucc j) = A (Fin.castSucc j) (Fin.last n) :=
    fun j ↦ by rw [← transpose_apply A (Fin.castSucc j), hA]
  simp only [dotProduct, mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, col,
    submatrix_apply, hsym, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ i : Fin n, w i * (A (Fin.castSucc i) (Fin.last n) * y) =
      ∑ i : Fin n, y * (A (Fin.castSucc i) (Fin.last n) * w i) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h1]
  ring_nf
  rw [Finset.sum_mul]

/-- **The test is correct**, for symmetric real matrices: `none` means positive definite, and
`some v` gives `v ≠ 0` with `vᵀ A v ≤ 0`. -/
theorem test_spec : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), Aᵀ = A →
    (test A = none → ∀ v, v ≠ 0 → 0 < v ⬝ᵥ A *ᵥ v) ∧
      ∀ v, test A = some v → v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v ≤ 0
  | 0, A, _ => ⟨fun _ v hv ↦ absurd (Subsingleton.elim v 0) hv, fun v h ↦ by simp [test] at h⟩
  | n + 1, A, hA => by
    have hB : (lead A)ᵀ = lead A := by rw [transpose_submatrix, hA]
    obtain ⟨ihnone, ihsome⟩ := test_spec (lead A) hB
    cases hB' : test (lead A) with
    | some w =>
      obtain ⟨hw0, hw⟩ := ihsome w hB'
      have htest : test A = some (Fin.snoc (α := fun _ ↦ ℝ) w 0) := by simp [test, hB']
      refine ⟨fun h ↦ by simp [htest] at h, fun v hv ↦ ?_⟩
      rw [htest, Option.some.injEq] at hv
      subst hv
      refine ⟨fun h ↦ hw0 (funext fun i ↦ ?_), ?_⟩
      · have := congrFun h (Fin.castSucc i)
        simpa using this
      · rw [quad_snoc hA]
        simpa using hw
    | none =>
      have hBpd := ihnone hB'
      set d := (lead A).det
      set u := cof A
      set b := col A
      set c := A (Fin.last n) (Fin.last n)
      have hd : 0 < d := (Ellipsoid.posDef_of_quad hB hBpd).det_pos
      -- `B u = d b`, so `uᵀ B u = d bᵀu` and `uᵀ B w = d bᵀw`.
      have hBu : lead A *ᵥ u = d • b := by
        simp only [u, cof, b, d, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
      have huBu : u ⬝ᵥ lead A *ᵥ u = d * (b ⬝ᵥ u) := by
        rw [hBu, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      have huBw : ∀ w, u ⬝ᵥ lead A *ᵥ w = d * (b ⬝ᵥ w) := fun w ↦ by
        rw [Ellipsoid.dotProduct_mulVec_comm hB, hBu, dotProduct_smul, smul_eq_mul,
          dotProduct_comm]
      by_cases hs : schur A ≤ 0
      · have htest : test A = some (witness A) := by simp [test, hB', hs]
        refine ⟨fun h ↦ by simp [htest] at h, fun v hv ↦ ?_⟩
        rw [htest, Option.some.injEq] at hv
        subst hv
        refine ⟨fun h ↦ hd.ne' ?_, ?_⟩
        · have := congrFun h (Fin.last n)
          simpa [witness] using this
        · rw [witness, quad_snoc hA]
          have : -u ⬝ᵥ lead A *ᵥ -u = d * (b ⬝ᵥ u) := by
            rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, huBu]
          rw [this, dotProduct_neg]
          have hs' : c * d - b ⬝ᵥ u ≤ 0 := hs
          nlinarith
      · have htest : test A = none := by simp [test, hB', hs]
        refine ⟨fun _ v hv ↦ ?_, fun v h ↦ by simp [htest] at h⟩
        push Not at hs
        have hs' : 0 < c * d - b ⬝ᵥ u := hs
        rw [← Fin.snoc_init_self v]
        set w := Fin.init v
        set y := v (Fin.last n)
        rw [quad_snoc hA]
        -- `d² vᵀ A v = (d w + y u)ᵀ B (d w + y u) + d s y²`.
        have hkey : d ^ 2 * (w ⬝ᵥ lead A *ᵥ w + 2 * y * (b ⬝ᵥ w) + c * y ^ 2) =
            (d • w + y • u) ⬝ᵥ lead A *ᵥ (d • w + y • u) + d * (c * d - b ⬝ᵥ u) * y ^ 2 := by
          simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
            smul_dotProduct, smul_eq_mul, huBu, huBw,
            Ellipsoid.dotProduct_mulVec_comm hB u w]
          ring
        have hq : 0 ≤ (d • w + y • u) ⬝ᵥ lead A *ᵥ (d • w + y • u) := by
          rcases eq_or_ne (d • w + y • u) 0 with h | h
          · simp [h]
          · exact (hBpd _ h).le
        by_cases hy : y = 0
        · have hw : w ≠ 0 := by
            intro hw
            apply hv
            funext i
            induction i using Fin.lastCases with
            | last => exact hy
            | cast j => exact congrFun hw j
          rw [hy]
          simpa using hBpd w hw
        · have : 0 < d ^ 2 * (w ⬝ᵥ lead A *ᵥ w + 2 * y * (b ⬝ᵥ w) + c * y ^ 2) := by
            rw [hkey]
            have : 0 < d * (c * d - b ⬝ᵥ u) * y ^ 2 := by positivity
            linarith
          exact pos_of_mul_pos_right this (by positivity)

/-! ### Changing the ring -/

/-- **The test commutes with sign-preserving ring maps**, such as `ℚ → ℝ`: it can run on rationals
and be specified over the reals. -/
theorem test_map {S : Type*} [CommRing S] [LinearOrder S] (f : R →+* S)
    (hf : ∀ x, f x ≤ 0 ↔ x ≤ 0) :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) R), test (A.map f) = (test A).map (fun v ↦ f ∘ v)
  | 0, _ => rfl
  | n + 1, A => by
    have hlead : lead (A.map f) = (lead A).map f := rfl
    have hcol : col (A.map f) = f ∘ col A := rfl
    have hdet : (lead (A.map f)).det = f (lead A).det := by
      rw [hlead]
      exact (RingHom.map_det f _).symm
    have hcof : cof (A.map f) = f ∘ cof A := by
      have hadj : ((lead A).map f).adjugate = (lead A).adjugate.map f :=
        (RingHom.map_adjugate f (lead A)).symm
      ext i
      simp only [cof, hlead, hcol, hadj, Function.comp_apply, mulVec, dotProduct, map_apply,
        map_sum, map_mul]
    have hschur : schur (A.map f) = f (schur A) := by
      simp only [schur, hdet, hcof, hcol, map_sub, map_mul, dotProduct, map_sum,
        Function.comp_apply, map_apply]
    have hwit : witness (A.map f) = f ∘ witness A := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [witness, hdet]
      | cast j => simp [witness, hcof]
    have hrec := test_map f hf (lead A)
    rw [← hlead] at hrec
    simp only [test, hrec]
    cases h : test (lead A) with
    | some v =>
      simp only [Option.map_some]
      congr 1
      ext i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simp
    | none =>
      simp only [Option.map_none, hschur, hf]
      split_ifs
      · simp [hwit]
      · rfl

/-! ### The test, unrolled -/

/-- The leading `(k + 1) × (k + 1)` block. -/
def leadBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (k : Fin n) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  A.submatrix (Fin.castLE k.isLt) (Fin.castLE k.isLt)

/-- Whether the test stops at the leading `(k + 1) × (k + 1)` block. -/
def stopsAt {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (k : Fin n) : Bool :=
  decide (schur (leadBlock A k) ≤ 0)

/-- The witness of the leading `(k + 1) × (k + 1)` block, padded with zeros. -/
def padWitness {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (k : Fin n) : Fin n → R :=
  fun j ↦ if h : (j : ℕ) ≤ k then witness (leadBlock A k) ⟨j, by omega⟩ else 0

omit [CommRing R] [LinearOrder R] in
theorem leadBlock_lead {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k : Fin n) :
    leadBlock (lead A) k = leadBlock A k.castSucc := rfl

omit [LinearOrder R] in
theorem schur_leadBlock_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    schur (leadBlock A (Fin.last n)) = schur A := by
  have : leadBlock A (Fin.last n) = A := by
    ext i j
    simp [leadBlock]
  rw [this]

omit [LinearOrder R] in
theorem witness_leadBlock_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    padWitness A (Fin.last n) = witness A := by
  have : leadBlock A (Fin.last n) = A := by
    ext i j
    simp [leadBlock]
  funext j
  simp only [padWitness, Fin.val_last, Fin.is_le, dite_true]
  rw [this]

/-- **The test, unrolled**: it stops at the first leading block whose Schur complement is not
positive, with that block's witness padded by zeros. -/
theorem test_eq_find : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    test A = ((List.finRange n).find? (stopsAt A)).map (padWitness A)
  | 0, _ => rfl
  | n + 1, A => by
    have ih := test_eq_find (lead A)
    have hstop : stopsAt (lead A) = stopsAt A ∘ Fin.castSucc := rfl
    have hpad : ∀ k : Fin n, Fin.snoc (α := fun _ ↦ R) (padWitness (lead A) k) 0 =
        padWitness A k.castSucc := by
      intro k
      funext j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, padWitness, Fin.val_last, Fin.val_castSucc]
        split_ifs with hk
        · exact absurd hk (by omega)
        · rfl
      | cast j =>
        simp only [Fin.snoc_castSucc, padWitness, Fin.val_castSucc]
        rfl
    rw [List.finRange_succ_last, List.find?_append, List.find?_map, ← hstop]
    simp only [test]
    rw [ih]
    cases h : (List.finRange n).find? (stopsAt (lead A)) with
    | some k =>
      simp only [Option.map_some, Option.some_or]
      rw [hpad]
    | none =>
      simp only [Option.map_none, Option.none_or, List.find?_cons, List.find?_nil]
      unfold stopsAt
      rw [schur_leadBlock_last]
      split_ifs with hs
      · simp [hs, witness_leadBlock_last]
      · simp [hs]

end SoS.PDTest
