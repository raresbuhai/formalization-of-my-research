module

public import ABBKS26.Assembly.ExecFrameAuxNormalize
public import Background.SumOfSquares.Algorithm.PDTestRat

/-!
# Rational orthogonal frames on lists

The adjugate construction is adapted from `BS23/Colinear/Basis.lean` and
`BS23/Colinear/PolyTimeLinAlg.lean`, without importing another paper. Determinants use
complexitylib's integer determinant after clearing the rational denominators.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux.Linear

open Matrix
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open Cslib (rowEntry tabulateTable rowEntry_tabulateTable_of_lt)
open Cslib.Circuits.Rational (detRows detRows_eq_det_of_rowEntry)
open scoped BigOperators

variable {α : Type} {input : α ↪ List Bool}

/-- A case distinction on a decidable proposition. -/
theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a ↦ decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a ↦ if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- A power of a rational with a unary exponent: the powers of the numerator and the
denominator, which stay coprime. -/
theorem rat_pow' {f : α → ℚ} {e : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ e a) input encRat :=
  rat_of_numDen (g := fun a ↦ ((f a).num ^ e a, (f a).den ^ e a))
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.intBin_pow' (rat_num' hf).tidy
      he.tidy)).prod (binary_pow' (rat_den' hf) he))
    fun a ↦ by rw [Rat.num_pow, Rat.den_pow]

/-- The natural ceiling of a rational, in binary. -/
theorem rat_natCeil' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌈f a⌉₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (-⌊-f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp
      (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hf)).tidy))
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_neg, neg_neg, Int.ceil_toNat]

/-- The natural floor of a rational, in binary. -/
theorem rat_natFloor' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌊f a⌋₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (⌊f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp (rat_floor' hf).tidy)
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_toNat]

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
                 simp

theorem sum_fin_eq_list {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (g : ℕ → M)
    (h : ∀ i : Fin n, g i = f i) : ∑ i, f i = ((List.range n).map g).sum := by
  rw [← sum_range_eq_list, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ (h i).symm

theorem getD_map_range {β : Type*} (g : ℕ → β) {n a : ℕ} (d : β) (h : a < n) :
    ((List.range n).map g).getD a d = g a := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]

variable {d : ℕ}

def quad {K : Type*} [Field K] (C : Matrix (Fin d) (Fin d) K) (v : Fin d → K) : K :=
  v ⬝ᵥ (C *ᵥ v)

def lead {K : Type*} [Field K] (C : Matrix (Fin d) (Fin d) K) (i : Fin d) :
    Matrix (Fin (i + 1)) (Fin (i + 1)) K :=
  C.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)

def basisVec {K : Type*} [Field K] (C : Matrix (Fin d) (Fin d) K) (i : Fin d) :
    Fin d → K := fun j ↦
  if h : j.val ≤ i.val then (lead C i).adjugate ⟨j.val, Nat.lt_succ_of_le h⟩ (Fin.last i)
  else 0

/-- Vectors, as lists of rationals. -/
abbrev encV : List ℚ ↪ List Bool := encList encRat

/-- Matrices and point sets, as lists of rows. -/
abbrev encM : List (List ℚ) ↪ List Bool := encList (encList encRat)

/-! ### Representations -/

/-- Entry `(a, b)` of a table; missing entries read as `0`. -/
def ent (P : List (List ℚ)) (a b : ℕ) : ℚ := (P.getD a []).getD b 0

/-- The list `v` represents the vector `w`. -/
def RepV {d : ℕ} (v : List ℚ) (w : Fin d → ℚ) : Prop := ∀ a : Fin d, v.getD a 0 = w a

/-- The table `P` represents the family of vectors (or matrix) `Y`. -/
def RepT {m d : ℕ} (P : List (List ℚ)) (Y : Fin m → Fin d → ℚ) : Prop :=
  ∀ (j : Fin m) (a : Fin d), ent P j a = Y j a

theorem RepT.row {m d : ℕ} {P : List (List ℚ)} {Y : Fin m → Fin d → ℚ} (h : RepT P Y)
    (j : Fin m) : RepV (P.getD j []) (Y j) := h j

theorem repV_map_range {d : ℕ} (g : ℕ → ℚ) (w : Fin d → ℚ)
    (h : ∀ a : Fin d, g a = w a) :
    RepV ((List.range d).map g) w := fun a ↦ by rw [getD_map_range g 0 a.2, h]

theorem repT_map_range {m d : ℕ} (g : ℕ → ℕ → ℚ) (Y : Fin m → Fin d → ℚ)
    (h : ∀ (j : Fin m) (a : Fin d), g j a = Y j a) :
    RepT ((List.range m).map fun j ↦ (List.range d).map (g j)) Y := fun j a ↦ by
  rw [ent, getD_map_range _ [] j.2, getD_map_range _ 0 a.2, h]

/-! ### Dot products, matrix-vector products, quadratic forms -/

/-- The dot product of the first `d` entries. -/
def dotL (d : ℕ) (u v : List ℚ) : ℚ :=
  ((List.range d).map fun a ↦ u.getD a 0 * v.getD a 0).sum

/-- The matrix-vector product, on the first `d` rows and columns. -/
def mulVecL (d : ℕ) (C : List (List ℚ)) (v : List ℚ) : List ℚ :=
  (List.range d).map fun a ↦ dotL d (C.getD a []) v

/-- The quadratic form `vᵀ C v`. -/
def quadL (d : ℕ) (C : List (List ℚ)) (v : List ℚ) : ℚ := dotL d v (mulVecL d C v)

variable {d : ℕ}

theorem dotL_eq {u v : List ℚ} {u' v' : Fin d → ℚ} (hu : RepV u u') (hv : RepV v v') :
    dotL d u v = u' ⬝ᵥ v' := by
  rw [dotL, dotProduct]
  exact (sum_fin_eq_list _ _ fun a ↦ by rw [hu a, hv a]).symm

theorem mulVecL_rep {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} {v : List ℚ}
    {v' : Fin d → ℚ} (hC : RepT C M) (hv : RepV v v') : RepV (mulVecL d C v) (M *ᵥ v') :=
  repV_map_range _ _ fun a ↦ dotL_eq (hC.row a) hv

theorem quadL_eq {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} {v : List ℚ}
    {v' : Fin d → ℚ} (hC : RepT C M) (hv : RepV v v') : quadL d C v = quad M v' :=
  dotL_eq hv (mulVecL_rep hC hv)

/-! ### The basis -/

/-- The leading block of the integer table `S`, with row `i` replaced by `D eⱼ`. -/
def adjRows (S : List (List ℤ)) (D : ℤ) (i j : ℕ) : List (List ℤ) :=
  tabulateTable (i + 1) (i + 1) fun r c ↦
    if r = i then (if c = j then D else 0) else rowEntry S r c

/-- The basis vectors: entry `j ≤ i` of vector `i` is `det (adjRows (D C) D i j) / D^(i+1)`, with
`D` the product of the denominators of `C`. -/
def basisL (d : ℕ) (C : List (List ℚ)) : List (List ℚ) :=
  (List.range d).map fun i ↦ (List.range d).map fun j ↦
    if j ≤ i then
      (detRows (adjRows (SoS.PDTestRat.scale C) (SoS.PDTestRat.commonDen C) i j) : ℚ) /
        (SoS.PDTestRat.commonDen C : ℚ) ^ (i + 1)
    else 0

theorem adjugate_eq {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} (hC : RepT C M)
    (i j : Fin d) (hji : j.val ≤ i.val) :
    (detRows (adjRows (SoS.PDTestRat.scale C) (SoS.PDTestRat.commonDen C) i j) : ℚ) /
        (SoS.PDTestRat.commonDen C : ℚ) ^ (i.val + 1) =
      (lead M i).adjugate ⟨j.val, Nat.lt_succ_of_le hji⟩ (Fin.last i) := by
  set D := SoS.PDTestRat.commonDen C
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast (SoS.PDTestRat.commonDen_pos C).ne'
  set N : Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℤ := Matrix.of fun r c ↦
    if r.val = i.val then (if c.val = j.val then D else 0)
    else rowEntry (SoS.PDTestRat.scale C) r c
  have h1 : detRows (adjRows (SoS.PDTestRat.scale C) D i j) = N.det :=
    detRows_eq_det_of_rowEntry N (by simp [adjRows]) fun r c ↦ by
      rw [adjRows, rowEntry_tabulateTable_of_lt _ r.2 c.2]
      rfl
  have h2 : N.map (Int.cast : ℤ → ℚ) =
      (D : ℚ) • (lead M i).updateRow (Fin.last i)
        (Pi.single ⟨j.val, Nat.lt_succ_of_le hji⟩ 1) := by
    ext r c
    simp only [Matrix.map_apply, N, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.updateRow_apply]
    by_cases hr : r = Fin.last i
    · simp only [hr, Fin.val_last, ite_true, Pi.single_apply]
      by_cases hc : c.val = j.val
      · have hc' : c = ⟨j.val, Nat.lt_succ_of_le hji⟩ := Fin.ext hc
        simp [hc']
      · have hc' : c ≠ ⟨j.val, Nat.lt_succ_of_le hji⟩ := fun h ↦ hc (congrArg Fin.val h)
        simp [hc, hc']
    · have hr' : r.val ≠ i.val := fun h ↦ hr (Fin.ext (by rw [h, Fin.val_last]))
      simp only [hr', hr, ite_false]
      rw [SoS.PDTestRat.rowEntry_scale]
      congr 1
      exact hC (Fin.castLE i.isLt r) (Fin.castLE i.isLt c)
  rw [adjugate_apply, h1, Int.cast_det, h2, det_smul, Fintype.card_fin,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hD)]

theorem basisL_rep {C : List (List ℚ)} {M : Matrix (Fin d) (Fin d) ℚ} (hC : RepT C M) :
    RepT (basisL d C) fun i ↦ basisVec M i :=
  repT_map_range _ _ fun i j ↦ by
    rw [basisVec]
    split_ifs with h
    · exact adjugate_eq hC i j h
    · rfl

/-! ### Polynomial time -/

theorem ent_polytime : ComputableInPolyTime
    (fun p : List (List ℚ) × ℕ × ℕ ↦ ent p.1 p.2.1 p.2.2)
    (encPair encM (encPair encUnary encUnary)) encRat := by
  unfold ent
  exact listGetDWithInput (listGetDWithInput (fst _ _) ((fst _ _).comp (snd _ _)) [])
    ((snd _ _).comp (snd _ _)) 0

@[fun_prop]
theorem ent' {P : α → List (List ℚ)} {a b : α → ℕ}
    (hP : ComputableInPolyTime P input encM)
    (ha : ComputableInPolyTime a input encUnary) (hb : ComputableInPolyTime b input encUnary) :
    ComputableInPolyTime (fun x ↦ ent (P x) (a x) (b x)) input encRat :=
  ent_polytime.comp (g := fun x ↦ (P x, a x, b x)) (hP.prod (ha.prod hb))

@[fun_prop]
theorem vget' {v : α → List ℚ} {a : α → ℕ} (hv : ComputableInPolyTime v input encV)
    (ha : ComputableInPolyTime a input encUnary) :
    ComputableInPolyTime (fun x ↦ (v x).getD (a x) 0) input encRat :=
  listGetDWithInput hv ha 0

@[fun_prop]
theorem row' {P : α → List (List ℚ)} {a : α → ℕ} (hP : ComputableInPolyTime P input encM)
    (ha : ComputableInPolyTime a input encUnary) :
    ComputableInPolyTime (fun x ↦ (P x).getD (a x) []) input encV :=
  listGetDWithInput hP ha []

theorem dotL_polytime : ComputableInPolyTime
    (fun p : ℕ × List ℚ × List ℚ ↦ dotL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encV encV)) encRat := by
  unfold dotL
  set E := encPair encUnary (encPair encV encV)
  have hu : ComputableInPolyTime (fun p : (ℕ × List ℚ × List ℚ) × ℕ ↦ p.1.2.1)
      (encPair E encUnary) encV := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hv : ComputableInPolyTime (fun p : (ℕ × List ℚ × List ℚ) × ℕ ↦ p.1.2.2)
      (encPair E encUnary) encV := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact rat_sum' (mapWithInput (range.comp (fst _ _))
    (rat_mul' (vget' hu (snd _ _)) (vget' hv (snd _ _))))

@[fun_prop]
theorem dotL' {d : α → ℕ} {u v : α → List ℚ} (hd : ComputableInPolyTime d input encUnary)
    (hu : ComputableInPolyTime u input encV) (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ dotL (d x) (u x) (v x)) input encRat :=
  dotL_polytime.comp (g := fun x ↦ (d x, u x, v x)) (hd.prod (hu.prod hv))

theorem mulVecL_polytime : ComputableInPolyTime
    (fun p : ℕ × List (List ℚ) × List ℚ ↦ mulVecL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encM encV)) encV := by
  unfold mulVecL
  set E := encPair encUnary (encPair encM encV)
  have hd : ComputableInPolyTime (fun p : (ℕ × List (List ℚ) × List ℚ) × ℕ ↦ p.1.1)
      (encPair E encUnary) encUnary := (fst _ _).comp (fst _ _)
  have hC : ComputableInPolyTime (fun p : (ℕ × List (List ℚ) × List ℚ) × ℕ ↦ p.1.2.1)
      (encPair E encUnary) encM := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hv : ComputableInPolyTime (fun p : (ℕ × List (List ℚ) × List ℚ) × ℕ ↦ p.1.2.2)
      (encPair E encUnary) encV := (snd _ _).comp ((snd _ _).comp (fst _ _))
  exact mapWithInput (range.comp (fst _ _)) (dotL' hd (row' hC (snd _ _)) hv)

@[fun_prop]
theorem mulVecL' {d : α → ℕ} {C : α → List (List ℚ)} {v : α → List ℚ}
    (hd : ComputableInPolyTime d input encUnary) (hC : ComputableInPolyTime C input encM)
    (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ mulVecL (d x) (C x) (v x)) input encV :=
  mulVecL_polytime.comp (g := fun x ↦ (d x, C x, v x)) (hd.prod (hC.prod hv))

@[fun_prop]
theorem quadL' {d : α → ℕ} {C : α → List (List ℚ)} {v : α → List ℚ}
    (hd : ComputableInPolyTime d input encUnary) (hC : ComputableInPolyTime C input encM)
    (hv : ComputableInPolyTime v input encV) :
    ComputableInPolyTime (fun x ↦ quadL (d x) (C x) (v x)) input encRat := by
  unfold quadL
  exact dotL' hd hv (mulVecL' hd hC hv)

theorem adjRows_polytime : ComputableInPolyTime
    (fun p : List (List ℤ) × ℤ × ℕ × ℕ ↦ adjRows p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair SoS.PDTestRows.encRows (encPair encIntBin (encPair encUnary encUnary)))
    SoS.PDTestRows.encRows := by
  unfold adjRows
  fun_prop

@[fun_prop]
theorem adjRows' {S : α → List (List ℤ)} {D : α → ℤ} {i j : α → ℕ}
    (hS : ComputableInPolyTime S input SoS.PDTestRows.encRows)
    (hD : ComputableInPolyTime D input encIntBin) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x ↦ adjRows (S x) (D x) (i x) (j x)) input SoS.PDTestRows.encRows :=
  adjRows_polytime.comp (g := fun x ↦ (S x, D x, i x, j x)) (hS.prod (hD.prod (hi.prod hj)))

theorem basisL_polytime : ComputableInPolyTime (fun p : ℕ × List (List ℚ) ↦ basisL p.1 p.2)
    (encPair encUnary encM) encM := by
  unfold basisL
  set E := encPair encUnary encM
  have hC : ComputableInPolyTime (fun p : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦ p.1.1.2)
      (encPair (encPair E encUnary) encUnary) encM := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hi : ComputableInPolyTime (fun p : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair E encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hD : ComputableInPolyTime (fun p : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦
      SoS.PDTestRat.commonDen p.1.1.2) (encPair (encPair E encUnary) encUnary) encIntBin :=
    SoS.PDTestRat.commonDen_polytime.comp hC
  have hS : ComputableInPolyTime (fun p : ((ℕ × List (List ℚ)) × ℕ) × ℕ ↦
      SoS.PDTestRat.scale p.1.1.2) (encPair (encPair E encUnary) encUnary)
      SoS.PDTestRows.encRows := SoS.PDTestRat.scale_polytime.comp hC
  exact mapWithInput (range.comp (fst _ _)) (mapWithInput (range.comp ((fst _ _).comp (fst _ _)))
    (ite_prop (unary_le' (snd _ _) hi)
      (rat_div' (rat_intCast' (SoS.PDTestRows.detRows' (adjRows' hS hD hi (snd _ _))))
        (rat_pow' (rat_intCast' hD) (unary_add' hi (const 1))))
      (const 0)))


/-! The adjugate vectors are orthogonal; positivity is checked over the reals. -/

private theorem dotProduct_mulVec_comm {C : Matrix (Fin d) (Fin d) ℝ}
    (hC : Cᵀ = C) (x y : Fin d → ℝ) :
    x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hC]

private theorem lead_posDef {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (i : Fin d) : (lead C i).PosDef :=
  hC.submatrix (Fin.castLE_injective _)

private theorem det_lead_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (i : Fin d) : 0 < (lead C i).det :=
  (lead_posDef hC i).det_pos

theorem basisVec_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : i < j) :
    basisVec C i j = 0 := by
  simp [basisVec, not_le.mpr (Fin.lt_def.mp h)]

/-- The leading block maps `λᵢ` to `det C_{[i]} eᵢ`. -/
theorem mulVec_basisVec_of_le (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : j ≤ i) :
    (C *ᵥ basisVec C i) j = if j = i then (lead C i).det else 0 := by
  have hj : j.val < i.val + 1 := Nat.lt_succ_of_le h
  have hsum : (C *ᵥ basisVec C i) j =
      (lead C i * (lead C i).adjugate) ⟨j.val, hj⟩ (Fin.last i) := by
    simp only [mulVec, dotProduct]
    symm
    refine Fintype.sum_of_injective (Fin.castLE i.isLt) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro k hk
      have : ¬ k.val ≤ i.val := by
        intro hk'
        exact hk ⟨⟨k.val, Nat.lt_succ_of_le hk'⟩, Fin.ext rfl⟩
      simp [basisVec, this]
    · intro k
      have hk : (Fin.castLE i.isLt k).val ≤ i.val := Nat.le_of_lt_succ k.isLt
      simp only [basisVec, hk, dite_true, lead, submatrix_apply]
      congr 2
  rw [hsum, mul_adjugate, Matrix.smul_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    have : (⟨j.val, hj⟩ : Fin (j + 1)) = Fin.last j := Fin.ext rfl
    rw [this, Matrix.one_apply_eq, mul_one]
    simp
  · have : (⟨j.val, hj⟩ : Fin (i + 1)) ≠ Fin.last i := by
      intro h'
      exact hji (Fin.ext (by simpa [Fin.ext_iff] using h'))
    simp [Matrix.one_apply_ne this, hji]

theorem mulVec_basisVec_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : j < i) :
    (C *ᵥ basisVec C i) j = 0 := by
  simp [mulVec_basisVec_of_le C h.le, h.ne]

theorem mulVec_basisVec_self (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (C *ᵥ basisVec C i) i = (lead C i).det := by
  simp [mulVec_basisVec_of_le C le_rfl]

/-- The diagonal entry `(λᵢ)ᵢ` is the previous leading principal minor `det C_{[i-1]}`. -/
theorem basisVec_self (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    basisVec C i i = ((lead C i).submatrix Fin.castSucc Fin.castSucc).det := by
  have h : (⟨i.val, Nat.lt_succ_of_le le_rfl⟩ : Fin (i + 1)) = Fin.last i := Fin.ext rfl
  simp only [basisVec, le_refl, dite_true, h]
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp [← two_mul, pow_mul]

theorem basisVec_self_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    0 < basisVec C i i := by
  rw [basisVec_self]
  exact ((lead_posDef hC i).submatrix (Fin.castSucc_injective _)).det_pos

/-- `λᵢᵀ C λᵢ = det C_{[i]} · (λᵢ)ᵢ`. -/
theorem quad_basisVec (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    quad C (basisVec C i) = (lead C i).det * basisVec C i i := by
  unfold quad
  rw [dotProduct, Finset.sum_eq_single i, mulVec_basisVec_self, mul_comm]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [mulVec_basisVec_of_lt C hlt, mul_zero]
    · rw [basisVec_of_lt C hgt, zero_mul]
  · simp

theorem quad_basisVec_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    0 < quad C (basisVec C i) := by
  rw [quad_basisVec]
  exact mul_pos (det_lead_pos hC i) (basisVec_self_pos hC i)


theorem basisVec_orth_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : i < j) :
    basisVec C i ⬝ᵥ (C *ᵥ basisVec C j) = 0 := by
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases le_or_gt k i with hki | hki
  · rw [mulVec_basisVec_of_lt C (lt_of_le_of_lt hki h), mul_zero]
  · rw [basisVec_of_lt C hki, zero_mul]

/-- **`C`-orthogonality** of the basis vectors. -/
theorem basisVec_orth {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) {i j : Fin d} (h : i ≠ j) :
    basisVec C i ⬝ᵥ (C *ᵥ basisVec C j) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact basisVec_orth_of_lt C hlt
  · rw [dotProduct_mulVec_comm hC]
    exact basisVec_orth_of_lt C hgt

theorem dotProduct_cast (v w : Fin d → ℚ) :
    (fun a ↦ (v a : ℝ)) ⬝ᵥ (fun a ↦ (w a : ℝ)) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  simp [dotProduct]

theorem mulVec_cast (C : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    C.map ((↑) : ℚ → ℝ) *ᵥ (fun a ↦ (v a : ℝ)) = fun a ↦ ((C *ᵥ v) a : ℝ) := by
  funext a
  simp [mulVec, dotProduct]

theorem quad_cast (C : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) :
    quad (C.map ((↑) : ℚ → ℝ)) (fun a ↦ (v a : ℝ)) = ((quad C v : ℚ) : ℝ) := by
  rw [quad, quad, mulVec_cast, dotProduct_cast]

theorem lead_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    lead (C.map ((↑) : ℚ → ℝ)) i = (lead C i).map ((↑) : ℚ → ℝ) :=
  rfl

theorem basisVec_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    basisVec (C.map ((↑) : ℚ → ℝ)) i = fun j ↦ ((basisVec C i j : ℚ) : ℝ) := by
  have hadj : (lead (C.map ((↑) : ℚ → ℝ)) i).adjugate =
      (lead C i).adjugate.map ((↑) : ℚ → ℝ) := by
    rw [lead_cast]
    exact ((Rat.castHom ℝ).map_adjugate (lead C i)).symm
  funext j
  unfold basisVec
  split_ifs <;> simp [hadj]

/-- Base-`4` logarithms from base-`2` ones. -/
theorem log_four (N : ℕ) : Nat.log 4 N = Nat.log 2 N / 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h2 := Nat.pow_log_le_self 2 hN.ne'
  have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hN.ne'⟩)]
  have e : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k ↦ by rw [pow_mul]; norm_num
  constructor
  · rw [e]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h2
  · rw [e]
    exact h3.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Base-`4` ceiling logarithms from base-`2` ones. -/
theorem clog_four (N : ℕ) : Nat.clog 4 N = (Nat.clog 2 N + 1) / 2 := by
  have e : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k ↦ by rw [pow_mul]; norm_num
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), e]
    exact (Nat.le_pow_clog (by norm_num) N).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have h := Nat.le_pow_clog (by norm_num : 1 < 4) N
    rw [e, ← Nat.clog_le_iff_le_pow (by norm_num)] at h
    omega

/-- The dyadic row multiplier, computed using binary logarithms. -/
def scaleL (q : ℚ) : ℚ :=
  if 1 ≤ q then ((2 : ℚ) ^ (Nat.log 2 ⌊q⌋₊ / 2))⁻¹
  else (2 : ℚ) ^ ((Nat.clog 2 ⌈q⁻¹⌉₊ + 1) / 2)

theorem scaleL_eq (q : ℚ) : scaleL q = (2 : ℚ) ^ (-Int.log 4 q) := by
  rw [scaleL, Int.log]
  split_ifs
  · rw [log_four, _root_.zpow_neg, zpow_natCast]
  · rw [neg_neg, zpow_natCast, clog_four]

theorem scaleL_polytime : ComputableInPolyTime scaleL encRat encRat := by
  unfold scaleL
  exact ite_prop (rat_le' (const 1) id')
    (rat_inv' (rat_two_pow' ((unary_div_const 2).comp
      (binary_log_two.comp (rat_natFloor' id')))))
    (rat_two_pow' ((unary_div_const 2).comp
      (unary_add' (binary_clog_two.comp (rat_natCeil' (rat_inv' id'))) (const 1))))

theorem scaleL_pos (q : ℚ) : 0 < scaleL q := by
  rw [scaleL_eq]
  positivity

theorem scaleL_spec {q : ℚ} (hq : 0 < q) :
    1 ≤ scaleL q ^ 2 * q ∧ scaleL q ^ 2 * q < 4 := by
  have hlo := Int.zpow_log_le_self (R := ℚ) (b := 4) (by norm_num) hq
  have hhi := Int.lt_zpow_succ_log_self (R := ℚ) (b := 4) (by norm_num) q
  have he : scaleL q ^ 2 = (4 : ℚ) ^ (-Int.log 4 q) := by
    rw [scaleL_eq, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
    norm_num
  rw [he, _root_.zpow_neg, ← div_eq_inv_mul]
  constructor
  · exact (le_div_iff₀ (zpow_pos (by norm_num) _)).mpr (by simpa using hlo)
  · apply (div_lt_iff₀ (zpow_pos (by norm_num) _)).mpr
    rwa [zpow_add_one₀ (by norm_num), mul_comm] at hhi

def whitenMat (C : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j ↦ scaleL (quad C (basisVec C i)) * basisVec C i j

def whitenDiag (C : Matrix (Fin d) (Fin d) ℚ) : Fin d → ℚ :=
  fun i ↦ scaleL (quad C (basisVec C i)) ^ 2 * quad C (basisVec C i)

theorem quad_basisVec_pos_rat (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (C.map (algebraMap ℚ ℝ)).PosDef) (i : Fin d) :
    0 < quad C (basisVec C i) := by
  change (C.map ((↑) : ℚ → ℝ)).PosDef at hC
  have h := quad_basisVec_pos hC i
  rw [basisVec_cast, quad_cast] at h
  exact_mod_cast h

theorem whitenDiag_spec (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (C.map (algebraMap ℚ ℝ)).PosDef) (i : Fin d) :
    1 ≤ whitenDiag C i ∧ whitenDiag C i < 4 :=
  scaleL_spec (quad_basisVec_pos_rat C hC i)

theorem whitenMat_spec (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (C.map (algebraMap ℚ ℝ)).PosDef) :
    whitenMat C * C * (whitenMat C)ᵀ = diagonal (whitenDiag C) := by
  change (C.map ((↑) : ℚ → ℝ)).PosDef at hC
  have hsym : (C.map ((↑) : ℚ → ℝ))ᵀ = C.map ((↑) : ℚ → ℝ) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  have horth (i j : Fin d) (hij : i ≠ j) :
      basisVec C i ⬝ᵥ (C *ᵥ basisVec C j) = 0 := by
    have h := basisVec_orth hsym hij
    rw [basisVec_cast, basisVec_cast, mulVec_cast, dotProduct_cast] at h
    exact_mod_cast h
  ext i j
  rw [Matrix.mul_mul_apply, transpose_transpose]
  have hrow (i : Fin d) : whitenMat C i =
      scaleL (quad C (basisVec C i)) • basisVec C i := rfl
  rw [hrow, hrow, mulVec_smul, smul_dotProduct, dotProduct_smul]
  by_cases hij : i = j
  · subst j
    rw [diagonal_apply_eq]
    simp only [smul_eq_mul, whitenDiag, quad]
    ring
  · rw [diagonal_apply_ne _ hij, horth i j hij, smul_zero, smul_zero]

theorem whitenMat_det_ne_zero (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (C.map (algebraMap ℚ ℝ)).PosDef) : (whitenMat C).det ≠ 0 := by
  have h := congrArg Matrix.det (whitenMat_spec C hC)
  rw [det_mul, det_mul, det_transpose, det_diagonal] at h
  have hn : (∏ i, whitenDiag C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
    ne_of_gt (lt_of_lt_of_le (by norm_num) (whitenDiag_spec C hC i).1)
  intro hz
  rw [hz, zero_mul, zero_mul] at h
  exact hn h.symm

/-- The LA4 frame and its diagonal, both computed on rational lists. -/
def whitenL (d : ℕ) (C : MatrixL) : MatrixL :=
  (basisL d C).map fun v ↦ v.map (scaleL (quadL d C v) * ·)

def diagonalL (d : ℕ) (C : MatrixL) : Vector :=
  (basisL d C).map fun v ↦ scaleL (quadL d C v) ^ 2 * quadL d C v

theorem whitenL_polytime : ComputableInPolyTime (fun p : ℕ × MatrixL ↦ whitenL p.1 p.2)
    (encPair encUnary encMatrix) encMatrix := by
  unfold whitenL
  apply mapWithInput basisL_polytime
  have hd : ComputableInPolyTime (fun p : (ℕ × MatrixL) × Vector ↦ p.1.1)
      (encPair (encPair encUnary encMatrix) encVector) encUnary :=
    (fst _ _).comp (fst _ _)
  have hC : ComputableInPolyTime (fun p : (ℕ × MatrixL) × Vector ↦ p.1.2)
      (encPair (encPair encUnary encMatrix) encVector) encMatrix :=
    (snd _ _).comp (fst _ _)
  have hs := scaleL_polytime.comp (quadL' hd hC (snd _ _))
  apply mapWithInput (snd _ _)
  exact rat_mul' (hs.comp (fst _ _)) (snd _ _)

theorem diagonalL_polytime : ComputableInPolyTime
    (fun p : ℕ × MatrixL ↦ diagonalL p.1 p.2)
    (encPair encUnary encMatrix) encVector := by
  unfold diagonalL
  apply mapWithInput basisL_polytime
  have hq := quadL' ((fst _ _).comp (fst _ _))
    ((snd _ _).comp (fst _ _)) (snd _ _)
  exact rat_mul' (rat_sq' (scaleL_polytime.comp hq)) hq

theorem whitenL_length (d : ℕ) (C : MatrixL) : (whitenL d C).length = d := by
  simp [whitenL, basisL]

theorem diagonalL_length (d : ℕ) (C : MatrixL) : (diagonalL d C).length = d := by
  simp [diagonalL, basisL]

theorem matrixOf_whitenL (d : ℕ) (C : MatrixL) :
    matrixOf d (whitenL d C) = whitenMat (matrixOf d C) := by
  have hC : RepT C (matrixOf d C) := fun _ _ ↦ rfl
  have hB := basisL_rep hC
  ext i j
  change ((whitenL d C).getD i []).getD j 0 = _
  have hrow : (whitenL d C).getD i [] =
      ((basisL d C).getD i []).map
        (scaleL (quadL d C ((basisL d C).getD i [])) * ·) := by
    simpa only [List.map_nil, whitenL] using
      List.getD_map (l := basisL d C) (d := []) (n := i.val)
        (fun v ↦ v.map (scaleL (quadL d C v) * ·))
  rw [hrow]
  have he := List.getD_map (l := (basisL d C).getD i []) (d := 0) (n := j.val)
    (scaleL (quadL d C ((basisL d C).getD i [])) * ·)
  simp only [mul_zero] at he
  have hb : ((basisL d C).getD i []).getD j 0 = basisVec (matrixOf d C) i j := hB i j
  rw [he, quadL_eq hC (hB.row i), hb]
  rfl

theorem vectorOf_diagonalL (d : ℕ) (C : MatrixL) :
    vectorOf d (diagonalL d C) = whitenDiag (matrixOf d C) := by
  have hC : RepT C (matrixOf d C) := fun _ _ ↦ rfl
  have hB := basisL_rep hC
  have hlen : (basisL d C).length = d := by simp [basisL]
  ext i
  change (diagonalL d C).getD i 0 = _
  rw [diagonalL, List.getD_eq_getElem _ _ (by simp [hlen]),
    List.getElem_map]
  have hbi : (basisL d C).getD i [] = (basisL d C)[i.val]'(by simp [hlen]) :=
    List.getD_eq_getElem _ _ (by simp [hlen])
  rw [← hbi]
  rw [quadL_eq hC (hB.row i)]
  rfl

/-- LA4 for the actual list program, including its nonzero determinant. -/
theorem rational_frame (d : ℕ) (C : MatrixL)
    (hC : ((matrixOf d C).map (algebraMap ℚ ℝ)).PosDef) :
    let T := matrixOf d (whitenL d C)
    let q := vectorOf d (diagonalL d C)
    T.det ≠ 0 ∧ (∀ i, 1 ≤ q i ∧ q i < 4) ∧ T * matrixOf d C * Tᵀ = diagonal q := by
  dsimp only
  rw [matrixOf_whitenL, vectorOf_diagonalL]
  exact ⟨whitenMat_det_ne_zero _ hC, whitenDiag_spec _ hC, whitenMat_spec _ hC⟩

theorem whitenL_row_length (d : ℕ) (C : MatrixL) (i : Fin d) :
    ((whitenL d C).getD i []).length = d := by
  simp [whitenL, basisL, List.getD_eq_getElem?_getD]

theorem whitenL_eq_ofFn (d : ℕ) (C : MatrixL) :
    whitenL d C = List.ofFn (fun i ↦ List.ofFn (whitenMat (matrixOf d C) i)) := by
  apply List.ext_getElem
  · simp [whitenL_length]
  · intro i hi hi'
    have hid : i < d := by simpa using hi'
    simp only [List.getElem_ofFn]
    apply List.ext_getElem
    · have hrow := whitenL_row_length d C ⟨i, hid⟩
      rw [List.getD_eq_getElem _ _ hi] at hrow
      simpa using hrow
    · intro j hj hj'
      have hjd : j < d := by simpa using hj'
      have he := congrFun (congrFun (matrixOf_whitenL d C) ⟨i, hid⟩) ⟨j, hjd⟩
      simpa only [matrixOf, List.getD_eq_getElem _ _ hi,
        List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using he

theorem diagonalL_eq_ofFn (d : ℕ) (C : MatrixL) :
    diagonalL d C = List.ofFn (whitenDiag (matrixOf d C)) := by
  apply List.ext_getElem
  · simp [diagonalL_length]
  · intro i hi hi'
    have hid : i < d := by simpa using hi'
    have he := congrFun (vectorOf_diagonalL d C) ⟨i, hid⟩
    simpa only [vectorOf, List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using he

/-- LA4 followed by the requested LA5 normalization, without a selected real witness. -/
def normalizedL (d : ℕ) (C : MatrixL) (ζ : ℚ) : MatrixL :=
  finishRequested ζ (diagonalL d C) (whitenL d C)

theorem normalizedL_polytime : ComputableInPolyTime
    (fun p : (ℕ × MatrixL) × ℚ ↦ normalizedL p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encMatrix) encRat) encMatrix :=
  finishRequested_polytime (snd _ _) (diagonalL_polytime.comp (fst _ _))
    (whitenL_polytime.comp (fst _ _))

theorem matrixOf_normalizedL (d : ℕ) (C : MatrixL) (ζ : ℚ) :
    matrixOf d (normalizedL d C ζ) =
      diagonal (fun i ↦ invSqrt (normalizePrecision d ζ) (whitenDiag (matrixOf d C) i)) *
        whitenMat (matrixOf d C) := by
  rw [normalizedL, whitenL_eq_ofFn, diagonalL_eq_ofFn, matrixOf_finishRequested]

theorem whitenMat_spec_real (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (C.map (algebraMap ℚ ℝ)).PosDef) :
    let T := (whitenMat C).map (algebraMap ℚ ℝ)
    T * C.map (algebraMap ℚ ℝ) * Tᵀ = diagonal (fun i ↦ (whitenDiag C i : ℝ)) := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℚ ↦ A.map (algebraMap ℚ ℝ))
    (whitenMat_spec C hC)
  simp only [Matrix.map_mul, Matrix.transpose_map, diagonal_map (map_zero _)] at h
  exact h

theorem matrixOf_normalizedL_real (d : ℕ) (C : MatrixL) (ζ : ℚ) :
    (matrixOf d (normalizedL d C ζ)).map (algebraMap ℚ ℝ) =
      diagonal (fun i ↦ (invSqrt (normalizePrecision d ζ)
        (whitenDiag (matrixOf d C) i) : ℝ)) *
          (whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ) := by
  rw [matrixOf_normalizedL, Matrix.map_mul, diagonal_map (map_zero _)]
  rfl

/-- The final stored frame adds at most `ζ` to the filter's Frobenius error. -/
theorem normalizedL_error (d : ℕ) (C : MatrixL) (S : Common.Mat d) (e : ℝ) (ζ : ℚ)
    (hC : ((matrixOf d C).map (algebraMap ℚ ℝ)).PosDef) (he : 0 ≤ e) (hζ : 0 < ζ)
    (herr : let T := (whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ)
      Common.frobSq (T * (S - (matrixOf d C).map (algebraMap ℚ ℝ)) * Tᵀ) ≤ e ^ 2) :
    let T := (matrixOf d (normalizedL d C ζ)).map (algebraMap ℚ ℝ)
    Common.frobSq (T * S * Tᵀ - 1) ≤ (e + ζ) ^ 2 := by
  let T := (whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ)
  let q := whitenDiag (matrixOf d C)
  have hdiag : T * (matrixOf d C).map (algebraMap ℚ ℝ) * Tᵀ =
      diagonal (fun i ↦ (q i : ℝ)) := whitenMat_spec_real _ hC
  have hz : (0 : ℝ) ≤ ζ := by exact_mod_cast hζ.le
  have h := finish_error (normalizePrecision d ζ) q T
    ((matrixOf d C).map (algebraMap ℚ ℝ)) S e ζ (whitenDiag_spec _ hC)
    hdiag he hz herr (normalizePrecision_spec d hζ)
  dsimp only at h ⊢
  rw [matrixOf_normalizedL_real]
  exact h

/-- A clean filter pass gives the contract's accuracy for the executable normalization. -/
theorem normalizedL_pass {n k : ℕ} (D : Robust.Reference n k d)
    (st : Robust.FilterState n d) (π R : ℝ) (C : MatrixL) (ζ : ℚ)
    (hC : ((matrixOf d C).map (algebraMap ℚ ℝ)).PosDef) (hζ : 0 < ζ)
    (hcov : (matrixOf d C).map (algebraMap ℚ ℝ) = Robust.weightedCov D st)
    (hframe : st.frame = (whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ))
    (hi : Robust.IterationInvariant D st π) (hf : Robust.FrameNormalized D st)
    (he : D.contamination ≤ min (Robust.maxContamination π R) (π / 400))
    (hp : Robust.Pass st π R) :
    let T := (matrixOf d (normalizedL d C ζ)).map (algebraMap ℚ ℝ)
    Common.frobSq (T * D.cov * Tᵀ - 1) ≤
      (65 * Real.sqrt (Robust.sigmaSq π R) * Real.sqrt D.contamination + ζ) ^ 2 := by
  let T := (whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ)
  let e := 64 * Real.sqrt (Robust.sigmaSq π R) * Real.sqrt D.contamination
  have hσ : 0 ≤ Robust.sigmaSq π R := by unfold Robust.sigmaSq; positivity
  have hε : 0 ≤ D.contamination := by unfold Robust.Reference.contamination; positivity
  obtain ⟨_, _, herr, _⟩ := Robust.pass_accuracy D st π R hi hf he hp
  rw [← hcov, hframe] at herr
  have hsq : e ^ 2 = (64 : ℝ) ^ 2 * Robust.sigmaSq π R * D.contamination := by
    simp only [e, mul_pow, Real.sq_sqrt hσ, Real.sq_sqrt hε]
  have herror : Common.frobSq
      (T * (D.cov - (matrixOf d C).map (algebraMap ℚ ℝ)) * Tᵀ) ≤ e ^ 2 := by
    rw [← neg_sub ((matrixOf d C).map (algebraMap ℚ ℝ)) D.cov, mul_neg, neg_mul]
    simpa only [Common.frobSq, Matrix.neg_apply, neg_sq, hsq] using herr
  have hresult := normalizedL_error d C D.cov e ζ hC (by dsimp only [e]; positivity)
    hζ herror
  apply hresult.trans
  apply pow_le_pow_left₀ (by dsimp only [e]; positivity) _ 2
  dsimp only [e]
  have hnonneg := mul_nonneg (Real.sqrt_nonneg (Robust.sigmaSq π R))
    (Real.sqrt_nonneg D.contamination)
  linarith only [hnonneg]

end ABBKS26.Assembly.Exec.FrameAux.Linear
