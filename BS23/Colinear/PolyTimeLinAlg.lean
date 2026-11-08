module

public import BS23.Colinear.PolyTimeBasic
public import Background.SumOfSquares.Algorithm.PDTestRat

/-!
# Polynomial time for the colinear algorithm: linear algebra on lists

List programs for the linear algebra of the colinear algorithm (`BS23/Colinear/Alg.lean`), on
vectors given as lists of rationals and matrices given as lists of rows, with certificates
(`Turing.MultiTapeTM.ComputableInPolyTime`). A list represents a vector or a matrix when its
entries are those of the vector or matrix (`BS23.Colinear.PT.RepV`, `BS23.Colinear.PT.RepT`);
every program represents what it computes:

* dot products, matrix-vector products and quadratic forms;
* the empirical mean, the centered points and the empirical covariance;
* the basis vectors `BS23.Colinear.basisVec`, the adjugate columns of the leading blocks: their
  entries are determinants of integer matrices, the leading blocks scaled by the product `D` of
  the denominators with one row replaced (`BS23.Colinear.PT.adjRows`), divided by a power of `D`,
  and the determinants are computed by complexitylib's polynomial-time integer determinant.
-/

@[expose] public section

namespace BS23.Colinear.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Matrix
open Cslib (rowEntry tabulateTable rowEntry_tabulateTable_of_lt)
open Cslib.Circuits.Rational (detRows detRows_eq_det_of_rowEntry)

variable {α : Type} {input : α ↪ List Bool}

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

theorem repV_map_range {d : ℕ} (g : ℕ → ℚ) (w : Fin d → ℚ) (h : ∀ a : Fin d, g a = w a) :
    RepV ((List.range d).map g) w := fun a ↦ by rw [getD_map_range g 0 a.2, h]

theorem repT_map_range {m d : ℕ} (g : ℕ → ℕ → ℚ) (Y : Fin m → Fin d → ℚ)
    (h : ∀ (j : Fin m) (a : Fin d), g j a = Y j a) :
    RepT ((List.range m).map fun j ↦ (List.range d).map (g j)) Y := fun j a ↦ by
  rw [ent, getD_map_range _ [] j.2, getD_map_range _ 0 a.2, h]

theorem ent_pointsFun (pts : Points) : RepT pts (pointsFun pts) := fun _ _ ↦ rfl

/-! ### Dot products, matrix-vector products, quadratic forms -/

/-- The dot product of the first `d` entries. -/
def dotL (d : ℕ) (u v : List ℚ) : ℚ := ((List.range d).map fun a ↦ u.getD a 0 * v.getD a 0).sum

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

/-! ### Mean, centered points, covariance -/

/-- The empirical mean of the first `n` points, in dimension `d`. -/
def meanL (n d : ℕ) (P : List (List ℚ)) : List ℚ :=
  (List.range d).map fun a ↦ ((List.range n).map fun j ↦ ent P j a).sum / n

/-- The points minus the mean. -/
def centL (n d : ℕ) (P : List (List ℚ)) (mu : List ℚ) : List (List ℚ) :=
  (List.range n).map fun j ↦ (List.range d).map fun a ↦ ent P j a - mu.getD a 0

/-- The empirical covariance of centered points. -/
def covL (n d : ℕ) (cs : List (List ℚ)) : List (List ℚ) :=
  (List.range d).map fun a ↦ (List.range d).map fun b ↦
    ((List.range n).map fun j ↦ ent cs j a * ent cs j b).sum / n

variable {n : ℕ}

theorem meanL_rep {P : List (List ℚ)} {Y : Fin n → Fin d → ℚ} (hP : RepT P Y) :
    RepV (meanL n d P) (mean Y) :=
  repV_map_range _ _ fun a ↦ by
    rw [mean, sum_fin_eq_list (fun j ↦ Y j a) (fun j ↦ ent P j a) fun j ↦ hP j a]

theorem centL_rep {P : List (List ℚ)} {Y : Fin n → Fin d → ℚ} {mu : List ℚ} (hP : RepT P Y)
    (hmu : RepV mu (mean Y)) : RepT (centL n d P mu) fun j ↦ Y j - mean Y :=
  repT_map_range _ _ fun j a ↦ by rw [hP j a, hmu a, Pi.sub_apply]

theorem covL_rep {cs : List (List ℚ)} {Y : Fin n → Fin d → ℚ} (hc : RepT cs fun j ↦ Y j - mean Y) :
    RepT (covL n d cs) (empCov Y) :=
  repT_map_range _ _ fun a b ↦ by
    rw [empCov, sum_fin_eq_list (fun j ↦ (Y j a - mean Y a) * (Y j b - mean Y b))
      (fun j ↦ ent cs j a * ent cs j b) fun j ↦ by rw [hc j a, hc j b]; rfl]

/-! ### The basis -/

/-- The leading `(i+1) × (i+1)` block of the integer table `S`, with row `i` replaced by `D eⱼ`. -/
def adjRows (S : List (List ℤ)) (D : ℤ) (i j : ℕ) : List (List ℤ) :=
  tabulateTable (i + 1) (i + 1) fun r c ↦ if r = i then (if c = j then D else 0) else rowEntry S r c

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
      (D : ℚ) • (lead M i).updateRow (Fin.last i) (Pi.single ⟨j.val, Nat.lt_succ_of_le hji⟩ 1) := by
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

theorem ent_polytime : ComputableInPolyTime (fun p : List (List ℚ) × ℕ × ℕ ↦ ent p.1 p.2.1 p.2.2)
    (encPair encM (encPair encUnary encUnary)) encRat := by
  unfold ent
  exact listGetDWithInput (listGetDWithInput (fst _ _) ((fst _ _).comp (snd _ _)) [])
    ((snd _ _).comp (snd _ _)) 0

@[fun_prop]
theorem ent' {P : α → List (List ℚ)} {a b : α → ℕ} (hP : ComputableInPolyTime P input encM)
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

theorem dotL_polytime : ComputableInPolyTime (fun p : ℕ × List ℚ × List ℚ ↦ dotL p.1 p.2.1 p.2.2)
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

theorem meanL_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (List ℚ) ↦ meanL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encM)) encV := by
  unfold meanL
  set E := encPair encUnary (encPair encUnary encM)
  have hn : ComputableInPolyTime (fun p : (ℕ × ℕ × List (List ℚ)) × ℕ ↦ p.1.1)
      (encPair E encUnary) encUnary := (fst _ _).comp (fst _ _)
  have hP : ComputableInPolyTime (fun p : ((ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ p.1.1.2.2)
      (encPair (encPair E encUnary) encUnary) encM :=
    (snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))
  exact mapWithInput (range.comp ((fst _ _).comp (snd _ _)))
    (rat_div' (rat_sum' (mapWithInput (range.comp hn)
      (ent' hP (snd _ _) ((snd _ _).comp (fst _ _))))) (rat_ofUnary hn))

@[fun_prop]
theorem meanL' {n d : α → ℕ} {P : α → List (List ℚ)} (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hP : ComputableInPolyTime P input encM) :
    ComputableInPolyTime (fun x ↦ meanL (n x) (d x) (P x)) input encV :=
  meanL_polytime.comp (g := fun x ↦ (n x, d x, P x)) (hn.prod (hd.prod hP))

theorem centL_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (List ℚ) × List ℚ ↦ centL p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encM encV))) encM := by
  unfold centL
  set E := encPair encUnary (encPair encUnary (encPair encM encV))
  have hd : ComputableInPolyTime (fun p : (ℕ × ℕ × List (List ℚ) × List ℚ) × ℕ ↦ p.1.2.1)
      (encPair E encUnary) encUnary := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hP : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List (List ℚ) × List ℚ) × ℕ) × ℕ ↦ p.1.1.2.2.1)
      (encPair (encPair E encUnary) encUnary) encM :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _))))
  have hmu : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List (List ℚ) × List ℚ) × ℕ) × ℕ ↦ p.1.1.2.2.2)
      (encPair (encPair E encUnary) encUnary) encV :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((fst _ _).comp (fst _ _))))
  exact mapWithInput (range.comp (fst _ _)) (mapWithInput (range.comp hd)
    (rat_sub' (ent' hP ((snd _ _).comp (fst _ _)) (snd _ _)) (vget' hmu (snd _ _))))

@[fun_prop]
theorem centL' {n d : α → ℕ} {P : α → List (List ℚ)} {mu : α → List ℚ}
    (hn : ComputableInPolyTime n input encUnary) (hd : ComputableInPolyTime d input encUnary)
    (hP : ComputableInPolyTime P input encM) (hmu : ComputableInPolyTime mu input encV) :
    ComputableInPolyTime (fun x ↦ centL (n x) (d x) (P x) (mu x)) input encM :=
  centL_polytime.comp (g := fun x ↦ (n x, d x, P x, mu x)) (hn.prod (hd.prod (hP.prod hmu)))

theorem covL_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ × List (List ℚ) ↦ covL p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encM)) encM := by
  unfold covL
  set E := encPair encUnary (encPair encUnary encM)
  set E2 := encPair (encPair E encUnary) encUnary
  have hd : ComputableInPolyTime (fun p : (ℕ × ℕ × List (List ℚ)) × ℕ ↦ p.1.2.1)
      (encPair E encUnary) encUnary := (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ ↦ p.1.1.1) E2
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hc : ComputableInPolyTime (fun p : (((ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ p.1.1.1.2.2)
      (encPair E2 encUnary) encM :=
    (snd _ _).comp ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
  have ha : ComputableInPolyTime (fun p : (((ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ p.1.1.2)
      (encPair E2 encUnary) encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hb : ComputableInPolyTime (fun p : (((ℕ × ℕ × List (List ℚ)) × ℕ) × ℕ) × ℕ ↦ p.1.2)
      (encPair E2 encUnary) encUnary := (snd _ _).comp (fst _ _)
  exact mapWithInput (range.comp ((fst _ _).comp (snd _ _))) (mapWithInput (range.comp hd)
    (rat_div' (rat_sum' (mapWithInput (range.comp hn)
      (rat_mul' (ent' hc (snd _ _) ha) (ent' hc (snd _ _) hb)))) (rat_ofUnary hn)))

@[fun_prop]
theorem covL' {n d : α → ℕ} {cs : α → List (List ℚ)} (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary) (hc : ComputableInPolyTime cs input encM) :
    ComputableInPolyTime (fun x ↦ covL (n x) (d x) (cs x)) input encM :=
  covL_polytime.comp (g := fun x ↦ (n x, d x, cs x)) (hn.prod (hd.prod hc))

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

@[fun_prop]
theorem basisL' {d : α → ℕ} {C : α → List (List ℚ)} (hd : ComputableInPolyTime d input encUnary)
    (hC : ComputableInPolyTime C input encM) :
    ComputableInPolyTime (fun x ↦ basisL (d x) (C x)) input encM :=
  basisL_polytime.comp (g := fun x ↦ (d x, C x)) (hd.prod hC)

end BS23.Colinear.PT
