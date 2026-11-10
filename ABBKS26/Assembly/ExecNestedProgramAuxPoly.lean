module

public import ABBKS26.Assembly.ExecNestedAuxLayout

/-! # Polynomial-time certificates for the capped nested builder -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common
open Encoding (encRat)
open SoS.Solver (RawPoly encRawPoly encProblem)
open Turing.MultiTapeTM ComputableInPolyTime

private abbrev Args := NestedArgs × ℕ
private abbrev encArgs := encPair encNestedArgs encUnary
private abbrev encRows := encList (encList encNat)

private theorem maximum_time : ComputableInPolyTime
    (fun l : List ℕ ↦ l.foldl max 0) (encList encNat) encNat := by
  have hm : ComputableInPolyTime (fun p : ℕ × ℕ ↦ max p.1 p.2)
      (encPair encNat encNat) encNat := by
    have h := ite_decide (binary_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)
    exact h.of_enc_eq fun p ↦ by simp only [max_def]
  refine foldlWith_of_bounded_growth (par := fun l ↦ l) (list := fun l ↦ l)
    (init := fun _ ↦ 0) (step := fun _ s v ↦ max s v) id' id' (const 0)
    (hm.comp (((snd _ _).comp (fst _ _)).prod (snd _ _)))
    (growth := fun l ↦ (encList encNat l).length + 1)
    (PolyBounded.self.add (.const 1)) ?_
  intro l state value hv
  have hv' := SizedListEncoding.length_elem_le (encA := encNat)
    (encL := encList encNat) l value hv
  have hh := (Nat.size_le_size (show max state value ≤ state + value by omega)).trans
    (Nat.size_add_le state value)
  simp only [encNat_apply, Nat.size_eq_bits_len] at hv' ⊢
  omega

private theorem unary_sum_time :
    ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have h : ComputableInPolyTime
      (fun l : List ℕ ↦ l.flatMap fun n ↦ List.replicate n true)
      (encList encUnary) (encList encBool) :=
    flatMapWithInput id' (replicate (snd _ _) (const true))
  exact ((length_list encBool).comp h).of_enc_eq fun l ↦ by
    simp [List.length_flatMap]

@[local fun_prop]
private theorem raw_degree_time {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {p : α → RawPoly}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ SoS.Poly.degree (n a) (p a)) enc encNat := by
  unfold SoS.Poly.degree
  apply maximum_time.comp
  apply mapWithInput (filterWithInput hp (by fun_prop))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp
    (SoS.Poly.expo' (hn.comp (fst _ _)) ((fst _ _).comp (snd _ _))).tidy)

@[local fun_prop]
private theorem binary_of_unary {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) : ComputableInPolyTime n enc encNat :=
  unary_to_binary.comp hn

@[local fun_prop]
private theorem basis_time {α : Type} {enc : α ↪ List Bool}
    {fuel d K : α → ℕ} {p : α → RawPoly}
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hd : ComputableInPolyTime d enc encUnary)
    (hK : ComputableInPolyTime K enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ SoS.Mono.allB (fuel a) (d a)
      ((K a - SoS.Poly.degree (d a) (p a)) / 2)) enc encRows := by
  have hs : ComputableInPolyTime (fun a ↦ K a - SoS.Poly.degree (d a) (p a))
      enc encUnary := by
    have hmin := binary_min_unary' hK (raw_degree_time hd hp)
    have h := unary_sub' hK hmin
    exact h.of_enc_eq fun a ↦ by congr 1; omega
  exact SoS.PolyTime.allBE' hf hd ((unary_div_const 2).comp hs)

@[local fun_prop]
private theorem d_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ (nestedInput (q a)).family.dimension) enc encUnary := by
  dsimp only [nestedInput]
  fun_prop

@[local fun_prop]
private theorem K_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ (nestedInput (q a)).degree) enc encUnary := by
  dsimp only [nestedInput]
  fun_prop

@[local fun_prop]
private theorem fuel_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ (nestedInput (q a)).fuel) enc encUnary := by
  dsimp only [nestedInput]
  fun_prop

@[local fun_prop]
private theorem plain_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ (nestedInput (q a)).family.plain)
      enc (encList encRawPoly) := by
  dsimp only [nestedInput]
  fun_prop

@[local fun_prop]
private theorem families_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ (nestedInput (q a)).family.families)
      enc (encList encRawPoly) := by
  dsimp only [nestedInput]
  fun_prop

@[local fun_prop]
private theorem constant_time {α : Type} {enc : α ↪ List Bool} {c : α → ℚ}
    (hc : ComputableInPolyTime c enc encRat) :
    ComputableInPolyTime (fun a ↦ constant (c a)) enc encRawPoly := by
  unfold constant
  fun_prop

@[local fun_prop]
private theorem plainBases_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ plainBases (nestedInput (q a)))
      enc (encList encRows) := by
  unfold plainBases
  apply mapWithInput (cons' (constant_time (const 1)) (plain_time hq))
  exact basis_time (fuel_time (hq.comp (fst _ _))) (d_time (hq.comp (fst _ _)))
    (K_time (hq.comp (fst _ _))) (snd _ _)

@[local fun_prop]
private theorem familyBases_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ familyBases (nestedInput (q a)))
      enc (encList encRows) := by
  unfold familyBases
  apply mapWithInput (families_time hq)
  have hd := d_time (hq.comp (fst enc encRawPoly))
  have hK := K_time (hq.comp (fst enc encRawPoly))
  have hs : ComputableInPolyTime (fun a : α × RawPoly ↦
      (nestedInput (q a.1)).degree -
        SoS.Poly.degree (2 * (nestedInput (q a.1)).family.dimension) a.2)
      (encPair enc encRawPoly) encUnary := by
    have hmin := binary_min_unary' hK (raw_degree_time (unary_mul' (const 2) hd) (snd _ _))
    exact (unary_sub' hK hmin).of_enc_eq fun a ↦ by
      simp only [Function.comp_apply]
      congr 1
      omega
  exact SoS.PolyTime.allBE' (fuel_time (hq.comp (fst _ _))) hd
    ((unary_div_const 2).comp hs)

@[local fun_prop]
private theorem slots_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ slots (nestedInput (q a))) enc encIndices := by
  unfold slots
  apply filterWithInput
  · dsimp only [nestedInput]
    fun_prop
  · exact binary_lt' (snd _ _)
      (binary_of_unary ((length_list encRawPoly).comp (families_time (hq.comp (fst _ _)))))

@[local fun_prop]
private theorem rows_get_time {α : Type} {enc : α ↪ List Bool}
    {l : α → List (List (List ℕ))} {i : α → ℕ}
    (hl : ComputableInPolyTime l enc (encList encRows))
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun a ↦ (l a).getD (i a) []) enc encRows := by
  exact listGetDWithInput hl hi []

@[local fun_prop]
private theorem plainStart_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {j : α → ℕ} (hq : ComputableInPolyTime q enc encArgs)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a ↦ plainStart (nestedInput (q a)) (j a)) enc encUnary := by
  unfold plainStart
  apply unary_add' (d_time hq)
  apply unary_sum_time.comp
  apply mapWithInput
    (.of_tidy (ComputableTidilyInPolyTime.listTakeWithInput (plainBases_time hq).tidy hj.tidy))
  have hl := (length_list (encList encNat)).comp (snd enc encRows)
  exact (unary_mul' hl hl).of_enc_eq fun a ↦ by congr 1; simp [pow_two]

@[local fun_prop]
private theorem slotStart_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {j : α → ℕ} (hq : ComputableInPolyTime q enc encArgs)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a ↦ slotStart (nestedInput (q a)) (j a)) enc encUnary := by
  unfold slotStart
  apply unary_add' (plainStart_time hq ((length_list encRows).comp (plainBases_time hq)))
  apply unary_sum_time.comp
  apply mapWithInput
    (.of_tidy (ComputableTidilyInPolyTime.listTakeWithInput (slots_time hq).tidy hj.tidy))
  have hrows : ComputableInPolyTime (fun a : α × ℕ ↦
      ((familyBases (nestedInput (q a.1))).getD a.2 []).length)
      (encPair enc encNat) encUnary := by
    exact (length_list (encList encNat)).comp
      (.of_tidy (ComputableTidilyInPolyTime.listGetD_binary []
        (familyBases_time (hq.comp (fst _ _))).tidy (by fun_prop)))
  have hd := d_time (hq.comp (fst enc encNat))
  exact (unary_add' (unary_mul' hrows hrows) (unary_mul' hd hd)).of_enc_eq
    fun a ↦ by congr 1; simp [pow_two]

@[local fun_prop]
private theorem numVars_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun a ↦ numVars (nestedInput (q a))) enc encUnary := by
  unfold numVars
  exact slotStart_time hq ((length_list encNat).comp (slots_time hq))

@[local fun_prop]
private theorem zip_time {α β : Type} {enc : α ↪ List Bool} {e : β ↪ List Bool}
    {l : α → List β} (hl : ComputableInPolyTime l enc (encList e)) :
    ComputableInPolyTime (fun a ↦ (l a).zipIdx) enc (encList (encPair e encUnary)) :=
  .of_tidy ((ComputableTidilyInPolyTime.zipIdx e).comp hl.tidy)

@[local fun_prop]
private theorem gramRaw_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {s : α → ℕ} {M : α → List (List ℕ)}
    (hq : ComputableInPolyTime q enc encArgs) (hs : ComputableInPolyTime s enc encUnary)
    (hM : ComputableInPolyTime M enc encRows) :
    ComputableInPolyTime (fun a ↦ gramRaw (nestedInput (q a)) (s a) (M a))
      enc encRawPoly := by
  unfold gramRaw
  dsimp only
  apply flatMapWithInput (range.comp ((length_list (encList encNat)).comp hM))
  have hrow : ComputableInPolyTime (fun a : α × ℕ ↦
      (M a.1).zipIdx.map fun b ↦
        (b.1 ++ unitExp (numVars (nestedInput (q a.1)))
          (s a.1 + b.2 * (M a.1).length + a.2) 1, (1 : ℚ)))
      (encPair enc encUnary) encRawPoly := by
    apply mapWithInput (zip_time (hM.comp (fst _ _)))
    exact (listAppend' ((fst _ _).comp (snd _ _))
      (unitExp_polytime (numVars_time (hq.comp ((fst _ _).comp (fst _ _))))
        (unary_add'
          (unary_add' (hs.comp ((fst _ _).comp (fst _ _)))
            (unary_mul' ((snd _ _).comp (snd _ _))
              ((length_list (encList encNat)).comp
                (hM.comp ((fst _ _).comp (fst _ _))))))
          ((snd _ _).comp (fst _ _))) (const 1))).prod (const 1)
  exact SoS.PolyTime.mulRaw'
    (unary_add' (d_time (hq.comp (fst _ _))) (numVars_time (hq.comp (fst _ _))))
    hrow hrow

@[local fun_prop]
private theorem index_get_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {a : α → ℕ} (hq : ComputableInPolyTime q enc encArgs)
    (ha : ComputableInPolyTime a enc encUnary) :
    ComputableInPolyTime (fun x ↦ (slots (nestedInput (q x))).getD (a x) 0)
      enc encNat := listGetDWithInput (slots_time hq) ha 0

@[local fun_prop]
private theorem family_rows_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {a : α → ℕ} (hq : ComputableInPolyTime q enc encArgs)
    (ha : ComputableInPolyTime a enc encNat) :
    ComputableInPolyTime (fun x ↦ (familyBases (nestedInput (q x))).getD (a x) [])
      enc encRows :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary [] (familyBases_time hq).tidy ha.tidy)

@[local fun_prop]
private theorem replacement_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {a i : α → ℕ} (hq : ComputableInPolyTime q enc encArgs)
    (ha : ComputableInPolyTime a enc encUnary) (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x ↦ replacement (nestedInput (q x)) (a x) (i x))
      enc encRawPoly := by
  unfold replacement
  dsimp only
  apply ite_decide (unary_lt' hi (d_time hq))
  · apply mapWithInput (range.comp (d_time hq))
    have hq' : ComputableInPolyTime (fun x : α × ℕ ↦ q x.1)
        (encPair enc encUnary) encArgs := hq.comp (fst enc encUnary)
    have hd := d_time hq'
    have hl := (length_list (encList encNat)).comp
      (family_rows_time hq' (index_get_time hq' (ha.comp (fst _ _))))
    have hblock := unary_mul' hl hl
    have hbase := unary_add' (slotStart_time hq' (ha.comp (fst enc encUnary))) hblock
    have hoff := unary_mul' (hi.comp (fst enc encUnary)) hd
    have hind := unary_add' (unary_add' hbase hoff) (snd enc encUnary)
    have hleft := unitExp_polytime hd (snd enc encUnary) (const 1)
    have hright := unitExp_polytime (numVars_time hq') hind (const 1)
    exact ((listAppend' hleft hright).prod
      (const (1 : ℚ) (encOut := encRat))).of_enc_eq fun x ↦ by
      simp only [Function.comp_apply, pow_two]
      rfl
  · exact cons' ((unitExp_polytime (d_time hq)
      (unary_sub' hi (d_time hq)) (const 1)).prod (const 1)) (const [])

@[local fun_prop]
private theorem clean_time {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ clean (d a) (p a)) enc encRawPoly :=
  clean_polytime.comp (hd.prod hp)

@[local fun_prop]
private theorem substitute_time {α : Type} {enc : α ↪ List Bool}
    {q : α → Args} {a : α → ℕ} {p : α → RawPoly}
    (hq : ComputableInPolyTime q enc encArgs) (ha : ComputableInPolyTime a enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun x ↦ substitute (nestedInput (q x)) (a x) (p x))
      enc encRawPoly := by
  unfold substitute
  dsimp only
  apply flatMapWithInput (clean_time (unary_mul' (const 2) (d_time hq)) hp)
  apply scale_polytime ((snd _ _).comp (snd _ _))
  apply SoS.Poly.prodRaw'
    (unary_add' (d_time (hq.comp (fst _ _))) (numVars_time (hq.comp (fst _ _))))
    (fuel_time (hq.comp (fst _ _)))
  apply flatMapWithInput (range.comp (unary_mul' (const 2) (d_time (hq.comp (fst _ _)))))
  have hq' := hq.comp ((fst enc (encPair (encList encNat) encRat)).comp
    (fst (encPair enc (encPair (encList encNat) encRat)) encUnary))
  have he : ComputableInPolyTime (fun x : (α × (List ℕ × ℚ)) × ℕ ↦
      x.1.2.1.getD x.2 0) (encPair (encPair enc (encPair (encList encNat) encRat)) encUnary)
      encNat := by fun_prop
  have hcap := binary_min_unary' (K_time hq') he
  have hrep := replicate hcap
    (replacement_time hq' (ha.comp ((fst _ _).comp (fst _ _))) (snd _ _))
  exact hrep.of_enc_eq fun x ↦ by
    apply congrArg (encList encRawPoly)
    congr 1
    exact min_comm _ _

@[local fun_prop]
private theorem templateRaw_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun x ↦ templateRaw (nestedInput (q x))) enc encRawPoly := by
  unfold templateRaw
  dsimp only
  apply listAppend'
  · apply flatMapWithInput (zip_time (cons' (constant_time (const 1)) (plain_time hq)))
    have hq' := hq.comp (fst enc (encPair encRawPoly encUnary))
    exact SoS.PolyTime.mulRaw' (unary_add' (d_time hq') (numVars_time hq'))
      (gramRaw_time hq' (plainStart_time hq' ((snd _ _).comp (snd _ _)))
        (rows_get_time (plainBases_time hq') ((snd _ _).comp (snd _ _))))
      (clean_time (d_time hq') ((fst _ _).comp (snd _ _)))
  · apply flatMapWithInput (zip_time (slots_time hq))
    have hq' := hq.comp (fst enc (encPair encNat encUnary))
    have ha := (snd encNat encUnary).comp (snd enc (encPair encNat encUnary))
    exact SoS.PolyTime.mulRaw' (unary_add' (d_time hq') (numVars_time hq'))
      (gramRaw_time hq' (slotStart_time hq' ha)
        (family_rows_time hq' ((fst _ _).comp (snd _ _))))
      (substitute_time hq' ha
        (.of_tidy (ComputableTidilyInPolyTime.listGetD_binary [] (families_time hq').tidy
          (by fun_prop))))

@[local fun_prop]
private theorem residual_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun x ↦ residual (nestedInput (q x))) enc encRawPoly := by
  unfold residual
  dsimp only
  have huv : ComputableInPolyTime (fun x ↦
      (List.range (nestedInput (q x)).family.dimension).map fun i ↦
        (unitExp (nestedInput (q x)).family.dimension i 1 ++
          unitExp (numVars (nestedInput (q x))) i 1, (1 : ℚ))) enc encRawPoly := by
    apply mapWithInput (range.comp (d_time hq))
    exact (listAppend' (unitExp_polytime (d_time (hq.comp (fst _ _))) (snd _ _) (const 1))
      (unitExp_polytime (numVars_time (hq.comp (fst _ _))) (snd _ _) (const 1))).prod
        (const 1)
  have hε : ComputableInPolyTime (fun x ↦ (nestedInput (q x)).epsilon) enc encRat := by
    dsimp only [nestedInput]
    fun_prop
  exact listAppend'
    (listAppend' (constant_time (rat_mul' (const 4) hε))
      (scale_polytime (const (-1))
        (SoS.PolyTime.mulRaw' (unary_add' (d_time hq) (numVars_time hq)) huv huv)))
    (scale_polytime (const (-1)) (templateRaw_time hq))

@[local fun_prop]
private theorem normRaw_time {α : Type} {enc : α ↪ List Bool} {n d : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encUnary) :
    ComputableInPolyTime (fun x ↦ normRaw (n x) (d x)) enc encRawPoly := by
  unfold normRaw
  apply mapWithInput (range.comp hd)
  exact (unitExp_polytime (hn.comp (fst _ _)) (snd _ _) (const 2)).prod (const 1)

@[local fun_prop]
private theorem constraints_time {α : Type} {enc : α ↪ List Bool} {q : α → Args}
    (hq : ComputableInPolyTime q enc encArgs) :
    ComputableInPolyTime (fun x ↦ constraints (nestedInput (q x)))
      enc (encList encRawPoly) := by
  unfold constraints
  dsimp only
  have hs := listAppend' (normRaw_time (numVars_time hq) (d_time hq))
    (constant_time (const (-1)))
  apply listAppend'
  · apply listAppend' (cons' hs (cons' (scale_polytime (const (-1)) hs) (const [])))
    apply flatMapWithInput (SoS.PolyTime.allBE' (fuel_time hq) (d_time hq) (K_time hq))
    have hc := split_polytime.comp
      ((d_time (hq.comp (fst _ _))).prod
        ((snd _ _).prod (residual_time (hq.comp (fst _ _)))))
    exact cons' hc (cons' (scale_polytime (const (-1)) hc) (const []))
  · apply cons' _ (const [])
    have hB : ComputableInPolyTime (fun x ↦ (nestedInput (q x)).ball) enc encRat := by
      dsimp only [nestedInput]
      fun_prop
    exact listAppend' (constant_time hB)
      (scale_polytime (const (-1)) (normRaw_time (numVars_time hq) (numVars_time hq)))

private theorem degree_time : ComputableInPolyTime
    (fun q : Args ↦ degree (nestedInput q)) encArgs encNat := by
  unfold degree
  dsimp only
  have hdegrees : ComputableInPolyTime (fun q : Args ↦
      (nestedInput q).family.families.map
        (SoS.Poly.degree (2 * (nestedInput q).family.dimension))) encArgs (encList encNat) := by
    apply mapWithInput (families_time id')
    exact raw_degree_time (unary_mul' (const 2) (d_time (fst _ _))) (snd _ _)
  have hmax := maximum_time.comp hdegrees
  have hK := binary_of_unary (K_time (id' (encIn := encArgs)))
  have hnum := binary_add.comp ((binary_add.comp
    ((binary_mul' (const 2) hK).prod (binary_add.comp ((const 2).prod hmax)))).prod (const 1))
  exact binary_mul' (const 2)
    (binary_div.comp (hnum.prod (const 2)))

/-- The list implementation is polynomial in the entire input, with unary local fuel. -/
theorem concrete_build_polytime : ComputableInPolyTime build
    (encPair encNestedArgs encUnary) encProblem := by
  change ComputableInPolyTime (fun q : Args ↦
    (numVars (nestedInput q), degree (nestedInput q), constraints (nestedInput q), [], []))
    encArgs (encPair encNat (encPair encNat
      (encPair (encList encRawPoly) (encPair encRawPoly (encList encRawPoly)))))
  exact (binary_of_unary (numVars_time id')).prod
    (degree_time.prod ((constraints_time id').prod ((const []).prod (const []))))

end ABBKS26.Assembly.Exec.NestedProgram
