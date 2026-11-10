module

public import ABBKS26.Assembly.ExecNestedAuxLayout

/-! # Semantics of the sparse nested expansion -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common MvPolynomial
open SoS.Solver (RawPoly)
open scoped BigOperators

noncomputable section

private def liftRaw (d n : ℕ) (p : RawPoly) : Rounding.Template d :=
  eval₂Hom (C.comp (C.comp (Rat.castHom ℝ)))
    (Fin.addCases X (fun i : Fin n ↦ C (X i.val))) (p.toPoly (d + n))

private theorem lift_append (d n : ℕ) (p q : RawPoly) :
    liftRaw d n (p ++ q) = liftRaw d n p + liftRaw d n q := by
  simp [liftRaw, SoS.Poly.toPoly_append]

private theorem lift_mul (d n : ℕ) (p q : RawPoly) :
    liftRaw d n (SoS.Coords.mulRaw (d + n) p q) = liftRaw d n p * liftRaw d n q := by
  simp [liftRaw, SoS.Coords.toPoly_mulRaw]

private theorem lift_constant (d n : ℕ) (c : ℚ) :
    liftRaw d n (constant c) = C (C (c : ℝ)) := by
  simp [liftRaw, constant_toPoly]

private theorem lift_scale (d n : ℕ) (c : ℚ) (p : RawPoly) :
    liftRaw d n (scale c p) = C (C (c : ℝ)) * liftRaw d n p := by
  simp [liftRaw, scale_toPoly]

private theorem lift_list (d n : ℕ) (p : RawPoly) :
    liftRaw d n p = (p.map fun t ↦
      monomial (SoS.Mono.toFinsupp d t.1)
        (decode n [(t.1.drop d, t.2)])).sum := by
  unfold liftRaw
  rw [SoS.Solver.RawPoly.toPoly, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, map_mul, map_prod, map_pow, eval₂Hom_C,
    eval₂Hom_X', RingHom.comp_apply, Fin.prod_univ_add, Fin.addCases_left,
    Fin.addCases_right]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ ↦ by simp)]
  have hd : decode n [(t.1.drop d, t.2)] =
      C (t.2 : ℝ) * ∏ i : Fin n, X i.val ^ t.1.getD (d + i.val) 0 := by
    simp [decode, SoS.Solver.RawPoly.toPoly, SoS.toReal, List.getD_eq_getElem?_getD,
      List.getElem?_drop]
  rw [hd, map_mul, map_prod]
  simp only [SoS.Mono.toFinsupp_apply, Fin.val_castAdd, Fin.val_natAdd,
    ← map_pow, Rat.coe_castHom]
  ring

private theorem lift_split (d n : ℕ) (p : RawPoly) (μ : List ℕ) (hμ : μ.length = d) :
    (liftRaw d n p).coeff (SoS.Mono.toFinsupp d μ) =
      decode n (Rounding.splitCoeffsRaw d μ p) := by
  rw [lift_list]
  induction p with
  | nil => simp [decode, Rounding.splitCoeffsRaw, SoS.Solver.RawPoly.toPoly, SoS.toReal]
  | cons t p ih =>
    simp only [List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih]
    by_cases he : SoS.Poly.expo d t.1 = μ
    · have hf : SoS.Mono.toFinsupp d t.1 = SoS.Mono.toFinsupp d μ := by
        rw [← SoS.Poly.toFinsupp_expo d t.1, he]
      have hs : Rounding.splitCoeffsRaw d μ (t :: p) =
          [(t.1.drop d, t.2)] ++ Rounding.splitCoeffsRaw d μ p := by
        simp [Rounding.splitCoeffsRaw, he]
      rw [hs, decode_append]
      simp only [coeff_monomial, hf, ↓reduceIte]
    · have hf : SoS.Mono.toFinsupp d t.1 ≠ SoS.Mono.toFinsupp d μ := by
        intro h
        apply he
        apply SoS.Mono.toFinsupp_inj (SoS.Poly.length_expo _ _) hμ
        simpa only [SoS.Poly.toFinsupp_expo] using h
      simp [coeff_monomial, hf, Rounding.splitCoeffsRaw, he]

private theorem lift_single_append (d n : ℕ) (e f : List ℕ) (c : ℚ)
    (he : e.length = d) :
    liftRaw d n [(e ++ f, c)] =
      C (decode n [(f, c)]) * monomial (SoS.Mono.toFinsupp d e) 1 := by
  rw [lift_list]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hpre : SoS.Mono.toFinsupp d (e ++ f) = SoS.Mono.toFinsupp d e := by
    ext i
    exact List.getD_append _ _ _ _ (by omega)
  rw [hpre, ← he, List.drop_left, C_mul_monomial, mul_one]

private theorem lift_terms (d n : ℕ) (p : RawPoly) :
    liftRaw d n p = (p.map fun t ↦ liftRaw d n [t]).sum := by
  rw [lift_list]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [lift_list, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem lift_flatMap {α : Type} (d n : ℕ) (l : List α) (f : α → RawPoly) :
    liftRaw d n (l.flatMap f) = (l.map fun a ↦ liftRaw d n (f a)).sum := by
  induction l with
  | nil => simp [liftRaw, SoS.Solver.RawPoly.toPoly]
  | cons a l ih => simp [lift_append, ih]

private theorem lift_embed (d n : ℕ) (p : RawPoly)
    (hp : ∀ t ∈ p, t.1.length ≤ d) :
    liftRaw d n p = Rounding.embedCoeff (SoS.toReal (p.toPoly d)) := by
  rw [lift_list, Rounding.embedCoeff, SoS.Poly.toPoly_eq_sum']
  simp only [SoS.toReal, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have he : t.1.drop d = [] := List.drop_eq_nil_iff.2 (hp t ht)
  simp [he, decode, SoS.Solver.RawPoly.toPoly, SoS.toReal, SoS.Poly.termPoly]

private theorem lift_clean (d n : ℕ) (p : RawPoly) :
    liftRaw d n (clean d p) = Rounding.embedCoeff (SoS.toReal (p.toPoly d)) := by
  rw [lift_embed, clean_toPoly]
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 ht
  simp

private theorem lift_unit (n i e : ℕ) (hi : i < n) :
    decode n [(unitExp n i e, (1 : ℚ))] = (X i : Rounding.NPoly) ^ e := by
  simp [decode, unit_toPoly n i e 1 hi, SoS.toReal]

private theorem lift_gram (I : Rounding.RawInput) (s : ℕ) (M : List (List ℕ))
    (hM : ∀ e ∈ M, e.length = I.family.dimension)
    (hs : s + M.length ^ 2 ≤ numVars I) :
    liftRaw I.family.dimension (numVars I) (gramRaw I s M) =
      Rounding.gram s (M.map (SoS.Mono.toFinsupp I.family.dimension)) := by
  unfold gramRaw
  rw [lift_flatMap, SoS.Coords.sum_range_map]
  unfold Rounding.gram
  have hlen : (M.map (SoS.Mono.toFinsupp I.family.dimension)).length = M.length := by simp
  conv_rhs => rw [← Fin.sum_congr' _ hlen.symm]
  apply Finset.sum_congr rfl
  intro c _
  rw [lift_mul, ← pow_two]
  congr 1
  conv_rhs => rw [← Fin.sum_congr' _ hlen.symm]
  rw [lift_terms, List.map_map, SoS.Coords.sum_map_getElem]
  have hz : M.zipIdx.length = M.length := by simp
  conv_lhs => rw [← Fin.sum_congr' _ hz.symm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.getElem_fin, List.getElem_zipIdx, List.getElem_map, Fin.val_cast,
    Function.comp_apply, Nat.zero_add, List.length_map]
  rw [lift_single_append _ _ _ _ _ (hM _ (List.getElem_mem a.isLt))]
  rw [lift_unit _ _ _ ((Rounding.RawAux.matrix_index a.isLt c.isLt).trans_le hs), pow_one]

private theorem prefix_sum {α : Type} (l : List α) (f : α → ℕ) (z : α)
    (j : ℕ) (hj : j ≤ l.length) :
    ((l.take j).map f).sum = ((List.range j).map fun i ↦ f (l.getD i z)).sum := by
  rw [SoS.Coords.sum_map_getElem, SoS.Coords.sum_range_map]
  rw [← Fin.sum_congr' _ (List.length_take_of_le hj).symm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin, Fin.val_cast, List.getElem_take,
    List.getD_eq_getElem _ _ (i.isLt.trans_le hj)]

private theorem plain_offset (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j ≤ I.family.plain.length + 1) :
    plainStart I j = Rounding.plainOffset I.family.real I.degree j := by
  unfold plainStart Rounding.plainOffset
  rw [prefix_sum (plainBases I) (fun M ↦ M.length ^ 2) [] j (by simpa [plainBases] using hj)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [plain_rows I hfuel i ((List.mem_range.1 hi).trans_le hj)]

private theorem slot_offset (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a ≤ (slots I).length) :
    slotStart I a = Rounding.slotOffset I.family.real I.degree a := by
  unfold slotStart Rounding.slotOffset
  rw [prefix_sum (slots I)
    (fun s ↦ ((familyBases I).getD s []).length ^ 2 + I.family.dimension ^ 2) 0 a ha]
  have hlen : (plainBases I).length = I.family.plain.length + 1 := by simp [plainBases]
  rw [hlen, plain_offset I hfuel _ le_rfl]
  have hplain : I.family.real.plain.length = I.family.plain.length := by
    simp [Rounding.RawFamily.real]
  rw [hplain]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' := (List.mem_range.1 hi).trans_le ha
  have hslot : (slots I).getD i 0 < I.family.families.length := by
    have hm : (slots I).getD i 0 ∈ slots I := by
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    simpa only [decide_eq_true_eq] using (List.mem_filter.1 hm).2
  rw [family_rows I hfuel _ hslot]
  have hh : (I.family.real.slots[i]?.map Fin.val |>.getD 0) = (slots I).getD i 0 := by
    rw [slots_agree]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [hh]

private def replacePoly (I : Rounding.RawInput) (a : ℕ)
    (i : Fin (2 * I.family.dimension)) : Rounding.Template I.family.dimension :=
  let d := I.family.dimension
  let M := (familyBases I).getD ((slots I).getD a 0) []
  if h : i.val < d then
    ∑ j : Fin d, C (X (slotStart I a + M.length ^ 2 + i.val * d + j.val)) * X j
  else X ⟨i.val - d, by omega⟩

private theorem lift_replacement (I : Rounding.RawInput) (a : ℕ)
    (i : Fin (2 * I.family.dimension))
    (hs : slotStart I a +
      ((familyBases I).getD ((slots I).getD a 0) []).length ^ 2 +
        I.family.dimension ^ 2 ≤ numVars I) :
    liftRaw I.family.dimension (numVars I) (replacement I a i.val) = replacePoly I a i := by
  by_cases hi : i.val < I.family.dimension
  · simp only [replacement, hi, ↓reduceIte, replacePoly]
    rw [lift_terms, List.map_map, SoS.Coords.sum_range_map]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [Function.comp_apply]
    rw [lift_single_append _ _ _ _ _ (by simp [unitExp]),
      lift_unit _ _ _ ((Rounding.RawAux.matrix_index hi j.isLt).trans_le hs), pow_one]
    rw [unitExp_toFinsupp _ _ _ j.isLt]
    simp only [← X_pow_eq_monomial, pow_one]
  · simp only [replacement, hi, ↓reduceIte, replacePoly]
    have hj : i.val - I.family.dimension < I.family.dimension := by omega
    rw [lift_embed]
    · rw [unit_toPoly _ _ _ _ hj]
      simp [Rounding.embedCoeff, SoS.toReal]
    · intro t ht
      obtain rfl := List.mem_singleton.1 ht
      simp [unitExp]

private theorem clean_term_degree (v : ℕ) (p : RawPoly) (t : List ℕ × ℚ)
    (ht : t ∈ clean v p) : t.1.length = v ∧ t.1.sum ≤ SoS.Poly.degree v p := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  refine ⟨by simp, ?_⟩
  exact SoS.Poly.le_foldl_max (List.mem_map_of_mem
    (f := fun s : List ℕ × ℚ ↦ (SoS.Poly.expo v s.1).sum) hs) 0

private theorem expo_eq (v : ℕ) (e : List ℕ) (he : e.length = v) :
    SoS.Poly.expo v e = e := by
  apply List.ext_getElem (by simp [he])
  intro i hi hi'
  simp only [SoS.Poly.expo, List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ hi'

private theorem getD_le_sum (e : List ℕ) (i : ℕ) : e.getD i 0 ≤ e.sum := by
  by_cases hi : i < e.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

private theorem fuel_pow (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) : (I.family.dimension + 1) ^ I.degree ≤ I.fuel := by
  have hd := Rounding.RawAux.dimension_le_vars I.family.real I.degree
  exact ((Nat.pow_le_pow_left (by omega) _).trans
    (Nat.pow_le_pow_right (by omega) (by omega))).trans hfuel

private theorem replacement_length (I : Rounding.RawInput) (a i : ℕ) :
    (replacement I a i).length ≤ I.family.dimension + 1 := by
  unfold replacement
  dsimp only
  split_ifs <;> simp

private theorem replacement_ne_nil (I : Rounding.RawInput) (a : ℕ)
    (i : Fin (2 * I.family.dimension)) : replacement I a i.val ≠ [] := by
  unfold replacement
  dsimp only
  split_ifs with hi
  · have hd : 0 < I.family.dimension := by omega
    intro h
    have hh := congrArg List.length h
    simp only [List.length_map, List.length_range, List.length_nil] at hh
    omega
  · simp

private theorem prod_range_map {M : Type} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range m).map f).prod = ∏ i : Fin m, f i.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Fin.prod_univ_castSucc]
    simp

private theorem prod_flatMap {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a ↦ (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem lift_substitute (I : Rounding.RawInput) (a : ℕ) (p : RawPoly)
    (hdeg : SoS.Poly.degree (2 * I.family.dimension) p ≤ I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hs : slotStart I a +
      ((familyBases I).getD ((slots I).getD a 0) []).length ^ 2 +
        I.family.dimension ^ 2 ≤ numVars I) :
    liftRaw I.family.dimension (numVars I) (substitute I a p) =
      eval₂Hom (C.comp (C.comp (Rat.castHom ℝ))) (replacePoly I a)
        (p.toPoly (2 * I.family.dimension)) := by
  rw [← clean_toPoly (2 * I.family.dimension) p]
  unfold substitute
  rw [lift_flatMap, SoS.Solver.RawPoly.toPoly, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  obtain ⟨hlen, hsum⟩ := clean_term_degree _ p t ht
  have hsum' := hsum.trans hdeg
  have hcap (i : ℕ) : min (t.1.getD i 0) I.degree = t.1.getD i 0 :=
    min_eq_left ((getD_le_sum t.1 i).trans hsum')
  simp only [hcap]
  let fs := (List.range (2 * I.family.dimension)).flatMap fun i ↦
    List.replicate (t.1.getD i 0) (replacement I a i)
  have hlength : fs.length = t.1.sum := by
    simp only [fs, List.length_flatMap, List.length_replicate]
    exact congrArg List.sum (expo_eq _ _ hlen)
  have hne : ∀ f ∈ fs, f ≠ [] := by
    intro f hf
    obtain ⟨i, hi, hf⟩ := List.mem_flatMap.1 hf
    have hf' := (List.mem_replicate.1 hf).2
    subst f
    exact replacement_ne_nil I a ⟨i, List.mem_range.1 hi⟩
  have hbound : (fs.map List.length).prod ≤ I.fuel := by
    apply le_trans _ (fuel_pow I hfuel)
    calc
      _ ≤ (I.family.dimension + 1) ^ (fs.map List.length).length :=
        List.prod_le_pow_length _ _ (by
          intro n hn
          obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hn
          obtain ⟨i, _, hf⟩ := List.mem_flatMap.1 hf
          rw [(List.mem_replicate.1 hf).2]
          exact replacement_length I a i)
      _ ≤ (I.family.dimension + 1) ^ I.degree := by
        simp only [List.length_map, hlength]
        exact Nat.pow_le_pow_right (by omega) hsum'
  rw [lift_scale]
  change C (C (t.2 : ℝ)) * liftRaw _ _ (SoS.Poly.prodRaw _ _ fs) = _
  unfold liftRaw
  rw [SoS.Poly.toPoly_prodRaw hne hbound, map_list_prod]
  simp only [fs, List.map_flatMap, List.map_replicate, prod_flatMap,
    List.prod_replicate, Function.comp_apply, map_mul, map_prod, map_pow,
    eval₂Hom_C, RingHom.comp_apply, eval₂Hom_X']
  rw [prod_range_map]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← lift_replacement I a i hs]
  rfl

private theorem plain_basis_monos (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j < I.family.plain.length + 1) :
    ((plainBases I).getD j []).map (SoS.Mono.toFinsupp I.family.dimension) =
      Rounding.monos I.family.dimension
        ((I.degree - ((Rounding.constraintsWithOne I.family.real).getD j 0).totalDegree) / 2) := by
  have hj' : j < (constant 1 :: I.family.plain).length := by simpa using hj
  rw [plainBases, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
    bases_uncapped I hfuel _ (by omega)]
  rw [show ((Rounding.constraintsWithOne I.family.real).getD j 0).totalDegree =
    SoS.Poly.degree I.family.dimension ((constant 1 :: I.family.plain)[j]) by
      simpa only [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem?_getD]
        using plain_degree I j]
  rfl

private theorem family_basis_monos (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (s : ℕ) (hs : s < I.family.families.length) :
    ((familyBases I).getD s []).map (SoS.Mono.toFinsupp I.family.dimension) =
      Rounding.monos I.family.dimension
        ((I.degree - (I.family.real.families.getD s 0).totalDegree) / 2) := by
  rw [familyBases, List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map,
    bases_uncapped I hfuel _ (by omega)]
  have hs' : s < I.family.real.families.length := by simpa [Rounding.RawFamily.real] using hs
  rw [List.getD_eq_getElem _ _ hs']
  simp only [Rounding.RawFamily.real, List.getElem_map, family_degree]
  rfl

private theorem plain_basis_lengths (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j < I.family.plain.length + 1) :
    ∀ e ∈ (plainBases I).getD j [], e.length = I.family.dimension := by
  have hj' : j < (constant 1 :: I.family.plain).length := by simpa using hj
  rw [plainBases, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
    bases_uncapped I hfuel _ (by omega)]
  exact fun e he ↦ (SoS.Mono.mem_all.1 he).1

private theorem family_basis_lengths (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (s : ℕ) (hs : s < I.family.families.length) :
    ∀ e ∈ (familyBases I).getD s [], e.length = I.family.dimension := by
  rw [familyBases, List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map,
    bases_uncapped I hfuel _ (by omega)]
  exact fun e he ↦ (SoS.Mono.mem_all.1 he).1

private theorem slot_label (I : Rounding.RawInput) (a : ℕ) :
    (I.family.real.slots[a]?.map Fin.val |>.getD 0) = (slots I).getD a 0 := by
  rw [slots_agree]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]

private theorem slot_in_range (I : Rounding.RawInput) (a : ℕ) (ha : a < (slots I).length) :
    (slots I).getD a 0 < I.family.families.length := by
  have hm : (slots I).getD a 0 ∈ slots I := by
    rw [List.getD_eq_getElem _ _ ha]
    exact List.getElem_mem ha
  simpa [slots] using (List.mem_filter.1 hm).2

private theorem slot_storage (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a < (slots I).length) :
    slotStart I a + ((familyBases I).getD ((slots I).getD a 0) []).length ^ 2 +
      I.family.dimension ^ 2 ≤ numVars I := by
  rw [slot_offset I hfuel _ ha.le, family_rows I hfuel _ (slot_in_range I a ha),
    vars_agree I hfuel, ← slot_label]
  apply Rounding.RawAux.slot_block
  simpa only [slots_agree, List.length_map] using ha

private theorem lift_plain_block (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j < I.family.plain.length + 1) :
    liftRaw I.family.dimension (numVars I)
      (SoS.Coords.mulRaw (I.family.dimension + numVars I)
        (gramRaw I (plainStart I j) ((plainBases I).getD j []))
        (clean I.family.dimension ((constant 1 :: I.family.plain).getD j []))) =
      Rounding.gram (Rounding.plainOffset I.family.real I.degree j)
        (Rounding.monos I.family.dimension ((I.degree -
          ((Rounding.constraintsWithOne I.family.real).getD j 0).totalDegree) / 2)) *
        Rounding.embedCoeff ((Rounding.constraintsWithOne I.family.real).getD j 0) := by
  rw [lift_mul, lift_gram I _ _ (plain_basis_lengths I hfuel j hj),
    plain_basis_monos I hfuel j hj, plain_offset I hfuel j hj.le, lift_clean]
  · congr 2
    change SoS.toReal (((constant 1 :: I.family.plain).getD j []).toPoly I.family.dimension) = _
    rw [← plain_decode I]
    have hj' : j < (constant 1 :: I.family.plain).length := by simpa using hj
    have hj'' : j < ((constant 1 :: I.family.plain).map fun p ↦
        SoS.toReal (p.toPoly I.family.dimension)).length := by simpa using hj'
    rw [List.getD_eq_getElem _ _ hj'', List.getElem_map,
      List.getD_eq_getElem _ _ hj']
  · rw [plain_offset I hfuel j hj.le, plain_rows I hfuel j hj, vars_agree I hfuel]
    apply Rounding.RawAux.plain_block
    simpa [Rounding.RawFamily.real] using hj

private theorem family_eval (d : ℕ)
    (ψ : Fin d ⊕ Fin d → Rounding.Template d) (p : MvPolynomial (Fin (d + d)) ℚ) :
    eval₂Hom (C.comp (C.comp (Rat.castHom ℝ))) (fun i ↦ ψ (Rounding.sumIndex d i)) p =
      aeval ψ ((rename (Rounding.sumIndex d) (SoS.toReal p)).map
        (C : ℝ →+* Rounding.NPoly)) := by
  have he : eval₂Hom (C.comp (C.comp (Rat.castHom ℝ)))
      (fun i ↦ ψ (Rounding.sumIndex d i)) =
      (aeval ψ).toRingHom.comp ((map (C : ℝ →+* Rounding.NPoly)).comp
        ((rename (Rounding.sumIndex d)).toRingHom.comp (map (algebraMap ℚ ℝ)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [algebraMap_eq]
    · intro i
      simp
  exact congrArg (fun f : MvPolynomial (Fin (d + d)) ℚ →+* Rounding.Template d ↦ f p) he

private theorem replacement_agrees (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a < (slots I).length)
    (i : Fin (2 * I.family.dimension)) :
    replacePoly I a i =
      Sum.elim (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val)
        X (Rounding.sumIndex I.family.dimension ⟨i.val, by omega⟩) := by
  unfold replacePoly
  dsimp only
  rw [slot_offset I hfuel a ha.le, family_rows I hfuel _ (slot_in_range I a ha),
    ← slot_label I a]
  by_cases hi : i.val < I.family.dimension
  · simp only [hi, ↓reduceDIte, Rounding.sumIndex, Sum.elim_inl, Rounding.xiLin]
  · simp only [hi, ↓reduceDIte, Rounding.sumIndex, Sum.elim_inr]

private theorem family_value (I : Rounding.RawInput) (s : ℕ)
    (hs : s < I.family.families.length) :
    I.family.real.families.getD s 0 =
      rename (Rounding.sumIndex I.family.dimension)
        (SoS.toReal ((I.family.families.getD s []).toPoly
          (I.family.dimension + I.family.dimension))) := by
  have hs' : s < I.family.real.families.length := by simpa [Rounding.RawFamily.real] using hs
  rw [List.getD_eq_getElem _ _ hs', List.getD_eq_getElem _ _ hs]
  simp only [Rounding.RawFamily.real, List.getElem_map]

private theorem raw_eval_cast {R : Type} [CommSemiring R] (v w : ℕ) (h : v = w)
    (p : RawPoly) (f : ℚ →+* R) (g : Fin w → R) :
    eval₂Hom f (fun i ↦ g (i.cast h)) (p.toPoly v) = eval₂Hom f g (p.toPoly w) := by
  subst w
  rfl

private theorem cast_family_eval (I : Rounding.RawInput) (a : ℕ) (p : RawPoly) :
    eval₂Hom (C.comp (C.comp (Rat.castHom ℝ)))
      (fun i : Fin (2 * I.family.dimension) ↦
        Sum.elim (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val)
          X (Rounding.sumIndex I.family.dimension ⟨i.val, by omega⟩))
      (p.toPoly (2 * I.family.dimension)) =
      aeval (Sum.elim
        (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val) X)
        ((rename (Rounding.sumIndex I.family.dimension)
          (SoS.toReal (p.toPoly (I.family.dimension + I.family.dimension)))).map
            (C : ℝ →+* Rounding.NPoly)) := by
  let ψ : Fin I.family.dimension ⊕ Fin I.family.dimension →
      Rounding.Template I.family.dimension :=
    Sum.elim (fun j ↦ Rounding.xiLin I.family.real I.degree a j.val) X
  have hcast := raw_eval_cast (2 * I.family.dimension)
    (I.family.dimension + I.family.dimension) (two_mul I.family.dimension) p
    (C.comp (C.comp (Rat.castHom ℝ))) (fun i ↦ ψ (Rounding.sumIndex I.family.dimension i))
  exact hcast.trans (family_eval I.family.dimension ψ
    (p.toPoly (I.family.dimension + I.family.dimension)))

private theorem family_raw_degree (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree) (s : ℕ) (hs : s < I.family.families.length) :
    SoS.Poly.degree (2 * I.family.dimension) (I.family.families.getD s []) ≤ I.degree := by
  rw [← family_degree, ← family_value I s hs]
  apply hI.2.2
  rw [List.getD_eq_getElem _ _ (by simpa [Rounding.RawFamily.real] using hs)]
  exact List.getElem_mem _

private theorem substitute_agrees (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a < (slots I).length) :
    liftRaw I.family.dimension (numVars I)
      (substitute I a (I.family.families.getD ((slots I).getD a 0) [])) =
      aeval (Sum.elim
        (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val) X)
        ((I.family.real.families.getD ((slots I).getD a 0) 0).map
          (C : ℝ →+* Rounding.NPoly)) := by
  have hs := slot_in_range I a ha
  rw [lift_substitute I a _ (family_raw_degree I hI _ hs) hfuel
    (slot_storage I hfuel a ha), family_value I _ hs]
  have he : replacePoly I a = fun i ↦
      Sum.elim (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val)
        X (Rounding.sumIndex I.family.dimension ⟨i.val, by omega⟩) := by
    funext i
    exact replacement_agrees I hfuel a ha i
  rw [he]
  exact cast_family_eval I a _

private theorem lift_family_block (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a < (slots I).length) :
    liftRaw I.family.dimension (numVars I)
      (SoS.Coords.mulRaw (I.family.dimension + numVars I)
        (gramRaw I (slotStart I a) ((familyBases I).getD ((slots I).getD a 0) []))
        (substitute I a (I.family.families.getD ((slots I).getD a 0) []))) =
      Rounding.gram (Rounding.slotOffset I.family.real I.degree a)
        (Rounding.monos I.family.dimension ((I.degree -
          (I.family.real.families.getD ((slots I).getD a 0) 0).totalDegree) / 2)) *
        aeval (Sum.elim
          (fun j : Fin I.family.dimension ↦ Rounding.xiLin I.family.real I.degree a j.val) X)
          ((I.family.real.families.getD ((slots I).getD a 0) 0).map
            (C : ℝ →+* Rounding.NPoly)) := by
  have hs := slot_in_range I a ha
  have hstorage := slot_storage I hfuel a ha
  rw [lift_mul, lift_gram I _ _ (family_basis_lengths I hfuel _ hs) (by omega),
    family_basis_monos I hfuel _ hs, slot_offset I hfuel a ha.le,
    substitute_agrees I hI hfuel a ha]

private theorem sum_zipIdx {α M : Type} [AddCommMonoid M] (l : List α) (f : α × ℕ → M) :
    (l.zipIdx.map f).sum = ∑ i : Fin l.length, f (l[i], i.val) := by
  rw [SoS.Coords.sum_map_getElem]
  have hz : l.zipIdx.length = l.length := by simp
  conv_lhs => rw [← Fin.sum_congr' _ hz.symm]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getElem_zipIdx]

private theorem lift_template (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    liftRaw I.family.dimension (numVars I) (templateRaw I) =
      Rounding.template I.family.real I.degree := by
  unfold templateRaw
  rw [lift_append, lift_flatMap, lift_flatMap, sum_zipIdx, sum_zipIdx]
  unfold Rounding.template
  apply congrArg₂ (· + ·)
  · have hlen : I.family.real.plain.length + 1 = (constant 1 :: I.family.plain).length := by
      simp [Rounding.RawFamily.real]
    conv_rhs => rw [← Fin.sum_congr' _ hlen.symm]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    simp only [Fin.getElem_fin]
    have hj : j.val < I.family.plain.length + 1 := by simpa using j.isLt
    rw [← List.getD_eq_getElem _ _ j.isLt, lift_plain_block I hfuel j.val hj]
    have hj' : j.val < (Rounding.constraintsWithOne I.family.real).length := by
      simpa [Rounding.constraintsWithOne, Rounding.RawFamily.real] using hj
    simp only [Fin.val_cast, List.getD_eq_getElem _ _ hj']
  · have hlen : I.family.real.slots.length = (slots I).length := by
      rw [slots_agree, List.length_map]
    conv_rhs => rw [← Fin.sum_congr' _ hlen.symm]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    simp only [Fin.getElem_fin]
    rw [← List.getD_eq_getElem _ _ a.isLt, lift_family_block I hI hfuel a.val a.isLt]
    have ha : a.val < I.family.real.slots.length := by omega
    have hlabel : (I.family.real.slots[a.val]).val = (slots I).getD a.val 0 := by
      simpa only [List.getElem?_eq_getElem ha, Option.map_some, Option.getD_some] using
        slot_label I a.val
    have hs : (slots I).getD a.val 0 < I.family.real.families.length := by
      simpa [Rounding.RawFamily.real] using slot_in_range I a.val a.isLt
    simp only [Fin.val_cast, hlabel, List.getD_eq_getElem _ _ hs]

private theorem lift_target (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    liftRaw I.family.dimension (numVars I)
      (constant (4 * I.epsilon) ++ scale (-1)
        (SoS.Coords.mulRaw (I.family.dimension + numVars I)
          ((List.range I.family.dimension).map fun i ↦
            (unitExp I.family.dimension i 1 ++ unitExp (numVars I) i 1, (1 : ℚ)))
          ((List.range I.family.dimension).map fun i ↦
            (unitExp I.family.dimension i 1 ++ unitExp (numVars I) i 1, (1 : ℚ))))) =
      Rounding.target (d := I.family.dimension) I.epsilon := by
  have hd : I.family.dimension ≤ numVars I := by
    rw [vars_agree I hfuel]
    exact Rounding.RawAux.dimension_le_vars _ _
  rw [lift_append, lift_constant, lift_scale, lift_mul]
  have huv : liftRaw I.family.dimension (numVars I)
      ((List.range I.family.dimension).map fun i ↦
        (unitExp I.family.dimension i 1 ++ unitExp (numVars I) i 1, (1 : ℚ))) =
      ∑ i : Fin I.family.dimension, C (X i.val : Rounding.NPoly) * X i := by
    rw [lift_terms, List.map_map, SoS.Coords.sum_range_map]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [Function.comp_apply]
    rw [lift_single_append _ _ _ _ _ (by simp [unitExp]),
      lift_unit _ _ _ (i.isLt.trans_le hd), pow_one, unitExp_toFinsupp _ _ _ i.isLt]
    simp only [← X_pow_eq_monomial, pow_one]
  rw [huv]
  simp [Rounding.target, pow_two, sub_eq_add_neg]

/-- Sparse coefficient extraction agrees with the analytic nested template. -/
theorem concrete_coefficient_agrees (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (μ : List ℕ)
    (hμ : μ ∈ SoS.Mono.all I.family.dimension I.degree) :
    decode (numVars I) (Rounding.splitCoeffsRaw I.family.dimension μ (residual I)) =
      Rounding.coefficient I.family.real I.degree I.epsilon
        (SoS.Mono.toFinsupp I.family.dimension μ) := by
  rw [← lift_split _ _ _ _ (SoS.Mono.mem_all.1 hμ).1]
  unfold residual
  rw [lift_append, lift_target I hfuel, lift_scale, lift_template I hI hfuel]
  simp [Rounding.coefficient, sub_eq_add_neg]

end

end ABBKS26.Assembly.Exec.NestedProgram
