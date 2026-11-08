module

public import BHJK25.RS.Alg.Guess

/-!
# The algorithm decides acceptance

For a valid guess, the points that the algorithm reads are the bit lists of the pairs
`(α_v, β_v)` of the columns (`BHJK25.RS.AlgAux.points_eq`), and the distinct first coordinates
at which a polynomial agrees with them form its agreement set
(`BHJK25.RS.AlgAux.toFinset_agree`). So the decoder decides the acceptance of the guess
(`BHJK25.RS.AlgAux.guessOK_iff`): by `BHJK25.RS.decodeL_spec` when `m ≥ 2`, and otherwise, when
the polynomials are the constants, by `BHJK25.RS.AlgAux.constCheck`
(`BHJK25.RS.AlgAux.constCheck_map`). As the indices run through all guesses, the algorithm
decides `BHJK25.RS.Accept` (`BHJK25.RS.AlgAux.run_eq`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Function

variable {k T n : ℕ}

/-! ### The decoder for constants -/

/-- The decoder for constants, on the bit lists of points: some value is taken at `t ≥ 1`
distinct first coordinates. -/
theorem constCheck_map {F : Type} [DecidableEq F] (e : F → List ℕ) (he : Injective e) {t : ℕ}
    (ht : 1 ≤ t) (pts : List (F × F)) :
    constCheck t (pts.map fun xy ↦ (e xy.1, e xy.2)) = true ↔
      ∃ c, t ≤ ((pts.filter fun xy ↦ xy.2 = c).map Prod.fst).toFinset.card := by
  have hcount : ∀ b : F, ((((pts.map fun xy ↦ (e xy.1, e xy.2)).filter
      fun xy ↦ xy.2 == e b).map Prod.fst).dedup.length) =
        ((pts.filter fun xy ↦ xy.2 = b).map Prod.fst).toFinset.card := by
    intro b
    rw [← List.card_toFinset, List.filter_map, List.map_map]
    have hf : (pts.filter ((fun xy : List ℕ × List ℕ ↦ xy.2 == e b) ∘
        fun xy : F × F ↦ (e xy.1, e xy.2))) = pts.filter fun xy ↦ xy.2 = b := by
      refine List.filter_congr fun xy _ ↦ ?_
      rw [comp_apply, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, he.eq_iff]
    have himg : ∀ l : List F, (l.map e).toFinset = l.toFinset.image e := fun l ↦ by
      ext
      simp
    rw [hf, show (Prod.fst ∘ fun xy : F × F ↦ (e xy.1, e xy.2)) = e ∘ Prod.fst from rfl,
      ← List.map_map, himg, Finset.card_image_of_injective _ he]
  unfold constCheck
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q, hq, hle⟩
    obtain ⟨⟨a, b⟩, -, rfl⟩ := List.mem_map.1 hq
    refine ⟨b, ?_⟩
    rw [← hcount b]
    exact of_decide_eq_true hle
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (Nat.lt_of_lt_of_le ht hc)
    obtain ⟨xy, hxy, -⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨hxy, hc'⟩ := List.mem_filter.1 hxy
    have hc' : xy.2 = c := of_decide_eq_true hc'
    refine ⟨(e xy.1, e xy.2), List.mem_map_of_mem hxy, ?_⟩
    rw [hcount, hc']
    exact decide_eq_true hc

/-! ### The points of a guess -/

/-- The pairs `(α_v, β_v)` of the columns of the guess of `f`, in increasing order of `v`. -/
noncomputable def fieldPoints (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    List (Fld T n × Fld T n) :=
  ((List.finRange n).filter fun v : Fin n ↦
      !decide ((v : ℕ) ∈ digits (mkDat k T n (table M)) (finFunctionFinEquiv f))).map
    fun v ↦ (readElt (guessOf f) 0 M v, readElt (guessOf f) 1 M v)

theorem length_fieldPoints (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    (fieldPoints M f).length ≤ n := by
  unfold fieldPoints
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_finRange).le

/-- **The points of a valid guess** are the bit lists of the pairs of its columns. -/
theorem points_eq (hk : 1 ≤ k) (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (hg : (guessOf f).Valid) :
    points k (mkDat k T n (table M)) (finFunctionFinEquiv f) =
      (fieldPoints M f).map fun xy ↦ (eltList xy.1, eltList xy.2) := by
  unfold points fieldPoints
  rw [show (mkDat k T n (table M)).n = n from rfl, ← List.map_coe_finRange_eq_range,
    List.filter_map, List.map_map, List.map_map]
  refine List.map_congr_left fun v hv ↦ ?_
  have hcol : IsCol (guessOf f) v := by
    have := (List.mem_filter.1 hv).2
    simp only [comp_apply, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact (not_mem_digits (table M) f v).1 this
  simp only [comp_apply, Prod.mk.injEq]
  exact ⟨bitList_eq hk M f hg hcol 0, bitList_eq hk M f hg hcol 1⟩

open Classical in
/-- The distinct first coordinates at which `p` agrees with the points form its agreement set. -/
theorem toFinset_agree (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (p : Polynomial (Fld T n)) :
    (((fieldPoints M f).filter fun xy ↦ p.eval xy.1 = xy.2).map Prod.fst).toFinset =
      agreeSet (guessOf f) M p := by
  ext x
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, fieldPoints, agreeSet,
    Finset.mem_filter, Finset.mem_univ, true_and, List.mem_finRange, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hp⟩, rfl⟩
    exact ⟨v, (not_mem_digits (table M) f v).1 hv, rfl, hp.symm⟩
  · rintro ⟨v, hv, rfl, hp⟩
    exact ⟨_, ⟨⟨v, (not_mem_digits (table M) f v).2 hv, rfl⟩, hp.symm⟩, rfl⟩

theorem eltList_injective : Injective (eltList (T := T) (n := n)) :=
  LeftInverse.injective val_eltList

open Classical in
/-- **The decoder decides the acceptance of a valid guess.** -/
theorem decidePts_iff (hk : 1 ≤ k) (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (hg : (guessOf f).Valid) :
    decidePts (mkDat k T n (table M)) (points k (mkDat k T n (table M)) (finFunctionFinEquiv f)) =
        true ↔
      ∃ p : Polynomial (Fld T n), p.natDegree < mdeg T n ∧
        thr T n ≤ (agreeSet (guessOf f) M p).card := by
  rw [points_eq hk M f hg]
  unfold decidePts
  by_cases hm : 2 ≤ mdeg T n
  · have hm' : 2 ≤ (mkDat k T n (table M)).m := hm
    simp only [hm', ↓reduceIte]
    change decodeL (irrPoly (rbits T n)) ((List.range (2 ^ rbits T n)).map (bitsOf (rbits T n)))
      (mdeg T n) (wdeg T n) _ = true ↔ _
    rw [decodeL_spec T n hm (fieldPoints M f) (length_fieldPoints M f), decide_eq_true_iff]
    simp only [toFinset_agree]
  · have hm1 : mdeg T n = 1 := by have := mdeg_pos T n; omega
    have hm' : ¬2 ≤ (mkDat k T n (table M)).m := hm
    simp only [hm', ↓reduceIte]
    change constCheck (thr T n) _ = true ↔ _
    rw [constCheck_map eltList eltList_injective (by unfold thr; omega)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨Polynomial.C c, by rw [Polynomial.natDegree_C, hm1]; omega, ?_⟩
      rw [← toFinset_agree]
      convert hc using 4
      refine List.filter_congr fun xy _ ↦ ?_
      simp only [Polynomial.eval_C, decide_eq_decide]
      exact eq_comm
    · rintro ⟨p, hp, hc⟩
      obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.1 (show p.natDegree = 0 by omega)
      refine ⟨c, ?_⟩
      rw [← toFinset_agree] at hc
      convert hc using 4
      refine List.filter_congr fun xy _ ↦ ?_
      simp only [Polynomial.eval_C, decide_eq_decide]
      exact eq_comm

/-- **A guess of the algorithm is accepted exactly when it is accepted.** -/
theorem guessOK_iff (hk : 1 ≤ k) (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    guessOK k (mkDat k T n (table M)) (finFunctionFinEquiv f) = true ↔
      AcceptGuess (guessOf f) M := by
  unfold guessOK AcceptGuess
  rw [Bool.and_eq_true, nodupB_digits]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, (decidePts_iff hk M f hg).1 h⟩
  · rintro ⟨hg, h⟩
    exact ⟨hg, (decidePts_iff hk M f hg).2 h⟩

open Classical in
/-- **The algorithm decides acceptance.** -/
theorem run_eq (hk : 1 ≤ k) (M : Tensor k n) : run k T ⟨n, M⟩ = decide (Accept k T n M) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, run, List.any_eq_true]
  simp only [mkDat, List.mem_range]
  constructor
  · rintro ⟨idx, hidx, h⟩
    set f := finFunctionFinEquiv.symm ⟨idx, hidx⟩
    have hf : (finFunctionFinEquiv f : ℕ) = idx := by simp [f]
    rw [← hf] at h
    exact ⟨guessOf f, (guessOK_iff hk M f).1 h⟩
  · rintro ⟨g, hg⟩
    obtain ⟨f, rfl⟩ := guessOf_surjective g
    exact ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).2, (guessOK_iff hk M f).2 hg⟩

end BHJK25.RS.AlgAux
