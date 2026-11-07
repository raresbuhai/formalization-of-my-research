module

public import Background.SumOfSquares.Algorithm.Coords
public import Background.SumOfSquares.Algorithm.PDTestRat

/-!
# The separation oracle, on lists

The oracle of `Background/SumOfSquares/Separation.lean`, computed on lists of rationals. At a
center `c`, every test gives a list of cuts (empty if the test passes):

* `SoS.Oracle.boxCuts`: the coordinates beyond `R`;
* `SoS.Oracle.psdYCuts`, `SoS.Oracle.psdWCuts`: the positive definiteness test of the moment
  matrices of the moments and of each auxiliary sequence, shifted by `τ`
  (`SoS.PDTestRat.test`);
* `SoS.Oracle.distCuts`: the distance constraints.

The oracle (`SoS.Oracle.oracle`) answers with the first cut, or declares the center feasible and
answers with the gradient of the objective (`SoS.Oracle.objSp`). Every cut is valid
(`SoS.Oracle.validAnswer_of_mem_cuts`), no cut means the center is in the set
(`SoS.Oracle.inSet_of_cuts_eq_nil`), and the objective cut keeps the points with smaller
objective (`SoS.Oracle.objective_cut`).
-/

@[expose] public section

namespace SoS.Oracle

open MvPolynomial Matrix SoS.Solver SoS.Poly SoS.Lifted SoS.Coords

/-! ### The tests -/

/-- The vector `a eⱼ` of length `N`. -/
def unitVec (N j : ℕ) (a : ℚ) : List ℚ := (List.range N).map fun i => if i = j then a else 0

/-- A vector, or `e₀` in its place if it is `0`. -/
def orDef (a : List ℚ) : List ℚ :=
  if a.all (fun q => decide (q = 0)) then unitVec a.length 0 1 else a

/-- The cuts of the box: `±eⱼ` for the coordinates beyond `R`. -/
def boxCuts (R : ℚ) (c : List ℚ) : List (List ℚ) :=
  (c.zipIdx.filter fun p => decide (R < |p.1|)).map fun p =>
    unitVec c.length p.2 (if 0 < p.1 then 1 else -1)

/-- The moment matrix of `f` on the monomials `ms`, shifted by `τ`. -/
def momRows (n : ℕ) (f : List ℕ → ℚ) (τ : ℚ) (ms : List (List ℕ)) : List (List ℚ) :=
  (List.range ms.length).map fun i => (List.range ms.length).map fun j =>
    f (addE n (ms.getD i []) (ms.getD j [])) + if i = j then τ else 0

/-- `g²` for `g = ∑ wᵢ x^(msᵢ)`. -/
def sqRaw (n : ℕ) (ms : List (List ℕ)) (w : List ℤ) : RawPoly :=
  mulRaw n (polyRaw ms (w.map (Int.cast : ℤ → ℚ))) (polyRaw ms (w.map (Int.cast : ℤ → ℚ)))

/-- The positive definiteness cut of the moments: `-∇ L(g²)` for the witness `g`. -/
def psdYCuts (n : ℕ) (cs : List Crd) (τ : ℚ) (ms : List (List ℕ)) (c : List ℚ) :
    List (List ℚ) :=
  (PDTestRat.test (momRows n (yv cs c) τ ms)).elim [] fun w =>
    [orDef (dense cs (scale (-1) (spY n (sqRaw n ms w))))]

/-- The positive definiteness cut of the auxiliary sequence of `v`. -/
def psdWCuts (n : ℕ) (cs : List Crd) (τ : ℚ) (v : List ℕ) (ms : List (List ℕ)) (c : List ℚ) :
    List (List ℚ) :=
  (PDTestRat.test (momRows n (wv cs c v) τ ms)).elim [] fun w =>
    [orDef (dense cs (scale (-1) (spW n v (sqRaw n ms w))))]

/-- The residual `L_y(xᵉ f_v) - w_v(e)`, for the product `f_v` of the constraints of `v`. -/
def resid (n : ℕ) (cs : List Crd) (c : List ℚ) (v : List ℕ) (fv : RawPoly) (e : List ℕ) : ℚ :=
  evalY n cs c (shift n e fv) - wv cs c v e

/-- The gradient of the squared residuals, `∑ₑ 2 rₑ ∇rₑ`, sparse. -/
def distSp (n : ℕ) (cs : List Crd) (c : List ℚ) (v : List ℕ) (fv : RawPoly)
    (ms : List (List ℕ)) : Sp :=
  ms.flatMap fun e => scale (2 * resid n cs c v fv e)
    (spY n (shift n e fv) ++ scale (-1) (spW n v [(e, 1)]))

/-- The distance cut of `v`, if `∑ₑ rₑ² > η² ν`, where `ν = ∏ ‖fᵢ‖₂²`. -/
def distCuts (n : ℕ) (cs : List Crd) (η : ℚ) (c : List ℚ) (v : List ℕ) (ms : List (List ℕ))
    (fv : RawPoly) (ν : ℚ) : List (List ℚ) :=
  if η ^ 2 * ν < (ms.map fun e => resid n cs c v fv e ^ 2).sum then
    [orDef (dense cs (distSp n cs c v fv ms))] else []

/-- The data of a set of constraints: its indicator vector `v`, the monomials of degree at most
`(ℓ - deg v) / 2` and `ℓ - deg v`, the product `f_v` of its constraints, and `∏ ‖fᵢ‖₂²`. -/
abbrev SetData := List ℕ × List (List ℕ) × List (List ℕ) × RawPoly × ℚ

/-- All the cuts at `c`. -/
def cuts (n : ℕ) (cs : List Crd) (msY : List (List ℕ)) (sd : List SetData) (η τ R : ℚ)
    (c : List ℚ) : List (List ℚ) :=
  boxCuts R c ++ psdYCuts n cs τ msY c ++ sd.flatMap (fun d => psdWCuts n cs τ d.1 d.2.1 c) ++
    sd.flatMap fun d => distCuts n cs η c d.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- The objective `L_y(q₀) + ∑ⱼ L_y(qⱼ)²` at `c`. -/
def objVal (n : ℕ) (cs : List Crd) (q₀ : RawPoly) (qs : List RawPoly) (c : List ℚ) : ℚ :=
  evalY n cs c q₀ + (qs.map fun q => evalY n cs c q ^ 2).sum

/-- The gradient of the objective at `c`, sparse. -/
def objSp (n : ℕ) (cs : List Crd) (q₀ : RawPoly) (qs : List RawPoly) (c : List ℚ) : Sp :=
  spY n q₀ ++ qs.flatMap fun q => scale (2 * evalY n cs c q) (spY n q)

/-- **The oracle**: whether `c` is declared feasible, and the cut. -/
def oracle (n : ℕ) (cs : List Crd) (msY : List (List ℕ)) (sd : List SetData) (q₀ : RawPoly)
    (qs : List RawPoly) (η τ R : ℚ) (c : List ℚ) : Bool × List ℚ :=
  if (cuts n cs msY sd η τ R c).isEmpty then (true, orDef (dense cs (objSp n cs q₀ qs c)))
  else (false, (cuts n cs msY sd η τ R c).headD [])

/-! ### Correctness -/

theorem list_sum_apply {ι : Type*} (l : List (ι → ℝ)) (k : ι) :
    l.sum k = (l.map fun f => f k).sum := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih]

section Spec

variable {n ℓ : ℕ} {A : System (Fin n) ℚ} {ds : List ℕ}

theorem length_dense (cs : List Crd) (sp : Sp) : (dense cs sp).length = cs.length := by
  simp [dense]

theorem pt_unitVec (h : DegsSpec A ℓ ds) {j : ℕ} (hj : j < (coordsL n ℓ ds).length) (a : ℚ) :
    pt h (unitVec (coordsL n ℓ ds).length j a) =
      Pi.single ((equiv h).symm ⟨j, hj⟩) (a : ℝ) := by
  classical
  ext k
  rw [pt, unitVec, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  by_cases hk : k = (equiv h).symm ⟨j, hj⟩
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, ite_eq_right]
    · simp
    · intro hkj
      apply hk
      rw [Equiv.eq_symm_apply]
      exact Fin.ext hkj

/-- **`orDef`** is `SoS.Lifted.orDefault` with the first coordinate. -/
theorem pt_orDef (h : DegsSpec A ℓ ds) {a : List ℚ} (ha : a.length = (coordsL n ℓ ds).length)
    (hN : 0 < (coordsL n ℓ ds).length) :
    pt h (orDef a) = orDefault ((equiv h).symm ⟨0, hN⟩) (pt h a) := by
  classical
  unfold orDef orDefault
  by_cases hall : a.all fun q => decide (q = 0)
  · have h0 : pt h a = 0 := by
      ext k
      rw [pt]
      by_cases hk : (equiv h k : ℕ) < a.length
      · rw [List.getD_eq_getElem _ _ hk]
        have := List.all_eq_true.1 hall _ (List.getElem_mem hk)
        simp only [decide_eq_true_eq] at this
        simp [this]
      · rw [List.getD_eq_default _ _ (not_lt.1 hk)]
        simp
    rw [ite_eq_left hall, ite_eq_left h0, ha, pt_unitVec h hN]
    simp
  · have hne : pt h a ≠ 0 := by
      intro h0
      apply hall
      rw [List.all_eq_true]
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
      have := congrFun h0 ((equiv h).symm ⟨j, ha ▸ hj⟩)
      simp only [pt, Equiv.apply_symm_apply, Pi.zero_apply] at this
      rw [List.getD_eq_getElem _ _ hj] at this
      simpa using this
    rw [ite_eq_right hall, ite_eq_right hne]

/-- The moment matrix on lists is `SoS.momentMatrix`. -/
theorem entry_momRows {f : List ℕ → ℚ} {τ : ℚ} {ms : List (List ℕ)} {i j : ℕ}
    (hi : i < ms.length) (hj : j < ms.length) :
    PDTestRat.entry (momRows n f τ ms) i j = f (addE n ms[i] ms[j]) + if i = j then τ else 0 := by
  simp [PDTestRat.entry, momRows, List.getD_eq_getElem?_getD, hi, hj]

theorem ofFn_add_toFinsupp (a b : List ℕ) :
    List.ofFn (Mono.toFinsupp n a + Mono.toFinsupp n b) = addE n a b := by
  rw [← toFinsupp_addE, ofFn_toFinsupp (length_addE _ _ _)]

/-- The monomials `ms` as a function. -/
noncomputable def msF (n : ℕ) (ms : List (List ℕ)) : Fin ms.length → Fin n →₀ ℕ :=
  fun i => Mono.toFinsupp n ms[i]

theorem msF_injective (n D : ℕ) : Function.Injective (msF n (Mono.all n D)) := by
  intro i j hij
  have hi := Mono.mem_all.1 (List.getElem_mem i.2)
  have hj := Mono.mem_all.1 (List.getElem_mem j.2)
  have := Mono.toFinsupp_inj hi.1 hj.1 hij
  exact Fin.ext ((Mono.nodup_all n D).getElem_inj_iff.1 this)

theorem mem_range_msF (n D : ℕ) (s : Fin n →₀ ℕ) :
    s ∈ Set.range (msF n (Mono.all n D)) ↔ s.degree ≤ D := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi := Mono.mem_all.1 (List.getElem_mem i.2)
    change (Mono.toFinsupp n (Mono.all n D)[i.1]).degree ≤ D
    rw [Mono.degree_toFinsupp hi.1]
    exact hi.2
  · intro hs
    have hmem : List.ofFn s ∈ Mono.all n D :=
      Mono.mem_all.2 ⟨by simp, by rw [sum_ofFn_finsupp]; exact hs⟩
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    exact ⟨⟨i, hi⟩, by change Mono.toFinsupp n (Mono.all n D)[i] = s; rw [he, toFinsupp_ofFn]⟩

theorem toReal_sqRaw {ms : List (List ℕ)} {v : Fin ms.length → ℤ} :
    toReal ((sqRaw n ms (List.ofFn v)).toPoly n) =
      polyOf (msF n ms) (fun i => (v i : ℝ)) * polyOf (msF n ms) (fun i => (v i : ℝ)) := by
  rw [sqRaw, toPoly_mulRaw, toReal_mul, toReal_toPoly_polyRaw n (by simp)]
  simp only [List.getElem_map, List.getElem_ofFn]
  push_cast
  rfl

theorem moment_entry {f : (Fin n →₀ ℕ) → ℝ} {g : List ℕ → ℚ}
    (hfg : ∀ s, f s = (g (List.ofFn s) : ℝ)) {τ : ℚ} {ms : List (List ℕ)}
    (hms : ∀ e ∈ ms, e.length = n) (i j : Fin ms.length) :
    momentMatrix f τ (msF n ms) i j = (PDTestRat.entry (momRows n g τ ms) i j : ℝ) := by
  have hi := hms _ (List.getElem_mem i.2)
  rw [momentMatrix, entry_momRows i.2 j.2, hfg, msF, msF, ofFn_add_toFinsupp]
  rw [Rat.cast_add, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero]
  simp [Fin.ext_iff]

/-- **The box cuts are valid.** -/
theorem validAnswer_of_mem_boxCuts (h : DegsSpec A ℓ ds) {η τ R : ℚ} {c a : List ℚ}
    (hc : c.length = (coordsL n ℓ ds).length) (ha : a ∈ boxCuts R c) :
    ValidAnswer (η : ℝ) τ R (pt h c) (some (pt h a)) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  obtain ⟨hp, hR⟩ := List.mem_filter.1 hp
  simp only [decide_eq_true_eq] at hR
  obtain ⟨hj, hpj⟩ := List.mem_zipIdx' hp
  have hj' : p.2 < (coordsL n ℓ ds).length := hc ▸ hj
  set k := (equiv h).symm ⟨p.2, hj'⟩
  have hck : pt h c k = (p.1 : ℝ) := by
    rw [pt, Equiv.apply_symm_apply]
    simp only
    rw [List.getD_eq_getElem _ _ hj, ← hpj]
  rw [hc, pt_unitVec h hj']
  have := validAnswer_of_box (η := (η : ℝ)) (τ := (τ : ℝ)) (R := (R : ℝ)) (c := pt h c) (i := k)
    (by rw [hck]; exact_mod_cast hR)
  have hsign : (((if 0 < p.1 then 1 else -1 : ℚ)) : ℝ) = if 0 < pt h c k then 1 else -1 := by
    rw [hck]
    by_cases h1 : 0 < p.1
    · have : (0 : ℝ) < p.1 := by exact_mod_cast h1
      simp [h1, this]
    · have : ¬ (0 : ℝ) < p.1 := by exact_mod_cast h1
      simp [h1, this]
  rw [hsign]
  exact this

theorem cast_ne_zero_fun {N : ℕ} {v : Fin N → ℤ} (hv : v ≠ 0) : (fun i => (v i : ℝ)) ≠ 0 :=
  fun h0 => hv (funext fun i => by have := congrFun h0 i; simpa using this)

/-- **The positive definiteness cut of the moments is valid.** -/
theorem validAnswer_of_mem_psdYCuts (h : DegsSpec A ℓ ds) {η τ R : ℚ} (hτ : 0 < τ)
    {c a : List ℚ} (hN : 0 < (coordsL n ℓ ds).length)
    (ha : a ∈ psdYCuts n (coordsL n ℓ ds) τ (Mono.all n (ℓ / 2)) c) :
    ValidAnswer (η : ℝ) τ R (pt h c) (some (pt h a)) := by
  unfold psdYCuts at ha
  cases hw : PDTestRat.test (momRows n (yv (coordsL n ℓ ds) c) τ (Mono.all n (ℓ / 2))) with
  | none => rw [hw] at ha; simp at ha
  | some w =>
    rw [hw] at ha
    simp only [Option.elim, List.mem_singleton] at ha
    subst ha
    have hms : ∀ e ∈ Mono.all n (ℓ / 2), e.length = n := fun e he => (Mono.mem_all.1 he).1
    obtain ⟨-, hsome⟩ := PDTestRat.test_spec _ (by simp [momRows])
      (momentMatrix (ys (pt h c)) τ (msF n (Mono.all n (ℓ / 2))))
      (fun i j => moment_entry (fun s => ys_pt h c s) hms i j) (momentMatrix_transpose _ _ _)
    obtain ⟨v, rfl, hv, hle⟩ := hsome _ hw
    have := validAnswer_of_psd (η := (η : ℝ)) (R := (R : ℝ)) (msF_injective n (ℓ / 2))
      (mem_range_msF n (ℓ / 2)) (by exact_mod_cast hτ) (cast_ne_zero_fun hv) hle
      ((equiv h).symm ⟨0, hN⟩)
    rw [pt_orDef h (length_dense _ _) hN]
    convert this using 3
    ext k
    rw [pt_dense, spAt_scale, Rat.cast_mul, spAt_spY, toReal_sqRaw]
    simp

/-- **The positive definiteness cut of an auxiliary sequence is valid.** -/
theorem validAnswer_of_mem_psdWCuts (h : DegsSpec A ℓ ds) {η τ R : ℚ} (hτ : 0 < τ)
    {c a : List ℚ} (hN : 0 < (coordsL n ℓ ds).length) (S : sets A ℓ)
    (ha : a ∈ psdWCuts n (coordsL n ℓ ds) τ (ind S.1) (Mono.all n ((ℓ - A.degree S.1) / 2)) c) :
    ValidAnswer (η : ℝ) τ R (pt h c) (some (pt h a)) := by
  unfold psdWCuts at ha
  cases hw : PDTestRat.test (momRows n (wv (coordsL n ℓ ds) c (ind S.1)) τ
      (Mono.all n ((ℓ - A.degree S.1) / 2))) with
  | none => rw [hw] at ha; simp at ha
  | some w =>
    rw [hw] at ha
    simp only [Option.elim, List.mem_singleton] at ha
    subst ha
    have hms : ∀ e ∈ Mono.all n ((ℓ - A.degree S.1) / 2), e.length = n :=
      fun e he => (Mono.mem_all.1 he).1
    obtain ⟨-, hsome⟩ := PDTestRat.test_spec _ (by simp [momRows])
      (momentMatrix (ws (pt h c) S) τ (msF n (Mono.all n ((ℓ - A.degree S.1) / 2))))
      (fun i j => moment_entry (fun s => ws_pt h c S s) hms i j) (momentMatrix_transpose _ _ _)
    obtain ⟨v, rfl, hv, hle⟩ := hsome _ hw
    have := validAnswer_of_psd_aux (η := (η : ℝ)) (R := (R : ℝ)) S
      (msF_injective n ((ℓ - A.degree S.1) / 2)) (mem_range_msF n _) (by exact_mod_cast hτ)
      (cast_ne_zero_fun hv) hle ((equiv h).symm ⟨0, hN⟩)
    rw [pt_orDef h (length_dense _ _) hN]
    convert this using 3
    ext k
    rw [pt_dense, spAt_scale, Rat.cast_mul, spAt_spW, toReal_sqRaw]
    simp

/-- The residuals on lists are `SoS.Lifted.resid`. -/
theorem resid_pt (h : DegsSpec A ℓ ds) (c : List ℚ) (S : sets A ℓ) {fv : RawPoly}
    (hfv : fv.toPoly n = A.prod S.1) (s : Fin n →₀ ℕ) :
    Lifted.resid (pt h c) S s =
      (resid n (coordsL n ℓ ds) c (ind S.1) fv (List.ofFn s) : ℝ) := by
  rw [Lifted.resid, loc, resid, ← hfv, Rat.cast_sub, ws_pt, ← riesz_ys_pt h c, toPoly_shift,
    toReal_mul, toFinsupp_ofFn]
  congr 2
  simp [toReal]

theorem toReal_monomial_one (s : Fin n →₀ ℕ) : toReal (monomial s (1 : ℚ)) = monomial s 1 := by
  simp [toReal]

theorem toReal_toPoly_single (e : List ℕ) :
    toReal (RawPoly.toPoly n [(e, 1)]) = monomial (Mono.toFinsupp n e) 1 := by
  rw [toReal_toPoly]
  simp

/-- **The distance cut is valid.** -/
theorem validAnswer_of_mem_distCuts (h : DegsSpec A ℓ ds) {η τ R : ℚ} {c a : List ℚ}
    (hN : 0 < (coordsL n ℓ ds).length) (S : sets A ℓ) {fv : RawPoly}
    (hfv : fv.toPoly n = A.prod S.1) {ν : ℚ}
    (hν : (ν : ℝ) = ∏ i ∈ S.1, coeffNorm (toReal (A.get i)) ^ 2)
    (ha : a ∈ distCuts n (coordsL n ℓ ds) η c (ind S.1) (Mono.all n (ℓ - A.degree S.1)) fv ν) :
    ValidAnswer (η : ℝ) τ R (pt h c) (some (pt h a)) := by
  unfold distCuts at ha
  split_ifs at ha with hviol
  · rw [List.mem_singleton] at ha
    subst ha
    have hsum : ∑ m ∈ monomialsLE (Fin n) (ℓ - A.degree S.1), Lifted.resid (pt h c) S m ^ 2 =
        (((Mono.all n (ℓ - A.degree S.1)).map fun e =>
          resid n (coordsL n ℓ ds) c (ind S.1) fv e ^ 2).sum : ℚ) := by
      rw [sum_monomialsLE, Rat.cast_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun e he => ?_
      simp only [Function.comp, resid_pt h c S hfv, Rat.cast_pow,
        ofFn_toFinsupp (Mono.mem_all.1 he).1]
    have hS : ((η : ℝ) * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2 <
        ∑ m ∈ monomialsLE (Fin n) (ℓ - A.degree S.1), Lifted.resid (pt h c) S m ^ 2 := by
      rw [hsum, mul_pow, ← Finset.prod_pow, ← hν]
      exact_mod_cast hviol
    have := validAnswer_of_dist (η := (η : ℝ)) (τ := (τ : ℝ)) (R := (R : ℝ)) S hS
      ((equiv h).symm ⟨0, hN⟩)
    rw [pt_orDef h (length_dense _ _) hN]
    convert this using 3
    ext k
    rw [pt_dense, distSp, spAt_flatMap, Finset.sum_apply, sum_monomialsLE, Rat.cast_list_sum,
      List.map_map]
    congr 1
    refine List.map_congr_left fun e he => ?_
    have hlen := (Mono.mem_all.1 he).1
    have h1 : (spAt (spY n (shift n e fv)) (crd k) : ℝ) =
        gradY (monomial (Mono.toFinsupp n e) 1 * toReal (A.prod S.1)) k := by
      rw [spAt_spY, toPoly_shift, toReal_mul, hfv, toReal_monomial_one]
    have h2 : (spAt (spW n (ind S.1) [(e, 1)]) (crd k) : ℝ) =
        gradW S (monomial (Mono.toFinsupp n e) 1) k := by
      rw [spAt_spW, toReal_toPoly_single]
    simp only [Function.comp, spAt_scale, spAt_append, Rat.cast_mul, Rat.cast_add, Rat.cast_neg,
      Rat.cast_one, Rat.cast_ofNat, h1, h2, Pi.smul_apply, smul_eq_mul, gradResid, Pi.sub_apply,
      resid_pt h c S hfv, ofFn_toFinsupp hlen]
    ring
  · simp at ha

/-- The data of the sets, for constraint products `F` and norms `G`. -/
def setData (n ℓ : ℕ) (ds : List ℕ) (F : List ℕ → RawPoly) (G : List ℕ → ℚ) : List SetData :=
  (setsL ℓ ds).map fun v =>
    (v, Mono.all n ((ℓ - dsum ds v) / 2), Mono.all n (ℓ - dsum ds v), F v, G v)

/-- The products `F v` and norms `G v` are right for every set. -/
structure SetDataSpec (A : System (Fin n) ℚ) (ℓ : ℕ) (F : List ℕ → RawPoly) (G : List ℕ → ℚ) :
    Prop where
  prod : ∀ S ∈ sets A ℓ, (F (ind S)).toPoly n = A.prod S
  norm : ∀ S ∈ sets A ℓ, (G (ind S) : ℝ) = ∏ i ∈ S, coeffNorm (toReal (A.get i)) ^ 2

theorem mem_setData (h : DegsSpec A ℓ ds) {F : List ℕ → RawPoly} {G : List ℕ → ℚ}
    {d : SetData} (hd : d ∈ setData n ℓ ds F G) :
    ∃ S : sets A ℓ, d = (ind S.1, Mono.all n ((ℓ - A.degree S.1) / 2),
      Mono.all n (ℓ - A.degree S.1), F (ind S.1), G (ind S.1)) := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hd
  obtain ⟨S, hS, rfl⟩ := (mem_setsL h).1 hv
  exact ⟨⟨S, hS⟩, by simp only [dsum_ind_eq_of_mem h hS]⟩

theorem ind_mem_setData (h : DegsSpec A ℓ ds) (F : List ℕ → RawPoly) (G : List ℕ → ℚ)
    (S : sets A ℓ) : (ind S.1, Mono.all n ((ℓ - A.degree S.1) / 2),
      Mono.all n (ℓ - A.degree S.1), F (ind S.1), G (ind S.1)) ∈ setData n ℓ ds F G := by
  refine List.mem_map.2 ⟨ind S.1, (mem_setsL h).2 ⟨S.1, S.2, rfl⟩, ?_⟩
  simp only [dsum_ind_eq_of_mem h S.2]

/-- **Every cut is valid.** -/
theorem validAnswer_of_mem_cuts (h : DegsSpec A ℓ ds) {F : List ℕ → RawPoly}
    {G : List ℕ → ℚ} (hFG : SetDataSpec A ℓ F G) {η τ R : ℚ} (hτ : 0 < τ) {c a : List ℚ}
    (hc : c.length = (coordsL n ℓ ds).length) (hN : 0 < (coordsL n ℓ ds).length)
    (ha : a ∈ cuts n (coordsL n ℓ ds) (Mono.all n (ℓ / 2)) (setData n ℓ ds F G) η τ R c) :
    ValidAnswer (η : ℝ) τ R (pt h c) (some (pt h a)) := by
  simp only [cuts, List.mem_append, List.mem_flatMap] at ha
  rcases ha with ((ha | ha) | ⟨d, hd, ha⟩) | ⟨d, hd, ha⟩
  · exact validAnswer_of_mem_boxCuts h hc ha
  · exact validAnswer_of_mem_psdYCuts h hτ hN ha
  · obtain ⟨S, rfl⟩ := mem_setData h hd
    exact validAnswer_of_mem_psdWCuts h hτ hN S ha
  · obtain ⟨S, rfl⟩ := mem_setData h hd
    exact validAnswer_of_mem_distCuts h hN S (hFG.prod S.1 S.2) (hFG.norm S.1 S.2) ha

theorem pos_def_of_test {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hM : ∀ v, v ≠ 0 → 0 < v ⬝ᵥ M *ᵥ v) : ∀ v, v ≠ 0 → 0 < v ⬝ᵥ M *ᵥ v := hM

/-- **No cut: the center is in the set.** -/
theorem inSet_of_cuts_eq_nil (h : DegsSpec A ℓ ds) {F : List ℕ → RawPoly}
    {G : List ℕ → ℚ} (hFG : SetDataSpec A ℓ F G) {η τ R : ℚ} {c : List ℚ}
    (hc : c.length = (coordsL n ℓ ds).length)
    (hnil : cuts n (coordsL n ℓ ds) (Mono.all n (ℓ / 2)) (setData n ℓ ds F G) η τ R c = []) :
    InSet A ℓ η τ R (pt h c) := by
  simp only [cuts, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hnil
  obtain ⟨⟨⟨hbox, hpsd⟩, hpsdS⟩, hdist⟩ := hnil
  have hms : ∀ D, ∀ e ∈ Mono.all n D, e.length = n := fun D e he => (Mono.mem_all.1 he).1
  refine validAnswer_none (η := (η : ℝ)) ?_ (msF_injective n (ℓ / 2)) (mem_range_msF n (ℓ / 2))
    ?_ (fun S => ⟨_, msF n (Mono.all n ((ℓ - A.degree S.1) / 2))⟩) (fun S => msF_injective n _)
    (fun S => mem_range_msF n _) ?_ ?_
  · -- The box.
    intro k
    have hk : (equiv h k : ℕ) < c.length := by rw [hc]; exact (equiv h k).2
    have hmem : (c[(equiv h k : ℕ)], (equiv h k : ℕ)) ∈ c.zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (by simp [hk])
    have := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 hbox) _ hmem
    simp only [decide_eq_true_eq, not_lt] at this
    rw [pt, List.getD_eq_getElem _ _ hk]
    exact_mod_cast this
  · -- The moments.
    unfold psdYCuts at hpsd
    cases hw : PDTestRat.test (momRows n (yv (coordsL n ℓ ds) c) τ (Mono.all n (ℓ / 2))) with
    | some w => rw [hw] at hpsd; simp at hpsd
    | none =>
      exact (PDTestRat.test_spec _ (by simp [momRows])
        (momentMatrix (ys (pt h c)) τ (msF n (Mono.all n (ℓ / 2))))
        (fun i j => moment_entry (fun s => ys_pt h c s) (hms _) i j)
        (momentMatrix_transpose _ _ _)).1 hw
  · -- The auxiliary sequences.
    intro S
    have := hpsdS _ (ind_mem_setData h F G S)
    unfold psdWCuts at this
    cases hw : PDTestRat.test (momRows n (wv (coordsL n ℓ ds) c (ind S.1)) τ
        (Mono.all n ((ℓ - A.degree S.1) / 2))) with
    | some w => rw [hw] at this; simp at this
    | none =>
      exact (PDTestRat.test_spec _ (by simp [momRows])
        (momentMatrix (ws (pt h c) S) τ (msF n (Mono.all n ((ℓ - A.degree S.1) / 2))))
        (fun i j => moment_entry (fun s => ws_pt h c S s) (hms _) i j)
        (momentMatrix_transpose _ _ _)).1 hw
  · -- The distances.
    intro S
    have := hdist _ (ind_mem_setData h F G S)
    have hviol : ¬ (η ^ 2 * G (ind S.1) < ((Mono.all n (ℓ - A.degree S.1)).map fun e =>
        resid n (coordsL n ℓ ds) c (ind S.1) (F (ind S.1)) e ^ 2).sum) := by
      intro hv
      simp [distCuts, hv] at this
    rw [not_lt] at hviol
    have hsum : ∑ m ∈ monomialsLE (Fin n) (ℓ - A.degree S.1), Lifted.resid (pt h c) S m ^ 2 =
        (((Mono.all n (ℓ - A.degree S.1)).map fun e =>
          resid n (coordsL n ℓ ds) c (ind S.1) (F (ind S.1)) e ^ 2).sum : ℚ) := by
      rw [sum_monomialsLE, Rat.cast_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun e he => ?_
      simp only [Function.comp, resid_pt h c S (hFG.prod S.1 S.2), Rat.cast_pow,
        ofFn_toFinsupp (Mono.mem_all.1 he).1]
    change ∑ m ∈ monomialsLE (Fin n) (ℓ - A.degree S.1), Lifted.resid (pt h c) S m ^ 2 ≤ _
    rw [hsum, mul_pow, ← Finset.prod_pow, ← hFG.norm S.1 S.2]
    exact_mod_cast hviol

/-! ### The objective -/

/-- The objective at a point is `SoS.Oracle.objVal`. -/
theorem obj_pt (h : DegsSpec A ℓ ds) (q₀ : RawPoly) (qs : List RawPoly) (c : List ℚ) :
    obj (toReal (q₀.toPoly n)) (qs.map fun q => toReal (q.toPoly n)) (ys (pt h c)) =
      (objVal n (coordsL n ℓ ds) q₀ qs c : ℝ) := by
  rw [obj, objVal, Rat.cast_add, riesz_ys_pt, Rat.cast_list_sum, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun q _ => ?_
  simp [riesz_ys_pt]

theorem pt_objSp (h : DegsSpec A ℓ ds) (q₀ : RawPoly) (qs : List RawPoly) (c : List ℚ) :
    pt h (dense (coordsL n ℓ ds) (objSp n (coordsL n ℓ ds) q₀ qs c)) =
      gradObj (toReal (q₀.toPoly n)) (qs.map fun q => toReal (q.toPoly n)) (pt h c) := by
  ext k
  rw [pt_dense, objSp, spAt_append, spAt_flatMap, gradObj, Pi.add_apply, Rat.cast_add, spAt_spY,
    list_sum_apply, Rat.cast_list_sum, List.map_map, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun q _ => ?_
  simp [spAt_scale, spAt_spY, riesz_ys_pt]

/-! ### The oracle -/

/-- **The oracle is correct.** Its cut is nonzero. If it declares the center infeasible, the cut
keeps the points of `InSet A ℓ η (τ / 2) R`. If it declares it feasible, the center is in
`InSet A ℓ η τ R`, and the cut keeps the points with smaller objective. -/
theorem oracle_spec (h : DegsSpec A ℓ ds) {F : List ℕ → RawPoly} {G : List ℕ → ℚ}
    (hFG : SetDataSpec A ℓ F G) {q₀ : RawPoly} {qs : List RawPoly}
    (hq : ∀ q ∈ q₀ :: qs, (q.toPoly n).totalDegree ≤ ℓ) {η τ R : ℚ} (hτ : 0 < τ) {c : List ℚ}
    (hc : c.length = (coordsL n ℓ ds).length) (hN : 0 < (coordsL n ℓ ds).length) :
    let r := oracle n (coordsL n ℓ ds) (Mono.all n (ℓ / 2)) (setData n ℓ ds F G) q₀ qs η τ R c
    pt h r.2 ≠ 0 ∧
      (r.1 = false → ∀ x, InSet A ℓ η (τ / 2) R x → pt h r.2 ⬝ᵥ (x - pt h c) ≤ 0) ∧
      (r.1 = true → InSet A ℓ η τ R (pt h c) ∧
        ∀ x, obj (toReal (q₀.toPoly n)) (qs.map fun q => toReal (q.toPoly n)) (ys x) <
          obj (toReal (q₀.toPoly n)) (qs.map fun q => toReal (q.toPoly n)) (ys (pt h c)) →
          pt h r.2 ⬝ᵥ (x - pt h c) ≤ 0) := by
  intro r
  simp only [r, oracle]
  split_ifs with hempty
  · rw [List.isEmpty_iff] at hempty
    refine ⟨?_, by simp, fun _ => ⟨inSet_of_cuts_eq_nil h hFG hc hempty, fun x hx => ?_⟩⟩
    · rw [pt_orDef h (length_dense _ _) hN]
      exact orDefault_ne_zero _ _
    · rw [pt_orDef h (length_dense _ _) hN, pt_objSp]
      refine Lifted.objective_cut (fun q hq' => ?_) _ _ x hx
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact (totalDegree_toReal_le _).trans (hq _ List.mem_cons_self)
      · obtain ⟨q', hq'', rfl⟩ := List.mem_map.1 hq'
        exact (totalDegree_toReal_le _).trans (hq _ (List.mem_cons_of_mem _ hq''))
  · rw [List.isEmpty_iff] at hempty
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hempty
    have hva := validAnswer_of_mem_cuts h hFG hτ hc hN (a := a)
      (by rw [hl]; exact List.mem_cons_self)
    rw [hl, List.headD_cons]
    exact ⟨hva.1, fun _ => hva.2, by simp⟩

end Spec

end SoS.Oracle
