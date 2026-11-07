module

public import Background.SumOfSquares.Algorithm.RawPoly
public import Background.SumOfSquares.Separation

/-!
# The coordinates, on lists

The coordinates of the set the algorithm searches (`SoS.Lifted.Coord`), as an explicit list.

* A set `S` of constraints is its indicator vector `SoS.Coords.ind S`. The sets that get an
  auxiliary sequence (`SoS.Lifted.sets`) are listed by `SoS.Coords.setsL`, from the degrees of the
  constraints capped at `ℓ + 1` (`SoS.Coords.mem_setsL`).
* A coordinate is `(none, e)` for the moment of `xᵉ`, or `(some v, e)` for the auxiliary moment of
  `xᵉ` for the set with indicator vector `v`. `SoS.Coords.coordsL` lists them all, once each, and
  `SoS.Coords.equiv` identifies their positions with `SoS.Lifted.Coord`.
* A point is a list of rationals, one per coordinate. `SoS.Coords.yv` and `SoS.Coords.wv` read its
  moments, as `SoS.Lifted.ys` and `SoS.Lifted.ws` do (`SoS.Coords.ys_pt`, `SoS.Coords.ws_pt`).
* A cut is computed as a sparse list of (coordinate, coefficient) pairs and made dense by
  `SoS.Coords.dense`. The gradients `SoS.Lifted.gradY` and `SoS.Lifted.gradW` of a raw polynomial
  are the dense forms of `SoS.Coords.spY` and `SoS.Coords.spW`.
-/

@[expose] public section

namespace SoS.Coords

open MvPolynomial SoS.Solver SoS.Poly SoS.Lifted

/-! ### Sums over ranges -/

theorem sum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i : Fin m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
    simp

/-! ### Sets of constraints -/

section Sets

variable {m : ℕ}

/-- The indicator vector of a set of constraints. -/
def ind (S : Finset (Fin m)) : List ℕ := List.ofFn fun i => if i ∈ S then 1 else 0

@[simp] theorem length_ind (S : Finset (Fin m)) : (ind S).length = m := by simp [ind]

theorem getD_ind (S : Finset (Fin m)) (i : Fin m) :
    (ind S).getD i 0 = if i ∈ S then 1 else 0 := by
  simp [ind, List.getD_eq_getElem?_getD, i.2]

theorem le_one_of_mem_ind {S : Finset (Fin m)} {a : ℕ} (ha : a ∈ ind S) : a ≤ 1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  split_ifs <;> simp

/-- The set with indicator vector `v`. -/
def ofInd (m : ℕ) (v : List ℕ) : Finset (Fin m) := Finset.univ.filter fun i => v.getD i 0 = 1

theorem ofInd_ind (S : Finset (Fin m)) : ofInd m (ind S) = S := by
  ext i
  simp only [ofInd, Finset.mem_filter, Finset.mem_univ, true_and, getD_ind]
  split_ifs with h <;> simp [h]

theorem ind_injective : Function.Injective (ind (m := m)) := fun S S' h => by
  rw [← ofInd_ind S, h, ofInd_ind]

theorem ind_ofInd {v : List ℕ} (hv : v.length = m) (h01 : ∀ a ∈ v, a ≤ 1) :
    ind (ofInd m v) = v := by
  apply List.ext_getElem (by simp [hv])
  intro i h1 h2
  have hle := h01 _ (List.getElem_mem h2)
  simp only [ind, ofInd, List.getElem_ofFn, Finset.mem_filter, Finset.mem_univ, true_and,
    List.getD_eq_getElem _ _ h2]
  split_ifs with h
  · exact h.symm
  · omega

/-- The weighted sum `∑ vᵢ dᵢ`: the degree of the set with indicator vector `v`, for the degrees
`d`. -/
def dsum (ds v : List ℕ) : ℕ := ((List.range ds.length).map fun i => v.getD i 0 * ds.getD i 0).sum

theorem dsum_ind {ds : List ℕ} (hds : ds.length = m) (S : Finset (Fin m)) :
    dsum ds (ind S) = ∑ i ∈ S, ds.getD i 0 := by
  subst hds
  rw [dsum, sum_range_map]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  simp only [getD_ind]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i => i ∉ S) (fun i hi => by
    simp [(Finset.mem_filter.1 hi).2]), add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact Finset.sum_congr rfl fun i hi => by simp [hi]

/-- Whether `v` is the indicator vector of a set that gets an auxiliary sequence: nonempty, of
nonconstant constraints, of degree at most `ℓ`. -/
def isSet (ℓ : ℕ) (ds v : List ℕ) : Bool :=
  v.all (fun a => decide (a ≤ 1)) && decide (v.sum ≠ 0) &&
    (List.range ds.length).all (fun i => decide (v.getD i 0 = 0 ∨ ds.getD i 0 ≠ 0)) &&
    decide (dsum ds v ≤ ℓ)

/-- The indicator vectors of the sets that get an auxiliary sequence. -/
def setsL (ℓ : ℕ) (ds : List ℕ) : List (List ℕ) := (Mono.all ds.length ℓ).filter (isSet ℓ ds)

theorem nodup_setsL (ℓ : ℕ) (ds : List ℕ) : (setsL ℓ ds).Nodup :=
  (Mono.nodup_all _ _).filter _

end Sets

section SetsSpec

variable {σ K : Type*} [Field K] {A : System σ K} {ℓ : ℕ} {ds : List ℕ}

/-- `ds` lists the degrees of the constraints, capped at `ℓ + 1`. -/
structure DegsSpec (A : System σ K) (ℓ : ℕ) (ds : List ℕ) : Prop where
  length : ds.length = A.length
  getD : ∀ i : Fin A.length, ds.getD i 0 = min (ℓ + 1) (A.get i).totalDegree

theorem sum_ind (S : Finset (Fin A.length)) : (ind S).sum = S.card := by
  classical
  rw [ind, List.sum_ofFn, Finset.sum_boole]
  simp

theorem dsum_ind_eq (h : DegsSpec A ℓ ds) {S : Finset (Fin A.length)}
    (hS : ∀ i ∈ S, (A.get i).totalDegree ≤ ℓ) : dsum ds (ind S) = A.degree S := by
  rw [dsum_ind h.length, System.degree]
  exact Finset.sum_congr rfl fun i hi => by rw [h.getD i, min_eq_right (by have := hS i hi; omega)]

theorem dsum_ind_eq_of_mem (h : DegsSpec A ℓ ds) {S : Finset (Fin A.length)} (hS : S ∈ sets A ℓ) :
    dsum ds (ind S) = A.degree S := by
  classical
  refine dsum_ind_eq h fun i hi => ?_
  have := degree_le_of_mem_sets hS
  rw [System.degree] at this
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans this

/-- **The sets, listed.** -/
theorem mem_setsL (h : DegsSpec A ℓ ds) {v : List ℕ} :
    v ∈ setsL ℓ ds ↔ ∃ S ∈ sets A ℓ, ind S = v := by
  classical
  constructor
  · intro hv
    obtain ⟨hall, hset⟩ := List.mem_filter.1 hv
    obtain ⟨hlen, -⟩ := Mono.mem_all.1 hall
    simp only [isSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at hset
    obtain ⟨⟨⟨h01, hsum⟩, hnc⟩, hd⟩ := hset
    have hlenA : v.length = A.length := hlen.trans h.length
    refine ⟨ofInd A.length v, ?_, ind_ofInd hlenA h01⟩
    have hind := ind_ofInd hlenA h01
    -- Every chosen constraint is nonconstant, of degree at most `ℓ`.
    have hmem : ∀ i, i ∈ ofInd A.length v ↔ v.getD i 0 = 1 := fun i => by simp [ofInd]
    have hnc' : ∀ i ∈ ofInd A.length v, (A.get i).totalDegree ≠ 0 := by
      intro i hi
      have h1 := hnc i (by rw [h.length]; exact i.2)
      rw [(hmem i).1 hi] at h1
      have h2 := h.getD i
      simp only [one_ne_zero, false_or] at h1
      omega
    have hdS : dsum ds (ind (ofInd A.length v)) = ∑ i ∈ ofInd A.length v, ds.getD i 0 :=
      dsum_ind h.length _
    rw [hind] at hdS
    have hle : ∀ i ∈ ofInd A.length v, (A.get i).totalDegree ≤ ℓ := by
      intro i hi
      have h1 : ds.getD i 0 ≤ ℓ :=
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans
          (show ∑ i ∈ ofInd A.length v, ds.getD i 0 ≤ ℓ by rw [← hdS]; exact hd)
      have h2 := h.getD i
      omega
    unfold sets
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hnc', ?_⟩
    · by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply hsum
      rw [← hind, hne]
      simp [ind]
    · rw [← dsum_ind_eq h hle, hind]
      exact hd
  · rintro ⟨S, hS, rfl⟩
    have hS' := hS
    unfold sets at hS'
    obtain ⟨-, hne, hnc, hdeg⟩ := Finset.mem_filter.1 hS'
    have hdsum := dsum_ind_eq_of_mem h hS
    refine List.mem_filter.2 ⟨Mono.mem_all.2 ⟨by simp [h.length], ?_⟩, ?_⟩
    · rw [sum_ind, Finset.card_eq_sum_ones]
      refine le_trans (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hnc i hi)) hdeg
    · simp only [isSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range]
      refine ⟨⟨⟨fun a ha => le_one_of_mem_ind ha, ?_⟩, fun i hi => ?_⟩, hdsum ▸ hdeg⟩
      · rw [sum_ind]
        exact Finset.card_ne_zero.2 hne
      · have hi' : i < A.length := h.length ▸ hi
        have := getD_ind S ⟨i, hi'⟩
        simp only at this
        rw [this]
        by_cases hiS : (⟨i, hi'⟩ : Fin A.length) ∈ S
        · right
          have h2 := h.getD ⟨i, hi'⟩
          have := hnc _ hiS
          simp only at h2
          omega
        · left
          simp [hiS]

end SetsSpec

/-! ### Coordinates -/

/-- A coordinate: `(none, e)` for the moment of `xᵉ`, `(some v, e)` for the auxiliary moment of
`xᵉ` for the set with indicator vector `v`. -/
abbrev Crd := Option (List ℕ) × List ℕ

/-- All coordinates: the nonconstant monomials of degree at most `ℓ`, then for each set `v` the
monomials of degree at most `ℓ - deg v`. -/
def coordsL (n ℓ : ℕ) (ds : List ℕ) : List Crd :=
  ((Mono.all n ℓ).filter fun e => decide (e.sum ≠ 0)).map (fun e => (none, e)) ++
    (setsL ℓ ds).flatMap fun v => (Mono.all n (ℓ - dsum ds v)).map fun e => (some v, e)

theorem nodup_coordsL (n ℓ : ℕ) (ds : List ℕ) : (coordsL n ℓ ds).Nodup := by
  rw [coordsL, List.nodup_append]
  refine ⟨((Mono.nodup_all n ℓ).filter _).map fun _ _ h => by simpa using h, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => (Mono.nodup_all _ _).map fun _ _ h => by simpa using h,
      (nodup_setsL ℓ ds).pairwise_of_forall_ne fun v _ v' _ hne => ?_⟩
    intro c hc hc'
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨e', -, he⟩ := List.mem_map.1 hc'
    simp only [Prod.mk.injEq, Option.some.injEq] at he
    exact hne he.1.symm
  · intro a ha b hb hab
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 hb
    obtain ⟨e', -, rfl⟩ := List.mem_map.1 hv
    simp at hab

section CoordsSpec

variable {n ℓ : ℕ} {A : System (Fin n) ℚ} {ds : List ℕ}

theorem sum_ofFn_finsupp (s : Fin n →₀ ℕ) : (List.ofFn s).sum = s.degree := by
  rw [List.sum_ofFn, Finsupp.degree_eq_sum]

theorem ofFn_inj {s s' : Fin n →₀ ℕ} (h : List.ofFn s = List.ofFn s') : s = s' := by
  rw [← toFinsupp_ofFn s, ← toFinsupp_ofFn s', h]

theorem ofFn_toFinsupp {e : List ℕ} (he : e.length = n) : List.ofFn (Mono.toFinsupp n e) = e := by
  subst he
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem ofFn_toFinsupp_expo (e : List ℕ) : List.ofFn (Mono.toFinsupp n e) = expo n e := by
  rw [← toFinsupp_expo, ofFn_toFinsupp (length_expo _ _)]

/-- The coordinate of a point of `SoS.Lifted.Coord`. -/
def crd : Coord A ℓ → Crd
  | .inl s => (none, List.ofFn s.1)
  | .inr p => (some (ind p.1.1), List.ofFn p.2.1)

theorem crd_injective : Function.Injective (crd (A := A) (ℓ := ℓ)) := by
  rintro (s | ⟨S, s⟩) (s' | ⟨S', s'⟩) h <;> simp only [crd, Prod.mk.injEq, reduceCtorEq,
    false_and, Option.some.injEq] at h
  · exact congrArg Sum.inl (Subtype.ext (ofFn_inj h.2))
  · obtain ⟨h1, h2⟩ := h
    have hS : S = S' := Subtype.ext (ind_injective h1)
    subst hS
    exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext (ofFn_inj h2))))

/-- **The coordinates, listed.** -/
theorem mem_coordsL (h : DegsSpec A ℓ ds) {c : Crd} :
    c ∈ coordsL n ℓ ds ↔ ∃ k : Coord A ℓ, crd k = c := by
  classical
  constructor
  · intro hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      obtain ⟨he, hsum⟩ := List.mem_filter.1 he
      obtain ⟨hlen, hle⟩ := Mono.mem_all.1 he
      have hd : (Mono.toFinsupp n e).degree = e.sum := Mono.degree_toFinsupp hlen
      refine ⟨.inl ⟨Mono.toFinsupp n e, Finset.mem_erase.2 ⟨fun h0 => ?_, ?_⟩⟩, ?_⟩
      · rw [h0] at hd
        simp only [decide_eq_true_eq] at hsum
        simp at hd
        omega
      · exact mem_monomialsLE.2 (hd ▸ hle)
      · simp [crd, ofFn_toFinsupp hlen]
    · obtain ⟨v, hv, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      obtain ⟨S, hS, rfl⟩ := (mem_setsL h).1 hv
      obtain ⟨hlen, hle⟩ := Mono.mem_all.1 he
      have hd : (Mono.toFinsupp n e).degree = e.sum := Mono.degree_toFinsupp hlen
      refine ⟨.inr ⟨⟨S, hS⟩, ⟨Mono.toFinsupp n e, mem_monomialsLE.2 ?_⟩⟩, ?_⟩
      · rw [hd, ← dsum_ind_eq_of_mem h hS]
        exact hle
      · simp [crd, ofFn_toFinsupp hlen]
  · rintro ⟨k, rfl⟩
    rcases k with ⟨s, hs⟩ | ⟨⟨S, hS⟩, ⟨s, hs⟩⟩
    · obtain ⟨hs0, hs⟩ := Finset.mem_erase.1 hs
      refine List.mem_append_left _ (List.mem_map.2 ⟨List.ofFn s, List.mem_filter.2
        ⟨Mono.mem_all.2 ⟨by simp, ?_⟩, ?_⟩, rfl⟩)
      · rw [sum_ofFn_finsupp]
        exact mem_monomialsLE.1 hs
      · rw [sum_ofFn_finsupp]
        simp only [ne_eq, decide_eq_true_eq]
        intro h0
        exact hs0 ((Finsupp.degree_eq_zero_iff _).1 h0)
    · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨ind S, (mem_setsL h).2 ⟨S, hS, rfl⟩,
        List.mem_map.2 ⟨List.ofFn s, Mono.mem_all.2 ⟨by simp, ?_⟩, rfl⟩⟩)
      rw [sum_ofFn_finsupp, dsum_ind_eq_of_mem h hS]
      exact mem_monomialsLE.1 hs

/-- The coordinates of `SoS.Lifted.Coord` are the elements of `coordsL`. -/
noncomputable def coordEquiv (h : DegsSpec A ℓ ds) : Coord A ℓ ≃ {c // c ∈ coordsL n ℓ ds} :=
  Equiv.ofBijective (fun k => ⟨crd k, (mem_coordsL h).2 ⟨k, rfl⟩⟩)
    ⟨fun k k' hk => crd_injective (congrArg Subtype.val hk), fun c => by
      obtain ⟨k, hk⟩ := (mem_coordsL h).1 c.2
      exact ⟨k, Subtype.ext hk⟩⟩

/-- **The coordinates, numbered** by their positions in `coordsL`. -/
noncomputable def equiv (h : DegsSpec A ℓ ds) : Coord A ℓ ≃ Fin (coordsL n ℓ ds).length :=
  (coordEquiv h).trans ((nodup_coordsL n ℓ ds).getEquiv _).symm

theorem get_equiv (h : DegsSpec A ℓ ds) (k : Coord A ℓ) :
    (coordsL n ℓ ds).get (equiv h k) = crd k := by
  have := congrArg Subtype.val
    (((nodup_coordsL n ℓ ds).getEquiv _).apply_symm_apply (coordEquiv h k))
  exact this

theorem equiv_apply (h : DegsSpec A ℓ ds) (k : Coord A ℓ) :
    (equiv h k : ℕ) = (coordsL n ℓ ds).idxOf (crd k) := by
  rw [← get_equiv h k, List.get_idxOf (nodup_coordsL n ℓ ds)]

end CoordsSpec

/-! ### Points -/

/-- The value of a point at a coordinate, or `0` if it is not a coordinate. -/
def val (cs : List Crd) (x : List ℚ) (c : Crd) : ℚ := if c ∈ cs then x.getD (cs.idxOf c) 0 else 0

/-- The moment of `xᵉ`: `1` for `e = 0`. -/
def yv (cs : List Crd) (x : List ℚ) (e : List ℕ) : ℚ := if e.sum = 0 then 1 else val cs x (none, e)

/-- The auxiliary moment of `xᵉ` for the set `v`. -/
def wv (cs : List Crd) (x : List ℚ) (v e : List ℕ) : ℚ := val cs x (some v, e)

section PointsSpec

variable {n ℓ : ℕ} {A : System (Fin n) ℚ} {ds : List ℕ}

/-- The point of `SoS.Lifted.Coord → ℝ` that a list stands for. -/
noncomputable def pt (h : DegsSpec A ℓ ds) (x : List ℚ) : Coord A ℓ → ℝ :=
  fun k => (x.getD (equiv h k) 0 : ℝ)

theorem pt_apply (h : DegsSpec A ℓ ds) (x : List ℚ) (k : Coord A ℓ) :
    pt h x k = (val (coordsL n ℓ ds) x (crd k) : ℝ) := by
  rw [pt, val, ite_eq_left ((mem_coordsL h).2 ⟨k, rfl⟩), equiv_apply]

/-- **The moments of a point.** -/
theorem ys_pt (h : DegsSpec A ℓ ds) (x : List ℚ) (s : Fin n →₀ ℕ) :
    ys (pt h x) s = (yv (coordsL n ℓ ds) x (List.ofFn s) : ℝ) := by
  classical
  rw [ys, yv, sum_ofFn_finsupp]
  by_cases hs : s ∈ (monomialsLE (Fin n) ℓ).erase 0
  · rw [dite_eq_left hs, pt_apply, ite_eq_right (fun h0 => (Finset.mem_erase.1 hs).1
      ((Finsupp.degree_eq_zero_iff _).1 h0))]
    rfl
  · rw [dite_eq_right hs]
    by_cases h0 : s = 0
    · simp [h0]
    · rw [ite_eq_right h0, ite_eq_right (fun h' => h0 ((Finsupp.degree_eq_zero_iff _).1 h')), val,
        ite_eq_right]
      · simp
      · intro hmem
        obtain ⟨k, hk⟩ := (mem_coordsL h).1 hmem
        rcases k with ⟨s', hs'⟩ | ⟨S, s'⟩
        · simp only [crd, Prod.mk.injEq, true_and] at hk
          rw [ofFn_inj hk] at hs'
          exact hs hs'
        · simp [crd] at hk

/-- **The auxiliary moments of a point.** -/
theorem ws_pt (h : DegsSpec A ℓ ds) (x : List ℚ) (S : sets A ℓ) (s : Fin n →₀ ℕ) :
    ws (pt h x) S s = (wv (coordsL n ℓ ds) x (ind S.1) (List.ofFn s) : ℝ) := by
  classical
  rw [ws, wv]
  by_cases hs : s ∈ monomialsLE (Fin n) (ℓ - A.degree S.1)
  · rw [dite_eq_left hs, pt_apply]
    rfl
  · rw [dite_eq_right hs, val, ite_eq_right]
    · simp
    · intro hmem
      obtain ⟨k, hk⟩ := (mem_coordsL h).1 hmem
      rcases k with ⟨s', hs'⟩ | ⟨S', ⟨s', hs'⟩⟩
      · simp [crd] at hk
      · simp only [crd, Prod.mk.injEq, Option.some.injEq] at hk
        have hS : S' = S := Subtype.ext (ind_injective hk.1)
        subst hS
        rw [ofFn_inj hk.2] at hs'
        exact hs hs'

/-- The Riesz functional of the moments of a point on a raw polynomial. -/
def evalY (n : ℕ) (cs : List Crd) (x : List ℚ) (p : RawPoly) : ℚ :=
  (p.map fun t => t.2 * yv cs x (expo n t.1)).sum

theorem riesz_ys_pt (h : DegsSpec A ℓ ds) (x : List ℚ) (p : RawPoly) :
    riesz (ys (pt h x)) (toReal (p.toPoly n)) = (evalY n (coordsL n ℓ ds) x p : ℝ) := by
  rw [riesz_toPoly, evalY, Rat.cast_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by
    simp only [Function.comp, Rat.cast_mul]
    rw [ys_pt, ofFn_toFinsupp_expo]

end PointsSpec

/-! ### Sparse vectors -/

/-- A sparse vector: (coordinate, coefficient) pairs; a coordinate may appear several times. -/
abbrev Sp := List (Crd × ℚ)

/-- The coefficient of a coordinate in a sparse vector: the sum of its pairs. -/
def spAt (sp : Sp) (c : Crd) : ℚ := ((sp.filter fun q => decide (q.1 = c)).map Prod.snd).sum

/-- The dense vector on the coordinates `cs`. -/
def dense (cs : List Crd) (sp : Sp) : List ℚ := cs.map (spAt sp)

/-- A sparse vector times `a`. -/
def scale (a : ℚ) (sp : Sp) : Sp := sp.map fun q => (q.1, a * q.2)

/-- The gradient of `x ↦ L_{y(x)}(p)`, sparse. -/
def spY (n : ℕ) (p : RawPoly) : Sp := p.map fun t => ((none, expo n t.1), t.2)

/-- The gradient of `x ↦ L_{w_v(x)}(p)`, sparse. -/
def spW (n : ℕ) (v : List ℕ) (p : RawPoly) : Sp := p.map fun t => ((some v, expo n t.1), t.2)

theorem spAt_append (sp sp' : Sp) (c : Crd) : spAt (sp ++ sp') c = spAt sp c + spAt sp' c := by
  simp [spAt, List.filter_append]

theorem spAt_scale (a : ℚ) (sp : Sp) (c : Crd) : spAt (scale a sp) c = a * spAt sp c := by
  simp only [spAt, scale, List.filter_map, List.map_map]
  rw [← List.sum_map_mul_left]
  rfl

theorem spAt_flatMap {β : Type*} (l : List β) (f : β → Sp) (c : Crd) :
    spAt (l.flatMap f) c = (l.map fun b => spAt (f b) c).sum := by
  induction l with
  | nil => simp [spAt]
  | cons b l ih => rw [List.flatMap_cons, spAt_append, ih, List.map_cons, List.sum_cons]

theorem spAt_spY_none (n : ℕ) (p : RawPoly) (e : List ℕ) :
    spAt (spY n p) (none, e) = coeff n p e := by
  simp [spAt, spY, coeff, List.filter_map, Function.comp_def]

theorem spAt_spY_some (n : ℕ) (p : RawPoly) (v e : List ℕ) : spAt (spY n p) (some v, e) = 0 := by
  simp [spAt, spY, List.filter_map, Function.comp_def]

theorem spAt_spW_none (n : ℕ) (v : List ℕ) (p : RawPoly) (e : List ℕ) :
    spAt (spW n v p) (none, e) = 0 := by
  simp [spAt, spW, List.filter_map, Function.comp_def]

theorem spAt_spW_some (n : ℕ) (v : List ℕ) (p : RawPoly) (v' e : List ℕ) :
    spAt (spW n v p) (some v', e) = if v = v' then coeff n p e else 0 := by
  split_ifs with hv
  · subst hv
    simp [spAt, spW, coeff, List.filter_map, Function.comp_def]
  · simp [spAt, spW, List.filter_map, Function.comp_def, hv]

section SparseSpec

variable {n ℓ : ℕ} {A : System (Fin n) ℚ} {ds : List ℕ}

/-- **Dense vectors**: the point of a dense vector reads its sparse coefficients. -/
theorem pt_dense (h : DegsSpec A ℓ ds) (sp : Sp) (k : Coord A ℓ) :
    pt h (dense (coordsL n ℓ ds) sp) k = (spAt sp (crd k) : ℝ) := by
  rw [pt, dense, List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  congr 2
  exact get_equiv h k

theorem coeff_toReal_toPoly (p : RawPoly) (s : Fin n →₀ ℕ) :
    (toReal (p.toPoly n)).coeff s = (coeff n p (List.ofFn s) : ℝ) := by
  rw [toReal, coeff_map, ← coeff_toPoly p (by simp), toFinsupp_ofFn]
  rfl

/-- **The gradient on the moments**, sparse. -/
theorem spAt_spY (p : RawPoly) (k : Coord A ℓ) :
    (spAt (spY n p) (crd k) : ℝ) = gradY (toReal (p.toPoly n)) k := by
  rcases k with s | s
  · rw [crd, spAt_spY_none, gradY, Sum.elim_inl, coeff_toReal_toPoly]
  · rw [crd, spAt_spY_some, gradY, Sum.elim_inr]
    simp

/-- **The gradient on an auxiliary sequence**, sparse. -/
theorem spAt_spW (S : sets A ℓ) (p : RawPoly) (k : Coord A ℓ) :
    (spAt (spW n (ind S.1) p) (crd k) : ℝ) = gradW S (toReal (p.toPoly n)) k := by
  rcases k with s | ⟨S', s⟩
  · rw [crd, spAt_spW_none, gradW, Sum.elim_inl]
    simp
  · rw [crd, spAt_spW_some, gradW, Sum.elim_inr]
    by_cases hS : S' = S
    · subst hS
      simp [coeff_toReal_toPoly]
    · have : ind S.1 ≠ ind S'.1 := fun h' => hS (Subtype.ext (ind_injective h').symm)
      simp [this, hS]

end SparseSpec

/-! ### Monomials as lists -/

theorem monomialsLE_eq (n D : ℕ) :
    monomialsLE (Fin n) D = ((Mono.all n D).map (Mono.toFinsupp n)).toFinset := by
  classical
  ext s
  rw [mem_monomialsLE, List.mem_toFinset, List.mem_map]
  constructor
  · intro hs
    exact ⟨List.ofFn s, Mono.mem_all.2 ⟨by simp, by rw [sum_ofFn_finsupp]; exact hs⟩,
      toFinsupp_ofFn s⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨hlen, hle⟩ := Mono.mem_all.1 he
    rw [Mono.degree_toFinsupp hlen]
    exact hle

/-- A sum over the monomials of degree at most `D` is a sum over `Mono.all n D`. -/
theorem sum_monomialsLE {M : Type*} [AddCommMonoid M] (n D : ℕ) (F : (Fin n →₀ ℕ) → M) :
    ∑ s ∈ monomialsLE (Fin n) D, F s =
      ((Mono.all n D).map fun e => F (Mono.toFinsupp n e)).sum := by
  classical
  have hinj : ∀ e ∈ Mono.all n D, ∀ e' ∈ Mono.all n D,
      Mono.toFinsupp n e = Mono.toFinsupp n e' → e = e' :=
    fun e he e' he' h => Mono.toFinsupp_inj (Mono.mem_all.1 he).1 (Mono.mem_all.1 he').1 h
  have hnd : ((Mono.all n D).map (Mono.toFinsupp n)).Nodup := (Mono.nodup_all n D).map_on hinj
  rw [monomialsLE_eq, List.sum_toFinset _ hnd, List.map_map]
  rfl

/-! ### Polynomials from coefficient vectors -/

/-- `∑ wᵢ x^(eᵢ)` as a raw polynomial. -/
def polyRaw (es : List (List ℕ)) (w : List ℚ) : RawPoly := es.zip w

theorem sum_map_getElem {M β : Type*} [AddCommMonoid M] (l : List β) (f : β → M) :
    (l.map f).sum = ∑ i : Fin l.length, f l[i] := by
  have : l.map f = List.ofFn fun i : Fin l.length => f l[i] := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [this, List.sum_ofFn]

/-- The polynomial of a coefficient vector on the monomials `es` is `SoS.polyOf`. -/
theorem toReal_toPoly_polyRaw (n : ℕ) {es : List (List ℕ)} {w : List ℚ}
    (hw : w.length = es.length) :
    toReal ((polyRaw es w).toPoly n) =
      polyOf (fun i : Fin es.length => Mono.toFinsupp n es[i])
        (fun i => (w[i.1]'(by rw [hw]; exact i.2) : ℝ)) := by
  rw [toReal_toPoly, polyRaw, sum_map_getElem, polyOf]
  have hlen : (es.zip w).length = es.length := by simp [hw]
  refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
  simp [List.getElem_zip]

/-- The product of raw polynomials, term by term. -/
def mulRaw (n : ℕ) (p q : RawPoly) : RawPoly :=
  p.flatMap fun s => q.map fun t => (addE n s.1 t.1, s.2 * t.2)

theorem toPoly_mulRaw (n : ℕ) (p q : RawPoly) :
    (mulRaw n p q).toPoly n = p.toPoly n * q.toPoly n := by
  rw [toPoly_eq_sum', toPoly_eq_sum', toPoly_eq_sum', mulRaw, List.flatMap, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_map, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [termPoly, toFinsupp_addE, monomial_mul_monomial]

end SoS.Coords
