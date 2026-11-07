module

public import Background.SumOfSquares.Algorithm.Loop
public import Background.SumOfSquares.GridMoments

/-!
# The algorithm

`SoS.Core.core (x, L)`: the sum-of-squares algorithm on the input `x` with the budget `L`.

1. Read the problem, with the number of variables and the degree capped at `L`, and the degrees
   of the constraints capped at `ℓ + 1` (`SoS.Poly.degCap`).
2. List the sets of constraints, the coordinates, and the data of each set: its monomials, the
   product of its constraints (`SoS.Poly.prodRaw`) and the product of their squared norms, all
   within the budget (`SoS.Core.setsB`, `SoS.Core.coordsB`, `SoS.Core.setDataB`). With a large
   enough budget these are the lists of `Background/SumOfSquares/Algorithm/Coords.lean` and
   `Background/SumOfSquares/Algorithm/Oracle.lean` (`SoS.Core.setsB_eq`, `SoS.Core.coordsB_eq`,
   `SoS.Core.setDataB_eq`).
3. Run the ellipsoid loop with the oracle, from the ball of radius `√s` around `0`, with the
   parameters of `SoS.Core.expK` (the number of steps), `SoS.Core.expP` (the precision) and
   `SoS.Core.expB` (the clamp), all powers of `2` in the size `Z = |x| + L + 4` and the
   dimension `N`.
4. Mix the best center's moments with the grid moments in the ratio `1 : t`
   (`SoS.Core.outputL`, `SoS.Core.coeff_outputL`).
-/

@[expose] public section

namespace SoS.Core

open MvPolynomial SoS.Solver SoS.Poly SoS.Coords SoS.Oracle SoS.Loop SoS.Lifted

/-! ### The constraints of a set -/

/-- The constraints of the set with indicator vector `v`. -/
def pick (As : List RawPoly) (v : List ℕ) : List RawPoly :=
  ((List.range As.length).filter fun i => decide (v.getD i 0 = 1)).map fun i => As.getD i []

theorem toFinset_filter_ind {m : ℕ} (S : Finset (Fin m)) :
    ((List.range m).filter fun i => decide ((ind S).getD i 0 = 1)).toFinset =
      S.map Fin.valEmbedding := by
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hi, h1⟩
    refine ⟨⟨i, hi⟩, ?_, rfl⟩
    have := getD_ind S ⟨i, hi⟩
    simp only at this
    rw [this] at h1
    by_contra hS
    simp [hS] at h1
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2, ?_⟩
    rw [getD_ind S j]
    simp [hj]

/-- A product over a set of constraints is a product over `pick`. -/
theorem prod_pick {M : Type*} [CommMonoid M] (φ : RawPoly → M) (As : List RawPoly) {m : ℕ}
    (hm : m = As.length) (S : Finset (Fin m)) :
    ((pick As (ind S)).map φ).prod = ∏ i ∈ S, φ (As.getD i []) := by
  subst hm
  have hnd : ((List.range As.length).filter fun i => decide ((ind S).getD i 0 = 1)).Nodup :=
    List.nodup_range.filter _
  rw [pick, List.map_map, ← List.prod_toFinset _ hnd, toFinset_filter_ind, Finset.prod_map]
  rfl

theorem get_map_toPoly (n : ℕ) (As : List RawPoly) (i : Fin (As.map (RawPoly.toPoly n)).length) :
    (As.map (RawPoly.toPoly n)).get i = (As.getD i []).toPoly n := by
  have hi : (i : ℕ) < As.length := by simpa using i.2
  simp [List.getElem?_eq_getElem hi]

/-- The product of the constraints of `S`. -/
theorem prod_pick_toPoly (n : ℕ) (As : List RawPoly)
    (S : Finset (Fin (As.map (RawPoly.toPoly n)).length)) :
    ((pick As (ind S)).map (RawPoly.toPoly n)).prod =
      System.prod (As.map (RawPoly.toPoly n)) S := by
  rw [prod_pick _ As (by simp), System.prod]
  exact Finset.prod_congr rfl fun i _ => (get_map_toPoly n As i).symm

/-- **The data of the sets are right**, when the products are within the budget. -/
theorem setDataSpec (n ℓ L : ℕ) (As : List RawPoly)
    (hL : ∀ S ∈ sets (As.map (RawPoly.toPoly n)) ℓ,
      ((pick As (ind S)).map List.length).prod ≤ L) :
    SetDataSpec (As.map (RawPoly.toPoly n)) ℓ (fun v => prodRaw n L (pick As v))
      (fun v => ((pick As v).map (normSq n)).prod) := by
  classical
  refine ⟨fun S hS => ?_, fun S hS => ?_⟩
  · rw [toPoly_prodRaw _ (hL S hS), prod_pick_toPoly]
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hi, hiS⟩ := List.mem_filter.1 hi
    have hi' : i < As.length := List.mem_range.1 hi
    have hmem : (⟨i, by simpa using hi'⟩ : Fin (As.map (RawPoly.toPoly n)).length) ∈ S := by
      have := getD_ind S ⟨i, by simpa using hi'⟩
      simp only at this
      simp only [decide_eq_true_eq, this] at hiS
      by_contra h
      simp [h] at hiS
    have hnc := (Finset.mem_filter.1 hS).2.2.1 _ hmem
    rw [get_map_toPoly] at hnc
    intro h0
    rw [h0] at hnc
    simp [RawPoly.toPoly] at hnc
  · rw [Rat.cast_list_prod, List.map_map, prod_pick ((Rat.cast : ℚ → ℝ) ∘ normSq n) As (by simp)]
    exact Finset.prod_congr rfl fun i _ => by rw [get_map_toPoly, coeffNorm_toReal_sq]; rfl

/-! ### Within the budget -/

/-- The sets, within the budget. -/
def setsB (L ℓ : ℕ) (ds : List ℕ) : List (List ℕ) := (Mono.allB L ds.length ℓ).filter (isSet ℓ ds)

/-- The coordinates, within the budget. -/
def coordsB (L n ℓ : ℕ) (ds : List ℕ) : List Crd :=
  ((Mono.allB L n ℓ).filter fun e => decide (e.sum ≠ 0)).map (fun e => (none, e)) ++
    (setsB L ℓ ds).flatMap fun v => (Mono.allB L n (ℓ - dsum ds v)).map fun e => (some v, e)

/-- The data of the sets, within the budget. -/
def setDataB (L n ℓ : ℕ) (As : List RawPoly) (ds : List ℕ) : List SetData :=
  (setsB L ℓ ds).map fun v => (v, Mono.allB L n ((ℓ - dsum ds v) / 2),
    Mono.allB L n (ℓ - dsum ds v), prodRaw n L (pick As v), ((pick As v).map (normSq n)).prod)

/-- The budget is large enough: it covers the degree and the monomials in `n` variables and in
`m` variables (for the sets). -/
structure Enough (L n m ℓ : ℕ) : Prop where
  deg : ℓ ≤ L
  vars : (n + 1) ^ ℓ ≤ L
  cons : (m + 1) ^ ℓ ≤ L

theorem allB_eq_of_le {L n ℓ D : ℕ} (h : Enough L n 0 ℓ) (hD : D ≤ ℓ) :
    Mono.allB L n D = Mono.all n D :=
  Mono.allB_eq (hD.trans h.deg)
    ((Nat.pow_le_pow_right (Nat.succ_pos _) hD).trans h.vars)

theorem setsB_eq {L n ℓ : ℕ} {ds : List ℕ} (h : Enough L n ds.length ℓ) :
    setsB L ℓ ds = setsL ℓ ds := by
  rw [setsB, setsL, Mono.allB_eq h.deg h.cons]

theorem coordsB_eq {L n ℓ : ℕ} {ds : List ℕ} (h : Enough L n ds.length ℓ) :
    coordsB L n ℓ ds = coordsL n ℓ ds := by
  have h' : Enough L n 0 ℓ :=
    ⟨h.deg, h.vars, by simpa using (Nat.one_le_pow _ _ (Nat.succ_pos n)).trans h.vars⟩
  rw [coordsB, coordsL, setsB_eq h, allB_eq_of_le h' le_rfl]
  congr 1
  refine List.flatMap_congr fun v _ => ?_
  rw [allB_eq_of_le h' (Nat.sub_le _ _)]

theorem setDataB_eq {L n ℓ : ℕ} {As : List RawPoly} {ds : List ℕ} (h : Enough L n ds.length ℓ) :
    setDataB L n ℓ As ds = setData n ℓ ds (fun v => prodRaw n L (pick As v))
      (fun v => ((pick As v).map (normSq n)).prod) := by
  have h' : Enough L n 0 ℓ :=
    ⟨h.deg, h.vars, by simpa using (Nat.one_le_pow _ _ (Nat.succ_pos n)).trans h.vars⟩
  rw [setDataB, setData, setsB_eq h]
  refine List.map_congr_left fun v _ => ?_
  rw [allB_eq_of_le h' ((Nat.div_le_self _ _).trans (Nat.sub_le _ _)),
    allB_eq_of_le h' (Nat.sub_le _ _)]

/-! ### The output -/

/-- The grid moment of `xᵉ`: `∏ i, (∑ t ≤ d, t^(eᵢ)) / (d + 1)`. -/
def gridL (d : ℕ) (e : List ℕ) : ℚ :=
  (e.map fun k => ((List.range (d + 1)).map fun t : ℕ => (t : ℚ) ^ k).sum / (d + 1)).prod

theorem gridL_eq {n : ℕ} (d : ℕ) {e : List ℕ} (he : e.length = n) :
    gridL d e = gridMoment d (Mono.toFinsupp n e) := by
  subst he
  rw [gridL, gridMoment]
  conv_lhs => rw [← List.ofFn_getElem (xs := e)]
  rw [List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Mono.toFinsupp_apply, List.getD_eq_getElem _ _ i.2, Function.comp_apply, sum_range_map,
    ← Fin.sum_univ_eq_sum_range (fun t => (t : ℚ) ^ e[(i : ℕ)])]

/-- The output: the moments of `x` mixed with the grid moments in the ratio `1 : t`, for the
monomials of degree at most `ℓ`. -/
def outputL (L n ℓ : ℕ) (cs : List Crd) (x : List ℚ) (t : ℚ) : RawPoly :=
  (Mono.allB L n ℓ).map fun e => (e, (yv cs x e + t * gridL (ℓ / 2) e) / (1 + t))

theorem coeff_map_of_mem {n : ℕ} {l : List (List ℕ)} (hl : l.Nodup) (hlen : ∀ e ∈ l, e.length = n)
    (g : List ℕ → ℚ) {m : List ℕ} (hm : m ∈ l) : coeff n (l.map fun e => (e, g e)) m = g m := by
  rw [coeff, List.filter_map, List.map_map]
  have hfilter : l.filter ((fun t : List ℕ × ℚ => decide (expo n t.1 = m)) ∘ fun e => (e, g e)) =
      [m] := by
    have : l.filter ((fun t : List ℕ × ℚ => decide (expo n t.1 = m)) ∘ fun e => (e, g e)) =
        l.filter fun e => e == m := by
      refine List.filter_congr fun e he => ?_
      have hee : expo n e = e := by
        rw [← ofFn_toFinsupp_expo, ofFn_toFinsupp (hlen e he)]
      simp only [Function.comp, hee, beq_eq_decide]
    rw [this, List.filter_beq, List.count_eq_one_of_mem hl hm, List.replicate_one]
  rw [hfilter]
  simp

/-- **The output's coefficients.** -/
theorem coeff_outputL {L n ℓ : ℕ} (h : Enough L n 0 ℓ) (cs : List Crd) (x : List ℚ) (t : ℚ)
    (s : Fin n →₀ ℕ) (hs : s.degree ≤ ℓ) :
    ((outputL L n ℓ cs x t).toPoly n).coeff s =
      (yv cs x (List.ofFn s) + t * gridMoment (ℓ / 2) s) / (1 + t) := by
  have hmem : List.ofFn s ∈ Mono.all n ℓ :=
    Mono.mem_all.2 ⟨by simp, by rw [sum_ofFn_finsupp]; exact hs⟩
  conv_lhs => rw [← toFinsupp_ofFn s]
  rw [coeff_toPoly _ (by simp), outputL, allB_eq_of_le h le_rfl,
    coeff_map_of_mem (Mono.nodup_all n ℓ) (fun e he => (Mono.mem_all.1 he).1) _ hmem,
    gridL_eq (n := n) _ (by simp), toFinsupp_ofFn]

/-! ### The algorithm -/

/-- The number of steps: `6 N² (64 Z⁴ + 8 Z² + 1)`. -/
def expK (Z N : ℕ) : ℕ := 6 * N ^ 2 * (64 * Z ^ 4 + 8 * Z ^ 2 + 1)

/-- The precision `p`: numbers are multiples of `2^-p`. -/
def expP (Z N : ℕ) : ℕ := 2 * expK Z N + 3 * N + 16

/-- The clamp `B = 2^b`. -/
def expB (Z N : ℕ) : ℕ := 2 * expK Z N + 1 + 8 * Z ^ 2

/-- The size `Z = |x| + L + 4`. -/
def sizeZ (x : Input) (L : ℕ) : ℕ := (encInput x).length + L + 4

/-- The context of the loop: the number of variables, the coordinates, the monomials of the
moment matrix, the data of the sets, the objective, and the oracle's `η`, `τ`, `R`. -/
abbrev Ctx := ℕ × List Crd × List (List ℕ) × List SetData × RawPoly × List RawPoly × ℚ × ℚ × ℚ

/-- The context for the input `x` and the budget `L`. -/
def ctx (x : Input × ℕ) : Ctx :=
  let L := x.2
  let Z := sizeZ x.1 L
  let n := min L x.1.1.1
  let ℓ := min L x.1.1.2.1
  let As := x.1.1.2.2.1
  let ds := As.map (degCap n (ℓ + 1))
  (n, coordsB L n ℓ ds, Mono.allB L n (ℓ / 2), setDataB L n ℓ As ds, x.1.1.2.2.2.1,
    x.1.1.2.2.2.2, x.1.2.1 + x.1.2.2 / 2, 1 / 2 ^ (16 * Z ^ 4), 2 ^ (3 * Z ^ 2 + 1))

/-- The oracle of a context. -/
def ctxOracle (c : Ctx) : List ℚ → Bool × List ℚ :=
  oracle c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1
    c.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2

/-- The objective of a context. -/
def ctxObj (c : Ctx) : List ℚ → ℚ := objVal c.1 c.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1

/-- The starting shape `s I`. -/
def shape₀ (N : ℕ) (s : ℚ) : List (List ℚ) :=
  (List.range N).map fun i => (List.range N).map fun j => if i = j then s else 0

/-- The final state of the loop. -/
def finalState (x : Input × ℕ) : State :=
  let Z := sizeZ x.1 x.2
  let N := (ctx x).2.1.length
  run N (expP Z N) (2 ^ expB Z N) (ctxOracle (ctx x)) (ctxObj (ctx x)) (List.replicate N 0)
    (shape₀ N (2 ^ (8 * Z ^ 2))) (expK Z N)

/-- **The algorithm** on the input `x` with the budget `L`. -/
def core (x : Input × ℕ) : Output :=
  let Z := sizeZ x.1 x.2
  let ℓ := min x.2 x.1.1.2.1
  let N := (ctx x).2.1.length
  outputL x.2 (ctx x).1 ℓ (ctx x).2.1
    (if (finalState x).2.2.1 then (finalState x).2.2.2 else List.replicate N 0)
    (1 / 2 ^ (8 * Z ^ 2))

end SoS.Core
