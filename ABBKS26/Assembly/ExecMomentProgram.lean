module

public import ABBKS26.Assembly.ExecMomentProgramAuxPoly
public import ABBKS26.Assembly.ExecMomentProgramAuxAnalytic
public import ABBKS26.Assembly.ExecMomentProgramAuxRead

/-!
# The moment program

The shared moment interfaces (here to avoid an import cycle with `ExecMoment`). The program
builds rational coefficient equations with row-major Gram blocks, calls the budgeted solver,
and reads clipped rational weights on the original block. Its guard bounds expansion counts,
not coefficient bits; when it succeeds, the budgeted expansions agree with the original
program.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Robust
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

abbrev MomentArgs := Points × List ℕ × List ℕ × ℚ × ℚ
abbrev encMomentArgs := encPair encPoints
  (encPair encIndices (encPair encIndices (encPair encRat encRat)))
abbrev encMomentInput := encPair encMomentArgs encUnary
abbrev MomentInput := MomentArgs × ℕ

structure MomentCode where
  prepare : MomentInput → SoS.Solver.Input × ℕ
  recover : MomentInput × SoS.Solver.Output → List SoS.Solver.RawPoly

/-- Both the degree-two solver call and recovery retain the original rational sample. -/
def momentL (M : MomentCode) (q : MomentInput) : List SoS.Solver.RawPoly :=
  M.recover (q, SoS.Core.core (M.prepare q))

noncomputable def momentProc (M : MomentCode) : MomentProc :=
  fun x N J w ε fuel r ↦
    ((momentL M ((pointsOf x, indexList N, J.sort (· ≤ ·), w, ε), fuel)).getD r []).toPoly _

/-- A sharper sufficient budget than the coarse original `MomentContract` hypothesis. -/
noncomputable def momentFuel (n d : ℕ) (J : Finset ℕ) : ℕ :=
  (n + d + 2) ^ (100 * (Rounding.solverConstant + 1)) *
    (d + 2) ^ (100 * (Rounding.solverConstant + 1) * (J.sup id + 1) ^ 2)

/-- The same analytic guarantee, with an absolute exponent on the sample size. -/
def MomentAdequate (run : MomentProc) : Prop :=
  ∀ {n k d} (D : Reference n k d) (x : Fin n → Fin d → ℚ)
    (J : Finset ℕ) (w ε : ℚ) (θ : ℝ) fuel,
    D.Valid w → (∀ l i, D.observed l i = (x l i : ℝ)) → (∀ j ∈ J, 1 ≤ j) →
    D.Resilient (2 * J.sup id) θ → 0 ≤ θ → θ ≤ 1 / 100000000 →
    D.contamination ≤ ε → ε ≤ 1 / 8 →
    (∀ j, sqnorm (D.model.mean j) ≤ 2 / w) →
    (∀ j, LE (D.model.cov j) ((1.1 / (w : ℝ)) • (1 : Mat d))) →
    momentFuel n d J ≤ fuel →
    Certified D.model (fun r ↦ SoS.toReal (run x D.block J w ε fuel r)) J
      (fun r ↦ 250 * ε * momentBudget w r + 3 * θ ^ 2 * momentBudget w r)

namespace MomentProgram

open MvPolynomial
open SoS.Solver (RawPoly Problem)
open scoped BigOperators

/-- The largest requested order, also for empty or repeated degree lists. -/
def maxDegree (J : List ℕ) : ℕ := J.foldr max 0

/-- Keep each original row once, in its original order, ignoring junk block indices. -/
def blockPoints (a : MomentArgs) : Points :=
  (a.1.zipIdx.filter fun p ↦ p.2 ∈ a.2.1).map Prod.fst

def dimension (a : MomentArgs) : ℕ := dim a.1

def orders (a : MomentArgs) : List ℕ := a.2.2.1

/-- A deliberately generous bound on every outer polynomial expansion. -/
def expansionBound (a : MomentArgs) : ℕ :=
  (dimension a + 2) ^ (6 * (maxDegree (orders a) + 1))

/-- Test the binary order before exponentiation; no large list is built before this guard. -/
def enabled (q : MomentInput) : Bool :=
  if maxDegree (orders q.1) ≤ q.2 then decide (expansionBound q.1 ≤ q.2) else false

/-- The exponent vector of a single variable, with explicit ambient dimension. -/
def unitExp (v i e : ℕ) : List ℕ :=
  (List.range v).map fun j ↦ if j = i then e else 0

def constant (c : ℚ) : RawPoly := [([], c)]

def scale (c : ℚ) (p : RawPoly) : RawPoly := p.map fun t ↦ (t.1, c * t.2)

/-- Sequential multiplication bounds coefficient bits linearly in the order. -/
def power (d : ℕ) (p : RawPoly) (r : ℕ) : RawPoly :=
  (fun q ↦ SoS.Coords.mulRaw d q p)^[r] (constant 1)

def linear (d : ℕ) (x : Vector) : RawPoly :=
  (List.range d).map fun i ↦ (unitExp d i 1, x.getD i 0)

def normSq (d : ℕ) : RawPoly :=
  (List.range d).map fun i ↦ (unitExp d i 2, 1)

/-- Exactly the offsets in `Robust.momentGramOffset`, without real coefficients. -/
def gramOffset (n d : ℕ) (J : List ℕ) (a : ℕ) : ℕ :=
  n + ((J.take a).map fun r ↦ (SoS.Mono.all d r).length ^ 2).sum

def numVars (n d : ℕ) (J : List ℕ) : ℕ := gramOffset n d J J.length

/-- Twice the analytic moment budget leaves room for deleting the reference outliers. -/
def budget (w : ℚ) (r : ℕ) : ℚ := 4 * (20 * r / w) ^ r

/-- The coefficient of `v^μ` in the row-major Gram factor expansion.
The column index is shared by the two entries; both row indices range independently. -/
def gramCoeff (v d start r : ℕ) (μ : List ℕ) : RawPoly :=
  let L := SoS.Mono.all d r
  L.zipIdx.flatMap fun a ↦ L.zipIdx.flatMap fun b ↦
    if SoS.Poly.addE d a.1 b.1 = μ then
      (List.range L.length).map fun c ↦
        (SoS.Poly.addE v (unitExp v (start + a.2 * L.length + c) 1)
          (unitExp v (start + b.2 * L.length + c) 1), 1)
    else []

/-- One coefficient equation: radial constant minus weighted data minus Gram products. -/
def coefficient (d : ℕ) (pts : Points) (J : List ℕ) (w : ℚ)
    (a : ℕ) (μ : List ℕ) : RawPoly :=
  let r := J.getD a 0
  let v := numVars pts.length d J
  constant (budget w r * pts.length * SoS.Poly.coeff d (power d (normSq d) r) μ) ++
    (pts.zipIdx.map fun p ↦
      (unitExp v p.2 1, -SoS.Poly.coeff d (power d (linear d p.1) (2 * r)) μ)) ++
    scale (-1) (gramCoeff v d (gramOffset pts.length d J a) r μ)

/-- Explicit ball, weight interval, mass, and paired coefficient constraints, in that order. -/
def constraints (d : ℕ) (pts : Points) (J : List ℕ) (w ε ball : ℚ) : List RawPoly :=
  let v := numVars pts.length d J
  [constant ball ++ (List.range v).map (fun i ↦ (unitExp v i 2, -1))] ++
    (List.range pts.length).flatMap (fun i ↦
      [[(unitExp v i 1, 1)], constant 1 ++ [(unitExp v i 1, -1)]]) ++
    [(List.range pts.length).map (fun i ↦ (unitExp v i 1, 1)) ++
      constant (-((1 - ε) * pts.length))] ++
    (List.range J.length).flatMap (fun a ↦
      (SoS.Mono.all d (2 * J.getD a 0)).flatMap fun μ ↦
        let c := coefficient d pts J w a μ
        [c, scale (-1) c])

/-- A dyadic ball whose exponent is polynomial in data bits and the largest order. -/
def ball (a : MomentArgs) : ℚ :=
  2 ^ (((encMomentArgs a).length + 2) ^ 4 * (maxDegree (orders a) + 1) ^ 4)

/-- Zero objective, degree two, and all unknowns including the Gram-factor entries. -/
def problem (a : MomentArgs) : Problem :=
  let pts := blockPoints a
  let d := dimension a
  let J := orders a
  (numVars pts.length d J, 2, constraints d pts J a.2.2.2.1 a.2.2.2.2 (ball a), [], [])

/-- The fallback also has degree two and an explicit ball in zero numVars. -/
def fallback : Problem := (0, 2, [constant 1], [], [])

def guardedProblem (q : MomentInput) : Problem :=
  if enabled q then problem q.1 else fallback

/-- Accuracy pays for the coefficient bits as well as the mass and clipping residuals. -/
def precision (q : MomentInput) : ℕ :=
  ((SoS.Solver.encProblem (guardedProblem q)).length + (encMomentArgs q.1).length + 2) ^ 2

def accuracy (q : MomentInput) : ℚ := 1 / 2 ^ precision q

/-- The solver budget is cubic in its encoded problem size because its degree is two. -/
def prepare (q : MomentInput) : SoS.Solver.Input × ℕ :=
  ((guardedProblem q, accuracy q, accuracy q),
    ((SoS.Solver.encProblem (guardedProblem q)).length + 2) ^ 3)

/-- Read a degree-one pseudo-moment and clip it in rational arithmetic. -/
def readWeight (v : ℕ) (out : SoS.Solver.Output) (i : ℕ) : ℚ :=
  min (max (SoS.Poly.coeff v out (unitExp v i 1)) 0) 1

/-- Normalized rational moments; the solver's rational rounding is retained exactly. -/
def recover (qout : MomentInput × SoS.Solver.Output) : List RawPoly :=
  let q := qout.1
  if enabled q then
    let a := q.1
    let pts := blockPoints a
    let d := dimension a
    let J := orders a
    let v := numVars pts.length d J
    let weights := (List.range pts.length).map (readWeight v qout.2)
    let W := weights.sum
    (List.range (maxDegree J + 1)).map fun r ↦
      if r ∈ J then
        (pts.zip weights).flatMap fun p ↦ scale (p.2 / W) (power d (linear d p.1) r)
      else []
  else []

def code : MomentCode := ⟨prepare, recover⟩

/-- Decode a list of rational rows using an explicit outer dimension. -/
noncomputable def realPoints (d : ℕ) (pts : Points) : Fin pts.length → Vec d :=
  fun i j ↦ ((pts[i]).getD j.val 0 : ℝ)

/-- Executable and analytic Gram offsets agree, including empty prefixes. -/
theorem gramOffset_agrees (n d : ℕ) (J : List ℕ) (a : ℕ) :
    gramOffset n d J a = momentGramOffset n d J a := by
  simp [gramOffset, momentGramOffset, Rounding.monos]

/-- The rational radial budget is exactly twice the analytic budget. -/
theorem budget_agrees (w : ℚ) (r : ℕ) :
    (budget w r : ℝ) = 2 * momentBudget w r := by
  simp only [budget, momentBudget, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_natCast]
  ring

/-- The list maximum agrees with the finite-set maximum used in both contracts. -/
theorem maxDegree_sort (J : Finset ℕ) : maxDegree (J.sort (· ≤ ·)) = J.sup id := by
  simpa [maxDegree] using
    (List.foldr_sup_eq_sup_toFinset (J.sort (· ≤ ·)))

/-- Empty typed samples lose their dimension; every nonempty sample retains it. -/
theorem dimension_pointsOf_le {n d : ℕ} (x : Fin n → Fin d → ℚ)
    (N J : List ℕ) (w ε : ℚ) : dimension (pointsOf x, N, J, w, ε) ≤ d := by
  cases n with
  | zero => simp [dimension, dim, pointsOf]
  | succ n => simp [dimension, dim, pointsOf, List.ofFn_succ]

/-- A bound on expansion counts also bounds the order, so it opens the entire guard. -/
theorem enabled_of_bound (q : MomentInput) (h : expansionBound q.1 ≤ q.2) :
    enabled q = true := by
  have hm : maxDegree (orders q.1) ≤ expansionBound q.1 := by
    let r := maxDegree (orders q.1)
    calc
      r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
      _ ≤ (dimension q.1 + 2) ^ r := Nat.pow_le_pow_left (by omega) _
      _ ≤ expansionBound q.1 := Nat.pow_le_pow_right (by omega) (by
        dsimp only [r]; omega)
  simp [enabled, hm.trans h, h]

/-- The original coarse hypothesis opens the guard without any bound on sample bits. -/
theorem enabled_of_coarse {n d : ℕ} (x : Fin n → Fin d → ℚ) (N : Finset (Fin n))
    (J : Finset ℕ) (w ε : ℚ) (fuel : ℕ)
    (hf : (n + d + 2) ^ (100 * (J.sup id + 1)) ≤ fuel) :
    enabled ((pointsOf x, indexList N, J.sort (· ≤ ·), w, ε), fuel) = true := by
  apply enabled_of_bound
  apply le_trans _ hf
  dsimp only [expansionBound, orders]
  rw [maxDegree_sort]
  have hd := dimension_pointsOf_le x (indexList N) (J.sort (· ≤ ·)) w ε
  calc
    _ ≤ (n + d + 2) ^ (6 * (J.sup id + 1)) := Nat.pow_le_pow_left (by omega) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

/-- The sharper sufficient fuel opens the same guard by a separate dimension estimate. -/
theorem enabled_of_adequate {n d : ℕ} (x : Fin n → Fin d → ℚ)
    (N : Finset (Fin n)) (J : Finset ℕ) (w ε : ℚ) (fuel : ℕ)
    (hf : momentFuel n d J ≤ fuel) :
    enabled ((pointsOf x, indexList N, J.sort (· ≤ ·), w, ε), fuel) = true := by
  apply enabled_of_bound
  apply le_trans _ hf
  dsimp only [expansionBound, orders, momentFuel]
  rw [maxDegree_sort]
  have hd := dimension_pointsOf_le x (indexList N) (J.sort (· ≤ ·)) w ε
  have hexp : 6 * (J.sup id + 1) ≤
      100 * (Rounding.solverConstant + 1) * (J.sup id + 1) ^ 2 := by
    have hs : 1 ≤ Rounding.solverConstant + 1 := by omega
    have hr : J.sup id + 1 ≤ (J.sup id + 1) ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ (d + 2) ^ (6 * (J.sup id + 1)) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (d + 2) ^ (100 * (Rounding.solverConstant + 1) * (J.sup id + 1) ^ 2) :=
      Nat.pow_le_pow_right (by omega) hexp
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

/-- Every call, including the fallback, uses exactly degree two. -/
theorem degree_two (q : MomentInput) : (prepare q).1.1.degree = 2 := by
  dsimp only [prepare]
  unfold guardedProblem
  split <;> rfl

/-- The prepared unary budget is exactly the existing solver's certified budget. -/
theorem prepare_budget (q : MomentInput) : (prepare q).2 = SoS.Solver.budget (prepare q).1 := by
  change _ = ((SoS.Solver.encProblem (guardedProblem q)).length + 2) ^
    ((guardedProblem q).degree + 1)
  have hd : (guardedProblem q).degree = 2 := degree_two q
  rw [hd]
  rfl

/-- Both requested solver accuracies are strictly positive dyadic rationals. -/
theorem accuracy_pos (q : MomentInput) : 0 < accuracy q := by
  unfold accuracy
  positivity

/-- Constant lists have their advertised polynomial value in every dimension. -/
theorem constant_toPoly (v : ℕ) (c : ℚ) :
    (constant c).toPoly v = C c := by
  simp [constant, SoS.Solver.RawPoly.toPoly]

/-- Scaling a raw polynomial scales its interpretation, with duplicate terms retained. -/
theorem scale_toPoly (v : ℕ) (c : ℚ) (p : RawPoly) :
    (scale c p).toPoly v = C c * p.toPoly v := by
  simp only [scale, SoS.Solver.RawPoly.toPoly, List.map_map,
    ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [mul_assoc]

/-- Sequential raw powers agree with polynomial powers. -/
theorem power_toPoly (d : ℕ) (p : RawPoly) (r : ℕ) :
    (power d p r).toPoly d = p.toPoly d ^ r := by
  induction r with
  | zero => simp [power, constant_toPoly]
  | succ r ih =>
    rw [power, Function.iterate_succ_apply', SoS.Coords.toPoly_mulRaw]
    change (power d p r).toPoly d * p.toPoly d = _
    rw [ih, pow_succ]

/-- A dense single-variable exponent vector decodes to the corresponding finitely supported one. -/
theorem unitExp_toFinsupp (v i e : ℕ) (hi : i < v) :
    SoS.Mono.toFinsupp v (unitExp v i e) = Finsupp.single ⟨i, hi⟩ e := by
  ext j
  simp [unitExp, List.getD_eq_getElem?_getD, Finsupp.single_apply, Fin.ext_iff,
    eq_comm]

/-- Interpreting a singleton term needs only an in-range variable index. -/
theorem unit_toPoly (v i e : ℕ) (c : ℚ) (hi : i < v) :
    SoS.Solver.RawPoly.toPoly v [(unitExp v i e, c)] = C c * X ⟨i, hi⟩ ^ e := by
  rw [SoS.Poly.toPoly_eq_sum']
  simp [SoS.Poly.termPoly, unitExp_toFinsupp v i e hi, X_pow_eq_monomial,
    C_mul_monomial]

/-- The finite variable decoder, followed by the natural-index embedding. -/
noncomputable def decode (v : ℕ) (p : RawPoly) : Rounding.NPoly :=
  rename Fin.val (SoS.toReal (p.toPoly v))

theorem decode_constant (v : ℕ) (c : ℚ) : decode v (constant c) = C (c : ℝ) := by
  simp [decode, constant_toPoly, SoS.toReal]

theorem decode_append (v : ℕ) (p q : RawPoly) :
    decode v (p ++ q) = decode v p + decode v q := by
  simp [decode, SoS.Poly.toPoly_append, SoS.toReal_add]

theorem decode_scale (v : ℕ) (c : ℚ) (p : RawPoly) :
    decode v (scale c p) = C (c : ℝ) * decode v p := by
  simp [decode, scale_toPoly, SoS.toReal]

theorem decode_unit (v i e : ℕ) (c : ℚ) (hi : i < v) :
    decode v [(unitExp v i e, c)] = C (c : ℝ) * X i ^ e := by
  simp [decode, unit_toPoly v i e c hi, SoS.toReal]

/-- The raw linear form uses every coordinate once, with zero-padding for short rows. -/
theorem linear_toPoly (d : ℕ) (x : Vector) :
    (linear d x).toPoly d = ∑ i : Fin d, C (x.getD i.val 0) * X i := by
  have h : linear d x = List.ofFn (fun i : Fin d ↦ (unitExp d i.val 1, x.getD i.val 0)) := by
    apply List.ext_getElem (by simp [linear])
    intro i hi hi'
    simp [linear]
  rw [h, SoS.Solver.RawPoly.toPoly, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have ht := unit_toPoly d i.val 1 (x.getD i.val 0) i.isLt
  simpa only [Function.comp_def, SoS.Solver.RawPoly.toPoly, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, pow_one] using ht

/-- The raw squared norm agrees with `Common.nsq`. -/
theorem normSq_toPoly (d : ℕ) : (normSq d).toPoly d = ∑ i : Fin d, X i ^ 2 := by
  have h : normSq d = List.ofFn (fun i : Fin d ↦ (unitExp d i.val 2, (1 : ℚ))) := by
    apply List.ext_getElem (by simp [normSq])
    intro i hi hi'
    simp [normSq]
  rw [h, SoS.Solver.RawPoly.toPoly, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have ht := unit_toPoly d i.val 2 1 i.isLt
  simpa only [Function.comp_def, SoS.Solver.RawPoly.toPoly, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, C_1, one_mul] using ht

/-- Coefficient reading commutes with the rational-to-real map. -/
theorem coeff_real (d : ℕ) (p : RawPoly) (μ : List ℕ) (hμ : μ.length = d) :
    (SoS.Poly.coeff d p μ : ℝ) =
      (SoS.toReal (p.toPoly d)).coeff (SoS.Mono.toFinsupp d μ) := by
  rw [← SoS.Poly.coeff_toPoly p hμ]
  simp [SoS.toReal, coeff_map]

/-- The decoder respects termwise products. -/
theorem decode_mul (v : ℕ) (p q : RawPoly) :
    decode v (SoS.Coords.mulRaw v p q) = decode v p * decode v q := by
  simp [decode, SoS.Coords.toPoly_mulRaw, SoS.toReal]

/-- Two unit exponents give the product of the two indexed unknowns. -/
theorem decode_pair (v i j : ℕ) (hi : i < v) (hj : j < v) :
    decode v [(SoS.Poly.addE v (unitExp v i 1) (unitExp v j 1), 1)] =
      X i * X j := by
  have h := decode_mul v [(unitExp v i 1, 1)] [(unitExp v j 1, 1)]
  rw [decode_unit v i 1 1 hi, decode_unit v j 1 1 hj] at h
  simpa [SoS.Coords.mulRaw] using h

/-- Flattening a raw list program becomes a finite sum under interpretation. -/
theorem decode_flatMap {α : Type} (v : ℕ) (l : List α) (f : α → RawPoly) :
    decode v (l.flatMap f) = ∑ i : Fin l.length, decode v (f l[i]) := by
  induction l with
  | nil => simp [decode, SoS.Solver.RawPoly.toPoly]
  | cons a l ih =>
    simpa only [List.flatMap_cons, List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ, decode_append] using congrArg (decode v (f a) + ·) ih


/-- A zip-indexed list sum can be indexed by its original finite type. -/
theorem sum_zipIdx {α M : Type} [AddCommMonoid M] (l : List α) (f : α × ℕ → M) :
    (l.zipIdx.map f).sum = ∑ a : Fin l.length, f (l[a], a.val) := by
  have h : l.zipIdx.map f =
      List.ofFn (fun a : Fin l.length ↦ f (l[a], a.val)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  rw [h, List.sum_ofFn]

/-- A range sum uses the canonical finite type without transporting its instance. -/
theorem sum_range {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  have h : (List.range n).map f = List.ofFn (fun i : Fin n ↦ f i.val) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  rw [h, List.sum_ofFn]

/-- The list form of decoding a flattened constructor avoids dependent-index transports. -/
theorem decode_flatMap_list {α : Type} (v : ℕ) (l : List α) (f : α → RawPoly) :
    decode v (l.flatMap f) = (l.map fun a ↦ decode v (f a)).sum := by
  induction l with
  | nil => simp [decode, SoS.Solver.RawPoly.toPoly]
  | cons a l ih => simp only [List.flatMap_cons, decode_append, List.map_cons,
      List.sum_cons, ih]

theorem decode_map_list {α : Type} (v : ℕ) (l : List α) (f : α → List ℕ × ℚ) :
    decode v (l.map f) = (l.map fun a ↦ decode v [f a]).sum := by
  induction l with
  | nil => simp [decode, SoS.Solver.RawPoly.toPoly]
  | cons a l ih =>
    change decode v ([(f a)] ++ l.map f) = _
    simp only [decode_append, ih, List.map_cons, List.sum_cons]

/-- Prefix blocks fit within the total allocated variable count. -/
theorem gram_block (n d : ℕ) (J : List ℕ) (a : ℕ) (ha : a < J.length) :
    gramOffset n d J a + (SoS.Mono.all d (J.getD a 0)).length ^ 2 ≤ numVars n d J := by
  let sizes := J.map fun r ↦ (SoS.Mono.all d r).length ^ 2
  have hlen : a < sizes.length := by simpa [sizes] using ha
  have hsplit := List.sum_take_add_sum_drop sizes (a + 1)
  have hstep := List.sum_take_succ sizes a hlen
  simp only [sizes, List.getElem_map] at hstep hsplit
  simp only [gramOffset, numVars, List.take_length]
  rw [List.getD_eq_getElem _ _ ha, List.map_take]
  omega

/-- Every row-major entry of an allocated square block is in range. -/
theorem gram_index (v start m a c : ℕ) (ha : a < m) (hc : c < m)
    (hblock : start + m ^ 2 ≤ v) : start + a * m + c < v := by
  have hh := Nat.mul_le_mul_right m (show a + 1 ≤ m by omega)
  nlinarith

/-- The Gram coefficient loops match the coefficient of the analytic square expansion. -/
theorem gramCoeff_decode (v d start r : ℕ) (μ : List ℕ) (hμ : μ.length = d)
    (hblock : start + (SoS.Mono.all d r).length ^ 2 ≤ v) :
    decode v (gramCoeff v d start r μ) =
      (Rounding.gram start (Rounding.monos d r)).coeff (SoS.Mono.toFinsupp d μ) := by
  let L := SoS.Mono.all d r
  let F := SoS.Mono.toFinsupp d μ
  have hidx (a c : Fin L.length) : start + a.val * L.length + c.val < v :=
    gram_index v start L.length a.val c.val a.isLt c.isLt hblock
  have hcoeff (a b : List ℕ) :
      SoS.Mono.toFinsupp d a + SoS.Mono.toFinsupp d b = F ↔
        SoS.Poly.addE d a b = μ := by
    rw [← SoS.Poly.toFinsupp_addE]
    exact ⟨SoS.Mono.toFinsupp_inj (SoS.Poly.length_addE d a b) hμ,
      congrArg (SoS.Mono.toFinsupp d)⟩
  have hgram : (Rounding.gram start (Rounding.monos d r)).coeff F =
      ∑ a : Fin L.length, ∑ b : Fin L.length,
        if SoS.Poly.addE d L[a] L[b] = μ then
          ∑ c : Fin L.length,
            (X (start + a.val * L.length + c.val) : Rounding.NPoly) *
              X (start + b.val * L.length + c.val) else 0 := by
    let M := Rounding.monos d r
    have hlen : M.length = L.length := by simp [M, L, Rounding.monos]
    have hmono (a : Fin M.length) :
        M[a] = SoS.Mono.toFinsupp d L[(finCongr hlen a).val] := by
      change ((SoS.Mono.all d r).map (SoS.Mono.toFinsupp d))[a.val] = _
      rw [List.getElem_map]
      rfl
    calc
      _ = ∑ c : Fin M.length, ∑ a : Fin M.length, ∑ b : Fin M.length,
          if M[a] + M[b] = F then
            (X (start + a.val * M.length + c.val) : Rounding.NPoly) *
              X (start + b.val * M.length + c.val) else 0 := by
        simp only [Rounding.gram, pow_two, Finset.sum_mul_sum, coeff_sum,
          C_mul_monomial, monomial_mul_monomial, mul_one, coeff_monomial]
        rfl
      _ = ∑ c : Fin L.length, ∑ a : Fin L.length, ∑ b : Fin L.length,
          if SoS.Poly.addE d L[a] L[b] = μ then
            (X (start + a.val * L.length + c.val) : Rounding.NPoly) *
              X (start + b.val * L.length + c.val) else 0 := by
        apply Fintype.sum_equiv (finCongr hlen)
        intro c
        apply Fintype.sum_equiv (finCongr hlen)
        intro a
        apply Fintype.sum_equiv (finCongr hlen)
        intro b
        simp only [hmono, hlen, Fin.getElem_fin, finCongr_apply_coe, hcoeff]
        rfl
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp
  rw [hgram]
  unfold gramCoeff
  change decode v (L.zipIdx.flatMap _) = _
  rw [decode_flatMap_list, sum_zipIdx]
  apply Finset.sum_congr rfl
  intro a _
  rw [decode_flatMap_list, sum_zipIdx]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with he
  · rw [decode_map_list, sum_range]
    apply Finset.sum_congr rfl
    intro c _
    exact decode_pair v _ _ (hidx a c) (hidx b c)
  · simp [decode, SoS.Solver.RawPoly.toPoly]

/-- One raw coefficient equation decodes to the corresponding template coefficient. -/
theorem coefficient_decode (d : ℕ) (pts : Points) (J : List ℕ) (w : ℚ)
    (a : Fin J.length) (μ : List ℕ) (hμ : μ.length = d) :
    decode (numVars pts.length d J) (coefficient d pts J w a.val μ) =
      (momentTemplate (realPoints d pts) J (fun r ↦ (budget w r : ℝ)) a).coeff
        (SoS.Mono.toFinsupp d μ) := by
  let v := numVars pts.length d J
  let r := J[a.val]
  let F := SoS.Mono.toFinsupp d μ
  have hn : pts.length ≤ v := by dsimp [v, numVars, gramOffset]; omega
  have hnorm : SoS.toReal ((power d (normSq d) r).toPoly d) = (nsq : RPoly d) ^ r := by
    simp [power_toPoly, normSq_toPoly, SoS.toReal, nsq]
  have hlin (i : Fin pts.length) :
      SoS.toReal ((power d (linear d pts[i]) (2 * r)).toPoly d) =
        lin (realPoints d pts i) ^ (2 * r) := by
    simp [power_toPoly, linear_toPoly, SoS.toReal, lin, realPoints]
  have hdata : decode v (pts.zipIdx.map fun p ↦
      (unitExp v p.2 1, -SoS.Poly.coeff d (power d (linear d p.1) (2 * r)) μ)) =
      -(∑ i : Fin pts.length, X i.val *
        C ((lin (realPoints d pts i) ^ (2 * r)).coeff F)) := by
    rw [decode_map_list, sum_zipIdx]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_unit v i.val 1 _ (i.isLt.trans_le hn)]
    rw [Rat.cast_neg, coeff_real d _ μ hμ, hlin i]
    simp [F, mul_comm]
  have hg := gramCoeff_decode v d (gramOffset pts.length d J a.val) r μ hμ
    (by simpa only [r, v, List.getD_eq_getElem _ _ a.isLt] using
      gram_block pts.length d J a.val a.isLt)
  dsimp only [v, r, F] at hdata hg hnorm
  unfold coefficient
  rw [List.getD_eq_getElem _ _ a.isLt]
  rw [decode_append, decode_append, decode_constant, hdata, decode_scale, hg]
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_natCast, coeff_real d _ μ hμ, hnorm]
  simp only [Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul]
  simp only [momentTemplate, coeff_sub, coeff_sum, coeff_C_mul,
    Rounding.embedCoeff, coeff_map, map_mul]
  simp only [map_C, Fin.getElem_fin, gramOffset_agrees]
  simp only [mul_assoc, coeff_C_mul, coeff_map]
  ring

/-- Flattened programs agree if their branches agree on the enumerated list. -/
theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp)]
    rw [ih (fun b hb ↦ h b (by simp [hb]))]

/-- Mapping a program indexed by naturals gives the same order as `finRange`. -/
theorem map_flatMap_range {α β : Type} (n : ℕ) (f : ℕ → List α) (g : α → β) :
    ((List.range n).flatMap f).map g =
      (List.finRange n).flatMap (fun i ↦ (f i.val).map g) := by
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map, List.map_flatMap]

/-- The first raw constraint is exactly the explicit Euclidean ball. -/
theorem ball_decode (v : ℕ) (b : ℚ) :
    decode v (constant b ++ (List.range v).map (fun i ↦ (unitExp v i 2, -1))) =
      C (b : ℝ) - ∑ i ∈ Finset.range v, X i ^ 2 := by
  rw [decode_append, decode_constant, decode_map_list, sum_range]
  have h : (∑ i : Fin v, decode v [(unitExp v i.val 2, -1)]) =
      -∑ i : Fin v, (X i.val : Rounding.NPoly) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_unit v i.val 2 (-1) i.isLt]
    simp
  rw [h, Fin.sum_univ_eq_sum_range (fun i ↦ (X i : Rounding.NPoly) ^ 2) v]
  simp only [sub_eq_add_neg]

/-- The mass constraint sums precisely the weight variables before subtracting its threshold. -/
theorem mass_decode (n v : ℕ) (ε : ℚ) (hn : n ≤ v) :
    decode v ((List.range n).map (fun i ↦ (unitExp v i 1, 1)) ++
      constant (-((1 - ε) * n))) =
      (∑ i : Fin n, X i.val) - C ((1 - (ε : ℝ)) * n) := by
  rw [decode_append, decode_map_list, sum_range, decode_constant]
  have h : (∑ i : Fin n, decode v [(unitExp v i.val 1, 1)]) =
      ∑ i : Fin n, (X i.val : Rounding.NPoly) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [decode_unit v i.val 1 1 (i.isLt.trans_le hn)]
    simp
  rw [h]
  simp [sub_eq_add_neg]

/-- Reification matches every constraint, including the exact offsets and both equality signs. -/
theorem constraints_reify (d : ℕ) (pts : Points) (J : List ℕ) (w ε ball : ℚ) :
    (constraints d pts J w ε ball).map
      (fun p ↦ rename Fin.val (SoS.toReal (p.toPoly (numVars pts.length d J)))) =
    momentConstraints (realPoints d pts) J (fun r ↦ (budget w r : ℝ)) ε ball := by
  let v := numVars pts.length d J
  have hn : pts.length ≤ v := by dsimp [v, numVars, gramOffset]; omega
  have hweights :
      ((List.range pts.length).flatMap (fun i ↦
        [[(unitExp v i 1, (1 : ℚ))], constant 1 ++ [(unitExp v i 1, -1)]])).map
          (decode v) =
      (List.finRange pts.length).flatMap (fun i ↦
        [(X i.val : Rounding.NPoly), 1 - X i.val]) := by
    rw [map_flatMap_range]
    apply flatMap_congr_mem
    intro i _
    simp only [List.map_cons, List.map_nil, decode_append, decode_constant]
    rw [decode_unit v i.val 1 1 (i.isLt.trans_le hn),
      decode_unit v i.val 1 (-1) (i.isLt.trans_le hn)]
    simp [sub_eq_add_neg]
  have hcoeffs :
      ((List.range J.length).flatMap (fun a ↦
        (SoS.Mono.all d (2 * J.getD a 0)).flatMap fun μ ↦
          let c := coefficient d pts J w a μ
          [c, scale (-1) c])).map (decode v) =
      (List.finRange J.length).flatMap (fun a ↦
        (Rounding.monos d (2 * J[a])).flatMap fun μ ↦
          let c := (momentTemplate (realPoints d pts) J (fun r ↦ (budget w r : ℝ)) a).coeff μ
          [c, -c]) := by
    rw [map_flatMap_range]
    apply flatMap_congr_mem
    intro a _
    rw [List.getD_eq_getElem _ _ a.isLt]
    simp only [Rounding.monos, List.flatMap_map, List.map_flatMap]
    apply flatMap_congr_mem
    intro μ hμ
    have h := coefficient_decode d pts J w a μ (SoS.Mono.mem_all.mp hμ).1
    simp only [List.map_cons, List.map_nil, decode_scale, Rat.cast_neg, Rat.cast_one,
      C_neg, C_1, neg_one_mul]
    rw [h]
    rfl
  change (constraints d pts J w ε ball).map (decode v) = _
  simp only [constraints, List.map_append, List.map_cons, List.map_nil]
  rw [ball_decode, hweights, mass_decode _ _ ε hn, hcoeffs]
  rw [show v = momentVars pts.length d J by
    simp only [v, numVars, momentVars, gramOffset_agrees]]
  rfl

/-- The exact number of constraints counts both signs of every coefficient equation. -/
theorem constraints_length (d : ℕ) (pts : Points) (J : List ℕ) (w ε b : ℚ) :
    (constraints d pts J w ε b).length =
      2 + 2 * pts.length + 2 * (J.map fun r ↦ (SoS.Mono.all d (2 * r)).length).sum := by
  have hsum : ((List.range J.length).map fun a ↦
      2 * (SoS.Mono.all d (2 * J.getD a 0)).length).sum =
      2 * (J.map fun r ↦ (SoS.Mono.all d (2 * r)).length).sum := by
    rw [sum_range, SoS.Coords.sum_map_getElem, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [List.getD_eq_getElem _ _ a.isLt]
    rfl
  simp only [constraints, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  simp only [Nat.reduceAdd, List.length_range]
  simp_rw [Nat.mul_comm _ 2]
  rw [hsum]
  omega

private theorem maxDegree_polytime : ComputableInPolyTime maxDegree encIndices encNat :=
  MomentExpansion.maximum_polytime

private theorem dimension_polytime : ComputableInPolyTime dimension encMomentArgs encUnary :=
  (length_list encRat).comp ((headD (encL := encList encVector) []).comp (fst _ _))

private theorem orders_polytime : ComputableInPolyTime orders encMomentArgs encIndices :=
  (fst _ _).comp ((snd _ _).comp (snd _ _))

private theorem cappedMax_polytime : ComputableInPolyTime
    (fun q : MomentInput ↦ min q.2 (maxDegree (orders q.1))) encMomentInput encUnary :=
  binary_min_unary' (snd _ _)
    ((maxDegree_polytime.comp orders_polytime).comp (fst _ _))

private theorem enabled_polytime : ComputableInPolyTime enabled encMomentInput encBool := by
  have hmax := (maxDegree_polytime.comp orders_polytime).comp (fst _ encUnary)
  have hdim := dimension_polytime.comp (fst _ encUnary)
  have hpow := binary_pow'
    (unary_to_binary.comp (unary_add' hdim (const 2)))
    (unary_mul' (const 6) (unary_add' cappedMax_polytime (const 1)))
  have h := ite_decide (binary_le' hmax (unary_to_binary.comp (snd _ _)))
    (binary_le' hpow (unary_to_binary.comp (snd _ _))) (const false)
  exact h.of_enc_eq fun q ↦ by
    by_cases hq : maxDegree (orders q.1) ≤ q.2
    · simp only [Function.comp_apply, min_eq_right hq, enabled, ite_eq_left hq,
        expansionBound]
      rfl
    · simp [enabled, hq]

private theorem blockPoints_polytime : ComputableInPolyTime blockPoints
    encMomentArgs encPoints := by
  have hz : ComputableInPolyTime (fun a : MomentArgs ↦ a.1.zipIdx)
      encMomentArgs (encList (encPair encVector encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx encVector).comp (fst _ _).tidy)
  have hf : ComputableInPolyTime
      (fun a : MomentArgs ↦ a.1.zipIdx.filter fun p ↦ p.2 ∈ a.2.1)
      encMomentArgs (encList (encPair encVector encUnary)) := by
    apply filterWithInput hz
    exact decide_mem (((fst _ _).comp (snd _ _)).comp (fst _ _))
      (unary_to_binary.comp ((snd _ _).comp (snd _ _)))
  exact mapWithInput hf ((fst _ _).comp (snd _ _))

@[fun_prop] private theorem unitExp_polytime {α : Type} {input : α ↪ List Bool}
    {v i e : α → ℕ} (hv : ComputableInPolyTime v input encUnary)
    (hi : ComputableInPolyTime i input encUnary)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a ↦ unitExp (v a) (i a) (e a))
      input (encList encNat) := by
  unfold unitExp
  apply mapWithInput (range.comp hv)
  exact ite_decide (.of_tidy (ComputableTidilyInPolyTime.decide_eq'
    (snd _ _).tidy (hi.comp (fst _ _)).tidy))
    (he.comp (fst _ _)) (const 0)

@[fun_prop] private theorem constant_polytime {α : Type} {input : α ↪ List Bool}
    {c : α → ℚ} (hc : ComputableInPolyTime c input encRat) :
    ComputableInPolyTime (fun a ↦ constant (c a)) input SoS.Solver.encRawPoly := by
  unfold constant
  fun_prop

@[fun_prop] private theorem scale_polytime {α : Type} {input : α ↪ List Bool}
    {c : α → ℚ} {p : α → RawPoly} (hc : ComputableInPolyTime c input encRat)
    (hp : ComputableInPolyTime p input SoS.Solver.encRawPoly) :
    ComputableInPolyTime (fun a ↦ scale (c a) (p a)) input SoS.Solver.encRawPoly := by
  unfold scale
  apply mapWithInput hp
  exact ((fst _ _).comp (snd _ _)).prod
    (rat_mul' (hc.comp (fst _ _)) ((snd _ _).comp (snd _ _)))

@[fun_prop] private theorem linear_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {x : α → Vector} (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime x input encVector) :
    ComputableInPolyTime (fun a ↦ linear (d a) (x a)) input SoS.Solver.encRawPoly := by
  unfold linear
  apply mapWithInput (range.comp hd)
  exact (unitExp_polytime (hd.comp (fst _ _)) (snd _ _) (const 1)).prod
    (listGetDWithInput (hx.comp (fst _ _)) (snd _ _) 0)

@[fun_prop] private theorem normSq_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} (hd : ComputableInPolyTime d input encUnary) :
    ComputableInPolyTime (fun a ↦ normSq (d a)) input SoS.Solver.encRawPoly := by
  unfold normSq
  apply mapWithInput (range.comp hd)
  exact (unitExp_polytime (hd.comp (fst _ _)) (snd _ _) (const 2)).prod (const 1)

@[fun_prop] private theorem powerB_polytime {α : Type} {input : α ↪ List Bool}
    {L d r : α → ℕ} {p : α → RawPoly}
    (hL : ComputableInPolyTime L input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input SoS.Solver.encRawPoly)
    (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a ↦ MomentExpansion.powerB (L a) (d a) (p a) (r a))
      input SoS.Solver.encRawPoly :=
  MomentExpansion.powerB_polytime.comp (hL.prod (hd.prod (hp.prod hr)))

@[fun_prop] private theorem allB_polytime {α : Type} {input : α ↪ List Bool}
    {L d r : α → ℕ} (hL : ComputableInPolyTime L input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a ↦ SoS.Mono.allB (L a) (d a) (r a))
      input (encList (encList encNat)) :=
  MomentExpansion.allB_polytime.comp (hL.prod (hd.prod hr))

private def gramOffsetB (L n d : ℕ) (J : List ℕ) (a : ℕ) : ℕ :=
  n + ((J.take a).map fun r ↦ (SoS.Mono.allB L d r).length ^ 2).sum

@[fun_prop] private theorem gramOffsetB_polytime {α : Type} {input : α ↪ List Bool}
    {L n d a : α → ℕ} {J : α → List ℕ}
    (hL : ComputableInPolyTime L input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hJ : ComputableInPolyTime J input (encList encUnary))
    (ha : ComputableInPolyTime a input encUnary) :
    ComputableInPolyTime (fun x ↦ gramOffsetB (L x) (n x) (d x) (J x) (a x))
      input encUnary := by
  unfold gramOffsetB
  apply unary_add' hn
  apply MomentExpansion.unary_sum.comp
  apply mapWithInput (.of_tidy
    (ComputableTidilyInPolyTime.listTakeWithInput hJ.tidy ha.tidy))
  exact (unary_pow 2).comp ((length_list (encList encNat)).comp
    (allB_polytime (hL.comp (fst _ _)) (hd.comp (fst _ _)) (snd _ _)))

private def gramCoeffB (L v d start r : ℕ) (μ : List ℕ) : RawPoly :=
  let M := SoS.Mono.allB L d r
  M.zipIdx.flatMap fun a ↦ M.zipIdx.flatMap fun b ↦
    if SoS.Poly.addE d a.1 b.1 = μ then
      (List.range M.length).map fun c ↦
        (SoS.Poly.addE v (unitExp v (start + a.2 * M.length + c) 1)
          (unitExp v (start + b.2 * M.length + c) 1), 1)
    else []

private theorem gramProducts_polytime {α : Type} {input : α ↪ List Bool}
    {v start m a b : α → ℕ} (hv : ComputableInPolyTime v input encUnary)
    (hs : ComputableInPolyTime start input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (ha : ComputableInPolyTime a input encUnary)
    (hb : ComputableInPolyTime b input encUnary) :
    ComputableInPolyTime (fun x ↦ (List.range (m x)).map fun c ↦
      (SoS.Poly.addE (v x) (unitExp (v x) (start x + a x * m x + c) 1)
        (unitExp (v x) (start x + b x * m x + c) 1), (1 : ℚ)))
      input SoS.Solver.encRawPoly := by
  apply mapWithInput (range.comp hm)
  have hbase := fst input encUnary
  have hi := unary_add'
    (unary_add' (hs.comp hbase) (unary_mul' (ha.comp hbase) (hm.comp hbase))) (snd _ _)
  have hj := unary_add'
    (unary_add' (hs.comp hbase) (unary_mul' (hb.comp hbase) (hm.comp hbase))) (snd _ _)
  exact (SoS.Poly.addE' (hv.comp hbase)
    (unitExp_polytime (hv.comp hbase) hi (const 1))
    (unitExp_polytime (hv.comp hbase) hj (const 1))).prod (const 1)

@[fun_prop] private theorem gramCoeffB_polytime {α : Type} {input : α ↪ List Bool}
    {L v d start r : α → ℕ} {μ : α → List ℕ}
    (hL : ComputableInPolyTime L input encUnary)
    (hv : ComputableInPolyTime v input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hs : ComputableInPolyTime start input encUnary)
    (hr : ComputableInPolyTime r input encUnary)
    (hμ : ComputableInPolyTime μ input (encList encNat)) :
    ComputableInPolyTime (fun x ↦ gramCoeffB (L x) (v x) (d x) (start x) (r x) (μ x))
      input SoS.Solver.encRawPoly := by
  have hm := allB_polytime hL hd hr
  have hlen := (length_list (encList encNat)).comp hm
  have hz := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.zipIdx (encList encNat)).comp hm.tidy)
  unfold gramCoeffB
  apply flatMapWithInput hz
  apply flatMapWithInput (hz.comp (fst _ _))
  have hbase := (fst input (encPair (encList encNat) encUnary)).comp
    (fst _ (encPair (encList encNat) encUnary))
  apply ite_decide
  · exact .of_tidy (ComputableTidilyInPolyTime.decide_eq'
      (SoS.Poly.addE' (hd.comp hbase)
        (((fst _ _).comp (snd _ _)).comp (fst _ _))
        ((fst _ _).comp (snd _ _))).tidy (hμ.comp hbase).tidy)
  · exact gramProducts_polytime (hv.comp hbase) (hs.comp hbase) (hlen.comp hbase)
      (((snd _ _).comp (snd _ _)).comp (fst _ _)) ((snd _ _).comp (snd _ _))
  · exact const []

private def coefficientB (L d : ℕ) (pts : Points) (J : List ℕ) (w : ℚ)
    (a : ℕ) (μ : List ℕ) : RawPoly :=
  let r := J.getD a 0
  let v := gramOffsetB L pts.length d J J.length
  constant (budget w r * pts.length *
    SoS.Poly.coeff d (MomentExpansion.powerB L d (normSq d) r) μ) ++
    (pts.zipIdx.map fun p ↦
      (unitExp v p.2 1, -SoS.Poly.coeff d
        (MomentExpansion.powerB L d (linear d p.1) (2 * r)) μ)) ++
    scale (-1) (gramCoeffB L v d (gramOffsetB L pts.length d J a) r μ)

@[fun_prop] private theorem coefficientB_polytime {α : Type} {input : α ↪ List Bool}
    {L d a : α → ℕ} {pts : α → Points} {J : α → List ℕ} {w : α → ℚ}
    {μ : α → List ℕ} (hL : ComputableInPolyTime L input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input (encList encVector))
    (hJ : ComputableInPolyTime J input (encList encUnary))
    (hw : ComputableInPolyTime w input encRat)
    (ha : ComputableInPolyTime a input encUnary)
    (hμ : ComputableInPolyTime μ input (encList encNat)) :
    ComputableInPolyTime (fun x ↦ coefficientB (L x) (d x) (pts x) (J x) (w x) (a x) (μ x))
      input SoS.Solver.encRawPoly := by
  have hr := listGetDWithInput hJ ha 0
  have hn := (length_list encVector).comp hx
  have hv := gramOffsetB_polytime hL hn hd hJ ((length_list encUnary).comp hJ)
  have hb : ComputableInPolyTime (fun x ↦ budget (w x) ((J x).getD (a x) 0))
      input encRat := rat_mul' (const 4) (MomentExpansion.rat_pow'
        (rat_div' (rat_mul' (const 20) (rat_natCast' (unary_to_binary.comp hr))) hw) hr)
  unfold coefficientB
  apply listAppend'
  · apply listAppend'
    · exact constant_polytime (rat_mul' (rat_mul' hb
        (rat_natCast' (unary_to_binary.comp hn)))
        (SoS.Poly.coeff' hd (powerB_polytime hL hd (normSq_polytime hd) hr) hμ))
    · have hz := ComputableInPolyTime.of_tidy
        ((ComputableTidilyInPolyTime.zipIdx encVector).comp hx.tidy)
      apply mapWithInput hz
      have hbase := fst input (encPair encVector encUnary)
      exact (unitExp_polytime (hv.comp hbase) ((snd _ _).comp (snd _ _)) (const 1)).prod
        (rat_neg' (SoS.Poly.coeff' (hd.comp hbase)
          (powerB_polytime (hL.comp hbase) (hd.comp hbase)
            (linear_polytime (hd.comp hbase) ((fst _ _).comp (snd _ _)))
            (unary_mul' (const 2) (hr.comp hbase))) (hμ.comp hbase)))
  · exact scale_polytime (const (-1)) (gramCoeffB_polytime hL hv hd
      (gramOffsetB_polytime hL hn hd hJ ha) hr hμ)

private def constraintsB (L d : ℕ) (pts : Points) (J : List ℕ)
    (w ε ball : ℚ) : List RawPoly :=
  let v := gramOffsetB L pts.length d J J.length
  [constant ball ++ (List.range v).map (fun i ↦ (unitExp v i 2, -1))] ++
    (List.range pts.length).flatMap (fun i ↦
      [[(unitExp v i 1, 1)], constant 1 ++ [(unitExp v i 1, -1)]]) ++
    [(List.range pts.length).map (fun i ↦ (unitExp v i 1, 1)) ++
      constant (-((1 - ε) * pts.length))] ++
    (List.range J.length).flatMap (fun a ↦
      (SoS.Mono.allB L d (2 * J.getD a 0)).flatMap fun μ ↦
        let c := coefficientB L d pts J w a μ
        [c, scale (-1) c])

private theorem constraintsB_polytime {α : Type} {input : α ↪ List Bool}
    {L d : α → ℕ} {pts : α → Points} {J : α → List ℕ} {w ε b : α → ℚ}
    (hL : ComputableInPolyTime L input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input (encList encVector))
    (hJ : ComputableInPolyTime J input (encList encUnary))
    (hw : ComputableInPolyTime w input encRat)
    (he : ComputableInPolyTime ε input encRat)
    (hb : ComputableInPolyTime b input encRat) :
    ComputableInPolyTime (fun x ↦ constraintsB (L x) (d x) (pts x) (J x) (w x) (ε x) (b x))
      input (encList SoS.Solver.encRawPoly) := by
  have hn := (length_list encVector).comp hx
  have hj := (length_list encUnary).comp hJ
  have hv := gramOffsetB_polytime hL hn hd hJ hj
  have hball : ComputableInPolyTime
      (fun x ↦ constant (b x) ++ (List.range (gramOffsetB (L x)
        (pts x).length (d x) (J x) (J x).length)).map
          (fun i ↦ (unitExp (gramOffsetB (L x) (pts x).length (d x) (J x)
            (J x).length) i 2, (-1 : ℚ)))) input SoS.Solver.encRawPoly := by
    apply listAppend' (constant_polytime hb)
    apply mapWithInput (range.comp hv)
    exact (unitExp_polytime (hv.comp (fst _ _)) (snd _ _) (const 2)).prod (const (-1))
  have hweights : ComputableInPolyTime (fun x ↦ (List.range (pts x).length).flatMap
      fun i ↦ [[(unitExp (gramOffsetB (L x) (pts x).length (d x) (J x)
        (J x).length) i 1, (1 : ℚ))], constant 1 ++
          [(unitExp (gramOffsetB (L x) (pts x).length (d x) (J x)
            (J x).length) i 1, (-1 : ℚ))]]) input (encList SoS.Solver.encRawPoly) := by
    apply flatMapWithInput (range.comp hn)
    have hu := unitExp_polytime (hv.comp (fst _ _)) (snd _ _) (const 1)
    exact cons' (cons' (hu.prod (const 1)) (const []))
      (cons' (listAppend' (constant_polytime (const 1))
        (cons' (hu.prod (const (-1))) (const []))) (const []))
  have hmass : ComputableInPolyTime (fun x ↦
      (List.range (pts x).length).map (fun i ↦
        (unitExp (gramOffsetB (L x) (pts x).length (d x) (J x) (J x).length) i 1,
          (1 : ℚ))) ++ constant (-((1 - ε x) * (pts x).length)))
      input SoS.Solver.encRawPoly := by
    apply listAppend'
    · apply mapWithInput (range.comp hn)
      exact (unitExp_polytime (hv.comp (fst _ _)) (snd _ _) (const 1)).prod (const 1)
    · exact constant_polytime (rat_neg'
        (rat_mul' (rat_sub' (const 1) he) (rat_natCast' (unary_to_binary.comp hn))))
  have hcoeffs : ComputableInPolyTime (fun x ↦ (List.range (J x).length).flatMap
      fun a ↦ (SoS.Mono.allB (L x) (d x) (2 * (J x).getD a 0)).flatMap fun μ ↦
        let c := coefficientB (L x) (d x) (pts x) (J x) (w x) a μ
        [c, scale (-1) c]) input (encList SoS.Solver.encRawPoly) := by
    apply flatMapWithInput (range.comp hj)
    have hbase := fst input encUnary
    have hr := listGetDWithInput (hJ.comp hbase) (snd _ _) 0
    apply flatMapWithInput
      (allB_polytime (hL.comp hbase) (hd.comp hbase) (unary_mul' (const 2) hr))
    have hbase' := hbase.comp (fst _ (encList encNat))
    have hc := coefficientB_polytime (hL.comp hbase') (hd.comp hbase')
      (hx.comp hbase') (hJ.comp hbase') (hw.comp hbase')
      ((snd _ _).comp (fst _ _)) (snd _ _)
    exact cons' hc (cons' (scale_polytime (const (-1)) hc) (const []))
  exact listAppend' (listAppend' (listAppend' (cons' hball (const [])) hweights)
    (cons' hmass (const []))) hcoeffs

private def cappedOrders (q : MomentInput) : List ℕ :=
  (orders q.1).map (min q.2)

private theorem cappedOrders_polytime : ComputableInPolyTime cappedOrders
    encMomentInput (encList encUnary) := by
  apply mapWithInput (orders_polytime.comp (fst _ _))
  exact binary_min_unary' ((snd _ _).comp (fst _ _)) (snd _ _)

private def ballB (q : MomentInput) : ℚ :=
  2 ^ (((encMomentArgs q.1).length + 2) ^ 4 *
    (min q.2 (maxDegree (orders q.1)) + 1) ^ 4)

private theorem wInput_polytime : ComputableInPolyTime
    (fun q : MomentInput ↦ q.1.2.2.2.1) encMomentInput encRat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _))))

private theorem epsInput_polytime : ComputableInPolyTime
    (fun q : MomentInput ↦ q.1.2.2.2.2) encMomentInput encRat :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (fst _ _))))

private theorem ballB_polytime : ComputableInPolyTime ballB encMomentInput encRat := by
  have hlen : ComputableInPolyTime (fun q : MomentInput ↦ (encMomentArgs q.1).length)
      encMomentInput encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.encoding_length encMomentArgs).comp (fst _ _).tidy)
  exact rat_two_pow' (unary_mul'
    ((unary_pow 4).comp (unary_add' hlen (const 2)))
    ((unary_pow 4).comp (unary_add' cappedMax_polytime (const 1))))

private def problemB (q : MomentInput) : Problem :=
  let a := q.1
  let pts := blockPoints a
  let d := dimension a
  let J := cappedOrders q
  (gramOffsetB q.2 pts.length d J J.length, 2,
    constraintsB q.2 d pts J a.2.2.2.1 a.2.2.2.2 (ballB q), [], [])

private theorem varsB_polytime : ComputableInPolyTime
    (fun q : MomentInput ↦ gramOffsetB q.2 (blockPoints q.1).length
      (dimension q.1) (cappedOrders q) (cappedOrders q).length) encMomentInput encUnary := by
  have hL := snd encMomentArgs encUnary
  have hx := blockPoints_polytime.comp (fst _ encUnary)
  have hd := dimension_polytime.comp (fst _ encUnary)
  have hn := (length_list encVector).comp hx
  have hJ := cappedOrders_polytime
  exact gramOffsetB_polytime hL hn hd hJ ((length_list encUnary).comp hJ)

private theorem inputConstraintsB_polytime : ComputableInPolyTime
    (fun q : MomentInput ↦ constraintsB q.2 (dimension q.1) (blockPoints q.1)
      (cappedOrders q) q.1.2.2.2.1 q.1.2.2.2.2 (ballB q))
    encMomentInput (encList SoS.Solver.encRawPoly) :=
  constraintsB_polytime (snd _ _) (dimension_polytime.comp (fst _ _))
    (blockPoints_polytime.comp (fst _ _)) cappedOrders_polytime
    wInput_polytime epsInput_polytime ballB_polytime

private theorem problemB_polytime : ComputableInPolyTime problemB
    encMomentInput SoS.Solver.encProblem := by
  have hobj : ComputableInPolyTime (fun _ : MomentInput ↦ (([] : RawPoly), ([] : List RawPoly)))
      encMomentInput (encPair SoS.Solver.encRawPoly (encList SoS.Solver.encRawPoly)) :=
    (const []).prod (const [])
  exact (unary_to_binary.comp varsB_polytime).prod ((const 2).prod
    (inputConstraintsB_polytime.prod hobj))

private theorem le_maxDegree {r : ℕ} {J : List ℕ} (hr : r ∈ J) : r ≤ maxDegree J := by
  induction J with
  | nil => simp at hr
  | cons s J ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_max_left _ _
    · exact (ih hr).trans (le_max_right _ _)

private theorem getD_le_maxDegree (J : List ℕ) (a : ℕ) : J.getD a 0 ≤ maxDegree J := by
  by_cases ha : a < J.length
  · rw [List.getD_eq_getElem _ _ ha]
    exact le_maxDegree (List.getElem_mem ha)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

private theorem allB_eq_of_bound {L d R s : ℕ}
    (hL : (d + 2) ^ (6 * (R + 1)) ≤ L) (hs : s ≤ 2 * R) :
    SoS.Mono.allB L d s = SoS.Mono.all d s := by
  have hpow : (d + 1) ^ s ≤ L := by
    calc
      _ ≤ (d + 2) ^ s := Nat.pow_le_pow_left (by omega) _
      _ ≤ (d + 2) ^ (6 * (R + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := hL
  apply SoS.Mono.allB_eq _ hpow
  calc
    s ≤ 2 ^ s := (Nat.lt_two_pow_self).le
    _ ≤ (d + 2) ^ s := Nat.pow_le_pow_left (by omega) _
    _ ≤ (d + 2) ^ (6 * (R + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := hL

private theorem powerB_eq_of_bound {L d R s : ℕ} (p : RawPoly)
    (hL : (d + 2) ^ (6 * (R + 1)) ≤ L) (hs : s ≤ 2 * R) (hp : p.length ≤ d) :
    MomentExpansion.powerB L d p s = power d p s := by
  apply MomentExpansion.powerB_eq
  calc
    (max 1 p.length) ^ s ≤ (d + 2) ^ s := Nat.pow_le_pow_left (by omega) _
    _ ≤ (d + 2) ^ (6 * (R + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ L + 1 := by omega

private theorem gramOffsetB_eq {L n d : ℕ} (J : List ℕ) (a : ℕ)
    (hL : (d + 2) ^ (6 * (maxDegree J + 1)) ≤ L) :
    gramOffsetB L n d J a = gramOffset n d J a := by
  unfold gramOffsetB gramOffset
  congr 2
  apply List.map_congr_left
  intro r hr
  rw [allB_eq_of_bound hL (by
    have := le_maxDegree (List.mem_of_mem_take hr)
    omega)]

private theorem coefficientB_eq {L d : ℕ} (pts : Points) (J : List ℕ) (w : ℚ)
    (a : ℕ) (μ : List ℕ) (hL : (d + 2) ^ (6 * (maxDegree J + 1)) ≤ L) :
    coefficientB L d pts J w a μ = coefficient d pts J w a μ := by
  have hr := getD_le_maxDegree J a
  have hnorm := powerB_eq_of_bound (normSq d) hL (by omega : J.getD a 0 ≤ 2 * maxDegree J)
    (by simp [normSq])
  have hlin (p : Vector) := powerB_eq_of_bound (linear d p) hL
    (by omega : 2 * J.getD a 0 ≤ 2 * maxDegree J) (by simp [linear])
  simp only [coefficientB, coefficient, gramOffsetB_eq J _ hL, hnorm, hlin,
    gramCoeffB, allB_eq_of_bound hL (by omega : J.getD a 0 ≤ 2 * maxDegree J),
    gramCoeff, numVars]

private theorem constraintsB_eq {L d : ℕ} (pts : Points) (J : List ℕ) (w ε b : ℚ)
    (hL : (d + 2) ^ (6 * (maxDegree J + 1)) ≤ L) :
    constraintsB L d pts J w ε b = constraints d pts J w ε b := by
  simp only [constraintsB, constraints, gramOffsetB_eq J _ hL, numVars]
  congr 1
  apply flatMap_congr_mem
  intro a _
  rw [allB_eq_of_bound hL (Nat.mul_le_mul_left 2 (getD_le_maxDegree J a))]
  apply flatMap_congr_mem
  intro μ _
  rw [coefficientB_eq pts J w a μ hL]

private theorem problemB_eq (q : MomentInput) (hen : enabled q = true) :
    problemB q = problem q.1 := by
  have hm : maxDegree (orders q.1) ≤ q.2 := by
    by_contra hm
    simp [enabled, hm] at hen
  have hL : expansionBound q.1 ≤ q.2 := by simpa [enabled, hm] using hen
  have hJ : cappedOrders q = orders q.1 := by
    unfold cappedOrders
    calc
      (orders q.1).map (min q.2) = (orders q.1).map id := by
        apply List.map_congr_left
        intro r hr
        exact min_eq_right ((le_maxDegree hr).trans hm)
      _ = _ := List.map_id _
  simp only [problemB, problem, ballB, hJ, min_eq_right hm, constraintsB_eq _ _ _ _ _ hL,
    gramOffsetB_eq _ _ hL, numVars, ball]

private theorem guardedProblem_polytime_aux : ComputableInPolyTime guardedProblem
    encMomentInput SoS.Solver.encProblem := by
  have h := ite' enabled_polytime problemB_polytime (const fallback)
  exact h.of_enc_eq fun q ↦ by
    by_cases hen : enabled q = true
    · simp [hen, guardedProblem, problemB_eq q hen]
    · simp [hen, guardedProblem]


/-- A machine certificate for the guarded constructor, on arbitrary (including junk) inputs. -/
theorem guarded_problem_polytime : ComputableInPolyTime guardedProblem encMomentInput
    SoS.Solver.encProblem := by
  exact guardedProblem_polytime_aux

/-- Encoding lengths, dyadic accuracies and the cubic unary budget compose in polynomial time. -/
theorem prepare_polytime : ComputableInPolyTime prepare encMomentInput
    (encPair SoS.Solver.encInput encUnary) := by
  have hP := guarded_problem_polytime
  have hlen : ComputableInPolyTime
      (fun q ↦ (SoS.Solver.encProblem (guardedProblem q)).length)
      encMomentInput encUnary :=
    (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.encoding_length SoS.Solver.encProblem)).comp hP
  have ha : ComputableInPolyTime (fun q : MomentInput ↦ (encMomentArgs q.1).length)
      encMomentInput encUnary :=
    (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.encoding_length encMomentArgs)).comp (fst _ _)
  have hp : ComputableInPolyTime precision encMomentInput encUnary :=
    (unary_pow 2).comp (unary_add' (unary_add' hlen ha) (const 2))
  have hacc : ComputableInPolyTime accuracy encMomentInput encRat :=
    rat_div' (const 1) (rat_two_pow' hp)
  exact (hP.prod (hacc.prod hacc)).prod
    ((unary_pow 3).comp (unary_add' hlen (const 2)))

private theorem blockPoints_reindex {n d : ℕ} (x : Fin n → Fin d → ℚ)
    (N : Finset (Fin n)) (J : List ℕ) (w ε : ℚ) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin n),
      blockPoints (pointsOf x, indexList N, J, w, ε) =
        List.ofFn (fun i ↦ List.ofFn (x (e i))) ∧ Finset.univ.image e = N := by
  classical
  let L := (pointsOf x).zipIdx.filter fun p ↦ p.2 ∈ indexList N
  have hmem (i : Fin L.length) : L[i] ∈ (pointsOf x).zipIdx :=
    (List.mem_filter.mp (List.getElem_mem i.isLt)).1
  let f : Fin L.length → Fin n := fun i ↦
    ⟨L[i].2, by simpa [pointsOf] using List.snd_lt_of_mem_zipIdx (hmem i)⟩
  have hrow (i : Fin L.length) : L[i].1 = List.ofFn (x (f i)) := by
    have hh := List.mem_zipIdx_iff_getElem?.mp (hmem i)
    obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hh
    simpa [pointsOf, f] using heq.symm
  have hnd : (L.map Prod.snd).Nodup := by
    have hnd' : ((pointsOf x).zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    exact hnd'.sublist ((List.filter_sublist).map Prod.snd)
  have hf : Function.Injective f := by
    intro i j hij
    have heq : (L.map Prod.snd)[i.val]'(by simp) =
        (L.map Prod.snd)[j.val]'(by simp) := by
      simpa only [List.getElem_map, f, Fin.getElem_fin] using congrArg Fin.val hij
    exact Fin.ext (hnd.getElem_inj.mp heq)
  let e : Fin L.length ↪ Fin n := ⟨f, hf⟩
  refine ⟨L.length, e, ?_, ?_⟩
  · change L.map Prod.fst = _
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simpa [e] using hrow ⟨i, by simpa using hi⟩
  · ext l
    constructor
    · intro hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      have hh := (List.mem_filter.mp (List.getElem_mem i.isLt : L[i] ∈ L)).2
      have hh' : (e i).val ∈ indexList N := of_decide_eq_true hh
      obtain ⟨j, hj, heq⟩ := List.mem_map.mp hh'
      exact (Fin.ext heq : j = e i) ▸ (by simpa using hj)
    · intro hl
      have hidx : l.val ∈ indexList N := List.mem_map.mpr
        ⟨l, by simpa using hl, rfl⟩
      have hp : (List.ofFn (x l), l.val) ∈ L := by
        apply List.mem_filter.mpr
        refine ⟨?_, decide_eq_true hidx⟩
        simp [List.mem_zipIdx_iff_getElem?, pointsOf]
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp
      apply Finset.mem_image.mpr
      refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      change L[i].2 = l.val
      rw [heq]

private theorem preimage_block {m n : ℕ} (e : Fin m ↪ Fin n)
    (N G : Finset (Fin n)) (he : Finset.univ.image e = N) (hG : G ⊆ N) :
    let H := Finset.univ.filter fun i ↦ e i ∈ G
    H.image e = G := by
  classical
  ext l
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (he.symm ▸ hG hl)
    exact ⟨i, hl, rfl⟩

private theorem args_bounds (a : MomentArgs) :
    7 ≤ (encMomentArgs a).length ∧ dimension a ≤ (encMomentArgs a).length ∧
    (blockPoints a).length ≤ (encMomentArgs a).length ∧
    (orders a).length ≤ (encMomentArgs a).length ∧
    (encRat a.2.2.2.1).length ≤ (encMomentArgs a).length := by
  have hpts : (encPoints a.1).length ≤ (encMomentArgs a).length := by
    simp only [encMomentArgs, length_encPair]
    omega
  have horders : (encIndices (orders a)).length ≤ (encMomentArgs a).length := by
    simp only [encMomentArgs, orders, length_encPair]
    omega
  have hlenpts : a.1.length ≤ (encPoints a.1).length :=
    SizedListEncoding.length_le (encA := encVector) (encL := encList encVector) _
  have hdim : dimension a ≤ (encPoints a.1).length := by
    cases h : a.1 with
    | nil => simp [dimension, dim, h]
    | cons row rows =>
      have hr : row.length ≤ (encVector row).length :=
        SizedListEncoding.length_le (encA := encRat) (encL := encVector) _
      have hrow : (encVector row).length ≤ (encPoints a.1).length :=
        SizedListEncoding.length_elem_le (encA := encVector) (encL := encList encVector)
          _ row (by simp [h])
      simpa [dimension, dim, h] using hr.trans hrow
  have hblock : (blockPoints a).length ≤ a.1.length := by
    simpa only [blockPoints, List.length_map, List.length_zipIdx] using
      List.length_filter_le (l := a.1.zipIdx) (p := fun p ↦ p.2 ∈ a.2.1)
  have ho : (orders a).length ≤ (encIndices (orders a)).length :=
    SizedListEncoding.length_le (encA := encNat) (encL := encIndices) _
  have hw := SoS.Correct.one_le_length_encRat a.2.2.2.1
  have he := SoS.Correct.one_le_length_encRat a.2.2.2.2
  refine ⟨?_, hdim.trans hpts, hblock.trans (hlenpts.trans hpts), ho.trans horders, ?_⟩
  · simp only [encMomentArgs, length_encPair]
    omega
  · simp only [encMomentArgs, length_encPair]
    omega

private theorem ball_trace_bound (a : MomentArgs) (hw : 0 < a.2.2.2.1) :
    (blockPoints a).length + ∑ i : Fin (orders a).length,
      momentTraceBound (blockPoints a).length (dimension a) (orders a)[i]
        (budget a.2.2.2.1 (orders a)[i] : ℝ) ≤ (ball a : ℝ) := by
  let b := (encMomentArgs a).length
  let R := maxDegree (orders a)
  let T := 20 * b * (R + 1) ^ 3
  obtain ⟨hb, hd, hn, hJ, hwlen⟩ := args_bounds a
  have hwR : 0 < (a.2.2.2.1 : ℝ) := Rat.cast_pos.mpr hw
  have hinv : (a.2.2.2.1 : ℝ)⁻¹ ≤ 2 ^ b := by
    have h := SoS.Correct.two_pow_inv_le hw
    have hpow : (0 : ℝ) < 2 ^ (encRat a.2.2.2.1).length := by positivity
    have hh := (div_le_iff₀ hpow).mp h
    rw [inv_eq_one_div, div_le_iff₀ hwR]
    have hh' : 1 ≤ 2 ^ (encRat a.2.2.2.1).length * (a.2.2.2.1 : ℝ) := by
      simpa only [mul_comm] using hh
    exact hh'.trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hwlen) hwR.le)
  have htrace (i : Fin (orders a).length) :
      momentTraceBound (blockPoints a).length (dimension a) (orders a)[i]
        (budget a.2.2.2.1 (orders a)[i] : ℝ) ≤ 2 ^ T := by
    have hr : (orders a)[i] ≤ R := le_maxDegree (List.getElem_mem i.isLt)
    have hbud := MomentAnalytic.radial_budget_le (by omega : 1 ≤ b) hr hwR hinv
    have hb0 : 0 ≤ (budget a.2.2.2.1 (orders a)[i] : ℝ) := by
      simp only [budget, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_natCast]
      positivity
    apply MomentAnalytic.traceBound_le (by omega) hn hd hr hb0
    simpa only [budget, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_natCast] using hbud
  have hbpow : (b : ℝ) ≤ 2 ^ b := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hT : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  have hcount : (blockPoints a).length + ∑ i : Fin (orders a).length,
      momentTraceBound (blockPoints a).length (dimension a) (orders a)[i]
        (budget a.2.2.2.1 (orders a)[i] : ℝ) ≤ 2 ^ (T + b + 1) := by
    have hnR : ((blockPoints a).length : ℝ) ≤ b := by exact_mod_cast hn
    have hJR : ((orders a).length : ℝ) ≤ b := by exact_mod_cast hJ
    calc
      _ ≤ b + (orders a).length * (2 : ℝ) ^ T := by
        exact add_le_add hnR (by
          simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ htrace i))
      _ ≤ (2 : ℝ) ^ b * 2 ^ T + 2 ^ b * 2 ^ T := by
        exact add_le_add
          (hbpow.trans (le_mul_of_one_le_right (by positivity) hT))
          (mul_le_mul_of_nonneg_right (hJR.trans hbpow) (by positivity))
      _ = _ := by rw [← two_mul, ← pow_add, pow_succ, add_comm T b]; ring
  refine hcount.trans ?_
  simp only [ball, Rat.cast_pow, Rat.cast_ofNat]
  apply pow_le_pow_right₀ (by norm_num)
  exact MomentAnalytic.ball_exponent_bound b R hb

private theorem ball_toPoly (v : ℕ) (b : ℚ) :
    (constant b ++ (List.range v).map (fun i ↦ (unitExp v i 2, -1))).toPoly v =
      C b - ∑ i : Fin v, X i ^ 2 := by
  rw [SoS.Poly.toPoly_append, constant_toPoly]
  have hm : SoS.Solver.RawPoly.toPoly v
      ((List.range v).map (fun i ↦ (unitExp v i 2, (-1 : ℚ)))) =
      -∑ i : Fin v, X i ^ 2 := by
    rw [SoS.Solver.RawPoly.toPoly, List.map_map, SoS.Coords.sum_range_map,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have ht := unit_toPoly v i.val 2 (-1) i.isLt
    simpa only [SoS.Solver.RawPoly.toPoly, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, C_neg, C_1, neg_one_mul,
      Function.comp_def] using ht
  rw [hm]
  simp only [sub_eq_add_neg]

private theorem valid_of_natural (d : ℕ) (pts : Points) (J : List ℕ) (w ε b : ℚ)
    (hy : ∃ y : ℕ → ℝ, ∀ f ∈ momentConstraints (realPoints d pts) J
      (fun r ↦ (budget w r : ℝ)) ε b, 0 ≤ eval y f) :
    SoS.Solver.Problem.Valid
      (numVars pts.length d J, 2, constraints d pts J w ε b, [], []) := by
  obtain ⟨y, hy⟩ := hy
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst q
    simp [SoS.Solver.RawPoly.toPoly]
  · refine ⟨b, List.mem_map.mpr ⟨_, ?_, ball_toPoly _ b⟩⟩
    simp only [constraints, List.mem_append, List.mem_cons, true_or]
  · refine ⟨fun i ↦ y i.val, ?_⟩
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    have hmem : decode (numVars pts.length d J) p ∈
        momentConstraints (realPoints d pts) J (fun r ↦ (budget w r : ℝ)) ε b := by
      rw [← constraints_reify]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    simpa only [decode, eval_rename, Function.comp_def] using hy _ hmem

private theorem constraints_cast {m n d : ℕ} (h : m = n) (x : Fin n → Vec d)
    (J : List ℕ) (B : ℕ → ℝ) (ε b : ℝ) :
    momentConstraints (fun i : Fin m ↦ x (Fin.cast h i)) J B ε b =
      momentConstraints x J B ε b := by
  subst h
  rfl

/-- The explicit finite-dimensional input has a reference solution inside the chosen ball. -/
theorem problem_valid {n k d : ℕ} (D : Reference n k d) (x : Fin n → Fin d → ℚ)
    (J : Finset ℕ) (w ε : ℚ) (θ : ℝ)
    (hD : D.Valid w) (hx : ∀ l i, D.observed l i = (x l i : ℝ))
    (hJ : ∀ j ∈ J, 1 ≤ j) (hres : D.Resilient (2 * J.sup id) θ)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1 / 100000000)
    (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / (w : ℝ)) • (1 : Mat d))) :
    (problem (pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε)).Valid := by
  classical
  let a : MomentArgs := (pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε)
  have hw : 0 < w := Rat.cast_pos.mp hD.1.1
  have he8R : (ε : ℝ) ≤ 1 / 8 := by
    have h : (ε : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := Rat.cast_le.mpr he8
    norm_num at h
    exact h
  obtain ⟨_, hblock, hgoodB, _, hsize⟩ :=
    MomentAnalytic.reference_counts D w ε hD he he8R
  obtain ⟨m, e, hpts, heimage⟩ := blockPoints_reindex x D.block (J.sort (· ≤ ·)) w ε
  change blockPoints a = _ at hpts
  have hmcard : m = D.block.card := by
    have hh := congrArg Finset.card heimage
    simpa only [Finset.card_image_of_injective _ e.injective, Finset.card_univ,
      Fintype.card_fin] using hh
  have hn : n ≠ 0 := by
    intro hn
    subst n
    obtain ⟨l, _⟩ := hD.2.2.2.2.1
    exact isEmptyElim l
  have hdim : dimension a = d := by
    cases n with
    | zero => contradiction
    | succ n => simp [a, dimension, dim, pointsOf, List.ofFn_succ]
  let G : Finset (Fin m) := Finset.univ.filter fun i ↦ e i ∈ D.good
  have hGimage : G.image e = D.good := preimage_block e D.block D.good heimage hD.2.2.1
  have hGcard : G.card = D.good.card := by
    have hh := congrArg Finset.card hGimage
    simpa only [Finset.card_image_of_injective _ e.injective] using hh
  let z : Fin m → Vec d := fun i j ↦ (x (e i) j : ℝ)
  have hclean (r : ℕ) : (∑ i ∈ G, lin (z i) ^ (2 * r)) =
      ∑ l ∈ D.good, lin (D.clean l) ^ (2 * r) := by
    rw [← hGimage, Finset.sum_image (fun i _ j _ hij ↦ e.injective hij)]
    apply Finset.sum_congr rfl
    intro i hi
    have hgood : e i ∈ D.good := (Finset.mem_filter.mp hi).2
    have hz : z i = D.clean (e i) := by
      funext j
      exact (hx (e i) j).symm.trans (congrFun (hD.2.2.2.1 (e i) hgood) j)
    rw [hz]
  have hcert (r : ℕ) (hr : r ∈ J.sort (· ≤ ·)) :
      IsSumSq (C ((budget w r : ℝ) * m) * nsq ^ r -
        ∑ i ∈ G, lin (z i) ^ (2 * r)) := by
    have hrJ : r ∈ J := by simpa using hr
    have hrmax : r ≤ J.sup id := Finset.le_sup (f := id) hrJ
    have hh := MomentAnalytic.reference_sum_bound D w θ hD r (hJ r hrJ)
      (MomentAnalytic.resilient_mono D hres (by omega) hθ)
      ⟨hθ, by linarith only [hθsmall]⟩ hm hc hsize
    have hsub : IsSumSq ((∑ l ∈ D.reference, lin (D.clean l) ^ (2 * r)) -
        ∑ l ∈ D.good, lin (D.clean l) ^ (2 * r)) := by
      rw [← Finset.sum_sdiff hD.2.1, add_sub_cancel_right]
      apply IsSumSq.sum
      intro i _
      rw [pow_mul']
      exact SoS.isSumSq_sq _
    rw [hclean, budget_agrees, hmcard]
    convert hh.add hsub using 1
    ring
  have hball := ball_trace_bound a hw
  rw [hdim, hpts] at hball
  simp only [List.length_ofFn] at hball
  have hy := momentProgram_feasible_at_ball z G (J.sort (· ≤ ·))
    (fun r ↦ (budget w r : ℝ)) ε (ball a)
    ⟨(by simpa only [hmcard, hGcard] using hgoodB),
    (fun r _ ↦ by
      simp only [budget, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_natCast]
      have hwR := hD.1.1
      positivity), hcert, hball⟩
  change (problem a).Valid
  unfold problem
  rw [hdim, hpts]
  apply valid_of_natural
  have hlen : (List.ofFn (fun i ↦ List.ofFn (x (e i)))).length = m := by simp
  have hreal : realPoints d (List.ofFn fun i ↦ List.ofFn (x (e i))) =
      fun i ↦ z (Fin.cast hlen i) := by
    funext i j
    simp [realPoints, z, List.getD_eq_getElem?_getD]
    congr 2
  rw [hreal, constraints_cast hlen]
  exact hy

private theorem readWeight_polytime {α : Type} {input : α ↪ List Bool}
    {v i : α → ℕ} {out : α → SoS.Solver.Output}
    (hv : ComputableInPolyTime v input encUnary)
    (ho : ComputableInPolyTime out input SoS.Solver.encOutput)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x ↦ readWeight (v x) (out x) (i x)) input encRat :=
  rat_min' (rat_max' (SoS.Poly.coeff' hv ho (unitExp_polytime hv hi (const 1)))
    (const 0)) (const 1)

private def recoveryB (L d : ℕ) (pts : Points) (J : List ℕ) (R v : ℕ)
    (out : SoS.Solver.Output) : List RawPoly :=
  let weights := (List.range pts.length).map (readWeight v out)
  let W := weights.sum
  (List.range (R + 1)).map fun r ↦
    if r ∈ J then
      (pts.zip weights).flatMap fun p ↦
        scale (p.2 / W) (MomentExpansion.powerB L d (linear d p.1) r)
    else []

private theorem recoveryB_polytime {α : Type} {input : α ↪ List Bool}
    {L d R v : α → ℕ} {pts : α → Points} {J : α → List ℕ}
    {out : α → SoS.Solver.Output} (hL : ComputableInPolyTime L input encUnary)
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input (encList encVector))
    (hJ : ComputableInPolyTime J input (encList encUnary))
    (hR : ComputableInPolyTime R input encUnary)
    (hv : ComputableInPolyTime v input encUnary)
    (ho : ComputableInPolyTime out input SoS.Solver.encOutput) :
    ComputableInPolyTime
      (fun x ↦ recoveryB (L x) (d x) (pts x) (J x) (R x) (v x) (out x))
      input (encList SoS.Solver.encRawPoly) := by
  have hn := (length_list encVector).comp hx
  have hweights : ComputableInPolyTime
      (fun x ↦ (List.range (pts x).length).map (readWeight (v x) (out x)))
      input encVector := mapWithInput (range.comp hn)
    (readWeight_polytime (hv.comp (fst _ _)) (ho.comp (fst _ _)) (snd _ _))
  have hW := rat_sum' hweights
  have hzip := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.zip encVector encRat).comp (hx.prod hweights).tidy)
  unfold recoveryB
  apply mapWithInput (range.comp (unary_add' hR (const 1)))
  apply ite_decide (decide_mem (hJ.comp (fst _ _)) (snd _ _))
  · apply flatMapWithInput (hzip.comp (fst _ _))
    have hbase := (fst input encUnary).comp (fst _ (encPair encVector encRat))
    exact scale_polytime
      (rat_div' ((snd _ _).comp (snd _ _)) (hW.comp hbase))
      (powerB_polytime (hL.comp hbase) (hd.comp hbase)
        (linear_polytime (hd.comp hbase) ((fst _ _).comp (snd _ _)))
        ((snd _ _).comp (fst _ _)))
  · exact const []

private def recoverB (qout : MomentInput × SoS.Solver.Output) : List RawPoly :=
  let q := qout.1
  recoveryB q.2 (dimension q.1) (blockPoints q.1) (cappedOrders q)
    (min q.2 (maxDegree (orders q.1)))
    (gramOffsetB q.2 (blockPoints q.1).length (dimension q.1)
      (cappedOrders q) (cappedOrders q).length) qout.2

private theorem recoverB_polytime : ComputableInPolyTime recoverB
    (encPair encMomentInput SoS.Solver.encOutput) (encList SoS.Solver.encRawPoly) := by
  have hbase := fst encMomentInput SoS.Solver.encOutput
  exact recoveryB_polytime ((snd _ _).comp hbase)
    (dimension_polytime.comp ((fst _ _).comp hbase))
    (blockPoints_polytime.comp ((fst _ _).comp hbase))
    (cappedOrders_polytime.comp hbase) (cappedMax_polytime.comp hbase)
    (varsB_polytime.comp hbase) (snd _ _)

private theorem recoverB_eq (qout : MomentInput × SoS.Solver.Output)
    (hen : enabled qout.1 = true) : recoverB qout = recover qout := by
  let q := qout.1
  change enabled q = true at hen
  have hm : maxDegree (orders q.1) ≤ q.2 := by
    by_contra hm
    simp [enabled, hm] at hen
  have hL : expansionBound q.1 ≤ q.2 := by simpa [enabled, hm] using hen
  have hJ : cappedOrders q = orders q.1 := by
    unfold cappedOrders
    calc
      (orders q.1).map (min q.2) = (orders q.1).map id := by
        apply List.map_congr_left
        intro r hr
        exact min_eq_right ((le_maxDegree hr).trans hm)
      _ = _ := List.map_id _
  simp only [recoverB, recoveryB, show qout.1 = q from rfl, hJ, min_eq_right hm,
    gramOffsetB_eq _ _ hL, recover, hen, numVars]
  apply List.map_congr_left
  intro r hr
  have hr' : r ≤ maxDegree (orders q.1) := by
    simpa only [List.mem_range, Nat.lt_succ_iff] using hr
  split_ifs
  · apply flatMap_congr_mem
    intro p _
    rw [powerB_eq_of_bound (linear (dimension q.1) p.1) hL (by omega)
      (by simp [linear])]
  · rfl

/-- A machine certificate for clipping, normalizing, and expanding all requested moments. -/
theorem recover_polytime : ComputableInPolyTime recover
    (encPair encMomentInput SoS.Solver.encOutput) (encList SoS.Solver.encRawPoly) := by
  have h := ite' (enabled_polytime.comp (fst _ _)) recoverB_polytime (const [])
  exact h.of_enc_eq fun qout ↦ by
    by_cases hen : enabled qout.1 = true
    · simp [hen, recoverB_eq qout hen]
    · simp [hen, recover]

private theorem decoded_bounds (a : MomentArgs)
    (E : SoS.PseudoExpectation (Fin (numVars (blockPoints a).length
      (dimension a) (orders a))) 2)
    (hv : 0 < numVars (blockPoints a).length (dimension a) (orders a))
    (η : ℝ) (hE : E.ApproxSatisfies (problem a).system η 0) :
    ∀ f ∈ momentConstraints (realPoints (dimension a) (blockPoints a)) (orders a)
        (fun r ↦ (budget a.2.2.2.1 r : ℝ)) a.2.2.2.2 (ball a),
      -(η * SoS.coeffNorm f) ≤ MomentRead.lift E hv f ∧
        SoS.coeffNorm1 f ≤ 2 ^ (SoS.Solver.encProblem (problem a)).length := by
  let v := numVars (blockPoints a).length (dimension a) (orders a)
  intro f hf
  have hdeg := MomentAux.constraints_degree (realPoints (dimension a) (blockPoints a))
    (orders a) (fun r ↦ (budget a.2.2.2.1 r : ℝ))
    (a.2.2.2.2 : ℝ) (ball a) f hf
  rw [← constraints_reify] at hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
  have hback : rename (MomentRead.indexBack v hv)
      (decode v p) = SoS.toReal (p.toPoly v) := by
    rw [decode, rename_rename]
    have h : MomentRead.indexBack v hv ∘ Fin.val = id := by
      funext i
      exact MomentRead.indexBack_val v hv i
    simp only [h, rename_id, AlgHom.id_apply]
  have hd : (p.toPoly v).totalDegree ≤ 2 := by
    rw [← MomentRead.totalDegree_toReal]
    rw [← hback]
    exact (totalDegree_rename_le _ _).trans hdeg
  have hmem : p.toPoly v ∈ (problem a).system := List.mem_map.mpr ⟨p, hp, rfl⟩
  have hlo := hE.neg_le_apply_of_mem hmem (by simpa only [max_zero] using hd)
  have hnorm := (SoS.Correct.coeffNorm1_toReal_le v p).trans (SoS.Correct.rawNorm1_le p)
  have hsize := SoS.Correct.length_encRaw_le_of_mem (P := problem a) hp
  constructor
  · simpa only [MomentRead.coeffNorm_rename _ Fin.val_injective,
      MomentRead.lift_rename] using hlo
  · rw [MomentRead.coeffNorm1_rename _ Fin.val_injective]
    exact hnorm.trans (pow_le_pow_right₀ (by norm_num) hsize)

private theorem mono_length_ge (d r : ℕ) (hd : 0 < d) :
    r + 1 ≤ (SoS.Mono.all d r).length := by
  classical
  have hinj : Function.Injective (unitExp d 0) := by
    intro e f hef
    have hh := congrArg (fun l : List ℕ ↦ l.getD 0 0) hef
    simpa [unitExp, List.getD_eq_getElem?_getD, hd] using hh
  have hmem (e : ℕ) (he : e ∈ List.range (r + 1)) : unitExp d 0 e ∈ SoS.Mono.all d r := by
    have hlen : (unitExp d 0 e).length = d := by simp [unitExp]
    have hh := SoS.Mono.degree_toFinsupp hlen
    rw [unitExp_toFinsupp d 0 e hd, Finsupp.degree_single] at hh
    exact SoS.Mono.mem_all.mpr ⟨hlen, by simp only [List.mem_range] at he; omega⟩
  calc
    r + 1 = (((List.range (r + 1)).map (unitExp d 0)).toFinset).card := by
      rw [List.toFinset_card_of_nodup (List.nodup_range.map hinj), List.length_map,
        List.length_range]
    _ ≤ (SoS.Mono.all d r).toFinset.card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
      exact List.mem_toFinset.mpr (hmem j hj)
    _ ≤ _ := List.toFinset_card_le _

private theorem coefficient_sum_bound (a : MomentArgs) (i : Fin (orders a).length)
    (hbound : ∀ f ∈ momentConstraints (realPoints (dimension a) (blockPoints a)) (orders a)
        (fun r ↦ (budget a.2.2.2.1 r : ℝ)) a.2.2.2.2 (ball a),
      SoS.coeffNorm1 f ≤ 2 ^ (SoS.Solver.encProblem (problem a)).length) :
    (∑ μ ∈ (Rounding.monos (dimension a) (2 * (orders a)[i])).toFinset,
      SoS.coeffNorm1 ((momentTemplate (realPoints (dimension a) (blockPoints a)) (orders a)
        (fun r ↦ (budget a.2.2.2.1 r : ℝ)) i).coeff μ)) ≤
      (SoS.Solver.encProblem (problem a)).length *
        (2 : ℝ) ^ (SoS.Solver.encProblem (problem a)).length := by
  let S := (SoS.Solver.encProblem (problem a)).length
  have hsum := List.le_sum_of_mem (List.mem_map.mpr
    ⟨(orders a)[i], List.getElem_mem i.isLt, rfl⟩ :
      (SoS.Mono.all (dimension a) (2 * (orders a)[i])).length ∈
        (orders a).map fun r ↦ (SoS.Mono.all (dimension a) (2 * r)).length)
  have hlen := constraints_length (dimension a) (blockPoints a) (orders a)
    a.2.2.2.1 a.2.2.2.2 (ball a)
  have hsize := SoS.Correct.length_cons_le (problem a)
  have hcount : (Rounding.monos (dimension a) (2 * (orders a)[i])).toFinset.card ≤ S := by
    have hmono := List.toFinset_card_le
      (l := Rounding.monos (dimension a) (2 * (orders a)[i]))
    simp only [Rounding.monos, List.length_map] at hmono
    change (constraints (dimension a) (blockPoints a) (orders a)
      a.2.2.2.1 a.2.2.2.2 (ball a)).length ≤ S at hsize
    dsimp only [Rounding.monos]
    omega
  calc
    _ ≤ ∑ _μ ∈ (Rounding.monos (dimension a) (2 * (orders a)[i])).toFinset,
        (2 : ℝ) ^ S := by
      apply Finset.sum_le_sum
      intro μ hμ
      exact hbound _ (MomentAux.coefficient_constraints_mem _ _ _ _ _ i μ
        (List.mem_toFinset.mp hμ)).1
    _ ≤ S * (2 : ℝ) ^ S := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)

private theorem data_coordinate_bound (a : MomentArgs)
    (i : Fin (blockPoints a).length) (j : Fin (dimension a)) :
    |realPoints (dimension a) (blockPoints a) i j| ≤ 2 ^ (encMomentArgs a).length := by
  have hrow : (blockPoints a)[i] ∈ a.1 := by
    have hh := List.getElem_mem i.isLt
    change (blockPoints a)[i] ∈ blockPoints a at hh
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hh
    rw [← heq]
    exact List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hp).1
  have hpts : (encPoints a.1).length ≤ (encMomentArgs a).length := by
    simp only [encMomentArgs, length_encPair]
    omega
  have hrowlen : (encVector (blockPoints a)[i]).length ≤ (encPoints a.1).length :=
    SizedListEncoding.length_elem_le (encA := encVector) (encL := encList encVector)
      _ _ hrow
  unfold realPoints
  by_cases hj : j.val < ((blockPoints a)[i]).length
  · rw [List.getD_eq_getElem _ _ hj]
    have hentry := SizedListEncoding.length_elem_le (encA := encRat) (encL := encVector)
      _ _ (List.getElem_mem hj)
    exact (SoS.Correct.abs_le_two_pow_length _).trans
      (pow_le_pow_right₀ (by norm_num) ((hentry.trans hrowlen).trans hpts))
  · rw [List.getD_eq_default _ _ (by omega), Rat.cast_zero, abs_zero]
    positivity

private theorem data_norm_bound (a : MomentArgs) (i : Fin (orders a).length)
    (hr : 1 ≤ (orders a)[i]) (hP : (problem a).Valid) :
    (∑ j, sqnorm (realPoints (dimension a) (blockPoints a) j) ^ (orders a)[i]) ≤
      (2 : ℝ) ^ ((SoS.Solver.encProblem (problem a)).length * (encMomentArgs a).length) := by
  by_cases hd : dimension a = 0
  · have hri : (orders a)[i.val] ≠ 0 := by
      have hh := hr
      simp only [Fin.getElem_fin] at hh
      omega
    simp [hd, sqnorm, dotProduct, hri]
  · obtain ⟨_, hdA, hmA, _, _⟩ := args_bounds a
    have hlen := mono_length_ge (dimension a) (orders a)[i] (by omega)
    have hblock := gram_block (blockPoints a).length (dimension a) (orders a) i.val i.isLt
    rw [List.getD_eq_getElem _ _ i.isLt] at hblock
    have hv := SoS.Correct.numVars_le hP
    change numVars (blockPoints a).length (dimension a) (orders a) ≤
      (SoS.Solver.encProblem (problem a)).length at hv
    simp only [Fin.getElem_fin] at hlen hr
    have hS : 4 * (orders a)[i] ≤ (SoS.Solver.encProblem (problem a)).length := by
      have hsq := Nat.pow_le_pow_left hlen 2
      change 4 * (orders a)[i.val] ≤ _
      cases hri : (orders a)[i.val] with
      | zero => simp
      | succ r => simp only [hri] at hsq hblock; nlinarith
    exact MomentRead.sample_norm_sum_le _ hmA hdA hr hS (data_coordinate_bound a)

private theorem accuracy_mass_bound (q : MomentInput) (m : ℕ) (ε : ℝ)
    (hm : 0 < m) (hmA : m ≤ (encMomentArgs q.1).length) (he : 2 / m ≤ ε) :
    (accuracy q : ℝ) ≤ ε / 32 := by
  have hprec : (encMomentArgs q.1).length + 4 ≤ precision q := by
    have hA := (args_bounds q.1).1
    unfold precision
    apply le_trans (b := ((encMomentArgs q.1).length + 2) ^ 2)
    · nlinarith
    · exact Nat.pow_le_pow_left (by omega) 2
  have hpow : 16 * (m : ℝ) ≤ 2 ^ precision q := by
    calc
      _ ≤ 16 * (2 : ℝ) ^ (encMomentArgs q.1).length := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact_mod_cast hmA.trans (Nat.lt_two_pow_self).le
      _ = (2 : ℝ) ^ ((encMomentArgs q.1).length + 4) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hprec
  have hacc : (accuracy q : ℝ) ≤ 1 / (16 * m) := by
    simp only [accuracy, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
    exact one_div_le_one_div_of_le (by positivity) hpow
  apply hacc.trans
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  convert he using 1
  field_simp
  norm_num

private theorem readWeight_agrees (v : ℕ) (hv : 0 < v) (out : SoS.Solver.Output)
    (E : SoS.PseudoExpectation (Fin v) 2) (hMom : SoS.Solver.HasMoments E (out.toPoly v))
    (i : ℕ) (hi : i < v) :
    (readWeight v out i : ℝ) = clipped (MomentRead.lift E hv (X i)) := by
  have hh := hMom (Finsupp.single ⟨i, hi⟩ 1) (by simp [Finsupp.degree_single])
  rw [← X_pow_eq_monomial, pow_one] at hh
  have hc : (SoS.Poly.coeff v out (unitExp v i 1) : ℝ) = E (X ⟨i, hi⟩) := by
    rw [← SoS.Poly.coeff_toPoly out (by simp [unitExp]), unitExp_toFinsupp v i 1 hi]
    exact hh.symm
  have hL := MomentRead.lift_rename E hv (X ⟨i, hi⟩)
  simp only [rename_X] at hL
  simp only [readWeight, Rat.cast_min, Rat.cast_max, Rat.cast_zero, Rat.cast_one,
    hc, clipped, hL]

private theorem realize_flatMap {α : Type} (d : ℕ) (l : List α) (f : α → RawPoly) :
    SoS.toReal (RawPoly.toPoly d (l.flatMap f)) =
      (l.map fun a ↦ SoS.toReal ((f a).toPoly d)).sum := by
  induction l with
  | nil => simp [SoS.Solver.RawPoly.toPoly]
  | cons a l ih =>
    simp only [List.flatMap_cons, SoS.Poly.toPoly_append, SoS.toReal_add,
      ih, List.map_cons, List.sum_cons]

private theorem weighted_raw (d : ℕ) (pts : Points) (u : Fin pts.length → ℚ) (r : ℕ) :
    SoS.toReal (RawPoly.toPoly d ((pts.zip (List.ofFn u)).flatMap fun p ↦
      scale (p.2 / (List.ofFn u).sum) (power d (linear d p.1) r))) =
      weightedMoment (fun i ↦ (u i : ℝ)) (realPoints d pts) r := by
  have hzip : pts.zip (List.ofFn u) =
      List.ofFn (fun i : Fin pts.length ↦ (pts[i], u i)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  have hW : ((List.ofFn u).sum : ℝ) = ∑ i, (u i : ℝ) := by
    push_cast
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have hlin (i : Fin pts.length) :
      SoS.toReal ((power d (linear d pts[i]) r).toPoly d) =
        lin (realPoints d pts i) ^ r := by
    simp [power_toPoly, linear_toPoly, SoS.toReal, realPoints, lin]
  rw [hzip, realize_flatMap, List.map_ofFn, List.sum_ofFn]
  unfold weightedMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_def, scale_toPoly, SoS.toReal_mul, hlin]
  simp [SoS.toReal, hW, div_eq_mul_inv, C_mul, mul_assoc, mul_comm]

private theorem recover_weighted (q : MomentInput) (out : SoS.Solver.Output)
    (hen : enabled q = true) (r : ℕ) (hr : r ∈ orders q.1) :
    SoS.toReal (((recover (q, out)).getD r []).toPoly (dimension q.1)) =
      weightedMoment (fun i : Fin (blockPoints q.1).length ↦
        (readWeight (numVars (blockPoints q.1).length (dimension q.1) (orders q.1))
          out i.val : ℝ)) (realPoints (dimension q.1) (blockPoints q.1)) r := by
  have hrmax := le_maxDegree hr
  have hu : (List.range (blockPoints q.1).length).map
      (readWeight (numVars (blockPoints q.1).length (dimension q.1) (orders q.1)) out) =
      List.ofFn (fun i : Fin (blockPoints q.1).length ↦
        readWeight (numVars (blockPoints q.1).length (dimension q.1) (orders q.1))
          out i.val) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  simp only [recover, hen, ite_true]
  rw [List.getD_eq_getElem _ _ (by simpa using Nat.lt_succ_of_le hrmax)]
  simp only [List.getElem_map, List.getElem_range, ite_eq_left hr, hu]
  exact weighted_raw _ _ _ _

private theorem blockPoints_observed {n d : ℕ} (x : Fin n → Fin d → ℚ)
    (N : Finset (Fin n)) (J : List ℕ) (w ε : ℚ) :
    let pts := blockPoints (pointsOf x, indexList N, J, w, ε)
    ∃ e : Fin pts.length ↪ Fin n, Finset.univ.image e = N ∧
      ∀ i j, realPoints d pts i j = (x (e i) j : ℝ) := by
  classical
  dsimp only
  obtain ⟨m, e, hpts, he⟩ := blockPoints_reindex x N J w ε
  have hlen : (blockPoints (pointsOf x, indexList N, J, w, ε)).length = m := by
    rw [hpts, List.length_ofFn]
  let f : Fin (blockPoints (pointsOf x, indexList N, J, w, ε)).length ↪ Fin n :=
    (finCongr hlen).toEmbedding.trans e
  refine ⟨f, ?_, ?_⟩
  · ext l
    constructor
    · rintro hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      have hh : f i ∈ Finset.univ.image e :=
        Finset.mem_image.mpr ⟨Fin.cast hlen i, Finset.mem_univ _, rfl⟩
      exact he ▸ hh
    · intro hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (he.symm ▸ hl)
      refine Finset.mem_image.mpr ⟨Fin.cast hlen.symm i, Finset.mem_univ _, ?_⟩
      simp [f]
  · intro i j
    simp [realPoints, hpts, f, List.getD_eq_getElem?_getD]
    congr 2

private theorem read_moment_bound (q : MomentInput) (hen : enabled q = true)
    (E : SoS.PseudoExpectation (Fin (numVars (blockPoints q.1).length
      (dimension q.1) (orders q.1))) 2)
    (hv : 0 < numVars (blockPoints q.1).length (dimension q.1) (orders q.1))
    (hE : E.ApproxSatisfies (problem q.1).system (2 * (accuracy q : ℝ)) 0)
    (hP : (problem q.1).Valid) (i : Fin (orders q.1).length) (hr : 1 ≤ (orders q.1)[i]) :
    IsSumSq (C ((budget q.1.2.2.2.1 (orders q.1)[i] : ℝ) *
        (blockPoints q.1).length + 1) * nsq ^ (orders q.1)[i] -
      ∑ j : Fin (blockPoints q.1).length,
        C (clipped (MomentRead.lift E hv (X j.val))) *
          lin (realPoints (dimension q.1) (blockPoints q.1) j) ^ (2 * (orders q.1)[i])) := by
  let η : ℝ := 2 * (accuracy q : ℝ)
  let S := (SoS.Solver.encProblem (problem q.1)).length
  let A := (encMomentArgs q.1).length
  let C₀ := ∑ μ ∈ (Rounding.monos (dimension q.1) (2 * (orders q.1)[i])).toFinset,
    SoS.coeffNorm1 ((momentTemplate (realPoints (dimension q.1) (blockPoints q.1))
      (orders q.1) (fun r ↦ (budget q.1.2.2.2.1 r : ℝ)) i).coeff μ)
  let V := ∑ j, sqnorm (realPoints (dimension q.1) (blockPoints q.1) j) ^ (orders q.1)[i]
  have hη : 0 ≤ η := by
    have h : (0 : ℝ) < accuracy q := Rat.cast_pos.mpr (accuracy_pos q)
    positivity
  have hsingle := decoded_bounds q.1 E hv η hE
  have hC : C₀ ≤ S * (2 : ℝ) ^ S :=
    coefficient_sum_bound q.1 i (fun f hf ↦ (hsingle f hf).2)
  have hV : V ≤ (2 : ℝ) ^ (S * A) := data_norm_bound q.1 i hr hP
  have hp : precision q = (S + A + 2) ^ 2 := by
    unfold precision
    rw [guardedProblem, hen, ite_eq_left rfl]
  have herr : η * C₀ + 2 * η * V ≤ 1 := by
    have h := MomentRead.dyadic_error_bound S A C₀ V (by
      have hh := (args_bounds q.1).1
      omega) hC hV
    dsimp only [η]
    simp only [accuracy, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, hp]
    convert h using 1
    ring
  have hh := MomentRead.single_approximate_clipped_sos (MomentRead.lift E hv)
    (realPoints (dimension q.1) (blockPoints q.1)) (orders q.1)
    (fun r ↦ (budget q.1.2.2.2.1 r : ℝ)) q.1.2.2.2.2 (ball q.1) η hη
    (fun f hf ↦ (hsingle f hf).1) i
  have hslack : IsSumSq (C (1 - (η * C₀ + 2 * η * V)) *
      (nsq : RPoly (dimension q.1)) ^ (orders q.1)[i]) :=
    SoS.isSumSq_C_mul (sub_nonneg.mpr herr)
      (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) _)
  convert hh.add hslack using 1
  simp only [C_add, C_sub, C₀, V]
  ring

private theorem momentBudget_ge_one {n k d : ℕ} (D : Reference n k d) (w : ℝ)
    (hD : D.Valid w) (r : ℕ) (hr : 1 ≤ r) : 1 ≤ momentBudget w r := by
  obtain ⟨l, _⟩ := hD.2.2.2.2.1
  have hweight := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) ↦ hD.1.1.le.trans (hD.1.2.1 j))
    (Finset.mem_univ (D.label l))
  rw [hD.1.2.2.1] at hweight
  have hw : w ≤ 1 := (hD.1.2.1 (D.label l)).trans hweight
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hbase : (1 : ℝ) ≤ 20 * r / w :=
    (le_div_iff₀ hD.1.1).mpr (by linarith)
  have hpow := one_le_pow₀ hbase (n := r)
  unfold momentBudget
  linarith

/-- Correct pseudo-moments yield population certificates after clipping and normalization.
This is independent of a fuel formula: the explicit guard and solver correctness suffice. -/
theorem recovery_certificate {n k d : ℕ} (D : Reference n k d)
    (x : Fin n → Fin d → ℚ) (J : Finset ℕ) (w ε : ℚ) (θ : ℝ) (fuel : ℕ)
    (out : SoS.Solver.Output)
    (hD : D.Valid w) (hx : ∀ l i, D.observed l i = (x l i : ℝ))
    (hJ : ∀ j ∈ J, 1 ≤ j) (hres : D.Resilient (2 * J.sup id) θ)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1 / 100000000)
    (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / (w : ℝ)) • (1 : Mat d)))
    (hen : enabled ((pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε), fuel) = true)
    (hout : let q := ((pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε), fuel)
      SoS.Solver.Correct (guardedProblem q) (accuracy q) (accuracy q) out) :
    Certified D.model (fun r ↦
      let q : MomentInput := ((pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε), fuel)
      SoS.toReal (((recover (q, out)).getD r []).toPoly d)) J
      (fun r ↦ 250 * ε * momentBudget w r + 3 * θ ^ 2 * momentBudget w r) := by
  classical
  let a : MomentArgs := (pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε)
  let q : MomentInput := (a, fuel)
  let pts := blockPoints a
  let m := pts.length
  let v := numVars m (dimension a) (orders a)
  let η : ℝ := 2 * (accuracy q : ℝ)
  have he8R : (ε : ℝ) ≤ 1 / 8 := by
    have h : (ε : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := Rat.cast_le.mpr he8
    norm_num at h
    exact h
  obtain ⟨hε, hblock, hgoodB, _, hsize⟩ :=
    MomentAnalytic.reference_counts D w ε hD he he8R
  obtain ⟨e, heimage, hobs⟩ := blockPoints_observed x D.block (J.sort (· ≤ ·)) w ε
  change Fin m ↪ Fin n at e
  have hmcard : m = D.block.card := by
    have hh := congrArg Finset.card heimage
    simpa only [Finset.card_image_of_injective _ e.injective, Finset.card_univ,
      Fintype.card_fin] using hh
  have hmpos : 0 < m := by exact_mod_cast (hmcard.symm ▸ hblock)
  have hn : n ≠ 0 := by
    obtain ⟨l, _⟩ := hD.2.2.2.2.1
    have hl := l.isLt
    omega
  have hdim : dimension a = d := by
    cases n with
    | zero => contradiction
    | succ n => simp [a, dimension, dim, pointsOf, List.ofFn_succ]
  have hmv : m ≤ v := by dsimp [v, numVars, gramOffset]; omega
  have hv : 0 < v := hmpos.trans_le hmv
  have hP := problem_valid D x J w ε θ hD hx hJ hres hθ hθsmall he he8 hm hc
  change (problem a).Valid at hP
  change enabled q = true at hen
  change SoS.Solver.Correct (guardedProblem q) (accuracy q) (accuracy q) out at hout
  rw [guardedProblem, hen, ite_eq_left rfl] at hout
  obtain ⟨E, hMom, hE, _⟩ := hout
  change SoS.PseudoExpectation (Fin v) 2 at E
  have hηeq : (accuracy q : ℝ) + accuracy q = η := by dsimp [η]; ring
  rw [hηeq] at hE
  have hηpos : 0 < η := mul_pos (by norm_num) (Rat.cast_pos.mpr (accuracy_pos q))
  let u : Fin m → ℝ := fun i ↦ clipped (MomentRead.lift E hv (X i.val))
  let z : Fin m → Vec d := realPoints d pts
  have hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 := fun i ↦ MomentAux.clipped_bounds _
  have hsingle := decoded_bounds a E hv η hE
  have hsingle' : ∀ f ∈ momentConstraints z (orders a)
      (fun r ↦ (budget w r : ℝ)) ε (ball a),
      -(η * SoS.coeffNorm f) ≤ MomentRead.lift E hv f := by
    intro f hf
    apply (hsingle f _).1
    change f ∈ momentConstraints (realPoints (dimension a) pts) (orders a)
      (fun r ↦ (budget w r : ℝ)) ε (ball a)
    rw [hdim]
    exact hf
  have hmass := MomentRead.single_read_clipped_mass (MomentRead.lift E hv) z
    (orders a) (fun r ↦ (budget w r : ℝ)) ε (ball a) η hηpos.le
    ⟨hε.le, by linarith⟩ hsingle'
  have hfloor : 2 / (m : ℝ) ≤ ε := by
    have hh : 2 / (D.block.card : ℝ) ≤ ε :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans he
    simpa only [hmcard] using hh
  have hacc := accuracy_mass_bound q m ε hmpos (args_bounds a).2.2.1 hfloor
  let α : ℝ := ε + 4 * η
  have hα : 0 < α ∧ α ≤ 1 / 4 := by dsimp [α, η]; constructor <;> linarith
  have hαε : α ≤ 5 / 4 * (ε : ℝ) := by dsimp [α, η]; linarith
  let G : Finset (Fin m) := Finset.univ.filter fun i ↦ e i ∈ D.good
  have hGimage : G.image e = D.good := preimage_block e _ _ heimage hD.2.2.1
  have hGcard : G.card = D.good.card := by
    have hh := congrArg Finset.card hGimage
    simpa only [Finset.card_image_of_injective _ e.injective] using hh
  have hclean (s : ℕ) : (∑ i ∈ G, lin (z i) ^ s) =
      ∑ l ∈ D.good, lin (D.clean l) ^ s := by
    rw [← hGimage, Finset.sum_image (fun i _ j _ hij ↦ e.injective hij)]
    apply Finset.sum_congr rfl
    intro i hi
    have hgood : e i ∈ D.good := (Finset.mem_filter.mp hi).2
    have hz : z i = D.clean (e i) := by
      funext j
      exact (hobs i j).trans ((hx (e i) j).symm.trans
        (congrFun (hD.2.2.2.1 (e i) hgood) j))
    rw [hz]
  have hGmass : (1 - α) * m ≤ G.card := by
    have hh : (1 - (ε : ℝ)) * m ≤ G.card := by
      simpa only [hmcard, hGcard] using hgoodB
    dsimp only [α]
    nlinarith only [hh, mul_nonneg hηpos.le (Nat.cast_nonneg (α := ℝ) m)]
  have hGmom (r : ℕ) (_hr : r ∈ J) :
      empiricalMoment G z r = empiricalMoment D.good D.clean r := by
    simp only [empiricalMoment, hGcard, hclean]
  have hGsos (r : ℕ) (hr : r ∈ J) :
      IsSumSq (C (2 * momentBudget w r * m) * nsq ^ r -
        ∑ i ∈ G, lin (z i) ^ (2 * r)) := by
    have hrmax : r ≤ J.sup id := Finset.le_sup (f := id) hr
    have hh := MomentAnalytic.reference_sum_bound D w θ hD r (hJ r hr)
      (MomentAnalytic.resilient_mono D hres (by omega) hθ)
      ⟨hθ, by linarith⟩ hm hc hsize
    have hsub : IsSumSq ((∑ l ∈ D.reference, lin (D.clean l) ^ (2 * r)) -
        ∑ l ∈ D.good, lin (D.clean l) ^ (2 * r)) := by
      rw [← Finset.sum_sdiff hD.2.1, add_sub_cancel_right]
      apply IsSumSq.sum
      intro i _
      rw [pow_mul']
      exact SoS.isSumSq_sq _
    rw [hclean, hmcard]
    convert hh.add hsub using 1
    ring
  have husos (r : ℕ) (hr : r ∈ J) :
      IsSumSq (C (3 * momentBudget w r * m) * nsq ^ r -
        ∑ i, C (u i) * lin (z i) ^ (2 * r)) := by
    have hrlist : r ∈ orders a := by simpa only [a, orders] using (J.mem_sort _).mpr hr
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hrlist
    have hh := read_moment_bound q hen E hv hE hP ⟨i, hi⟩ (by
      change 1 ≤ (orders a)[i]
      simpa only [Fin.getElem_fin, hir] using hJ r hr)
    change IsSumSq (C ((budget w (orders a)[i] : ℝ) * m + 1) *
      (nsq : RPoly (dimension a)) ^ (orders a)[i] -
        ∑ j : Fin m, C (u j) *
          lin (realPoints (dimension a) pts j) ^ (2 * (orders a)[i])) at hh
    rw [hir, hdim, budget_agrees] at hh
    have hB := momentBudget_ge_one D w hD r (hJ r hr)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hslack : IsSumSq (C (momentBudget w r * m - 1) * (nsq : RPoly d) ^ r) :=
      SoS.isSumSq_C_mul (by nlinarith)
        (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) r)
    convert hh.add hslack using 1
    simp only [C_add, C_sub, C_mul, map_ofNat, z]
    ring
  have hcert := MomentAnalytic.certified_transfer D z G u J w ε θ α hD he he8R hres
    hθ hθsmall hm hc hJ hmpos hu hα hαε hGmass
    (by
      convert hmass using 1
      dsimp [α, u]
      ring) hGmom hGsos husos
  intro r hr
  have hrlist : r ∈ orders a := by simpa only [a, orders] using (J.mem_sort _).mpr hr
  have hraw := recover_weighted q out hen r hrlist
  have hweights : (fun i : Fin m ↦ (readWeight v out i.val : ℝ)) = u := by
    funext i
    exact readWeight_agrees v hv out E hMom i.val (i.isLt.trans_le hmv)
  change SoS.toReal (((recover (q, out)).getD r []).toPoly (dimension a)) =
    weightedMoment (fun i : Fin m ↦ (readWeight v out i.val : ℝ))
      (realPoints (dimension a) pts) r at hraw
  rw [hweights, hdim] at hraw
  change SoS.toReal (((recover (q, out)).getD r []).toPoly d) = weightedMoment u z r at hraw
  simpa only [← hraw] using hcert r hr

/-- The certified solver theorem applies with precisely the budget prepared above. -/
theorem solver_correct (q : MomentInput) (hP : (guardedProblem q).Valid) :
    SoS.Solver.Correct (guardedProblem q) (accuracy q) (accuracy q)
      (SoS.Core.core (prepare q)) := by
  have h := SoS.Correct.core_correct (guardedProblem q) hP (accuracy q) (accuracy q)
    (accuracy_pos q) (accuracy_pos q)
  change SoS.Solver.Correct (guardedProblem q) (accuracy q) (accuracy q)
    (SoS.Core.core ((prepare q).1, SoS.Solver.budget (prepare q).1)) at h
  rw [← prepare_budget q] at h
  exact h

/-- Solver validity and recovery correctness compose independently of the chosen fuel bound. -/
theorem certified_of_enabled {n k d : ℕ} (D : Reference n k d)
    (x : Fin n → Fin d → ℚ) (J : Finset ℕ) (w ε : ℚ) (θ : ℝ) (fuel : ℕ)
    (hD : D.Valid w) (hx : ∀ l i, D.observed l i = (x l i : ℝ))
    (hJ : ∀ j ∈ J, 1 ≤ j) (hres : D.Resilient (2 * J.sup id) θ)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1 / 100000000)
    (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / (w : ℝ)) • (1 : Mat d)))
    (hen : enabled ((pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε), fuel) = true) :
    Certified D.model
      (fun r ↦ SoS.toReal (momentProc code x D.block J w ε fuel r)) J
      (fun r ↦ 250 * ε * momentBudget w r + 3 * θ ^ 2 * momentBudget w r) := by
  let q : MomentInput := ((pointsOf x, indexList D.block, J.sort (· ≤ ·), w, ε), fuel)
  have hP : (guardedProblem q).Valid := by
    rw [guardedProblem, show enabled q = true from hen, ite_eq_left rfl]
    exact problem_valid D x J w ε θ hD hx hJ hres hθ hθsmall he he8 hm hc
  exact recovery_certificate D x J w ε θ fuel (SoS.Core.core (prepare q)) hD hx hJ
    hres hθ hθsmall he he8 hm hc hen (solver_correct q hP)

/-- The original coarse sufficient budget satisfies `MomentContract` for the explicit code. -/
theorem contract : MomentContract (momentProc code) := by
  intro n k d D x J w ε θ fuel hD hx hJ hres hθ hθsmall he he8 hm hc hf
  exact certified_of_enabled D x J w ε θ fuel hD hx hJ hres hθ hθsmall he he8 hm hc
    (enabled_of_coarse x D.block J w ε fuel hf)

/-- The sharper budget satisfies the same guarantee, using its own guard estimate. -/
theorem adequate : MomentAdequate (momentProc code) := by
  intro n k d D x J w ε θ fuel hD hx hJ hres hθ hθsmall he he8 hm hc hf
  exact certified_of_enabled D x J w ε θ fuel hD hx hJ hres hθ hθsmall he he8 hm hc
    (enabled_of_adequate x D.block J w ε fuel hf)

end MomentProgram

end ABBKS26.Assembly.Exec
