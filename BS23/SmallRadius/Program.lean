module

public import BS23.SmallRadius.RawAlg
public import Background.SumOfSquares.Boolean

/-!
# The sum-of-squares program of the small-radius algorithm

One round of the algorithm for [BS23, Theorem 1.3] hands the sum-of-squares solver a Boolean
program on the `n` remaining points `z₀, …, zₙ₋₁ ∈ ℚ^d`. Its variables (`BS23.SmallRadius.Lay`)
are, in this order,

* `wᵢ` for `i < n` (`Lay.wv`), the indicator of the cluster being found;
* `μₐ` for `a < d` (`Lay.mv`), its mean;
* `σ` (`Lay.sv`), its size;
* `C_α` for the exponent vectors `α` of degree at most `2s` (`Lay.cv`, the list `Lay.As`), the
  coefficients of `∑ᵢ wᵢ ⟨zᵢ - μ, v⟩^{2s}` as a polynomial in an auxiliary `v ∈ ℝ^d`;
* `P_{βc}` for `β, c` in the exponent vectors of degree at most `t` (`Lay.pv`, the list
  `Lay.Bs`), a Gram factor.

The constraints (`Lay.constraints`), each equality as the pair `±h`:

* (Ball) `Bd - ∑ xₖ² ≥ 0` over all variables;
* (Bool) `wᵢ² - wᵢ = 0` (only the `w`-variables are Boolean);
* (Sum) `σ - ∑ᵢ wᵢ = 0`;
* (Coef) for every `α` with `|α| ≤ 2s`: `Coef_α = 0`, the coefficient of `v^α` in
  `F_coef = ∑_α C_α v^α - ∑ᵢ wᵢ ⟨zᵢ - μ, v⟩^{2s}`;
* (Mom) for every `γ` with `|γ| ≤ 2t`: `Mom_γ = 0`, the coefficient of `v^γ` in
  `F_mom = K σ^m B̃(v) - (∑_α C_α v^α)^m - ∑_c (∑_β P_{βc} v^β)²`, where
  `B̃(v) = ∑_γ b_γ v^γ` has the given coefficients `b`.

The objective is `q₀ = -∑ᵢ wᵢ` and the degree is `64 t` (`BS23.SmallRadius.problem`).

Rather than expanding these coefficients by hand (multinomial coefficients, tuples summing to
`γ`), the polynomials `F_coef` and `F_mom` are built as raw polynomials in the program variables
together with `d` extra variables `v` (with `SoS.Poly.prodRaw` for the powers), and the constraint
for `γ` keeps their terms with `v`-exponent `γ` (`RawAlg.coeffV`). So `C_α` exists also for
`|α| < 2s`, where the constraint forces `C_α = 0`.

## Main statements

* **The identities** (`Lay.mom_identity`, `Lay.coef_identity`), in every commutative
  `ℚ`-algebra, after substituting `ψ` for the program variables and `φ` for `v`:
  `∑_γ φ^γ Mom_γ = K σ^m B̃(φ) - (∑_α C_α φ^α)^m - ∑_c (∑_β P_{βc} φ^β)²` and
  `∑_α φ^α Coef_α = ∑_α C_α φ^α - ∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s}`. Their forms for symbolic real
  polynomials `φ` (`Lay.mom_identity_X`, `Lay.coef_identity_X`) and at a real point, where a
  constraint is the coefficient of `v^γ` in a polynomial in `v` (`Lay.eval_momRaw`,
  `Lay.eval_coefRaw`).
  They need `Lay.Good`: the lists of exponent vectors are the right ones and nothing is cut.
* **The system** (`BS23.SmallRadius.hasEq_bool`, `hasEq_sum`, `hasEq_coef`, `hasEq_mom`,
  `ball_mem_system`), the degrees of the constraints (`Lay.totalDegree_coefRaw_le`,
  `Lay.totalDegree_momRaw_le`, `BS23.SmallRadius.totalDegree_le_of_mem_system`), validity from a
  feasible point (`BS23.SmallRadius.valid_of_eval`; points are built block by block with
  `Lay.point`) and the objective (`BS23.SmallRadius.objective_eq`).
* **`B̃` from data** (`BS23.SmallRadius.bOf`): the coefficients of `(n t^t)⁻¹ ∑ⱼ ⟨Yⱼ, v⟩^{2t}`,
  so that `B̃(φ) = (n t^t)⁻¹ ∑ⱼ ⟨Yⱼ, φ⟩^{2t}` (`BS23.SmallRadius.sum_bOf_mul_powE`).

The lists of exponent vectors are cut by a unary budget `Lb` (`SoS.Mono.allB`), which also cuts
the products; nothing is cut when `m s ≤ t`, `s ≤ t` and `(2d + 2)^{2t} ≤ Lb`
(`BS23.SmallRadius.Fits`; then `BS23.SmallRadius.good_lay` gives `Lay.Good`).
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg

/-! ### The layout of the variables -/

/-- The variables of the program: `n` weights, `d` mean coordinates, the size, one coefficient per
exponent vector in `As`, and one Gram entry per pair of exponent vectors in `Bs`. -/
structure Lay where
  /-- The number of points. -/
  n : ℕ
  /-- The dimension. -/
  d : ℕ
  /-- The exponent vectors indexing the coefficients `C_α`. -/
  As : List (List ℕ)
  /-- The exponent vectors indexing the rows and columns of the Gram factor `P`. -/
  Bs : List (List ℕ)

namespace Lay

variable (L : Lay)

/-- The number of coefficient variables. -/
abbrev A : ℕ := L.As.length

/-- The number of rows (and columns) of the Gram factor. -/
abbrev B : ℕ := L.Bs.length

/-- The number of variables. -/
abbrev N : ℕ := L.n + L.d + 1 + L.A + L.B * L.B

/-- The weight `wᵢ`. -/
def wv (i : Fin L.n) : Fin L.N :=
  Fin.castAdd (L.B * L.B) (Fin.castAdd L.A (Fin.castAdd 1 (Fin.castAdd L.d i)))

/-- The mean coordinate `μₐ`. -/
def mv (a : Fin L.d) : Fin L.N :=
  Fin.castAdd (L.B * L.B) (Fin.castAdd L.A (Fin.castAdd 1 (Fin.natAdd L.n a)))

/-- The size `σ`. -/
def sv : Fin L.N :=
  Fin.castAdd (L.B * L.B) (Fin.castAdd L.A (Fin.natAdd (L.n + L.d) (0 : Fin 1)))

/-- The coefficient `C_α` for `α = As[j]`. -/
def cv (j : Fin L.A) : Fin L.N := Fin.castAdd (L.B * L.B) (Fin.natAdd (L.n + L.d + 1) j)

/-- The Gram entry `P_{βc}` for `β = Bs[β]`, `c = Bs[c]`. -/
def pv (β c : Fin L.B) : Fin L.N := Fin.natAdd (L.n + L.d + 1 + L.A) (finProdFinEquiv (β, c))

@[simp] theorem val_wv (i : Fin L.n) : (L.wv i : ℕ) = i := rfl

@[simp] theorem val_mv (a : Fin L.d) : (L.mv a : ℕ) = L.n + a := rfl

@[simp] theorem val_sv : (L.sv : ℕ) = L.n + L.d := rfl

@[simp] theorem val_cv (j : Fin L.A) : (L.cv j : ℕ) = L.n + L.d + 1 + j := rfl

@[simp] theorem val_pv (β c : Fin L.B) :
    (L.pv β c : ℕ) = L.n + L.d + 1 + L.A + (c + L.B * β) := by
  simp [pv, finProdFinEquiv_apply_val]

/-- A point of the program, given by its blocks. -/
def point {R : Type*} (yw : Fin L.n → R) (yμ : Fin L.d → R) (yσ : R) (yC : Fin L.A → R)
    (yP : Fin L.B → Fin L.B → R) : Fin L.N → R :=
  Fin.append (Fin.append (Fin.append (Fin.append yw yμ) fun _ : Fin 1 => yσ) yC)
    fun k => yP (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

section Point

variable {R : Type*} (yw : Fin L.n → R) (yμ : Fin L.d → R) (yσ : R) (yC : Fin L.A → R)
  (yP : Fin L.B → Fin L.B → R)

@[simp] theorem point_wv (i : Fin L.n) : L.point yw yμ yσ yC yP (L.wv i) = yw i := by
  simp [point, wv]

@[simp] theorem point_mv (a : Fin L.d) : L.point yw yμ yσ yC yP (L.mv a) = yμ a := by
  simp [point, mv]

@[simp] theorem point_sv : L.point yw yμ yσ yC yP L.sv = yσ := by
  simp [point, sv]

@[simp] theorem point_cv (j : Fin L.A) : L.point yw yμ yσ yC yP (L.cv j) = yC j := by
  simp [point, cv]

@[simp] theorem point_pv (β c : Fin L.B) : L.point yw yμ yσ yC yP (L.pv β c) = yP β c := by
  simp only [point, pv, Fin.append_right, Equiv.symm_apply_apply]

/-- The sum of squares of the coordinates of a point, block by block. -/
theorem sum_point_sq [CommSemiring R] :
    ∑ k, L.point yw yμ yσ yC yP k ^ 2 = ∑ i, yw i ^ 2 + ∑ a, yμ a ^ 2 + yσ ^ 2 + ∑ j, yC j ^ 2 +
      ∑ β, ∑ c, yP β c ^ 2 := by
  simp only [point, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.univ_unique,
    Finset.sum_singleton]
  congr 1
  rw [← Finset.sum_product', Finset.univ_product_univ]
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl

end Point

/-! ### The raw polynomials -/

section Raw

variable (z : Fin L.n → Fin L.d → ℚ)

/-- `⟨zᵢ - μ, v⟩ = ∑ₐ (zᵢₐ - μₐ) vₐ`, in the program variables and `v`. -/
def linRaw (i : Fin L.n) : RawPoly :=
  (List.finRange L.d).flatMap fun a : Fin L.d =>
    [tm (List.replicate L.N 0) (unitExp L.d a 1) (z i a),
      tm (unitExp L.N (L.mv a) 1) (unitExp L.d a 1) (-1)]

/-- `wᵢ`, in the program variables and `v`. -/
def wTerm (i : Fin L.n) : RawPoly := [tm (unitExp L.N (L.wv i) 1) [] 1]

/-- `∑_α C_α v^α`. -/
def cLin : RawPoly := (List.finRange L.A).map fun j => tm (unitExp L.N (L.cv j) 1) (L.As.get j) 1

/-- `∑_β P_{βc} v^β`, the `c`-th column of the Gram factor. -/
def pLin (c : Fin L.B) : RawPoly :=
  (List.finRange L.B).map fun β => tm (unitExp L.N (L.pv β c) 1) (L.Bs.get β) 1

/-- `F_coef = ∑_α C_α v^α - ∑ᵢ wᵢ ⟨zᵢ - μ, v⟩^{2s}`. -/
def coefF (s Lb : ℕ) : RawPoly :=
  L.cLin ++ neg ((List.finRange L.n).flatMap fun i =>
    prodRaw (L.N + L.d) Lb (L.wTerm i :: List.replicate (2 * s) (L.linRaw z i)))

/-- `K σ^m B̃(v)`, with `B̃(v) = ∑_{γ ∈ Gs} b_γ v^γ`. -/
def bPart (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) : RawPoly :=
  Gs.map fun γ => tm (unitExp L.N L.sv m) γ (K * b γ)

/-- `F_mom = K σ^m B̃(v) - (∑_α C_α v^α)^m - ∑_c (∑_β P_{βc} v^β)²`. -/
def momF (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) (Lb : ℕ) : RawPoly :=
  L.bPart Gs b m K ++ neg (prodRaw (L.N + L.d) Lb (List.replicate m L.cLin)) ++
    neg ((List.finRange L.B).flatMap fun c => prodRaw (L.N + L.d) Lb (List.replicate 2 (L.pLin c)))

/-- The constraint `Coef_α`: the coefficient of `v^α` in `F_coef`. -/
def coefRaw (s Lb : ℕ) (α : List ℕ) : RawPoly := coeffV L.N L.d (L.coefF z s Lb) α

/-- The constraint `Mom_γ`: the coefficient of `v^γ` in `F_mom`. -/
def momRaw (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) (Lb : ℕ) (γ : List ℕ) :
    RawPoly :=
  coeffV L.N L.d (L.momF Gs b m K Lb) γ

/-- The ball `Bd - ∑ₖ xₖ²`, over all variables. -/
def ballRaw (Bd : ℚ) : RawPoly :=
  ([], Bd) :: (List.finRange L.N).map fun k : Fin L.N => (unitExp L.N k 2, -1)

/-- `wᵢ² - wᵢ`. -/
def boolRaw (i : Fin L.n) : RawPoly := [(unitExp L.N (L.wv i) 2, 1), (unitExp L.N (L.wv i) 1, -1)]

/-- `σ - ∑ᵢ wᵢ`. -/
def sumRaw : RawPoly :=
  (unitExp L.N L.sv 1, 1) :: (List.finRange L.n).map fun i => (unitExp L.N (L.wv i) 1, -1)

/-- The objective `q₀ = -∑ᵢ wᵢ`. -/
def objRaw : RawPoly := (List.finRange L.n).map fun i => (unitExp L.N (L.wv i) 1, -1)

/-- The constraints: the ball, then `±` the Boolean, size, coefficient and moment equalities. -/
def constraints (Gs : List (List ℕ)) (b : List ℕ → ℚ) (s m : ℕ) (K Bd : ℚ) (Lb : ℕ) :
    List RawPoly :=
  L.ballRaw Bd :: ((List.finRange L.n).flatMap fun i => [L.boolRaw i, neg (L.boolRaw i)]) ++
    [L.sumRaw, neg L.sumRaw] ++
    (L.As.flatMap fun α => [L.coefRaw z s Lb α, neg (L.coefRaw z s Lb α)]) ++
    (Gs.flatMap fun γ => [L.momRaw Gs b m K Lb γ, neg (L.momRaw Gs b m K Lb γ)])

end Raw

end Lay

/-! ### The problem -/

/-- The layout for `n` points in dimension `d`, with the exponent vectors of degree at most `2s`
and at most `t` (cut by the budget `Lb`). -/
def lay (n d s t Lb : ℕ) : Lay := ⟨n, d, Mono.allB Lb d (2 * s), Mono.allB Lb d t⟩

/-- The exponent vectors `γ` of the moment constraints: degree at most `2t`. -/
def gams (d t Lb : ℕ) : List (List ℕ) := Mono.allB Lb d (2 * t)

/-- **The program of one round** on the points `z₀, …, zₙ₋₁ ∈ ℚ^d`, with the coefficients `b`
of `B̃`, the degrees `s, t`, the power `m`, the constant `K`, the ball radius `Bd` and the budget
`Lb`: degree `64 t`, the constraints `BS23.SmallRadius.Lay.constraints`, objective `-∑ᵢ wᵢ`. -/
def problem {n d : ℕ} (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (s t m : ℕ) (K Bd : ℚ)
    (Lb : ℕ) : Problem :=
  ((lay n d s t Lb).N, 64 * t, (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb,
    ((lay n d s t Lb).objRaw, []))

/-! ### The polynomials -/

namespace Lay

variable (L : Lay)

theorem toPoly_ballRaw (Bd : ℚ) : (L.ballRaw Bd).toPoly L.N = C Bd - ∑ k, X k ^ 2 := by
  rw [ballRaw, toPoly_cons, termPoly_nil, toPoly_map, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  rw [termPoly_unitExp, map_neg, map_one, neg_one_mul]

theorem toPoly_boolRaw (i : Fin L.n) : (L.boolRaw i).toPoly L.N = X (L.wv i) ^ 2 - X (L.wv i) := by
  rw [boolRaw, toPoly_cons, toPoly_cons, toPoly_nil, termPoly_unitExp, termPoly_unitExp]
  simp only [map_one, one_mul, map_neg, neg_mul, pow_one, add_zero]
  ring

theorem toPoly_sumRaw : L.sumRaw.toPoly L.N = X L.sv - ∑ i, X (L.wv i) := by
  rw [sumRaw, toPoly_cons, termPoly_unitExp, toPoly_map, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  simp only [map_one, one_mul, pow_one]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  rw [termPoly_unitExp, map_neg, map_one, neg_one_mul, pow_one]

theorem toPoly_objRaw : L.objRaw.toPoly L.N = -∑ i, X (L.wv i) := by
  rw [objRaw, toPoly_map, ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [termPoly_unitExp, map_neg, map_one, neg_one_mul, pow_one]

@[simp] theorem length_cLin : L.cLin.length = L.A := by simp [cLin]

@[simp] theorem length_pLin (c : Fin L.B) : (L.pLin c).length = L.B := by simp [pLin]

@[simp] theorem length_linRaw (z : Fin L.n → Fin L.d → ℚ) (i : Fin L.n) :
    (L.linRaw z i).length = 2 * L.d := by
  simp [linRaw, List.length_flatMap, mul_comm]

section Aeval

variable {S : Type*} [CommRing S] [Algebra ℚ S] (ψ : Fin L.N → S) (φ : Fin L.d → S)

theorem aeval_linRaw (z : Fin L.n → Fin L.d → ℚ) (i : Fin L.n) :
    aeval (Fin.append ψ φ) ((L.linRaw z i).toPoly (L.N + L.d)) =
      ∑ a, (algebraMap ℚ S (z i a) - ψ (L.mv a)) * φ a := by
  rw [linRaw, toPoly_flatMap, map_list_sum, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply, toPoly_cons, toPoly_nil, add_zero, map_add, aeval_append_tm0,
    aeval_append_tm, powE_unitExp, map_neg, map_one, pow_one]
  ring

theorem aeval_wTerm (i : Fin L.n) :
    aeval (Fin.append ψ φ) ((L.wTerm i).toPoly (L.N + L.d)) = ψ (L.wv i) := by
  simp only [wTerm, toPoly_cons, toPoly_nil, add_zero, aeval_append_tm, powE_nil, map_one,
    one_mul, pow_one, mul_one]

theorem aeval_cLin :
    aeval (Fin.append ψ φ) (L.cLin.toPoly (L.N + L.d)) = ∑ j, ψ (L.cv j) * powE φ (L.As.get j) := by
  rw [cLin, toPoly_map, map_list_sum, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, aeval_append_tm, map_one, one_mul, pow_one]

theorem aeval_pLin (c : Fin L.B) :
    aeval (Fin.append ψ φ) ((L.pLin c).toPoly (L.N + L.d)) =
      ∑ β, ψ (L.pv β c) * powE φ (L.Bs.get β) := by
  rw [pLin, toPoly_map, map_list_sum, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp only [Function.comp_apply, aeval_append_tm, map_one, one_mul, pow_one]

theorem aeval_bPart (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) :
    aeval (Fin.append ψ φ) ((L.bPart Gs b m K).toPoly (L.N + L.d)) =
      algebraMap ℚ S K * ψ L.sv ^ m * (Gs.map fun γ => algebraMap ℚ S (b γ) * powE φ γ).sum := by
  rw [bPart, toPoly_map, map_list_sum, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun γ _ => ?_
  simp only [Function.comp_apply, aeval_append_tm, map_mul]
  ring

/-- `F_coef(ψ, φ) = ∑_α C_α φ^α - ∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s}`, when the products are not cut. -/
theorem aeval_coefF (z : Fin L.n → Fin L.d → ℚ) {s Lb : ℕ} (hLb : (2 * L.d) ^ (2 * s) ≤ Lb) :
    aeval (Fin.append ψ φ) ((L.coefF z s Lb).toPoly (L.N + L.d)) =
      ∑ j, ψ (L.cv j) * powE φ (L.As.get j) -
        ∑ i, ψ (L.wv i) * (∑ a, (algebraMap ℚ S (z i a) - ψ (L.mv a)) * φ a) ^ (2 * s) := by
  rw [coefF, toPoly_append, toPoly_neg, toPoly_flatMap, map_add, map_neg, aeval_cLin,
    map_list_sum, List.map_map, sub_eq_add_neg]
  congr 2
  rw [Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, toPoly_prodRaw' (by simpa [wTerm] using hLb), List.map_cons,
    List.prod_cons, List.map_replicate, List.prod_replicate, map_mul, map_pow, aeval_wTerm,
    aeval_linRaw]

/-- `F_mom(ψ, φ) = K σ^m B̃(φ) - (∑_α C_α φ^α)^m - ∑_c (∑_β P_{βc} φ^β)²`, when the products are
not cut. -/
theorem aeval_momF {Gs : List (List ℕ)} {b : List ℕ → ℚ} {m : ℕ} {K : ℚ} {Lb : ℕ}
    (hA : L.A ^ m ≤ Lb) (hB : L.B ^ 2 ≤ Lb) :
    aeval (Fin.append ψ φ) ((L.momF Gs b m K Lb).toPoly (L.N + L.d)) =
      algebraMap ℚ S K * ψ L.sv ^ m * (Gs.map fun γ => algebraMap ℚ S (b γ) * powE φ γ).sum -
        (∑ j, ψ (L.cv j) * powE φ (L.As.get j)) ^ m -
        ∑ c, (∑ β, ψ (L.pv β c) * powE φ (L.Bs.get β)) ^ 2 := by
  rw [momF, toPoly_append, toPoly_append, toPoly_neg, toPoly_neg,
    toPoly_prodRaw_replicate (by rwa [length_cLin]), toPoly_flatMap, map_add, map_add, map_neg,
    map_neg, map_pow, aeval_bPart, aeval_cLin, map_list_sum, List.map_map,
    sub_eq_add_neg, sub_eq_add_neg]
  congr 2
  rw [Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rw [Function.comp_apply, toPoly_prodRaw_replicate (by rwa [length_pLin]), map_pow, aeval_pLin]

end Aeval

/-! ### Where the terms live: `v`-degrees and degrees -/

theorem vpart_tm_unit {k : Fin L.N} {e : ℕ} {α : List ℕ} {c : ℚ} (hα : α.length = L.d) :
    vpart L.N L.d (tm (unitExp L.N k e) α c).1 = α :=
  vpart_append_of_length (length_unitExp _ _ _) hα

/-- Every `v`-part of a term of `F_coef` is an exponent vector of degree at most `2s`. -/
theorem vpart_mem_coefF {s : ℕ} (memA : ∀ e, e ∈ L.As ↔ e.length = L.d ∧ e.sum ≤ 2 * s)
    (z : Fin L.n → Fin L.d → ℚ) (Lb : ℕ) : ∀ τ ∈ L.coefF z s Lb, vpart L.N L.d τ.1 ∈ L.As := by
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hτ
    rw [L.vpart_tm_unit ((memA _).1 (List.get_mem _ _)).1]
    exact List.get_mem _ _
  · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
    rw [he]
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hi
    rw [List.forall₂_cons_right_iff] at htup
    obtain ⟨t0, tup', h0, htup', rfl⟩ := htup
    obtain ⟨hlen, hmem⟩ := forall₂_replicate htup'
    refine (memA _).2 ⟨length_vpart _ _ _, ?_⟩
    rw [sum_vpart_prodTerm, List.map_cons, List.sum_cons]
    have h0' : (vpart L.N L.d t0.1).sum = 0 := by
      rw [wTerm, List.mem_singleton] at h0
      rw [h0, tm, sum_vpart_append (length_unitExp _ _ _)]
      simp
    have h1 : ∀ τ ∈ tup', (vpart L.N L.d τ.1).sum ≤ 1 := by
      intro τ hτ
      obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 (hmem τ hτ)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [tm, vpart_append_of_length (List.length_replicate ..) (length_unitExp _ _ _),
          sum_unitExp]
      · rw [L.vpart_tm_unit (length_unitExp _ _ _), sum_unitExp]
    have := sum_map_le tup' (fun τ => (vpart L.N L.d τ.1).sum) h1
    rw [hlen] at this
    omega

/-- Every `v`-part of a term of `F_mom` lies in `Gs`, the exponent vectors of degree at most
`2t`, when `m s ≤ t`. -/
theorem vpart_mem_momF {Gs : List (List ℕ)} {s t m : ℕ}
    (memA : ∀ e, e ∈ L.As ↔ e.length = L.d ∧ e.sum ≤ 2 * s)
    (memB : ∀ e, e ∈ L.Bs ↔ e.length = L.d ∧ e.sum ≤ t)
    (memG : ∀ e, e ∈ Gs ↔ e.length = L.d ∧ e.sum ≤ 2 * t) (hms : m * s ≤ t)
    (b : List ℕ → ℚ) (K : ℚ) (Lb : ℕ) : ∀ τ ∈ L.momF Gs b m K Lb, vpart L.N L.d τ.1 ∈ Gs := by
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · rcases List.mem_append.1 hτ with hτ | hτ
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hτ
      rw [L.vpart_tm_unit ((memG _).1 hγ).1]
      exact hγ
    · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
      rw [he]
      obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hτ'
      obtain ⟨hlen, hmem⟩ := forall₂_replicate htup
      refine (memG _).2 ⟨length_vpart _ _ _, ?_⟩
      rw [sum_vpart_prodTerm]
      have h1 : ∀ τ ∈ tup, (vpart L.N L.d τ.1).sum ≤ 2 * s := by
        intro τ hτ
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 (hmem τ hτ)
        rw [L.vpart_tm_unit ((memA _).1 (List.get_mem _ _)).1]
        exact ((memA _).1 (List.get_mem _ _)).2
      have := sum_map_le tup (fun τ => (vpart L.N L.d τ.1).sum) h1
      rw [hlen] at this
      nlinarith
  · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
    rw [he]
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hc
    obtain ⟨hlen, hmem⟩ := forall₂_replicate htup
    refine (memG _).2 ⟨length_vpart _ _ _, ?_⟩
    rw [sum_vpart_prodTerm]
    have h1 : ∀ τ ∈ tup, (vpart L.N L.d τ.1).sum ≤ t := by
      intro τ hτ
      obtain ⟨β, -, rfl⟩ := List.mem_map.1 (hmem τ hτ)
      rw [L.vpart_tm_unit ((memB _).1 (List.get_mem _ _)).1]
      exact ((memB _).1 (List.get_mem _ _)).2
    have := sum_map_le tup (fun τ => (vpart L.N L.d τ.1).sum) h1
    rw [hlen] at this
    omega

/-- Every term of `F_coef` has degree at most `2s + 1` in the program variables. -/
theorem udeg_coefF (z : Fin L.n → Fin L.d → ℚ) (s Lb : ℕ) :
    ∀ τ ∈ L.coefF z s Lb, udeg L.N τ.1 ≤ 2 * s + 1 := by
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hτ
    rw [udeg_tm]
    omega
  · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
    rw [he]
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hi
    rw [List.forall₂_cons_right_iff] at htup
    obtain ⟨t0, tup', h0, htup', rfl⟩ := htup
    obtain ⟨hlen, hmem⟩ := forall₂_replicate htup'
    rw [udeg_prodTerm (Nat.le_add_right _ _), List.map_cons, List.sum_cons]
    have h0' : udeg L.N t0.1 = 1 := by
      rw [wTerm, List.mem_singleton] at h0
      rw [h0, udeg_tm]
    have h1 : ∀ τ ∈ tup', udeg L.N τ.1 ≤ 1 := by
      intro τ hτ
      obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 (hmem τ hτ)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [udeg_tm0]
        omega
      · rw [udeg_tm]
    have := sum_map_le tup' (fun τ => udeg L.N τ.1) h1
    rw [hlen] at this
    omega

/-- Every term of `F_mom` has degree at most `max m 2` in the program variables. -/
theorem udeg_momF (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) (Lb : ℕ) :
    ∀ τ ∈ L.momF Gs b m K Lb, udeg L.N τ.1 ≤ max m 2 := by
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · rcases List.mem_append.1 hτ with hτ | hτ
    · obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hτ
      rw [udeg_tm]
      omega
    · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
      rw [he]
      obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hτ'
      obtain ⟨hlen, hmem⟩ := forall₂_replicate htup
      rw [udeg_prodTerm (Nat.le_add_right _ _)]
      have h1 : ∀ τ ∈ tup, udeg L.N τ.1 ≤ 1 := by
        intro τ hτ
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 (hmem τ hτ)
        rw [udeg_tm]
      have := sum_map_le tup (fun τ => udeg L.N τ.1) h1
      rw [hlen] at this
      omega
  · obtain ⟨τ', hτ', he⟩ := mem_neg hτ
    rw [he]
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hc
    obtain ⟨hlen, hmem⟩ := forall₂_replicate htup
    rw [udeg_prodTerm (Nat.le_add_right _ _)]
    have h1 : ∀ τ ∈ tup, udeg L.N τ.1 ≤ 1 := by
      intro τ hτ
      obtain ⟨β, -, rfl⟩ := List.mem_map.1 (hmem τ hτ)
      rw [udeg_tm]
    have := sum_map_le tup (fun τ => udeg L.N τ.1) h1
    rw [hlen] at this
    omega

/-- **`Coef_α` has degree at most `2s + 1`.** -/
theorem totalDegree_coefRaw_le (z : Fin L.n → Fin L.d → ℚ) (s Lb : ℕ) (α : List ℕ) :
    ((L.coefRaw z s Lb α).toPoly L.N).totalDegree ≤ 2 * s + 1 :=
  totalDegree_toPoly_le fun τ hτ => L.udeg_coefF z s Lb τ (coeffV_sublist _ _ _ _ hτ)

/-- **`Mom_γ` has degree at most `max m 2`.** -/
theorem totalDegree_momRaw_le (Gs : List (List ℕ)) (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) (Lb : ℕ)
    (γ : List ℕ) : ((L.momRaw Gs b m K Lb γ).toPoly L.N).totalDegree ≤ max m 2 :=
  totalDegree_toPoly_le fun τ hτ => L.udeg_momF Gs b m K Lb τ (coeffV_sublist _ _ _ _ hτ)

/-! ### The identities -/

/-- What the identities need: the lists of exponent vectors are the right ones, without
duplicates, and the products are not cut. -/
structure Good (Gs : List (List ℕ)) (s t m Lb : ℕ) : Prop where
  memA : ∀ e, e ∈ L.As ↔ e.length = L.d ∧ e.sum ≤ 2 * s
  memB : ∀ e, e ∈ L.Bs ↔ e.length = L.d ∧ e.sum ≤ t
  memG : ∀ e, e ∈ Gs ↔ e.length = L.d ∧ e.sum ≤ 2 * t
  nodupA : L.As.Nodup
  nodupB : L.Bs.Nodup
  nodupG : Gs.Nodup
  ms : m * s ≤ t
  lin : (2 * L.d) ^ (2 * s) ≤ Lb
  powA : L.A ^ m ≤ Lb
  powB : L.B ^ 2 ≤ Lb

variable {L} {Gs : List (List ℕ)} {s t m Lb : ℕ}

section Identities

variable {S : Type*} [CommRing S] [Algebra ℚ S] (ψ : Fin L.N → S) (φ : Fin L.d → S)

/-- **The coefficient identity**: `∑_α φ^α Coef_α = ∑_α C_α φ^α - ∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s}`, after
substituting `ψ` for the program variables, in every commutative `ℚ`-algebra. -/
theorem coef_identity (hL : L.Good Gs s t m Lb) (z : Fin L.n → Fin L.d → ℚ) :
    (L.As.map fun α => powE φ α * aeval ψ ((L.coefRaw z s Lb α).toPoly L.N)).sum =
      ∑ j, ψ (L.cv j) * powE φ (L.As.get j) -
        ∑ i, ψ (L.wv i) * (∑ a, (algebraMap ℚ S (z i a) - ψ (L.mv a)) * φ a) ^ (2 * s) := by
  rw [← L.aeval_coefF ψ φ z hL.lin]
  exact (aeval_append_eq_sum_coeffV ψ φ hL.nodupA (L.vpart_mem_coefF hL.memA z Lb)).symm

/-- **The moment identity**:
`∑_γ φ^γ Mom_γ = K σ^m B̃(φ) - (∑_α C_α φ^α)^m - ∑_c (∑_β P_{βc} φ^β)²` with
`B̃(φ) = ∑_γ b_γ φ^γ`, after substituting `ψ` for the program variables, in every commutative
`ℚ`-algebra. -/
theorem mom_identity (hL : L.Good Gs s t m Lb) (b : List ℕ → ℚ) (K : ℚ) :
    (Gs.map fun γ => powE φ γ * aeval ψ ((L.momRaw Gs b m K Lb γ).toPoly L.N)).sum =
      algebraMap ℚ S K * ψ L.sv ^ m * (Gs.map fun γ => algebraMap ℚ S (b γ) * powE φ γ).sum -
        (∑ j, ψ (L.cv j) * powE φ (L.As.get j)) ^ m -
        ∑ c, (∑ β, ψ (L.pv β c) * powE φ (L.Bs.get β)) ^ 2 := by
  rw [← L.aeval_momF ψ φ hL.powA hL.powB]
  exact (aeval_append_eq_sum_coeffV ψ φ hL.nodupG
    (L.vpart_mem_momF hL.memA hL.memB hL.memG hL.ms b K Lb)).symm

end Identities

/-- **The coefficient identity** for real polynomials `φ` in the program variables. -/
theorem coef_identity_X (hL : L.Good Gs s t m Lb) (z : Fin L.n → Fin L.d → ℚ)
    (φ : Fin L.d → MvPolynomial (Fin L.N) ℝ) :
    (L.As.map fun α => powE φ α * toReal ((L.coefRaw z s Lb α).toPoly L.N)).sum =
      ∑ j, X (L.cv j) * powE φ (L.As.get j) -
        ∑ i, X (L.wv i) * (∑ a, (C (z i a : ℝ) - X (L.mv a)) * φ a) ^ (2 * s) := by
  have h := coef_identity X φ hL z
  simp only [aeval_X_eq_toReal, MvPolynomial.algebraMap_apply] at h
  simpa using h

/-- **The moment identity** for real polynomials `φ` in the program variables. -/
theorem mom_identity_X (hL : L.Good Gs s t m Lb) (b : List ℕ → ℚ) (K : ℚ)
    (φ : Fin L.d → MvPolynomial (Fin L.N) ℝ) :
    (Gs.map fun γ => powE φ γ * toReal ((L.momRaw Gs b m K Lb γ).toPoly L.N)).sum =
      C (K : ℝ) * X L.sv ^ m * (Gs.map fun γ => C (b γ : ℝ) * powE φ γ).sum -
        (∑ j, X (L.cv j) * powE φ (L.As.get j)) ^ m -
        ∑ c, (∑ β, X (L.pv β c) * powE φ (L.Bs.get β)) ^ 2 := by
  have h := mom_identity X φ hL b K
  simp only [aeval_X_eq_toReal, MvPolynomial.algebraMap_apply] at h
  simpa using h

/-- **`Coef_α` at a point** `y`: the coefficient of `v^α` in
`∑_α C_α v^α - ∑ᵢ wᵢ ⟨zᵢ - μ, v⟩^{2s}` at `y`. -/
theorem eval_coefRaw (hL : L.Good Gs s t m Lb) (z : Fin L.n → Fin L.d → ℚ) (y : Fin L.N → ℝ)
    {α : List ℕ} (hα : α ∈ L.As) :
    eval y (toReal ((L.coefRaw z s Lb α).toPoly L.N)) =
      (∑ j, C (y (L.cv j)) * powE X (L.As.get j) -
        ∑ i, C (y (L.wv i)) * (∑ a, (C (z i a : ℝ) - C (y (L.mv a))) * X a) ^ (2 * s) :
          MvPolynomial (Fin L.d) ℝ).coeff (Mono.toFinsupp L.d α) := by
  rw [coefRaw, eval_coeffV y hL.nodupA (fun e he => ((hL.memA e).1 he).1)
    (L.vpart_mem_coefF hL.memA z Lb) hα, L.aeval_coefF _ _ z hL.lin]
  simp [MvPolynomial.algebraMap_apply]

/-- **`Mom_γ` at a point** `y`: the coefficient of `v^γ` in
`K σ^m B̃(v) - (∑_α C_α v^α)^m - ∑_c (∑_β P_{βc} v^β)²` at `y`. -/
theorem eval_momRaw (hL : L.Good Gs s t m Lb) (b : List ℕ → ℚ) (K : ℚ) (y : Fin L.N → ℝ)
    {γ : List ℕ} (hγ : γ ∈ Gs) :
    eval y (toReal ((L.momRaw Gs b m K Lb γ).toPoly L.N)) =
      (C ((K : ℝ) * y L.sv ^ m) * (Gs.map fun γ' => C (b γ' : ℝ) * powE X γ').sum -
        (∑ j, C (y (L.cv j)) * powE X (L.As.get j)) ^ m -
        ∑ c, (∑ β, C (y (L.pv β c)) * powE X (L.Bs.get β)) ^ 2 :
          MvPolynomial (Fin L.d) ℝ).coeff (Mono.toFinsupp L.d γ) := by
  rw [momRaw, eval_coeffV y hL.nodupG (fun e he => ((hL.memG e).1 he).1)
    (L.vpart_mem_momF hL.memA hL.memB hL.memG hL.ms b K Lb) hγ,
    L.aeval_momF _ _ hL.powA hL.powB]
  simp [MvPolynomial.algebraMap_apply]

end Lay

/-! ### The constraints -/

namespace Lay

variable (L : Lay) (z : Fin L.n → Fin L.d → ℚ) (Gs : List (List ℕ)) (b : List ℕ → ℚ)
  (s m : ℕ) (K Bd : ℚ) (Lb : ℕ)

theorem ballRaw_mem : L.ballRaw Bd ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))

theorem boolRaw_mem (i : Fin L.n) : L.boolRaw i ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_cons_self⟩))))

theorem neg_boolRaw_mem (i : Fin L.n) : neg (L.boolRaw i) ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_flatMap.2 ⟨i, List.mem_finRange i, by simp⟩))))

theorem sumRaw_mem : L.sumRaw ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))

theorem neg_sumRaw_mem : neg L.sumRaw ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))

theorem coefRaw_mem {α : List ℕ} (hα : α ∈ L.As) :
    L.coefRaw z s Lb α ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨α, hα, by simp⟩))

theorem neg_coefRaw_mem {α : List ℕ} (hα : α ∈ L.As) :
    neg (L.coefRaw z s Lb α) ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨α, hα, by simp⟩))

theorem momRaw_mem {γ : List ℕ} (hγ : γ ∈ Gs) :
    L.momRaw Gs b m K Lb γ ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨γ, hγ, by simp⟩)

theorem neg_momRaw_mem {γ : List ℕ} (hγ : γ ∈ Gs) :
    neg (L.momRaw Gs b m K Lb γ) ∈ L.constraints z Gs b s m K Bd Lb :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨γ, hγ, by simp⟩)

variable {L z Gs b s m K Bd Lb} in
/-- **The constraints, case by case.** -/
theorem cases_of_mem_constraints {r : RawPoly} (hr : r ∈ L.constraints z Gs b s m K Bd Lb) :
    r = L.ballRaw Bd ∨ (∃ i, r = L.boolRaw i ∨ r = neg (L.boolRaw i)) ∨
      (r = L.sumRaw ∨ r = neg L.sumRaw) ∨
      (∃ α ∈ L.As, r = L.coefRaw z s Lb α ∨ r = neg (L.coefRaw z s Lb α)) ∨
      ∃ γ ∈ Gs, r = L.momRaw Gs b m K Lb γ ∨ r = neg (L.momRaw Gs b m K Lb γ) := by
  simp only [constraints, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    true_and, List.not_mem_nil, or_false] at hr
  rcases hr with (((h | ⟨i, h⟩) | h) | ⟨α, hα, h⟩) | ⟨γ, hγ, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨i, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨α, hα, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨γ, hγ, h⟩)))

variable {L z Gs b s m K Bd Lb} in
/-- **Every constraint has degree at most `max (2s + 1) (max m 2)`.** -/
theorem totalDegree_le_of_mem {r : RawPoly} (hr : r ∈ L.constraints z Gs b s m K Bd Lb) :
    (r.toPoly L.N).totalDegree ≤ max (2 * s + 1) (max m 2) := by
  have hneg : ∀ p : RawPoly, (neg p).toPoly L.N = -p.toPoly L.N := toPoly_neg _
  rcases cases_of_mem_constraints hr with rfl | ⟨i, rfl | rfl⟩ | (rfl | rfl) |
    ⟨α, -, rfl | rfl⟩ | ⟨γ, -, rfl | rfl⟩
  · refine totalDegree_toPoly_le fun τ hτ => ?_
    rcases List.mem_cons.1 hτ with rfl | hτ
    · simp [udeg, List.getD_eq_getElem?_getD]
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hτ
      rw [udeg_unitExp]
      omega
  · refine totalDegree_toPoly_le fun τ hτ => ?_
    simp only [boolRaw, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl <;> rw [udeg_unitExp] <;> omega
  · rw [hneg, totalDegree_neg]
    refine totalDegree_toPoly_le fun τ hτ => ?_
    simp only [boolRaw, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl <;> rw [udeg_unitExp] <;> omega
  · refine totalDegree_toPoly_le fun τ hτ => ?_
    rcases List.mem_cons.1 hτ with rfl | hτ
    · rw [udeg_unitExp]
      omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hτ
      rw [udeg_unitExp]
      omega
  · rw [hneg, totalDegree_neg]
    refine totalDegree_toPoly_le fun τ hτ => ?_
    rcases List.mem_cons.1 hτ with rfl | hτ
    · rw [udeg_unitExp]
      omega
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hτ
      rw [udeg_unitExp]
      omega
  · exact (L.totalDegree_coefRaw_le z s Lb α).trans (le_max_left _ _)
  · rw [hneg, totalDegree_neg]
    exact (L.totalDegree_coefRaw_le z s Lb α).trans (le_max_left _ _)
  · exact (L.totalDegree_momRaw_le Gs b m K Lb γ).trans (le_max_right _ _)
  · rw [hneg, totalDegree_neg]
    exact (L.totalDegree_momRaw_le Gs b m K Lb γ).trans (le_max_right _ _)

end Lay

/-! ### The problem: no cuts, the system, validity, the objective -/

/-- **Nothing is cut** by the budget `Lb` when `m s ≤ t`, `s ≤ t` and `(2d + 2)^{2t} ≤ Lb`. -/
def Fits (d s t m Lb : ℕ) : Prop := m * s ≤ t ∧ s ≤ t ∧ (2 * d + 2) ^ (2 * t) ≤ Lb

theorem allB_eq_of_fits {d s t m Lb D : ℕ} (h : Fits d s t m Lb) (hD : D ≤ 2 * t) :
    Mono.allB Lb d D = Mono.all d D := by
  obtain ⟨-, -, hLb⟩ := h
  have h1 : (d + 1) ^ D ≤ (2 * d + 2) ^ (2 * t) :=
    (Nat.pow_le_pow_right (by omega) hD).trans (Nat.pow_le_pow_left (by omega) _)
  have h2 : D ≤ (2 * d + 2) ^ (2 * t) :=
    hD.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _))
  exact Mono.allB_eq (h2.trans hLb) (h1.trans hLb)

/-- **The layout of the problem satisfies the hypotheses of the identities** when nothing is
cut. -/
theorem good_lay {n d s t m Lb : ℕ} (h : Fits d s t m Lb) :
    (lay n d s t Lb).Good (gams d t Lb) s t m Lb := by
  have hA : Mono.allB Lb d (2 * s) = Mono.all d (2 * s) :=
    allB_eq_of_fits h (by have := h.2.1; omega)
  have hB : Mono.allB Lb d t = Mono.all d t := allB_eq_of_fits h (by omega)
  have hG : Mono.allB Lb d (2 * t) = Mono.all d (2 * t) := allB_eq_of_fits h le_rfl
  obtain ⟨hms, hst, hLb⟩ := h
  have hd : (d + 1) ^ (2 * t) ≤ Lb := (Nat.pow_le_pow_left (by omega) _).trans hLb
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, ?_, ?_, ?_, hms, ?_, ?_, ?_⟩
  · change e ∈ Mono.allB Lb d (2 * s) ↔ _
    rw [hA, Mono.mem_all]
    exact Iff.rfl
  · change e ∈ Mono.allB Lb d t ↔ _
    rw [hB, Mono.mem_all]
    exact Iff.rfl
  · change e ∈ Mono.allB Lb d (2 * t) ↔ _
    rw [hG, Mono.mem_all]
    exact Iff.rfl
  · change (Mono.allB Lb d (2 * s)).Nodup
    rw [hA]
    exact Mono.nodup_all _ _
  · change (Mono.allB Lb d t).Nodup
    rw [hB]
    exact Mono.nodup_all _ _
  · change (Mono.allB Lb d (2 * t)).Nodup
    rw [hG]
    exact Mono.nodup_all _ _
  · change (2 * d) ^ (2 * s) ≤ Lb
    exact (Nat.pow_le_pow_left (by omega) _).trans
      ((Nat.pow_le_pow_right (by omega) (by omega)).trans hLb)
  · change (Mono.allB Lb d (2 * s)).length ^ m ≤ Lb
    rw [hA]
    calc (Mono.all d (2 * s)).length ^ m ≤ ((d + 1) ^ (2 * s)) ^ m :=
          Nat.pow_le_pow_left (Mono.length_all_le _ _) _
      _ = (d + 1) ^ (2 * s * m) := (pow_mul _ _ _).symm
      _ ≤ (d + 1) ^ (2 * t) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ ≤ Lb := hd
  · change (Mono.allB Lb d t).length ^ 2 ≤ Lb
    rw [hB]
    calc (Mono.all d t).length ^ 2 ≤ ((d + 1) ^ t) ^ 2 :=
          Nat.pow_le_pow_left (Mono.length_all_le _ _) _
      _ = (d + 1) ^ (2 * t) := by rw [← pow_mul, mul_comm]
      _ ≤ Lb := hd

section System

variable {n d : ℕ} (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (s t m : ℕ) (K Bd : ℚ) (Lb : ℕ)

/-- The constraints of the problem as real polynomials. -/
noncomputable abbrev realSystem : System (Fin (lay n d s t Lb).N) ℝ :=
  (problem z b s t m K Bd Lb).system.map toReal

variable {z b s t m K Bd Lb}

theorem system_problem :
    (problem z b s t m K Bd Lb).system =
      ((lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb).map
        (RawPoly.toPoly (lay n d s t Lb).N) :=
  rfl

theorem mem_system {r : RawPoly}
    (hr : r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb) :
    r.toPoly (lay n d s t Lb).N ∈ (problem z b s t m K Bd Lb).system :=
  List.mem_map.2 ⟨r, hr, rfl⟩

theorem mem_realSystem {r : RawPoly}
    (hr : r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb) :
    toReal (r.toPoly (lay n d s t Lb).N) ∈ realSystem z b s t m K Bd Lb :=
  List.mem_map.2 ⟨_, mem_system hr, rfl⟩

theorem toReal_neg' {σ : Type*} (p : MvPolynomial σ ℚ) : toReal (-p) = -toReal p :=
  map_neg _ _

/-- An equality `r = 0` given as the pair `r ≥ 0`, `-r ≥ 0`. -/
theorem hasEq_of_mem {r : RawPoly}
    (h₁ : r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb)
    (h₂ : neg r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb) :
    HasEq (realSystem z b s t m K Bd Lb) (toReal (r.toPoly (lay n d s t Lb).N)) := by
  refine ⟨mem_realSystem h₁, ?_⟩
  have := mem_realSystem h₂
  rwa [toPoly_neg, toReal_neg'] at this

/-- **The ball** `Bd - ∑ₖ xₖ² ≥ 0` is a constraint. -/
theorem ball_mem_system :
    (C Bd - ∑ k : Fin (lay n d s t Lb).N, X k ^ 2) ∈ (problem z b s t m K Bd Lb).system := by
  have := mem_system (z := z) (b := b) (s := s) (t := t) (m := m) (K := K) (Lb := Lb)
    ((lay n d s t Lb).ballRaw_mem z (gams d t Lb) b s m K Bd Lb)
  rwa [Lay.toPoly_ballRaw] at this

theorem ball_mem_realSystem :
    (C (Bd : ℝ) - ∑ k : Fin (lay n d s t Lb).N, X k ^ 2) ∈ realSystem z b s t m K Bd Lb := by
  have := mem_realSystem (z := z) (b := b) (s := s) (t := t) (m := m) (K := K) (Lb := Lb)
    ((lay n d s t Lb).ballRaw_mem z (gams d t Lb) b s m K Bd Lb)
  rw [Lay.toPoly_ballRaw] at this
  simpa [toReal] using this

/-- **Booleanity of the weights** `wᵢ² = wᵢ` (only of the weights). -/
theorem hasEq_bool (i : Fin n) :
    HasEq (realSystem z b s t m K Bd Lb)
      (X ((lay n d s t Lb).wv i) ^ 2 - X ((lay n d s t Lb).wv i)) := by
  have := hasEq_of_mem ((lay n d s t Lb).boolRaw_mem z (gams d t Lb) b s m K Bd Lb i)
    ((lay n d s t Lb).neg_boolRaw_mem z (gams d t Lb) b s m K Bd Lb i)
  rw [Lay.toPoly_boolRaw (lay n d s t Lb) i] at this
  simpa [toReal] using this

/-- **The size** `σ = ∑ᵢ wᵢ`. -/
theorem hasEq_sum :
    HasEq (realSystem z b s t m K Bd Lb)
      (X (lay n d s t Lb).sv - ∑ i, X ((lay n d s t Lb).wv i)) := by
  have := hasEq_of_mem ((lay n d s t Lb).sumRaw_mem z (gams d t Lb) b s m K Bd Lb)
    ((lay n d s t Lb).neg_sumRaw_mem z (gams d t Lb) b s m K Bd Lb)
  rw [Lay.toPoly_sumRaw] at this
  simpa [toReal] using this

/-- **The coefficient constraints** `Coef_α = 0`, `|α| ≤ 2s`. -/
theorem hasEq_coef {α : List ℕ} (hα : α ∈ (lay n d s t Lb).As) :
    HasEq (realSystem z b s t m K Bd Lb)
      (toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N)) :=
  hasEq_of_mem ((lay n d s t Lb).coefRaw_mem z (gams d t Lb) b s m K Bd Lb hα)
    ((lay n d s t Lb).neg_coefRaw_mem z (gams d t Lb) b s m K Bd Lb hα)

/-- **The moment constraints** `Mom_γ = 0`, `|γ| ≤ 2t`. -/
theorem hasEq_mom {γ : List ℕ} (hγ : γ ∈ gams d t Lb) :
    HasEq (realSystem z b s t m K Bd Lb)
      (toReal (((lay n d s t Lb).momRaw (gams d t Lb) b m K Lb γ).toPoly (lay n d s t Lb).N)) :=
  hasEq_of_mem ((lay n d s t Lb).momRaw_mem z (gams d t Lb) b s m K Bd Lb hγ)
    ((lay n d s t Lb).neg_momRaw_mem z (gams d t Lb) b s m K Bd Lb hγ)

/-- **Every constraint of the problem has degree at most `max (2s + 1) (max m 2)`.** -/
theorem totalDegree_le_of_mem_system {f : MvPolynomial (Fin (lay n d s t Lb).N) ℚ}
    (hf : f ∈ (problem z b s t m K Bd Lb).system) :
    f.totalDegree ≤ max (2 * s + 1) (max m 2) := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
  exact Lay.totalDegree_le_of_mem hr

/-- **Validity from a feasible point**: if `t ≥ 1` and a real point `y` satisfies the ball, the
Boolean and size equalities and the coefficient and moment equalities, the problem is valid for
the solver. -/
theorem valid_of_eval (ht : 1 ≤ t) (y : Fin (lay n d s t Lb).N → ℝ)
    (hball : ∑ k, y k ^ 2 ≤ Bd)
    (hbool : ∀ i, y ((lay n d s t Lb).wv i) ^ 2 = y ((lay n d s t Lb).wv i))
    (hsum : y (lay n d s t Lb).sv = ∑ i, y ((lay n d s t Lb).wv i))
    (hcoef : ∀ α ∈ (lay n d s t Lb).As,
      eval y (toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N)) = 0)
    (hmom : ∀ γ ∈ gams d t Lb,
      eval y (toReal (((lay n d s t Lb).momRaw (gams d t Lb) b m K Lb γ).toPoly
        (lay n d s t Lb).N)) = 0) :
    (problem z b s t m K Bd Lb).Valid := by
  refine ⟨⟨32 * t, show 64 * t = 32 * t + 32 * t by ring⟩, show 2 ≤ 64 * t by omega, ?_,
    ⟨Bd, ball_mem_system⟩, y, ?_⟩
  · intro q hq
    simp only [problem, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    refine (totalDegree_toPoly_le (D := 1) fun τ hτ => ?_).trans (show 1 ≤ 64 * t by omega)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hτ
    change udeg (lay n d s t Lb).N (unitExp (lay n d s t Lb).N ((lay n d s t Lb).wv i) 1) ≤ 1
    rw [udeg_unitExp]
  · intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
    change r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb at hr
    change 0 ≤ eval y (toReal (r.toPoly (lay n d s t Lb).N))
    have hneg : ∀ p : RawPoly, eval y (toReal ((neg p).toPoly (lay n d s t Lb).N)) =
        -eval y (toReal (p.toPoly (lay n d s t Lb).N)) := fun p => by
      rw [toPoly_neg, toReal_neg', eval_neg]
    rcases Lay.cases_of_mem_constraints hr with rfl | ⟨i, rfl | rfl⟩ | (rfl | rfl) |
      ⟨α, hα, rfl | rfl⟩ | ⟨γ, hγ, rfl | rfl⟩
    · rw [Lay.toPoly_ballRaw]
      simp [toReal]
      linarith
    · rw [Lay.toPoly_boolRaw]
      simp [toReal, hbool]
    · rw [hneg, Lay.toPoly_boolRaw]
      simp [toReal, hbool]
    · rw [Lay.toPoly_sumRaw]
      simp [toReal, hsum]
    · rw [hneg, Lay.toPoly_sumRaw]
      simp [toReal, hsum]
    · rw [hcoef α hα]
    · rw [hneg, hcoef α hα, neg_zero]
    · rw [hmom γ hγ]
    · rw [hneg, hmom γ hγ, neg_zero]

/-- **The objective** `Ẽ[q₀] = -∑ᵢ Ẽ[wᵢ]`. -/
theorem objective_eq {ℓ : ℕ} (E : PseudoExpectation (Fin (lay n d s t Lb).N) ℓ) :
    (problem z b s t m K Bd Lb).objective E = -∑ i, E (X ((lay n d s t Lb).wv i)) := by
  change E (toReal ((lay n d s t Lb).objRaw.toPoly (lay n d s t Lb).N)) +
    (([] : List RawPoly).map fun q => E (toReal (q.toPoly (lay n d s t Lb).N)) ^ 2).sum = _
  rw [Lay.toPoly_objRaw, toReal_neg', toReal_sum, List.map_nil, List.sum_nil, add_zero,
    PseudoExpectation.map_neg, PseudoExpectation.map_sum]
  simp [toReal]

end System

/-! ### The coefficients of `B̃` from data -/

section BTilde

variable {nY d : ℕ} (Y : Fin nY → Fin d → ℚ)

/-- `⟨Yⱼ, v⟩` in the variables `v`. -/
def yLin (j : Fin nY) : RawPoly := (List.finRange d).map fun a : Fin d => (unitExp d a 1, Y j a)

/-- `B̃(v) = (n t^t)⁻¹ ∑ⱼ ⟨Yⱼ, v⟩^{2t}`, in the variables `v`, for `n` points `Yⱼ`. -/
def bRaw (t Lb : ℕ) : RawPoly :=
  (List.finRange nY).flatMap fun j =>
    smul ((nY : ℚ) * t ^ t)⁻¹ (prodRaw d Lb (List.replicate (2 * t) (yLin Y j)))

/-- The coefficients of `B̃`: `b_γ = (n t^t)⁻¹ ∑ⱼ multinom(γ) Yⱼ^γ`, read off `bRaw`. -/
def bOf (t Lb : ℕ) (γ : List ℕ) : ℚ := SoS.Poly.coeff d (bRaw Y t Lb) γ

theorem expo_mem_bRaw {t Lb : ℕ} {Gs : List (List ℕ)}
    (memG : ∀ e, e ∈ Gs ↔ e.length = d ∧ e.sum ≤ 2 * t) :
    ∀ τ ∈ bRaw Y t Lb, expo d τ.1 ∈ Gs := by
  intro τ hτ
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hτ
  obtain ⟨τ', hτ', he⟩ := mem_smul hj
  rw [he]
  obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hτ'
  obtain ⟨hlen, hmem⟩ := forall₂_replicate htup
  refine (memG _).2 ⟨length_expo _ _, ?_⟩
  have hsum : (expo d (prodTerm d tup).1).sum =
      (tup.map fun τ => ((List.range d).map fun i => τ.1.getD i 0).sum).sum :=
    sum_getD_sumE (List.range d) (fun i hi => List.mem_range.1 hi) tup
  rw [hsum]
  have h1 : ∀ τ ∈ tup, ((List.range d).map fun i => τ.1.getD i 0).sum ≤ 1 := by
    intro τ hτ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (hmem τ hτ)
    rw [map_getD_range (length_unitExp _ _ _), sum_unitExp]
  have := sum_map_le tup (fun τ => ((List.range d).map fun i => τ.1.getD i 0).sum) h1
  rw [hlen] at this
  omega

/-- **`B̃` from its coefficients**: `∑_{γ ∈ Gs} b_γ φ^γ = (n t^t)⁻¹ ∑ⱼ ⟨Yⱼ, φ⟩^{2t}`, when `Gs`
lists the exponent vectors of degree at most `2t` once each and nothing is cut. -/
theorem sum_bOf_mul_powE {S : Type*} [CommRing S] [Algebra ℚ S] {t Lb : ℕ}
    (hLb : d ^ (2 * t) ≤ Lb) {Gs : List (List ℕ)}
    (memG : ∀ e, e ∈ Gs ↔ e.length = d ∧ e.sum ≤ 2 * t) (hG : Gs.Nodup) (φ : Fin d → S) :
    (Gs.map fun γ => algebraMap ℚ S (bOf Y t Lb γ) * powE φ γ).sum =
      algebraMap ℚ S ((nY : ℚ) * t ^ t)⁻¹ * ∑ j, (∑ a, algebraMap ℚ S (Y j a) * φ a) ^ (2 * t) := by
  rw [show (Gs.map fun γ => algebraMap ℚ S (bOf Y t Lb γ) * powE φ γ) =
      Gs.map fun γ => algebraMap ℚ S (SoS.Poly.coeff d (bRaw Y t Lb) γ) * powE φ γ from rfl,
    sum_coeff_mul_powE φ hG (expo_mem_bRaw Y memG), bRaw, toPoly_flatMap, map_list_sum,
    List.map_map, Finset.mul_sum, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have hlin : aeval φ ((yLin Y j).toPoly d) = ∑ a, algebraMap ℚ S (Y j a) * φ a := by
    rw [yLin, toPoly_map, map_list_sum, List.map_map, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [Function.comp_apply, termPoly_unitExp]
    simp
  rw [Function.comp_apply, toPoly_smul, toPoly_prodRaw_replicate (by simpa [yLin] using hLb),
    map_mul, map_pow, aeval_C, hlin]

/-- `sum_bOf_mul_powE` for the problem, when nothing is cut. -/
theorem sum_bOf_mul_powE_of_fits {S : Type*} [CommRing S] [Algebra ℚ S] {s t m Lb : ℕ}
    (h : Fits d s t m Lb) (φ : Fin d → S) :
    ((gams d t Lb).map fun γ => algebraMap ℚ S (bOf Y t Lb γ) * powE φ γ).sum =
      algebraMap ℚ S ((nY : ℚ) * t ^ t)⁻¹ * ∑ j, (∑ a, algebraMap ℚ S (Y j a) * φ a) ^ (2 * t) :=
  sum_bOf_mul_powE Y ((Nat.pow_le_pow_left (by omega) _).trans h.2.2)
    ((good_lay (n := 0) h).memG) ((good_lay (n := 0) h).nodupG) φ

end BTilde

end BS23.SmallRadius
