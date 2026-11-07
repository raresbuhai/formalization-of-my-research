module

public import Background.SumOfSquares.Algorithm.Oracle
public import Background.Ellipsoid

/-!
# The ellipsoid loop, on lists

The rounded step of the ellipsoid method (`Ellipsoid.stepCenter`, `Ellipsoid.stepShape`) on lists
of rationals, and the loop that runs it and keeps the best center declared feasible.

* `SoS.Loop.stepL`: the step. The square root `√(aᵀPa)` is avoided by writing
  `(P a)ᵢ / √(aᵀPa) = sign((P a)ᵢ) √((P a)ᵢ² / aᵀPa)` and taking that square root from below
  with an integer square root (`SoS.Loop.sqrtP`); every number is then rounded down to a
  multiple of `2^-p` (`SoS.Loop.roundP`) and clamped to `[-B, B]` (`SoS.Loop.clamp`). The
  clamps keep the numbers small on every input; on the inputs that matter they never act, and
  the step is within `2 / 2^p` of the exact one (`SoS.Loop.stepL_spec`).
* `SoS.Loop.loopStep`: one step of the loop. It asks the oracle at the center, remembers the
  center if it is declared feasible with the smallest objective so far, and steps.
  `SoS.Loop.best_spec`: after `K` steps, the remembered center is declared feasible and has the
  smallest objective among the centers declared feasible.
-/

@[expose] public section

namespace SoS.Loop

open Matrix

/-! ### Rounding, clamping and square roots -/

/-- `x` rounded down to a multiple of `2^-p`. -/
def roundP (p : ℕ) (x : ℚ) : ℚ := (⌊x * 2 ^ p⌋ : ℚ) / 2 ^ p

theorem abs_roundP_sub_le (p : ℕ) (x : ℚ) : |roundP p x - x| ≤ 1 / 2 ^ p := by
  have h2 : (0 : ℚ) < 2 ^ p := by positivity
  have h1 := Int.floor_le (x * 2 ^ p)
  have h3 := Int.lt_floor_add_one (x * 2 ^ p)
  have hr : roundP p x - x = ((⌊x * 2 ^ p⌋ : ℚ) - x * 2 ^ p) / 2 ^ p := by
    rw [roundP]
    field_simp
  rw [hr, abs_div, abs_of_pos h2, div_le_div_iff_of_pos_right h2, abs_le]
  constructor <;> linarith

/-- `x` clamped to `[-B, B]`. -/
def clamp (B x : ℚ) : ℚ := max (-B) (min B x)

theorem clamp_of_abs_le {B x : ℚ} (h : |x| ≤ B) : clamp B x = x := by
  rw [abs_le] at h
  rw [clamp, min_eq_right h.2, max_eq_right h.1]

theorem abs_clamp_le {B : ℚ} (hB : 0 ≤ B) (x : ℚ) : |clamp B x| ≤ B := by
  rw [clamp, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- `√r` from below, within `2^-p`, for `r ≥ 0`: `⌊√⌊r 4^p⌋⌋ / 2^p`. -/
def sqrtP (p : ℕ) (r : ℚ) : ℚ := (Nat.sqrt (⌊r * 4 ^ p⌋.natAbs) : ℚ) / 2 ^ p

theorem abs_sqrtP_sub_le (p : ℕ) {r : ℚ} (hr : 0 ≤ r) :
    |(sqrtP p r : ℝ) - Real.sqrt r| ≤ 1 / 2 ^ p := by
  set M := ⌊r * 4 ^ p⌋.natAbs
  set s := Nat.sqrt M
  have h4 : (4 : ℚ) ^ p = (2 ^ p) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hM0 : 0 ≤ ⌊r * 4 ^ p⌋ := Int.floor_nonneg.2 (by positivity)
  have hMcast : (M : ℚ) = (⌊r * 4 ^ p⌋ : ℚ) := by
    simp only [M]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hM0)]
  have hMle : (M : ℝ) ≤ (r : ℝ) * (2 ^ p) ^ 2 := by
    have : (M : ℚ) ≤ r * 4 ^ p := by rw [hMcast]; exact Int.floor_le _
    rw [h4] at this
    exact_mod_cast this
  have hMlt : (r : ℝ) * (2 ^ p) ^ 2 < M + 1 := by
    have : r * 4 ^ p < M + 1 := by rw [hMcast]; exact Int.lt_floor_add_one _
    rw [h4] at this
    exact_mod_cast this
  have hs1 : ((s : ℝ)) ^ 2 ≤ M := by exact_mod_cast Nat.sqrt_le' M
  have hs2 : (M : ℝ) + 1 ≤ ((s : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' M
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set t := Real.sqrt r * 2 ^ p
  have ht0 : 0 ≤ t := by positivity
  have htsq : t ^ 2 = (r : ℝ) * (2 ^ p) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hr)]
  have hst : (s : ℝ) ≤ t := by
    rw [← sq_le_sq₀ (by positivity) ht0, htsq]
    linarith
  have hts : t < s + 1 := by
    rw [← sq_lt_sq₀ ht0 (by positivity), htsq]
    linarith
  have hsq : (sqrtP p r : ℝ) - Real.sqrt r = ((s : ℝ) - t) / 2 ^ p := by
    simp only [sqrtP, s, t, M]
    push_cast
    field_simp
  rw [hsq, abs_div, abs_of_pos hp, div_le_div_iff_of_pos_right hp, abs_le]
  constructor <;> linarith

/-! ### Vectors and matrices -/

/-- The vector of a list. -/
def vecL (N : ℕ) (l : List ℚ) : Fin N → ℝ := fun i => (l.getD i 0 : ℝ)

/-- The matrix of a list of rows. -/
def matL (N : ℕ) (P : List (List ℚ)) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ((P.getD i []).getD j 0 : ℝ)

/-- The dot product of lists. -/
def dotL (u v : List ℚ) : ℚ := (List.zipWith (· * ·) u v).sum

/-- The product of a matrix and a vector. -/
def mulVecL (P : List (List ℚ)) (a : List ℚ) : List ℚ := P.map fun row => dotL row a

theorem dotL_eq : ∀ {N : ℕ} {u v : List ℚ}, u.length = N → v.length = N →
    (dotL u v : ℝ) = vecL N u ⬝ᵥ vecL N v
  | 0, [], [], _, _ => by simp [dotL, dotProduct]
  | 0, _ :: _, _, hu, _ => absurd hu (by simp)
  | 0, [], _ :: _, _, hv => absurd hv (by simp)
  | N + 1, [], _, hu, _ => absurd hu (by simp)
  | N + 1, _ :: _, [], _, hv => absurd hv (by simp)
  | N + 1, x :: u, y :: v, hu, hv => by
    have ih := dotL_eq (N := N) (u := u) (v := v) (by simpa using hu) (by simpa using hv)
    rw [dotProduct, Fin.sum_univ_succ]
    simp only [dotL, List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul] at ih ⊢
    rw [ih, dotProduct]
    simp [vecL]

theorem vecL_mulVecL {N : ℕ} {P : List (List ℚ)} {a : List ℚ} (hP : P.length = N)
    (hrows : ∀ row ∈ P, row.length = N) (ha : a.length = N) :
    vecL N (mulVecL P a) = matL N P *ᵥ vecL N a := by
  ext i
  have hi : (i : ℕ) < P.length := hP ▸ i.2
  rw [vecL, mulVecL, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    dotL_eq (hrows _ (List.getElem_mem hi)) ha, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (P[(i : ℕ)].getD j 0 : ℝ) * _ = ((P.getD i []).getD j 0 : ℝ) * _
  rw [List.getD_eq_getElem _ _ hi]

/-! ### The step -/

/-- The sign of `x`, as `±1`. -/
def sgn (x : ℚ) : ℚ := if 0 ≤ x then 1 else -1

/-- **The rounded step** in dimension `N`, at precision `2^-p`, clamped to `[-B, B]`, cutting at
the center `c` by `a`. -/
def stepL (N p : ℕ) (B : ℚ) (c a : List ℚ) (P : List (List ℚ)) : List ℚ × List (List ℚ) :=
  ((c.zip (mulVecL P a)).map fun x => clamp B (roundP p (x.1 - 1 / (4 * N) *
      (sgn x.2 * sqrtP p (x.2 ^ 2 / dotL a (mulVecL P a))))),
    (P.zip (mulVecL P a)).map fun x => (x.1.zip (mulVecL P a)).map fun y =>
      clamp B (roundP p ((1 + 4 * (1 / (4 * N)) ^ 2) *
        (y.1 - 2 * (1 / (4 * N)) / dotL a (mulVecL P a) * (x.2 * y.2)))))

theorem length_stepL_fst {N p : ℕ} {B : ℚ} {c a : List ℚ} {P : List (List ℚ)}
    (hc : c.length = N) (hP : P.length = N) : (stepL N p B c a P).1.length = N := by
  simp [stepL, mulVecL, hc, hP]

theorem length_stepL_snd {N p : ℕ} {B : ℚ} {c a : List ℚ} {P : List (List ℚ)}
    (hP : P.length = N) : (stepL N p B c a P).2.length = N := by
  simp [stepL, mulVecL, hP]

theorem length_row_stepL {N p : ℕ} {B : ℚ} {c a : List ℚ} {P : List (List ℚ)}
    (hP : P.length = N) (hrows : ∀ row ∈ P, row.length = N) :
    ∀ row ∈ (stepL N p B c a P).2, row.length = N := by
  intro row hrow
  simp only [stepL, List.mem_map] at hrow
  obtain ⟨x, hx, rfl⟩ := hrow
  have := hrows _ (List.of_mem_zip hx).1
  simp [mulVecL, this, hP]

theorem sgn_mul_sqrt {x q : ℝ} (hq : 0 < q) :
    (if 0 ≤ x then 1 else -1) * Real.sqrt (x ^ 2 / q) = x / Real.sqrt q := by
  rw [Real.sqrt_div' _ hq.le, Real.sqrt_sq_eq_abs, ← mul_div_assoc]
  split_ifs with hx
  · rw [abs_of_nonneg hx, one_mul]
  · rw [abs_of_neg (not_le.1 hx)]
    ring

/-- **The rounded step is close to the exact one**: within `2 / 2^p` in every entry, when the
clamps do not act. It keeps the lengths, and the symmetry of the shape. -/
theorem stepL_spec {N p : ℕ} {B : ℚ} {c a : List ℚ} {P : List (List ℚ)} (hc : c.length = N)
    (ha : a.length = N) (hP : P.length = N) (hrows : ∀ row ∈ P, row.length = N)
    (hq : 0 < vecL N a ⬝ᵥ matL N P *ᵥ vecL N a)
    (hBc : ∀ i, |Ellipsoid.stepCenter (vecL N c) (vecL N a) (matL N P) i| + 2 / 2 ^ p ≤ B)
    (hBP : ∀ i j, |Ellipsoid.stepShape (vecL N a) (matL N P) i j| + 2 / 2 ^ p ≤ B) :
    (∀ i, |vecL N (stepL N p B c a P).1 i -
        Ellipsoid.stepCenter (vecL N c) (vecL N a) (matL N P) i| ≤ 2 / 2 ^ p) ∧
      (∀ i j, |matL N (stepL N p B c a P).2 i j -
        Ellipsoid.stepShape (vecL N a) (matL N P) i j| ≤ 2 / 2 ^ p) := by
  set Pa := mulVecL P a with hPa_def
  set q := dotL a Pa with hq_def
  set σ : ℚ := 1 / (4 * N) with hσ_def
  have hPa_len : Pa.length = N := by simp [Pa, mulVecL, hP]
  have hvPa : vecL N Pa = matL N P *ᵥ vecL N a := vecL_mulVecL hP hrows ha
  have hqR : (q : ℝ) = vecL N a ⬝ᵥ matL N P *ᵥ vecL N a := by
    rw [hq_def, dotL_eq ha hPa_len, hvPa]
  have hq' : (0 : ℝ) < q := hqR ▸ hq
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq'
  have hN : (1 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp [dotProduct] at hq
    · exact_mod_cast h
  have hσR : (Ellipsoid.stepSize (Fin N) : ℝ) = (σ : ℝ) := by
    simp [Ellipsoid.stepSize, σ]
  have hσ0 : (0 : ℝ) ≤ σ := by rw [← hσR]; unfold Ellipsoid.stepSize; positivity
  have hσ1 : (σ : ℝ) ≤ 1 := by
    rw [hσ_def]
    push_cast
    rw [div_le_one (by positivity)]
    linarith
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  -- Rounding and then clamping a good approximation.
  have key : ∀ (y : ℚ) (z : ℝ), |(y : ℝ) - z| ≤ 1 / 2 ^ p → |z| + 2 / 2 ^ p ≤ B →
      |((clamp B (roundP p y) : ℚ) : ℝ) - z| ≤ 2 / 2 ^ p := by
    intro y z hyz hz
    have hr : |((roundP p y : ℚ) : ℝ) - y| ≤ 1 / 2 ^ p := by
      have h' : ((|roundP p y - y| : ℚ) : ℝ) ≤ ((1 / 2 ^ p : ℚ) : ℝ) :=
        Rat.cast_le.2 (abs_roundP_sub_le p y)
      push_cast at h'
      exact h'
    have h1 : |((roundP p y : ℚ) : ℝ) - z| ≤ 2 / 2 ^ p := by
      calc |((roundP p y : ℚ) : ℝ) - z| = |(((roundP p y : ℚ) : ℝ) - y) + ((y : ℝ) - z)| := by
            ring_nf
        _ ≤ |((roundP p y : ℚ) : ℝ) - y| + |(y : ℝ) - z| := abs_add_le _ _
        _ ≤ 1 / 2 ^ p + 1 / 2 ^ p := add_le_add hr hyz
        _ = 2 / 2 ^ p := by ring
    have h2 : |roundP p y| ≤ B := by
      have : |((roundP p y : ℚ) : ℝ)| ≤ B := by
        calc |((roundP p y : ℚ) : ℝ)| = |(((roundP p y : ℚ) : ℝ) - z) + z| := by ring_nf
          _ ≤ |((roundP p y : ℚ) : ℝ) - z| + |z| := abs_add_le _ _
          _ ≤ 2 / 2 ^ p + |z| := add_le_add_left h1 _
          _ ≤ B := by linarith
      exact_mod_cast this
    rw [clamp_of_abs_le h2]
    exact h1
  have hPai : ∀ i : Fin N, (matL N P *ᵥ vecL N a) i = (Pa[(i : ℕ)]'(hPa_len ▸ i.2) : ℝ) := by
    intro i
    rw [← hvPa, vecL, List.getD_eq_getElem _ _ (hPa_len ▸ i.2)]
  constructor
  · intro i
    have hi : (i : ℕ) < c.length := hc ▸ i.2
    have hiPa : (i : ℕ) < Pa.length := hPa_len ▸ i.2
    have hlen : (i : ℕ) < (c.zip Pa).length := by simp [hi, hiPa]
    have hentry : vecL N (stepL N p B c a P).1 i = ((clamp B (roundP p (c[(i : ℕ)] - σ *
        (sgn Pa[(i : ℕ)] * sqrtP p (Pa[(i : ℕ)] ^ 2 / q)))) : ℚ) : ℝ) := by
      simp only [vecL, stepL]
      rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map, List.getElem_zip]
    rw [hentry]
    refine key _ _ ?_ (hBc i)
    -- The square root of `(P a)ᵢ² / q`, with the sign of `(P a)ᵢ`, is `(P a)ᵢ / √q`.
    have hsgn : ((sgn Pa[(i : ℕ)] : ℚ) : ℝ) = if 0 ≤ (Pa[(i : ℕ)] : ℝ) then 1 else -1 := by
      by_cases h1 : (0 : ℚ) ≤ Pa[(i : ℕ)]
      · have h2 : (0 : ℝ) ≤ Pa[(i : ℕ)] := by exact_mod_cast h1
        simp [sgn, h1, h2]
      · have h2 : ¬ (0 : ℝ) ≤ Pa[(i : ℕ)] := by exact_mod_cast h1
        simp [sgn, h1, h2]
    have hs := sgn_mul_sqrt (x := (Pa[(i : ℕ)] : ℝ)) hq'
    have hc' : vecL N c i = (c[(i : ℕ)] : ℝ) := by rw [vecL, List.getD_eq_getElem _ _ hi]
    have hcen : Ellipsoid.stepCenter (vecL N c) (vecL N a) (matL N P) i =
        c[(i : ℕ)] - σ * ((if 0 ≤ (Pa[(i : ℕ)] : ℝ) then 1 else -1) *
          Real.sqrt ((Pa[(i : ℕ)] : ℝ) ^ 2 / q)) := by
      rw [hs, Ellipsoid.stepCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hPai, hc', hσR,
        ← hqR]
      ring
    have hsq := abs_sqrtP_sub_le p (r := Pa[(i : ℕ)] ^ 2 / q) (by positivity)
    rw [hcen]
    push_cast
    rw [hsgn]
    have hcast : ((Pa[(i : ℕ)] ^ 2 / q : ℚ) : ℝ) = (Pa[(i : ℕ)] : ℝ) ^ 2 / q := by push_cast; rfl
    rw [hcast] at hsq
    have : (c[(i : ℕ)] : ℝ) - σ * ((if 0 ≤ (Pa[(i : ℕ)] : ℝ) then 1 else -1) *
        (sqrtP p (Pa[(i : ℕ)] ^ 2 / q) : ℝ)) - (c[(i : ℕ)] - σ * ((if 0 ≤ (Pa[(i : ℕ)] : ℝ) then
          1 else -1) * Real.sqrt ((Pa[(i : ℕ)] : ℝ) ^ 2 / q))) =
        σ * (if 0 ≤ (Pa[(i : ℕ)] : ℝ) then 1 else -1) * (Real.sqrt ((Pa[(i : ℕ)] : ℝ) ^ 2 / q) -
          sqrtP p (Pa[(i : ℕ)] ^ 2 / q)) := by ring
    rw [this, abs_mul, abs_mul, abs_of_nonneg hσ0, abs_sub_comm]
    have hsg : |(if 0 ≤ (Pa[(i : ℕ)] : ℝ) then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
    rw [hsg, mul_one]
    calc (σ : ℝ) * |(sqrtP p (Pa[(i : ℕ)] ^ 2 / q) : ℝ) - Real.sqrt ((Pa[(i : ℕ)] : ℝ) ^ 2 / q)|
        ≤ 1 * (1 / 2 ^ p) := mul_le_mul hσ1 hsq (abs_nonneg _) zero_le_one
      _ = 1 / 2 ^ p := one_mul _
  · intro i j
    have hi : (i : ℕ) < P.length := hP ▸ i.2
    have hiPa : (i : ℕ) < Pa.length := hPa_len ▸ i.2
    have hjPa : (j : ℕ) < Pa.length := hPa_len ▸ j.2
    have hrow : P[(i : ℕ)].length = N := hrows _ (List.getElem_mem hi)
    have hj : (j : ℕ) < P[(i : ℕ)].length := by rw [hrow]; exact j.2
    have hentry : matL N (stepL N p B c a P).2 i j = ((clamp B (roundP p ((1 + 4 * σ ^ 2) *
        (P[(i : ℕ)][(j : ℕ)] - 2 * σ / q * (Pa[(i : ℕ)] * Pa[(j : ℕ)])))) : ℚ) : ℝ) := by
      have h1 : (i : ℕ) < (stepL N p B c a P).2.length := by rw [length_stepL_snd hP]; exact i.2
      have hrl := length_row_stepL (p := p) (B := B) (c := c) (a := a) hP hrows _
        (List.getElem_mem h1)
      have h2 : (j : ℕ) < ((stepL N p B c a P).2)[(i : ℕ)].length := by rw [hrl]; exact j.2
      change (((stepL N p B c a P).2.getD i []).getD j 0 : ℝ) = _
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [stepL, List.getElem_map, List.getElem_zip]
      rfl
    rw [hentry]
    refine key _ _ ?_ (hBP i j)
    have hshape : Ellipsoid.stepShape (vecL N a) (matL N P) i j = (((1 + 4 * σ ^ 2) *
        (P[(i : ℕ)][(j : ℕ)] - 2 * σ / q * (Pa[(i : ℕ)] * Pa[(j : ℕ)])) : ℚ) : ℝ) := by
      rw [Ellipsoid.stepShape]
      simp only [Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, smul_eq_mul, hPai, hσR,
        ← hqR]
      have hPij : matL N P i j = (P[(i : ℕ)][(j : ℕ)] : ℝ) := by
        rw [matL, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rw [hPij]
      push_cast
      ring
    rw [hshape, sub_self, abs_zero]
    positivity

/-- **The step keeps the shape symmetric.** -/
theorem stepL_symm {N p : ℕ} {B : ℚ} {c a : List ℚ} {P : List (List ℚ)}
    (hP : P.length = N) (hrows : ∀ row ∈ P, row.length = N) (hsym : (matL N P)ᵀ = matL N P) :
    (matL N (stepL N p B c a P).2)ᵀ = matL N (stepL N p B c a P).2 := by
  set Pa := mulVecL P a
  have hPa_len : Pa.length = N := by simp [Pa, mulVecL, hP]
  have hentry : ∀ i j : Fin N, matL N (stepL N p B c a P).2 i j = ((clamp B (roundP p
      ((1 + 4 * (1 / (4 * N)) ^ 2) * ((P.getD i []).getD j 0 - 2 * (1 / (4 * N)) / dotL a Pa *
        (Pa.getD i 0 * Pa.getD j 0)))) : ℚ) : ℝ) := by
    intro i j
    have hi : (i : ℕ) < P.length := by rw [hP]; exact i.2
    have hj : (j : ℕ) < P[(i : ℕ)].length := by rw [hrows _ (List.getElem_mem hi)]; exact j.2
    have hiPa : (i : ℕ) < Pa.length := by rw [hPa_len]; exact i.2
    have hjPa : (j : ℕ) < Pa.length := by rw [hPa_len]; exact j.2
    have h1 : (i : ℕ) < (stepL N p B c a P).2.length := by rw [length_stepL_snd hP]; exact i.2
    have hrl := length_row_stepL (p := p) (B := B) (c := c) (a := a) hP hrows _
      (List.getElem_mem h1)
    have h2 : (j : ℕ) < ((stepL N p B c a P).2)[(i : ℕ)].length := by rw [hrl]; exact j.2
    change (((stepL N p B c a P).2.getD i []).getD j 0 : ℝ) = _
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getD_eq_getElem P [] hi,
      List.getD_eq_getElem _ 0 hj, List.getD_eq_getElem Pa 0 hiPa, List.getD_eq_getElem Pa 0 hjPa]
    simp only [stepL, List.getElem_map, List.getElem_zip]
    rfl
  have hPij : ∀ i j : Fin N, (P.getD j []).getD i 0 = (P.getD i []).getD j 0 := by
    intro i j
    have := congrFun (congrFun hsym i) j
    simp only [Matrix.transpose_apply, matL] at this
    exact_mod_cast this
  ext i j
  rw [Matrix.transpose_apply, hentry, hentry, hPij, mul_comm (Pa.getD j 0)]

/-! ### The loop -/

/-- The state of the loop: the center, the shape, whether a center was declared feasible, and
the one with the smallest objective. -/
abbrev State := List ℚ × List (List ℚ) × Bool × List ℚ

/-- Whether the center `c` replaces the remembered one: it is declared feasible, and no center was
before or it has a smaller objective. -/
def better (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ) (s : State) : Bool :=
  (orc s.1).1 && (!s.2.2.1 || decide (f s.1 < f s.2.2.2))

/-- **One step of the loop**, with the oracle `orc` and the objective `f`: ask the oracle at the
center, remember the center if it is declared feasible with the smallest objective so far, and
step. -/
def loopStep (N p : ℕ) (B : ℚ) (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ) (s : State) :
    State :=
  ((stepL N p B s.1 (orc s.1).2 s.2.1).1, (stepL N p B s.1 (orc s.1).2 s.2.1).2,
    s.2.2.1 || (orc s.1).1, if better orc f s then s.1 else s.2.2.2)

/-- The state after `k` steps from the center `c₀` and the shape `P₀`. -/
def run (N p : ℕ) (B : ℚ) (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ) (c₀ : List ℚ)
    (P₀ : List (List ℚ)) (k : ℕ) : State :=
  (loopStep N p B orc f)^[k] (c₀, P₀, false, c₀)

theorem run_succ (N p : ℕ) (B : ℚ) (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ)
    (c₀ : List ℚ) (P₀ : List (List ℚ)) (k : ℕ) :
    run N p B orc f c₀ P₀ (k + 1) = loopStep N p B orc f (run N p B orc f c₀ P₀ k) := by
  rw [run, run, Function.iterate_succ_apply']

/-- **The best center.** After `K` steps, a center was declared feasible exactly if one of the
first `K` was, and then the remembered center is one of them, with the smallest objective. -/
theorem best_spec (N p : ℕ) (B : ℚ) (orc : List ℚ → Bool × List ℚ) (f : List ℚ → ℚ)
    (c₀ : List ℚ) (P₀ : List (List ℚ)) (K : ℕ) :
    ((run N p B orc f c₀ P₀ K).2.2.1 = true ↔
        ∃ k < K, (orc (run N p B orc f c₀ P₀ k).1).1 = true) ∧
      ((run N p B orc f c₀ P₀ K).2.2.1 = true → ∃ j < K,
        (orc (run N p B orc f c₀ P₀ j).1).1 = true ∧
        (run N p B orc f c₀ P₀ K).2.2.2 = (run N p B orc f c₀ P₀ j).1 ∧
        ∀ k < K, (orc (run N p B orc f c₀ P₀ k).1).1 = true →
          f (run N p B orc f c₀ P₀ j).1 ≤ f (run N p B orc f c₀ P₀ k).1) := by
  induction K with
  | zero => simp [run]
  | succ K ih =>
    obtain ⟨hfound, hbest⟩ := ih
    rw [run_succ]
    set s := run N p B orc f c₀ P₀ K with hs
    simp only [loopStep]
    by_cases hfeas : (orc s.1).1 = true
    · by_cases hb : better orc f s = true
      · -- The current center becomes the best.
        simp only [hb, ite_true, hfeas, Bool.or_true, true_iff, forall_const]
        refine ⟨⟨K, Nat.lt_succ_self _, hfeas⟩, K, Nat.lt_succ_self _, hfeas, rfl, ?_⟩
        intro k hk hk'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · simp only [better, hfeas, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true',
            decide_eq_true_eq] at hb
          rcases hb with hnf | hlt
          · exact absurd ((hfound.2 ⟨k, hk, hk'⟩)) (by rw [hnf]; simp)
          · obtain ⟨j, hj, -, hbj, hmin⟩ := hbest (hfound.2 ⟨k, hk, hk'⟩)
            rw [hbj] at hlt
            exact hlt.le.trans (hmin k hk hk')
        · exact le_rfl
      · -- The remembered center stays.
        have hb' : better orc f s = false := by simpa using hb
        simp only [better, hfeas, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false',
          decide_eq_false_iff_not, not_lt] at hb'
        obtain ⟨hf, hge⟩ := hb'
        rw [ite_eq_right hb]
        simp only [hfeas, Bool.or_true, true_iff, forall_const]
        obtain ⟨j, hj, hjf, hbj, hmin⟩ := hbest hf
        refine ⟨⟨K, Nat.lt_succ_self _, hfeas⟩, j, Nat.lt_succ_of_lt hj, hjf, hbj, ?_⟩
        intro k hk hk'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact hmin k hk hk'
        · rw [← hbj]
          exact hge
    · -- Not declared feasible: nothing changes but the center and the shape.
      replace hfeas : (orc s.1).1 = false := by simpa using hfeas
      have hb : better orc f s = false := by simp [better, hfeas]
      simp only [hfeas, hb, Bool.or_false, Bool.false_eq_true, ite_false]
      refine ⟨?_, fun h => ?_⟩
      · rw [hfound]
        constructor
        · rintro ⟨k, hk, hk'⟩
          exact ⟨k, Nat.lt_succ_of_lt hk, hk'⟩
        · rintro ⟨k, hk, hk'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact ⟨k, hk, hk'⟩
          · rw [hfeas] at hk'
            exact absurd hk' (by simp)
      · obtain ⟨j, hj, hjf, hbj, hmin⟩ := hbest h
        refine ⟨j, Nat.lt_succ_of_lt hj, hjf, hbj, fun k hk hk' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact hmin k hk hk'
        · rw [hfeas] at hk'
          exact absurd hk' (by simp)

end SoS.Loop
