module

public import BS23.Separating.PolyTime
public import Background.BlackBox
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# The running time of the separating algorithm

`BS23.Separating.sepAlgU_runsInTime`: the algorithm of [BS23, Theorem 1.1] for all failure
probabilities (`BS23.Separating.sepAlgU`) runs in time `BS23.bipartitionTime C₀` for some `C₀`,
that is `(|x| + 2)^C₀ (d + 2)^(C₀ ⌈1/δ⌉^C₀ (L + 1))` with `L = logInv wmin`, in the sense of
`BS23.RunsInTime`.

On an input `x` with failure probability `δ` and coins `c`, the machine

* writes `R = rOf δ` (`max ⌈1/δ⌉ 100` for `δ > 0`, `0` otherwise) in unary: it computes it in
  binary in polynomial time (`BS23.Separating.RT.rOf_polytime`) and converts it, in time
  `O((R + 1)²)` (`Turing.MultiTapeTM.ComputableInO.natToUnary`);
* writes the budget `Lg = (d + 5)^(2t + 1)`, `t = 2^41 R (L + 1)`, in unary: it computes it in
  binary in time polynomial in the input with `R` (`BS23.Separating.RT.lgY_polytime`) and converts
  it, in time `O((Lg + 1)²)`;
* keeps the first `coinBits` coins and runs the list program `BS23.Separating.RT.algP` on the
  input with `R` and the budget, in time linear in the input with the coins plus a polynomial in
  the input with `R` and the budget (`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`).
  For `R = 0` it outputs nothing; otherwise it is `BS23.Separating.PT.runL r Kc` with `r = 2^41 R`
  and `Kc = ⌈log₂ (4R)⌉` computed from `R` (`BS23.Separating.PT.runL_polytime`, which takes `r`
  and `Kc` as part of its input).

So it runs within `O(W^E + |(x, c)|)` steps and cells, with `W = (|x| + 2) (R + 2) Lg`, for one
exponent `E` for all inputs. As `R ≤ 100 ⌈1/δ⌉`, `d ≤ |x|` and `d + 5 ≤ (d + 2)³`,
`W ≤ (|x| + 2)^5 (d + 2)^(K₀ ⌈1/δ⌉ (L + 1))` with `K₀ = 100 (3 · 2^42 + 1)`, so
`W^E ≤ bipartitionTime (5 (E + 1) K₀) x` (`BS23.Separating.RT.pow_le_bipartitionTime`).
-/

@[expose] public section

namespace BS23.Separating

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open BS23.Colinear.PT BS23.Separating.PT

namespace RT

/-! ### Certificates within powers -/

theorem exists_le_pow' {β : Type} {size u : β → ℕ} (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hb, hu⟩ := h
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.1 hb
  exact ⟨c, d, fun a ↦ (hu a).trans (hcd _)⟩

/-- A polynomial-time certificate, within `c (|a| + 1)^d` time and space. -/
theorem exists_inO_pow {β γ : Type} {f : β → γ} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} (h : ComputableInPolyTime f encB encC) :
    ∃ c d : ℕ, ComputableInO f encB encC (fun b ↦ c * ((encB b).length + 1) ^ d)
      (fun b ↦ c * ((encB b).length + 1) ^ d) := by
  obtain ⟨T, S, hT, hS, hO⟩ := h.exists_computableInO
  obtain ⟨cT, dT, hT'⟩ := exists_le_pow' hT
  obtain ⟨cS, dS, hS'⟩ := exists_le_pow' hS
  refine ⟨cT + cS, dT + dS, hO.mono_le (fun a ↦ (hT' a).trans ?_) (fun a ↦ (hS' a).trans ?_)⟩
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The padded input -/

/-- The inputs `(δ, wmin, points)`. -/
abbrev encX3 : ℚ × ℚ × Points ↪ List Bool := encPair encRat (encPair encRat encM)

/-- The inputs `(wmin, points)`. -/
abbrev encX : ℚ × Points ↪ List Bool := encPair encRat encM

/-- The inputs `(wmin, points)` with the parameter `R`, in unary. -/
abbrev encXR : (ℚ × Points) × ℕ ↪ List Bool := encPair encX encUnary

/-- The inputs with `R` and the budget, in unary. -/
abbrev encXRL : ((ℚ × Points) × ℕ) × ℕ ↪ List Bool := encPair encXR encUnary

/-- The input, encoded as `(δ, wmin, points)`. -/
theorem length_encBipartitionInput (x : BipartitionInput) :
    (encBipartitionInput x).length = (encX3 (x.δ, x.wmin, x.points)).length := rfl

/-- The list program on the input with `R` and the budget, and the coins: nothing for `R = 0`,
`runL (ratioR R) (kcR R)` otherwise. -/
def algP (z : (((ℚ × Points) × ℕ) × ℕ) × List Bool) : BS23.Output :=
  if z.1.1.2 = 0 then [] else runL (ratioR z.1.1.2) (kcR z.1.1.2) (z.1.1.1, z.2, z.1.2)

theorem algP_polytime : ComputableInPolyTime algP (encPair encXRL encBits) BS23.encOutput := by
  unfold algP
  set E := encPair encXRL encBits
  have hR : ComputableInPolyTime (fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦ z.1.1.2) E
      encUnary := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hr : ComputableInPolyTime (fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦
      ratioR z.1.1.2) E encUnary := by
    unfold ratioR
    exact unary_mul' (const _) hR
  have hK : ComputableInPolyTime (fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦
      kcR z.1.1.2) E encUnary := by
    unfold kcR
    exact binary_clog_two.comp (toBinary' (unary_mul' (const 4) hR))
  have hy : ComputableInPolyTime (fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦
      (z.1.1.1, z.2, z.1.2)) E encY :=
    ((fst _ _).comp ((fst _ _).comp (fst _ _))).prod ((snd _ _).prod ((snd _ _).comp (fst _ _)))
  have hrun : ComputableInPolyTime (fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦
      runL (ratioR z.1.1.2) (kcR z.1.1.2) (z.1.1.1, z.2, z.1.2)) E BS23.encOutput :=
    runL_polytime.comp (g := fun z : (((ℚ × Points) × ℕ) × ℕ) × List Bool ↦
      ((ratioR z.1.1.2, kcR z.1.1.2), (z.1.1.1, z.2, z.1.2))) ((hr.prod hK).prod hy)
  exact ite_prop (decide_eq' hR (const 0)) (const []) hrun

/-- The number of coins read. -/
def cbits (y : ((ℚ × Points) × ℕ) × ℕ) : ℕ := coinBits y.1.1.2.length (kcR y.1.2)

theorem cbits_polytime : ComputableInPolyTime cbits encXRL encUnary := by
  unfold cbits coinBits kcR
  exact unary_add'
    (binary_clog_two.comp (toBinary' (len' ((snd _ _).comp ((fst _ _).comp (fst _ _))))))
    (binary_clog_two.comp (toBinary' (unary_mul' (const 4) ((snd _ _).comp (fst _ _)))))

theorem cbits_le (y : ((ℚ × Points) × ℕ) × ℕ) :
    cbits y ≤ 4 * ((encXRL y).length + 2) ^ 1 := by
  unfold cbits coinBits kcR
  have h1 : Nat.clog 2 y.1.1.2.length ≤ y.1.1.2.length :=
    (Nat.clog_le_iff_le_pow (by norm_num)).2 Nat.lt_two_pow_self.le
  have h1' : Nat.clog 2 (4 * y.1.2) ≤ 4 * y.1.2 :=
    (Nat.clog_le_iff_le_pow (by norm_num)).2 Nat.lt_two_pow_self.le
  have h2 : y.1.1.2.length ≤ (encM y.1.1.2).length :=
    SizedListEncoding.length_le (encA := encV) (encL := encM) y.1.1.2
  have h3 : (encXRL y).length =
      2 * (2 * (2 * (encRat y.1.1.1).length + 1 + (encM y.1.1.2).length) + 1 + y.1.2) + 1 +
        y.2 := by
    simp only [encXRL, encXR, encX, length_encPair, encUnary_apply, List.length_replicate]
  rw [pow_one, h3]
  omega

/-- `R` in binary. -/
theorem rOf_polytime : ComputableInPolyTime rOf encRat encNat := by
  have e : rOf = fun δ : ℚ ↦ if 0 < δ then (if δ⁻¹ ≤ 100 then 100 else ⌈δ⁻¹⌉₊) else 0 := by
    funext δ
    unfold rOf
    simp only [one_div]
    split_ifs with h1 h2
    · exact max_eq_right (Nat.ceil_le.2 (by exact_mod_cast h2))
    · exact max_eq_left (Nat.lt_ceil.2 (by exact_mod_cast (not_le.1 h2))).le
    · rfl
  rw [e]
  exact ite_prop (rat_lt' (const 0) id') (ite_prop (rat_le' (rat_inv' id') (const 100))
    (const 100) (rat_natCeil' (rat_inv' id'))) (const 0)

/-- The budget `Lg = (d + 5)^(2t + 1)`, `t = 2^41 R (L + 1)`, in binary. -/
def lgY (y : (ℚ × Points) × ℕ) : ℕ :=
  (dim y.1.2 + 5) ^ (2 * (ratioR y.2 * (logInv y.1.1 + 1)) + 1)

theorem lgY_polytime : ComputableInPolyTime lgY encXR encNat := by
  unfold lgY ratioR
  exact binary_pow' (toBinary' (unary_add' (dim' ((snd _ _).comp (fst _ _))) (const 5)))
    (unary_add' (unary_mul' (const 2) (unary_mul' (unary_mul' (const (2 ^ 41)) (snd _ _))
      (unary_add' (logInv' ((fst _ _).comp (fst _ _))) (const 1)))) (const 1))

/-- The padded input: the input with `R` and the budget `Lg`, in unary, and the coins. -/
def padF (xr : BipartitionInput × List Bool) : (((ℚ × Points) × ℕ) × ℕ) × List Bool :=
  ((((xr.1.wmin, xr.1.points), rOf xr.1.δ), lgY ((xr.1.wmin, xr.1.points), rOf xr.1.δ)), xr.2)

/-- **The algorithm on the padded input.** -/
theorem sepAlgU_eq_algP (xr : BipartitionInput × List Bool) :
    sepAlgU xr = algP ((padF xr).1, (padF xr).2.take (cbits (padF xr).1)) := by
  unfold sepAlgU algP padF
  dsimp only
  split_ifs
  · rfl
  · rw [runL_eq]
    rfl

/-! ### The bound -/

theorem one_le_lgY (y : (ℚ × Points) × ℕ) : 1 ≤ lgY y :=
  Nat.one_le_pow _ _ (by omega)

/-- `R ≤ 100 ⌈1/δ⌉`. -/
theorem rOf_le (δ : ℚ) : rOf δ ≤ 100 * ⌈1 / δ⌉₊ := by
  unfold rOf
  split_ifs with h
  · have : 1 ≤ ⌈1 / δ⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
    exact max_le (by omega) (by omega)
  · exact Nat.zero_le _

/-- The dimension is at most the length of the encoded points. -/
theorem dim_le_length_encM (pts : Points) : dim pts ≤ (encM pts).length := by
  cases pts with
  | nil => exact Nat.zero_le _
  | cons p ps =>
    have h1 : p.length ≤ (encV p).length :=
      SizedListEncoding.length_le (encA := encRat) (encL := encV) p
    have h2 : (encM (p :: ps)).length = 2 * (encV p).length + 1 + (encM ps).length := by
      simp only [encM, encV, length_encList, List.map_cons, List.sum_cons]
    change p.length ≤ _
    omega

/-- The dimension is at most the length of the input. -/
theorem dim_le_length (x : BipartitionInput) : dim x.points ≤ (encBipartitionInput x).length := by
  have h : (encBipartitionInput x).length =
      2 * (encRat x.δ).length + 1 + (2 * (encRat x.wmin).length + 1 + (encM x.points).length) := by
    rw [length_encBipartitionInput]
    simp only [encX3, length_encPair]
  have := dim_le_length_encM x.points
  omega

/-- The exponent of `W`: `R + 3 · 2^42 R (L + 1) ≤ K₀ ⌈1/δ⌉ (L + 1)`, `K₀ = 100 (3 · 2^42 + 1)`. -/
theorem exponent_le {R m L : ℕ} (hR : R ≤ 100 * m) :
    R + 3 * (2 * (2 ^ 41 * R * (L + 1))) ≤ 100 * (3 * 2 ^ 42 + 1) * m * (L + 1) := by
  have h1 : R + 3 * (2 * (2 ^ 41 * R * (L + 1))) ≤ (3 * 2 ^ 42 + 1) * R * (L + 1) := by
    have : R ≤ R * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
    have e : (3 * 2 ^ 42 + 1) * R * (L + 1) = 3 * (2 * (2 ^ 41 * R * (L + 1))) + R * (L + 1) := by
      ring
    omega
  calc R + 3 * (2 * (2 ^ 41 * R * (L + 1))) ≤ (3 * 2 ^ 42 + 1) * R * (L + 1) := h1
    _ ≤ (3 * 2 ^ 42 + 1) * (100 * m) * (L + 1) := by gcongr
    _ = 100 * (3 * 2 ^ 42 + 1) * m * (L + 1) := by ring

/-- `W = (|x| + 2) (R + 2) Lg ≤ (|x| + 2)^5 (d + 2)^(K₀ ⌈1/δ⌉ (L + 1))`. -/
theorem W_le (x : BipartitionInput) :
    ((encBipartitionInput x).length + 2) * (rOf x.δ + 2) * lgY ((x.wmin, x.points), rOf x.δ) ≤
      ((encBipartitionInput x).length + 2) ^ 5 *
        (dim x.points + 2) ^ (100 * (3 * 2 ^ 42 + 1) * ⌈1 / x.δ⌉₊ * (logInv x.wmin + 1)) := by
  unfold lgY ratioR
  dsimp only
  set A := (encBipartitionInput x).length
  set d := dim x.points
  set L := logInv x.wmin
  set R := rOf x.δ
  have hdA : d ≤ A := dim_le_length x
  have hd : d + 5 ≤ (d + 2) ^ 3 := by
    rw [pow_three]
    nlinarith [Nat.zero_le (d * d), Nat.zero_le (d * (d * d))]
  have hR2 : R + 2 ≤ 2 * (d + 2) ^ R :=
    calc R + 2 ≤ 2 * 2 ^ R := by have := Nat.lt_two_pow_self (n := R); omega
      _ ≤ 2 * (d + 2) ^ R := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hLg : (d + 5) ^ (2 * (2 ^ 41 * R * (L + 1)) + 1) ≤
      (A + 5) * (d + 2) ^ (3 * (2 * (2 ^ 41 * R * (L + 1)))) := by
    obtain ⟨T, hT⟩ : ∃ T, T = 2 * (2 ^ 41 * R * (L + 1)) := ⟨_, rfl⟩
    rw [← hT, pow_succ', pow_mul (d + 2) 3 T]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hd _)
  have hA5 : (A + 2) * (2 * (A + 5)) ≤ (A + 2) ^ 5 := by
    have h8 : 2 * (A + 5) ≤ (A + 2) ^ 4 := by
      have : 8 ≤ (A + 2) ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ (A + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      calc 2 * (A + 5) ≤ 8 * (A + 2) := by omega
        _ ≤ (A + 2) ^ 3 * (A + 2) := Nat.mul_le_mul_right _ this
        _ = (A + 2) ^ 4 := by ring
    calc (A + 2) * (2 * (A + 5)) ≤ (A + 2) * (A + 2) ^ 4 := Nat.mul_le_mul_left _ h8
      _ = (A + 2) ^ 5 := by ring
  have hexp := exponent_le (L := L) (rOf_le x.δ)
  calc (A + 2) * (R + 2) * (d + 5) ^ (2 * (2 ^ 41 * R * (L + 1)) + 1)
      ≤ (A + 2) * (2 * (d + 2) ^ R) * ((A + 5) * (d + 2) ^ (3 * (2 * (2 ^ 41 * R * (L + 1))))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hR2) hLg
    _ = (A + 2) * (2 * (A + 5)) * (d + 2) ^ (R + 3 * (2 * (2 ^ 41 * R * (L + 1)))) := by
        rw [pow_add]; ring
    _ ≤ (A + 2) ^ 5 * (d + 2) ^ (100 * (3 * 2 ^ 42 + 1) * ⌈1 / x.δ⌉₊ * (L + 1)) :=
        Nat.mul_le_mul hA5 (Nat.pow_le_pow_right (by omega) hexp)

/-- `W^E ≤ bipartitionTime (5 (E + 1) K₀) x`, `K₀ = 100 (3 · 2^42 + 1)`. -/
theorem pow_le_bipartitionTime (E : ℕ) (x : BipartitionInput) :
    (((encBipartitionInput x).length + 2) * (rOf x.δ + 2) * lgY ((x.wmin, x.points), rOf x.δ)) ^
        E ≤ bipartitionTime (5 * (E + 1) * (100 * (3 * 2 ^ 42 + 1))) x := by
  set K := 100 * (3 * 2 ^ 42 + 1) with hK
  set C := 5 * (E + 1) * K with hC
  have hK1 : 1 ≤ K := by rw [hK]; norm_num
  have hC1 : C ≠ 0 := by positivity
  set m := ⌈1 / x.δ⌉₊
  set A := (encBipartitionInput x).length
  set d := dim x.points
  set L := logInv x.wmin
  have hW := W_le x
  unfold bipartitionTime
  calc _ ≤ ((A + 2) ^ 5 * (d + 2) ^ (K * m * (L + 1))) ^ E := Nat.pow_le_pow_left hW E
    _ = (A + 2) ^ (5 * E) * (d + 2) ^ (E * K * m * (L + 1)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        ring_nf
    _ ≤ (A + 2) ^ C * (d + 2) ^ (C * m ^ C * (L + 1)) := by
        refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ?_)
          (Nat.pow_le_pow_right (by omega) ?_)
        · rw [hC]
          nlinarith
        · have hm : m ≤ m ^ C := Nat.le_self_pow hC1 m
          have h1 : E * K ≤ C := by rw [hC]; nlinarith
          calc E * K * m * (L + 1) ≤ C * m ^ C * (L + 1) := by gcongr

/-- The arithmetic of the bound: with `W = (A + 2) (R + 2) Lg`, every term is `O(W^E + N)`. -/
theorem bound_arith {N A A' Dl R Y1 Lg Y2 Z tR tL c₁ c₂ c₃ d₂ d₃ D : ℕ} (hAA : A' = A)
    (hAN : 2 * A + 1 ≤ N) (hDl : Dl ≤ A) (hY1 : Y1 ≤ 2 * A + 1 + R) (hY2 : Y2 = 2 * Y1 + 1 + Lg)
    (hZ : Z ≤ 2 * Y2 + 1 + N) (hLg : 1 ≤ Lg) (htR : tR ≤ (R + 1) ^ 2) (htL : tL ≤ (Lg + 1) ^ 2) :
    N + A + (N + A + (c₂ * (Dl + 1) ^ d₂ + tR)) +
          (N + A + (N + A + (c₂ * (Dl + 1) ^ d₂ + tR)) + (c₃ * (Y1 + 1) ^ d₃ + tL)) + N +
        c₁ * ((Y2 + 2) ^ D + Z + 1) ≤
      (20 + 3 * c₂ + c₃ + c₁ * (3 ^ D + 10)) *
        (((A' + 2) * (R + 2) * Lg) ^ (d₂ + d₃ + D + 2) + N + 1) := by
  rw [hAA]
  obtain ⟨W, hW⟩ : ∃ W, W = (A + 2) * (R + 2) * Lg := ⟨_, rfl⟩
  rw [← hW]
  have hAR : 2 * A + 2 * R + 4 ≤ (A + 2) * (R + 2) := by nlinarith
  have hW1 : (A + 2) * (R + 2) ≤ W := hW ▸ Nat.le_mul_of_pos_right _ hLg
  have hW2 : 4 * Lg ≤ W := hW ▸ Nat.mul_le_mul_right _ (by nlinarith)
  have hWpos : 1 ≤ W := by omega
  obtain ⟨X, hX⟩ : ∃ X, X = W ^ (d₂ + d₃ + D + 2) := ⟨_, rfl⟩
  rw [← hX]
  have hpow : ∀ {k : ℕ}, k ≤ d₂ + d₃ + D + 2 → W ^ k ≤ X := fun hk ↦
    hX ▸ Nat.pow_le_pow_right hWpos hk
  have h1 : (Dl + 1) ^ d₂ ≤ X := (Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega))
  have h2 : tR ≤ X := htR.trans ((Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega)))
  have h3 : (Y1 + 1) ^ d₃ ≤ X := (Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega))
  have h4 : tL ≤ X := htL.trans ((Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega)))
  have h5 : (Y2 + 2) ^ D ≤ 3 ^ D * X :=
    calc (Y2 + 2) ^ D ≤ (3 * W) ^ D := Nat.pow_le_pow_left (by omega) _
      _ = 3 ^ D * W ^ D := mul_pow _ _ _
      _ ≤ 3 ^ D * X := Nat.mul_le_mul_left _ (hpow (by omega))
  have hWX : W ≤ X := (Nat.le_self_pow (by omega) W).trans (hpow le_rfl)
  have hZ' : Z + 1 ≤ 6 * X + N := by omega
  have e1 := Nat.mul_le_mul_left c₂ h1
  have e2 := Nat.mul_le_mul_left c₃ h3
  have e3 : c₁ * ((Y2 + 2) ^ D + Z + 1) ≤ c₁ * (3 ^ D + 10) * (X + N + 1) := by
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have : (Y2 + 2) ^ D + Z + 1 ≤ 3 ^ D * X + (6 * X + N) := by omega
    refine this.trans ?_
    nlinarith [Nat.zero_le (3 ^ D * N), Nat.zero_le (3 ^ D)]
  have e4 : c₂ * X ≤ c₂ * (X + N + 1) := Nat.mul_le_mul_left _ (by omega)
  have e4' : c₃ * X ≤ c₃ * (X + N + 1) := Nat.mul_le_mul_left _ (by omega)
  have e5 : (20 + 3 * c₂ + c₃ + c₁ * (3 ^ D + 10)) * (X + N + 1) =
      20 * (X + N + 1) + 3 * (c₂ * (X + N + 1)) + c₃ * (X + N + 1) +
        c₁ * (3 ^ D + 10) * (X + N + 1) := by ring
  rw [e5]
  omega

theorem len_N (a : BipartitionInput × List Bool) :
    2 * (encX3 (a.1.δ, a.1.wmin, a.1.points)).length + 1 ≤
      (encPair encBipartitionInput encBits a).length := by
  rw [length_encPair (enc₁ := encBipartitionInput), length_encBipartitionInput]
  omega

theorem len_δ (a : BipartitionInput × List Bool) :
    (encRat a.1.δ).length ≤ (encX3 (a.1.δ, a.1.wmin, a.1.points)).length := by
  simp only [encX3, length_encPair]
  omega

theorem len_Y1 (a : BipartitionInput × List Bool) :
    (encXR ((a.1.wmin, a.1.points), rOf a.1.δ)).length ≤
      2 * (encX3 (a.1.δ, a.1.wmin, a.1.points)).length + 1 + rOf a.1.δ := by
  simp only [encX3, encXR, RT.encX, length_encPair, encUnary_apply, List.length_replicate]
  omega

theorem len_Y2 (a : BipartitionInput × List Bool) :
    (encXRL (padF a).1).length = 2 * (encXR ((a.1.wmin, a.1.points), rOf a.1.δ)).length + 1 +
      lgY ((a.1.wmin, a.1.points), rOf a.1.δ) := by
  rw [length_encPair, encUnary_apply, List.length_replicate]
  rfl

theorem len_Z (a : BipartitionInput × List Bool) :
    (encPair encXRL encBits (padF a)).length ≤
      2 * (encXRL (padF a).1).length + 1 + (encPair encBipartitionInput encBits a).length := by
  have h : (encBits (padF a).2).length = (encBits a.2).length := rfl
  rw [length_encPair, length_encPair (enc₁ := encBipartitionInput), h]
  omega

end RT

open RT in
/-- **The algorithm of Theorem 1.1 runs in time `bipartitionTime C₀`** for some `C₀`. -/
theorem sepAlgU_runsInTime :
    ∃ C₀ : ℕ, RunsInTime encBipartitionInput encOutput sepAlgU (bipartitionTime C₀) := by
  -- The list program on the padded input, keeping the first `cbits` coins.
  obtain ⟨D, hD⟩ := exists_computableInTimeAndSpace_take algP_polytime cbits_polytime cbits_le
  obtain ⟨c₁, hc₁⟩ := hD D le_rfl
  have hA := hc₁.computableInO
  -- Padding: the input, `R` and the budget in unary, the coins.
  obtain ⟨c₂, d₂, hR⟩ := exists_inO_pow rOf_polytime
  have hRU := ComputableInO.natToUnary.comp' hR
  obtain ⟨c₃, d₃, hL⟩ := exists_inO_pow lgY_polytime
  have hLU := ComputableInO.natToUnary.comp' hL
  have hx3 : ComputableInO (fun xr : BipartitionInput × List Bool ↦
        (xr.1.δ, xr.1.wmin, xr.1.points))
      (encPair encBipartitionInput encBits) encX3
      (fun xr ↦ (encPair encBipartitionInput encBits xr).length)
      (fun xr ↦ (encPair encBipartitionInput encBits xr).length) :=
    (ComputableInO.fst encBipartitionInput encBits).of_enc_eq fun _ ↦ rfl
  have hδ := (ComputableInO.fst encRat RT.encX).comp' hx3
  have hx := (ComputableInO.snd encRat RT.encX).comp' hx3
  have hy1 := hx.prod (hRU.comp' hδ)
  have hy2 := hy1.prod (hLU.comp' hy1)
  have hpad := hy2.prod (ComputableInO.snd encBipartitionInput encBits)
  have hall := hA.comp' (g := padF) hpad
  clear hA hRU hLU hR hL hx3 hδ hx hy1 hy2 hpad hD hc₁
  obtain ⟨c, hc, -⟩ := hall.mono (T' := fun a ↦ (((encBipartitionInput a.1).length + 2) *
      (rOf a.1.δ + 2) * lgY ((a.1.wmin, a.1.points), rOf a.1.δ)) ^ (d₂ + d₃ + D + 2) +
      (encPair encBipartitionInput encBits a).length)
    (S' := fun a ↦ (((encBipartitionInput a.1).length + 2) *
      (rOf a.1.δ + 2) * lgY ((a.1.wmin, a.1.points), rOf a.1.δ)) ^ (d₂ + d₃ + D + 2) +
      (encPair encBipartitionInput encBits a).length) (20 + 3 * c₂ + c₃ + c₁ * (3 ^ D + 10))
    (fun a ↦ bound_arith (length_encBipartitionInput a.1) (len_N a) (len_δ a) (len_Y1 a)
      (len_Y2 a) (len_Z a) (one_le_lgY _) le_rfl le_rfl)
    (fun a ↦ bound_arith (length_encBipartitionInput a.1) (len_N a) (len_δ a) (len_Y1 a)
      (len_Y2 a) (len_Z a) (one_le_lgY _) (by nlinarith) (by nlinarith))
  refine ⟨5 * (d₂ + d₃ + D + 2 + 1) * (100 * (3 * 2 ^ 42 + 1)), c, ?_⟩
  have heq : sepAlgU = fun xr ↦ algP ((padF xr).1, (padF xr).2.take (cbits (padF xr).1)) :=
    funext sepAlgU_eq_algP
  rw [heq]
  refine hc.mono (fun a ↦ ?_) (fun a ↦ ?_) <;>
    exact Nat.mul_le_mul_left c (Nat.add_le_add_right (Nat.add_le_add_right
      (pow_le_bipartitionTime (d₂ + d₃ + D + 2) a.1) _) _)

end BS23.Separating
