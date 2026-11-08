module

public import BS23.ColinearSoS.PolyTime
public import BS23.Separating.RunTime

/-!
# The running time of the sum-of-squares colinear algorithm

`BS23.ColinearSoS.colinearSoSAlg_runsInTime`: the algorithm of [BS23, Theorem 1.2] that follows
the sum-of-squares route (`BS23.ColinearSoS.colinearSoSAlg`) runs in time `BS23.colinearTime C`
for some `C`, that is `(|x| + 2)^(C (L + 1))` with `L = logInv wmin`, in the sense of
`BS23.RunsInTime`.

On an input `x` with coins `c`, the machine

* reads `(k, wmin, points)` off the input with the coins, ignoring the coins;
* writes the budget `Lgc x = (d + 5)^(2t + 1)`, `t = 256 (L + 1)`, in unary: it computes it in
  binary in polynomial time in `|x|` (`BS23.ColinearSoS.RTc.lgY_polytime`; the exponent
  `2t + 1` is computed in unary from `wmin`) and converts it, in time `O((Lgc x + 1)²)`
  (`Turing.MultiTapeTM.ComputableInO.natToUnary`);
* runs the list program `BS23.ColinearSoS.PTc.colL` on the input with the budget, in time
  polynomial in `|x| + Lgc x` (`BS23.ColinearSoS.PTc.colL_polytime`).

So it runs within `O(W^E + |(x, c)|)` steps and cells, with `W = (|x| + 2) Lgc x`, for one
exponent `E` for all inputs. As `d ≤ |x|`, `d + 5 ≤ (|x| + 2)³` and
`1 + 3 (2t + 1) ≤ 1540 (L + 1)`, `W ≤ (|x| + 2)^(1540 (L + 1))`, so
`W^E ≤ colinearTime (1540 E) x` (`BS23.ColinearSoS.RTc.pow_le_colinearTime`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open BS23.Colinear.PT BS23.ColinearSoS.PTc
open BS23.Separating.RT (exists_inO_pow dim_le_length_encM)

namespace RTc

/-! ### The padded input -/

/-- The budget `Lgc`, in binary, from `(k, wmin, points)`. -/
def lgY (y : ℕ × ℚ × Points) : ℕ := (dim y.2.2 + 5) ^ (2 * tCol y.2.1 + 1)

theorem lgY_polytime : ComputableInPolyTime lgY Colinear.PT.encX encNat := by
  unfold lgY
  exact binary_pow' (toBinary' (unary_add' (dim' ((snd _ _).comp (snd _ _))) (const 5)))
    (unary_add' (unary_mul' (const 2) (tCol' ((fst _ _).comp (snd _ _)))) (const 1))

/-- The padded input: `(k, wmin, points)` and the budget `Lgc`, in unary. -/
def padF (xr : ColinearInput × List Bool) : (ℕ × ℚ × Points) × ℕ :=
  ((xr.1.k, xr.1.wmin, xr.1.points), lgY (xr.1.k, xr.1.wmin, xr.1.points))

/-- **The algorithm on the padded input.** -/
theorem colinearSoSAlg_eq_colL (xr : ColinearInput × List Bool) :
    colinearSoSAlg xr = colL (padF xr) := by
  rw [padF, colL_eq]
  rfl

/-! ### The bound -/

theorem one_le_lgY (y : ℕ × ℚ × Points) : 1 ≤ lgY y :=
  Nat.one_le_pow _ _ (by omega)

/-- The input, encoded as `(k, wmin, points)`. -/
theorem length_encColinearInput (x : ColinearInput) :
    (encColinearInput x).length = (Colinear.PT.encX (x.k, x.wmin, x.points)).length := rfl

/-- The dimension is at most the length of the input. -/
theorem dim_le_length (x : ColinearInput) : dim x.points ≤ (encColinearInput x).length := by
  have h : (encColinearInput x).length = 2 * (encNat x.k).length + 1 +
      (2 * (encRat x.wmin).length + 1 + (encM x.points).length) := by
    rw [length_encColinearInput]
    simp only [Colinear.PT.encX, length_encPair]
  have := dim_le_length_encM x.points
  omega

/-- `((|x| + 2) Lgc x)^E ≤ colinearTime (1540 E) x`, as `d + 5 ≤ (|x| + 2)³` and
`1 + 3 (2t + 1) ≤ 1540 (L + 1)`. -/
theorem pow_le_colinearTime (E : ℕ) (x : ColinearInput) :
    (((encColinearInput x).length + 2) * Lgc x) ^ E ≤ colinearTime (1540 * E) x := by
  unfold colinearTime Lgc tCol sCol
  set A := (encColinearInput x).length
  set d := dim x.points
  set L := logInv x.wmin
  have hdA : d ≤ A := dim_le_length x
  have hd : d + 5 ≤ (A + 2) ^ 3 := by
    have h4 : 2 ^ 2 ≤ (A + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    calc d + 5 ≤ 2 ^ 2 * (A + 2) := by omega
      _ ≤ (A + 2) ^ 2 * (A + 2) := Nat.mul_le_mul_right _ h4
      _ = (A + 2) ^ 3 := by ring
  have hW : (A + 2) * (d + 5) ^ (2 * (256 * (L + 1)) + 1) ≤ (A + 2) ^ (1540 * (L + 1)) :=
    calc (A + 2) * (d + 5) ^ (2 * (256 * (L + 1)) + 1)
        ≤ (A + 2) * ((A + 2) ^ 3) ^ (2 * (256 * (L + 1)) + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
      _ = (A + 2) ^ (1 + 3 * (2 * (256 * (L + 1)) + 1)) := by rw [← pow_mul, pow_add, pow_one]
      _ ≤ (A + 2) ^ (1540 * (L + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  calc ((A + 2) * (d + 5) ^ (2 * (256 * (L + 1)) + 1)) ^ E
      ≤ ((A + 2) ^ (1540 * (L + 1))) ^ E := Nat.pow_le_pow_left hW E
    _ = (A + 2) ^ (1540 * E * (L + 1)) := by
        rw [← pow_mul]
        congr 1
        ring

/-- The arithmetic of the bound: with `W = (A + 2) Lg`, every term is `O(W^E + N)`. -/
theorem bound_arith {N A Lg P c₁ c₂ d₁ d₂ : ℕ} (hLg : 1 ≤ Lg) (hP : P = 2 * A + 1 + Lg) :
    N + (N + (c₂ * (A + 1) ^ d₂ + (Lg + 1) ^ 2)) + c₁ * (P + 1) ^ d₁ ≤
      (3 + c₂ + c₁ * 3 ^ d₁) * (((A + 2) * Lg) ^ (d₁ + d₂ + 2) + N + 1) := by
  obtain ⟨W, hW⟩ : ∃ W, W = (A + 2) * Lg := ⟨_, rfl⟩
  rw [← hW]
  have hW1 : A + 2 ≤ W := hW ▸ Nat.le_mul_of_pos_right _ hLg
  have hW2 : 2 * Lg ≤ W := hW ▸ Nat.mul_le_mul_right _ (by omega)
  have hWpos : 1 ≤ W := by omega
  obtain ⟨X, hX⟩ : ∃ X, X = W ^ (d₁ + d₂ + 2) := ⟨_, rfl⟩
  rw [← hX]
  have hpow : ∀ {k : ℕ}, k ≤ d₁ + d₂ + 2 → W ^ k ≤ X := fun hk ↦
    hX ▸ Nat.pow_le_pow_right hWpos hk
  have h1 : (A + 1) ^ d₂ ≤ X := (Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega))
  have h2 : (Lg + 1) ^ 2 ≤ X := (Nat.pow_le_pow_left (by omega) _).trans (hpow (by omega))
  have h3 : (P + 1) ^ d₁ ≤ 3 ^ d₁ * X :=
    calc (P + 1) ^ d₁ ≤ (3 * W) ^ d₁ := Nat.pow_le_pow_left (by omega) _
      _ = 3 ^ d₁ * W ^ d₁ := mul_pow _ _ _
      _ ≤ 3 ^ d₁ * X := Nat.mul_le_mul_left _ (hpow (by omega))
  have e1 : c₂ * (A + 1) ^ d₂ ≤ c₂ * (X + N + 1) :=
    Nat.mul_le_mul_left _ (h1.trans (by omega))
  have e3 : c₁ * (P + 1) ^ d₁ ≤ c₁ * 3 ^ d₁ * (X + N + 1) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ (by omega)))
  have e4 : (3 + c₂ + c₁ * 3 ^ d₁) * (X + N + 1) =
      3 * (X + N + 1) + c₂ * (X + N + 1) + c₁ * 3 ^ d₁ * (X + N + 1) := by ring
  omega

theorem length_padF (a : ColinearInput × List Bool) :
    (encY (padF a)).length =
      2 * (encColinearInput a.1).length + 1 + lgY (a.1.k, a.1.wmin, a.1.points) := by
  rw [length_encPair, encUnary_apply, List.length_replicate]
  rfl

end RTc

open RTc in
/-- **The sum-of-squares algorithm of Theorem 1.2 runs in time `colinearTime C`** for some
`C`. -/
theorem colinearSoSAlg_runsInTime :
    ∃ C : ℕ, RunsInTime encColinearInput encOutput colinearSoSAlg (colinearTime C) := by
  -- The list program on the padded input.
  obtain ⟨c₁, d₁, hA⟩ := exists_inO_pow colL_polytime
  -- Padding: `(k, wmin, points)` and the budget in unary.
  obtain ⟨c₂, d₂, hL⟩ := exists_inO_pow lgY_polytime
  have hLU := ComputableInO.natToUnary.comp' hL
  have hx : ComputableInO (fun xr : ColinearInput × List Bool ↦ (xr.1.k, xr.1.wmin, xr.1.points))
      (encPair encColinearInput encBits) Colinear.PT.encX
      (fun xr ↦ (encPair encColinearInput encBits xr).length)
      (fun xr ↦ (encPair encColinearInput encBits xr).length) :=
    (ComputableInO.fst encColinearInput encBits).of_enc_eq fun _ ↦ rfl
  have hall := hA.comp' (g := padF) (hx.prod (hLU.comp' hx))
  -- Every bound is `O(W^E + |(x, c)|)`, `W = (|x| + 2) Lgc x`.
  set E := d₁ + d₂ + 2
  set K := 3 + c₂ + c₁ * 3 ^ d₁
  have hb : ∀ a : ColinearInput × List Bool,
      (encPair encColinearInput encBits a).length +
          ((encPair encColinearInput encBits a).length +
            (c₂ * ((Colinear.PT.encX (a.1.k, a.1.wmin, a.1.points)).length + 1) ^ d₂ +
              (lgY (a.1.k, a.1.wmin, a.1.points) + 1) ^ 2)) +
        c₁ * ((encY (padF a)).length + 1) ^ d₁ ≤
      K * ((((encColinearInput a.1).length + 2) * Lgc a.1) ^ E +
        (encPair encColinearInput encBits a).length + 1) := fun a ↦
    bound_arith (one_le_lgY _) (length_padF a)
  have hb' : ∀ a : ColinearInput × List Bool,
      (encPair encColinearInput encBits a).length +
          ((encPair encColinearInput encBits a).length +
            (c₂ * ((Colinear.PT.encX (a.1.k, a.1.wmin, a.1.points)).length + 1) ^ d₂ +
              lgY (a.1.k, a.1.wmin, a.1.points))) +
        c₁ * ((encY (padF a)).length + 1) ^ d₁ ≤
      K * ((((encColinearInput a.1).length + 2) * Lgc a.1) ^ E +
        (encPair encColinearInput encBits a).length + 1) := fun a ↦ by
    have h := hb a
    have : lgY (a.1.k, a.1.wmin, a.1.points) ≤ (lgY (a.1.k, a.1.wmin, a.1.points) + 1) ^ 2 := by
      nlinarith
    omega
  obtain ⟨c, hc, -⟩ := hall.mono K hb hb'
  refine ⟨1540 * E, c, ?_⟩
  have heq : colinearSoSAlg = fun xr ↦ colL (padF xr) := funext colinearSoSAlg_eq_colL
  rw [heq]
  refine hc.mono (fun a ↦ ?_) (fun a ↦ ?_) <;>
    exact Nat.mul_le_mul_left c (Nat.add_le_add_right (Nat.add_le_add_right
      (pow_le_colinearTime E a.1) _) _)

end BS23.ColinearSoS
