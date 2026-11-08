module

public import BS23.SmallRadius.PolyTime
public import BS23.Separating.RunTime

/-!
# The running time of the small-radius algorithm

`BS23.SmallRadius.srAlg_runsInTime`: the algorithm of [BS23, Theorem 1.3]
(`BS23.SmallRadius.srAlg C₁`) runs in time `BS23.radiusTime C` for some `C`, that is
`(|x| + 2)^(C (⌈R²⌉ + L + 1))` with `L = logInv wmin`, in the sense of `BS23.RunsInTime`.

On an input `x` with coins `c`, the machine

* writes the budget `Lb = budgetOf C₁ x = (|x| + 2)^E`, `E = C₁ (⌈R²⌉ + L + 1)`, in unary: it
  computes `E` in binary in polynomial time, converts it to unary in time `O((E + 1)²)`
  (`Turing.MultiTapeTM.ComputableInO.natToUnary`), computes `Lb` in binary in polynomial time in
  `|x|` and `E` (`BS23.SmallRadius.RT.bpow_polytime`), and converts it to unary in time
  `O((Lb + 1)²)`;
* keeps the first `min n k · (n + 8)` coins, which are all the algorithm reads
  (`BS23.SmallRadius.RT.srCoreL_take`), and runs the list program
  `BS23.SmallRadius.PT.srCoreL` with the budget, in time linear in the input with the coins plus a
  polynomial in the input with the budget
  (`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`),
  since the list program runs in polynomial time in its input and its unary budget
  (`BS23.SmallRadius.PT.srCoreL_polytime`).

So it runs within `O(W^P + |(x, c)|)` steps and cells, with `W = (|x| + 2)^((C₁ + 2) X)`,
`X = ⌈R²⌉ + L + 1`: `|x| + 2`, `E + 1` and `Lb` are all at most `W`. And
`W^P = radiusTime (P (C₁ + 2)) x`.
-/

@[expose] public section

namespace BS23.SmallRadius

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open BS23.Colinear.PT BS23.SmallRadius.PT
open BS23.Separating.RT (exists_inO_pow)

namespace RT

/-! ### The budget -/

/-- The exponent `C₁ (⌈R²⌉ + logInv w + 1)` of the budget. -/
def bexp (C₁ : ℕ) (x : RadiusInput) : ℕ := C₁ * (⌈x.R ^ 2⌉₊ + logInv x.wmin + 1)

theorem bexp_polytime (C₁ : ℕ) : ComputableInPolyTime (bexp C₁) encRadiusInput encNat := by
  unfold bexp
  have hx := radT_polytime
  have hw : ComputableInPolyTime (fun x : RadiusInput => x.wmin) encRadiusInput encRat :=
    (fst _ _).comp ((snd _ _).comp hx)
  have hR : ComputableInPolyTime (fun x : RadiusInput => x.R) encRadiusInput encRat :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hx))
  exact binary_mul' (const C₁) (binAdd' (binAdd' (rat_natCeil' (rat_sq' hR))
    (toBinary' (logInv' hw))) (const 1))

/-- The budget `(|x| + 2)^E` from the input and the exponent. -/
def bpow (p : RadiusInput × ℕ) : ℕ := ((encRadiusInput p.1).length + 2) ^ p.2

theorem bpow_polytime : ComputableInPolyTime bpow (encPair encRadiusInput encUnary) encNat := by
  unfold bpow
  exact binary_pow' (toBinary' (unary_add' ((encoding_length encRadiusInput).comp (fst _ _))
    (const 2))) (snd _ _)

theorem budgetOf_eq (C₁ : ℕ) (x : RadiusInput) : budgetOf C₁ x = bpow (x, bexp C₁ x) := rfl

/-! ### The coins -/

/-- The number of coins read: `min n k` rounds of `n + 8` coins. -/
def cbits (y : RadiusInput × ℕ) : ℕ := min y.1.points.length y.1.k * coinBits y.1.points.length

theorem cbits_polytime : ComputableInPolyTime cbits (encPair encRadiusInput encUnary) encUnary := by
  unfold cbits coinBits
  have hx : ComputableInPolyTime (fun y : RadiusInput × ℕ => (y.1.k, y.1.wmin, y.1.R, y.1.points))
      (encPair encRadiusInput encUnary) (encPair encNat (encPair encRat (encPair encRat encM))) :=
    radT_polytime.comp (fst _ _)
  have hk : ComputableInPolyTime (fun y : RadiusInput × ℕ => y.1.k)
      (encPair encRadiusInput encUnary) encNat := (fst _ _).comp hx
  have hn : ComputableInPolyTime (fun y : RadiusInput × ℕ => y.1.points.length)
      (encPair encRadiusInput encUnary) encUnary :=
    len' ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hx)))
  exact unary_mul' (binary_min_unary' hn hk) (unary_add' hn (const 8))

theorem length_points_le (x : RadiusInput) : x.points.length ≤ (encRadiusInput x).length := by
  have h1 : x.points.length ≤ (encM x.points).length :=
    SizedListEncoding.length_le (encA := encV) (encL := encM) x.points
  have h2 : (encRadiusInput x).length = 2 * (encNat x.k).length + 1 +
      (2 * (encRat x.wmin).length + 1 +
        (2 * (encRat x.R).length + 1 + (encM x.points).length)) := by
    change (encPair encNat (encPair encRat (encPair encRat encM))
      (x.k, x.wmin, x.R, x.points)).length = _
    simp only [length_encPair]
  omega

theorem cbits_le (y : RadiusInput × ℕ) :
    cbits y ≤ 16 * ((encPair encRadiusInput encUnary y).length + 2) ^ 2 := by
  unfold cbits coinBits
  have h1 := length_points_le y.1
  have h2 : (encPair encRadiusInput encUnary y).length =
      2 * (encRadiusInput y.1).length + 1 + y.2 := by
    rw [length_encPair, encUnary_apply, List.length_replicate]
  have h3 : min y.1.points.length y.1.k ≤ (encPair encRadiusInput encUnary y).length + 2 := by
    have := min_le_left y.1.points.length y.1.k
    omega
  have h4 : y.1.points.length + 8 ≤ 4 * ((encPair encRadiusInput encUnary y).length + 2) := by
    omega
  calc min y.1.points.length y.1.k * (y.1.points.length + 8)
      ≤ ((encPair encRadiusInput encUnary y).length + 2) *
          (4 * ((encPair encRadiusInput encUnary y).length + 2)) := Nat.mul_le_mul h3 h4
    _ ≤ 16 * ((encPair encRadiusInput encUnary y).length + 2) ^ 2 := by nlinarith

/-- **The algorithm only reads the first `min n k · (n + 8)` coins.** -/
theorem srCoreL_take (x : RadiusInput) (c : List Bool) (Lb : ℕ) :
    srCoreL x (c.take (min x.points.length x.k * coinBits x.points.length)) Lb =
      srCoreL x c Lb := by
  rw [srCoreL_eq, srCoreL_eq]
  by_cases h : NumGuard x.k x.wmin x.R x.points.length (dim x.points) ∧
      LeadMinorsPos (secondMoment (Colinear.pointsFun x.points))
  · exact srCore_take (by rw [min_eq_right h.1.k_le]) c Lb
  · rw [srCore_of_not_guard _ _ h, srCore_of_not_guard _ _ h]

/-! ### The padded input -/

/-- The list program on the input with the budget, and the coins. -/
def algP (z : (RadiusInput × ℕ) × List Bool) : Output := srCoreL z.1.1 z.2 z.1.2

/-- The padded input: the input, the budget in unary, and the coins. -/
def padF (C₁ : ℕ) (xr : RadiusInput × List Bool) : (RadiusInput × ℕ) × List Bool :=
  ((xr.1, bpow (xr.1, bexp C₁ xr.1)), xr.2)

/-- **The algorithm on the padded input.** -/
theorem srAlg_eq_algP (C₁ : ℕ) (xr : RadiusInput × List Bool) :
    srAlg C₁ xr = algP ((padF C₁ xr).1, (padF C₁ xr).2.take (cbits (padF C₁ xr).1)) := by
  rw [algP, padF]
  dsimp only
  rw [cbits, srCoreL_take, srCoreL_eq, ← budgetOf_eq]
  rfl

/-! ### The bound -/

/-- `X = ⌈R²⌉ + logInv w + 1`, the exponent of `radiusTime 1`. -/
def xexp (x : RadiusInput) : ℕ := ⌈x.R ^ 2⌉₊ + logInv x.wmin + 1

/-- The scale `W = (|x| + 2)^((C₁ + 2) X)`: the input, the exponent of the budget and the budget
are at most `W`. -/
def wsc (C₁ : ℕ) (x : RadiusInput) : ℕ := ((encRadiusInput x).length + 2) ^ ((C₁ + 2) * xexp x)

theorem add_two_le_wsc (C₁ : ℕ) (x : RadiusInput) : (encRadiusInput x).length + 2 ≤ wsc C₁ x := by
  unfold wsc xexp
  calc (encRadiusInput x).length + 2 = ((encRadiusInput x).length + 2) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem bexp_add_one_le_wsc (C₁ : ℕ) (x : RadiusInput) : bexp C₁ x + 1 ≤ wsc C₁ x := by
  unfold wsc bexp
  set X := xexp x
  have h1 : C₁ * X + 1 ≤ (C₁ + 2) * X := by
    have : 1 ≤ X := by unfold X xexp; omega
    nlinarith
  calc C₁ * (⌈x.R ^ 2⌉₊ + logInv x.wmin + 1) + 1 = C₁ * X + 1 := rfl
    _ ≤ 2 ^ ((C₁ + 2) * X) := h1.trans Nat.lt_two_pow_self.le
    _ ≤ _ := Nat.pow_le_pow_left (by omega) _

theorem bpow_le_wsc (C₁ : ℕ) (x : RadiusInput) : bpow (x, bexp C₁ x) ≤ wsc C₁ x := by
  unfold bpow wsc bexp xexp
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))

theorem wsc_pow_eq (C₁ P : ℕ) (x : RadiusInput) :
    wsc C₁ x ^ P = radiusTime (P * (C₁ + 2)) x := by
  unfold wsc radiusTime xexp
  rw [← pow_mul]
  congr 1
  ring

/-- The arithmetic of the bound: with `Y = W^(dE + dg + D + 2)`, every term is `O(Y + R)`. -/
theorem bound_arith {A R E Lg P1 P2 Q W Y cE dE cg dg c₁ D : ℕ} (hAW : A + 2 ≤ W)
    (hEW : E + 1 ≤ W) (hLW : Lg ≤ W) (hAR : A ≤ R) (hY : Y = W ^ (dE + dg + D + 2))
    (hP1 : P1 = 2 * A + 1 + E) (hP2 : P2 = 2 * A + 1 + Lg) (hQ : Q ≤ 2 * P2 + 1 + R) :
    R + (R + (A + (cE * (A + 1) ^ dE + (E + 1) ^ 2) + cg * (P1 + 1) ^ dg + (Lg + 1) ^ 2)) + R +
        c₁ * ((P2 + 2) ^ D + Q + 1) ≤
      (10 + cE + cg * 3 ^ dg + c₁ * (3 ^ D + 10)) * (Y + R + 1) := by
  have hW1 : 1 ≤ W := by omega
  have hWY : ∀ k ≤ dE + dg + D + 2, W ^ k ≤ Y := fun k hk => hY ▸ Nat.pow_le_pow_right hW1 hk
  have hWleY : W ≤ Y := by simpa using hWY 1 (by omega)
  have e1 : (A + 1) ^ dE ≤ Y := (Nat.pow_le_pow_left (by omega) _).trans (hWY dE (by omega))
  have e2 : (E + 1) ^ 2 ≤ Y := (Nat.pow_le_pow_left hEW _).trans (hWY 2 (by omega))
  have e3 : (P1 + 1) ^ dg ≤ 3 ^ dg * Y :=
    calc (P1 + 1) ^ dg ≤ (3 * W) ^ dg := Nat.pow_le_pow_left (by omega) _
      _ = 3 ^ dg * W ^ dg := mul_pow _ _ _
      _ ≤ 3 ^ dg * Y := Nat.mul_le_mul_left _ (hWY dg (by omega))
  have e4 : (Lg + 1) ^ 2 ≤ 4 * Y :=
    calc (Lg + 1) ^ 2 ≤ (2 * W) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ = 4 * W ^ 2 := by ring
      _ ≤ 4 * Y := Nat.mul_le_mul_left _ (hWY 2 (by omega))
  have e5 : (P2 + 2) ^ D ≤ 3 ^ D * Y :=
    calc (P2 + 2) ^ D ≤ (3 * W) ^ D := Nat.pow_le_pow_left (by omega) _
      _ = 3 ^ D * W ^ D := mul_pow _ _ _
      _ ≤ 3 ^ D * Y := Nat.mul_le_mul_left _ (hWY D (by omega))
  have f1 : cE * (A + 1) ^ dE ≤ cE * (Y + R + 1) := Nat.mul_le_mul_left _ (by omega)
  have f3 : cg * (P1 + 1) ^ dg ≤ cg * 3 ^ dg * (Y + R + 1) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (e3.trans (Nat.mul_le_mul_left _ (by omega)))
  have f5 : c₁ * ((P2 + 2) ^ D + Q + 1) ≤ c₁ * (3 ^ D + 10) * (Y + R + 1) := by
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have g1 : 3 ^ D * Y ≤ 3 ^ D * (Y + R + 1) := Nat.mul_le_mul_left _ (by omega)
    have g2 : (3 ^ D + 10) * (Y + R + 1) = 3 ^ D * (Y + R + 1) + 10 * (Y + R + 1) := by ring
    omega
  have hK : (10 + cE + cg * 3 ^ dg + c₁ * (3 ^ D + 10)) * (Y + R + 1) =
      10 * (Y + R + 1) + cE * (Y + R + 1) + cg * 3 ^ dg * (Y + R + 1) +
        c₁ * (3 ^ D + 10) * (Y + R + 1) := by ring
  omega

end RT

open RT in
/-- **The algorithm of Theorem 1.3 runs in time `radiusTime C`** for some `C`. -/
theorem srAlg_runsInTime (C₁ : ℕ) :
    ∃ C : ℕ, RunsInTime encRadiusInput encOutput (srAlg C₁) (radiusTime C) := by
  -- The list program on the padded input, keeping the first `cbits` coins.
  obtain ⟨D, hD⟩ := exists_computableInTimeAndSpace_take srCoreL_polytime cbits_polytime cbits_le
  obtain ⟨c₁, hc₁⟩ := hD D le_rfl
  have hA := hc₁.computableInO
  -- The budget in unary.
  obtain ⟨cE, dE, hE⟩ := exists_inO_pow (bexp_polytime C₁)
  have hEU := ComputableInO.natToUnary.comp' hE
  have hxE := (ComputableInO.id' (encMid := encRadiusInput)).prod hEU
  obtain ⟨cg, dg, hg⟩ := exists_inO_pow bpow_polytime
  have hL := ComputableInO.natToUnary.comp' (hg.comp' hxE)
  have hx : ComputableInO (fun xr : RadiusInput × List Bool ↦ xr.1)
      (encPair encRadiusInput encBits) encRadiusInput
      (fun xr ↦ (encPair encRadiusInput encBits xr).length)
      (fun xr ↦ (encPair encRadiusInput encBits xr).length) :=
    ComputableInO.fst encRadiusInput encBits
  have hpad := (hx.prod (hL.comp' hx)).prod (ComputableInO.snd encRadiusInput encBits)
  have hall := hA.comp' (g := padF C₁) hpad
  -- Every bound is `O(Y + |(x, c)|)`, `Y = W^(dE + dg + D + 2)`.
  have hR : ∀ a : RadiusInput × List Bool, (encRadiusInput a.1).length ≤
      (encPair encRadiusInput encBits a).length := fun a => by
    rw [length_encPair]
    omega
  have hP1 : ∀ a : RadiusInput × List Bool,
      ((encPair encRadiusInput encUnary) (a.1, bexp C₁ a.1)).length =
        2 * (encRadiusInput a.1).length + 1 + bexp C₁ a.1 := fun a => by
    rw [length_encPair, encUnary_apply, List.length_replicate]
  have hP2 : ∀ a : RadiusInput × List Bool,
      ((encPair encRadiusInput encUnary) (padF C₁ a).1).length =
        2 * (encRadiusInput a.1).length + 1 + bpow (a.1, bexp C₁ a.1) := fun a => by
    rw [length_encPair, encUnary_apply, List.length_replicate]
    rfl
  have hQ : ∀ a : RadiusInput × List Bool,
      ((encPair (encPair encRadiusInput encUnary) encBits) (padF C₁ a)).length ≤
        2 * ((encPair encRadiusInput encUnary) (padF C₁ a).1).length + 1 +
          (encPair encRadiusInput encBits a).length := fun a => by
    have h1 : ((encPair (encPair encRadiusInput encUnary) encBits) (padF C₁ a)).length =
        2 * ((encPair encRadiusInput encUnary) (padF C₁ a).1).length + 1 + (encBits a.2).length :=
      length_encPair (p := padF C₁ a)
    have h2 : (encPair encRadiusInput encBits a).length =
        2 * (encRadiusInput a.1).length + 1 + (encBits a.2).length := length_encPair (p := a)
    omega
  set P := dE + dg + D + 2 with hPdef
  set K := 10 + cE + cg * 3 ^ dg + c₁ * (3 ^ D + 10) with hKdef
  have hb : ∀ a : RadiusInput × List Bool,
      (encPair encRadiusInput encBits a).length +
            ((encPair encRadiusInput encBits a).length +
              ((encRadiusInput a.1).length + (cE * ((encRadiusInput a.1).length + 1) ^ dE +
                (bexp C₁ a.1 + 1) ^ 2) +
                  cg * (((encPair encRadiusInput encUnary) (a.1, bexp C₁ a.1)).length + 1) ^ dg +
                (bpow (a.1, bexp C₁ a.1) + 1) ^ 2)) +
          (encPair encRadiusInput encBits a).length +
        c₁ * ((((encPair encRadiusInput encUnary) (padF C₁ a).1).length + 2) ^ D +
              ((encPair (encPair encRadiusInput encUnary) encBits) (padF C₁ a)).length + 1) ≤
      K * (wsc C₁ a.1 ^ P + (encPair encRadiusInput encBits a).length + 1) := fun a =>
    bound_arith (add_two_le_wsc C₁ a.1) (bexp_add_one_le_wsc C₁ a.1) (bpow_le_wsc C₁ a.1) (hR a)
      rfl (hP1 a) (hP2 a) (hQ a)
  have hb' : ∀ a : RadiusInput × List Bool,
      (encPair encRadiusInput encBits a).length +
            ((encPair encRadiusInput encBits a).length +
              ((encRadiusInput a.1).length + (cE * ((encRadiusInput a.1).length + 1) ^ dE +
                bexp C₁ a.1) +
                  cg * (((encPair encRadiusInput encUnary) (a.1, bexp C₁ a.1)).length + 1) ^ dg +
                bpow (a.1, bexp C₁ a.1))) +
          (encPair encRadiusInput encBits a).length +
        c₁ * ((((encPair encRadiusInput encUnary) (padF C₁ a).1).length + 2) ^ D +
              ((encPair (encPair encRadiusInput encUnary) encBits) (padF C₁ a)).length + 1) ≤
      K * (wsc C₁ a.1 ^ P + (encPair encRadiusInput encBits a).length + 1) := fun a => by
    have h := hb a
    have h1 : bexp C₁ a.1 ≤ (bexp C₁ a.1 + 1) ^ 2 := by nlinarith
    have h2 : bpow (a.1, bexp C₁ a.1) ≤ (bpow (a.1, bexp C₁ a.1) + 1) ^ 2 := by nlinarith
    omega
  obtain ⟨c, hc, -⟩ := hall.mono K hb hb'
  refine ⟨P * (C₁ + 2), c, ?_⟩
  have heq : srAlg C₁ = fun xr ↦
      algP ((padF C₁ xr).1, (padF C₁ xr).2.take (cbits (padF C₁ xr).1)) :=
    funext (srAlg_eq_algP C₁)
  rw [heq]
  refine hc.mono (fun a ↦ ?_) (fun a ↦ ?_) <;>
    exact Nat.mul_le_mul_left c (Nat.add_le_add_right (Nat.add_le_add_right
      (wsc_pow_eq C₁ P a.1).le _) _)

end BS23.SmallRadius
