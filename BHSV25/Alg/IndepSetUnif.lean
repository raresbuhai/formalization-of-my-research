module

public import BHSV25.Alg.IndepSetStopCorrect
public import BHSV25.Alg.IndepSetFull
public import BHSV25.TimePad

/-!
# Theorem 7.20 and Corollary 7.21 (Theorem 1.1)

[BHSV25, Theorem 7.20] (`BHSV25.Alg.indepSet_bottomRank`): for every `c > 0`, `λ ∈ (0, 1)` and
`γ ∈ (0, 1/4)`, one algorithm that outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices on regular graphs with an independent set of
`(1/2 - γ) n` vertices, and runs in time
`(D / (1 - λ))^D (D (1 + (1 - λ) / γ))^(D (t + 1)) · m^C` on the regular graphs with at most `t`
eigenvalues at most `-λ`, for every `t`, with `C` independent of all parameters and `D` depending
only on `c`. Corollary 7.21 (`BHSV25.Alg.indepSet_topRank`) follows from Corollary 4.2 (at most
`t` eigenvalues above `λ < 1/2` leave at most `t / λ²` at most `-√(2λ)`).

The algorithm is `BHSV25.Alg.indepAlgU`, which finds the number of rounds itself, with a
padding `2^(⌈log₂ (3 + 12 K)⌉ T)` for the stopping round `T ≤ t`
(`BHSV25.runsInTimeWith_graph_fix_pad`).
**The parameters**, for `c₁ = min(c, 1)` and `c'' = η = c₁/32`:
* `K = ⌈A (1 + (1 - λ)/γ)⌉` with `A = 32 (1 + 32/c₁) / c + 1`, so that the precision `4/K`
  costs `(1 + 1/η) (4/K)² ≤ (c/2) γ / (1 - λ)`, as for `t` rounds;
* `a = ⌈40 (3 + K/2) / c''⌉` and `β = ⌈4 / c''⌉`;
* `s = ⌈1 / (c'' (1 - λ))⌉` and `r = ⌊s (1 - λ)⌋`, so that
  `(1 - c'') (1 - λ) ≤ r / s ≤ 1 - λ`.

The threshold of the stopping round needs `λ` to the precision `c'' (1 - λ)`, so the machine
reads a fraction with denominator about `1 / (c'' (1 - λ))`: this costs the factor
`(D / (1 - λ))^D`, which does not depend on `t`. The loss `(1 - c'')²` in `1 - θ` is absorbed as
`(1 + c'') 4 / (1 - c'')² ≤ 4 + c/2` (`BHSV25.Alg.coef_loss_sq_le`).
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM

/-- The coefficient of the loss: `(1 + c'') 4 / ((1 - c'')² (1 - λ)) ≤ (4 + c/2) / (1 - λ)` for
`c'' = c₁ / 32`, `c₁ ≤ min(c, 1)`. -/
theorem coef_loss_sq_le {c c₁ cc lam : ℝ} (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hl1 : lam < 1) :
    (1 + cc) * 4 / ((1 - cc) ^ 2 * (1 - lam)) ≤ (4 + c / 2) / (1 - lam) := by
  have hl' : 0 < 1 - lam := by linarith
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 / 32 := by rw [hcc]; linarith
  have hsq : 0 < (1 - cc) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hsq hl') hl']
  -- `(1 + x) ≤ (1 + 4 x) (1 - x)²` for `0 ≤ x ≤ 1/7`
  have h2 : (1 + cc) * 4 ≤ (4 + 16 * cc) * (1 - cc) ^ 2 := by
    nlinarith [mul_nonneg hcc0.le (by linarith : (0 : ℝ) ≤ 1 - 7 * cc), pow_nonneg hcc0.le 3]
  have h3 : 16 * cc ≤ c / 2 := by rw [hcc]; linarith
  have h1 : (1 + cc) * 4 ≤ (4 + c / 2) * (1 - cc) ^ 2 :=
    h2.trans (mul_le_mul_of_nonneg_right (by linarith) hsq.le)
  calc (1 + cc) * 4 * (1 - lam) ≤ (4 + c / 2) * (1 - cc) ^ 2 * (1 - lam) :=
        mul_le_mul_of_nonneg_right h1 hl'.le
    _ = (4 + c / 2) * ((1 - cc) ^ 2 * (1 - lam)) := by ring

/-! ### The parameters -/

/-- The length of the parameters `(a, K, β, r, s)` in unary. -/
theorem unif_length_encUPar (p : UPar) :
    (encUPar p).length = 2 * p.1 + 2 * p.2.1 + 2 * p.2.2.1 + 2 * p.2.2.2.1 + p.2.2.2.2 + 4 := by
  simp [encUnary_apply]
  ring

/-- The parameter `β = ⌈4 / c''⌉` of the threshold: `c''/5 ≤ 1/β ≤ c''/4` and
`β ≤ 4 / c'' + 1`. -/
theorem unif_beta {cc : ℝ} (hcc0 : 0 < cc) (hcc1 : cc ≤ 1) {β : ℕ} (hβ : β = ⌈4 / cc⌉₊) :
    cc / 5 ≤ 1 / (β : ℝ) ∧ 1 / (β : ℝ) ≤ cc / 4 ∧ (β : ℝ) ≤ 4 / cc + 1 := by
  have hge : 4 / cc ≤ β := hβ ▸ Nat.le_ceil _
  have hlt : (β : ℝ) < 4 / cc + 1 := hβ ▸ Nat.ceil_lt_add_one (by positivity)
  have h4 : 0 < 4 / cc := by positivity
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le h4 hge
  refine ⟨?_, ?_, hlt.le⟩
  · rw [div_le_div_iff₀ (by norm_num) hβ0]
    have h := mul_le_mul_of_nonneg_left hlt.le hcc0.le
    have e : cc * (4 / cc + 1) = 4 + cc := by field_simp
    linarith
  · rw [div_le_div_iff₀ hβ0 (by norm_num)]
    have h := mul_le_mul_of_nonneg_left hge hcc0.le
    have e : cc * (4 / cc) = 4 := by field_simp
    linarith

/-- The fraction `r / s` of the threshold, for `s = ⌈1 / (c'' v)⌉` and `r = ⌊s v⌋`:
`0 < r ≤ s`, `(1 - c'') v ≤ r / s ≤ v` and `s ≤ 1 / (c'' v) + 1`. -/
theorem unif_ratio {cc v : ℝ} (hcc0 : 0 < cc) (hcc1 : cc ≤ 1 / 32) (hv0 : 0 < v) (hv1 : v ≤ 1)
    {r s : ℕ} (hs : s = ⌈1 / (cc * v)⌉₊) (hr : r = ⌊(s : ℝ) * v⌋₊) :
    0 < r ∧ r ≤ s ∧ (1 - cc) * v ≤ (r : ℝ) / s ∧ (r : ℝ) / s ≤ v ∧
      (s : ℝ) ≤ 1 / (cc * v) + 1 := by
  have hccv : 0 < cc * v := mul_pos hcc0 hv0
  have hsge : 1 / (cc * v) ≤ s := hs ▸ Nat.le_ceil _
  have hslt : (s : ℝ) < 1 / (cc * v) + 1 := hs ▸ Nat.ceil_lt_add_one (by positivity)
  have hccv1 : cc * v ≤ 1 / 32 := by nlinarith
  have hbig : 32 ≤ 1 / (cc * v) := by rw [le_div_iff₀ hccv]; linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have h1 : 1 ≤ cc * v * s := by
    have h := mul_le_mul_of_nonneg_left hsge hccv.le
    have e : cc * v * (1 / (cc * v)) = 1 := by field_simp
    linarith
  have hic : 32 ≤ 1 / cc := by rw [le_div_iff₀ hcc0]; linarith
  have hsv : 1 / cc ≤ s * v := by
    rw [div_le_iff₀ hcc0]
    linarith
  have hrle : (r : ℝ) ≤ s * v := by rw [hr]; exact Nat.floor_le (by positivity)
  have hrgt : (s : ℝ) * v - 1 < r := by
    have := Nat.lt_floor_add_one ((s : ℝ) * v)
    rw [← hr] at this
    linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hrs : (r : ℝ) ≤ s := hrle.trans (by nlinarith)
  refine ⟨by exact_mod_cast hr0, by exact_mod_cast hrs, ?_, ?_, hslt.le⟩
  · rw [le_div_iff₀ hs0]
    nlinarith
  · rw [div_le_iff₀ hs0]
    linarith

/-- **The size of the parameters**: `|(a, K, β, r, s)| + 1 ≤ 400 (A / c'') W / v` for
`K ≤ 2 A W`, `a ≤ 40 (3 + K/2) / c'' + 1`, `β ≤ 4 / c'' + 1` and `r ≤ s ≤ 1 / (c'' v) + 1`. -/
theorem unif_length_le {cc A₁ W v : ℝ} (hcc0 : 0 < cc) (hcc1 : cc ≤ 1) (hA₁ : 1 ≤ A₁)
    (hW : 1 ≤ W) (hv0 : 0 < v) (hv1 : v ≤ 1) {a K β r s : ℕ} (hK : (K : ℝ) ≤ 2 * A₁ * W)
    (ha : (a : ℝ) ≤ 40 * (3 + K / 2 : ℝ) / cc + 1) (hβ : (β : ℝ) ≤ 4 / cc + 1)
    (hs : (s : ℝ) ≤ 1 / (cc * v) + 1) (hrs : r ≤ s) :
    ((encUPar (a, K, β, r, s)).length : ℝ) + 1 ≤ 400 * A₁ / cc * W / v := by
  rw [unif_length_encUPar]
  push_cast
  obtain ⟨R, hR⟩ : ∃ x : ℝ, x = A₁ * (W / v) / cc := ⟨_, rfl⟩
  have hWv : W ≤ W / v := by rw [le_div_iff₀ hv0]; nlinarith
  have hic : 1 ≤ 1 / cc := by rw [le_div_iff₀ hcc0]; linarith
  have hAW : 1 ≤ A₁ * W := by nlinarith
  have hAWv : A₁ * W ≤ A₁ * (W / v) := mul_le_mul_of_nonneg_left hWv (by linarith)
  have hR1 : A₁ * W / cc ≤ R := by
    rw [hR]
    exact div_le_div_of_nonneg_right hAWv hcc0.le
  have hR2 : A₁ * W ≤ A₁ * W / cc := by
    rw [le_div_iff₀ hcc0]
    nlinarith
  have hR3 : 1 / cc ≤ A₁ * W / cc := div_le_div_of_nonneg_right hAW hcc0.le
  have hR4 : 1 / (cc * v) ≤ R := by
    have e : 1 / (cc * v) = 1 / v / cc := by field_simp
    have h1 : 1 / v ≤ W / v := div_le_div_of_nonneg_right hW hv0.le
    have h2 : W / v ≤ A₁ * (W / v) := le_mul_of_one_le_left (by positivity) hA₁
    rw [e, hR]
    exact div_le_div_of_nonneg_right (h1.trans h2) hcc0.le
  have hKc : (K : ℝ) / cc ≤ 2 * (A₁ * W / cc) := by
    rw [mul_div_assoc', ← mul_assoc]
    exact div_le_div_of_nonneg_right hK hcc0.le
  have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have ea : 40 * (3 + K / 2 : ℝ) / cc = 120 * (1 / cc) + 20 * (K / cc) := by
    field_simp
    ring
  have hR5 : 1 ≤ R := hic.trans (hR3.trans hR1)
  have ha' : (a : ℝ) ≤ 161 * R := by
    rw [ea] at ha
    linarith
  have hK' : (K : ℝ) ≤ 2 * R := by linarith
  have hβ' : (β : ℝ) ≤ 5 * R := by
    have e4 : 4 / cc = 4 * (1 / cc) := by ring
    linarith
  have hs' : (s : ℝ) ≤ 2 * R := by linarith
  have e : 400 * A₁ / cc * W / v = 400 * R := by
    rw [hR]
    field_simp
  rw [e]
  linarith

/-- **The padding**: for `K ≥ 1` and at most `t` rounds, `(2^padU + 1) (2^0 + 1) ≤ 4 (30 K)^t`,
as `2^⌈log₂ (3 + 12 K)⌉ ≤ 2 (3 + 12 K) ≤ 30 K`. -/
theorem unif_pad_le {a K β r s t : ℕ} (x : ℕ × List Bool) (hK : 1 ≤ K)
    (hR : roundsU (a, K, β, r, s) x ≤ t) :
    (2 ^ padU (a, K, β, r, s) x + 1) * (2 ^ 0 + 1) ≤ 4 * (30 * K) ^ t := by
  unfold padU
  have h1 : 2 ^ Nat.clog 2 (3 + 12 * K) ≤ 30 * K := by
    have h := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < 3 + 12 * K)
    have hpos : 0 < Nat.clog 2 (3 + 12 * K) := Nat.clog_pos one_lt_two (by omega)
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (3 + 12 * K) = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk, Nat.pred_succ] at h
    rw [hk, pow_succ]
    omega
  have h2 : 2 ^ (Nat.clog 2 (3 + 12 * K) * roundsU (a, K, β, r, s) x) ≤ (30 * K) ^ t := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left h1 _).trans (Nat.pow_le_pow_right (by omega) hR)
  have h3 : 1 ≤ (30 * K) ^ t := Nat.one_le_pow _ _ (by omega)
  simp only [pow_zero]
  omega

/-- **The budget**: `(3 + 12 K)^T ≤ 2^padU` for the stopping round `T`. -/
theorem unif_budget (a K β r s : ℕ) (x : ℕ × List Bool) :
    (3 + 12 * K) ^ roundsU (a, K, β, r, s) x ≤ 2 ^ padU (a, K, β, r, s) x := by
  unfold padU
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) _

/-- **The factor**: if `L ≤ M W / v` and `Z ≤ 4 (60 A W)^t` with `A, W ≥ 1` and `0 < v ≤ 1`, then
`c₀ L^C₀ Z^C₀ ≤ (D / v)^D (D W)^(D (t + 1))` for every `D ≥ max(1, c₀ M^C₀ 4^C₀) · 60 A` with
`D ≥ C₀ + 1`. -/
theorem unif_factor_le (c₀ C₀ : ℕ) {M A W v : ℝ} (hA : 1 ≤ A) (hW : 1 ≤ W) (hv0 : 0 < v)
    (hv1 : v ≤ 1) {D t : ℕ} (hD : max 1 ((c₀ : ℝ) * M ^ C₀ * 4 ^ C₀) * 60 * A ≤ D)
    (hDC : C₀ + 1 ≤ D) {L Z : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ M * W / v) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ 4 * (60 * A * W) ^ t) :
    (c₀ : ℝ) * L ^ C₀ * Z ^ C₀ ≤ ((D : ℝ) / v) ^ D * ((D : ℝ) * W) ^ (D * (t + 1)) := by
  obtain ⟨Y, hY⟩ : ∃ x : ℝ, x = max 1 ((c₀ : ℝ) * M ^ C₀ * 4 ^ C₀) := ⟨_, rfl⟩
  rw [← hY] at hD
  have hY1 : 1 ≤ Y := hY ▸ le_max_left _ _
  have hYc : (c₀ : ℝ) * M ^ C₀ * 4 ^ C₀ ≤ Y := hY ▸ le_max_right _ _
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = 60 * A * W := ⟨_, rfl⟩
  rw [← hX] at hZ
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hWX : W ≤ X := by rw [hX]; nlinarith
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hu1 : 1 ≤ 1 / v := by rw [le_div_iff₀ hv0]; linarith
  have hDW1 : (1 : ℝ) ≤ D * W := by nlinarith
  -- `c₀ L^C₀ Z^C₀ ≤ Y (1/v)^C₀ X^(C₀ (t + 1))`
  have h1 : (c₀ : ℝ) * L ^ C₀ * Z ^ C₀ ≤ (1 / v) ^ C₀ * (Y * X ^ (C₀ * (t + 1))) := by
    calc (c₀ : ℝ) * L ^ C₀ * Z ^ C₀ ≤ c₀ * (M * W / v) ^ C₀ * (4 * X ^ t) ^ C₀ :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL _) (Nat.cast_nonneg _))
            (pow_le_pow_left₀ hZ0 hZ _) (by positivity)
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hL0.trans hL) _))
      _ = (1 / v) ^ C₀ * ((c₀ * M ^ C₀ * 4 ^ C₀) * (W ^ C₀ * X ^ (t * C₀))) := by
          ring
      _ ≤ (1 / v) ^ C₀ * (Y * (X ^ C₀ * X ^ (t * C₀))) := by
          gcongr
      _ = (1 / v) ^ C₀ * (Y * X ^ (C₀ * (t + 1))) := by
          rw [← pow_add]
          ring_nf
  -- `(1/v)^C₀ ≤ (D/v)^D`
  have h2 : (1 / v) ^ C₀ ≤ ((D : ℝ) / v) ^ D := by
    calc (1 / v) ^ C₀ ≤ (1 / v) ^ D := pow_le_pow_right₀ hu1 (by omega)
      _ ≤ ((D : ℝ) / v) ^ D :=
          pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hD1 hv0.le) _
  -- `Y X^(C₀ (t + 1)) ≤ (D W)^(D (t + 1))`
  have h3 : Y * X ^ (C₀ * (t + 1)) ≤ ((D : ℝ) * W) ^ (D * (t + 1)) := by
    set m := (C₀ + 1) * (t + 1) with hm
    have hm1 : 1 ≤ m := by rw [hm]; nlinarith
    have hYX : Y * X ≤ D * W := by
      have e : Y * X = (Y * 60 * A) * W := by rw [hX]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hD (by linarith)
    calc Y * X ^ (C₀ * (t + 1)) ≤ Y ^ m * X ^ m :=
          mul_le_mul (le_self_pow₀ hY1 (by omega))
            (pow_le_pow_right₀ hX1 (Nat.mul_le_mul_right _ (by omega)))
            (by positivity) (by positivity)
      _ = (Y * X) ^ m := (mul_pow _ _ _).symm
      _ ≤ ((D : ℝ) * W) ^ m := pow_le_pow_left₀ (by positivity) hYX _
      _ ≤ ((D : ℝ) * W) ^ (D * (t + 1)) :=
          pow_le_pow_right₀ hDW1 (Nat.mul_le_mul_right _ hDC)
  exact h1.trans (mul_le_mul h2 h3 (by positivity) (by positivity))

/-! ### The guarantee -/

open Classical in
/-- **The guarantee for the chosen parameters**, on every regular graph: the output of
`BHSV25.Alg.indepAlgU` with the budget `2^padU` has at least `(1/2 - γ - (4 + c) γ / (1 - λ)) n`
vertices if the graph has an independent set of `(1/2 - γ) n` vertices, with `η = c''`. -/
theorem unif_card_final (G : Graph) (hreg : G.IsRegular) {lam : ℝ} (hl1 : lam < 1)
    {c c₁ cc γ A₁ W : ℝ} (hc : 0 < c) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hγ0 : 0 < γ) (hA₁ : A₁ = 32 * (1 + 32 / c₁) / c + 1)
    (hW : W = 1 + (1 - lam) / γ) {a K β r s : ℕ} (hK : 0 < K) (hKge : A₁ * W ≤ K)
    (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a) (hβ1 : cc / 5 ≤ 1 / (β : ℝ))
    (hβ2 : 1 / (β : ℝ) ≤ cc / 4) (hr : 0 < r) (hrs : r ≤ s)
    (hlo : (1 - cc) * (1 - lam) ≤ (r : ℝ) / s) (hhi : (r : ℝ) / s ≤ 1 - lam)
    (hInd : G.HasIndepSet ((1 / 2 - γ) * G.1)) :
    (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤
      (G.vertexSet (indepAlgU (a, K, β, r, s)
        ((2 ^ padU (a, K, β, r, s) (G.1, adjTable G), 2 ^ 0), (G.1, adjTable G)))).card := by
  obtain ⟨I, hI, hIcard⟩ := hInd
  obtain ⟨d, hd⟩ := hreg
  have hl' : 0 < 1 - lam := by linarith
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 / 32 := by rw [hcc]; linarith
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  by_cases hd0 : d = 0
  · -- no edges: all vertices
    subst hd0
    have h : G.1 ≤ (G.vertexSet (indepAlgU (a, K, β, r, s)
        ((2 ^ padU (a, K, β, r, s) (G.1, adjTable G), 2 ^ 0), (G.1, adjTable G)))).card :=
      card_indepAlg_of_degree_zero _ G hd
    have h' : (G.1 : ℝ) ≤ (G.vertexSet (indepAlgU (a, K, β, r, s)
        ((2 ^ padU (a, K, β, r, s) (G.1, adjTable G), 2 ^ 0), (G.1, adjTable G)))).card := by
      exact_mod_cast h
    have hn' : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    have hloss0 : 0 ≤ (4 + c) * γ / (1 - lam) := by positivity
    have : (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ G.1 := by nlinarith
    exact this.trans h'
  have hmain := card_indepAlgU_ge G hd hd0 hn hl1 le_rfl hcc0 hcc1 hK ha hβ1 hβ2 hr hrs hlo
    hhi _ (2 ^ 0) (unif_budget a K β r s _) hI hcc0
  have hg0 : 0 ≤ (G.1 : ℝ) / 2 - I.card := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith
  exact final_count_le hl1 hc (Nat.cast_nonneg _) hg0 (by linarith)
    (coef_loss_sq_le hc₁0 hc₁1 hc₁c hcc hl1) (coef_prec_le hc hc₁0 hcc hl1 hγ0 hA₁ hW hKge) hmain

open Classical in
/-- **Theorem 7.20** of [BHSV25]: for every `c > 0`, `λ ∈ (0, 1)` and `γ ∈ (0, 1/4)`, one
algorithm running in time `poly(n) · (1 - λ)^{-O(1)} · (γ / (1 - λ))^{-O(t)}` on regular graphs
with at most `t` eigenvalues at most `-λ`, for every `t`, that, on regular graphs with an
independent set of `(1/2 - γ) n` vertices, outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices. -/
theorem indepSet_bottomRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool, ∃ K : Graph → ℝ,
          RunsInTimeWith A encGraph Encoding.encBits K C ∧
          ∀ G : Graph, G.IsRegular →
            (∀ t : ℕ, (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
              K G ≤ ((D : ℝ) / (1 - lam)) ^ D * ((D : ℝ) * (1 + (1 - lam) / γ)) ^ (D * (t + 1))) ∧
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ (G.vertexSet (A G)).card) := by
  obtain ⟨c₀, C₀, hrun⟩ := runsInTimeWith_graph_fix_pad
    (V := fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ indepAlgU z.1 z.2)
    (F₁ := fun z : UPar × (ℕ × List Bool) ↦ padU z.1 z.2) (F₂ := fun _ ↦ 0)
    indepAlgU_polytime padU_polytime (ComputableInPolyTime.const 0)
  refine ⟨C₀, fun c hc ↦ ?_⟩
  -- the constants depending on `c`
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = min c 1 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := hc₁ ▸ lt_min hc one_pos
  have hc₁1 : c₁ ≤ 1 := hc₁ ▸ min_le_right _ _
  have hc₁c : c₁ ≤ c := hc₁ ▸ min_le_left _ _
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = c₁ / 32 := ⟨_, rfl⟩
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 / 32 := by rw [hcc]; linarith
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = 32 * (1 + 32 / c₁) / c + 1 := ⟨_, rfl⟩
  have hA₁1 : 1 ≤ A₁ := by
    have : 0 ≤ 32 * (1 + 32 / c₁) / c := by positivity
    rw [hA₁]
    linarith
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = 400 * A₁ / cc := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌈max 1 ((c₀ : ℝ) * M ^ C₀ * 4 ^ C₀) * 60 * A₁⌉₊ + C₀ + 1 :=
    ⟨_, rfl⟩
  have hDge : max 1 ((c₀ : ℝ) * M ^ C₀ * 4 ^ C₀) * 60 * A₁ ≤ D := by
    have := Nat.le_ceil (max 1 ((c₀ : ℝ) * M ^ C₀ * 4 ^ C₀) * 60 * A₁)
    rw [hD]
    push_cast
    linarith
  have hDC : C₀ + 1 ≤ D := by omega
  refine ⟨D, fun lam hl0 hl1 γ hγ0 hγ1 ↦ ?_⟩
  have hl' : 0 < 1 - lam := by linarith
  have hv1 : 1 - lam ≤ 1 := by linarith
  -- the parameters
  obtain ⟨W, hW⟩ : ∃ x : ℝ, x = 1 + (1 - lam) / γ := ⟨_, rfl⟩
  rw [← hW]
  have hW1 : 1 ≤ W := by
    rw [hW]
    have : 0 ≤ (1 - lam) / γ := div_nonneg hl'.le hγ0.le
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈A₁ * W⌉₊ := ⟨_, rfl⟩
  have hKge : A₁ * W ≤ K := hK ▸ Nat.le_ceil _
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := le_trans (by nlinarith) hKge
    exact_mod_cast this
  have hKle : (K : ℝ) ≤ 2 * A₁ * W := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ A₁ * W)
    rw [← hK] at this
    nlinarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈40 * (3 + K / 2 : ℝ) / cc⌉₊ := ⟨_, rfl⟩
  have hage : 40 * (3 + K / 2 : ℝ) / cc ≤ a := ha ▸ Nat.le_ceil _
  have hale : (a : ℝ) ≤ 40 * (3 + K / 2 : ℝ) / cc + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 40 * (3 + K / 2 : ℝ) / cc)
    rw [← ha] at this
    exact this.le
  obtain ⟨β, hβ⟩ : ∃ b : ℕ, b = ⌈4 / cc⌉₊ := ⟨_, rfl⟩
  obtain ⟨hβ1, hβ2, hβle⟩ := unif_beta hcc0 (by linarith) hβ
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ⌈1 / (cc * (1 - lam))⌉₊ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ⌊(s : ℝ) * (1 - lam)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hr0, hrs, hlo, hhi, hsle⟩ := unif_ratio hcc0 hcc1 hl' hv1 hs hr
  have hL := unif_length_le hcc0 (by linarith) hA₁1 hW1 hl' hv1 hKle hale hβle hsle hrs
  rw [← hM] at hL
  refine ⟨fun G ↦ indepAlgU (a, K, β, r, s)
      ((2 ^ padU (a, K, β, r, s) (G.1, adjTable G), 2 ^ 0), (G.1, adjTable G)),
    fun G ↦ (c₀ : ℝ) * (((encUPar (a, K, β, r, s)).length : ℝ) + 1) ^ C₀ *
      (((2 ^ padU (a, K, β, r, s) (G.1, adjTable G) + 1) * (2 ^ 0 + 1) : ℕ) : ℝ) ^ C₀,
    hrun (a, K, β, r, s), fun G hreg ↦ ⟨fun t ht ↦ ?_, isIndepSet_indepAlg _ G,
      unif_card_final G hreg hl1 hc hc₁0 hc₁1 hc₁c hcc hγ0 hA₁ hW hK1 hKge hage hβ1 hβ2 hr0
        hrs hlo hhi⟩⟩
  -- the running time
  have hR := roundsU_le G hreg hl1 ht hcc0 hcc1 hK1 hage hβ1 hβ2 hr0 hrs hhi
  have hZn := unif_pad_le (G.1, adjTable G) hK1 hR
  have hZ : (((2 ^ padU (a, K, β, r, s) (G.1, adjTable G) + 1) * (2 ^ 0 + 1) : ℕ) : ℝ) ≤
      4 * (60 * A₁ * W) ^ t := by
    have h1 : (((2 ^ padU (a, K, β, r, s) (G.1, adjTable G) + 1) * (2 ^ 0 + 1) : ℕ) : ℝ) ≤
        4 * (30 * (K : ℝ)) ^ t := by
      exact_mod_cast hZn
    refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ t)
      (by norm_num))
    linarith
  exact unif_factor_le c₀ C₀ hA₁1 hW1 hl' hv1 hDge hDC (by positivity) hL (by positivity) hZ

open Classical in
/-- **Theorem 1.1** of [BHSV25], full version (Corollary 7.21): for every `c > 0`,
`λ ∈ (0, 1/2)` and `γ ∈ (0, 1/4)`, one algorithm running in time
`poly(n) · (1 - √(2λ))^{-O(1)} · (γ / (1 - √(2λ)))^{-O(t/λ²)}` on regular graphs with at most `t`
eigenvalues larger than `λ` (`λ`-one-sided expanders for `t = 1`), for every `t`, that, on regular
graphs with an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n` vertices. -/
theorem indepSet_topRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 / 2 →
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool, ∃ K : Graph → ℝ,
          RunsInTimeWith A encGraph Encoding.encBits K C ∧
          ∀ G : Graph, G.IsRegular →
            (∀ t : ℕ, G.numEigGT lam ≤ t →
              K G ≤ ((D : ℝ) / (1 - Real.sqrt (2 * lam))) ^ D *
                ((D : ℝ) * (1 + (1 - Real.sqrt (2 * lam)) / γ)) ^
                  (D * (⌈(t : ℝ) / lam ^ 2⌉₊ + 1))) ∧
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
                (G.vertexSet (A G)).card) := by
  obtain ⟨C, hC⟩ := indepSet_bottomRank
  refine ⟨C, fun c hc ↦ ?_⟩
  obtain ⟨D, hD⟩ := hC c hc
  refine ⟨D, fun lam hl0 hl1 γ hγ0 hγ1 ↦ ?_⟩
  have hτ0 : 0 < Real.sqrt (2 * lam) := Real.sqrt_pos.2 (by linarith)
  have hτ1 : Real.sqrt (2 * lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  obtain ⟨A, K, hA, hcorr⟩ := hD (Real.sqrt (2 * lam)) hτ0 hτ1 γ hγ0 hγ1
  refine ⟨A, K, hA, fun G hreg ↦ ?_⟩
  obtain ⟨htime, hind, hsize⟩ := hcorr G hreg
  exact ⟨fun t ht ↦ htime _ (card_eig_le_neg_sqrt_le G hl0 hl1 ht), hind, hsize⟩

end BHSV25.Alg
