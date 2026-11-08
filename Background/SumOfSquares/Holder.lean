module

public import Background.SumOfSquares.Facts

/-!
# Comparing even pseudo-moments

For a degree-`ℓ` pseudo-expectation `Ẽ` and a polynomial `Y` with `2 t deg Y ≤ ℓ`, the even
pseudo-moments `a r = Ẽ[Y^(2r)]`, `r ≤ t`, form a log-convex sequence with `a 0 = 1`, by
Cauchy–Schwarz on `Y^(r-1) · Y^(r+1)`. So `a r ≤ a t^(r/t)`, as for true moments.

* `SoS.pow_le_pow_of_sq_le_mul`: a sequence of reals with `a 0 = 1`, `a r ≥ 0` and
  `a r² ≤ a (r-1) a (r+1)` for `1 ≤ r < t` has `a r^t ≤ a t^r` for `r ≤ t`.
* `SoS.PseudoExpectation.sq_apply_mul_le`: Cauchy–Schwarz in squared form,
  `Ẽ[f g]² ≤ Ẽ[f²] Ẽ[g²]`.
* `SoS.PseudoExpectation.pow_le_pow`: `Ẽ[Y^(2r)]^t ≤ Ẽ[Y^(2t)]^r` for `r ≤ t`.
* Consequences: `Ẽ[Y^(2r)] ≤ Ẽ[Y^(2t)]^(r/t)` (`apply_pow_le_rpow`),
  `Ẽ[Y²] ≤ Ẽ[Y^(2t)]^(1/t)` (`apply_sq_le_rpow`), `Ẽ[Y]^(2t) ≤ Ẽ[Y^(2t)]` (`pow_apply_le`) and
  `Ẽ[Y] ≤ Ẽ[Y^(2t)]^(1/(2t))` (`apply_le_rpow`); for products `Y = P Q`,
  `Ẽ[(PQ)^(2(t-m))] ≤ Ẽ[(PQ)^(2t)]^((t-m)/t)` (`apply_mul_pow_sub_le_rpow`) and
  `Ẽ[PQ] ≤ Ẽ[(PQ)^(2t)]^(1/(2t))` (`apply_mul_le_rpow`).
-/

@[expose] public section

namespace SoS

open MvPolynomial

/-! ### Log-convex sequences -/

/-- One step of log-convexity: if `a 0 = 1`, `a r ≥ 0` for `r ≤ t` and `a r² ≤ a (r-1) a (r+1)`
for `1 ≤ r < t`, then `a r^(r+1) ≤ a (r+1)^r` for `r < t`. -/
theorem pow_succ_le_pow_of_sq_le_mul {a : ℕ → ℝ} {t : ℕ} (h0 : a 0 = 1)
    (hnn : ∀ r ≤ t, 0 ≤ a r) (hlc : ∀ r, 1 ≤ r → r < t → a r ^ 2 ≤ a (r - 1) * a (r + 1)) :
    ∀ r < t, a r ^ (r + 1) ≤ a (r + 1) ^ r := by
  intro r
  induction r with
  | zero => intro _; simp [h0]
  | succ r ih =>
    intro hr
    have ih := ih (by omega)
    have h := hlc (r + 1) (by omega) hr
    rw [Nat.add_sub_cancel] at h
    have ha1 : 0 ≤ a (r + 1) := hnn _ hr.le
    have ha2 : 0 ≤ a (r + 1 + 1) := hnn _ hr
    -- `a (r+1)^r a (r+1)^(r+2) = (a (r+1)²)^(r+1) ≤ a r^(r+1) a (r+2)^(r+1)
    --   ≤ a (r+1)^r a (r+2)^(r+1)`.
    have key : a (r + 1) ^ r * a (r + 1) ^ (r + 1 + 1) ≤
        a (r + 1) ^ r * a (r + 1 + 1) ^ (r + 1) := by
      calc a (r + 1) ^ r * a (r + 1) ^ (r + 1 + 1) = (a (r + 1) ^ 2) ^ (r + 1) := by ring
        _ ≤ (a r * a (r + 1 + 1)) ^ (r + 1) := pow_le_pow_left₀ (sq_nonneg _) h _
        _ = a r ^ (r + 1) * a (r + 1 + 1) ^ (r + 1) := mul_pow _ _ _
        _ ≤ a (r + 1) ^ r * a (r + 1 + 1) ^ (r + 1) :=
          mul_le_mul_of_nonneg_right ih (pow_nonneg ha2 _)
    rcases ha1.eq_or_lt with h1 | h1
    · rw [← h1, zero_pow (by omega)]
      exact pow_nonneg ha2 _
    · exact le_of_mul_le_mul_left key (pow_pos h1 _)

/-- Log-convexity: if `a 0 = 1`, `a r ≥ 0` for `r ≤ t` and `a r² ≤ a (r-1) a (r+1)` for
`1 ≤ r < t`, then `a r^s ≤ a s^r` for `r ≤ s ≤ t`. -/
theorem pow_le_pow_of_sq_le_mul_of_le {a : ℕ → ℝ} {t : ℕ} (h0 : a 0 = 1)
    (hnn : ∀ r ≤ t, 0 ≤ a r) (hlc : ∀ r, 1 ≤ r → r < t → a r ^ 2 ≤ a (r - 1) * a (r + 1))
    {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ t) : a r ^ s ≤ a s ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [h0]
  have hstep := pow_succ_le_pow_of_sq_le_mul h0 hnn hlc
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
    have ih := ih (by omega)
    have hs' := hstep s (by omega)
    have har : 0 ≤ a r := hnn r (by omega)
    have has : 0 ≤ a s := hnn s (by omega)
    have has1 : 0 ≤ a (s + 1) := hnn (s + 1) hs
    -- Raise both sides to the power `s ≠ 0`.
    refine (pow_le_pow_iff_left₀ (pow_nonneg har _) (pow_nonneg has1 _)
      (show s ≠ 0 by omega)).1 ?_
    calc (a r ^ (s + 1)) ^ s = (a r ^ s) ^ (s + 1) := by ring
      _ ≤ (a s ^ r) ^ (s + 1) := pow_le_pow_left₀ (pow_nonneg har _) ih _
      _ = (a s ^ (s + 1)) ^ r := by ring
      _ ≤ (a (s + 1) ^ s) ^ r := pow_le_pow_left₀ (pow_nonneg has _) hs' _
      _ = (a (s + 1) ^ r) ^ s := by ring

/-- **Log-convexity**: if `a 0 = 1`, `a r ≥ 0` for `r ≤ t` and `a r² ≤ a (r-1) a (r+1)` for
`1 ≤ r < t`, then `a r^t ≤ a t^r` for `r ≤ t`. -/
theorem pow_le_pow_of_sq_le_mul {a : ℕ → ℝ} {t : ℕ} (h0 : a 0 = 1)
    (hnn : ∀ r ≤ t, 0 ≤ a r) (hlc : ∀ r, 1 ≤ r → r < t → a r ^ 2 ≤ a (r - 1) * a (r + 1))
    {r : ℕ} (hr : r ≤ t) : a r ^ t ≤ a t ^ r :=
  pow_le_pow_of_sq_le_mul_of_le h0 hnn hlc hr le_rfl

namespace PseudoExpectation

variable {σ : Type*} {ℓ : ℕ} (E : PseudoExpectation σ ℓ)

/-- **Cauchy–Schwarz**, squared: `Ẽ[f g]² ≤ Ẽ[f²] Ẽ[g²]` when `f` and `g` have degree at most `d`
and `2 d ≤ ℓ`. -/
theorem sq_apply_mul_le {f g : MvPolynomial σ ℝ} {d : ℕ} (hf : f.totalDegree ≤ d)
    (hg : g.totalDegree ≤ d) (hd : 2 * d ≤ ℓ) :
    E (f * g) ^ 2 ≤ E (f ^ 2) * E (g ^ 2) := by
  have h₁ := (E.mono hd).cauchy_schwarz hf hg
  have h₂ := (E.mono hd).cauchy_schwarz (g := -g) hf (by rwa [totalDegree_neg])
  simp only [mono_apply] at h₁ h₂
  rw [mul_neg, E.map_neg, neg_sq] at h₂
  have hf2 : 0 ≤ E (f ^ 2) := by
    rw [sq]
    exact E.map_mul_self_nonneg (by omega)
  have hg2 : 0 ≤ E (g ^ 2) := by
    rw [sq]
    exact E.map_mul_self_nonneg (by omega)
  have habs : |E (f * g)| ≤ √(E (f ^ 2)) * √(E (g ^ 2)) := abs_le.2 ⟨by linarith, h₁⟩
  calc E (f * g) ^ 2 = |E (f * g)| ^ 2 := (sq_abs _).symm
    _ ≤ (√(E (f ^ 2)) * √(E (g ^ 2))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = E (f ^ 2) * E (g ^ 2) := by rw [mul_pow, Real.sq_sqrt hf2, Real.sq_sqrt hg2]

/-- `deg (Y^k) ≤ t e` for `k ≤ t` and `deg Y ≤ e`. -/
private theorem totalDegree_pow_le_mul {Y : MvPolynomial σ ℝ} {e t k : ℕ}
    (hY : Y.totalDegree ≤ e) (hk : k ≤ t) : (Y ^ k).totalDegree ≤ t * e :=
  (totalDegree_pow Y k).trans ((Nat.mul_le_mul_left k hY).trans (Nat.mul_le_mul_right e hk))

/-- `Ẽ[Y^(2k)] ≥ 0` for `k ≤ t` when `deg Y ≤ e` and `2 t e ≤ ℓ`. -/
private theorem apply_pow_two_mul_nonneg_of_le {Y : MvPolynomial σ ℝ} {e t : ℕ}
    (hY : Y.totalDegree ≤ e) (hℓ : 2 * t * e ≤ ℓ) {k : ℕ} (hk : k ≤ t) :
    0 ≤ E (Y ^ (2 * k)) := by
  rw [pow_mul', sq]
  refine E.map_mul_self_nonneg ?_
  have := totalDegree_pow_le_mul hY hk
  rw [Nat.mul_assoc] at hℓ
  omega

/-- Log-convexity of the even pseudo-moments: `Ẽ[Y^(2r)]² ≤ Ẽ[Y^(2(r-1))] Ẽ[Y^(2(r+1))]` for
`1 ≤ r < t`, when `deg Y ≤ e` and `2 t e ≤ ℓ` (Cauchy–Schwarz on `Y^(r-1) · Y^(r+1)`). -/
theorem sq_apply_pow_le {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) {r : ℕ} (hr : 1 ≤ r) (hrt : r < t) :
    E (Y ^ (2 * r)) ^ 2 ≤ E (Y ^ (2 * (r - 1))) * E (Y ^ (2 * (r + 1))) := by
  have h := E.sq_apply_mul_le (totalDegree_pow_le_mul hY (show r - 1 ≤ t by omega))
    (totalDegree_pow_le_mul hY (show r + 1 ≤ t by omega)) (by rwa [← Nat.mul_assoc])
  have e₁ : Y ^ (r - 1) * Y ^ (r + 1) = Y ^ (2 * r) := by
    rw [← pow_add]
    congr 1
    omega
  rwa [e₁, ← pow_mul', ← pow_mul'] at h

/-- **Comparing even pseudo-moments**: `Ẽ[Y^(2r)]^t ≤ Ẽ[Y^(2t)]^r` for `r ≤ t`, when `deg Y ≤ e`
and `2 t e ≤ ℓ`. -/
theorem pow_le_pow {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) {r : ℕ} (hr : r ≤ t) :
    E (Y ^ (2 * r)) ^ t ≤ E (Y ^ (2 * t)) ^ r :=
  pow_le_pow_of_sq_le_mul (a := fun k ↦ E (Y ^ (2 * k))) (by simp)
    (fun _ hk ↦ E.apply_pow_two_mul_nonneg_of_le hY hℓ hk)
    (fun _ hk hkt ↦ E.sq_apply_pow_le hY hℓ hk hkt) hr

/-- `Ẽ[Y^(2r)] ≤ Ẽ[Y^(2t)]^(r/t)` for `r ≤ t`, `t ≠ 0`, when `deg Y ≤ e` and `2 t e ≤ ℓ`. -/
theorem apply_pow_le_rpow {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) (ht : t ≠ 0) {r : ℕ} (hr : r ≤ t) :
    E (Y ^ (2 * r)) ≤ E (Y ^ (2 * t)) ^ ((r : ℝ) / t) := by
  have h := E.pow_le_pow hY hℓ hr
  have h0r := E.apply_pow_two_mul_nonneg_of_le hY hℓ hr
  have h0t := E.apply_pow_two_mul_nonneg_of_le hY hℓ le_rfl
  calc E (Y ^ (2 * r)) = (E (Y ^ (2 * r)) ^ t) ^ ((t : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast h0r ht).symm
    _ ≤ (E (Y ^ (2 * t)) ^ r) ^ ((t : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg h0r _) h (by positivity)
    _ = E (Y ^ (2 * t)) ^ ((r : ℝ) / t) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0t, div_eq_mul_inv]

/-- `Ẽ[Y²] ≤ Ẽ[Y^(2t)]^(1/t)` for `t ≠ 0`, when `deg Y ≤ e` and `2 t e ≤ ℓ`. -/
theorem apply_sq_le_rpow {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) (ht : t ≠ 0) :
    E (Y ^ 2) ≤ E (Y ^ (2 * t)) ^ (1 / (t : ℝ)) := by
  have h := E.apply_pow_le_rpow hY hℓ ht (r := 1) (by omega)
  rwa [mul_one, Nat.cast_one] at h

/-- `Ẽ[Y]^(2t) ≤ Ẽ[Y^(2t)]` when `deg Y ≤ e` and `2 t e ≤ ℓ`. -/
theorem pow_apply_le {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) : E Y ^ (2 * t) ≤ E (Y ^ (2 * t)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  -- `Ẽ[Y]² ≤ Ẽ[1] Ẽ[Y²] = Ẽ[Y²]` by Cauchy–Schwarz on `1 · Y`.
  have h₁ : E Y ^ 2 ≤ E (Y ^ 2) := by
    have h := E.sq_apply_mul_le (f := 1) (g := Y) (d := e) (by simp) hY
      (le_trans (Nat.mul_le_mul_right e (by omega)) hℓ)
    rwa [one_mul, one_pow, E.map_one, one_mul] at h
  have h₂ := E.pow_le_pow hY hℓ (r := 1) (by omega)
  rw [mul_one, pow_one] at h₂
  calc E Y ^ (2 * t) = (E Y ^ 2) ^ t := pow_mul _ _ _
    _ ≤ E (Y ^ 2) ^ t := pow_le_pow_left₀ (sq_nonneg _) h₁ _
    _ ≤ E (Y ^ (2 * t)) := h₂

/-- `Ẽ[Y] ≤ Ẽ[Y^(2t)]^(1/(2t))` for `t ≠ 0`, when `deg Y ≤ e` and `2 t e ≤ ℓ`. -/
theorem apply_le_rpow {Y : MvPolynomial σ ℝ} {e t : ℕ} (hY : Y.totalDegree ≤ e)
    (hℓ : 2 * t * e ≤ ℓ) (ht : t ≠ 0) :
    E Y ≤ E (Y ^ (2 * t)) ^ (1 / (2 * t : ℝ)) := by
  have h := E.pow_apply_le hY hℓ
  have hn : 2 * t ≠ 0 := by omega
  have hc : (1 / (2 * t : ℝ)) = ((2 * t : ℕ) : ℝ)⁻¹ := by push_cast; rw [one_div]
  calc E Y ≤ |E Y| := le_abs_self _
    _ = (|E Y| ^ (2 * t)) ^ (((2 * t : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (abs_nonneg _) hn).symm
    _ = (E Y ^ (2 * t)) ^ (((2 * t : ℕ) : ℝ)⁻¹) := by
        rw [pow_mul, sq_abs, ← pow_mul]
    _ ≤ E (Y ^ (2 * t)) ^ (((2 * t : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) h (by positivity)
    _ = E (Y ^ (2 * t)) ^ (1 / (2 * t : ℝ)) := by rw [hc]

/-! ### Products -/

/-- The product form of `apply_pow_le_rpow` for `a r = Ẽ[(PQ)^(2r)]`:
`a (t-m) ≤ a t^((t-m)/t)` for `m ≤ t`, `t ≠ 0`, when `deg P ≤ e₁`, `deg Q ≤ e₂` and
`2 t (e₁ + e₂) ≤ ℓ`. -/
theorem apply_mul_pow_sub_le_rpow {P Q : MvPolynomial σ ℝ} {e₁ e₂ t m : ℕ}
    (hP : P.totalDegree ≤ e₁) (hQ : Q.totalDegree ≤ e₂) (hℓ : 2 * t * (e₁ + e₂) ≤ ℓ)
    (ht : t ≠ 0) (hm : m ≤ t) :
    E ((P * Q) ^ (2 * (t - m))) ≤ E ((P * Q) ^ (2 * t)) ^ (((t : ℝ) - m) / t) := by
  have h := E.apply_pow_le_rpow ((totalDegree_mul P Q).trans (add_le_add hP hQ)) hℓ ht
    (r := t - m) (by omega)
  rwa [Nat.cast_sub hm] at h

/-- The product form of `apply_le_rpow`: `Ẽ[PQ] ≤ Ẽ[(PQ)^(2t)]^(1/(2t))` for `t ≠ 0`, when
`deg P ≤ e₁`, `deg Q ≤ e₂` and `2 t (e₁ + e₂) ≤ ℓ`. -/
theorem apply_mul_le_rpow {P Q : MvPolynomial σ ℝ} {e₁ e₂ t : ℕ}
    (hP : P.totalDegree ≤ e₁) (hQ : Q.totalDegree ≤ e₂) (hℓ : 2 * t * (e₁ + e₂) ≤ ℓ)
    (ht : t ≠ 0) :
    E (P * Q) ≤ E ((P * Q) ^ (2 * t)) ^ (1 / (2 * t : ℝ)) :=
  E.apply_le_rpow ((totalDegree_mul P Q).trans (add_le_add hP hQ)) hℓ ht

end PseudoExpectation

end SoS
