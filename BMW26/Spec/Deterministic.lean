module

public import BMW26.Spec.Defs

/-!
# Spectral closeness from the five facts

[BMW26, Lemma 5.1], deterministically: if a `0/1`-weighted hypercube graph satisfies `LowRel`,
`LowSq`, `GoodNorm` and `BadLow`, then it is spectrally close to `p Q_m` with relative error `ε`
and a diagonal error `D` of small trace (`BMW26.specClose_of_facts`).

The proof replaces the paper's Schur complement by Cauchy–Schwarz. For `g`, write `g = g_U + g_R`
(good and bad vertices), and `h = g_U = h_l + h_h` (degree at most `r`, and above). Then
`Q(h) = Q(h_l) + 2 B(h_l, h_h) + Q(h_h)` for `Q(h) = energy w h - p energy 1 h` and its bilinear
form `B(a, b) = ∑ₓ a x (L_{w-p} b) x`:

* `|Q(h_l)| ≤ γ p E(h_l)` (`LowRel`);
* `|2 B(h_l, h_h)| ≤ 2 ‖h_h‖ ‖L_{w-p} h_l‖ ≤ 2 √(E(h_h)/(2(r+1))) √(4 p E(h_l))` (`LowSq`,
  `energy_one_high_ge`);
* `h_h = u + v` with `u` on the good vertices and `v = -Π_R h_l` (since `h` vanishes on `R`):
  `|Q(u)| ≤ 2 γ p m ‖u‖²` (`GoodNorm`), `|Q(v)|, |B(u, v)|` are bounded through
  `|Q| ≤ E ≤ 2m ‖·‖²` (and polarization for `B`) and `‖v‖² ≤ κ ‖g‖²` (`BadLow`);
* the cross terms between `g_U` and `g_R` and `Q(g_R)` go to the diagonal on `R` (weight
  `16 m² / λ + 16 m`) and on all vertices (weight `λ`), with `E(g_U) ≤ 2 E(g) + 4m ‖g_R‖²`.

If `ε p ≥ 1`, then `|Q(g)| ≤ E(g) ≤ ε p E(g)` directly. The helper lemmas are in
`BMW26.SpecA`; `BMW26.SpecA.core` is the bound for `h` vanishing on `R`.
-/

@[expose] public section

namespace BMW26

open Finset

namespace SpecA

variable {m : ℕ}

/-- The bilinear form of the Laplacian of the weights `w`: `∑ₓ a x (L_w b) x`. -/
noncomputable def bf (w : Fin m → Cube m → ℝ) (a b : Cube m → ℝ) : ℝ := ∑ x, a x * lap w b x

theorem lap_lin (w : Fin m → Cube m → ℝ) (c d : ℝ) (a b : Cube m → ℝ) (x : Cube m) :
    lap w (fun y ↦ c * a y + d * b y) x = c * lap w a x + d * lap w b x := by
  simp only [lap, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem energy_lin (w : Fin m → Cube m → ℝ) (c d : ℝ) (a b : Cube m → ℝ) :
    energy w (fun y ↦ c * a y + d * b y) =
      c ^ 2 * energy w a + 2 * c * d * bf w a b + d ^ 2 * energy w b := by
  rw [← sum_mul_lap, ← sum_mul_lap w a, ← sum_mul_lap w b, bf]
  have hc := sum_mul_lap_comm w b a
  simp only [lap_lin]
  have : ∀ x, (c * a x + d * b x) * (c * lap w a x + d * lap w b x) =
      c ^ 2 * (a x * lap w a x) + c * d * (a x * lap w b x) + c * d * (b x * lap w a x) +
        d ^ 2 * (b x * lap w b x) := fun x ↦ by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  ring

theorem energy_le_energy_one {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x ≤ 1)
    (g : Cube m → ℝ) : energy w g ≤ energy 1 g := by
  unfold energy
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  simp only [Pi.one_apply, one_mul]
  exact mul_le_of_le_one_left (sq_nonneg _) (hw i x)

theorem energy_one_nonneg (g : Cube m → ℝ) : 0 ≤ energy 1 g :=
  energy_nonneg (fun _ _ ↦ zero_le_one) g

theorem energy_sub_le {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) (a b : Cube m → ℝ) :
    energy w (fun y ↦ a y - b y) ≤ 2 * energy w a + 2 * energy w b := by
  unfold energy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have h0 := hw i x
  nlinarith [mul_nonneg h0 (sq_nonneg (a x - a (flip x i) + (b x - b (flip x i))))]

/-- `|Q(g)| ≤ E(g)` for `0/1` weights and `p ∈ [0, 1]`. -/
theorem abs_Q_le {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (g : Cube m → ℝ) :
    |energy (fun i y ↦ w i y - p) g| ≤ energy 1 g := by
  have hw0 : ∀ i x, 0 ≤ w i x := fun i x ↦ by rcases hw i x with h | h <;> simp [h]
  have hw1 : ∀ i x, w i x ≤ 1 := fun i x ↦ by rcases hw i x with h | h <;> simp [h]
  rw [energy_sub_const]
  have h1 := energy_nonneg hw0 g
  have h2 := energy_le_energy_one hw1 g
  have h3 := energy_one_nonneg g
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_Q_le' {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (g : Cube m → ℝ) :
    |energy (fun i y ↦ w i y - p) g| ≤ 2 * m * ∑ x, g x ^ 2 :=
  (abs_Q_le hw hp hp1 g).trans (energy_one_le g)

/-- Polarization: `t |B(a, b)| ≤ m t² ‖a‖² + m ‖b‖²`. -/
theorem bf_bound {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : Cube m → ℝ) {t : ℝ} (ht : 0 < t) :
    t * |bf (fun i y ↦ w i y - p) a b| ≤ m * t ^ 2 * ∑ x, a x ^ 2 + m * ∑ x, b x ^ 2 := by
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p
  have e1 := energy_lin w' t 1 a b
  have e2 := energy_lin w' t (-1) a b
  have q1 := abs_Q_le' hw hp hp1 (fun y ↦ t * a y + 1 * b y)
  have q2 := abs_Q_le' hw hp hp1 (fun y ↦ t * a y + (-1) * b y)
  have n : ∑ x, (t * a x + 1 * b x) ^ 2 + ∑ x, (t * a x + (-1) * b x) ^ 2 =
      2 * t ^ 2 * ∑ x, a x ^ 2 + 2 * ∑ x, b x ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  have h4 : 4 * t * bf w' a b = energy w' (fun y ↦ t * a y + 1 * b y) -
      energy w' (fun y ↦ t * a y + (-1) * b y) := by
    rw [e1, e2]; ring
  have hq1 := abs_le.mp q1
  have hq2 := abs_le.mp q2
  have hB : |4 * t * bf w' a b| ≤ 4 * (m * t ^ 2 * ∑ x, a x ^ 2 + m * ∑ x, b x ^ 2) := by
    rw [h4, abs_le]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * t)] at hB
  linarith

/-- `2 |B(a, b)| ≤ s m ‖a‖² + (4 m / s) ‖b‖²`. -/
theorem bf_bound_s {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : Cube m → ℝ) {s : ℝ} (hs : 0 < s) :
    2 * |bf (fun i y ↦ w i y - p) a b| ≤
      s * m * ∑ x, a x ^ 2 + 4 * m / s * ∑ x, b x ^ 2 := by
  have h := bf_bound hw hp hp1 a b (half_pos hs)
  set B := |bf (fun i y ↦ w i y - p) a b|
  set A := ∑ x, a x ^ 2
  set C := ∑ x, b x ^ 2
  have h' : s * (2 * B) ≤ s * (s * m * A + 4 * m / s * C) := by
    have e : s * (s * m * A + 4 * m / s * C) = 4 * (m * (s / 2) ^ 2 * A + m * C) := by
      field_simp; ring
    rw [e]; nlinarith
  exact le_of_mul_le_mul_left h' hs

/-- `2 |B(a, b)| ≤ λ ‖a‖² + (4 m² / λ) ‖b‖²`. -/
theorem bf_bound_lam {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : Cube m → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    2 * |bf (fun i y ↦ w i y - p) a b| ≤
      lam * ∑ x, a x ^ 2 + 4 * (m ^ 2 / lam) * ∑ x, b x ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h := bf_bound hw hp hp1 a b one_pos
    simp only [CharP.cast_eq_zero, zero_mul, add_zero, one_mul] at h
    have : 0 ≤ lam * ∑ x, a x ^ 2 := by positivity
    have e : ((0 : ℕ) : ℝ) ^ 2 / lam = 0 := by simp
    rw [e]
    linarith
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h := bf_bound_s hw hp hp1 a b (div_pos hlam hm')
    have e1 : lam / m * m = lam := by field_simp
    have e2 : 4 * m / (lam / m) = 4 * (m ^ 2 / lam) := by field_simp
    rwa [e1, e2] at h

/-- The bound for `h` vanishing on the bad vertices:
`|Q(h)| ≤ (151 γ + √(2/(p(r+1)))) p E(h) + 6 m κ/(γ p) ‖h‖²`. -/
theorem core {m r : ℕ} {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1)
    {p γ κ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hmr : (m : ℝ) ≤ 100 * (r + 1))
    (h2 : LowRel w p γ r) (h3 : LowSq w p r) (h4 : GoodNorm w p γ) (h5 : BadLow w p γ κ r)
    (h : Cube m → ℝ) (hR : ∀ x ∈ badSet w p γ, h x = 0) :
    |energy (fun i y ↦ w i y - p) h| ≤
      (151 * γ + Real.sqrt (2 / (p * (r + 1)))) * p * energy 1 h +
        6 * (m * κ / (γ * p)) * ∑ x, h x ^ 2 := by
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p with hw'
  set θ := Real.sqrt (2 / (p * (r + 1))) with hθdef
  set R := badSet w p γ with hRdef
  set hl : Cube m → ℝ := lowProj r h with hhl
  set hh : Cube m → ℝ := h - lowProj r h with hhh
  set u : Cube m → ℝ := fun x ↦ if x ∈ R then 0 else hh x with hu
  set v : Cube m → ℝ := fun x ↦ if x ∈ R then hh x else 0 with hv
  set El := energy 1 hl with hEldef
  set Eh := energy 1 hh with hEhdef
  have hEl : 0 ≤ El := energy_one_nonneg _
  have hEh : 0 ≤ Eh := energy_one_nonneg _
  have hsum : El + Eh = energy 1 h := energy_one_lowProj_add r h
  have hhigh : 2 * ((r : ℝ) + 1) * ∑ x, hh x ^ 2 ≤ Eh := energy_one_high_ge r h
  -- the two decompositions
  have ea : energy w' h = energy w' hl + 2 * bf w' hl hh + energy w' hh := by
    have e := energy_lin w' 1 1 hl hh
    have hfun : (fun y ↦ 1 * hl y + 1 * hh y) = h := by
      funext y; simp [hl, hh]
    rw [hfun] at e; rw [e]; ring
  have eb : energy w' hh = energy w' u + 2 * bf w' u v + energy w' v := by
    have e := energy_lin w' 1 1 u v
    have hfun : (fun y ↦ 1 * u y + 1 * v y) = hh := by
      funext y; by_cases hy : y ∈ R <;> simp [u, v, hy]
    rw [hfun] at e; rw [e]; ring
  -- low degree
  have fc : |energy w' hl| ≤ γ * p * El := by
    have := h2 h
    rwa [← energy_sub_const] at this
  -- the cross term between the low and high parts
  have fd : |2 * bf w' hl hh| ≤ θ * p * El + θ * p * Eh := by
    have hB : bf w' hl hh = ∑ x, hh x * lap w' hl x := sum_mul_lap_comm w' hl hh
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ hh (fun x ↦ lap w' hl x)
    have lsq : ∑ x, lap w' hl x ^ 2 ≤ 4 * p * El := h3 h
    have hNh : 0 ≤ ∑ x, hh x ^ 2 := by positivity
    have hθ2 : θ ^ 2 * (p * (r + 1)) = 2 := by
      rw [hθdef, Real.sq_sqrt (by positivity)]; field_simp
    have hr : (0 : ℝ) < r + 1 := by positivity
    have key : ((r : ℝ) + 1) * (2 * bf w' hl hh) ^ 2 ≤
        ((r : ℝ) + 1) * (θ * p * El + θ * p * Eh) ^ 2 := by
      have e : ((r : ℝ) + 1) * (θ * p * El + θ * p * Eh) ^ 2 =
          (θ ^ 2 * (p * (r + 1))) * (p * (El + Eh) ^ 2) := by ring
      rw [e, hθ2, hB]
      calc ((r : ℝ) + 1) * (2 * ∑ x, hh x * lap w' hl x) ^ 2
          = 4 * (r + 1) * (∑ x, hh x * lap w' hl x) ^ 2 := by ring
        _ ≤ 4 * (r + 1) * ((∑ x, hh x ^ 2) * ∑ x, lap w' hl x ^ 2) := by gcongr
        _ ≤ 4 * (r + 1) * ((∑ x, hh x ^ 2) * (4 * p * El)) := by gcongr
        _ = 8 * p * El * (2 * (r + 1) * ∑ x, hh x ^ 2) := by ring
        _ ≤ 8 * p * El * Eh := by gcongr
        _ ≤ 2 * (p * (El + Eh) ^ 2) := by nlinarith [mul_nonneg hp.le (sq_nonneg (El - Eh))]
    exact abs_le_of_sq_le_sq (le_of_mul_le_mul_left key hr) (by positivity)
  -- the good part of the high part
  have hNu : ∑ x, u x ^ 2 ≤ ∑ x, hh x ^ 2 := by
    refine Finset.sum_le_sum fun x _ ↦ ?_
    by_cases hx : x ∈ R
    · simp [u, hx, sq_nonneg]
    · simp [u, hx]
  have fe : |energy w' u| ≤ 2 * γ * p * m * ∑ x, u x ^ 2 := by
    have := h4 u (fun x hx ↦ by
      have hx' : x ∈ R := hx
      simp [u, hx'])
    rwa [← energy_sub_const] at this
  -- the bad part of the high part
  have ff := bf_bound_s hw hp.le hp1 u v (mul_pos hγ hp)
  have fg := abs_Q_le' hw hp.le hp1 v
  have hNv : ∑ x, v x ^ 2 ≤ κ * ∑ x, h x ^ 2 := by
    have e : ∑ x, v x ^ 2 = ∑ x ∈ R, hl x ^ 2 := by
      have : ∀ x, v x ^ 2 = if x ∈ R then hl x ^ 2 else 0 := fun x ↦ by
        by_cases hx : x ∈ R
        · simp [v, hx, hh, hl, hR x hx]
        · simp [v, hx]
      rw [Finset.sum_congr rfl (fun x _ ↦ this x), Finset.sum_ite_mem, Finset.univ_inter]
    rw [e]; exact h5 h
  have hmu : (m : ℝ) * ∑ x, u x ^ 2 ≤ 50 * Eh := by
    have h0 : 0 ≤ ∑ x, u x ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmr h0,
      mul_le_mul_of_nonneg_left hNu (by positivity : (0 : ℝ) ≤ 100 * (r + 1))]
  -- combine
  set c : ℝ := (m : ℝ) / (γ * p) with hc
  have hc0 : 0 ≤ c := by positivity
  have hmc : (m : ℝ) ≤ c := by
    rw [hc, le_div_iff₀ (mul_pos hγ hp)]
    have : γ * p ≤ 1 := by nlinarith
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have e4 : 4 * (m : ℝ) / (γ * p) = 4 * c := by rw [hc]; ring
  have e6 : (m : ℝ) * κ / (γ * p) = c * κ := by rw [hc]; ring
  rw [e4] at ff
  rw [e6, ← hsum, ea, eb]
  have t1 : γ * p * ((m : ℝ) * ∑ x, u x ^ 2) ≤ γ * p * (50 * Eh) :=
    mul_le_mul_of_nonneg_left hmu (by positivity)
  have hNv0 : 0 ≤ ∑ x, v x ^ 2 := by positivity
  have t2 : (m : ℝ) * ∑ x, v x ^ 2 ≤ c * ∑ x, v x ^ 2 := mul_le_mul_of_nonneg_right hmc hNv0
  have t3 : c * ∑ x, v x ^ 2 ≤ c * (κ * ∑ x, h x ^ 2) := mul_le_mul_of_nonneg_left hNv hc0
  have t4 : 0 ≤ γ * p * El := by positivity
  have t5 : 0 ≤ γ * p * Eh := by positivity
  have a1 := abs_le.mp fc
  have a2 := abs_le.mp fd
  have a3 := abs_le.mp fe
  have a5 := abs_le.mp fg
  have b1 := le_abs_self (bf w' u v)
  have b2 := neg_abs_le (bf w' u v)
  rw [abs_le]
  constructor <;> linarith

end SpecA

/-- **Spectral closeness** of a `0/1`-weighted hypercube graph from the facts `LowRel`, `LowSq`,
`GoodNorm` and `BadLow`, with a diagonal error `D` of trace at most
`2^m (40 m κ / (γ p) + λ) + |R| (16 m² / λ + 16 m)`, for any `λ > 0`. -/
theorem specClose_of_facts {m r : ℕ} {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1)
    {p γ ε κ lam : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 0 ≤ κ)
    (hlam : 0 < lam) (hmr : (m : ℝ) ≤ 100 * (r + 1))
    (hθ : 2 * (151 * γ + Real.sqrt (2 / (p * (r + 1)))) ≤ ε)
    (h2 : LowRel w p γ r) (h3 : LowSq w p r) (h4 : GoodNorm w p γ) (h5 : BadLow w p γ κ r) :
    ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧
      ∑ x, D x ≤ 2 ^ m * (40 * m * κ / (γ * p) + lam) +
        (badSet w p γ).card * (16 * (m : ℝ) ^ 2 / lam + 16 * m) ∧
      SpecClose w 1 p ε D := by
  set R := badSet w p γ with hRdef
  set θ := Real.sqrt (2 / (p * (r + 1))) with hθdef
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p with hw'
  have hγp : 0 < γ * p := mul_pos hγ hp
  have hc₀ : 0 ≤ 40 * (m * κ / (γ * p)) + lam := by positivity
  have hc₁ : 0 ≤ 16 * ((m : ℝ) ^ 2 / lam) + 16 * m := by positivity
  refine ⟨fun x ↦ (40 * (m * κ / (γ * p)) + lam) +
    if x ∈ R then 16 * ((m : ℝ) ^ 2 / lam) + 16 * m else 0, fun x ↦ ?_, ?_, ?_⟩
  · by_cases hx : x ∈ R
    · simp only [hx, ite_true]; positivity
    · simp only [hx, ite_false, add_zero]; positivity
  · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    apply le_of_eq
    ring
  · intro g
    set gR : Cube m → ℝ := fun x ↦ if x ∈ R then g x else 0 with hgR
    set gU : Cube m → ℝ := fun x ↦ if x ∈ R then 0 else g x with hgU
    have hD : ∑ x, ((40 * (m * κ / (γ * p)) + lam) +
        if x ∈ R then 16 * ((m : ℝ) ^ 2 / lam) + 16 * m else 0) * g x ^ 2 =
        (40 * (m * κ / (γ * p)) + lam) * ∑ x, g x ^ 2 +
          (16 * ((m : ℝ) ^ 2 / lam) + 16 * m) * ∑ x, gR x ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : x ∈ R
      · simp only [gR, hx, ite_true]; ring
      · simp only [gR, hx, ite_false]; ring
    have hN : ∑ x, g x ^ 2 = ∑ x, gU x ^ 2 + ∑ x, gR x ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : x ∈ R <;> simp [gR, gU, hx]
    have hNU : 0 ≤ ∑ x, gU x ^ 2 := by positivity
    have hNR : 0 ≤ ∑ x, gR x ^ 2 := by positivity
    have hE1 : 0 ≤ energy 1 g := SpecA.energy_one_nonneg g
    have hk : 0 ≤ (m : ℝ) * κ / (γ * p) := by positivity
    have hl2 : 0 ≤ (m : ℝ) ^ 2 / lam := by positivity
    rw [hD, ← energy_sub_const]
    by_cases hεp : 1 ≤ ε * p
    · -- trivial case: `|Q(g)| ≤ E(g) ≤ ε p E(g)`
      have h0 := SpecA.abs_Q_le hw hp.le hp1 g
      have t1 : energy 1 g ≤ ε * p * energy 1 g := by nlinarith
      have t2 : 0 ≤ (40 * (m * κ / (γ * p)) + lam) * ∑ x, g x ^ 2 := by positivity
      have t3 : 0 ≤ (16 * ((m : ℝ) ^ 2 / lam) + 16 * m) * ∑ x, gR x ^ 2 := by positivity
      linarith
    · replace hεp := (not_le.mp hεp).le
      have split : energy w' g = energy w' gU + 2 * SpecA.bf w' gU gR + energy w' gR := by
        have e := SpecA.energy_lin w' 1 1 gU gR
        have hfun : (fun y ↦ 1 * gU y + 1 * gR y) = g := by
          funext y; by_cases hy : y ∈ R <;> simp [gU, gR, hy]
        rw [hfun] at e; rw [e]; ring
      have fU := SpecA.core hw hp hp1 hγ hγ1 hmr h2 h3 h4 h5 gU (fun x hx ↦ by
        have hx' : x ∈ R := hx
        simp [gU, hx'])
      have fB := SpecA.bf_bound_lam hw hp.le hp1 gU gR hlam
      have fR := SpecA.abs_Q_le' hw hp.le hp1 gR
      have eU : energy 1 gU ≤ 2 * energy 1 g + 2 * energy 1 gR := by
        have := SpecA.energy_sub_le (w := 1) (fun _ _ ↦ zero_le_one) g gR
        have hfun : (fun y ↦ g y - gR y) = gU := by
          funext y; by_cases hy : y ∈ R <;> simp [gU, gR, hy]
        rwa [hfun] at this
      have eR := energy_one_le gR
      have hθ0 : 0 ≤ θ := Real.sqrt_nonneg _
      set X := (151 * γ + θ) * p with hX
      have hX0 : 0 ≤ X := by positivity
      have hX2 : 2 * X ≤ ε * p := by
        have := mul_le_mul_of_nonneg_right hθ hp.le
        rw [hX]; linarith
      have t1 : X * energy 1 gU ≤ X * (2 * energy 1 g + 4 * m * ∑ x, gR x ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hX0
      have t2 : (2 * X) * (2 * m * ∑ x, gR x ^ 2) ≤ 1 * (2 * m * ∑ x, gR x ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have t3 : (2 * X) * energy 1 g ≤ (ε * p) * energy 1 g :=
        mul_le_mul_of_nonneg_right hX2 hE1
      have t4 : 6 * (m * κ / (γ * p)) * ∑ x, gU x ^ 2 ≤ 40 * (m * κ / (γ * p)) * ∑ x, gU x ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hNU
      have t5 : 4 * ((m : ℝ) ^ 2 / lam) * ∑ x, gR x ^ 2 ≤
          16 * ((m : ℝ) ^ 2 / lam) * ∑ x, gR x ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hNR
      have t6 : 0 ≤ (40 * (m * κ / (γ * p)) + lam) * ∑ x, gR x ^ 2 := by positivity
      have t7 : 0 ≤ (m : ℝ) * ∑ x, gR x ^ 2 := by positivity
      have a1 := abs_le.mp fU
      have a3 := abs_le.mp fR
      have b1 := le_abs_self (SpecA.bf w' gU gR)
      have b2 := neg_abs_le (SpecA.bf w' gU gR)
      rw [split, hN, abs_le]
      constructor <;> linarith

end BMW26
