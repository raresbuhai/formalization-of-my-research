module

public import BMW26.Spec.Main

/-!
# Spectral concentration in the paper's form

[BMW26, Lemma 5.1] as stated in the paper: the error is `d² P_{>0} Π_R P_{>0}` for the set `R` of
bad vertices, and the failure probability is `1/d^C₁` for any `C₁`.

* `BMW26.specPaper_of_facts` (deterministic): from `LowRel`, `LowSq`, `GoodNorm` and `BadLow`. For
  `g`, let `h = g - ḡ` (both Laplacians kill constants, so `Q(h) = Q(g)` and `E(h) = E(g)`, with
  `Q(h) = energy w h - p energy 1 h` and `E = energy 1`), and `h = h_l + h_h` with
  `h_l = lowProj r h`. Then `|Q(h_l)| ≤ γ p E(h_l)` (`LowRel`);
  `2|B(h_l, h_h)| ≤ 2 ‖L_{w-p} h_l‖ ‖h_h‖ ≤ p √(2/(p(r+1))) E(h)` (`LowSq`, `energy_one_high_ge`);
  `h_h = u + v` with `u` vanishing on `R`: `|Q(u)| ≤ 2γpm ‖u‖² ≤ 100 γ p E(h_h)` (`GoodNorm`),
  `2|B(u, v)| ≤ 4m ‖u‖ ‖v‖ ≤ (m²/4) ‖v‖² + 16 ‖u‖²` with `16 ‖u‖² ≤ (800/m) E(h_h)`, and
  `|Q(v)| ≤ 2m ‖v‖² ≤ (m²/4) ‖v‖²`; finally `‖v‖² ≤ 2 ∑_{x∈R} h(x)² + 2κ ‖h‖²` (`BadLow`) and
  `‖h‖² ≤ E(h)/2` (the spectral gap of the hypercube, `h` has mean `0`).
* `BMW26.spectral_paper_whp`: with `γ = ε'/404` for `ε' = min(ε, 1)`, the five facts with failure
  probability `1/m^q` (`BMW26.badSmall_whp_pow`, `badLow_whp_pow`, `lowRel_whp_pow`,
  `lowSq_whp_pow`, `disc_whp_pow` with `goodNorm_of_disc`), `R` the bad vertices, at most
  `2^m/m^K` of them with `K = ⌈C₂⌉ + 4`, and `q = ⌈C₁⌉ + 1`. Each of the four terms of `hθ` is at
  most `ε'/4` (`BMW26.SpecP.theta_le`, `BMW26.SpecP.kappa_le`) when `C ≥ 3200/ε'²`.
-/

@[expose] public section

namespace BMW26

open MeasureTheory

namespace SpecP

variable {m : ℕ}

/-- The energy does not see constants. -/
theorem energy_sub_const_fun (w : Fin m → Cube m → ℝ) (g : Cube m → ℝ) (c : ℝ) :
    energy w (fun x ↦ g x - c) = energy w g := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

theorem lowProj_zero_of_sum_eq_zero {h : Cube m → ℝ} (hs : ∑ x, h x = 0) :
    lowProj 0 h = 0 := by
  funext x
  unfold lowProj
  refine Finset.sum_eq_zero fun S hS ↦ ?_
  have : S = ∅ := by simpa using hS
  subst this
  simp [fourier, chi, hs]

/-- **The spectral gap of the hypercube**: `2 ‖h‖² ≤ E(h)` for `h` of mean zero. -/
theorem gap {h : Cube m → ℝ} (hs : ∑ x, h x = 0) : 2 * ∑ x, h x ^ 2 ≤ energy 1 h := by
  have := energy_one_high_ge 0 h
  rw [lowProj_zero_of_sum_eq_zero hs, sub_zero] at this
  simpa using this

/-- The cross term between the low and high parts:
`|2 B(h_l, h_h)| ≤ θ p E(h_l) + θ p E(h_h)` with `θ = √(2/(p(r+1)))` (`LowSq`). -/
theorem cross {m r : ℕ} {w : Fin m → Cube m → ℝ} {p : ℝ} (hp : 0 < p) (h3 : LowSq w p r)
    (h : Cube m → ℝ) :
    |2 * SpecA.bf (fun i y ↦ w i y - p) (lowProj r h) (h - lowProj r h)| ≤
      Real.sqrt (2 / (p * (r + 1))) * p * energy 1 (lowProj r h) +
        Real.sqrt (2 / (p * (r + 1))) * p * energy 1 (h - lowProj r h) := by
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p with hw'
  set θ := Real.sqrt (2 / (p * (r + 1))) with hθdef
  set hl : Cube m → ℝ := lowProj r h with hhl
  set hh : Cube m → ℝ := h - lowProj r h with hhh
  set El := energy 1 hl with hEldef
  set Eh := energy 1 hh with hEhdef
  have hEl : 0 ≤ El := SpecA.energy_one_nonneg _
  have hEh : 0 ≤ Eh := SpecA.energy_one_nonneg _
  have hhigh : 2 * ((r : ℝ) + 1) * ∑ x, hh x ^ 2 ≤ Eh := energy_one_high_ge r h
  have hB : SpecA.bf w' hl hh = ∑ x, hh x * lap w' hl x := sum_mul_lap_comm w' hl hh
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ hh (fun x ↦ lap w' hl x)
  have lsq : ∑ x, lap w' hl x ^ 2 ≤ 4 * p * El := h3 h
  have hNh : 0 ≤ ∑ x, hh x ^ 2 := by positivity
  have hθ2 : θ ^ 2 * (p * (r + 1)) = 2 := by
    rw [hθdef, Real.sq_sqrt (by positivity)]; field_simp
  have hr : (0 : ℝ) < r + 1 := by positivity
  have key : ((r : ℝ) + 1) * (2 * SpecA.bf w' hl hh) ^ 2 ≤
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

/-- The high part: `|Q(h_h)| ≤ 100 γ p E(h_h) + (800/m) E(h_h) + (m²/2) ∑_{x ∈ R} h_h(x)²`
(`GoodNorm` on the good vertices). -/
theorem highPart {m r : ℕ} {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1)
    {p γ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hm : 8 ≤ m)
    (hmr : (m : ℝ) ≤ 100 * (r + 1)) (h4 : GoodNorm w p γ) (h : Cube m → ℝ) :
    |energy (fun i y ↦ w i y - p) (h - lowProj r h)| ≤
      100 * γ * p * energy 1 (h - lowProj r h) + 800 / (m : ℝ) * energy 1 (h - lowProj r h) +
        (m : ℝ) ^ 2 / 2 * ∑ x ∈ badSet w p γ, (h - lowProj r h) x ^ 2 := by
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p with hw'
  set R := badSet w p γ with hRdef
  set hh : Cube m → ℝ := h - lowProj r h with hhh
  set u : Cube m → ℝ := fun x ↦ if x ∈ R then 0 else hh x with hu
  set v : Cube m → ℝ := fun x ↦ if x ∈ R then hh x else 0 with hv
  set Eh := energy 1 hh with hEhdef
  have hhigh : 2 * ((r : ℝ) + 1) * ∑ x, hh x ^ 2 ≤ Eh := energy_one_high_ge r h
  have eb : energy w' hh = energy w' u + 2 * SpecA.bf w' u v + energy w' v := by
    have e := SpecA.energy_lin w' 1 1 u v
    have hfun : (fun y ↦ 1 * u y + 1 * v y) = hh := by
      funext y; by_cases hy : y ∈ R <;> simp [u, v, hy]
    rw [hfun] at e; rw [e]; ring
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
  have hmu : (m : ℝ) * ∑ x, u x ^ 2 ≤ 50 * Eh := by
    have h0 : 0 ≤ ∑ x, u x ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hmr h0
    have := mul_le_mul_of_nonneg_left hNu (by positivity : (0 : ℝ) ≤ 100 * (r + 1))
    linarith
  have h16 : 16 * ∑ x, u x ^ 2 ≤ 800 / (m : ℝ) * Eh := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    linarith
  have ff := SpecA.bf_bound_s hw hp.le hp1 u v (s := 16 / m) (by positivity)
  have e1 : 16 / (m : ℝ) * m = 16 := by field_simp
  have e2 : 4 * (m : ℝ) / (16 / m) = (m : ℝ) ^ 2 / 4 := by field_simp; ring
  rw [e1, e2] at ff
  have fg := SpecA.abs_Q_le' hw hp.le hp1 v
  have hNv0 : 0 ≤ ∑ x, v x ^ 2 := by positivity
  have h2m : 2 * (m : ℝ) * ∑ x, v x ^ 2 ≤ (m : ℝ) ^ 2 / 4 * ∑ x, v x ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hNv0
  have ev : ∑ x, v x ^ 2 = ∑ x ∈ R, hh x ^ 2 := by
    have : ∀ x, v x ^ 2 = if x ∈ R then hh x ^ 2 else 0 := fun x ↦ by
      by_cases hx : x ∈ R <;> simp [v, hx]
    rw [Finset.sum_congr rfl (fun x _ ↦ this x), Finset.sum_ite_mem, Finset.univ_inter]
  have t1 : γ * p * ((m : ℝ) * ∑ x, u x ^ 2) ≤ γ * p * (50 * Eh) :=
    mul_le_mul_of_nonneg_left hmu (by positivity)
  rw [eb, ← ev]
  have a3 := abs_le.mp fe
  have a5 := abs_le.mp fg
  have b1 := le_abs_self (SpecA.bf w' u v)
  have b2 := neg_abs_le (SpecA.bf w' u v)
  have hEh : 0 ≤ Eh := SpecA.energy_one_nonneg _
  have t5 : 0 ≤ γ * p * Eh := by positivity
  have t6 : 0 ≤ 800 / (m : ℝ) * Eh := by positivity
  rw [abs_le]
  constructor
  · linarith only [a3.1, a5.1, ff, b2, t1, t5, t6, h16, h2m, hNv0]
  · linarith only [a3.2, a5.2, ff, b1, t1, t5, t6, h16, h2m, hNv0]

/-- The bad vertices: `∑_{x ∈ R} h_h(x)² ≤ 2 ∑_{x ∈ R} h(x)² + 2 κ ‖h‖²` (`BadLow`). -/
theorem badPart {m r : ℕ} {w : Fin m → Cube m → ℝ} {p γ κ : ℝ} (h5 : BadLow w p γ κ r)
    (h : Cube m → ℝ) :
    ∑ x ∈ badSet w p γ, (h - lowProj r h) x ^ 2 ≤
      2 * ∑ x ∈ badSet w p γ, h x ^ 2 + 2 * (κ * ∑ x, h x ^ 2) := by
  have hb : ∑ x ∈ badSet w p γ, lowProj r h x ^ 2 ≤ κ * ∑ x, h x ^ 2 := h5 h
  have hle : ∑ x ∈ badSet w p γ, (h - lowProj r h) x ^ 2 ≤
      ∑ x ∈ badSet w p γ, (2 * h x ^ 2 + 2 * lowProj r h x ^ 2) :=
    Finset.sum_le_sum fun x _ ↦ by
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (h x + lowProj r h x)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hle
  linarith

/-- The bound for `h` with `2 ‖h‖² ≤ E(h)`: `|Q(h)| ≤ θ' p E(h) + m² ∑_{x ∈ R} h(x)²`. -/
theorem core {m r : ℕ} {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1)
    {p γ κ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hκ : 0 ≤ κ) (hm : 8 ≤ m)
    (hmr : (m : ℝ) ≤ 100 * (r + 1))
    (h2 : LowRel w p γ r) (h3 : LowSq w p r) (h4 : GoodNorm w p γ) (h5 : BadLow w p γ κ r)
    (h : Cube m → ℝ) (hgap : 2 * ∑ x, h x ^ 2 ≤ energy 1 h) :
    |energy (fun i y ↦ w i y - p) h| ≤
      (101 * γ + Real.sqrt (2 / (p * (r + 1))) + 800 / (p * m) + (m : ℝ) ^ 2 * κ / (2 * p)) *
        p * energy 1 h + (m : ℝ) ^ 2 * ∑ x ∈ badSet w p γ, h x ^ 2 := by
  have hm0 : (0 : ℝ) < m := by
    have : (8 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set w' : Fin m → Cube m → ℝ := fun i y ↦ w i y - p with hw'
  set θ := Real.sqrt (2 / (p * (r + 1))) with hθdef
  have fd := cross hp h3 h
  have fh := highPart hw hp hp1 hγ hm hmr h4 h
  have fb := badPart h5 h
  set R := badSet w p γ with hRdef
  set hl : Cube m → ℝ := lowProj r h with hhl
  set hh : Cube m → ℝ := h - lowProj r h with hhh
  set El := energy 1 hl with hEldef
  set Eh := energy 1 hh with hEhdef
  have hEl : 0 ≤ El := SpecA.energy_one_nonneg _
  have hEh : 0 ≤ Eh := SpecA.energy_one_nonneg _
  have hsum : El + Eh = energy 1 h := energy_one_lowProj_add r h
  have ea : energy w' h = energy w' hl + 2 * SpecA.bf w' hl hh + energy w' hh := by
    have e := SpecA.energy_lin w' 1 1 hl hh
    have hfun : (fun y ↦ 1 * hl y + 1 * hh y) = h := by
      funext y; simp [hl, hh]
    rw [hfun] at e; rw [e]; ring
  have fc : |energy w' hl| ≤ γ * p * El := by
    have := h2 h
    rwa [← energy_sub_const] at this
  have t2 : (m : ℝ) ^ 2 / 2 * ∑ x ∈ R, hh x ^ 2 ≤
      (m : ℝ) ^ 2 / 2 * (2 * ∑ x ∈ R, h x ^ 2 + 2 * (κ * ∑ x, h x ^ 2)) :=
    mul_le_mul_of_nonneg_left fb (by positivity)
  have t3 : (m : ℝ) ^ 2 * κ * (2 * ∑ x, h x ^ 2) ≤ (m : ℝ) ^ 2 * κ * energy 1 h :=
    mul_le_mul_of_nonneg_left hgap (by positivity)
  have eR : (101 * γ + θ + 800 / (p * m) + (m : ℝ) ^ 2 * κ / (2 * p)) * p * energy 1 h =
      101 * γ * p * energy 1 h + θ * p * energy 1 h + 800 / (m : ℝ) * energy 1 h +
        (m : ℝ) ^ 2 * κ / 2 * energy 1 h := by
    have e3 : 800 / (p * m) * p = 800 / (m : ℝ) := by field_simp
    have e4 : (m : ℝ) ^ 2 * κ / (2 * p) * p = (m : ℝ) ^ 2 * κ / 2 := by field_simp
    calc (101 * γ + θ + 800 / (p * m) + (m : ℝ) ^ 2 * κ / (2 * p)) * p * energy 1 h
        = 101 * γ * p * energy 1 h + θ * p * energy 1 h + 800 / (p * m) * p * energy 1 h +
          (m : ℝ) ^ 2 * κ / (2 * p) * p * energy 1 h := by ring
      _ = _ := by rw [e3, e4]
  rw [eR, ← hsum]
  rw [← hsum] at t3
  rw [ea]
  have t4 : 0 ≤ γ * p * El := by positivity
  have t5 : 0 ≤ γ * p * Eh := by positivity
  have t6 : 0 ≤ 800 / (m : ℝ) * El := by positivity
  have a1 := abs_le.mp fc
  have a2 := abs_le.mp fd
  have a3 := abs_le.mp fh
  rw [abs_le]
  constructor
  · linarith only [a1.1, a2.1, a3.1, t2, t3, t4, t5, t6]
  · linarith only [a1.2, a2.2, a3.2, t2, t3, t4, t5, t6]

/-- The bad-vertex term of `hθ`: `m² κ / (2p) ≤ ε/4` for `κ = |R|/2^m + t`. -/
theorem kappa_le {M n N t ε p : ℝ} {K : ℕ} (hM : 1 ≤ M) (hK : 4 ≤ K) (hn : 0 < n)
    (hN0 : 0 ≤ N) (hN : N ≤ n / M ^ K) (hpM : 1 ≤ p * M) (hε : 0 < ε) (hMε : 4 / ε ≤ M)
    (ht : M ^ 3 * t ≤ ε / 4) : M ^ 2 * (N / n + t) / (2 * p) ≤ ε / 4 := by
  have hM0 : 0 < M := by linarith
  have hp0 : 0 < p := by
    by_contra hp
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hp) hM0.le
    linarith
  have ha0 : 0 ≤ N / n := div_nonneg hN0 hn.le
  have ha : N / n * M ^ K ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hn]
    rwa [le_div_iff₀ (by positivity)] at hN
  have hpow : M ^ 4 ≤ M ^ K := pow_le_pow_right₀ hM hK
  have h4 : 4 ≤ M * ε := by rwa [div_le_iff₀ hε] at hMε
  have h1 : M * (M ^ 3 * (N / n)) ≤ M * (ε / 4) := by
    calc M * (M ^ 3 * (N / n)) = N / n * M ^ 4 := by ring
      _ ≤ N / n * M ^ K := mul_le_mul_of_nonneg_left hpow ha0
      _ ≤ 1 := ha
      _ ≤ M * (ε / 4) := by linarith
  have h2 : M ^ 3 * (N / n) ≤ ε / 4 := le_of_mul_le_mul_left h1 hM0
  rw [div_le_iff₀ (by positivity)]
  have h3 : M * (M ^ 2 * (N / n + t)) ≤ M * (ε / 4 * (2 * p)) := by
    calc M * (M ^ 2 * (N / n + t)) = M ^ 3 * (N / n) + M ^ 3 * t := by ring
      _ ≤ ε / 4 + ε / 4 := by linarith
      _ = ε / 2 * 1 := by ring
      _ ≤ ε / 2 * (p * M) := by gcongr
      _ = M * (ε / 4 * (2 * p)) := by ring
  exact le_of_mul_le_mul_left h3 hM0

/-- `5 / m^q ≤ 1 / m^C₁` for `q ≥ C₁ + 1` and `m ≥ 5`. -/
theorem five_div_le {M C₁ : ℝ} {q : ℕ} (hM : 5 ≤ M) (hq : C₁ + 1 ≤ q) :
    5 / M ^ q ≤ 1 / M ^ C₁ := by
  have hM0 : 0 < M := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : M ^ q = M ^ ((q : ℝ) - C₁) * M ^ C₁ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hM0]
    congr 1; ring
  have h1 : M ^ (1 : ℝ) ≤ M ^ ((q : ℝ) - C₁) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_one] at h1
  rw [e]
  have hC : 0 < M ^ C₁ := Real.rpow_pos_of_pos hM0 C₁
  nlinarith

/-- The terms `√(2/(p(r+1)))` and `800/(pm)` of `hθ` are at most `ε/4` when `p m ≥ C` with
`C ε² ≥ 3200`. -/
theorem theta_le {M p ε C : ℝ} {r : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 3200 ≤ C * ε ^ 2)
    (hCpM : C ≤ p * M) (hp0 : 0 < p) (hM0 : 0 < M) (hmr : M ≤ 100 * (r + 1)) :
    Real.sqrt (2 / (p * (r + 1))) ≤ ε / 4 ∧ 800 / (p * M) ≤ ε / 4 := by
  have hC0 : 0 ≤ C := by
    by_contra hC0
    have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hC0).le (sq_nonneg ε)
    linarith
  constructor
  · rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
    have h1 : C ≤ 100 * (p * (r + 1)) := by
      have := mul_le_mul_of_nonneg_left hmr hp0.le
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
    have e : (ε / 4) ^ 2 * (p * (r + 1)) = ε ^ 2 * (100 * (p * (r + 1))) / 1600 := by ring
    rw [e]
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 hC0
    have h3 := mul_le_mul_of_nonneg_left hCpM hε.le
    have e : ε / 4 * (p * M) = ε * (p * M) / 4 := by ring
    rw [e]
    nlinarith

end SpecP

/-- **Spectral closeness in the paper's form**, deterministically: for every `g`,
`|gᵀ(L_w - pL)g| ≤ ε p gᵀLg + m² ∑_{x ∈ R} (g x - ḡ)²` with `R` the bad vertices. -/
theorem specPaper_of_facts {m r : ℕ} {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x = 0 ∨ w i x = 1)
    {p γ ε κ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hκ : 0 ≤ κ) (hm : 8 ≤ m)
    (hmr : (m : ℝ) ≤ 100 * (r + 1))
    (hθ : 101 * γ + Real.sqrt (2 / (p * (r + 1))) + 800 / (p * m) + (m : ℝ) ^ 2 * κ / (2 * p) ≤ ε)
    (h2 : LowRel w p γ r) (h3 : LowSq w p r) (h4 : GoodNorm w p γ) (h5 : BadLow w p γ κ r) :
    ∀ g : Cube m → ℝ, |energy w g - p * energy 1 g| ≤
      ε * p * energy 1 g + (m : ℝ) ^ 2 * ∑ x ∈ badSet w p γ, (g x - (∑ y, g y) / 2 ^ m) ^ 2 := by
  intro g
  set gbar : ℝ := (∑ y, g y) / 2 ^ m with hgbar
  set h : Cube m → ℝ := fun x ↦ g x - gbar with hh
  have hs : ∑ x, h x = 0 := by
    have hcard : ((Finset.univ : Finset (Cube m)).card : ℝ) = 2 ^ m := by simp
    calc ∑ x, h x = ∑ x, g x - ((Finset.univ : Finset (Cube m)).card : ℝ) * gbar := by
          rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
      _ = 0 := by
          rw [hcard, hgbar]
          field_simp
          ring
  have hE : energy 1 h = energy 1 g := SpecP.energy_sub_const_fun 1 g gbar
  have hEw : energy w h = energy w g := SpecP.energy_sub_const_fun w g gbar
  have hc := SpecP.core hw hp hp1 hγ hκ hm hmr h2 h3 h4 h5 h (SpecP.gap hs)
  rw [energy_sub_const, hEw, hE] at hc
  have hR : ∑ x ∈ badSet w p γ, h x ^ 2 = ∑ x ∈ badSet w p γ, (g x - gbar) ^ 2 := rfl
  rw [hR] at hc
  have hE0 : 0 ≤ energy 1 g := SpecA.energy_one_nonneg g
  have := mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ p * energy 1 g)
  calc |energy w g - p * energy 1 g| ≤
      (101 * γ + Real.sqrt (2 / (p * (r + 1))) + 800 / (p * m) + (m : ℝ) ^ 2 * κ / (2 * p)) *
        p * energy 1 g + (m : ℝ) ^ 2 * ∑ x ∈ badSet w p γ, (g x - gbar) ^ 2 := hc
    _ ≤ ε * p * energy 1 g + (m : ℝ) ^ 2 * ∑ x ∈ badSet w p γ, (g x - gbar) ^ 2 := by
      linarith

/-- **Spectral concentration of the percolated hypercube**, in the paper's form ([BMW26,
Lemma 5.1]), for independent coins. -/
theorem spectral_paper_whp {ε : ℝ} (hε : 0 < ε) (C₁ C₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ C₁ ≤ μ.real {ω | ∃ R : Finset (Cube m),
          (R.card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ C₂ ∧ ∀ g : Cube m → ℝ,
            |energy (coinW a ω) g - p * energy 1 g| ≤
              ε * p * energy 1 g + (m : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ m) ^ 2} := by
  set ε' : ℝ := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set γ : ℝ := ε' / 404 with hγdef
  have hγ : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by rw [hγdef]; linarith
  set K : ℕ := ⌈C₂⌉₊ + 4 with hKdef
  set q : ℕ := ⌈C₁⌉₊ + 1 with hqdef
  obtain ⟨Cb, hCb, m₁, hbad⟩ := badSmall_whp_pow hγ hγ1 K q
  obtain ⟨m₂, hlow⟩ := badLow_whp_pow γ q
  obtain ⟨m₃, hrel⟩ := lowRel_whp_pow hγ q
  obtain ⟨m₄, hsq⟩ := lowSq_whp_pow q
  obtain ⟨η, hη, hη1, hgood⟩ := goodNorm_of_disc hγ hγ1
  obtain ⟨Cd, hCd, m₅, hdisc⟩ := disc_whp_pow hγ1 hη hη1 q
  obtain ⟨m₆, hm₆⟩ := SpecM.eventually_pow_mul_rpow_le 3 (c := ε' / 4) (by positivity)
  refine ⟨max (max Cb Cd) (3200 / ε' ^ 2), by positivity,
    max (max (max m₁ m₂) (max m₃ m₄)) (max (max m₅ m₆) (⌈4 / ε'⌉₊ + ⌈Real.exp 1⌉₊ + 8)), ?_⟩
  intro m hm p hpC hp1 Ω _ μ a ha
  simp only [ge_iff_le, max_le_iff] at hm
  obtain ⟨⟨⟨hm₁, hm₂⟩, hm₃, hm₄⟩, ⟨hm₅, hm₆'⟩, hm₇⟩ := hm
  have := ha.isProb
  set C := max (max Cb Cd) (3200 / ε' ^ 2) with hCdef
  -- the size of `m`
  have hm₇' : ((⌈4 / ε'⌉₊ + ⌈Real.exp 1⌉₊ + 8 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm₇
  push_cast at hm₇'
  have hc1 := Nat.le_ceil (4 / ε')
  have hc2 := Nat.le_ceil (Real.exp 1)
  have hc3 : (0 : ℝ) ≤ ⌈4 / ε'⌉₊ := Nat.cast_nonneg _
  have hc4 : (0 : ℝ) ≤ ⌈Real.exp 1⌉₊ := Nat.cast_nonneg _
  have hM8 : (8 : ℝ) ≤ m := by linarith
  have hm8 : 8 ≤ m := by exact_mod_cast hM8
  have hM0 : (0 : ℝ) < m := by linarith
  have hMε : 4 / ε' ≤ m := by linarith
  have hMe : Real.exp 1 ≤ m := by linarith
  have hlog : 1 ≤ Real.log m := (Real.le_log_iff_exp_le hM0).mpr hMe
  -- the constants
  have hC1 : Cb ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC5 : Cd ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC6 : 3200 / ε' ^ 2 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by positivity
  have hpC' : C * Real.log m ≤ p * m := (div_le_iff₀ hM0).mp hpC
  have hpm : ∀ C' : ℝ, C' ≤ C → C' * Real.log m / m ≤ p := fun C' h ↦
    le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by linarith)) hM0.le)
      hpC
  have hε2 : 3200 ≤ C * ε' ^ 2 := (div_le_iff₀ (by positivity)).mp hC6
  have hε2' : ε' ^ 2 ≤ 1 := pow_le_one₀ hε'0.le hε'1
  have hC3200 : 3200 ≤ C := hε2.trans (mul_le_of_le_one_right hC0 hε2')
  have hCge : C ≤ C * Real.log m := le_mul_of_one_le_right hC0 hlog
  have hCpM : C ≤ p * m := hCge.trans hpC'
  have hpM : 1 ≤ p * m := by linarith
  have hp0 : 0 < p := by
    by_contra hp
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hp) hM0.le
    linarith
  have hpm1 : 1 / (m : ℝ) ≤ p := by rw [div_le_iff₀ hM0]; linarith
  have hmr : (m : ℝ) ≤ 100 * ((m / 100 : ℕ) + 1) := by
    have : m ≤ 100 * (m / 100 + 1) := by omega
    exact_mod_cast this
  obtain ⟨hθ1, hθ2⟩ := SpecP.theta_le hε'0 hε'1 hε2 hCpM hp0 hM0 hmr
  have hK4 : 4 ≤ K := by omega
  have hKC : C₂ ≤ (K : ℝ) := by
    have := Nat.le_ceil C₂
    rw [hKdef]; push_cast; linarith
  have hqC : C₁ + 1 ≤ (q : ℝ) := by
    have := Nat.le_ceil C₁
    rw [hqdef]; push_cast; linarith
  -- the five events
  have E1 := hbad m hm₁ p (hpm Cb hC1) hp1 μ a ha
  have E2 := hlow m hm₂ p hp0.le hp1 μ a ha
  have E3 := hrel m hm₃ p hpm1 hp1 μ a ha
  have E4 := hsq m hm₄ p hpm1 hp1 μ a ha
  have E5 := hdisc m hm₅ p (hpm Cd hC5) hp1 μ a ha
  set A₁ := {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ K}
  set A₂ := {ω | BadLow (coinW a ω) p γ
    ((badSet (coinW a ω) p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100)}
  set A₃ := {ω | LowRel (coinW a ω) p γ (m / 100)}
  set A₄ := {ω | LowSq (coinW a ω) p (m / 100)}
  set A₅ := {ω | Disc (coinW a ω) p γ η}
  have hA₂ : MeasurableSet A₂ := SpecM.meas_coinW ha (fun w ↦ BadLow w p γ
    ((badSet w p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100))
  have hA₃ : MeasurableSet A₃ := SpecM.meas_coinW ha (fun w ↦ LowRel w p γ (m / 100))
  have hA₄ : MeasurableSet A₄ := SpecM.meas_coinW ha (fun w ↦ LowSq w p (m / 100))
  have hA₅ : MeasurableSet A₅ := SpecM.meas_coinW ha (fun w ↦ Disc w p γ η)
  have I2 := SpecM.inter_ge (μ := μ) (A := A₁) hA₂
  have I3 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂) hA₃
  have I4 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂ ∩ A₃) hA₄
  have I5 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂ ∩ A₃ ∩ A₄) hA₅
  -- on the intersection, `specPaper_of_facts`
  have hsub : A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ ⊆ {ω | ∃ R : Finset (Cube m),
      (R.card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ C₂ ∧ ∀ g : Cube m → ℝ,
        |energy (coinW a ω) g - p * energy 1 g| ≤
          ε * p * energy 1 g + (m : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ m) ^ 2} := by
    rintro ω ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    have hw := SpecM.coinW_01 a ω
    have hG := hgood hw hp0 hp1 h5
    have hκ : 0 ≤ ((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10) := by
      positivity
    have hk := SpecP.kappa_le (by linarith) hK4 (by positivity) (Nat.cast_nonneg _) h1 hpM
      hε'0 hMε (hm₆ m hm₆')
    have hθ : 101 * γ + Real.sqrt (2 / (p * ((m / 100 : ℕ) + 1))) + 800 / (p * m) +
        (m : ℝ) ^ 2 * (((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m +
          (2 : ℝ) ^ (-(m : ℝ) / 10)) / (2 * p) ≤ ε := by
      rw [hγdef]; linarith
    refine ⟨badSet (coinW a ω) p γ, ?_,
      specPaper_of_facts hw hp0 hp1 hγ hκ hm8 hmr hθ h3 h4 hG h2⟩
    refine h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hKC
  have hmono := measureReal_mono (μ := μ) hsub
  have hfin := SpecP.five_div_le (M := m) (by linarith) hqC
  have h5m : 1 - 1 / (m : ℝ) ^ q + (1 - 1 / (m : ℝ) ^ q) + (1 - 1 / (m : ℝ) ^ q) +
      (1 - 1 / (m : ℝ) ^ q) + (1 - 1 / (m : ℝ) ^ q) - 4 = 1 - 5 / (m : ℝ) ^ q := by ring
  linarith

end BMW26
