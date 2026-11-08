module

public import BS23.SmallRadius.IdentRules

/-!
# The identifiability inequality, abstractly

The sum-of-squares core of identifiability in the small-radius analysis
(`BS23/SmallRadius/Ident.lean`), for abstract polynomials in variables `σ` and a system `A` in which
the variables `wᵢ = X (wv i)`, `i < n'`, are Boolean. Fix a set `T` of points and write
`P = ∑_{i ∈ T} wᵢ`. The data are:

* polynomials `xᵢ` (degree `≤ 2`, `‖·‖₁ ≤ W^9`) and `yᵢ` (degree `≤ 1`, `‖·‖₁ ≤ W^7`) with
  `yᵢ - xᵢ = D` for `i ∈ T`, where `D` has degree `≤ 2` and `‖D‖₁ ≤ W^7`;
* **the moment axiom** `(∑ᵢ wᵢ xᵢ^(2s))^m ≤ K (∑ᵢ wᵢ)^m B` (in degree `5t`, norm `W^(38t)`) and the
  **scale bound** `B ≤ 32^t D^t` (a sum of squares);
* **the cluster bound** `∑_{i ∈ T} yᵢ^(2s) ≤ S (8s)^s D^s` (a sum of squares), `0 ≤ S ≤ W`.

Here `s = 2^a ≥ 8`, `m = 2^b`, `t = s m`, `0 ≤ K ≤ (256 s)^t`, `n' ≤ W` and `2^16 s ≤ W`. Then
(`BS23.SmallRadius.Core.H1`), in degree `9t` with norm `W^(48t)`,

  `P^(2t) D^(2t) ≤ W^m (2^16 s)^t P^(2t-m) D^t`.

The proof: `P D = ∑_{i ∈ T} wᵢ (yᵢ - xᵢ) = V - U` with `U = ∑_T wᵢ xᵢ`, `V = ∑_T wᵢ yᵢ`;
`(V - U)^(2s) ≤ 2^(2s-1) (U^(2s) + V^(2s))` (power mean); Hölder for idempotents
(`SoS.BooleanOn.holder`) gives `U^(2s) ≤ P^(2s-1) ∑_T wᵢ xᵢ^(2s) ≤ P^(2s-1) ∑ᵢ wᵢ xᵢ^(2s) = Z₁` and
`V^(2s) ≤ P^(2s-1) ∑_T wᵢ yᵢ^(2s) ≤ P^(2s-1) ∑_T yᵢ^(2s) ≤ P^(2s-1) S (8s)^s D^s = Z₂`. Raising
`(P D)^(2s) ≤ 2^(2s-1) (Z₁ + Z₂)` to the power `m` (`SoS.SosPlusIdeal.pow_sub_powW`) and the power
mean once more give `(P D)^(2t) ≤ 2^(2t-1) (Z₁^m + Z₂^m)`; the moment axiom, the scale bound and
`(∑ᵢ wᵢ)^m ≤ n'^m ≤ W^m` bound `Z₁^m ≤ K 32^t W^m P^(2t-m) D^t`, and `S ≤ W` bounds
`Z₂^m ≤ W^m (8s)^t P^(2t-m) D^t`. Finally `2^(2t-1) (K 32^t + (8s)^t) ≤ (2^16 s)^t`.
-/

@[expose] public section

namespace BS23.SmallRadius.Core

open MvPolynomial Finset SoS

variable {σ : Type*} {W : ℝ}

/-! ### Norms in powers of `W` -/

section Norms

variable {p q : MvPolynomial σ ℝ} {a b : ℕ}

theorem cn_pow (hp : coeffNorm1 p ≤ W ^ a) (r : ℕ) : coeffNorm1 (p ^ r) ≤ W ^ (a * r) :=
  (coeffNorm1_pow_le _ _).trans
    (by rw [pow_mul]; exact pow_le_pow_left₀ (coeffNorm1_nonneg _) hp r)

theorem cn_mul (hp : coeffNorm1 p ≤ W ^ a) (hq : coeffNorm1 q ≤ W ^ b) :
    coeffNorm1 (p * q) ≤ W ^ (a + b) :=
  (coeffNorm1_mul_le _ _).trans (by
    rw [pow_add]
    exact mul_le_mul hp hq (coeffNorm1_nonneg _) ((coeffNorm1_nonneg _).trans hp))

theorem cn_add (hW : 2 ≤ W) {e : ℕ} (hp : coeffNorm1 p ≤ W ^ a) (hq : coeffNorm1 q ≤ W ^ b)
    (ha : a ≤ e) (hb : b ≤ e) : coeffNorm1 (p + q) ≤ W ^ (e + 1) :=
  (coeffNorm1_add_le _ _).trans (add_le_pow_succ hW (hp.trans (pow_le_pow_of_two_le hW ha))
    (hq.trans (pow_le_pow_of_two_le hW hb)))

theorem cn_sub (hW : 2 ≤ W) {e : ℕ} (hp : coeffNorm1 p ≤ W ^ a) (hq : coeffNorm1 q ≤ W ^ b)
    (ha : a ≤ e) (hb : b ≤ e) : coeffNorm1 (p - q) ≤ W ^ (e + 1) :=
  (coeffNorm1_sub_le _ _).trans (add_le_pow_succ hW (hp.trans (pow_le_pow_of_two_le hW ha))
    (hq.trans (pow_le_pow_of_two_le hW hb)))

theorem cn_C_mul {c : ℝ} {e : ℕ} (hc : |c| ≤ W ^ e) (hp : coeffNorm1 p ≤ W ^ a) :
    coeffNorm1 (C c * p) ≤ W ^ (e + a) := by
  rw [coeffNorm1_C_mul, pow_add]
  exact mul_le_mul hc hp (coeffNorm1_nonneg _) ((abs_nonneg _).trans hc)

theorem cn_C {c : ℝ} {e : ℕ} (hc : |c| ≤ W ^ e) : coeffNorm1 (C c : MvPolynomial σ ℝ) ≤ W ^ e := by
  rw [coeffNorm1_C]; exact hc

theorem cn_sum (hW : 2 ≤ W) {ι : Type*} (T : Finset ι) {f : ι → MvPolynomial σ ℝ} {c : ℕ}
    (hT : (T.card : ℝ) ≤ W ^ c) (hf : ∀ j ∈ T, coeffNorm1 (f j) ≤ W ^ a) :
    coeffNorm1 (∑ j ∈ T, f j) ≤ W ^ (a + c) :=
  (coeffNorm1_sum_le _ _).trans (sum_le_pow hW T hf hT)

theorem cn_X (i : σ) : coeffNorm1 (X i : MvPolynomial σ ℝ) ≤ W ^ 0 := by
  rw [coeffNorm1_X, pow_zero]

theorem cn_mono (hW : 2 ≤ W) (hp : coeffNorm1 p ≤ W ^ a) (h : a ≤ b) :
    coeffNorm1 p ≤ W ^ b :=
  hp.trans (pow_le_pow_of_two_le hW h)

end Norms

theorem isSumSq_pow_two_mul (p : MvPolynomial σ ℝ) (r : ℕ) : IsSumSq (p ^ (2 * r)) := by
  rw [pow_mul']; exact isSumSq_sq _

/-! ### The abstract identifiability inequality -/

section H1

variable {A : System σ ℝ} {n' : ℕ} {wv : Fin n' → σ}

/-- The data of the abstract identifiability inequality. -/
structure H1Data (A : System σ ℝ) (n' : ℕ) (wv : Fin n' → σ) where
  /-- The set of points. -/
  T : Finset (Fin n')
  /-- The moment polynomials `xᵢ`. -/
  x : Fin n' → MvPolynomial σ ℝ
  /-- The cluster polynomials `yᵢ`. -/
  y : Fin n' → MvPolynomial σ ℝ
  /-- The squared distance `D`. -/
  D : MvPolynomial σ ℝ
  /-- The scale estimate `B`. -/
  B : MvPolynomial σ ℝ
  /-- The constant of the moment axiom. -/
  K : ℝ
  /-- The size of the cluster. -/
  S : ℝ

/-- The hypotheses of the abstract identifiability inequality. -/
structure H1Data.Good (H : H1Data A n' wv) (W : ℝ) (s m t : ℕ) : Prop where
  hbool : ∀ i, HasEq A (X (wv i) ^ 2 - X (wv i))
  hW : 2 ≤ W
  hn' : (n' : ℝ) ≤ W
  s_pow : ∃ a, s = 2 ^ a
  m_pow : ∃ b, m = 2 ^ b
  ht : t = s * m
  hs8 : 8 ≤ s
  hsW : 2 ^ 16 * (s : ℝ) ≤ W
  xd : ∀ i, (H.x i).totalDegree ≤ 2
  xn : ∀ i, coeffNorm1 (H.x i) ≤ W ^ 9
  yd : ∀ i, (H.y i).totalDegree ≤ 1
  yn : ∀ i, coeffNorm1 (H.y i) ≤ W ^ 7
  Dd : H.D.totalDegree ≤ 2
  Dn : coeffNorm1 H.D ≤ W ^ 7
  Dsos : IsSumSq H.D
  yx : ∀ i ∈ H.T, H.y i - H.x i = H.D
  K0 : 0 ≤ H.K
  K_le : H.K ≤ (256 * s) ^ t
  ax : SosPlusIdeal A (5 * t) (W ^ (38 * t))
    (C H.K * (∑ i, X (wv i)) ^ m * H.B - (∑ i, X (wv i) * H.x i ^ (2 * s)) ^ m)
  Bsos : IsSumSq (C ((32 : ℝ) ^ t) * H.D ^ t - H.B)
  Bd : H.B.totalDegree ≤ 2 * t
  Bn : coeffNorm1 H.B ≤ W ^ (16 * t)
  S0 : 0 ≤ H.S
  SW : H.S ≤ W
  E2 : IsSumSq (C (H.S * (8 * s) ^ s) * H.D ^ s - ∑ i ∈ H.T, H.y i ^ (2 * s))

namespace H1Data

variable {s m t : ℕ} {H : H1Data A n' wv}

/-- `P = ∑_{i ∈ T} wᵢ`. -/
noncomputable def P (H : H1Data A n' wv) : MvPolynomial σ ℝ := ∑ i ∈ H.T, X (wv i)

/-- `U = ∑_{i ∈ T} wᵢ xᵢ`. -/
noncomputable def U (H : H1Data A n' wv) : MvPolynomial σ ℝ :=
  ∑ i ∈ H.T, X (wv i) * H.x i

/-- `V = ∑_{i ∈ T} wᵢ yᵢ`. -/
noncomputable def V (H : H1Data A n' wv) : MvPolynomial σ ℝ :=
  ∑ i ∈ H.T, X (wv i) * H.y i

/-- `Mw = ∑ᵢ wᵢ xᵢ^(2s)`. -/
noncomputable def Mw (H : H1Data A n' wv) (s : ℕ) : MvPolynomial σ ℝ :=
  ∑ i, X (wv i) * H.x i ^ (2 * s)

/-- `Z₁ = P^(2s-1) Mw`. -/
noncomputable def Z₁ (H : H1Data A n' wv) (s : ℕ) : MvPolynomial σ ℝ :=
  H.P ^ (2 * s - 1) * H.Mw s

/-- `Z₂ = P^(2s-1) S (8s)^s D^s`. -/
noncomputable def Z₂ (H : H1Data A n' wv) (s : ℕ) : MvPolynomial σ ℝ :=
  H.P ^ (2 * s - 1) * (C (H.S * (8 * s) ^ s) * H.D ^ s)

/-- `Yp = 2^(2s-1) (Z₁ + Z₂)`. -/
noncomputable def Yp (H : H1Data A n' wv) (s : ℕ) : MvPolynomial σ ℝ :=
  C ((2 : ℝ) ^ (2 * s - 1)) * (H.Z₁ s + H.Z₂ s)

namespace Good

variable (hH : H.Good W s m t)
include hH

theorem one_le_s : 1 ≤ s := by have := hH.hs8; omega

theorem m_pos : 1 ≤ m := by
  obtain ⟨b, hb⟩ := hH.m_pow; rw [hb]; exact Nat.one_le_two_pow

theorem t_pos : 8 ≤ t := by
  rw [hH.ht]; have := hH.hs8; have := hH.m_pos; nlinarith

theorem m_le_t : m ≤ t := by rw [hH.ht]; have := hH.one_le_s; nlinarith

theorem card_T : (H.T.card : ℝ) ≤ W ^ 1 := by
  rw [pow_one]
  exact le_trans (by exact_mod_cast (card_le_univ H.T).trans (by simp)) hH.hn'

theorem card_univ : ((univ : Finset (Fin n')).card : ℝ) ≤ W ^ 1 := by
  rw [pow_one, Finset.card_univ, Fintype.card_fin]; exact hH.hn'

theorem W_pos : 0 < W := by have := hH.hW; linarith

theorem s_le_W : (s : ℝ) ≤ W := by
  have := hH.hsW
  have : (0 : ℝ) ≤ s := by positivity
  nlinarith

theorem eight_s_le : 8 * (s : ℝ) ≤ W := by
  have := hH.hsW
  have : (0 : ℝ) ≤ s := by positivity
  nlinarith

theorem two_le_W : (2 : ℝ) ≤ W := hH.hW

/-- `2^e ≤ W^e`. -/
theorem two_pow_le (e : ℕ) : (2 : ℝ) ^ e ≤ W ^ e := pow_le_pow_left₀ (by norm_num) hH.hW e

theorem abs_two_pow_le (e : ℕ) : |(2 : ℝ) ^ e| ≤ W ^ e := by
  rw [abs_of_nonneg (by positivity)]; exact hH.two_pow_le e

/-! #### Norms and degrees of the pieces -/

theorem Pn : coeffNorm1 H.P ≤ W ^ 1 := by
  have := cn_sum hH.hW H.T (f := fun i ↦ X (wv i)) (a := 0) hH.card_T fun i _ ↦ cn_X _
  simpa [P] using this

omit hH in
theorem Pd : H.P.totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun _ _ ↦ (totalDegree_X (R := ℝ) _).le

theorem Un : coeffNorm1 H.U ≤ W ^ 10 := by
  have := cn_sum hH.hW H.T (f := fun i ↦ X (wv i) * H.x i) (a := 9) hH.card_T fun i _ ↦ by
    have := cn_mul (cn_X (W := W) (wv i)) (hH.xn i); simpa using this
  simpa [U] using this

theorem Ud : H.U.totalDegree ≤ 3 :=
  totalDegree_finsetSum_le fun i _ ↦ (totalDegree_mul _ _).trans
    (by have := hH.xd i; rw [totalDegree_X]; omega)

theorem Vn : coeffNorm1 H.V ≤ W ^ 8 := by
  have := cn_sum hH.hW H.T (f := fun i ↦ X (wv i) * H.y i) (a := 7) hH.card_T fun i _ ↦ by
    have := cn_mul (cn_X (W := W) (wv i)) (hH.yn i); simpa using this
  simpa [V] using this

theorem Vd : H.V.totalDegree ≤ 3 :=
  totalDegree_finsetSum_le fun i _ ↦ (totalDegree_mul _ _).trans
    (by have := hH.yd i; rw [totalDegree_X]; omega)

/-- `V - U = P D`. -/
theorem V_sub_U : H.V - H.U = H.P * H.D := by
  rw [V, U, P, ← sum_sub_distrib, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [← mul_sub, hH.yx i hi]

theorem Mwn : coeffNorm1 (H.Mw s) ≤ W ^ (18 * s + 1) := by
  have := cn_sum hH.hW univ (f := fun i ↦ X (wv i) * H.x i ^ (2 * s)) (a := 18 * s)
    hH.card_univ fun i _ ↦ by
      have := cn_mul (cn_X (W := W) (wv i)) (cn_pow (hH.xn i) (2 * s))
      rw [zero_add] at this
      exact this.trans_eq (by ring_nf)
  simpa [Mw] using this

theorem Mwd : (H.Mw s).totalDegree ≤ 4 * s + 1 :=
  totalDegree_finsetSum_le fun i _ ↦ (totalDegree_mul _ _).trans (by
    have h1 := (totalDegree_pow (H.x i) (2 * s)).trans (Nat.mul_le_mul_left (2 * s) (hH.xd i))
    rw [totalDegree_X]; omega)

theorem Ppow_n (r : ℕ) : coeffNorm1 (H.P ^ r) ≤ W ^ r := by
  have := cn_pow hH.Pn r; rwa [one_mul] at this

omit hH in
theorem Ppow_d (r : ℕ) : (H.P ^ r).totalDegree ≤ r :=
  calc (H.P ^ r).totalDegree ≤ r * H.P.totalDegree := totalDegree_pow _ _
    _ ≤ r * 1 := Nat.mul_le_mul_left r Pd
    _ = r := mul_one r

theorem Dpow_n (r : ℕ) : coeffNorm1 (H.D ^ r) ≤ W ^ (7 * r) := cn_pow hH.Dn r

theorem Dpow_d (r : ℕ) : (H.D ^ r).totalDegree ≤ 2 * r :=
  calc (H.D ^ r).totalDegree ≤ r * H.D.totalDegree := totalDegree_pow _ _
    _ ≤ r * 2 := Nat.mul_le_mul_left r hH.Dd
    _ = 2 * r := mul_comm r 2

theorem Z₁n : coeffNorm1 (H.Z₁ s) ≤ W ^ (20 * s) := by
  have := cn_mul (hH.Ppow_n (2 * s - 1)) hH.Mwn
  refine cn_mono hH.hW this ?_
  have := hH.one_le_s; omega

theorem Z₁d : (H.Z₁ s).totalDegree ≤ 6 * s := by
  refine (totalDegree_mul _ _).trans ?_
  have := Ppow_d (H := H) (2 * s - 1)
  have := hH.Mwd
  have := hH.one_le_s
  omega

theorem Sc_abs : |H.S * (8 * s) ^ s| ≤ W ^ (s + 1) := by
  rw [abs_of_nonneg (mul_nonneg hH.S0 (by positivity)), pow_succ, mul_comm (W ^ s)]
  exact mul_le_mul hH.SW (pow_le_pow_left₀ (by positivity) hH.eight_s_le s) (by positivity)
    hH.W_pos.le

theorem CSD_n : coeffNorm1 (C (H.S * (8 * s) ^ s) * H.D ^ s) ≤ W ^ (8 * s + 1) := by
  have := cn_C_mul hH.Sc_abs (hH.Dpow_n s)
  exact cn_mono hH.hW this (by omega)

theorem CSD_d : (C (H.S * (8 * s) ^ s) * H.D ^ s).totalDegree ≤ 2 * s :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hH.Dpow_d s)

theorem Z₂n : coeffNorm1 (H.Z₂ s) ≤ W ^ (10 * s) := by
  have := cn_mul (hH.Ppow_n (2 * s - 1)) hH.CSD_n
  refine cn_mono hH.hW this ?_
  have := hH.one_le_s; omega

theorem Z₂d : (H.Z₂ s).totalDegree ≤ 6 * s := by
  refine (totalDegree_mul _ _).trans ?_
  have := Ppow_d (H := H) (2 * s - 1)
  have := hH.CSD_d
  omega

theorem Ypn : coeffNorm1 (H.Yp s) ≤ W ^ (22 * s) := by
  have h := cn_C_mul (hH.abs_two_pow_le (2 * s - 1))
    (cn_add hH.hW (e := 20 * s) hH.Z₁n hH.Z₂n le_rfl (by omega))
  refine cn_mono hH.hW h ?_
  have := hH.one_le_s; omega

theorem Ypd : (H.Yp s).totalDegree ≤ 6 * s :=
  (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact (totalDegree_add _ _).trans (max_le hH.Z₁d hH.Z₂d))

/-! #### The steps -/

/-- The certificate of `P^r ≥ 0`. -/
theorem P_pow (r : ℕ) : SosPlusIdeal A (r * 2) (W ^ (2 * r)) (H.P ^ r) := by
  have h := (sum_wW hH.hbool H.T hH.card_T).powW hH.hW (e := 1) hH.Pn le_rfl le_rfl r
  exact h.monoW hH.hW le_rfl (by omega)

/-- (I4) `(P D)^(2s) ≤ 2^(2s-1) (U^(2s) + V^(2s))`. -/
theorem step_I4 :
    SosPlusIdeal A (8 * s) (W ^ (22 * s + 1))
      (C ((2 : ℝ) ^ (2 * s - 1)) * (H.U ^ (2 * s) + H.V ^ (2 * s)) - (H.P * H.D) ^ (2 * s)) := by
  obtain ⟨a, ha⟩ := hH.s_pow
  have h2s : 2 * s = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
  have h := isSumSq_add_pow_le (-H.U) H.V (a + 1)
  rw [← h2s, (even_two_mul s).neg_pow, neg_add_eq_sub, hH.V_sub_U] at h
  refine SosPlusIdeal.of_isSumSqW A h ?_ ?_
  · have hPD : (H.P * H.D).totalDegree ≤ 3 :=
      (totalDegree_mul _ _).trans (by have := Pd (H := H); have := hH.Dd; omega)
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * s) hH.Ud; omega)
      · exact (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * s) hH.Vd; omega)
    · exact (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * s) hPD; omega)
  · have hU := cn_pow hH.Un (2 * s)
    have hV := cn_pow (cn_mono hH.hW hH.Vn (show 8 ≤ 10 by norm_num)) (2 * s)
    have h1 := cn_C_mul (hH.abs_two_pow_le (2 * s - 1))
      (cn_add hH.hW (e := 10 * (2 * s)) hU hV le_rfl le_rfl)
    have hPD : coeffNorm1 (H.P * H.D) ≤ W ^ 11 := by
      rw [← hH.V_sub_U]
      exact cn_sub hH.hW (e := 10) (cn_mono hH.hW hH.Vn (by norm_num)) hH.Un le_rfl le_rfl
    have h2 := cn_pow hPD (2 * s)
    have := hH.one_le_s
    exact cn_sub hH.hW (e := 22 * s) h1 h2 (by omega) (by omega)

/-- The Booleanity of the weights, as `SoS.BooleanOn`. -/
theorem boolOn [DecidableEq σ] : BooleanOn A (univ.image wv) := fun j hj ↦ by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hj; exact hH.hbool i

theorem three_le_sq : (3 : ℝ) ≤ W ^ 2 := by have := hH.hW; nlinarith

/-- (I5) `U^(2s) ≤ Z₁ = P^(2s-1) ∑ᵢ wᵢ xᵢ^(2s)`: Hölder on `T`, then the other points. -/
theorem step_T1 : SosPlusIdeal A (8 * s) (W ^ (44 * s + 1)) (H.Z₁ s - H.U ^ (2 * s)) := by
  classical
  obtain ⟨a, ha⟩ := hH.s_pow
  have h2s : 2 * s = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
  have hs1 := hH.one_le_s
  have hc : (1 : ℝ) ≤ W ^ 10 := one_le_pow_of_two_le hH.hW 10
  have hβc : (H.T.card : ℝ) * W ^ 9 ≤ W ^ 10 := by
    have := hH.card_T
    calc (H.T.card : ℝ) * W ^ 9 ≤ W ^ 1 * W ^ 9 :=
          mul_le_mul_of_nonneg_right this (pow_nonneg_of_two_le hH.hW 9)
      _ = W ^ 10 := by rw [← pow_add]
  have hhol := hH.boolOn.holder H.T (w := wv) (fun i _ ↦ mem_image_of_mem _ (mem_univ _)) H.x
    (e := 2) (fun i _ ↦ hH.xd i) (fun i _ ↦ hH.xn i) hc hβc (a + 1)
  rw [← h2s] at hhol
  have hhol' : SosPlusIdeal A (8 * s) (W ^ (44 * s))
      (H.P ^ (2 * s - 1) * ∑ i ∈ H.T, X (wv i) * H.x i ^ (2 * s) - H.U ^ (2 * s)) := by
    refine hhol.mono (by omega) ?_
    calc (3 * (W ^ 10) ^ 2) ^ (2 * s) ≤ (W ^ 22) ^ (2 * s) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          calc 3 * (W ^ 10) ^ 2 ≤ W ^ 2 * (W ^ 10) ^ 2 :=
                mul_le_mul_of_nonneg_right hH.three_le_sq (by positivity)
            _ = W ^ 22 := by ring
      _ = W ^ (44 * s) := by rw [← pow_mul]; ring_nf
  -- The other points.
  set R := univ \ H.T with hR
  have hRc : (R.card : ℝ) ≤ W ^ 1 := by
    rw [pow_one]
    exact le_trans (by exact_mod_cast (card_le_univ R).trans (by simp)) hH.hn'
  have hext : SosPlusIdeal A (2 * (s * 2) + 2) (W ^ (2 * 9 * s + 1))
      (∑ i ∈ R, X (wv i) * H.x i ^ (2 * s)) :=
    SosPlusIdeal.sumW hH.hW R hRc fun i _ ↦ w_mul_pow hH.hbool i (hH.xd i) (hH.xn i) s
  have hextn : coeffNorm1 (∑ i ∈ R, X (wv i) * H.x i ^ (2 * s)) ≤ W ^ (2 * 9 * s + 1) := by
    refine cn_sum hH.hW R hRc fun i _ ↦ ?_
    have := cn_mul (cn_X (W := W) (wv i)) (cn_pow (hH.xn i) (2 * s))
    exact this.trans_eq (by ring_nf)
  have hprod := SosPlusIdeal.mulW hH.hW (e := 2 * 9 * s + 1) (hH.P_pow (2 * s - 1)) hext hextn
    le_rfl le_rfl
  have hMw : H.Mw s = ∑ i ∈ H.T, X (wv i) * H.x i ^ (2 * s) +
      ∑ i ∈ R, X (wv i) * H.x i ^ (2 * s) := by
    rw [Mw, hR, add_comm, sum_sdiff (subset_univ _)]
  have h := SosPlusIdeal.addW hH.hW (e := 44 * s) hhol' (hprod.mono (by omega) le_rfl) le_rfl
    (by omega)
  refine h.congr ?_
  rw [Z₁, hMw]
  ring

/-- (I6) `V^(2s) ≤ Z₂ = P^(2s-1) S (8s)^s D^s`: Hölder on `T`, `wᵢ ≤ 1`, and the cluster
bound. -/
theorem step_T2 : SosPlusIdeal A (8 * s) (W ^ (36 * s + 1)) (H.Z₂ s - H.V ^ (2 * s)) := by
  classical
  obtain ⟨a, ha⟩ := hH.s_pow
  have h2s : 2 * s = 2 ^ (a + 1) := by rw [ha, pow_succ]; ring
  have hs1 := hH.one_le_s
  have hc : (1 : ℝ) ≤ W ^ 8 := one_le_pow_of_two_le hH.hW 8
  have hβc : (H.T.card : ℝ) * W ^ 7 ≤ W ^ 8 := by
    have := hH.card_T
    calc (H.T.card : ℝ) * W ^ 7 ≤ W ^ 1 * W ^ 7 :=
          mul_le_mul_of_nonneg_right this (pow_nonneg_of_two_le hH.hW 7)
      _ = W ^ 8 := by rw [← pow_add]
  have hhol := hH.boolOn.holder H.T (w := wv) (fun i _ ↦ mem_image_of_mem _ (mem_univ _)) H.y
    (e := 1) (fun i _ ↦ hH.yd i) (fun i _ ↦ hH.yn i) hc hβc (a + 1)
  rw [← h2s] at hhol
  have hhol' : SosPlusIdeal A (8 * s) (W ^ (36 * s))
      (H.P ^ (2 * s - 1) * ∑ i ∈ H.T, X (wv i) * H.y i ^ (2 * s) - H.V ^ (2 * s)) := by
    refine hhol.mono (by omega) ?_
    calc (3 * (W ^ 8) ^ 2) ^ (2 * s) ≤ (W ^ 18) ^ (2 * s) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          calc 3 * (W ^ 8) ^ 2 ≤ W ^ 2 * (W ^ 8) ^ 2 :=
                mul_le_mul_of_nonneg_right hH.three_le_sq (by positivity)
            _ = W ^ 18 := by ring
      _ = W ^ (36 * s) := by rw [← pow_mul]; ring_nf
  -- `∑_T wᵢ yᵢ^(2s) ≤ S (8s)^s D^s`.
  have h2a : SosPlusIdeal A (2 * (s * 1) + 2) (W ^ (2 * 7 * s + 2 + 1))
      (∑ i ∈ H.T, (1 - X (wv i)) * H.y i ^ (2 * s)) :=
    SosPlusIdeal.sumW hH.hW H.T hH.card_T fun i _ ↦
      one_sub_w_mul_pow hH.hbool hH.hW i (hH.yd i) (hH.yn i) s
  have hyT : coeffNorm1 (∑ i ∈ H.T, H.y i ^ (2 * s)) ≤ W ^ (7 * (2 * s) + 1) :=
    cn_sum hH.hW H.T hH.card_T fun i _ ↦ cn_pow (hH.yn i) (2 * s)
  have hwyT : coeffNorm1 (∑ i ∈ H.T, X (wv i) * H.y i ^ (2 * s)) ≤ W ^ (7 * (2 * s) + 1) := by
    refine cn_sum hH.hW H.T hH.card_T fun i _ ↦ ?_
    have := cn_mul (cn_X (W := W) (wv i)) (cn_pow (hH.yn i) (2 * s))
    rwa [zero_add] at this
  have h2b : SosPlusIdeal A (2 * (s * 1) + 2) (W ^ (14 * s + 2))
      (C (H.S * (8 * s) ^ s) * H.D ^ s - ∑ i ∈ H.T, H.y i ^ (2 * s)) := by
    refine SosPlusIdeal.of_isSumSqW A hH.E2 ?_ ?_
    · refine (totalDegree_sub _ _).trans (max_le (hH.CSD_d.trans (by omega)) ?_)
      refine totalDegree_finsetSum_le fun i _ ↦ (totalDegree_pow _ _).trans ?_
      have := Nat.mul_le_mul_left (2 * s) (hH.yd i)
      omega
    · exact cn_sub hH.hW (e := 14 * s + 1) hH.CSD_n hyT (by omega) (by omega)
  have h2 := SosPlusIdeal.addW hH.hW (e := 14 * s + 3) h2a h2b (by omega) (by omega)
  have h2e : ∑ i ∈ H.T, (1 - X (wv i)) * H.y i ^ (2 * s) +
      (C (H.S * (8 * s) ^ s) * H.D ^ s - ∑ i ∈ H.T, H.y i ^ (2 * s)) =
      C (H.S * (8 * s) ^ s) * H.D ^ s - ∑ i ∈ H.T, X (wv i) * H.y i ^ (2 * s) := by
    simp only [sub_mul, one_mul, sum_sub_distrib]
    ring
  rw [h2e] at h2
  have h2n : coeffNorm1 (C (H.S * (8 * s) ^ s) * H.D ^ s -
      ∑ i ∈ H.T, X (wv i) * H.y i ^ (2 * s)) ≤ W ^ (14 * s + 2) :=
    cn_sub hH.hW (e := 14 * s + 1) hH.CSD_n hwyT (by omega) (by omega)
  have hprod := SosPlusIdeal.mulW hH.hW (e := 14 * s + 4) (hH.P_pow (2 * s - 1)) h2 h2n
    le_rfl (by omega)
  have h := SosPlusIdeal.addW hH.hW (e := 36 * s) hhol' (hprod.mono (by omega) le_rfl) le_rfl
    (by omega)
  refine h.congr ?_
  rw [Z₂]
  ring

/-- `(P D)^(2s) ≤ Yp = 2^(2s-1) (Z₁ + Z₂)`. -/
theorem step_YX : SosPlusIdeal A (8 * s) (W ^ (46 * s + 2)) (H.Yp s - (H.P * H.D) ^ (2 * s)) := by
  have hs1 := hH.one_le_s
  have h12 := SosPlusIdeal.addW hH.hW (e := 44 * s + 1) hH.step_T1 hH.step_T2 le_rfl (by omega)
  have h3 := SosPlusIdeal.smulW hH.hW (c := (2 : ℝ) ^ (2 * s - 1)) (e := 2 * s - 1)
    (by positivity) (hH.two_pow_le _) h12
  have h := SosPlusIdeal.addW hH.hW (e := 46 * s + 1) hH.step_I4 h3 (by omega) (by omega)
  refine (h.monoW hH.hW le_rfl le_rfl).congr ?_
  rw [Yp]
  ring

/-- Raising to the power `m`: `(P D)^(2t) ≤ Yp^m`. -/
theorem step_pow :
    SosPlusIdeal A (8 * t) (W ^ (47 * t)) (H.Yp s ^ m - H.P ^ (2 * t) * H.D ^ (2 * t)) := by
  have hs1 := hH.one_le_s
  have hX : SosPlusIdeal A (8 * s) (W ^ (16 * s)) ((H.P * H.D) ^ (2 * s)) := by
    have hPD : coeffNorm1 (H.P * H.D) ≤ W ^ 8 := by
      have := cn_mul hH.Pn hH.Dn; exact this
    refine SosPlusIdeal.of_isSumSqW A (isSumSq_pow_two_mul _ s) ?_ ?_
    · refine (totalDegree_pow _ _).trans ?_
      have : (H.P * H.D).totalDegree ≤ 3 :=
        (totalDegree_mul _ _).trans (by have := Pd (H := H); have := hH.Dd; omega)
      have := Nat.mul_le_mul_left (2 * s) this
      omega
    · have := cn_pow hPD (2 * s); exact this.trans_eq (by ring_nf)
  have hXn : coeffNorm1 ((H.P * H.D) ^ (2 * s)) ≤ W ^ (22 * s) := by
    have hPD : coeffNorm1 (H.P * H.D) ≤ W ^ 8 := cn_mul hH.Pn hH.Dn
    exact cn_mono hH.hW (cn_pow hPD (2 * s)) (by omega)
  have h := SosPlusIdeal.pow_sub_powW hH.hW hX hH.step_YX hXn hH.Ypn m
  have hmax : max (16 * s) (max (46 * s + 2) (22 * s)) = 46 * s + 2 := by omega
  rw [hmax] at h
  have hsm : s * m = t := hH.ht.symm
  refine (h.monoW hH.hW (le_of_eq ?_) ?_).congr ?_
  · rw [← hsm]; ring
  · have hm := hH.m_pos
    have hs8 := hH.hs8
    rw [← hsm]
    nlinarith
  · rw [← pow_mul, mul_pow, ← hsm]
    ring_nf

/-- The power mean: `Yp^m ≤ 2^(2t-1) (Z₁^m + Z₂^m)`. -/
theorem step_mean :
    SosPlusIdeal A (8 * t) (W ^ (24 * t))
      (C ((2 : ℝ) ^ (2 * t - 1)) * (H.Z₁ s ^ m + H.Z₂ s ^ m) - H.Yp s ^ m) := by
  obtain ⟨b, hb⟩ := hH.m_pow
  have hs1 := hH.one_le_s
  have hm := hH.m_pos
  have hsm : s * m = t := hH.ht.symm
  have h := isSumSq_add_pow_le (H.Z₁ s) (H.Z₂ s) b
  rw [← hb] at h
  have h' := isSumSq_C_mul (c := (2 : ℝ) ^ ((2 * s - 1) * m)) (by positivity) h
  have hexp : (2 * s - 1) * m + (m - 1) = 2 * t - 1 := by
    rw [← hsm]
    have : (2 * s - 1) * m + m = 2 * (s * m) := by
      rw [← Nat.succ_mul, ← mul_assoc]; congr 1; omega
    have : 1 ≤ 2 * (s * m) := by nlinarith
    omega
  have heq : C ((2 : ℝ) ^ ((2 * s - 1) * m)) *
      (C ((2 : ℝ) ^ (m - 1)) * (H.Z₁ s ^ m + H.Z₂ s ^ m) - (H.Z₁ s + H.Z₂ s) ^ m) =
      C ((2 : ℝ) ^ (2 * t - 1)) * (H.Z₁ s ^ m + H.Z₂ s ^ m) - H.Yp s ^ m := by
    rw [Yp, mul_pow, ← C_pow, ← pow_mul, ← hexp, pow_add, C_mul]
    ring
  rw [heq] at h'
  refine SosPlusIdeal.of_isSumSqW A h' ?_ ?_
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_pow _ _).trans ?_
        have := Nat.mul_le_mul_left m hH.Z₁d
        rw [← hsm]; nlinarith
      · refine (totalDegree_pow _ _).trans ?_
        have := Nat.mul_le_mul_left m hH.Z₂d
        rw [← hsm]; nlinarith
    · refine (totalDegree_pow _ _).trans ?_
      have := Nat.mul_le_mul_left m hH.Ypd
      rw [← hsm]; nlinarith
  · have hZ := cn_add hH.hW (e := 20 * s * m) (cn_pow hH.Z₁n m) (cn_pow hH.Z₂n m) le_rfl
      (by nlinarith)
    have h1 := cn_C_mul (hH.abs_two_pow_le (2 * t - 1)) hZ
    have h2 := cn_pow hH.Ypn m
    refine cn_mono hH.hW (cn_sub hH.hW (e := 22 * t) h1 h2 ?_ ?_) ?_
    · rw [← hsm]
      have : 2 * (s * m) - 1 + (20 * s * m + 1) = 22 * (s * m) := by
        have : 1 ≤ s * m := by nlinarith
        have : 20 * s * m = 20 * (s * m) := by ring
        omega
      omega
    · rw [← hsm]; nlinarith
    · have := hH.t_pos; omega

theorem K_le_W : H.K ≤ W ^ (2 * t) := by
  have hs := hH.s_le_W
  have h256 : 256 * (s : ℝ) ≤ W ^ 2 := by
    have := hH.hsW; have : (0 : ℝ) ≤ s := by positivity
    nlinarith [hH.hW]
  calc H.K ≤ (256 * s) ^ t := hH.K_le
    _ ≤ (W ^ 2) ^ t := pow_le_pow_left₀ (by positivity) h256 t
    _ = W ^ (2 * t) := by rw [← pow_mul]

theorem thirtytwo_le : (32 : ℝ) ≤ W := by
  have := hH.hsW; have : (8 : ℝ) ≤ s := by exact_mod_cast hH.hs8
  nlinarith

theorem Dpow_sos (r : ℕ) : IsSumSq (H.D ^ r) := isSumSq_pow hH.Dsos r

/-- `Z₁^m ≤ K 32^t W^m P^(2t-m) D^t`: the moment axiom, the scale bound and
`(∑ᵢ wᵢ)^m ≤ n'^m ≤ W^m`. -/
theorem step_Z1 :
    SosPlusIdeal A (9 * t) (W ^ (43 * t))
      (C (H.K * 32 ^ t * W ^ m) * H.P ^ ((2 * s - 1) * m) * H.D ^ t - H.Z₁ s ^ m) := by
  classical
  have hs1 := hH.one_le_s
  have hm := hH.m_pos
  have ht8 := hH.t_pos
  have hmt := hH.m_le_t
  have hsm : s * m = t := hH.ht.symm
  have hW := hH.hW
  have hK2 := hH.K_le_W
  have h32 : |(32 : ℝ) ^ t| ≤ W ^ t := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by norm_num) hH.thirtytwo_le t
  -- (b) `K (∑ᵢ wᵢ)^m (32^t D^t - B) ≥ 0`.
  have hsw := sum_wW hH.hbool (univ : Finset (Fin n')) hH.card_univ
  have hswn : coeffNorm1 (∑ i, X (wv i) : MvPolynomial σ ℝ) ≤ W ^ 1 := by
    have := cn_sum hW (univ : Finset (Fin n')) (f := fun i ↦ (X (wv i) : MvPolynomial σ ℝ))
      (a := 0) hH.card_univ fun i _ ↦ cn_X _
    simpa using this
  have hswm := hsw.powW hW (e := 1) hswn le_rfl le_rfl m
  have hqd : (C ((32 : ℝ) ^ t) * H.D ^ t - H.B).totalDegree ≤ 2 * t :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_mul _ _).trans
      (by rw [totalDegree_C, zero_add]; exact hH.Dpow_d t)) hH.Bd)
  have hqn : coeffNorm1 (C ((32 : ℝ) ^ t) * H.D ^ t - H.B) ≤ W ^ (16 * t + 1) :=
    cn_sub hW (e := 16 * t) (cn_C_mul h32 (hH.Dpow_n t)) hH.Bn (by omega) le_rfl
  have hb := SosPlusIdeal.mulSOSW hW (k₁ := 2 * t) hH.Bsos hqd hqn hswm
  have hb' := SosPlusIdeal.smulW hW (c := H.K) (e := 2 * t) hH.K0 hK2 hb
  -- (c) `K 32^t D^t (n'^m - (∑ᵢ wᵢ)^m) ≥ 0`.
  have hcs := card_sub_sum_wW hH.hbool hW (univ : Finset (Fin n')) hH.card_univ
  have hCn : coeffNorm1 (C ((univ : Finset (Fin n')).card : ℝ) : MvPolynomial σ ℝ) ≤ W ^ 1 :=
    cn_C (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hH.card_univ)
  have hc := SosPlusIdeal.pow_sub_powW hW hsw hcs hswn hCn m
  simp only [show max 1 (max (1 + 2) 1) + 4 = 7 by norm_num] at hc
  have hKc0 : 0 ≤ H.K * 32 ^ t := mul_nonneg hH.K0 (by positivity)
  have hKc : |H.K * 32 ^ t| ≤ W ^ (3 * t) := by
    rw [abs_of_nonneg hKc0, show 3 * t = 2 * t + t by ring, pow_add]
    exact mul_le_mul hK2 (by simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 32 ^ t)] using h32)
      (by positivity) (by positivity)
  have hq'n : coeffNorm1 (C (H.K * 32 ^ t) * H.D ^ t) ≤ W ^ (3 * t + 7 * t) :=
    cn_C_mul hKc (hH.Dpow_n t)
  have hq'd : (C (H.K * 32 ^ t) * H.D ^ t).totalDegree ≤ 2 * t :=
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hH.Dpow_d t)
  have hc' := SosPlusIdeal.mulSOSW hW (k₁ := 2 * t) (isSumSq_C_mul hKc0 (hH.Dpow_sos t)) hq'd
    hq'n hc
  -- (d) `K 32^t (W^m - n'^m) D^t ≥ 0`.
  have hnW : ((univ : Finset (Fin n')).card : ℝ) ^ m ≤ W ^ m :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa using hH.card_univ) m
  have hd0 : 0 ≤ H.K * 32 ^ t * (W ^ m - ((univ : Finset (Fin n')).card : ℝ) ^ m) :=
    mul_nonneg hKc0 (by linarith)
  have hdn : coeffNorm1 (C (H.K * 32 ^ t * (W ^ m - ((univ : Finset (Fin n')).card : ℝ) ^ m)) *
      H.D ^ t) ≤ W ^ (4 * t + 7 * t) := by
    refine cn_C_mul ?_ (hH.Dpow_n t)
    rw [abs_of_nonneg hd0, show 4 * t = 3 * t + t by ring, pow_add]
    refine mul_le_mul (by rwa [abs_of_nonneg hKc0] at hKc) ?_ (by linarith) (by positivity)
    have : (0 : ℝ) ≤ ((univ : Finset (Fin n')).card : ℝ) ^ m := by positivity
    calc W ^ m - ((univ : Finset (Fin n')).card : ℝ) ^ m ≤ W ^ m := by linarith
      _ ≤ W ^ t := pow_le_pow_of_two_le hW hmt
  have hd := SosPlusIdeal.of_isSumSqW A (k := 5 * t) (isSumSq_C_mul hd0 (hH.Dpow_sos t))
    ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; have := hH.Dpow_d t; omega))
    hdn
  -- Combining.
  have h1 := SosPlusIdeal.addW hW (e := 38 * t) hH.ax (hb'.mono (by omega) le_rfl) le_rfl
    (by omega)
  have h2 := SosPlusIdeal.addW hW (e := 38 * t + 1) h1 (hc'.mono (by omega) le_rfl) le_rfl
    (by omega)
  have h3 := SosPlusIdeal.addW hW (e := 38 * t + 2) h2 hd le_rfl (by omega)
  have hsum : C H.K * (∑ i, X (wv i)) ^ m * H.B - (∑ i, X (wv i) * H.x i ^ (2 * s)) ^ m +
      C H.K * ((C ((32 : ℝ) ^ t) * H.D ^ t - H.B) * (∑ i, X (wv i)) ^ m) +
      C (H.K * 32 ^ t) * H.D ^ t * (C ((univ : Finset (Fin n')).card : ℝ) ^ m -
        (∑ i, X (wv i)) ^ m) +
      C (H.K * 32 ^ t * (W ^ m - ((univ : Finset (Fin n')).card : ℝ) ^ m)) * H.D ^ t =
      C (H.K * 32 ^ t * W ^ m) * H.D ^ t - H.Mw s ^ m := by
    simp only [Mw, map_mul, map_sub, map_pow]
    ring
  rw [hsum] at h3
  have hchn : coeffNorm1 (C (H.K * 32 ^ t * W ^ m) * H.D ^ t - H.Mw s ^ m) ≤ W ^ (19 * t + 1) := by
    have hc1 : |H.K * 32 ^ t * W ^ m| ≤ W ^ (4 * t) := by
      rw [abs_of_nonneg (mul_nonneg hKc0 (by positivity)), show 4 * t = 3 * t + t by ring,
        pow_add]
      exact mul_le_mul (by rwa [abs_of_nonneg hKc0] at hKc) (pow_le_pow_of_two_le hW hmt)
        (by positivity) (by positivity)
    have hMm := cn_pow hH.Mwn m
    refine cn_sub hW (e := 19 * t) (cn_C_mul hc1 (hH.Dpow_n t)) hMm (by omega) ?_
    rw [← hsm]; nlinarith
  have hP := hH.P_pow ((2 * s - 1) * m)
  have hPm : (2 * s - 1) * m ≤ 2 * t := by
    rw [← hsm, ← mul_assoc]; exact Nat.mul_le_mul_right m (by omega)
  have h := SosPlusIdeal.mulW hW (e := 38 * t + 3) hP h3 hchn le_rfl (by omega)
  refine (h.monoW hW (by omega) (by omega)).congr ?_
  rw [Z₁, mul_pow, ← pow_mul]
  ring

/-- `Z₂^m ≤ W^m (8s)^t P^(2t-m) D^t`, from `S ≤ W`. -/
theorem step_Z2 :
    SosPlusIdeal A (9 * t) (W ^ (13 * t))
      (C (W ^ m * (8 * s) ^ t) * H.P ^ ((2 * s - 1) * m) * H.D ^ t - H.Z₂ s ^ m) := by
  have hs1 := hH.one_le_s
  have hm := hH.m_pos
  have hmt := hH.m_le_t
  have hsm : s * m = t := hH.ht.symm
  have hW := hH.hW
  have hSm : H.S ^ m ≤ W ^ m := pow_le_pow_left₀ hH.S0 hH.SW m
  have hS0 : 0 ≤ H.S ^ m := pow_nonneg hH.S0 m
  have hc0 : 0 ≤ (W ^ m - H.S ^ m) * (8 * s) ^ t := mul_nonneg (by linarith) (by positivity)
  have hcn : |(W ^ m - H.S ^ m) * (8 * (s : ℝ)) ^ t| ≤ W ^ (2 * t) := by
    rw [abs_of_nonneg hc0, two_mul, pow_add]
    refine mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) hH.eight_s_le t) (by positivity)
      (by positivity)
    calc W ^ m - H.S ^ m ≤ W ^ m := by linarith
      _ ≤ W ^ t := pow_le_pow_of_two_le hW hmt
  have hq := isSumSq_C_mul hc0 (hH.Dpow_sos t)
  have hqd : (C ((W ^ m - H.S ^ m) * (8 * (s : ℝ)) ^ t) * H.D ^ t).totalDegree ≤ 2 * t :=
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hH.Dpow_d t)
  have hPm : (2 * s - 1) * m ≤ 2 * t := by
    rw [← hsm, ← mul_assoc]; exact Nat.mul_le_mul_right m (by omega)
  have h := SosPlusIdeal.mulSOSW hW (k₁ := 2 * t) hq hqd (cn_C_mul hcn (hH.Dpow_n t))
    (hH.P_pow ((2 * s - 1) * m))
  have e1 : (H.S * (8 * (s : ℝ)) ^ s) ^ m = H.S ^ m * (8 * (s : ℝ)) ^ t := by
    rw [mul_pow, ← pow_mul, hsm]
  have hZ : H.Z₂ s ^ m = C (H.S ^ m * (8 * (s : ℝ)) ^ t) * H.P ^ ((2 * s - 1) * m) * H.D ^ t := by
    conv_lhs => rw [Z₂, mul_pow, mul_pow, ← C_pow, e1, ← pow_mul, ← pow_mul, hsm]
    ring
  refine (h.monoW hW (by omega) (by omega)).congr ?_
  rw [hZ]
  simp only [map_mul, map_sub]
  ring

end Good

/-- The constants: `2^(2t-1) (K 32^t + (8s)^t) ≤ (2^16 s)^t` for `K ≤ (256 s)^t`. -/
theorem const_check {K : ℝ} {s t : ℕ} (ht : 1 ≤ t) (hK : K ≤ (256 * s) ^ t) :
    (2 : ℝ) ^ (2 * t - 1) * (K * 32 ^ t + (8 * s) ^ t) ≤ (2 ^ 16 * s) ^ t := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have h1 : K * 32 ^ t ≤ (8192 * s) ^ t := by
    calc K * 32 ^ t ≤ (256 * s) ^ t * 32 ^ t := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (8192 * s) ^ t := by rw [← mul_pow]; ring_nf
  have h2 : (8 * (s : ℝ)) ^ t ≤ (8192 * s) ^ t :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) t
  have h3 : (2 : ℝ) ^ (2 * t - 1) * 2 = 4 ^ t := by
    rw [← pow_succ, show 2 * t - 1 + 1 = 2 * t by omega, pow_mul]; norm_num
  calc (2 : ℝ) ^ (2 * t - 1) * (K * 32 ^ t + (8 * s) ^ t)
      ≤ 2 ^ (2 * t - 1) * (2 * (8192 * s) ^ t) := by gcongr; linarith
    _ = 4 ^ t * (8192 * s) ^ t := by rw [← h3]; ring
    _ = (32768 * s) ^ t := by rw [← mul_pow]; ring_nf
    _ ≤ (2 ^ 16 * s) ^ t := pow_le_pow_left₀ (by positivity) (by nlinarith) t

namespace Good

variable (hH : H.Good W s m t)
include hH

/-- **(H1) The abstract identifiability inequality**:
`P^(2t) D^(2t) ≤ W^m (2^16 s)^t P^(2t-m) D^t`, in degree `9t` with norm `W^(48t)`. -/
theorem H1 :
    SosPlusIdeal A (9 * t) (W ^ (48 * t))
      (C (W ^ m * (2 ^ 16 * s) ^ t) * H.P ^ ((2 * s - 1) * m) * H.D ^ t -
        H.P ^ (2 * t) * H.D ^ (2 * t)) := by
  have hs1 := hH.one_le_s
  have hm := hH.m_pos
  have ht8 := hH.t_pos
  have hmt := hH.m_le_t
  have hsm : s * m = t := hH.ht.symm
  have hW := hH.hW
  set cf : ℝ := W ^ m * (2 ^ 16 * s) ^ t -
    2 ^ (2 * t - 1) * (H.K * 32 ^ t * W ^ m + W ^ m * (8 * s) ^ t) with hcf
  have hcf0 : 0 ≤ cf := by
    have := const_check (by omega : 1 ≤ t) hH.K_le
    have hWm : 0 ≤ W ^ m := pow_nonneg hH.W_pos.le m
    have : 2 ^ (2 * t - 1) * (H.K * 32 ^ t * W ^ m + W ^ m * (8 * s) ^ t) =
        W ^ m * (2 ^ (2 * t - 1) * (H.K * 32 ^ t + (8 * s) ^ t)) := by ring
    rw [hcf, this, ← mul_sub]
    exact mul_nonneg hWm (by linarith)
  have hcfn : |cf| ≤ W ^ (2 * t) := by
    rw [abs_of_nonneg hcf0, two_mul, pow_add]
    have h1 : cf ≤ W ^ m * (2 ^ 16 * s) ^ t := by
      have : 0 ≤ 2 ^ (2 * t - 1) * (H.K * 32 ^ t * W ^ m + W ^ m * (8 * s) ^ t) := by
        have := hH.K0; positivity
      linarith
    refine h1.trans (mul_le_mul (pow_le_pow_of_two_le hW hmt)
      (pow_le_pow_left₀ (by positivity) hH.hsW t) (by positivity) (by positivity))
  have hPm : (2 * s - 1) * m ≤ 2 * t := by
    rw [← hsm, ← mul_assoc]; exact Nat.mul_le_mul_right m (by omega)
  have hlast := SosPlusIdeal.mulSOSW hW (k₁ := 2 * t) (isSumSq_C_mul hcf0 (hH.Dpow_sos t))
    ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hH.Dpow_d t))
    (cn_C_mul hcfn (hH.Dpow_n t)) (hH.P_pow ((2 * s - 1) * m))
  have hGH := SosPlusIdeal.addW hW (e := 43 * t) hH.step_Z1 hH.step_Z2 le_rfl (by omega)
  have hGH' := SosPlusIdeal.smulW hW (c := (2 : ℝ) ^ (2 * t - 1)) (e := 2 * t - 1)
    (by positivity) (hH.two_pow_le _) hGH
  have h1 := SosPlusIdeal.addW hW (e := 47 * t) (hH.step_pow.mono (k' := 9 * t) (by omega) le_rfl)
    (hH.step_mean.mono (k' := 9 * t) (by omega) le_rfl) le_rfl (by omega)
  have h2 := SosPlusIdeal.addW hW (e := 47 * t + 1) h1 hGH' le_rfl (by omega)
  have h3 := SosPlusIdeal.addW hW (e := 47 * t + 2) h2 (hlast.mono (k' := 9 * t) (by omega)
    le_rfl) le_rfl (by omega)
  refine (h3.monoW hW le_rfl (by omega)).congr ?_
  simp only [hcf, map_mul, map_sub, map_add, map_pow]
  ring

end Good

end H1Data

end H1

end BS23.SmallRadius.Core
