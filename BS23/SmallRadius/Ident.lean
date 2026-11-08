module

public import BS23.SmallRadius.IdentCross
public import BS23.SmallRadius.MomentAxiom
public import BS23.SmallRadius.MomentSoS

/-!
# Identifiability in the small-radius analysis

One round of the small-radius algorithm for [BS23, Theorem 1.3] solves the program
`BS23.SmallRadius.problem` on the remaining points `z_{idx i}`, `i < n'`, of a good frame
(`BS23.SmallRadius.SRFrame.Good`). Here we show that a pseudo-expectation satisfying it puts little
mass on pairs of points from different clusters. The round is `BS23.SmallRadius.IdCtx`: the frame
`F`, the remaining points `idx : Fin n' → Fin n`, the degrees `s, t` (`m = t / s`) and the budget
`Lb`; `IdCtx.sys K Bd` is the system of the program over `ℝ`.

In the program variables (`BS23.SmallRadius.IdCtx`): `wᵢ` the weights, `μ` the mean,
`β = G⁻¹ μ` (`IdCtx.βP`), and for a cluster `j`, `b_j = β - m_j` (`IdCtx.bP`),
`D_j = ‖b_j‖²` (`IdCtx.DP`), `v_j = G⁻ᵀ b_j` (`IdCtx.vP`), the remaining points
`T_j = {i : ℓ(idx i) = j}` (`IdCtx.Tset`) and `p_j = ∑_{i ∈ T_j} wᵢ` (`IdCtx.pP`). Since
`z = G ζ` and `μ = G β`: `⟨z_{idx i} - μ, v_j⟩ = ⟨ζ_{idx i} - β, b_j⟩` (`IdCtx.xP_eq`), so that
`⟨ζ_{idx i} - m_j, b_j⟩ - ⟨z_{idx i} - μ, v_j⟩ = D_j` (`IdCtx.yP_sub_xP`), and
`B̃(v_j) = B_std(b_j)` (`IdCtx.BP_eq_aeval`).

## Main statements

* `BS23.SmallRadius.IdCtx.H1` (**(H1)**): for every cluster `j`, modulo the equality constraints
  (`SoS.SosPlusIdeal`), in degree `9t` with norm `n^(48t)`,
  `p_j^(2t) D_j^(2t) ≤ n^m (2^16 s)^t p_j^(2t-m) D_j^t`. It is the abstract inequality
  `BS23.SmallRadius.Core.H1Data.Good.H1` for the data `IdCtx.h1Data` (`IdCtx.h1Data_good`): the
  moment axiom at `φ = v_j` (`BS23.SmallRadius.moment_axiom_bOf`, with the coefficients of `B̃`
  bounded by `BS23.SmallRadius.abs_bOf_le`), the scale bound (E3) at `b_j` (`IdCtx.Bsos`) and the
  cluster bound (E2) at `b_j` for the remaining points of `j` (`IdCtx.E2`).
* `BS23.SmallRadius.IdCtx.cross_le_dist`, `BS23.SmallRadius.IdCtx.cross_le`: for a
  pseudo-expectation `Ẽ` of degree `ℓ ≥ 22t` (the program has `ℓ = 64t`) that satisfies the
  system up to `η` with soundness error `sosErr (sys K Bd) η (n^(50t)) ≤ 1/4`, and `j ≠ l`,
  `Ẽ[p_j p_l] ≤ 2 n² (2^18 s / ‖m_j - m_l‖²)^s + 1 ≤ 2 n² ρ^s + 1`, `ρ = 2^18 s / (Csep ln (1/w))`
  (`BS23.SmallRadius.Core.cross_abstract`, with the triangle identity
  `D_j + D_l - ‖m_j - m_l‖²/2 = 2 ‖β - (m_j + m_l)/2‖²`, `IdCtx.DP_add_DP_sub`).
* `BS23.SmallRadius.IdCtx.cross_sum_le`: `∑_{j ≠ l} Ẽ[p_j p_l] ≤ k² (2 n² ρ^s + 1)`, and
  `BS23.SmallRadius.IdCtx.cross_pairs_le`, the same bound for the sum of `Ẽ[wᵢ wᵢ']` over the pairs
  of remaining points in different clusters (`IdCtx.sum_cross_eq`).
* `BS23.SmallRadius.SRParams.pow_fifty_le`: the norm budget `n^(50t)` is at most `2^n`.

The hypotheses besides the good frame: `idx` is injective, nothing is cut by the budget
(`BS23.SmallRadius.Fits d s t m Lb`), `0 ≤ K ≤ (256 s)^t`, and `Csep > 0` for `cross_le`.
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial Finset SoS Matrix
open BS23.Separating (lin lin_add)

/-! ### Two generic facts -/

/-- `∑ₐ (G u)ₐ (G⁻ᵀ w)ₐ = ∑_c u_c w_c` for polynomial vectors `u`, `w`, when `G⁻¹ G = 1`. -/
theorem sum_mulVec_mul_invT {σ : Type*} {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (hG : G⁻¹ * G = 1) (u w : Fin d → MvPolynomial σ ℝ) :
    ∑ a, (∑ c, C (G a c) * u c) * (∑ e, C (G⁻¹ e a) * w e) = ∑ c, u c * w c := by
  have h1 : ∀ c e, ∑ a, G⁻¹ e a * G a c = if e = c then 1 else 0 := fun c e ↦ by
    have := congrFun (congrFun hG e) c
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
  have e1 : ∀ a, (∑ c, C (G a c) * u c) * (∑ e, C (G⁻¹ e a) * w e) =
      ∑ c, ∑ e, C (G⁻¹ e a * G a c) * (u c * w e) := fun a ↦ by
    rw [Finset.sum_mul_sum]
    refine sum_congr rfl fun c _ ↦ sum_congr rfl fun e _ ↦ ?_
    rw [C_mul]
    ring
  calc ∑ a, (∑ c, C (G a c) * u c) * (∑ e, C (G⁻¹ e a) * w e)
      = ∑ a, ∑ c, ∑ e, C (G⁻¹ e a * G a c) * (u c * w e) := sum_congr rfl fun a _ ↦ e1 a
    _ = ∑ c, ∑ e, ∑ a, C (G⁻¹ e a * G a c) * (u c * w e) := by
        rw [Finset.sum_comm]; exact sum_congr rfl fun c _ ↦ Finset.sum_comm
    _ = ∑ c, ∑ e, C (∑ a, G⁻¹ e a * G a c) * (u c * w e) := by
        simp only [map_sum, Finset.sum_mul]
    _ = ∑ c, u c * w c := by
        refine sum_congr rfl fun c _ ↦ ?_
        simp only [h1]
        rw [Finset.sum_eq_single c (fun e _ he ↦ by simp [he]) (by simp)]
        simp

/-- **The coefficients of `B̃` are bounded**: `|b_γ| ≤ (d B)^(2t)` when every `|Y_{ja}| ≤ B`. -/
theorem abs_bOf_le {nY d : ℕ} (Y : Fin nY → Fin d → ℚ) {s t m Lb : ℕ} (hfit : Fits d s t m Lb)
    {B : ℝ} (hY : ∀ j a, |(Y j a : ℝ)| ≤ B) (ht : 1 ≤ t) {γ : List ℕ}
    (hγ : γ ∈ gams d t Lb) : |(bOf Y t Lb γ : ℝ)| ≤ (d * B) ^ (2 * t) := by
  classical
  have hL := good_lay (n := 0) hfit
  have h := sum_bOf_mul_powE_of_fits (S := MvPolynomial (Fin d) ℝ) Y hfit
    (X : Fin d → MvPolynomial (Fin d) ℝ)
  simp only [MvPolynomial.algebraMap_apply] at h
  rw [← List.sum_toFinset _ hL.nodupG] at h
  have hc := congrArg (fun p : MvPolynomial (Fin d) ℝ ↦ p.coeff (Mono.toFinsupp d γ)) h
  rw [coeff_sum] at hc
  have hlen : ∀ e ∈ gams d t Lb, e.length = d := fun e he ↦ ((hL.memG e).1 he).1
  rw [Finset.sum_eq_single γ (fun e he hne ↦ by
      have hne' : Mono.toFinsupp d e ≠ Mono.toFinsupp d γ := fun h' ↦ hne
        (Mono.toFinsupp_inj (hlen e (List.mem_toFinset.1 he)) (hlen γ hγ) h')
      simp [RawAlg.powE_X_eq_monomial, coeff_C_mul, coeff_monomial, hne'])
    (fun h' ↦ absurd (List.mem_toFinset.2 hγ) h')] at hc
  simp only [RawAlg.powE_X_eq_monomial, coeff_C_mul, coeff_monomial, ite_true, mul_one] at hc
  simp only [eq_ratCast] at hc
  rw [hc, abs_mul]
  refine (mul_le_mul_of_nonneg_left (abs_coeff_le_coeffNorm1 _ _) (abs_nonneg _)).trans ?_
  have hlin : ∀ j, coeffNorm1 (∑ a, C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ)) ≤ d * B :=
    fun j ↦ by
      refine (coeffNorm1_sum_le _ _).trans ?_
      calc ∑ a, coeffNorm1 (C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ))
          = ∑ a, |(Y j a : ℝ)| := by simp [coeffNorm1_C_mul, coeffNorm1_X]
        _ ≤ ∑ _a : Fin d, B := sum_le_sum fun a _ ↦ hY j a
        _ = d * B := by simp
  have hlin0 : ∀ j, 0 ≤ coeffNorm1 (∑ a, C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ)) :=
    fun j ↦ coeffNorm1_nonneg _
  have hsum : coeffNorm1 (∑ j, (∑ a, C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ)) ^ (2 * t)) ≤
      nY * (d * B) ^ (2 * t) := by
    refine (coeffNorm1_sum_le _ _).trans ?_
    calc ∑ j, coeffNorm1 ((∑ a, C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ)) ^ (2 * t))
        ≤ ∑ _j : Fin nY, (d * B) ^ (2 * t) := sum_le_sum fun j _ ↦ (coeffNorm1_pow_le _ _).trans
          (pow_le_pow_left₀ (hlin0 j) (hlin j) _)
      _ = nY * (d * B) ^ (2 * t) := by simp
  have hpow : 0 ≤ (d * B) ^ (2 * t) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  have hc : |(((((nY : ℚ) * t ^ t)⁻¹ : ℚ)) : ℝ)| * nY ≤ 1 := by
    push_cast
    rcases Nat.eq_zero_or_pos nY with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (t : ℝ) ^ t := one_le_pow₀ (by exact_mod_cast ht)
      have h2 : (0 : ℝ) < nY := by exact_mod_cast h0
      rw [abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity), mul_one]
      nlinarith
  calc |(((((nY : ℚ) * t ^ t)⁻¹ : ℚ)) : ℝ)| *
        coeffNorm1 (∑ j, (∑ a, C (Y j a : ℝ) * (X a : MvPolynomial (Fin d) ℝ)) ^ (2 * t))
      ≤ |(((((nY : ℚ) * t ^ t)⁻¹ : ℚ)) : ℝ)| * (nY * (d * B) ^ (2 * t)) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = (|(((((nY : ℚ) * t ^ t)⁻¹ : ℚ)) : ℝ)| * nY) * (d * B) ^ (2 * t) := by ring
    _ ≤ 1 * (d * B) ^ (2 * t) := mul_le_mul_of_nonneg_right hc hpow
    _ = (d * B) ^ (2 * t) := one_mul _

/-! ### The norm budget -/

/-- `14 L² ≤ 2^L` for `L ≥ 20`. -/
theorem fourteen_sq_le_two_pow {L : ℕ} (hL : 20 ≤ L) : 14 * L ^ 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h : 14 * (L + 1) ^ 2 ≤ 2 * (14 * L ^ 2) := by nlinarith
    calc 14 * (L + 1) ^ 2 ≤ 2 * (14 * L ^ 2) := h
      _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (L + 1) := by rw [pow_succ]; ring

/-- **The norm budget is at most `2^n`**: `n^(50t) ≤ 2^n` when `n ≥ 2^20` and `2^(4t) ≤ n`. -/
theorem pow_fifty_le_two_pow {n t : ℕ} (hn : 2 ^ 20 ≤ n) (ht : 2 ^ (4 * t) ≤ n) :
    n ^ (50 * t) ≤ 2 ^ n := by
  have hn0 : n ≠ 0 := by positivity
  set L := Nat.log 2 n with hLdef
  have hL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hL' : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h4t : 4 * t < L + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (ht.trans_lt hL')
  have h20 : 20 < L + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hn.trans_lt hL')
  have h1 : n ^ (50 * t) ≤ 2 ^ ((L + 1) * (50 * t)) := by
    rw [pow_mul 2]; exact Nat.pow_le_pow_left hL'.le _
  have h2 : (L + 1) * (50 * t) ≤ 14 * L ^ 2 := by
    have : 50 * t ≤ 13 * L := by omega
    calc (L + 1) * (50 * t) ≤ (L + 1) * (13 * L) := Nat.mul_le_mul_left _ this
      _ ≤ 14 * L ^ 2 := by nlinarith
  calc n ^ (50 * t) ≤ 2 ^ ((L + 1) * (50 * t)) := h1
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num)
        (h2.trans ((fourteen_sq_le_two_pow (by omega)).trans hL))

/-- `n^(50t) ≤ 2^n` under the parameter facts. -/
theorem SRParams.pow_fifty_le {k d n : ℕ} {w R : ℝ} {s t : ℕ} (h : SRParams k d n w R s t) :
    (n : ℝ) ^ (50 * t) ≤ 2 ^ n := by
  exact_mod_cast pow_fifty_le_two_pow h.n_ge h.tpow_le

/-! ### The polynomials of a round -/

/-- The data of one round of the analysis: a frame `F`, the `n'` remaining points `idx i`, the
degrees `s`, `t` and the budget `Lb` of the program. -/
structure IdCtx (n d k : ℕ) where
  /-- The standard frame. -/
  F : SRFrame n d k
  /-- The number of remaining points. -/
  n' : ℕ
  /-- The remaining points, as indices into the sample. -/
  idx : Fin n' → Fin n
  /-- The identification degree. -/
  s : ℕ
  /-- The scale degree. -/
  t : ℕ
  /-- The budget. -/
  Lb : ℕ

namespace IdCtx

variable {n d k : ℕ} (c : IdCtx n d k)

/-- The layout of the program. -/
abbrev L : Lay := lay c.n' d c.s c.t c.Lb

/-- The program variables. -/
abbrev V : Type := Fin c.L.N

/-- The system of the program, over `ℝ`: on the points `z_{idx i}`, with `B̃` from all points. -/
noncomputable abbrev sys (K Bd : ℚ) : System c.V ℝ :=
  realSystem (fun i ↦ c.F.z (c.idx i)) (bOf c.F.z c.t c.Lb) c.s c.t (c.t / c.s) K Bd c.Lb

/-- `μₐ`. -/
noncomputable def μX (a : Fin d) : MvPolynomial c.V ℝ := X (c.L.mv a)

/-- `β = G⁻¹ μ`, the mean in the standard frame. -/
noncomputable def βP (a : Fin d) : MvPolynomial c.V ℝ := ∑ e, C (c.F.G⁻¹ a e) * c.μX e

/-- `b_j = β - m_j`. -/
noncomputable def bP (j : Fin k) (a : Fin d) : MvPolynomial c.V ℝ := c.βP a - C (c.F.m j a)

/-- `D_j = ‖β - m_j‖²`. -/
noncomputable def DP (j : Fin k) : MvPolynomial c.V ℝ := ∑ a, c.bP j a ^ 2

/-- `v_j = G⁻ᵀ b_j`, the direction of the moment axiom. -/
noncomputable def vP (j : Fin k) (a : Fin d) : MvPolynomial c.V ℝ :=
  ∑ e, C (c.F.G⁻¹ e a) * c.bP j e

/-- `T_j`: the remaining points of cluster `j`. -/
def Tset (j : Fin k) : Finset (Fin c.n') := univ.filter fun i ↦ c.F.ℓ (c.idx i) = j

/-- `p_j = ∑_{i ∈ T_j} wᵢ`. -/
noncomputable def pP (j : Fin k) : MvPolynomial c.V ℝ := ∑ i ∈ c.Tset j, X (c.L.wv i)

/-- `xᵢ = ⟨z_{idx i} - μ, v_j⟩`, as in the moment axiom. -/
noncomputable def xP (j : Fin k) (i : Fin c.n') : MvPolynomial c.V ℝ :=
  ∑ a, (C (c.F.z (c.idx i) a : ℝ) - X (c.L.mv a)) * c.vP j a

/-- `yᵢ = ⟨ζ_{idx i} - m_j, b_j⟩`. -/
noncomputable def yP (j : Fin k) (i : Fin c.n') : MvPolynomial c.V ℝ :=
  ∑ a, C (c.F.ζ (c.idx i) a - c.F.m j a) * c.bP j a

/-- `B̃(v_j) = (n t^t)⁻¹ ∑_{j'} ⟨z_{j'}, v_j⟩^(2t)`. -/
noncomputable def BP (j : Fin k) : MvPolynomial c.V ℝ :=
  C (((n : ℝ) * (c.t : ℝ) ^ c.t)⁻¹) * ∑ j' : Fin n, (∑ a, C (c.F.z j' a : ℝ) * c.vP j a) ^ (2 * c.t)

/-! #### Identities -/

section Identities

variable {w R Csep : ℝ} (hF : c.F.Good w R Csep c.s c.t)
include hF

theorem C_z_eq (j' : Fin n) (a : Fin d) :
    (C (c.F.z j' a : ℝ) : MvPolynomial c.V ℝ) = ∑ e, C (c.F.G a e) * C (c.F.ζ j' e) := by
  have h := congrFun (hF.z_eq j') a
  simp only [SRFrame.zR, mulVec, dotProduct] at h
  rw [h, map_sum]
  simp only [map_mul]

theorem μX_eq (a : Fin d) : c.μX a = ∑ e, C (c.F.G a e) * c.βP e := by
  have hG : c.F.G * c.F.G⁻¹ = 1 := mul_nonsing_inv _ hF.G_inv
  simp only [βP, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ f, ∑ e, C (c.F.G a e) * (C (c.F.G⁻¹ e f) * c.μX f) =
      C ((c.F.G * c.F.G⁻¹) a f) * c.μX f := fun f ↦ by
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [C_mul]; ring
  simp only [this, hG, Matrix.one_apply]
  rw [Finset.sum_eq_single a (fun f _ hf ↦ by simp [Ne.symm hf]) (by simp)]
  simp

/-- `⟨z_{j'}, v_j⟩ = ⟨ζ_{j'}, b_j⟩`. -/
theorem zv_eq (j : Fin k) (j' : Fin n) :
    ∑ a, C (c.F.z j' a : ℝ) * c.vP j a = ∑ e, C (c.F.ζ j' e) * c.bP j e := by
  simp only [C_z_eq c hF, vP]
  exact sum_mulVec_mul_invT c.F.G (nonsing_inv_mul _ hF.G_inv) _ _

/-- `xᵢ = ⟨ζ_{idx i} - β, b_j⟩`. -/
theorem xP_eq (j : Fin k) (i : Fin c.n') :
    c.xP j i = ∑ e, (C (c.F.ζ (c.idx i) e) - c.βP e) * c.bP j e := by
  have h : ∀ a, (C (c.F.z (c.idx i) a : ℝ) - X (c.L.mv a) : MvPolynomial c.V ℝ) =
      ∑ e, C (c.F.G a e) * (C (c.F.ζ (c.idx i) e) - c.βP e) := fun a ↦ by
    rw [C_z_eq c hF, show (X (c.L.mv a) : MvPolynomial c.V ℝ) = c.μX a from rfl, μX_eq c hF,
      ← sum_sub_distrib]
    exact sum_congr rfl fun e _ ↦ by ring
  simp only [xP, h, vP]
  exact sum_mulVec_mul_invT c.F.G (nonsing_inv_mul _ hF.G_inv) _ _

/-- `yᵢ - xᵢ = D_j`. -/
theorem yP_sub_xP (j : Fin k) (i : Fin c.n') : c.yP j i - c.xP j i = c.DP j := by
  rw [xP_eq c hF, yP, DP, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [bP, map_sub]
  ring

end Identities

/-- `aeval b_j (lin u) = ∑ₐ uₐ (b_j)ₐ`. -/
theorem aeval_lin (j : Fin k) (u : Fin d → ℝ) :
    aeval (c.bP j) (lin u) = ∑ a, C (u a) * c.bP j a := by
  simp [lin, map_sum, map_mul, aeval_X, MvPolynomial.algebraMap_eq]

theorem aeval_nsq (j : Fin k) : aeval (c.bP j) (nsq d) = c.DP j := by
  simp [nsq, DP, map_sum, map_pow, aeval_X]

theorem yP_eq_aeval (j : Fin k) (i : Fin c.n') :
    c.yP j i = aeval (c.bP j) (lin (c.F.ζ (c.idx i) - c.F.m j)) := by
  rw [aeval_lin, yP]
  rfl

theorem BP_eq_aeval {w R Csep : ℝ} (hF : c.F.Good w R Csep c.s c.t) (j : Fin k) :
    c.BP j = aeval (c.bP j) (c.F.Bstd c.t) := by
  rw [SRFrame.Bstd, map_mul, aeval_C, MvPolynomial.algebraMap_eq, map_sum, BP, one_div]
  congr 1
  refine sum_congr rfl fun j' _ ↦ ?_
  rw [map_pow, aeval_lin, zv_eq c hF]

/-! #### Norms and degrees, in powers of `n` -/

section Norms

open Core

variable {w R Csep : ℝ} (hF : c.F.Good w R Csep c.s c.t)
include hF

theorem two_le_n : (2 : ℝ) ≤ n := by
  have : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hF.params.n_ge
  push_cast at this; linarith

theorem card_d : ((univ : Finset (Fin d)).card : ℝ) ≤ (n : ℝ) ^ 1 := by
  rw [pow_one, Finset.card_univ, Fintype.card_fin]
  exact_mod_cast hF.params.d_lt_n.le

omit hF in
theorem sq_le_dotProduct (v : Fin d → ℝ) (a : Fin d) : v a ^ 2 ≤ v ⬝ᵥ v := by
  rw [dotProduct, sq]
  exact single_le_sum (f := fun b ↦ v b * v b) (fun b _ ↦ mul_self_nonneg _) (mem_univ a)

omit hF in
theorem abs_le_of_sq_le' {x : ℝ} {N : ℝ} (hN : 1 ≤ N) (h : x ^ 2 ≤ N) : |x| ≤ N :=
  abs_le_of_sq_le_sq (h.trans (by nlinarith)) (by linarith)

theorem abs_Ginv (a e : Fin d) : |c.F.G⁻¹ a e| ≤ (n : ℝ) ^ 1 := by
  have h := hF.Ginv_mulVec_le (Pi.single e 1)
  have he : c.F.G⁻¹ *ᵥ Pi.single e 1 = fun a ↦ c.F.G⁻¹ a e := by
    ext a; simp
  rw [he] at h
  have h1 := sq_le_dotProduct (fun a ↦ c.F.G⁻¹ a e) a
  have h2 : Pi.single e (1 : ℝ) ⬝ᵥ Pi.single e 1 = 1 := by simp
  rw [h2, mul_one] at h
  have h3 := hF.three_R_sq_le_n
  rw [pow_one]
  exact abs_le_of_sq_le' (by linarith [two_le_n c hF]) (by linarith)

theorem abs_m (j : Fin k) (a : Fin d) : |c.F.m j a| ≤ (n : ℝ) ^ 1 := by
  have h1 := sq_le_dotProduct (c.F.m j) a
  have h2 := hF.radius j
  have h3 := hF.three_R_sq_le_n
  rw [pow_one]
  exact abs_le_of_sq_le' (by linarith [two_le_n c hF]) (by nlinarith)

theorem abs_ζ (j' : Fin n) (a : Fin d) : |c.F.ζ j' a| ≤ (n : ℝ) ^ 2 := by
  have h1 := sq_le_dotProduct (c.F.ζ j') a
  have h2 := hF.ζ_sq_le j'
  have hn := two_le_n c hF
  have hR : R ^ 2 ≤ n := by have := hF.three_R_sq_le_n; nlinarith [sq_nonneg R]
  have hd : (d : ℝ) ≤ n := by exact_mod_cast hF.params.d_lt_n.le
  have h4 : 4 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h5 : 2 * (n : ℝ) * d ≤ 2 * n * n := by nlinarith
  refine abs_le_of_sq_le_sq (h1.trans (h2.trans ?_)) (by positivity)
  have hn8 : (8 : ℝ) ≤ n := by
    have : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hF.params.n_ge
    push_cast at this; linarith
  have h6 : (n : ℝ) ^ 2 * 9 ≤ ((n : ℝ) ^ 2) ^ 2 := by
    rw [sq ((n : ℝ) ^ 2)]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith

theorem abs_ζ_sub_m (j' : Fin n) (j : Fin k) (a : Fin d) :
    |c.F.ζ j' a - c.F.m j a| ≤ (n : ℝ) ^ 3 := by
  have h1 := abs_ζ c hF j' a
  have h2 := abs_m c hF j a
  have hn := two_le_n c hF
  calc |c.F.ζ j' a - c.F.m j a| ≤ |c.F.ζ j' a| + |c.F.m j a| := abs_sub _ _
    _ ≤ (n : ℝ) ^ 2 + (n : ℝ) ^ 1 := add_le_add h1 h2
    _ ≤ (n : ℝ) ^ 3 := by nlinarith

omit hF in
theorem μX_n (a : Fin d) : coeffNorm1 (c.μX a) ≤ (n : ℝ) ^ 0 := cn_X _

theorem βP_n (a : Fin d) : coeffNorm1 (c.βP a) ≤ (n : ℝ) ^ 2 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun e _ ↦ cn_C_mul (abs_Ginv c hF a e) (μX_n c e)

theorem bP_n (j : Fin k) (a : Fin d) : coeffNorm1 (c.bP j a) ≤ (n : ℝ) ^ 3 :=
  cn_sub (two_le_n c hF) (e := 2) (βP_n c hF a) (cn_C (abs_m c hF j a)) le_rfl (by norm_num)

theorem vP_n (j : Fin k) (a : Fin d) : coeffNorm1 (c.vP j a) ≤ (n : ℝ) ^ 5 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun e _ ↦ cn_C_mul (abs_Ginv c hF e a) (bP_n c hF j e)

theorem DP_n (j : Fin k) : coeffNorm1 (c.DP j) ≤ (n : ℝ) ^ 7 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun a _ ↦ cn_pow (bP_n c hF j a) 2

theorem xP_n (j : Fin k) (i : Fin c.n') : coeffNorm1 (c.xP j i) ≤ (n : ℝ) ^ 9 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun a _ ↦
    cn_mul (cn_sub (two_le_n c hF) (e := 2) (cn_C (hF.abs_z_le (c.idx i) a)) (cn_X _) le_rfl
      (by norm_num)) (vP_n c hF j a)

theorem yP_n (j : Fin k) (i : Fin c.n') : coeffNorm1 (c.yP j i) ≤ (n : ℝ) ^ 7 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun a _ ↦
    cn_C_mul (abs_ζ_sub_m c hF (c.idx i) j a) (bP_n c hF j a)

theorem zv_n (j : Fin k) (j' : Fin n) :
    coeffNorm1 (∑ a, C (c.F.z j' a : ℝ) * c.vP j a) ≤ (n : ℝ) ^ 8 :=
  cn_sum (two_le_n c hF) univ (card_d c hF) fun a _ ↦
    cn_C_mul (hF.abs_z_le j' a) (vP_n c hF j a)

theorem BP_n (j : Fin k) : coeffNorm1 (c.BP j) ≤ (n : ℝ) ^ (16 * c.t) := by
  have hn := two_le_n c hF
  have ht : (1 : ℝ) ≤ (c.t : ℝ) ^ c.t := one_le_pow₀ (by exact_mod_cast hF.params.t_pos)
  rw [BP, coeffNorm1_C_mul]
  have hs := coeffNorm1_sum_le_card_mul (univ : Finset (Fin n))
    (fun j' ↦ (∑ a, C (c.F.z j' a : ℝ) * c.vP j a) ^ (2 * c.t)) (b := (n : ℝ) ^ (16 * c.t))
    fun j' _ ↦ (cn_pow (zv_n c hF j j') (2 * c.t)).trans_eq (by ring_nf)
  rw [Finset.card_univ, Fintype.card_fin] at hs
  have hpos : 0 < (n : ℝ) * (c.t : ℝ) ^ c.t := by positivity
  rw [abs_of_pos (inv_pos.2 hpos)]
  calc ((n : ℝ) * (c.t : ℝ) ^ c.t)⁻¹ * coeffNorm1 (∑ j' : Fin n,
        (∑ a, C (c.F.z j' a : ℝ) * c.vP j a) ^ (2 * c.t))
      ≤ ((n : ℝ) * (c.t : ℝ) ^ c.t)⁻¹ * (n * (n : ℝ) ^ (16 * c.t)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (n : ℝ) ^ (16 * c.t) := by
        rw [inv_mul_le_iff₀ hpos]
        have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (16 * c.t) := by positivity
        have h1 : (n : ℝ) * 1 ≤ n * (c.t : ℝ) ^ c.t :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        have := mul_le_mul_of_nonneg_right h1 h0
        linarith

omit hF in
theorem βP_d (a : Fin d) : (c.βP a).totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun e _ ↦ (totalDegree_mul _ _).trans
    (by rw [totalDegree_C, μX, totalDegree_X])

omit hF in
theorem bP_d (j : Fin k) (a : Fin d) : (c.bP j a).totalDegree ≤ 1 :=
  (totalDegree_sub_C_le _ _).trans (βP_d c a)

omit hF in
theorem vP_d (j : Fin k) (a : Fin d) : (c.vP j a).totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun e _ ↦ (totalDegree_mul _ _).trans
    (by rw [totalDegree_C, zero_add]; exact bP_d c j e)

omit hF in
theorem DP_d (j : Fin k) : (c.DP j).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun a _ ↦ (totalDegree_pow _ _).trans
    (by have := bP_d c j a; omega)

omit hF in
theorem xP_d (j : Fin k) (i : Fin c.n') : (c.xP j i).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun a _ ↦ (totalDegree_mul _ _).trans (by
    have h1 : (C (c.F.z (c.idx i) a : ℝ) - X (c.L.mv a) : MvPolynomial c.V ℝ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) (by rw [totalDegree_X]))
    have := vP_d c j a
    omega)

omit hF in
theorem yP_d (j : Fin k) (i : Fin c.n') : (c.yP j i).totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun a _ ↦ (totalDegree_mul _ _).trans
    (by rw [totalDegree_C, zero_add]; exact bP_d c j a)

omit hF in
theorem BP_d (j : Fin k) : (c.BP j).totalDegree ≤ 2 * c.t :=
  (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    refine totalDegree_finsetSum_le fun j' _ ↦ (totalDegree_pow _ _).trans ?_
    have : (∑ a, C (c.F.z j' a : ℝ) * c.vP j a).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun a _ ↦ (totalDegree_mul _ _).trans
        (by rw [totalDegree_C, zero_add]; exact vP_d c j a)
    have := Nat.mul_le_mul_left (2 * c.t) this
    omega)

omit hF in
theorem isSumSq_DP (j : Fin k) : IsSumSq (c.DP j) :=
  IsSumSq.sum fun _ _ ↦ isSumSq_sq _

end Norms

/-! #### The data of the abstract inequality -/

section Good

open Core

variable {w R Csep : ℝ} (hF : c.F.Good w R Csep c.s c.t)

/-- The data of the abstract identifiability inequality for cluster `j`. -/
noncomputable def h1Data (K Bd : ℚ) (j : Fin k) : H1Data (c.sys K Bd) c.n' c.L.wv :=
  ⟨c.Tset j, c.xP j, c.yP j, c.DP j, c.BP j, (K : ℝ), ((cluster c.F.ℓ j).card : ℝ)⟩

include hF

omit hF in
theorem n'_le (hidx : Function.Injective c.idx) : (c.n' : ℝ) ≤ n := by
  have := Fintype.card_le_of_injective c.idx hidx
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

theorem two_pow_sixteen_s_le : 2 ^ 16 * (c.s : ℝ) ≤ n := by
  have ht8 := hF.params.eight_le_t
  have hst := hF.params.s_le_t
  have h1 : 2 ^ 16 * c.s ≤ 2 ^ (4 * c.t) := by
    calc 2 ^ 16 * c.s ≤ 2 ^ 16 * 2 ^ c.t :=
          Nat.mul_le_mul_left _ (hst.trans (Nat.lt_two_pow_self).le)
      _ = 2 ^ (16 + c.t) := by rw [pow_add]
      _ ≤ 2 ^ (4 * c.t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h1.trans hF.params.tpow_le

/-- The cluster bound (E2) for the remaining points of cluster `j`:
`∑_{i ∈ T_j} yᵢ^(2s) ≤ |S_j| (8s)^s D_j^s`. -/
theorem E2 (hidx : Function.Injective c.idx) (j : Fin k) :
    IsSumSq (C (((cluster c.F.ℓ j).card : ℝ) * (8 * c.s) ^ c.s) * c.DP j ^ c.s -
      ∑ i ∈ c.Tset j, c.yP j i ^ (2 * c.s)) := by
  classical
  have hTS : (c.Tset j).image c.idx ⊆ cluster c.F.ℓ j := fun j' hj' ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hj'
    simp only [Tset, mem_filter, mem_univ, true_and] at hi
    simp [cluster, hi]
  have h0 := hF.cluster_moment_sos j
  have hsub := isSumSq_sum_lin_pow_sub_of_subset hTS (fun j' ↦ c.F.g j' + c.F.e j') c.s
  have h1 := isSumSq_sub_trans hsub h0
  have hrw : ∑ j' ∈ (c.Tset j).image c.idx, lin (c.F.g j' + c.F.e j') ^ (2 * c.s) =
      ∑ j' ∈ (c.Tset j).image c.idx, lin (c.F.ζ j' - c.F.m j) ^ (2 * c.s) := by
    refine sum_congr rfl fun j' hj' ↦ ?_
    have hl : c.F.ℓ j' = j := by
      have := hTS hj'
      simpa [cluster] using this
    congr 2
    rw [SRFrame.ζ, hl]
    abel
  rw [hrw] at h1
  have h2 := isSumSq_aeval (c.bP j) h1
  rw [map_sub, map_mul, aeval_C, MvPolynomial.algebraMap_eq, map_pow, aeval_nsq, map_sum,
    sum_image (fun i _ i' _ h ↦ hidx h)] at h2
  convert h2 using 2
  refine sum_congr rfl fun i _ ↦ ?_
  rw [map_pow, yP_eq_aeval]

theorem Bsos (j : Fin k) : IsSumSq (C ((32 : ℝ) ^ c.t) * c.DP j ^ c.t - c.BP j) := by
  have h := isSumSq_aeval (c.bP j) hF.covEst_upper
  rwa [map_sub, map_mul, aeval_C, MvPolynomial.algebraMap_eq, map_pow (aeval (c.bP j)) (nsq d),
    aeval_nsq, ← BP_eq_aeval c hF] at h

/-- The moment axiom at `φ = v_j`, with its norm bounded by `n^(38t)`. -/
theorem ax (hfit : Fits d c.s c.t (c.t / c.s) c.Lb) {K : ℚ} (hK0 : 0 ≤ (K : ℝ))
    (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (Bd : ℚ) (hidx : Function.Injective c.idx) (j : Fin k) :
    SosPlusIdeal (c.sys K Bd) (5 * c.t) ((n : ℝ) ^ (38 * c.t))
      (C (K : ℝ) * (∑ i, X (c.L.wv i)) ^ (c.t / c.s) * c.BP j -
        (∑ i, X (c.L.wv i) * c.xP j i ^ (2 * c.s)) ^ (c.t / c.s)) := by
  have hn := two_le_n c hF
  have ht8 := hF.params.eight_le_t
  have hs1 : 1 ≤ c.s := hF.params.s_pos
  have hmt : c.t / c.s ≤ c.t := Nat.div_le_self _ _
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hW : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
  have hb : ∀ γ ∈ gams d c.t c.Lb, |(bOf c.F.z c.t c.Lb γ : ℝ)| ≤ (n : ℝ) ^ (6 * c.t) :=
    fun γ hγ ↦ by
      refine (abs_bOf_le c.F.z hfit (fun j' a ↦ hF.abs_z_le j' a) (by omega) hγ).trans ?_
      have hd : (d : ℝ) ≤ n := by exact_mod_cast hF.params.d_lt_n.le
      calc ((d : ℝ) * (n : ℝ) ^ 2) ^ (2 * c.t) ≤ ((n : ℝ) ^ 3) ^ (2 * c.t) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            calc (d : ℝ) * (n : ℝ) ^ 2 ≤ n * (n : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right hd (by positivity)
              _ = (n : ℝ) ^ 3 := by ring
        _ = (n : ℝ) ^ (6 * c.t) := by rw [← pow_mul]; ring_nf
  have h := moment_axiom_bOf (fun i ↦ c.F.z (c.idx i)) K Bd c.F.z hfit hs1 (k := 5 * c.t) le_rfl
    (φ := c.vP j) hW (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
    (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (6 * c.t)) (vP_d c j) (vP_n c hF j)
    (fun i a ↦ hF.abs_z_le (c.idx i) a) hb
  refine h.mono le_rfl ?_
  -- The norm.
  have hn' := n'_le c hidx
  have hd : (d : ℝ) + 1 ≤ n := by
    have := hF.params.d_lt_n; exact_mod_cast this
  have hK2 : |(K : ℝ)| ≤ (n : ℝ) ^ (2 * c.t) := by
    rw [abs_of_nonneg hK0]
    refine hK.trans ?_
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have := two_pow_sixteen_s_le c hF
    have : (0 : ℝ) ≤ c.s := by positivity
    nlinarith
  have hm2 : ((c.t / c.s : ℕ) : ℝ) + 2 ≤ n := by
    have h1 : c.t + 2 ≤ 2 ^ (4 * c.t) := by
      have := Nat.lt_two_pow_self (n := 4 * c.t)
      omega
    have h2 := h1.trans hF.params.tpow_le
    have : c.t / c.s + 2 ≤ n := by omega
    exact_mod_cast this
  have e1 : ((c.t / c.s : ℕ) : ℝ) + 2 ≤ (n : ℝ) ^ 1 := by rwa [pow_one]
  have e2 : 1 + |(K : ℝ)| * (n : ℝ) ^ (6 * c.t) ≤ (n : ℝ) ^ (8 * c.t + 1) := by
    have h1 : |(K : ℝ)| * (n : ℝ) ^ (6 * c.t) ≤ (n : ℝ) ^ (8 * c.t) := by
      calc |(K : ℝ)| * (n : ℝ) ^ (6 * c.t) ≤ (n : ℝ) ^ (2 * c.t) * (n : ℝ) ^ (6 * c.t) :=
            mul_le_mul_of_nonneg_right hK2 (by positivity)
        _ = (n : ℝ) ^ (8 * c.t) := by rw [← pow_add]; ring_nf
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ (8 * c.t) := one_le_pow₀ hn1
    rw [pow_succ]
    nlinarith
  have e3 : ((c.n' : ℝ) + 1) ^ (c.t / c.s) ≤ (n : ℝ) ^ (2 * c.t) := by
    calc ((c.n' : ℝ) + 1) ^ (c.t / c.s) ≤ ((n : ℝ) ^ 2) ^ (c.t / c.s) :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) _
      _ ≤ ((n : ℝ) ^ 2) ^ c.t := pow_le_pow_right₀ (by nlinarith) hmt
      _ = (n : ℝ) ^ (2 * c.t) := by rw [← pow_mul]
  have e4 : (((d : ℝ) + 1) * ((n : ℝ) ^ 2 + 1) * (n : ℝ) ^ 5) ^ (3 * c.t) ≤
      (n : ℝ) ^ (27 * c.t) := by
    calc (((d : ℝ) + 1) * ((n : ℝ) ^ 2 + 1) * (n : ℝ) ^ 5) ^ (3 * c.t)
        ≤ ((n : ℝ) ^ 9) ^ (3 * c.t) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have h1 : (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 3 := by nlinarith
          calc ((d : ℝ) + 1) * ((n : ℝ) ^ 2 + 1) * (n : ℝ) ^ 5 ≤ n * (n : ℝ) ^ 3 * (n : ℝ) ^ 5 := by
                gcongr
            _ = (n : ℝ) ^ 9 := by ring
      _ = (n : ℝ) ^ (27 * c.t) := by rw [← pow_mul]; ring_nf
  calc (((c.t / c.s : ℕ) : ℝ) + 2) * (1 + |(K : ℝ)| * (n : ℝ) ^ (6 * c.t)) *
        ((c.n' : ℝ) + 1) ^ (c.t / c.s) *
        (((d : ℝ) + 1) * ((n : ℝ) ^ 2 + 1) * (n : ℝ) ^ 5) ^ (3 * c.t)
      ≤ (n : ℝ) ^ 1 * (n : ℝ) ^ (8 * c.t + 1) * (n : ℝ) ^ (2 * c.t) * (n : ℝ) ^ (27 * c.t) := by
        gcongr
    _ = (n : ℝ) ^ (37 * c.t + 2) := by
        rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    _ ≤ (n : ℝ) ^ (38 * c.t) := pow_le_pow_right₀ hn1 (by omega)

/-- **The hypotheses of the abstract identifiability inequality** hold for every cluster. -/
theorem h1Data_good (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    {K : ℚ} (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (Bd : ℚ) (j : Fin k) :
    (c.h1Data K Bd j).Good (n : ℝ) c.s (c.t / c.s) c.t where
  hbool := fun i ↦ hasEq_bool i
  hW := two_le_n c hF
  hn' := n'_le c hidx
  s_pow := hF.params.s_pow
  m_pow := hF.params.m_pow
  ht := by rw [mul_comm]; exact hF.params.div_mul_s.symm
  hs8 := hF.params.eight_le_s
  hsW := two_pow_sixteen_s_le c hF
  xd := xP_d c j
  xn := xP_n c hF j
  yd := yP_d c j
  yn := yP_n c hF j
  Dd := DP_d c j
  Dn := DP_n c hF j
  Dsos := isSumSq_DP c j
  yx := fun i _ ↦ yP_sub_xP c hF j i
  K0 := hK0
  K_le := hK
  ax := ax c hF hfit hK0 hK Bd hidx j
  Bsos := Bsos c hF j
  Bd := BP_d c j
  Bn := BP_n c hF j
  S0 := Nat.cast_nonneg _
  SW := by
    change ((cluster c.F.ℓ j).card : ℝ) ≤ n
    have := card_le_univ (cluster c.F.ℓ j)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  E2 := E2 c hF hidx j

end Good

/-! ### (H1) and the cross moments -/

section Main

open Core

/-- The triangle identity
`D_j + D_l - ‖m_j - m_l‖²/2 = 2 ‖β - (m_j + m_l)/2‖²`. -/
theorem DP_add_DP_sub (j l : Fin k) :
    c.DP j + c.DP l - C (((c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l)) / 2) =
      ∑ a, C 2 * (c.βP a - C ((c.F.m j a + c.F.m l a) / 2)) ^ 2 := by
  rw [DP, DP, dotProduct, Finset.sum_div, map_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  set p : MvPolynomial c.V ℝ := C ((c.F.m j a + c.F.m l a) / 2)
  set q : MvPolynomial c.V ℝ := C ((c.F.m j a - c.F.m l a) / 2)
  have ha : (C (c.F.m j a) : MvPolynomial c.V ℝ) = p + q := by
    rw [← C_add]; congr 1; ring
  have hb : (C (c.F.m l a) : MvPolynomial c.V ℝ) = p - q := by
    rw [← C_sub]; congr 1; ring
  have hd : (C ((c.F.m j - c.F.m l) a * (c.F.m j - c.F.m l) a / 2) : MvPolynomial c.V ℝ) =
      C 2 * q ^ 2 := by
    rw [← C_pow, ← C_mul]; congr 1; simp only [Pi.sub_apply]; ring
  rw [bP, bP, ha, hb, hd, show (C 2 : MvPolynomial c.V ℝ) = 2 from map_ofNat C 2]
  ring

theorem isSumSq_triangle (j l : Fin k) :
    IsSumSq (c.DP j + c.DP l - C (((c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l)) / 2)) := by
  rw [DP_add_DP_sub]
  exact IsSumSq.sum fun a _ ↦ isSumSq_C_mul (by norm_num) (isSumSq_sq _)

variable {w R Csep : ℝ} (hF : c.F.Good w R Csep c.s c.t)
include hF

/-- **(H1) Identifiability in sum-of-squares form.** For every cluster `j`, modulo the equality
constraints of the program, in degree `9t` and with norm `n^(48t)`:

  `p_j^(2t) D_j^(2t) ≤ n^m (2^16 s)^t p_j^(2t-m) D_j^t`,

where `m = t / s`, `p_j = ∑_{i ∈ T_j} wᵢ` and `D_j = ‖G⁻¹ μ - m_j‖²`. -/
theorem H1 (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    {K : ℚ} (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (Bd : ℚ) (j : Fin k) :
    SosPlusIdeal (c.sys K Bd) (9 * c.t) ((n : ℝ) ^ (48 * c.t))
      (C ((n : ℝ) ^ (c.t / c.s) * (2 ^ 16 * c.s) ^ c.t) *
          c.pP j ^ ((2 * c.s - 1) * (c.t / c.s)) * c.DP j ^ c.t -
        c.pP j ^ (2 * c.t) * c.DP j ^ (2 * c.t)) :=
  (c.h1Data_good hF hidx hfit hK0 hK Bd j).H1

/-- **The cross moment of two clusters**, with their distance `Δ² = ‖m_j - m_l‖² > 0`: for a
pseudo-expectation `Ẽ` of degree `ℓ ≥ 22t` satisfying the program up to `η`, with soundness
error at most `1/4` at norm `n^(50t)`,

  `Ẽ[p_j p_l] ≤ 2 n² (2^18 s / Δ²)^s + 1`. -/
theorem cross_le_dist {ℓ : ℕ} (E : PseudoExpectation c.V ℓ) {η : ℝ} (hη : 0 ≤ η) {K Bd : ℚ}
    (hE : E.ApproxSatisfies (c.sys K Bd) η 0) (hℓ : 22 * c.t ≤ ℓ)
    (hacc : sosErr (c.sys K Bd) η ((n : ℝ) ^ (50 * c.t)) ≤ 1 / 4)
    (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) {j l : Fin k}
    (hΔ : 0 < (c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l)) :
    E (c.pP j * c.pP l) ≤
      2 * (n : ℝ) ^ 2 * (2 ^ 18 * c.s / ((c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l))) ^ c.s +
        1 := by
  have hGj := c.h1Data_good hF hidx hfit hK0 hK Bd j
  have hGl := c.h1Data_good hF hidx hfit hK0 hK Bd l
  have hW := two_le_n c hF
  have hsm : c.s * (c.t / c.s) = c.t := by rw [mul_comm]; exact hF.params.div_mul_s
  have hTj := hGj.card_T
  have hTl := hGl.card_T
  have hTj' : ((c.Tset j).card : ℝ) ≤ n := by have := hTj; rwa [pow_one] at this
  have hTl' : ((c.Tset l).card : ℝ) ≤ n := by have := hTl; rwa [pow_one] at this
  exact cross_abstract hη hE hW hsm hF.params.s_pos hGj.m_pos hF.params.t_pow hℓ hacc
    (H1Data.Good.Pd (H := c.h1Data K Bd j)) (H1Data.Good.Pd (H := c.h1Data K Bd l))
    (DP_d c j) (DP_d c l) hGj.Pn hGl.Pn
    (sum_wW (fun i ↦ hasEq_bool i) (c.Tset j) hTj)
    (card_sub_sum_wW (fun i ↦ hasEq_bool i) hW (c.Tset j) hTj) (Nat.cast_nonneg _) hTj'
    (sum_wW (fun i ↦ hasEq_bool i) (c.Tset l) hTl)
    (card_sub_sum_wW (fun i ↦ hasEq_bool i) hW (c.Tset l) hTl) (Nat.cast_nonneg _) hTl'
    (c.H1 hF hidx hfit hK0 hK Bd j) (c.H1 hF hidx hfit hK0 hK Bd l) hΔ (isSumSq_triangle c j l)

/-- `Csep ln (1/w) > 0` for `Csep > 0`. -/
theorem sep_pos (hCsep : 0 < Csep) : 0 < Csep * Real.log (1 / w) := by
  have h := hF.params.two_le_inv_w
  exact mul_pos hCsep (Real.log_pos (by linarith))

/-- **The cross moment of two distinct clusters**: with `ρ = 2^18 s / (Csep ln (1/w))`,
`Ẽ[p_j p_l] ≤ 2 n² ρ^s + 1` for `j ≠ l`. -/
theorem cross_le {ℓ : ℕ} (E : PseudoExpectation c.V ℓ) {η : ℝ} (hη : 0 ≤ η) {K Bd : ℚ}
    (hE : E.ApproxSatisfies (c.sys K Bd) η 0) (hℓ : 22 * c.t ≤ ℓ)
    (hacc : sosErr (c.sys K Bd) η ((n : ℝ) ^ (50 * c.t)) ≤ 1 / 4)
    (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (hCsep : 0 < Csep) {j l : Fin k}
    (hjl : j ≠ l) :
    E (c.pP j * c.pP l) ≤
      2 * (n : ℝ) ^ 2 * (2 ^ 18 * c.s / (Csep * Real.log (1 / w))) ^ c.s + 1 := by
  have hsep := hF.sep j l hjl
  have hpos := sep_pos c hF hCsep
  have hΔ : 0 < (c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l) := hpos.trans_le hsep
  refine (cross_le_dist c hF E hη hE hℓ hacc hidx hfit hK0 hK hΔ).trans ?_
  have h1 : 2 ^ 18 * (c.s : ℝ) / ((c.F.m j - c.F.m l) ⬝ᵥ (c.F.m j - c.F.m l)) ≤
      2 ^ 18 * c.s / (Csep * Real.log (1 / w)) :=
    div_le_div_of_nonneg_left (by positivity) hpos hsep
  have h2 := pow_le_pow_left₀ (by positivity) h1 c.s
  have : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by positivity
  nlinarith

/-- **The cross moments**: with `ρ = 2^18 s / (Csep ln (1/w))`,
`∑_{j ≠ l} Ẽ[p_j p_l] ≤ k² (2 n² ρ^s + 1)`. -/
theorem cross_sum_le {ℓ : ℕ} (E : PseudoExpectation c.V ℓ) {η : ℝ} (hη : 0 ≤ η) {K Bd : ℚ}
    (hE : E.ApproxSatisfies (c.sys K Bd) η 0) (hℓ : 22 * c.t ≤ ℓ)
    (hacc : sosErr (c.sys K Bd) η ((n : ℝ) ^ (50 * c.t)) ≤ 1 / 4)
    (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (hCsep : 0 < Csep) :
    ∑ j, ∑ l ∈ univ.filter (· ≠ j), E (c.pP j * c.pP l) ≤
      (k : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 * (2 ^ 18 * c.s / (Csep * Real.log (1 / w))) ^ c.s + 1) := by
  set B : ℝ := 2 * (n : ℝ) ^ 2 * (2 ^ 18 * c.s / (Csep * Real.log (1 / w))) ^ c.s + 1 with hB
  have hpos := sep_pos c hF hCsep
  have hB0 : 0 ≤ B := by positivity
  calc ∑ j, ∑ l ∈ univ.filter (· ≠ j), E (c.pP j * c.pP l)
      ≤ ∑ j : Fin k, ∑ _l ∈ univ.filter (· ≠ j), B :=
        sum_le_sum fun j _ ↦ sum_le_sum fun l hl ↦
          cross_le c hF E hη hE hℓ hacc hidx hfit hK0 hK hCsep (Ne.symm (mem_filter.1 hl).2)
    _ ≤ ∑ _j : Fin k, (k : ℝ) * B := by
        refine sum_le_sum fun j _ ↦ ?_
        rw [sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hB0
        have := card_le_univ (univ.filter (· ≠ j) : Finset (Fin k))
        rw [Fintype.card_fin] at this
        exact_mod_cast this
    _ = (k : ℝ) ^ 2 * B := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit hF in
/-- **The cross moments in terms of the weights**: `∑_{j ≠ l} Ẽ[p_j p_l]` is the sum of
`Ẽ[wᵢ wᵢ']` over the pairs of remaining points in different clusters. -/
theorem sum_cross_eq {ℓ : ℕ} (E : PseudoExpectation c.V ℓ) :
    ∑ j, ∑ l ∈ univ.filter (· ≠ j), E (c.pP j * c.pP l) =
      ∑ i, ∑ i' ∈ univ.filter (fun i' ↦ c.F.ℓ (c.idx i) ≠ c.F.ℓ (c.idx i')),
        E (X (c.L.wv i) * X (c.L.wv i')) := by
  classical
  set f : Fin c.n' → Fin c.n' → ℝ := fun i i' ↦ E (X (c.L.wv i) * X (c.L.wv i')) with hf
  set cl : Fin c.n' → Fin k := fun i ↦ c.F.ℓ (c.idx i) with hcl
  have hpp : ∀ j l, E (c.pP j * c.pP l) = ∑ i ∈ c.Tset j, ∑ i' ∈ c.Tset l, f i i' :=
    fun j l ↦ by
      rw [pP, pP, Finset.sum_mul_sum, E.map_sum]
      exact sum_congr rfl fun i _ ↦ E.map_sum _ _
  simp only [hpp]
  rw [← Finset.sum_fiberwise univ cl
    (fun i ↦ ∑ i' ∈ univ.filter (fun i' ↦ cl i ≠ cl i'), f i i')]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  have hij : cl i = j := (mem_filter.1 hi).2
  simp only [hij]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun i' ↦ j ≠ cl i'))
    (t := univ.filter (· ≠ j)) (g := cl)
    (fun i' hi' ↦ by
      simp only [mem_filter, mem_univ, true_and] at hi' ⊢
      exact Ne.symm hi')]
  refine sum_congr rfl fun l hl ↦ ?_
  have hlj : l ≠ j := (mem_filter.1 hl).2
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext i'
  simp only [Tset, mem_filter, mem_univ, true_and, hcl]
  constructor
  · intro h; exact ⟨fun h' ↦ hlj (h ▸ h'.symm), h⟩
  · exact fun h ↦ h.2

/-- **The cross moments, pairwise**: the sum of `Ẽ[wᵢ wᵢ']` over the pairs of remaining points in
different clusters is at most `k² (2 n² ρ^s + 1)`, `ρ = 2^18 s / (Csep ln (1/w))`. -/
theorem cross_pairs_le {ℓ : ℕ} (E : PseudoExpectation c.V ℓ) {η : ℝ} (hη : 0 ≤ η) {K Bd : ℚ}
    (hE : E.ApproxSatisfies (c.sys K Bd) η 0) (hℓ : 22 * c.t ≤ ℓ)
    (hacc : sosErr (c.sys K Bd) η ((n : ℝ) ^ (50 * c.t)) ≤ 1 / 4)
    (hidx : Function.Injective c.idx) (hfit : Fits d c.s c.t (c.t / c.s) c.Lb)
    (hK0 : 0 ≤ (K : ℝ)) (hK : (K : ℝ) ≤ (256 * c.s) ^ c.t) (hCsep : 0 < Csep) :
    ∑ i, ∑ i' ∈ univ.filter (fun i' ↦ c.F.ℓ (c.idx i) ≠ c.F.ℓ (c.idx i')),
        E (X (c.L.wv i) * X (c.L.wv i')) ≤
      (k : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 * (2 ^ 18 * c.s / (Csep * Real.log (1 / w))) ^ c.s + 1) := by
  rw [← sum_cross_eq]
  exact cross_sum_le c hF E hη hE hℓ hacc hidx hfit hK0 hK hCsep

end Main

end IdCtx

end BS23.SmallRadius
