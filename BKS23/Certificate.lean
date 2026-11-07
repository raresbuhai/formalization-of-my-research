module

public import BKS23.Biclique

/-!
# Biclique certificates

[BKS23, `thm:certification-density-half`, `thm:certification-large-p` (2)]: if the bipartite
graph `H` between `U` and its complement `V` has good characters at every level `m = 1, …, t`
(`BKS23.Biclique.Characters`), with `Γ/λ ≤ C`, and its right vertices have at most `d`
neighbours in `U`, then

  `B(H) ⊢ |x|^(4t) |y| ≤ F_t⁴ |V| C⁴`, in degree `8t + 6`

(`BKS23.Biclique.Axioms.certificate`), where `F_t = ∑_m a(t, m) ≤ (2t + 1)^t` is the sum of the
coefficients of `|x|^t = ∑_{m ≤ t} a(t, m) e_m` (`SoS.Boolean.pow_sub_esymm`). For
`p`-biased characters this is the paper's bound `(1000t)^(10t) n (n/k)^4` (`p = 1/2`) or its
analogue for `p ≥ 1/2`, with `F_t⁴ ≤ (2t + 1)^(4t)` in place of `(1000t)^(10t)`.

**Deviation from the paper.** The paper proves `B(H) ⊢ e_t⁴ |y| ≤ ω` at the single level `t`
and then replaces `e_t` by `|x|^t` (`lem:power-vs-sets`), with univariate sum-of-squares proofs
(Fact 3.12) of `s(s-1)⋯(s-t+1) ≥ s^t / 2^t - 2t^t`. That route needs Fact 3.12 (a univariate
polynomial nonnegative on `ℝ` is a sum of squares of bounded bit complexity,
not formalized here), and this polynomial is nonnegative on `ℝ` only for even `t`
([README](README.md), item 5). We use instead the exact expansion `|x|^t = ∑_m a(t, m) e_m` with
nonnegative coefficients (Boolean axioms), the certificates of all levels `m ≤ t`
(`BKS23.Biclique.Axioms.level`; level `0` is `|y| ≤ |V|`), and the inequality
`(∑ aₘ zₘ)⁴ ≤ (∑ aₘ)³ ∑ aₘ zₘ⁴` (`BKS23.Biclique.isSOS_jensen`, two Cauchy–Schwarz steps). The
levels below `t` only need the balancedness of smaller sets, which the random graphs have as well.
-/

@[expose] public section

namespace BKS23.Biclique

open SoS MvPolynomial Finset

variable {σ : Type*}

/-! ### Jensen's inequality for the fourth power -/

/-- Cauchy–Schwarz: `(∑ aᵢ)(∑ aᵢ zᵢ²) - (∑ aᵢ zᵢ)² = ∑_{i, j} (aᵢ aⱼ / 2)(zᵢ - zⱼ)²`. -/
theorem cs_identity {ι : Type*} (s : Finset ι) (a : ι → ℝ) (z : ι → MvPolynomial σ ℝ) :
    (∑ i ∈ s, C (a i)) * (∑ i ∈ s, C (a i) * z i ^ 2) - (∑ i ∈ s, C (a i) * z i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, C (a i * a j / 2) * (z i - z j) ^ 2 := by
  have hC : ∀ i j, (C (a i * a j / 2) : MvPolynomial σ ℝ) = C (1 / 2) * (C (a i) * C (a j)) := by
    intro i j
    rw [← C_mul, ← C_mul]
    ring_nf
  have h2 : (C (1 / 2 : ℝ) : MvPolynomial σ ℝ) * 2 = 1 := by
    rw [show (2 : MvPolynomial σ ℝ) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  have e1 : ∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z i ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z j ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have e2 : (∑ i ∈ s, C (a i)) * (∑ i ∈ s, C (a i) * z i ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z j ^ 2 := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have e3 : (∑ i ∈ s, C (a i) * z i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * (z i * z j) := by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have e4 : ∑ i ∈ s, ∑ j ∈ s, C (a i * a j / 2) * (z i - z j) ^ 2 =
      C (1 / 2) * (∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z i ^ 2) +
      C (1 / 2) * (∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z j ^ 2) -
      ∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * (z i * z j) := by
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [hC]
    linear_combination (-(C (a i) * C (a j) * z i * z j)) * h2
  rw [e4, e2, e3, e1]
  linear_combination (-(∑ i ∈ s, ∑ j ∈ s, C (a i) * C (a j) * z j ^ 2)) * h2

theorem isSOS_cs {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (z : ι → MvPolynomial σ ℝ) :
    IsSOS ((∑ i ∈ s, C (a i)) * (∑ i ∈ s, C (a i) * z i ^ 2) - (∑ i ∈ s, C (a i) * z i) ^ 2) := by
  rw [cs_identity]
  exact IsSOS.sum _ fun i hi ↦ IsSOS.sum _ fun j hj ↦
    (IsSOS.const (by have := ha i hi; have := ha j hj; positivity)).mul (IsSOS.sq _)

/-- **Jensen's inequality for the fourth power**, as a sum of squares: for `aᵢ ≥ 0`,
`(∑ aᵢ)³ ∑ aᵢ zᵢ⁴ - (∑ aᵢ zᵢ)⁴` is a sum of squares. It is
`(∑ a)² [(∑ a)(∑ a z⁴) - (∑ a z²)²] + (P - Q)(P + Q)` with `P = (∑ a)(∑ a z²)` and
`Q = (∑ a z)²`, and `P - Q` is Cauchy–Schwarz. -/
theorem isSOS_jensen {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (z : ι → MvPolynomial σ ℝ) :
    IsSOS (C ((∑ i ∈ s, a i) ^ 3) * ∑ i ∈ s, C (a i) * z i ^ 4 - (∑ i ∈ s, C (a i) * z i) ^ 4) := by
  set A : MvPolynomial σ ℝ := ∑ i ∈ s, C (a i)
  set P := A * ∑ i ∈ s, C (a i) * z i ^ 2
  set Q := (∑ i ∈ s, C (a i) * z i) ^ 2
  have hA : C (∑ i ∈ s, a i) = A := map_sum C a s
  have hAs : IsSOS A := by
    rw [← hA]
    exact IsSOS.const (sum_nonneg ha)
  have h₁ := isSOS_cs s ha (fun i ↦ z i ^ 2)
  have h₂ := isSOS_cs s ha z
  have hP : IsSOS P := hAs.mul (IsSOS.sum _ fun i hi ↦ (IsSOS.const (ha i hi)).mul (IsSOS.sq _))
  have hQ : IsSOS Q := IsSOS.sq _
  have key := ((IsSOS.sq A).mul h₁).add (h₂.mul (hP.add hQ))
  convert key using 1
  rw [map_pow, hA]
  simp only [← pow_mul]
  ring

/-! ### `p`-biased characters -/

section PBiasedChars

/-- The `p`-biased character of a pair [BKS23, `def:char-matrix`]: `√((1-p)/p)` for an edge and
`-√(p/(1-p))` for a non-edge. Over a `p`-random graph it has mean `0` and variance `1`. -/
noncomputable def charP (p : ℝ) (adj : σ → σ → Prop) [DecidableRel adj] (w v : σ) : ℝ :=
  if adj w v then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))

/-- The character `u_{p,S}(v) = ∏_{w ∈ S} H_p(w, v)` of a set `S`. -/
noncomputable def charSet (p : ℝ) (adj : σ → σ → Prop) [DecidableRel adj] (S : Finset σ)
    (v : σ) : ℝ :=
  ∏ w ∈ S, charP p adj w v

/-- The larger of the two squared characters, `max((1-p)/p, p/(1-p)) ≥ 1`. -/
noncomputable def charMax (p : ℝ) : ℝ := max ((1 - p) / p) (p / (1 - p))

variable {adj : σ → σ → Prop} [DecidableRel adj] {p : ℝ}

theorem one_le_charMax (hp : 0 < p) (hp1 : p < 1) : 1 ≤ charMax p := by
  unfold charMax
  rcases le_total p (1 / 2) with h | h
  · exact le_max_of_le_left (by rw [le_div_iff₀ hp]; linarith)
  · exact le_max_of_le_right (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem charSet_of_full {S : Finset σ} {v : σ} (h : ∀ w ∈ S, adj w v) :
    charSet p adj S v = Real.sqrt ((1 - p) / p) ^ S.card := by
  rw [charSet, ← prod_const]
  exact prod_congr rfl fun w hw ↦ by simp [charP, h w hw]

theorem charP_sq_le (hp : 0 < p) (hp1 : p < 1) (w v : σ) : charP p adj w v ^ 2 ≤ charMax p := by
  unfold charP charMax
  split_ifs
  · rw [Real.sq_sqrt (div_nonneg (by linarith) hp.le)]
    exact le_max_left _ _
  · rw [neg_sq, Real.sq_sqrt (div_nonneg hp.le (by linarith))]
    exact le_max_right _ _

theorem charSet_sq_le (hp : 0 < p) (hp1 : p < 1) (S : Finset σ) (v : σ) :
    charSet p adj S v ^ 2 ≤ charMax p ^ S.card := by
  rw [charSet, ← prod_pow]
  calc ∏ w ∈ S, charP p adj w v ^ 2 ≤ ∏ _w ∈ S, charMax p :=
        prod_le_prod₀ (fun _ _ ↦ sq_nonneg _) fun w _ ↦ charP_sq_le hp hp1 w v
    _ = charMax p ^ S.card := prod_const _

theorem abs_charSet_le (hp : 0 < p) (hp1 : p < 1) (S : Finset σ) (v : σ) :
    |charSet p adj S v| ≤ charMax p ^ S.card := by
  have h1 : 1 ≤ charMax p ^ S.card := one_le_pow₀ (one_le_charMax hp hp1)
  refine abs_le_of_sq_le_sq ((charSet_sq_le hp hp1 S v).trans ?_) (by linarith)
  nlinarith

end PBiasedChars

/-! ### The certificate -/

variable [Fintype σ] [DecidableEq σ] {A : System σ ℝ} {U : Finset σ} {adj : σ → σ → Prop}
  {k : ℝ}

/-- Characters for level `m` of the bipartite graph `adj` (see `BKS23/Biclique.lean`), with all
sizes at most `W`, `λ = a² (k - d) - Δ ≥ 1/W`, and `Γ / λ ≤ c`. -/
structure Characters (U : Finset σ) (adj : σ → σ → Prop) (k d W c : ℝ) (m : ℕ) where
  /-- The characters `u_S(v)`. -/
  u : Finset σ → σ → ℝ
  /-- The value of `u_S(v)` when every vertex of `S` is adjacent to `v`. -/
  a : ℝ
  /-- The bound on the diagonal sums `∑_v u_S(v)²`. -/
  Γ : ℝ
  /-- The balancedness: the bound on the sums `∑_v u_S(v) u_T(v)` for `S ≠ T`. -/
  Δ : ℝ
  abs_a_le : |a| ≤ W
  Γ_nonneg : 0 ≤ Γ
  Γ_le : Γ ≤ W
  Δ_nonneg : 0 ≤ Δ
  Δ_le : Δ ≤ W
  abs_u_le : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W
  full : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, (∀ w ∈ S, adj w v) → u S v = a
  diag : ∀ S ∈ U.powersetCard m, ∑ v ∈ Uᶜ, u S v ^ 2 ≤ Γ
  off : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T → ∑ v ∈ Uᶜ, u S v * u T v ≤ Δ
  lam_pos : 0 < a ^ 2 * (k - d) - Δ
  one_le_lam : 1 ≤ W * (a ^ 2 * (k - d) - Δ)
  ratio_le : Γ / (a ^ 2 * (k - d) - Δ) ≤ c

namespace Axioms

variable {W c d : ℝ}

/-- One level, with the common bound `c`: `e_m⁴ |y| ≤ |V| c⁴`. Level `0` is `|y| ≤ |V|`. -/
theorem level_le (hA : Axioms A U adj k) [DecidableRel adj] (hW : 2 ≤ W)
    (hU : (U.card : ℝ) ≤ W) (hV : (Uᶜ.card : ℝ) ≤ W) {t m : ℕ} (hm : m ≤ t) (ht : (t : ℝ) ≤ W)
    (hc : 1 ≤ c) (hcW : c ≤ W) (hdW : d ≤ W)
    (hd : ∀ v ∈ Uᶜ, ((U.filter (adj · v)).card : ℝ) ≤ d)
    (hchar : ∀ m ∈ Icc 1 t, Nonempty (Characters U adj k d W c m)) :
    DerivesN A (6 * t + 6) (W ^ (6 * t + 26))
      (C (Uᶜ.card * c ^ 4) - esymmOn U m ^ 4 * ∑ v ∈ Uᶜ, X v) := by
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hV0 : (0 : ℝ) ≤ Uᶜ.card := Nat.cast_nonneg _
  have hconst : (Uᶜ.card : ℝ) * c ^ 4 ≤ W ^ 5 := by
    calc (Uᶜ.card : ℝ) * c ^ 4 ≤ W * W ^ 4 :=
          mul_le_mul hV (pow_le_pow_left₀ hc0 hcW 4) (by positivity) hW0
      _ = W ^ 5 := by ring
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- `|V| C⁴ - |y| = |V| (C⁴ - 1) + ∑_v (1 - y_v)`, with `1 - y = (1 - y)² - (y² - y)`.
    have hone : ∀ v ∈ Uᶜ, DerivesN A (6 * t + 6) 5 (1 - X v) := by
      intro v _
      have h₁ := DerivesN.ofIsSOS A (IsSOS.sq (1 - X v)) (k := 6 * t + 6) (M := 4)
        ((totalDegree_pow _ 2).trans (by
          have := (totalDegree_sub (1 : MvPolynomial σ ℝ) (X v)).trans
            (max_le (by simp) (by rw [totalDegree_X]))
          omega))
        ((coeffNorm1_pow_le _ 2).trans (by
          nlinarith [coeffNorm1_one_sub_X_le (σ := σ) v,
            coeffNorm1_nonneg (1 - X v : MvPolynomial σ ℝ)]))
      exact ((h₁.add ((hA.bool.eq v).2.mono (by omega) le_rfl)).mono le_rfl
        (by norm_num)).congr (by ring)
    have h₁ := DerivesN.sum Uᶜ hone
    have hc4 : (1 : ℝ) ≤ c ^ 4 := one_le_pow₀ hc
    have h₂ := DerivesN.ofIsSOS A (IsSOS.const (mul_nonneg hV0 (sub_nonneg.2 hc4)))
      (k := 6 * t + 6) (M := W ^ 5) (by rw [totalDegree_C]; omega) (by
        rw [coeffNorm1_C, abs_of_nonneg (mul_nonneg hV0 (sub_nonneg.2 hc4))]
        nlinarith)
    refine ((h₁.add h₂).mono le_rfl ?_).congr ?_
    · rw [sum_const, nsmul_eq_mul]
      have h3 : (5 : ℝ) ≤ W ^ 3 := le_pow_of_le_two_pow hW (by norm_num)
      have : (Uᶜ.card : ℝ) * 5 ≤ W ^ 25 := by
        calc (Uᶜ.card : ℝ) * 5 ≤ W * W ^ 3 := mul_le_mul hV h3 (by norm_num) hW0
          _ = W ^ 4 := by ring
          _ ≤ W ^ 25 := pow_le_pow_of_two_le hW (by omega)
      calc _ ≤ W ^ 26 := add_le_pow_succ hW this (pow_le_pow_of_two_le hW (by omega))
        _ ≤ _ := pow_le_pow_of_two_le hW (by omega)
    · have he0 : esymmOn U 0 = 1 := by simp [esymmOn]
      have hsum : ∑ v ∈ Uᶜ, (1 - X v : MvPolynomial σ ℝ) = (Uᶜ.card : MvPolynomial σ ℝ) -
          ∑ v ∈ Uᶜ, X v := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
      have hC : (C ((Uᶜ.card : ℝ) * (c ^ 4 - 1)) : MvPolynomial σ ℝ) =
          C ((Uᶜ.card : ℝ) * c ^ 4) - (Uᶜ.card : MvPolynomial σ ℝ) := by
        rw [mul_sub, mul_one, map_sub, map_natCast]
      rw [he0, one_pow, one_mul, hsum, hC]
      ring
  · obtain ⟨ch⟩ := hchar m (mem_Icc.2 ⟨hm1, hm⟩)
    have hmW : (m : ℝ) ≤ W := (Nat.cast_le.2 hm).trans ht
    have hl := hA.level hW hU hV hmW ch.abs_a_le ch.Γ_nonneg ch.Γ_le ch.Δ_nonneg ch.Δ_le hdW
      ch.abs_u_le ch.full ch.diag ch.off hd ch.lam_pos ch.one_le_lam
    set r := ch.Γ / (ch.a ^ 2 * (k - d) - ch.Δ)
    have hr0 : 0 ≤ r := div_nonneg ch.Γ_nonneg ch.lam_pos.le
    have hr4 : r ^ 4 ≤ c ^ 4 := pow_le_pow_left₀ hr0 ch.ratio_le 4
    have hgap : 0 ≤ (Uᶜ.card : ℝ) * (c ^ 4 - r ^ 4) := mul_nonneg hV0 (sub_nonneg.2 hr4)
    have h₂ := DerivesN.ofIsSOS A (IsSOS.const hgap) (k := 6 * t + 6) (M := W ^ 5)
      (by rw [totalDegree_C]; omega) (by
        rw [coeffNorm1_C, abs_of_nonneg hgap]
        nlinarith [pow_nonneg hr0 4])
    refine ((hl.mono (by omega) le_rfl).add h₂).mono le_rfl ?_ |>.congr ?_
    · exact add_le_pow_succ hW (pow_le_pow_of_two_le hW (by omega))
        (pow_le_pow_of_two_le hW (by omega))
    · have : (C ((Uᶜ.card : ℝ) * r ^ 4) : MvPolynomial σ ℝ) + C (Uᶜ.card * (c ^ 4 - r ^ 4)) =
          C (Uᶜ.card * c ^ 4) := by
        rw [← map_add]
        ring_nf
      linear_combination this

/-- **The biclique certificate** [BKS23, `thm:certification-density-half`,
`thm:certification-large-p` (2)]: `|x|^(4t) |y| ≤ F_t⁴ |V| c⁴` in degree `8t + 6`, where
`F_t = ∑_{m ≤ t} a(t, m) ≤ (2t + 1)^t` (`SoS.sum_stirlingCoeff_le`). -/
theorem certificate (hA : Axioms A U adj k) [DecidableRel adj] (hW : 2 ≤ W)
    (hU : (U.card : ℝ) + 1 ≤ W) (hV : (Uᶜ.card : ℝ) ≤ W) {t : ℕ} (ht : 2 * (t : ℝ) + 1 ≤ W)
    (hc : 1 ≤ c) (hcW : c ≤ W) (hdW : d ≤ W)
    (hd : ∀ v ∈ Uᶜ, ((U.filter (adj · v)).card : ℝ) ≤ d)
    (hchar : ∀ m ∈ Icc 1 t, Nonempty (Characters U adj k d W c m)) :
    DerivesN A (8 * t + 6) (W ^ (15 * t + 28))
      (C ((∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ^ 4 * Uᶜ.card * c ^ 4) -
        (∑ u ∈ U, X u) ^ (4 * t) * ∑ v ∈ Uᶜ, X v) := by
  set a : ℕ → ℝ := fun m ↦ (stirlingCoeff t m : ℝ) with hadef
  set F := ∑ m ∈ range (t + 1), a m with hFdef
  set Y : MvPolynomial σ ℝ := ∑ v ∈ Uᶜ, X v with hYdef
  set s : MvPolynomial σ ℝ := ∑ u ∈ U, X u with hsdef
  set E := ∑ m ∈ range (t + 1), C (a m) * esymmOn U m with hEdef
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hU' : (U.card : ℝ) ≤ W := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have ht' : (t : ℝ) ≤ W := by linarith
  have ha0 : ∀ m, 0 ≤ a m := fun m ↦ Nat.cast_nonneg _
  have hF0 : 0 ≤ F := sum_nonneg fun m _ ↦ ha0 m
  have hF : F ≤ W ^ t := by
    have hFn : F = ((∑ m ∈ range (t + 1), stirlingCoeff t m : ℕ) : ℝ) := by
      rw [hFdef, hadef]
      push_cast
      rfl
    calc F ≤ (2 * t + 1) ^ t := by
          rw [hFn]
          exact_mod_cast sum_stirlingCoeff_le t
      _ ≤ W ^ t := pow_le_pow_left₀ (by positivity) ht t
  have he : ∀ m ∈ range (t + 1), coeffNorm1 (esymmOn U m) ≤ W ^ t := fun m hm ↦
    (coeffNorm1_esymmOn_le hW hU' m).trans (pow_le_pow_of_two_le hW (mem_range_succ_iff.1 hm))
  have hed : ∀ m ∈ range (t + 1), (esymmOn U m).totalDegree ≤ t := fun m hm ↦
    (totalDegree_esymmOn_le U m).trans (mem_range_succ_iff.1 hm)
  have hE : coeffNorm1 E ≤ W ^ (2 * t) := by
    refine (coeffNorm1_sum_le _ _).trans ?_
    calc ∑ m ∈ range (t + 1), coeffNorm1 (C (a m) * esymmOn U m)
        ≤ ∑ m ∈ range (t + 1), a m * W ^ t := sum_le_sum fun m hm ↦ by
          rw [coeffNorm1_C_mul, abs_of_nonneg (ha0 m)]
          exact mul_le_mul_of_nonneg_left (he m hm) (ha0 m)
      _ = F * W ^ t := by rw [← sum_mul]
      _ ≤ W ^ t * W ^ t := mul_le_mul_of_nonneg_right hF (pow_nonneg_of_two_le hW _)
      _ = W ^ (2 * t) := by ring
  have hEd : E.totalDegree ≤ t := totalDegree_finsetSum_le fun m hm ↦
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hed m hm)
  have hs : coeffNorm1 s ≤ W := (coeffNorm1_sum_le _ _).trans (by simpa [coeffNorm1_X] using hU')
  have hsd : s.totalDegree ≤ 1 := totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]
  have hY : coeffNorm1 Y ≤ W := (coeffNorm1_sum_le _ _).trans (by simpa [coeffNorm1_X] using hV)
  have hYd : Y.totalDegree ≤ 1 := totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]
  -- (F2) `∑_m a(t, m) (|V| c⁴ - e_m⁴ |y|) ≥ 0`, times `F³`.
  have h₂ := DerivesN.sum (range (t + 1)) fun m hm ↦
    (hA.level_le hW hU' hV (mem_range_succ_iff.1 hm) ht' hc hcW hdW hd hchar).smul (ha0 m)
  have h₂' := (h₂.smul (pow_nonneg hF0 3)).mono (k' := 8 * t + 6) (by omega)
    (M' := W ^ (10 * t + 26)) (by
      rw [← sum_mul]
      calc F ^ 3 * (F * W ^ (6 * t + 26)) ≤ (W ^ t) ^ 3 * (W ^ t * W ^ (6 * t + 26)) := by
            gcongr
        _ = W ^ (10 * t + 26) := by ring)
  -- (F3) Jensen, times `|y| ≥ 0`.
  have hJ := isSOS_jensen (range (t + 1)) (fun m _ ↦ ha0 m) (esymmOn U)
  set Q := C (F ^ 3) * ∑ m ∈ range (t + 1), C (a m) * esymmOn U m ^ 4 - E ^ 4 with hQdef
  have hQ : coeffNorm1 Q ≤ W ^ (8 * t + 1) := by
    refine (coeffNorm1_sub_le _ _).trans (add_le_pow_succ hW ?_ ?_)
    · rw [coeffNorm1_C_mul, abs_of_nonneg (pow_nonneg hF0 3)]
      calc F ^ 3 * coeffNorm1 (∑ m ∈ range (t + 1), C (a m) * esymmOn U m ^ 4)
          ≤ F ^ 3 * (F * W ^ (4 * t)) := by
            refine mul_le_mul_of_nonneg_left ((coeffNorm1_sum_le _ _).trans ?_)
              (pow_nonneg hF0 3)
            rw [sum_mul]
            refine sum_le_sum fun m hm ↦ ?_
            rw [coeffNorm1_C_mul, abs_of_nonneg (ha0 m)]
            refine mul_le_mul_of_nonneg_left ((coeffNorm1_pow_le _ 4).trans ?_) (ha0 m)
            calc coeffNorm1 (esymmOn U m) ^ 4 ≤ (W ^ t) ^ 4 :=
                  pow_le_pow_left₀ (coeffNorm1_nonneg _) (he m hm) 4
              _ = W ^ (4 * t) := by ring
        _ ≤ (W ^ t) ^ 3 * (W ^ t * W ^ (4 * t)) := by gcongr
        _ = W ^ (8 * t) := by ring
    · calc coeffNorm1 (E ^ 4) ≤ coeffNorm1 E ^ 4 := coeffNorm1_pow_le _ 4
        _ ≤ (W ^ (2 * t)) ^ 4 := pow_le_pow_left₀ (coeffNorm1_nonneg _) hE 4
        _ = W ^ (8 * t) := by ring
  have hQd : Q.totalDegree ≤ 4 * t := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ((totalDegree_pow _ 4).trans (by omega)))
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_finsetSum_le fun m hm ↦ (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact (totalDegree_pow _ 4).trans (by have := hed m hm; omega))
  have hyv : ∀ v ∈ Uᶜ, DerivesN A 2 5 (X v) := fun v _ ↦ by
    have := hA.bool.nonneg {v}
    rw [card_singleton] at this
    simp only [xS, prod_singleton] at this
    exact this.mono le_rfl (by norm_num)
  have h₃ := (DerivesN.sum Uᶜ fun v hv ↦ (hyv v hv).mulSOS hJ).mono (k' := 8 * t + 6)
    (by omega) (M' := W ^ (8 * t + 5)) (by
      have h5 : (5 : ℝ) ≤ W ^ 3 := le_pow_of_le_two_pow hW (by norm_num)
      have := sum_le_pow hW Uᶜ (a := 8 * t + 4) (c := 1) (f := fun _ ↦ coeffNorm1 Q * 5)
        (fun _ _ ↦ by
          calc coeffNorm1 Q * 5 ≤ W ^ (8 * t + 1) * W ^ 3 :=
                mul_le_mul hQ h5 (by norm_num) (pow_nonneg_of_two_le hW _)
            _ = W ^ (8 * t + 4) := by ring) (by simpa using hV)
      simpa using this)
  -- (F5) `(s^(4t) - E⁴) |y| = 0`, from `s^t = E`.
  have hst := hA.bool.pow_sub_esymm U t
  set r := (s ^ (3 * t) + s ^ (2 * t) * E + s ^ t * E ^ 2 + E ^ 3) * Y with hrdef
  have hr : coeffNorm1 r ≤ W ^ (6 * t + 4) := by
    have hsp : ∀ n, coeffNorm1 (s ^ n) ≤ W ^ n := fun n ↦
      (coeffNorm1_pow_le _ n).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hs n)
    have hEp : ∀ n, coeffNorm1 (E ^ n) ≤ W ^ (2 * t * n) := fun n ↦
      (coeffNorm1_pow_le _ n).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) hE n).trans_eq
        (by rw [← pow_mul]))
    have hmul : ∀ {p q : MvPolynomial σ ℝ} {i j : ℕ}, coeffNorm1 p ≤ W ^ i →
        coeffNorm1 q ≤ W ^ j → coeffNorm1 (p * q) ≤ W ^ (i + j) := fun hp hq ↦
      (coeffNorm1_mul_le _ _).trans ((mul_le_mul hp hq (coeffNorm1_nonneg _)
        (pow_nonneg_of_two_le hW _)).trans_eq (pow_add _ _ _).symm)
    have t₁ : coeffNorm1 (s ^ (3 * t)) ≤ W ^ (6 * t) :=
      (hsp _).trans (pow_le_pow_of_two_le hW (by omega))
    have t₂ : coeffNorm1 (s ^ (2 * t) * E) ≤ W ^ (6 * t) :=
      (hmul (hsp _) hE).trans (pow_le_pow_of_two_le hW (by omega))
    have t₃ : coeffNorm1 (s ^ t * E ^ 2) ≤ W ^ (6 * t) :=
      (hmul (hsp _) (hEp 2)).trans (pow_le_pow_of_two_le hW (by omega))
    have t₄ : coeffNorm1 (E ^ 3) ≤ W ^ (6 * t) := (hEp 3).trans (pow_le_pow_of_two_le hW (by omega))
    have p₁ : coeffNorm1 (s ^ (3 * t) + s ^ (2 * t) * E) ≤ W ^ (6 * t + 1) :=
      (coeffNorm1_add_le _ _).trans (add_le_pow_succ hW t₁ t₂)
    have p₂ : coeffNorm1 (s ^ (3 * t) + s ^ (2 * t) * E + s ^ t * E ^ 2) ≤ W ^ (6 * t + 2) :=
      (coeffNorm1_add_le _ _).trans (add_le_pow_succ hW p₁
        (t₃.trans (pow_le_pow_of_two_le hW (by omega))))
    have hsum : coeffNorm1 (s ^ (3 * t) + s ^ (2 * t) * E + s ^ t * E ^ 2 + E ^ 3) ≤
        W ^ (6 * t + 3) :=
      (coeffNorm1_add_le _ _).trans (add_le_pow_succ hW p₂
        (t₄.trans (pow_le_pow_of_two_le hW (by omega))))
    exact hmul (i := 6 * t + 3) (j := 1) hsum (by rw [pow_one]; exact hY)
  have hrd : r.totalDegree ≤ 3 * t + 1 := by
    refine (totalDegree_mul _ _).trans (add_le_add ?_ hYd)
    have hsp : ∀ n, (s ^ n).totalDegree ≤ n := fun n ↦
      (totalDegree_pow _ n).trans (by nlinarith)
    have hEp : ∀ n, (E ^ n).totalDegree ≤ t * n := fun n ↦
      (totalDegree_pow _ n).trans (by nlinarith)
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le ((hsp _).trans (by omega)) ?_)) ?_))
      ((hEp 3).trans (by omega)))
    · exact (totalDegree_mul _ _).trans (by have := hsp (2 * t); omega)
    · exact (totalDegree_mul _ _).trans (by have := hsp t; have := hEp 2; omega)
  have h₅ := (hst.mul r).2.mono (k' := 8 * t + 6) (by omega) (M' := W ^ (15 * t + 12)) (by
    have h1 := add_one_sq_le_pow hW (coeffNorm1_nonneg r) hr
    have h2 : Boolean.powNorm U.card t ≤ W ^ (3 * t + 2) := by
      unfold Boolean.powNorm
      have hN : (U.card : ℝ) + 1 ≤ W := hU
      have h4t : 4 * (t : ℝ) ^ 2 ≤ W ^ 2 := by
        calc 4 * (t : ℝ) ^ 2 ≤ (2 * t + 1) ^ 2 := by nlinarith
          _ ≤ W ^ 2 := pow_le_pow_left₀ (by positivity) ht 2
      calc 4 * (t : ℝ) ^ 2 * ((U.card : ℝ) + 1) ^ (2 * t) * (2 * t + 1) ^ t
          ≤ W ^ 2 * W ^ (2 * t) * W ^ t := by
            gcongr
        _ = W ^ (3 * t + 2) := by ring
    calc (coeffNorm1 r + 1) ^ 2 * Boolean.powNorm U.card t
        ≤ W ^ (2 * (6 * t + 4) + 2) * W ^ (3 * t + 2) :=
          mul_le_mul h1 h2 (Boolean.powNorm_nonneg _ _) (pow_nonneg_of_two_le hW _)
      _ = W ^ (15 * t + 12) := by ring)
  -- Assembly.
  refine ((h₂'.add h₃).add h₅).mono le_rfl ?_ |>.congr ?_
  · exact add_le_pow_succ hW (add_le_pow_succ hW (pow_le_pow_of_two_le hW (by omega))
      (pow_le_pow_of_two_le hW (by omega))) (pow_le_pow_of_two_le hW (by omega))
  · have e1 : ∑ m ∈ range (t + 1), C (a m) * (C ((Uᶜ.card : ℝ) * c ^ 4) - esymmOn U m ^ 4 * Y) =
        C (F * (Uᶜ.card * c ^ 4)) - (∑ m ∈ range (t + 1), C (a m) * esymmOn U m ^ 4) * Y := by
      have h : (C (F * (Uᶜ.card * c ^ 4)) : MvPolynomial σ ℝ) =
          ∑ m ∈ range (t + 1), C (a m) * C ((Uᶜ.card : ℝ) * c ^ 4) := by
        rw [← sum_mul, ← map_sum, ← map_mul]
      rw [h, sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun m _ ↦ by ring
    have e2 : ∑ v ∈ Uᶜ, Q * X v = Q * Y := by rw [hYdef, mul_sum]
    have e3 : (C (F ^ 4 * Uᶜ.card * c ^ 4) : MvPolynomial σ ℝ) =
        C (F ^ 3) * C (F * (Uᶜ.card * c ^ 4)) := by
      rw [← map_mul]
      ring_nf
    rw [e1, e2, e3, hQdef, hrdef]
    ring

end Axioms

/-! ### `p`-biased characters: the certificate -/

section PBiased

variable {p : ℝ} [DecidableRel adj]

/-- The characters of level `m` are `p`-biased characters, with `a = (√((1-p)/p))^m`,
`Γ = |V| max((1-p)/p, p/(1-p))^m` and the balancedness `Δ`. -/
noncomputable def pBiased (hp : 0 < p) (hp1 : p < 1) {k d W c Δ : ℝ} {m : ℕ}
    (hMW : charMax p ^ m ≤ W) (hΓW : Uᶜ.card * charMax p ^ m ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W)
    (hbal : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, charSet p adj S v * charSet p adj T v ≤ Δ)
    (hlam : 1 ≤ W * (((1 - p) / p) ^ m * (k - d) - Δ))
    (hratio : Uᶜ.card * charMax p ^ m / (((1 - p) / p) ^ m * (k - d) - Δ) ≤ c) :
    Characters U adj k d W c m where
  u := charSet p adj
  a := Real.sqrt ((1 - p) / p) ^ m
  Γ := Uᶜ.card * charMax p ^ m
  Δ := Δ
  abs_a_le := by
    rw [abs_of_nonneg (by positivity)]
    refine le_trans ?_ hMW
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ m
    calc Real.sqrt ((1 - p) / p) ≤ Real.sqrt (charMax p) :=
          Real.sqrt_le_sqrt (le_max_left _ _)
      _ ≤ charMax p := by
          have h1 := one_le_charMax hp hp1
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  Γ_nonneg := by
    have := one_le_charMax hp hp1
    positivity
  Γ_le := hΓW
  Δ_nonneg := hΔ
  Δ_le := hΔW
  abs_u_le S hS v _ := by
    have := abs_charSet_le (adj := adj) hp hp1 S v
    rw [(mem_powersetCard.1 hS).2] at this
    exact this.trans hMW
  full S hS v _ h := by
    rw [charSet_of_full h, (mem_powersetCard.1 hS).2]
  diag S hS := by
    calc ∑ v ∈ Uᶜ, charSet p adj S v ^ 2 ≤ ∑ _v ∈ Uᶜ, charMax p ^ m :=
          sum_le_sum fun v _ ↦ (mem_powersetCard.1 hS).2 ▸ charSet_sq_le hp hp1 S v
      _ = Uᶜ.card * charMax p ^ m := by rw [sum_const, nsmul_eq_mul]
  off := hbal
  lam_pos := by
    have hsq : (Real.sqrt ((1 - p) / p) ^ m) ^ 2 = ((1 - p) / p) ^ m := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (div_nonneg (by linarith) hp.le)]
    rw [hsq]
    by_contra h
    rw [not_lt] at h
    nlinarith
  one_le_lam := by
    have hsq : (Real.sqrt ((1 - p) / p) ^ m) ^ 2 = ((1 - p) / p) ^ m := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (div_nonneg (by linarith) hp.le)]
    rwa [hsq]
  ratio_le := by
    have hsq : (Real.sqrt ((1 - p) / p) ^ m) ^ 2 = ((1 - p) / p) ^ m := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (div_nonneg (by linarith) hp.le)]
    rwa [hsq]

/-- **The biclique certificate for `p`-biased characters** [BKS23,
`thm:certification-density-half`, `thm:certification-large-p` (2)]: if the right vertices have
at most `d` neighbours in `U`, and the `p`-biased characters have balancedness `Δ m` at every
level `m = 1, …, t` with `λ_m = ((1-p)/p)^m (k - d) - Δ m ≥ 1/W` and
`|V| max((1-p)/p, p/(1-p))^m / λ_m ≤ c`, then `|x|^(4t) |y| ≤ F_t⁴ |V| c⁴` in degree `8t + 6`.
For `p = 1/2` the characters are `±1` and `λ_m = k - d - Δ m`. -/
theorem Axioms.certificate_pBiased (hA : Axioms A U adj k) {W c d : ℝ} {t : ℕ} {Δ : ℕ → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hW : 2 ≤ W) (hU : (U.card : ℝ) + 1 ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) (ht : 2 * (t : ℝ) + 1 ≤ W) (hc : 1 ≤ c) (hcW : c ≤ W)
    (hdW : d ≤ W) (hd : ∀ v ∈ Uᶜ, ((U.filter (adj · v)).card : ℝ) ≤ d)
    (hMW : ∀ m ∈ Icc 1 t, charMax p ^ m ≤ W) (hΓW : ∀ m ∈ Icc 1 t, Uᶜ.card * charMax p ^ m ≤ W)
    (hΔ : ∀ m ∈ Icc 1 t, 0 ≤ Δ m ∧ Δ m ≤ W)
    (hbal : ∀ m ∈ Icc 1 t, ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, charSet p adj S v * charSet p adj T v ≤ Δ m)
    (hlam : ∀ m ∈ Icc 1 t, 1 ≤ W * (((1 - p) / p) ^ m * (k - d) - Δ m))
    (hratio : ∀ m ∈ Icc 1 t,
      Uᶜ.card * charMax p ^ m / (((1 - p) / p) ^ m * (k - d) - Δ m) ≤ c) :
    DerivesN A (8 * t + 6) (W ^ (15 * t + 28))
      (C ((∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ^ 4 * Uᶜ.card * c ^ 4) -
        (∑ u ∈ U, X u) ^ (4 * t) * ∑ v ∈ Uᶜ, X v) :=
  hA.certificate hW hU hV ht hc hcW hdW hd fun m hm ↦
    ⟨pBiased hp hp1 (hMW m hm) (hΓW m hm) (hΔ m hm).1 (hΔ m hm).2 (hbal m hm) (hlam m hm)
      (hratio m hm)⟩

end PBiased

end BKS23.Biclique
