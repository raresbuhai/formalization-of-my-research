module

public import Background.SumOfSquares.Boolean

/-!
# Biclique certificates, one level

[BKS23, §4]: sum-of-squares certificates that a bipartite graph `H` between `U` and its
complement `V` has no unbalanced bicliques of total size `k`. The variables are `σ`; those in `U`
are the paper's `x`, the others its `y`.

A system `A` *contains the biclique axioms* `B(H)` (`BKS23.Biclique.Axioms`) if all variables are
Boolean, `∑ᵢ xᵢ = k`, and `x_u x_v = 0` for `u ∈ U`, `v ∉ U` not adjacent in `H`. Containing, not
equal: the certificates then hold in the clique axioms `A(G)` directly, and for every subgraph of
`H` (more non-edges only add constraints).

Write `|y| = ∑_{v ∉ U} x_v` and `e_m = ∑_{S ⊆ U, |S| = m} x_S` (`SoS.esymmOn`). The certificate
at level `m` (`BKS23.Biclique.Axioms.level`) is

  `B(H) ⊢ e_m⁴ |y| ≤ |V| (Γ/λ)⁴`, in degree `6m + 6`, with `λ = a² (k - d) - Δ > 0`,

for a bipartite graph whose right vertices have at most `d` neighbours in `U`, and characters
`u_S(v)` (`|S| = m`, `v ∉ U`) with

* `u_S(v) = a` whenever every vertex of `S` is adjacent to `v`;
* `∑_v u_S(v)² ≤ Γ` (the diagonal) and `∑_v u_S(v) u_T(v) ≤ Δ` for `S ≠ T` (balancedness).

For `p`-biased characters (`def:char-matrix`, `BKS23.Biclique.charSet`),
`u_S(v) = ∏_{w ∈ S} H_p(w, v)`, `a = ((1-p)/p)^(m/2)` and `Γ = |V| max(p/(1-p), (1-p)/p)^m`; for
`p = 1/2` they are the `±1` characters, with `a = 1` and `Γ = |V|`. The proof follows the paper:

* `BKS23.Biclique.Axioms.main` (`lem:biclique-certificate`, `lem:biclique-certificate-large-p`):
  `a² e_m² |y| ≤ Γ e_m + Δ e_m²`, from `∑_v (Z_v (1 - y_v))² ≥ 0` with
  `Z_v = ∑_{|S| = m} u_S(v) x_S` (`BKS23.Biclique.zv`). It splits into
  `∑_v Z_v² ≤ Γ e_m + Δ e_m²` (`stageA`) and `a² e_m² |y| ≤ ∑_v Z_v²` (`stageB`).
* `BKS23.Biclique.Axioms.lower` (`lem:lower-bound-LHS-trick`): `y_j |y| ≥ (k - d) y_j`.
* `BKS23.Biclique.Axioms.vertex` (`lem:biclique-certificate-final`): with `b = y_j e_m`, the two
  give `b² ≤ (Γ/λ) b`. Cancellation (Fact 3.11 with `t = 2`, here the identity
  `C⁴ - b⁴ = (C² + b²)(C - b)² + 2 (C² + b²)(C b - b²)`) gives `y_j e_m⁴ ≤ (Γ/λ)⁴`.
* `BKS23.Biclique.Axioms.level`: the sum over `j`.

The paper then replaces `e_m` by `|x|^m` with univariate sum-of-squares proofs
(`lem:power-vs-sets`); we combine the levels instead (`BKS23/Certificate.lean`).

Degrees are larger than the paper's `4m + 2` by a constant factor: equalities are pairs of
inequalities, and multiplying one by a polynomial `r` costs degree `2 deg r`
(`SoS.DerivesEq.mul`). Norms of the multipliers are powers of a size parameter `W ≥ 2` that
bounds `|U|`, `|V|`, `m`, the characters, `a`, `Γ`, `Δ`, `d` and `1/λ`.
-/

@[expose] public section

namespace BKS23.Biclique

open SoS MvPolynomial Finset

variable {σ : Type*}

/-! ### Sizes -/

section Sizes

variable {U : Finset σ} {W : ℝ}

theorem card_powersetCard_le (hU : (U.card : ℝ) ≤ W) (m : ℕ) :
    ((U.powersetCard m).card : ℝ) ≤ W ^ m := by
  rw [card_powersetCard]
  calc ((U.card.choose m : ℕ) : ℝ) ≤ (U.card : ℝ) ^ m := by exact_mod_cast Nat.choose_le_pow _ _
    _ ≤ W ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hU m

theorem coeffNorm1_esymmOn_le (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W) (m : ℕ) :
    coeffNorm1 (esymmOn U m) ≤ W ^ m := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  have := sum_le_pow hW (U.powersetCard m) (a := 0) (fun S _ ↦ (coeffNorm1_xS_le S).trans_eq
    (pow_zero W).symm) (card_powersetCard_le hU m)
  rwa [zero_add] at this

theorem totalDegree_esymmOn_le (U : Finset σ) (m : ℕ) : (esymmOn U m).totalDegree ≤ m :=
  totalDegree_finsetSum_le fun S hS ↦ (totalDegree_xS_le S).trans (mem_powersetCard.1 hS).2.le

/-- `Z_v = ∑_{|S| = m} u_S(v) x_S`, the `v`-th coordinate of `∑_{|S| = m} x_S u_S`. -/
noncomputable def zv (U : Finset σ) (m : ℕ) (u : Finset σ → σ → ℝ) (v : σ) : MvPolynomial σ ℝ :=
  ∑ S ∈ U.powersetCard m, C (u S v) * xS S

theorem totalDegree_zv_le (U : Finset σ) (m : ℕ) (u : Finset σ → σ → ℝ) (v : σ) :
    (zv U m u v).totalDegree ≤ m :=
  totalDegree_finsetSum_le fun S hS ↦ (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact (totalDegree_xS_le S).trans (mem_powersetCard.1 hS).2.le)

theorem coeffNorm1_zv_le (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W) {m : ℕ} {u : Finset σ → σ → ℝ}
    {v : σ} (hu : ∀ S ∈ U.powersetCard m, |u S v| ≤ W) : coeffNorm1 (zv U m u v) ≤ W ^ (m + 1) := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  have h : ∀ S ∈ U.powersetCard m, coeffNorm1 (C (u S v) * xS S) ≤ W ^ 1 := fun S hS ↦ by
    rw [coeffNorm1_C_mul, pow_one]
    calc |u S v| * coeffNorm1 (xS S) ≤ |u S v| * 1 :=
          mul_le_mul_of_nonneg_left (coeffNorm1_xS_le S) (abs_nonneg _)
      _ ≤ W := by rw [mul_one]; exact hu S hS
  have := sum_le_pow hW _ h (card_powersetCard_le hU m)
  rwa [add_comm] at this

theorem coeffNorm1_one_sub_X_le (i : σ) : coeffNorm1 (1 - X i : MvPolynomial σ ℝ) ≤ 2 := by
  have := coeffNorm1_sub_le (1 : MvPolynomial σ ℝ) (X i)
  rw [coeffNorm1_one, coeffNorm1_X] at this
  linarith

/-- `∑_{S, T} (u_S(v) u_T(v) - a²) x_S x_T y_v = Z_v² y_v - a² e_m² y_v`. -/
theorem sum_sum_coeff (U : Finset σ) (m : ℕ) (u : Finset σ → σ → ℝ) (a : ℝ) (v : σ) :
    ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
        C (u S v * u T v - a ^ 2) * (xS S * xS T * X v) =
      zv U m u v ^ 2 * X v - C (a ^ 2) * esymmOn U m ^ 2 * X v := by
  have h₁ : zv U m u v ^ 2 * X v = ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
      C (u S v * u T v) * (xS S * xS T * X v) := by
    rw [pow_two (zv U m u v), zv, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun S _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun T _ ↦ ?_
    rw [map_mul]
    ring
  have h₂ : C (a ^ 2) * esymmOn U m ^ 2 * X v = ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
      C (a ^ 2) * (xS S * xS T * X v) := by
    rw [pow_two (esymmOn U m), esymmOn, sum_mul_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun S _ ↦ ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun T _ ↦ ?_
    ring
  rw [h₁, h₂, ← sum_sub_distrib]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun T _ ↦ ?_
  rw [map_sub]
  ring

end Sizes

variable [Fintype σ] [DecidableEq σ]

/-- The system `A` contains the biclique axioms `B(H)` [BKS23, (eq:biclique-system)] for the
bipartite graph `H` between `U` and its complement given by `adj`: all variables are Boolean,
`∑ᵢ xᵢ = k`, and `x_u x_v = 0` for `u ∈ U`, `v ∉ U` not adjacent. -/
structure Axioms (A : System σ ℝ) (U : Finset σ) (adj : σ → σ → Prop) (k : ℝ) : Prop where
  bool : Boolean A
  card : HasEq A (∑ i, X i - C k)
  edge : ∀ u ∈ U, ∀ v ∈ Uᶜ, ¬ adj u v → HasEq A (X u * X v)

variable {A : System σ ℝ} {U : Finset σ} {adj : σ → σ → Prop} {k : ℝ}


/-! ### The key lemma -/

namespace Axioms

theorem edge_eq (hA : Axioms A U adj k) {w v : σ} (hw : w ∈ U) (hv : v ∈ Uᶜ) (hn : ¬ adj w v) :
    DerivesEq A 2 1 (X w * X v) :=
  (hA.edge w hw v hv hn).derivesEq
    ((totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X])) le_rfl

/-- A term `c x_S x_T y_v` with a vertex of `S ∪ T` not adjacent to `v` vanishes. -/
theorem kill (hA : Axioms A U adj k) {m : ℕ} {S T : Finset σ} (hS : S ∈ U.powersetCard m)
    (hT : T ∈ U.powersetCard m) {v : σ} (hv : v ∈ Uᶜ) (c : ℝ)
    (hc : (∀ w ∈ S, adj w v) → (∀ w ∈ T, adj w v) → c = 0) :
    DerivesEq A (4 * m) ((|c| + 1) ^ 2) (C c * (xS S * xS T * X v)) := by
  rw [mem_powersetCard] at hS hT
  by_cases hfull : (∀ w ∈ S, adj w v) ∧ (∀ w ∈ T, adj w v)
  · rw [hc hfull.1 hfull.2]
    simpa using DerivesEq.zero A (4 * m) (by positivity : (0 : ℝ) ≤ (|(0 : ℝ)| + 1) ^ 2)
  simp only [not_and_or, not_forall, exists_prop] at hfull
  -- The term is `r x_w x_v` for a non-neighbour `w` of `v`, with `deg r ≤ 2m - 1`.
  have key : ∀ {w : σ} {r : MvPolynomial σ ℝ}, w ∈ U → ¬ adj w v →
      r.totalDegree + 1 ≤ 2 * m → coeffNorm1 r ≤ |c| → r * (X w * X v) = C c * (xS S * xS T * X v) →
      DerivesEq A (4 * m) ((|c| + 1) ^ 2) (C c * (xS S * xS T * X v)) := by
    intro w r hw hn hdeg hnorm he
    have h := (hA.edge_eq hw hv hn).mul r
    refine (h.mono (by omega) ?_).congr he
    rw [mul_one]
    exact pow_le_pow_left₀ (by linarith [coeffNorm1_nonneg r]) (by linarith) 2
  have hdeg : ∀ (R₁ R₂ : Finset σ), (C c * xS R₁ * xS R₂).totalDegree ≤ R₁.card + R₂.card :=
    fun R₁ R₂ ↦ (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]; exact totalDegree_xS_le R₁)) (totalDegree_xS_le R₂))
  have hnorm : ∀ (R₁ R₂ : Finset σ), coeffNorm1 (C c * xS R₁ * xS R₂) ≤ |c| := by
    intro R₁ R₂
    rw [mul_assoc, coeffNorm1_C_mul]
    calc |c| * coeffNorm1 (xS R₁ * xS R₂) ≤ |c| * 1 := mul_le_mul_of_nonneg_left
          ((coeffNorm1_mul_le _ _).trans (by
            nlinarith [coeffNorm1_xS_le R₁, coeffNorm1_xS_le R₂, coeffNorm1_nonneg (xS R₁),
              coeffNorm1_nonneg (xS R₂)])) (abs_nonneg _)
      _ = |c| := mul_one _
  rcases hfull with ⟨w, hw, hn⟩ | ⟨w, hw, hn⟩
  · refine key (r := C c * xS (S.erase w) * xS T) (hS.1 hw) hn ?_ (hnorm _ _) ?_
    · have := hdeg (S.erase w) T
      have := card_erase_of_mem hw
      have := card_pos.2 ⟨w, hw⟩
      omega
    · rw [← X_mul_xS_erase hw]
      ring
  · refine key (r := C c * xS S * xS (T.erase w)) (hT.1 hw) hn ?_ (hnorm _ _) ?_
    · have := hdeg S (T.erase w)
      have := card_erase_of_mem hw
      have := card_pos.2 ⟨w, hw⟩
      omega
    · rw [← X_mul_xS_erase hw]
      ring

variable {W : ℝ}

/-- One coordinate of the second half of the key lemma: `a² e_m² y_v ≤ Z_v²`. -/
theorem stageB_v (hA : Axioms A U adj k) (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W) {m : ℕ}
    {u : Finset σ → σ → ℝ} {a : ℝ} (ha : |a| ≤ W) {v : σ} (hv : v ∈ Uᶜ)
    (hu : ∀ S ∈ U.powersetCard m, |u S v| ≤ W)
    (hfull : ∀ S ∈ U.powersetCard m, (∀ w ∈ S, adj w v) → u S v = a) :
    DerivesN A (4 * m + 2) (W ^ (2 * m + 10))
      (zv U m u v ^ 2 - C (a ^ 2) * esymmOn U m ^ 2 * X v) := by
  set z := zv U m u v with hzdef
  have hz : coeffNorm1 z ≤ W ^ (m + 1) := coeffNorm1_zv_le hW hU hu
  have hzd : z.totalDegree ≤ m := totalDegree_zv_le U m u v
  have hz2d : (z ^ 2).totalDegree ≤ 2 * m := (totalDegree_pow _ 2).trans (by omega)
  have hW1 : (1 : ℝ) ≤ W := by linarith
  -- `∑_v (Z_v (1 - y_v))² ≥ 0`.
  have h₁ := DerivesN.ofIsSOS A (IsSOS.sq (z * (1 - X v))) (k := 4 * m + 2) (M := W ^ (2 * m + 8))
    ((totalDegree_pow _ 2).trans (by
      have := (totalDegree_mul z (1 - X v)).trans (add_le_add hzd ((totalDegree_sub _ _).trans
        (max_le (by simp) (by rw [totalDegree_X])) : (1 - X v : MvPolynomial σ ℝ).totalDegree ≤ 1))
      omega))
    (by
      refine (coeffNorm1_pow_le _ 2).trans ?_
      have h1 : coeffNorm1 (z * (1 - X v)) ≤ W ^ (m + 1) * 2 :=
        (coeffNorm1_mul_le _ _).trans (mul_le_mul hz (coeffNorm1_one_sub_X_le v)
          (coeffNorm1_nonneg _) (pow_nonneg_of_two_le hW _))
      calc coeffNorm1 (z * (1 - X v)) ^ 2 ≤ (W ^ (m + 1) * 2) ^ 2 :=
            pow_le_pow_left₀ (coeffNorm1_nonneg _) h1 2
        _ ≤ (W ^ (m + 1) * W) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hW (by positivity)) 2
        _ = W ^ (2 * m + 4) := by rw [← pow_succ, ← pow_mul]; ring_nf
        _ ≤ W ^ (2 * m + 8) := pow_le_pow_of_two_le hW (by omega))
  -- `Z_v² (y_v² - y_v) = 0`.
  have h₂ := ((hA.bool.eq v).mulSOS (IsSOS.sq z)).2
  have hz2 : coeffNorm1 (z ^ 2) ≤ W ^ (2 * m + 2) :=
    (coeffNorm1_pow_le _ 2).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) hz 2).trans_eq
      (by rw [← pow_mul]; ring_nf))
  -- The terms `(u_S(v) u_T(v) - a²) x_S x_T y_v` vanish.
  have h₃ := DerivesEq.sum (k := 4 * m) (U.powersetCard m) fun S hS ↦
    DerivesEq.sum (k := 4 * m) (U.powersetCard m) fun T hT ↦
      hA.kill hS hT hv (u S v * u T v - a ^ 2) (fun h₁ h₂ ↦ by
        rw [hfull S hS h₁, hfull T hT h₂]; ring)
  have hc : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m,
      (|u S v * u T v - a ^ 2| + 1) ^ 2 ≤ W ^ 8 := by
    intro S hS T hT
    have h1 := hu S hS
    have h2 := hu T hT
    have hp : |u S v * u T v| ≤ W * W := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
    have ha2 : a ^ 2 ≤ W * W := by
      rw [← sq_abs a]
      nlinarith [abs_nonneg a]
    have hW3 : W * W + W * W ≤ W ^ 3 := by nlinarith
    have : |u S v * u T v - a ^ 2| ≤ W ^ 3 := by
      rw [abs_le] at hp ⊢
      constructor <;> nlinarith [sq_nonneg a]
    exact add_one_sq_le_pow hW (abs_nonneg _) this
  have h₃n : ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
      (|u S v * u T v - a ^ 2| + 1) ^ 2 ≤ W ^ (2 * m + 8) := by
    have := sum_le_pow hW (U.powersetCard m) (a := 8 + m) (fun S hS ↦
      sum_le_pow hW (U.powersetCard m) (fun T hT ↦ hc S hS T hT) (card_powersetCard_le hU m))
      (card_powersetCard_le hU m)
    exact this.trans (pow_le_pow_of_two_le hW (by omega))
  have hsum := ((h₁.add (h₂.mono (by omega) (M' := W ^ (2 * m + 8))
    (by rw [mul_one]; exact hz2.trans (pow_le_pow_of_two_le hW (by omega))))).add
    (h₃.1.mono (by omega) h₃n))
  refine (hsum.mono le_rfl ?_).congr ?_
  · exact add_le_pow_succ hW (add_le_pow_succ hW le_rfl le_rfl) (pow_le_pow_of_two_le hW (by omega))
  · rw [sum_sum_coeff]
    ring

/-- The second half of the key lemma: `a² e_m² |y| ≤ ∑_v Z_v²`. -/
theorem stageB (hA : Axioms A U adj k) (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) {m : ℕ} {u : Finset σ → σ → ℝ} {a : ℝ} (ha : |a| ≤ W)
    (hu : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W)
    (hfull : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, (∀ w ∈ S, adj w v) → u S v = a) :
    DerivesN A (4 * m + 2) (W ^ (2 * m + 11))
      (∑ v ∈ Uᶜ, zv U m u v ^ 2 - C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, X v) := by
  have h := DerivesN.sum Uᶜ fun v hv ↦
    hA.stageB_v hW hU ha hv (fun S hS ↦ hu S hS v hv) (fun S hS ↦ hfull S hS v hv)
  refine (h.mono le_rfl ?_).congr ?_
  · have := sum_le_pow hW Uᶜ (a := 2 * m + 10) (c := 1) (fun _ _ ↦ le_rfl) (by simpa using hV)
    simpa using this
  · rw [sum_sub_distrib, mul_sum]

/-- `∑_v Z_v² = ∑_{S, T} B(S, T) x_S x_T` with `B(S, T) = ∑_v u_S(v) u_T(v)`. -/
theorem sum_zv_sq (U : Finset σ) (m : ℕ) (u : Finset σ → σ → ℝ) :
    ∑ v ∈ Uᶜ, zv U m u v ^ 2 = ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
      C (∑ v ∈ Uᶜ, u S v * u T v) * (xS S * xS T) := by
  have h : ∀ v, zv U m u v ^ 2 = ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
      C (u S v * u T v) * (xS S * xS T) := by
    intro v
    rw [zv, sq, sum_mul_sum]
    refine sum_congr rfl fun S _ ↦ sum_congr rfl fun T _ ↦ ?_
    rw [map_mul]
    ring
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun T _ ↦ ?_
  rw [map_sum, sum_mul]

/-- The first half of the key lemma: `∑_v Z_v² ≤ Γ e_m + Δ e_m²`. The diagonal terms are at
most `Γ x_S² = Γ x_S`, the others at most `Δ x_S x_T`, with `x_S x_T ≥ 0`. -/
theorem stageA (hA : Axioms A U adj k) (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) {m : ℕ} (hm : (m : ℝ) ≤ W) {u : Finset σ → σ → ℝ} {Γ Δ : ℝ}
    (hΓ : 0 ≤ Γ) (hΓW : Γ ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W)
    (hu : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W)
    (hdiag : ∀ S ∈ U.powersetCard m, ∑ v ∈ Uᶜ, u S v ^ 2 ≤ Γ)
    (hoff : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, u S v * u T v ≤ Δ) :
    DerivesN A (4 * m + 2) (W ^ (2 * m + 9))
      (C Γ * esymmOn U m + C Δ * esymmOn U m ^ 2 - ∑ v ∈ Uᶜ, zv U m u v ^ 2) := by
  set B : Finset σ → Finset σ → ℝ := fun S T ↦ ∑ v ∈ Uᶜ, u S v * u T v
  have hB : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, |B S T| ≤ W ^ 3 := by
    intro S hS T hT
    calc |B S T| ≤ ∑ v ∈ Uᶜ, |u S v * u T v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Uᶜ, W * W := sum_le_sum fun v hv ↦ by
          rw [abs_mul]
          exact mul_le_mul (hu S hS v hv) (hu T hT v hv) (abs_nonneg _) (by linarith)
      _ = Uᶜ.card * (W * W) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ W * (W * W) := mul_le_mul_of_nonneg_right hV (by positivity)
      _ = W ^ 3 := by ring
  have hW1 : (1 : ℝ) ≤ W := by linarith
  -- Each pair `(S, T)`.
  have hpair : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, DerivesN A (4 * m + 2) (W ^ 9)
      ((if S = T then C Γ * xS S else 0) + C Δ * (xS S * xS T) - C (B S T) * (xS S * xS T)) := by
    intro S hS T hT
    have hSc := (mem_powersetCard.1 hS).2
    have hTc := (mem_powersetCard.1 hT).2
    split_ifs with hST
    · subst hST
      have hBS : 0 ≤ B S S := sum_nonneg fun v _ ↦ mul_self_nonneg _
      have hBΓ : B S S ≤ Γ := by simpa [B, sq] using hdiag S hS
      have hx2 : coeffNorm1 (xS S ^ 2) ≤ 1 :=
        (coeffNorm1_pow_le _ 2).trans (pow_le_one₀ (coeffNorm1_nonneg _) (coeffNorm1_xS_le S))
      have hxd : (xS S ^ 2).totalDegree ≤ 2 * m :=
        (totalDegree_pow _ 2).trans (by have := totalDegree_xS_le S; omega)
      have h₁ := DerivesN.ofIsSOS A ((IsSOS.const (sub_nonneg.2 hBΓ)).mul (IsSOS.sq (xS S)))
        (k := 4 * m + 2) (M := W ^ 7)
        ((totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega))
        (by
          rw [coeffNorm1_C_mul, abs_of_nonneg (sub_nonneg.2 hBΓ)]
          calc (Γ - B S S) * coeffNorm1 (xS S ^ 2) ≤ W * 1 :=
                mul_le_mul (by linarith) hx2 (coeffNorm1_nonneg _) (by linarith)
            _ ≤ W ^ 7 := by rw [mul_one]; exact le_pow_of_two_le hW (by omega))
      have h₂ := DerivesN.ofIsSOS A ((IsSOS.const hΔ).mul (IsSOS.sq (xS S)))
        (k := 4 * m + 2) (M := W ^ 7)
        ((totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega))
        (by
          rw [coeffNorm1_C_mul, abs_of_nonneg hΔ]
          calc Δ * coeffNorm1 (xS S ^ 2) ≤ W * 1 :=
                mul_le_mul hΔW hx2 (coeffNorm1_nonneg _) (by linarith)
            _ ≤ W ^ 7 := by rw [mul_one]; exact le_pow_of_two_le hW (by omega))
      have h₃ := ((hA.bool.sq_sub S).2.smul hΓ).mono (k' := 4 * m + 2) (by omega)
        (M' := W ^ 7) (by
          rw [hSc]
          have h4 : 4 * (m : ℝ) ≤ W ^ 3 := by
            have : (4 : ℝ) ≤ W * W := by nlinarith
            calc 4 * (m : ℝ) ≤ W * W * W := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
              _ = W ^ 3 := by ring
          calc Γ * (4 * (m : ℝ)) ≤ W * W ^ 3 :=
                mul_le_mul hΓW h4 (by positivity) (by linarith)
            _ = W ^ 4 := by ring
            _ ≤ W ^ 7 := pow_le_pow_of_two_le hW (by omega))
      refine ((h₁.add h₂).add h₃).mono le_rfl
        (add_le_pow_succ hW (add_le_pow_succ hW le_rfl le_rfl) (pow_le_pow_of_two_le hW
          (by omega))) |>.congr ?_
      rw [map_sub]
      ring
    · have hBΔ : 0 ≤ Δ - B S T := sub_nonneg.2 (hoff S hS T hT hST)
      have h := ((hA.bool.mul_nonneg S T).smul hBΔ).mono (k' := 4 * m + 2) (by omega)
        (M' := W ^ 9) (by
          rw [hSc, hTc]
          have h1 : Δ - B S T ≤ W ^ 4 := by
            have := (abs_le.1 (hB S hS T hT)).1
            have h3 : W ^ 3 ≤ W ^ 4 := pow_le_pow_of_two_le hW (by omega)
            have h4 : W ≤ W ^ 3 := le_pow_of_two_le hW (by omega)
            nlinarith
          have h2 : 4 * ((m : ℝ) + m) + 1 ≤ W ^ 5 := by
            have h5 : (16 : ℝ) ≤ W ^ 4 := by
              calc (16 : ℝ) = 2 ^ 4 := by norm_num
                _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hW 4
            calc 4 * ((m : ℝ) + m) + 1 ≤ 9 * W := by nlinarith
              _ ≤ W ^ 4 * W := by nlinarith
              _ = W ^ 5 := by ring
          calc (Δ - B S T) * (4 * ((m : ℝ) + m) + 1) ≤ W ^ 4 * W ^ 5 :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = W ^ 9 := by rw [← pow_add])
      refine h.congr ?_
      rw [map_sub]
      ring
  have h := DerivesN.sum (U.powersetCard m) fun S hS ↦ DerivesN.sum (U.powersetCard m) fun T hT ↦
    hpair S hS T hT
  refine (h.mono le_rfl ?_).congr ?_
  · have := sum_le_pow hW (U.powersetCard m) (a := 9 + m)
      (fun S _ ↦ sum_le_pow hW (U.powersetCard m) (fun _ _ ↦ le_rfl)
        (card_powersetCard_le hU m)) (card_powersetCard_le hU m)
    exact this.trans (pow_le_pow_of_two_le hW (by omega))
  · rw [sum_zv_sq]
    have e1 : ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m,
        (if S = T then C Γ * xS S else 0) = C Γ * esymmOn U m := by
      rw [esymmOn, mul_sum]
      exact sum_congr rfl fun S hS ↦ by rw [sum_ite_eq]; simp [hS]
    have e2 : ∑ S ∈ U.powersetCard m, ∑ T ∈ U.powersetCard m, C Δ * (xS S * xS T) =
        C Δ * esymmOn U m ^ 2 := by
      rw [pow_two, esymmOn, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun S _ ↦ by rw [mul_sum]
    simp only [sum_add_distrib, sum_sub_distrib]
    rw [e1, e2]

/-- **The key lemma** [BKS23, `lem:biclique-certificate`, `lem:biclique-certificate-large-p`]:
`a² e_m² |y| ≤ Γ e_m + Δ e_m²`, from `∑_v (Z_v (1 - y_v))² ≥ 0`. -/
theorem main (hA : Axioms A U adj k) (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) {m : ℕ} (hm : (m : ℝ) ≤ W) {u : Finset σ → σ → ℝ} {a Γ Δ : ℝ}
    (ha : |a| ≤ W) (hΓ : 0 ≤ Γ) (hΓW : Γ ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W)
    (hu : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W)
    (hfull : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, (∀ w ∈ S, adj w v) → u S v = a)
    (hdiag : ∀ S ∈ U.powersetCard m, ∑ v ∈ Uᶜ, u S v ^ 2 ≤ Γ)
    (hoff : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, u S v * u T v ≤ Δ) :
    DerivesN A (4 * m + 2) (W ^ (2 * m + 12))
      (C Γ * esymmOn U m + C Δ * esymmOn U m ^ 2 -
        C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, X v) := by
  have h := (hA.stageA hW hU hV hm hΓ hΓW hΔ hΔW hu hdiag hoff).add
    (hA.stageB hW hU hV ha hu hfull)
  refine (h.mono le_rfl (add_le_pow_succ hW (pow_le_pow_of_two_le hW (by omega)) le_rfl)).congr ?_
  ring

/-- [BKS23, `lem:lower-bound-LHS-trick`]: `y_j |y| ≥ (k - d) y_j` if `j` has at most `d`
neighbours in `U`, since `y_j |x| = ∑_{u ∼ j} x_u y_j ≤ d y_j` and `|x| + |y| = k`. -/
theorem lower (hA : Axioms A U adj k) [DecidableRel adj] (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    {j : σ} (hj : j ∈ Uᶜ) {d : ℝ} (hd : ((U.filter (adj · j)).card : ℝ) ≤ d) (hdW : d ≤ W) :
    DerivesN A 4 (W ^ 7) (X j * ∑ v ∈ Uᶜ, X v - C (k - d) * X j) := by
  have hX : coeffNorm1 (X j : MvPolynomial σ ℝ) = 1 := coeffNorm1_X j
  -- `y_j (∑ᵢ xᵢ - k) = 0`.
  have h₁ := (hA.card.derivesEq (k := 1) (M := 1) ((totalDegree_sub _ _).trans
    (max_le (totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]) (by simp))) le_rfl).mul
      (X j)
  rw [totalDegree_X, hX] at h₁
  -- `x_u y_j ≤ y_j`, and `x_u y_j = 0` for the non-neighbours `u`.
  have hf : ∀ u ∈ U, DerivesN A 4 12 ((if adj u j then X j else 0) - X j * X u) := by
    intro u hu
    split_ifs with hadj
    · have hd1 : (X j - X j * X u : MvPolynomial σ ℝ).totalDegree ≤ 2 :=
        (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X]; omega)
          ((totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X])))
      have hn1 : coeffNorm1 (X j - X j * X u : MvPolynomial σ ℝ) ≤ 2 := by
        have h1 := coeffNorm1_sub_le (X j : MvPolynomial σ ℝ) (X j * X u)
        have h2 := coeffNorm1_mul_le (X j : MvPolynomial σ ℝ) (X u)
        rw [hX, coeffNorm1_X] at h2
        rw [hX] at h1
        linarith
      have e₁ := DerivesN.ofIsSOS A (IsSOS.sq (X j - X j * X u)) (k := 4) (M := 4)
        ((totalDegree_pow _ 2).trans (by omega))
        ((coeffNorm1_pow_le _ 2).trans (by
          nlinarith [coeffNorm1_nonneg (X j - X j * X u : MvPolynomial σ ℝ)]))
      have e₂ := ((hA.bool.eq u).mul (X j)).2
      rw [totalDegree_X, hX] at e₂
      have e₃ := ((hA.bool.eq j).mulSOS (IsSOS.sq (1 - X u))).2
      have hd₃ : ((1 - X u : MvPolynomial σ ℝ) ^ 2).totalDegree ≤ 2 :=
        (totalDegree_pow _ 2).trans (by
          have := (totalDegree_sub (1 : MvPolynomial σ ℝ) (X u)).trans
            (max_le (by simp) (by rw [totalDegree_X]))
          omega)
      have hn₃ : coeffNorm1 ((1 - X u : MvPolynomial σ ℝ) ^ 2) ≤ 4 :=
        (coeffNorm1_pow_le _ 2).trans (by
          nlinarith [coeffNorm1_one_sub_X_le (σ := σ) u,
            coeffNorm1_nonneg (1 - X u : MvPolynomial σ ℝ)])
      refine ((e₁.add (e₂.mono (by omega) le_rfl)).add (e₃.mono (by omega) (M' := 4)
        (by linarith))).mono le_rfl (by norm_num) |>.congr ?_
      ring
    · have := (hA.edge_eq hu hj hadj).2
      refine (this.mono (by omega) (by norm_num)).congr ?_
      ring
  have h₂ := DerivesN.sum U hf
  -- `(d - |N(j)|) y_j ≥ 0`.
  have hN : (0 : ℝ) ≤ d - (U.filter (adj · j)).card := sub_nonneg.2 hd
  have h₃ := (hA.bool.nonneg {j}).smul hN
  have hxj : xS {j} = (X j : MvPolynomial σ ℝ) := by simp [xS]
  rw [hxj, card_singleton] at h₃
  have hsum := (h₁.1.mono (k' := 4) (by omega) le_rfl).add (h₂.add (h₃.mono (by omega) le_rfl))
  refine (hsum.mono le_rfl ?_).congr ?_
  · rw [sum_const, nsmul_eq_mul]
    have h6 : (64 : ℝ) ≤ W ^ 6 := le_pow_of_le_two_pow hW (by norm_num)
    have h7 : 64 * W ≤ W ^ 7 := by
      have := mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ W)
      calc 64 * W = W * 64 := by ring
        _ ≤ W * W ^ 6 := this
        _ = W ^ 7 := by ring
    have hd' : d - ((U.filter (adj · j)).card : ℝ) ≤ W := by
      have : (0 : ℝ) ≤ (U.filter (adj · j)).card := Nat.cast_nonneg _
      linarith
    push_cast
    nlinarith
  · rw [sum_sub_distrib, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, ← mul_sum,
      ← sum_add_sum_compl U fun i ↦ (X i : MvPolynomial σ ℝ), map_sub, map_sub, map_natCast]
    ring

/-- `‖g‖₁ ≤ W^(2m + 5)` for the polynomial `g = Γ e_m + Δ e_m² - a² e_m² |y|` of the key lemma. -/
theorem coeffNorm1_main_le (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W) (hV : (Uᶜ.card : ℝ) ≤ W)
    {m : ℕ} {a Γ Δ : ℝ} (ha : |a| ≤ W) (hΓ : 0 ≤ Γ) (hΓW : Γ ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W) :
    coeffNorm1 (C Γ * esymmOn U m + C Δ * esymmOn U m ^ 2 -
      C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)) ≤ W ^ (2 * m + 5) := by
  have he := coeffNorm1_esymmOn_le hW hU m
  have he2 : coeffNorm1 (esymmOn U m ^ 2) ≤ W ^ (2 * m) :=
    (coeffNorm1_pow_le _ 2).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) he 2).trans_eq
      (by rw [← pow_mul, mul_comm]))
  have hY : coeffNorm1 (∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)) ≤ W :=
    (coeffNorm1_sum_le _ _).trans (by simpa [coeffNorm1_X] using hV)
  have ha2 : a ^ 2 ≤ W ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have t₁ : coeffNorm1 (C Γ * esymmOn U m) ≤ W ^ (2 * m + 3) := by
    rw [coeffNorm1_C_mul, abs_of_nonneg hΓ]
    calc Γ * coeffNorm1 (esymmOn U m) ≤ W * W ^ m := mul_le_mul hΓW he (coeffNorm1_nonneg _) hW0
      _ = W ^ (m + 1) := by ring
      _ ≤ _ := pow_le_pow_of_two_le hW (by omega)
  have t₂ : coeffNorm1 (C Δ * esymmOn U m ^ 2) ≤ W ^ (2 * m + 3) := by
    rw [coeffNorm1_C_mul, abs_of_nonneg hΔ]
    calc Δ * coeffNorm1 (esymmOn U m ^ 2) ≤ W * W ^ (2 * m) :=
          mul_le_mul hΔW he2 (coeffNorm1_nonneg _) hW0
      _ = W ^ (2 * m + 1) := by ring
      _ ≤ _ := pow_le_pow_of_two_le hW (by omega)
  have t₃ : coeffNorm1 (C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)) ≤
      W ^ (2 * m + 3) := by
    refine (coeffNorm1_mul_le _ _).trans ?_
    rw [coeffNorm1_C_mul, abs_of_nonneg (sq_nonneg a)]
    calc a ^ 2 * coeffNorm1 (esymmOn U m ^ 2) * coeffNorm1 (∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ))
        ≤ W ^ 2 * W ^ (2 * m) * W :=
          mul_le_mul (mul_le_mul ha2 he2 (coeffNorm1_nonneg _) (by positivity)) hY
            (coeffNorm1_nonneg _) (by positivity)
      _ = W ^ (2 * m + 3) := by ring
  calc _ ≤ coeffNorm1 (C Γ * esymmOn U m + C Δ * esymmOn U m ^ 2) +
        coeffNorm1 (C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)) :=
        coeffNorm1_sub_le _ _
    _ ≤ (coeffNorm1 (C Γ * esymmOn U m) + coeffNorm1 (C Δ * esymmOn U m ^ 2)) +
        coeffNorm1 (C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)) := by
        gcongr
        exact coeffNorm1_add_le _ _
    _ ≤ W ^ (2 * m + 5) := add_le_pow_succ hW (add_le_pow_succ hW t₁ t₂)
        (t₃.trans (pow_le_pow_of_two_le hW (by omega)))

theorem totalDegree_main_le (U : Finset σ) (m : ℕ) (a Γ Δ : ℝ) :
    (C Γ * esymmOn U m + C Δ * esymmOn U m ^ 2 -
      C (a ^ 2) * esymmOn U m ^ 2 * ∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)).totalDegree ≤
      2 * m + 1 := by
  have he := totalDegree_esymmOn_le U m
  have he2 : (esymmOn U m ^ 2).totalDegree ≤ 2 * m := (totalDegree_pow _ 2).trans (by omega)
  have hY : (∑ v ∈ Uᶜ, (X v : MvPolynomial σ ℝ)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  · exact (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans
      (by rw [totalDegree_C]; omega)) hY)

/-- [BKS23, `lem:biclique-certificate-final`], one vertex: `y_j e_m⁴ ≤ (Γ/λ)⁴` with
`λ = a² (k - d) - Δ`. The key lemma times `y_j` and the lower bound times `a² e_m²` give
`b² ≤ (Γ/λ) b` for `b = y_j e_m`; then cancellation. -/
theorem vertex (hA : Axioms A U adj k) [DecidableRel adj] (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) {m : ℕ} (hm : (m : ℝ) ≤ W) {u : Finset σ → σ → ℝ} {a Γ Δ d : ℝ}
    (ha : |a| ≤ W) (hΓ : 0 ≤ Γ) (hΓW : Γ ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W) (hdW : d ≤ W)
    (hu : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W)
    (hfull : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, (∀ w ∈ S, adj w v) → u S v = a)
    (hdiag : ∀ S ∈ U.powersetCard m, ∑ v ∈ Uᶜ, u S v ^ 2 ≤ Γ)
    (hoff : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, u S v * u T v ≤ Δ)
    (hlam : 0 < a ^ 2 * (k - d) - Δ) (hlamW : 1 ≤ W * (a ^ 2 * (k - d) - Δ))
    {j : σ} (hj : j ∈ Uᶜ) (hd : ((U.filter (adj · j)).card : ℝ) ≤ d) :
    DerivesN A (6 * m + 6) (W ^ (6 * m + 24))
      (C ((Γ / (a ^ 2 * (k - d) - Δ)) ^ 4) - esymmOn U m ^ 4 * X j) := by
  set lam := a ^ 2 * (k - d) - Δ with hlamdef
  set c := Γ / lam with hcdef
  set e := esymmOn U m with hedef
  set Y : MvPolynomial σ ℝ := ∑ v ∈ Uᶜ, X v with hYdef
  set g := C Γ * e + C Δ * e ^ 2 - C (a ^ 2) * e ^ 2 * Y with hgdef
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hX : coeffNorm1 (X j : MvPolynomial σ ℝ) = 1 := coeffNorm1_X j
  have hX2 : coeffNorm1 (X j ^ 2 : MvPolynomial σ ℝ) ≤ 1 := coeffNorm1_X_sq_le j
  have he : coeffNorm1 e ≤ W ^ m := coeffNorm1_esymmOn_le hW hU m
  have hed : e.totalDegree ≤ m := totalDegree_esymmOn_le U m
  have he2 : coeffNorm1 (e ^ 2) ≤ W ^ (2 * m) :=
    (coeffNorm1_pow_le _ 2).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) he 2).trans_eq
      (by rw [← pow_mul, mul_comm]))
  have he2d : (e ^ 2).totalDegree ≤ 2 * m := (totalDegree_pow _ 2).trans (by omega)
  have hinvW : 1 / lam ≤ W := by rw [div_le_iff₀ hlam]; linarith
  have hc0 : 0 ≤ c := div_nonneg hΓ hlam.le
  have hcW : c ≤ W ^ 2 := by
    rw [hcdef, div_eq_mul_one_div, pow_two]
    exact mul_le_mul hΓW hinvW (by positivity) hW0
  -- (C1) `y_j g ≥ 0`, from `y_j² g ≥ 0` and `(y_j² - y_j) g = 0`.
  have hg := hA.main hW hU hV hm ha hΓ hΓW hΔ hΔW hu hfull hdiag hoff
  have c1a := hg.mulSOS (IsSOS.sq (X j))
  have c1b := ((hA.bool.eq j).mul g).2
  have hgd : g.totalDegree ≤ 2 * m + 1 := totalDegree_main_le U m a Γ Δ
  have hgn : coeffNorm1 g ≤ W ^ (2 * m + 5) := coeffNorm1_main_le hW hU hV ha hΓ hΓW hΔ hΔW
  have c1 := (c1a.mono (k' := 4 * m + 4) (by rw [totalDegree_X_pow]; omega) (M' := W ^ (4 * m + 12))
    (by
      calc coeffNorm1 (X j ^ 2 : MvPolynomial σ ℝ) * W ^ (2 * m + 12) ≤ 1 * W ^ (2 * m + 12) :=
            mul_le_mul_of_nonneg_right hX2 (pow_nonneg_of_two_le hW _)
        _ ≤ _ := by rw [one_mul]; exact pow_le_pow_of_two_le hW (by omega))).add
    (c1b.mono (by omega) (M' := W ^ (4 * m + 12)) (by
      rw [mul_one]
      have := add_one_sq_le_pow hW (coeffNorm1_nonneg g) hgn
      exact this.trans (pow_le_pow_of_two_le hW (by omega))))
  -- (C2) `a² e_m² (y_j |y| - (k - d) y_j) ≥ 0`.
  have hl := hA.lower hW hU hj hd hdW
  have c2 := (hl.mulSOS (IsSOS.sq e)).smul (sq_nonneg a)
  have ha2 : a ^ 2 ≤ W ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have c2' := c2.mono (k' := 4 * m + 4) (by omega) (M' := W ^ (4 * m + 12)) (by
    calc a ^ 2 * (coeffNorm1 (e ^ 2) * W ^ 7) ≤ W ^ 2 * (W ^ (2 * m) * W ^ 7) :=
          mul_le_mul ha2 (mul_le_mul_of_nonneg_right he2 (pow_nonneg_of_two_le hW _))
            (mul_nonneg (coeffNorm1_nonneg _) (pow_nonneg_of_two_le hW _)) (by positivity)
      _ = W ^ (2 * m + 9) := by ring
      _ ≤ _ := pow_le_pow_of_two_le hW (by omega))
  -- (C3, C4) `c b - b² ≥ 0` for `b = e_m y_j`.
  have c4 := (c1.add c2').smul (one_div_nonneg.2 hlam.le)
  have c5 := c4.add (((hA.bool.eq j).mulSOS (IsSOS.sq e)).2.mono (k' := 4 * m + 4) (by omega)
    le_rfl)
  have hinv : C (1 / lam) * C lam = (1 : MvPolynomial σ ℝ) := by
    rw [← C_mul, one_div_mul_cancel hlam.ne', C_1]
  have hcC : (C c : MvPolynomial σ ℝ) = C (1 / lam) * C Γ := by rw [← C_mul, hcdef]; ring_nf
  have hlamC : (C lam : MvPolynomial σ ℝ) = C (a ^ 2) * C (k - d) - C Δ := by
    rw [hlamdef, map_sub, map_mul]
  set b := e * X j with hbdef
  have c5' : DerivesN A (4 * m + 4) (W ^ (4 * m + 16)) (C c * b - b ^ 2) := by
    refine (c5.mono le_rfl (M' := W ^ (4 * m + 16)) ?_).congr ?_
    · have h1 : 1 / lam * (W ^ (4 * m + 12) + W ^ (4 * m + 12) + W ^ (4 * m + 12)) ≤
          W ^ (4 * m + 15) := by
        calc 1 / lam * (W ^ (4 * m + 12) + W ^ (4 * m + 12) + W ^ (4 * m + 12))
            ≤ W * W ^ (4 * m + 14) :=
              mul_le_mul hinvW (add_le_pow_succ hW (add_le_pow_succ hW le_rfl le_rfl)
                (pow_le_pow_of_two_le hW (by omega))) (by positivity) hW0
          _ = W ^ (4 * m + 15) := by ring
      have h2 : coeffNorm1 (e ^ 2) * 1 ≤ W ^ (4 * m + 15) := by
        rw [mul_one]; exact he2.trans (pow_le_pow_of_two_le hW (by omega))
      exact add_le_pow_succ hW h1 h2
    · rw [hcC, hgdef]
      linear_combination (-(e ^ 2 * X j)) * hinv + (C (1 / lam) * e ^ 2 * X j) * hlamC
  -- (C6) Cancellation: `c⁴ - b⁴ = (c² + b²)(c - b)² + 2 (c² + b²)(c b - b²)`.
  have hbd : b.totalDegree ≤ m + 1 :=
    (totalDegree_mul _ _).trans (add_le_add hed (by rw [totalDegree_X]))
  have hbn : coeffNorm1 b ≤ W ^ m :=
    (coeffNorm1_mul_le _ _).trans (by rw [hX, mul_one]; exact he)
  have hq : IsSOS (C (c ^ 2) + b ^ 2) := (IsSOS.const (sq_nonneg c)).add (IsSOS.sq b)
  have hqd : (C (c ^ 2) + b ^ 2).totalDegree ≤ 2 * m + 2 :=
    (totalDegree_add _ _).trans (max_le (by rw [totalDegree_C]; omega)
      ((totalDegree_pow _ 2).trans (by omega)))
  have hqn : coeffNorm1 (C (c ^ 2) + b ^ 2) ≤ W ^ (2 * m + 5) := by
    refine (coeffNorm1_add_le _ _).trans (add_le_pow_succ hW ?_ ?_)
    · rw [coeffNorm1_C, abs_of_nonneg (sq_nonneg c)]
      calc c ^ 2 ≤ (W ^ 2) ^ 2 := pow_le_pow_left₀ hc0 hcW 2
        _ = W ^ 4 := by ring
        _ ≤ _ := pow_le_pow_of_two_le hW (by omega)
    · refine (coeffNorm1_pow_le _ 2).trans ?_
      calc coeffNorm1 b ^ 2 ≤ (W ^ m) ^ 2 := pow_le_pow_left₀ (coeffNorm1_nonneg _) hbn 2
        _ = W ^ (2 * m) := by ring
        _ ≤ _ := pow_le_pow_of_two_le hW (by omega)
  have hcbd : (C c - b).totalDegree ≤ m + 1 :=
    (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) hbd)
  have hcb2 : ((C c - b) ^ 2).totalDegree ≤ 2 * m + 2 := (totalDegree_pow _ 2).trans (by omega)
  have c6a := DerivesN.ofIsSOS A (hq.mul (IsSOS.sq (C c - b))) (k := 6 * m + 6)
    (M := W ^ (6 * m + 22))
    ((totalDegree_mul _ _).trans (by omega))
    (by
      refine (coeffNorm1_mul_le _ _).trans ?_
      have h1 : coeffNorm1 ((C c - b) ^ 2) ≤ W ^ (2 * m + 6) := by
        refine (coeffNorm1_pow_le _ 2).trans ?_
        have : coeffNorm1 (C c - b) ≤ W ^ (m + 3) := by
          refine (coeffNorm1_sub_le _ _).trans ?_
          rw [coeffNorm1_C, abs_of_nonneg hc0]
          exact add_le_pow_succ hW (hcW.trans (pow_le_pow_of_two_le hW (by omega)))
            (hbn.trans (pow_le_pow_of_two_le hW (by omega)))
        calc coeffNorm1 (C c - b) ^ 2 ≤ (W ^ (m + 3)) ^ 2 :=
              pow_le_pow_left₀ (coeffNorm1_nonneg _) this 2
          _ = W ^ (2 * m + 6) := by ring
      calc coeffNorm1 (C (c ^ 2) + b ^ 2) * coeffNorm1 ((C c - b) ^ 2)
          ≤ W ^ (2 * m + 5) * W ^ (2 * m + 6) :=
            mul_le_mul hqn h1 (coeffNorm1_nonneg _) (pow_nonneg_of_two_le hW _)
        _ = W ^ (4 * m + 11) := by ring
        _ ≤ _ := pow_le_pow_of_two_le hW (by omega))
  have c6b := c5'.mulSOS ((IsSOS.const (by norm_num : (0 : ℝ) ≤ 2)).mul hq)
  have h2q : (C (2 : ℝ) * (C (c ^ 2) + b ^ 2)).totalDegree ≤ 2 * m + 2 :=
    (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  have c6b' := c6b.mono (k' := 6 * m + 6) (by omega) (M' := W ^ (6 * m + 22)) (by
      have h2 : coeffNorm1 (C (2 : ℝ) * (C (c ^ 2) + b ^ 2)) ≤ W ^ (2 * m + 6) := by
        rw [coeffNorm1_C_mul, abs_two]
        calc 2 * coeffNorm1 (C (c ^ 2) + b ^ 2) ≤ W * W ^ (2 * m + 5) :=
              mul_le_mul hW hqn (coeffNorm1_nonneg _) hW0
          _ = W ^ (2 * m + 6) := by ring
      calc coeffNorm1 (C (2 : ℝ) * (C (c ^ 2) + b ^ 2)) * W ^ (4 * m + 16)
          ≤ W ^ (2 * m + 6) * W ^ (4 * m + 16) :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg_of_two_le hW _)
        _ = W ^ (6 * m + 22) := by ring)
  -- (C7) `b⁴ = e_m⁴ y_j`: `y⁴ - y = ((y + 1/2)² + 3/4)(y² - y)`.
  have hr : IsSOS (e ^ 4 * ((X j + C (1 / 2 : ℝ)) ^ 2 + C (3 / 4))) := by
    have : e ^ 4 = (e ^ 2) ^ 2 := by ring
    rw [this]
    exact (IsSOS.sq _).mul ((IsSOS.sq _).add (IsSOS.const (by norm_num)))
  have c7 := ((hA.bool.eq j).mulSOS hr).1
  have c7' := c7.mono (k' := 6 * m + 6) (by
    have h1 : (e ^ 4).totalDegree ≤ 4 * m := (totalDegree_pow _ 4).trans (by omega)
    have h2 : ((X j + C (1 / 2 : ℝ)) ^ 2 + C (3 / 4) : MvPolynomial σ ℝ).totalDegree ≤ 2 :=
      (totalDegree_add _ _).trans (max_le ((totalDegree_pow _ 2).trans (by
        have := (totalDegree_add (X j : MvPolynomial σ ℝ) (C (1 / 2))).trans
          (max_le (by rw [totalDegree_X]) (by rw [totalDegree_C]; omega))
        omega)) (by rw [totalDegree_C]; omega))
    have := (totalDegree_mul (e ^ 4) ((X j + C (1 / 2 : ℝ)) ^ 2 + C (3 / 4))).trans
      (add_le_add h1 h2)
    omega) (M' := W ^ (6 * m + 22)) (by
      rw [mul_one]
      refine (coeffNorm1_mul_le _ _).trans ?_
      have h1 : coeffNorm1 (e ^ 4) ≤ W ^ (4 * m) :=
        (coeffNorm1_pow_le _ 4).trans ((pow_le_pow_left₀ (coeffNorm1_nonneg _) he 4).trans_eq
          (by rw [← pow_mul, mul_comm]))
      have h2 : coeffNorm1 ((X j + C (1 / 2 : ℝ)) ^ 2 + C (3 / 4)) ≤ W ^ 2 := by
        refine (coeffNorm1_add_le _ _).trans ?_
        rw [coeffNorm1_C, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
        have : coeffNorm1 (X j + C (1 / 2 : ℝ)) ≤ 3 / 2 := by
          refine (coeffNorm1_add_le _ _).trans ?_
          rw [hX, coeffNorm1_C, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          norm_num
        have := (coeffNorm1_pow_le (X j + C (1 / 2 : ℝ)) 2).trans
          (pow_le_pow_left₀ (coeffNorm1_nonneg _) this 2)
        nlinarith
      calc coeffNorm1 (e ^ 4) * coeffNorm1 ((X j + C (1 / 2 : ℝ)) ^ 2 + C (3 / 4))
          ≤ W ^ (4 * m) * W ^ 2 :=
            mul_le_mul h1 h2 (coeffNorm1_nonneg _) (pow_nonneg_of_two_le hW _)
        _ = W ^ (4 * m + 2) := by ring
        _ ≤ _ := pow_le_pow_of_two_le hW (by omega))
  refine ((c6a.add c6b').add c7').mono le_rfl
    (add_le_pow_succ hW (add_le_pow_succ hW le_rfl le_rfl)
      (pow_le_pow_of_two_le hW (by omega))) |>.congr ?_
  have h4 : (C (c ^ 4) : MvPolynomial σ ℝ) = C c ^ 4 := map_pow C c 4
  have h2 : (C (c ^ 2) : MvPolynomial σ ℝ) = C c ^ 2 := map_pow C c 2
  have hA' : (C (1 / 2 : ℝ) : MvPolynomial σ ℝ) * 2 = 1 := by
    rw [show (2 : MvPolynomial σ ℝ) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  have hB' : (C (1 / 2 : ℝ) : MvPolynomial σ ℝ) * C (1 / 2) + C (3 / 4) = 1 := by
    rw [← C_mul, ← C_add]; norm_num
  have h22 : C (2 : ℝ) = (2 : MvPolynomial σ ℝ) := map_ofNat C 2
  rw [h4, h2, h22, hbdef]
  linear_combination (e ^ 4 * X j * (X j ^ 2 - X j)) * hA' + (e ^ 4 * (X j ^ 2 - X j)) * hB'

/-- **The certificate at level `m`** [BKS23, `lem:biclique-certificate-final`,
`lem:biclique-certificate-final-large-p`]: `e_m⁴ |y| ≤ |V| (Γ/λ)⁴` with `λ = a² (k - d) - Δ`,
in degree `6m + 6`. -/
theorem level (hA : Axioms A U adj k) [DecidableRel adj] (hW : 2 ≤ W) (hU : (U.card : ℝ) ≤ W)
    (hV : (Uᶜ.card : ℝ) ≤ W) {m : ℕ} (hm : (m : ℝ) ≤ W) {u : Finset σ → σ → ℝ} {a Γ Δ d : ℝ}
    (ha : |a| ≤ W) (hΓ : 0 ≤ Γ) (hΓW : Γ ≤ W) (hΔ : 0 ≤ Δ) (hΔW : Δ ≤ W) (hdW : d ≤ W)
    (hu : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, |u S v| ≤ W)
    (hfull : ∀ S ∈ U.powersetCard m, ∀ v ∈ Uᶜ, (∀ w ∈ S, adj w v) → u S v = a)
    (hdiag : ∀ S ∈ U.powersetCard m, ∑ v ∈ Uᶜ, u S v ^ 2 ≤ Γ)
    (hoff : ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      ∑ v ∈ Uᶜ, u S v * u T v ≤ Δ)
    (hd : ∀ v ∈ Uᶜ, ((U.filter (adj · v)).card : ℝ) ≤ d)
    (hlam : 0 < a ^ 2 * (k - d) - Δ) (hlamW : 1 ≤ W * (a ^ 2 * (k - d) - Δ)) :
    DerivesN A (6 * m + 6) (W ^ (6 * m + 25))
      (C (Uᶜ.card * (Γ / (a ^ 2 * (k - d) - Δ)) ^ 4) - esymmOn U m ^ 4 * ∑ v ∈ Uᶜ, X v) := by
  have h := DerivesN.sum Uᶜ fun j hj ↦
    hA.vertex hW hU hV hm ha hΓ hΓW hΔ hΔW hdW hu hfull hdiag hoff hlam hlamW hj (hd j hj)
  refine (h.mono le_rfl ?_).congr ?_
  · have := sum_le_pow hW Uᶜ (a := 6 * m + 24) (c := 1) (fun _ _ ↦ le_rfl) (by simpa using hV)
    simpa using this
  · rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum, map_mul, map_natCast]

end Axioms

end BKS23.Biclique
