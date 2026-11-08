module

public import BS23.SmallRadius.Program
public import Background.SumOfSquares.IdealSOS

/-!
# Unpacking the moment axiom

The program of one round of the small-radius algorithm (`BS23.SmallRadius.problem`) states the
moment inequality `(∑_α C_α v^α)^m ≤ K σ^m B̃(v)` through its coefficients: the constraints
`Mom_γ = 0` say that `K σ^m B̃(v) - (∑_α C_α v^α)^m` is the Gram form `∑_c (∑_β P_{βc} v^β)²`, and
the constraints `Coef_α = 0` and `σ = ∑ᵢ wᵢ` say what `C_α` and `σ` are. Substituting polynomials
`φ` of degree at most `1` for `v`, the inequality comes back in the program variables, as a sum
of squares plus an explicit combination of the equality constraints
(`SoS.SosPlusIdeal`):

  `K (∑ᵢ wᵢ)^m B̃(φ) - (∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s})^m ≥ 0`,

where `⟨zᵢ - μ, φ⟩ = ∑ₐ (zᵢₐ - μₐ) φₐ` and `B̃(φ) = ∑_γ b_γ φ^γ`.

1. By the moment identity (`BS23.SmallRadius.Lay.mom_identity_X`),
   `K σ^m B̃(φ) - X'^m = ∑_c (∑_β P_{βc} φ^β)² + ∑_γ φ^γ Mom_γ` with `X' = ∑_α C_α φ^α`.
2. By the coefficient identity (`BS23.SmallRadius.Lay.coef_identity_X`),
   `X' - Y' = ∑_α φ^α Coef_α` with `Y' = ∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s}`, so
   `X'^m - Y'^m = (∑_{i<m} X'^i Y'^{m-1-i}) (X' - Y')` lies in the ideal.
3. In the same way `(∑ᵢ wᵢ)^m - σ^m` is a multiple of `σ - ∑ᵢ wᵢ`.

## Main statements

* `BS23.SmallRadius.moment_axiom`: for `φ` with `deg φₐ ≤ 1` and `‖φₐ‖₁ ≤ W` (`W ≥ 1`), data with
  `|zᵢₐ| ≤ Z₀` and coefficients with `|b_γ| ≤ b₀`, when nothing is cut
  (`BS23.SmallRadius.Fits`) and `s ≥ 1`: the inequality above holds in degree `5t` (or any
  `k ≥ 5t`) with norm `(m + 2) (1 + |K| b₀) (n + 1)^m ((d + 1)(Z₀ + 1) W)^{3t}`.
* `BS23.SmallRadius.moment_axiom_bOf`: the same with the coefficients `b = bOf Y` of
  `B̃(φ) = (n_Y t^t)⁻¹ ∑ⱼ ⟨Yⱼ, φ⟩^{2t}` (`BS23.SmallRadius.bOf`).
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg Finset

/-! ### Helpers -/

section Helpers

variable {ι : Type*}

theorem sum_getD_fin {d : ℕ} {e : List ℕ} (he : e.length = d) :
    ∑ a : Fin d, e.getD a 0 = e.sum := by
  subst he
  simp [List.getD_eq_getElem?_getD]

/-- `deg φ^e ≤ |e|` when every `φₐ` has degree at most `1`. -/
theorem totalDegree_powE_le {d : ℕ} {φ : Fin d → MvPolynomial ι ℝ}
    (hφ : ∀ a, (φ a).totalDegree ≤ 1) {e : List ℕ} (he : e.length = d) :
    (powE φ e).totalDegree ≤ e.sum := by
  rw [← sum_getD_fin he]
  unfold powE
  refine (totalDegree_finsetProd _ _).trans (sum_le_sum fun a _ => ?_)
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e.getD a 0) (hφ a))

/-- `‖φ^e‖₁ ≤ W^|e|` when every `φₐ` has `‖·‖₁ ≤ W`. -/
theorem coeffNorm1_powE_le {d : ℕ} {φ : Fin d → MvPolynomial ι ℝ} {W : ℝ}
    (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) {e : List ℕ} (he : e.length = d) :
    coeffNorm1 (powE φ e) ≤ W ^ e.sum := by
  rw [← sum_getD_fin he, ← prod_pow_eq_pow_sum]
  unfold powE
  refine (coeffNorm1_prod_le _ _).trans
    (Finset.prod_le_prod₀ (fun a _ => coeffNorm1_nonneg _) fun a _ => ?_)
  exact (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hφ a) _)

/-- The degree of `∑_{i<m} x^i y^{m-1-i}`. -/
theorem totalDegree_geom_le {x y : MvPolynomial ι ℝ} {D : ℕ} (hx : x.totalDegree ≤ D)
    (hy : y.totalDegree ≤ D) (m : ℕ) :
    (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)).totalDegree ≤ (m - 1) * D := by
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi := mem_range.1 hi
  have h1 := (totalDegree_pow x i).trans (Nat.mul_le_mul_left i hx)
  have h2 := (totalDegree_pow y (m - 1 - i)).trans (Nat.mul_le_mul_left (m - 1 - i) hy)
  refine (totalDegree_mul _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  rw [← add_mul]
  congr 1
  omega

/-- The norm of `∑_{i<m} x^i y^{m-1-i}`. -/
theorem coeffNorm1_geom_le {x y : MvPolynomial ι ℝ} {Θ : ℝ} (hx : coeffNorm1 x ≤ Θ)
    (hy : coeffNorm1 y ≤ Θ) (m : ℕ) :
    coeffNorm1 (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) ≤ m * Θ ^ (m - 1) := by
  have hΘ : 0 ≤ Θ := (coeffNorm1_nonneg _).trans hx
  refine (coeffNorm1_sum_le_card_mul _ _ fun i hi => ?_).trans (by rw [card_range])
  have hi := mem_range.1 hi
  calc coeffNorm1 (x ^ i * y ^ (m - 1 - i))
      ≤ coeffNorm1 (x ^ i) * coeffNorm1 (y ^ (m - 1 - i)) := coeffNorm1_mul_le _ _
    _ ≤ Θ ^ i * Θ ^ (m - 1 - i) :=
        mul_le_mul ((coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hx _))
          ((coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hy _))
          (coeffNorm1_nonneg _) (pow_nonneg hΘ _)
    _ = Θ ^ (m - 1) := by
        rw [← pow_add]
        congr 1
        omega

/-- A duplicate-free list of exponent vectors in `d` variables of degree at most `D` has at most
`(d + 1)^D` entries. -/
theorem length_le_of_mem_all {l : List (List ℕ)} {d D : ℕ} (hl : l.Nodup)
    (h : ∀ e ∈ l, e.length = d ∧ e.sum ≤ D) : l.length ≤ (d + 1) ^ D :=
  ((hl.subperm fun e he => Mono.mem_all.2 (h e he)).length_le).trans (Mono.length_all_le d D)

end Helpers

/-! ### The pieces: degrees and norms -/

namespace Lay

variable {L : Lay} {Gs : List (List ℕ)} {s t m Lb : ℕ} {φ : Fin L.d → MvPolynomial (Fin L.N) ℝ}
  {W : ℝ}

/-- `deg ∑_α C_α φ^α ≤ 2s + 1`. -/
theorem totalDegree_cSum_le (hL : L.Good Gs s t m Lb) (hφ : ∀ a, (φ a).totalDegree ≤ 1) :
    (∑ j, X (L.cv j) * powE φ (L.As.get j)).totalDegree ≤ 2 * s + 1 := by
  refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
  have hm := (hL.memA _).1 (List.get_mem L.As j)
  have := (totalDegree_powE_le hφ hm.1).trans hm.2
  rw [totalDegree_X]
  omega

/-- `‖∑_α C_α φ^α‖₁ ≤ |𝒜| W^{2s}`. -/
theorem coeffNorm1_cSum_le (hL : L.Good Gs s t m Lb) (hW : 1 ≤ W)
    (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) :
    coeffNorm1 (∑ j, X (L.cv j) * powE φ (L.As.get j)) ≤ L.A * W ^ (2 * s) := by
  refine (coeffNorm1_sum_le_card_mul _ _ (b := W ^ (2 * s)) fun j _ => ?_).trans (by simp)
  have hm := (hL.memA _).1 (List.get_mem L.As j)
  refine (coeffNorm1_mul_le _ _).trans ?_
  rw [coeffNorm1_X, one_mul]
  exact (coeffNorm1_powE_le hφ hm.1).trans (pow_le_pow_right₀ hW hm.2)

/-- `deg ⟨zᵢ - μ, φ⟩ ≤ 2`. -/
theorem totalDegree_linZ_le (z : Fin L.n → Fin L.d → ℚ) (hφ : ∀ a, (φ a).totalDegree ≤ 1)
    (i : Fin L.n) : (∑ a, (C (z i a : ℝ) - X (L.mv a)) * φ a).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun a _ => (totalDegree_mul _ _).trans ?_
  have h1 : (C (z i a : ℝ) - X (L.mv a)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) (by rw [totalDegree_X]))
  have := hφ a
  omega

/-- `‖⟨zᵢ - μ, φ⟩‖₁ ≤ d (Z₀ + 1) W`. -/
theorem coeffNorm1_linZ_le (z : Fin L.n → Fin L.d → ℚ) {Z₀ : ℝ}
    (hz : ∀ i a, |(z i a : ℝ)| ≤ Z₀) (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) (i : Fin L.n) :
    coeffNorm1 (∑ a, (C (z i a : ℝ) - X (L.mv a)) * φ a) ≤ L.d * ((Z₀ + 1) * W) := by
  refine (coeffNorm1_sum_le_card_mul _ _ (b := (Z₀ + 1) * W) fun a _ => ?_).trans (by simp)
  refine (coeffNorm1_mul_le _ _).trans (mul_le_mul ?_ (hφ a) (coeffNorm1_nonneg _) ?_)
  · refine (coeffNorm1_sub_le _ _).trans ?_
    rw [coeffNorm1_C, coeffNorm1_X]
    linarith [hz i a]
  · linarith [abs_nonneg (z i a : ℝ), hz i a]

/-- `deg ∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s} ≤ 4s + 1`. -/
theorem totalDegree_ySum_le (z : Fin L.n → Fin L.d → ℚ) (hφ : ∀ a, (φ a).totalDegree ≤ 1) :
    (∑ i, X (L.wv i) * (∑ a, (C (z i a : ℝ) - X (L.mv a)) * φ a) ^ (2 * s)).totalDegree ≤
      4 * s + 1 := by
  refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
  have := (totalDegree_pow _ (2 * s)).trans
    (Nat.mul_le_mul_left (2 * s) (totalDegree_linZ_le z hφ i))
  rw [totalDegree_X]
  omega

/-- `‖∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s}‖₁ ≤ n (d (Z₀ + 1) W)^{2s}`. -/
theorem coeffNorm1_ySum_le (z : Fin L.n → Fin L.d → ℚ) {Z₀ : ℝ}
    (hz : ∀ i a, |(z i a : ℝ)| ≤ Z₀) (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) :
    coeffNorm1 (∑ i, X (L.wv i) * (∑ a, (C (z i a : ℝ) - X (L.mv a)) * φ a) ^ (2 * s)) ≤
      L.n * (L.d * ((Z₀ + 1) * W)) ^ (2 * s) := by
  refine (coeffNorm1_sum_le_card_mul _ _ (b := (L.d * ((Z₀ + 1) * W)) ^ (2 * s))
    fun i _ => ?_).trans (by simp)
  refine (coeffNorm1_mul_le _ _).trans ?_
  rw [coeffNorm1_X, one_mul]
  exact (coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (coeffNorm1_nonneg _) (coeffNorm1_linZ_le z hz hφ i) _)

/-- The Gram form `∑_c (∑_β P_{βc} φ^β)²` is a sum of squares. -/
theorem isSumSq_gram (φ : Fin L.d → MvPolynomial (Fin L.N) ℝ) :
    IsSumSq (∑ c, (∑ β, X (L.pv β c) * powE φ (L.Bs.get β)) ^ 2) :=
  IsSumSq.sum fun _ _ => isSumSq_sq _

/-- `deg ∑_c (∑_β P_{βc} φ^β)² ≤ 2t + 2`. -/
theorem totalDegree_gram_le (hL : L.Good Gs s t m Lb) (hφ : ∀ a, (φ a).totalDegree ≤ 1) :
    (∑ c, (∑ β, X (L.pv β c) * powE φ (L.Bs.get β)) ^ 2).totalDegree ≤ 2 * t + 2 := by
  refine totalDegree_finsetSum_le fun c _ => (totalDegree_pow _ 2).trans ?_
  have : (∑ β, X (L.pv β c) * powE φ (L.Bs.get β)).totalDegree ≤ t + 1 := by
    refine totalDegree_finsetSum_le fun β _ => (totalDegree_mul _ _).trans ?_
    have hm := (hL.memB _).1 (List.get_mem L.Bs β)
    have := (totalDegree_powE_le hφ hm.1).trans hm.2
    rw [totalDegree_X]
    omega
  omega

/-- `‖∑_c (∑_β P_{βc} φ^β)²‖₁ ≤ |ℬ| (|ℬ| W^t)²`. -/
theorem coeffNorm1_gram_le (hL : L.Good Gs s t m Lb) (hW : 1 ≤ W)
    (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) :
    coeffNorm1 (∑ c, (∑ β, X (L.pv β c) * powE φ (L.Bs.get β)) ^ 2) ≤
      L.B * (L.B * W ^ t) ^ 2 := by
  refine (coeffNorm1_sum_le_card_mul _ _ (b := (L.B * W ^ t) ^ 2) fun c _ => ?_).trans (by simp)
  refine (coeffNorm1_pow_le _ 2).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) ?_ 2)
  refine (coeffNorm1_sum_le_card_mul _ _ (b := W ^ t) fun β _ => ?_).trans (by simp)
  have hm := (hL.memB _).1 (List.get_mem L.Bs β)
  refine (coeffNorm1_mul_le _ _).trans ?_
  rw [coeffNorm1_X, one_mul]
  exact (coeffNorm1_powE_le hφ hm.1).trans (pow_le_pow_right₀ hW hm.2)

/-- `deg B̃(φ) ≤ 2t`. -/
theorem totalDegree_bTil_le (hL : L.Good Gs s t m Lb) (b : List ℕ → ℚ)
    (hφ : ∀ a, (φ a).totalDegree ≤ 1) :
    (Gs.map fun γ => C (b γ : ℝ) * powE φ γ).sum.totalDegree ≤ 2 * t := by
  rw [← List.sum_toFinset _ hL.nodupG]
  refine totalDegree_finsetSum_le fun γ hγ => (totalDegree_mul _ _).trans ?_
  have hm := (hL.memG γ).1 (List.mem_toFinset.1 hγ)
  rw [totalDegree_C, zero_add]
  exact (totalDegree_powE_le hφ hm.1).trans hm.2

/-- `‖B̃(φ)‖₁ ≤ |Gs| b₀ W^{2t}`. -/
theorem coeffNorm1_bTil_le (hL : L.Good Gs s t m Lb) (b : List ℕ → ℚ) {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    (hb : ∀ γ ∈ Gs, |(b γ : ℝ)| ≤ b₀) (hW : 1 ≤ W) (hφ : ∀ a, coeffNorm1 (φ a) ≤ W) :
    coeffNorm1 (Gs.map fun γ => C (b γ : ℝ) * powE φ γ).sum ≤ Gs.length * (b₀ * W ^ (2 * t)) := by
  rw [← List.sum_toFinset _ hL.nodupG]
  refine (coeffNorm1_sum_le_card_mul _ _ (b := b₀ * W ^ (2 * t)) fun γ hγ => ?_).trans ?_
  · have hγ' := List.mem_toFinset.1 hγ
    have hm := (hL.memG γ).1 hγ'
    rw [coeffNorm1_C_mul]
    exact mul_le_mul (hb γ hγ') ((coeffNorm1_powE_le hφ hm.1).trans (pow_le_pow_right₀ hW hm.2))
      (coeffNorm1_nonneg _) hb₀
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le Gs)
      (mul_nonneg hb₀ (pow_nonneg (by linarith) _))

end Lay

/-! ### Arithmetic -/

/-- The degree of the coefficient multipliers. -/
theorem coef_deg_arith {s t m : ℕ} (hms : m * s ≤ t) (hs : 1 ≤ s) (hst : s ≤ t) :
    2 * s + (m - 1) * (4 * s + 1) + (2 * s + 1) ≤ 5 * t := by
  rcases m with _ | m
  · simp only [zero_tsub, zero_mul, add_zero]
    omega
  · have e₁ : (m + 1 - 1) * (4 * s + 1) = 4 * (m * s) + m := by
      rw [Nat.add_sub_cancel]
      ring
    have e₂ : (m + 1) * s = m * s + s := by ring
    have : m + 1 ≤ (m + 1) * s := Nat.le_mul_of_pos_right _ hs
    omega

/-- The norm bound, piece by piece. -/
theorem moment_norm_arith {n d m s t : ℕ} {W Z₀ b₀ κ B A G T₁ T₂ : ℝ} (hW : 1 ≤ W)
    (hZ₀ : 0 ≤ Z₀) (hb₀ : 0 ≤ b₀) (hκ : 0 ≤ κ) (hms : m * s ≤ t)
    (hB0 : 0 ≤ B) (hB : B ≤ ((d : ℝ) + 1) ^ t) (hA : A ≤ ((d : ℝ) + 1) ^ (2 * s))
    (hG : G ≤ ((d : ℝ) + 1) ^ (2 * t)) (hT₁0 : 0 ≤ T₁) (hT₁ : T₁ ≤ G) (hT₂0 : 0 ≤ T₂)
    (hT₂ : T₂ ≤ A) :
    B * (B * W ^ t) ^ 2 + T₁ * W ^ (2 * t) +
        T₂ * (W ^ (2 * s) *
          (m * (((n : ℝ) + 1) * (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (2 * s)) ^ (m - 1))) +
        κ * (m * ((n : ℝ) + 1) ^ (m - 1)) * (G * (b₀ * W ^ (2 * t))) ≤
      (m + 2) * (1 + κ * b₀) * ((n : ℝ) + 1) ^ m *
        (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (3 * t) := by
  set V : ℝ := ((d : ℝ) + 1) * (Z₀ + 1) * W with hVdef
  have hD1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hW0 : 0 ≤ W := by linarith
  have hDW : ((d : ℝ) + 1) * W ≤ V := by
    rw [hVdef, mul_right_comm]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hV : 1 ≤ V := le_trans (one_le_mul_of_one_le_of_one_le hD1 hW) hDW
  have hV0 : 0 ≤ V := by linarith
  have hDWk : ∀ k, ((d : ℝ) + 1) ^ k * W ^ k ≤ V ^ k := fun k => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hDW k
  have hV3 := pow_le_pow_right₀ hV (show 2 * t ≤ 3 * t by omega)
  set P : ℝ := ((n : ℝ) + 1) ^ m * V ^ (3 * t) with hPdef
  have hP : V ^ (3 * t) ≤ P := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hN1)
  -- the Gram form
  have p₁ : B * (B * W ^ t) ^ 2 ≤ V ^ (3 * t) := by
    calc B * (B * W ^ t) ^ 2 = B ^ 3 * W ^ (2 * t) := by ring
      _ ≤ (((d : ℝ) + 1) ^ t) ^ 3 * W ^ (3 * t) :=
          mul_le_mul (pow_le_pow_left₀ hB0 hB 3) (pow_le_pow_right₀ hW (by omega))
            (by positivity) (by positivity)
      _ = ((d : ℝ) + 1) ^ (3 * t) * W ^ (3 * t) := by ring
      _ ≤ V ^ (3 * t) := hDWk _
  -- the moment multipliers
  have hGW : G * W ^ (2 * t) ≤ V ^ (3 * t) :=
    (mul_le_mul_of_nonneg_right hG (by positivity)).trans ((hDWk _).trans hV3)
  have p₂ : T₁ * W ^ (2 * t) ≤ V ^ (3 * t) :=
    (mul_le_mul_of_nonneg_right hT₁ (by positivity)).trans hGW
  -- the coefficient multipliers
  have p₃ : T₂ * (W ^ (2 * s) * (m * (((n : ℝ) + 1) * V ^ (2 * s)) ^ (m - 1))) ≤ m * P := by
    rcases m with _ | m
    · simp
    · have hT : T₂ * W ^ (2 * s) ≤ V ^ (2 * s) :=
        (mul_le_mul_of_nonneg_right (hT₂.trans hA) (by positivity)).trans (hDWk _)
      have hexp : 2 * s + 2 * s * m ≤ 3 * t := by
        have : (m + 1) * s ≤ t := hms
        nlinarith
      rw [Nat.add_sub_cancel]
      calc T₂ * (W ^ (2 * s) * (((m + 1 : ℕ) : ℝ) * (((n : ℝ) + 1) * V ^ (2 * s)) ^ m))
          = ((m + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ m * ((T₂ * W ^ (2 * s)) * (V ^ (2 * s)) ^ m) := by
            rw [mul_pow]
            ring
        _ ≤ ((m + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (m + 1) * (V ^ (2 * s) * (V ^ (2 * s)) ^ m) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hN1 (by omega)) (by positivity))
              (mul_le_mul_of_nonneg_right hT (by positivity)) ?_ (by positivity)
            exact mul_nonneg (mul_nonneg hT₂0 (by positivity)) (by positivity)
        _ = ((m + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (m + 1) * V ^ (2 * s + 2 * s * m) := by
            rw [← pow_mul, ← pow_add]
        _ ≤ ((m + 1 : ℕ) : ℝ) * (((n : ℝ) + 1) ^ (m + 1) * V ^ (3 * t)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV hexp) (by positivity))
              (by positivity)
  -- the size multiplier
  have p₄ : κ * (m * ((n : ℝ) + 1) ^ (m - 1)) * (G * (b₀ * W ^ (2 * t))) ≤ κ * b₀ * (m * P) := by
    have h1 : ((n : ℝ) + 1) ^ (m - 1) ≤ ((n : ℝ) + 1) ^ m := pow_le_pow_right₀ hN1 (by omega)
    calc κ * (m * ((n : ℝ) + 1) ^ (m - 1)) * (G * (b₀ * W ^ (2 * t)))
        = κ * b₀ * m * (((n : ℝ) + 1) ^ (m - 1) * (G * W ^ (2 * t))) := by ring
      _ ≤ κ * b₀ * m * (((n : ℝ) + 1) ^ m * V ^ (3 * t)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h1 hGW ?_ (by positivity)) (by positivity)
          exact mul_nonneg (le_trans hT₁0 hT₁) (by positivity)
      _ = κ * b₀ * (m * P) := by rw [hPdef]; ring
  have hmP : 0 ≤ (m : ℝ) * P := by positivity
  have hκb : 0 ≤ κ * b₀ := mul_nonneg hκ hb₀
  have hκbP : 0 ≤ κ * b₀ * P := by positivity
  calc _ ≤ V ^ (3 * t) + V ^ (3 * t) + m * P + κ * b₀ * (m * P) := by
        gcongr
    _ ≤ (m + 2) * (1 + κ * b₀) * P := by nlinarith
    _ = _ := by rw [hPdef]; ring

/-! ### The moment axiom -/

section Axiom

variable {n d : ℕ} (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) {s t m : ℕ} (K Bd : ℚ) {Lb : ℕ}

/-- **The moment axiom in the program variables.** Let `φ₀, …, φ_{d-1}` be polynomials in the
program variables of degree at most `1` with `‖φₐ‖₁ ≤ W` (`W ≥ 1`), let `|zᵢₐ| ≤ Z₀` and
`|b_γ| ≤ b₀` for `|γ| ≤ 2t`, and suppose nothing is cut (`BS23.SmallRadius.Fits`) and `s ≥ 1`.
Then, for every `k ≥ 5t`, modulo the equality constraints of the program,

  `K (∑ᵢ wᵢ)^m B̃(φ) - (∑ᵢ wᵢ ⟨zᵢ - μ, φ⟩^{2s})^m`

is a sum of squares, in degree `k` and with norm `(m + 2) (1 + |K| b₀) (n + 1)^m V^{3t}`,
`V = (d + 1)(Z₀ + 1) W`. Here `⟨zᵢ - μ, φ⟩ = ∑ₐ (zᵢₐ - μₐ) φₐ` and
`B̃(φ) = ∑_{|γ| ≤ 2t} b_γ φ^γ`. -/
theorem moment_axiom (hfit : Fits d s t m Lb) (hs : 1 ≤ s) {k : ℕ} (hk : 5 * t ≤ k)
    {φ : Fin d → MvPolynomial (Fin (lay n d s t Lb).N) ℝ} {W Z₀ b₀ : ℝ} (hW : 1 ≤ W)
    (hZ₀ : 0 ≤ Z₀) (hb₀ : 0 ≤ b₀) (hφd : ∀ a, (φ a).totalDegree ≤ 1)
    (hφn : ∀ a, coeffNorm1 (φ a) ≤ W) (hz : ∀ i a, |(z i a : ℝ)| ≤ Z₀)
    (hb : ∀ γ ∈ gams d t Lb, |(b γ : ℝ)| ≤ b₀) :
    SosPlusIdeal (realSystem z b s t m K Bd Lb) k
      ((m + 2) * (1 + |(K : ℝ)| * b₀) * ((n : ℝ) + 1) ^ m *
        (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (3 * t))
      (C (K : ℝ) * (∑ i, X ((lay n d s t Lb).wv i)) ^ m *
          ((gams d t Lb).map fun γ => C (b γ : ℝ) * powE φ γ).sum -
        (∑ i, X ((lay n d s t Lb).wv i) *
          (∑ a, (C (z i a : ℝ) - X ((lay n d s t Lb).mv a)) * φ a) ^ (2 * s)) ^ m) := by
  have hL := good_lay (n := n) hfit
  obtain ⟨hms, hst, -⟩ := hfit
  have ht : 1 ≤ t := hs.trans hst
  have hmt : m ≤ t := (Nat.le_mul_of_pos_right m hs).trans hms
  refine SosPlusIdeal.mono ?_ hk le_rfl
  -- The pieces.
  set Bt := ((gams d t Lb).map fun γ => C (b γ : ℝ) * powE φ γ).sum with hBt
  set ws : MvPolynomial (Fin (lay n d s t Lb).N) ℝ := ∑ i, X ((lay n d s t Lb).wv i) with hws
  set σv : MvPolynomial (Fin (lay n d s t Lb).N) ℝ := X (lay n d s t Lb).sv with hσv
  set Xp := ∑ j, X ((lay n d s t Lb).cv j) * powE φ ((lay n d s t Lb).As.get j) with hXp
  set Yp := ∑ i, X ((lay n d s t Lb).wv i) *
    (∑ a, (C (z i a : ℝ) - X ((lay n d s t Lb).mv a)) * φ a) ^ (2 * s) with hYp
  set Ps := ∑ c, (∑ β, X ((lay n d s t Lb).pv β c) * powE φ ((lay n d s t Lb).Bs.get β)) ^ 2
    with hPs
  set Q := ∑ i ∈ range m, Xp ^ i * Yp ^ (m - 1 - i) with hQ
  set Q₂ := ∑ i ∈ range m, ws ^ i * σv ^ (m - 1 - i) with hQ₂
  set Θ : ℝ := ((n : ℝ) + 1) * (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (2 * s) with hΘ
  have hW0 : 0 ≤ W := by linarith
  have hD1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- Sizes of the lists of exponent vectors.
  have hAlen : ((lay n d s t Lb).A : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * s) := by
    exact_mod_cast length_le_of_mem_all hL.nodupA fun e he => (hL.memA e).1 he
  have hBlen : ((lay n d s t Lb).B : ℝ) ≤ ((d : ℝ) + 1) ^ t := by
    exact_mod_cast length_le_of_mem_all hL.nodupB fun e he => (hL.memB e).1 he
  have hGlen : ((gams d t Lb).length : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * t) := by
    exact_mod_cast length_le_of_mem_all hL.nodupG fun e he => (hL.memG e).1 he
  -- Norms of `X'` and `Y'`.
  have hXpn : coeffNorm1 Xp ≤ Θ := by
    refine (Lay.coeffNorm1_cSum_le hL hW hφn).trans ?_
    calc ((lay n d s t Lb).A : ℝ) * W ^ (2 * s) ≤ ((d : ℝ) + 1) ^ (2 * s) * W ^ (2 * s) :=
          mul_le_mul_of_nonneg_right hAlen (by positivity)
      _ = (((d : ℝ) + 1) * W) ^ (2 * s) := (mul_pow _ _ _).symm
      _ ≤ (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (2 * s) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          rw [mul_right_comm]
          exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ Θ := le_mul_of_one_le_left (by positivity) hN1
  have hYpn : coeffNorm1 Yp ≤ Θ := by
    refine (Lay.coeffNorm1_ySum_le (L := lay n d s t Lb) z hz hφn).trans ?_
    change (n : ℝ) * ((d : ℝ) * ((Z₀ + 1) * W)) ^ (2 * s) ≤ Θ
    refine mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
      (by positivity)
    have : (d : ℝ) * ((Z₀ + 1) * W) ≤ ((d : ℝ) + 1) * ((Z₀ + 1) * W) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [this, show ((d : ℝ) + 1) * (Z₀ + 1) * W = ((d : ℝ) + 1) * ((Z₀ + 1) * W) by ring]
  -- Step 1: the moment identity.
  have h₁ : SosPlusIdeal (realSystem z b s t m K Bd Lb) (5 * t)
      ((lay n d s t Lb).B * ((lay n d s t Lb).B * W ^ t) ^ 2) Ps :=
    SosPlusIdeal.of_isSumSq _ (Lay.isSumSq_gram (L := lay n d s t Lb) φ)
      ((Lay.totalDegree_gram_le hL hφd).trans (by omega)) (Lay.coeffNorm1_gram_le hL hW hφn)
  have hmomId : ∑ γ ∈ (gams d t Lb).toFinset, powE φ γ *
      toReal (((lay n d s t Lb).momRaw (gams d t Lb) b m K Lb γ).toPoly (lay n d s t Lb).N) =
      C (K : ℝ) * σv ^ m * Bt - Xp ^ m - Ps := by
    have h := Lay.mom_identity_X hL b K φ
    rw [← List.sum_toFinset _ hL.nodupG] at h
    exact h
  have h₂ := h₁.of_eq_add_ideal (gams d t Lb).toFinset
    (e := fun γ => toReal (((lay n d s t Lb).momRaw (gams d t Lb) b m K Lb γ).toPoly
      (lay n d s t Lb).N))
    (q := fun γ => powE φ γ) (M' := W ^ (2 * t)) (g' := C (K : ℝ) * σv ^ m * Bt - Xp ^ m)
    (fun γ hγ => hasEq_mom (List.mem_toFinset.1 hγ)) (fun γ hγ => ?_) (fun γ hγ => ?_)
    (by rw [hmomId]; ring)
  rotate_left
  · have hm := (hL.memG γ).1 (List.mem_toFinset.1 hγ)
    have h1 := (totalDegree_powE_le hφd hm.1).trans hm.2
    have h2 := (totalDegree_toReal_le _).trans
      ((lay n d s t Lb).totalDegree_momRaw_le (gams d t Lb) b m K Lb γ)
    have h3 : max m 2 ≤ 3 * t := max_le (by omega) (by omega)
    omega
  · have hm := (hL.memG γ).1 (List.mem_toFinset.1 hγ)
    exact (coeffNorm1_powE_le hφn hm.1).trans (pow_le_pow_right₀ hW hm.2)
  -- Step 2: from `X'` to `Y'`.
  have hcoefId : ∑ α ∈ (lay n d s t Lb).As.toFinset, powE φ α *
      toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N) = Xp - Yp := by
    have h := Lay.coef_identity_X hL z φ
    rw [← List.sum_toFinset _ hL.nodupA] at h
    exact h
  have hgeom := geom_sum₂_mul Xp Yp m
  have h₃ := h₂.of_eq_add_ideal (lay n d s t Lb).As.toFinset
    (e := fun α => toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N))
    (q := fun α => powE φ α * Q) (M' := W ^ (2 * s) * (m * Θ ^ (m - 1)))
    (g' := C (K : ℝ) * σv ^ m * Bt - Yp ^ m)
    (fun α hα => hasEq_coef (List.mem_toFinset.1 hα)) (fun α hα => ?_) (fun α hα => ?_) ?_
  rotate_left
  · have hm := (hL.memA α).1 (List.mem_toFinset.1 hα)
    have h1 := (totalDegree_powE_le hφd hm.1).trans hm.2
    have h2 := (totalDegree_toReal_le _).trans
      ((lay n d s t Lb).totalDegree_coefRaw_le z s Lb α)
    have h3 : Q.totalDegree ≤ (m - 1) * (4 * s + 1) :=
      totalDegree_geom_le ((Lay.totalDegree_cSum_le hL hφd).trans (by omega))
        (Lay.totalDegree_ySum_le (L := lay n d s t Lb) z hφd) m
    have h4 := totalDegree_mul (powE φ α) Q
    have h5 := coef_deg_arith hms hs hst
    omega
  · have hm := (hL.memA α).1 (List.mem_toFinset.1 hα)
    refine (coeffNorm1_mul_le _ _).trans (mul_le_mul ?_ (coeffNorm1_geom_le hXpn hYpn m)
      (coeffNorm1_nonneg _) (by positivity))
    exact (coeffNorm1_powE_le hφn hm.1).trans (pow_le_pow_right₀ hW hm.2)
  · have e₁ : ∑ α ∈ (lay n d s t Lb).As.toFinset, powE φ α * Q *
        toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N) =
        Q * ∑ α ∈ (lay n d s t Lb).As.toFinset, powE φ α *
          toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N) := by
      rw [mul_sum]
      exact sum_congr rfl fun α _ => by ring
    rw [e₁, hcoefId]
    linear_combination -hgeom
  -- Step 3: from `σ` to `∑ᵢ wᵢ`.
  have hgeom₂ := geom_sum₂_mul ws σv m
  have hσ := hasEq_sum (z := z) (b := b) (s := s) (t := t) (m := m) (K := K) (Bd := Bd) (Lb := Lb)
  have h₄ := SosPlusIdeal.ideal hσ (-(C (K : ℝ) * Q₂ * Bt)) (k := 5 * t)
    (M := |(K : ℝ)| * (m * ((n : ℝ) + 1) ^ (m - 1)) *
      ((gams d t Lb).length * (b₀ * W ^ (2 * t)))) ?_ ?_
  rotate_left
  · have h1 : Q₂.totalDegree ≤ (m - 1) * 1 :=
      totalDegree_geom_le (totalDegree_finsetSum_le fun i _ => (totalDegree_X _).le)
        (totalDegree_X _).le m
    have h2 : Bt.totalDegree ≤ 2 * t := Lay.totalDegree_bTil_le hL b hφd
    have h3 := totalDegree_mul (C (K : ℝ) * Q₂) Bt
    have h4 := totalDegree_mul (C (K : ℝ)) Q₂
    have h5 : (X (lay n d s t Lb).sv - ∑ i, X ((lay n d s t Lb).wv i) :
        MvPolynomial (Fin (lay n d s t Lb).N) ℝ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X _).le
        (totalDegree_finsetSum_le fun i _ => (totalDegree_X _).le))
    rw [totalDegree_neg]
    rw [totalDegree_C, zero_add] at h4
    omega
  · rw [coeffNorm1_neg]
    refine (coeffNorm1_mul_le _ _).trans (mul_le_mul ?_
      (Lay.coeffNorm1_bTil_le hL b hb₀ hb hW hφn) (coeffNorm1_nonneg _) (by positivity))
    rw [coeffNorm1_C_mul]
    refine mul_le_mul_of_nonneg_left (coeffNorm1_geom_le ?_ ?_ m) (abs_nonneg _)
    · refine (coeffNorm1_sum_le_card_mul _ _ fun i _ => (coeffNorm1_X _).le).trans ?_
      rw [card_univ, Fintype.card_fin, mul_one]
      change (n : ℝ) ≤ n + 1
      linarith
    · rw [coeffNorm1_X]
      exact hN1
  -- Assembly.
  refine ((h₃.add h₄).congr ?_).mono le_rfl ?_
  · linear_combination (C (K : ℝ) * Bt) * hgeom₂
  · have hT₁ : (((gams d t Lb).toFinset.card : ℕ) : ℝ) ≤ (gams d t Lb).length := by
      exact_mod_cast List.toFinset_card_le _
    have hT₂ : (((lay n d s t Lb).As.toFinset.card : ℕ) : ℝ) ≤ (lay n d s t Lb).A := by
      exact_mod_cast List.toFinset_card_le _
    exact moment_norm_arith hW hZ₀ hb₀ (abs_nonneg _) hms (Nat.cast_nonneg _) hBlen hAlen
      hGlen (Nat.cast_nonneg _) hT₁ (Nat.cast_nonneg _) hT₂

/-- **The moment axiom with `B̃` from data**: `moment_axiom` for the coefficients `b = bOf Y` of
`B̃(φ) = (n_Y t^t)⁻¹ ∑ⱼ ⟨Yⱼ, φ⟩^{2t}`. -/
theorem moment_axiom_bOf {nY : ℕ} (Y : Fin nY → Fin d → ℚ) (hfit : Fits d s t m Lb)
    (hs : 1 ≤ s) {k : ℕ} (hk : 5 * t ≤ k)
    {φ : Fin d → MvPolynomial (Fin (lay n d s t Lb).N) ℝ} {W Z₀ b₀ : ℝ} (hW : 1 ≤ W)
    (hZ₀ : 0 ≤ Z₀) (hb₀ : 0 ≤ b₀) (hφd : ∀ a, (φ a).totalDegree ≤ 1)
    (hφn : ∀ a, coeffNorm1 (φ a) ≤ W) (hz : ∀ i a, |(z i a : ℝ)| ≤ Z₀)
    (hb : ∀ γ ∈ gams d t Lb, |(bOf Y t Lb γ : ℝ)| ≤ b₀) :
    SosPlusIdeal (realSystem z (bOf Y t Lb) s t m K Bd Lb) k
      ((m + 2) * (1 + |(K : ℝ)| * b₀) * ((n : ℝ) + 1) ^ m *
        (((d : ℝ) + 1) * (Z₀ + 1) * W) ^ (3 * t))
      (C (K : ℝ) * (∑ i, X ((lay n d s t Lb).wv i)) ^ m *
          (C (((nY : ℝ) * t ^ t)⁻¹) * ∑ j, (∑ a, C (Y j a : ℝ) * φ a) ^ (2 * t)) -
        (∑ i, X ((lay n d s t Lb).wv i) *
          (∑ a, (C (z i a : ℝ) - X ((lay n d s t Lb).mv a)) * φ a) ^ (2 * s)) ^ m) := by
  have h := sum_bOf_mul_powE_of_fits Y hfit φ
  simp only [MvPolynomial.algebraMap_apply] at h
  have h' : ((gams d t Lb).map fun γ => C (bOf Y t Lb γ : ℝ) * powE φ γ).sum =
      C (((nY : ℝ) * t ^ t)⁻¹) * ∑ j, (∑ a, C (Y j a : ℝ) * φ a) ^ (2 * t) := by
    simpa using h
  rw [← h']
  exact moment_axiom z (bOf Y t Lb) K Bd hfit hs hk hW hZ₀ hb₀ hφd hφn hz hb

end Axiom

end BS23.SmallRadius
