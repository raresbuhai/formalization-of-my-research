module

public import BKS23.AlgorithmPolyTime
public import BKS23.RandomCut
public import BKS23.Random
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Assembly

The proof of [BKS23, Theorem 5.6 (2)] from its parts.

* **The parameter** `t` (`BKS23.Assembly.tOf`): the least integer above `3/(8ε) - 1/2`, so that
  `(8t + 4) ε > 3` (the certificate beats the coverage) and `(2t + 1) ε ≤ 1` (the characters'
  bias is paid by the size condition).
* **Sizes**: the threshold `Δ = ⌈n^(1/(2t))⌉` (`BKS23.Assembly.rootCeil_pow_ge`,
  `BKS23.Assembly.rootCeil_le`) and the constraint norms (`BKS23.Assembly.constraintNorm_le`).
-/

@[expose] public section

namespace BKS23.Assembly

open SoS MvPolynomial Finset Filter Topology

/-! ### The parameter `t` -/

/-- `t = ⌊3/(8ε) - 1/2⌋ + 1`. -/
noncomputable def tOf (ε : ℝ) : ℕ := ⌊3 / (8 * ε) - 1 / 2⌋₊ + 1

theorem tOf_spec {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    3 < (8 * (tOf ε : ℝ) + 4) * ε ∧ (2 * (tOf ε : ℝ) + 1) * ε ≤ 1 ∧ 1 ≤ tOf ε := by
  set y := 3 / (8 * ε) - 1 / 2 with hy
  have hy0 : 0 ≤ y := by
    rw [hy, sub_nonneg, le_div_iff₀ (by positivity)]
    linarith
  have h1 := Nat.lt_floor_add_one y
  have h2 := Nat.floor_le hy0
  have ht : (tOf ε : ℝ) = ⌊y⌋₊ + 1 := by simp [tOf, hy]
  refine ⟨?_, ?_, by simp [tOf]⟩
  · have : 3 / ε = 8 * y + 4 := by rw [hy]; field_simp; ring
    have h3 : 3 = (8 * y + 4) * ε := by rw [← this]; field_simp
    rw [h3]
    exact mul_lt_mul_of_pos_right (by rw [ht]; linarith) hε
  · have : (2 * (tOf ε : ℝ) + 1) * ε ≤ (2 * y + 3) * ε :=
      mul_le_mul_of_nonneg_right (by rw [ht]; linarith) hε.le
    refine this.trans ?_
    rw [hy]
    field_simp
    nlinarith

/-! ### The threshold `Δ = ⌈n^(1/m)⌉` -/

theorem rootCeil_eq {n m : ℕ} (hm : 1 ≤ m) (_hn : 1 ≤ n) :
    Algorithm.rootCeil n m = Nat.find (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m) := by
  classical
  set r := Nat.find (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m) with hr
  have hrn : r ≤ n := Nat.find_min' _ (Nat.le_self_pow (by omega) n)
  have hiff : ∀ d, d ^ m < n ↔ d < r := by
    intro d
    constructor
    · intro h
      by_contra hd
      rw [not_lt] at hd
      have := Nat.find_spec (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m)
      rw [← hr] at this
      exact absurd (this.trans (Nat.pow_le_pow_left hd m)) (by omega)
    · intro h
      have := Nat.find_min (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m) (hr ▸ h)
      omega
  rw [Algorithm.rootCeil,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter fun d ↦ decide (d ^ m < n))]
  have : ((List.range (n + 1)).filter fun d ↦ decide (d ^ m < n)).toFinset = Finset.range r := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq, hiff,
      Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- `Δ^m ≥ n`. -/
theorem rootCeil_pow_ge {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : n ≤ Algorithm.rootCeil n m ^ m := by
  rw [rootCeil_eq hm hn]
  exact Nat.find_spec (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m)

/-- `(Δ - 1)^m < n`. -/
theorem rootCeil_sub_pow_lt {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (Algorithm.rootCeil n m - 1) ^ m < n := by
  rw [rootCeil_eq hm hn]
  have hpos : 0 < Nat.find (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m) := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    have := Nat.find_spec (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m)
    rw [h, zero_pow (by omega)] at this
    omega
  have := Nat.find_min (⟨n, Nat.le_self_pow (by omega) n⟩ : ∃ d, n ≤ d ^ m)
    (Nat.sub_lt hpos one_pos)
  omega

theorem rootCeil_ge {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 / (m : ℝ)) ≤ Algorithm.rootCeil n m := by
  have h : (n : ℝ) ≤ (Algorithm.rootCeil n m : ℝ) ^ m := by exact_mod_cast rootCeil_pow_ge hm hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc (n : ℝ) ^ (1 / (m : ℝ)) ≤ ((Algorithm.rootCeil n m : ℝ) ^ m) ^ (1 / (m : ℝ)) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = Algorithm.rootCeil n m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel hm'.ne',
          Real.rpow_one]

theorem rootCeil_le {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (Algorithm.rootCeil n m : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ)) + 1 := by
  have h := rootCeil_sub_pow_lt hm hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ((Algorithm.rootCeil n m - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ)) := by
    have h' : ((Algorithm.rootCeil n m - 1 : ℕ) : ℝ) ^ m ≤ n := by exact_mod_cast h.le
    calc ((Algorithm.rootCeil n m - 1 : ℕ) : ℝ) =
          (((Algorithm.rootCeil n m - 1 : ℕ) : ℝ) ^ m) ^ (1 / (m : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel hm'.ne',
            Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 / (m : ℝ)) := Real.rpow_le_rpow (by positivity) h' (by positivity)
  have : (Algorithm.rootCeil n m : ℝ) ≤ ((Algorithm.rootCeil n m - 1 : ℕ) : ℝ) + 1 := by
    have : Algorithm.rootCeil n m ≤ (Algorithm.rootCeil n m - 1) + 1 := by omega
    exact_mod_cast this
  linarith

/-! ### The constraint norms -/

theorem length_nonEdges_le (n : ℕ) (a : List Bool) : (Algorithm.nonEdges n a).length ≤ n ^ 2 := by
  have h1 : (Algorithm.nonEdges n a).length ≤ (Algorithm.pairs n).length := by
    rw [Algorithm.nonEdges, List.length_map]
    exact (List.length_filter_le _ _).trans (by rw [List.length_zip]; omega)
  have h2 : (Algorithm.pairs n).length ≤ n ^ 2 := by
    rw [Algorithm.pairs, List.length_flatMap, sq]
    calc (List.map (fun i ↦ ((List.filter (fun j ↦ decide (i < j)) (List.range n)).map
          fun j ↦ (i, j)).length) (List.range n)).sum ≤ (List.map (fun _ ↦ n) (List.range n)).sum :=
          List.sum_le_sum fun i _ ↦ by
            rw [List.length_map]
            exact (List.length_filter_le _ _).trans (by simp)
      _ = n * n := by simp
  omega

theorem two_mul_add_three_le : ∀ n : ℕ, 2 * n + 3 ≤ 2 ^ (n + 2)
  | 0 => by norm_num
  | n + 1 => by have := two_mul_add_three_le n; rw [pow_succ]; omega

/-- **The constraint norms** `∏ᵢ (1 + ‖fᵢ‖₂) ≤ 2^(2 (n + 2)^3)`, for `k ≤ n` and at most `n²`
non-edges. -/
theorem constraintNorm_le {n k ℓ : ℕ} {L : List (ℕ × ℕ)} (hk : k ≤ n) (hL : L.length ≤ n ^ 2) :
    Rounding.constraintNorm n k ℓ L ≤ 2 ^ (2 * (n + 2) ^ 3) := by
  unfold Rounding.constraintNorm
  set A := Clique.realSystem n k ℓ L
  have hlen : A.length = 2 * n + 3 + 2 * L.length := by
    simp [A, Clique.realSystem, SoS.Solver.Problem.system, Clique.problem,
      Clique.length_constraints]
  have hfac : ∀ i : Fin A.length, 1 + coeffNorm (A.get i) ≤ 2 * n + 3 := by
    intro i
    have hmem : A.get i ∈ A := List.get_mem _ _
    simp only [A, Clique.realSystem, SoS.Solver.Problem.system, Clique.problem, List.map_map,
      List.mem_map] at hmem
    obtain ⟨r, hr, hri⟩ := hmem
    have hget : A.get i = toReal (Solver.RawPoly.toPoly n r) := hri.symm
    rw [hget]
    have := Clique.coeffNorm_le (n := n) (k := k) (L := L) hr
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  calc ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) ≤ ∏ _i : Fin A.length, (2 * (n : ℝ) + 3) :=
        Finset.prod_le_prod₀ (fun i _ ↦ by have := coeffNorm_nonneg (A.get i); linarith)
          fun i _ ↦ hfac i
    _ = (2 * (n : ℝ) + 3) ^ A.length := by rw [prod_const, card_univ, Fintype.card_fin]
    _ ≤ ((2 : ℝ) ^ (n + 2)) ^ (2 * (n + 2) ^ 2) := by
        have h2 : 2 * n + 3 ≤ 2 ^ (n + 2) := two_mul_add_three_le n
        have h2' : 2 * (n : ℝ) + 3 ≤ (2 : ℝ) ^ (n + 2) := by exact_mod_cast h2
        have hlen' : A.length ≤ 2 * (n + 2) ^ 2 := by rw [hlen]; nlinarith
        calc (2 * (n : ℝ) + 3) ^ A.length ≤ ((2 : ℝ) ^ (n + 2)) ^ A.length :=
              pow_le_pow_left₀ (by positivity) h2' _
          _ ≤ ((2 : ℝ) ^ (n + 2)) ^ (2 * (n + 2) ^ 2) :=
              pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hlen'
    _ = 2 ^ (2 * (n + 2) ^ 3) := by rw [← pow_mul]; ring_nf

/-! ### The certificate for a good cut -/

/-- The failure probability `δ₀ = 1/400` of the good cut. -/
noncomputable def δ₀ : ℝ := 1 / 400

theorem one_le_log_four_hundred {t n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n) :
    1 ≤ Real.log (400 * t * n ^ (2 * t)) := by
  have h4 : (4 : ℝ) ≤ 400 * t * n ^ (2 * t) := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have : (1 : ℝ) ≤ (n : ℝ) ^ (2 * t) := one_le_pow₀ (by exact_mod_cast hn)
    nlinarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) h4
  linarith [Real.log_two_gt_d9]

/-- **The certificate for a good cut.** If the cut of `R'` at the planted set `U` is good for a
`q ∈ [1/2, 1)` (`BKS23.Random.Good`, with `δ₀`) and contains that of `G`, and
`X = k (1 - q)^(2t + 1)` satisfies `32 n log(400 t n^(2t)) ≤ X²`, then the clique program of `G`
proves `|x|^(4t) |y| ≤ F_t⁴ |Uᶜ| c⁴` with `c = 2n / X`, in degree `8t + 6` with multipliers of
norm at most `((n + 2t + 2)²)^(15t + 28)`. -/
theorem certificate_good {n k t : ℕ} {L : List (ℕ × ℕ)} {G R' : SimpleGraph (Fin n)}
    (hL : Clique.ListsNonEdges G L) {U : Finset (Fin n)} (hU : U.card = k)
    (hcut : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → R'.Adj u v)
    {q : ℝ} (hq : 1 / 2 ≤ q) (hq1 : q < 1) (ht : 1 ≤ t) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hgood : Random.Good U q t δ₀ R')
    (hX : 32 * n * Real.log (400 * t * n ^ (2 * t)) ≤ ((k : ℝ) * (1 - q) ^ (2 * t + 1)) ^ 2) :
    DerivesN (Clique.realSystem n k (8 * t + 6) L) (8 * t + 6)
      ((((n : ℝ) + 2 * t + 2) ^ 2) ^ (15 * t + 28))
      (C ((∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ^ 4 * Uᶜ.card *
        (2 * n / ((k : ℝ) * (1 - q) ^ (2 * t + 1))) ^ 4) -
        (∑ u ∈ U, X u) ^ (4 * t) * ∑ v ∈ Uᶜ, X v) := by
  classical
  have hA := Clique.axioms (k := k) (ℓ := 8 * t + 6) hL (adj := R'.Adj) hcut
  obtain ⟨β, hβ⟩ : ∃ β, β = 1 - q := ⟨_, rfl⟩
  rw [← hβ] at hX ⊢
  obtain ⟨X, hXdef⟩ : ∃ X, X = (k : ℝ) * β ^ (2 * t + 1) := ⟨_, rfl⟩
  rw [← hXdef] at hX ⊢
  obtain ⟨W, hW⟩ : ∃ W, W = ((n : ℝ) + 2 * t + 2) ^ 2 := ⟨_, rfl⟩
  rw [← hW]
  set L₀ := Real.log (400 * t * n ^ (2 * t)) with hL₀
  have hβ0 : 0 < β := by linarith
  have hβ1 : β ≤ 1 / 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := hk1.trans hkn'
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hUc : (Uᶜ.card : ℝ) = n - k := by
    rw [card_compl, Fintype.card_fin, hU, Nat.cast_sub hkn]
  have hUc0 : (0 : ℝ) ≤ Uᶜ.card := Nat.cast_nonneg _
  have hUk : (U.card : ℝ) = k := by rw [hU]
  -- `charMax q = q / β`.
  have hcm : Biclique.charMax q = q / β := by
    unfold Biclique.charMax
    rw [← hβ]
    refine max_eq_right ?_
    rw [div_le_div_iff₀ hq0 hβ0]
    exact mul_le_mul (by linarith) (by linarith) hβ0.le (by linarith)
  -- `X ≤ k β^j` for `j ≤ 2t + 1`, so `X ≤ k ≤ n`.
  have hβpow : ∀ j ≤ 2 * t + 1, X ≤ (k : ℝ) * β ^ j := fun j hj ↦ by
    rw [hXdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hβ0.le (by linarith) hj) (by positivity)
  have hX0 : 0 < X := by rw [hXdef]; positivity
  have hXk : X ≤ k := by simpa using hβpow 0 (by omega)
  have hXn : X ≤ n := hXk.trans hkn'
  have hL₀1 : 1 ≤ L₀ := one_le_log_four_hundred ht (by exact_mod_cast hn1)
  have hnL : (1 : ℝ) ≤ n * L₀ := one_le_mul_of_one_le_of_one_le hn1 hL₀1
  have hX1 : 1 ≤ X := by
    by_contra h
    push Not at h
    have : X ^ 2 < 1 := pow_lt_one₀ hX0.le h two_ne_zero
    linarith
  have h32 : 32 * L₀ ≤ X := by
    have h1 : X ^ 2 ≤ X * n := by rw [sq]; exact mul_le_mul_of_nonneg_left hXn hX0.le
    have h2 : 32 * L₀ * n ≤ X * n := by linarith
    exact le_of_mul_le_mul_right h2 (by linarith)
  -- The logarithms are at most `L₀`.
  have hlogm : ∀ m ∈ Icc 1 t, Real.log (t * U.card ^ (2 * m) / δ₀) ≤ L₀ := by
    intro m hm
    have hm' := mem_Icc.1 hm
    rw [hUk, δ₀]
    refine Real.log_le_log (by positivity) ?_
    have h1 : (k : ℝ) ^ (2 * m) ≤ (n : ℝ) ^ (2 * t) :=
      (pow_le_pow_left₀ (by positivity) hkn' _).trans (pow_le_pow_right₀ hn1 (by omega))
    have h2 : (t : ℝ) * k ^ (2 * m) / (1 / 400) = 400 * t * k ^ (2 * m) := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hlogd : Real.log (Uᶜ.card / δ₀) ≤ L₀ := by
    rcases eq_or_lt_of_le hUc0 with h0 | hpos
    · rw [← h0, zero_div, Real.log_zero]
      linarith
    refine Real.log_le_log (by rw [δ₀]; positivity) ?_
    have h1 : (Uᶜ.card : ℝ) ≤ n := by rw [hUc]; linarith
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ (2 * t) := le_self_pow₀ hn1 (by omega)
    have h3 : (n : ℝ) ^ (2 * t) ≤ t * (n : ℝ) ^ (2 * t) := le_mul_of_one_le_left (by positivity) ht1
    have h4 : (Uᶜ.card : ℝ) / δ₀ = 400 * Uᶜ.card := by rw [δ₀]; field_simp
    rw [h4]
    linarith
  -- The square roots.
  have hsqrt : ∀ {a b : ℝ}, 0 ≤ b → a ≤ b ^ 2 → √a ≤ b := fun hb hab ↦
    (Real.sqrt_le_sqrt hab).trans_eq (Real.sqrt_sq hb)
  have hkβ : X ≤ k * β ^ 2 := hβpow 2 (by omega)
  have hsqd : √(2 * U.card * Real.log (Uᶜ.card / δ₀)) ≤ k * β / 4 := by
    refine hsqrt (by positivity) ?_
    rw [hUk]
    have h1 : 2 * (k : ℝ) * Real.log (Uᶜ.card / δ₀) ≤ 2 * k * L₀ :=
      mul_le_mul_of_nonneg_left hlogd (by positivity)
    have h2 : (k : ℝ) * (32 * L₀) ≤ k * (k * β ^ 2) :=
      mul_le_mul_of_nonneg_left (h32.trans hkβ) (by positivity)
    have h3 : ((k : ℝ) * β / 4) ^ 2 = k * (k * β ^ 2) / 16 := by ring
    rw [h3]
    linarith
  have hsqΔ : ∀ m ∈ Icc 1 t, √(2 * Uᶜ.card * Real.log (t * U.card ^ (2 * m) / δ₀)) ≤ X / 4 := by
    intro m hm
    refine hsqrt (by positivity) ?_
    have h1 : 2 * (Uᶜ.card : ℝ) * Real.log (t * U.card ^ (2 * m) / δ₀) ≤ 2 * Uᶜ.card * L₀ :=
      mul_le_mul_of_nonneg_left (hlogm m hm) (by positivity)
    have h2 : (Uᶜ.card : ℝ) ≤ n := by rw [hUc]; linarith
    have h3 : 2 * (Uᶜ.card : ℝ) * L₀ ≤ 2 * n * L₀ :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h4 : (X / 4) ^ 2 = X ^ 2 / 16 := by ring
    rw [h4]
    linarith
  -- The key inequality `(q/β)^m X ≤ (β/q)^m k β`, for `m ≤ t`.
  have haβ : ∀ m : ℕ, (q / β) ^ m * β ^ m ≤ 1 := fun m ↦ by
    rw [← mul_pow, div_mul_cancel₀ _ hβ0.ne']
    exact pow_le_one₀ hq0.le hq1.le
  have hbβ : ∀ m : ℕ, β ^ m ≤ (β / q) ^ m := fun m ↦
    pow_le_pow_left₀ hβ0.le (by rw [le_div_iff₀ hq0]; exact mul_le_of_le_one_right hβ0.le hq1.le) m
  have hb1 : ∀ m : ℕ, (β / q) ^ m ≤ 1 := fun m ↦
    pow_le_one₀ (by positivity) (by rw [div_le_one hq0]; linarith)
  have hkey : ∀ m ≤ t, (q / β) ^ m * X ≤ (β / q) ^ m * (k * β) := by
    intro m hm
    have h1 : X ≤ (k : ℝ) * β ^ (2 * m + 1) := hβpow _ (by omega)
    have ha0 : 0 ≤ (q / β) ^ m := by positivity
    calc (q / β) ^ m * X ≤ (q / β) ^ m * ((k : ℝ) * β ^ (2 * m + 1)) :=
          mul_le_mul_of_nonneg_left h1 ha0
      _ = ((q / β) ^ m * β ^ m) * (k * β ^ (m + 1)) := by ring
      _ ≤ 1 * (k * β ^ (m + 1)) := mul_le_mul_of_nonneg_right (haβ m) (by positivity)
      _ = β ^ m * (k * β) := by ring
      _ ≤ (β / q) ^ m * (k * β) := mul_le_mul_of_nonneg_right (hbβ m) (by positivity)
  have hbk : ∀ m : ℕ, (β / q) ^ m * (k * β) ≤ k := fun m ↦
    calc (β / q) ^ m * (k * β) ≤ 1 * (k * 1) :=
          mul_le_mul (hb1 m) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
            (by positivity) (by norm_num)
      _ = k := by ring
  have hamax : ∀ m ≤ t, (q / β) ^ m ≤ n := by
    intro m hm
    have h := hkey m hm
    have := hbk m
    have : (q / β) ^ m ≤ (q / β) ^ m * X := le_mul_of_one_le_right (by positivity) hX1
    linarith
  -- `Δ_m ≤ (β/q)^m k β / 4` and `λ_m ≥ (β/q)^m k β / 2 ≥ 1/2`.
  have hΔm : ∀ m ∈ Icc 1 t, Random.balance U q δ₀ t m ≤ (β / q) ^ m * (k * β) / 4 := by
    intro m hm
    unfold Random.balance
    rw [hcm]
    have h1 := mul_le_mul_of_nonneg_left (hsqΔ m hm) (by positivity : (0 : ℝ) ≤ (q / β) ^ m)
    have h2 := hkey m (mem_Icc.1 hm).2
    linarith
  have hΔ0 : ∀ m, 0 ≤ Random.balance U q δ₀ t m := fun m ↦ by
    unfold Random.balance
    rw [hcm]
    positivity
  have hkd : (k : ℝ) - Random.degreeBound U q δ₀ ≥ 3 * (k * β) / 4 := by
    unfold Random.degreeBound
    rw [hUk] at hsqd ⊢
    have : (k : ℝ) * β = k - k * q := by rw [hβ]; ring
    linarith
  have hlamb : ∀ m ∈ Icc 1 t, (β / q) ^ m * (k * β) / 2 ≤
      (β / q) ^ m * (k - Random.degreeBound U q δ₀) - Random.balance U q δ₀ t m := by
    intro m hm
    have h1 := mul_le_mul_of_nonneg_left hkd (by positivity : (0 : ℝ) ≤ (β / q) ^ m)
    have h2 := hΔm m hm
    linarith
  have hlam_half : ∀ m ∈ Icc 1 t, (1 : ℝ) / 2 ≤ (β / q) ^ m * (k * β) / 2 := by
    intro m hm
    have h1 : X ≤ (k : ℝ) * β ^ (m + 1) := hβpow _ (by have := (mem_Icc.1 hm).2; omega)
    have h2 : (k : ℝ) * β ^ (m + 1) ≤ (β / q) ^ m * (k * β) := by
      calc (k : ℝ) * β ^ (m + 1) = β ^ m * (k * β) := by ring
        _ ≤ (β / q) ^ m * (k * β) := mul_le_mul_of_nonneg_right (hbβ m) (by positivity)
    linarith
  -- `W` is large.
  have hWge : (n : ℝ) + 2 * t + 2 ≤ W := by
    rw [hW]
    exact le_self_pow₀ (by linarith) two_ne_zero
  have hWn2 : (n : ℝ) * n ≤ W := by
    rw [hW, sq]
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hW2n : 2 * (n : ℝ) ≤ W := by
    rw [hW, sq]
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  refine hA.certificate_pBiased (p := q) (W := W) (c := 2 * n / X)
    (d := Random.degreeBound U q δ₀) (Δ := Random.balance U q δ₀ t) hq0 hq1
    (by linarith) (by rw [hUk]; linarith) (by rw [hUc]; linarith) (by linarith)
    (by rw [le_div_iff₀ hX0]; linarith) ?_ ?_ hgood.2 ?_ ?_ ?_ (fun m hm S hS T hT hST ↦
      hgood.1 m hm S hS T hT hST) ?_ ?_
  · -- `c ≤ W`
    rw [div_le_iff₀ hX0]
    have : W ≤ W * X := le_mul_of_one_le_right (by linarith) hX1
    linarith
  · -- `d ≤ W`
    unfold Random.degreeBound
    have h1 : (U.card : ℝ) * q ≤ k := by
      rw [hUk]; exact mul_le_of_le_one_right (by positivity) hq1.le
    have h2 : (k : ℝ) * β ≤ k * (1 / 2) := mul_le_mul_of_nonneg_left hβ1 (by positivity)
    linarith
  · -- `charMax^m ≤ W`
    intro m hm
    rw [hcm]
    have := hamax m (mem_Icc.1 hm).2
    linarith
  · -- `|Uᶜ| charMax^m ≤ W`
    intro m hm
    rw [hcm]
    have := hamax m (mem_Icc.1 hm).2
    have h2 : (Uᶜ.card : ℝ) ≤ n := by rw [hUc]; linarith
    calc (Uᶜ.card : ℝ) * (q / β) ^ m ≤ n * n := mul_le_mul h2 this (by positivity) (by positivity)
      _ ≤ W := hWn2
  · -- `0 ≤ Δ_m ≤ W`
    intro m hm
    refine ⟨hΔ0 m, (hΔm m hm).trans ?_⟩
    have := hbk m
    linarith
  · -- `1 ≤ W λ_m`
    intro m hm
    rw [← hβ]
    have hlm := (hlam_half m hm).trans (hlamb m hm)
    calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
      _ ≤ W * _ := mul_le_mul (by linarith) hlm (by norm_num) (by linarith)
  · -- `|Uᶜ| charMax^m / λ_m ≤ c`
    intro m hm
    rw [hcm, ← hβ]
    have h1 := hlamb m hm
    have h2 := hlam_half m hm
    have hpos : 0 < (β / q) ^ m * (k - Random.degreeBound U q δ₀) - Random.balance U q δ₀ t m :=
      lt_of_lt_of_le (by norm_num) (h2.trans h1)
    refine (div_le_div_iff₀ hpos hX0).2 ?_
    have h3 := hkey m (mem_Icc.1 hm).2
    have h4 : (Uᶜ.card : ℝ) ≤ n := by rw [hUc]; linarith
    have h5 : (Uᶜ.card : ℝ) * ((q / β) ^ m * X) ≤ n * ((β / q) ^ m * (k * β)) :=
      mul_le_mul h4 h3 (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ n)
    calc (Uᶜ.card : ℝ) * (q / β) ^ m * X = (Uᶜ.card : ℝ) * ((q / β) ^ m * X) := by ring
      _ ≤ n * ((β / q) ^ m * (k * β)) := h5
      _ = 2 * (n * ((β / q) ^ m * (k * β) / 2)) := by ring
      _ ≤ 2 * (n * ((β / q) ^ m * (k - Random.degreeBound U q δ₀) -
            Random.balance U q δ₀ t m)) := mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = 2 * n * ((β / q) ^ m * (k - Random.degreeBound U q δ₀) -
            Random.balance U q δ₀ t m) := by ring

/-! ### The rounding, numerically -/

/-- The factor the solver's error must beat: `16 (2n)^T (2M + 8 n^(T+1) 10^(T+1)) +
4 T² (30n + 20)^T (2n)^T + 16 · 10^(T+1)`. -/
noncomputable def roundZ (n T : ℕ) (M : ℝ) : ℝ :=
  16 * (2 * (n : ℝ)) ^ T * (2 * M + 8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1)) +
    4 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T * (2 * (n : ℝ)) ^ T + 16 * 10 ^ (T + 1)

/-- **The numerical hypotheses of the rounding** (`BKS23.Rounding.exists_round_eq`): if
`n ≤ k² `, the certificate's bound `ω` satisfies `4 ω (2n/k²)^T ≤ 1/8`, and the solver's error
`τ = (η + γ) ∏ (1 + ‖fᵢ‖₂)` satisfies `τ Z ≤ 1` (`BKS23.Assembly.roundZ`), then the errors are
small, the coverage is at least `k²/(2n)`, and the ratio of `hsmall` is below `3/8`. -/
theorem round_numeric {n k T : ℕ} {η γ PN ω M ε cov eH : ℝ} (hη : 0 < η) (hγ : 0 < γ)
    (hPN : 0 ≤ PN) (hM : 0 ≤ M) (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (hmain : 4 * ω * (2 * n / (k : ℝ) ^ 2) ^ T ≤ 1 / 8)
    (htiny : (η + γ) * PN * roundZ n T M ≤ 1)
    (hlam : γ / (η + γ) * (5 * n) ≤ 1 / 8) (hηγ : η + γ ≤ 1 / 8)
    (hε : ε = (η + γ) * (2 * 10 ^ (T + 1)) * PN)
    (hcov : cov = (k - ε) ^ 2 / n - γ / (η + γ) * (4 * n + k) - (η + γ))
    (heH : eH = (η + γ) * PN * (2 * (T : ℝ) ^ 2 * (30 * k + 20) ^ T)) :
    ε ≤ 1 ∧ ε ≤ k ∧ 0 < cov ∧ 0 < cov ^ T - eH ∧
      2 * (ω + (η + γ) * M * PN + (k : ℝ) ^ T * n * ε) / (cov ^ T - eH) +
        n * (2 * (k : ℝ) ^ T * ε / (cov ^ T - eH)) < 1 / 2 := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (η + γ) * PN := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := hk1.trans hkn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hkk' : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hkk
  have hετ : ε = τ * (2 * 10 ^ (T + 1)) := by rw [hε, hτ]; ring
  have heHτ : eH = τ * (2 * (T : ℝ) ^ 2 * (30 * k + 20) ^ T) := by rw [heH, hτ]
  -- The three parts of `τ Z ≤ 1`.
  have hZ : τ * roundZ n T M ≤ 1 := by rw [hτ]; exact htiny
  unfold roundZ at hZ
  set P := (2 * (n : ℝ)) ^ T with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hP0 : 0 < P := by linarith
  have hZ1 : τ * (16 * 10 ^ (T + 1)) ≤ 1 := by
    have : 0 ≤ τ * (16 * P * (2 * M + 8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1)) +
        4 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T * P) := by positivity
    linarith
  have hZ2 : τ * (4 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T * P) ≤ 1 := by
    have : 0 ≤ τ * (16 * P * (2 * M + 8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1)) + 16 * 10 ^ (T + 1)) :=
      by positivity
    linarith
  have hZ3 : τ * (16 * P * (2 * M + 8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1))) ≤ 1 := by
    have : 0 ≤ τ * (4 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T * P + 16 * 10 ^ (T + 1)) := by positivity
    linarith
  -- The error `ε ≤ 1/8`.
  have hε8 : ε ≤ 1 / 8 := by rw [hετ]; linarith
  have hε0 : 0 ≤ ε := by rw [hετ]; positivity
  -- The coverage is at least `c₀ = k² / (2n)`.
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = (k : ℝ) ^ 2 / (2 * n) := ⟨_, rfl⟩
  have hc₀half : 1 / 2 ≤ c₀ := by rw [hc₀, le_div_iff₀ (by positivity)]; linarith
  have hlam0 : 0 ≤ γ / (η + γ) := by positivity
  have hcovc : c₀ ≤ cov := by
    rw [hcov, hc₀]
    have h1 : ((k : ℝ) ^ 2 - 2 * k * ε) / n ≤ (k - ε) ^ 2 / n :=
      div_le_div_of_nonneg_right (by have := sq_nonneg ε; linarith) hn0.le
    have h2 : 2 * (k : ℝ) * ε / n ≤ 2 * ε := by
      rw [div_le_iff₀ hn0]
      have := mul_le_mul_of_nonneg_left hkn' (by linarith : (0 : ℝ) ≤ 2 * ε)
      linarith
    have h3 : γ / (η + γ) * (4 * n + k) ≤ γ / (η + γ) * (5 * n) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam0
    have h4 : ((k : ℝ) ^ 2 - 2 * k * ε) / n = (k : ℝ) ^ 2 / n - 2 * k * ε / n := by ring
    have h5 : (k : ℝ) ^ 2 / (2 * n) = (k : ℝ) ^ 2 / n / 2 := by ring
    have h6 : 1 ≤ (k : ℝ) ^ 2 / n := by rw [le_div_iff₀ hn0]; linarith
    linarith
  have hc₀0 : 0 < c₀ := by linarith
  -- `c₀^T ≥ 1/P`.
  have hc₀P : 1 ≤ c₀ ^ T * P := by
    rw [hP, ← mul_pow]
    refine one_le_pow₀ ?_
    rw [hc₀, div_mul_eq_mul_div, mul_comm (2 : ℝ), mul_div_assoc,
      div_self (by positivity), mul_one]
    linarith
  -- `eH ≤ c₀^T / 2`.
  have heH2 : eH ≤ c₀ ^ T / 2 := by
    rw [heHτ]
    have h1 : (30 * (k : ℝ) + 20) ^ T ≤ (30 * n + 20) ^ T :=
      pow_le_pow_left₀ (by positivity) (by linarith) T
    have h2 : τ * (2 * (T : ℝ) ^ 2 * (30 * k + 20) ^ T) ≤
        τ * (2 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hτ0
    have h3 : τ * (2 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T) * P ≤ 1 / 2 := by linarith
    have h4 : τ * (2 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T) * P ≤ c₀ ^ T * P / 2 := by linarith
    have h5 : τ * (2 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T) ≤ c₀ ^ T / 2 := by
      have := (mul_le_mul_iff_of_pos_right hP0).1 (h4.trans_eq (by ring) :
        τ * (2 * (T : ℝ) ^ 2 * (30 * n + 20) ^ T) * P ≤ c₀ ^ T / 2 * P)
      exact this
    linarith
  have hcovT : c₀ ^ T ≤ cov ^ T := pow_le_pow_left₀ hc₀0.le hcovc T
  have hY : c₀ ^ T / 2 ≤ cov ^ T - eH := by linarith
  have hc₀T : 0 < c₀ ^ T := pow_pos hc₀0 T
  have hYpos : 0 < cov ^ T - eH := by linarith
  -- The numerator is at most `3 c₀^T / 16`.
  have hd : (2 * n / (k : ℝ) ^ 2) ^ T * c₀ ^ T = 1 := by
    rw [← mul_pow, hc₀, div_mul_div_comm, mul_comm (2 * (n : ℝ)), div_self (by positivity),
      one_pow]
  have hωb : 2 * ω ≤ c₀ ^ T / 16 := by
    have h1 : 4 * ω * (2 * n / (k : ℝ) ^ 2) ^ T * c₀ ^ T ≤ 1 / 8 * c₀ ^ T :=
      mul_le_mul_of_nonneg_right hmain hc₀T.le
    have h2 : 4 * ω * (2 * n / (k : ℝ) ^ 2) ^ T * c₀ ^ T = 4 * ω := by
      rw [mul_assoc, hd, mul_one]
    linarith
  have hMb : 2 * (τ * M) ≤ c₀ ^ T / 16 := by
    have h1 : τ * M * P ≤ 1 / 32 := by
      have : 0 ≤ τ * (16 * P * (8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1))) := by positivity
      linarith
    have h2 : τ * M * P ≤ c₀ ^ T * P / 32 := by linarith
    have h3 : τ * M ≤ c₀ ^ T / 32 :=
      (mul_le_mul_iff_of_pos_right hP0).1 (h2.trans_eq (by ring))
    linarith
  have hkT : (k : ℝ) ^ T * n ≤ (n : ℝ) ^ (T + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hkn' T) (by positivity)
  have hεb : 4 * (n : ℝ) * (k : ℝ) ^ T * ε ≤ c₀ ^ T / 16 := by
    have h1 : τ * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1) * P ≤ 1 / 128 := by
      have : 0 ≤ τ * (16 * P * (2 * M)) := by positivity
      linarith
    have h2 : τ * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1) ≤ c₀ ^ T / 128 := by
      have h3 : τ * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1) * P ≤ c₀ ^ T * P / 128 := by linarith
      exact (mul_le_mul_iff_of_pos_right hP0).1 (h3.trans_eq (by ring))
    have h4 : 4 * (n : ℝ) * (k : ℝ) ^ T * ε = 8 * τ * ((k : ℝ) ^ T * n) * 10 ^ (T + 1) := by
      rw [hετ]; ring
    have h5 : 8 * τ * ((k : ℝ) ^ T * n) * 10 ^ (T + 1) ≤ 8 * τ * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkT (by positivity)) (by positivity)
    linarith
  refine ⟨by linarith, by linarith, by linarith, hYpos, ?_⟩
  have hsum : 2 * (ω + (η + γ) * M * PN + (k : ℝ) ^ T * n * ε) / (cov ^ T - eH) +
      n * (2 * (k : ℝ) ^ T * ε / (cov ^ T - eH)) =
      (2 * ω + 2 * (τ * M) + 4 * (n : ℝ) * (k : ℝ) ^ T * ε) / (cov ^ T - eH) := by
    rw [hτ]; field_simp; ring
  rw [hsum, div_lt_iff₀ hYpos]
  linarith

/-! ### Success on a good cut -/

theorem accγ_le_accη (n t : ℕ) : (Algorithm.accγ n t : ℝ) ≤ Algorithm.accη n t := by
  unfold Algorithm.accγ Algorithm.accη
  push_cast
  gcongr
  · norm_num
  · omega

theorem accη_pos (n t : ℕ) : (0 : ℝ) < Algorithm.accη n t := by
  unfold Algorithm.accη; push_cast; positivity

theorem accγ_pos (n t : ℕ) : (0 : ℝ) < Algorithm.accγ n t := by
  unfold Algorithm.accγ; push_cast; positivity

/-- The certificate's bound `ω = F_t⁴ (n - k) c⁴`, `c = 2n / (k (1 - q)^(2t + 1))`. -/
noncomputable def omegaOf (n k t : ℕ) (q : ℝ) : ℝ :=
  (∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ^ 4 * ((n : ℝ) - k) *
    (2 * n / ((k : ℝ) * (1 - q) ^ (2 * t + 1))) ^ 4

/-- The certificate's norm `M = ((n + 2t + 2)²)^(15t + 28)`. -/
noncomputable def normOf (n t : ℕ) : ℝ := (((n : ℝ) + 2 * t + 2) ^ 2) ^ (15 * t + 28)

/-- **The algorithm succeeds on a good cut.** Let `U` be the planted set and `R` the random graph.
If some `R'` contains the cut of `R` and has a good cut for `q ∈ [1/2, 1)`, the cut of `R` has no
biclique with `Δ` vertices in `U`, and the numerical conditions hold, then for every coin string
the output on `G = Adv.graph U R` is a list of `k`-cliques of `G`, containing `U`, of at most
`(n/k)(1 + 2nΔ/k²)` entries. -/
theorem succeeds_of_good {n k t : ℕ} (ht : 1 ≤ t) {q : ℝ} (hq : 1 / 2 ≤ q) (hq1 : q < 1)
    (Adv : Adversary n) {U : Finset (Fin n)} (hU : U.card = k) {R R' : SimpleGraph (Fin n)}
    (hRR' : ∀ u ∈ U, ∀ v ∈ Uᶜ, R.Adj u v → R'.Adj u v) (hgood : Random.Good U q t δ₀ R')
    (hnb : Random.NoBiclique U (Algorithm.rootCeil n (2 * t)) R)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (hX : 32 * n * Real.log (400 * t * n ^ (2 * t)) ≤ ((k : ℝ) * (1 - q) ^ (2 * t + 1)) ^ 2)
    (hmain : 4 * omegaOf n k t q * (2 * n / (k : ℝ) ^ 2) ^ (4 * t) ≤ 1 / 8)
    (htiny : ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) * 2 ^ (2 * (n + 2) ^ 3) *
      roundZ n (4 * t) (normOf n t) ≤ 1)
    (hlam : (Algorithm.accγ n t : ℝ) / (Algorithm.accη n t + Algorithm.accγ n t) * (5 * n) ≤ 1 / 8)
    (hηγ : (Algorithm.accη n t : ℝ) + Algorithm.accγ n t ≤ 1 / 8)
    (hΔk : Algorithm.rootCeil n (2 * t) ≤ k) (h2 : 2 * n * Algorithm.rootCeil n (2 * t) ≤ k ^ 2)
    {bound : ℝ} (hbound : n / k * (1 + 2 * n * Algorithm.rootCeil n (2 * t) / (k : ℝ) ^ 2) ≤ bound)
    (r : List Bool) :
    Succeeds k (Adv.graph U R) U bound (Algorithm.alg t (input (Adv.graph U R) k, r)) := by
  classical
  set G := Adv.graph U R
  have hS : G.IsNClique k U := by
    refine ⟨fun u hu v hv huv ↦ Adv.clique U R u hu v hv huv, hU⟩
  obtain ⟨E, hA, hopt, hcl, hmem, hlen⟩ := Algorithm.alg_spec (t := t) G hS r
  set L := Algorithm.nonEdges n (adjBits G)
  have hLc := Algorithm.listsNonEdges G
  have hLs := Algorithm.onlyNonEdges G
  have hLlen : L.length ≤ n ^ 2 := length_nonEdges_le n _
  have hcutR : ∀ u ∈ U, ∀ v ∉ U, G.Adj u v → R.Adj u v := fun u hu v hv h ↦
    Adv.cut U R u v hu hv h
  have hcutG : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → R'.Adj u v := fun u hu v hv h ↦
    hRR' u hu v hv (hcutR u hu v (mem_compl.1 hv) h)
  have hcert := certificate_good hLc hU hcutG hq hq1 ht hk hkn hgood hX
  have hUc : (Uᶜ.card : ℝ) = n - k := by
    rw [card_compl, Fintype.card_fin, hU, Nat.cast_sub hkn]
  rw [hUc] at hcert
  -- The rounding.
  have hPN := constraintNorm_le (ℓ := 8 * t + 6) hkn hLlen
  have hPN0 := Rounding.constraintNorm_nonneg n k (8 * t + 6) L
  have hM0 : 0 ≤ normOf n t := by unfold normOf; positivity
  have hZ0 : 0 ≤ roundZ n (4 * t) (normOf n t) := by unfold roundZ; positivity
  have hηγ0 : (0 : ℝ) ≤ Algorithm.accη n t + Algorithm.accγ n t := by
    have := accη_pos n t; have := accγ_pos n t; linarith
  have htiny' : ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) *
      Rounding.constraintNorm n k (8 * t + 6) L * roundZ n (4 * t) (normOf n t) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPN hηγ0) hZ0) htiny
  obtain ⟨h1, h2', h3, h4, h5⟩ := round_numeric (n := n) (k := k) (T := 4 * t)
    (accη_pos n t) (accγ_pos n t) hPN0 hM0 hk hkn hkk hmain htiny' hlam hηγ rfl rfl rfl
  obtain ⟨Q, hQ⟩ := Rounding.exists_round_eq (ℓ := Algorithm.deg t) (T := 4 * t)
    (D := 8 * t + 6) hS hLc hLs (accη_pos n t) (accγ_pos n t) (accγ_le_accη n t) hA hopt
    (by simp only [Algorithm.deg]; omega) (by simp only [Algorithm.deg]; omega) hcert h1 h2' h3 h4
    h5
  refine ⟨?_, hcl, ?_⟩
  · exact hmem Q U hQ hS fun S' hS' hne ↦ Cleanup.card_inter_lt hU hnb hcutR hS' hne
  · exact (hlen (by omega) hΔk h2).trans hbound

/-! ### Consequences of the size condition -/

section Size

variable {ε : ℝ} {t n k : ℕ} {p : ℝ}

/-- `k ≥ n^(1/2 + ε)`. -/
theorem le_k (hp : 0 ≤ p) (hp1 : p < 1) (hε : 0 < ε)
    (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k) : (n : ℝ) ^ (1 / 2 + ε) ≤ k := by
  have h1 : (1 - p) ^ (1 / ε) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have h0 : 0 < (1 - p) ^ (1 / ε) := Real.rpow_pos_of_pos (by linarith) _
  refine le_trans ?_ hsize
  rw [le_div_iff₀ h0]
  exact mul_le_of_le_one_right (by positivity) h1

/-- `k (1 - q)^(2t + 1) ≥ 2^-(2t + 1) n^(1/2 + ε)` for `q = max p (1/2)`, when `(2t + 1) ε ≤ 1`. -/
theorem le_X (hp : 0 ≤ p) (hp1 : p < 1) (hε : 0 < ε) (ht : (2 * (t : ℝ) + 1) * ε ≤ 1)
    (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k) :
    (1 / 2) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 + ε) ≤ k * (1 - max p (1 / 2)) ^ (2 * t + 1) := by
  rcases le_total p (1 / 2) with h | h
  · rw [max_eq_right h, mul_comm, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    exact mul_le_mul_of_nonneg_right (le_k hp hp1 hε hsize) (by positivity)
  · rw [max_eq_left h]
    have hb : 0 < 1 - p := by linarith
    have h0 : 0 < (1 - p) ^ (1 / ε) := Real.rpow_pos_of_pos hb _
    have hk : (n : ℝ) ^ (1 / 2 + ε) ≤ k * (1 - p) ^ (1 / ε) := by
      rwa [div_le_iff₀ h0] at hsize
    -- `(1 - p)^(1/ε) ≤ (1 - p)^(2t + 1)`, as `2t + 1 ≤ 1/ε` and `1 - p ≤ 1`.
    have hexp : (1 - p) ^ (1 / ε) ≤ (1 - p) ^ (2 * t + 1) := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_ge hb (by linarith) ?_
      rw [le_div_iff₀ hε]
      push_cast
      linarith
    have : (n : ℝ) ^ (1 / 2 + ε) ≤ k * (1 - p) ^ (2 * t + 1) :=
      hk.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have h2 : (1 / 2 : ℝ) ^ (2 * t + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 2 + ε)]

/-- `1 - p ≥ n^(-ε/2)`, when `k ≤ n`. -/
theorem one_sub_ge (hp1 : p < 1) (hε : 0 < ε) (hn : 1 ≤ n)
    (hkn : k ≤ n) (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k) :
    (n : ℝ) ^ (-(ε / 2)) ≤ 1 - p := by
  have hb : 0 < 1 - p := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 < (1 - p) ^ (1 / ε) := Real.rpow_pos_of_pos hb _
  have hk : (n : ℝ) ^ (1 / 2 + ε) ≤ n * (1 - p) ^ (1 / ε) := by
    rw [div_le_iff₀ h0] at hsize
    exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) h0.le)
  -- `n^(ε - 1/2) ≤ (1 - p)^(1/ε)`.
  have h1 : (n : ℝ) ^ (ε - 1 / 2) ≤ (1 - p) ^ (1 / ε) := by
    have : (n : ℝ) ^ (1 / 2 + ε) = n * (n : ℝ) ^ (ε - 1 / 2) := by
      rw [show (1 / 2 + ε) = 1 + (ε - 1 / 2) by ring, Real.rpow_add hn0, Real.rpow_one]
    rw [this] at hk
    exact le_of_mul_le_mul_left hk hn0
  -- Raise to the power `ε`.
  have h2 : ((n : ℝ) ^ (ε - 1 / 2)) ^ ε ≤ ((1 - p) ^ (1 / ε)) ^ ε :=
    Real.rpow_le_rpow (by positivity) h1 hε.le
  rw [← Real.rpow_mul hn0.le, ← Real.rpow_mul hb.le, one_div_mul_cancel hε.ne', Real.rpow_one] at h2
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ?_) h2
  nlinarith

end Size

/-! ### Large `n` -/

/-- The list-size slack `δ(n) = 2Δ / n^(2ε)`, with `Δ = ⌈n^(1/(2t))⌉`. -/
noncomputable def δOf (ε : ℝ) (t n : ℕ) : ℝ := 2 * Algorithm.rootCeil n (2 * t) / (n : ℝ) ^ (2 * ε)

/-- The conditions on `n` alone under which the algorithm succeeds on good cuts. -/
structure Large (ε : ℝ) (t n : ℕ) : Prop where
  one_le : 1 ≤ n
  log_le : 32 * Real.log (400 * t * n ^ (2 * t)) ≤
    ((1 / 2 : ℝ) ^ (2 * t + 1)) ^ 2 * (n : ℝ) ^ (2 * ε)
  main : 4 * ((2 * t + 1 : ℝ) ^ t) ^ 4 * n *
      (2 * n / ((1 / 2 : ℝ) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 + ε))) ^ 4 *
      (2 * n / ((n : ℝ) ^ (1 / 2 + ε)) ^ 2) ^ (4 * t) ≤ 1 / 8
  tiny : ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) * 2 ^ (2 * (n + 2) ^ 3) *
      roundZ n (4 * t) (normOf n t) ≤ 1
  lam : (Algorithm.accγ n t : ℝ) / (Algorithm.accη n t + Algorithm.accγ n t) * (5 * n) ≤ 1 / 8
  acc : (Algorithm.accη n t : ℝ) + Algorithm.accγ n t ≤ 1 / 8
  nb : (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) ^ (ε / 2)) ≤ 1 / 400
  list : 2 * ((n : ℝ) ^ (1 / (2 * t : ℝ)) + 1) ≤ (n : ℝ) ^ (2 * ε)

theorem rpow_half_add_sq {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) :
    ((n : ℝ) ^ (1 / 2 + ε)) ^ 2 = n * (n : ℝ) ^ (2 * ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, show (1 / 2 + ε) * ((2 : ℕ) : ℝ) = 1 + 2 * ε by
    push_cast; ring, Real.rpow_add hn0, Real.rpow_one]

/-- **Success for large `n`**, for every admissible `p` and `k`. -/
theorem succeeds_of_large {ε : ℝ} {t n : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (ht : (2 * (t : ℝ) + 1) * ε ≤ 1) (ht1 : 1 ≤ t) (hL : Large ε t n) {p : ℝ} (hp : 0 ≤ p)
    (hp1 : p < 1) {k : ℕ} (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k) (hkn : k ≤ n)
    (Adv : Adversary n) {U : Finset (Fin n)} (hU : U.card = k) {R R' : SimpleGraph (Fin n)}
    (hRR' : ∀ u ∈ U, ∀ v ∈ Uᶜ, R.Adj u v → R'.Adj u v)
    (hgood : Random.Good U (max p (1 / 2)) t δ₀ R')
    (hnb : Random.NoBiclique U (Algorithm.rootCeil n (2 * t)) R) (r : List Bool) :
    Succeeds k (Adv.graph U R) U ((1 + δOf ε t n) * n / k)
      (Algorithm.alg t (input (Adv.graph U R) k, r)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hL.one_le
  have hn0 : (0 : ℝ) < n := by linarith
  have hka := le_k hp hp1 hε hsize
  have hna1 : 1 ≤ (n : ℝ) ^ (1 / 2 + ε) := Real.one_le_rpow hn1 (by linarith)
  have hk1 : (1 : ℝ) ≤ k := hna1.trans hka
  have hk : 1 ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hn2ε : 1 ≤ (n : ℝ) ^ (2 * ε) := Real.one_le_rpow hn1 (by linarith)
  have hksq : n * (n : ℝ) ^ (2 * ε) ≤ (k : ℝ) ^ 2 := by
    rw [← rpow_half_add_sq hL.one_le]
    exact pow_le_pow_left₀ (by positivity) hka 2
  have hkk : n ≤ k ^ 2 := by
    have : (n : ℝ) ≤ (k : ℝ) ^ 2 := le_trans (le_mul_of_one_le_right hn0.le hn2ε) hksq
    exact_mod_cast this
  set q := max p (1 / 2) with hq
  have hq1 : 1 / 2 ≤ q := le_max_right _ _
  have hq2 : q < 1 := max_lt hp1 (by norm_num)
  have hXb := le_X hp hp1 hε ht hsize
  rw [← hq] at hXb
  set κ : ℝ := (1 / 2) ^ (2 * t + 1) with hκ
  have hκ0 : 0 < κ := by positivity
  have hX0 : 0 < κ * (n : ℝ) ^ (1 / 2 + ε) := by positivity
  -- The certificate's condition.
  have hX : 32 * n * Real.log (400 * t * n ^ (2 * t)) ≤ ((k : ℝ) * (1 - q) ^ (2 * t + 1)) ^ 2 := by
    have h1 : (κ * (n : ℝ) ^ (1 / 2 + ε)) ^ 2 ≤ ((k : ℝ) * (1 - q) ^ (2 * t + 1)) ^ 2 :=
      pow_le_pow_left₀ hX0.le hXb 2
    have h2 : (κ * (n : ℝ) ^ (1 / 2 + ε)) ^ 2 = n * (κ ^ 2 * (n : ℝ) ^ (2 * ε)) := by
      rw [mul_pow, rpow_half_add_sq hL.one_le]; ring
    have h3 := mul_le_mul_of_nonneg_left hL.log_le hn0.le
    nlinarith
  -- The main term.
  have hmain : 4 * omegaOf n k t q * (2 * n / (k : ℝ) ^ 2) ^ (4 * t) ≤ 1 / 8 := by
    refine le_trans ?_ hL.main
    unfold omegaOf
    have hF : (∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ≤ (2 * t + 1 : ℝ) ^ t := by
      exact_mod_cast sum_stirlingCoeff_le t
    have hF0 : 0 ≤ (∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) := by positivity
    have hnk : (n : ℝ) - k ≤ n := by linarith
    have hnk0 : 0 ≤ (n : ℝ) - k := by have : (k : ℝ) ≤ n := by exact_mod_cast hkn
                                      linarith
    have hc : 2 * n / ((k : ℝ) * (1 - q) ^ (2 * t + 1)) ≤ 2 * n / (κ * (n : ℝ) ^ (1 / 2 + ε)) :=
      div_le_div_of_nonneg_left (by positivity) hX0 hXb
    have hd : 2 * n / (k : ℝ) ^ 2 ≤ 2 * n / ((n : ℝ) ^ (1 / 2 + ε)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hka 2)
    have hc0 : 0 ≤ 2 * n / ((k : ℝ) * (1 - q) ^ (2 * t + 1)) := by
      have : 0 < 1 - q := by linarith
      positivity
    calc _ = 4 * (∑ m ∈ range (t + 1), (stirlingCoeff t m : ℝ)) ^ 4 * ((n : ℝ) - k) *
          (2 * n / ((k : ℝ) * (1 - q) ^ (2 * t + 1))) ^ 4 * (2 * n / (k : ℝ) ^ 2) ^ (4 * t) := by
          ring
      _ ≤ _ := by gcongr
  -- The list size.
  have hΔle := rootCeil_le (m := 2 * t) (by omega) hL.one_le
  push_cast at hΔle
  have hlist := hL.list
  have hΔ2 : 2 * (Algorithm.rootCeil n (2 * t) : ℝ) ≤ (n : ℝ) ^ (2 * ε) := by linarith
  have hΔk : Algorithm.rootCeil n (2 * t) ≤ k := by
    have h1 : (n : ℝ) ^ (2 * ε) ≤ (n : ℝ) ^ (1 / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have : (Algorithm.rootCeil n (2 * t) : ℝ) ≤ k := by
      have := Nat.cast_nonneg (α := ℝ) (Algorithm.rootCeil n (2 * t))
      linarith
    exact_mod_cast this
  have h2 : 2 * n * Algorithm.rootCeil n (2 * t) ≤ k ^ 2 := by
    have : 2 * (n : ℝ) * Algorithm.rootCeil n (2 * t) ≤ (k : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hΔ2 hn0.le
      nlinarith
    exact_mod_cast this
  have hbound : n / k * (1 + 2 * n * Algorithm.rootCeil n (2 * t) / (k : ℝ) ^ 2) ≤
      (1 + δOf ε t n) * n / k := by
    have hδ : 2 * n * (Algorithm.rootCeil n (2 * t) : ℝ) / (k : ℝ) ^ 2 ≤ δOf ε t n := by
      unfold δOf
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : (0 : ℝ) ≤ 2 * Algorithm.rootCeil n (2 * t) := by positivity
      have := mul_le_mul_of_nonneg_left hksq h0
      nlinarith
    calc (n : ℝ) / k * (1 + 2 * n * Algorithm.rootCeil n (2 * t) / (k : ℝ) ^ 2) ≤
          n / k * (1 + δOf ε t n) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (1 + δOf ε t n) * n / k := by ring
  exact succeeds_of_good ht1 hq1 hq2 Adv hU hRR' hgood hnb hk hkn hkk hX hmain hL.tiny hL.lam
    hL.acc hΔk h2 hbound r

/-! ### Asymptotics -/

theorem tendsto_natCast_rpow {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ r) atTop atTop :=
  (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop

theorem eventually_le_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ r :=
  (tendsto_natCast_rpow hr).eventually_ge_atTop c

theorem eventually_log_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * (n : ℝ) ^ r := by
  have h := ((isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop).bound hc
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rwa [abs_of_nonneg h1, abs_of_nonneg (by positivity)] at hn

theorem eventually_rpow_neg_le {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-b) ≤ c :=
  ((tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hc)

theorem eventually_pow_div_two_pow_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ m / 2 ^ n ≤ c :=
  (tendsto_pow_const_div_const_pow_of_one_lt m one_lt_two).eventually (ge_mem_nhds hc)

/-- The logarithm condition. -/
theorem eventually_log_cond {ε : ℝ} (hε : 0 < ε) (t : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 32 * Real.log (400 * t * n ^ (2 * t)) ≤ κ * (n : ℝ) ^ (2 * ε) := by
  have h1 := eventually_le_rpow (64 * |Real.log (400 * t)| / κ) (by linarith : 0 < 2 * ε)
  have h2 := eventually_log_le (by positivity : 0 < κ / (128 * ((t : ℝ) + 1)))
    (by linarith : 0 < 2 * ε)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn1 hn2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (2 * ε) := by positivity
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Nat.cast_zero, mul_zero, zero_mul, Real.log_zero]
    positivity
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h3 : 32 * Real.log (400 * t) ≤ κ * (n : ℝ) ^ (2 * ε) / 2 := by
    have := (div_le_iff₀ hκ).1 hn1
    have := le_abs_self (Real.log (400 * t))
    nlinarith
  have h4 : 32 * (((2 * t : ℕ) : ℝ) * Real.log n) ≤ κ * (n : ℝ) ^ (2 * ε) / 2 := by
    push_cast
    have h5 : 64 * (t : ℝ) * Real.log n ≤
        64 * t * (κ / (128 * ((t : ℝ) + 1)) * (n : ℝ) ^ (2 * ε)) :=
      mul_le_mul_of_nonneg_left hn2 (by positivity)
    have h6 : 64 * (t : ℝ) * (κ / (128 * ((t : ℝ) + 1)) * (n : ℝ) ^ (2 * ε)) ≤
        κ * (n : ℝ) ^ (2 * ε) / 2 := by
      rw [show 64 * (t : ℝ) * (κ / (128 * ((t : ℝ) + 1)) * (n : ℝ) ^ (2 * ε)) =
        (t / (t + 1)) * (κ * (n : ℝ) ^ (2 * ε) / 2) by field_simp; ring]
      have : (t : ℝ) / (t + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ κ * (n : ℝ) ^ (2 * ε) / 2 := by positivity
      nlinarith
    linarith
  linarith

/-- The main term as a power of `n`. -/
theorem main_eq {ε : ℝ} {t n : ℕ} (hn : 1 ≤ n) :
    4 * ((2 * t + 1 : ℝ) ^ t) ^ 4 * n *
      (2 * n / ((1 / 2 : ℝ) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 + ε))) ^ 4 *
      (2 * n / ((n : ℝ) ^ (1 / 2 + ε)) ^ 2) ^ (4 * t) =
    4 * ((2 * t + 1 : ℝ) ^ t) ^ 4 * (2 / (1 / 2 : ℝ) ^ (2 * t + 1)) ^ 4 * 2 ^ (4 * t) *
      (n : ℝ) ^ (3 - (8 * t + 4) * ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : 2 * n / ((1 / 2 : ℝ) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 + ε)) =
      2 / (1 / 2 : ℝ) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 - ε) := by
    rw [show (1 / 2 - ε) = 1 - (1 / 2 + ε) by ring, Real.rpow_sub hn0, Real.rpow_one]
    field_simp
  have e2 : 2 * n / ((n : ℝ) ^ (1 / 2 + ε)) ^ 2 = 2 * (n : ℝ) ^ (-(2 * ε)) := by
    rw [rpow_half_add_sq hn, Real.rpow_neg hn0.le]
    field_simp
  rw [e1, e2, mul_pow, mul_pow]
  have e3 : (n : ℝ) * ((n : ℝ) ^ (1 / 2 - ε)) ^ 4 * ((n : ℝ) ^ (-(2 * ε))) ^ (4 * t) =
      (n : ℝ) ^ (3 - (8 * t + 4) * ε) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 - ε)), ← Real.rpow_natCast ((n : ℝ) ^ (-(2 * ε))),
      ← Real.rpow_mul hn0.le, ← Real.rpow_mul hn0.le]
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  rw [← e3]
  ring

/-- The main condition. -/
theorem eventually_main {ε : ℝ} {t : ℕ} (hmain : 3 < (8 * (t : ℝ) + 4) * ε) :
    ∀ᶠ n : ℕ in atTop, 4 * ((2 * t + 1 : ℝ) ^ t) ^ 4 * n *
      (2 * n / ((1 / 2 : ℝ) ^ (2 * t + 1) * (n : ℝ) ^ (1 / 2 + ε))) ^ 4 *
      (2 * n / ((n : ℝ) ^ (1 / 2 + ε)) ^ 2) ^ (4 * t) ≤ 1 / 8 := by
  set K := 4 * ((2 * t + 1 : ℝ) ^ t) ^ 4 * (2 / (1 / 2 : ℝ) ^ (2 * t + 1)) ^ 4 * 2 ^ (4 * t)
  have hK : 0 < K := by positivity
  have h := eventually_rpow_neg_le (b := (8 * t + 4) * ε - 3) (by linarith)
    (by positivity : 0 < 1 / (8 * K))
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  rw [main_eq hn1, show (3 - (8 * (t : ℝ) + 4) * ε) = -((8 * t + 4) * ε - 3) by ring]
  change K * _ ≤ _
  calc K * (n : ℝ) ^ (-((8 * t + 4) * ε - 3)) ≤ K * (1 / (8 * K)) :=
        mul_le_mul_of_nonneg_left hn hK.le
    _ = 1 / 8 := by field_simp

/-- The degree of the polynomial bound on `roundZ`. -/
def zm (t : ℕ) : ℕ := 2 * (4 * t) + 1 + 2 * (15 * t + 28)

/-- The constant of the polynomial bound on `roundZ`. -/
noncomputable def zK (t : ℕ) : ℝ :=
  16 * 2 ^ (4 * t) * (2 + 8 * 10 ^ (4 * t + 1)) + 4 * ((4 * t : ℕ) : ℝ) ^ 2 * 30 ^ (4 * t) *
    2 ^ (4 * t) + 16 * 10 ^ (4 * t + 1)

theorem roundZ_le (n t : ℕ) :
    roundZ n (4 * t) (normOf n t) ≤ zK t * ((n : ℝ) + 2 * t + 2) ^ zm t := by
  unfold roundZ normOf zK zm
  set N := (n : ℝ) + 2 * t + 2 with hN
  set T := 4 * t
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hN1 : 1 ≤ N := by rw [hN]; linarith
  have hnN : (n : ℝ) ≤ N := by rw [hN]; linarith
  have hpow : ∀ a b : ℕ, a ≤ b → N ^ a ≤ N ^ b := fun a b h ↦ pow_le_pow_right₀ hN1 h
  have h2n : (2 * (n : ℝ)) ^ T ≤ 2 ^ T * N ^ T := by
    rw [mul_pow]; gcongr
  have h30 : (30 * (n : ℝ) + 20) ^ T ≤ 30 ^ T * N ^ T := by
    rw [← mul_pow]; gcongr; rw [hN]; nlinarith
  have hnT : (n : ℝ) ^ (T + 1) ≤ N ^ (T + 1) := by gcongr
  have hM : (N ^ 2) ^ (15 * t + 28) = N ^ (2 * (15 * t + 28)) := by rw [← pow_mul]
  rw [hM]
  set m := 2 * T + 1 + 2 * (15 * t + 28)
  have e1 : N ^ T * N ^ (2 * (15 * t + 28)) ≤ N ^ m := by
    rw [← pow_add]; exact hpow _ _ (by omega)
  have e2 : N ^ T * N ^ (T + 1) ≤ N ^ m := by rw [← pow_add]; exact hpow _ _ (by omega)
  have e3 : N ^ T * N ^ T ≤ N ^ m := by rw [← pow_add]; exact hpow _ _ (by omega)
  have e4 : 1 ≤ N ^ m := one_le_pow₀ hN1
  have h1 : 16 * (2 * (n : ℝ)) ^ T * (2 * N ^ (2 * (15 * t + 28)) +
      8 * (n : ℝ) ^ (T + 1) * 10 ^ (T + 1)) ≤ 16 * (2 ^ T * N ^ T) * (2 * N ^ (2 * (15 * t + 28)) +
        8 * N ^ (T + 1) * 10 ^ (T + 1)) := by gcongr
  have h2 : 4 * ((T : ℕ) : ℝ) ^ 2 * (30 * (n : ℝ) + 20) ^ T * (2 * (n : ℝ)) ^ T ≤
      4 * ((T : ℕ) : ℝ) ^ 2 * (30 ^ T * N ^ T) * (2 ^ T * N ^ T) := by gcongr
  have hP2 : (0 : ℝ) ≤ 2 ^ T := by positivity
  have hP10 : (0 : ℝ) ≤ 10 ^ (T + 1) := by positivity
  have hP30 : (0 : ℝ) ≤ 30 ^ T := by positivity
  have hT2 : (0 : ℝ) ≤ ((T : ℕ) : ℝ) ^ 2 := by positivity
  -- Name the powers, so that `linarith` sees atoms.
  generalize N ^ T = A at *
  generalize N ^ (2 * (15 * t + 28)) = B at *
  generalize N ^ (T + 1) = D at *
  generalize N ^ m = Q at *
  generalize (2 : ℝ) ^ T = P2 at *
  generalize (10 : ℝ) ^ (T + 1) = P10 at *
  generalize (30 : ℝ) ^ T = P30 at *
  have f1 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 32 * P2)
  have f2 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 128 * P2 * P10)
  have f3 := mul_le_mul_of_nonneg_left e3
    (by positivity : (0 : ℝ) ≤ 4 * ((T : ℕ) : ℝ) ^ 2 * P30 * P2)
  have f4 := mul_le_mul_of_nonneg_left e4 (by positivity : (0 : ℝ) ≤ 16 * P10)
  nlinarith [h1, h2, f1, f2, f3, f4]

theorem cast_accη (n t : ℕ) : (Algorithm.accη n t : ℝ) = 1 / 2 ^ Algorithm.accExp n t := by
  unfold Algorithm.accη; push_cast; rfl

theorem cast_accγ (n t : ℕ) : (Algorithm.accγ n t : ℝ) = 1 / 2 ^ (2 * Algorithm.accExp n t) := by
  unfold Algorithm.accγ; push_cast; rfl

theorem accExp_ge (n t : ℕ) : 2 * (n + 2) ^ 3 + n ≤ Algorithm.accExp n t := by
  unfold Algorithm.accExp
  have h1 : (n + 2) ^ 4 ≤ (n + 2) ^ 4 * (t + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : (n + 2) ^ 4 = (n + 2) * (n + 2) ^ 3 := by ring
  have h4 : (n + 2) * (n + 2) ^ 3 = 2 * (n + 2) ^ 3 + n * (n + 2) ^ 3 := by ring
  have h5 : n ≤ n * (n + 2) ^ 3 := Nat.le_mul_of_pos_right n (by positivity)
  rw [h2] at h1
  linarith

theorem acc_sum_le (n t : ℕ) :
    (Algorithm.accη n t : ℝ) + Algorithm.accγ n t ≤ 2 / 2 ^ Algorithm.accExp n t := by
  rw [cast_accη, cast_accγ]
  have : (1 : ℝ) / 2 ^ (2 * Algorithm.accExp n t) ≤ 1 / 2 ^ Algorithm.accExp n t :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [show (2 : ℝ) / 2 ^ Algorithm.accExp n t = 1 / 2 ^ Algorithm.accExp n t +
    1 / 2 ^ Algorithm.accExp n t by ring]
  linarith

theorem acc_le (n t : ℕ) : (Algorithm.accη n t : ℝ) + Algorithm.accγ n t ≤ 1 / 8 := by
  refine (acc_sum_le n t).trans ?_
  have h : 16 ≤ Algorithm.accExp n t := by
    have h1 := accExp_ge n t
    have h2 : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (2 : ℝ) ^ 16 ≤ 2 ^ Algorithm.accExp n t := pow_le_pow_right₀ (by norm_num) h
  linarith

theorem tiny_le (n t : ℕ) :
    ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) * 2 ^ (2 * (n + 2) ^ 3) ≤ 2 / 2 ^ n := by
  refine (mul_le_mul_of_nonneg_right (acc_sum_le n t) (by positivity)).trans ?_
  have h : (2 : ℝ) ^ (2 * (n + 2) ^ 3) * 2 ^ n ≤ 2 ^ Algorithm.accExp n t := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (accExp_ge n t)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- The solver's errors are eventually small. -/
theorem eventually_tiny (t : ℕ) :
    ∀ᶠ n : ℕ in atTop, ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) * 2 ^ (2 * (n + 2) ^ 3) *
      roundZ n (4 * t) (normOf n t) ≤ 1 := by
  have hK : 0 < zK t := by unfold zK; positivity
  have h := eventually_pow_div_two_pow_le (zm t) (by positivity : 0 < 1 / (2 * zK t * 2 ^ zm t))
  filter_upwards [h, eventually_ge_atTop (2 * t + 2)] with n hn hn2
  have hZ := roundZ_le n t
  have hZ0 : 0 ≤ roundZ n (4 * t) (normOf n t) := by unfold roundZ normOf; positivity
  have hN : (n : ℝ) + 2 * t + 2 ≤ 2 * n := by
    have : ((2 * t + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn2
    push_cast at this; linarith
  have hNm : ((n : ℝ) + 2 * t + 2) ^ zm t ≤ 2 ^ zm t * (n : ℝ) ^ zm t := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hN _
  calc ((Algorithm.accη n t : ℝ) + Algorithm.accγ n t) * 2 ^ (2 * (n + 2) ^ 3) *
        roundZ n (4 * t) (normOf n t) ≤ 2 / 2 ^ n * (zK t * (2 ^ zm t * (n : ℝ) ^ zm t)) :=
        mul_le_mul (tiny_le n t) (hZ.trans (mul_le_mul_of_nonneg_left hNm hK.le)) hZ0
          (by positivity)
    _ = 2 * zK t * 2 ^ zm t * ((n : ℝ) ^ zm t / 2 ^ n) := by ring
    _ ≤ 2 * zK t * 2 ^ zm t * (1 / (2 * zK t * 2 ^ zm t)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 1 := by field_simp

/-- The mixing weight is eventually small. -/
theorem eventually_lam (t : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (Algorithm.accγ n t : ℝ) / (Algorithm.accη n t + Algorithm.accγ n t) * (5 * n) ≤ 1 / 8 := by
  have h := eventually_pow_div_two_pow_le 1 (by positivity : (0 : ℝ) < 1 / 40)
  filter_upwards [h] with n hn
  have hη := accη_pos n t
  have hγ := accγ_pos n t
  have h1 : (Algorithm.accγ n t : ℝ) / (Algorithm.accη n t + Algorithm.accγ n t) ≤
      Algorithm.accγ n t / Algorithm.accη n t :=
    div_le_div_of_nonneg_left hγ.le hη (by linarith)
  have h2 : (Algorithm.accγ n t : ℝ) / Algorithm.accη n t ≤ 1 / 2 ^ n := by
    rw [cast_accγ, cast_accη, show (1 : ℝ) / 2 ^ (2 * Algorithm.accExp n t) /
      (1 / 2 ^ Algorithm.accExp n t) = 1 / 2 ^ Algorithm.accExp n t by rw [pow_mul']; field_simp]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by have := accExp_ge n t; omega))
  rw [pow_one] at hn
  calc (Algorithm.accγ n t : ℝ) / (Algorithm.accη n t + Algorithm.accγ n t) * (5 * n) ≤
        1 / 2 ^ n * (5 * n) := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    _ = 5 * (n / 2 ^ n) := by ring
    _ ≤ 5 * (1 / 40) := by gcongr
    _ = 1 / 8 := by norm_num

/-- The no-biclique condition. -/
theorem eventually_nb {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) ^ (ε / 2)) ≤ 1 / 400 := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / ε) 1 one_pos).comp
    (tendsto_natCast_rpow (by linarith : 0 < ε / 2))
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 400))] with n hn
  simp only [Function.comp_apply] at hn
  have e : ((n : ℝ) ^ (ε / 2)) ^ (4 / ε) = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg n), show ε / 2 * (4 / ε) = 2 by field_simp; norm_num,
      Real.rpow_two]
  rwa [e, neg_one_mul] at hn

/-- The list-size condition, when `1/(2t) < 2ε`. -/
theorem eventually_list {ε : ℝ} {t : ℕ} (h : 1 / (2 * t : ℝ) < 2 * ε) (ht : 1 ≤ t) :
    ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) ^ (1 / (2 * t : ℝ)) + 1) ≤ (n : ℝ) ^ (2 * ε) := by
  have ht0 : (0 : ℝ) < 2 * t := by have : (1 : ℝ) ≤ t := by exact_mod_cast ht
                                   linarith
  have hpos : 0 < 1 / (2 * t : ℝ) := by positivity
  have h1 := eventually_le_rpow 4 (by linarith : 0 < 2 * ε - 1 / (2 * t : ℝ))
  have h2 := eventually_le_rpow 4 (by linarith : 0 < 2 * ε)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn1 hn2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) ^ (2 * ε) =
      (n : ℝ) ^ (1 / (2 * t : ℝ)) * (n : ℝ) ^ (2 * ε - 1 / (2 * t : ℝ)) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hA : 0 ≤ (n : ℝ) ^ (1 / (2 * t : ℝ)) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hn1 hA
  rw [← e] at h3
  linarith

/-- The list-size slack tends to `0`, when `1/(2t) < 2ε`. -/
theorem tendsto_δOf {ε : ℝ} {t : ℕ} (h : 1 / (2 * t : ℝ) < 2 * ε) (ht : 1 ≤ t) :
    Tendsto (δOf ε t) atTop (𝓝 0) := by
  have hpos : 0 < 1 / (2 * t : ℝ) := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    positivity
  have hb1 : 0 < 2 * ε - 1 / (2 * t : ℝ) := by linarith
  have hb2 : 0 < 2 * ε := by linarith
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) ^ (-(2 * ε - 1 / (2 * t : ℝ))) +
      2 * (n : ℝ) ^ (-(2 * ε))) atTop (𝓝 0) := by
    have l1 := ((tendsto_rpow_neg_atTop hb1).comp tendsto_natCast_atTop_atTop).const_mul 2
    have l2 := ((tendsto_rpow_neg_atTop hb2).comp tendsto_natCast_atTop_atTop).const_mul 2
    simpa using l1.add l2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun n ↦ by unfold δOf; positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΔ := rootCeil_le (m := 2 * t) (by omega) hn
    push_cast at hΔ
    unfold δOf
    rw [div_le_iff₀ (by positivity)]
    have e1 : (n : ℝ) ^ (-(2 * ε - 1 / (2 * t : ℝ))) * (n : ℝ) ^ (2 * ε) =
        (n : ℝ) ^ (1 / (2 * t : ℝ)) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have e2 : (n : ℝ) ^ (-(2 * ε)) * (n : ℝ) ^ (2 * ε) = 1 := by
      rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]
    have e3 : (2 * (n : ℝ) ^ (-(2 * ε - 1 / (2 * t : ℝ))) + 2 * (n : ℝ) ^ (-(2 * ε))) *
        (n : ℝ) ^ (2 * ε) = 2 * (n : ℝ) ^ (1 / (2 * t : ℝ)) + 2 := by
      rw [add_mul, mul_assoc, mul_assoc, e1, e2, mul_one]
    rw [e3]
    linarith

theorem one_div_lt {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    1 / (2 * (tOf ε : ℝ)) < 2 * ε := by
  obtain ⟨h1, -, h3⟩ := tOf_spec hε hε1
  have ht : (1 : ℝ) ≤ tOf ε := by exact_mod_cast h3
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- **Eventually all the conditions hold.** -/
theorem eventually_large {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∀ᶠ n : ℕ in atTop, Large ε (tOf ε) n := by
  obtain ⟨h1, h2, h3⟩ := tOf_spec hε hε1
  have hlt := one_div_lt hε hε1
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_cond hε (tOf ε) (by positivity : (0 : ℝ) < ((1 / 2 : ℝ) ^ (2 * tOf ε + 1)) ^ 2),
    eventually_main h1, eventually_tiny (tOf ε), eventually_lam (tOf ε), eventually_nb hε,
    eventually_list hlt h3] with n hn1 hn2 hn3 hn4 hn5 hn6 hn7
  exact ⟨hn1, hn2, hn3, hn4, hn5, acc_le n _, hn6, hn7⟩

/-! ### The probability -/

section Probability

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph

theorem coinProb_eq_one {m : ℕ} {P : List Bool → Prop} (h : ∀ r, P r) : coinProb m P = 1 := by
  classical
  unfold coinProb
  rw [Finset.filter_true_of_mem fun r _ ↦ h _, Finset.card_univ]
  simp

theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb; positivity

theorem sum_geom_le {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) (m : ℕ) :
    ∑ j ∈ Icc 1 m, x ^ j ≤ 2 * x := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  refine (geom_sum_Ico_le_of_lt_one hx (by linarith)).trans ?_
  rw [pow_one, div_le_iff₀ (by linarith)]
  nlinarith

/-- **Few bicliques**: with probability at least `1 - 1/200`, the cut has no biclique with `Δ`
vertices in the planted set. -/
theorem prob_not_noBiclique_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) {t n : ℕ}
    (ht : (2 * (t : ℝ) + 1) * ε ≤ 1) (ht1 : 1 ≤ t) (hL : Large ε t n) {p : I}
    {k : ℕ} (hp1 : (p : ℝ) < 1) (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k)
    (hkn : k ≤ n) {U : Finset (Fin n)} (hU : U.card = k) :
    (G(Fin n, p)).real {R | ¬ Random.NoBiclique U (Algorithm.rootCeil n (2 * t)) R} ≤ 1 / 200 := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hL.one_le
  have hn0 : (0 : ℝ) < n := by linarith
  set Δ := Algorithm.rootCeil n (2 * t)
  refine (Random.prob_not_noBiclique U p Δ).trans ?_
  set x := (U.card : ℝ) * Uᶜ.card * (p : ℝ) ^ Δ with hx
  have hx0 : 0 ≤ x := by positivity
  -- `p^Δ ≤ exp(-(1 - p) Δ) ≤ exp(-n^(ε/2))`.
  have h1 : (p : ℝ) ≤ Real.exp (-(1 - p)) := by
    have := Real.add_one_le_exp (-(1 - (p : ℝ))); linarith
  have h2 : (p : ℝ) ^ Δ ≤ Real.exp (-((1 - p) * Δ)) := by
    calc (p : ℝ) ^ Δ ≤ Real.exp (-(1 - p)) ^ Δ := pow_le_pow_left₀ hp0 h1 Δ
      _ = Real.exp (-((1 - p) * Δ)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h3 : (n : ℝ) ^ (ε / 2) ≤ (1 - p) * Δ := by
    have hq := one_sub_ge hp1 hε hL.one_le hkn hsize
    have hΔ := rootCeil_ge (m := 2 * t) (by omega) hL.one_le
    push_cast at hΔ
    have hΔε : (n : ℝ) ^ ε ≤ (n : ℝ) ^ (1 / (2 * t : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      have : (0 : ℝ) < 2 * t := by have : (1 : ℝ) ≤ t := by exact_mod_cast ht1
                                   linarith
      rw [le_div_iff₀ this]
      linarith
    have e : (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    rw [e]
    exact mul_le_mul hq (hΔε.trans hΔ) (by positivity) (by linarith)
  have h4 : Real.exp (-((1 - p) * Δ)) ≤ Real.exp (-(n : ℝ) ^ (ε / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have hcard : (U.card : ℝ) * Uᶜ.card ≤ (n : ℝ) ^ 2 := by
    have a : (U.card : ℝ) ≤ n := by rw [hU]; exact_mod_cast hkn
    have b : (Uᶜ.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans (by simp)
    rw [sq]; exact mul_le_mul a b (by positivity) (by positivity)
  have hx1 : x ≤ 1 / 400 := by
    calc x ≤ (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) ^ (ε / 2)) :=
          mul_le_mul hcard (h2.trans h4) (by positivity) (by positivity)
      _ ≤ 1 / 400 := hL.nb
  have := sum_geom_le hx0 (by linarith) U.card
  linarith

/-- **The success probability for large `n`** is at least `0.99`, for every admissible `p` and
`k`, every planted `k`-set, every adversary, and every number of coins. -/
theorem le_successProb_of_large {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) {n : ℕ}
    (hL : Large ε (tOf ε) n) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) {k : ℕ}
    (hsize : (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k) (hkn : k ≤ n) {S : Finset (Fin n)}
    (hU : S.card = k) (Adv : Adversary n) (T : ℕ → ℕ) :
    0.99 ≤ successProb n k p S Adv (Algorithm.alg (tOf ε)) T
      ((1 + δOf ε (tOf ε) n) * n / k) := by
  classical
  obtain ⟨ht3, ht, ht1⟩ := tOf_spec hε hε1
  set t := tOf ε
  set pI : I := ⟨p, hp, hp1.le⟩
  refine le_of_le_of_eq ?_ (Random.successProb_eq pI S Adv _ T _).symm
  set E : Set (SimpleGraph (Fin n)) := {R | (∃ R', (∀ u ∈ S, ∀ v ∈ Sᶜ, R.Adj u v → R'.Adj u v) ∧
    Random.Good S (max p (1 / 2)) t δ₀ R') ∧ Random.NoBiclique S (Algorithm.rootCeil n (2 * t)) R}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  refine le_trans ?_ (Random.mul_measureReal_le_integral (μ := G(Fin n, pI)) (b := 1)
    Integrable.of_finite (fun R ↦ coinProb_nonneg _ _) hE fun R hR ↦ ?_)
  swap
  · obtain ⟨⟨R', hRR', hgood⟩, hnb⟩ := hR
    exact (coinProb_eq_one fun r ↦ succeeds_of_large hε hε1 ht ht1 hL hp hp1 hsize hkn Adv hU
      hRR' hgood hnb r).ge
  rw [one_mul]
  -- The bad events.
  have hδ₀ : (0 : ℝ) < δ₀ := by unfold δ₀; norm_num
  have hδ₀1 : δ₀ ≤ 1 := by unfold δ₀; norm_num
  have hA : (G(Fin n, pI)).real {R | ¬ ∃ R', (∀ u ∈ S, ∀ v ∈ Sᶜ, R.Adj u v → R'.Adj u v) ∧
      Random.Good S (max p (1 / 2)) t δ₀ R'} ≤ 1 / 200 := by
    rcases le_total p (1 / 2) with h | h
    · rw [max_eq_right h]
      refine (measureReal_mono (fun R hR ↦ ?_) (measure_ne_top _ _)).trans
        ((Random.prob_not_le_good_half S (p := pI) h t hδ₀ hδ₀1).trans (by unfold δ₀; norm_num))
      simp only [Set.mem_ofPred_eq] at hR ⊢
      rintro ⟨R', hle, hg⟩
      exact hR ⟨R', fun u _ v _ h' ↦ hle h', hg⟩
    · rw [max_eq_left h]
      refine (measureReal_mono (fun R hR ↦ ?_) (measure_ne_top _ _)).trans
        ((Random.prob_not_good S (p := pI) (by change (0 : ℝ) < p; linarith) hp1 t hδ₀
          hδ₀1).trans (by unfold δ₀; norm_num))
      simp only [Set.mem_ofPred_eq] at hR ⊢
      intro hg
      exact hR ⟨R, fun u _ v _ h' ↦ h', hg⟩
  have hB := prob_not_noBiclique_le hε hε1 ht ht1 hL (p := pI) hp1 hsize hkn hU
  have hsub : Eᶜ ⊆ {R | ¬ ∃ R', (∀ u ∈ S, ∀ v ∈ Sᶜ, R.Adj u v → R'.Adj u v) ∧
      Random.Good S (max p (1 / 2)) t δ₀ R'} ∪
      {R | ¬ Random.NoBiclique S (Algorithm.rootCeil n (2 * t)) R} := by
    intro R hR
    simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hR
    exact hR
  have hc : (G(Fin n, pI)).real Eᶜ ≤ 1 / 100 :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans
      (by linarith))
  have := measureReal_add_measureReal_compl (μ := G(Fin n, pI)) hE
  rw [probReal_univ] at this
  norm_num
  linarith

end Probability

end BKS23.Assembly
