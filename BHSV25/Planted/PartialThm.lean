module

public import BHSV25.Planted.StopCorrect
public import BHSV25.TimePad

/-!
# Theorem 7.12

[BHSV25, Theorem 7.12], with the additional error `ε` of `BHSV25/Challenge.lean`
(`BHSV25.Planted.plantedColoring_partial`): with `γ = 1/4`, `λ₀ = 1 / (8192 k⁴)`,
`B = 5 · 2²¹ k¹¹`, `P = (k (4k + 1))⁴ + k + 2 k²`, and for `ε > 0` the algorithm
`BHSV25.Planted.planAlgU` with the precision `4 / K` of the net, `K = ⌈65536 k⁴ / ε⌉ + 1`, and the
power `2 a n` of the filter, `a = 2 K + 8`, for all `t`.

* **The probability** (`BHSV25.Planted.unifP_plantProb_ge`): on every good coloring of a host of
  at least `(k (4k + 1))⁴` vertices, the algorithm stops after at most `(k + 1) (1 + 2²⁶ k⁸) t`
  rounds and succeeds (`BHSV25.Planted.planted_good`), and at most `(k + 2 k²) k^n / n` colorings
  are not good (`BHSV25.Planted.card_not_good_le`). Smaller hosts are covered by `P / n ≥ 1`; on a
  host without edges the planted graph has none, so the algorithm stops at once, and the error is
  at least `1`.
* **The running time** (`BHSV25.Planted.unifP_factor_le`): the machine reads its parameters
  `(k, K, a)` and the paddings `2^padP₁`, `2^padP₂` with the graph, so it runs in time
  `c₀ (|p| + 1)^C₀ ((2^padP₁ + 1) (2^padP₂ + 1))^C₀ · m^C₀`
  (`BHSV25.runsInTimeWith_graph_fix_pad`); the paddings are exponential in the number of rounds,
  so the factor is at most `D^(t + 1)` when it is at most `(k + 1) (1 + 2²⁶ k⁸) t`, for `D`
  depending only on `k` and `K`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {k : ℕ}

theorem isColoring_of_le {G : Graph} {c : List ℕ} {δ δ' : ℝ} (h : G.IsColoring k δ c)
    (hδ : δ ≤ δ') : G.IsColoring k δ' c :=
  ⟨h.1, le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) h.2⟩

theorem isColoring_of_one_le {G : Graph} {c : List ℕ} {δ : ℝ} (h : G.IsPartialColoring k c)
    (hδ : 1 ≤ δ) : G.IsColoring k δ c :=
  ⟨h, le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)⟩

theorem isColoring_of_zero {G : Graph} {c : List ℕ} {δ : ℝ} (h : G.IsPartialColoring k c)
    (hn : G.1 = 0) : G.IsColoring k δ c :=
  ⟨h, by rw [hn, Nat.cast_zero, mul_zero]; exact Nat.cast_nonneg _⟩

/-! ### The probability -/

open Classical in
/-- If every good coloring succeeds, the planted graph succeeds with probability at least
`1 - (k + 2 k²) / n`. -/
theorem plantProb_ge_of_good (hk : 0 < k) (H : Graph) (hn : 0 < H.1) {s : ℝ}
    (hX : IsWeight (fun x y ↦ H.normAdj x y) s) (E : Graph → Prop)
    (hE : ∀ χ : Fin H.1 → Fin k, Good (fun x y ↦ H.normAdj x y) χ → E (H.plant χ)) :
    1 - (k + 2 * (k : ℝ) ^ 2) / H.1 ≤ H.plantProb k E := by
  have hkn : (0 : ℝ) < (k : ℝ) ^ H.1 := by positivity
  have hbad := card_not_good_le hk hn hX (k := k)
  have hcover : (univ : Finset (Fin H.1 → Fin k)) ⊆
      (univ.filter fun χ : Fin H.1 → Fin k ↦ E (H.plant χ)) ∪
        univ.filter fun χ : Fin H.1 → Fin k ↦ ¬ Good (fun x y ↦ H.normAdj x y) χ := by
    intro χ _
    by_cases h : Good (fun x y ↦ H.normAdj x y) χ
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hE χ h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h⟩)
  have hcard : (k : ℝ) ^ H.1 ≤ ((univ.filter fun χ : Fin H.1 → Fin k ↦ E (H.plant χ)).card : ℝ) +
      (univ.filter fun χ : Fin H.1 → Fin k ↦ ¬ Good (fun x y ↦ H.normAdj x y) χ).card := by
    have h1 := (card_le_card hcover).trans (card_union_le _ _)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h1
    exact_mod_cast h1
  rw [Graph.plantProb, le_div_iff₀ hkn]
  have e : (1 - (k + 2 * (k : ℝ) ^ 2) / H.1) * (k : ℝ) ^ H.1 =
      (k : ℝ) ^ H.1 - (k + 2 * (k : ℝ) ^ 2) * ((k : ℝ) ^ H.1 / H.1) := by ring
  rw [e]
  linarith

open Classical in
/-- If every coloring succeeds, the planted graph succeeds with probability `1 ≥ 1 - P / n`. -/
theorem unifP_le_plantProb_of_forall (hk : 0 < k) (H : Graph) {P : ℝ} (hP : 0 ≤ P)
    (E : Graph → Prop) (h : ∀ χ : Fin H.1 → Fin k, E (H.plant χ)) :
    1 - P / H.1 ≤ H.plantProb k E := by
  have h1 : H.plantProb k E = 1 := by
    rw [Graph.plantProb, filter_true_of_mem fun χ _ ↦ h χ, card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
    push_cast
    exact div_self (by positivity)
  rw [h1]
  have : 0 ≤ P / H.1 := by positivity
  linarith

/-! ### The budgets -/

/-- The constant `c = (k + 1) (1 + 2²⁶ k⁸)` with `numT k t = c t`. -/
def unifP_numC (k : ℕ) : ℕ := (k + 1) * (1 + 2 ^ 26 * k ^ 8)

/-- `numT k t = c t` for the constant `c = unifP_numC k`. -/
theorem unifP_numT_eq (k t : ℕ) : numT k t = unifP_numC k * t := by
  unfold numT unifP_numC; ring

/-- `2^a + 1 ≤ 2^(a + 1)`. -/
theorem unifP_two_pow_succ_le (a : ℕ) : 2 ^ a + 1 ≤ 2 ^ (a + 1) := by
  have := Nat.one_le_two_pow (n := a)
  rw [pow_succ]
  omega

/-- **The budget of the net**: `(3 + 12 K)^T ≤ 2^padP₁` for the number `T` of rounds. -/
theorem unifP_budget₁ (k K a : ℕ) (x : ℕ × List Bool) :
    (3 + 12 * K) ^ roundsP (k, K, a) x ≤ 2 ^ padP₁ (k, K, a) x := by
  rw [padP₁, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _

/-- **The budgets of the tuples**: `(2^padP₁ + 1)^k ≤ 2^padP₂` and
`(2 K' + 1)^(k²) ≤ 2^padP₂`. -/
theorem unifP_budget₂ (k K a : ℕ) (x : ℕ × List Bool) :
    (2 ^ padP₁ (k, K, a) x + 1) ^ k ≤ 2 ^ padP₂ (k, K, a) x ∧
      (2 * gridK k + 1) ^ (k * k) ≤ 2 ^ padP₂ (k, K, a) x := by
  have e : padP₂ (k, K, a) x =
      k * (padP₁ (k, K, a) x + 1) + k * k * Nat.clog 2 (2 * gridK k + 1) + 1 := rfl
  constructor
  · calc (2 ^ padP₁ (k, K, a) x + 1) ^ k ≤ (2 ^ (padP₁ (k, K, a) x + 1)) ^ k :=
          Nat.pow_le_pow_left (unifP_two_pow_succ_le _) _
      _ = 2 ^ (k * (padP₁ (k, K, a) x + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ padP₂ (k, K, a) x := Nat.pow_le_pow_right (by norm_num) (by rw [e]; omega)
  · calc (2 * gridK k + 1) ^ (k * k) ≤ (2 ^ Nat.clog 2 (2 * gridK k + 1)) ^ (k * k) :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
      _ = 2 ^ (k * k * Nat.clog 2 (2 * gridK k + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ padP₂ (k, K, a) x := Nat.pow_le_pow_right (by norm_num) (by rw [e]; omega)

/-! ### The running time -/

/-- **The paddings**: for at most `c t` rounds, `(2^padP₁ + 1) (2^padP₂ + 1) ≤ Z Y^t` for
`Z = 2^(k + k² κ₂ + 3)` and `Y = 2^((κ + k κ) c)`, where `κ = ⌈log₂ (3 + 12 K)⌉` and
`κ₂ = ⌈log₂ (2 K' + 1)⌉`. -/
theorem unifP_pads_le (k K a : ℕ) (x : ℕ × List Bool) {t : ℕ}
    (hT : roundsP (k, K, a) x ≤ unifP_numC k * t) :
    (2 ^ padP₁ (k, K, a) x + 1) * (2 ^ padP₂ (k, K, a) x + 1) ≤
      2 ^ (k + k * k * Nat.clog 2 (2 * gridK k + 1) + 3) *
        (2 ^ ((Nat.clog 2 (3 + 12 * K) + k * Nat.clog 2 (3 + 12 * K)) * unifP_numC k)) ^ t := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Nat.clog 2 (3 + 12 * K) := ⟨_, rfl⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ κ₂, κ₂ = Nat.clog 2 (2 * gridK k + 1) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = roundsP (k, K, a) x := ⟨_, rfl⟩
  have e1 : padP₁ (k, K, a) x = κ * T := by rw [hκ, hTdef]; rfl
  have e2 : padP₂ (k, K, a) x = k * (padP₁ (k, K, a) x + 1) + k * k * κ₂ + 1 := by
    rw [hκ₂]; rfl
  rw [← hκ, ← hκ₂, ← pow_mul, e2, e1]
  rw [← hTdef] at hT
  have hle : (κ + k * κ) * T ≤ (κ + k * κ) * unifP_numC k * t := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ hT
  calc (2 ^ (κ * T) + 1) * (2 ^ (k * (κ * T + 1) + k * k * κ₂ + 1) + 1)
      ≤ 2 ^ (κ * T + 1) * 2 ^ (k * (κ * T + 1) + k * k * κ₂ + 1 + 1) :=
        Nat.mul_le_mul (unifP_two_pow_succ_le _) (unifP_two_pow_succ_le _)
    _ = 2 ^ (k + k * k * κ₂ + 3) * 2 ^ ((κ + k * κ) * T) := by
        rw [← pow_add, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (k + k * k * κ₂ + 3) * 2 ^ ((κ + k * κ) * unifP_numC k * t) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hle)

/-- The base `D = (c₀ + 1) ((|p| + 1) Z Y)^C₀` of the running time, for `p = (k, K, 2 K + 8)`,
`Z = 2^(k + k² κ₂ + 3)` and `Y = 2^((κ + k κ) c)` (`BHSV25.Planted.unifP_pads_le`). -/
def unifP_D (k K c₀ C₀ : ℕ) : ℕ :=
  (c₀ + 1) * (((encPPar (k, K, 2 * K + 8)).length + 1) *
    2 ^ (k + k * k * Nat.clog 2 (2 * gridK k + 1) + 3) *
    2 ^ ((Nat.clog 2 (3 + 12 * K) + k * Nat.clog 2 (3 + 12 * K)) * unifP_numC k)) ^ C₀

/-- **The factor of the running time**: for at most `c t` rounds,
`c₀ (|p| + 1)^C₀ ((2^padP₁ + 1) (2^padP₂ + 1))^C₀ ≤ D^(t + 1)`. -/
theorem unifP_factor_le (k K c₀ C₀ : ℕ) (x : ℕ × List Bool) {t : ℕ}
    (hT : roundsP (k, K, 2 * K + 8) x ≤ unifP_numC k * t) :
    (c₀ : ℝ) * (((encPPar (k, K, 2 * K + 8)).length : ℝ) + 1) ^ C₀ *
      (((2 ^ padP₁ (k, K, 2 * K + 8) x + 1) * (2 ^ padP₂ (k, K, 2 * K + 8) x + 1) : ℕ) :
        ℝ) ^ C₀ ≤ (unifP_D k K c₀ C₀ : ℝ) ^ (t + 1) := by
  have h := unifP_pads_le k K (2 * K + 8) x hT
  obtain ⟨L, hL⟩ : ∃ L, L = (encPPar (k, K, 2 * K + 8)).length + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ (k + k * k * Nat.clog 2 (2 * gridK k + 1) + 3) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y,
      Y = 2 ^ ((Nat.clog 2 (3 + 12 * K) + k * Nat.clog 2 (3 + 12 * K)) * unifP_numC k) :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M,
      M = (2 ^ padP₁ (k, K, 2 * K + 8) x + 1) * (2 ^ padP₂ (k, K, 2 * K + 8) x + 1) :=
    ⟨_, rfl⟩
  rw [← hZ, ← hY, ← hM] at h
  have hD : unifP_D k K c₀ C₀ = (c₀ + 1) * (L * Z * Y) ^ C₀ := by rw [unifP_D, hL, hZ, hY]
  have hL1 : 1 ≤ L := by omega
  have hZ1 : 1 ≤ Z := hZ ▸ Nat.one_le_two_pow
  have hY1 : 1 ≤ Y := hY ▸ Nat.one_le_two_pow
  have h1 : L * M ≤ (L * Z * Y) ^ (t + 1) := by
    calc L * M ≤ L * Z * Y ^ t := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ h
      _ ≤ (L * Z) ^ (t + 1) * Y ^ (t + 1) :=
          Nat.mul_le_mul (Nat.le_self_pow (by omega) _) (Nat.pow_le_pow_right hY1 (by omega))
      _ = (L * Z * Y) ^ (t + 1) := (mul_pow _ _ _).symm
  have h2 : c₀ * (L * M) ^ C₀ ≤ ((c₀ + 1) * (L * Z * Y) ^ C₀) ^ (t + 1) := by
    calc c₀ * (L * M) ^ C₀ ≤ (c₀ + 1) * ((L * Z * Y) ^ (t + 1)) ^ C₀ :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h1 _)
      _ = (c₀ + 1) * ((L * Z * Y) ^ C₀) ^ (t + 1) := by ring
      _ ≤ (c₀ + 1) ^ (t + 1) * ((L * Z * Y) ^ C₀) ^ (t + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) _)
      _ = ((c₀ + 1) * (L * Z * Y) ^ C₀) ^ (t + 1) := (mul_pow _ _ _).symm
  have hcast : (c₀ : ℝ) * (((encPPar (k, K, 2 * K + 8)).length : ℝ) + 1) ^ C₀ * (M : ℝ) ^ C₀ =
      ((c₀ * (L * M) ^ C₀ : ℕ) : ℝ) := by
    rw [hL]; push_cast; rw [mul_pow]; ring
  rw [← hM, hcast, hD]
  exact_mod_cast h2

/-! ### The algorithm and the probability -/

/-- **The algorithm** of Theorem 7.12 on a graph: `BHSV25.Planted.planAlgU` with the parameters
`p = (k, K, 2 K + 8)` and the paddings `2^padP₁` and `2^padP₂`. -/
noncomputable def unifP_alg (k K : ℕ) (G : Graph) : List ℕ :=
  planAlgU (k, K, 2 * K + 8) ((2 ^ padP₁ (k, K, 2 * K + 8) (G.1, adjTable G),
    2 ^ padP₂ (k, K, 2 * K + 8) (G.1, adjTable G)), (G.1, adjTable G))

/-- The factor of the running time of `BHSV25.Planted.unifP_alg`
(`BHSV25.runsInTimeWith_graph_fix_pad`). -/
noncomputable def unifP_fac (k K c₀ C₀ : ℕ) (G : Graph) : ℝ :=
  (c₀ : ℝ) * (((encPPar (k, K, 2 * K + 8)).length : ℝ) + 1) ^ C₀ *
    (((2 ^ padP₁ (k, K, 2 * K + 8) (G.1, adjTable G) + 1) *
      (2 ^ padP₂ (k, K, 2 * K + 8) (G.1, adjTable G) + 1) : ℕ) : ℝ) ^ C₀

/-- The output of `BHSV25.Planted.unifP_alg` is always a partial coloring. -/
theorem unifP_isPartialColoring (hk : 0 < k) (K : ℕ) (G : Graph) :
    G.IsPartialColoring k (unifP_alg k K G) :=
  isPartialColoring_planAlgU hk K _ _ _ (unifP_budget₂ k K _ _).1 (unifP_budget₂ k K _ _).2 G

open Classical in
/-- **The probability of Theorem 7.12**: with probability at least `1 - P / n`, the factor of
the running time is at most `D^(t + 1)` and the output is a `(k, B / (d + 1)^(1/4) + ε)`-coloring.
Hosts without vertices or edges have no rounds, and `P / n ≥ 1` for small hosts. -/
theorem unifP_plantProb_ge (hk : 3 ≤ k) {K : ℕ} (hK : 0 < K) (c₀ C₀ : ℕ) (H : Graph) {d : ℕ}
    (hreg : H.2.IsRegularOfDegree d) {t : ℕ}
    (hrank : (univ.filter fun i ↦ lamP k ≤ H.eig i).card ≤ t)
    {ε : ℝ} (hε : 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2 ≤ ε) :
    1 - ((minN k + k + 2 * k ^ 2 : ℕ) : ℝ) / H.1 ≤ H.plantProb k fun G ↦
      unifP_fac k K c₀ C₀ G ≤ (unifP_D k K c₀ C₀ : ℝ) ^ (t + 1) ∧
      G.IsColoring k (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + ε) (unifP_alg k K G) := by
  have hk0 : 0 < k := by omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hP0 : (0 : ℝ) ≤ ((minN k + k + 2 * k ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have htime : ∀ G : Graph, roundsP (k, K, 2 * K + 8) (G.1, adjTable G) ≤ unifP_numC k * t →
      unifP_fac k K c₀ C₀ G ≤ (unifP_D k K c₀ C₀ : ℝ) ^ (t + 1) :=
    fun G hT ↦ unifP_factor_le k K c₀ C₀ _ hT
  -- hosts without vertices or edges: no rounds
  have hzero : ∀ χ : Fin H.1 → Fin k, d * H.1 = 0 →
      roundsP (k, K, 2 * K + 8) ((H.plant χ).1, adjTable (H.plant χ)) ≤ unifP_numC k * t :=
    fun χ h ↦ by
      rw [roundsP_eq_zero _ (by simp) (H.plant χ)
        (Nat.le_zero.1 ((count_true_plant_le H hreg χ).trans h.le))]
      exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos H.1 with hn0 | hn0
  · exact unifP_le_plantProb_of_forall hk0 H hP0 _ fun χ ↦
      ⟨htime _ (hzero χ (by rw [hn0, mul_zero])),
        isColoring_of_zero (G := H.plant χ) (unifP_isPartialColoring hk0 K _) hn0⟩
  have hnR : (0 : ℝ) < H.1 := by exact_mod_cast hn0
  by_cases hsmall : H.1 < minN k + k + 2 * k ^ 2
  · -- small hosts: `P / n ≥ 1`
    have h1 : (1 : ℝ) ≤ ((minN k + k + 2 * k ^ 2 : ℕ) : ℝ) / H.1 := by
      rw [le_div_iff₀ hnR, one_mul]
      exact_mod_cast hsmall.le
    have h2 : 0 ≤ H.plantProb k fun G ↦
        unifP_fac k K c₀ C₀ G ≤ (unifP_D k K c₀ C₀ : ℝ) ^ (t + 1) ∧
        G.IsColoring k (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + ε) (unifP_alg k K G) := by
      unfold Graph.plantProb; positivity
    linarith
  push Not at hsmall
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- hosts without edges: every partial coloring
    refine unifP_le_plantProb_of_forall hk0 H hP0 _ fun χ ↦
      ⟨htime _ (hzero χ (by rw [hd0, zero_mul])),
        isColoring_of_one_le (G := H.plant χ) (unifP_isPartialColoring hk0 K _) ?_⟩
    have hε0 : 0 ≤ ε := le_trans (by positivity) hε
    rw [hd0, Nat.cast_zero, zero_add, Real.one_rpow, div_one, errB]
    have : (1 : ℝ) ≤ 5 * 2 ^ 21 * (k : ℝ) ^ 11 := by
      nlinarith [pow_le_pow_left₀ zero_le_one hk1 11]
    linarith
  have hmain := plantProb_ge_of_good hk0 H hn0 (isWeight_normAdj H hreg hd.ne')
    (fun G ↦ unifP_fac k K c₀ C₀ G ≤ (unifP_D k K c₀ C₀ : ℝ) ^ (t + 1) ∧
      G.IsColoring k (errB k / ((d : ℝ) + 1) ^ ((1 : ℝ) / 4) + ε) (unifP_alg k K G))
    fun χ hgood ↦ by
      obtain ⟨hT, hcol⟩ := planted_good hk hK t H hreg hd hrank χ (by omega) hgood
      refine ⟨htime _ (by rw [← unifP_numT_eq]; exact hT), ?_⟩
      have hb := unifP_budget₂ k K (2 * K + 8) ((H.plant χ).1, adjTable (H.plant χ))
      exact isColoring_of_le (hcol _ _ (unifP_budget₁ _ _ _ _) hb.1 hb.2) (by linarith)
  refine le_trans ?_ hmain
  have : ((k + 2 * (k : ℝ) ^ 2)) / H.1 ≤ ((minN k + k + 2 * k ^ 2 : ℕ) : ℝ) / H.1 := by
    refine div_le_div_of_nonneg_right ?_ hnR.le
    push_cast
    have : (0 : ℝ) ≤ minN k := Nat.cast_nonneg _
    linarith
  linarith

/-! ### The theorem -/

open Classical in
/-- **Theorem 7.12** of [BHSV25] (random planting, partial recovery), with the additional error
`ε` of `BHSV25/Challenge.lean`: one algorithm for all `t`, which on the planted graph runs in time
`D^(t + 1) · m^C` and outputs a `(k, B / (d + 1)^(1/4) + ε)`-coloring with probability at least
`1 - P / n`. -/
theorem plantedColoring_partial :
    ∃ C : ℕ, ∃ γ : ℝ, 0 < γ ∧ ∀ k : ℕ, 3 ≤ k → ∃ lam₀ B P : ℝ, 0 < lam₀ ∧
      ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∃ A : Graph → List ℕ, ∃ K : Graph → ℝ,
        RunsInTimeWith A encGraph encColoring K C ∧
        ∀ (H : Graph) (d : ℕ), H.2.IsRegularOfDegree d → ∀ t : ℕ,
          (Finset.univ.filter fun i ↦ lam₀ ≤ H.eig i).card ≤ t →
          1 - P / H.1 ≤ H.plantProb k fun G ↦ K G ≤ (D : ℝ) ^ (t + 1) ∧
            G.IsColoring k (B / ((d : ℝ) + 1) ^ γ + ε) (A G) := by
  obtain ⟨c₀, C₀, hrun⟩ := runsInTimeWith_graph_fix_pad
    (V := fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ planAlgU z.1 z.2)
    (F₁ := fun z ↦ padP₁ z.1 z.2) (F₂ := fun z ↦ padP₂ z.1 z.2)
    planAlgU_polytime padP₁_polytime padP₂_polytime
  refine ⟨C₀, 1 / 4, by norm_num, fun k hk ↦ ⟨lamP k, errB k, (minN k + k + 2 * k ^ 2 : ℕ),
    lamP_pos (by omega), fun ε hε ↦ ?_⟩⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈65536 * (k : ℝ) ^ 4 / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by omega
  have hKε : 65536 * (k : ℝ) ^ 4 / (K : ℝ) ^ 2 ≤ ε := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have h1 : 65536 * (k : ℝ) ^ 4 / ε ≤ K := by
      rw [hKdef]; push_cast
      linarith [Nat.le_ceil (65536 * (k : ℝ) ^ 4 / ε)]
    rw [div_le_iff₀ hε] at h1
    rw [div_le_iff₀ (by positivity)]
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hKK hε.le]
  exact ⟨unifP_D k K c₀ C₀, unifP_alg k K, unifP_fac k K c₀ C₀, hrun (k, K, 2 * K + 8),
    fun H d hreg t hrank ↦ unifP_plantProb_ge hk hK c₀ C₀ H hreg hrank hKε⟩

end Planted

end BHSV25
