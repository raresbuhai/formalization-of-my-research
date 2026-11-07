module

public import BBKS24.Algorithm
public import BBKS24.Recovery

/-!
# Assembly: the success probability

[BBKS24, Theorem 4.1]: the algorithm `BBKS24.Alg.alg` succeeds with probability at least `0.99`
on `SRPC(n, k, p)`, for all large `n`, every real `0 ≤ p < 1` and every `k` with
`C √n log² n max(1, (p/(1-p))⁴) ≤ k ≤ n`.

* **The pruning threshold** `Δ = ⌊k²/(n L³)⌋ + 1`, `L = ⌊log₂ n⌋ + 1`, is at most `k`, has
  `2nΔ ≤ k²` and `2nΔ/k² ≤ 2/L³ + 2/(C² log⁴ n)` (`BBKS24.Asm.delta_facts`), and the planted set
  meets every other `k`-clique in fewer than `Δ` vertices with probability at least `1 - 1/n`
  (`BBKS24.Asm.prob_not_noBiclique_le`).
* **`p ≥ 1/2`**: the grid point `q = ⌊pM⌋/M ≤ p` recovers with probability at least
  `1 - 1/400` under `G(n, q)` (`BBKS24.eventually_recovers`), hence under `G(n, p)` up to
  `C(n, 2)/M ≤ 1/(2n)` (`RandomGraph.abs_binomialRandom_sub_le`).
* **`p < 1/2`**: with `j = ⌊rM⌋`, `r = (1/2 - p)/(1 - p)`, the coins add `G(n, j/M)` and the
  result is `G(n, p')`, `1/2 - 1/M ≤ p' ≤ 1/2` (`Sampling.sum_mass_coins_sup`), where `q = 1/2`
  recovers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Finset Real RandomGraph SimpleGraph Filter
open Topology

namespace BBKS24.Asm

open Alg

/-! ### Sizes -/

theorem logN_pos (n : ℕ) : 1 ≤ logN n := by unfold logN; omega

theorem lt_two_pow_logN (n : ℕ) : n < 2 ^ logN n := Nat.lt_pow_succ_log_self (by norm_num) n

/-- `L = ⌊log₂ n⌋ + 1 ≤ 5/2 · log n` for `n ≥ 3`. -/
theorem logN_le {n : ℕ} (hn : 3 ≤ n) : (logN n : ℝ) ≤ 5 / 2 * Real.log n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hl2 := Real.log_two_gt_d9
  have : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]
    exact hlog
  have : Real.log n / Real.log 2 ≤ 3 / 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold logN
  push_cast
  linarith

/-- `M = 2^(3L) > n³`. -/
theorem cube_lt_gridM (n : ℕ) : (n : ℝ) ^ 3 < gridM n := by
  have h := lt_two_pow_logN n
  have h3 : n ^ 3 < (2 ^ logN n) ^ 3 := Nat.pow_lt_pow_left h (by norm_num)
  rw [← pow_mul, mul_comm] at h3
  exact_mod_cast h3

/-! ### The pruning threshold -/

/-- The facts about `Δ`: with `C √n log² n ≤ k ≤ n`, `C ≥ 2`, `n ≥ 3`. -/
theorem delta_facts {n k : ℕ} {C : ℝ} (hn : 3 ≤ n) (hC : 2 ≤ C)
    (hk : C * √(n : ℝ) * Real.log n ^ 2 ≤ k) (hkn : k ≤ n) :
    delta n k ≤ k ∧ 2 * n * delta n k ≤ k ^ 2 ∧
      (k : ℝ) ^ 2 / (n * logN n ^ 3) ≤ delta n k ∧
      2 * n * (delta n k : ℝ) / (k : ℝ) ^ 2 ≤
        2 / (logN n : ℝ) ^ 3 + 2 / (C ^ 2 * Real.log n ^ 4) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL2 : 2 ≤ logN n := by
    unfold logN
    have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega
  have hL2' : (2 : ℝ) ≤ logN n := by exact_mod_cast hL2
  have hL3 : (8 : ℝ) ≤ (logN n : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL2' 3
    norm_num at this
    linarith
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  -- `k² ≥ C² n log⁴ n ≥ 4 n`.
  have hk2 : C ^ 2 * n * Real.log n ^ 4 ≤ (k : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hk 2
    calc C ^ 2 * n * Real.log n ^ 4 = (C * √(n : ℝ) * Real.log n ^ 2) ^ 2 := by
          rw [mul_pow, mul_pow, hsq]; ring
      _ ≤ _ := this
  have hΛ4 : 1 ≤ Real.log n ^ 4 := one_le_pow₀ hΛ
  have hC2 : (4 : ℝ) ≤ C ^ 2 := by nlinarith
  have hk4n : 4 * (n : ℝ) ≤ (k : ℝ) ^ 2 :=
    calc 4 * (n : ℝ) = 4 * n * 1 := by ring
      _ ≤ C ^ 2 * n * Real.log n ^ 4 := by gcongr
      _ ≤ _ := hk2
  have hkpos : (0 : ℝ) < k := by nlinarith
  have hk2' : (2 : ℝ) ≤ k := by nlinarith
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hD : (n : ℝ) * logN n ^ 3 > 0 := by positivity
  -- `k²/(n L³) ≤ Δ ≤ k²/(n L³) + 1`.
  have hup : (delta n k : ℝ) ≤ (k : ℝ) ^ 2 / (n * logN n ^ 3) + 1 := by
    unfold delta
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := k ^ 2) (n := n * logN n ^ 3)
    push_cast at this
    linarith
  have hlow : (k : ℝ) ^ 2 / (n * logN n ^ 3) ≤ delta n k := by
    unfold delta
    have h := Nat.lt_div_mul_add (a := k ^ 2) (b := n * logN n ^ 3) (by positivity)
    have h' : ((k ^ 2 : ℕ) : ℝ) < ((k ^ 2 / (n * logN n ^ 3) : ℕ) : ℝ) * (n * logN n ^ 3) +
        n * logN n ^ 3 := by exact_mod_cast h
    push_cast at h' ⊢
    rw [div_le_iff₀ hD]
    linarith
  have hkL : (k : ℝ) ^ 2 / (n * logN n ^ 3) ≤ k / 8 := by
    rw [div_le_div_iff₀ hD (by norm_num)]
    have : (k : ℝ) ^ 2 * 8 ≤ k * n * 8 := by nlinarith
    nlinarith
  refine ⟨?_, ?_, hlow, ?_⟩
  · have : (delta n k : ℝ) ≤ k := by linarith
    exact_mod_cast this
  · have h1 : 2 * (n : ℝ) * delta n k ≤ (k : ℝ) ^ 2 := by
      have h2 : 2 * (n : ℝ) * ((k : ℝ) ^ 2 / (n * logN n ^ 3)) ≤ (k : ℝ) ^ 2 / 4 := by
        rw [show 2 * (n : ℝ) * ((k : ℝ) ^ 2 / (n * logN n ^ 3)) = 2 * (k : ℝ) ^ 2 / logN n ^ 3 by
          field_simp]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    exact_mod_cast h1
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * (n : ℝ) * delta n k ≤ 2 * n * ((k : ℝ) ^ 2 / (n * logN n ^ 3) + 1) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    have h2 : 2 * (n : ℝ) * ((k : ℝ) ^ 2 / (n * logN n ^ 3) + 1) =
        2 / (logN n : ℝ) ^ 3 * k ^ 2 + 2 * n := by
      field_simp
    have h3 : 2 * (n : ℝ) ≤ 2 / (C ^ 2 * Real.log n ^ 4) * k ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith

/-! ### The clique intersection -/

/-- **Few common vertices** [BBKS24, Lemma B.3, from BKS23, Lemmas 5.7, 5.8]: under `G(n, q)`,
`1/2 ≤ q < 1`, with `C √n log² n (q/(1-q))⁴ ≤ k ≤ n`, `C ≥ 12`, `n ≥ 3`, some biclique across the
cut of the planted set has `Δ` vertices inside with probability at most `1/n`. -/
theorem prob_not_noBiclique_le {n k : ℕ} {q : I} (hq : 1 / 2 ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1)
    {C : ℝ} (hC : 12 ≤ C) (hn : 3 ≤ n)
    (hsize : C * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k) (hkn : k ≤ n)
    (S : Finset (Fin n)) (hS : S.card = k) :
    (G(Fin n, q)).real {R | ¬ NoBiclique S (delta n k) R} ≤ 1 / n := by
  have hq0 : 0 < (q : ℝ) := by linarith
  obtain ⟨B, hB⟩ : ∃ B, B = pminus q := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := hB ▸ one_le_pminus hq hq1
  have hB8 : ((q : ℝ) / (1 - q)) ^ 4 = B ^ 8 := by
    rw [hB, ← pminus_sq hq1 hq0.le, ← pow_mul]
  rw [hB8] at hsize
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hk : C * √(n : ℝ) * Real.log n ^ 2 ≤ k := by
    have : C * √(n : ℝ) * Real.log n ^ 2 * 1 ≤ C * √(n : ℝ) * Real.log n ^ 2 * B ^ 8 := by
      gcongr
      exact one_le_pow₀ hB1
    linarith
  obtain ⟨-, -, hlow, -⟩ := delta_facts hn (by linarith) hk hkn
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hkpos : (0 : ℝ) < k := by
    have : 0 < C * √(n : ℝ) * Real.log n ^ 2 := by
      have := Real.sqrt_pos.2 (show (0 : ℝ) < n by linarith)
      positivity
    linarith
  -- `q^Δ ≤ n⁻⁴`.
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hk2 : C ^ 2 * n * Real.log n ^ 4 * B ^ 16 ≤ (k : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hsize 2
    calc C ^ 2 * n * Real.log n ^ 4 * B ^ 16 = (C * √(n : ℝ) * Real.log n ^ 2 * B ^ 8) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, hsq]; ring
      _ ≤ _ := this
  have hL := logN_le hn
  have hL3 : (logN n : ℝ) ^ 3 ≤ 16 * Real.log n ^ 3 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 3
    nlinarith [pow_pos (show (0 : ℝ) < Real.log n by linarith) 3]
  have h1q : 1 / (2 * B ^ 2) ≤ 1 - q := by
    rw [one_sub_eq hq0 hq1, ← hB]
    have : 1 ≤ B ^ 2 := one_le_pow₀ hB1
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hΔ : 4 * Real.log n ≤ delta n k * (1 - q) := by
    have hLpos : (0 : ℝ) < logN n := by exact_mod_cast logN_pos n
    have hB14 : 1 ≤ B ^ 14 := one_le_pow₀ hB1
    have h1 : C ^ 2 * Real.log n ^ 4 * B ^ 16 / logN n ^ 3 ≤ (k : ℝ) ^ 2 / (n * logN n ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hk2 (show (0 : ℝ) ≤ logN n ^ 3 by positivity)
      nlinarith
    have h2 : C ^ 2 * Real.log n ^ 4 / (32 * Real.log n ^ 3) * B ^ 14 ≤
        C ^ 2 * Real.log n ^ 4 * B ^ 16 / logN n ^ 3 * (1 / (2 * B ^ 2)) := by
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ C ^ 2 * Real.log n ^ 4 * B ^ 16 := by positivity
      have hB2 : 0 < B ^ 2 := by positivity
      have e1 : C ^ 2 * Real.log n ^ 4 * B ^ 14 * (logN n ^ 3 * (2 * B ^ 2)) =
          (C ^ 2 * Real.log n ^ 4 * B ^ 16) * (2 * logN n ^ 3) := by ring
      have e2 : C ^ 2 * Real.log n ^ 4 * B ^ 16 * 1 * (32 * Real.log n ^ 3) =
          (C ^ 2 * Real.log n ^ 4 * B ^ 16) * (32 * Real.log n ^ 3) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (by linarith) this
    have h3 : 4 * Real.log n ≤ C ^ 2 * Real.log n ^ 4 / (32 * Real.log n ^ 3) * B ^ 14 := by
      have hlog : 0 < Real.log n := by linarith
      have : C ^ 2 * Real.log n ^ 4 / (32 * Real.log n ^ 3) = C ^ 2 / 32 * Real.log n := by
        field_simp
      rw [this]
      have hC2 : (128 : ℝ) ≤ C ^ 2 := by nlinarith
      calc 4 * Real.log n = 4 * Real.log n * 1 := by ring
        _ ≤ C ^ 2 / 32 * Real.log n * B ^ 14 := by
            gcongr
            linarith
    calc 4 * Real.log n ≤ _ := h3
      _ ≤ _ := h2
      _ ≤ (k : ℝ) ^ 2 / (n * logN n ^ 3) * (1 - q) := by gcongr
      _ ≤ delta n k * (1 - q) := by gcongr
  have hqΔ : (q : ℝ) ^ delta n k ≤ 1 / (n : ℝ) ^ 4 := by
    have hlogq : Real.log q ≤ -(1 - q) := by
      have := Real.log_le_sub_one_of_pos hq0
      linarith
    calc (q : ℝ) ^ delta n k = Real.exp (delta n k * Real.log q) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hq0 _)]
      _ ≤ Real.exp (-(4 * Real.log n)) := by
          rw [Real.exp_le_exp]
          nlinarith [Nat.cast_nonneg (α := ℝ) (delta n k)]
      _ = 1 / (n : ℝ) ^ 4 := by
          rw [Real.exp_neg, show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num,
            ← Real.log_pow, Real.exp_log (by positivity), one_div]
  -- The first moment.
  refine (prob_not_noBiclique S q (delta n k)).trans ?_
  rw [hS]
  have hx : (k : ℝ) * (Sᶜ.card : ℝ) * (q : ℝ) ^ delta n k ≤ 1 / (n : ℝ) ^ 2 := by
    have hc : (Sᶜ.card : ℝ) ≤ n := by
      have := card_le_univ Sᶜ
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    calc (k : ℝ) * (Sᶜ.card : ℝ) * (q : ℝ) ^ delta n k ≤ n * n * (1 / (n : ℝ) ^ 4) := by
          gcongr
      _ = 1 / (n : ℝ) ^ 2 := by field_simp
  have hx0 : 0 ≤ (k : ℝ) * (Sᶜ.card : ℝ) * (q : ℝ) ^ delta n k := by positivity
  have hx1 : (k : ℝ) * (Sᶜ.card : ℝ) * (q : ℝ) ^ delta n k ≤ 1 := by
    refine hx.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  calc ∑ j ∈ Icc 1 k, ((k : ℝ) * Sᶜ.card * (q : ℝ) ^ delta n k) ^ j
      ≤ ∑ _j ∈ Icc 1 k, (k : ℝ) * Sᶜ.card * (q : ℝ) ^ delta n k := by
        refine sum_le_sum fun j hj ↦ ?_
        rw [mem_Icc] at hj
        exact pow_le_of_le_one hx0 hx1 (by omega)
    _ = k * ((k : ℝ) * Sᶜ.card * (q : ℝ) ^ delta n k) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ n * (1 / (n : ℝ) ^ 2) := by gcongr
    _ = 1 / n := by field_simp

/-! ### The success probability as a sum -/

/-- `p` as a point of the unit interval. -/
def toI {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) : I := ⟨p, hp, hp1.le⟩

theorem erdosRenyiProb_eq {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (R : SimpleGraph (Fin n)) :
    erdosRenyiProb p R = (G(Fin n, toI hp hp1)).real {R} := by
  unfold erdosRenyiProb
  exact (binomialRandom_real_singleton (toI hp hp1) R).symm

/-- Probabilities of events as sums over the graphs. -/
theorem real_eq_sum_ite {n : ℕ} (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ]
    (P : SimpleGraph (Fin n) → Prop) [DecidablePred P] :
    μ.real {R | P R} = ∑ R, if P R then μ.real {R} else 0 := by
  have hset : ({R | P R} : Set (SimpleGraph (Fin n))) =
      ((univ.filter P : Finset (SimpleGraph (Fin n))) : Set (SimpleGraph (Fin n))) := by
    ext
    simp
  rw [hset, ← sum_measureReal_singleton, sum_filter]

/-! ### Success, deterministically -/

/-- The graph of the adversary is planted on `S` with the cut of `R`. -/
theorem planted_adv {n : ℕ} (Adv : Adversary n) (S : Finset (Fin n)) (R : SimpleGraph (Fin n)) :
    Planted (Adv.graph S R) R S :=
  ⟨Adv.clique S R, fun a ha v hv ↦ Adv.cut S R a v ha hv⟩

/-- Adding edges keeps the clique, and adds them to the cut. -/
theorem planted_sup {n : ℕ} {G R : SimpleGraph (Fin n)} {S : Finset (Fin n)} (h : Planted G R S)
    (Z : SimpleGraph (Fin n)) : Planted (G ⊔ Z) (R ⊔ Z) S :=
  ⟨fun a ha b hb hab ↦ Or.inl (h.clique a ha b hb hab), fun a ha v hv ↦ by
    simp only [SimpleGraph.sup_adj]
    rw [h.onCut a ha v hv]⟩

/-- **Success, deterministically.** If the cut of `R` has no biclique with `Δ` vertices in `S`,
`k` is in range, and `S` is the refined set of a triple at a grid point, the algorithm succeeds on
the adversary's graph with the coins `r`. -/
theorem succeeds_of {n k : ℕ} {C : ℝ} (hn : 3 ≤ n) (hC : 2 ≤ C)
    (hk : C * √(n : ℝ) * Real.log n ^ 2 ≤ k) (hkn : k ≤ n) {S : Finset (Fin n)} (hS : S.card = k)
    (Adv : Adversary n) {R : SimpleGraph (Fin n)} (hNB : NoBiclique S (delta n k) R)
    (r : List Bool)
    (hcand : (∃ j, gridM n / 2 ≤ j ∧ j < gridM n ∧ ∃ α : Finset (Fin n), α.card = 3 ∧
          refine (Adv.graph S R) k (selected ((j : ℝ) / gridM n) (Adv.graph S R) k α) = S) ∨
        (∃ j ≤ gridM n / 2, ∃ α : Finset (Fin n), α.card = 3 ∧
          refine (Adv.graph S R ⊔ Sampling.chunkGraph n (nBits n) j r) k
            (selected (1 / 2) (Adv.graph S R ⊔ Sampling.chunkGraph n (nBits n) j r) k α) = S)) :
    Succeeds k (Adv.graph S R) S
      ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C ^ 2 * Real.log n ^ 4))) * n / k)
      (alg (input (Adv.graph S R) k, r)) := by
  obtain ⟨hΔk, h2, -, hδ⟩ := delta_facts hn hC hk hkn
  have hP := planted_adv Adv S R
  have hScl : (Adv.graph S R).IsNClique k S := by
    refine ⟨fun a ha b hb hab ↦ hP.clique a ha b hb hab, hS⟩
  have hother : ∀ S', (Adv.graph S R).IsNClique k S' → S' ≠ S → (S' ∩ S).card < delta n k :=
    fun S' hS' hne ↦ Pruning.card_inter_lt hS hNB
      (fun u hu v hv h ↦ (hP.onCut u hu v hv).1 h) hS' hne
  obtain ⟨h1, h2', h3⟩ := alg_spec (k := k) (Adv.graph S R) r
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hΛ : 1 ≤ Real.log n := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        linarith [Real.exp_one_lt_d9]
      have := Real.sqrt_pos.2 (show (0 : ℝ) < n by linarith)
      have : 0 < C * √(n : ℝ) * Real.log n ^ 2 := by positivity
      linarith
    exact_mod_cast this
  refine ⟨h2' S hScl hother hcand, h1, ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  calc ((alg (input (Adv.graph S R) k, r)).length : ℝ)
      ≤ n / k * (1 + 2 * n * delta n k / (k : ℝ) ^ 2) := h3 hkpos hΔk h2
    _ ≤ n / k * (1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C ^ 2 * Real.log n ^ 4))) := by gcongr
    _ = (1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C ^ 2 * Real.log n ^ 4))) * n / k := by ring

/-! ### Coins and probabilities -/

theorem coinProb_eq_one {m : ℕ} {P : List Bool → Prop} (h : ∀ r, P r) : coinProb m P = 1 := by
  classical
  unfold coinProb
  rw [filter_true_of_mem fun r _ ↦ h _, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  exact div_self (by positivity)

theorem coinProb_mono {m : ℕ} {P Q : List Bool → Prop} (h : ∀ r, Q r → P r) :
    coinProb m Q ≤ coinProb m P := by
  classical
  unfold coinProb
  gcongr
  exact h _

theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb
  positivity

theorem coinProb_le_one (m : ℕ) (P : List Bool → Prop) : coinProb m P ≤ 1 := by
  classical
  unfold coinProb
  rw [div_le_one (by positivity)]
  have := card_le_univ (univ.filter fun r : Fin m → Bool ↦ P (List.ofFn r))
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  exact_mod_cast this

theorem length_input_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (k : ℕ) :
    (encInput (input G k)).length = (encInput (input G' k)).length := by
  have h : (adjBits G).length = (adjBits G').length := by
    rw [adjBits_eq, adjBits_eq, List.length_map, List.length_map]
  change (Encoding.frame (Encoding.encNat n) ++
      (Encoding.frame (Encoding.encNat k) ++ adjBits G)).length =
    (Encoding.frame (Encoding.encNat n) ++
      (Encoding.frame (Encoding.encNat k) ++ adjBits G')).length
  simp only [List.length_append, h]

/-- The pairs are at most `n²/2`. -/
theorem card_pair_le (n : ℕ) : (Fintype.card (Pair (Fin n)) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin, Nat.choose_two_right]
  rw [le_div_iff₀ (by norm_num)]
  have h : n * (n - 1) / 2 * 2 ≤ n ^ 2 := (Nat.div_mul_le_self _ 2).trans
    (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have : ((n * (n - 1) / 2 * 2 : ℕ) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at this
  linarith

/-- The total variation between a grid point within `1/M` and its target: at most `1/(2n)`. -/
theorem tv_le {n : ℕ} (hn : 1 ≤ n) (p q : I) (hpq : |(p : ℝ) - q| ≤ 1 / gridM n)
    (E : Set (SimpleGraph (Fin n))) :
    |(G(Fin n, p)).real E - (G(Fin n, q)).real E| ≤ 1 / (2 * n) := by
  refine (abs_binomialRandom_sub_le p q E).trans ?_
  have hM := cube_lt_gridM n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM' : (n : ℝ) ^ 3 ≤ gridM n := by exact_mod_cast hM.le
  calc (Fintype.card (Pair (Fin n)) : ℝ) * |(p : ℝ) - q| ≤ (n : ℝ) ^ 2 / 2 * (1 / gridM n) :=
        mul_le_mul (card_pair_le n) hpq (abs_nonneg _) (by positivity)
    _ ≤ (n : ℝ) ^ 2 / 2 * (1 / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hM') (by positivity)
    _ = 1 / (2 * n) := by field_simp

/-- No large bicliques is antitone, so it is likelier for smaller `p`. -/
theorem prob_not_noBiclique_mono {n : ℕ} (S : Finset (Fin n)) (Δ : ℕ) {p q : I} (hpq : p ≤ q) :
    (G(Fin n, p)).real {R | ¬ NoBiclique S Δ R} ≤ (G(Fin n, q)).real {R | ¬ NoBiclique S Δ R} := by
  have hE : MeasurableSet {R : SimpleGraph (Fin n) | NoBiclique S Δ R} := MeasurableSet.of_discrete
  have h := binomialRandom_le_of_antitone hpq hE fun R R' hRR' hR' A hA B hB hℓ hne hsum ↦ by
    obtain ⟨a, ha, b, hb, hab⟩ := hR' A hA B hB hℓ hne hsum
    exact ⟨a, ha, b, hb, fun h ↦ hab (hRR' h)⟩
  have hc : ∀ r : I, (G(Fin n, r)).real {R | ¬ NoBiclique S Δ R} =
      1 - (G(Fin n, r)).real {R | NoBiclique S Δ R} := fun r ↦ by
    rw [← probReal_compl_eq_one_sub hE]
    rfl
  rw [hc, hc]
  have := ENNReal.toReal_mono (measure_ne_top _ _) h
  simp only [← measureReal_def] at this
  linarith

/-! ### The success probability, bounded below -/

theorem coinProb_eq {m : ℕ} (P : List Bool → Prop) [DecidablePred P] :
    coinProb m P = ((univ.filter fun r : Fin m → Bool ↦ P (List.ofFn r)).card : ℝ) / 2 ^ m := by
  unfold coinProb
  congr

/-- The success probability as a sum over `R ∼ G(n, p)`; the number of coins does not depend on
the graph. -/
theorem successProb_eq_sum {n k : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (S : Finset (Fin n))
    (Adv : Adversary n) (A : Input × List Bool → Output) (T : ℕ → ℕ) (bound : ℝ) :
    successProb n k p S Adv A T bound = ∑ R, (G(Fin n, toI hp hp1)).real {R} *
      coinProb (T (encInput (input (⊥ : SimpleGraph (Fin n)) k)).length) fun r ↦
        Succeeds k (Adv.graph S R) S bound (A (input (Adv.graph S R) k, r)) := by
  unfold successProb
  refine sum_congr rfl fun R _ ↦ ?_
  rw [erdosRenyiProb_eq hp hp1, length_input_eq (Adv.graph S R) ⊥]

theorem sum_mul_le_sum_mul {n : ℕ} (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ]
    {f g : SimpleGraph (Fin n) → ℝ} (h : ∀ R, g R ≤ f R) :
    ∑ R, μ.real {R} * g R ≤ ∑ R, μ.real {R} * f R :=
  sum_le_sum fun R _ ↦ mul_le_mul_of_nonneg_left (h R) measureReal_nonneg

theorem sum_mul_sub_ite {n : ℕ} (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ]
    (f : SimpleGraph (Fin n) → ℝ) (B : SimpleGraph (Fin n) → Prop) [DecidablePred B] :
    ∑ R, μ.real {R} * (f R - if B R then 1 else 0) =
      ∑ R, μ.real {R} * f R - μ.real {R | B R} := by
  rw [real_eq_sum_ite μ B, ← sum_sub_distrib]
  refine sum_congr rfl fun R _ ↦ ?_
  split_ifs <;> ring

theorem sum_mul_ite {n : ℕ} (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ]
    (A : SimpleGraph (Fin n) → Prop) [DecidablePred A] :
    ∑ R, μ.real {R} * (if A R then 1 else 0) = μ.real {R | A R} := by
  rw [real_eq_sum_ite μ A]
  refine sum_congr rfl fun R _ ↦ ?_
  split_ifs <;> ring

theorem size_facts {n k : ℕ} {C p : ℝ} (hC : 0 ≤ C)
    (hsize : C * √(n : ℝ) * Real.log n ^ 2 * max 1 ((p / (1 - p)) ^ 4) ≤ k) :
    C * √(n : ℝ) * Real.log n ^ 2 ≤ k ∧ C * √(n : ℝ) * Real.log n ^ 2 * (p / (1 - p)) ^ 4 ≤ k := by
  have h0 : 0 ≤ C * √(n : ℝ) * Real.log n ^ 2 := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left (le_max_left 1 ((p / (1 - p)) ^ 4)) h0
    linarith
  · have := mul_le_mul_of_nonneg_left (le_max_right 1 ((p / (1 - p)) ^ 4)) h0
    linarith

theorem final_arith {n : ℕ} (hn : 300 ≤ n) {a b c : ℝ} (ha : 1 - 1 / 400 ≤ a)
    (hab : |b - a| ≤ 1 / (2 * n)) (hc : c ≤ 1 / n) : 0.99 ≤ b - c := by
  have hn' : (300 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (n : ℝ) ≤ 1 / 300 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : 1 / (2 * (n : ℝ)) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have := (abs_le.1 hab).1
  norm_num at *
  linarith

theorem gridM_pos (n : ℕ) : (0 : ℝ) < gridM n := by
  have := two_le_gridM n
  have : (2 : ℝ) ≤ gridM n := by exact_mod_cast this
  linarith

theorem cast_gridM_half (n : ℕ) : ((gridM n / 2 : ℕ) : ℝ) = 1 / 2 * gridM n := by
  have := gridM_half n
  rwa [div_eq_iff (gridM_pos n).ne'] at this

/-- **`p ≥ 1/2`.** The grid point `q = ⌊pM⌋/M`. -/
theorem le_successProb_high {n k : ℕ} {C₁ : ℝ} (hC₁ : 12 ≤ C₁) (hn : 300 ≤ n)
    {S : Finset (Fin n)} (hS : S.card = k)
    (hrec : ∀ q : I, 1 / 2 ≤ (q : ℝ) → (q : ℝ) < 1 →
      C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k →
      1 - 1 / 400 ≤ (G(Fin n, q)).real {R | Recovers q k S R})
    {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1)
    (hsize : C₁ * √(n : ℝ) * Real.log n ^ 2 * (p / (1 - p)) ^ 4 ≤ k)
    (hk : C₁ * √(n : ℝ) * Real.log n ^ 2 ≤ k) (hkn : k ≤ n) (Adv : Adversary n) (m : ℕ) :
    0.99 ≤ ∑ R, (G(Fin n, toI (by linarith) hp1)).real {R} * coinProb m fun r ↦
      Succeeds k (Adv.graph S R) S
        ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4))) * n / k)
        (alg (input (Adv.graph S R) k, r)) := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hMpos := gridM_pos n
  obtain ⟨j, hj⟩ : ∃ j, j = ⌊p * gridM n⌋₊ := ⟨_, rfl⟩
  have hj1 : (j : ℝ) ≤ p * gridM n := hj ▸ Nat.floor_le (by positivity)
  have hj2 : p * gridM n < j + 1 := hj ▸ Nat.lt_floor_add_one _
  have hjlo : gridM n / 2 ≤ j := by
    rw [hj]
    apply Nat.le_floor
    rw [cast_gridM_half]
    nlinarith
  have hjM : j < gridM n := by
    have : (j : ℝ) < gridM n := by nlinarith
    exact_mod_cast this
  obtain ⟨q, hq⟩ : ∃ q : I, (q : ℝ) = j / gridM n :=
    ⟨⟨j / gridM n, by positivity, (div_le_one hMpos).2 (by exact_mod_cast hjM.le)⟩, rfl⟩
  have hq12 : 1 / 2 ≤ (q : ℝ) := by
    rw [hq, le_div_iff₀ hMpos, ← cast_gridM_half]
    exact_mod_cast hjlo
  have hqp : (q : ℝ) ≤ p := by
    rw [hq, div_le_iff₀ hMpos]
    exact hj1
  have hq1 : (q : ℝ) < 1 := by linarith
  have hpq : |((toI (by linarith) hp1 : I) : ℝ) - q| ≤ 1 / gridM n := by
    change |p - q| ≤ _
    rw [abs_of_nonneg (by linarith), hq]
    have e : p - j / gridM n = (p * gridM n - j) / gridM n := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hMpos.le
  have hsq : C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k := by
    refine le_trans ?_ hsize
    have h1 : (q : ℝ) / (1 - q) ≤ p / (1 - p) :=
      div_le_div₀ hp0 hqp (by linarith) (by linarith)
    gcongr
  have hrq := hrec q hq12 hq1 hsq
  have htv := tv_le (by omega) (toI (by linarith) hp1) q hpq {R | Recovers q k S R}
  have hnb := prob_not_noBiclique_le (q := toI (by linarith) hp1) hp hp1 hC₁ (by omega) hsize
    hkn S hS
  refine (final_arith hn hrq htv hnb).trans ?_
  rw [← sum_mul_ite, ← sum_mul_sub_ite]
  refine sum_mul_le_sum_mul _ fun R ↦ ?_
  by_cases hNB : NoBiclique S (delta n k) R
  · rw [ite_eq_right_iff.2 fun h ↦ absurd hNB h, sub_zero]
    by_cases hR : Recovers q k S R
    · rw [ite_eq_left_iff.2 fun h ↦ absurd hR h]
      refine (coinProb_eq_one fun r ↦ ?_).ge
      obtain ⟨α, hα, hαS⟩ := hR _ (planted_adv Adv S R)
      refine succeeds_of (by omega) (by linarith) hk hkn hS Adv hNB r
        (Or.inl ⟨j, hjlo, hjM, α, (mem_powersetCard.1 hα).2, ?_⟩)
      rw [← hq]
      exact hαS
    · rw [ite_eq_right_iff.2 fun h ↦ absurd h hR]
      exact coinProb_nonneg _ _
  · have := coinProb_nonneg m fun r ↦ Succeeds k (Adv.graph S R) S
      ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4))) * n / k)
      (alg (input (Adv.graph S R) k, r))
    split_ifs <;> linarith

/-- **`p < 1/2`.** The coins add `G(n, j/M)`, `j = ⌊ρM⌋`, `ρ = (1/2 - p)/(1 - p)`, which makes
the edge probability `p' = p + (1 - p) j/M ∈ [1/2 - 1/M, 1/2]`. -/
theorem le_successProb_low {n k : ℕ} {C₁ : ℝ} (hC₁ : 12 ≤ C₁) (hn : 300 ≤ n)
    {S : Finset (Fin n)} (hS : S.card = k)
    (hrec : ∀ q : I, 1 / 2 ≤ (q : ℝ) → (q : ℝ) < 1 →
      C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k →
      1 - 1 / 400 ≤ (G(Fin n, q)).real {R | Recovers q k S R})
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1 / 2)
    (hk : C₁ * √(n : ℝ) * Real.log n ^ 2 ≤ k) (hkn : k ≤ n) (Adv : Adversary n) {m : ℕ}
    (hm : n.choose 2 * nBits n ≤ m) :
    0.99 ≤ ∑ R, (G(Fin n, toI hp (by linarith))).real {R} * coinProb m fun r ↦
      Succeeds k (Adv.graph S R) S
        ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4))) * n / k)
        (alg (input (Adv.graph S R) k, r)) := by
  classical
  have hMpos := gridM_pos n
  have h1p : 0 < 1 - p := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 / 2 - p) / (1 - p) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := hρ ▸ div_nonneg (by linarith) h1p.le
  have hρ12 : ρ ≤ 1 / 2 := by
    rw [hρ, div_le_iff₀ h1p]
    linarith
  have hρp : p + ρ * (1 - p) = 1 / 2 := by
    rw [hρ, div_mul_cancel₀ _ h1p.ne']
    ring
  obtain ⟨j, hj⟩ : ∃ j, j = ⌊ρ * gridM n⌋₊ := ⟨_, rfl⟩
  have hj1 : (j : ℝ) ≤ ρ * gridM n := hj ▸ Nat.floor_le (by positivity)
  have hj2 : ρ * gridM n < j + 1 := hj ▸ Nat.lt_floor_add_one _
  have hjM : j ≤ gridM n / 2 := by
    have : (j : ℝ) ≤ ((gridM n / 2 : ℕ) : ℝ) := by
      rw [cast_gridM_half]
      nlinarith
    exact_mod_cast this
  have hjb : j ≤ 2 ^ nBits n := hjM.trans (Nat.div_le_self _ _)
  obtain ⟨p', hp'⟩ : ∃ p' : I,
      p' = Sampling.supProb (toI hp (by linarith)) (Sampling.dyadic (nBits n) j hjb) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = j / gridM n := ⟨_, rfl⟩
  have hp'v : (p' : ℝ) = p + d - p * d := by
    rw [hp', hd]
    simp [Sampling.supProb, Sampling.dyadic, toI, gridM]
  have hd1 : d ≤ ρ := by
    rw [hd, div_le_iff₀ hMpos]
    exact hj1
  have hd2 : ρ - d ≤ 1 / gridM n := by
    rw [hd, show ρ - j / gridM n = (ρ * gridM n - j) / gridM n by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hMpos.le
  obtain ⟨q, hq⟩ : ∃ q : I, (q : ℝ) = 1 / 2 := ⟨⟨1 / 2, by norm_num, by norm_num⟩, rfl⟩
  have hpq : |(p' : ℝ) - q| ≤ 1 / gridM n := by
    rw [hp'v, hq]
    have e : p + d - p * d - 1 / 2 = -((ρ - d) * (1 - p)) := by
      rw [← hρp]
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) h1p.le)]
    calc (ρ - d) * (1 - p) ≤ (ρ - d) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ _ := by linarith
  have hsq : C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k := by
    have : ((1 : ℝ) / 2 / (1 - 1 / 2)) ^ 4 = 1 := by norm_num
    rw [hq, this, mul_one]
    exact hk
  have hrq := hrec q hq.ge (by rw [hq]; norm_num) hsq
  rw [hq] at hrq
  have htv := tv_le (by omega) p' q hpq {R | Recovers (1 / 2) k S R}
  have hpq' : toI hp (by linarith) ≤ q := Subtype.coe_le_coe.1 (by
    change p ≤ (q : ℝ)
    rw [hq]
    linarith)
  have hnb := (prob_not_noBiclique_mono S (delta n k) hpq').trans
    (prob_not_noBiclique_le (q := q) hq.ge (by rw [hq]; norm_num) hC₁ (by omega) hsq hkn S hS)
  refine (final_arith hn hrq htv hnb).trans ?_
  have hsum := Sampling.sum_mass_coins_sup hm hjb (toI hp (by linarith)) (Recovers (1 / 2) k S)
  rw [← hp'] at hsum
  have hc : ∀ R : SimpleGraph (Fin n),
      coinProb m (fun r ↦ Recovers (1 / 2) k S (R ⊔ Sampling.chunkGraph n (nBits n) j r)) =
        ((univ.filter fun c : Fin m → Bool ↦
          Recovers (1 / 2) k S (R ⊔ Sampling.chunkGraph n (nBits n) j (List.ofFn c))).card : ℝ) /
          2 ^ m := fun R ↦ coinProb_eq _
  simp only [← hc] at hsum
  rw [← hsum, ← sum_mul_sub_ite]
  refine sum_mul_le_sum_mul _ fun R ↦ ?_
  by_cases hNB : NoBiclique S (delta n k) R
  · rw [ite_eq_right_iff.2 fun h ↦ absurd hNB h, sub_zero]
    refine coinProb_mono fun r hr ↦ ?_
    obtain ⟨α, hα, hαS⟩ :=
      hr _ (planted_sup (planted_adv Adv S R) (Sampling.chunkGraph n (nBits n) j r))
    exact succeeds_of (by omega) (by linarith) hk hkn hS Adv hNB r
      (Or.inr ⟨j, hjM, α, (mem_powersetCard.1 hα).2, hαS⟩)
  · have := coinProb_nonneg m fun r ↦ Succeeds k (Adv.graph S R) S
      ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4))) * n / k)
      (alg (input (Adv.graph S R) k, r))
    have := coinProb_le_one m
      fun r ↦ Recovers (1 / 2) k S (R ⊔ Sampling.chunkGraph n (nBits n) j r)
    split_ifs
    linarith

/-- **The success probability for fixed large `n`** [BBKS24, Theorem 4.1]: with `n ≥ 300`,
`C₁ ≥ 12`, recovery at every grid point with probability `1 - 1/400`, and enough coins. -/
theorem le_successProb {n k : ℕ} {C₁ : ℝ} (hC₁ : 12 ≤ C₁) (hn : 300 ≤ n)
    {S : Finset (Fin n)} (hS : S.card = k)
    (hrec : ∀ q : I, 1 / 2 ≤ (q : ℝ) → (q : ℝ) < 1 →
      C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k →
      1 - 1 / 400 ≤ (G(Fin n, q)).real {R | Recovers q k S R})
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (hsize : C₁ * √(n : ℝ) * Real.log n ^ 2 * max 1 ((p / (1 - p)) ^ 4) ≤ k) (hkn : k ≤ n)
    (Adv : Adversary n) (T : ℕ → ℕ)
    (hT : n.choose 2 * nBits n ≤ T (encInput (input (⊥ : SimpleGraph (Fin n)) k)).length) :
    0.99 ≤ successProb n k p S Adv alg T
      ((1 + (2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4))) * n / k) := by
  obtain ⟨hk, hk'⟩ := size_facts (by linarith) hsize
  rw [successProb_eq_sum hp hp1]
  rcases le_or_gt (1 / 2) p with h | h
  · exact le_successProb_high hC₁ hn hS hrec h hp1 hk' hk hkn Adv _
  · exact le_successProb_low hC₁ hn hS hrec hp h hk hkn Adv hT

/-! ### For all large `n` -/

theorem choose_le_length_input {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    n.choose 2 ≤ (encInput (input G k)).length := by
  have h : (adjBits G).length = n.choose 2 := by
    rw [adjBits_eq, List.length_map, Sampling.length_pairsF]
  change n.choose 2 ≤ (Encoding.frame (Encoding.encNat n) ++
    (Encoding.frame (Encoding.encNat k) ++ adjBits G)).length
  simp only [List.length_append, h]
  omega

/-- With time `(N + 2)^d`, `d ≥ 2`, there are enough coins: `C(n, 2) · 3L`. -/
theorem coins_le {n d : ℕ} (hn : 7 ≤ n) (hd : 2 ≤ d) (k : ℕ) :
    n.choose 2 * nBits n ≤ ((encInput (input (⊥ : SimpleGraph (Fin n)) k)).length + 2) ^ d := by
  have h1 := choose_le_length_input (⊥ : SimpleGraph (Fin n)) k
  have h2 : nBits n ≤ n.choose 2 := by
    have hL : logN n ≤ n := by
      have := Nat.log_lt_self 2 (show n ≠ 0 by omega)
      unfold logN
      omega
    have h6 : n * 6 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    unfold nBits
    omega
  obtain ⟨N, hN⟩ : ∃ N, N = (encInput (input (⊥ : SimpleGraph (Fin n)) k)).length := ⟨_, rfl⟩
  rw [← hN] at h1 ⊢
  calc n.choose 2 * nBits n ≤ (N + 2) * (N + 2) := Nat.mul_le_mul (by omega) (by omega)
    _ = (N + 2) ^ 2 := (sq _).symm
    _ ≤ (N + 2) ^ d := Nat.pow_le_pow_right (by omega) hd

/-- The excess of the list size, `δ(n) = 2/L³ + 2/(C² log⁴ n)`, tends to `0`. -/
theorem tendsto_delta {C₁ : ℝ} (hC₁ : 0 < C₁) :
    Tendsto (fun n : ℕ ↦ 2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ ↦ (logN n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlog
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := lt_two_pow_logN n
    have h1 : Real.log n < logN n * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast h)
    have h2 : (logN n : ℝ) * Real.log 2 ≤ logN n :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith [Real.log_two_lt_d9])
    linarith
  rw [show (0 : ℝ) = 0 + 0 by simp]
  refine Tendsto.add ?_ ?_
  · exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hL)
  · exact tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop (by positivity) ((tendsto_pow_atTop (by norm_num)).comp hlog))

/-- **[BBKS24, Theorem 4.1]**, for the algorithm `alg` with any time bound `(N + 2)^d`, `d ≥ 2`
(enough for the coins). -/
theorem eventually_le_successProb : ∃ C : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ d : ℕ, 2 ≤ d → ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
      C * √(n : ℝ) * Real.log n ^ 2 * max 1 ((p / (1 - p)) ^ 4) ≤ k → k ≤ n →
      ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
        0.99 ≤ successProb n k p S Adv alg (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) := by
  obtain ⟨C₁, hC₁, hev⟩ := eventually_recovers
  refine ⟨C₁, fun n ↦ 2 / (logN n : ℝ) ^ 3 + 2 / (C₁ ^ 2 * Real.log n ^ 4),
    tendsto_delta (by linarith), fun d hd ↦ ?_⟩
  filter_upwards [hev, eventually_ge_atTop 300] with n hrec hn p hp hp1 k hsize hkn S hS Adv
  exact le_successProb (by linarith) hn hS (fun q hq hq1 hsq ↦ hrec q hq hq1 k hsq hkn S hS)
    hp hp1 hsize hkn Adv _ (coins_le (by omega) hd k)

end BBKS24.Asm
