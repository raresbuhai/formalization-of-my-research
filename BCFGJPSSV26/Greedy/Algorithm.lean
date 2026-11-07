module

public import BCFGJPSSV26.Greedy.Alg.Core
public import BCFGJPSSV26.Greedy.Reduction.Scale
public import BCFGJPSSV26.Stable.Alg.LocalSearch
public import BCFGJPSSV26.Stable.LocalSearch.ThreeApprox

/-!
# The algorithms of Theorem 1.2

On the tuple `(n, m, k, table)` of an instance (`BCFGJPSSV26.Raw`):

* **The main algorithm** (`BCFGJPSSV26.Greedy.algMain`, for constants `c`): output the trivial
  solution if it has at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities (this covers `opt = 0`, `n ≤ 1`
  and `k ≥ m`); otherwise run the core on the scaled input for every guess `Λ` and output the
  cheapest output (`BCFGJPSSV26.Combine.best`, among the lists of at most `k + 6R` distinct
  facilities). Its guarantee (`BCFGJPSSV26.Greedy.algMain_spec`): cost at most
  `(ρ + 10δ)(1 + ε') opt k`; at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities, or, when the trivial
  solution is too large (then `⌊log₂ n⌋ ⌈1/δ²⌉ < n`), at most `k + 6R`.
* **The large-`ε` algorithm** (`BCFGJPSSV26.Greedy.algLS`): the trivial solution if it has at most
  `k` facilities, otherwise the local search of Part II (`BCFGJPSSV26.Stable.localSearch`, swaps of
  size `24 N` for `N = 201`, polynomial budget), whose output is an approximate local optimum of
  cost at most `4 opt k` (`BCFGJPSSV26.Stable.isALO_localSearch`,
  `BCFGJPSSV26.Stable.costF_le_four_opt`). Its guarantee: `BCFGJPSSV26.Greedy.algLS_spec`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-! ### The main algorithm -/

/-- The number of extra facilities allowed to the trivial solution: `⌊log₂ n⌋ ⌈1/δ²⌉`. -/
def bcomp (c : Consts) (n : ℕ) : ℕ := Nat.log 2 n * ⌈1 / c.δ ^ 2⌉₊

/-- The outputs of the core for all guesses. -/
def coreRuns (c : Consts) (x : Raw) : List (List ℕ) :=
  (guesses x).map fun Λ ↦ core c (scaledIn c x Λ)

/-- **The main algorithm** for the constants `c`. -/
def algMain (c : Consts) (x : Raw) : List ℕ :=
  if trivialSol x = [] then [0]
  else if (trivialSol x).length ≤ x.k + bcomp c x.n then trivialSol x
  else Combine.best x.n x.m (x.k + 6 * Rof c x.n) x.table (coreRuns c x)

/-- The arithmetic of the reduction: with `Λ ≤ opt ≤ n Λ`, `t = ε' Λ / n` and a ratio
`r ∈ [1, 41/20]`, a scaled cost `s ≤ r (opt / t + n)` is below `M = 8 n² / ε' + 1`, and
`t s ≤ r (1 + ε') opt`. -/
theorem scale_arith {n εp Λ opt r s : ℝ} (hn : 1 ≤ n) (hε : 0 < εp) (hε1 : εp ≤ 1) (hΛ : 0 < Λ)
    (hΛo : Λ ≤ opt) (hon : opt ≤ n * Λ) (hr : 1 ≤ r) (hr' : r ≤ 41 / 20)
    (hs : s ≤ r * (opt / (εp * Λ / n) + n)) :
    s < 8 * n ^ 2 / εp + 1 ∧ εp * Λ / n * s ≤ r * (1 + εp) * opt := by
  have hn0 : 0 < n := by linarith
  have ht : 0 < εp * Λ / n := by positivity
  have hopt : 0 < opt := hΛ.trans_le hΛo
  have h1 : opt / (εp * Λ / n) ≤ n ^ 2 / εp := by
    rw [div_le_div_iff₀ ht hε]
    have e : n ^ 2 * (εp * Λ / n) = n * εp * Λ := by
      field_simp
    rw [e]
    nlinarith
  have h2 : n ≤ n ^ 2 / εp := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hq : 0 ≤ n ^ 2 / εp := by positivity
  constructor
  · have h3 : s ≤ r * (2 * (n ^ 2 / εp)) :=
      hs.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have e8 : 8 * n ^ 2 / εp = 8 * (n ^ 2 / εp) := by ring
    have h4 := mul_le_mul_of_nonneg_right hr' (by positivity : (0 : ℝ) ≤ 2 * (n ^ 2 / εp))
    rw [e8]
    linarith
  · have e : εp * Λ / n * (r * (opt / (εp * Λ / n) + n)) = r * (opt + εp * Λ) := by
      field_simp
    calc εp * Λ / n * s ≤ εp * Λ / n * (r * (opt / (εp * Λ / n) + n)) :=
          mul_le_mul_of_nonneg_left hs ht.le
      _ = r * (opt + εp * Λ) := e
      _ ≤ r * (1 + εp) * opt := by
          nlinarith [mul_le_mul_of_nonneg_left hΛo (by positivity : (0 : ℝ) ≤ r * εp)]

theorem ratio_ge_one {c : Consts} (hc : c.Good) : (1 : ℚ) ≤ (ρ + 10 * c.δ) * (1 + c.εp) := by
  have := one_le_ρ
  have := hc.δ_pos
  have := hc.εp_pos
  nlinarith

/-- **The guarantee of the main algorithm.** -/
theorem algMain_spec {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algMain c (toRaw I)) ∧
      ((algMain c (toRaw I)).length ≤ I.k + bcomp c I.n ∨
        (bcomp c I.n < I.n ∧ 2 ≤ I.n ∧ (algMain c (toRaw I)).length ≤ I.k + 6 * Rof c I.n)) ∧
      I.cost (I.centers (algMain c (toRaw I))) ≤
        (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) * I.opt I.k := by
  have hratio : (1 : ℝ) ≤ (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) := by
    exact_mod_cast ratio_ge_one hc
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hk1 := hI.one_le_k
  have hm1 := hI.one_le_m
  unfold algMain
  split_ifs with h0 h1
  · -- no clients
    have hn0 : I.n = 0 := trivialSol_eq_nil_iff.1 h0
    refine ⟨⟨by simp, by simp, fun i hi ↦ ?_⟩, .inl ?_, ?_⟩
    · rw [List.mem_singleton] at hi
      omega
    · simp only [List.length_singleton]
      omega
    · have : I.cost (I.centers [0]) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ absurd j.2 (by omega)
      rw [this]
      positivity
  · -- the trivial solution
    have hn : 1 ≤ I.n := by
      by_contra hn
      exact h0 (trivialSol_eq_nil_iff.2 (by omega))
    exact ⟨isCenterList_trivialSol hI hn, .inl h1,
      (cost_trivialSol_le hI hn).trans (le_mul_of_one_le_left hopt0 hratio)⟩
  · -- the core on the guesses
    have hk : I.k < (trivialSol (toRaw I)).length := by
      change ¬ _ ≤ I.k + bcomp c I.n at h1
      omega
    obtain ⟨hpos, hn2, hkn, hkm⟩ := of_k_lt_length hI hk
    have hbn : bcomp c I.n < I.n := by
      have := trivialSol_length_le_n (I := I)
      change ¬ _ ≤ I.k + bcomp c I.n at h1
      omega
    obtain ⟨O, hOopt, Λ, hΛmem, hΛpos, hΛopt, hoptΛ⟩ := exists_good_guess hI hkm.le hpos
    have hx := coreOK_scaled hc hI hn2 hkn hkm hΛpos
    obtain ⟨hSne, hSnd, hSlt, hSlen, hScost⟩ := core_spec hc hx
    have hSmem : core c (scaledIn c (toRaw I) Λ) ∈ coreRuns c (toRaw I) :=
      List.mem_map.2 ⟨Λ, hΛmem, rfl⟩
    have hSvalid : Combine.valid I.m (I.k + 6 * Rof c I.n)
        (core c (scaledIn c (toRaw I) Λ)) = true :=
      Combine.valid_iff.2 ⟨hSne, hSnd, hSlt, hSlen⟩
    obtain ⟨hbv, hbcost⟩ := Combine.costQ_best_le (n := I.n) (distTable I) hSmem hSvalid
    obtain ⟨hBne, hBnd, hBlt, hBlen⟩ := Combine.valid_iff.1 hbv
    refine ⟨⟨hBne, hBnd, hBlt⟩, .inr ⟨hbn, hn2, hBlen⟩, ?_⟩
    -- the cost of the output is at most that of the core on the right guess
    have hB : I.cost (I.centers (Combine.best I.n I.m (I.k + 6 * Rof c I.n) (distTable I)
        (coreRuns c (toRaw I)))) ≤ I.cost (I.centers (core c (scaledIn c (toRaw I) Λ))) := by
      rw [← Combine.costQ_eq I hBne hBlt, ← Combine.costQ_eq I hSne hSlt]
      exact_mod_cast hbcost
    refine hB.trans ?_
    -- the core on the right guess
    have hn1 : 1 ≤ I.n := by omega
    have hOne := hOopt.nonempty hI
    have hOk : O.card ≤ I.k := hOopt.card.le
    have hsc := hScost O hOne hOk
    have hsc' := costF_scaled_le hc hI hn1 hΛpos hOne
    rw [hOopt.cost] at hsc'
    have hρ : ρ + 10 * c.δ ≤ 41 / 20 := by
      have := hc.δ_le
      rw [ρ_eq]
      linarith
    have hr1 : (1 : ℚ) ≤ ρ + 10 * c.δ := by
      have := one_le_ρ
      have := hc.δ_pos
      linarith
    have hs : (coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) : ℝ) ≤
        ((ρ + 10 * c.δ : ℚ) : ℝ) * (I.opt I.k / (c.εp * Λ / I.n) + I.n) := by
      have h1 : (coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) : ℝ) ≤
          ((ρ + 10 * c.δ : ℚ) : ℝ) *
            (costF (scaledSpace c hc I hI (by omega) Λ hΛpos).d O : ℝ) := by
        exact_mod_cast hsc
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ht : ((tOf c I.n Λ : ℚ) : ℝ) = (c.εp : ℝ) * Λ / I.n := by
        simp [tOf]
      rw [← ht]
      exact hsc'
    obtain ⟨hcap, hfin⟩ := scale_arith (by exact_mod_cast hn1) (by exact_mod_cast hc.εp_pos)
      (by exact_mod_cast hc.εp_le) (by exact_mod_cast hΛpos) hΛopt hoptΛ
      (by exact_mod_cast hr1)
      (by have h := (Rat.cast_le (K := ℝ)).2 hρ
          rwa [show ((41 / 20 : ℚ) : ℝ) = 41 / 20 by norm_num] at h) hs
    have hcap' : coreCost (scaledIn c (toRaw I) Λ) (core c (scaledIn c (toRaw I) Λ)) <
        Mof c I.n := by
      have : ((Mof c I.n : ℚ) : ℝ) = 8 * (I.n : ℝ) ^ 2 / c.εp + 1 := by
        simp [Mof]
      exact_mod_cast (this ▸ hcap)
    have hcl := cost_le_of_coreCost_lt hc hI hn1 hΛpos hSne hSlt hcap'
    have ht : ((tOf c I.n Λ : ℚ) : ℝ) = c.εp * Λ / I.n := by
      simp [tOf]
    rw [ht] at hcl
    have he : (((ρ + 10 * c.δ) * (1 + c.εp) : ℚ) : ℝ) = ((ρ + 10 * c.δ : ℚ) : ℝ) * (1 + c.εp) := by
      push_cast
      ring
    rw [he]
    exact hcl.trans hfin

/-! ### The large-`ε` algorithm -/

/-- The parameter `N` of the local search of Part II. -/
def lsN : ℕ := 201

/-- The budget of the local search: `(|enc x| + 2)^(2 p + 2)` for swaps of size `p = 24 N`. -/
def lsBudget (x : Raw) : ℕ := ((encRaw x).length + 2) ^ (2 * Stable.Par.p lsN + 2)

/-- **The large-`ε` algorithm.** -/
def algLS (x : Raw) : List ℕ :=
  if trivialSol x = [] then [0]
  else if (trivialSol x).length ≤ x.k then trivialSol x
  else Stable.localSearch lsN x (lsBudget x)

/-- The budget suffices for the local search when `k < m`. -/
theorem lsBudget_ge {I : Instance} (hkm : I.k < I.m) :
    (I.k * I.m) ^ Stable.Par.p lsN ≤ lsBudget (toRaw I) ∧
      2 * lsN * I.k * (encInstance I).length + 2 ≤ lsBudget (toRaw I) := by
  -- the encoding has a row for each point
  have hL : I.m ≤ (encInstance I).length := by
    have h : (distTable I).length ≤
        (Encoding.encList (Encoding.encList Encoding.encRat) (distTable I)).length :=
      Turing.MultiTapeTM.length_le_length_encList _ _
    have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
    rw [Combine.length_encInstance]
    omega
  have hB : lsBudget (toRaw I) =
      ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) := by
    rw [lsBudget, ← encInstance_eq]
  rw [hB]
  have hp : 9 ≤ 2 * Stable.Par.p lsN := by
    norm_num [Stable.Par.p, lsN]
  have hkL : I.k * I.m ≤ ((encInstance I).length + 2) ^ 2 := by
    have := Nat.mul_le_mul (hkm.le.trans hL) hL
    nlinarith
  constructor
  · calc (I.k * I.m) ^ Stable.Par.p lsN
        ≤ (((encInstance I).length + 2) ^ 2) ^ Stable.Par.p lsN := Nat.pow_le_pow_left hkL _
      _ = ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) := by rw [← pow_mul]
      _ ≤ ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  · have h512 : 2 ^ 9 ≤ ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) :=
      (Nat.pow_le_pow_right (by norm_num) hp).trans (Nat.pow_le_pow_left (by omega) _)
    have hsplit : ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) =
        ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) *
          ((encInstance I).length + 2) ^ 2 := pow_add _ _ _
    rw [hsplit]
    have hk : I.k ≤ (encInstance I).length := hkm.le.trans hL
    have h1 : 2 * lsN * I.k * (encInstance I).length + 2 ≤
        2 ^ 9 * ((encInstance I).length + 2) ^ 2 := by
      have := Nat.mul_le_mul_left (2 * lsN) (Nat.mul_le_mul_right (encInstance I).length hk)
      unfold lsN at this ⊢
      nlinarith
    exact h1.trans (Nat.mul_le_mul_right _ h512)

/-- **The guarantee of the large-`ε` algorithm**: at most `k` facilities, of cost at most
`4 opt k`. -/
theorem algLS_spec {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algLS (toRaw I)) ∧ (algLS (toRaw I)).length ≤ I.k ∧
      I.cost (I.centers (algLS (toRaw I))) ≤ 4 * I.opt I.k := by
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hk1 := hI.one_le_k
  have hm1 := hI.one_le_m
  unfold algLS
  split_ifs with h0 h1
  · have hn0 : I.n = 0 := trivialSol_eq_nil_iff.1 h0
    refine ⟨⟨by simp, by simp, fun i hi ↦ ?_⟩, ?_, ?_⟩
    · rw [List.mem_singleton] at hi
      omega
    · simp only [List.length_singleton]
      omega
    · have : I.cost (I.centers [0]) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ absurd j.2 (by omega)
      rw [this]
      positivity
  · have hn : 1 ≤ I.n := by
      by_contra hn
      exact h0 (trivialSol_eq_nil_iff.2 (by omega))
    exact ⟨isCenterList_trivialSol hI hn, h1, (cost_trivialSol_le hI hn).trans (by linarith)⟩
  · have hk : I.k < (trivialSol (toRaw I)).length := by
      change ¬ _ ≤ I.k at h1
      omega
    obtain ⟨-, -, -, hkm⟩ := of_k_lt_length hI hk
    obtain ⟨hnd, hlen, hlt⟩ := Stable.localSearch_spec hkm.le lsN (lsBudget (toRaw I))
    have hne : Stable.localSearch lsN (toRaw I) (lsBudget (toRaw I)) ≠ [] := by
      intro h
      rw [h, List.length_nil] at hlen
      omega
    obtain ⟨hB₁, hB₂⟩ := lsBudget_ge hkm
    have hALO := Stable.isALO_localSearch hI hkm.le (by norm_num [lsN]) hB₁ hB₂
    have h4 := Stable.costF_le_four_opt hI hkm.le (le_refl lsN) hALO
    refine ⟨⟨hne, hnd, hlt⟩, hlen.le, ?_⟩
    rw [← Instance.costF_eq_cost (Instance.centers_nonempty hne hlt)]
    exact h4

end BCFGJPSSV26.Greedy
